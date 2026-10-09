import LeanNCD.Semantics.Source.NumericalProfile
import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter

namespace LeanNCD.Semantics.Source.NativeLegs

open LeanNCD.Eval LeanNCD.Eval.Plan
open NumericalProfile

structure NativeSource where
  snapshot : SourceSnapshot
  admitted : AdmittedSource
  admission : admitSource snapshot = .ok admitted

def NativeSource.program (source : NativeSource) : TLProgram :=
  ⟨source.snapshot.resolved.decls, source.snapshot.resolved.stmts⟩

inductive IdentityRefusal
  | sameNameDistinctUID (first second : AxisSpec)
  | sameUIDDistinctName (first second : AxisSpec)
  deriving DecidableEq, Repr

private def programAxes (program : TLProgram) : List AxisSpec :=
  program.decls.flatMap (fun d =>
    (Decl.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) d).run) ++
  program.stmts.flatMap (fun s =>
    (Stmt.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run)

/-- The production resolver canonicalizes by name. Only a bijective name/UID relation
can preserve resolved-source identity through that intentional relabeling. -/
def checkIdentity (source : NativeSource) : Except IdentityRefusal (List AxisSpec) := do
  let axes := programAxes source.program
  let mut seen : List AxisSpec := []
  for ax in axes do
    for previous in seen do
      if previous.name == ax.name && previous.uid != ax.uid then
        throw (.sameNameDistinctUID previous ax)
      if previous.uid == ax.uid && previous.name != ax.name then
        throw (.sameUIDDistinctName previous ax)
    seen := seen ++ [ax]
  pure axes

private def checkInputBuffers (source : AdmittedSource) :
    Except Unsupported
      (Std.HashMap String DenseTensor × List CheckedValue) := do
  let mut env : Std.HashMap String DenseTensor := {}
  let mut values := []
  for t in List.finRange source.source.table.entries.length do
    let entry := source.source.table.entry t
    if h : entry.role = .input then
      let mut data : Array Float := #[]
      for (value, cell) in (source.source.inputs.buffers t h).values.zipIdx do
        let checked ← checkValue
          { origin := { side := .input, declaration := some entry.declaration },
            cell := some cell } .input value
        data := data.push (Float.ofBits (expectedBits checked.integer))
        values := values ++ [checked]
      env := env.insert entry.name ⟨entry.axes.map Axis.extent, data⟩
  pure (env, values)

structure NativeInputs (source : AdmittedSource) where
  env : Std.HashMap String DenseTensor
  values : List CheckedValue
  checked : checkInputBuffers source = .ok (env, values)

def prepareNativeInputs (source : AdmittedSource) :
    Except Unsupported (NativeInputs source) :=
  match h : checkInputBuffers source with
  | .error reason => .error reason
  | .ok (env, values) => .ok ⟨env, values, h⟩

structure TensorOrigin where
  tensorUID : UID
  declaration : Nat
  name : String
  origin : SourceOrigin
  axes : Shape
  shape : List Nat
  deriving DecidableEq, Repr

def outputOrigins (source : AdmittedSource) : List TensorOrigin :=
  (List.finRange source.source.table.entries.length).filterMap fun t =>
    let entry := source.source.table.entry t
    if entry.role == .output then
      some ⟨t.val, entry.declaration, entry.name,
        { side := .declaration, declaration := some entry.declaration },
        entry.axes, entry.axes.map Axis.extent⟩
    else none

inductive BindingIssue
  | missingOutput (metadata : TensorOrigin)
  | extraOutput (name : String) (shape : List Nat) (length : Nat)
  | rank (metadata : TensorOrigin) (expected actual : List Nat)
      (expectedLength actualLength : Nat)
  | shape (metadata : TensorOrigin) (expected actual : List Nat)
      (expectedLength actualLength : Nat)
  | length (metadata : TensorOrigin) (expected actual : List Nat)
      (expectedLength actualLength : Nat)
  deriving DecidableEq, Repr

structure OutputBinding where
  metadata : TensorOrigin
  shape : List Nat
  bits : Array UInt64
  deriving DecidableEq, Repr

structure NativeObservation where
  report : EvalReport
  outputs : Except (List BindingIssue) (List OutputBinding)
  backendInternals : Debug.Evidence Unit := .unobserved .noBackendInternalHook

/-- Check every requested binding's entire structure before projecting any cells.
Inputs and declared nonoutputs remain in the raw report, never extra outputs. -/
def observeBindings (source : AdmittedSource) (report : EvalReport) : NativeObservation := Id.run do
  let requested := outputOrigins source
  let mut issues := []
  for metadata in requested do
    match report.env[metadata.name]? with
    | none => issues := issues ++ [.missingOutput metadata]
    | some actual =>
      let count := metadata.shape.foldl (· * ·) 1
      if metadata.shape.length != actual.shape.length then
        issues := issues ++ [.rank metadata metadata.shape actual.shape count actual.data.size]
      if metadata.shape != actual.shape then
        issues := issues ++ [.shape metadata metadata.shape actual.shape count actual.data.size]
      if count != actual.data.size then
        issues := issues ++ [.length metadata metadata.shape actual.shape count actual.data.size]
  for (name, actual) in report.env.toList.mergeSort (fun a b => a.1 ≤ b.1) do
    unless source.source.table.entries.any (fun entry => entry.name == name) do
      issues := issues ++ [.extraOutput name actual.shape actual.data.size]
  if !issues.isEmpty then
    return ⟨report, .error issues, .unobserved .noBackendInternalHook⟩
  let mut outputs := []
  for metadata in requested do
    match report.env[metadata.name]? with
    | none => return ⟨report, .error [.missingOutput metadata], .unobserved .noBackendInternalHook⟩
    | some actual =>
      outputs := outputs ++ [⟨metadata, actual.shape, actual.data.map Float.toBits⟩]
  return ⟨report, .ok outputs, .unobserved .noBackendInternalHook⟩

structure StatementMapping where
  name : String
  originals : List SourceOrigin
  scheduledIndex : Option Nat
  deriving DecidableEq, Repr

private def originals (source : NativeSource) (name : String) : List SourceOrigin :=
  source.admitted.statements.filterMap fun statement =>
    let entry := source.admitted.source.table.entry statement.output.tensor
    if entry.name == name then some
      { side := .output, declaration := some entry.declaration,
        statement := some statement.original }
    else none

def sourceMappings (source : NativeSource) : List StatementMapping :=
  source.snapshot.resolved.stmts.map fun statement =>
    ⟨statement.lhsName, originals source statement.lhsName, none⟩

def scheduledMappings (source : NativeSource) (scheduled : ScheduledProgram) :
    List StatementMapping :=
  scheduled.stmts.zipIdx.map fun (statement, index) =>
    let name := match statement with
      | .plain statement => statement.lhsName
      | .scan name .. | .scanPre name .. => name
    ⟨name, originals source name, some index⟩

inductive NativeUnavailable
  | identity (reason : IdentityRefusal)
  | input (reason : Unsupported)
  deriving Repr

inductive LegacyPhase
  | compilation | scheduledEvaluation
  deriving DecidableEq, Repr

structure LegacyFailure where
  phase : LegacyPhase
  original : EvalFailure
  mappings : List StatementMapping

inductive LegacyOutcome
  | unavailable (reason : NativeUnavailable)
  | failure (error : LegacyFailure)
  | observed (result : NativeObservation)

inductive CompileWarnings
  | unavailableAtSourceCompilation
  deriving DecidableEq, Repr

structure SourceCompileFailure where
  cause : CompileError
  warnings : CompileWarnings
  mappings : List StatementMapping

structure CheckedPreparationFailure where
  original : PlanCompileFailure
  mappings : List StatementMapping

structure CheckedRuntimeFailure where
  original : PlanRunFailure
  mappings : List StatementMapping

inductive CheckedOutcome
  | unavailable (reason : NativeUnavailable)
  | sourceCompilation (error : SourceCompileFailure)
  | preparation (error : CheckedPreparationFailure)
  | runtime (error : CheckedRuntimeFailure)
  | observed (result : NativeObservation) (mappings : List StatementMapping)

private def availableInputs (source : NativeSource) :
    Except NativeUnavailable (NativeInputs source.admitted) := do
  let _ ← (checkIdentity source).mapError NativeUnavailable.identity
  (prepareNativeInputs source.admitted).mapError NativeUnavailable.input

private def legacyWithInputs (source : NativeSource)
    (inputs : Except NativeUnavailable (NativeInputs source.admitted)) : LegacyOutcome :=
  match inputs with
  | .error reason => .unavailable reason
  | .ok inputs =>
    match LeanNCD.Eval.TLProgram.eval source.program inputs.env with
    | .error error =>
      let phase := match error.error with
        | .compile _ => LegacyPhase.compilation
        | _ => LegacyPhase.scheduledEvaluation
      .failure ⟨phase, error, sourceMappings source⟩
    | .ok report => .observed (observeBindings source.admitted report)

private def checkedWithInputs (source : NativeSource)
    (inputs : Except NativeUnavailable (NativeInputs source.admitted)) : CheckedOutcome :=
  match inputs with
  | .error reason => .unavailable reason
  | .ok inputs =>
    match source.program.compileToScheduled |>.run 0 with
    | .error cause _ =>
      .sourceCompilation ⟨cause, .unavailableAtSourceCompilation, sourceMappings source⟩
    | .ok scheduled _ =>
      let mappings := scheduledMappings source scheduled
      match prepareEvalPlan scheduled (InputSignature.ofDenseInputs inputs.env) with
      | .error error => .preparation ⟨error, mappings⟩
      | .ok plan =>
        match runPreparedDense plan inputs.env with
        | .error error => .runtime ⟨error, mappings⟩
        | .ok report => .observed (observeBindings source.admitted report) mappings

def runLegacy (source : NativeSource) : LegacyOutcome :=
  legacyWithInputs source (availableInputs source)

def runChecked (source : NativeSource) : CheckedOutcome :=
  checkedWithInputs source (availableInputs source)

structure NativeRun where
  source : NativeSource
  identity : Except IdentityRefusal (List AxisSpec)
  shared : Except Unsupported SharedFragment
  inputs : Except Unsupported (NativeInputs source.admitted)
  legacy : LegacyOutcome
  checked : CheckedOutcome

/-- Structural shared-profile eligibility is metadata, not a gate on observing actual
backend failures or known overwrite behavior. Neither leg falls back to the other. -/
def runNative (snapshot : SourceSnapshot) : Except SourceDiagnostic NativeRun :=
  match h : admitSource snapshot with
  | .error error => .error error
  | .ok admitted =>
    let source : NativeSource := ⟨snapshot, admitted, h⟩
    let identity := checkIdentity source
    let inputs := prepareNativeInputs admitted
    let available := do
      let _ ← identity.mapError NativeUnavailable.identity
      inputs.mapError NativeUnavailable.input
    .ok ⟨source, identity, checkStructure admitted, inputs,
      legacyWithInputs source available, checkedWithInputs source available⟩

end LeanNCD.Semantics.Source.NativeLegs

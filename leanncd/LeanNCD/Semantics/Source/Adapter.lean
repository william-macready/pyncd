import LeanNCD.Semantics.Source.Context
import LeanNCD.DSL.Pipeline.Structural
import LeanNCD.Semantics.RationalReference

namespace LeanNCD.Semantics.Source

inductive SourceSide
  | program | declaration | input | output | read
  deriving DecidableEq, Repr

structure SourceOrigin where
  side : SourceSide := .program
  declaration : Option Nat := none
  statement : Option Nat := none
  term : Option Nat := none
  factor : Option Nat := none
  slot : Option Nat := none
  deriving DecidableEq, Repr

inductive SourceStage
  | resolution | declarations | signatures | inputs | statement | output | read | support
  deriving DecidableEq, Repr

inductive TensorRole
  | input | defined | output
  deriving DecidableEq, Repr

inductive UnsupportedSource
  | iteration | predicate | complex
  | scatter | recurMorphism | marked | scanSlot | affine
  | nonSum | nonIdentity | iverson | unary
  deriving DecidableEq, Repr

inductive SourceCause
  | resolution (error : CompileError)
  | unsupported (form : UnsupportedSource)
  | duplicateAxis (uid : UID)
  | duplicateTensor (name : String)
  | duplicateSpec (declaration : Nat)
  | duplicateInput (declaration : Nat)
  | missingDomain (uid : UID)
  | unbound (uid : UID)
  | axisKind (uid : UID) (actual : AxisKind)
  | undeclaredTensor (name : String)
  | missingSpec (declaration : Nat)
  | unexpectedSpec (declaration : Nat)
  | missingInput (declaration : Nat)
  | unexpectedInput (declaration : Nat)
  | role (expected actual : TensorRole)
  | shape (expected actual : List Nat)
  | length (expected actual : Nat)
  | domain (uid : UID) (expected actual : Nat)
  | rank (expected actual : Nat)
  | context (error : Diagnostic)
  deriving Repr

structure SourceDiagnostic where
  stage : SourceStage
  cause : SourceCause
  origin : SourceOrigin
  deriving Repr

def sourceError (stage : SourceStage) (origin : SourceOrigin) (cause : SourceCause) :
    SourceDiagnostic := ⟨stage, cause, origin⟩

structure TensorSpec where
  declaration : Nat
  role : TensorRole
  shape : List Nat
  deriving Repr

structure InputBinding where
  declaration : Nat
  shape : List Nat
  values : List ℚ
  deriving Repr

structure SourceSnapshot where
  resolved : ResolvedProgram
  specs : List TensorSpec
  inputs : List InputBinding

private def tensorName : Decl → Option String
  | .tensor name _ | .typedTensor _ name _ | .predicate name _
    | .linear name _ _ | .typedLinear _ name _ _ => some name
  | .axis .. | .iter .. => none

private def resolutionOrigin (raw : TLProgram) : CompileError → SourceOrigin
  | .duplicateTensorDecl name =>
    { side := .declaration, declaration :=
      ((raw.decls.zipIdx.filter (fun (d, _) => tensorName d == some name))[1]?).map Prod.snd }
  | .unsupportedElementType name spelling =>
    { side := .declaration, declaration :=
      (raw.decls.zipIdx.find? (fun (d, _) =>
        d.name == name && d.elementType?.any (fun ty => ty.spelling == spelling))).map Prod.snd }
  | _ => {}

/-- Raw name binding is performed exactly once, by the production resolution seam. -/
def resolveSource (raw : TLProgram) (specs : List TensorSpec) (inputs : List InputBinding) :
    Except SourceDiagnostic SourceSnapshot :=
  match (do
    let labeled ← assignUIDs raw
    resolveDecls labeled : FreshM ResolvedProgram).run 0 with
  | .ok resolved _ => .ok ⟨resolved, specs, inputs⟩
  | .error e _ => .error (sourceError .resolution (resolutionOrigin raw e) (.resolution e))

structure TensorEntry where
  declaration : Nat
  name : String
  elementType : TensorElementType
  role : TensorRole
  axes : Shape
  deriving Repr

structure TensorTable where
  entries : List TensorEntry

def TensorTable.declarations (table : TensorTable) : Declarations Unit where
  Tensor := Fin table.entries.length
  uid := Fin.val
  unique := Fin.val_injective
  signature := fun t => ⟨(), (table.entries.get t).axes⟩

def TensorTable.find (table : TensorTable) (name : String) :
    Option table.declarations.Tensor :=
  (List.finRange table.entries.length).find? (fun i => (table.entries.get i).name == name)

def TensorTable.entry (table : TensorTable) (t : table.declarations.Tensor) : TensorEntry :=
  table.entries.get t

structure InputBuffer (axes : Shape) where
  values : List ℚ
  length : values.length = (canonicalLayout axes).count

def InputBuffer.value (buffer : InputBuffer axes) (p : Coord axes) : ℚ :=
  buffer.values.get ⟨((canonicalLayout axes).enumerate.symm p).val, by
    rw [buffer.length]
    exact ((canonicalLayout axes).enumerate.symm p).isLt⟩

structure CheckedInputs (table : TensorTable) where
  buffers : (t : table.declarations.Tensor) →
    (table.entry t).role = .input → InputBuffer (table.entry t).axes

structure AdaptedSource where
  context : Context
  table : TensorTable
  inputs : CheckedInputs table
  statements : List (Nat × Stmt)

private def axisOrigin (i : Nat) : SourceOrigin :=
  { side := .declaration, declaration := some i }

private def checkAxes (decls : List Decl) : Except SourceDiagnostic Context := do
  let mut axes : Shape := []
  for (i, d) in decls.zipIdx |>.map (fun (d, i) => (i, d)) do
    let origin := axisOrigin i
    match d with
    | .axis a size =>
      if a.uid ∈ axes.map Axis.uid then
        throw (sourceError .declarations origin (.duplicateAxis a.uid))
      match size with
      | none => throw (sourceError .declarations origin (.missingDomain a.uid))
      | some n => axes := axes ++ [⟨a.uid, n⟩]
    | .iter _ _ => throw (sourceError .declarations origin (.unsupported .iteration))
    | .tensor .. | .typedTensor .. | .predicate .. | .linear .. | .typedLinear .. => pure ()
  (checkContext axes).mapError (fun e => sourceError .declarations {} (.context e))
    |>.map Subtype.val

def sourceAxis (c : Context) (stage : SourceStage) (origin : SourceOrigin)
    (a : AxisSpec) : Except SourceDiagnostic Axis := do
  match c.axes.find? (fun b => b.uid == a.uid) with
  | none => throw (sourceError stage origin (.unbound a.uid))
  | some b => pure b

private def tensorDecl (origin : SourceOrigin) :
    Decl → Except SourceDiagnostic (Option (String × TensorElementType × List AxisSpec))
  | .axis .. => .ok none
  | .iter .. => .error (sourceError .declarations origin (.unsupported .iteration))
  | .tensor name axes | .linear name axes _ => .ok (some (name, .f32, axes))
  | .typedTensor ty name axes | .typedLinear ty name axes _ =>
    match ty with
    | .f32 | .f64 => .ok (some (name, ty, axes))
    | .complex64 | .complex128 =>
      .error (sourceError .declarations origin (.unsupported .complex))
  | .predicate .. => .error (sourceError .declarations origin (.unsupported .predicate))

private def checkTable (c : Context) (decls : List Decl) (specs : List TensorSpec) :
    Except SourceDiagnostic TensorTable := do
  let mut seen : List Nat := []
  for spec in specs do
    let origin := axisOrigin spec.declaration
    if spec.declaration ∈ seen then
      throw (sourceError .signatures origin (.duplicateSpec spec.declaration))
    seen := seen ++ [spec.declaration]
  let mut entries : List TensorEntry := []
  for (d, i) in decls.zipIdx do
    let origin := axisOrigin i
    match ← tensorDecl origin d with
    | none => pure ()
    | some (name, ty, axes) =>
      if entries.any (fun t => t.name == name) then
        throw (sourceError .declarations origin (.duplicateTensor name))
      let mut shape : Shape := []
      for (a, j) in axes.zipIdx do
        shape := shape ++ [← sourceAxis c .declarations { origin with slot := some j } a]
      let spec ← match specs.find? (fun s => s.declaration == i) with
        | none => throw (sourceError .signatures origin (.missingSpec i))
        | some s => pure s
      if shape.map Axis.extent != spec.shape then
        throw (sourceError .signatures origin (.shape (shape.map Axis.extent) spec.shape))
      entries := entries ++ [⟨i, name, ty, spec.role, shape⟩]
  for spec in specs do
    unless entries.any (fun t => t.declaration == spec.declaration) do
      throw (sourceError .signatures (axisOrigin spec.declaration)
        (.unexpectedSpec spec.declaration))
  pure ⟨entries⟩

private def inputBuffer (entry : TensorEntry) (bindings : List InputBinding) :
    Except SourceDiagnostic (InputBuffer entry.axes) := do
  let origin : SourceOrigin := { side := .input, declaration := some entry.declaration }
  let binding ← match bindings.find? (fun b => b.declaration == entry.declaration) with
    | none => throw (sourceError .inputs origin (.missingInput entry.declaration))
    | some b => pure b
  let expected := entry.axes.map Axis.extent
  if expected != binding.shape then
    throw (sourceError .inputs origin (.shape expected binding.shape))
  if hl : binding.values.length = (canonicalLayout entry.axes).count then
    pure ⟨binding.values, hl⟩
  else
    throw (sourceError .inputs origin
      (.length (canonicalLayout entry.axes).count binding.values.length))

private def inputBuffers (bindings : List InputBinding) :
    (entries : List TensorEntry) →
    Except SourceDiagnostic ((t : Fin entries.length) →
      (entries.get t).role = .input → InputBuffer (entries.get t).axes)
  | [] => .ok (fun t => nomatch t)
  | entry :: entries => do
    let head ← if h : entry.role = .input then do
      let buffer ← inputBuffer entry bindings
      pure (fun (_ : entry.role = .input) => buffer)
    else
      pure (fun (hi : entry.role = .input) => False.elim (h hi))
    let rest ← inputBuffers bindings entries
    pure (Fin.cases head rest)

private def checkInputs (table : TensorTable) (bindings : List InputBinding) :
    Except SourceDiagnostic (CheckedInputs table) := do
  let mut seen : List Nat := []
  for binding in bindings do
    let origin : SourceOrigin := { side := .input, declaration := some binding.declaration }
    if binding.declaration ∈ seen then
      throw (sourceError .inputs origin (.duplicateInput binding.declaration))
    seen := seen ++ [binding.declaration]
    match table.entries.find? (fun t => t.declaration == binding.declaration) with
    | none => throw (sourceError .inputs origin (.unexpectedInput binding.declaration))
    | some t =>
      if t.role != .input then throw (sourceError .inputs origin (.role .input t.role))
  let buffers ← inputBuffers bindings table.entries
  pure ⟨buffers⟩

/-- Neither the cached environment nor external-name classification determines semantic roles. -/
def adaptSource (snapshot : SourceSnapshot) : Except SourceDiagnostic AdaptedSource := do
  let context ← checkAxes snapshot.resolved.decls
  let table ← checkTable context snapshot.resolved.decls snapshot.specs
  let inputs ← checkInputs table snapshot.inputs
  pure ⟨context, table, inputs,
    snapshot.resolved.stmts.zipIdx |>.map (fun (s, i) => (i, s))⟩

end LeanNCD.Semantics.Source

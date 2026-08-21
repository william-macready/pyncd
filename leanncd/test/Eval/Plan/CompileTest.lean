import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Compile

/-!
# Wave C C4 capability preflight tests

One baseline accepted program (`Y[i] := X[i]`) plus rejected cases for every `CapabilityError`
category (11 total): 3 cases for `unsupportedLhsSlot` (`freeNorm`/`iterAt`/`iterNext`), 2 for
`unsupportedNonlin` (pointwise/axiswise), 2 for `unsupportedAgg` (max/min), and one each for the
remaining categories;
the two structurally-unreachable categories (`unsupportedDtype`, `dynamicShape`) are exercised
directly on the constructor rather than through `capabilityPreflight`. Also covers `prepareEvalPlan`
end-to-end on accepted programs — an identity copy, a zero-coefficient contraction, and a
repeated-assignment (no-dedup) case — every `PlanCompileCause` variant reached through the real
pipeline (`inputSignature`, `capability`, `shape`), and non-empty preparation warnings surviving a
later `shape` failure unchanged.
-/

namespace LeanNCD.Eval.Plan.CompileTest
open LeanNCD LeanNCD.Eval.Plan
open Std

def isOk : Except CapabilityError Unit → Bool
  | .ok _ => true | .error _ => false

def errOf : Except CapabilityError Unit → Option CapabilityError
  | .ok _ => none | .error e => some e

-- accepted: an ordinary in-fragment scheduled program (`Y[i] := X[i]`)
def acceptedSched : ScheduledProgram :=
  { decls := [.tensor "X" [], .tensor "Y" []]
  , stmts := [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
      { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })]
  , env := {}
  , extNames := {}
  , explicitSizes := {} }

#guard isOk (capabilityPreflight acceptedSched)

-- noAdvancingAxis: a `.scan` ScanStmt declaring no advancing axis. (Wave C rejected EVERY `.scan`
-- here with `scanNode`; F4 admits well-formed ones, so this fixture now pins the empty-axis
-- rejection specifically — see `Eval.Plan.ScanCompileTest` for the admitted cases.)
#guard errOf (capabilityPreflight
    { acceptedSched with stmts := [.scan "s" [] [] [] false] })
  == some (.noAdvancingAxis "s")

-- recurrenceOrCallback via `.scanPre` (checked directly on the sub-function, not through a whole
-- program, to keep this fixture minimal — `capabilityPreflight` is already exercised end-to-end
-- above). Reuses the constructor `Stmt.recurMorphism` already gets: a `.scanPre`'s payload IS a
-- pre-built step morphism (proposal §5.2 / plan §4.1), not a distinct capability.
#guard errOf (checkScanStmt (.scanPre "s" ⟨"l", 0, .nat⟩ default)) == some (.recurrenceOrCallback "s")

-- `scanNode` has no producer left in `Compile.lean` (F4 replaced both of its throw sites), but the
-- constructor is retained on `CapabilityError` — deleting a shipped closed-family constructor is
-- itself a semantic version change. Exercised directly, same pattern as `unsupportedDtype` below.
#guard (CapabilityError.scanNode "retained") == CapabilityError.scanNode "retained"

-- scatterOrAffineLhs: a scatter statement
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.scatter "Out" [] { body := { terms := [] }, nonlin := .identity } {})] })
  == some (.scatterOrAffineLhs "Out")

-- scatterOrAffineLhs: an affine LHS slot on an ordinary assign
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.affine (.axis ⟨"i", 0, .nat⟩)]
          { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })] })
  == some (.scatterOrAffineLhs "Y: affine LHS slot")

-- unsupportedLhsSlot: freeNorm
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.freeNorm ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })] })
  == some (.unsupportedLhsSlot "Y: freeNorm i")

-- unsupportedLhsSlot: iterAt
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.iterAt ⟨"i", 0, .nat⟩ 0]
          { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })] })
  == some (.unsupportedLhsSlot "Y: iterAt i")

-- unsupportedLhsSlot: iterNext
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.iterNext ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })] })
  == some (.unsupportedLhsSlot "Y: iterNext i")

-- unsupportedNonlin: pointwise
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .pointwise .relu })] })
  == some (.unsupportedNonlin "Y: pointwise nonlinearity")

-- unsupportedNonlin: axiswise
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }
          , nonlin := .axiswise .softmax none })] })
  == some (.unsupportedNonlin "Y: axiswise nonlinearity")

-- maskOrPredicate: an iverson factor
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors :=
              [.iverson (.rel .eq (.embed (.const 0)) (.embed (.const 0)))] }] }
          , nonlin := .identity })] })
  == some (.maskOrPredicate "Y: iverson factor")

-- unaryFactor
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.unaryFn .log "X" []] }] }, nonlin := .identity })] })
  == some (.unaryFactor "Y: unary function on X")

-- unsupportedAgg: max
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }
          , nonlin := .identity, agg := .max })] })
  == some (.unsupportedAgg "Y: max aggregation")

-- unsupportedAgg: min
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }
          , nonlin := .identity, agg := .min })] })
  == some (.unsupportedAgg "Y: min aggregation")

-- booleanOutput: a predicate decl
#guard errOf (capabilityPreflight { acceptedSched with decls := [.predicate "P" []] })
  == some (.booleanOutput "P")

-- recurrenceOrCallback: a recurMorphism stmt
#guard errOf (capabilityPreflight
    { acceptedSched with stmts := [.plain (.recurMorphism "R" ⟨"l", 0, .nat⟩ default)] })
  == some (.recurrenceOrCallback "R")

-- unsupportedDtype: structurally unreachable via `capabilityPreflight` — `Decl` (`DSL/Ast.lean`)
-- carries no dtype field on any constructor (`.tensor`/`.linear`/`.predicate` are name+axes only;
-- dtype is an `InputSignature`/backend concept a LATER C4 step resolves, not a source declaration),
-- so nothing in this file's checkers can ever construct this value. Exercised directly, same
-- pattern as `dynamicShape` below.
#guard (CapabilityError.unsupportedDtype "unreachable") == CapabilityError.unsupportedDtype "unreachable"

-- dynamicShape: structurally unreachable via `capabilityPreflight` — `IdxExpr` (`DSL/Ast.lean`) has
-- exactly five constructors (`axis`, `const`, `scale`, `shift`, `affine`), all integer-affine over
-- declared `AxisSpec`s; there is no value-dependent/runtime-shape construct anywhere in the AST for
-- this checker to reject. Exercised directly, same pattern as `unsupportedDtype` above.
#guard (CapabilityError.dynamicShape "unreachable") == CapabilityError.dynamicShape "unreachable"

-- Example 1: identity copy `Y[i] := X[i]`, axis i : ℕ = 3.
def axI1 : AxisSpec := { name := "i", uid := 1, kind := .nat }
def identitySched : ScheduledProgram :=
  { decls := [.axis axI1 (some 3)]
  , stmts := [.plain (.assign "Y" [.free axI1]
      { body := { terms := [{ factors := [.read "X" [.axis axI1]] }] }, nonlin := .identity })]
  , env := {}, extNames := insert "X" (∅ : Finset String)
  , explicitSizes := (({} : HashMap UID Nat).insert axI1.uid 3) }
def identityInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" (⟨[3], #[10.0, 20.0, 30.0]⟩ : DenseTensor)
def identitySig : InputSignature := InputSignature.ofDenseInputs identityInputs
#guard (prepareEvalPlan identitySched identitySig).toOption.isSome

-- Example 2: contraction `Y[i] := A[i] · B[j]` contracted over j — ALSO the zero-coefficient
-- contracted-axis case (A[i]'s row over basis [i,j] densifies to a zero column for j — proposal
-- §7.4: "do not infer reduction axes from matrix coefficients," confirmed here: the zero column
-- does not cause j to be dropped from the basis).
def axI2 : AxisSpec := { name := "i", uid := 1, kind := .nat }
def axJ2 : AxisSpec := { name := "j", uid := 2, kind := .nat }
def contractSched : ScheduledProgram :=
  { decls := [.axis axI2 (some 2), .axis axJ2 (some 3)]
  , stmts := [.plain (.assign "Y" [.free axI2]
      { body := { terms := [{ factors := [.read "A" [.axis axI2], .read "B" [.axis axJ2]] }] }
      , nonlin := .identity })]
  , env := {}, extNames := insert "A" (insert "B" (∅ : Finset String))
  , explicitSizes := ((({} : HashMap UID Nat).insert axI2.uid 2).insert axJ2.uid 3) }
def contractInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" (⟨[2], #[10.0, 100.0]⟩ : DenseTensor)).insert
    "B" (⟨[3], #[1.0, 2.0, 3.0]⟩ : DenseTensor)
def contractSig : InputSignature := InputSignature.ofDenseInputs contractInputs
#guard (prepareEvalPlan contractSched contractSig).toOption.isSome

def contractPrepared : Option PreparedPlan := (prepareEvalPlan contractSched contractSig).toOption

/-- `PlanStep` field-access helper: every fixture in this file is scan-free by construction
    (`prepareEvalPlan`'s Step D only ever emits `.assign` steps, wrapped via `stepsAcc.map .assign`),
    so the `.scan` arm should never actually be hit — made explicit here (fails the assertion, since
    `AssignPlan` derives `Inhabited`) rather than silently defaulting or re-projecting a field that no
    longer exists directly on `PlanStep`. Same reasoning covers `.pointwise`/`.axiswise` (Thread 4):
    `prepareEvalPlan` does not compile to those constructors yet, so they are just as unreachable
    here as `.scan`. -/
def assignStep : PlanStep → AssignPlan
  | .assign a => a
  | .scan _ => panic! "unreachable: CompileTest fixtures are scan-free by construction"
  | .pointwise _ | .axiswise _ =>
      panic! "unreachable: CompileTest fixtures never compile to a nonlinearity step"

#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.iterationShape) == some #[2, 3]
#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.outputPos) == some #[0]
#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.reductionPos) == some #[1]
#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.contextPos) == some #[]
#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).contextShape) == some #[]
#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.factors[0]!.map.coeffs) ==
  some #[#[1, 0]]   -- A[i]: zero coefficient in the j (contracted) column — still counted
#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.factors[1]!.map.coeffs) ==
  some #[#[0, 1]]   -- B[j]

-- Example 2b: multiple factors and ORDERED reductions `Y[i] := A[i,j]·B[j,k]·C[k]`, contracting
-- over TWO axes (j then k, in first-encountered order via `termAxisUIDs`) — Example 2 above never
-- exercises more than one contracted axis, and neither does `PropertyOracle.enumPrograms` (its
-- generator caps every term at 2 factors and never puts more than one contracted axis `j` into
-- play — confirmed by reading `Gen.lean` directly), so this is the only coverage anywhere in the
-- suite for reduction ORDER with more than one axis, and the only multi-dimensional-read (`A[i,j]`,
-- two idx-expr rows in one factor) coverage in this file.
def axI2b : AxisSpec := { name := "i", uid := 1, kind := .nat }
def axJ2b : AxisSpec := { name := "j", uid := 2, kind := .nat }
def axK2b : AxisSpec := { name := "k", uid := 3, kind := .nat }
def multiReductionSched : ScheduledProgram :=
  { decls := [.axis axI2b (some 2), .axis axJ2b (some 2), .axis axK2b (some 2)]
  , stmts := [.plain (.assign "Y" [.free axI2b]
      { body := { terms := [{ factors :=
          [ .read "A" [.axis axI2b, .axis axJ2b]
          , .read "B" [.axis axJ2b, .axis axK2b]
          , .read "C" [.axis axK2b] ] }] }
      , nonlin := .identity })]
  , env := {}, extNames := insert "A" (insert "B" (insert "C" (∅ : Finset String)))
  , explicitSizes :=
      (((({} : HashMap UID Nat).insert axI2b.uid 2).insert axJ2b.uid 2).insert axK2b.uid 2) }
def multiReductionInputs : HashMap String DenseTensor :=
  ((({} : HashMap String DenseTensor).insert "A" ⟨[2, 2], #[1.0, 2.0, 3.0, 4.0]⟩).insert
    "B" ⟨[2, 2], #[1.0, 0.0, 0.0, 1.0]⟩).insert "C" ⟨[2], #[1.0, 1.0]⟩
def multiReductionSig : InputSignature := InputSignature.ofDenseInputs multiReductionInputs
#guard (prepareEvalPlan multiReductionSched multiReductionSig).toOption.isSome

def multiReductionPrepared : Option PreparedPlan :=
  (prepareEvalPlan multiReductionSched multiReductionSig).toOption

#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.iterationShape) == some #[2, 2, 2]
#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.outputPos) == some #[0]
#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.reductionPos) == some #[1, 2]  -- j, then k
#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.contextPos) == some #[]
-- A[i,j]: one row per read dimension, over basis [i, j, k].
#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.factors[0]!.map.coeffs) ==
  some #[#[1, 0, 0], #[0, 1, 0]]
-- B[j,k]
#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.factors[1]!.map.coeffs) ==
  some #[#[0, 1, 0], #[0, 0, 1]]
-- C[k]
#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.factors[2]!.map.coeffs) ==
  some #[#[0, 0, 1]]

-- Example 3: repeated assignment `Y[i]:=A[i]; Y[i]:=B[i]; Z[i]:=Y[i]`, axis i : ℕ = 2.
def axI3 : AxisSpec := { name := "i", uid := 1, kind := .nat }
def repeatSched : ScheduledProgram :=
  { decls := [.axis axI3 (some 2)]
  , stmts :=
      [ .plain (.assign "Y" [.free axI3]
          { body := { terms := [{ factors := [.read "A" [.axis axI3]] }] }, nonlin := .identity })
      , .plain (.assign "Y" [.free axI3]
          { body := { terms := [{ factors := [.read "B" [.axis axI3]] }] }, nonlin := .identity })
      , .plain (.assign "Z" [.free axI3]
          { body := { terms := [{ factors := [.read "Y" [.axis axI3]] }] }, nonlin := .identity }) ]
  , env := {}, extNames := insert "A" (insert "B" (∅ : Finset String))
  , explicitSizes := (({} : HashMap UID Nat).insert axI3.uid 2) }
def repeatInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" (⟨[2], #[1.0, 2.0]⟩ : DenseTensor)).insert
    "B" (⟨[2], #[100.0, 200.0]⟩ : DenseTensor)
def repeatSig : InputSignature := InputSignature.ofDenseInputs repeatInputs
#guard (prepareEvalPlan repeatSched repeatSig).toOption.isSome

def repeatPrepared : Option PreparedPlan := (prepareEvalPlan repeatSched repeatSig).toOption
-- NOT deduplicated: two entries for "Y" (one per write), then "Z" — matches §5.4's own text.
#guard repeatPrepared.map (fun p => p.bindings.materializedNames.map (·.name)) == some #["Y", "Y", "Z"]
def repeatYSlots : Option (Array TensorSlot) :=
  repeatPrepared.map (fun p => (p.bindings.materializedNames.filter (·.name == "Y")).map (·.slot))
#guard repeatYSlots.map (fun ss => ss[0]! == ss[1]!) == some false   -- two DISTINCT "Y" slots

-- Deterministic slot assignment: same input, same structural output.
-- `RequiredBindings` has no derived `BEq` (same established precedent as `PreparedPlan` itself, per
-- `Prepared.lean`'s own doc comment: private-constructor types compare through field projections,
-- not whole-struct equality), so compare through `.bindings` instead.
#guard ((prepareEvalPlan contractSched contractSig).toOption.map (·.bindings.requiredInputs.bindings)) ==
       ((prepareEvalPlan contractSched contractSig).toOption.map (·.bindings.requiredInputs.bindings))
#guard ((prepareEvalPlan contractSched contractSig).toOption.map (·.plan.raw)) ==
       ((prepareEvalPlan contractSched contractSig).toOption.map (·.plan.raw))

-- Step A/B wiring: failures propagate through prepareEvalPlan with the right cause.
def causeOf (r : Except PlanCompileFailure PreparedPlan) : Option PlanCompileFailure :=
  match r with | .ok _ => none | .error e => some e
#guard causeOf (prepareEvalPlan identitySched (InputSignature.mk ({} : HashMap String TensorSignature))) ==
  some { cause := .inputSignature (.missingSignature "X"), warnings := [] }
def badDtypeSig : InputSignature :=
  InputSignature.mk (({} : HashMap String TensorSignature).insert "X" { shape := #[3], dtype := .bool })
#guard causeOf (prepareEvalPlan identitySched badDtypeSig) ==
  some { cause := .inputSignature (.dtypeNotAdmitted "X" .bool), warnings := [] }

-- `prepareEvalPlan`'s OWN capability-rejection path: Step A runs `capabilityPreflight` before
-- shape inference, so an axis-less `.scan` statement is rejected with a `.capability`-tagged
-- `PlanCompileFailure` and `warnings := []` (Step A fails before any warnings could accrue) — the
-- same schedule/error pair `capabilityPreflight`'s own `noAdvancingAxis` guard above uses.
#guard causeOf (prepareEvalPlan { acceptedSched with stmts := [.scan "s" [] [] [] false] } identitySig) ==
  some { cause := .capability (.noAdvancingAxis "s"), warnings := [] }

-- `PlanCompileCause.shape` through `prepareEvalPlan`: axis `i` never appears in any read, so shape
-- inference succeeds vacuously (no read positions to fail on) but leaves `i` unsized;
-- `resolveSizeOrFail` then fails on it while resolving the statement's output shape.
def axUnsized : AxisSpec := { name := "i", uid := 1, kind := .nat }

def unsizedSched : ScheduledProgram :=
  { decls := [.axis axUnsized none]
  , stmts := [.plain (.assign "Y" [.free axUnsized]
      { body := { terms := [{ factors := [] }] }, nonlin := .identity })]
  , env := {}, extNames := (∅ : Finset String)
  , explicitSizes := {} }

def emptySig : InputSignature := InputSignature.mk ({} : HashMap String TensorSignature)

#guard causeOf (prepareEvalPlan unsizedSched emptySig) ==
  some { cause := .shape (.unsizedAxis 1 (.assignOutput "Y")), warnings := [] }

/-- Manual renderer for `PlanCompileCause` (used only for test-failure messages): the type
    deliberately has no `Repr`/`ToString` (`ShapeError` — nested via `.shape` — has neither), so a
    diagnosable message has to dispatch per-constructor to whichever rendering each nested cause
    DOES support (`Repr` for `CapabilityError`/`InputSignatureError`/`PlanError`, `ToString` for
    `ShapeError`). -/
private def renderCompileCause : PlanCompileCause → String
  | .inputSignature c => s!"inputSignature: {repr c}"
  | .capability c     => s!"capability: {repr c}"
  | .shape c          => s!"shape: {c}"
  | .scan c            => s!"scan: {repr c}"
  | .invalidPlan c     => s!"invalidPlan: {repr c}"
  | .bindings c        => s!"bindings: {repr c}"

-- non-empty `warnings` surviving into a real `prepareEvalPlan` failure: a second statement's
-- unsized-axis failure must not touch or clear warnings the first statement already accumulated.
private def warnProg : TLProgram := tlprog!{
  axis i : ℕ = 4
  axis j : ℕ = 3
  Y[i, j] := X[2 * i + j]
}
private def warnInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[6], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]⟩
def axUnsized2 : AxisSpec := { name := "k", uid := 1000, kind := .nat }

-- statement 1 alone, for cross-check that the combined program's warnings didn't change.
def warnBaselinePrepared : Option PreparedPlan := Id.run do
  match warnProg.compileToScheduled.run 0 with
  | .error _ _ => none
  | .ok sched _ => (prepareEvalPlan sched (InputSignature.ofDenseInputs warnInputs)).toOption

run_cmd do
  match warnProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"warnProg compile failed: {repr e}"
  | .ok sched _ =>
    let combined : ScheduledProgram :=
      { sched with
          decls := sched.decls ++ [.axis axUnsized2 none]
          stmts := sched.stmts ++ [.plain (.assign "Z" [.free axUnsized2]
            { body := { terms := [{ factors := [] }] }, nonlin := .identity })] }
    match causeOf (prepareEvalPlan combined (InputSignature.ofDenseInputs warnInputs)) with
    | none => throwError "expected prepareEvalPlan to fail on the combined program"
    | some f =>
        unless !f.warnings.isEmpty do
          throwError "expected non-empty warnings to survive into the Step D failure"
        unless f.cause == .shape (.unsizedAxis 1000 (.assignOutput "Z")) do
          throwError s!"wrong cause: {renderCompileCause f.cause}"
        match warnBaselinePrepared with
        | none => throwError "unreachable: baseline already confirmed some above"
        | some baseline =>
            unless f.warnings == baseline.warnings do
              throwError s!"combined warnings diverged from statement-1-alone: {f.warnings} vs {baseline.warnings}"

end LeanNCD.Eval.Plan.CompileTest

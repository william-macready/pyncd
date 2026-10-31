import Eval.Plan.B5cSingleBoxTest

/-!
# Scatter geometry slice A: multi-axis `Y[a+b]` (programmatic forms)

Hand-built `TLProgram`s (the surface cannot say a multi-axis slot; slice B adds it) with an explicit
`.scatter` statement, run through the real pipeline (`compileToScheduled`, `prepareEvalPlan`,
`runPreparedDense`/`runPreparedDense32`, `evalScheduled`) by the B5 harness (`B5NativeTest`).

Inputs throughout: `A[a] = [1,2,3,4]` (`|a| = 4`), `B[b] = [1,10,100]` (`|b| = 3`). The anti-diagonal
sums of `A[a]*B[b]` are the polynomial product `[1, 12, 123, 234, 340, 400]`, whose exact reach is
`0..5`, so the destination extent is 6 (M1; the legacy sum rule gave 7 and a trailing `0`).
-/

namespace LeanNCD.Eval.Plan.ScatterGeometryTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.Eval.Plan.B5NativeTest Std

private def a : AxisSpec := ⟨"a", 90, .nat⟩
private def b : AxisSpec := ⟨"b", 91, .nat⟩
private def k : AxisSpec := ⟨"k", 92, .nat⟩

/-- Donor: `B5BoundaryTest.twoAxes` reduced to ONE scatter writer. `S` is declared over the
    unpinned axis `k`, so its shape is derived from the write form (no box). -/
def convOf (slot : LHSSlot) (agg : AggOp := .sum) : TLProgram :=
  { decls := [.axis a (some 4), .axis b (some 3), .axis k none,
      .typedTensor .f32 "A" [a], .typedTensor .f32 "B" [b], .typedTensor .f32 "S" [k]]
    stmts := [.scatter "S" [slot]
      { body := { terms := [{ factors := [.read "A" [.axis a], .read "B" [.axis b]] }] }
        nonlin := .identity, agg := agg }] }

def sumSlot : LHSSlot := .affine (.affine 0 [(1, a), (1, b)])
def wideSlot : LHSSlot := .affine (.affine 0 [(1, a), (4, b)])

def conv : TLProgram := convOf sumSlot
def convWide : TLProgram := convOf wideSlot

def convIn64 : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "A" ⟨[4], #[1, 2, 3, 4]⟩ |>.insert "B" ⟨[3], #[1, 10, 100]⟩
def convIn32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "A" ⟨[4], #[1, 2, 3, 4]⟩ |>.insert "B" ⟨[3], #[1, 10, 100]⟩

/-- The reference evaluator's published shape of `S`. -/
def refShapeOf (p : TLProgram) : Option (List Nat) :=
  (ref64 p convIn64).bind fun e => e["S"]?.map (·.shape)

/-- The checked backend's refusal cause at preparation, or `none` if it accepted. -/
def prepCause (p : TLProgram) : Option PlanCompileCause :=
  (scheduled (as64 p)).bind fun s =>
    match prepareEvalPlan s (InputSignature.ofDenseInputs convIn64) with
    | .error f => some f.cause
    | .ok _ => none

-- T1 (M1): the reference publishes the EXACT REACH. `a+b`: 0..5, extent 6 (the legacy rule: 7);
-- `a+4b`: 0..11, extent 12 (legacy 16).
#guard refShapeOf conv == some [6]
#guard refShapeOf convWide == some [12]
-- ... and the values are the polynomial product (no trailing zero cell).
#guard ((ref64 conv convIn64).bind fun e => e["S"]?.map (·.data)) ==
  some #[1, 12, 123, 234, 340, 400]
-- The checked leg still REFUSES multi-axis geometry at this task (T2 lifts it), by its own
-- capability constructor, not by a shape or range error.
#guard prepCause conv == some (.capability (.multiAxisScatterLhs "S: affine LHS slot"))
#guard prepCause convWide == some (.capability (.multiAxisScatterLhs "S: affine LHS slot"))

end LeanNCD.Eval.Plan.ScatterGeometryTest

import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Compile
import LeanNCD.Eval.Plan.Adapter   -- `runPreparedDense`: every fixture below executes its own plan
import Eval.ExplicitF64

/-!
# S-A Task 5 — source reachability of `PlanStep.scatter`

The connectivity proof for the scatter feature. Tasks 1-4 built the IR node, the checker, the dense
worker, and the `checkPlan`/`runDensePlan` wiring, but **no source program could reach any of it**,
and no compile error said so — `Compile.lean` built clean through every round of the IR node's own
perturbation measurement. A green build is therefore not evidence that this feature is reachable;
these fixtures are.

Every fixture here starts from real `tlprog!{…}` SURFACE SYNTAX, not a hand-built
`ScheduledProgram`: parse → `compileToScheduled` (whose `lowerArith` phase reclassifies an affine or
diagonal LHS into `Stmt.scatter`) → `prepareEvalPlan` → a real `PlanStep.scatter` → `runDensePlan`.
Each one is then checked THREE ways: the compiled plan really carries a `.scatter` step, the checked
backend's value matches the independently measured reference value, and the reference evaluator
(`evalScheduled`, which has executed affine LHS writes end to end since long before the checked
backend existed) agrees element for element. The measured values are the plan's own §2.1 table.

Capability-boundary fixtures for a scatter (a multi-axis affine LHS, a constant affine LHS, a
non-identity nonlinearity, an unimplemented collision policy) live beside their siblings in
`CompileTest.lean`; the scan-block rejections that S-A deliberately does NOT lift are in
`ScanCompileTest.lean`. This file is only about what a source program can reach.
-/

namespace LeanNCD.Eval.Plan.ScatterCompileTest
open LeanNCD LeanNCD.Eval.Plan LeanNCD.Eval.ExplicitF64
open Std

/-- A dense tensor from a shape and row-major data (the portfolio harness's `tl`, reproduced rather
    than imported so this file does not pull in LSpec for one constructor). -/
def dt (shape : List Nat) (xs : List Float) : DenseTensor := ⟨shape, xs.toArray⟩

/-- Source program → logical schedule, through the REAL compile pipeline (`assignUIDs` …
    source validation … `lowerArith` … `schedule`). Going through `compileToScheduled` rather
    than hand-writing a `ScheduledProgram` is the whole point of this file: a hand-built schedule
    could present a `Stmt.scatter` that `lowerArith` would never produce, which proves nothing about
    source reachability. The fixtures declare no tensors, so `explicitF64` declares their names
    `f64`: undeclared names are binary32 since the default flip, and the inputs here are `Float`. -/
def schedOf (p : TLProgram) : Option ScheduledProgram :=
  match p.explicitF64.compileToScheduled.run 0 with
  | .ok s _ => some s
  | .error _ _ => none

/-- Source program + concrete inputs → prepared checked plan. -/
def preparedOf (p : TLProgram) (env : HashMap String DenseTensor) : Option PreparedPlan :=
  match schedOf p with
  | none => none
  | some sched => (prepareEvalPlan sched (InputSignature.ofDenseInputs env)).toOption

/-- The `ScatterPlan` at step `i`, or `none` if that step is not a scatter. Deliberately `Option`-
    valued rather than a `panic!`-defaulting projection: "step 0 is a scatter" is precisely the
    claim these fixtures exist to make, so it must be asserted, not assumed. -/
def scatterStepAt (p : PreparedPlan) (i : Nat) : Option ScatterPlan :=
  match p.plan.raw.steps[i]? with
  | some (.scatter s) => some s
  | _ => none

/-- Does this plan contain a `PlanStep.scatter` at all? -/
def hasScatterStep (p : PreparedPlan) : Bool :=
  p.plan.raw.steps.any (fun s => match s with | .scatter _ => true | _ => false)

open Lean Elab Command in
/-- The three-way check: a source program compiles to a plan containing a real `.scatter` step, the
    checked backend executes it to `expect`, and the reference evaluator agrees with the checked
    backend element for element. The reference leg is what makes this more than a self-consistency
    check — `expect` is a measured value, and the reference has produced it since before any of this
    machinery existed. -/
def assertScatterParity (nm : String) (prog : TLProgram) (env : HashMap String DenseTensor)
    (key : String) (expect : DenseTensor) : CommandElabM Unit := do
  let sched ← match prog.explicitF64.compileToScheduled.run 0 with
    | .ok s _ => pure s
    | .error e _ => throwError s!"{nm}: source compilation failed: {repr e}"
  let prepared ← match prepareEvalPlan sched (InputSignature.ofDenseInputs env) with
    | .ok p => pure p
    | .error _ => throwError s!"{nm}: prepareEvalPlan rejected a source-compiled scatter program"
  unless hasScatterStep prepared do
    throwError s!"{nm}: the compiled plan carries no PlanStep.scatter"
  let dense ← match runPreparedDense prepared env with
    | .ok r => pure r
    | .error e => throwError s!"{nm}: checked execution failed: {repr e.cause}"
  let direct ← match LeanNCD.Eval.evalScheduled sched env with
    | .ok r => pure r
    | .error e => throwError s!"{nm}: reference execution failed: {e.error}"
  match dense.env[key]?, direct.env[key]? with
  | some d, some r =>
      unless d.shape == expect.shape && d.data == expect.data do
        throwError s!"{nm}: checked {d.shape}/{d.data.toList} ≠ measured {expect.shape}/{expect.data.toList}"
      unless r.shape == d.shape && r.data == d.data do
        throwError s!"{nm}: reference {r.shape}/{r.data.toList} disagrees with the checked plan"
  | _, _ => throwError s!"{nm}: '{key}' was not published by both backends"

/-! ## S1 — `Out[2*i] := X[i]`, the load-bearing fixture

The one whose compiled plan is inspected field by field, because every other fixture only compares
values and a value comparison cannot see a swapped axis or a wrong placement row on a rank-1 output.
-/

def upsampleProg : TLProgram := tlprog!{ Out[2*i] := X[i] }
def upsampleEnv : HashMap String DenseTensor :=
  HashMap.ofList [("X", dt [3] [1.0, 2.0, 3.0])]
def upsamplePrepared : Option PreparedPlan := preparedOf upsampleProg upsampleEnv

-- The claim the whole task exists to establish: surface syntax reaches a real `PlanStep.scatter`.
#guard upsamplePrepared.map hasScatterStep == some true

def upsampleScatter : Option ScatterPlan := upsamplePrepared.bind (scatterStepAt · 0)

-- The SOURCE iteration domain, not the destination extent — the separation `ScatterPlan` exists
-- for. `X` is `[3]`, so `i : 3`.
#guard upsampleScatter.map (·.compute.outputShape) == some #[3]
-- The DESTINATION extent, `2 · 3 = 6` by the `scale · n + offset` convention. Six, not five:
-- max-coordinate + 1 is 4 + 1 = 5, and the convention deliberately differs from it.
#guard upsampleScatter.map (·.destShape) == some #[6]
-- One placement row per destination dimension, of source-basis width: `dest = 2 · i + 0`.
#guard upsampleScatter.map (·.outCoeffs) == some #[#[2]]
#guard upsampleScatter.map (·.outBias) == some #[0]
-- The compute half contracts nothing: `scatterSourceAxes` unions the LHS axes with every RHS axis,
-- so no axis is left to reduce over and each source coordinate carries exactly one value. That is
-- the reference evaluator's own equation, and it is what makes the two legs comparable at all.
#guard upsampleScatter.map (fun s => s.compute.terms.size) == some 1
#guard upsampleScatter.map (fun s => (s.compute.terms[0]!).reductionPos) == some #[]
#guard upsampleScatter.map (fun s => (s.compute.terms[0]!).iterationShape) == some #[3]
-- The destination signature registered for the step carries the DESTINATION extent, which is what
-- `checkAssign`'s parameterised destination-shape clause is for.
#guard (upsamplePrepared.bind (fun p => p.plan.raw.tensorSigs[1]?)).map (·.shape) == some #[6]

run_cmd do
  assertScatterParity "S1 Out[2*i] := X[i]" upsampleProg upsampleEnv "Out"
    (dt [6] [1.0, 0.0, 2.0, 0.0, 3.0, 0.0])

/-! ## S2-S4 — the rest of the measured reference table -/

-- A non-zero bias on a strided row: stride-aligned extent `2 · 3 = 6`.
def shiftedProg : TLProgram := tlprog!{ Out[2*i + 1] := X[i] }
def shiftedScatter : Option ScatterPlan :=
  (preparedOf shiftedProg upsampleEnv).bind (scatterStepAt · 0)
#guard shiftedScatter.map (·.outCoeffs) == some #[#[2]]
#guard shiftedScatter.map (·.outBias) == some #[1]
#guard shiftedScatter.map (·.destShape) == some #[6]
run_cmd do
  assertScatterParity "S2 Out[2*i + 1] := X[i]" shiftedProg upsampleEnv "Out"
    (dt [6] [0.0, 1.0, 0.0, 2.0, 0.0, 3.0])

-- A pure offset (unit coefficient): extent `1 · 3 + 2 = 5`.
def offsetProg : TLProgram := tlprog!{ Out[i + 2] := X[i] }
def offsetScatter : Option ScatterPlan :=
  (preparedOf offsetProg upsampleEnv).bind (scatterStepAt · 0)
#guard offsetScatter.map (·.outCoeffs) == some #[#[1]]
#guard offsetScatter.map (·.outBias) == some #[2]
#guard offsetScatter.map (·.destShape) == some #[5]
run_cmd do
  assertScatterParity "S3 Out[i + 2] := X[i]" offsetProg upsampleEnv "Out"
    (dt [5] [0.0, 0.0, 1.0, 2.0, 3.0])

-- The DIAGONAL trigger, which carries NO `.affine` slot at all: `lowerArith` reclassifies it on a
-- repeated free axis (`slotsBecomeScatter`). Two destination dimensions, one source axis, so both
-- placement rows are the same `1 · i + 0` — the case that would survive a value comparison on a
-- rank-1 output but not on this one.
def diagProg : TLProgram := tlprog!{ Y[i, i] := V[i] }
def diagEnv : HashMap String DenseTensor :=
  HashMap.ofList [("V", dt [3] [7.0, 8.0, 9.0])]
def diagScatter : Option ScatterPlan := (preparedOf diagProg diagEnv).bind (scatterStepAt · 0)
#guard diagScatter.map (·.compute.outputShape) == some #[3]
#guard diagScatter.map (·.outCoeffs) == some #[#[1], #[1]]
#guard diagScatter.map (·.outBias) == some #[0, 0]
#guard diagScatter.map (·.destShape) == some #[3, 3]
run_cmd do
  assertScatterParity "S4 Y[i, i] := V[i]" diagProg diagEnv "Y"
    (dt [3, 3] [7.0, 0.0, 0.0, 0.0, 8.0, 0.0, 0.0, 0.0, 9.0])

/-! ## S5 — a scatter's output feeding a LATER statement

Sizing flows out of a scatter into its consumer: `Up`'s `[6]` extent is what sizes `k`. The step
sequence is `.scatter` then `.assign`, which also pins that `slotOf` publication makes a scatter's
destination visible to later statements exactly as an assignment's is. -/

def chainedProg : TLProgram := tlprog!{ Up[2*i] := X[i]
                                        Z[k] := Up[k] }
def chainedPrepared : Option PreparedPlan := preparedOf chainedProg upsampleEnv
#guard chainedPrepared.map (fun p => p.plan.raw.steps.size) == some 2
#guard (chainedPrepared.bind (scatterStepAt · 0)).map (·.destShape) == some #[6]
-- `k` sized itself from the scatter's OWN derived extent, not from any input shape.
#guard (chainedPrepared.bind (scatterStepAt · 1)).isNone
run_cmd do
  assertScatterParity "S5 Up[2*i] := X[i] ; Z[k] := Up[k]" chainedProg upsampleEnv "Z"
    (dt [6] [1.0, 0.0, 2.0, 0.0, 3.0, 0.0])

/-! ## S6 — an `.assign` step immediately PRECEDING a `.scatter` step

`rawPublicationSlots`' (`Prepared.lean`) reachability question, answered: its `.assign` lookahead
suppresses a destination slot only when the NEXT step is a `.pointwise`/`.axiswise` reading it (a
nonlinearity fusion), and publishes it otherwise through a catch-all whose reachability over a
scatter lowering was flagged open when it was written. This program reaches it — step 0 is `W`'s
`.assign`, step 1 is the `.scatter`, and the catch-all fires — and the behaviour is correct: `W` is
a separate statement's result and genuinely IS published. `runPreparedDense` proves it, because
`checkPreparedBindings` compares `rawPublicationSlots` against the emitter's own
`materializedNames` and rejects any disagreement (`publicationSlots`). -/

def assignThenScatterProg : TLProgram := tlprog!{ W[i] := X[i] · X[i]
                                                 Out[2*i] := W[i] }
def assignThenScatterPrepared : Option PreparedPlan := preparedOf assignThenScatterProg upsampleEnv
#guard assignThenScatterPrepared.map (fun p => p.plan.raw.steps.size) == some 2
-- Step 0 is NOT a scatter (it is `W`'s assignment) and step 1 is: exactly the adjacency
-- `rawPublicationSlots`' `.assign` lookahead falls through on.
#guard (assignThenScatterPrepared.bind (scatterStepAt · 0)).isNone
#guard (assignThenScatterPrepared.bind (scatterStepAt · 1)).map (·.destShape) == some #[6]
-- Both names publish, in source order: `W` at the assignment's own slot, `Out` at the scatter's.
#guard assignThenScatterPrepared.map
    (fun p => p.bindings.materializedNames.map (·.name)) == some #[ "W", "Out" ]
run_cmd do
  assertScatterParity "S6 W[i] := X[i]·X[i] ; Out[2*i] := W[i]" assignThenScatterProg
    upsampleEnv "Out" (dt [6] [1.0, 0.0, 4.0, 0.0, 9.0, 0.0])

/-! ## S7 — a two-dimensional strided write

Two independent source axes, one per destination dimension: the case where a swapped axis order in
the placement map WOULD change the answer, since the two extents differ. `X` is `2 × 3`, so `Out` is
`4 × 6` with the input values at even coordinates. -/

def upsample2dProg : TLProgram := tlprog!{ Out[2*i, 2*j] := X[i, j] }
def upsample2dEnv : HashMap String DenseTensor :=
  HashMap.ofList [("X", dt [2, 3] [1.0, 2.0, 3.0, 4.0, 5.0, 6.0])]
def upsample2dScatter : Option ScatterPlan :=
  (preparedOf upsample2dProg upsample2dEnv).bind (scatterStepAt · 0)
#guard upsample2dScatter.map (·.compute.outputShape) == some #[2, 3]
#guard upsample2dScatter.map (·.destShape) == some #[4, 6]
#guard upsample2dScatter.map (·.outCoeffs) == some #[#[2, 0], #[0, 2]]
#guard upsample2dScatter.map (·.outBias) == some #[0, 0]
run_cmd do
  assertScatterParity "S7 Out[2*i, 2*j] := X[i, j]" upsample2dProg upsample2dEnv "Out"
    (dt [4, 6] [ 1.0, 0.0, 2.0, 0.0, 3.0, 0.0
               , 0.0, 0.0, 0.0, 0.0, 0.0, 0.0
               , 4.0, 0.0, 5.0, 0.0, 6.0, 0.0
               , 0.0, 0.0, 0.0, 0.0, 0.0, 0.0 ])

/-! ## S8 — an RHS-only axis is a SOURCE axis, not a contracted one

The structural fact the emitter's whole shape depends on, isolated. `scatterSourceAxes` unions the
LHS axes with EVERY RHS axis, so `j` — which appears in no LHS slot — lands in the compute half's
OUTPUT basis rather than its reduction basis, and each `(i, j)` pair is enumerated as a separate
source coordinate that places its own value. That is the reference evaluator's equation. Had `j`
been treated as an ordinary assignment's contracted axis instead, it would have been SUMMED away and
this program would still have produced a plausible rank-1 answer — of the wrong semantics.

`Y` is deliberately extent 1, so the placement stays injective and the program has a value to
compare at all in the pre-S3a world; with a wider `Y` every source coordinate `(i, j)` lands on the
same `2·i`, which since S3a both backends SUM (see S10). -/

def rhsOnlyAxisProg : TLProgram := tlprog!{ Out[2*i] := X[i] · Y[j] }
def rhsOnlyAxisEnv : HashMap String DenseTensor :=
  HashMap.ofList [("X", dt [3] [1.0, 2.0, 3.0]), ("Y", dt [1] [10.0])]
def rhsOnlyAxisScatter : Option ScatterPlan :=
  (preparedOf rhsOnlyAxisProg rhsOnlyAxisEnv).bind (scatterStepAt · 0)
-- `j` is in the source domain, giving it rank 2 against a rank-1 destination …
#guard rhsOnlyAxisScatter.map (·.compute.outputShape) == some #[3, 1]
#guard rhsOnlyAxisScatter.map (·.destShape) == some #[6]
-- … and the placement row is source-basis wide, with a zero column for the axis no destination
-- dimension depends on.
#guard rhsOnlyAxisScatter.map (·.outCoeffs) == some #[#[2, 0]]
-- … and NOTHING is reduced: `j` sits in the output positions, not the reduction positions.
#guard rhsOnlyAxisScatter.map (fun s => (s.compute.terms[0]!).outputPos) == some #[0, 1]
#guard rhsOnlyAxisScatter.map (fun s => (s.compute.terms[0]!).reductionPos) == some #[]
run_cmd do
  assertScatterParity "S8 Out[2*i] := X[i]·Y[j]" rhsOnlyAxisProg rhsOnlyAxisEnv "Out"
    (dt [6] [10.0, 0.0, 20.0, 0.0, 30.0, 0.0])

/-! ## S9 / S9b — the zero-coefficient forms `Out[0*i]` and `Out[0*i+5]` are rejected by BOTH backends (B6)

`Out[0*i]` elaborates to `.affine (.scale 0 i)` and is genuinely surface-reachable: `lowerArith`'s
`LHSSlot.collapses` matches only `.affine (.const _)`, so it survives as a real `Stmt.scatter`, and
it still passes `capabilityPreflight` (`CompileTest` pins that). Its derived destination extent is
`0 · 3 = 0` (and `5` for `Out[0*i+5]`), so every write lands OUTSIDE the destination: an out-of-range
scatter write is an error in both backends (decision note §B6). The reference evaluator raises
`EvalError.scatterWriteOutOfRange` and `prepareEvalPlan`'s `checkScatter` rejects the plan with
`PlanError.scatterWriteOutOfRange`. These fixtures USED to assert agreement on the empty tensor
`dt [0] []` (S9) through `assertScatterParity`; they are flipped to a both-reject parity, not
weakened. Because `prepareEvalPlan` now rejects, the compiled plan's fields can no longer be
inspected through `preparedOf` — the former `outCoeffs`/`destShape` guards are replaced by the
rejection payload, which carries the same facts (image and extent). Accept neighbour: S1/S6/S8, the
in-range placements of the same family.

NOTE the channel: the checked-plan rejection reaches the caller as
`PlanCompileCause.invalidPlan (.assign (.nodeError 0 cause))` — the compiler-bug channel — because `compile` only
ever expected `checkPlan` to accept what the lowering emits. A surface `Out[0*i]` is a user error,
not a compiler bug; that classification is recorded, not changed, here. -/

/-- The `prepareEvalPlan` rejection cause, or `none` if it accepted (or the source did not compile). -/
def prepareCauseOf (p : TLProgram) (env : HashMap String DenseTensor) : Option PlanCompileCause :=
  match schedOf p with
  | none => none
  | some sched => match prepareEvalPlan sched (InputSignature.ofDenseInputs env) with
      | .error f => some f.cause
      | .ok _ => none

/-- The reference evaluator's out-of-range rejection `(tensor, outCoord, sourceCoord)`, or `none`
    if it accepted or failed any other way. -/
def referenceWriteOutOfRange (p : TLProgram) (env : HashMap String DenseTensor) :
    Option (String × List Int × List Nat) :=
  match schedOf p with
  | none => none
  | some sched => match LeanNCD.Eval.evalScheduled sched env with
      | .error e => match e.error with
          | .scatterWriteOutOfRange nm oc sc => some (nm, oc, sc)
          | _ => none
      | .ok _ => none

def zeroCoeffProg : TLProgram := tlprog!{ Out[0*i] := X[i] }
-- S9: both backends reject, with the same location (tensor `Out`, write at 0, source coordinate 0).
#guard prepareCauseOf zeroCoeffProg upsampleEnv
  == some (.invalidPlan (.assign (.nodeError 0 (.scatterWriteOutOfRange 0 0 0 0))))
#guard referenceWriteOutOfRange zeroCoeffProg upsampleEnv == some ("Out", [0], [0])

def zeroCoeffBiasProg : TLProgram := tlprog!{ Out[0*i+5] := X[i] }
-- S9b: extent 5, every write at 5.
#guard prepareCauseOf zeroCoeffBiasProg upsampleEnv
  == some (.invalidPlan (.assign (.nodeError 0 (.scatterWriteOutOfRange 0 5 5 5))))
#guard referenceWriteOutOfRange zeroCoeffBiasProg upsampleEnv == some ("Out", [5], [0])

/-! ## S10 — a surface-reachable collision is folded with the destination ⊕ (S3a)

`Out[2*i] := X[i, j]` has a source axis, `j`, absent from the LHS, so the `j` values of one `i` land
on the same destination cell: a collision, which both backends resolve with the destination's
additive monoid (real `+`, from 0_K = 0) instead of refusing it. `X = [[1,2],[3,4],[5,6]]` gives
`Out[0] = 1+2`, `Out[2] = 3+4`, `Out[4] = 5+6`; the odd cells are the empty fibre, 0. The reference
and the checked plan must agree with each other and with this hand-computed sum. Accept neighbour:
S8 / S7, the injective placements of the same family. -/

def collideProg : TLProgram := tlprog!{ Out[2*i] := X[i, j] }
def collideEnv : HashMap String DenseTensor :=
  HashMap.ofList [("X", dt [3, 2] [1.0, 2.0, 3.0, 4.0, 5.0, 6.0])]
run_cmd do
  assertScatterParity "S10 Out[2*i] := X[i, j]" collideProg collideEnv "Out"
    (dt [6] [3.0, 0.0, 7.0, 0.0, 11.0, 0.0])

end LeanNCD.Eval.Plan.ScatterCompileTest

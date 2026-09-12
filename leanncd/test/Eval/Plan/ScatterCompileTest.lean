import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Compile
import LeanNCD.Eval.Plan.Adapter   -- `runPreparedDense`: every fixture below executes its own plan

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
open LeanNCD LeanNCD.Eval.Plan
open Std

/-- A dense tensor from a shape and row-major data (the portfolio harness's `tl`, reproduced rather
    than imported so this file does not pull in LSpec for one constructor). -/
def dt (shape : List Nat) (xs : List Float) : DenseTensor := ⟨shape, xs.toArray⟩

/-- Source program → logical schedule, through the REAL compile pipeline (`assignUIDs` …
    `checkScatterNoScan` … `lowerArith` … `schedule`). Going through `compileToScheduled` rather
    than hand-writing a `ScheduledProgram` is the whole point of this file: a hand-built schedule
    could present a `Stmt.scatter` that `lowerArith` would never produce, which proves nothing about
    source reachability. -/
def schedOf (p : TLProgram) : Option ScheduledProgram :=
  match p.compileToScheduled.run 0 with
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
  let sched ← match prog.compileToScheduled.run 0 with
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
-- `fill` is the destination algebra's own reduction identity, which for real sum-product is `0.0`
-- — the same value `lowerArith` hard-codes as the source-level `ScatterOpts.fill`.
#guard upsampleScatter.map (·.fill) == some (ScalarConst.f64 (Float.toBits 0.0))
#guard upsampleScatter.map (·.reduce) == some LeanNCD.CollisionReduce.rejectCollisions
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

-- A non-zero bias on a strided row: extent `2 · 3 + 1 = 7`.
def shiftedProg : TLProgram := tlprog!{ Out[2*i + 1] := X[i] }
def shiftedScatter : Option ScatterPlan :=
  (preparedOf shiftedProg upsampleEnv).bind (scatterStepAt · 0)
#guard shiftedScatter.map (·.outCoeffs) == some #[#[2]]
#guard shiftedScatter.map (·.outBias) == some #[1]
#guard shiftedScatter.map (·.destShape) == some #[7]
run_cmd do
  assertScatterParity "S2 Out[2*i + 1] := X[i]" shiftedProg upsampleEnv "Out"
    (dt [7] [0.0, 1.0, 0.0, 2.0, 0.0, 3.0, 0.0])

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
compare at all: with a wider `Y` every source coordinate `(i, j)` would land on the same `2·i`, and
BOTH backends would (correctly, and in agreement) refuse it as a collision. -/

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

/-! ## S9 — the zero-coefficient degeneracy, `Out[0*i]`, reaches the emitter

`Out[0*i]` elaborates to `.affine (.scale 0 i)` and is genuinely surface-reachable: `lowerArith`'s
`LHSSlot.collapses` matches only `.affine (.const _)`, so it survives as a real `Stmt.scatter`.
`LHSSlot.outExtent`'s `.scale` arm answers `0 · 3 = 0`, the placement-row reconstruction answers the
same `0`, and the result is the empty destination tensor `checkScatter` was designed to admit and
`ScatterCheckTest` pins at the CHECKER level.

This fixture pins it at the SOURCE level, which is a different claim and the one that was briefly
false: `checkScatterLHSSlot` decided its constant-slot rejection by asking whether the NORMALISED
coefficient list was empty, and `normalizeCoeffs` drops zero coefficients — so `.scale 0 i` and
`.const n` were indistinguishable to it and this program was rejected under a locator naming the
wrong form. A checker-level pin cannot see that, because it never asks whether the emitter can
produce the plan from source at all. -/

def zeroCoeffProg : TLProgram := tlprog!{ Out[0*i] := X[i] }
def zeroCoeffScatter : Option ScatterPlan :=
  (preparedOf zeroCoeffProg upsampleEnv).bind (scatterStepAt · 0)
-- The source domain is the full `i : 3` — nothing about the degeneracy shrinks the COMPUTE half …
#guard zeroCoeffScatter.map (·.compute.outputShape) == some #[3]
-- … only the destination, whose single row is all-zero with a zero bias, giving extent `0`.
#guard zeroCoeffScatter.map (·.outCoeffs) == some #[#[0]]
#guard zeroCoeffScatter.map (·.outBias) == some #[0]
#guard zeroCoeffScatter.map (·.destShape) == some #[0]
run_cmd do
  assertScatterParity "S9 Out[0*i] := X[i]" zeroCoeffProg upsampleEnv "Out" (dt [0] [])

end LeanNCD.Eval.Plan.ScatterCompileTest

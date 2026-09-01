-- leanncd/test/Eval/Plan/BlockTest.lean
import LeanNCD.Eval.Plan.Block

/-!
# Wave F F2 block-checker tests

The context-indexed positive fixture reuses `KernelDenseTest.lean`'s `ctxPlan` verbatim (same
assignment, same expected values `ctx=0 -> [1,2,3]`, `ctx=1 -> [4,5,6]`, already independently
observed there) under a `RawPlanBlock` wrapper, so this file adds no new hand-derived numbers.
-/

namespace LeanNCD.Eval.Plan.BlockTest
open LeanNCD.Eval LeanNCD.Eval.Plan

-- One step block, contextShape=#[2]: input X (shape [2,3]), output Y (shape [3]),
-- Y[o] := X[ctx,o] — the exact assignment KernelDenseTest.lean's `ctxPlan` already verifies at
-- ctx=0 -> [1,2,3] and ctx=1 -> [4,5,6], now wrapped in a block with input/output ports.

def blockSigs : Array TensorSignature :=
  #[{ shape := #[2,3], dtype := .f64 }, { shape := #[3], dtype := .f64 }]

def blockReadX : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1,0], #[0,1]], bias := #[0,0] }
  , sourceShape := #[2,3], oobPolicy := .zeroPad }

def blockAssign : AssignPlan :=
  { contextShape := #[2], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[2,3], contextPos := #[0], outputPos := #[1], reductionPos := #[]
               , factors := #[.read blockReadX] }]
  , algebra := admittedAlgebra }

def stepBlock : RawPlanBlock :=
  { contextShape := #[2], tensorSigs := blockSigs, inputs := #[0]
  , steps := #[.assign blockAssign], outputs := #[1] }

run_cmd do
  match checkPlanBlock stepBlock with
  | .error e => throwError s!"checkPlanBlock rejected a well-formed block: {repr e}"
  | .ok _checked => pure ()

-- Mutation: duplicate output slot must be rejected with the exact witness, not merely "some error".
def dupOutputBlock : RawPlanBlock :=
  { stepBlock with outputs := #[1, 1] }

run_cmd do
  match checkPlanBlock dupOutputBlock with
  | .ok _ => throwError "duplicate output slot should have been rejected"
  | .error e =>
      unless e == .duplicateOutputSlot 1 do
        throwError s!"duplicate output: wrong error {repr e}"

-- Mutation: an assignment whose contextShape disagrees with the block's declared contextShape
-- must be rejected with the exact witness.
def wrongContextAssign : AssignPlan := { blockAssign with contextShape := #[3] }

def wrongContextBlock : RawPlanBlock :=
  { stepBlock with steps := #[.assign wrongContextAssign] }

run_cmd do
  match checkPlanBlock wrongContextBlock with
  | .ok _ => throwError "context-mismatched assignment should have been rejected"
  | .error e =>
      unless e == .blockContextMismatch 0 #[2] #[3] do
        throwError s!"context mismatch: wrong error {repr e}"

-- Execution: same `stepBlock` as Task 1, run at ctx=0 and ctx=1. Expected values are the same
-- [1,2,3]/[4,5,6] KernelDenseTest.lean's `ctxPlan` already observed for this exact assignment.
run_cmd do
  match checkPlanBlock stepBlock with
  | .error e => throwError s!"checkPlanBlock rejected a well-formed block: {repr e}"
  | .ok checked =>
      let x : DenseTensor := { shape := [2,3], data := #[1,2,3,4,5,6] }
      match runDenseBlock checked [0] #[x] with
      | .error e => throwError s!"ctx=0 failed: {repr e}"
      | .ok store => unless store[1]!.data == #[1,2,3] do
          throwError s!"ctx=0 wrong: {repr store[1]!.data}"
      match runDenseBlock checked [1] #[x] with
      | .error e => throwError s!"ctx=1 failed: {repr e}"
      | .ok store => unless store[1]!.data == #[4,5,6] do
          throwError s!"ctx=1 wrong: {repr store[1]!.data}"

-- Mutation: `runDenseBlock` arity mismatch (checked block expects exactly one input) must be
-- rejected with the same `PositionalInputError.arityMismatch` constructor `runDensePlan` uses.
run_cmd do
  match checkPlanBlock stepBlock with
  | .error e => throwError s!"checkPlanBlock rejected a well-formed block: {repr e}"
  | .ok checked =>
      match runDenseBlock checked [0] #[] with
      | .ok _ => throwError "arity mismatch should have been rejected"
      | .error e =>
          unless e == .arityMismatch 1 0 do
            throwError s!"arity mismatch: wrong error {repr e}"

-- Mutation: reaching `.wiring (.invalidForwardRead ...)` — the seven reused `PlanError` cases
-- wrapped by `BlockError.wiring` are otherwise untested by this file. A 2-node block with the
-- production order swapped: assignment A (index 0) reads slot 1, but slot 1's producer,
-- assignment B, is placed AFTER it (index 1), so A's read of slot 1 happens before slot 1 is ever
-- available.
def fwdSigs : Array TensorSignature :=
  #[{ shape := #[4], dtype := .f64 }, { shape := #[4], dtype := .f64 }, { shape := #[4], dtype := .f64 }]

def fwdReadSlot0 : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[4], oobPolicy := .zeroPad }

def fwdReadSlot1 : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[4], oobPolicy := .zeroPad }

-- A: writes slot 2, reads slot 1 (not yet produced when A runs).
def fwdAssignA : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[4]
  , terms := #[{ iterationShape := #[4], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read fwdReadSlot1] }]
  , algebra := admittedAlgebra }

-- B: writes slot 1, reads slot 0 — the true producer of slot 1, placed after A.
def fwdAssignB : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[4]
  , terms := #[{ iterationShape := #[4], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read fwdReadSlot0] }]
  , algebra := admittedAlgebra }

def forwardReadBlock : RawPlanBlock :=
  { contextShape := #[], tensorSigs := fwdSigs, inputs := #[0]
  , steps := #[.assign fwdAssignA, .assign fwdAssignB], outputs := #[2] }

run_cmd do
  match checkPlanBlock forwardReadBlock with
  | .ok _ => throwError "forward read of a not-yet-produced slot should have been rejected"
  | .error e =>
      -- Observed exact witness: node 0 (assignment A), term 0, factor 0, source slot 1.
      unless e == .wiring (.invalidForwardRead 0 0 0 1) do
        throwError s!"forward read: wrong error {repr e}"

-- Task 5.1: block forward-read locator with an Iverson factor BEFORE the failing read. Assignment A's
-- term becomes `[iverson, read(slot 1)]` (iteration basis `#[4]`, size 1, so leaf width 1). Block
-- checking skips the predicate but keeps the all-factor index, so it reports `fi = 1`, NOT filtered-
-- read 0.
def fwdBlockPred : PosBoolExpr :=
  .rel .lt (.affine { coeffs := #[0], bias := 0 }) (.affine { coeffs := #[0], bias := 1 })

def fwdAssignAIverson : AssignPlan :=
  { fwdAssignA with terms := #[{ fwdAssignA.terms[0]! with
      factors := #[.iverson fwdBlockPred, .read fwdReadSlot1] }] }

def forwardReadBlockIverson : RawPlanBlock :=
  { forwardReadBlock with steps := #[.assign fwdAssignAIverson, .assign fwdAssignB] }

run_cmd do
  match checkPlanBlock forwardReadBlockIverson with
  | .ok _ => throwError "forward read (with a preceding Iverson factor) should have been rejected"
  | .error e =>
      unless e == .wiring (.invalidForwardRead 0 0 1 1) do
        throwError s!"forward read (Iverson): wrong error {repr e}"

-- Task 5.1: `BlockStep.sourceSlots` excludes Iverson factors (filterMap reads). An assign whose term
-- is `[read(slot 0), iverson, read(slot 1)]` yields only the two read slots, in order.
def blockSourceSlotIversonAssign : AssignPlan :=
  { fwdAssignA with terms := #[{ fwdAssignA.terms[0]! with
      factors := #[.read fwdReadSlot0, .iverson fwdBlockPred, .read fwdReadSlot1] }] }

#guard (BlockStep.assign blockSourceSlotIversonAssign).sourceSlots == #[0, 1]

-- Mutation: reaching `.wiring (.missingProduction ...)` — a scratch slot (slot 2) is declared in
-- `tensorSigs` but is neither a block input nor produced by any assignment.
def scratchAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[4]
  , terms := #[{ iterationShape := #[4], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read fwdReadSlot0] }]
  , algebra := admittedAlgebra }

def missingProductionBlock : RawPlanBlock :=
  { contextShape := #[], tensorSigs := fwdSigs, inputs := #[0]
  , steps := #[.assign scratchAssign], outputs := #[1] }

run_cmd do
  match checkPlanBlock missingProductionBlock with
  | .ok _ => throwError "undeclared-producer slot should have been rejected"
  | .error e =>
      -- Observed exact witness: slot 2 (never an input, never produced).
      unless e == .wiring (.missingProduction 2) do
        throwError s!"missing production: wrong error {repr e}"

/-! ## Nonlinear block steps (Task 3)

`RawPlanBlock.steps` admits `.pointwise`/`.axiswise` alongside `.assign`. These five fixtures are
the first to exercise that: two positive (checking plus Dense execution, one per nonlinear kind) and
three negative, covering the ordinary wiring failures a nonlinear step can hit and the one
obligation that is specific to it — a nonlinear step's source must be a PRECEDING `.assign` step's
destination.

Expected values are the ones observed from the pre-implementation rehearsal in
`papers/implementation_seeds/nonlinearity_route_fragments/blockstep_migration/`, re-derived here
against the production types.
-/

-- Fixture 1. `stepBlock` plus a ReLU over the assignment's own result. X[ctx,o] at ctx=0 is
-- [1,-2,3], so the ReLU is [1,0,3].
def pointwiseBlock : RawPlanBlock :=
  { contextShape := #[2]
  , tensorSigs := blockSigs ++ #[{ shape := #[3], dtype := .f64 }]
  , inputs := #[0]
  , steps := #[.assign blockAssign,
      .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[3], fn := .relu }]
  , outputs := #[2] }

run_cmd do
  match checkPlanBlock pointwiseBlock with
  | .error e => throwError s!"checkPlanBlock rejected a well-formed pointwise block: {repr e}"
  | .ok checked =>
      let x : DenseTensor := { shape := [2,3], data := #[1,-2,3,4,-5,6] }
      match runDenseBlock checked [0] #[x] with
      | .error e => throwError s!"pointwise execution failed: {repr e}"
      | .ok store => unless store[2]!.data == #[1,0,3] do
          throwError s!"pointwise wrong result: {repr store[2]!.data}"

-- Fixture 2. The same block with an axiswise `normalize` instead. At ctx=0 the assignment yields
-- [1,2,3], which sum-normalizes to [1/6, 2/6, 3/6] — asserted as an exact sum plus strict
-- monotonicity rather than by pinning three Float literals.
def axiswiseBlock : RawPlanBlock :=
  { contextShape := #[2]
  , tensorSigs := blockSigs ++ #[{ shape := #[3], dtype := .f64 }]
  , inputs := #[0]
  , steps := #[.assign blockAssign,
      .axiswise { sourceSlot := 1, destinationSlot := 2, shape := #[3]
                , axisPos := 0, fn := .normalize }]
  , outputs := #[2] }

run_cmd do
  match checkPlanBlock axiswiseBlock with
  | .error e => throwError s!"checkPlanBlock rejected a well-formed axiswise block: {repr e}"
  | .ok checked =>
      let x : DenseTensor := { shape := [2,3], data := #[1,2,3,4,5,6] }
      match runDenseBlock checked [0] #[x] with
      | .error e => throwError s!"axiswise execution failed: {repr e}"
      | .ok store =>
          let d := store[2]!.data
          unless d.size == 3 && d[0]! < d[1]! && d[1]! < d[2]! &&
              ((d[0]! + d[1]! + d[2]!) - 1.0).abs < 0.000001 do
            throwError s!"axiswise wrong result: {repr d}"

-- Fixture 3. A `.pointwise` step reading a slot whose producer is placed AFTER it — the same
-- forward-read failure `forwardReadBlock` pins for assignments, now reached through a nonlinear
-- step's own source check.
def unproducedPointwiseBlock : RawPlanBlock :=
  { contextShape := #[], tensorSigs := fwdSigs, inputs := #[0]
  , steps := #[
      .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[4], fn := .relu },
      .assign fwdAssignB]
  , outputs := #[2] }

run_cmd do
  match checkPlanBlock unproducedPointwiseBlock with
  | .ok _ => throwError "a pointwise read of a not-yet-produced slot should have been rejected"
  | .error e => unless e == .wiring (.invalidForwardRead 0 0 0 1) do
      throwError s!"pointwise forward read: wrong error {repr e}"

-- Fixture 4. Source production restored, but a later assignment collides on the pointwise step's
-- destination — ordinary duplicate-destination wiring, reported against the nonlinear step as the
-- first producer.
def collidingPointwiseDestinationBlock : RawPlanBlock :=
  { contextShape := #[], tensorSigs := fwdSigs, inputs := #[0]
  , steps := #[.assign fwdAssignB,
      .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[4], fn := .relu },
      .assign fwdAssignA]
  , outputs := #[2] }

run_cmd do
  match checkPlanBlock collidingPointwiseDestinationBlock with
  | .ok _ => throwError "a duplicate destination on a pointwise step should have been rejected"
  | .error e => unless e == .wiring (.duplicateDestination 2 1 2) do
      throwError s!"pointwise duplicate destination: wrong error {repr e}"

-- Fixture 7. Nonlinearity chained directly onto nonlinearity: an axiswise step sourcing the
-- pointwise step's result. Its source IS available and IS produced by a preceding step — but that
-- step is not an `.assign`, so provenance rejects it.
def nonlinearChainBlock : RawPlanBlock :=
  { pointwiseBlock with
    tensorSigs := pointwiseBlock.tensorSigs ++ #[{ shape := #[3], dtype := .f64 }]
    steps := pointwiseBlock.steps ++ #[
      .axiswise { sourceSlot := 2, destinationSlot := 3, shape := #[3]
                , axisPos := 0, fn := .normalize }]
    outputs := #[3] }

run_cmd do
  match checkPlanBlock nonlinearChainBlock with
  | .ok _ => throwError "an axiswise step sourcing a pointwise result should have been rejected"
  | .error e => unless e == .nonlinearSourceNotLocalAssignment 2 2 do
      throwError s!"nonlinearity-onto-nonlinearity provenance: wrong error {repr e}"

-- `BlockError.nonlin` reachability. Every fixture above carries a geometrically VALID nonlinear
-- step, so none of them shows that a `checkPointwise`/`checkAxiswise` failure surfaces as
-- `.nonlin ni e` rather than being swallowed or mis-wrapped as `.wiring (.nodeError ni …)`. This
-- one has a pointwise step whose declared `shape` disagrees with its source slot's signature.
-- It also pins the node index, which is otherwise free to drift to a constant.
def badShapeNonlinBlock : RawPlanBlock :=
  { pointwiseBlock with
    steps := #[.assign blockAssign,
      .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[7], fn := .relu }] }

run_cmd do
  match checkPlanBlock badShapeNonlinBlock with
  | .ok _ => throwError "a pointwise step with a mismatched declared shape should have been rejected"
  | .error e => unless e == .nonlin 1 (.sourceShapeMismatch #[7] #[3]) do
      throwError s!"BlockError.nonlin routing: wrong error {repr e}"

-- Check ORDER, pinned. `checkPlanBlock`'s docstring states that provenance is enforced inside
-- `sourceCheck`, hence before the step's own local checker runs. This block's pointwise step
-- violates BOTH — it sources a block input (not a preceding assignment) AND declares a shape its
-- slot does not have. A correct implementation reports the provenance failure; one that ran
-- `localCheck` first would report `.nonlin`.
def badProvenanceAndShapeBlock : RawPlanBlock :=
  { contextShape := #[2]
  , tensorSigs := blockSigs ++ #[{ shape := #[3], dtype := .f64 }]
  , inputs := #[0]
  , steps := #[.assign blockAssign,
      .pointwise { sourceSlot := 0, destinationSlot := 2, shape := #[7], fn := .relu }]
  , outputs := #[2] }

run_cmd do
  match checkPlanBlock badProvenanceAndShapeBlock with
  | .ok _ => throwError "a pointwise step violating both provenance and shape should have been rejected"
  | .error e => unless e == .nonlinearSourceNotLocalAssignment 1 0 do
      throwError s!"provenance must precede local check: wrong error {repr e}"

/-!
## `CheckedPlanBlock` construction boundary (compile-time privacy check)

Pins that `checkPlanBlock` is the only way to obtain a `CheckedPlanBlock`, matching
`CheckedPrivacyTest.lean`'s check for `CheckedAssignPlan`: the structure's constructor is
`private mk ::`, so anonymous-constructor notation (`⟨...⟩`) cannot be used to smuggle an
unchecked `RawPlanBlock` past `checkPlanBlock` from outside `LeanNCD.Eval.Plan`.

As in `CheckedPrivacyTest.lean`, the negative half of this check is NOT an automated `#guard` — it
is a documented manual verification. The line below is deliberately commented out; it must never be
uncommented in committed code, because it must NOT compile:

```
-- def smuggled : CheckedPlanBlock := ⟨stepBlock⟩
```

Manually verified (2026-08-14) by uncommenting that exact line (with `stepBlock : RawPlanBlock`
already in scope above) and running, from `leanncd/`:

```
lake env lean test/Eval/Plan/BlockTest.lean
```

Observed failure, exit code 1, literal captured stdout/stderr:

```
test/Eval/Plan/BlockTest.lean:194:35: error: Invalid `⟨...⟩` notation: Constructor for `LeanNCD.Eval.Plan.CheckedPlanBlock` is marked as private
```

The line was re-commented immediately after confirming the failure; this file compiles clean with
it commented out, exercising only the positive half (normal construction via `checkPlanBlock`
works, already exercised by the fixtures above).
-/

-- normal construction via the checker succeeds (already exercised above; restated here for
-- parity with CheckedPrivacyTest.lean's structure)
#guard (checkPlanBlock stepBlock).toOption.isSome

-- must NOT compile: def smuggled : CheckedPlanBlock := ⟨stepBlock⟩

end LeanNCD.Eval.Plan.BlockTest

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
               , factors := #[blockReadX] }]
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
               , factors := #[fwdReadSlot1] }]
  , algebra := admittedAlgebra }

-- B: writes slot 1, reads slot 0 — the true producer of slot 1, placed after A.
def fwdAssignB : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[4]
  , terms := #[{ iterationShape := #[4], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[fwdReadSlot0] }]
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

-- Mutation: reaching `.wiring (.missingProduction ...)` — a scratch slot (slot 2) is declared in
-- `tensorSigs` but is neither a block input nor produced by any assignment.
def scratchAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[4]
  , terms := #[{ iterationShape := #[4], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[fwdReadSlot0] }]
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

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
  , assignments := #[blockAssign], outputs := #[1] }

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
  { stepBlock with assignments := #[wrongContextAssign] }

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

end LeanNCD.Eval.Plan.BlockTest

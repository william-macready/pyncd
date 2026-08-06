import LeanNCD.Eval.Plan.Check

/-!
# Wave C C3 graph checker tests

Reference graphs plus mutation coverage for `checkPlan`'s wiring invariants (slot availability,
production order) on top of `checkAssign`'s already-tested local invariants.
-/

namespace LeanNCD.Eval.Plan.GraphCheckTest
open LeanNCD.Eval.Plan

/-- An identity read: `Y[i] := X[slot][i]`. -/
def idRead (slot : TensorSlot) : ReadPlan :=
  { sourceSlot := slot, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[2], oobPolicy := .zeroPad }

/-- An identity node: destination `dest` copies `src` verbatim. -/
def idNode (dest src : TensorSlot) : AssignPlan :=
  { destinationSlot := dest, outputShape := #[2]
  , terms := #[{ iterationShape := #[2], outputPos := #[0], reductionPos := #[]
               , factors := #[idRead src] }]
  , algebra := admittedAlgebra }

/-!
## Chain: X -> Y -> Z
-/

def chainSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }   -- 0 = X (input)
   , { shape := #[2], dtype := .f64 }   -- 1 = Y
   , { shape := #[2], dtype := .f64 } ] -- 2 = Z

def chainPlan : RawEvalPlan :=
  { version := admittedVersion, tensorSigs := chainSigs, inputSlots := #[0]
  , steps := #[idNode 1 0, idNode 2 1], numericMode := .reference64 }

def isOk : Except PlanError CheckedEvalPlan → Bool
  | .ok _ => true | .error _ => false

def errOf : Except PlanError CheckedEvalPlan → Option PlanError
  | .ok _ => none | .error e => some e

-- the chain is accepted
#guard isOk (checkPlan chainPlan)

/-!
## Diamond / fan-out with an unused input: X -> A, X -> B, {A, B} -> C; slot 4 (`W`) is a second
input never read by any node.
-/

def diamondSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }   -- 0 = X (input)
   , { shape := #[2], dtype := .f64 }   -- 1 = A
   , { shape := #[2], dtype := .f64 }   -- 2 = B
   , { shape := #[2], dtype := .f64 }   -- 3 = C
   , { shape := #[2], dtype := .f64 } ] -- 4 = W (input, unused)

/-- `C[i] := A[i] + B[i]`: two single-factor terms, folded by `reduceOp = add`. -/
def nodeC : AssignPlan :=
  { destinationSlot := 3, outputShape := #[2]
  , terms := #[ { iterationShape := #[2], outputPos := #[0], reductionPos := #[]
                , factors := #[idRead 1] }
              , { iterationShape := #[2], outputPos := #[0], reductionPos := #[]
                , factors := #[idRead 2] } ]
  , algebra := admittedAlgebra }

def diamondPlan : RawEvalPlan :=
  { version := admittedVersion, tensorSigs := diamondSigs, inputSlots := #[0, 4]
  , steps := #[idNode 1 0, idNode 2 0, nodeC], numericMode := .reference64 }

-- the diamond (fan-out + convergence + an unused input) is accepted
#guard isOk (checkPlan diamondPlan)

/-!
## Mutations
-/

-- version not admitted
#guard errOf (checkPlan { diamondPlan with version := 2 }) == some (.versionNotAdmitted 2)

-- duplicate input slot
#guard errOf (checkPlan { diamondPlan with inputSlots := #[0, 0] })
  == some (.duplicateInputSlot 0)

-- input slots not ordered (decreasing, not equal)
#guard errOf (checkPlan { diamondPlan with inputSlots := #[4, 0] })
  == some (.inputSlotsNotOrdered 0)

-- input slot out of range
#guard errOf (checkPlan { diamondPlan with inputSlots := #[0, 99] })
  == some (.slotOutOfRange 99 5)

-- node-level destination slot out of range: nodeA (index 0) targets slot 99, which doesn't exist
-- in the 5-slot table. Wrapped with node context via `.nodeError`, matching every other per-node
-- failure in this loop.
#guard errOf (checkPlan { diamondPlan with steps := #[idNode 99 0, idNode 2 0, nodeC] })
  == some (.nodeError 0 (.slotOutOfRange 99 5))

-- node-level source slot out of range: nodeC (index 2) reads slot 99 via its first term/first
-- factor instead of slot 1. Wrapped with node context, same as the destination case above.
#guard errOf (checkPlan
  { diamondPlan with steps := #[idNode 1 0, idNode 2 0,
      { nodeC with terms := #[{ nodeC.terms[0]! with factors := #[idRead 99] }, nodeC.terms[1]!] }] })
  == some (.nodeError 2 (.slotOutOfRange 99 5))

-- invalid forward read: nodeC (index 2) reads slot 3 (its own not-yet-produced destination) via
-- its first term/first factor instead of slot 1
#guard errOf (checkPlan
  { diamondPlan with steps := #[idNode 1 0, idNode 2 0,
      { nodeC with terms := #[{ nodeC.terms[0]! with factors := #[idRead 3] }, nodeC.terms[1]!] }] })
  == some (.invalidForwardRead 2 0 0 3)

-- reordering a DEPENDENT node is rejected outright, not merely "a different but valid result":
-- moving nodeC (which reads slots 1 and 2) before the nodes that produce them is an
-- invalidForwardRead, not a permitted reordering — "reordering preserves results only when
-- dependencies permit it" (A.7) is enforced by rejection here, not by computing a wrong answer.
#guard errOf (checkPlan { diamondPlan with steps := #[nodeC, idNode 1 0, idNode 2 0] })
  == some (.invalidForwardRead 0 0 0 1)

-- duplicate destination: nodeB (index 1) overwritten to also target slot 1 (nodeA's destination)
#guard errOf (checkPlan { diamondPlan with steps := #[idNode 1 0, idNode 1 0, nodeC] })
  == some (.duplicateDestination 1 0 1)

-- input slot overwritten: a node targets input slot 4 (W)
#guard errOf (checkPlan { diamondPlan with steps := #[idNode 4 0, idNode 2 0, nodeC] })
  == some (.inputSlotOverwritten 4 0)

-- missing production: drop nodeC, so slot 3 (C) is declared in tensorSigs but never produced
#guard errOf (checkPlan { diamondPlan with steps := #[idNode 1 0, idNode 2 0] })
  == some (.missingProduction 3)

-- local error propagated with node context: nodeA's own outputShape is mutated to disagree with
-- its destination signature, which checkAssign already rejects (destinationShapeMismatch),
-- wrapped here with the node index that produced it
#guard errOf (checkPlan
  { diamondPlan with steps := #[{ idNode 1 0 with outputShape := #[3] }, idNode 2 0, nodeC] })
  == some (.nodeError 0 (.destinationShapeMismatch #[3] #[2]))

-- numericModeNotAdmitted: structurally unreachable via checkPlan (NumericMode has exactly one
-- constructor, reference64), same pattern as checkAssign's single-valued-vocabulary
-- unreachables — named directly instead of exercised through checkPlan.
#guard (PlanError.numericModeNotAdmitted .reference64) == PlanError.numericModeNotAdmitted .reference64

/-!
## `CheckedEvalPlan` privacy (compile-time check, folded into this file per A.3's module list —
no separate privacy-test module for C3)
-/

-- normal construction via the checker succeeds
#guard (checkPlan diamondPlan).toOption.isSome

-- must NOT compile: def smuggled : CheckedEvalPlan := ⟨diamondPlan, #[]⟩

end LeanNCD.Eval.Plan.GraphCheckTest

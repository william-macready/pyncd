import LeanNCD.Eval.Plan.Dense

/-!
# Wave C C3 graph interpreter tests

Every expected tensor here is hand-computed and confirmed by an actual run; none is read back from
this interpreter's own output. Mirrors `GraphCheckTest`'s reference graphs (chain, diamond) rather
than inventing a third topology.
-/

namespace LeanNCD.Eval.Plan.GraphDenseTest
open LeanNCD.Eval LeanNCD.Eval.Plan

/-- An identity read: `Y[i] := X[slot][i]`. -/
def idRead (slot : TensorSlot) : ReadPlan :=
  { sourceSlot := slot, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[2], oobPolicy := .zeroPad }

/-- An identity node: destination `dest` copies `src` verbatim. -/
def idNode (dest src : TensorSlot) : AssignPlan :=
  { contextShape := #[], destinationSlot := dest, outputShape := #[2]
  , terms := #[{ iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[idRead src] }]
  , algebra := admittedAlgebra }

def runGraph (raw : RawEvalPlan) (inputs : Array DenseTensor) :
    Except String (Array DenseTensor) :=
  match checkPlan raw with
  | .error e => .error s!"check failed: {repr e}"
  | .ok c => match runDensePlan c inputs with
             | .error e => .error s!"run failed: {repr e}"
             | .ok store => .ok store

def dataOf (store : Except String (Array DenseTensor)) (slot : TensorSlot) : Option (Array Float) :=
  match store with
  | .error _ => none
  | .ok s => (s[slot]?).map DenseTensor.data

/-!
## One node
-/

def oneNodeSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }, { shape := #[2], dtype := .f64 } ]

def oneNodePlan : RawEvalPlan :=
  { version := admittedVersion, tensorSigs := oneNodeSigs, inputSlots := #[0]
  , steps := #[idNode 1 0], numericMode := .reference64 }

def oneNodeInputs : Array DenseTensor := #[ { shape := [2], data := #[3.0, 4.0] } ]

-- Y[i] := X[i]; hand computation: Y = X = [3, 4].
#guard dataOf (runGraph oneNodePlan oneNodeInputs) 1 == some #[3.0, 4.0]

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

def chainInputs : Array DenseTensor := #[ { shape := [2], data := #[5.0, 7.0] } ]

-- X = [5, 7]; Y := X; Z := Y. Hand computation: the whole store is X duplicated three times.
#guard dataOf (runGraph chainPlan chainInputs) 0 == some #[5.0, 7.0]
#guard dataOf (runGraph chainPlan chainInputs) 1 == some #[5.0, 7.0]
#guard dataOf (runGraph chainPlan chainInputs) 2 == some #[5.0, 7.0]

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
  { contextShape := #[], destinationSlot := 3, outputShape := #[2]
  , terms := #[ { iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
                , factors := #[idRead 1] }
              , { iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
                , factors := #[idRead 2] } ]
  , algebra := admittedAlgebra }

def diamondPlan : RawEvalPlan :=
  { version := admittedVersion, tensorSigs := diamondSigs, inputSlots := #[0, 4]
  , steps := #[idNode 1 0, idNode 2 0, nodeC], numericMode := .reference64 }

-- inputs ordered by inputSlots = #[0, 4]: X first, then W.
def diamondInputs : Array DenseTensor :=
  #[ { shape := [2], data := #[5.0, 7.0] }, { shape := [2], data := #[9.0, 11.0] } ]

-- X=[5,7], W=[9,11] (unused). A := X = [5,7]; B := X = [5,7]; C := A+B = [10,14].
#guard dataOf (runGraph diamondPlan diamondInputs) 0 == some #[5.0, 7.0]
#guard dataOf (runGraph diamondPlan diamondInputs) 1 == some #[5.0, 7.0]
#guard dataOf (runGraph diamondPlan diamondInputs) 2 == some #[5.0, 7.0]
#guard dataOf (runGraph diamondPlan diamondInputs) 3 == some #[10.0, 14.0]
#guard dataOf (runGraph diamondPlan diamondInputs) 4 == some #[9.0, 11.0]

/-!
## Noncontiguous input placement with a produced-slot chain

Distinct from both topologies above. `diamondPlan` leaves its second input slot (4) *unread*, so it
cannot show that a high-numbered input was placed at the right slot. Here slot 4 is an input that the
first node *reads*, the second node can only read the slot the first node just produced, and the third
node sums a produced slot with an input slot. The expected full store therefore distinguishes input
placement (slot 4, not slot 1), node order, and final arithmetic together.

Shared with the JAX affine bridge: `experiments/jax_bridge/EvalPlanAffineSmoke.lean` renders this same
plan as its positional-graph fixture, so the two backends compare on one checked graph rather than two
hand-built ones. These definitions live here, in a default Lake target, so an `Eval/Plan` field change
breaks `lake build` rather than only the untargeted bridge driver.
-/

def placementSigs : Array TensorSignature :=
  Array.replicate 5 { shape := #[2], dtype := .f64 }

/-- Sums two slots into `dest`, one term per source, in the given order. -/
def sumNode (dest srcA srcB : TensorSlot) : AssignPlan :=
  { contextShape := #[], destinationSlot := dest, outputShape := #[2]
  , terms := #[ { iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
                , factors := #[idRead srcA] }
              , { iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
                , factors := #[idRead srcB] } ]
  , algebra := admittedAlgebra }

def placementPlan : RawEvalPlan :=
  { version := admittedVersion, tensorSigs := placementSigs, inputSlots := #[0, 4]
  , steps := #[idNode 1 4, idNode 2 1, sumNode 3 2 0], numericMode := .reference64 }

/-- Inputs ordered by `inputSlots = #[0, 4]`: slot 0 first, then slot 4. -/
def placementInputs : Array DenseTensor :=
  #[ { shape := [2], data := #[2.0, 3.0] }, { shape := [2], data := #[5.0, 7.0] } ]

-- slot0=[2,3], slot4=[5,7]. slot1 := slot4 = [5,7]; slot2 := slot1 = [5,7];
-- slot3 := slot2 + slot0 = [7,10]. Hand-computed.
#guard dataOf (runGraph placementPlan placementInputs) 0 == some #[2.0, 3.0]
#guard dataOf (runGraph placementPlan placementInputs) 1 == some #[5.0, 7.0]
#guard dataOf (runGraph placementPlan placementInputs) 2 == some #[5.0, 7.0]
#guard dataOf (runGraph placementPlan placementInputs) 3 == some #[7.0, 10.0]
#guard dataOf (runGraph placementPlan placementInputs) 4 == some #[5.0, 7.0]

-- reordering independent nodes: swap A/B's step order (neither depends on the other) — the graph
-- is still accepted and the final store is identical, slot-for-slot.
def diamondPlanSwapped : RawEvalPlan :=
  { diamondPlan with steps := #[idNode 2 0, idNode 1 0, nodeC] }

#guard dataOf (runGraph diamondPlanSwapped diamondInputs) 1 == some #[5.0, 7.0]
#guard dataOf (runGraph diamondPlanSwapped diamondInputs) 2 == some #[5.0, 7.0]
#guard dataOf (runGraph diamondPlanSwapped diamondInputs) 3 == some #[10.0, 14.0]

-- manual sequential composition agrees with `runDensePlan`: thread the store by hand, node by
-- node, calling `checkAssign`/`runDenseAssign` directly instead of going through `checkPlan`/
-- `runDensePlan`, and confirm the destination slots agree.
def manualDiamond : Except String (Array DenseTensor) := do
  let store0 : Array DenseTensor :=
    #[ { shape := [2], data := #[5.0, 7.0] }, { shape := [], data := #[] }
     , { shape := [], data := #[] }, { shape := [], data := #[] }
     , { shape := [2], data := #[9.0, 11.0] } ]
  let cA ← match checkAssign diamondSigs (idNode 1 0) with
    | .ok c => pure c | .error e => .error s!"{repr e}"
  let a ← match runDenseAssign cA store0 with
    | .ok d => pure d | .error e => .error s!"{repr e}"
  let store1 := store0.set! 1 a
  let cB ← match checkAssign diamondSigs (idNode 2 0) with
    | .ok c => pure c | .error e => .error s!"{repr e}"
  let b ← match runDenseAssign cB store1 with
    | .ok d => pure d | .error e => .error s!"{repr e}"
  let store2 := store1.set! 2 b
  let cC ← match checkAssign diamondSigs nodeC with
    | .ok c => pure c | .error e => .error s!"{repr e}"
  let c ← match runDenseAssign cC store2 with
    | .ok d => pure d | .error e => .error s!"{repr e}"
  return store2.set! 3 c

#guard (manualDiamond.map (fun s => (s[1]!.data, s[2]!.data, s[3]!.data))).toOption ==
  some (#[5.0, 7.0], #[5.0, 7.0], #[10.0, 14.0])
#guard dataOf (runGraph diamondPlan diamondInputs) 3 ==
  (manualDiamond.map (fun s => s[3]!.data)).toOption

/-!
## Reordering Float-sensitive terms inside one node is not graph equivalence

This restates C2's `KernelDenseTest.fosPlan` fixture (three term values chosen so binary64 addition
is non-associative) wrapped in a trivial one-node graph, to confirm `runDensePlan` does not disturb
node-level term-fold order via any graph-level buffering. The numeric phenomenon itself (folding
`1e16, 1.0, -1e16` strictly in array order yields `0.0`, not `1.0`) was already established and
hand-verified in C2; this fixture is a graph-level integration check, not a new numeric claim.
-/

def fosSigs : Array TensorSignature :=
  #[ { shape := #[], dtype := .f64 }
   , { shape := #[], dtype := .f64 }
   , { shape := #[], dtype := .f64 }
   , { shape := #[1], dtype := .f64 } ]

def fosRead (slot : TensorSlot) : ReadPlan :=
  { sourceSlot := slot, map := { coeffs := #[], bias := #[] }
  , sourceShape := #[], oobPolicy := .zeroPad }

def fosTerm (slot : TensorSlot) : TermPlan :=
  { iterationShape := #[1], contextPos := #[], outputPos := #[0], reductionPos := #[]
  , factors := #[fosRead slot] }

def fosNode : AssignPlan :=
  { contextShape := #[], destinationSlot := 3, outputShape := #[1]
  , terms := #[fosTerm 0, fosTerm 1, fosTerm 2], algebra := admittedAlgebra }

def fosPlan : RawEvalPlan :=
  { version := admittedVersion, tensorSigs := fosSigs, inputSlots := #[0, 1, 2]
  , steps := #[fosNode], numericMode := .reference64 }

def fosInputs : Array DenseTensor :=
  #[ { shape := [], data := #[1e16] }, { shape := [], data := #[1.0] }
   , { shape := [], data := #[-1e16] } ]

-- ((0 + 1e16) + 1.0) + (-1e16) = 0.0, in `fosNode.terms` array order — matches C2's confirmed run.
#guard dataOf (runGraph fosPlan fosInputs) 3 == some #[0.0]

/-!
## `PositionalInputError` cases
-/

def posErrOf (raw : RawEvalPlan) (inputs : Array DenseTensor) : Option PositionalInputError :=
  match checkPlan raw with
  | .error _ => none
  | .ok c => match runDensePlan c inputs with
             | .error e => some e
             | .ok _ => none

-- wrong arity (too few): chainPlan expects 1 input, given 0.
#guard posErrOf chainPlan #[] == some (.arityMismatch 1 0)

-- wrong arity (too many): chainPlan expects 1 input, given 2.
#guard posErrOf chainPlan #[chainInputs[0]!, chainInputs[0]!] == some (.arityMismatch 1 2)

-- wrong runtime shape: X declared shape #[2], but the runtime tensor has shape [3].
#guard posErrOf chainPlan #[{ shape := [3], data := #[1.0, 2.0, 3.0] }] ==
  some (.shapeMismatch 0 #[2] [3])

-- malformed storage: X declares shape [2] (matching the plan) but its data array holds only 1
-- element — shape agrees, storage size does not.
#guard posErrOf chainPlan #[{ shape := [2], data := #[1.0] }] == some (.storageMismatch 0 [2] 1)

-- unread input still validated: W (slot 4) is never read by any node in the diamond, but a
-- wrong-shaped W is still caught before `runDensePlan` returns — an unread input slot is not a
-- validation loophole. Inputs are ordered by `diamondPlan.inputSlots = #[0, 4]`, so X (correct)
-- comes first and W (declared shape #[2], supplied shape [3]) comes second.
#guard posErrOf diamondPlan
    #[ { shape := [2], data := #[5.0, 7.0] }, { shape := [3], data := #[9.0, 11.0, 1.0] } ] ==
  some (.shapeMismatch 4 #[2] [3])

end LeanNCD.Eval.Plan.GraphDenseTest

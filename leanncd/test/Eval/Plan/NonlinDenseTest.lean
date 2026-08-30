import LeanNCD.Eval.Plan.EvalPlan

/-!
# Thread 4 (Task 2) dense-worker graph tests

`.pointwise`/`.axiswise` steps chained after an `.assign`, end-to-end through `checkPlan`/
`runDensePlan`. Mirrors `GraphDenseTest.lean`'s `idRead`/`idNode`/`oneNodeSigs`/`oneNodePlan`
shape directly; every expected tensor is hand-computed, not read back from the interpreter.
-/

namespace LeanNCD.Eval.Plan.NonlinDenseTest
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
## `.assign → .pointwise` chain: `Y := X; Z := relu(Y)`

Donor value: `NonlinTest.lean`'s `reluT (t1 [-1, 2, -3, 4]) == t1 [0, 2, 0, 4]`, same function,
smaller vector.
-/

def oneNodeSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }, { shape := #[2], dtype := .f64 }
   , { shape := #[2], dtype := .f64 } ]

def pointwisePlan : RawEvalPlan :=
  { tensorSigs := oneNodeSigs, inputSlots := #[0]
  , steps := #[.assign (idNode 1 0)
              , .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[2], fn := .relu }]
  }

def pointwiseInputs : Array DenseTensor := #[ { shape := [2], data := #[-1.0, 2.0] } ]

-- Y := X = [-1, 2]; Z := relu(Y) = [0, 2].
#guard dataOf (runGraph pointwisePlan pointwiseInputs) 2 == some #[0.0, 2.0]

/-!
## `.assign → .axiswise` chain: `Y := X; Z := normalize(Y, axis 1)`

Donor value: `NormTest.lean`'s NM1, `A=[[1,3],[2,2]] ⇒ [[0.25,0.75],[0.5,0.5]]` — the flattened
`1,3,2,2` is `A`'s data in row-major order (not its shape).
-/

def axiswiseSigs : Array TensorSignature :=
  #[ { shape := #[2,2], dtype := .f64 }, { shape := #[2,2], dtype := .f64 }
   , { shape := #[2,2], dtype := .f64 } ]

/-- An identity read over a `#[2,2]`-shaped slot. -/
def idRead22 (slot : TensorSlot) : ReadPlan :=
  { sourceSlot := slot, map := { coeffs := #[#[1,0], #[0,1]], bias := #[0,0] }
  , sourceShape := #[2,2], oobPolicy := .zeroPad }

/-- An identity node over a `#[2,2]`-shaped slot: destination `dest` copies `src` verbatim. -/
def idNode22 (dest src : TensorSlot) : AssignPlan :=
  { contextShape := #[], destinationSlot := dest, outputShape := #[2,2]
  , terms := #[{ iterationShape := #[2,2], contextPos := #[], outputPos := #[0,1]
               , reductionPos := #[], factors := #[idRead22 src] }]
  , algebra := admittedAlgebra }

def axiswisePlan : RawEvalPlan :=
  { tensorSigs := axiswiseSigs, inputSlots := #[0]
  , steps := #[.assign (idNode22 1 0)
              , .axiswise { sourceSlot := 1, destinationSlot := 2, shape := #[2,2]
                          , axisPos := 1, fn := .normalize }]
  }

def axiswiseInputs : Array DenseTensor := #[ { shape := [2,2], data := #[1.0, 3.0, 2.0, 2.0] } ]

-- Y := X = [[1,3],[2,2]]; Z := normalize(Y, axis 1) = [[0.25,0.75],[0.5,0.5]].
#guard dataOf (runGraph axiswisePlan axiswiseInputs) 2 == some #[0.25, 0.75, 0.5, 0.5]

/-!
## Runtime trust boundary: the nonlinearity workers re-validate their source slot

`runDensePointwise`/`runDenseAxiswise` re-check the runtime store against the shape the checker
validated before applying the function — the same discipline `runDenseAssignAt`/`validateStore`
(`Dense.lean`) already honor, now applied symmetrically to all three workers. These fixtures drive
the workers directly (not through `runDensePlan`) with a deliberately malformed store, mirroring
`KernelDenseTest.lean`'s `posErrOf` fixtures for `runDenseAssign`. Each expected error is derived by
hand from the mismatch, not read back from the worker.
-/

-- A pointwise op reading slot 0 (shape #[2]) and writing slot 1.
def probePointwise : RawPointwisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[2], fn := .relu }

def pwErrOf (store : Array DenseTensor) : Option PositionalInputError :=
  match checkPointwise oneNodeSigs probePointwise with
  | .error _ => none
  | .ok c => match runDensePointwise c store with
             | .error e => some e
             | .ok _ => none

-- missing slot: an empty store cannot provide source slot 0.
#guard pwErrOf #[] == some (.missingSlot 0 0)

-- wrong runtime shape: slot 0 has runtime shape [3], but the checked shape is #[2].
#guard pwErrOf #[ { shape := [3], data := #[1.0, 2.0, 3.0] } ] == some (.shapeMismatch 0 #[2] [3])

-- malformed storage: slot 0 declares shape [2] but its data array holds only one element.
#guard pwErrOf #[ { shape := [2], data := #[1.0] } ] == some (.storageMismatch 0 [2] 1)

-- well-formed store: no error (the function applies).
#guard pwErrOf #[ { shape := [2], data := #[-1.0, 2.0] } ] == none

-- An axiswise op reading slot 0 (shape #[2,2]) and writing slot 1, reducing axis 1.
def probeAxiswise : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[2,2], axisPos := 1, fn := .normalize }

def axErrOf (store : Array DenseTensor) : Option PositionalInputError :=
  match checkAxiswise axiswiseSigs probeAxiswise with
  | .error _ => none
  | .ok c => match runDenseAxiswise c store with
             | .error e => some e
             | .ok _ => none

-- missing slot: an empty store cannot provide source slot 0.
#guard axErrOf #[] == some (.missingSlot 0 0)

-- wrong runtime shape: slot 0 has runtime shape [2,3], but the checked shape is #[2,2].
#guard axErrOf #[ { shape := [2,3], data := #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0] } ]
  == some (.shapeMismatch 0 #[2,2] [2,3])

-- malformed storage: slot 0 declares shape [2,2] but its data array holds only three elements.
#guard axErrOf #[ { shape := [2,2], data := #[1.0, 2.0, 3.0] } ]
  == some (.storageMismatch 0 [2,2] 3)

-- well-formed store: no error (the function applies).
#guard axErrOf #[ { shape := [2,2], data := #[1.0, 3.0, 2.0, 2.0] } ] == none

end LeanNCD.Eval.Plan.NonlinDenseTest

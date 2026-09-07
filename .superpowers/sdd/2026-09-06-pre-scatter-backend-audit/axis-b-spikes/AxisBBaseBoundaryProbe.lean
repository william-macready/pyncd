/-
Axis B / Task B1 construction spikes, part 2 — base-boundary looseness + `DSL/Ast.lean` slot
functions. FINDINGS-ONLY. Not in lakefile.toml, not in any default target.
Run with:  lake env lean spikes/AxisBBaseBoundaryProbe.lean
-/
import LeanNCD.Eval.Plan.Scan
import LeanNCD.DSL.Ast

namespace LeanNCD.Eval.Plan.AxisBProbe2
open LeanNCD.Eval.Plan

/-! ## S14 — a base write that touches the lower boundary of only ONE of two advancing dims -/

def sigs2D : Array TensorSignature :=
  #[ { shape := #[], dtype := .f64 }
   , { shape := #[3, 3], dtype := .f64 }
   , { shape := #[3, 3], dtype := .f64 } ]

def state2D : StateSlot :=
  { destSlot := 2, advancingDims := #[0, 1], materialization := .completeHistory }

def base2D : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[{ shape := #[], dtype := .f64 }]
  , inputs := #[0], steps := #[], outputs := #[0] }

-- dp[0, 1] := S0 — dim0 pinned to 0 (boundary), dim1 pinned to 1 (NOT the boundary).
def offBoundaryMap : AffineMap := { coeffs := #[#[], #[]], bias := #[0, 1] }
def baseWriteOff : StateWriteMap := { outputSlot := 0, stateIndex := 0, map := offBoundaryMap }

def offRows : Array (Option WriteRowKind) := writeRowKinds 2 0 baseWriteOff

#eval ( offRows
      , baseWriteRowsOk #[0, 1] 0 offRows
      , pinnedLiteralsInRange #[3, 3] offRows
      , freeExtentsAgree #[3, 3] #[] offRows )

-- Step block: dp[r+1, c+1] := T[r, c]
def stepReadT : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1, 0], #[0, 1]], bias := #[0, 0] }
  , sourceShape := #[3, 3], oobPolicy := .zeroPad }

def stepTermT : TermPlan :=
  { iterationShape := #[2, 2], contextPos := #[0, 1], outputPos := #[], reductionPos := #[]
  , factors := #[.read stepReadT] }

def stepAssign2D : AssignPlan :=
  { contextShape := #[2, 2], destinationSlot := 2, outputShape := #[], terms := #[stepTermT]
  , algebra := admittedAlgebra }

def step2D : RawPlanBlock :=
  { contextShape := #[2, 2]
  , tensorSigs := #[ { shape := #[3, 3], dtype := .f64 }
                   , { shape := #[3, 3], dtype := .f64 }
                   , { shape := #[], dtype := .f64 } ]
  , inputs := #[0, 1], steps := #[.assign stepAssign2D], outputs := #[2] }

def stepWrite2D : StateWriteMap :=
  { outputSlot := 2, stateIndex := 0
  , map := { coeffs := #[#[1, 0], #[0, 1]], bias := #[1, 1] } }

def scanOff : RawScanPlan :=
  { states := #[state2D]
  , baseBlock := base2D, baseCaptures := #[{ inputSlot := 0, source := .external 0 }]
  , baseWrites := #[baseWriteOff]
  , stepBlock := step2D
  , stepCaptures := #[{ inputSlot := 0, source := .external 1 }
                     , { inputSlot := 1, source := .state 0 }]
  , stepWrites := #[stepWrite2D]
  , historyExtents := #[3, 3]
  , iterationOrder := .axisZeroFastest, boundaryPolicy := .zeroThenBaseOverlay
  , snapshotPolicy := .immutablePreStep }

def store2D : Array DenseTensor :=
  #[ { shape := [], data := #[7.0] }
   , { shape := [3, 3], data := Array.replicate 9 1.0 }
   , { shape := [3, 3], data := Array.replicate 9 0.0 } ]

def probe (label : String) (p : RawScanPlan) : String :=
  match checkScanPlan sigs2D p with
  | .error e => s!"{label}: checkScanPlan REJECTED: {repr e}"
  | .ok c => match runDenseScan sigs2D c store2D with
    | .error e => s!"{label}: checkScanPlan .ok; runDenseScan error: {repr e}"
    | .ok out => s!"{label}: checkScanPlan .ok; dp = {repr (out.getD 2 default).data}"

#eval probe "S14 (base write off the boundary of advancing dim 1)" scanOff

-- Control: pin dim1 to 2 (the far end of a size-3 advancing dim) — still in range.
def farMap : AffineMap := { coeffs := #[#[], #[]], bias := #[0, 2] }
#eval probe "S14b (base write pinned to the FAR end of advancing dim 1)"
  { scanOff with baseWrites := #[{ baseWriteOff with map := farMap }] }

-- Control: pin dim1 to 3 (out of range) — must be rejected.
def oorMap : AffineMap := { coeffs := #[#[], #[]], bias := #[0, 3] }
#eval probe "S14c (base write pinned OUT of range on advancing dim 1)"
  { scanOff with baseWrites := #[{ baseWriteOff with map := oorMap }] }

/-! ## S15 — `LHSSlot.outExtent` / `outIdx` / `toReadIdx` / `slotsBecomeScatter` -/

def axI : AxisSpec := { name := "i", uid := 1, kind := .nat }
def axJ : AxisSpec := { name := "j", uid := 2, kind := .nat }

def sz : UID → Option Nat := fun u => if u == 1 then some 4 else if u == 2 then some 3 else none

-- the four extent conventions, side by side
#eval ( LHSSlot.outExtent (.free axI) sz            -- .axis  -> size
      , LHSSlot.outExtent (.iterAt axI 5) sz        -- .const -> n+1
      , LHSSlot.outExtent (.iterNext axI) sz        -- .shift -> size + 1
      , LHSSlot.outExtent (.affine (.scale 2 axI)) sz          -- .scale -> c * size
      , LHSSlot.outExtent (.affine (.affine 1 [(2, axI)])) sz ) -- .affine -> c0 + c*size

-- NEGATIVE affine forms: every one collapses to extent 0 through `Int.toNat`, with no rejection.
#eval ( LHSSlot.outExtent (.iterAt axI (-5)) sz                  -- (-5+1).toNat
      , LHSSlot.outExtent (.affine (.scale (-2) axI)) sz         -- (-2*4).toNat
      , LHSSlot.outExtent (.affine (.shift axI (-9))) sz         -- (4-9).toNat
      , LHSSlot.outExtent (.affine (.affine (-100) [(1, axI)])) sz )

-- an unsized axis is `none` (fail-loud) — contrast with the negative cases above
#eval ( LHSSlot.outExtent (.free { name := "k", uid := 9, kind := .nat }) sz
      , LHSSlot.outExtent (.affine (.affine 0 [(1, axI), (1, { name := "k", uid := 9, kind := .nat })])) sz )

-- toReadIdx: the `.affine => none` arm (defect instance 5's home)
#eval ( (LHSSlot.toReadIdx (.free axI)).isSome
      , (LHSSlot.toReadIdx (.freeNorm axI)).isSome
      , (LHSSlot.toReadIdx (.iterAt axI 0)).isSome
      , (LHSSlot.toReadIdx (.iterNext axI)).isSome
      , (LHSSlot.toReadIdx (.affine (.scale 2 axI))).isSome )

-- slotsBecomeScatter: which slot lists route to scatter
#eval ( slotsBecomeScatter [.free axI, .free axJ]
      , slotsBecomeScatter [.free axI, .free axI]
      , slotsBecomeScatter [.free axI, .freeNorm axI]
      , slotsBecomeScatter [.affine (.scale 2 axI)]
      , slotsBecomeScatter [.iterNext axI, .free axJ]
      , slotsBecomeScatter [.iterAt axI 0, .iterAt axI 1] )

end LeanNCD.Eval.Plan.AxisBProbe2

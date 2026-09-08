/-
Axis B / Task B1 construction spikes — write-geometry predicate surface.
FINDINGS-ONLY. Not in lakefile.toml, not in any default target.
Run with:  lake env lean spikes/AxisBWriteGeometryProbe.lean
-/
import LeanNCD.Eval.Plan.Scan

namespace LeanNCD.Eval.Plan.AxisBProbe
open LeanNCD.Eval.Plan

/-! ## S1 — `classifyWriteRow` cannot emit `.advancing` at `contextWidth = 0` -/

-- advancing-shaped row (single 1, bias 1) at base width 0
#eval (classifyWriteRow 0 #[1] 1, classifyWriteRow 0 #[1, 0] 1, classifyWriteRow 0 #[0, 1] 1)
-- same rows at step width 2
#eval (classifyWriteRow 2 #[1, 0] 1, classifyWriteRow 2 #[0, 1] 1)

/-! ## S2 — `baseWriteRowsOk` ADMITS a hand-built `.advancing` row (candidate gap 1) -/

-- state rank 2, both dims advancing, scalar output. dim0 = .pinned 0 satisfies clause 3;
-- dim1 = .advancing 0 is dropped by clause 2's filterMap and inspected by nothing.
#eval baseWriteRowsOk #[0, 1] 0 #[some (.pinned 0), some (.advancing 0)]
-- the same row shape at a NON-advancing dim (advancingDims = #[0] only, rank 2, scalar output)
#eval baseWriteRowsOk #[0] 0 #[some (.pinned 0), some (.advancing 0)]
-- and `.pinned` at a non-advancing dim with an arbitrary literal
#eval baseWriteRowsOk #[0] 0 #[some (.pinned 0), some (.pinned 99)]

/-! ## S3 — `stepWriteRowsOk` (the FIXED predicate) rejects all off-canonical placements -/

#eval ( stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.advancing 0)]  -- advancing @ non-adv
      , stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.pinned 0)]     -- pinned @ non-adv
      , stepWriteRowsOk #[0] 1 #[some (.pinned 0),    some (.free 0)]       -- pinned @ adv
      , stepWriteRowsOk #[0] 1 #[some (.free 0),      some (.free 1)]       -- free @ adv
      , stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.free 0)]       -- canonical
      , stepWriteRowsOk #[0, 1] 0 #[some (.advancing 1), some (.advancing 0)] )  -- swapped ctx pos

/-! ## S4 — the two value predicates are blind outside their own kind -/

-- freeExtentsAgree ignores .pinned and .advancing entirely (outputShape #[9] vs state #[3,3])
#eval freeExtentsAgree #[3, 3] #[9] #[some (.pinned 0), some (.advancing 0)]
-- pinnedLiteralsInRange ignores .free and .advancing entirely
#eval pinnedLiteralsInRange #[3, 3] #[some (.free 7), some (.advancing 9)]
-- but each DOES constrain its own kind
#eval ( freeExtentsAgree #[3, 3] #[9] #[some (.pinned 0), some (.free 0)]
      , pinnedLiteralsInRange #[3, 3] #[some (.pinned 0), some (.pinned 5)]
      , pinnedLiteralsInRange #[3, 3] #[some (.pinned 0), some (.pinned (-1))] )

/-! ## S5 — `writesCollide` is asymmetric in its argument LENGTHS -/

-- A shorter first argument stops the scan early: dim 1 pins 0 vs 1 and would separate them.
#eval ( writesCollide #[some (.pinned 0)] #[some (.pinned 0), some (.pinned 1)]
      , writesCollide #[some (.pinned 0), some (.pinned 1)] #[some (.pinned 0)] )
-- .free / .advancing / none can never separate two writes
#eval ( writesCollide #[some (.free 0)] #[some (.free 0)]
      , writesCollide #[some (.advancing 0)] #[some (.advancing 0)]
      , writesCollide #[none] #[none] )

/-! ## S6 — `writeRowKinds` pads a SHORT coeffs/bias array into `.pinned 0` rows -/

-- rank 3 requested, one coeff row supplied: dims 1,2 become `.pinned 0` out of thin air.
def shortWrite : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[1]], bias := #[0] } }

#eval writeRowKinds 3 0 shortWrite

-- rank 1 requested, three coeff rows supplied: rows 1,2 silently dropped.
def longWrite : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0
  , map := { coeffs := #[#[1], #[1], #[1]], bias := #[0, 0, 0] } }

#eval writeRowKinds 1 0 longWrite

/-! ## S7 — coeff-row WIDTH (candidate gap 2), predicate level -/

-- contextWidth 1, declared output rank 0 => real iteration domain width 1.
-- A 4-wide advancing row: single 1 at p=0 < contextWidth, bias 1.
#eval classifyWriteRow 1 #[1, 0, 0, 0] 1
-- A 4-wide row whose single 1 sits at p=3, i.e. OUTSIDE the real domain, bias 0.
#eval classifyWriteRow 1 #[0, 0, 0, 1] 0
-- ... and whether the geometry predicates accept that free position
#eval ( stepWriteRowsOk #[0] 0 #[some (.free 2)]
      , stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.free 2)]
      , baseWriteRowsOk  #[0] 1 #[some (.pinned 0),   some (.free 2)] )

-- applyAffine's own truncation behaviour on an over-wide / under-wide row
def wideMap : AffineMap := { coeffs := #[#[1, 0, 0, 0]], bias := #[1] }
def narrowMap : AffineMap := { coeffs := #[#[1]], bias := #[1] }

#eval (applyAffine wideMap [(2 : Int)], applyAffine narrowMap [(2 : Int), 5, 7])

/-! ## S8 — full-plan construction: free row at an ADVANCING dim in a base write -/

-- Outer slots: 0 = ROWFACE (shape [3]), 1 = T (shape [3,3]), 2 = dp (shape [3,3]).
def sigs2D : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }
   , { shape := #[3, 3], dtype := .f64 }
   , { shape := #[3, 3], dtype := .f64 } ]

-- BOTH dims advancing (2-axis scan), so the base write's free row sits at advancing dim 1.
def state2D : StateSlot :=
  { destSlot := 2, advancingDims := #[0, 1], materialization := .completeHistory }

def base2D : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[{ shape := #[3], dtype := .f64 }]
  , inputs := #[0], steps := #[], outputs := #[0] }

-- dp[0, c] := ROWFACE[c] — dim0 pinned to 0, dim1 (ADVANCING) free.
def baseWrite2D : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[0], #[1]], bias := #[0, 0] } }

def baseRows2D : Array (Option WriteRowKind) := writeRowKinds 2 0 baseWrite2D

#eval (baseRows2D, baseWriteRowsOk #[0, 1] 1 baseRows2D, freeExtentsAgree #[3,3] #[3] baseRows2D)

-- Step block: dp[r+1, c+1] := T[r, c]; context width 2 (stepExtents #[2,2]), scalar output.
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

def scan2D : RawScanPlan :=
  { states := #[state2D]
  , baseBlock := base2D, baseCaptures := #[{ inputSlot := 0, source := .external 0 }]
  , baseWrites := #[baseWrite2D]
  , stepBlock := step2D
  , stepCaptures := #[{ inputSlot := 0, source := .external 1 }
                     , { inputSlot := 1, source := .state 0 }]
  , stepWrites := #[stepWrite2D]
  , historyExtents := #[3, 3]
  , iterationOrder := .axisZeroFastest, boundaryPolicy := .zeroThenBaseOverlay
  , snapshotPolicy := .immutablePreStep }

def store2D : Array DenseTensor :=
  #[ { shape := [3], data := #[1.0, 2.0, 3.0] }
   , { shape := [3, 3], data := Array.replicate 9 1.0 }
   , { shape := [3, 3], data := Array.replicate 9 0.0 } ]

def probe (label : String) (p : RawScanPlan) : String :=
  match checkScanPlan sigs2D p with
  | .error e => s!"{label}: checkScanPlan REJECTED: {repr e}"
  | .ok c => match runDenseScan sigs2D c store2D with
    | .error e => s!"{label}: checkScanPlan .ok; runDenseScan error: {repr e}"
    | .ok out => s!"{label}: checkScanPlan .ok; dp = {repr (out.getD 2 default).data}"

#eval probe "S8 (free row at advancing dim, base)" scan2D

/-! ## S9 — full-plan construction: an OVER-WIDE base coeff row (candidate gap 2) -/

-- Same plan, but the base write's rows are 4 wide (real base domain width = outputShape.size = 1).
def wideBaseMap : AffineMap := { coeffs := #[#[0, 0, 0, 0], #[1, 0, 0, 0]], bias := #[0, 0] }
def baseWrite2DWide : StateWriteMap := { baseWrite2D with map := wideBaseMap }

#eval writeRowKinds 2 0 baseWrite2DWide
#eval probe "S9 (over-wide base coeff rows)" { scan2D with baseWrites := #[baseWrite2DWide] }

-- And a base row whose single 1 sits OUTSIDE the real domain (p = 3, domain width 1).
def outBaseMap : AffineMap := { coeffs := #[#[0, 0, 0, 0], #[0, 0, 0, 1]], bias := #[0, 0] }
def baseWrite2DOut : StateWriteMap := { baseWrite2D with map := outBaseMap }

#eval writeRowKinds 2 0 baseWrite2DOut
#eval probe "S9b (base coeff 1 outside the real domain)" { scan2D with baseWrites := #[baseWrite2DOut] }

/-! ## S10 — an over-wide STEP coeff row (contextWidth 2, domain width 2) -/

def wideStepMap : AffineMap := { coeffs := #[#[1, 0, 0, 0, 0], #[0, 1, 0, 0, 0]], bias := #[1, 1] }
def stepWrite2DWide : StateWriteMap := { stepWrite2D with map := wideStepMap }

#eval writeRowKinds 2 2 stepWrite2DWide
#eval probe "S10 (over-wide step coeff rows)" { scan2D with stepWrites := #[stepWrite2DWide] }

/-! ## S11 — can an `.advancing`-SHAPED base row reach `checkScanPlan .ok`? (candidate gap 1) -/

-- dim0 row: single 1 at p=0, bias 1 — the advancing shape, at base width 0.
def advBaseMap : AffineMap := { coeffs := #[#[1], #[1]], bias := #[1, 0] }
def baseWrite2DAdv : StateWriteMap := { baseWrite2D with map := advBaseMap }

#eval writeRowKinds 2 0 baseWrite2DAdv
#eval probe "S11 (advancing-shaped base row)" { scan2D with baseWrites := #[baseWrite2DAdv] }

/-! ## S12 — coefficients other than 1, and two nonzeros (the shapes B2's affine LHS will need) -/

#eval ( classifyWriteRow 0 #[2] 0        -- stride 2, base
      , classifyWriteRow 0 #[1, 1] 0     -- two nonzeros
      , classifyWriteRow 2 #[2, 0] 1     -- stride 2 at a context position
      , classifyWriteRow 0 #[1] 5 )      -- coefficient 1, arbitrary bias, base

/-! ## S13 — `rows.size` vs `stateRank`: what the standalone predicates do off-contract -/

-- advancingDims naming a dim BEYOND rows.size: `rows.getD d none` yields `none`.
#eval ( baseWriteRowsOk #[5] 1 #[some (.free 0)]
      , stepWriteRowsOk #[5] 1 #[some (.free 0)]
      , freeExtentsAgree #[3] #[3, 3, 3] #[some (.free 0), some (.free 1), some (.free 2)]
      , pinnedLiteralsInRange #[] #[some (.pinned 0)] )

end LeanNCD.Eval.Plan.AxisBProbe

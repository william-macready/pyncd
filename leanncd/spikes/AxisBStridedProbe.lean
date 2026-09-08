/-
Axis B / Task B2 construction spikes, part 1 — the `strided` row kind across the write-geometry
surface. FINDINGS-ONLY. Not in lakefile.toml, not in any default target.
Run with:  lake env lean spikes/AxisBStridedProbe.lean

Probes S17-S22. No production code is changed and NO `strided` constructor is added: every probe
below runs the REAL `classifyWriteRow`/`writeRowKinds`/`baseWriteRowsOk`/`stepWriteRowsOk`/
`freeExtentsAgree`/`pinnedLiteralsInRange`/`writesCollide`/`applyAffine`/`inBoundsPerDim`/
`flatIndex`/`LHSSlot.outExtent` over hand-built `AffineMap`s and row arrays.

Imports `LeanNCD.Eval.Plan.Scan` only (NOT the `LeanNCD` umbrella): `LeanNCD/DSL/Syntax.lean`
declares `"bias"` as a syntax token, which makes `{ coeffs := …, bias := … }` a parse error in any
file importing the umbrella. S22 additionally checks what this single import makes visible.
-/
import LeanNCD.Eval.Plan.Scan

namespace LeanNCD.Eval.Plan.AxisBProbe3
open LeanNCD.Eval.Plan

/-! ## S17 — the three strided coefficient/bias shapes, through the REAL `classifyWriteRow`

The `AffineMap` rows a strided write comes from, one per `LHSSlot.outExtent` arm that produces
them, asked at base width 0 and at step width 2 (with the nonzero in the OUTPUT half both times).
Every one is `none` today — this is fact 1 (`classifyWriteRow` is the single chokepoint), stated
over the exact shapes the affine-LHS feature must admit rather than over B1's generic `#[2]`. -/

-- `.scale 2 a`      => coefficient 2, bias 0
-- `.shift a 3`      => coefficient 1, bias 3
-- `.affine 3 [(2,a)]` => coefficient 2, bias 3
#eval ( classifyWriteRow 0 #[2] 0          -- scale, base
      , classifyWriteRow 0 #[1] 3          -- shift, base
      , classifyWriteRow 0 #[2] 3 )        -- affine, base

#eval ( classifyWriteRow 2 #[0, 0, 2] 0    -- scale, step, nonzero in the OUTPUT half (p = 2 ≥ 2)
      , classifyWriteRow 2 #[0, 0, 1] 3    -- shift, step
      , classifyWriteRow 2 #[0, 0, 2] 3 )  -- affine, step

-- The `.shift a 1` collision: coefficient 1 WITH bias 1 is `.advancing` when the nonzero sits in
-- the CONTEXT half and `none` today when it sits in the output half. A strided branch placed
-- BEFORE the advancing branch would shadow `.advancing` entirely; placed after, it must still be
-- guarded on `p ≥ contextWidth` or it re-admits the same row under a second name.
#eval ( classifyWriteRow 0 #[1] 1          -- base: no context half exists at all
      , classifyWriteRow 2 #[1, 0, 0] 1    -- step, p = 0 < 2  => .advancing 0
      , classifyWriteRow 2 #[0, 0, 1] 1 )  -- step, p = 2 ≥ 2  => none today

-- A two-nonzero row (`.affine 0 [(1,a),(1,b)]`, i.e. `Out[i + j]`) stays `none` even with the
-- minimal single-`outputPos` strided kind: `classifyWriteRow`'s `| _ => none` arm matches on the
-- LENGTH of the nonzero list, which a one-position strided constructor cannot extend.
#eval ( classifyWriteRow 0 #[1, 1] 0
      , classifyWriteRow 0 #[2, 3] 5
      , classifyWriteRow 2 #[0, 0, 1, 1] 0 )

/-! ## S18 — a strided-shaped BASE write through the real entry, today

Same plan family as B1's S8-S11 (rank-2 `dp`, both dims advancing), with the base write's dim-1 row
carrying coefficient 2. Today `writeRowKinds` yields `none` there and clause 1 of
`baseWriteRowsOk` (`rows.all Option.isSome`) fires. -/

def sigs2D : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }
   , { shape := #[3, 3], dtype := .f64 }
   , { shape := #[3, 3], dtype := .f64 } ]

def state2D : StateSlot :=
  { destSlot := 2, advancingDims := #[0, 1], materialization := .completeHistory }

def base2D : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[{ shape := #[3], dtype := .f64 }]
  , inputs := #[0], steps := #[], outputs := #[0] }

-- dp[0, c] := ROWFACE[c] — the ADMITTED control (B1's S8 shape).
def baseWrite2D : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[0], #[1]], bias := #[0, 0] } }

-- dp[0, 2*c] := ROWFACE[c] — the strided base write the affine-LHS feature must lower.
def stridedBaseMap : AffineMap := { coeffs := #[#[0], #[2]], bias := #[0, 0] }
def baseWrite2DStrided : StateWriteMap := { baseWrite2D with map := stridedBaseMap }

#eval writeRowKinds 2 0 baseWrite2DStrided
#eval baseWriteRowsOk #[0, 1] 1 (writeRowKinds 2 0 baseWrite2DStrided)

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

#eval probe "S18 (strided-shaped base row, coefficient 2)"
  { scan2D with baseWrites := #[baseWrite2DStrided] }

-- The `.shift`-flavoured strided base row (coefficient 1, bias 5) reaches the same clause.
def shiftBaseMap : AffineMap := { coeffs := #[#[0], #[1]], bias := #[0, 5] }
#eval writeRowKinds 2 0 { baseWrite2D with map := shiftBaseMap }
#eval probe "S18b (strided-shaped base row, coefficient 1 bias 5)"
  { scan2D with baseWrites := #[{ baseWrite2D with map := shiftBaseMap }] }

/-! ## S19 — `baseWriteRowsOk` clause 2's `filterMap` on a non-`.free` `some` row

The clause is
  `(rows.toList.filterMap (fun r => match r with | some (.free p) => some p | _ => none))
     == List.range outputShapeSize`
whose `| _ => none` arm is CONSTRUCTOR-BLIND: it drops every `some` row that is not `.free`,
including a fourth constructor that does not exist yet. Measured with the two non-`.free`
constructors that DO exist, at exactly the parameters B1's fact-2 shape names — rank-3 state,
`outputShapeSize = 1`, dim0 `.pinned 0` satisfying clause 3, dim1 the row under test, dim2
`.free 0` supplying the whole cover. -/

#eval ( baseWriteRowsOk #[0] 1 #[some (.pinned 0), some (.pinned 2),   some (.free 0)]
      , baseWriteRowsOk #[0] 1 #[some (.pinned 0), some (.advancing 0), some (.free 0)]
      , baseWriteRowsOk #[0, 1] 1 #[some (.pinned 0), some (.pinned 2),   some (.free 0)]
      , baseWriteRowsOk #[0, 1] 1 #[some (.pinned 0), some (.advancing 0), some (.free 0)] )

-- Control: the SAME shape with a second `.free` at dim1 does NOT pass — a genuine `.free` row is
-- counted into the cover and breaks it, which is precisely what being dropped avoids.
#eval ( baseWriteRowsOk #[0] 1 #[some (.pinned 0), some (.free 1), some (.free 0)]
      , baseWriteRowsOk #[0] 1 #[some (.pinned 0), some (.free 0), some (.free 0)] )

-- And the two value predicates at those parameters: both `| _ => true` outside their own kind.
#eval ( freeExtentsAgree #[1, 3, 3] #[3] #[some (.pinned 0), some (.advancing 0), some (.free 0)]
      , freeExtentsAgree #[1, 1, 3] #[3] #[some (.pinned 0), some (.advancing 0), some (.free 0)]
      , pinnedLiteralsInRange #[1, 3, 3] #[some (.pinned 0), some (.advancing 0), some (.free 0)] )

-- `stepWriteRowsOk` at the same rows, both dimension classes: clause 2 (advancing dims must be
-- `.advancing i`) and clause 3 (every other dim must be `.free`) each reject a non-`.free`
-- non-`.advancing` row IN THE STEP PHASE, where they actually run.
#eval ( stepWriteRowsOk #[0, 1] 1 #[some (.pinned 0), some (.pinned 2), some (.free 0)]
      , stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.pinned 2), some (.free 0)]
      , stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.free 0), some (.free 1)] )

-- `writesCollide`'s catch-all `| _, _ => false` (fact 3), over the non-`.pinned` constructors.
#eval ( writesCollide #[some (.free 0)] #[some (.free 0)]
      , writesCollide #[some (.advancing 0)] #[some (.pinned 1)]
      , writesCollide #[some (.pinned 0), some (.advancing 0)]
                      #[some (.pinned 0), some (.pinned 1)] )

/-! ## S20 — what `commitWrite`'s arithmetic does with a strided BASE coordinate

`commitWrite` calls NO `inBoundsPerDim` before `flatIndex` (its own docstring says so). At base
`ctx = []`, so `iter = oc`. The map below is the rank-3 fact-2 shape with dim1 STRIDED:
`dp[0, 2*oc0, oc0] := out[oc0]` on a `[1,3,3]` state, output shape `[3]`. -/

def stridedAtBaseMap : AffineMap :=
  { coeffs := #[#[0], #[2], #[1]], bias := #[0, 0, 0] }

#eval writeRowKinds 3 0 { outputSlot := 0, stateIndex := 0, map := stridedAtBaseMap }

#eval ( applyAffine stridedAtBaseMap [(0 : Int)]
      , applyAffine stridedAtBaseMap [(1 : Int)]
      , applyAffine stridedAtBaseMap [(2 : Int)] )

#eval ( inBoundsPerDim [1, 3, 3] (applyAffine stridedAtBaseMap [(0 : Int)])
      , inBoundsPerDim [1, 3, 3] (applyAffine stridedAtBaseMap [(1 : Int)])
      , inBoundsPerDim [1, 3, 3] (applyAffine stridedAtBaseMap [(2 : Int)]) )

-- The flat addresses `flatIndex` would hand to `Array.set!` on a 9-element store.
#eval ( flatIndex [1, 3, 3] ((applyAffine stridedAtBaseMap [(0 : Int)]).map Int.toNat)
      , flatIndex [1, 3, 3] ((applyAffine stridedAtBaseMap [(1 : Int)]).map Int.toNat)
      , flatIndex [1, 3, 3] ((applyAffine stridedAtBaseMap [(2 : Int)]).map Int.toNat) )

-- The `.shift`-flavoured variant, `dp[0, oc0 + 5, oc0]`: out of range at EVERY coordinate.
def shiftAtBaseMap : AffineMap :=
  { coeffs := #[#[0], #[1], #[1]], bias := #[0, 5, 0] }

#eval ( applyAffine shiftAtBaseMap [(0 : Int)]
      , inBoundsPerDim [1, 3, 3] (applyAffine shiftAtBaseMap [(0 : Int)])
      , flatIndex [1, 3, 3] ((applyAffine shiftAtBaseMap [(0 : Int)]).map Int.toNat) )

-- A NEGATIVE strided coordinate: `Int.toNat` collapses it to 0, so a negative offset aliases
-- silently onto the lower boundary instead of failing.
def negAtBaseMap : AffineMap :=
  { coeffs := #[#[0], #[1], #[1]], bias := #[0, -2, 0] }

#eval ( applyAffine negAtBaseMap [(0 : Int)]
      , inBoundsPerDim [1, 3, 3] (applyAffine negAtBaseMap [(0 : Int)])
      , ((applyAffine negAtBaseMap [(0 : Int)]).map Int.toNat)
      , flatIndex [1, 3, 3] ((applyAffine negAtBaseMap [(0 : Int)]).map Int.toNat) )

/-! ## S21 — `LHSSlot.outExtent`'s arms vs the checked-plan row kinds

`LHSSlot.outIdx` is total over all five `LHSSlot` constructors and `IdxExpr` has exactly five
constructors, so `outExtent`'s five arms are exhaustive over its own input. Which arm is which
checked-plan row kind's image, measured at `size(i) = 4`:

  `.axis a`      <- `.free`/`.freeNorm`            -> checked `.free`      (coeff 1, bias 0)
  `.const n`     <- `.iterAt a n`                  -> checked `.pinned n`  (all-zero row, bias n)
  `.shift a 1`   <- `.iterNext a`                  -> checked `.advancing` (coeff 1, bias 1)
  `.shift a c`   <- `.affine (.shift a c)`, c≠1     -> STRIDED (scale 1, offset c)
  `.scale c a`   <- `.affine (.scale c a)`          -> STRIDED (scale c, offset 0)
  `.affine c0 [(c,a)]` <- `.affine (.affine ..)`    -> STRIDED (scale c, offset c0)
  `.affine c0 xs`, |xs| ≥ 2                         -> NO checked image (S17's two-nonzero row) -/

def axI : AxisSpec := { name := "i", uid := 1, kind := .nat }
def axJ : AxisSpec := { name := "j", uid := 2, kind := .nat }
def sz : UID → Option Nat := fun u => if u == 1 then some 4 else if u == 2 then some 3 else none

#eval ( LHSSlot.outExtent (.free axI) sz                              -- .axis   -> 4
      , LHSSlot.outExtent (.iterAt axI 5) sz                          -- .const  -> 6
      , LHSSlot.outExtent (.iterNext axI) sz                          -- .shift 1 -> 5
      , LHSSlot.outExtent (.affine (.shift axI 3)) sz                 -- .shift 3 -> 7
      , LHSSlot.outExtent (.affine (.scale 2 axI)) sz                 -- .scale   -> 8
      , LHSSlot.outExtent (.affine (.affine 3 [(2, axI)])) sz )       -- .affine  -> 11

-- `.iterNext` and a `.shift a 1` affine slot are the SAME `outIdx`, hence the same extent — the
-- surface-level sibling of S17's advancing/strided coefficient collision.
#eval ( LHSSlot.outIdx (.iterNext axI) == LHSSlot.outIdx (.affine (.shift axI 1))
      , LHSSlot.outExtent (.iterNext axI) sz == LHSSlot.outExtent (.affine (.shift axI 1)) sz )

-- The two-axis affine form has an extent but no checked-plan row image (S17).
#eval ( LHSSlot.outExtent (.affine (.affine 0 [(1, axI), (1, axJ)])) sz
      , LHSSlot.outIdx (.affine (.affine 0 [(1, axI), (1, axJ)])) )

-- The synthetic-`AxisSpec` adapter a positional checked-plan site would need in order to CALL
-- `outExtent` instead of copying it: `outExtent` takes an `LHSSlot` plus a `UID → Option Nat`,
-- neither of which the checked plan has, but a fabricated `AxisSpec` whose looked-up size IS the
-- block output's extent reproduces the number exactly.
def synthetic (outputExtent : Nat) : (UID → Option Nat) :=
  fun u => if u == 0 then some outputExtent else none
def syntheticAxis : AxisSpec := { name := "_out", uid := 0, kind := .nat }

-- output extent 3, scale 2, offset 0 => the state dimension a strided row needs is 6.
#eval ( LHSSlot.outExtent (.affine (.scale 2 syntheticAxis)) (synthetic 3)
      , LHSSlot.outExtent (.affine (.shift syntheticAxis 3)) (synthetic 3)
      , LHSSlot.outExtent (.affine (.affine 3 [(2, syntheticAxis)])) (synthetic 3) )

-- ... versus the number `freeExtentsAgree` actually compares against (`outputShape.getD p 0`).
#eval ( freeExtentsAgree #[6, 3] #[3] #[some (.free 0), some (.free 0)]
      , freeExtentsAgree #[3, 3] #[3] #[some (.free 0), some (.free 0)] )

/-! ## S22 — is `LHSSlot.outExtent` even VISIBLE from the checked-plan subtree?

Every `#eval` in S21 compiled under `import LeanNCD.Eval.Plan.Scan` ALONE (B1's S15 imported
`LeanNCD.DSL.Ast` explicitly; this file does not). `Eval/Plan/Kernel.lean` imports
`LeanNCD.DSL.Ast`, and `Scan.lean` reaches it transitively via `Block -> Dense -> Check ->
Error -> Kernel`. So the obstruction to `Scan.lean` calling the shared formula is the ARGUMENT
VOCABULARY (an `LHSSlot` and a UID-keyed sizing lookup, in a positional UID-free IR), not the
import graph. -/

#eval (LHSSlot.outExtent (.affine (.scale 2 axI)) sz).isSome

end LeanNCD.Eval.Plan.AxisBProbe3

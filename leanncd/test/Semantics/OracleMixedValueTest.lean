import Semantics.OracleMixedDifferential

/-! Oracle sorts T4: value rows for `compareMixedSource` on the ACCEPTED path (the predictor says the
program is accepted, production accepts it, both native legs run), the mixed numerical profile, and
the non-finite class.

Every accepted row asserts three things, so none is vacuous: the classification is `fourLegParity`
(oracle, Core, legacy and checked agree; Core runs per target, stratified), the oracle's own and the
Core leg's own cells equal hand-derived values, and the sort each statement RAN in (the predictor's
`stmtSorts`). The only rows that stay `threeLegParity "core not run: non-finite intermediate"` are
those where a later statement reads an earlier tropical cell that was never written (`-inf`/`+inf`):
Core inputs are rationals, so the Core leg stops there (`MixedRun.core` is `none`; the targets it ran
before stopping are `MixedRun.corePrefix`, compared with the oracle). Values are derived from the inputs of
`Semantics.OracleMixedFixtures` (`X=[20,2,3,40]`, `Z` rows `[-5,-4,-3] [5,6,7] [15,16,17] [25,26,27]`,
`B=Q` rows `[1,9,2] [3,8,4] [7,5,6] [0,10,11]`), not copied from production. -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open Debug Oracle NativeLegs SortedDifferential LeanNCD.OracleSorts OracleMixed

namespace OracleMixedValueTest

/-- A fixture: the snapshot and the original-declaration order of its non-input tensors. -/
private structure Fx where
  snap : SourceSnapshot
  order : List Nat

private def fx (ts : List T) (stmts : List Stmt) : Fx := ⟨mk ts stmts, orderOf ts⟩

private def run (f : Fx) : Except String MixedRun :=
  (compareMixedSource f.snap (some f.order)).mapError (fun d => s!"refused {repr d.cause}")

private def classOf (f : Fx) : String :=
  match run f with
  | .ok r => toString (repr r.classification)
  | .error e => e

private def four : String := "OracleMixed.MixedClassification.fourLegParity"

/-- The classification of a row whose Core leg stopped at a blocked target: an earlier cell it needs
is non-finite, and Core inputs are rationals. (The note string says "not run" for historical reasons;
the targets before the blocked one did run and are compared as the Core prefix.) -/
private def threeNotRun : String :=
  "OracleMixed.MixedClassification.threeLegParity \"core not run: non-finite intermediate\""

/-- Is the classification any parity (three- or four-leg)? -/
private def isParityClass (f : Fx) : Bool :=
  match run f with
  | .ok r => match r.classification with
    | .threeLegParity _ | .fourLegParity => true
    | _ => false
  | .error _ => false

/-- The cells of the tensor named `n` in a list of observations. -/
private def cellsIn (ts : List (TensorObservation ExtVal)) (n : String) : Option (List ExtVal) :=
  (ts.find? (·.name == some n)).map (fun t => t.values.filterMap id)

/-- The oracle's cells of the tensor named `n`. -/
private def cellsOf (f : Fx) (n : String) : Option (List ExtVal) :=
  match run f with
  | .ok r =>
    match r.oracle with
    | .ok ts => cellsIn ts n
    | .error _ => none
  | .error _ => none

/-- The Core leg's cells of the tensor named `n` (`none` when the Core leg was not run or failed). -/
private def coreCellsOf (f : Fx) (n : String) : Option (List ExtVal) :=
  match run f with
  | .ok r =>
    match r.core with
    | some (.ok ts) => cellsIn ts n
    | _ => none
  | .error _ => none

/-- Did the Core leg not complete (`MixedRun.core` is `none`, as opposed to run and failed)? -/
private def coreNotRun (f : Fx) : Bool :=
  match run f with
  | .ok r => r.core.isNone
  | .error _ => false

private def fins (qs : List ℚ) : List ExtVal := qs.map .fin

/-- Both legs are `.unavailable` (the profile errored, so no bits were compared). -/
private def legsUnavailable (f : Fx) : Bool :=
  match run f with
  | .ok r => match r.legacy, r.checked with
    | .unavailable, .unavailable => true
    | _, _ => false
  | .error _ => false

/-- Both legs agree with the oracle bit for bit (a real comparison, not an absent one). -/
private def legsAgree (f : Fx) : Bool :=
  match run f with
  | .ok r => match r.legacy, r.checked with
    | .agrees, .agrees => true
    | _, _ => false
  | .error _ => false

/-- An accepted row: `fourLegParity`, legs agreeing, and both the oracle's and the Core leg's own cells
of `n` equal `qs` (so the Core leg really ran and produced them). -/
private def parity (f : Fx) (n : String) (qs : List ℚ) : Bool :=
  classOf f == four && legsAgree f && cellsOf f n == some (fins qs) && coreCellsOf f n == some (fins qs)

/-- The sorts the statements RAN in (the predictor's, aligned with the statement list). -/
private def ranIn (f : Fx) : Option (List MSort) :=
  match run f with
  | .ok r => some r.prediction.stmtSorts
  | .error _ => none

/-! ### Mixed Bellman programs: a contraction beside a bare copy, both orders -/

private def contY (agg : AggOp) : Stmt := st "Y" agg (rd "Z" [axA, axB])
private def termY (agg : AggOp) : Stmt := st "Y" agg (rd "X" [axA])
private def bellman (s1 s2 : AggOp) : Fx := fx [tX, tZ, tOut "Y"] [contY s1, termY s2]
private def bellmanRev (s1 s2 : AggOp) : Fx := fx [tX, tZ, tOut "Y"] [termY s2, contY s1]

-- homogeneous control (the typed path says `fourLegParity`; here too it is `fourLegParity`)
#guard parity (bellman .max .max) "Y" [20, 7, 17, 40]
#guard ranIn (bellman .max .max) == some [.maxPlus, .maxPlus]

-- a max contraction beside a sum copy and beside a min copy: the group is max-plus
#guard parity (bellman .max .sum) "Y" [20, 7, 17, 40]
#guard parity (bellmanRev .max .sum) "Y" [20, 7, 17, 40]
#guard parity (bellman .max .min) "Y" [20, 7, 17, 40]
#guard parity (bellmanRev .max .min) "Y" [20, 7, 17, 40]
-- a min contraction beside a sum copy: the group is min-plus
#guard parity (bellman .min .sum) "Y" [-5, 2, 3, 25]
#guard parity (bellmanRev .min .sum) "Y" [-5, 2, 3, 25]
-- a sum contraction beside a max copy: the group is real
#guard parity (bellman .sum .max) "Y" [8, 20, 51, 118]
#guard parity (bellmanRev .sum .max) "Y" [8, 20, 51, 118]

-- the copy RUNS in the group's sort, not its own annotation (Review Focus 1)
#guard ranIn (bellman .max .min) == some [.maxPlus, .maxPlus]
#guard ranIn (bellmanRev .max .min) == some [.maxPlus, .maxPlus]
#guard ranIn (bellman .min .sum) == some [.minPlus, .minPlus]

/-! ### R11: a neutral max/min copy beside a non-neutral writer abstains (four rows)

If neutral writers voted, the real group `[8,20,51,118]` would conflict (`multiWriterAlgebra`) and the
legs would refuse a program the predictor accepts: `refusalMismatch [] ..`, not parity. -/

#guard parity (bellman .sum .max) "Y" [8, 20, 51, 118]
#guard ranIn (bellman .sum .max) == some [.real, .real]
#guard parity (bellmanRev .sum .max) "Y" [8, 20, 51, 118]
#guard ranIn (bellmanRev .sum .max) == some [.real, .real]
#guard parity (bellman .max .sum) "Y" [20, 7, 17, 40]
#guard ranIn (bellman .max .sum) == some [.maxPlus, .maxPlus]
#guard parity (bellmanRev .max .sum) "Y" [20, 7, 17, 40]
#guard ranIn (bellmanRev .max .sum) == some [.maxPlus, .maxPlus]

/-! ### Neutral-copy chains (single writers and a group fed by an intermediate) -/

-- a single-writer neutral max copy is max-plus by its own annotation; a max reader accepts it
private def chainMaxMax : Fx :=
  fx [tX, tDef "T", tOut "O"] [st "T" .max (rd "X" [axA]), st "O" .max (rd "T" [axA])]
-- ... and a sum reader reads it by identity
private def chainMaxSum : Fx :=
  fx [tX, tDef "T", tOut "O"] [st "T" .max (rd "X" [axA]), st "O" .sum (rd "T" [axA])]
-- a min contraction feeds a group whose max copy abstains beside the non-neutral min writer
private def chainMinGroup : Fx :=
  fx [tZ, tB, tDef "N", tOut "T"]
    [st "N" .min (rd "Z" [axA, axB]), st "T" .max (rd "N" [axA]), st "T" .min (rd "B" [axA, axB])]
private def chainMinGroupRev : Fx :=
  fx [tZ, tB, tDef "N", tOut "T"]
    [st "N" .min (rd "Z" [axA, axB]), st "T" .min (rd "B" [axA, axB]), st "T" .max (rd "N" [axA])]
-- a min copy beside a sum writer runs as sum
private def minCopyBesideSum : Fx :=
  fx [tX, tZ, tOut "Y"] [contY .sum, termY .min]
-- a two-stage chain: a mixed group, then a reader of the group's result
private def chainGroupThenRead : Fx :=
  fx [tX, tZ, tDef "Y", tOut "O"] [contY .max, termY .sum, st "O" .sum (rd "Y" [axA])]

#guard parity chainMaxMax "O" [20, 2, 3, 40]
#guard ranIn chainMaxMax == some [.maxPlus, .maxPlus]
#guard parity chainMaxSum "O" [20, 2, 3, 40]
#guard ranIn chainMaxSum == some [.maxPlus, .real]
#guard parity chainMinGroup "T" [-5, 3, 5, 0]
#guard ranIn chainMinGroup == some [.minPlus, .minPlus, .minPlus]
#guard parity chainMinGroupRev "T" [-5, 3, 5, 0]
#guard parity minCopyBesideSum "Y" [8, 20, 51, 118]
#guard ranIn minCopyBesideSum == some [.real, .real]
#guard parity chainGroupThenRead "O" [20, 7, 17, 40]
#guard ranIn chainGroupThenRead == some [.maxPlus, .maxPlus, .real]

/-! ### Real <-> tropical identity reads, and the laundered form -/

private def castMax : Fx :=
  fx [tZ, tDef "M", tOut "R"] [st "M" .max (rd "Z" [axA, axB]), st "R" .sum (rd "M" [axA])]
private def castMin : Fx :=
  fx [tZ, tDef "M", tOut "R"] [st "M" .min (rd "Z" [axA, axB]), st "R" .sum (rd "M" [axA])]
private def castReal : Fx :=
  fx [tZ, tDef "S", tOut "O"] [st "S" .sum (rd "Z" [axA, axB]), st "O" .max (rd "S" [axA])]
private def castRealMin : Fx :=
  fx [tZ, tDef "S", tOut "O"] [st "S" .sum (rd "Z" [axA, axB]), st "O" .min (rd "S" [axA])]
/-- max-plus -> real copy -> min-plus: accepted (cast decision A). -/
private def launder : Fx :=
  fx [tZ, tDef "M", tDef "R", tOut "O"]
    [st "M" .max (rd "Z" [axA, axB]), st "R" .sum (rd "M" [axA]), st "O" .min (rd "R" [axA])]
/-- max-plus read by a min-plus statement: refused, so no value is compared. -/
private def castDirect : Fx :=
  fx [tZ, tDef "M", tOut "O"] [st "M" .max (rd "Z" [axA, axB]), st "O" .min (rd "M" [axA])]

#guard parity castMax "R" [-3, 7, 17, 27]
#guard ranIn castMax == some [.maxPlus, .real]
#guard parity castMin "R" [-5, 5, 15, 25]
#guard ranIn castMin == some [.minPlus, .real]
#guard parity castReal "O" [-12, 18, 48, 78]
#guard ranIn castReal == some [.real, .maxPlus]
#guard parity castRealMin "O" [-12, 18, 48, 78]
#guard ranIn castRealMin == some [.real, .minPlus]
#guard parity launder "O" [-3, 7, 17, 27]
#guard ranIn launder == some [.maxPlus, .real, .minPlus]
#guard classOf castDirect == "OracleMixed.MixedClassification.refusalParity \"sortCastUnsupported\""
-- the same chain through a single-writer neutral max copy is refused too (it is max-plus)
#guard classOf (fx [tX, tDef "T", tOut "O"] [st "T" .max (rd "X" [axA]), st "O" .min (rd "T" [axA])])
  == "OracleMixed.MixedClassification.refusalParity \"sortCastUnsupported\""

/-! ### Non-finite cells read by a real statement (D5)

`M[2*a]` writes the even cells of `M` (axis `k`, extent 8); the odd cells stay at the sort's zero
(`-inf` for max-plus, `+inf` for min-plus). A real statement reading one has no finite value to
compare, whatever the native legs print (`-inf` bits for a copy, `NaN` for `-inf * 0`): the class is
`unsupportedNumericalProfile (nonFiniteIntoReal ..)` at the first such read, never a parity row. -/

private def unwritten (agg : AggOp) (reader : AggOp) (fs : List Factor) : Fx :=
  fx [tX, tW8, tDef "M" [axK], tOut "R" [axK]]
    [zR "M" [.affine (.scale 2 axA)] agg [rd "X" [axA]], zR "R" [.free axK] reader fs]

/-- Is the classification `nonFiniteIntoReal` at the named declaration, cell `c`? -/
private def nonFiniteAt (f : Fx) (n : String) (c : List Nat) : Bool :=
  match declarationIndex f.snap n, run f with
  | some d, .ok r =>
    match r.classification with
    | .unsupportedNumericalProfile (.nonFiniteIntoReal site) =>
      site.origin.declaration == some d && site.coordinate == c
    | _ => false
  | _, _ => false

private def copyMax := unwritten .max .sum [rd "M" [axK]]
private def productMax := unwritten .max .sum [rd "M" [axK], rd "W8" [axK]]
private def copyMin := unwritten .min .sum [rd "M" [axK]]
private def copyMaxMoved : Fx :=
  fx [tX, tDef "M" [axK], tW8, tOut "R" [axK]] copyMax.snap.resolved.stmts
-- a tropical reader of the same unwritten cells is fine: `-inf` is its own value
private def maxReadsMax := unwritten .max .max [rd "M" [axK]]

-- The first unwritten cell is `[1]`, independently of `M`'s declaration position.
#guard nonFiniteAt copyMax "M" [1]
#guard nonFiniteAt productMax "M" [1]
#guard nonFiniteAt copyMin "M" [1]
#guard nonFiniteAt copyMaxMoved "M" [1]
#guard declarationIndex copyMaxMoved.snap "M" != declarationIndex copyMax.snap "M"
#guard declarationIndex copyMaxMoved.snap "missing" == none
#guard !nonFiniteAt copyMaxMoved "W8" [1]
#guard !nonFiniteAt copyMaxMoved "missing" [1]
#guard !nonFiniteAt copyMaxMoved "M" [0]
#guard !isParityClass copyMax
#guard !isParityClass productMax
#guard !isParityClass copyMin
-- the legs are `.unavailable` on these rows because the profile errored (as in the typed path's
-- `legOf`): the native bits are deliberately not compared (D5), and the Core leg is not run
#guard legsUnavailable copyMax
#guard legsUnavailable productMax
#guard legsUnavailable copyMin
#guard cellsOf maxReadsMax "R" ==
  some [.fin 20, .negInf, .fin 2, .negInf, .fin 3, .negInf, .fin 40, .negInf]
-- the Core leg does NOT complete here: `R` reads `M`'s `-inf` cells and Core inputs are rationals, so
-- it stops at `R` after running `M` (the prefix, compared below). The row
-- stays `threeLegParity` with its note, never a silent four-leg claim (Review Focus 5)
#guard classOf maxReadsMax == threeNotRun
#guard coreNotRun maxReadsMax
#guard legsAgree maxReadsMax
private def minReadsMin := unwritten .min .min [rd "M" [axK]]
#guard cellsOf minReadsMin "R" ==
  some [.fin 20, .posInf, .fin 2, .posInf, .fin 3, .posInf, .fin 40, .posInf]
#guard classOf minReadsMin == threeNotRun
#guard coreNotRun minReadsMin
#guard legsAgree minReadsMin

/-- The Core observations computed before the Core leg stopped at a blocked target (`MixedRun.corePrefix`),
for the tensor named `n`. -/
private def corePrefixOf (f : Fx) (n : String) : Option (List ExtVal) :=
  match run f with
  | .ok r => cellsIn r.corePrefix n
  | .error _ => none

-- the stopped Core leg is not discarded: the `M` it computed before it stopped is compared with the
-- oracle's `M` (the two are the same cells), and `R`, the blocked target, is not in the prefix
#guard corePrefixOf maxReadsMax "M" ==
  some [.fin 20, .negInf, .fin 2, .negInf, .fin 3, .negInf, .fin 40, .negInf]
#guard corePrefixOf maxReadsMax "M" == cellsOf maxReadsMax "M"
#guard corePrefixOf maxReadsMax "R" == none
#guard corePrefixOf minReadsMin "M" ==
  some [.fin 20, .posInf, .fin 2, .posInf, .fin 3, .posInf, .fin 40, .posInf]
#guard corePrefixOf minReadsMin "M" == cellsOf minReadsMin "M"
#guard corePrefixOf minReadsMin "R" == none

/-! ### Existing programs re-expressed (T4 dispatch 2)

Each program below exists elsewhere in the test tree as a typed-path row (`SourceSortedDifferentialTest`)
or a TL/plan fixture (`CollectEvalTest`, `CollectPlanTest`). Here it runs through `compareMixedSource`
on the shared fixture inputs, in the Source sublanguage: f64 tensors, bare-index monomials. Extents are
the fixture's (`a` 4, `b` 3, `k` 8), so the inputs differ from the donors and every expected value is
derived from `X=[20,2,3,40]`, `Z`, `Q`, `W=[1,10,100]` by hand. Each row asserts the classification
(`fourLegParity`), both legs, the oracle's and Core's cells and the sorts the statements ran in; a program that
ran in the wrong sort would flip the cells. -/

/-- As `parity`, for cells that may be `-inf`/`+inf`. -/
private def parityExt (f : Fx) (n : String) (vs : List ExtVal) : Bool :=
  classOf f == four && legsAgree f && cellsOf f n == some vs && coreCellsOf f n == some vs

private def tWb : T := ⟨"W", [axB], .input, [1, 10, 100]⟩
private def tXneg : T := ⟨"X", [axA], .input, [-1, -2, -3, -4]⟩
private def tS : T := ⟨"S", [axB], .input, [2, 9, 5]⟩
private def tA (vals : List ℚ) : T := ⟨"A", [axA], .input, vals⟩
/-- `Tr[a,b,k]` is `0` where `k = a + b` and `-100` elsewhere (finite: inputs are rationals, so the
donors' `-inf` entries are not expressible). -/
private def tTr : T :=
  ⟨"Tr", [axA, axB, axK], .input,
    (List.range 96).map fun i => if i % 8 = i / 24 + (i / 8) % 3 then (0 : ℚ) else -100⟩

private def contract (agg : AggOp) : Fx :=
  fx [tZ, tWb, tOut "Y"] [zR "Y" free1 agg [rd "Z" [axA, axB], rd "W" [axB]]]
private def productX (agg : AggOp) (x : T := tX) : Fx :=
  fx [x, tWb, tOut "Y"] [zR "Y" free1 agg [rd "X" [axA], rd "W" [axB]]]
private def strided (agg : AggOp) : Fx :=
  fx [tX, tOut "Y" [axK]] [zR "Y" [.affine (.scale 2 axA)] agg [rd "X" [axA]]]
private def collide (agg : AggOp) : Fx :=
  fx [tZ, tOut "Y" [axK]] [.scatter "Y" [.affine (.scale 2 axA)] (rhs agg [[rd "Z" [axA, axB]]])]
private def zeroY (agg : AggOp) : Fx := fx [tOut "Y"] [.assign "Y" free1 (rhs agg [[]])]

-- product (`SourceSortedDifferentialTest`): `Y[a] = (+)_b X[a] (x) W[b]`; max-plus `X[a] + 100`
#guard parity (productX .max) "Y" [120, 102, 103, 140]
#guard ranIn (productX .max) == some [.maxPlus]
-- min-plus `X[a] + 1`
#guard parity (productX .min) "Y" [21, 3, 4, 41]
#guard ranIn (productX .min) == some [.minPlus]
-- negative inputs, where max-times and max-plus disagree (max-times would give `-1,-2,-3,-4`)
#guard parity (productX .max tXneg) "Y" [99, 98, 97, 96]
#guard parity (productX .min tXneg) "Y" [0, -1, -2, -3]
-- the real sort multiplies: `X[a] * 111`
#guard parity (productX .sum) "Y" [2220, 222, 333, 4440]
#guard ranIn (productX .sum) == some [.real]

-- contract: `Y[a] = (+)_b Z[a,b] (x) W[b]`; max-plus `Z[a,2] + 100`, min-plus `Z[a,0] + 1`
#guard parity (contract .max) "Y" [97, 107, 117, 127]
#guard parity (contract .min) "Y" [-4, 6, 16, 26]
#guard ranIn (contract .max) == some [.maxPlus]
#guard ranIn (contract .min) == some [.minPlus]

-- strided (`Y[2*a] := agg X[a]`): odd cells are never written and hold the sort's zero
#guard parityExt (strided .max) "Y"
  [.fin 20, .negInf, .fin 2, .negInf, .fin 3, .negInf, .fin 40, .negInf]
#guard parityExt (strided .min) "Y"
  [.fin 20, .posInf, .fin 2, .posInf, .fin 3, .posInf, .fin 40, .posInf]

-- collide (`.scatter`, `Y[2*a] := agg_b Z[a,b]`): the three `b` writes of each `a` meet in cell `2a`
#guard parityExt (collide .max) "Y"
  [.fin (-3), .negInf, .fin 7, .negInf, .fin 17, .negInf, .fin 27, .negInf]
#guard parityExt (collide .min) "Y"
  [.fin (-5), .posInf, .fin 5, .posInf, .fin 15, .posInf, .fin 25, .posInf]

-- zeroY: the empty product is the sort's one (`0` for both tropical sorts, `1` for the real sort)
#guard parity (zeroY .max) "Y" [0, 0, 0, 0]
#guard parity (zeroY .min) "Y" [0, 0, 0, 0]
#guard parity (zeroY .sum) "Y" [1, 1, 1, 1]

-- bellman, min twin of the homogeneous control: `[min(-5,20), min(5,2), min(15,3), min(25,40)]`
#guard parity (bellman .min .min) "Y" [-5, 2, 3, 25]
#guard ranIn (bellman .min .min) == some [.minPlus, .minPlus]

-- J4 / j4m (`CollectEvalTest`): two same-sort contraction writers collected with that sort
private def j4 (agg : AggOp) : Fx :=
  fx [tZ, tQ, tOut "Y"] [st "Y" agg (rd "Z" [axA, axB]), st "Y" agg (rd "Q" [axA, axB])]
-- max: `max([-3,7,17,27], [9,8,7,11])`; the sum collector would give `[6,15,24,38]`
#guard parity (j4 .max) "Y" [9, 8, 17, 27]
#guard ranIn (j4 .max) == some [.maxPlus, .maxPlus]
-- min: `min([-5,5,15,25], [1,3,5,0])`
#guard parity (j4 .min) "Y" [-5, 3, 5, 0]
#guard ranIn (j4 .min) == some [.minPlus, .minPlus]

-- tcopyMax / tcopyMin (`CollectPlanTest`): a sum-annotated neutral copy beside a max (min) writer
private def tcopy (agg : AggOp) (vals : List ℚ) : Fx :=
  fx [tZ, tA vals, tOut "Y"] [st "Y" agg (rd "Z" [axA, axB]), st "Y" .sum (rd "A" [axA])]
-- `max([-3,7,17,27], [-1,-9,20,0])`; the sum would give `[-4,-2,37,27]`
#guard parity (tcopy .max [-1, -9, 20, 0]) "Y" [-1, 7, 20, 27]
#guard ranIn (tcopy .max [-1, -9, 20, 0]) == some [.maxPlus, .maxPlus]
-- `min([-5,5,15,25], [1,9,20,0])`; the sum would give `[-4,14,35,25]`
#guard parity (tcopy .min [1, 9, 20, 0]) "Y" [-5, 5, 15, 0]
#guard ranIn (tcopy .min [1, 9, 20, 0]) == some [.minPlus, .minPlus]

-- Bellman P1 / P1c / P5 (`CollectPlanTest`): `Q` row maxima `[9,8,7,11]` against the terminal `X`
private def p1 : Fx := fx [tQ, tX, tOut "Y"] [st "Y" .max (rd "Q" [axA, axB]), st "Y" .max (rd "X" [axA])]
private def p1c : Fx := fx [tQ, tX, tOut "Y"] [st "Y" .max (rd "Q" [axA, axB]), st "Y" .sum (rd "X" [axA])]
private def p5 : Fx :=
  fx [tQ, tX, tOut "Y"] [.assign "Y" free1 (rhs .max [[rd "Q" [axA, axB]], [rd "X" [axA]]])]
#guard parity p1 "Y" [20, 8, 7, 40]
#guard parity p1c "Y" [20, 8, 7, 40]
#guard parity p5 "Y" [20, 8, 7, 40]
#guard ranIn p1 == some [.maxPlus, .maxPlus]
#guard ranIn p1c == some [.maxPlus, .maxPlus]
#guard ranIn p5 == some [.maxPlus]

-- Bellman P2 / P2c: `Y[a] = max_{b,k} Q[a,b] + Tr[a,b,k] + W8[k]` against the terminal `X`.
-- `Tr` is `0` only at `k = a + b`, so the contraction is `max_b Q[a,b] + W8[a+b]` = `[9,10,10,16]`
-- (a=3: `10 + W8[4] = 14`, `11 + W8[5] = 16`).
private def p2 (copy : AggOp) : Fx :=
  fx [tQ, tTr, tW8, tX, tOut "Y"]
    [zR "Y" free1 .max [rd "Q" [axA, axB], rd "Tr" [axA, axB, axK], rd "W8" [axK]],
     st "Y" copy (rd "X" [axA])]
#guard parity (p2 .max) "Y" [20, 10, 10, 40]
#guard parity (p2 .sum) "Y" [20, 10, 10, 40]
#guard ranIn (p2 .sum) == some [.maxPlus, .maxPlus]

-- Bellman P3 / P3c / P5m: shortest paths `D[b] = min_a Q[a,b] + X[a]` = `[5,8,6]`, source init `S=[2,9,5]`
private def p3 : Fx :=
  fx [tQ, tX, tS, tOut "D" [axB]]
    [zR "D" [.free axB] .min [rd "Q" [axA, axB], rd "X" [axA]], zR "D" [.free axB] .min [rd "S" [axB]]]
private def p3c : Fx :=
  fx [tQ, tX, tS, tOut "D" [axB]]
    [zR "D" [.free axB] .min [rd "Q" [axA, axB], rd "X" [axA]], zR "D" [.free axB] .sum [rd "S" [axB]]]
private def p5m : Fx :=
  fx [tQ, tX, tS, tOut "D" [axB]]
    [.assign "D" [.free axB] (rhs .min [[rd "Q" [axA, axB], rd "X" [axA]], [rd "S" [axB]]])]
#guard parity p3 "D" [2, 8, 5]
#guard parity p3c "D" [2, 8, 5]
#guard parity p5m "D" [2, 8, 5]
#guard ranIn p3c == some [.minPlus, .minPlus]

-- vrSumMax / vrSumMaxR / vrSumMin / vrSumOnly (`CollectPlanTest`), bare-index form (the donors' `B[i+1]`
-- pads out of range, which is an affine read): a non-neutral SUM contraction beside a neutral max/min
-- copy. The copy abstains and runs as sum: `Q` row sums `[12,15,18,21]` plus `X`; a max collector would
-- give `[20,15,18,40]`.
private def vr (first : Bool) (copy : AggOp) : Fx :=
  let c := st "Y" .sum (rd "Q" [axA, axB])
  let t := st "Y" copy (rd "X" [axA])
  fx [tQ, tX, tOut "Y"] (if first then [c, t] else [t, c])
#guard parity (vr true .max) "Y" [32, 17, 21, 61]
#guard parity (vr false .max) "Y" [32, 17, 21, 61]
#guard parity (vr true .min) "Y" [32, 17, 21, 61]
#guard parity (vr true .sum) "Y" [32, 17, 21, 61]
#guard ranIn (vr true .max) == some [.real, .real]
#guard ranIn (vr false .max) == some [.real, .real]
#guard ranIn (vr true .min) == some [.real, .real]

/-! ### Existing refusal and reader programs (`CollectPlanTest`: `nbMM`, `nbMMr`, `nbSM`, `nbMS`,
`rdMin`, `rdMax`, `rdReal`)

Two NON-neutral writers of different sorts vote against each other, in both orders; a min reader of a
max group is a cast the rules refuse; a max reader and a real (sum) reader of it are accepted. -/

private def nb (a1 a2 : AggOp) : Fx :=
  fx [tZ, tQ, tOut "Y"] [st "Y" a1 (rd "Z" [axA, axB]), st "Y" a2 (rd "Q" [axA, axB])]
private def rdGroup (reader : Stmt) (out : T) : Fx :=
  fx [tQ, tX, tDef "Vn", out]
    [st "Vn" .max (rd "Q" [axA, axB]), reader, st "Vn" .sum (rd "X" [axA])]

#guard classOf (nb .max .min) == "OracleMixed.MixedClassification.refusalParity \"multiWriterAlgebra\""
#guard classOf (nb .min .max) == "OracleMixed.MixedClassification.refusalParity \"multiWriterAlgebra\""
#guard classOf (nb .sum .max) == "OracleMixed.MixedClassification.refusalParity \"multiWriterAlgebra\""
#guard classOf (nb .max .sum) == "OracleMixed.MixedClassification.refusalParity \"multiWriterAlgebra\""
-- rdMin: a min statement reading the max group
#guard classOf (rdGroup (st "Z" .min (rd "Vn" [axA])) (tOut "Z")) ==
  "OracleMixed.MixedClassification.refusalParity \"sortCastUnsupported\""
-- rdMax: `Vn = max([9,8,7,11], X)`, read by a max statement
#guard parity (rdGroup (st "Z" .max (rd "Vn" [axA])) (tOut "Z")) "Z" [20, 8, 7, 40]
-- rdReal: a real statement sums the group's cells: `20 + 8 + 7 + 40`
#guard parity (rdGroup (zR "Tot" [] .sum [rd "Vn" [axA]]) (tOut "Tot" [])) "Tot" [75]

/-! ### Negative control: a doctored prediction is caught, never agreed with

`compareMixedSource` takes the rule predictor's verdict through `doctor`. Rewriting `stmtSorts` so a max
(min) group runs as sum makes the oracle evaluate a different program than the native legs ran, so
the classification must be `nativeDiscrepancy`; it may never be a parity. (The Core leg takes the same
doctored sorts, so it agrees with the doctored oracle: only the native legs expose the lie.) The
undoctored rows are the same programs, accepted as `fourLegParity` above. -/

private def allReal (p : Prediction) : Prediction := { p with stmtSorts := p.stmtSorts.map fun _ => .real }

private def runDoctored (f : Fx) : Except String MixedRun :=
  (compareMixedSource f.snap (some f.order) allReal).mapError (fun d => s!"refused {repr d.cause}")

private def isDiscrepancy (f : Fx) : Bool :=
  match runDoctored f with
  | .ok r => match r.classification with
    | .nativeDiscrepancy _ _ => true
    | _ => false
  | .error _ => false

private def isParity (f : Fx) : Bool :=
  match runDoctored f with
  | .ok r => match r.classification with
    | .threeLegParity _ | .fourLegParity => true
    | _ => false
  | .error _ => false

-- the doctored run really ran as sum: the oracle's cells are the real-sum values, not the max ones
private def doctoredCells (f : Fx) (n : String) : Option (List ExtVal) :=
  match runDoctored f with
  | .ok r => match r.oracle with
    | .ok ts => (ts.find? (·.name == some n)).map (fun t => t.values.filterMap id)
    | .error _ => none
  | .error _ => none

-- the control programs themselves are parity rows when undoctored
#guard parity (bellman .max .max) "Y" [20, 7, 17, 40]
#guard parity (bellman .min .min) "Y" [-5, 2, 3, 25]
#guard parity (j4 .max) "Y" [9, 8, 17, 27]
-- doctored: `[max(-3,20), ..]` run as sum is `[-12 + 20, 18 + 2, 48 + 3, 78 + 40]`
#guard isDiscrepancy (bellman .max .max)
#guard !isParity (bellman .max .max)
#guard doctoredCells (bellman .max .max) "Y" == some (fins [8, 20, 51, 118])
#guard isDiscrepancy (bellman .min .min)
#guard isDiscrepancy (j4 .max)
#guard isDiscrepancy (contract .max)
#guard isDiscrepancy (tcopy .max [-1, -9, 20, 0])

/-! ### Stratified chains (T5): three or more targets, each group run in its own sort

The Core leg runs one single-sort group at a time: each target's statements (with `agg` set to the
group's sort) over the inputs and the Core leg's OWN earlier outputs. -/

/-- Three targets: max-plus row maxima, a real product reading them, a min-plus copy of that.
`T1 = max_b Z[a,b] = [-3,7,17,27]`; `T2 = T1 * X = [-60,14,51,1080]`; `O = T2`. -/
private def chain3 : Fx :=
  fx [tX, tZ, tDef "T1", tDef "T2", tOut "O"]
    [st "T1" .max (rd "Z" [axA, axB]), zR "T2" free1 .sum [rd "T1" [axA], rd "X" [axA]],
     st "O" .min (rd "T2" [axA])]

/-- Four targets crossing every sort: min-plus row minima `U = [1,3,5,0]`; a real group `V` (a
non-neutral sum product beside a neutral max copy that abstains and runs as sum)
`V = U * X + X = [40,8,18,40]`; a max-plus group `W = max(V, max_b Z) = [40,8,18,40]`; a real total
`O = 106`. -/
private def chain4 : Fx :=
  fx [tX, tZ, tQ, tDef "U", tDef "V", tDef "W", tOut "O" []]
    [st "U" .min (rd "Q" [axA, axB]), zR "V" free1 .sum [rd "U" [axA], rd "X" [axA]], st "V" .max (rd "X" [axA]),
     st "W" .max (rd "V" [axA]), st "W" .max (rd "Z" [axA, axB]), zR "O" [] .sum [rd "W" [axA]]]

#guard parity chain3 "O" [-60, 14, 51, 1080]
#guard ranIn chain3 == some [.maxPlus, .real, .minPlus]
-- the Core leg's own intermediates are the stratified ones
#guard coreCellsOf chain3 "T1" == some (fins [-3, 7, 17, 27])
#guard coreCellsOf chain3 "T2" == some (fins [-60, 14, 51, 1080])
#guard parity chain4 "O" [106]
#guard ranIn chain4 == some [.minPlus, .real, .real, .maxPlus, .maxPlus, .real]
#guard coreCellsOf chain4 "U" == some (fins [1, 3, 5, 0])
#guard coreCellsOf chain4 "V" == some (fins [40, 8, 18, 40])
#guard coreCellsOf chain4 "W" == some (fins [40, 8, 18, 40])

/-! ### Negative control: a wrong earlier value fed to Core is a `referenceDiscrepancy`

`feed` rewrites the rational cells of an earlier target (by declaration) before they enter a later
group's Core run as inputs. The oracle and both native legs still agree with each other, so the only
detector is the Core comparison. The identity feed is the parity row above. -/

private def runFed (f : Fx) (feed : Nat → List ℚ → List ℚ) : Option MixedRun :=
  match compareMixedSource f.snap (some f.order) id feed with
  | .ok r => some r
  | .error _ => none

private def isRefDiscrepancy (f : Fx) (feed : Nat → List ℚ → List ℚ) : Bool :=
  match runFed f feed with
  | some r => match r.classification with
    | .referenceDiscrepancy => true
    | _ => false
  | none => false

private def bump (d : Nat) : Nat → List ℚ → List ℚ :=
  fun x vs => if x == d then vs.map (· + 1) else vs

-- `T1` is declaration 5, `T2` declaration 6; `U` is 6, `V` 7, `W` 8 (`X`,`Z`,`Q` are 3,4,5)
#guard isRefDiscrepancy chain3 (bump 5)
#guard isRefDiscrepancy chain3 (bump 6)
#guard isRefDiscrepancy chain4 (bump 6)
#guard isRefDiscrepancy chain4 (bump 8)
-- the native legs and the oracle are untouched by the feed: they still agree with each other
#guard match runFed chain3 (bump 5) with
  | some r => match r.legacy, r.checked with
    | .agrees, .agrees => true
    | _, _ => false
  | none => false
-- the wrong value really reached the Core leg's output: `(T1 + 1) * X`, not `T1 * X`
#guard match runFed chain3 (bump 5) with
  | some r => match r.core with
    | some (.ok ts) => cellsIn ts "T2" == some (fins [-40, 16, 54, 1120])
    | _ => false
  | none => false
-- a feed that changes nothing (a bump on a declaration no group reads) is still parity
#guard match runFed chain3 (bump 99) with
  | some r => match r.classification with
    | .fourLegParity => true
    | _ => false
  | none => false

/-! ### Negative control: a disagreeing Core PREFIX is a `referenceDiscrepancy`, not `threeLegParity`

The Core leg stops at a target whose read tensor has a non-finite cell (`R` reads `M`, whose odd cells
are `-inf`). What it computed before stopping (`T`, `M`) is still compared with the oracle. Here `T`
(declaration 5, a real copy of `X`) is bumped on its way into `M`'s Core run, so Core's `M` differs from
the oracle's although Core never reached `R`: the class is `referenceDiscrepancy`, where the unbumped
row is `threeLegParity` (the prefix agrees). -/

private def blockedAfterT : Fx :=
  fx [tX, tW8, tDef "T", tDef "M" [axK], tOut "R" [axK]]
    [st "T" .sum (rd "X" [axA]), zR "M" [.affine (.scale 2 axA)] .max [rd "T" [axA]],
     zR "R" [.free axK] .max [rd "M" [axK]]]

#guard classOf blockedAfterT == threeNotRun
#guard coreNotRun blockedAfterT
#guard corePrefixOf blockedAfterT "T" == some (fins [20, 2, 3, 40])
#guard isRefDiscrepancy blockedAfterT (bump 5)
#guard match runFed blockedAfterT (bump 5) with
  | some r => match r.classification with
    | .threeLegParity _ => false
    | _ => true
  | none => false
-- the oracle and both native legs are untouched by the feed
#guard match runFed blockedAfterT (bump 5) with
  | some r => match r.legacy, r.checked with
    | .agrees, .agrees => true
    | _, _ => false
  | none => false
-- the wrong value is in the Core PREFIX (not a finished Core leg): `M` at the even cells is `X + 1`
#guard match runFed blockedAfterT (bump 5) with
  | some r => r.core.isNone &&
      cellsIn r.corePrefix "M" == some [.fin 21, .negInf, .fin 3, .negInf, .fin 4, .negInf, .fin 41, .negInf]
  | none => false

/-! ### The mixed profile REJECTS an occurrence outside the numerical envelope

`checkMixedProfile` is the only gate between the oracle's exact rationals and the f64 native legs, so
its rejection arm is exercised here, not just its accepting arm. The envelope is `NumericalProfile.limit`
(`2^20`): every input, read, partial product and cell must be an integer of at most that magnitude. The
rejection is pinned by kind and value, so it is the per-OCCURRENCE check that fires (a statement-level or
final-cell check would report `tensorCell`): a real statement is bounded by its PRODUCT of reads
(`partialProduct`), a tropical one by the SUM of the magnitudes of its reads (`subsetProductBound`).
Each rejected row has an accepted control one step inside the envelope (so it is the magnitude, nothing
else, that rejects). The legs are `.unavailable` on a rejected row: their bits are not compared. -/

private def tBigX (x0 : ℚ) : T := ⟨"X", [axA], .input, [x0, 2, 3, 40]⟩
private def tBigA (a0 : ℚ) : T := ⟨"A", [axA], .input, [a0, 1, 1, 1]⟩
private def twoReads (agg : AggOp) (x0 a0 : ℚ) : Fx :=
  fx [tBigX x0, tBigA a0, tOut "Y"] [zR "Y" free1 agg [rd "X" [axA], rd "A" [axA]]]

/-- Rejected at statement 0, cell `[0]`, as a partial product of value `v`. -/
private def rejectedProduct (f : Fx) (v : ℚ) : Bool :=
  match run f with
  | .ok r =>
    match r.classification with
    | .unsupportedNumericalProfile (.outsideEnvelope site .partialProduct value _) =>
      value == v && site.origin.statement == some 0 && site.coordinate == [0]
    | _ => false
  | .error _ => false

/-- Rejected at statement 0, cell `[0]`, as a sum of magnitudes of value `v`. -/
private def rejectedSum (f : Fx) (v : ℚ) : Bool :=
  match run f with
  | .ok r =>
    match r.classification with
    | .unsupportedNumericalProfile (.outsideEnvelope site .subsetProductBound value _) =>
      value == v && site.origin.statement == some 0 && site.coordinate == [0]
    | _ => false
  | .error _ => false

-- real: `2048 * 2048 = 4194304 > 2^20`; the control `1024 * 1024 = 2^20` is at the limit, accepted
#guard rejectedProduct (twoReads .sum 2048 2048) 4194304
#guard legsUnavailable (twoReads .sum 2048 2048)
#guard !isParityClass (twoReads .sum 2048 2048)
#guard parity (twoReads .sum 1024 1024) "Y" [1048576, 2, 3, 40]
-- tropical: `600000 + 600000 = 1200000 > 2^20` (each read alone is inside); the control sums to `10^6`
#guard rejectedSum (twoReads .max 600000 600000) 1200000
#guard rejectedSum (twoReads .min 600000 600000) 1200000
#guard legsUnavailable (twoReads .max 600000 600000)
#guard !isParityClass (twoReads .max 600000 600000)
#guard parity (twoReads .max 500000 500000) "Y" [1000000, 3, 4, 41]
#guard parity (twoReads .min 500000 500000) "Y" [1000000, 3, 4, 41]
-- the two bounds differ: the same inputs `2048, 2048` are fine for a tropical statement (sum 4096)
#guard parity (twoReads .max 2048 2048) "Y" [4096, 3, 4, 41]

end OracleMixedValueTest

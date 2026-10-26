import Semantics.OracleMixedDifferential

/-! Oracle sorts T4: value rows for `compareMixedSource` on the ACCEPTED path (the predictor says the
program is accepted, production accepts it, both native legs run), the mixed numerical profile, and
the non-finite class.

Every accepted row asserts three things, so none is vacuous: the classification is `threeLegParity`
(oracle, legacy and checked bits agree; the Core leg is not run for mixed programs, T5 upgrades finite
rows to `fourLegParity`), the oracle's own cells equal hand-derived values, and the sort each
statement RAN in (the predictor's `stmtSorts`). Values are derived from the inputs of
`Semantics.OracleMixedFixtures` (`X=[20,2,3,40]`, `Z` rows `[-5,-4,-3] [5,6,7] [15,16,17] [25,26,27]`,
`B=Q` rows `[1,9,2] [3,8,4] [7,5,6] [0,10,11]`), not copied from production. -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open Oracle NativeLegs SortedDifferential LeanNCD.OracleSorts OracleMixed

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

private def three : String := "OracleMixed.MixedClassification.threeLegParity \"core leg not run\""

/-- The oracle's cells of the tensor named `n`. -/
private def cellsOf (f : Fx) (n : String) : Option (List ExtVal) :=
  match run f with
  | .ok r =>
    match r.oracle with
    | .ok ts => (ts.find? (·.name == some n)).map (fun t => t.values.filterMap id)
    | .error _ => none
  | .error _ => none

private def fins (qs : List ℚ) : List ExtVal := qs.map .fin

/-- Both legs agree with the oracle bit for bit (a real comparison, not an absent one). -/
private def legsAgree (f : Fx) : Bool :=
  match run f with
  | .ok r => match r.legacy, r.checked with
    | .agrees, .agrees => true
    | _, _ => false
  | .error _ => false

/-- An accepted row: `threeLegParity`, legs agreeing, and the oracle's cells of `n` equal `qs`. -/
private def parity (f : Fx) (n : String) (qs : List ℚ) : Bool :=
  classOf f == three && legsAgree f && cellsOf f n == some (fins qs)

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

-- homogeneous control (the typed path says `fourLegParity`; here Core is not run)
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

/-- Is the classification `nonFiniteIntoReal` at declaration `d`, cell `c`? -/
private def nonFiniteAt (f : Fx) (d : Nat) (c : List Nat) : Bool :=
  match run f with
  | .ok r =>
    match r.classification with
    | .unsupportedNumericalProfile (.nonFiniteIntoReal site) =>
      site.origin.declaration == some d && site.coordinate == c
    | _ => false
  | .error _ => false

private def copyMax := unwritten .max .sum [rd "M" [axK]]
private def productMax := unwritten .max .sum [rd "M" [axK], rd "W8" [axK]]
private def copyMin := unwritten .min .sum [rd "M" [axK]]
-- a tropical reader of the same unwritten cells is fine: `-inf` is its own value
private def maxReadsMax := unwritten .max .max [rd "M" [axK]]

-- `M` is declaration 5; its first unwritten cell is `[1]`
#guard nonFiniteAt copyMax 5 [1]
#guard nonFiniteAt productMax 5 [1]
#guard nonFiniteAt copyMin 5 [1]
#guard !(classOf copyMax == three)
#guard !(classOf productMax == three)
#guard !(classOf copyMin == three)
#guard cellsOf maxReadsMax "R" ==
  some [.fin 20, .negInf, .fin 2, .negInf, .fin 3, .negInf, .fin 40, .negInf]
#guard classOf maxReadsMax == three
#guard legsAgree maxReadsMax

end OracleMixedValueTest

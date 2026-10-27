import LeanNCD.Semantics.Source.SortedDifferential
import Semantics.OracleSortRules
import Semantics.OracleMixedFixtures
import Semantics.OracleMixedEval

/-! Oracle sorts T3: agreement guards for the heterogeneous evaluator `runMixed`.

(a) On single-sort programs `runMixed` agrees cell for cell with the typed `Oracle.runWith`
(`Carrier.real|maxPlus|minPlus`). (b) The mixed-sort values observed on both native legs
(`papers/semantics/oracle_sorts_plan_facts.md` section 0), including that a neutral copy whose
annotation disagrees with its group's sort RUNS in the group's sort (Review Focus 1). (c) The cast
cells. (d) The unwritten-cell shapes a real statement may never read (`nonFiniteIntoReal`). -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open Oracle LeanNCD.OracleSorts
open OracleMixed

namespace OracleMixedEvalTest

/-- A fixture: the snapshot and the original-declaration order of its non-input tensors. -/
private structure Fx where
  snap : SourceSnapshot
  order : List Nat

private def fx (ts : List T) (stmts : List Stmt) : Fx := ⟨mk ts stmts, orderOf ts⟩

private def tW : T := ⟨"W", [axB], .input, [1, 10, 100]⟩

private def contY (agg : AggOp) : Stmt := st "Y" agg (rd "Z" [axA, axB])
private def termY (agg : AggOp) : Stmt := st "Y" agg (rd "X" [axA])
private def bellman (s1 s2 : AggOp) : Fx := fx [tX, tZ, tOut "Y"] [contY s1, termY s2]
private def single (agg : AggOp) : Fx := fx [tX, tZ, tOut "Y"] [contY agg]
private def product (agg : AggOp) : Fx :=
  fx [tX, tW, tOut "Y"] [zR "Y" free1 agg [rd "X" [axA], rd "W" [axB]]]
private def strided (agg : AggOp) : Fx :=
  fx [tX, tW8, tOut "Y" [axK]] [zR "Y" [.affine (.scale 2 axA)] agg [rd "X" [axA]]]
private def collide (agg : AggOp) : Fx :=
  fx [tZ, tOut "Y" [axK]] [zR "Y" [.affine (.scale 2 axA)] agg [rd "Z" [axA, axB]]]

private abbrev Cells := List (Nat × List ExtVal)

private def adm (f : Fx) : Except String AdmittedSource :=
  (admitSourceAffine f.snap true).mapError (fun d => s!"admit {repr d.cause}")

/-- The typed path: `Oracle.runWith` over a fixed carrier, observed into `ExtVal`. -/
private def typed {K : Type} [Semiring K] (C : Carrier K) (f : Fx) : Except String Cells := do
  match Oracle.runWith C (← adm f) (some f.order) with
  | .ok r => .ok (r.tensors.map fun t => (t.declaration, t.values.map C.observe))
  | .error u => .error s!"typed unavailable {repr u}"

/-- The heterogeneous path: `runMixed` driven by the independent predictor. -/
private def mixed (f : Fx) : Except String MixedResult := do
  let a ← adm f
  let p := predict f.snap.resolved.decls f.snap.resolved.stmts
  match runMixed a f.snap.resolved.stmts p f.order with
  | .ok r => .ok r
  | .error e => .error (toString (repr e))

private def mixedCells (f : Fx) : Except String Cells :=
  (mixed f).map fun r => r.tensors.map fun t => (t.declaration, t.values)

private def agree (x y : Except String Cells) : Bool :=
  match x, y with
  | .ok u, .ok v => u == v
  | _, _ => false

private def fins (qs : List ℚ) : List ExtVal := qs.map .fin

/-- The cells of the tensor named `n`. -/
private def named (f : Fx) (n : String) : Except String (List ExtVal) := do
  match (← mixed f).tensors.find? (·.name == n) with
  | some t => .ok t.values
  | none => .error s!"no tensor {n}"

private def is (r : Except String (List ExtVal)) (qs : List ℚ) : Bool :=
  match r with
  | .ok v => v == fins qs
  | .error _ => false

/-- The distinct (statement, running sort, own annotation sort) triples of a run's occurrences. -/
private def sortsOf (f : Fx) : Except String (List (Nat × MSort × MSort)) :=
  (mixed f).map fun r =>
    (r.occurrences.map (fun o => (o.statement, o.sort, o.own))).eraseDups

/-- The error `runMixed` raised, as a printed string; `ran` if it succeeded. -/
private def failure (f : Fx) : String :=
  match mixed f with
  | .ok _ => "ran"
  | .error e => e

/-! ### (a) Agreement with the typed path on single-sort programs -/

#guard agree (typed Carrier.maxPlus (bellman .max .max)) (mixedCells (bellman .max .max))
#guard agree (typed Carrier.minPlus (bellman .min .min)) (mixedCells (bellman .min .min))
#guard agree (typed Carrier.real (bellman .sum .sum)) (mixedCells (bellman .sum .sum))
#guard agree (typed Carrier.real (single .sum)) (mixedCells (single .sum))
#guard agree (typed Carrier.maxPlus (single .max)) (mixedCells (single .max))
#guard agree (typed Carrier.minPlus (single .min)) (mixedCells (single .min))
#guard agree (typed Carrier.maxPlus (collide .max)) (mixedCells (collide .max))
#guard agree (typed Carrier.minPlus (collide .min)) (mixedCells (collide .min))
#guard agree (typed Carrier.maxPlus (strided .max)) (mixedCells (strided .max))
#guard agree (typed Carrier.minPlus (strided .min)) (mixedCells (strided .min))
#guard agree (typed Carrier.real (strided .sum)) (mixedCells (strided .sum))
#guard agree (typed Carrier.maxPlus (product .max)) (mixedCells (product .max))
#guard agree (typed Carrier.minPlus (product .min)) (mixedCells (product .min))
#guard agree (typed Carrier.real (product .sum)) (mixedCells (product .sum))

-- The agreement is not vacuous: the compared cells hold infinities and real numbers.
#guard (named (strided .max) "Y").toOption ==
  some [.fin 20, .negInf, .fin 2, .negInf, .fin 3, .negInf, .fin 40, .negInf]
#guard (named (strided .min) "Y").toOption ==
  some [.fin 20, .posInf, .fin 2, .posInf, .fin 3, .posInf, .fin 40, .posInf]
#guard (named (collide .max) "Y").toOption ==
  some [.fin (-3), .negInf, .fin 7, .negInf, .fin 17, .negInf, .fin 27, .negInf]
#guard is (named (product .max) "Y") [120, 102, 103, 140]
#guard is (named (product .min) "Y") [21, 3, 4, 41]
#guard is (named (product .sum) "Y") [2220, 222, 333, 4440]
#guard is (named (single .sum) "Y") [-12, 18, 48, 78]

/-! ### (b) Mixed-sort values, observed on both native legs (facts section 0) -/

#guard is (named (bellman .max .max) "Y") [20, 7, 17, 40]
#guard is (named (bellman .max .sum) "Y") [20, 7, 17, 40]
#guard is (named (bellman .max .min) "Y") [20, 7, 17, 40]
#guard is (named (bellman .min .sum) "Y") [-5, 2, 3, 25]
#guard is (named (bellman .sum .max) "Y") [8, 20, 51, 118]

-- Review Focus 1: an abstaining neutral copy RUNS in its group's sort, not its own annotation.
-- The values above cannot tell (one occurrence per cell); the running sort recorded per occurrence can.
#guard sortsOf (bellman .max .min) == .ok [(0, .maxPlus, .maxPlus), (1, .maxPlus, .minPlus)]
#guard sortsOf (bellman .max .sum) == .ok [(0, .maxPlus, .maxPlus), (1, .maxPlus, .real)]
#guard sortsOf (bellman .min .sum) == .ok [(0, .minPlus, .minPlus), (1, .minPlus, .real)]
#guard sortsOf (bellman .sum .max) == .ok [(0, .real, .real), (1, .real, .maxPlus)]
#guard sortsOf (bellman .max .max) == .ok [(0, .maxPlus, .maxPlus), (1, .maxPlus, .maxPlus)]

/-! ### (c) Cast cells -/

private def castMax : Fx :=
  fx [tZ, tDef "M", tOut "R"]
    [st "M" .max (rd "Z" [axA, axB]), st "R" .sum (rd "M" [axA])]
private def castReal : Fx :=
  fx [tZ, tDef "S", tOut "O"]
    [st "S" .sum (rd "Z" [axA, axB]), st "O" .max (rd "S" [axA])]
private def launder : Fx :=
  fx [tZ, tDef "M", tDef "R", tOut "O"]
    [st "M" .max (rd "Z" [axA, axB]), st "R" .sum (rd "M" [axA]), st "O" .min (rd "R" [axA])]
/-- A max-plus tensor read by a min-plus statement: the predictor refuses it, so reaching the
evaluator is a harness bug. -/
private def direct : Fx :=
  fx [tZ, tDef "M", tOut "O"]
    [st "M" .max (rd "Z" [axA, axB]), st "O" .min (rd "M" [axA])]

#guard is (named castMax "R") [-3, 7, 17, 27]
#guard is (named castReal "O") [-12, 18, 48, 78]
#guard is (named launder "O") [-3, 7, 17, 27]
#guard sortsOf castMax == .ok [(0, .maxPlus, .maxPlus), (1, .real, .real)]
#guard sortsOf castReal == .ok [(0, .real, .real), (1, .maxPlus, .maxPlus)]
#guard (failure direct).startsWith "LeanNCD.OracleSorts.MixedEvalError.inconsistent"

/-! ### (d) Unwritten tropical cells read by a real statement (D5) -/

private def unwritten (agg : AggOp) (fs : List Factor) : Fx :=
  fx [tX, tW8, tDef "M" [axK], tOut "R" [axK]]
    [zR "M" [.affine (.scale 2 axA)] agg [rd "X" [axA]], zR "R" [.free axK] .sum fs]

private def copyMax := unwritten .max [rd "M" [axK]]
private def productMax := unwritten .max [rd "M" [axK], rd "W8" [axK]]
private def copyMin := unwritten .min [rd "M" [axK]]
private def copyMaxMoved : Fx :=
  fx [tX, tDef "M" [axK], tW8, tOut "R" [axK]] copyMax.snap.resolved.stmts

private def nonFiniteAt (f : Fx) (n : String) (c : List Nat) : Bool :=
  match declarationIndex f.snap n with
  | some d => failure f == toString (repr (MixedEvalError.nonFiniteIntoReal d c))
  | none => false

-- The first unwritten cell is `[1]`, even when `M` moves in the declaration list.
#guard nonFiniteAt copyMax "M" [1]
#guard nonFiniteAt productMax "M" [1]
#guard nonFiniteAt copyMin "M" [1]
#guard nonFiniteAt copyMaxMoved "M" [1]
#guard declarationIndex copyMaxMoved.snap "M" != declarationIndex copyMax.snap "M"
#guard declarationIndex copyMaxMoved.snap "missing" == none
#guard !nonFiniteAt copyMaxMoved "W8" [1]
#guard !nonFiniteAt copyMaxMoved "missing" [1]
#guard !nonFiniteAt copyMaxMoved "M" [0]

-- The same unwritten cells are legal for a tropical reader of the same sort.
#guard (named (fx [tX, tW8, tDef "M" [axK], tOut "R" [axK]]
    [zR "M" [.affine (.scale 2 axA)] .max [rd "X" [axA]], zR "R" [.free axK] .max [rd "M" [axK]]]) "R").toOption ==
  some [.fin 20, .negInf, .fin 2, .negInf, .fin 3, .negInf, .fin 40, .negInf]

end OracleMixedEvalTest

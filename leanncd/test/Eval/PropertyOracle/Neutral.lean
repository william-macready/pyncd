import LeanNCD.DSL.Ast

/-!
# Test-side sort-neutral writer predicate (leaf module)

`oracleNeutral` lives in its own leaf module so that the mixed-sort oracle modules can use it
without importing `Eval.PropertyOracle.ScanUnroll`, whose import chain runs the scan generator's
elaboration-time guards. This file imports only `LeanNCD.DSL.Ast`.
-/
namespace LeanNCD.PropertyOracle
open LeanNCD

/-- The axis uids an index expression mentions, by its own case split (not `idxAffineForm`). -/
private def oracleIdxUids : IdxExpr → List UID
  | .axis a | .scale _ a | .shift a _ => [a.uid]
  | .const _ => []
  | .affine _ xs => xs.map (fun p => p.2.uid)

/-- The axis uids an LHS slot names, by its own case split (not the library's slot helper). -/
private def oracleSlotUids : LHSSlot → List UID
  | .free a | .freeNorm a | .iterNext a | .iterAt a _ => [a.uid]
  | .affine e => oracleIdxUids e

/-- Sort-neutral writer, stated test-side from the plan's TEXT and deliberately in a different shape
    from production's neutrality predicate (which nests `match`es on the first term and factor): the
    statement has exactly one factor in total, that factor is a read (so no Iverson factor), the
    nonlinearity is the identity, the CONTRACTED axes (the read's axes minus the LHS axes) are none,
    and no LHS slot mentions two distinct axes (such a slot writes one cell from many axis points, so
    those writes combine). Such a statement has nothing to combine and so says nothing about its state's sort. Public
    so `ScanOracle` can pin its agreement with production on the scan corpus. -/
def oracleNeutral (s : Stmt) : Bool :=
  match s with
  | .recurMorphism _ _ _ => false
  | .assign _ ls r | .scatter _ ls r =>
      let factorCounts := r.body.terms.map (fun t => t.factors.length)
      let readAxes := r.body.terms.flatMap (fun t => t.factors.flatMap (fun
        | .read _ es | .unaryFn _ _ es => es.flatMap oracleIdxUids
        | .iverson _ => []))
      let readFactors := r.body.terms.flatMap (fun t => t.factors.filter (fun
        | .iverson _ => false
        | _ => true))
      let lhsAxes := ls.flatMap oracleSlotUids
      let contracted := readAxes.filter (fun u => !lhsAxes.contains u)
      let collidingSlot := ls.any (fun sl => (oracleSlotUids sl).eraseDups.length > 1)
      factorCounts == [1] && readFactors.length == 1 && r.nonlin == .identity && contracted.isEmpty
        && !collidingSlot

end LeanNCD.PropertyOracle

import Semantics.PlanFusionCorrectnessTest

/- Slice 2 (T4) fixtures: the case x class table at FUSED-command granularity. Each fixture fuses
   adjacent commands of a slice-1 DONOR singleton plan (same flat annotation sequence) and asserts
   (i) the verdict of the fused plan (`verdictF`, = clauses of its expansion), of its expansion by
   the slice-1 clause list, and of the donor, and (ii) the fused run against the donor run.
   Every asserted value was observed from a real run. -/

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

/-- `verdictF` of the fused plan, slice-1 `verdict` of its expansion, `verdict` of the donor. -/
def verdictTrio {K : S → Type} {σ : Declarations S} {r : Registry K} {P : Program K σ r}
    [DecidableEq σ.Tensor] (π donor : P.Plan) :
    (Bool × List String) × (Bool × List String) × (Bool × List String) :=
  (verdictF π, verdict π.expand, verdict donor)

/-- Kind of the fused run, kind of the donor run, whether the final memories agree on the three
    slots, the fused run's slots, the donor run's slots. -/
def runPair {P : Program Carrier declarations registry} (a b : PlanOutcome P) :
    String × String × Bool × List (Option ℚ) × List (Option ℚ) :=
  let x := outcomeRow a
  let y := outcomeRow b
  (x.1, y.1, x.2.2.2 == y.2.2.2, x.2.2.2, y.2.2.2)

/-- (a5) re-init after consume: `acc g1; initZero` fused (donor `reinitMid`). -/
def t4Reinit : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc [occ 0 0, occ 0 1], .initZero block],
    [.acc [occ 1 0, occ 1 1]], [.pub block]]
/-- (a6) duplicate occurrence across two annotations of one command (donor `dupGroup`). -/
def t4Dup : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc group, .acc [occ 0 0]], [.pub block]]
/-- (a7) overlapping publications in one command (donor `pubTwice`). -/
def t4PubTwice : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc group], [.pub block, .pub [addr 1]]]
/-- (a9) `initZero` of the empty fibers fused with the final publication (donor `lateEmptyInit`). -/
def t4InitPub : taggedOut.Plan :=
  unitPlan [[.initZero [addr 1]], [.acc group], [.initZero [addr 0, addr 2], .pub block]]
/-- (a3, split) the consumer is a LATER command than the fused producer pair `acc; pub`: its read
    view is the expanded position `offset 2 = 3`, not the command index 2 (donor `chainPlan`). -/
def t4ReadSplit : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0], .pub [cAddr 1]], [.acc [cOcc 1]],
    [.pub [cAddr 0, cAddr 2]]]
/-- (a4) accumulate whose reader precedes the producer's publication, fused (donor `chainEarly`). -/
def t4Unpub : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 1], .acc [cOcc 0]], [.pub cAll]]
/-- (a3, valid) the consumer reads a publication of the SAME command (donor `chainPlan`). -/
def t4ReadSame : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0], .pub [cAddr 1], .acc [cOcc 1]],
    [.pub [cAddr 0, cAddr 2]]]
/-- Singleton donor of `t4ReadSame`'s mis-fusion: the publication placed after the read. -/
def chainReadFirst : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0]], [.acc [cOcc 1]], [.pub [cAddr 1]],
    [.pub [cAddr 0, cAddr 2]]]
/-- (a3, mis-fused) the publication comes AFTER the read inside the command. -/
def t4ReadFirst : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0], .acc [cOcc 1], .pub [cAddr 1]],
    [.pub [cAddr 0, cAddr 2]]]

/-! ### Fixtures. Donor note: the donor has the same flat annotation sequence as the fused plan. -/

-- donor chainPlan; fused [acc0, pub1] then a separate [acc1] that reads the fused command's publication.
-- (The a2 case, publish before accumulate in one command, is pinned by P2a/P2b: `misfused-expand-rejected`,
-- `fusedcorr-misfused-verdicts` = pubOrder@1.)
#eval check "t4-a3split-chainPlan"
  (verdictTrio t4ReadSplit chainPlan,
    runPair (t4ReadSplit.runPlan ops (Start chainInput)) (chainPlan.runPlan ops (Start chainInput)))
  (((true, []), (true, []), (true, [])), ("done", "done", true, [some 0, some 3, some 4], [some 0, some 3, some 4]))

-- donor chainPlan = [init],[acc0],[pub1],[acc1],[pub 0 2]; fused [acc0, pub1, acc1]: acc1 reads point 1 published in the SAME command (valid, D15).
#eval check "t4-a3-chainPlan"
  (verdictTrio t4ReadSame chainPlan,
    runPair (t4ReadSame.runPlan ops (Start chainInput)) (chainPlan.runPlan ops (Start chainInput)))
  (((true, []), (true, []), (true, [])), ("done", "done", true, [some 0, some 3, some 4], [some 0, some 3, some 4]))

-- donor chainReadFirst = [init],[acc0],[acc1],[pub1],[pub 0 2]; fused [acc0, acc1, pub1]: the publication follows the read (D15 counterpart).
#eval check "t4-a3mis-chainReadFirst"
  (verdictTrio t4ReadFirst chainReadFirst,
    runPair (t4ReadFirst.runPlan ops (Start chainInput)) (chainReadFirst.runPlan ops (Start chainInput)))
  (((false, ["ready@2"]), (false, ["ready@2"]), (false, ["ready@2"])), ("stuck", "stuck", false, [some 0, some 0, some 0], [some 0, some 3, some 0]))

-- donor chainEarly = [init],[acc1],[acc0],[pub]; fused [acc1, acc0]: reads an accumulator that is never published first.
#eval check "t4-a4-chainEarly"
  (verdictTrio t4Unpub chainEarly,
    runPair (t4Unpub.runPlan ops (Start chainInput)) (chainEarly.runPlan ops (Start chainInput)))
  (((false, ["ready@1"]), (false, ["ready@1"]), (false, ["ready@1"])), ("stuck", "stuck", true, [some 0, some 0, some 0], [some 0, some 0, some 0]))

-- donor reinitMid = [init],[acc g1],[init],[acc g2],[pub]; fused [acc g1, init] (re-init after consume wipes g1: 10 not 14).
#eval check "t4-a5-reinitMid"
  (verdictTrio t4Reinit reinitMid,
    runPair (t4Reinit.runPlan ops (Start η0)) (reinitMid.runPlan ops (Start η0)))
  (((false, ["initFresh@2"]), (false, ["initFresh@2"]), (false, ["initFresh@2"])), ("done", "done", true, [some 0, some 10, some 0], [some 0, some 10, some 0]))

-- donor dupGroup = [init],[acc group],[acc [occ 0 0]],[pub]; fused [acc group, acc [occ 0 0]] (duplicate across annotations).
#eval check "t4-a6-dupGroup"
  (verdictTrio t4Dup dupGroup,
    runPair (t4Dup.runPlan ops (Start η0)) (dupGroup.runPlan ops (Start η0)))
  (((false, ["cov1Nodup", "accFresh@2"]), (false, ["cov1Nodup", "accFresh@2"]), (false, ["cov1Nodup", "accFresh@2"])), ("done", "done", true, [some 0, some 16, some 0], [some 0, some 16, some 0]))

-- donor pubTwice = [init],[acc],[pub block],[pub [addr 1]]; fused [pub block, pub [addr 1]] (overlapping blocks).
#eval check "t4-a7-pubTwice"
  (verdictTrio t4PubTwice pubTwice,
    runPair (t4PubTwice.runPlan ops (Start η0)) (pubTwice.runPlan ops (Start η0)))
  (((false, ["cov2Nodup", "pubFresh@3"]), (false, ["cov2Nodup", "pubFresh@3"]), (false, ["cov2Nodup", "pubFresh@3"])), ("done", "done", true, [some 0, some 14, some 0], [some 0, some 14, some 0]))

-- donor lateEmptyInit = [init 1],[acc],[init 0 2],[pub block]; fused [init 0 2, pub block] (empty fibers initialised, then published).
#eval check "t4-a9-lateEmptyInit"
  (verdictTrio t4InitPub lateEmptyInit,
    runPair (t4InitPub.runPlan ops (Start η0)) (lateEmptyInit.runPlan ops (Start η0)))
  (((true, []), (true, []), (true, [])), ("done", "done", true, [some 0, some 14, some 0], [some 0, some 14, some 0]))

end LeanNCD.Semantics.PlanFixtures

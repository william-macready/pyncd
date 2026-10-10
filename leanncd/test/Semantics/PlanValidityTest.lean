import Semantics.PlanSimulationTest

/- checkPlan fixtures (A3a). Each row is `(checkPlan, failing clauses in
   checkPlan's order)`: the first entry of the list is the first failing
   clause. Clause names are the Valid fields; `@pc` is the command index. -/

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

/-- Every checkPlan clause with its Bool, in checkPlan's evaluation order. -/
def clauseRow {K : S → Type} {σ : Declarations S} {r : Registry K} {P : Program K σ r}
    [DecidableEq σ.Tensor] (π : P.Plan) : List (String × Bool) :=
  [("singleton", π.checkSingleton), ("cov1Nodup", π.checkCov1Nodup),
    ("cov1Complete", π.checkCov1Complete), ("cov2Nodup", π.checkCov2Nodup),
    ("cov2Complete", π.checkCov2Complete)] ++
  (List.range π.commands.length).flatMap fun pc =>
    match π.commands[pc]? with
    | some [Ann.initZero xs] => [(s!"initFresh@{pc}", π.checkInit pc xs)]
    | some [Ann.acc g] => [(s!"accFresh@{pc}", π.checkAccFresh pc g),
        (s!"accMat@{pc}", π.checkAccMat pc g), (s!"ready@{pc}", π.checkReady pc g)]
    | some [Ann.pub b] => [(s!"pubFresh@{pc}", π.checkPubFresh pc b),
        (s!"pubMat@{pc}", π.checkPubMat pc b), (s!"pubOrder@{pc}", π.checkPubOrder pc b)]
    | _ => []

def verdict {K : S → Type} {σ : Declarations S} {r : Registry K} {P : Program K σ r}
    [DecidableEq σ.Tensor] (π : P.Plan) : Bool × List String :=
  (π.checkPlan, (clauseRow π).filterMap fun (n, b) => if b then none else some n)

/-! ### Valid plans (A2 fixtures) -/

#eval check "valid-accepted"
  [verdict plan, verdict (pPlan 2 reciprocalBody), verdict (pPlan 2 failureAfterBody),
    verdict (sPlan true), verdict (sPlan false), verdict chainPlan]
  [(true, []), (true, []), (true, []), (true, []), (true, []), (true, [])]

-- The same verdicts in the kernel.
example : plan.checkPlan = true := by decide
example : (pPlan 2 reciprocalBody).checkPlan = true := by decide
example : (pPlan 2 failureAfterBody).checkPlan = true := by decide
example : (sPlan true).checkPlan = true := by decide
example : (sPlan false).checkPlan = true := by decide
example : chainPlan.checkPlan = true := by decide

/-! ### A2 invalid plans -/

#eval check "invalid-publish-before-acc" (verdict earlyStep) (false, ["pubOrder@1"])
#eval check "invalid-duplicate-member" (verdict dupGroup) (false, ["cov1Nodup", "accFresh@2"])
#eval check "invalid-missing-init" (verdict noInit) (false, ["accMat@0", "pubMat@1"])
#eval check "invalid-missing-init-empty-fiber" (verdict partialInit) (false, ["pubMat@2"])
#eval check "invalid-fused" (verdict fused) (false, ["singleton"])
#eval check "invalid-read-unpublished" (verdict chainEarly) (false, ["ready@1"])

example : earlyStep.checkPlan = false := by decide
example : dupGroup.checkPlan = false := by decide
example : noInit.checkPlan = false := by decide
example : partialInit.checkPlan = false := by decide
example : fused.checkPlan = false := by decide
example : chainEarly.checkPlan = false := by decide

/-! ### New invalid plans -/

/-- Coverage: the only group omits occurrence (1, 1). -/
def missingOcc : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc [occ 0 0, occ 0 1, occ 1 0]], [.pub block]]

/-- Condition 4: point 1 is published after only the first of two groups. -/
def earlyHalf : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc [occ 0 0, occ 0 1]], [.pub block],
    [.acc [occ 1 0, occ 1 1]]]

#eval check "invalid-missing-occurrence" (verdict missingOcc)
  (false, ["cov1Complete", "pubOrder@2"])
#eval check "invalid-publish-after-one-group" (verdict earlyHalf, outcomeRow (earlyHalf.runPlan ops (Start η0)))
  ((false, ["pubOrder@2"]), ("done", 4, none, [some 0, some 14, some 0]))

example : missingOcc.checkPlan = false := by decide
example : earlyHalf.checkPlan = false := by decide

/-- N2 freshness: re-initialising point 1 after the first group has consumed
    into it. Only `initFresh` rejects it; unchecked, the run silently returns
    10 (the second group alone) instead of 14. -/
def reinitMid : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc [occ 0 0, occ 0 1]], [.initZero block],
    [.acc [occ 1 0, occ 1 1]], [.pub block]]

#eval check "invalid-reinit-after-consume"
  (verdict reinitMid, outcomeRow (reinitMid.runPlan ops (Start η0)))
  ((false, ["initFresh@2"]), ("done", 5, none, [some 0, some 10, some 0]))

example : reinitMid.checkPlan = false := by decide

/-! ### Publication freshness (`checkPubFresh`)

`checkPubFresh` and `checkCov2Nodup` fire together: a member that repeats
inside a block, or that an earlier block already published, is a repeat in
`pubFlat` (a defined address is never an input, so `Pub` is membership in an
earlier block). Neither run goes wrong here: both end `done` with point 1
holding 14, as `plan` does. -/

/-- Point 1 published by the full block, then again by a second block. -/
def pubTwice : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc group], [.pub block], [.pub [addr 1]]]

/-- Point 1 listed twice inside the one publication block. -/
def pubDupIn : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc group], [.pub [addr 0, addr 1, addr 1, addr 2]]]

/-- Accept-neighbour: `plan` with its block split in two; distinct blocks
    over disjoint members are fresh. -/
def pubSplit : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc group], [.pub [addr 0, addr 1]], [.pub [addr 2]]]

#eval check "invalid-publish-twice-across-blocks"
  (verdict pubTwice, outcomeRow (pubTwice.runPlan ops (Start η0)))
  ((false, ["cov2Nodup", "pubFresh@3"]), ("done", 4, none, [some 0, some 14, some 0]))
#eval check "invalid-publish-twice-in-block"
  (verdict pubDupIn, outcomeRow (pubDupIn.runPlan ops (Start η0)))
  ((false, ["cov2Nodup", "pubFresh@2"]), ("done", 3, none, [some 0, some 14, some 0]))
#eval check "valid-publish-split-blocks"
  (verdict pubSplit, outcomeRow (pubSplit.runPlan ops (Start η0)))
  ((true, []), ("done", 4, none, [some 0, some 14, some 0]))

example : pubTwice.checkPlan = false := by decide
example : pubDupIn.checkPlan = false := by decide
example : pubSplit.checkPlan = true := by decide

end LeanNCD.Semantics.PlanFixtures

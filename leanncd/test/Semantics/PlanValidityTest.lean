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

/-! ### Accumulation freshness (`checkAccFresh`)

`checkAccFresh` and `checkCov1Nodup` fire together: a within-group repeat
or a member an earlier group consumed (`dupGroup`) is a repeat in `accFlat`. -/

/-- Occurrence (0, 0) listed twice in the one group. Unchecked, the run
    silently returns 16 (the value 2 counted twice) instead of 14. -/
def dupWithin : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc [occ 0 0, occ 0 0, occ 0 1, occ 1 0, occ 1 1]], [.pub block]]

/-- Accept-neighbour: `plan` with its group split in two disjoint groups. -/
def accSplit : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc [occ 0 0, occ 0 1]], [.acc [occ 1 0, occ 1 1]], [.pub block]]

#eval check "invalid-duplicate-within-group"
  (verdict dupWithin, outcomeRow (dupWithin.runPlan ops (Start η0)))
  ((false, ["cov1Nodup", "accFresh@1"]), ("done", 3, none, [some 0, some 16, some 0]))
#eval check "valid-accumulate-split-groups"
  (verdict accSplit, outcomeRow (accSplit.runPlan ops (Start η0)))
  ((true, []), ("done", 4, none, [some 0, some 14, some 0]))

example : dupWithin.checkPlan = false := by decide
example : accSplit.checkPlan = true := by decide

/-! ### Accumulate into an unmaterialised target (`checkAccMat`)

No plan fails `checkAccMat` alone. If the target `t` of a group at `pc` is
not materialised there, `t` must still be published (else `cov2Complete`);
a publication before `pc` fails `pubOrder` (or `accFresh`, if the member was
consumed earlier); a publication after `pc` either finds `t` unmaterialised
(`pubMat`) or follows an `initZero` of `t` placed after `pc`, which a consumed
occurrence already targets (`initFresh`). Each attempt below shows one branch
(`noInit` above shows `pubMat` with nothing materialised). -/

/-- Materialise every point only after the accumulate. -/
def accThenInit : taggedOut.Plan :=
  unitPlan [[.acc group], [.initZero block], [.pub block]]

/-- Materialise only the empty fibers, never the target. -/
def emptyOnlyInit : taggedOut.Plan :=
  unitPlan [[.initZero [addr 0, addr 2]], [.acc group], [.pub block]]

/-- As `emptyOnlyInit`, but never publish the target. -/
def targetUnpub : taggedOut.Plan :=
  unitPlan [[.initZero [addr 0, addr 2]], [.acc group], [.pub [addr 0, addr 2]]]

/-- Materialise the target between its two groups. -/
def halfThenInit : taggedOut.Plan :=
  unitPlan [[.initZero [addr 0, addr 2]], [.acc [occ 0 0, occ 0 1]], [.initZero [addr 1]],
    [.acc [occ 1 0, occ 1 1]], [.pub block]]

/-- Accept-neighbour: the empty fibers materialised after the accumulate;
    only the target need be materialised before it. -/
def lateEmptyInit : taggedOut.Plan :=
  unitPlan [[.initZero [addr 1]], [.acc group], [.initZero [addr 0, addr 2]], [.pub block]]

#eval check "invalid-acc-unmaterialised-attempts"
  (([accThenInit, emptyOnlyInit, targetUnpub, halfThenInit] : List taggedOut.Plan).map
    fun (π : taggedOut.Plan) => (verdict π, outcomeRow (π.runPlan ops (Start η0))))
  [((false, ["accMat@0", "initFresh@1"]), ("stuck", 0, none, [none, none, none])),
   ((false, ["accMat@1", "pubMat@2"]), ("stuck", 1, none, [some 0, none, some 0])),
   ((false, ["cov2Complete", "accMat@1"]), ("stuck", 1, none, [some 0, none, some 0])),
   ((false, ["accMat@1", "initFresh@2"]), ("stuck", 1, none, [some 0, none, some 0]))]
#eval check "valid-late-empty-fiber-init"
  (verdict lateEmptyInit, outcomeRow (lateEmptyInit.runPlan ops (Start η0)))
  ((true, []), ("done", 4, none, [some 0, some 14, some 0]))

example : accThenInit.checkPlan = false := by decide
example : emptyOnlyInit.checkPlan = false := by decide
example : targetUnpub.checkPlan = false := by decide
example : halfThenInit.checkPlan = false := by decide
example : lateEmptyInit.checkPlan = true := by decide

/-! ### Initialisation of a published address (`checkInit`, not-published half)

`reinitMid` shows the consumed-target half. Here the re-initialised member is
`addr 0`, an empty-fiber address no occurrence targets, so only the
not-published half can reject: it is already published, and the late
`initZero` writes 0 over 0 (the run ends as `plan`'s does). -/

/-- Re-initialise the published empty-fiber address 0 after the publication. -/
def reinitPub : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc group], [.pub block], [.initZero [addr 0]]]

/-- Accept-neighbour: the same `initZero [addr 0]` placed before the publication. -/
def reinitBeforePub : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc group], [.initZero [addr 0]], [.pub block]]

#eval check "invalid-reinit-after-publish"
  (verdict reinitPub, outcomeRow (reinitPub.runPlan ops (Start η0)))
  ((false, ["initFresh@3"]), ("done", 4, none, [some 0, some 14, some 0]))
#eval check "valid-reinit-before-publish"
  (verdict reinitBeforePub, outcomeRow (reinitBeforePub.runPlan ops (Start η0)))
  ((true, []), ("done", 4, none, [some 0, some 14, some 0]))

-- The two halves of `checkInit` at pc 3 for `[addr 0]`, read separately: the
-- consumed-target half holds (no consumed occurrence targets address 0), so
-- the not-published half (address 0 is published) alone causes the rejection.
#eval check "invalid-reinit-after-publish-halves"
  (decide (reinitPub.Pub 3 (addr 0).addr),
    (reinitPub.consList 3).all fun y => decide (y.target ≠ addr 0))
  (true, true)

example : reinitPub.checkPlan = false := by decide
example : reinitBeforePub.checkPlan = true := by decide

/-! ### The empty command

`emptyCmd` (PlanStepTest) is `plan` with `[]` inserted after the init: only
`checkSingleton` rejects it, and the run is `stuck` at the empty command's
index (`stepCommand`'s catch-all), so `singleton` is the guard that matters. -/

#eval check "invalid-empty-command"
  (verdict emptyCmd, outcomeRow (emptyCmd.runPlan ops (Start η0)))
  ((false, ["singleton"]), ("stuck", 1, none, [some 0, some 0, some 0]))

example : emptyCmd.checkPlan = false := by decide

/-! ### The two A2-e distinguishing plans are `checkPlan`-invalid

`a2eSeqVisible` and `a2eFailedVsStuck` (PlanStepTest) are the invalid plans on which the
non-transactional accumulate mutant differs from the shipped kernel; the verdicts below pin
that they are outside `checkPlan`'s domain, where transactional and sequential commit are
unobservable. -/

#eval check "invalid-a2e-seq-visible"
  (verdict a2eSeqVisible) (false, ["pubOrder@1"])

#eval check "invalid-a2e-failed-vs-stuck"
  (verdict a2eFailedVsStuck) (false, ["accMat@1", "pubMat@2"])

example : a2eSeqVisible.checkPlan = false := by decide

example : a2eFailedVsStuck.checkPlan = false := by decide

end LeanNCD.Semantics.PlanFixtures

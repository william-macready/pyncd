import Semantics.PlanFixtures

/- Observed-value checks for reference-side batching (Lemma 32.1). -/

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

def batched := accumulateBatch taggedOut start0 group values
def batchedPerm := accumulateBatch taggedOut start0 groupPerm values

-- All four occurrence identities are retained: 2 + 2 + 5 + 5 = 14 at point 1.
#eval check "batch-accumulators" (accRow batched) [0, 14, 0]
-- Accumulate leaves the published store unchanged.
#eval check "batch-published" (vectorStore batched) [none, none, none]
-- The batch consumes the whole group.
#eval check "batch-pending" (batched.pending T).card 0
-- A permuted enumeration of the same group gives the same accumulators.
#eval check "batch-permuted" (accRow batchedPerm) [0, 14, 0]
-- The reference executor's own trace on `tagged` agrees (donor expectation).
#eval check "batch-agrees-reference"
  (accRow batched, vectorStore (snapshot taggedResult.outcome))
  ([0, 14, 0], [some 0, some 14, some 0])

-- Lemma 32.1 instantiated on the fixture: a genuine reference segment.
example : Execution taggedOut ops (contributionEvents taggedOut group values)
    (.running start0) (.running batched) :=
  batch_execution taggedOut ops start0 group values (by decide)
    (by intro x _; simp [start0, Program.initial])
    (by intro x hx; simp only [group, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> rfl)

example : Execution taggedOut ops (contributionEvents taggedOut groupPerm values)
    (.running start0) (.running batched) :=
  batch_execution_perm taggedOut ops start0 (by decide) values (by decide)
    (by intro x _; simp [start0, Program.initial])
    (by intro x hx; simp only [group, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> rfl)

-- The logical post-state function, prefix by prefix (values from evalReady).
def refRow (pc : Nat) : Option (List ℚ × List (Option ℚ)) :=
  (plan.refState ops η0 pc).map (fun c => (accRow c, vectorStore c))

#eval check "refState-prefixes" ((List.range 4).map refRow)
  [some ([0, 0, 0], [none, none, none]), some ([0, 0, 0], [none, none, none]),
   some ([0, 14, 0], [none, none, none]), some ([0, 14, 0], [some 0, some 14, some 0])]

-- Publishing before accumulating violates the fiber premise: post fails.
def earlyPlan : taggedOut.Plan := unitPlan [[.initZero block], [.pub block], [.acc group]]
#eval check "refState-early-publish" ((earlyPlan.refState ops η0 2).isSome) false

-- Schedule view: 4 occurrence keys + 3 publication keys, all distinct.
#eval check "flat-schedule"
  (plan.accFlat.length, plan.pubFlat.length, plan.flatKeys.length,
    decide plan.accFlat.Nodup, decide plan.pubFlat.Nodup)
  (4, 3, 7, true, true)

end LeanNCD.Semantics.PlanFixtures

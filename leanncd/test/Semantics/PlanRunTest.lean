import Semantics.PlanValidityTest

/- run_R instances (A3a): Valid comes from checkPlan by `decide` and
   `checkPlan_sound`; the run lemma then yields R at pc = m (tagged) and a
   matched reference failure (scalarRole true), with no hand-chained steps. -/

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

theorem plan_valid : plan.Valid := plan.checkPlan_sound (by decide)

/-- R at pc = length on the memory runPlan actually returns, from `run_R`. -/
theorem tagged_run_R :
    ∃ c, plan.refState ops η0 3 = some c ∧ plan.R ops η0 3 m3 c ∧
      ∃ events, Execution taggedOut ops events (.running start0) (.running c) := by
  have hrun : plan.runPlan ops (Start η0) = .done 3 m3 := rfl
  rcases runPlan_R ops plan_valid η0 with ⟨M', c', h, hc, hR, hex⟩ | ⟨_, _, _, _, _, h, -⟩
  · rw [hrun] at h
    obtain ⟨-, rfl⟩ := PlanOutcome.done.inj h
    exact ⟨c', hc, hR, hex⟩
  · rw [hrun] at h
    cases h

theorem sPlan_bad_valid : (sPlan true).Valid := (sPlan true).checkPlan_sound (by decide)

/-- scalarRole true fails at pc 3 on tensor 2; run_R supplies the matching
    reference execution to a failed state, and that failure is on tensor 2. -/
theorem scalar_bad_matched :
    ∃ o M' c' events, (sPlan true).runPlan ops (Start (scalarInput true)) = .failed o 3 M' ∧
      o.1.val = 2 ∧
      Execution (scalarRole true) ops events (.running ((scalarRole true).initial (scalarInput true)))
        (.failed o.1 o.2 c') := by
  rcases runPlan_R ops sPlan_bad_valid (scalarInput true) with
    ⟨_, _, h, -⟩ | ⟨o, pc', M', c', ev, h, hex⟩
  · have hrun : (sPlan true).runPlan ops (Start (scalarInput true)) =
        .failed (sOcc true 2 rfl) 3 (finalMemory (sRun true)) := rfl
    rw [hrun] at h
    cases h
  · have hrun : (sPlan true).runPlan ops (Start (scalarInput true)) =
        .failed (sOcc true 2 rfl) 3 (finalMemory (sRun true)) := rfl
    rw [hrun] at h
    obtain ⟨rfl, rfl, rfl⟩ := PlanOutcome.failed.inj h
    exact ⟨_, _, c', ev, hrun, rfl, hex⟩

#print axioms plan_valid
#print axioms tagged_run_R
#print axioms scalar_bad_matched

end LeanNCD.Semantics.PlanFixtures

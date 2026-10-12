import Semantics.PlanReuseTest

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

-- Only grouping changes: allocation and all other annotations come from the accepted donor.
def reuseFused : (routed chainBody).Plan :=
  { reuseGood with commands := reuseGood.commands.take 3 ++
      [[.retire [cAddr 0], .initZero [cAddr 2]]] ++ reuseGood.commands.drop 5 }

def reuseFusedConflict : (routed chainBody).Plan :=
  { reuseGood with commands := reuseGood.commands.take 3 ++
      [[.initZero [cAddr 2], .retire [cAddr 0]]] ++ reuseGood.commands.drop 5 }

#eval check "reuse-fused-accepted"
  (reuseFused.checkPlanF, chainRow reuseFused, reuseDecode reuseFused)
  (true, ("done", 6, none, [some 4, some 3, some 4]), some [])

theorem reuseFused_expand : reuseFused.expand = reuseGood := rfl
example : reuseFused.allocation = reuseGoodAllocation := rfl
example : reuseFusedConflict.allocation = reuseGoodAllocation := rfl

theorem reuseFused_valid : reuseFused.FValid := by
  change reuseFused.expand.Valid
  rw [reuseFused_expand]
  exact reuseGood_valid

example : reuseFused.checkPlanF = true :=
  reuseFused.checkPlanF_complete reuseFused_valid

theorem reuseFused_done :
    reuseFused.runPlan ops (reuseFused.Start chainInput) =
      .done 6 (chainMem reuseFused 6) := rfl

theorem reuseFused_R_every_pc : ∀ pc, pc ≤ 6 → ∃ c,
    reuseFused.refState ops chainInput pc = some c ∧
      reuseFused.R ops chainInput pc (chainMem reuseFused pc) c :=
  R_every_pc_F_of reuseFused reuseFused_valid 6 rfl
    (by intro k hk; interval_cases k <;> rfl)

example : PlanOutcome.Agree
    (reuseFused.runPlan ops (reuseFused.Start chainInput))
    (reuseFused.expand.runPlan ops (reuseFused.expand.Start chainInput)) := by
  have hs : reuseFused.expand.Start chainInput = reuseFused.Start chainInput := by
    funext ξ
    cases ξ <;> rfl
  simpa only [hs] using reuseFused.runPlan_agree ops (reuseFused.Start chainInput)

#eval check "reuse-fused-shared-slot-trace"
  [chainMem reuseFused 3 reuseSharedSlot, chainMem reuseFused 4 reuseSharedSlot,
    chainMem reuseFused 5 reuseSharedSlot, chainMem reuseFused 6 reuseSharedSlot]
  [some 0, some 0, some 4, some 4]
#eval check "reuse-fused-retired-read-vs-ghost"
  (reuseFused.readPub 6 (chainMem reuseFused 6) (cAddr 0).addr,
    (reuseFused.refState ops chainInput 6).bind fun c => c.published (cAddr 0).addr,
    reuseFused.readPub 6 (chainMem reuseFused 6) (cAddr 2).addr)
  (none, some 0, some 4)

-- Both outer sides are injective. Only the expansion sees pub 0 collide with acc 2.
#eval check "reuse-fused-conflict-outer-vs-internal"
  ((List.range 7).map reuseFusedConflict.checkLayoutAt,
    (List.range 8).map reuseFusedConflict.expand.checkLayoutAt,
    reuseFusedConflict.checkLayouts, reuseFusedConflict.expand.checkLayouts,
    reuseFusedConflict.checkPlanF)
  ([true, true, true, true, true, true, true],
    [true, true, true, true, false, true, true, true], true, false, false)
#eval check "reuse-fused-conflict-resource-boundaries"
  (reuseRoles reuseFusedConflict 3, reuseRoles reuseFusedConflict.expand 4,
    reuseRoles reuseFusedConflict 4)
  ([true, true, false, false, false, false],
    [true, true, false, false, false, true],
    [false, true, false, false, false, true])
#eval check "reuse-fused-conflict-unchecked-run" (chainRow reuseFusedConflict)
  ("stuck", 4, none, [none, some 3, none])

example : ¬ reuseFusedConflict.expand.LayoutOK 4 := by
  intro h
  have he := h (.pub (cAddr 0).addr) (.acc (cAddr 2)) reuseSharedSlot rfl rfl
  cases he

-- The oracle is consulted before pub 2, after acc 2 has committed its write to the reused slot.
theorem reuseFused_fault_after_write :
    reuseFused.runPlanE ops (faultAt 6 .kernelFault) (reuseFused.Start chainInput) =
      .error .kernelFault 5 (chainMem reuseFused 5) := rfl

#eval check "reuse-fused-fault-after-write"
  (chainRowE reuseFused (faultAt 6 .kernelFault))
  ("error", 5, some .kernelFault, [some 4, some 3, some 4])
#eval check "reuse-fused-fault-physical-vs-ghost"
  (chainMem reuseFused 5 reuseSharedSlot,
    reuseFused.readPub 5 (chainMem reuseFused 5) (cAddr 0).addr,
    (reuseFused.refState ops chainInput 5).bind fun c => c.published (cAddr 0).addr)
  (some 4, none, some 0)

theorem reuseFused_error_R : ∃ c,
    reuseFused.refState ops chainInput 5 = some c ∧
      reuseFused.R ops chainInput 5 (chainMem reuseFused 5) c :=
  runPlanE_error_R ops reuseFused_valid (faultAt 6 .kernelFault) chainInput
    reuseFused_fault_after_write

theorem reuseFused_noFaults : reuseFused.NoFaultsInPlan (fun _ => none) :=
  by intro _ _; rfl

theorem reuseFused_noFault_parity :
    reuseFused.runPlanE ops (fun _ => none) (reuseFused.Start chainInput) =
      .run (reuseFused.runPlan ops (reuseFused.Start chainInput)) :=
  reuseFused.runPlanE_noFault ops (by intro _; rfl) _

#eval check "reuse-fused-fault-free-wrapper" (chainRowE reuseFused (fun _ => none))
  ("run:done", 6, none, [some 4, some 3, some 4])

theorem reuseFused_errorFree :
    reuseFused.ErrorFreeRun ops (fun _ => none) (reuseFused.Start chainInput) :=
  reuseFused.errorFreeRun_of_noFaultsInPlan ops reuseFused_noFaults _

theorem reuseFused_done_iff_model :
    (∃ m M, reuseFused.runPlanE ops (fun _ => none) (reuseFused.Start chainInput) =
      .run (.done m M)) ↔ ∃ ρ, (routed chainBody).Models ops chainInput ρ :=
  done_iff_model_FE ops reuseFused_valid _ chainInput reuseFused_errorFree

theorem reuseFused_wrapper_model_unique : ∃ ρ,
    (∀ ρ', (routed chainBody).Models ops chainInput ρ' ↔ ρ' = ρ) ∧
      reuseFused.Decode 6 (chainMem reuseFused 6) =
        some ((routed chainBody).outputProjection ρ) := by
  have hrun : reuseFused.runPlanE ops (fun _ => none) (reuseFused.Start chainInput) =
      .run (.done 6 (chainMem reuseFused 6)) := by
    rw [reuseFused_noFault_parity, reuseFused_done]
  obtain ⟨c, success, hmod, hd, -⟩ :=
    done_correct_FE ops reuseFused_valid (fun _ => none) chainInput hrun
  exact ⟨_, hmod, hd⟩

#print axioms reuseFused_R_every_pc
#print axioms reuseFused_error_R
#print axioms reuseFused_noFault_parity
#print axioms reuseFused_done_iff_model
#print axioms reuseFused_wrapper_model_unique

end LeanNCD.Semantics.PlanFixtures

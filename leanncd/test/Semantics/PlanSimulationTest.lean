import Semantics.PlanStepTest

/- Elaborated simulation instances: R at every pc of the taggedOut plan along
   the actual concrete run, failure matching on failureAfterBody, and the D9
   counterexample (disjointness of groups does not follow from 2 + 4). -/

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

theorem group_complete (y : OccRef taggedOut) : y ∈ group := by
  rcases y with ⟨⟨⟨⟩, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
  fin_cases s <;> fin_cases v <;> simp [group, occ, T]

/-! ### The concrete memories of the run, by `stepPlan` -/

def m1 : Memory Carrier declarations := execInit block (Start η0)
def m2 : Memory Carrier declarations :=
  match plan.stepPlan ops 1 m1 with | .ok M => M | _ => m1
def m3 : Memory Carrier declarations :=
  match plan.stepPlan ops 2 m2 with | .ok M => M | _ => m2

theorem run0 : plan.stepPlan ops 0 (Start η0) = .ok m1 := rfl
theorem run1 : plan.stepPlan ops 1 m1 = .ok m2 := rfl
theorem run2 : plan.stepPlan ops 2 m2 = .ok m3 := rfl

theorem ok0 : plan.AnnOK 0 (.initZero block) := by
  intro x _
  exact ⟨fun h => by simp [(plan.pub_zero _)] at h, fun o h => absurd h (plan.not_cons_zero _)⟩

theorem ok1 : plan.AnnOK 1 (.acc group) := by
  refine ⟨by decide, fun x hx => ?_⟩
  simp only [group, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem ok2 : plan.AnnOK 2 (.pub block) := by
  refine ⟨by decide, fun x hx => ⟨?_, ?_, fun o _ => ?_⟩⟩
  · simp only [block, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> decide
  · simp only [block, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> decide
  · show _ ∈ plan.consList 2
    rw [show plan.consList 2 = group from rfl]
    exact group_complete _

/-- R holds at every pc along the actual run, with refState as the witness. -/
theorem tagged_R_every_pc :
    plan.R ops η0 0 (Start η0) start0 ∧
    (∃ c, plan.refState ops η0 1 = some c ∧ plan.R ops η0 1 m1 c) ∧
    (∃ c, plan.refState ops η0 2 = some c ∧ plan.R ops η0 2 m2 c) ∧
    (∃ c, plan.refState ops η0 3 = some c ∧ plan.R ops η0 3 m3 c) := by
  have R0 := plan.R_start ops η0
  have hc0 : plan.refState ops η0 0 = some start0 := rfl
  obtain ⟨c1, hc1, R1, -⟩ := step_R ops R0 hc0 rfl ok0 run0
  obtain ⟨c2, hc2, R2, -⟩ := step_R ops R1 hc1 rfl ok1 run1
  obtain ⟨c3, hc3, R3, -⟩ := step_R ops R2 hc2 rfl ok2 run2
  exact ⟨R0, ⟨c1, hc1, R1⟩, ⟨c2, hc2, R2⟩, ⟨c3, hc3, R3⟩⟩

-- The proved-related final memory is the one runPlan returns.
example : finalMemory taggedRun = m3 := rfl
#eval check "sim-tagged-m-rows"
  ([m1, m2, m3].map (fun M => block.map (fun x => M (place x.addr))))
  [[some 0, some 0, some 0], [some 0, some 14, some 0], [some 0, some 14, some 0]]

/-! ### Failure matching on failureAfterBody -/

abbrev FP := program 2 failureAfterBody

def fm1 : Memory Carrier declarations := execInit (pBlock 2 failureAfterBody) (Start (pInput 2 failureAfterBody))

theorem fOk0 : (pPlan 2 failureAfterBody).AnnOK 0 (.initZero (pBlock 2 failureAfterBody)) := by
  intro x _
  exact ⟨fun h => by simp [((pPlan 2 failureAfterBody).pub_zero _)] at h,
    fun o h => absurd h ((pPlan 2 failureAfterBody).not_cons_zero _)⟩

theorem fRun1 : (pPlan 2 failureAfterBody).stepPlan ops 1 fm1 = .semFail (pOcc 2 failureAfterBody 1) :=
  rfl

/-- The plan's reported failure is a reference `undefined` event from the
    related state, so the input has no model. -/
theorem failure_matched :
    ∃ c, (pPlan 2 failureAfterBody).refState ops (pInput 2 failureAfterBody) 1 = some c ∧
      Execution FP ops [.undefined (pOcc 2 failureAfterBody 1).1 (pOcc 2 failureAfterBody 1).2]
        (.running c) (.failed (pOcc 2 failureAfterBody 1).1 (pOcc 2 failureAfterBody 1).2 c) ∧
      ¬ ∃ ρ, FP.Models ops (pInput 2 failureAfterBody) ρ := by
  have R0 := (pPlan 2 failureAfterBody).R_start ops (pInput 2 failureAfterBody)
  obtain ⟨c1, hc1, R1, -⟩ := step_R ops R0 rfl rfl fOk0 rfl
  have notCons : ∀ G, [Ann.acc ((List.finRange 2).map (pOcc 2 failureAfterBody))] = [.acc G] →
      ∀ x ∈ G, ¬ (pPlan 2 failureAfterBody).Cons 1 x := by
    intro G hG x _ hx
    simp [Cons, consList, prefixAnn, pPlan, unitPlan, Ann.groups] at hx
  exact ⟨c1, hc1, step_failed ops R1 rfl notCons fRun1,
    step_failed_no_model ops R1 rfl notCons fRun1⟩

/-! ### D9: disjointness of groups does not follow from conditions 2 and 4 -/

def twice : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc group], [.acc group], [.pub block]]

theorem twice_pub_complete (y : DefAddr taggedOut) : y ∈ twice.pubFlat := by
  rcases y with ⟨⟨⟨⟩, ht⟩, ⟨i, u⟩⟩
  cases u
  fin_cases i <;> decide +revert

theorem twice_order4 : twice.Order4 := by
  intro pc a h y hy o _
  match pc, h with
  | 3, h =>
    show _ ∈ twice.consList 3
    rw [show twice.consList 3 = group ++ group from rfl]
    exact List.mem_append_left _ (group_complete _)
  | 0, h | 1, h | 2, h =>
    simp only [twice, unitPlan, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq, List.cons.injEq, and_true] at h
    subst h
    simp [Ann.blocks] at hy
  | _ + 4, h => simp [twice, unitPlan] at h

theorem twice_not_disjoint : ¬ twice.accFlat.Nodup := by decide

-- Conditions 2 (union half) and 4 hold, so D9 gives coverage; disjointness fails.
example : ∀ x, x ∈ twice.accFlat :=
  accFlat_complete twice (fun cmd h => by
    simp only [twice, unitPlan, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
    twice_pub_complete twice_order4

end LeanNCD.Semantics.PlanFixtures

import Semantics.PlanRetireTest

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

/- All three physical buffers have the same sort and capacity, but independent identities.
   Only slot 0 is placed; slot 1 and the third buffer exercise unmapped storage. -/
def reuseAllocation (lastBuffer : Fin 3) : Allocation (routed chainBody) where
  Buffer := Fin 3
  bufferEq := inferInstance
  buffers := [0, 1, 2]
  buffers_nodup := by decide
  buffers_complete := by intro b; fin_cases b <;> simp
  sort := fun _ => ()
  capacity := fun _ => 2
  locate := fun x =>
    ⟨⟨if x.2.1 = 2 then lastBuffer else x.2.1, (0 : Fin 2)⟩, rfl⟩

def reuseGoodAllocation : Allocation (routed chainBody) := reuseAllocation 0
def reuseBadAllocation : Allocation (routed chainBody) := reuseAllocation 1
def reuseSeparateAllocation : Allocation (routed chainBody) := reuseAllocation 2

def reuseGood : (routed chainBody).Plan :=
  { rtInitAfter with allocation := reuseGoodAllocation }
def reuseBad : (routed chainBody).Plan :=
  { rtInitAfter with allocation := reuseBadAllocation }

def reuseDecode (π : (routed chainBody).Plan) : Option (List ℚ) :=
  match π.runPlan ops (π.Start chainInput) with
  | .done pc M =>
    (π.Decode pc M).map fun out =>
      (π.tensors.filterMap fun t =>
        if h : (routed chainBody).output t = true then
          some ((List.finRange 3).map fun i => out ⟨t, h⟩ (point i))
        else none).flatten
  | _ => none

-- Raw rows intentionally expose physical aliasing; published reads below exclude retired ghosts.
#eval check "reuse-good-run" (reuseGood.checkPlan, chainRow reuseGood)
  (true, ("done", 7, none, [some 4, some 3, some 4]))
#eval check "reuse-good-empty-output" (reuseDecode reuseGood) (some [])
#eval check "reuse-bad-live-alias-run" (reuseBad.checkPlan, chainRow reuseBad)
  (false, ("done", 7, none, [none, some 1, some 1]))

set_option maxHeartbeats 1000000 in
theorem reuseGood_layout : ∀ pc, pc ≤ 7 → reuseGood.LayoutOK pc := by
  intro pc hpc
  interval_cases pc <;>
    rintro (⟨⟨⟩, ⟨i, ⟨⟩⟩⟩ | ⟨⟨⟨⟩, hi⟩, ⟨i, ⟨⟩⟩⟩)
      (⟨⟨⟩, ⟨j, ⟨⟩⟩⟩ | ⟨⟨⟨⟩, hj⟩, ⟨j, ⟨⟩⟩⟩) ξ h₁ h₂ <;>
    fin_cases i <;> fin_cases j <;>
    simp [SlotView, Live, Pub, Ret, Mat, pubList, retList, matList, prefixAnn,
      Ann.blocks, Ann.rets, Ann.inits, DefAddr.addr, reuseGood, rtInitAfter, unitPlan, cAddr, point,
      routed, program, place, reuseGoodAllocation, reuseAllocation] at h₁ h₂ <;>
    simp_all <;> cases h₁ <;> cases h₂

theorem reuseGood_valid : reuseGood.Valid := by
  apply reuseGood.checkPlan_sound
  rw [checkPlan]
  have hb : (reuseGood.checkSingleton && reuseGood.checkCov1Nodup &&
      reuseGood.checkCov1Complete && reuseGood.checkCov2Nodup &&
      reuseGood.checkCov2Complete && reuseGood.checkSteps) = true := by decide
  rw [hb, Bool.true_and]
  exact reuseGood.checkLayouts_iff.mpr (by simpa [reuseGood, rtInitAfter, unitPlan]
    using reuseGood_layout)

theorem reuseGood_R_every_pc : ∀ pc, pc ≤ 7 → ∃ c,
    reuseGood.refState ops chainInput pc = some c ∧
      reuseGood.R ops chainInput pc (chainMem reuseGood pc) c :=
  R_every_pc_of reuseGood reuseGood_valid 7 rfl
    (by intro k hk; interval_cases k <;> rfl)

example : place reuseGood.allocation (cAddr 0).addr =
    place reuseGood.allocation (cAddr 2).addr := rfl
example : place reuseGood.allocation (cAddr 0).addr ≠
    place reuseGood.allocation (cAddr 1).addr := by
  intro h
  cases h

def reuseSharedSlot : Slot reuseGood.allocation := .inr ⟨(0 : Fin 3), (0 : Fin 2)⟩
def reuseSpareCapacity : Slot reuseGood.allocation := .inr ⟨(0 : Fin 3), (1 : Fin 2)⟩
def reuseSpareBuffer : Slot reuseGood.allocation := .inr ⟨(2 : Fin 3), (0 : Fin 2)⟩

example : place reuseGood.allocation (cAddr 0).addr = reuseSharedSlot := rfl
example : chainMem reuseGood 4 reuseSharedSlot = none := rfl
example : chainMem reuseGood 5 reuseSharedSlot = some 0 := rfl
#eval check "reuse-shared-slot-trace"
  ([chainMem reuseGood 4 reuseSharedSlot, chainMem reuseGood 5 reuseSharedSlot,
    chainMem reuseGood 6 reuseSharedSlot, chainMem reuseGood 7 reuseSharedSlot])
  [none, some 0, some 4, some 4]
#eval check "reuse-retired-ghost-vs-live"
  (reuseGood.readPub 7 (chainMem reuseGood 7) (cAddr 0).addr,
    (reuseGood.refState ops chainInput 7).bind fun c => c.published (cAddr 0).addr,
    reuseGood.readPub 7 (chainMem reuseGood 7) (cAddr 2).addr)
  (none, some 0, some 4)
#eval check "reuse-bad-corrupted-live-source"
  (reuseBad.readPub 7 (chainMem reuseBad 7) (cAddr 1).addr,
    (reuseBad.refState ops chainInput 7).bind fun c => c.published (cAddr 1).addr,
    reuseBad.readPub 7 (chainMem reuseBad 7) (cAddr 2).addr)
  (some 1, some 3, some 1)

theorem reuseGood_unused_dead_every_pc : ∀ pc, pc ≤ 7 →
    chainMem reuseGood pc reuseSpareCapacity = none ∧
      chainMem reuseGood pc reuseSpareBuffer = none := by
  intro pc hpc
  obtain ⟨c, _, hR⟩ := reuseGood_R_every_pc pc hpc
  have hCapacity : ∀ res, reuseGood.SlotView pc res ≠ some reuseSpareCapacity := by
    intro res
    cases res <;> simp only [SlotView] <;> split_ifs <;>
      simp [place, reuseGood, reuseGoodAllocation, reuseAllocation, reuseSpareCapacity,
        routed, program]
  have hBuffer : ∀ res, reuseGood.SlotView pc res ≠ some reuseSpareBuffer := by
    intro res
    cases res <;> simp only [SlotView] <;> split_ifs <;>
      simp [place, reuseGood, reuseGoodAllocation, reuseAllocation, reuseSpareBuffer,
        routed, program] <;> split_ifs <;> simp_all
  exact ⟨hR.dead _ hCapacity, hR.dead _ hBuffer⟩

/- The component rows isolate the represented pair at the selected boundary.
   Coverage/step validity of these schedules is deliberately not a premise. -/
def reusePairPlan (A : Allocation (routed chainBody))
    (cmds : List (Command (routed chainBody))) : (routed chainBody).Plan :=
  { unitPlan cmds with allocation := A }

def reusePubPair (A : Allocation (routed chainBody)) : (routed chainBody).Plan :=
  reusePairPlan A [[.initZero [cAddr 1]], [.acc [cOcc 0]], [.pub [cAddr 1]],
    [.initZero [cAddr 2]], [.acc [cOcc 1]], [.pub [cAddr 2]]]
def reuseAccPair (A : Allocation (routed chainBody)) : (routed chainBody).Plan :=
  reusePairPlan A [[.initZero [cAddr 1, cAddr 2]]]

def reuseRoles (π : (routed chainBody).Plan) (pc : Nat) : List Bool :=
  [Resource.pub (cAddr 0).addr, .pub (cAddr 1).addr, .pub (cAddr 2).addr,
    .acc (cAddr 0), .acc (cAddr 1), .acc (cAddr 2)].map fun res =>
      (π.SlotView pc res).isSome

#eval check "reuse-pub-pub-component"
  ((reusePubPair reuseBadAllocation).checkLayoutAt 6,
    (reusePubPair reuseSeparateAllocation).checkLayoutAt 6,
    reuseRoles (reusePubPair reuseBadAllocation) 6)
  (false, true, [false, true, true, false, false, false])
#eval check "reuse-pub-acc-component"
  ((reusePubPair reuseBadAllocation).checkLayoutAt 4,
    (reusePubPair reuseSeparateAllocation).checkLayoutAt 4,
    reuseRoles (reusePubPair reuseBadAllocation) 4)
  (false, true, [false, true, false, false, false, true])
#eval check "reuse-acc-acc-component"
  ((reuseAccPair reuseBadAllocation).checkLayoutAt 1,
    (reuseAccPair reuseSeparateAllocation).checkLayoutAt 1,
    reuseRoles (reuseAccPair reuseBadAllocation) 1)
  (false, true, [false, false, false, false, true, true])

theorem reuseSeparate_place_injective :
    Function.Injective (place reuseSeparateAllocation) := by
  rintro ⟨⟨⟩, ⟨i, ⟨⟩⟩⟩ ⟨⟨⟩, ⟨j, ⟨⟩⟩⟩ h
  fin_cases i <;> fin_cases j <;> cases h <;> rfl

example : ¬ (reusePubPair reuseBadAllocation).LayoutOK 6 := by
  intro h
  have he := h (.pub (cAddr 1).addr) (.pub (cAddr 2).addr)
    (place reuseBadAllocation (cAddr 1).addr) rfl rfl
  have hc := congrArg (fun res : Resource (routed chainBody) =>
    match res with | .pub a => a.2.1 | .acc x => x.2.1) he
  cases hc
example : (reusePubPair reuseSeparateAllocation).LayoutOK 6 :=
  (reusePubPair reuseSeparateAllocation).layoutOK_of_place_injective
    reuseSeparate_place_injective 6
example : ¬ (reusePubPair reuseBadAllocation).LayoutOK 4 := by
  intro h
  have he := h (.pub (cAddr 1).addr) (.acc (cAddr 2))
    (place reuseBadAllocation (cAddr 1).addr) rfl rfl
  cases he
example : (reusePubPair reuseSeparateAllocation).LayoutOK 4 :=
  (reusePubPair reuseSeparateAllocation).layoutOK_of_place_injective
    reuseSeparate_place_injective 4
example : ¬ (reuseAccPair reuseBadAllocation).LayoutOK 1 := by
  intro h
  have he := h (.acc (cAddr 1)) (.acc (cAddr 2))
    (place reuseBadAllocation (cAddr 1).addr) rfl rfl
  have hc := congrArg (fun res : Resource (routed chainBody) =>
    match res with | .pub a => a.2.1 | .acc x => x.2.1) he
  cases hc
example : (reuseAccPair reuseSeparateAllocation).LayoutOK 1 :=
  (reuseAccPair reuseSeparateAllocation).layoutOK_of_place_injective
    reuseSeparate_place_injective 1

-- The only collision appears at the final init boundary; omitting it accepts this component.
#eval check "reuse-final-boundary-coverage"
  ((reuseAccPair reuseBadAllocation).checkLayoutAt 0,
    (reuseAccPair reuseBadAllocation).checkLayoutAt 1,
    (reuseAccPair reuseBadAllocation).checkLayouts,
    (reuseAccPair reuseSeparateAllocation).checkLayouts)
  (true, false, false, true)

#print axioms reuseGood_R_every_pc
#print axioms reuseGood_unused_dead_every_pc

end LeanNCD.Semantics.PlanFixtures

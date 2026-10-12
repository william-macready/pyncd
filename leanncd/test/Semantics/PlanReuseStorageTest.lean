import Semantics.PlanRetireTest
import Semantics.PlanMultiSortTest

namespace LeanNCD.Semantics.PlanReuseStorage

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures
open PlanFixtures

/- Tensor 2 and output tensor 1 have different logical identities, but share
   index 0 of a single independent buffer. Index 1 is deliberately unused. -/
inductive ReuseBuffer
  | workspace
  deriving DecidableEq

def reuseAllocation : Allocation (scalarRole false) where
  Buffer := ReuseBuffer
  bufferEq := inferInstance
  buffers := [.workspace]
  buffers_nodup := by simp
  buffers_complete := by intro b; cases b; simp
  sort := fun _ => ()
  capacity := fun _ => 2
  locate := fun _ => ⟨⟨.workspace, 0⟩, rfl⟩

def reuse : (scalarRole false).Plan :=
  { scalarPlan false
      [[.initZero [sAddr false 2 rfl]], [.acc [sOcc false 2 rfl]],
       [.pub [sAddr false 2 rfl]], [.retire [sAddr false 2 rfl]],
       [.initZero [sAddr false 1 rfl]], [.acc [sOcc false 1 rfl]],
       [.pub [sAddr false 1 rfl]]] with
    allocation := reuseAllocation }

def reuseRun := reuse.runPlan ops (reuse.Start (scalarInput false))

def reusePrefix (pc : Nat) :=
  reuse.runFrom ops 0 (reuse.Start (scalarInput false)) (reuse.commands.take pc)

def reuseMemory (pc : Nat) := finalMemory (reusePrefix pc)

def reusePhysical (pc : Nat) : List (Option ℚ) :=
  [reuseMemory pc (.inr ⟨.workspace, ⟨0, by decide⟩⟩),
   reuseMemory pc (.inr ⟨.workspace, ⟨1, by decide⟩⟩)]

def reuseLogical (pc : Nat) : List (Option ℚ) :=
  [reuse.readPub pc (reuseMemory pc) ⟨0, ()⟩,
   reuse.readPub pc (reuseMemory pc) ⟨1, ()⟩,
   reuse.readPub pc (reuseMemory pc) ⟨2, ()⟩]

def reuseGhost (pc : Nat) : Option ℚ :=
  (reuse.refState ops (scalarInput false) pc).bind fun c => c.published ⟨2, ()⟩

def reuseKind : String × Nat :=
  match reuseRun with
  | .done pc _ => ("done", pc)
  | .failed _ pc _ => ("failed", pc)
  | .stuck pc _ => ("stuck", pc)

example : (sAddr false 1 rfl).addr ≠ (sAddr false 2 rfl).addr := by decide
example : place reuse.allocation ⟨1, ()⟩ = place reuse.allocation ⟨2, ()⟩ := rfl
example : place reuse.allocation ⟨0, ()⟩ = .inl ⟨⟨0, rfl⟩, ⟨0, by decide⟩⟩ := rfl
example : place reuse.allocation ⟨1, ()⟩ =
    .inr ⟨.workspace, ⟨0, by decide⟩⟩ := rfl

-- Keeping the internal publication alive prevents even the output initializer.
def retainedInternal : (scalarRole false).Plan :=
  { reuse with commands :=
      [[.initZero [sAddr false 2 rfl]], [.acc [sOcc false 2 rfl]],
       [.pub [sAddr false 2 rfl]], [.initZero [sAddr false 1 rfl]],
       [.acc [sOcc false 1 rfl]], [.pub [sAddr false 1 rfl]],
       [.retire [sAddr false 2 rfl]]] }

-- After publication, output storage cannot be cleared or claimed again.
def retireOutput : (scalarRole false).Plan :=
  { reuse with commands := reuse.commands ++ [[.retire [sAddr false 1 rfl]]] }

def overwriteOutput : (scalarRole false).Plan :=
  { reuse with commands := reuse.commands ++ [[.initZero [sAddr false 2 rfl]]] }

set_option maxHeartbeats 1000000 in
theorem reuse_layout : ∀ pc, pc ≤ 7 → reuse.LayoutOK pc := by
  intro pc hpc
  interval_cases pc <;>
    rintro (⟨t, ⟨⟩⟩ | ⟨⟨t, ht⟩, ⟨⟩⟩)
      (⟨u, ⟨⟩⟩ | ⟨⟨u, hu⟩, ⟨⟩⟩) ξ h₁ h₂ <;>
    fin_cases t <;> fin_cases u <;>
    simp [SlotView, Live, Pub, Ret, Mat, pubList, retList, matList, prefixAnn,
      Ann.blocks, Ann.rets, Ann.inits, DefAddr.addr, reuse, scalarPlan,
      sAddr, scalarRole, place, reuseAllocation] at h₁ h₂ <;>
    simp_all [scalarRole] <;> cases h₁ <;> cases h₂

theorem reuse_valid : reuse.Valid := reuse.checkPlan_sound (by
  have hb : (reuse.checkSingleton && reuse.checkCov1Nodup && reuse.checkCov1Complete &&
      reuse.checkCov2Nodup && reuse.checkCov2Complete && reuse.checkSteps) = true := by decide
  rw [checkPlan, hb, Bool.true_and]
  exact reuse.checkLayouts_iff.mpr reuse_layout)

theorem reuse_done :
    reuseRun = .done 7 (finalMemory reuseRun) := by rfl

theorem reuse_R :
    ∃ c, reuse.refState ops (scalarInput false) 7 = some c ∧
      reuse.R ops (scalarInput false) 7 (finalMemory reuseRun) c := by
  rcases reuse.runPlan_R ops reuse_valid (scalarInput false) with
    ⟨M, c, hrun, hc, hR, _⟩ | ⟨o, pc, M, c, events, hrun, _⟩
  · have h : PlanOutcome.done 7 (finalMemory reuseRun) = .done 7 M :=
      reuse_done.symm.trans hrun
    cases h
    exact ⟨c, hc, hR⟩
  · have h := reuse_done.symm.trans hrun
    cases h

#eval check "storage-cross-tensor-decode"
  (reuse.checkPlan, reuseKind, sDecodeOf reuse, sDecodeOf (sPlan false), sDecodeOf rtScalar)
  (true, ("done", 7), some 2, some 2, some 2)
#eval check "storage-cross-tensor-all-boundaries"
  ((List.range 8).map fun pc => (pc, reusePhysical pc, reuseLogical pc, reuseGhost pc))
  [(0, [none, none], [some 7, none, none], none),
   (1, [some 0, none], [some 7, none, none], none),
   (2, [some 3, none], [some 7, none, none], none),
   (3, [some 3, none], [some 7, none, some 3], some 3),
   (4, [none, none], [some 7, none, none], some 3),
   (5, [some 0, none], [some 7, none, none], some 3),
   (6, [some 2, none], [some 7, none, none], some 3),
   (7, [some 2, none], [some 7, some 2, none], some 3)]
#eval check "storage-retention-rejections"
  (retainedInternal.checkPlan, retainedInternal.checkLayouts,
    retireOutput.checkPlan, overwriteOutput.checkPlan)
  (false, false, false, false)

/- Physical buffer names do not come from the tensors, and scalar coordinates
   need not occupy index 0. Sort compatibility is certified by `locate`. -/
inductive TypedBuffer
  | integerBank
  | rationalBank
  deriving DecidableEq

def typedAllocation : Allocation PlanMultiSort.prog where
  Buffer := TypedBuffer
  bufferEq := inferInstance
  buffers := [.rationalBank, .integerBank]
  buffers_nodup := by decide
  buffers_complete := by intro b; cases b <;> simp
  sort := fun b => match b with
    | .integerBank => false
    | .rationalBank => true
  capacity := fun b => match b with
    | .integerBank => 3
    | .rationalBank => 2
  locate := fun x => match x.1.val with
    | 0 => ⟨⟨.integerBank, 1⟩, rfl⟩
    | 1 => ⟨⟨.rationalBank, 0⟩, rfl⟩

def typed : PlanMultiSort.prog.Plan :=
  { PlanMultiSort.pl with allocation := typedAllocation }

def typedRun := typed.runPlan PlanMultiSort.msOps (typed.Start PlanMultiSort.η)

def typedMemory (pc : Nat) :=
  finalMemory (typed.runFrom PlanMultiSort.msOps 0 (typed.Start PlanMultiSort.η)
    (typed.commands.take pc))

def typedPhysical (pc : Nat) : List (Option ℤ) × List (Option ℚ) :=
  ([typedMemory pc (.inr ⟨.integerBank, ⟨0, by decide⟩⟩),
    typedMemory pc (.inr ⟨.integerBank, ⟨1, by decide⟩⟩),
    typedMemory pc (.inr ⟨.integerBank, ⟨2, by decide⟩⟩)],
   [typedMemory pc (.inr ⟨.rationalBank, ⟨0, by decide⟩⟩),
    typedMemory pc (.inr ⟨.rationalBank, ⟨1, by decide⟩⟩)])

def typedRow : String × Nat × Option ℤ × Option ℚ :=
  match typedRun with
  | .done pc M => ("done", pc, typed.readPub pc M ⟨0, ()⟩, typed.readPub pc M ⟨1, ()⟩)
  | .failed _ pc _ => ("failed", pc, none, none)
  | .stuck pc _ => ("stuck", pc, none, none)

def typedDecode : Option (ℤ × ℚ) :=
  match typedRun with
  | .done pc M => (typed.Decode pc M).map fun out => (out ⟨0, rfl⟩ (), out ⟨1, rfl⟩ ())
  | _ => none

example : place typed.allocation ⟨0, ()⟩ =
    .inr ⟨.integerBank, ⟨1, by decide⟩⟩ := rfl
example : place typed.allocation ⟨1, ()⟩ =
    .inr ⟨.rationalBank, ⟨0, by decide⟩⟩ := rfl

theorem typed_valid : typed.Valid := typed.checkPlan_sound (by
  have hinj : Function.Injective (place typed.allocation) := by
    rintro ⟨t, p⟩ ⟨u, q⟩ h
    fin_cases t <;> fin_cases u <;> cases p <;> cases q <;>
      simp_all [place, typed, typedAllocation, PlanMultiSort.prog,
        PlanMultiSort.msDeclarations]
  have hl : typed.checkLayouts = true := typed.checkLayouts_iff.mpr
    (fun pc _ => typed.layoutOK_of_place_injective hinj pc)
  rw [checkPlan, hl, Bool.and_true]
  decide)

theorem typed_done :
    typedRun = .done 3 (finalMemory typedRun) := by rfl

theorem typed_R :
    ∃ c, typed.refState PlanMultiSort.msOps PlanMultiSort.η 3 = some c ∧
      typed.R PlanMultiSort.msOps PlanMultiSort.η 3 (finalMemory typedRun) c := by
  rcases typed.runPlan_R PlanMultiSort.msOps typed_valid PlanMultiSort.η with
    ⟨M, c, hrun, hc, hR, _⟩ | ⟨o, pc, M, c, events, hrun, _⟩
  · have h : PlanOutcome.done 3 (finalMemory typedRun) = .done 3 M :=
      typed_done.symm.trans hrun
    cases h
    exact ⟨c, hc, hR⟩
  · have h := typed_done.symm.trans hrun
    cases h

#eval check "storage-typed-independent-buffers"
  (typed.checkPlan, typedRow, typedDecode, PlanMultiSort.decodeRow)
  (true, ("done", 3, some 11, some (7 / 8)), some (11, 7 / 8), some (11, 7 / 8))
#eval check "storage-typed-unused-capacity-all-boundaries"
  ((List.range 4).map fun pc => (pc, typedPhysical pc))
  [(0, [none, none, none], [none, none]),
   (1, [none, some 0, none], [some 0, none]),
   (2, [none, some 11, none], [some (7 / 8), none]),
   (3, [none, some 11, none], [some (7 / 8), none])]

/- The existing zero-extent declaration has no addresses at all, even when
   output flagged. Its canonical buffer therefore needs no physical slots. -/
@[reducible] def emptyOutput : Program Carrier emptyDeclarations registry :=
  { emptyRole false with
    output := fun _ => true
    output_defined := fun _ _ => rfl }

def emptyPlan : emptyOutput.Plan where
  tensors := [()]
  tensors_nodup := by simp
  tensors_complete := by intro t; cases t; simp
  commands := []
def emptyInput : emptyOutput.Input := ⟨fun _ => none, by intro t; rfl⟩
def emptyRun := emptyPlan.runPlan ops (emptyPlan.Start emptyInput)

example : IsEmpty (BufferSlot emptyPlan.allocation) :=
  ⟨fun ξ => Fin.elim0 ξ.2⟩
example : IsEmpty (Slot emptyPlan.allocation) := ⟨fun ξ => by
  cases ξ with
  | inl ξ => cases ξ.1.property
  | inr ξ => exact Fin.elim0 ξ.2⟩

example : emptyRun = .done 0 (finalMemory emptyRun) := rfl

#eval check "storage-empty-domain-versus-scalar"
  (emptyPlan.checkPlan, finalPc emptyRun,
    emptyPlan.allocation.capacity (), emptyPlan.allAddrList.length,
    (emptyPlan.Decode 0 (finalMemory emptyRun)).isSome,
    (canonicalLayout []).count)
  (true, 0, 0, 0, true, 1)

#print axioms reuse_R
#print axioms typed_R

end LeanNCD.Semantics.PlanReuseStorage

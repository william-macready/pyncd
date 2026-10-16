import LeanNCD.Semantics.Plan.ScanHistory.Core
import LeanNCD.Semantics.Plan.Memory

namespace LeanNCD.Semantics.Program.Plan.ScanHistory

variable {V : Type} {d N : Nat} {r : Registry (Carrier V)}

/-- Independent slice buffers, with no reuse and no allocation of input storage. -/
@[reducible] def allocation (f : RegisteredF r d) (N : Nat) : Allocation (program f N) where
  Buffer := Fin (N + 1)
  bufferEq := inferInstance
  buffers := List.finRange (N + 1)
  buffers_nodup := List.nodup_finRange _
  buffers_complete := List.mem_finRange
  sort := fun _ => ()
  capacity := fun _ => d
  locate := fun x => by
    rcases x with ⟨⟨t, ht⟩, p⟩
    cases t
    · simp [isInput] at ht
    · simp [isInput] at ht
    · exact ⟨⟨p.2.1, p.1⟩, rfl⟩

theorem history_locate (f : RegisteredF r d) (N : Nat)
    (i : Fin d) (l : Fin (N + 1)) :
    ((allocation f N).locate (historyDefAddr f N i l)).val = ⟨l, i⟩ := rfl

theorem history_place (f : RegisteredF r d) (N : Nat)
    (i : Fin d) (l : Fin (N + 1)) :
    place (allocation f N) (historyAddress d N i l) = .inr ⟨l, i⟩ := rfl

theorem place_injective (f : RegisteredF r d) (N : Nat) :
    Function.Injective (place (allocation f N)) := by
  rintro ⟨t, p⟩ ⟨u, q⟩ h
  cases t <;> cases u
  all_goals simp only [place, program, isInput, Bool.false_eq_true,
    dite_true, dite_false] at h
  all_goals try contradiction
  · have hi := congrArg (fun x : InputSlot (program f N) => x.2.val) (Sum.inl.inj h)
    have hp : p = q := (canonicalLayout (stateShape d).axes).enumerate.symm.injective
      (Fin.ext hi)
    cases hp
    rfl
  · have ht := congrArg (fun x => x.1.val) (Sum.inl.inj h)
    cases ht
  · have ht := congrArg (fun x => x.1.val) (Sum.inl.inj h)
    cases ht
  · have hi := congrArg (fun x : InputSlot (program f N) => x.2.val) (Sum.inl.inj h)
    have hp : p = q := (canonicalLayout (stateShape d).axes).enumerate.symm.injective
      (Fin.ext hi)
    cases hp
    rfl
  · rcases p with ⟨i, l, e⟩
    rcases q with ⟨j, m, e'⟩
    cases e
    cases e'
    change Sum.inr (⟨l, i⟩ : BufferSlot (allocation f N)) =
      Sum.inr (⟨m, j⟩ : BufferSlot (allocation f N)) at h
    have hl : l = m := congrArg Sigma.fst (Sum.inr.inj h)
    have hiNat : i.val = j.val :=
      congrArg (fun x : BufferSlot (allocation f N) => x.2.val) (Sum.inr.inj h)
    have hi : i = j := Fin.ext hiNat
    cases hl
    cases hi
    rfl

#print axioms history_locate
#print axioms history_place
#print axioms place_injective

end LeanNCD.Semantics.Program.Plan.ScanHistory

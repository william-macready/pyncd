import LeanNCD.Semantics.Plan.Simulation

namespace LeanNCD.Semantics.Program.Plan.ScanHistory

variable {K : S → Type} {σ : Declarations S} {r : Registry K}
variable {P : Program K σ r}

def sliceCommands (B : List (DefAddr P)) (G : List (OccRef P)) :
    List (Command P) :=
  [[.initZero B], [.acc G], [.pub B]]

def scheduleCommands {ι : Type} (slices : List ι)
    (blocks : ι → List (DefAddr P)) (groups : ι → List (OccRef P)) :
    List (Command P) :=
  slices.flatMap fun t => sliceCommands (blocks t) (groups t)

theorem scheduleCommands_length {ι : Type} (slices : List ι)
    (blocks : ι → List (DefAddr P)) (groups : ι → List (OccRef P)) :
    (scheduleCommands slices blocks groups).length = 3 * slices.length := by
  induction slices with
  | nil => simp [scheduleCommands]
  | cons t ts ih => simpa [scheduleCommands, sliceCommands, Nat.mul_succ] using ih

theorem take_flatMap_three {α β : Type} (items : List α) (emit : α → List β)
    (size : ∀ x, (emit x).length = 3) (k : Nat) :
    (items.flatMap emit).take (3 * k) = (items.take k).flatMap emit := by
  induction k generalizing items with
  | zero => simp
  | succ k ih =>
    cases items with
    | nil => simp
    | cons x xs =>
      rw [List.flatMap_cons, List.take_succ_cons, List.flatMap_cons, List.take_append]
      rw [List.take_of_length_le (by rw [size]; omega), size]
      simp only [Nat.mul_succ, Nat.add_sub_cancel]
      rw [ih]

theorem scheduleCommands_take {ι : Type} (slices : List ι)
    (blocks : ι → List (DefAddr P)) (groups : ι → List (OccRef P)) (k : Nat) :
    (scheduleCommands slices blocks groups).take (3 * k) =
      scheduleCommands (slices.take k) blocks groups :=
  take_flatMap_three slices _ (fun _ => rfl) k

theorem scheduleCommands_pubs {ι : Type} (slices : List ι)
    (blocks : ι → List (DefAddr P)) (groups : ι → List (OccRef P)) :
    (scheduleCommands slices blocks groups).flatten.flatMap Ann.blocks =
      slices.flatMap blocks := by
  induction slices with
  | nil => simp [scheduleCommands]
  | cons t ts ih => simpa [scheduleCommands, sliceCommands, Ann.blocks] using ih

theorem pubList_at_slice_boundary {ι : Type} (π : P.Plan) (slices : List ι)
    (blocks : ι → List (DefAddr P)) (groups : ι → List (OccRef P))
    (cmds : π.commands = scheduleCommands slices blocks groups) (k : Nat) :
    π.pubList (3 * k) = (slices.take k).flatMap blocks := by
  simp only [pubList, prefixAnn, cmds, scheduleCommands_take]
  exact scheduleCommands_pubs _ _ _

theorem scheduleCommands_groups {ι : Type} (slices : List ι)
    (blocks : ι → List (DefAddr P)) (groups : ι → List (OccRef P)) :
    (scheduleCommands slices blocks groups).flatten.flatMap Ann.groups =
      slices.flatMap groups := by
  induction slices with
  | nil => simp [scheduleCommands]
  | cons t ts ih => simpa [scheduleCommands, sliceCommands, Ann.groups] using ih

theorem consList_at_slice_boundary {ι : Type} (π : P.Plan) (slices : List ι)
    (blocks : ι → List (DefAddr P)) (groups : ι → List (OccRef P))
    (cmds : π.commands = scheduleCommands slices blocks groups) (k : Nat) :
    π.consList (3 * k) = (slices.take k).flatMap groups := by
  simp only [consList, prefixAnn, cmds, scheduleCommands_take]
  exact scheduleCommands_groups _ _ _

theorem scheduleCommands_inits {ι : Type} (slices : List ι)
    (blocks : ι → List (DefAddr P)) (groups : ι → List (OccRef P)) :
    (scheduleCommands slices blocks groups).flatten.flatMap Ann.inits =
      slices.flatMap blocks := by
  induction slices with
  | nil => simp [scheduleCommands]
  | cons t ts ih => simpa [scheduleCommands, sliceCommands, Ann.inits] using ih

theorem matList_at_slice_boundary {ι : Type} (π : P.Plan) (slices : List ι)
    (blocks : ι → List (DefAddr P)) (groups : ι → List (OccRef P))
    (cmds : π.commands = scheduleCommands slices blocks groups) (k : Nat) :
    π.matList (3 * k) = (slices.take k).flatMap blocks := by
  simp only [matList, prefixAnn, cmds, scheduleCommands_take]
  exact scheduleCommands_inits _ _ _

theorem scheduleCommands_rets {ι : Type} (slices : List ι)
    (blocks : ι → List (DefAddr P)) (groups : ι → List (OccRef P)) :
    (scheduleCommands slices blocks groups).flatten.flatMap Ann.rets = [] := by
  induction slices with
  | nil => simp [scheduleCommands]
  | cons t ts ih => simpa [scheduleCommands, sliceCommands, Ann.rets] using ih

theorem retList_at_any_boundary {ι : Type} (π : P.Plan) (slices : List ι)
    (blocks : ι → List (DefAddr P)) (groups : ι → List (OccRef P))
    (cmds : π.commands = scheduleCommands slices blocks groups) (pc : Nat) :
    π.retList pc = [] := by
  have whole : π.ann.flatMap Ann.rets = [] := by
    simp only [ann, cmds]
    exact scheduleCommands_rets _ _ _
  have sub : (π.retList pc).Sublist (π.ann.flatMap Ann.rets) :=
    ((List.take_sublist pc π.commands).flatten).flatMap Ann.rets
  rw [whole] at sub
  exact List.sublist_nil.mp sub

theorem singleton_of_scheduleCommands {ι : Type} (π : P.Plan) (slices : List ι)
    (blocks : ι → List (DefAddr P)) (groups : ι → List (OccRef P))
    (cmds : π.commands = scheduleCommands slices blocks groups) : π.Singleton := by
  intro cmd hc
  rw [cmds] at hc
  obtain ⟨t, _, ht⟩ := List.mem_flatMap.mp hc
  simp only [sliceCommands, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

#print axioms scheduleCommands_length
#print axioms take_flatMap_three
#print axioms scheduleCommands_take
#print axioms scheduleCommands_pubs
#print axioms pubList_at_slice_boundary
#print axioms scheduleCommands_groups
#print axioms consList_at_slice_boundary
#print axioms scheduleCommands_inits
#print axioms matList_at_slice_boundary
#print axioms scheduleCommands_rets
#print axioms retList_at_any_boundary
#print axioms singleton_of_scheduleCommands

end LeanNCD.Semantics.Program.Plan.ScanHistory

import IndexedComponentCompositionProgram

namespace IndexedComponentComposition

open LeanNCD.Semantics
open LeanNCD.Semantics.Program.Executor

variable {σA σB : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB)
variable (wire : Boundary A B)

def keyEquiv : Key (program A B wire) ≃ Key A.program ⊕ Key B.program where
  toFun
    | .occurrence ⟨.inl t, h⟩ o => .inl (.occurrence ⟨t, h⟩ o)
    | .occurrence ⟨.inr t, _⟩ o => .inr (.occurrence t o)
    | .publication ⟨.inl t, h⟩ p => .inl (.publication ⟨t, h⟩ p)
    | .publication ⟨.inr t, _⟩ p => .inr (.publication t p)
  invFun
    | .inl (.occurrence t o) => .occurrence (upstreamDefined A B wire t) o
    | .inr (.occurrence t o) => .occurrence (downstreamDefined A B wire t) o
    | .inl (.publication t p) => .publication (upstreamDefined A B wire t) p
    | .inr (.publication t p) => .publication (downstreamDefined A B wire t) p
  left_inv := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨t, h⟩
      cases t <;> rfl
    | publication t p =>
      rcases t with ⟨t, h⟩
      cases t <;> rfl
  right_inv := by
    intro k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl

def definedTensor? (t : σB.Tensor) : Option B.program.Defined :=
  if h : B.program.input t = false then some ⟨t, h⟩ else none

theorem definedTensor?_mem (t : B.program.Defined) :
    t ∈ (B.schedule.tensors.filterMap (definedTensor? B)) := by
  apply List.mem_filterMap.mpr
  exact ⟨t.val, B.schedule.tensors_complete t.val, by
    simp [definedTensor?, t.property]⟩

theorem definedTensor?_nodup :
    (B.schedule.tensors.filterMap (definedTensor? B)).Nodup := by
  apply B.schedule.tensors_nodup.filterMap
  intro t u d ht hu
  unfold definedTensor? at ht hu
  split at ht <;> split at hu <;> simp_all
  exact congrArg Subtype.val (ht.trans hu.symm)

def tensorOrder : List (declarations A B).Tensor :=
  A.schedule.tensors.map Sum.inl ++
    (B.schedule.tensors.filterMap (definedTensor? B)).map Sum.inr

theorem tensorOrder_nodup : (tensorOrder A B).Nodup := by
  unfold tensorOrder
  apply List.Nodup.append
  · exact A.schedule.tensors_nodup.map Sum.inl_injective
  · exact (definedTensor?_nodup B).map Sum.inr_injective
  · intro t ht hu
    rcases List.mem_map.mp ht with ⟨_, _, rfl⟩
    rcases List.mem_map.mp hu with ⟨_, _, h⟩
    cases h

theorem tensorOrder_complete (t : (declarations A B).Tensor) :
    t ∈ tensorOrder A B := by
  cases t with
  | inl t =>
    exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
      ⟨t, A.schedule.tensors_complete t, rfl⟩))
  | inr t =>
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
      ⟨t, definedTensor?_mem B t, rfl⟩))

def keyOrder : List (Key (program A B wire)) :=
  A.schedule.keys.map (fun k => (keyEquiv A B wire).symm (.inl k)) ++
    B.schedule.keys.map (fun k => (keyEquiv A B wire).symm (.inr k))

theorem keyOrder_nodup : (keyOrder A B wire).Nodup := by
  unfold keyOrder
  apply List.Nodup.append
  · apply A.schedule.keys_nodup.map
    exact (keyEquiv A B wire).symm.injective.comp Sum.inl_injective
  · apply B.schedule.keys_nodup.map
    exact (keyEquiv A B wire).symm.injective.comp Sum.inr_injective
  · intro k hk hl
    rcases List.mem_map.mp hk with ⟨x, _, rfl⟩
    rcases List.mem_map.mp hl with ⟨y, _, h⟩
    have he := (keyEquiv A B wire).symm.injective h
    cases he

theorem keyOrder_complete (k : Key (program A B wire)) :
    k ∈ keyOrder A B wire := by
  have hi := (keyEquiv A B wire).symm_apply_apply k
  cases he : keyEquiv A B wire k with
  | inl x =>
    unfold keyOrder
    rw [he] at hi
    rw [← hi]
    exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
      ⟨x, A.schedule.keys_complete x, rfl⟩))
  | inr x =>
    unfold keyOrder
    rw [he] at hi
    rw [← hi]
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
      ⟨x, B.schedule.keys_complete x, rfl⟩))

def schedule : Schedule (program A B wire) where
  tensors := tensorOrder A B
  tensors_nodup := tensorOrder_nodup A B
  tensors_complete := tensorOrder_complete A B
  keys := keyOrder A B wire
  keys_nodup := keyOrder_nodup A B wire
  keys_complete := keyOrder_complete A B wire

end IndexedComponentComposition

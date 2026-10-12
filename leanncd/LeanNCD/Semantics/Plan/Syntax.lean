import LeanNCD.Semantics.ReferenceExecutor

/- Execution plans (spec Part V, Section 29): command syntax, annotation
   expansion, command prefixes and the static prefix sets Pub/Cons/Mat.
   Slice-1 to slice-4 profile: batched Accumulate, block Publish, initZero and block retire.
   Every group/block is a List; its order is presentation data and is never
   obtained by choosing a Finset order. -/

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}

/-- A tagged contribution occurrence (spec `𝒪_P`). -/
abbrev OccRef (P : Program K σ r) := (t : P.Defined) × P.Occurrence t

/-- A defined logical address (spec `Addr_Def`). -/
abbrev DefAddr (P : Program K σ r) := (t : P.Defined) × Coord (σ.signature t.val).axes

def DefAddr.addr {P : Program K σ r} (x : DefAddr P) : Address σ := ⟨x.1.val, x.2⟩

theorem DefAddr.addr_injective {P : Program K σ r} :
    Function.Injective (DefAddr.addr (P := P)) := by
  rintro ⟨⟨t, ht⟩, p⟩ ⟨⟨u, hu⟩, q⟩ h
  simp only [DefAddr.addr, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  obtain rfl := eq_of_heq h
  rfl

/-- Finite reusable buffers and a sort-preserving, bounded placement. Buffer
    identity is independent of logical tensor identity. -/
structure Allocation (P : Program K σ r) where
  Buffer : Type
  bufferEq : DecidableEq Buffer
  buffers : List Buffer
  buffers_nodup : buffers.Nodup
  buffers_complete : ∀ b, b ∈ buffers
  sort : Buffer → S
  capacity : Buffer → Nat
  locate : (x : DefAddr P) →
    {ξ : (b : Buffer) × Fin (capacity b) // sort ξ.1 = (σ.signature x.1.val).sort}

/-- The old dense placement, used when a plan supplies no custom allocation. -/
def Allocation.canonical (P : Program K σ r) (ts : List σ.Tensor)
    (hn : ts.Nodup) (hc : ∀ t, t ∈ ts) : Allocation P where
  Buffer := σ.Tensor
  bufferEq := fun t u => decidable_of_iff (σ.uid t = σ.uid u)
    ⟨fun h => σ.unique h, congrArg σ.uid⟩
  buffers := ts
  buffers_nodup := hn
  buffers_complete := hc
  sort := fun t => (σ.signature t).sort
  capacity := fun t => (canonicalLayout (σ.signature t).axes).count
  locate := fun x => ⟨⟨x.1.val,
    (canonicalLayout (σ.signature x.1.val).axes).enumerate.symm x.2⟩, rfl⟩

/-- One logical annotation. `acc G` is spec `Accumulate(G)`, `pub B` is
    `Publish(B)`, `initZero S` is the storage operation materialising zero
    accumulators at the addresses `S`, `retire B` retires the published defined
    addresses `B` (their physical slots are cleared). -/
inductive Ann (P : Program K σ r)
  | acc (G : List (OccRef P))
  | pub (B : List (DefAddr P))
  | initZero (S : List (DefAddr P))
  | retire (B : List (DefAddr P))

/-- A (possibly fused) command is its finite annotation sequence. -/
abbrev Command (P : Program K σ r) := List (Ann P)

/-- A plan. `tensors` is the duplicate-free complete tensor list Start uses to
    validate input presence, exactly as `Executor.Schedule.tensors` serves
    `Executor.validate`. -/
structure _root_.LeanNCD.Semantics.Program.Plan (P : Program K σ r) where
  tensors : List σ.Tensor
  tensors_nodup : tensors.Nodup
  tensors_complete : ∀ t, t ∈ tensors
  commands : List (Command P)
  allocation : Allocation P := Allocation.canonical P tensors tensors_nodup tensors_complete

namespace Ann

variable {P : Program K σ r}

def groups : Ann P → List (OccRef P)
  | .acc G => G
  | _ => []

def blocks : Ann P → List (DefAddr P)
  | .pub B => B
  | _ => []

def inits : Ann P → List (DefAddr P)
  | .initZero S => S
  | _ => []

def rets : Ann P → List (DefAddr P)
  | .retire B => B
  | _ => []

def occKey (x : OccRef P) : Key P := .occurrence x.1 x.2
def pubKey (x : DefAddr P) : Key P := .publication x.1 x.2

/-- Singleton-key view of one annotation. -/
def keys : Ann P → List (Key P)
  | .acc G => G.map occKey
  | .pub B => B.map pubKey
  | .initZero _ => []
  | .retire _ => []

theorem occKey_injective : Function.Injective (occKey (P := P)) := by
  rintro ⟨t, o⟩ ⟨u, q⟩ h
  simp only [occKey, Key.occurrence.injEq] at h
  obtain ⟨rfl, h⟩ := h
  obtain rfl := eq_of_heq h
  rfl

theorem pubKey_injective : Function.Injective (pubKey (P := P)) := by
  rintro ⟨t, o⟩ ⟨u, q⟩ h
  simp only [pubKey, Key.publication.injEq] at h
  obtain ⟨rfl, h⟩ := h
  obtain rfl := eq_of_heq h
  rfl

end Ann

variable {P : Program K σ r} (π : P.Plan)

/-- Annotation expansion: fused commands flattened in their stated order. -/
def ann : List (Ann P) := π.commands.flatten

/-- The annotations of the first `pc` commands. -/
def prefixAnn (pc : Nat) : List (Ann P) := (π.commands.take pc).flatten

def consList (pc : Nat) : List (OccRef P) := (π.prefixAnn pc).flatMap Ann.groups
def pubList (pc : Nat) : List (DefAddr P) := (π.prefixAnn pc).flatMap Ann.blocks
def matList (pc : Nat) : List (DefAddr P) := (π.prefixAnn pc).flatMap Ann.inits
def retList (pc : Nat) : List (DefAddr P) := (π.prefixAnn pc).flatMap Ann.rets

/-- `Pub(pc)`: input addresses plus every address published by the prefix. -/
def Pub (pc : Nat) (a : Address σ) : Prop :=
  P.input a.1 = true ∨ a ∈ (π.pubList pc).map DefAddr.addr

/-- `Cons(pc)`: occurrences in the prefix's accumulation groups. -/
def Cons (pc : Nat) (x : OccRef P) : Prop := x ∈ π.consList pc

/-- `Mat(pc)`: addresses whose zero accumulator the prefix materialised. -/
def Mat (pc : Nat) (x : DefAddr P) : Prop := x ∈ π.matList pc

/-- `Ret(pc)`: addresses retired by the prefix. -/
def Ret (pc : Nat) (a : Address σ) : Prop := a ∈ (π.retList pc).map DefAddr.addr

/-- `Live(pc)`: published and not retired. -/
def Live (pc : Nat) (a : Address σ) : Prop := π.Pub pc a ∧ ¬ π.Ret pc a

section Decidable

variable [DecidableEq σ.Tensor]

instance (pc : Nat) (a : Address σ) : Decidable (π.Pub pc a) :=
  letI := addressEq (σ := σ)
  inferInstanceAs (Decidable (_ ∨ _))

instance (pc : Nat) (x : OccRef P) : Decidable (π.Cons pc x) :=
  inferInstanceAs (Decidable (x ∈ π.consList pc))

instance (pc : Nat) (x : DefAddr P) : Decidable (π.Mat pc x) :=
  letI : ∀ t : P.Defined, DecidableEq (Coord (σ.signature t.val).axes) :=
    fun t => coordDecidableEq (σ.signature t.val).axes
  inferInstanceAs (Decidable (x ∈ π.matList pc))

instance (pc : Nat) (a : Address σ) : Decidable (π.Ret pc a) :=
  letI := addressEq (σ := σ)
  inferInstanceAs (Decidable (a ∈ _))

instance (pc : Nat) (a : Address σ) : Decidable (π.Live pc a) :=
  inferInstanceAs (Decidable (_ ∧ ¬ _))

end Decidable

theorem prefixAnn_zero : π.prefixAnn 0 = [] := by simp [prefixAnn]

/-! ### Expansion (spec 29.3): the schedule of a fused plan -/

/-- The expanded plan: every annotation of `π` in its own command. -/
def expand : P.Plan := { π with commands := π.ann.map (fun a => [a]) }

theorem expand_allocation : π.expand.allocation = π.allocation := rfl

/-- Number of annotations in the first `pc` commands (the expanded position of command `pc`). -/
def offset (pc : Nat) : Nat := (π.prefixAnn pc).length

theorem flatten_map_single {α : Type _} (l : List α) : (l.map fun a => [a]).flatten = l := by
  induction l <;> simp [*]

theorem expand_ann : π.expand.ann = π.ann := flatten_map_single π.ann

theorem expand_prefixAnn (n : Nat) : π.expand.prefixAnn n = π.ann.take n := by
  show (List.take n (π.ann.map fun a => [a])).flatten = _
  rw [← List.map_take, flatten_map_single]

theorem expand_commands_getElem? {n : Nat} {a : Ann P} (h : π.ann[n]? = some a) :
    π.expand.commands[n]? = some [a] := by
  simp [expand, h]

theorem ann_eq_append (pc : Nat) : π.ann = π.prefixAnn pc ++ (π.commands.drop pc).flatten := by
  simp only [ann, prefixAnn, ← List.flatten_append, List.take_append_drop]

theorem prefixAnn_eq_expand (pc : Nat) : π.prefixAnn pc = π.expand.prefixAnn (π.offset pc) := by
  rw [expand_prefixAnn, offset, ann_eq_append π pc, List.take_left' rfl]

theorem drop_flatten {pc : Nat} {cmd : Command P} (h : π.commands[pc]? = some cmd) :
    (π.commands.drop pc).flatten = cmd ++ (π.commands.drop (pc + 1)).flatten := by
  obtain ⟨hpc, hc⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hpc, hc, List.flatten_cons]

theorem ann_getElem?_offset {pc : Nat} {cmd : Command P} (h : π.commands[pc]? = some cmd)
    {j : Nat} {a : Ann P} (hj : cmd[j]? = some a) : π.ann[π.offset pc + j]? = some a := by
  have hlt : j < cmd.length := (List.getElem?_eq_some_iff.mp hj).1
  rw [ann_eq_append π pc, drop_flatten π h, offset, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hlt, hj]

theorem not_cons_zero (x : OccRef P) : ¬ π.Cons 0 x := by
  simp [Cons, consList, prefixAnn_zero]

theorem not_mat_zero (x : DefAddr P) : ¬ π.Mat 0 x := by
  simp [Mat, matList, prefixAnn_zero]

theorem pub_zero (a : Address σ) : π.Pub 0 a ↔ P.input a.1 = true := by
  simp [Pub, pubList, prefixAnn_zero]

theorem ret_zero (a : Address σ) : ¬ π.Ret 0 a := by
  simp [Ret, retList, prefixAnn_zero]

theorem live_zero (a : Address σ) : π.Live 0 a ↔ P.input a.1 = true := by
  simp [Live, ret_zero, pub_zero]

theorem Live.pub {pc : Nat} {a : Address σ} (h : π.Live pc a) : π.Pub pc a := h.1

/-- Inputs are always live: `Ret` mentions only defined addresses. -/
theorem live_input (pc : Nat) (a : Address σ) (h : P.input a.1 = true) : π.Live pc a := by
  refine ⟨Or.inl h, ?_⟩
  rintro hr
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
  have := x.1.2
  simp [DefAddr.addr] at h
  simp_all

/-! ### Schedule view (spec 29.3 conditions 1-2) -/

def accFlat : List (OccRef P) := π.ann.flatMap Ann.groups
def pubFlat : List (DefAddr P) := π.ann.flatMap Ann.blocks

/-- The flattened singleton-key view, the `Executor.Schedule.keys` shape. -/
def flatKeys : List (Key P) := π.ann.flatMap Ann.keys

/-- Condition 1: the accumulation groups are duplicate-free, pairwise disjoint,
    and cover every occurrence. -/
def Coverage1 : Prop := π.accFlat.Nodup ∧ ∀ x, x ∈ π.accFlat

/-- Condition 2: the publication blocks are duplicate-free, pairwise disjoint,
    and cover every defined address. -/
def Coverage2 : Prop := π.pubFlat.Nodup ∧ ∀ x, x ∈ π.pubFlat

theorem keys_perm_aux (anns : List (Ann P)) :
    (anns.flatMap Ann.keys).Perm
      ((anns.flatMap Ann.groups).map Ann.occKey ++ (anns.flatMap Ann.blocks).map Ann.pubKey) := by
  induction anns with
  | nil => simp
  | cons a as ih =>
    cases a with
    | acc G =>
      simp only [List.flatMap_cons, Ann.keys, Ann.groups, Ann.blocks, List.nil_append,
        List.map_append, List.append_assoc]
      exact ih.append_left _
    | pub B =>
      simp only [List.flatMap_cons, Ann.keys, Ann.groups, Ann.blocks, List.nil_append,
        List.map_append]
      exact (ih.append_left _).trans (List.perm_append_comm_assoc _ _ _)
    | initZero S =>
      simpa [Ann.keys, Ann.groups, Ann.blocks, List.flatMap_cons] using ih
    | retire B =>
      simpa [Ann.keys, Ann.groups, Ann.blocks, List.flatMap_cons] using ih

theorem flatKeys_perm :
    π.flatKeys.Perm (π.accFlat.map Ann.occKey ++ π.pubFlat.map Ann.pubKey) :=
  keys_perm_aux π.ann

/-- Spec 29.3 conditions 1-2 are exactly `keys_nodup`/`keys_complete` of the
    flattened singleton-key list. -/
theorem coverage_iff_schedule :
    (π.Coverage1 ∧ π.Coverage2) ↔ (π.flatKeys.Nodup ∧ ∀ k, k ∈ π.flatKeys) := by
  have hp := π.flatKeys_perm
  rw [hp.nodup_iff]
  simp only [hp.mem_iff, Coverage1, Coverage2, List.nodup_append,
    List.nodup_map_iff Ann.occKey_injective, List.nodup_map_iff Ann.pubKey_injective,
    List.mem_append]
  have disj : ∀ a ∈ π.accFlat.map Ann.occKey, ∀ b ∈ π.pubFlat.map Ann.pubKey, a ≠ b := by
    intro a ha b hb h
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
    cases h
  constructor
  · rintro ⟨⟨n1, c1⟩, ⟨n2, c2⟩⟩
    refine ⟨⟨n1, n2, disj⟩, ?_⟩
    intro k
    cases k with
    | occurrence t o => exact Or.inl (List.mem_map_of_mem (f := Ann.occKey) (c1 ⟨t, o⟩))
    | publication t p => exact Or.inr (List.mem_map_of_mem (f := Ann.pubKey) (c2 ⟨t, p⟩))
  · rintro ⟨⟨n1, n2, _⟩, c⟩
    refine ⟨⟨n1, fun x => ?_⟩, ⟨n2, fun x => ?_⟩⟩
    · rcases c (Ann.occKey x) with h | h
      · exact (List.mem_map_of_injective Ann.occKey_injective).mp h
      · obtain ⟨y, _, hy⟩ := List.mem_map.mp h
        cases hy
    · rcases c (Ann.pubKey x) with h | h
      · obtain ⟨y, _, hy⟩ := List.mem_map.mp h
        cases hy
      · exact (List.mem_map_of_injective Ann.pubKey_injective).mp h

#print axioms DefAddr.addr_injective
#print axioms coverage_iff_schedule
#print axioms ret_zero
#print axioms live_input
#print axioms expand_allocation

end LeanNCD.Semantics.Program.Plan

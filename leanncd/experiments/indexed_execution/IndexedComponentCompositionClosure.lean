import IndexedComponentClosureFacts
import IndexedComponentTransportExpr

namespace IndexedComponentComposition

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open IndexedOpenComposition
open IndexedComponentTransport

variable {σA σB σ : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable [Fintype σ.Tensor] [DecidableEq σ.Tensor]

def mapWriter (f : Embedding σA σ) (rename : Nat → Nat)
    (w : Writer σA) : Writer σ where
  tag := rename w.tag
  capability := rename w.capability
  destination := f.address w.destination
  reads := w.reads.map f.address
  body := transport f (fun _ : Unit => ()) w.body

def mapRow (f : Embedding σA σ) (rename : Nat → Nat)
    (row : Address σA × List Nat) : Address σ × List Nat :=
  (f.address row.1, row.2.map rename)

def mapStep (f : Embedding σA σ) (rename : Nat → Nat) :
    Step σA → Step σ
  | .write w => .write (mapWriter f rename w)
  | .collect a caps => .collect (f.address a) (caps.map rename)

def assembledContract (f : Embedding σA σ) (g : Embedding σB σ)
    (idA idB : Nat → Nat) (tensors : List σ.Tensor) (input : σ.Tensor → Bool)
    (a : Contract σA) (b : Contract σB) : Contract σ where
  tensors := tensors
  input := input
  collectors := a.collectors.map (mapRow f idA) ++ b.collectors.map (mapRow g idB)
  readable := letI : DecidableEq (Address σ) := Program.Executor.addressEq (σ := σ)
    (a.readable.map f.address ++ b.readable.map g.address).dedup
  outputs := b.outputs.map g.address

def assembledFragment (f : Embedding σA σ) (g : Embedding σB σ)
    (idA idB : Nat → Nat) (a : Fragment σA) (b : Fragment σB) :
    Fragment σ where
  writers := a.writers.map (mapWriter f idA) ++ b.writers.map (mapWriter g idB)

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σ.Tensor]
    [DecidableEq σ.Tensor] in
theorem mapWriter_reads (f : Embedding σA σ) (rename : Nat → Nat)
    (w : Writer σA) : (mapWriter f rename w).reads =
      footprint (mapWriter f rename w).body () ↔
      w.reads = footprint w.body () := by
  simp only [mapWriter, footprint_transport]
  exact (List.map_injective_iff.mpr f.address_injective).eq_iff

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σ.Tensor]
    [DecidableEq σ.Tensor] in
theorem find_mapped_writer (f : Embedding σA σ) (rename : Nat → Nat)
    (hinj : Function.Injective rename) (ws : List (Writer σA)) (cap : Nat) :
    (ws.map (mapWriter f rename)).find? (fun w => w.capability == rename cap) =
      (ws.find? (fun w => w.capability == cap)).map (mapWriter f rename) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    by_cases h : w.capability = cap
    · simp [List.find?, mapWriter, h]
    · have hb : (w.capability == cap) = false :=
        Bool.eq_false_iff.mpr (fun ht => h (beq_iff_eq.mp ht))
      simp [List.find?, mapWriter, hb, hinj.ne h, ih]

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σ.Tensor]
    [DecidableEq σ.Tensor] in
theorem find_foreign_writer (f : Embedding σA σ) (idA idB : Nat → Nat)
    (hdisj : ∀ x y, idA x ≠ idB y) (ws : List (Writer σA)) (cap : Nat) :
    (ws.map (mapWriter f idA)).find? (fun w => w.capability == idB cap) = none := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp [mapWriter, hdisj, ih]

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σB.Tensor]
    [DecidableEq σB.Tensor] [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem find_appended_writerA (f : Embedding σA σ) (g : Embedding σB σ)
    (idA idB : Nat → Nat) (hinj : Function.Injective idA)
    (hdisj : ∀ x y, idA x ≠ idB y)
    (wsA : List (Writer σA)) (wsB : List (Writer σB)) (cap : Nat) :
    ((wsA.map (mapWriter f idA)) ++ (wsB.map (mapWriter g idB))).find?
        (fun w => w.capability == idA cap) =
      (wsA.find? (fun w => w.capability == cap)).map (mapWriter f idA) := by
  rw [List.find?_append, find_mapped_writer f idA hinj]
  cases h : wsA.find? (fun w => w.capability == cap)
  · have hnone : (wsB.map (mapWriter g idB)).find?
        (fun w => w.capability == idA cap) = none := by
      apply find_foreign_writer g idB idA
      intro x y heq
      exact hdisj y x heq.symm
    simp [hnone]
  · simp

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σB.Tensor]
    [DecidableEq σB.Tensor] [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem find_appended_writerB (f : Embedding σA σ) (g : Embedding σB σ)
    (idA idB : Nat → Nat) (hinj : Function.Injective idB)
    (hdisj : ∀ x y, idA x ≠ idB y)
    (wsA : List (Writer σA)) (wsB : List (Writer σB)) (cap : Nat) :
    ((wsA.map (mapWriter f idA)) ++ (wsB.map (mapWriter g idB))).find?
        (fun w => w.capability == idB cap) =
      (wsB.find? (fun w => w.capability == cap)).map (mapWriter g idB) := by
  rw [List.find?_append, find_foreign_writer f idA idB hdisj,
    find_mapped_writer g idB hinj]
  rfl

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σB.Tensor]
    [DecidableEq σB.Tensor] [Fintype σ.Tensor] in
theorem canonicalSteps_assembled (f : Embedding σA σ) (g : Embedding σB σ)
    (idA idB : Nat → Nat) (hinjA : Function.Injective idA)
    (hinjB : Function.Injective idB)
    (hdisj : ∀ x y, idA x ≠ idB y)
    (tensors : List σ.Tensor) (input : σ.Tensor → Bool)
    (a : Contract σA) (b : Contract σB)
    (fa : Fragment σA) (fb : Fragment σB) :
    canonicalSteps (assembledContract f g idA idB tensors input a b)
        (assembledFragment f g idA idB fa fb) =
      (canonicalSteps a fa).map (mapStep f idA) ++
      (canonicalSteps b fb).map (mapStep g idB) := by
  simp only [canonicalSteps, assembledContract, assembledFragment,
    List.flatMap_append, List.map_flatMap, List.flatMap_map]
  congr 1
  · apply List.flatMap_congr
    intro row hr
    simp only [mapRow, List.map_append, List.map_cons, List.map_nil, mapStep,
      List.filterMap_map, List.map_map]
    congr 1
    simp only [Function.comp_apply]
    simp_rw [find_appended_writerA f g idA idB hinjA hdisj fa.writers fb.writers]
    simp only [List.map_filterMap, Option.map_map]
    congr 1
  · apply List.flatMap_congr
    intro row hr
    simp only [mapRow, List.map_append, List.map_cons, List.map_nil, mapStep,
      List.filterMap_map, List.map_map]
    congr 1
    simp only [Function.comp_apply]
    simp_rw [find_appended_writerB f g idA idB hinjB hdisj fa.writers fb.writers]
    simp only [List.map_filterMap, Option.map_map]
    congr 1

structure ClosureScope (f : Embedding σA σ) (g : Embedding σB σ)
    (input : σ.Tensor → Bool) (a : Contract σA) (b : Contract σB) : Prop where
  upstream_roles : ∀ t, input (f.tensor t) = a.input t
  downstream_defined : ∀ t, b.input t = false → input (g.tensor t) = false
  defined_partition : ∀ z : Address σ, input z.1 = false →
    (∃ x : Address σA, a.input x.1 = false ∧ f.address x = z) ∨
    (∃ y : Address σB, b.input y.1 = false ∧ g.address y = z)
  defined_disjoint : ∀ x : Address σA, ∀ y : Address σB,
    a.input x.1 = false → b.input y.1 = false → f.address x ≠ g.address y
  boundary_collector : ∀ y : Address σB, b.input y.1 = true →
    g.address y ∈ (a.collectors.map fun row => f.address row.1)

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σ.Tensor]
    [DecidableEq σ.Tensor] in
theorem mapped_addresses (f : Embedding σA σ) (rename : Nat → Nat)
    (rows : List (Address σA × List Nat)) :
    (rows.map (mapRow f rename)).map Prod.fst =
      (rows.map Prod.fst).map f.address := by
  simp [mapRow, List.map_map]

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σ.Tensor]
    [DecidableEq σ.Tensor] in
theorem mapped_capabilities (f : Embedding σA σ) (rename : Nat → Nat)
    (rows : List (Address σA × List Nat)) :
    (rows.map (mapRow f rename)).flatMap Prod.snd =
      (rows.flatMap Prod.snd).map rename := by
  simp [mapRow, List.flatMap_map, List.map_flatMap]

theorem nodup_mapped_append {α β γ : Type} [DecidableEq γ]
    (xs : List α) (ys : List β) (p : α → γ) (q : β → γ)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hdisj : ∀ x y, p x ≠ q y)
    (hx : xs.Nodup) (hy : ys.Nodup) :
    (xs.map p ++ ys.map q).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hx.map hp, hy.map hq, ?_⟩
  intro z hz v hv
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hz
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hv
  exact hdisj x y

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σ.Tensor]
    [DecidableEq σ.Tensor] in
theorem find_mapped_row (f : Embedding σA σ) (rename : Nat → Nat)
    (hinj : Function.Injective rename)
    (rows : List (Address σA × List Nat)) (cap : Nat) :
    (rows.map (mapRow f rename)).find?
        (fun row => row.2.contains (rename cap)) =
      (rows.find? (fun row => row.2.contains cap)).map (mapRow f rename) := by
  rw [List.find?_map]
  have hp : ((fun row => row.2.contains (rename cap)) ∘ mapRow f rename) =
      (fun row => row.2.contains cap) := by
    funext row
    simp [mapRow, List.mem_map, hinj.eq_iff]
  rw [hp]

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σ.Tensor]
    [DecidableEq σ.Tensor] in
theorem find_foreign_row (f : Embedding σA σ) (idA idB : Nat → Nat)
    (hdisj : ∀ x y, idA x ≠ idB y)
    (rows : List (Address σA × List Nat)) (cap : Nat) :
    (rows.map (mapRow f idA)).find?
        (fun row => row.2.contains (idB cap)) = none := by
  rw [List.find?_map]
  suffices h : rows.find? ((fun row => row.2.contains (idB cap)) ∘ mapRow f idA) =
      none by simp only [h, Option.map_none]
  apply List.find?_eq_none.mpr
  intro row hr
  simp [mapRow, List.mem_map, hdisj]

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σB.Tensor]
    [DecidableEq σB.Tensor] [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem find_assembled_rowA (f : Embedding σA σ) (g : Embedding σB σ)
    (idA idB : Nat → Nat) (hinj : Function.Injective idA)
    (hdisj : ∀ x y, idA x ≠ idB y)
    (a : Contract σA) (b : Contract σB) (cap : Nat) :
    (a.collectors.map (mapRow f idA) ++ b.collectors.map (mapRow g idB)).find?
        (fun row => row.2.contains (idA cap)) =
      (a.collectors.find? (fun row => row.2.contains cap)).map (mapRow f idA) := by
  rw [List.find?_append, find_mapped_row f idA hinj]
  cases h : a.collectors.find? (fun row => row.2.contains cap)
  · have hn : (b.collectors.map (mapRow g idB)).find?
        (fun row => row.2.contains (idA cap)) = none := by
      apply find_foreign_row g idB idA
      intro x y heq
      exact hdisj y x heq.symm
    rw [hn]
    rfl
  · simp

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σB.Tensor]
    [DecidableEq σB.Tensor] [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem find_assembled_rowB (f : Embedding σA σ) (g : Embedding σB σ)
    (idA idB : Nat → Nat) (hinj : Function.Injective idB)
    (hdisj : ∀ x y, idA x ≠ idB y)
    (a : Contract σA) (b : Contract σB) (cap : Nat) :
    (a.collectors.map (mapRow f idA) ++ b.collectors.map (mapRow g idB)).find?
        (fun row => row.2.contains (idB cap)) =
      (b.collectors.find? (fun row => row.2.contains cap)).map (mapRow g idB) := by
  rw [List.find?_append, find_foreign_row f idA idB hdisj,
    find_mapped_row g idB hinj]
  rfl

theorem valid_writer_readable (c : Contract σA) (w : Writer σA)
    (h : validateWriter c w = .ok ()) :
    ∀ x ∈ w.reads, x ∈ c.readable := by
  letI : DecidableEq (Address σA) := Program.Executor.addressEq (σ := σA)
  obtain ⟨row, hrow, hdst, hreads⟩ :=
    validated_writer_destination_reads c w h
  have hvalid : w.reads.all (fun x =>
      c.readable.any (fun port => decide (port = x))) = true := by
    have hrow' : c.collectors.find? (fun row => row.2.contains w.capability) =
        some row := by simpa [List.contains_iff_mem] using hrow
    simp only [validateWriter, hrow', hdst, hreads, decide_true, Bool.not_true,
      Bool.false_eq_true, if_false, pure_bind] at h
    change (if !(footprint w.body ()).all
      (fun x => c.readable.any (fun port => decide (port = x))) then
        (Except.error Error.unreadableRead : Except Error Unit) else
        .ok ()) = .ok () at h
    cases hb : (footprint w.body ()).all
      (fun x => c.readable.any (fun port => decide (port = x))) with
    | false => simp [hb] at h
    | true => simpa only [hreads] using hb
  intro x hx
  obtain ⟨port, hp, heq⟩ := List.any_eq_true.mp (List.all_eq_true.mp hvalid x hx)
  simpa [of_decide_eq_true heq] using hp

omit [Fintype σ.Tensor] in
theorem validate_mapped_writer (f : Embedding σA σ) (rename : Nat → Nat)
    (source : Contract σA) (target : Contract σ) (w : Writer σA)
    (hsource : validateWriter source w = .ok ())
    (hlookup : target.collectors.find?
        (fun row => row.2.contains (rename w.capability)) =
      (source.collectors.find? (fun row => row.2.contains w.capability)).map
        (mapRow f rename))
    (hreadable : ∀ x ∈ source.readable, f.address x ∈ target.readable) :
    validateWriter target (mapWriter f rename w) = .ok () := by
  letI : DecidableEq (Address σ) := Program.Executor.addressEq (σ := σ)
  obtain ⟨row, hrow, hdst, hreads⟩ :=
    validated_writer_destination_reads source w hsource
  have hrow' : source.collectors.find? (fun row => row.2.contains w.capability) =
      some row := by simpa [List.contains_iff_mem] using hrow
  have hfind : target.collectors.find?
      (fun row => row.2.contains (mapWriter f rename w).capability) =
      some (mapRow f rename row) := by
    change target.collectors.find? (fun row => row.2.contains (rename w.capability)) =
      some (mapRow f rename row)
    rw [hlookup, hrow']
    rfl
  have hdest : (mapWriter f rename w).destination = (mapRow f rename row).1 := by
    simpa [mapWriter, mapRow] using congrArg f.address hdst
  have hfpt : (mapWriter f rename w).reads =
      footprint (mapWriter f rename w).body () :=
    (mapWriter_reads f rename w).mpr hreads
  have hread : ∀ x ∈ (mapWriter f rename w).reads, x ∈ target.readable := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (show x ∈ w.reads.map f.address from hx)
    exact hreadable y (valid_writer_readable source w hsource y hy)
  have hreads' : (mapWriter f rename w).reads.all
      (fun x => target.readable.any (fun port => decide (port = x))) = true := by
    apply List.all_eq_true.mpr
    intro x hx
    exact List.any_eq_true.mpr ⟨x, hread x hx, by simp⟩
  simp only [validateWriter, hfind, hdest, hfpt, decide_true, Bool.not_true,
    Bool.false_eq_true, if_false, pure_bind]
  rw [← hfpt]
  change (if !((mapWriter f rename w).reads.all
    (fun x => target.readable.any (fun port => decide (port = x)))) then
      (Except.error Error.unreadableRead : Except Error Unit) else .ok ()) = .ok ()
  simp [hreads']

omit [Fintype σ.Tensor] in
theorem validateWriters_of_forall (c : Contract σ)
    (ws : List (Writer σ))
    (h : ∀ w ∈ ws, validateWriter c w = .ok ()) :
    validateWriters c ws = .ok () := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [validateWriters, h w (List.mem_cons_self)]
    exact ih (fun v hv => h v (List.mem_cons_of_mem w hv))

theorem closureFacts_assembled (f : Embedding σA σ) (g : Embedding σB σ)
    (idA idB : Nat → Nat)
    (hinjA : Function.Injective idA) (hinjB : Function.Injective idB)
    (hids : ∀ x y, idA x ≠ idB y)
    (tensors : List σ.Tensor) (input : σ.Tensor → Bool)
    (a : Contract σA) (b : Contract σB)
    (fa : Fragment σA) (fb : Fragment σB)
    (ha : ClosureFacts a fa) (hb : ClosureFacts b fb)
    (hscope : ClosureScope f g input a b)
    (htensors : tensors.Nodup)
    (htensorCount : tensors.length = Fintype.card σ.Tensor) :
    ClosureFacts (assembledContract f g idA idB tensors input a b)
      (assembledFragment f g idA idB fa fb) := by
  let c := assembledContract f g idA idB tensors input a b
  let fr := assembledFragment f g idA idB fa fb
  letI : DecidableEq (Address σ) := Program.Executor.addressEq (σ := σ)
  have hcollectA (x : Address σA) (hx : a.input x.1 = false) :
      f.address x ∈ c.collectors.map Prod.fst := by
    simp only [c, assembledContract, List.map_append, mapped_addresses,
      List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨x, (ha.collector_iff x).mpr hx, rfl⟩)
  have hcollectB (y : Address σB) (hy : b.input y.1 = false) :
      g.address y ∈ c.collectors.map Prod.fst := by
    simp only [c, assembledContract, List.map_append, mapped_addresses,
      List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨y, (hb.collector_iff y).mpr hy, rfl⟩)
  have hreadA (x : Address σA) (hx : x ∈ a.readable) :
      f.address x ∈ c.readable := by
    simp only [c, assembledContract, List.mem_dedup, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨x, hx, rfl⟩)
  have hreadB (y : Address σB) (hy : y ∈ b.readable) :
      g.address y ∈ c.readable := by
    simp only [c, assembledContract, List.mem_dedup, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨y, hy, rfl⟩)
  refine {
    tensors_nodup := htensors
    tensors_count := htensorCount
    collectors_nodup := ?_
    collectors_defined := ?_
    collectors_cover := ?_
    readable_nodup := ?_
    readable_valid := ?_
    outputs_nodup := ?_
    outputs_covered := ?_
    capabilities_nodup := ?_
    tags_nodup := ?_
    writer_capabilities_nodup := ?_
    capabilities_covered := ?_
    writers_valid := ?_
  }
  · simp only [assembledContract, List.map_append, mapped_addresses]
    apply List.nodup_append.mpr
    refine ⟨ha.collectors_nodup.map f.address_injective,
      hb.collectors_nodup.map g.address_injective, ?_⟩
    intro x hx y hy heq
    obtain ⟨xa, hxa, rfl⟩ := List.mem_map.mp hx
    obtain ⟨yb, hyb, rfl⟩ := List.mem_map.mp hy
    exact hscope.defined_disjoint xa yb
      ((ha.collector_iff xa).mp hxa) ((hb.collector_iff yb).mp hyb) heq
  · intro row hr
    rcases List.mem_append.mp (show row ∈ a.collectors.map (mapRow f idA) ++
      b.collectors.map (mapRow g idB) from hr) with hra | hrb
    · obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hra
      simpa only [c, assembledContract, mapRow, Embedding.address] using
        (hscope.upstream_roles source.1.1).trans (ha.collectors_defined source hsource)
    · obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hrb
      exact hscope.downstream_defined source.1.1
        (hb.collectors_defined source hsource)
  · intro z hz
    have hz' : input z.1 = false :=
      ((mem_definedAddresses_iff c z).mp hz).2
    rcases hscope.defined_partition z hz' with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
    · exact hcollectA x hx
    · exact hcollectB y hy
  · exact List.nodup_dedup _
  · intro z hz
    have hz' : z ∈ a.readable.map f.address ++ b.readable.map g.address := by
      simpa only [c, assembledContract, List.mem_dedup] using hz
    rcases List.mem_append.mp hz' with hza | hzb
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hza
      rcases ha.readable_valid x hx with hi | hd
      · exact Or.inl ((hscope.upstream_roles x.1).trans hi)
      · exact Or.inr (hcollectA x ((ha.collector_iff x).mp hd))
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hzb
      rcases hb.readable_valid y hy with hi | hd
      · apply Or.inr
        simp only [assembledContract, List.map_append, mapped_addresses,
          List.mem_append]
        exact Or.inl (by simpa only [List.map_map, Function.comp_apply] using
          hscope.boundary_collector y hi)
      · exact Or.inr (hcollectB y ((hb.collector_iff y).mp hd))
  · simpa only [c, assembledContract] using hb.outputs_nodup.map g.address_injective
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact hcollectB y ((hb.collector_iff y).mp (hb.outputs_covered y hy))
  · simp only [assembledContract, List.flatMap_append, mapped_capabilities]
    exact nodup_mapped_append _ _ idA idB hinjA hinjB hids
      ha.capabilities_nodup hb.capabilities_nodup
  · simpa [fr, assembledFragment, mapWriter, List.map_append, List.map_map,
      Function.comp_def] using
      (nodup_mapped_append _ _ idA idB hinjA hinjB hids
        ha.tags_nodup hb.tags_nodup)
  · simpa [fr, assembledFragment, mapWriter, List.map_append, List.map_map,
      Function.comp_def] using
      (nodup_mapped_append _ _ idA idB hinjA hinjB hids
        ha.writer_capabilities_nodup hb.writer_capabilities_nodup)
  · intro cap hcap
    simp only [assembledContract, List.flatMap_append, mapped_capabilities,
      List.mem_append] at hcap
    rcases hcap with hca | hcb
    · obtain ⟨sourceCap, hc, rfl⟩ := List.mem_map.mp hca
      obtain ⟨w, hw, hcapEq⟩ := ha.capabilities_covered sourceCap hc
      exact ⟨mapWriter f idA w, List.mem_append.mpr
        (Or.inl (List.mem_map.mpr ⟨w, hw, rfl⟩)), by simp [mapWriter, hcapEq]⟩
    · obtain ⟨sourceCap, hc, rfl⟩ := List.mem_map.mp hcb
      obtain ⟨w, hw, hcapEq⟩ := hb.capabilities_covered sourceCap hc
      exact ⟨mapWriter g idB w, List.mem_append.mpr
        (Or.inr (List.mem_map.mpr ⟨w, hw, rfl⟩)), by simp [mapWriter, hcapEq]⟩
  · apply validateWriters_of_forall
    intro w hw
    rcases List.mem_append.mp hw with hwa | hwb
    · obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hwa
      apply validate_mapped_writer f idA a c source
        (validated_writers_forall a fa.writers ha.writers_valid source hs)
      · exact find_assembled_rowA f g idA idB hinjA hids a b source.capability
      · exact hreadA
    · obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hwb
      apply validate_mapped_writer g idB b c source
        (validated_writers_forall b fb.writers hb.writers_valid source hs)
      · exact find_assembled_rowB f g idA idB hinjB hids a b source.capability
      · exact hreadB

def assembledGraph (f : Embedding σA σ) (g : Embedding σB σ)
    (idA idB : Nat → Nat) (tensors : List σ.Tensor) (input : σ.Tensor → Bool)
    (a : Contract σA) (b : Contract σB)
    (fa : Fragment σA) (fb : Fragment σB) : Closed σ where
  contract := assembledContract f g idA idB tensors input a b
  steps := (canonicalSteps a fa).map (mapStep f idA) ++
    (canonicalSteps b fb).map (mapStep g idB)

theorem close_assembled (f : Embedding σA σ) (g : Embedding σB σ)
    (idA idB : Nat → Nat)
    (hinjA : Function.Injective idA) (hinjB : Function.Injective idB)
    (hids : ∀ x y, idA x ≠ idB y)
    (tensors : List σ.Tensor) (input : σ.Tensor → Bool)
    (a : Contract σA) (b : Contract σB)
    (fa : Fragment σA) (fb : Fragment σB)
    (ga : Closed σA) (gb : Closed σB)
    (hcloseA : close a fa = .ok ga) (hcloseB : close b fb = .ok gb)
    (hscope : ClosureScope f g input a b)
    (htensors : tensors.Nodup)
    (htensorCount : tensors.length = Fintype.card σ.Tensor) :
    close (assembledContract f g idA idB tensors input a b)
      (assembledFragment f g idA idB fa fb) =
        .ok (assembledGraph f g idA idB tensors input a b fa fb) := by
  have h := closureFacts_assembled f g idA idB hinjA hinjB hids tensors input
    a b fa fb (ClosureFacts.of_close hcloseA) (ClosureFacts.of_close hcloseB)
    hscope htensors htensorCount
  rw [h.close, canonicalSteps_assembled f g idA idB hinjA hinjB hids]
  rfl

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σB.Tensor]
    [DecidableEq σB.Tensor] [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem assembled_writer_length (f : Embedding σA σ) (g : Embedding σB σ)
    (idA idB : Nat → Nat) (fa : Fragment σA) (fb : Fragment σB) :
    (assembledFragment f g idA idB fa fb).writers.length =
      fa.writers.length + fb.writers.length := by
  simp [assembledFragment]

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σB.Tensor]
    [DecidableEq σB.Tensor] [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem assembled_writer_upstream (f : Embedding σA σ) (g : Embedding σB σ)
    (idA idB : Nat → Nat) (fa : Fragment σA) (fb : Fragment σB)
    (i : Nat) (hi : i < fa.writers.length) :
    (assembledFragment f g idA idB fa fb).writers[i]'(by
      simpa [assembledFragment] using Nat.lt_add_right fb.writers.length hi) =
      mapWriter f idA fa.writers[i] := by
  simp [assembledFragment, List.getElem_append_left, hi]

omit [Fintype σA.Tensor] [DecidableEq σA.Tensor] [Fintype σB.Tensor]
    [DecidableEq σB.Tensor] [Fintype σ.Tensor] [DecidableEq σ.Tensor] in
theorem assembled_writer_downstream (f : Embedding σA σ) (g : Embedding σB σ)
    (idA idB : Nat → Nat) (fa : Fragment σA) (fb : Fragment σB)
    (i : Nat) (hi : i < fb.writers.length) :
    (assembledFragment f g idA idB fa fb).writers[fa.writers.length + i]'(by
      simpa [assembledFragment] using Nat.add_lt_add_left hi fa.writers.length) =
      mapWriter g idB fb.writers[i] := by
  simp [assembledFragment, List.getElem_append_right]

end IndexedComponentComposition

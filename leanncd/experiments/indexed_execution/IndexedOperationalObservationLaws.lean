import IndexedOperationalHistory

namespace IndexedComponentTransport

open LeanNCD.Semantics

def Domain.symm (d : Domain x y) : Domain y x where
  axes := d.axes.symm
  extent := fun i => by simpa using (d.extent (d.axes.symm i)).symm
  coord := d.coord.symm
  raw := d.raw.symm
  raw_axis := by
    intro q i
    have h := d.raw_axis (d.raw.symm q) (d.axes.symm i)
    simpa using h.symm
  coherent := by
    intro p
    apply d.raw.injective
    simpa using (d.coherent (d.coord.symm p)).symm

end IndexedComponentTransport

namespace IndexedOperationalHistory

open LeanNCD.Semantics LeanNCD.Semantics.Program IndexedOpenComposition
open IndexedComponentTransport IndexedComponentComposition

variable {σ τ υ : Declarations Unit}

def MetadataTransport.refl (σ : Declarations Unit) : MetadataTransport σ σ where
  toGraphTransport := ⟨Equiv.refl _, Equiv.refl _⟩
  tensor := Equiv.refl _
  domain := fun a => Domain.id (σ.signature a).axes
  address_eq := fun _ => rfl

def MetadataTransport.inverseDomain (t : MetadataTransport σ τ) (b : τ.Tensor) :
    Domain (τ.signature b).axes (σ.signature (t.tensor.symm b)).axes := by
  simpa only [Equiv.apply_symm_apply] using (t.domain (t.tensor.symm b)).symm

private theorem dependent_congr {α : Sort*} {β : α → Sort*} (f : ∀ a, β a)
    {a b : α} (h : a = b) : HEq (f a) (f b) := by cases h; rfl

private theorem inverseDomain_heq (t : MetadataTransport σ τ) (a : σ.Tensor) :
    HEq (t.inverseDomain (t.tensor a)) (t.domain a).symm := by
  unfold MetadataTransport.inverseDomain
  exact (cast_heq _ _).trans
    (dependent_congr (fun a => (t.domain a).symm) (t.tensor.symm_apply_apply a))

private theorem domain_address_eq {a b : σ.Tensor} {c : τ.Tensor}
    (d : Domain (τ.signature c).axes (σ.signature a).axes)
    (e : Domain (τ.signature c).axes (σ.signature b).axes)
    (h : a = b) (hd : HEq d e) (p : Coord (τ.signature c).axes) :
    (⟨a, d.coord p⟩ : Address σ) = ⟨b, e.coord p⟩ := by
  subst b
  cases eq_of_heq hd
  rfl

private theorem inverseDomain_address (t : MetadataTransport σ τ) (a : σ.Tensor)
    (p : Coord (τ.signature (t.tensor a)).axes) :
    (⟨t.tensor.symm (t.tensor a), (t.inverseDomain (t.tensor a)).coord p⟩ : Address σ) =
      ⟨a, (t.domain a).coord.symm p⟩ :=
  domain_address_eq _ _ (t.tensor.symm_apply_apply a) (inverseDomain_heq t a) p

def MetadataTransport.symm (t : MetadataTransport σ τ) : MetadataTransport τ σ where
  toGraphTransport := t.toGraphTransport.symm
  tensor := t.tensor.symm
  domain := t.inverseDomain
  address_eq := by
    rintro ⟨b, p⟩
    obtain ⟨a, rfl⟩ := t.tensor.surjective b
    change t.address.symm ⟨t.tensor a, p⟩ =
      ⟨t.tensor.symm (t.tensor a), (t.inverseDomain (t.tensor a)).coord p⟩
    rw [inverseDomain_address]
    apply t.address.injective
    simp only [Equiv.apply_symm_apply]
    rw [t.address_eq]
    simp

def MetadataTransport.trans (t : MetadataTransport σ τ) (u : MetadataTransport τ υ) :
    MetadataTransport σ υ where
  toGraphTransport := ⟨t.address.trans u.address, t.identity.trans u.identity⟩
  tensor := t.tensor.trans u.tensor
  domain := fun a => (t.domain a).comp (u.domain (t.tensor a))
  address_eq := by
    intro a
    change u.address (t.address a) = _
    rw [t.address_eq, u.address_eq]
    rfl

private theorem port_ext (p q : Port σ) (h : p.tensor = q.tensor) : p = q := by
  rcases p with ⟨a, s, ax, hs, ha⟩
  rcases q with ⟨b, v, bx, hv, hb⟩
  dsimp only at h
  subst b
  cases hs
  cases hv
  cases ha
  cases hb
  rfl

@[simp] theorem MetadataTransport.port_refl (p : Port σ) :
    (MetadataTransport.refl σ).port p = p := port_ext _ _ rfl

@[simp] theorem MetadataTransport.port_symm (t : MetadataTransport σ τ) (p : Port σ) :
    t.symm.port (t.port p) = p := by
  apply port_ext
  exact t.tensor.symm_apply_apply p.tensor

theorem MetadataTransport.port_trans (t : MetadataTransport σ τ)
    (u : MetadataTransport τ υ) (p : Port σ) :
    (t.trans u).port p = u.port (t.port p) := port_ext _ _ rfl

theorem MetadataTransport.agrees_refl {Adapters : Type*}
    (x : GraphMetadata σ Adapters) :
    (MetadataTransport.refl σ).Agrees (Equiv.refl Adapters) x x := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · have hp : (MetadataTransport.refl σ).port = id := funext port_refl
    rw [hp, List.map_id]
  · have hp : (MetadataTransport.refl σ).port = id := funext port_refl
    rw [hp, List.map_id]
  · intro a; rfl
  · intro a
    change x.input a = (x.input a).map id
    simp

private theorem inverse_input {a b : σ.Tensor} {c : τ.Tensor}
    (d : Domain (σ.signature a).axes (τ.signature c).axes)
    (e : Domain (τ.signature c).axes (σ.signature b).axes)
    (hab : b = a) (hd : HEq e d.symm)
    (x : InputBinding (K := RationalReference.Carrier) (σ := σ))
    (y : Option (Coord (τ.signature c).axes → ℚ))
    (hy : y = (x a).map (fun v p => v (d.coord.symm p))) :
    x b = y.map (fun v p => v (e.coord.symm p)) := by
  subst b
  cases eq_of_heq hd
  rw [hy]
  simp [Domain.symm, Option.map_map, Function.comp_def]

theorem MetadataTransport.agrees_symm {Adapters Other : Type*}
    (t : MetadataTransport σ τ) (adapters : Adapters ≃ Other)
    {x : GraphMetadata σ Adapters} {y : GraphMetadata τ Other}
    (h : t.Agrees adapters x y) : t.symm.Agrees adapters.symm y x := by
  rcases h with ⟨hi, ho, hr, hv, ha⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hi, List.map_map]
    simp [Function.comp_def]
  · rw [ho, List.map_map]
    simp [Function.comp_def]
  · intro b
    obtain ⟨a, rfl⟩ := t.tensor.surjective b
    simpa [symm] using (hr a).symm
  · intro b
    obtain ⟨a, rfl⟩ := t.tensor.surjective b
    exact inverse_input (t.domain a) (t.inverseDomain (t.tensor a))
      (t.tensor.symm_apply_apply a) (inverseDomain_heq t a) x.input
      (y.input (t.tensor a)) (hv a)
  · rw [ha]
    simp

theorem MetadataTransport.agrees_trans {Adapters Other Last : Type*}
    (t : MetadataTransport σ τ) (u : MetadataTransport τ υ)
    (adapters : Adapters ≃ Other) (next : Other ≃ Last)
    {x : GraphMetadata σ Adapters} {y : GraphMetadata τ Other}
    {z : GraphMetadata υ Last}
    (h : t.Agrees adapters x y) (k : u.Agrees next y z) :
    (t.trans u).Agrees (adapters.trans next) x z := by
  rcases h with ⟨hi, ho, hr, hv, ha⟩
  rcases k with ⟨ki, ko, kr, kv, ka⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ki, hi, List.map_map]
    apply List.map_congr_left
    intro p _
    exact (port_trans t u p).symm
  · rw [ko, ho, List.map_map]
    apply List.map_congr_left
    intro p _
    exact (port_trans t u p).symm
  · intro a
    exact (kr (t.tensor a)).trans (hr a)
  · intro a
    change z.input (u.tensor (t.tensor a)) = (x.input a).map
      (fun v p => v ((t.domain a).coord.symm ((u.domain (t.tensor a)).coord.symm p)))
    rw [kv, hv, Option.map_map]
    rfl
  · rw [ka, ha]
    rfl

@[simp] theorem MetadataTransport.history_refl (h : GraphHistory σ) :
    (MetadataTransport.refl σ).toGraphTransport.history.apply h = h := by
  induction h <;>
    simp_all [Transport.apply, History.map, refl, GraphTransport.history,
      GraphTransport.stateEquiv, GraphTransport.eventEquiv, GraphTransport.mapState,
      GraphTransport.mapEvent, IndexedComponentExecution.mapLedger]
  all_goals cases ‹Event σ› <;> rfl

theorem MetadataTransport.history_symm (t : MetadataTransport σ τ) :
    t.symm.toGraphTransport.history = t.toGraphTransport.history.symm := rfl

theorem MetadataTransport.history_trans (t : MetadataTransport σ τ)
    (u : MetadataTransport τ υ) (h : GraphHistory σ) :
    (t.trans u).toGraphTransport.history.apply h =
      u.toGraphTransport.history.apply (t.toGraphTransport.history.apply h) := by
  induction h <;>
    simp_all [Transport.apply, History.map, trans, GraphTransport.history,
      GraphTransport.stateEquiv, GraphTransport.eventEquiv, GraphTransport.mapState,
      GraphTransport.mapEvent, IndexedComponentExecution.mapLedger, List.map_map,
      Function.comp_def, Equiv.trans_apply]
  all_goals cases ‹Event σ› <;> rfl

theorem CompleteObservation.agrees_refl {Adapters : Type*}
    (x : CompleteObservation σ Adapters) :
    x.Agrees (MetadataTransport.refl σ) (Equiv.refl Adapters) x :=
  ⟨MetadataTransport.agrees_refl _, (MetadataTransport.history_refl _).symm⟩

theorem CompleteObservation.agrees_symm {Adapters Other : Type*}
    (t : MetadataTransport σ τ) (adapters : Adapters ≃ Other)
    {x : CompleteObservation σ Adapters} {y : CompleteObservation τ Other}
    (h : x.Agrees t adapters y) : y.Agrees t.symm adapters.symm x := by
  refine ⟨t.agrees_symm adapters h.1, ?_⟩
  rw [h.2, t.history_symm, Transport.apply_symm]

theorem CompleteObservation.agrees_trans {Adapters Other Last : Type*}
    (t : MetadataTransport σ τ) (u : MetadataTransport τ υ)
    (adapters : Adapters ≃ Other) (next : Other ≃ Last)
    {x : CompleteObservation σ Adapters} {y : CompleteObservation τ Other}
    {z : CompleteObservation υ Last}
    (h : x.Agrees t adapters y) (k : y.Agrees u next z) :
    x.Agrees (t.trans u) (adapters.trans next) z := by
  refine ⟨t.agrees_trans u adapters next h.1 k.1, ?_⟩
  rw [k.2, h.2, MetadataTransport.history_trans]

theorem MetadataTransport.agrees_congr {Adapters Other : Type*}
    (t : MetadataTransport σ τ) (adapters : Adapters ≃ Other)
    {x x' : GraphMetadata σ Adapters} {y y' : GraphMetadata τ Other}
    (hx : x = x') (hy : y = y') :
    t.Agrees adapters x y ↔ t.Agrees adapters x' y' := by rw [hx, hy]

theorem CompleteObservation.agrees_congr {Adapters Other : Type*}
    (t : MetadataTransport σ τ) (adapters : Adapters ≃ Other)
    {x x' : CompleteObservation σ Adapters} {y y' : CompleteObservation τ Other}
    (hx : x.metadata = x'.metadata) (hy : y.metadata = y'.metadata)
    (hhx : x.history = x'.history) (hhy : y.history = y'.history) :
    x.Agrees t adapters y ↔ x'.Agrees t adapters y' := by
  simp only [Agrees, hx, hy, hhx, hhy]

namespace MetadataLawFixtures

open IndexedComponentCompositionLocalFixtures IndexedComponentCompositionPortFixtures

def absentEmptyMetadata : GraphMetadata emptyProducerDeclarations Unit where
  inputs := []
  outputs := Fixtures.emptyMetadata.outputs
  inputRole := fun _ => false
  input := fun _ => none
  valid := fun _ => rfl
  adapters := ()
  inputs_nodup := by simp
  outputs_nodup := Fixtures.emptyMetadata.outputs_nodup
  inputs_exact := by intro a; simp

example : (MetadataTransport.refl emptyProducerDeclarations).Agrees
    (Equiv.refl Unit) Fixtures.emptyMetadata Fixtures.emptyMetadata :=
  MetadataTransport.agrees_refl _

example : ¬(MetadataTransport.refl emptyProducerDeclarations).Agrees
    (Equiv.refl Unit) Fixtures.emptyMetadata absentEmptyMetadata := by
  intro h
  have hl := congrArg List.length h.1
  have bad : (0 : Nat) = 1 := by
    simpa only [List.length_map] using hl
  contradiction

example : ∀ a : Address emptyProducerDeclarations,
    (initial Fixtures.emptyMetadata.input).available a =
      (initial absentEmptyMetadata.input).available a := by
  intro a
  exact Fin.elim0 a.2.1

example : ¬(MetadataTransport.refl emptyProducerDeclarations).Agrees
    (Equiv.refl Unit) Fixtures.emptyMetadata absentEmptyMetadata := by
  intro h
  have hv := h.2.2.2.1 emptyExternalInput
  simp [absentEmptyMetadata, Fixtures.emptyMetadata, GraphMetadata.ofComponent,
    MetadataTransport.refl, Domain.id, emptyValidatedInput, emptyPresentInput] at hv

end MetadataLawFixtures

#print axioms Domain.symm
#print axioms MetadataTransport.symm
#print axioms MetadataTransport.agrees_refl
#print axioms MetadataTransport.agrees_symm
#print axioms MetadataTransport.agrees_trans
#print axioms CompleteObservation.agrees_refl
#print axioms CompleteObservation.agrees_symm
#print axioms CompleteObservation.agrees_trans
#print axioms CompleteObservation.agrees_congr

end IndexedOperationalHistory

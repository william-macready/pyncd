import LeanNCD.Semantics.RationalReference
import LeanNCD.Semantics.Readiness

namespace IndexedComponentTransport

open LeanNCD.Semantics

abbrev K := RationalReference.Carrier
abbrev R := RationalReference.registry

/-- Explicit axis correspondence, with adapters certified against that correspondence.
    In particular these fields cannot certify an arbitrary reshape. -/
structure Domain (src dst : Shape) where
  axes : Fin src.length ≃ Fin dst.length
  extent : ∀ i, (src.get i).extent = (dst.get (axes i)).extent
  coord : Coord src ≃ Coord dst
  raw : RawCoord src ≃ RawCoord dst
  raw_axis : ∀ q i, raw q (axes i) = q i
  coherent : ∀ p, raw (Coord.raw p) = Coord.raw (coord p)

def Domain.id (sh : Shape) : Domain sh sh where
  axes := Equiv.refl _
  extent := fun _ => rfl
  coord := Equiv.refl _
  raw := Equiv.refl _
  raw_axis := fun _ _ => rfl
  coherent := fun _ => rfl

def Domain.comp (a : Domain x y) (b : Domain y z) : Domain x z where
  axes := a.axes.trans b.axes
  extent := fun i => (a.extent i).trans (b.extent (a.axes i))
  coord := a.coord.trans b.coord
  raw := a.raw.trans b.raw
  raw_axis := by intro q i; exact (b.raw_axis _ _).trans (a.raw_axis _ _)
  coherent := by intro p; change b.raw (a.raw (Coord.raw p)) = _; rw [a.coherent, b.coherent]; rfl

def mapOutcome (e : C → D) : ReadOutcome ℚ C → ReadOutcome ℚ D
  | .at p => .at (e p)
  | .const c => .const c
  | .reject => .reject

def mapResolved (e : C → D) : Resolved ℚ C → Resolved ℚ D
  | .at p => .at (e p)
  | .const c => .const c

theorem outcome_map (e : C → D) (v : Resolved ℚ C) :
    (mapResolved e v).outcome = mapOutcome e v.outcome := by cases v <;> rfl

def Domain.policy (d : Domain x y) (p : ReadPolicy ℚ x) : ReadPolicy ℚ y where
  resolve := fun q => mapOutcome d.coord (p.resolve (d.raw.symm q))
  inBounds := by
    intro q
    have h : d.raw.symm (Coord.raw q) = Coord.raw (d.coord.symm q) := by
      apply d.raw.injective
      simp only [Equiv.apply_symm_apply, d.coherent]
    rw [h, p.inBounds]
    simp [mapOutcome]

def Domain.read (d : Domain x y) (h : Δ → Γ) (a : AdmittedRead ℚ x Γ) :
    AdmittedRead ℚ y Δ where
  policy := d.policy a.policy
  raw := fun γ => d.raw (a.raw (h γ))
  resolved := fun γ => mapResolved d.coord (a.resolved (h γ))
  admission := by
    intro γ
    simp only [Domain.policy, Equiv.symm_apply_apply, a.admission, outcome_map]

theorem Domain.policy_id (p : ReadPolicy ℚ x) (q : RawCoord x) :
    ((Domain.id x).policy p).resolve q = p.resolve q := by
  change mapOutcome (Equiv.refl (Coord x)) (p.resolve q) = p.resolve q
  cases p.resolve q <;> rfl

theorem Domain.policy_comp (a : Domain x y) (b : Domain y z)
    (p : ReadPolicy ℚ x) (q : RawCoord z) :
    ((a.comp b).policy p).resolve q = (b.policy (a.policy p)).resolve q := by
  change mapOutcome (a.coord.trans b.coord) (p.resolve (a.raw.symm (b.raw.symm q))) =
    mapOutcome b.coord (mapOutcome a.coord (p.resolve (a.raw.symm (b.raw.symm q))))
  cases p.resolve (a.raw.symm (b.raw.symm q)) <;> rfl

structure Embedding (src dst : Declarations Unit) where
  tensor : src.Tensor → dst.Tensor
  injective : Function.Injective tensor
  domain : ∀ t, Domain (src.signature t).axes (dst.signature (tensor t)).axes

def Embedding.address (f : Embedding src dst) : Address src → Address dst :=
  fun a => ⟨f.tensor a.1, (f.domain a.1).coord a.2⟩

theorem Embedding.address_injective (f : Embedding src dst) :
    Function.Injective f.address := by
  rintro ⟨t, p⟩ ⟨u, q⟩ h
  have ht : t = u := f.injective (congrArg Sigma.fst h)
  subst u
  have hp := Sigma.mk.inj_iff.mp h
  have : (f.domain t).coord p = (f.domain t).coord q := eq_of_heq hp.2
  exact congrArg (Sigma.mk t) ((f.domain t).coord.injective this)

def Embedding.pull (f : Embedding src dst) (s : PartialStore K dst) : PartialStore K src :=
  fun a => s (f.address a)

def Embedding.pullComplete (f : Embedding src dst) (s : Store K dst) : Store K src :=
  fun a => s (f.address a)

def Embedding.id (src : Declarations Unit) : Embedding src src :=
  ⟨fun t => t, Function.injective_id, fun t => Domain.id (src.signature t).axes⟩

def Embedding.comp (f : Embedding src mid) (g : Embedding mid dst) : Embedding src dst :=
  ⟨g.tensor ∘ f.tensor, g.injective.comp f.injective,
    fun t => (f.domain t).comp (g.domain (f.tensor t))⟩

@[simp] theorem Embedding.address_id (a : Address src) : (Embedding.id src).address a = a := rfl
@[simp] theorem Embedding.address_comp (f : Embedding src mid) (g : Embedding mid dst)
    (a : Address src) : (f.comp g).address a = g.address (f.address a) := rfl

@[simp] theorem Embedding.pull_comp (f : Embedding src mid) (g : Embedding mid dst)
    (s : PartialStore K dst) : (f.comp g).pull s = f.pull (g.pull s) := rfl

end IndexedComponentTransport

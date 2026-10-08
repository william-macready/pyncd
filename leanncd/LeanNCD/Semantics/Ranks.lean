import LeanNCD.Semantics.Machine

namespace LeanNCD.Semantics.Program

variable {K : S → Type} {σ : Declarations S} {r : Registry K}

abbrev DefinedAddress (P : Program K σ r) :=
  (t : P.Defined) × Coord (σ.signature t.val).axes

def definedAddress (P : Program K σ r) (a : P.DefinedAddress) : Address σ :=
  ⟨a.1.val, a.2⟩

theorem definedAddress_injective (P : Program K σ r) :
    Function.Injective P.definedAddress := by
  rintro ⟨t, p⟩ ⟨u, q⟩ h
  have ht : t = u := Subtype.ext (congrArg Sigma.fst h)
  subst u
  have hp : p = q := by simpa [definedAddress] using h
  subst q
  rfl

def dependencies (P : Program K σ r) (a : Address σ) : Set (Address σ) :=
  {b | ∃ (t : P.Defined) (o : P.Occurrence t),
    a = ⟨t.val, P.destination t o.1 o.2⟩ ∧ b ∈ footprint (P.body t o.1) o.2}

theorem input_dependencies_empty (P : Program K σ r) (a : Address σ)
    (input : P.input a.1 = true) : P.dependencies a = ∅ := by
  ext b
  constructor
  · rintro ⟨t, o, h, _⟩
    have ht := congrArg Sigma.fst h
    simp only at ht
    rw [ht, t.property] at input
    contradiction
  · simp

structure RankCertificate (P : Program K σ r) where
  rank : Address σ → Nat
  decreases : ∀ a b, b ∈ P.dependencies a → rank b < rank a

noncomputable instance definedFintype (P : Program K σ r) : Fintype P.Defined := by
  classical
  letI := P.tensors
  exact inferInstance

noncomputable instance definedAddressFintype (P : Program K σ r) :
    Fintype P.DefinedAddress := by
  letI : ∀ t : P.Defined, Fintype (Coord (σ.signature t.val).axes) :=
    fun t => Fintype.ofEquiv _ (canonicalLayout (σ.signature t.val).axes).enumerate
  exact inferInstance

end LeanNCD.Semantics.Program

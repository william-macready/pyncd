import Mathlib
import LeanNCD.Core.Graded

namespace LeanNCD

open CategoryTheory

/-- Structural congruence on `C`-morphisms (graded_prop.md §7.1): two morphisms are related iff
    they agree on connectivity (weave shapes, op names, routing) and differ only on `SizeExpr`
    sizes. STUB body — the real relation compares the structural skeletons.

    `HomRel C` unfolds to `∀ {X Y : C}, (X ⟶ Y) → (X ⟶ Y) → Prop`; the seam
    (`instCategoryOfColoredPROP`) supplies the `Category C` the `⟶` notation needs. -/
def structuralCongruence (C : Type) [ColoredPROP C] : HomRel C :=
  fun _ _ _ _ => True   -- SIGNATURE: replace with the real connectivity-agreement relation.

/-- The structural congruence is a `Congruence` (graded_prop.md §7.1): an equivalence relation,
    stable under pre- and post-composition. Proved for the `True` stub (the real relation must be re-proved a genuine congruence). -/
instance structuralCongruence.instCongruence (C : Type) [ColoredPROP C] :
    Congruence (structuralCongruence C) where
  -- The `True` stub is trivially a congruence.
  comp_left  := fun {_} {_} {_} _f {_} {_} h => h
  comp_right := fun {_} {_} {_} {_} {_} _g h => h
  equivalence := ⟨fun _ => trivial, fun h => h, fun _ _ => trivial⟩

/-- `C♯` — the structural index PROP: `C` with `SizeExpr` sizes erased, realised as the categorical
    quotient of `C` by `structuralCongruence`. `CategoryTheory.Quotient` takes the `HomRel`
    directly (the `Congruence` instance above witnesses that it is a quotient of categories).

    Spelled `Cˢʰᵃʳᵖ` via the notation below (the superscript `ˢʰᵃʳᵖ` is not a legal Lean
    identifier, so the underlying definition is `CSharp`). -/
abbrev CSharp (C : Type) [ColoredPROP C] : Type :=
  CategoryTheory.Quotient (structuralCongruence C)

/-- `C♯`, the structural index PROP (see `CSharp`). -/
notation "Cˢʰᵃʳᵖ" => CSharp

/-! ## No data functor here (removed 2026-11-24)

A covariant `Dat : C♯ ⥤ Type` (and `Dat' := Dat ⋙ typeToCat`, for `CategoryTheory.Grothendieck`)
used to live here as a `Unit`-valued stub. It was removed because a covariant functor is the
wrong shape for the size data (graded_prop.md §5, Prop 8.3). Sizes over a morphism form a span
between its boundary sizings, since internal wires carry sizes that neither boundary sees. A
faithful version is the sizing functor `U : C → C♯` with its fibres described, or a
`Span`-valued lax functor. `grothendieck_split` was already deleted as false-as-stated
(`2229cf66`). -/

end LeanNCD

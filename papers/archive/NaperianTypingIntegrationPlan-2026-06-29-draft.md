# Naperian Typing Integration Plan for LeanNCD

## Executive summary

Add Naperian/applicative structure as **opt-in mixins** around the existing `DGradedColoredPROP` core. Do not replace `DGradedColoredPROP` or `Elemental` in the first pass. The minimum useful integration is:

1. create `LeanNCD/Core/Naperian.lean` with the mixin classes and Naperian evaluation API;
2. create a `StObj` instance in a small instance file;
3. connect Naperian evaluations to existing `ev_p`;
4. use the new point API to restate later proof obligations (`broadcast_gen`, pointwise lifting, reindexing) extensionally.

Important current-code fact: `Base/St.lean` currently defines `Axis` only as

```lean
structure Axis where
  name : Option String
  size : Numeric
```

There is no `Axis.point` or `Axis.enum` yet. Because `size : Numeric` is symbolic, finite coordinate types cannot be derived from it alone. The integration should therefore **augment** axes with a separate point/enumeration semantics, rather than immediately changing the existing `Axis` structure and risking breakage in `StMat`, the DSL bridge, and quotient code.

---

## 1. New files to create

### 1.1 `leanncd/LeanNCD/Core/Naperian.lean`

**Module:** `LeanNCD.Core.Naperian`

**Imports:**

```lean
import Mathlib
import LeanNCD.Core.Graded
```

**Purpose:** Define the reusable Naperian/applicative mixins over any `DGradedColoredPROP`. This file should not import `St` or `Br`; it is generic.

#### Structure

```lean
namespace LeanNCD
open CategoryTheory

/-- Finite, strong-monoidal point semantics for an index PROP `D`.

`point_hom` is the practical bridge to existing `ev_p`, whose point argument is a
morphism `I_D ⟶ P` represented in `Dᵒᵖ` as `op P ⟶ op I_D`.
-/
class NaperianAxis (D : Type) [ColoredPROP D] where
  El : D → Type
  finite : ∀ P : D, Fintype (El P)
  point_hom : ∀ P : D, El P → SmallCategory.hom (ColoredPROP.unit : D) P
  strong_monoidal : ∀ P Q : D,
    El (ColoredPROP.tensor P Q) ≃ El P × El Q
  unit_point : El (ColoredPROP.unit : D) ≃ Unit
  -- Functorial action on points (needed for naturality of the iso in P).
  mapEl : ∀ {P Q : D}, SmallCategory.hom P Q → El P → El Q
  mapEl_id : ∀ P (p : El P), mapEl (SmallCategory.id P) p = p
  mapEl_comp : ∀ {P Q R : D} (f : SmallCategory.hom P Q)
      (g : SmallCategory.hom Q R) (p : El P),
    mapEl (SmallCategory.comp f g) p = mapEl g (mapEl f p)
  point_hom_natural : ∀ {P Q : D} (η : SmallCategory.hom P Q) (p : El P),
    SmallCategory.comp (point_hom P p) η = point_hom Q (mapEl η p)
  -- Monoidal coherence (El is a genuine strong monoidal functor D → FinSet).
  strong_monoidal_assoc : ∀ P Q R : D,
    (strong_monoidal (ColoredPROP.tensor P Q) R).trans
      (Equiv.prodCongr (strong_monoidal P Q) (Equiv.refl _)) =
    (strong_monoidal P (ColoredPROP.tensor Q R)).trans
      (Equiv.prodCongr (Equiv.refl _) (strong_monoidal Q R)).trans
      (Equiv.prodAssoc _ _ _)
  strong_monoidal_unit_l : ∀ P : D,
    (strong_monoidal (ColoredPROP.unit : D) P).trans
      (Equiv.prodCongr unit_point (Equiv.refl _)) =
    Equiv.punitProd _
  strong_monoidal_unit_r : ∀ P : D,
    (strong_monoidal P (ColoredPROP.unit : D)).trans
      (Equiv.prodCongr (Equiv.refl _) unit_point) =
    Equiv.prodPUnit _

attribute [instance] NaperianAxis.finite

/-- Existing `ev_p` specialized to Naperian points. -/
def ev_naperian {D C : Type} [ColoredPROP D] [ColoredPROP C]
    [DGradedColoredPROP D C] [NaperianAxis D]
    {P : D} (p : NaperianAxis.El P) (X : C) :
    SmallCategory.hom
      (DGradedColoredPROP.act.obj (X, Opposite.op P)) X :=
  ev_p (Opposite.op (NaperianAxis.point_hom P p)) X
```

Note: the originally proposed field list did not include `point_hom`. Without it, `ev_naperian` cannot call existing `ev_p`. If a later design makes `El P` definitionally equal to `SmallCategory.hom I P`, `point_hom` can be `id` and marked reducible.

Without `mapEl`, contravariant naturality of `F(X ⊛ P) ≃ (El(P) → F(X))` in `P` cannot be stated or proved. For `StObj`, `mapEl η p` applies the affine stride map `η : StMat P Q` to coordinates.

Without monoidal coherence, nested shapes may be inconsistent — `El ((P ⊗ Q) ⊗ R)` and `El (P ⊗ (Q ⊗ R))` may have incompatible product structures. These fields may be sorry'd in the MVP but must be present.

#### Representability API

Keep this in `Core/Naperian.lean` as a lightweight, target-agnostic family interface. Do **not** force it into `Algebra` yet.

```lean
/-- A semantic family whose lifted values are represented by functions out of `El P`.

Think `F X` as the value type interpreting a `C` object `X`. This is deliberately
simpler than `Algebra`: it can later be instantiated by executable tensors, `Type`,
or a concrete target actegory.

This class is the representability assumption. It is not derived from
`NaperianAxis`: strong monoidality of `El` does not by itself prove
`F (X ⊛ P) ≃ (El P → F X)`. The assumption is encoded explicitly by the
`lookup`/`tabulate` fields and their inverse laws. `NaperianFamily` is an
independent representability assumption, not derived from `NaperianAxis`.
-/
class NaperianFamily (D C : Type) [ColoredPROP D] [ColoredPROP C]
    [DGradedColoredPROP D C] [NaperianAxis D]
    (F : C → Type) where
  lookup : ∀ {X : C} {P : D},
    F (DGradedColoredPROP.act.obj (X, Opposite.op P)) →
      NaperianAxis.El P → F X
  tabulate : ∀ {X : C} {P : D},
    (NaperianAxis.El P → F X) →
      F (DGradedColoredPROP.act.obj (X, Opposite.op P))
  lookup_tabulate : ∀ {X : C} {P : D} (f : NaperianAxis.El P → F X),
    lookup (tabulate f) = f
  tabulate_lookup : ∀ {X : C} {P : D}
      (x : F (DGradedColoredPROP.act.obj (X, Opposite.op P))),
    tabulate (lookup x) = x

namespace NaperianFamily

noncomputable def naperian_iso {D C : Type} [ColoredPROP D] [ColoredPROP C]
    [DGradedColoredPROP D C] [NaperianAxis D]
    {F : C → Type} [NaperianFamily D C F]
    (X : C) (P : D) :
    F (DGradedColoredPROP.act.obj (X, Opposite.op P)) ≃
      (NaperianAxis.El P → F X) where
  toFun := NaperianFamily.lookup
  invFun := NaperianFamily.tabulate
  left_inv := NaperianFamily.tabulate_lookup
  right_inv := NaperianFamily.lookup_tabulate

end NaperianFamily
```

Use names exactly once: either top-level `lookup`/`tabulate` projections or namespace-qualified names. Avoid global unqualified definitions that conflict with other files.

#### Broadcast join mixin

```lean
/-- Canonical common shape for broadcasting. Categorically this should be a chosen
join/alignment in the broadcastable fragment of `D`. -/
class BroadcastJoin (D : Type) [ColoredPROP D] [NaperianAxis D] where
  Join : D → D → D
  inl : ∀ P Q : D, SmallCategory.hom P (Join P Q)
  inr : ∀ P Q : D, SmallCategory.hom Q (Join P Q)
  -- Coordinate projection: points of the join project to points of each factor.
  projl : ∀ P Q : D, NaperianAxis.El (Join P Q) → NaperianAxis.El P
  projr : ∀ P Q : D, NaperianAxis.El (Join P Q) → NaperianAxis.El Q
  projl_natural : ∀ P Q p,
    SmallCategory.comp (NaperianAxis.point_hom (Join P Q) p) (inl P Q) =
      NaperianAxis.point_hom P (projl P Q p)
  projr_natural : ∀ P Q p,
    SmallCategory.comp (NaperianAxis.point_hom (Join P Q) p) (inr P Q) =
      NaperianAxis.point_hom Q (projr P Q p)
  -- Universal property: a point into the join is determined by its projections.
  join_point_sep : ∀ P Q (r s : NaperianAxis.El (Join P Q)),
    projl P Q r = projl P Q s → projr P Q r = projr P Q s → r = s
```

The precise instance of `BroadcastJoin StObj` depends on the chosen axis-alignment strategy (append vs UID union) and is deferred.

#### Reindex action mixin

```lean
/-- Reindexing is contravariant precomposition by a `D` morphism. The lookup law
uses `NaperianAxis.mapEl`, the induced map on finite points. -/
class ReindexAction (D C : Type) [ColoredPROP D] [ColoredPROP C]
    [DGradedColoredPROP D C] [NaperianAxis D] where
  reindex : ∀ {X : C} {P Q : D}, SmallCategory.hom P Q →
    SmallCategory.hom
      (DGradedColoredPROP.act.obj (X, Opposite.op Q))
      (DGradedColoredPROP.act.obj (X, Opposite.op P))
  reindex_def : ∀ {X : C} {P Q : D} (η : SmallCategory.hom P Q),
    reindex (X := X) η =
      DGradedColoredPROP.act.map
        (X := (X, Opposite.op Q)) (Y := (X, Opposite.op P))
        (𝟙 X, Opposite.op η)
  lookup_reindex : ∀ {X : C} {P Q : D} (η : SmallCategory.hom P Q)
      (p : NaperianAxis.El P),
    SmallCategory.comp (reindex (X := X) η) (ev_naperian p X) =
      ev_naperian (NaperianAxis.mapEl η p) X
```

For `StObj`, `mapEl η p` applies the affine stride map `η : StMat P Q` to coordinates. This requires the `AxisPointData.toCoeff` values to be valid coordinates for the domain; bounds and finite-point closure must be proved by the concrete instance.

#### Pointwise lift mixin

```lean
/-- Applicative lifting of base morphisms over a shape. -/
class PointwiseLift (D C : Type) [ColoredPROP D] [ColoredPROP C]
    [DGradedColoredPROP D C] [NaperianAxis D] where
  lift : ∀ {X Y : C} (P : D), SmallCategory.hom X Y →
    SmallCategory.hom
      (DGradedColoredPROP.act.obj (X, Opposite.op P))
      (DGradedColoredPROP.act.obj (Y, Opposite.op P))
  lift_def : ∀ {X Y : C} (P : D) (f : SmallCategory.hom X Y),
    lift P f =
      DGradedColoredPROP.act.map
        (X := (X, Opposite.op P)) (Y := (Y, Opposite.op P))
        (f, 𝟙 (Opposite.op P))
  ev_lift : ∀ {X Y : C} (P : D) (p : NaperianAxis.El P)
      (f : SmallCategory.hom X Y),
    SmallCategory.comp (lift P f) (ev_naperian p Y) =
      SmallCategory.comp (ev_naperian p X) f
```

`ev_lift` should be proved from existing `ev_p_naturality` once `lift_def` unfolds.

#### Elementality bridge

```lean
/-- D-point evaluations jointly separate lifted morphisms (joint monicity of ev_naperian).
    NOT the same as (Elem-C): that axiom uses I_C → X in C; this uses I_D → P in D
    to produce evaluations X ⊛ P → X via ev_naperian.
    Precise statement: if f g : Z → X ⊛ P satisfy
      ∀ p : El P, f ≫ ev_naperian p X = g ≫ ev_naperian p X
    then f = g.
    Proof strategy: from NaperianFamily.tabulate_lookup (if NaperianFamily holds),
    or from a broadcast-gen normal form.
    WARNING: if proved from broadcast_gen, do not use this to prove broadcast_gen. -/
theorem naperian_jointly_monic {D C : Type} [ColoredPROP D] [ColoredPROP C]
    [DGradedColoredPROP D C] [NaperianAxis D]
    {Z X : C} {P : D}
    (f g : SmallCategory.hom Z
      (DGradedColoredPROP.act.obj (X, Opposite.op P)))
    (h : ∀ p : NaperianAxis.El P,
      SmallCategory.comp f (ev_naperian p X) =
      SmallCategory.comp g (ev_naperian p X)) :
    f = g := by
  sorry

end LeanNCD
```

This statement may be simplified after the first implementation. The key is to state separation through `ev_naperian`, not through arbitrary `Br` points or full `Elemental C`.

---

### 1.2 `leanncd/LeanNCD/Instances/StNaperian.lean`

**Module:** `LeanNCD.Instances.StNaperian`

**Imports:**

```lean
import Mathlib
import LeanNCD.Core.Naperian
import LeanNCD.Base.St
```

**Purpose:** Provide the concrete `NaperianAxis StObj` instance and keep the new point semantics out of `Base/St.lean` until stable.

**Definitions:**

- `class AxisPointData` or an equivalent augmentation layer;
- recursive `StEl : StObj → Type`;
- `Fintype (StEl P)`;
- `StEl.appendEquiv : StEl (P ++ Q) ≃ StEl P × StEl Q`;
- `StEl.unitEquiv : StEl [] ≃ Unit`;
- `StEl.toStPoint : StEl P → StMat [] P`;
- `instance : NaperianAxis StObj`.

Detailed code appears in section 3.

---

### 1.3 Optional later file: `leanncd/LeanNCD/Algebra/Naperian.lean`

**Do not create in the MVP unless needed.**

**Module:** `LeanNCD.Algebra.Naperian`

**Imports:**

```lean
import LeanNCD.Core.Naperian
import LeanNCD.Algebra.Algebra
```

**Purpose:** Lift the `NaperianFamily` interface to existing categorical `Algebra` and target actegories. This is where a later concrete `DenseTensor` target should prove

```lean
F.obj (X ⊛ P) ≅ (NaperianAxis.El P → F.obj X)
```

in a target-specific form.

Reason to delay: current `TargetActegory StObj (Mat ℝ) ℝ` is knowingly impossible/placeholder for symbolic sizes, so forcing Naperian representability through it now would create artificial sorries.

---

## 2. Modifications to existing files

### 2.1 `Core/Graded.lean`

**Change:** Import nothing from `Core/Naperian.lean` initially. Keep `DGradedColoredPROP` unchanged.

**Why:** `NaperianAxis` complements the graded core. The existing fields (`act`, `δ`, `δ0`, `υ`, `α`, `broadcast_gen`) are categorical structure. Naperian typing adds finite point semantics and extensional reasoning over that structure.

**Follow-up after MVP:** Add comments near `ev_p` explaining that `Core/Naperian.lean` provides

```lean
ev_naperian {P : D} (p : NaperianAxis.El P) : (X ⊛ P) ⟶ X
```

by converting `p` to a global element `I_D ⟶ P`.

**Does it subsume existing fields?** No, not in the first pass.

- `ev_p` remains the primitive categorical slice.
- `ev_naperian` is a typed finite-coordinate wrapper around `ev_p`.
- `δ`, `δ0`, `υ`, `α` are still needed by the action. Naperian strong monoidality may make their **intended instance proofs** more canonical, but does not replace their fields without a larger redesign of `act`.

**Backward compatible:** Yes.

**Risk:** Low if no import cycle is introduced. `Core/Naperian.lean` should import `Core/Graded.lean`, never the reverse.

---

### 2.2 `Base/ColoredPROP.lean`

**Change:** Keep `class Elemental` unchanged. Add no dependency on Naperian in the MVP.

**Why:** `Elemental` is about arbitrary points of the object category `C`:

```lean
∀ x : I_C ⟶ X, x ; f = x ; g
```

`NaperianAxis` is about finite, enumerable points of the index category `D`, used to evaluate lifted objects `X ⊛ P`. It can imply useful elementality-like theorems for the broadcastable fragment, but `naperian_jointly_monic` is not definitionally the same as `Elemental C`.

**Connection plan:** In `Core/Naperian.lean`, state `naperian_jointly_monic` as a theorem. Later, if the theorem is strong enough, add an adapter:

```lean
noncomputable def elementalOfNaperian ... : Elemental C := ...
```

only for categories where Naperian evaluations really separate all `C` morphisms.

**Backward compatible:** Yes.

**Risk:** Low. The main risk is overclaiming: Naperian separation may hold for `St` and the broadcastable fragment of `Br`, but not for arbitrary quotient `Br` morphisms without a normal-form theorem.

---

### 2.3 `Instances/StBr.lean`

**Change:** Import `LeanNCD.Instances.StNaperian` after the `StObj` instance exists:

```lean
import LeanNCD.Instances.StNaperian
```

Then add or make available:

```lean
instance : NaperianAxis StObj := ...
```

**Why:** The flagship graded instance `D = St`, `C = Br` is where Naperian points provide concrete coordinate tuples. This gives a more explicit target for the deferred `act`, `broadcast_gen`, and pointwise-lift proofs.

**Does it close any of the 10 sorries immediately?** Not by itself. It gives better proof vocabulary:

- `act` can be specified as “append the finite coordinate tuple shape `P` to each array object”.
- `δ`, `δ0`, `υ`, `α` can be checked by comparing coordinate representations (`El (P ++ Q) ≃ El P × El Q`, `El [] ≃ Unit`).
- `broadcast_gen` can be reformulated as an applicative/reindexing normal form theorem.

The concrete definitions still require implementing the `Br` lift/action on quotient morphisms.

**Backward compatible:** Yes if `StNaperian.lean` is imported but no existing structures change.

**Risk:** Medium. If `Axis` itself is modified to carry `point : Type`, universe levels and existing deriving/quotient code may break. Prefer the augmentation layer in section 3.

---

### 2.4 `Algebra/Algebra.lean`

**Change:** No MVP change.

**Why:** Existing `Algebra` is target-actegory based and already includes `F_ev_p`. Naperian typing refines that field by replacing arbitrary `p : P ⟶ I` in `Dᵒᵖ` with `p : El P` and by adding `lookup/tabulate` representability.

When a concrete target satisfies both `Algebra` (which has `F_ev_p`) and `NaperianFamily` (which has `lookup`), a coherence condition is required: `NaperianFamily.lookup x p` must agree with `Algebra.F_ev_p p x` up to the relevant isomorphism. This will be the key law of `NaperianAlgebra` when that subclass is created. Do not instantiate both classes for the same target without verifying this agreement.

**Later optional change:** Add a subclass:

```lean
class NaperianAlgebra ... extends Algebra D C V R where
  -- target-specific representability/lookup-tabulate laws
```

Do this only after a concrete `DenseTensor`/finite-size target exists. Do not attach it to the current `Mat ℝ` target, whose `TargetActegory` instance is intentionally deferred.

**Backward compatible:** Yes.

**Risk:** Low if delayed; high if forced through `FGModuleCat ℝ` now.

---

### 2.5 `Mixins/Temporal.lean`

**Change:** No MVP change. Later add lemmas in `Core/Naperian.lean` or a small `Mixins/TemporalNaperian.lean` file.

**Interaction:** `TemporalGraded` adds directed prefix structure that is **not purely pointwise**. Naperian points tell us what a time coordinate is; `TemporalGraded` tells us which coordinates are causally available.

Useful later lemmas:

- `El (prefix N)` enumerates finite times `0..N`.
- `iotaTo h : prefix m ⟶ prefix n` induces monotone inclusion on `El`.
- `restrict h X` agrees with precomposition along that inclusion.
- `trace`/`iterate` lookup at time `t` depends only on earlier/equal `El` points.

**Backward compatible:** Yes.

**Risk:** Medium. Causality is directed/order-enriched; it should not be collapsed into ordinary Naperian pointwise equality.

---

### 2.6 `LeanNCD.lean`

**Change after MVP compiles:** add imports near the math tower section:

```lean
import LeanNCD.Core.Naperian
import LeanNCD.Instances.StNaperian
```

**Backward compatible:** Yes once new files compile.

**Risk:** Low, except for import cycles. `Instances/StBr.lean` may import `StNaperian`; `LeanNCD.lean` can import both.

---

## 3. Concrete `NaperianAxis StObj` instance

### 3.1 Design choice: augment, do not mutate `Axis` first

The requested instance assumes an axis has a finite point type and enumeration. Current code does not. The safest integration is this augmentation:

```lean
/-- External finite point semantics for symbolic `Axis` values. -/
class AxisPointData where
  Point : Axis → Type
  finite : ∀ a : Axis, Fintype (Point a)
  toCoeff : ∀ a : Axis, Point a → Coeff
  -- Consistency requirements (can be sorry'd in MVP but must be named):
  toCoeff_injective : ∀ a : Axis, Function.Injective (toCoeff a)
  -- Without `toCoeff_injective`, evaluations do not separate coordinates and
  -- `El P` fails to faithfully represent positions.
  -- The cardinality of `Point a` should match the semantics of `a.size`
  -- (enforced by concrete instances, not in the typeclass itself for symbolic sizes).
```

`toCoeff` embeds concrete coordinates into the existing symbolic affine `StMat` representation. In early experiments it can be opaque, but it must satisfy `toCoeff_injective`; for real executable sizes, use an injective `Fin n → Coeff`.
Without `toCoeff_injective`, evaluations do not separate coordinates and `El P` fails to faithfully represent positions. This field may be sorry'd in the MVP but must be present to avoid unsound instances.

A later breaking-change option is:

```lean
structure Axis where
  name : Option String
  size : Numeric
  point : Type
  pointFintype : Fintype point
  pointToCoeff : point → Coeff
```

Do not start there; adding a `Type` field changes the shape of `Axis` and may affect universe levels and existing object equality.

### 3.2 Actual Lean code sketch

Put this in `LeanNCD/Instances/StNaperian.lean`.

```lean
import Mathlib
import LeanNCD.Core.Naperian
import LeanNCD.Base.St

namespace LeanNCD
open CategoryTheory

/-- Finite point semantics attached externally to the existing symbolic `Axis`. -/
class AxisPointData where
  Point : Axis → Type
  finite : ∀ a : Axis, Fintype (Point a)
  toCoeff : ∀ a : Axis, Point a → Coeff
  -- Consistency requirements (can be sorry'd in MVP but must be named):
  toCoeff_injective : ∀ a : Axis, Function.Injective (toCoeff a)
  -- Without `toCoeff_injective`, evaluations do not separate coordinates and
  -- `El P` fails to faithfully represent positions.
  -- The cardinality of `Point a` should match the semantics of `a.size`
  -- (enforced by concrete instances, not in the typeclass itself for symbolic sizes).

attribute [instance] AxisPointData.finite

namespace StNaperian

variable [AxisPointData]

/-- Coordinate tuples for a shape. -/
def El : StObj → Type
  | [] => Unit
  | a :: axes => AxisPointData.Point a × El axes

instance instFintypeEl : ∀ P : StObj, Fintype (El P)
  | [] => inferInstanceAs (Fintype Unit)
  | a :: axes => inferInstanceAs (Fintype (AxisPointData.Point a × El axes))

/-- `El (P ++ Q) ≃ El P × El Q`. -/
def appendEquiv : ∀ P Q : StObj, El (P ++ Q) ≃ El P × El Q
  | [], Q =>
      { toFun := fun q => ((), q)
        invFun := fun x => x.2
        left_inv := by
          intro q
          rfl
        right_inv := by
          intro x
          cases x.1
          rfl }
  | a :: P, Q =>
      let e := appendEquiv P Q
      { toFun := fun x =>
          ((x.1, (e x.2).1), (e x.2).2)
        invFun := fun y =>
          (y.1.1, e.symm (y.1.2, y.2))
        left_inv := by
          intro x
          rcases x with ⟨pa, ps⟩
          simp
        right_inv := by
          intro y
          rcases y with ⟨⟨pa, ps⟩, q⟩
          simp }

/-- Variant for the α coherence iso: (X ⊛ P) ⊛ Q ≅ X ⊛ (Q ⊗ P) uses Q ++ P order. -/
def alphaElEquiv (P Q : StObj) : El (Q ++ P) ≃ El Q × El P :=
  appendEquiv Q P

-- Always use `alphaElEquiv` (not `appendEquiv`) when constructing or checking
-- the `α` coherence iso, to avoid coordinate-order confusion.

/-- Unit shape has exactly one coordinate tuple. -/
def unitEquiv : El ([] : StObj) ≃ Unit := Equiv.refl Unit

/-- Convert a coordinate tuple into the existing `St` global element `[] ⟶ P`.

For `StMat [] P`, the coefficient matrix has no columns; the bias vector stores
the selected coordinate in each output axis. This is a finite embedding into
the full hom-set, not a surjection onto all `StMat [] P` morphisms. -/
noncomputable def toStPoint : ∀ P : StObj, El P → StMat [] P
  | [], _ =>
      { coeffs := 0
        bias := fun i => i.elim0 }
  | a :: axes, p =>
      { coeffs := 0
        bias := fun i =>
          match i with
          | ⟨0, _⟩ => AxisPointData.toCoeff a p.1
          | ⟨Nat.succ n, h⟩ =>
              let i' : Fin axes.length := ⟨n, Nat.succ_lt_succ_iff.mp h⟩
              (toStPoint axes p.2).bias i' }

noncomputable instance instNaperianAxisStObj : NaperianAxis StObj where
  El := El
  finite := instFintypeEl
  point_hom := toStPoint
  mapEl := by
    intro P Q η p
    sorry
  mapEl_id := by
    intro P p
    sorry
  mapEl_comp := by
    intro P Q R f g p
    sorry
  point_hom_natural := by
    intro P Q η p
    sorry
  strong_monoidal := appendEquiv
  unit_point := unitEquiv
  strong_monoidal_assoc := by
    intro P Q R
    sorry
  strong_monoidal_unit_l := by
    intro P
    sorry
  strong_monoidal_unit_r := by
    intro P
    sorry

end StNaperian
end LeanNCD
```

### 3.3 Notes on the code

- `El [] = Unit` definitionally.
- `El (a :: axes) = AxisPointData.Point a × El axes` definitionally.
- Since `ColoredPROP.tensor` for `StObj` is list append, `strong_monoidal` is `appendEquiv`.
- `point_hom` builds the existing `StMat [] P` point used by `Elemental StObj`.
- `toStPoint` provides a finite embedding into `StMat [] P`, not a surjection. Consistency conditions (bounds, injectivity of `toCoeff`) are needed for the embedding to faithfully represent coordinates; see the `AxisPointData` consistency fields.
- Use `alphaElEquiv`, not `appendEquiv`, when proving the `α` coherence iso; `α` needs `El (Q ++ P) ≃ El Q × El P`.
- The code assumes `Coeff` is in scope from `Base/Numeric.lean` through `Base/St.lean`.
- The `Nat.succ_lt_succ_iff.mp h` line may need a small helper lemma if Lean does not infer it cleanly. If so, define a local helper for tail `Fin` indices.
- This is intentionally parameterized by `[AxisPointData]`. Without such data, a global finite `NaperianAxis StObj` instance is not constructible from symbolic `Numeric` sizes.

---

## 4. Which open sorries become easier or closeable

### 4.1 `Instances/StBr.lean`: `instDGradedStBr.act`

**Directly closes?** No.

**Helps?** Yes. `NaperianAxis.El P` makes the intended lift explicit: an object lifted by `P` is a family indexed by coordinate tuples of `P`.

**What is still needed:** Define the actual functor

```lean
act : (BrObj × StObjᵒᵖ) ⥤ BrObj
```

on objects and quotient morphisms. Object-level action is likely:

```lean
X ⊛ P = X.map (fun A => { A with shape := A.shape ++ P })
```

or the equivalent shape convention. Morphism-level action must map `BrMorph` constructors and respect `Rel`. Naperian points help state correctness but do not by themselves define quotient-respecting action.

---

### 4.2 `Instances/StBr.lean`: `δ`, `δ0`, `υ`, `α`

**Directly closes?** Not until `act` exists.

**Helps?** Strongly.

- `δ : (X ⊗ Y) ⊛ P ≅ (X ⊛ P) ⊗ (Y ⊛ P)` becomes “a `P`-indexed pair is a pair of `P`-indexed values”.
- `δ0 : I ⊛ P ≅ I` becomes the empty product law.
- `υ : X ⊛ I ≅ X` follows from `El [] ≃ Unit`.
- `α : (X ⊛ P) ⊛ Q ≅ X ⊛ (Q ⊗ P)` follows from `El (Q ++ P) ≃ El Q × El P`, plus the chosen action order. Use the named `alphaElEquiv P Q := appendEquiv Q P`; do not use `appendEquiv P Q` for this proof.

**What is still needed:** Constructor-level `BrMorph` isomorphisms and proofs they respect `Rel`. If `act` is implemented via list/shape append, many object equalities reduce to `List.append_nil` and `List.append_assoc`, matching existing `St`/`Br` proof style.

---

### 4.3 `Instances/StBr.lean`: `sh_act`

**Directly closes?** Maybe after object-level `act` is defined.

**Helps?** Yes. It clarifies that shapes compose by append:

```lean
sh_star sh (X ⊛ P) = sh_star sh X ⊗ P
```

For `StObj`, this should reduce to list append if the object action appends `P` to every array shape consistently.

**What is still needed:** A precise object-level definition of `act.obj` and a list-fold lemma for `sh_star` over mapped `BrObj` objects.

---

### 4.4 `Instances/StBr.lean`: `act_unit_assoc`, `υ_nat`, `dist_coh`

**Directly closes?** No.

**Helps?** It shifts them from opaque categorical coherence to pointwise extensional equalities over `El P`.

**What is still needed:** The actual isomorphism definitions for `υ`, `α`, `δ`, `δ0`; then prove functorial/naturality equations. Naperian lemmas should reduce these to:

- unit coordinate tuple uniqueness;
- associativity of coordinate tuple splitting;
- naturality of pointwise `act.map`.

---

### 4.5 `Instances/StBr.lean`: `broadcast_gen`

**Directly closes?** No.

**Helps substantially.** `broadcast_gen` is exactly where Naperian normal forms matter. The desired proof can be decomposed into:

1. every `BrBase` generator has a finite degree `P`;
2. every input/output weave is a reindexing from that degree;
3. lifted base morphisms are pointwise over `El P`;
4. tensor/comp/braid preserve the applicative normal form.

**What is still needed:** An induction/NbE theorem for `BrMorph` over the quotient `Rel`, or a separate broadcastable-normal-form structure with an interpretation into `BrMorph`. `naperian_jointly_monic` can provide uniqueness of the normal form, not existence by itself.

---

### 4.6 `Core/Weave.lean`: `weave_unique`

**Directly closes?** Not immediately.

**Does `naperian_jointly_monic` replace `brCancelPoint`?** It can replace the need for full `Elemental BrObj` **if** `weave_unique` is weakened/rephrased to compare weaves by all Naperian evaluations of their `St` degree. It does not automatically prove the current theorem, because the current theorem assumes `[Elemental C]` and separates by arbitrary `C` points `I_C ⟶ X`.

**Recommended path:** Add a new theorem first:

```lean
theorem weave_unique_naperian ... [NaperianAxis D] ... : Subsingleton ... := by
  -- use naperian_jointly_monic + broadcast_gen
```

Keep the existing `weave_unique` unchanged. If the Naperian theorem covers all consumers, later retire or de-prioritize the `Br` `Elemental` route.

**What is still needed:** A precise proof that evaluating all `El P` coordinates separates the boundary reindexings and lifted base morphism in a weave.

---

### 4.7 `Base/Br.lean`: `brCancelPoint`

**Directly closes?** No.

**Helps?** Indirectly, by possibly making it less important. `brCancelPoint` proves full `Elemental BrObj`. Naperian typing suggests the executable/broadcast fragment should use `St` coordinates instead of manufactured `Br` points.

**What is still needed if keeping current `Elemental BrObj`:** The planned `Br` normal-form/NbE proof remains necessary.

**Strategic choice:** Do not spend Naperian integration effort here first. Prove `weave_unique_naperian` and see whether any important consumer still needs `Elemental BrObj`.

---

### 4.8 `Algebra/Target.lean`: `actV`

**Directly closes?** No.

**Helps?** Conceptually, but not for the current target. The file documents that `TargetActegory StObj (Mat ℝ) ℝ` is impossible with symbolic sizes and multiplicative dimension constraints.

**What is needed:** A concrete finite-size value category, e.g. `DenseTensor` indexed by `El P`, where `actV X P = El P → X` or an equivalent finite tensor shape. Then `lookup/tabulate` become executable definitions.

---

### 4.9 `Grothendieck/Split.lean`: `grothendieck_split` if open

**Directly closes?** Unknown without inspecting the exact statement.

**Likely help:** If the split fibration proof needs chosen cartesian lifts, `ReindexAction` and `BroadcastJoin` provide explicit chosen reindexings and their pointwise semantics. It will still need categorical fibration laws.

---

## 5. Dependency order and milestone sequencing

### Milestone 0: confirm baseline

- Run existing build/test command for the Lean package.
- Record current sorries; do not attempt to close unrelated ones.

Verification: current build status unchanged.

### Milestone 1: generic Naperian API

Create `Core/Naperian.lean` with:

- `NaperianAxis`;
- `ev_naperian`;
- `NaperianFamily`, `lookup`, `tabulate`, `naperian_iso`;
- class skeletons for `BroadcastJoin`, `ReindexAction`, `PointwiseLift`;
- theorem statement `naperian_jointly_monic := by sorry`.

Prerequisite: none beyond existing `Core/Graded.lean`.

Verification: `lake build LeanNCD.Core.Naperian`.

### Milestone 2: St point semantics

Create `Instances/StNaperian.lean` with:

- `AxisPointData`;
- recursive `StNaperian.El`;
- `appendEquiv`, `unitEquiv`;
- `toStPoint`;
- `NaperianAxis StObj` instance.

Prerequisite: Milestone 1.

Verification:

```lean
#check (NaperianAxis.El ([] : StObj))
#check (NaperianAxis.strong_monoidal ([] : StObj) ([] : StObj))
#check (ev_naperian (P := ([] : StObj)) () ([] : BrObj))
```

The last check needs `DGradedColoredPROP StObj BrObj` in scope.

### Milestone 3: easy generic laws

Prove in `Core/Naperian.lean`:

- `PointwiseLift.ev_lift` default instance from `DGradedColoredPROP.act.map` and `ev_p_naturality`;
- basic unit/splitting simp lemmas for `El` in `StNaperian.lean`;
- `lookup_reindex` and concrete `mapEl` laws if needed by downstream proofs.

Prerequisite: Milestones 1-2.

Verification: targeted builds of `Core.Naperian` and `Instances.StNaperian`.

### Milestone 4: object-level `StBr.act`

Define at least the object action for `BrObj × StObjᵒᵖ` and decide the shape convention. Then extend to constructors.

Prerequisite: can proceed parallel to Milestone 3 after the API names stabilize.

Verification: `sh_act` object equation reduces to list append lemmas for simple objects.

### Milestone 5: coherence isomorphisms

Implement `υ`, `α`, `δ`, `δ0` for `StBr` using the object/morphism action. Use `El [] ≃ Unit` and `El (P ++ Q) ≃ El P × El Q` as the conceptual proof guide.

Prerequisite: Milestone 4.

Verification: close or reduce the corresponding `Instances/StBr.lean` sorries.

### Milestone 6: broadcast/applicative normal form

Develop a normal form for broadcastable `Br` morphisms:

```text
boundary reindexing ; pointwise lifted base op ; boundary reindexing
```

Use Naperian evaluations for uniqueness.

Prerequisite: Milestones 3-5.

Verification: close `broadcast_gen` or replace it with a stronger normal-form theorem from which `broadcast_gen` follows.

### Milestone 7: weave uniqueness via Naperian points

Add `weave_unique_naperian` and only then decide whether to refactor existing `weave_unique`.

Prerequisite: Milestone 6 and `naperian_jointly_monic` or a specialized separation theorem.

Verification: prove theorem without depending on `Elemental BrObj`/`brCancelPoint` if possible.

### Minimum viable integration

The smallest change that gives real proof benefit is:

1. `Core/Naperian.lean` with `NaperianAxis`, `ev_naperian`, `PointwiseLift`, and `naperian_jointly_monic` statement;
2. `Instances/StNaperian.lean` with the `StObj` instance;
3. comments/imports in `Instances/StBr.lean` showing future `act`/coherence proofs can use `El`.

This does not close major sorries yet, but it creates stable names and a finite-coordinate proof language for all future work.

---

## 6. Risks and open questions

### 6.1 `Axis.size : Numeric` is symbolic

`Numeric` does not determine a finite `Type`. Therefore `NaperianAxis StObj` needs either:

- an external `[AxisPointData]` environment;
- a concrete-size refinement of `Axis`;
- or a separate executable `AxisP`/`DenseTensor`-side Naperian instance.

Do not pretend `Fintype (Fin size)` exists for symbolic `Numeric`.

### 6.2 Quotient-based `Br`

Naperian semantics interacts with `Br` through `St` reindexings inside `BrBase` and through `act`. Any morphism-level construction over `BrMorph` must respect `Rel`. This is the same class of risk as existing `Br` quotient proofs.

Mitigation: implement Naperian structure over `StObj` first; only then lift it into `Br` via constructor-respecting maps and `Quotient.lift`/`Quotient.lift₂`.

### 6.3 Is `El (tensor P Q) ≃ El P × El Q` provable for `BrObj`?

Probably not the right question. `NaperianAxis` is intended for the index category `D`, especially `StObj`. `BrObj` is the operation PROP object category; its points are manufactured operation inputs and quotient syntax, not finite coordinate tuples. Do not make `NaperianAxis BrObj` a goal unless a separate use case appears.

### 6.4 Does `naperian_jointly_monic` depend on `brCancelPoint`?

It should not depend on `brCancelPoint` if stated as separation by `St`-indexed evaluations of lifted `C` objects. It will depend on a Naperian/applicative normal-form theorem for the relevant `C` fragment. If stated as full `Elemental BrObj`, it collapses back to `brCancelPoint`.

### 6.5 Typeclass coherence and diamonds

Potential diamonds:

- multiple `NaperianAxis StObj` instances with different coordinate semantics;
- global `[AxisPointData]` instances conflicting between symbolic and concrete-size regimes;
- future `BroadcastJoin StObj` instances choosing append vs axis-union.

Mitigation:

- keep `AxisPointData` explicit or local until semantics is canonical;
- avoid globally exporting more than one `NaperianAxis StObj`;
- name noncanonical instances and require them explicitly;
- delay `BroadcastJoin StObj` until axis identity/unification is specified.

### 6.6 Orientation of `act` and tensor order

Current `α` uses:

```lean
act.obj (act.obj (X, P), Q) ≅
  act.obj (X, Opposite.op (ColoredPROP.tensor Q.unop P.unop))
```

For `StObj`, this means nested lifts by `P` then `Q` correspond to `Q ++ P`, not `P ++ Q`. All `appendEquiv` use in proofs must respect this order.

### 6.7 Representability target

The clean formula

```text
F(X ⊛ P) ≅ El(P) → F(X)
```

is easiest in a `Type`/`DenseTensor` semantics. It is an additional representability assumption, encoded by `NaperianFamily.lookup`/`tabulate`, not a consequence of `NaperianAxis` alone. It is not naturally expressible in the current symbolic `FGModuleCat ℝ` placeholder. Keep `NaperianFamily` target-agnostic until a concrete target is available.

---

## Final recommendation

Proceed incrementally. Add the generic Naperian API and the `StObj` point instance first, with `AxisPointData` explicit. Do not refactor `DGradedColoredPROP`, `Elemental`, or `Algebra` yet. Once the names compile, use them to implement the `StBr` action and recast `broadcast_gen`/`weave_unique` as Naperian normal-form theorems over finite `St` coordinates.

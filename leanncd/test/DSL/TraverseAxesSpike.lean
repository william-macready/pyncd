-- test/DSL/TraverseAxesSpike.lean
--
-- E1 prototype: does one `traverseAxes` subsume the hand-written `mapUID`/`specs*`/`*AxisUIDs`
-- families? IdxExpr slice (leaf, no self-recursion): subsumes `IdxExpr.mapUID` (remap),
-- `specsIdx` (collect AxisSpecs), `idxAxisUIDs` (collect UIDs) — see
-- docs/superpowers/specs/2026-07-15-e1-traverseaxes-prototype-design.md.
-- PredArith slice (self-recursion + composition): subsumes `specsPred`/`predAxisUIDs`; the
-- remap direction is blocked by an unrelated production-code limitation (see the theorem's
-- own comment below) — see docs/superpowers/specs/2026-07-15-e1-traverseaxes-predarith-design.md.
-- BoolExpr slice (confirmation, one more delegation layer): subsumes `specsBool`/`boolAxisUIDs`;
-- remap blocked by the same production-code limitation as PredArith's — see
-- docs/superpowers/specs/2026-07-15-e1-traverseaxes-boolexpr-design.md.
-- Factor slice (first node carrying a tensor name): a `String` (untouched) and a `List IdxExpr`
-- traversed via a nested sub-traversal; subsumes `specsFactor`/(the inline Factor-match inside
-- `termAxisUIDs`); remap proved for `.read`/`.unaryFn`, blocked for `.iverson` (inherits
-- BoolExpr's wall) — see docs/superpowers/specs/2026-07-16-e1-traverseaxes-factor-design.md.
-- ProdTerm slice (first non-inductive node; record): subsumes `specsProdTerm'` (collect AxisSpecs)
-- and the real `termAxisUIDs` (collect UIDs); remap lemma is conditional (can't close unconditionally
-- when a factor is `.iverson`, inheriting that slice's limitation) — see
-- docs/superpowers/specs/2026-07-16-e1-traverseaxes-prodterm-design.md.
-- SumExpr slice (structurally identical one layer up; record): subsumes `specsSumExpr'` (collect
-- AxisSpecs) and the bare expression `s.terms.flatMap termAxisUIDs` (collect UIDs, no new named def);
-- the conditional-remap pattern generalizes mechanically (all three theorems pre-verified during
-- design, zero surprises) — see docs/superpowers/specs/2026-07-16-e1-traverseaxes-sumexpr-design.md.
-- Nonlin slice (first `Option` payload, not `List`): exhaustive 9-constructor match, closing
-- production's documented `specsNonlin` wildcard hazard by construction; subsumes local `specsNonlin'`
-- (no UID counterpart — production never touches mask UIDs) — see
-- docs/superpowers/specs/2026-07-16-e1-traverseaxes-rhsexpr-design.md.
-- RHSExpr slice (dual traversals, resolving mask asymmetry): `traverseAxesWithMask` for
-- AxisSpec-collecting-and-remap (conditional on body/nonlin), `traverseAxesNoMask` for
-- UID-collecting-only (mask excluded per `readAxisUIDs`); `specsRHS` includes, `readAxisUIDs`
-- excludes the mask axes — see docs/superpowers/specs/2026-07-16-e1-traverseaxes-rhsexpr-design.md.
import LeanNCD.DSL.Traverse
import LeanNCD.Eval.Contract
import Mathlib.Control.Traversable.Instances

namespace LeanNCD

open LeanNCD.Eval (idxAxisUIDs predAxisUIDs boolAxisUIDs termAxisUIDs readAxisUIDs)

/-- Local copy of `Structural.lean`'s private `specsIdx`, for comparison only — NOT the
    source of truth. Keep byte-identical to `Structural.lean:26-27` by inspection. -/
private def specsIdx' : IdxExpr → List AxisSpec
  | .axis a => [a] | .const _ => [] | .scale _ a => [a]
  | .shift a _ => [a] | .affine _ xs => xs.map (·.2)

/-- Minimal local constant-functor: `ConstL α β` is always `α`, ignoring `β`. Used to
    instantiate `traverseAxes` at a "collecting" applicative — `pure` is the empty list,
    `seq` combines via list append (List's monoid), no Mathlib `Monoid`/`Multiplicative`
    wrapper ceremony needed. -/
structure ConstL (α : Type) (β : Type) where run : α

instance {γ : Type} : Functor (ConstL (List γ)) where
  map _ x := ⟨x.run⟩

instance {γ : Type} : Applicative (ConstL (List γ)) where
  pure _ := ⟨[]⟩
  seq f x := ⟨f.run ++ (x ()).run⟩

/-- The E1 prototype: one traversal over `IdxExpr`'s single `AxisSpec` occurrences,
    generic over any `Applicative f`. Instantiated at `Id` it should behave as a remap
    (subsuming `IdxExpr.mapUID`); at a collecting applicative (`ConstL (List α)`) it
    should behave as a collector (subsuming `specsIdx`/`idxAxisUIDs`). -/
def IdxExpr.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : IdxExpr → f IdxExpr
  | .axis a      => IdxExpr.axis <$> g a
  | .const n     => pure (IdxExpr.const n)
  | .scale c a   => IdxExpr.scale c <$> g a
  | .shift a n   => (fun a' => IdxExpr.shift a' n) <$> g a
  | .affine n xs =>
      IdxExpr.affine n <$> Traversable.traverse (fun (ca : Int × AxisSpec) => Prod.mk ca.1 <$> g ca.2) xs

/-- Remap: instantiating `traverseAxes` at `Id` with `g := AxisSpec.mapUID f` should
    reproduce the existing `IdxExpr.mapUID`. -/
theorem traverseAxes_id_eq_mapUID (f : UData → UData) (e : IdxExpr) :
    IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) e = IdxExpr.mapUID f e := by
  cases e with
  | axis a => rfl
  | const n => rfl
  | scale c a => rfl
  | shift a n => rfl
  | affine n xs =>
      have hEq : (fun (ca : Int × AxisSpec) => Prod.mk ca.1 <$> AxisSpec.mapUID f ca.2 :
            Int × AxisSpec → Id (Int × AxisSpec))
          = pure ∘ (fun ca => (ca.1, AxisSpec.mapUID f ca.2)) := rfl
      simp only [IdxExpr.traverseAxes, IdxExpr.mapUID, Traversable.traverse, hEq,
        List.traverse_eq_map_id]
      rfl

/-- Collect `AxisSpec`s: instantiating at `ConstL (List AxisSpec)` with `g := fun a => ⟨[a]⟩`
    should reproduce `specsIdx'` (the local copy of `Structural.lean`'s private `specsIdx`). -/
theorem traverseAxes_const_eq_specsIdx (e : IdxExpr) :
    (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run = specsIdx' e := by
  cases e with
  | axis a => rfl
  | const n => rfl
  | scale c a => rfl
  | shift a n => rfl
  | affine n xs =>
      have hmap : (fun (ca : Int × AxisSpec) => Prod.mk ca.1 <$> (⟨[ca.2]⟩ : ConstL (List AxisSpec) AxisSpec))
          = (fun ca => (⟨[ca.2]⟩ : ConstL (List AxisSpec) (Int × AxisSpec))) := rfl
      have core : ∀ ys : List (Int × AxisSpec),
          (Traversable.traverse (fun ca => (⟨[ca.2]⟩ : ConstL (List AxisSpec) (Int × AxisSpec))) ys).run
            = ys.map (·.2) := by
        intro ys
        induction ys with
        | nil => rfl
        | cons hd tl ih =>
            show [hd.2] ++
                (Traversable.traverse (fun ca => (⟨[ca.2]⟩ : ConstL (List AxisSpec) (Int × AxisSpec))) tl).run
              = hd.2 :: List.map (·.2) tl
            rw [ih]
            rfl
      show (IdxExpr.affine n <$>
          Traversable.traverse (fun ca => Prod.mk ca.1 <$> (⟨[ca.2]⟩ : ConstL (List AxisSpec) AxisSpec)) xs :
          ConstL (List AxisSpec) IdxExpr).run = xs.map (·.2)
      rw [hmap]
      exact core xs

/-- Collect UIDs: instantiating at `ConstL (List UID)` with `g := fun a => ⟨[a.uid]⟩` should
    reproduce `idxAxisUIDs` (`Eval/Contract.lean`). -/
theorem traverseAxes_const_eq_idxAxisUIDs (e : IdxExpr) :
    (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run = idxAxisUIDs e := by
  cases e with
  | axis a => rfl
  | const n => rfl
  | scale c a => rfl
  | shift a n => rfl
  | affine n xs =>
      have hmap : (fun (ca : Int × AxisSpec) => Prod.mk ca.1 <$> (⟨[ca.2.uid]⟩ : ConstL (List UID) AxisSpec))
          = (fun ca => (⟨[ca.2.uid]⟩ : ConstL (List UID) (Int × AxisSpec))) := rfl
      have core : ∀ ys : List (Int × AxisSpec),
          (Traversable.traverse (fun ca => (⟨[ca.2.uid]⟩ : ConstL (List UID) (Int × AxisSpec))) ys).run
            = ys.map (·.2.uid) := by
        intro ys
        induction ys with
        | nil => rfl
        | cons hd tl ih =>
            show [hd.2.uid] ++
                (Traversable.traverse (fun ca => (⟨[ca.2.uid]⟩ : ConstL (List UID) (Int × AxisSpec))) tl).run
              = hd.2.uid :: List.map (·.2.uid) tl
            rw [ih]
            rfl
      show (IdxExpr.affine n <$>
          Traversable.traverse (fun ca => Prod.mk ca.1 <$> (⟨[ca.2.uid]⟩ : ConstL (List UID) AxisSpec)) xs :
          ConstL (List UID) IdxExpr).run = xs.map (·.2.uid)
      rw [hmap]
      exact core xs

/-- Local copy of `Structural.lean`'s private `specsPred`, for comparison only — NOT the
    source of truth. Keep byte-identical to `Structural.lean:30-31` by inspection. -/
private def specsPred' : PredArith → List AxisSpec
  | .embed e => specsIdx' e | .mul a b => specsPred' a ++ specsPred' b | .iabs a => specsPred' a

/-- Extends the E1 prototype to `PredArith`: genuine self-recursion (`.mul`/`.iabs`) and
    composition with the already-proven `IdxExpr.traverseAxes` (via `.embed`). -/
def PredArith.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : PredArith → f PredArith
  | .embed e => PredArith.embed <$> IdxExpr.traverseAxes g e
  | .mul a b => PredArith.mul <$> PredArith.traverseAxes g a <*> PredArith.traverseAxes g b
  | .iabs a  => PredArith.iabs <$> PredArith.traverseAxes g a

/- Remap: instantiating `traverseAxes` at `Id` with `g := AxisSpec.mapUID f` should
    reproduce the existing `PredArith.mapUID`.

    NOT PROVEN — commented out rather than left with a `sorry`. `PredArith.mapUID` is declared
    `partial def` in `Traverse.lean:22` (it genuinely self-recurses via `.mul`/`.iabs`, unlike
    `IdxExpr.mapUID`, which is also `partial` but never calls itself). Lean generates no
    equation lemmas for a `partial def`, and `unfold`/`delta`/`rfl` all fail to make any
    progress on `PredArith.mapUID f (PredArith.embed e) = PredArith.embed (IdxExpr.mapUID f e)`
    — confirmed even for this non-recursive `.embed` case, so the blocker is not proof search
    difficulty but the outright absence of any unfolding principle for `PredArith.mapUID` in
    the proof layer. Closing this would require changing `PredArith.mapUID`'s definition
    (e.g. dropping `partial` in favor of ordinary structural recursion, which the function's
    shape appears to support) — out of scope for this spike.
theorem traverseAxes_id_eq_predMapUID (f : UData → UData) (e : PredArith) :
    PredArith.traverseAxes (f := Id) (AxisSpec.mapUID f) e = PredArith.mapUID f e := by
  induction e with
  | embed e => exact traverseAxes_id_eq_mapUID f e
  | mul a b iha ihb => simp [PredArith.traverseAxes, PredArith.mapUID, iha, ihb]
  | iabs a iha => simp [PredArith.traverseAxes, PredArith.mapUID, iha]
-/

/-- Collect `AxisSpec`s: instantiating at `ConstL (List AxisSpec)` with `g := fun a => ⟨[a]⟩`
    should reproduce `specsPred'` (the local copy of `Structural.lean`'s private `specsPred`). -/
theorem traverseAxes_const_eq_specsPred (e : PredArith) :
    (PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run = specsPred' e := by
  induction e with
  | embed e => exact traverseAxes_const_eq_specsIdx e
  | mul a b iha ihb =>
      show ((PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run ++
            (PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run
              : List AxisSpec) = specsPred' a ++ specsPred' b
      rw [iha, ihb]
  | iabs a iha =>
      show (PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run = specsPred' a
      exact iha

/-- Collect UIDs: instantiating at `ConstL (List UID)` with `g := fun a => ⟨[a.uid]⟩` should
    reproduce `predAxisUIDs` (`Eval/Contract.lean`). -/
theorem traverseAxes_const_eq_predAxisUIDs (e : PredArith) :
    (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run = predAxisUIDs e := by
  induction e with
  | embed e => exact traverseAxes_const_eq_idxAxisUIDs e
  | mul a b iha ihb =>
      show ((PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run ++
            (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) b).run
              : List UID) = predAxisUIDs a ++ predAxisUIDs b
      rw [iha, ihb]
  | iabs a iha =>
      show (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run = predAxisUIDs a
      exact iha

/-- Local copy of `Structural.lean`'s private `specsBool`, for comparison only — NOT the
    source of truth. Keep byte-identical to `Structural.lean:33-36` by inspection. -/
private def specsBool' : BoolExpr → List AxisSpec
  | .rel _ a b => specsPred' a ++ specsPred' b
  | .and a b => specsBool' a ++ specsBool' b | .or a b => specsBool' a ++ specsBool' b
  | .not a => specsBool' a | .ieq a b => specsPred' a ++ specsPred' b

/-- Extends the E1 prototype to `BoolExpr`: same self-recursive-`<*>`-plus-delegation shape
    as `PredArith.traverseAxes` (confirmation, not a new risk), one layer higher. -/
def BoolExpr.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : BoolExpr → f BoolExpr
  | .rel op a b => BoolExpr.rel op <$> PredArith.traverseAxes g a <*> PredArith.traverseAxes g b
  | .and a b    => BoolExpr.and <$> BoolExpr.traverseAxes g a <*> BoolExpr.traverseAxes g b
  | .or a b     => BoolExpr.or <$> BoolExpr.traverseAxes g a <*> BoolExpr.traverseAxes g b
  | .not a      => BoolExpr.not <$> BoolExpr.traverseAxes g a
  | .ieq a b    => BoolExpr.ieq <$> PredArith.traverseAxes g a <*> PredArith.traverseAxes g b

/-- Collect `AxisSpec`s: instantiating at `ConstL (List AxisSpec)` with `g := fun a => ⟨[a]⟩`
    should reproduce `specsBool'` (the local copy of `Structural.lean`'s private `specsBool`). -/
theorem traverseAxes_const_eq_specsBool (e : BoolExpr) :
    (BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run = specsBool' e := by
  induction e with
  | rel op a b =>
      show ((PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run ++
            (PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run
              : List AxisSpec) = specsPred' a ++ specsPred' b
      rw [traverseAxes_const_eq_specsPred a, traverseAxes_const_eq_specsPred b]
  | and a b iha ihb =>
      show ((BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run ++
            (BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run
              : List AxisSpec) = specsBool' a ++ specsBool' b
      rw [iha, ihb]
  | or a b iha ihb =>
      show ((BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run ++
            (BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run
              : List AxisSpec) = specsBool' a ++ specsBool' b
      rw [iha, ihb]
  | not a iha =>
      show (BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run = specsBool' a
      exact iha
  | ieq a b =>
      show ((PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run ++
            (PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run
              : List AxisSpec) = specsPred' a ++ specsPred' b
      rw [traverseAxes_const_eq_specsPred a, traverseAxes_const_eq_specsPred b]

/-- Collect UIDs: instantiating at `ConstL (List UID)` with `g := fun a => ⟨[a.uid]⟩` should
    reproduce `boolAxisUIDs` (`Eval/Contract.lean`). -/
theorem traverseAxes_const_eq_boolAxisUIDs (e : BoolExpr) :
    (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run = boolAxisUIDs e := by
  induction e with
  | rel op a b =>
      show ((PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run ++
            (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) b).run
              : List UID) = predAxisUIDs a ++ predAxisUIDs b
      rw [traverseAxes_const_eq_predAxisUIDs a, traverseAxes_const_eq_predAxisUIDs b]
  | and a b iha ihb =>
      show ((BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run ++
            (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) b).run
              : List UID) = boolAxisUIDs a ++ boolAxisUIDs b
      rw [iha, ihb]
  | or a b iha ihb =>
      show ((BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run ++
            (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) b).run
              : List UID) = boolAxisUIDs a ++ boolAxisUIDs b
      rw [iha, ihb]
  | not a iha =>
      show (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run = boolAxisUIDs a
      exact iha
  | ieq a b =>
      show ((PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run ++
            (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) b).run
              : List UID) = predAxisUIDs a ++ predAxisUIDs b
      rw [traverseAxes_const_eq_predAxisUIDs a, traverseAxes_const_eq_predAxisUIDs b]

/- Remap: instantiating `traverseAxes` at `Id` with `g := AxisSpec.mapUID f` should reproduce
    the existing `BoolExpr.mapUID`.

    NOT PROVEN — commented out rather than left with a `sorry`, per the same wall the `PredArith`
    slice hit: `BoolExpr.mapUID` is `partial def` in `Traverse.lean` with genuine self-recursion
    (`.and`/`.or`/`.not` call it again), so Lean generates no equation lemmas for the whole
    definition — confirmed here by a standalone `rfl` failing even on the non-recursive `.rel`
    case. Same limitation, same fix if ever needed (drop `partial` from `BoolExpr.mapUID`,
    out of scope for this spike).
theorem traverseAxes_id_eq_boolMapUID (f : UData → UData) (e : BoolExpr) :
    BoolExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) e = BoolExpr.mapUID f e := by
  induction e with
  | rel op a b => simp [BoolExpr.traverseAxes, BoolExpr.mapUID]
  | and a b iha ihb => simp [BoolExpr.traverseAxes, BoolExpr.mapUID, iha, ihb]
  | or a b iha ihb => simp [BoolExpr.traverseAxes, BoolExpr.mapUID, iha, ihb]
  | not a iha => simp [BoolExpr.traverseAxes, BoolExpr.mapUID, iha]
  | ieq a b => simp [BoolExpr.traverseAxes, BoolExpr.mapUID]
-/

/-- Local copy of `Structural.lean`'s private `specsFactor`, for comparison only — NOT the
    source of truth. Keep byte-identical to `Structural.lean:41-43` by inspection. -/
private def specsFactor' : Factor → List AxisSpec
  | .read _ es => es.flatMap specsIdx' | .iverson b => specsBool' b
  | .unaryFn _ _ es => es.flatMap specsIdx'

/-- Local extraction of the inline per-`Factor` match inside `termAxisUIDs`
    (`Eval/Contract.lean:34-38`), for comparison only. NOT a copy of an existing standalone
    function — no `factorAxisUIDs` exists in production; `termAxisUIDs` matches `Factor`
    inline inside a `ProdTerm`-level `flatMap`. Keep this arm-for-arm identical to that inline
    match by inspection. -/
private def factorAxisUIDs' : Factor → List UID
  | .read _ es => es.flatMap idxAxisUIDs | .iverson b => boolAxisUIDs b
  | .unaryFn _ _ es => es.flatMap idxAxisUIDs

/-- Extends the E1 prototype to `Factor`: the first node carrying tensor names (`String`,
    passed through untouched) and a `List IdxExpr` traversed via a nested sub-traversal
    (`Traversable.traverse (IdxExpr.traverseAxes g)`), rather than a bare per-element
    projection. -/
def Factor.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : Factor → f Factor
  | .read nm es       => Factor.read nm <$> Traversable.traverse (IdxExpr.traverseAxes g) es
  | .iverson b        => Factor.iverson <$> BoolExpr.traverseAxes g b
  | .unaryFn op nm es => Factor.unaryFn op nm <$> Traversable.traverse (IdxExpr.traverseAxes g) es

/-- Collect `AxisSpec`s: instantiating at `ConstL (List AxisSpec)` with `g := fun a => ⟨[a]⟩`
    should reproduce `specsFactor'` (the local copy of `Structural.lean`'s private
    `specsFactor`). -/
theorem traverseAxes_const_eq_specsFactor (e : Factor) :
    (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run = specsFactor' e := by
  cases e with
  | read nm es =>
      show (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) es).run
        = es.flatMap specsIdx'
      have core : ∀ ys : List IdxExpr,
          (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ys).run
            = ys.flatMap specsIdx' := by
        intro ys
        induction ys with
        | nil => rfl
        | cons hd tl ih =>
            show (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) hd).run ++
                (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run
              = specsIdx' hd ++ tl.flatMap specsIdx'
            rw [traverseAxes_const_eq_specsIdx hd, ih]
      exact core es
  | iverson b =>
      show (BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run = specsBool' b
      exact traverseAxes_const_eq_specsBool b
  | unaryFn op nm es =>
      show (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) es).run
        = es.flatMap specsIdx'
      have core : ∀ ys : List IdxExpr,
          (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ys).run
            = ys.flatMap specsIdx' := by
        intro ys
        induction ys with
        | nil => rfl
        | cons hd tl ih =>
            show (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) hd).run ++
                (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run
              = specsIdx' hd ++ tl.flatMap specsIdx'
            rw [traverseAxes_const_eq_specsIdx hd, ih]
      exact core es

/-- Collect UIDs: instantiating at `ConstL (List UID)` with `g := fun a => ⟨[a.uid]⟩` should
    reproduce `factorAxisUIDs'` (the local extraction of `termAxisUIDs`'s inline `Factor`
    match). -/
theorem traverseAxes_const_eq_factorAxisUIDs (e : Factor) :
    (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run = factorAxisUIDs' e := by
  cases e with
  | read nm es =>
      show (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) es).run
        = es.flatMap idxAxisUIDs
      have core : ∀ ys : List IdxExpr,
          (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ys).run
            = ys.flatMap idxAxisUIDs := by
        intro ys
        induction ys with
        | nil => rfl
        | cons hd tl ih =>
            show (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) hd).run ++
                (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
              = idxAxisUIDs hd ++ tl.flatMap idxAxisUIDs
            rw [traverseAxes_const_eq_idxAxisUIDs hd, ih]
      exact core es
  | iverson b =>
      show (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) b).run = boolAxisUIDs b
      exact traverseAxes_const_eq_boolAxisUIDs b
  | unaryFn op nm es =>
      show (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) es).run
        = es.flatMap idxAxisUIDs
      have core : ∀ ys : List IdxExpr,
          (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ys).run
            = ys.flatMap idxAxisUIDs := by
        intro ys
        induction ys with
        | nil => rfl
        | cons hd tl ih =>
            show (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) hd).run ++
                (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
              = idxAxisUIDs hd ++ tl.flatMap idxAxisUIDs
            rw [traverseAxes_const_eq_idxAxisUIDs hd, ih]
      exact core es

/-- Remap for `.read`: instantiating `traverseAxes` at `Id` with `g := AxisSpec.mapUID f`
    should reproduce `Factor.mapUID`'s `.read` case. Full attempt — `Factor.mapUID`'s `.read`
    case only calls `IdxExpr.mapUID` (non-`partial`, no self-recursion), so the wall that
    blocked `PredArith`/`BoolExpr`'s remap theorems does not apply here. -/
theorem traverseAxes_id_eq_factorMapUID_read (f : UData → UData) (nm : String) (es : List IdxExpr) :
    Factor.traverseAxes (f := Id) (AxisSpec.mapUID f) (Factor.read nm es)
      = Factor.mapUID f (Factor.read nm es) := by
  show Factor.read nm (Traversable.traverse (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f)) es)
    = Factor.read nm (es.map (IdxExpr.mapUID f))
  have hEq : (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) : IdxExpr → Id IdxExpr)
      = pure ∘ IdxExpr.mapUID f := by
    funext x
    exact traverseAxes_id_eq_mapUID f x
  simp only [Traversable.traverse, hEq, List.traverse_eq_map_id]
  rfl

/-- Remap for `.unaryFn`: same shape as `.read` above, one extra untouched argument (`op`). -/
theorem traverseAxes_id_eq_factorMapUID_unaryFn (f : UData → UData) (op : UnaryOp) (nm : String) (es : List IdxExpr) :
    Factor.traverseAxes (f := Id) (AxisSpec.mapUID f) (Factor.unaryFn op nm es)
      = Factor.mapUID f (Factor.unaryFn op nm es) := by
  show Factor.unaryFn op nm (Traversable.traverse (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f)) es)
    = Factor.unaryFn op nm (es.map (IdxExpr.mapUID f))
  have hEq : (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) : IdxExpr → Id IdxExpr)
      = pure ∘ IdxExpr.mapUID f := by
    funext x
    exact traverseAxes_id_eq_mapUID f x
  simp only [Traversable.traverse, hEq, List.traverse_eq_map_id]
  rfl

/- Remap for `.iverson` — NOT ATTEMPTED, confirmed blocked during design (not implementation):
    `Factor.traverseAxes (f := Id) (AxisSpec.mapUID f) (Factor.iverson b) = Factor.mapUID f
    (Factor.iverson b)` reduces to `BoolExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) b =
    BoolExpr.mapUID f b` for arbitrary `b` — exactly the `BoolExpr` slice's own remap theorem,
    already found blocked there (`partial def`, zero equation lemmas; re-confirmed directly via
    `example (f) (op) (a b) : BoolExpr.mapUID f (BoolExpr.rel op a b) = BoolExpr.rel op
    (PredArith.mapUID f a) (PredArith.mapUID f b) := by rfl` failing). `Factor.mapUID` itself
    being non-`partial` does not help: its `.iverson` case's *top-level* equation unfolds fine
    (`Factor.mapUID f (Factor.iverson b) = Factor.iverson (BoolExpr.mapUID f b)` closes by
    `rfl`), but that just restates the goal in terms of the still-blocked `BoolExpr.mapUID`. Same
    limitation, same fix if ever needed (drop `partial` from `BoolExpr.mapUID`), out of scope
    for this spike. See docs/superpowers/specs/2026-07-16-e1-traverseaxes-factor-design.md. -/

/-- Local copy of the inline `t.factors.flatMap specsFactor` fragment inside `Structural.lean`'s
    private `specsRHS` (`Structural.lean:45-46`), for comparison only — NOT the source of truth.
    No standalone `specsProdTerm` exists in production; keep this arm-for-arm identical to that
    fragment by inspection. -/
private def specsProdTerm' (t : ProdTerm) : List AxisSpec := t.factors.flatMap specsFactor'

/-- Extends the E1 prototype to `ProdTerm`: the first non-inductive (record) node in the
    series. One field, one line of composition — no `cases`/`induction` on `ProdTerm` needed. -/
def ProdTerm.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) (p : ProdTerm) : f ProdTerm :=
  (fun fs => { factors := fs }) <$> Traversable.traverse (Factor.traverseAxes g) p.factors

/-- Collect `AxisSpec`s: instantiating at `ConstL (List AxisSpec)` with `g := fun a => ⟨[a]⟩`
    should reproduce `specsProdTerm'` (the local copy of `specsRHS`'s inline
    `t.factors.flatMap specsFactor` fragment). -/
theorem traverseAxes_const_eq_specsProdTerm (t : ProdTerm) :
    (ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) t).run = specsProdTerm' t := by
  show (Traversable.traverse (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) t.factors).run
    = t.factors.flatMap specsFactor'
  have core : ∀ ys : List Factor,
      (Traversable.traverse (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ys).run
        = ys.flatMap specsFactor' := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) hd).run ++
            (Traversable.traverse (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run
          = specsFactor' hd ++ tl.flatMap specsFactor'
        rw [traverseAxes_const_eq_specsFactor hd, ih]
  exact core t.factors

/-- Bridge: `termAxisUIDs`'s inline per-`Factor` match (`Eval/Contract.lean:34-38`) is exactly
    `factorAxisUIDs'` applied per element — `factorAxisUIDs'` (from the `Factor` slice) was
    built specifically to mirror that inline match. -/
theorem termAxisUIDs_eq_flatMap_factorAxisUIDs' (t : ProdTerm) :
    termAxisUIDs t = t.factors.flatMap factorAxisUIDs' := rfl

/-- Collect UIDs: instantiating at `ConstL (List UID)` with `g := fun a => ⟨[a.uid]⟩` should
    reproduce the REAL production `termAxisUIDs` (`Eval/Contract.lean:34-38`) — no local copy
    needed for this direction. -/
theorem traverseAxes_const_eq_termAxisUIDs (t : ProdTerm) :
    (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) t).run = termAxisUIDs t := by
  rw [termAxisUIDs_eq_flatMap_factorAxisUIDs']
  show (Traversable.traverse (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) t.factors).run
    = t.factors.flatMap factorAxisUIDs'
  have core : ∀ ys : List Factor,
      (Traversable.traverse (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ys).run
        = ys.flatMap factorAxisUIDs' := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) hd).run ++
            (Traversable.traverse (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
          = factorAxisUIDs' hd ++ tl.flatMap factorAxisUIDs'
        rw [traverseAxes_const_eq_factorAxisUIDs hd, ih]
  exact core t.factors

/-- Remap, CONDITIONAL: `ProdTerm.mapUID` only calls `Factor.mapUID` over the list, and
    `Factor`'s own remap is only proved for `.read`/`.unaryFn` (not `.iverson`) — so an
    UNCONDITIONAL theorem over all `p : ProdTerm` cannot close (a single `.iverson` anywhere in
    `p.factors` would need the still-blocked `Factor`/`BoolExpr` remap). This lemma instead
    shows the traversal composes correctly over `List` in the remap direction GIVEN that every
    factor individually satisfies its own remap equality. -/
theorem traverseAxes_id_eq_prodTermMapUID_of_factors (f : UData → UData) (p : ProdTerm)
    (h : ∀ x ∈ p.factors, Factor.traverseAxes (f := Id) (AxisSpec.mapUID f) x = Factor.mapUID f x) :
    ProdTerm.traverseAxes (f := Id) (AxisSpec.mapUID f) p = ProdTerm.mapUID f p := by
  show (fun fs => ({ factors := fs } : ProdTerm)) (Traversable.traverse (Factor.traverseAxes (f := Id) (AxisSpec.mapUID f)) p.factors)
    = { factors := p.factors.map (Factor.mapUID f) }
  have core : ∀ ys : List Factor, (∀ x ∈ ys, Factor.traverseAxes (f := Id) (AxisSpec.mapUID f) x = Factor.mapUID f x) →
      Traversable.traverse (Factor.traverseAxes (f := Id) (AxisSpec.mapUID f)) ys = ys.map (Factor.mapUID f) := by
    intro ys hys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        simp only [List.traverse_cons]
        rw [hys hd List.mem_cons_self, ih (fun x hx => hys x (List.mem_cons_of_mem hd hx))]
        rfl
  rw [core p.factors h]

/-- Local copy delegating to `specsProdTerm'` (the `ProdTerm` slice's own local copy), not
    re-derived through `specsFactor'` directly — mirrors `specsRHS`'s inline
    `r.body.terms.flatMap (fun t => t.factors.flatMap specsFactor)` fragment
    (`Structural.lean:45-46`) one layer at a time. -/
private def specsSumExpr' (s : SumExpr) : List AxisSpec := s.terms.flatMap specsProdTerm'

/-- Extends the E1 prototype to `SumExpr`: structurally identical to `ProdTerm` one layer up —
    a single field, one line of composition, no `cases`/`induction` on `SumExpr` needed. -/
def SumExpr.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) (s : SumExpr) : f SumExpr :=
  (fun ts => { terms := ts }) <$> Traversable.traverse (ProdTerm.traverseAxes g) s.terms

/-- Collect `AxisSpec`s: instantiating at `ConstL (List AxisSpec)` with `g := fun a => ⟨[a]⟩`
    should reproduce `specsSumExpr'`. -/
theorem traverseAxes_const_eq_specsSumExpr (s : SumExpr) :
    (SumExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run = specsSumExpr' s := by
  show (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) s.terms).run
    = s.terms.flatMap specsProdTerm'
  have core : ∀ ys : List ProdTerm,
      (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ys).run
        = ys.flatMap specsProdTerm' := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show (ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) hd).run ++
            (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run
          = specsProdTerm' hd ++ tl.flatMap specsProdTerm'
        rw [traverseAxes_const_eq_specsProdTerm hd, ih]
  exact core s.terms

/-- Collect UIDs: instantiating at `ConstL (List UID)` with `g := fun a => ⟨[a.uid]⟩` should
    reproduce the bare expression `s.terms.flatMap termAxisUIDs` — no new named def; this is
    exactly what `readAxisUIDs` (`Eval/Contract.lean:43-44`) builds from `rhs.body.terms`, just
    at the `SumExpr` level directly rather than via `RHSExpr`. -/
theorem traverseAxes_const_eq_termAxisUIDsSumExpr (s : SumExpr) :
    (SumExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) s).run = s.terms.flatMap termAxisUIDs := by
  show (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) s.terms).run
    = s.terms.flatMap termAxisUIDs
  have core : ∀ ys : List ProdTerm,
      (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ys).run
        = ys.flatMap termAxisUIDs := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) hd).run ++
            (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
          = termAxisUIDs hd ++ tl.flatMap termAxisUIDs
        rw [traverseAxes_const_eq_termAxisUIDs hd, ih]
  exact core s.terms

/-- Remap, CONDITIONAL: same reasoning as `ProdTerm`'s own conditional lemma one layer down —
    `SumExpr.mapUID` only calls `ProdTerm.mapUID` over the list, and since an unconditional
    theorem over all `p : ProdTerm` cannot close (a single `.iverson` factor anywhere blocks
    it), an unconditional `SumExpr`-level theorem cannot close either for the same reason,
    propagated up one more layer. This lemma instead shows the traversal composes correctly
    over `List` in the remap direction GIVEN that every `ProdTerm` in `s.terms` individually
    satisfies its own remap equality. -/
theorem traverseAxes_id_eq_sumExprMapUID_of_terms (f : UData → UData) (s : SumExpr)
    (h : ∀ x ∈ s.terms, ProdTerm.traverseAxes (f := Id) (AxisSpec.mapUID f) x = ProdTerm.mapUID f x) :
    SumExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) s = SumExpr.mapUID f s := by
  show (fun ts => ({ terms := ts } : SumExpr)) (Traversable.traverse (ProdTerm.traverseAxes (f := Id) (AxisSpec.mapUID f)) s.terms)
    = { terms := s.terms.map (ProdTerm.mapUID f) }
  have core : ∀ ys : List ProdTerm, (∀ x ∈ ys, ProdTerm.traverseAxes (f := Id) (AxisSpec.mapUID f) x = ProdTerm.mapUID f x) →
      Traversable.traverse (ProdTerm.traverseAxes (f := Id) (AxisSpec.mapUID f)) ys = ys.map (ProdTerm.mapUID f) := by
    intro ys hys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        simp only [List.traverse_cons]
        rw [hys hd List.mem_cons_self, ih (fun x hx => hys x (List.mem_cons_of_mem hd hx))]
        rfl
  rw [core s.terms h]

-- ===== Nonlin =====

/-- Extends the E1 prototype to `Nonlin`: the first traversal in this series over an `Option`
    payload rather than a `List`. All 9 constructors matched exhaustively — no wildcard — which
    is the whole point: production's `specsNonlin` (`Structural.lean:37-39`) uses a wildcard
    fallback documented as a hazard (it already silently swallowed `l2normalize`'s mask once);
    this traversal cannot make that mistake, since Lean's totality check forces every
    constructor to be handled. -/
def Nonlin.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : Nonlin → f Nonlin
  | .identity      => pure .identity
  | .relu          => pure .relu
  | .sigmoid       => pure .sigmoid
  | .tanh          => pure .tanh
  | .gelu          => pure .gelu
  | .leakyrelu     => pure .leakyrelu
  | .softmax m     => Nonlin.softmax <$> Traversable.traverse (BoolExpr.traverseAxes g) m
  | .normalize m   => Nonlin.normalize <$> Traversable.traverse (BoolExpr.traverseAxes g) m
  | .l2normalize m => Nonlin.l2normalize <$> Traversable.traverse (BoolExpr.traverseAxes g) m

/-- Local copy of `Structural.lean`'s private `specsNonlin`, for comparison only — NOT the
    source of truth. Keep byte-identical to `Structural.lean:37-39` by inspection, wildcard
    included — this copy intentionally mirrors production's CURRENT (hazard-prone) shape; the
    traversal above is what's exhaustive, not this comparison target. -/
private def specsNonlin' : Nonlin → List AxisSpec
  | .softmax (some m) => specsBool' m | .normalize (some m) => specsBool' m
  | .l2normalize (some m) => specsBool' m | _ => []

/-- Collect `AxisSpec`s: instantiating at `ConstL (List AxisSpec)` with `g := fun a => ⟨[a]⟩`
    should reproduce `specsNonlin'`. NO UID-collecting theorem exists for `Nonlin` — no
    production UID-collecting path ever touches the nonlin mask (see `RHSExpr`'s `NoMask`
    traversal in Task 2), so there is nothing to compare a UID-collecting theorem against. -/
theorem traverseAxes_const_eq_specsNonlin (n : Nonlin) :
    (Nonlin.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) n).run = specsNonlin' n := by
  cases n with
  | identity => rfl
  | relu => rfl
  | sigmoid => rfl
  | tanh => rfl
  | gelu => rfl
  | leakyrelu => rfl
  | softmax m =>
      cases m with
      | none => rfl
      | some b =>
          show (BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run = specsBool' b
          exact traverseAxes_const_eq_specsBool b
  | normalize m =>
      cases m with
      | none => rfl
      | some b =>
          show (BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run = specsBool' b
          exact traverseAxes_const_eq_specsBool b
  | l2normalize m =>
      cases m with
      | none => rfl
      | some b =>
          show (BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run = specsBool' b
          exact traverseAxes_const_eq_specsBool b

/-- Remap demonstration, unmasked case: no hypothesis needed at all — closes by plain `rfl`.
    The other 5 unmasked constructors (`relu`/`sigmoid`/`tanh`/`gelu`/`leakyrelu`) are
    structurally identical and not separately proved; they add no new information. -/
example (f : UData → UData) :
    Nonlin.traverseAxes (f := Id) (AxisSpec.mapUID f) Nonlin.identity = Nonlin.mapUID f Nonlin.identity := by
  rfl

/-- Remap demonstration, masked case: CONDITIONAL on the mask's own `BoolExpr` satisfying its
    remap equality (which is blocked in general — `BoolExpr.mapUID` is `partial def` with
    self-recursion — but satisfiable for specific `b`, demonstrated here). This is the
    `Nonlin`-level hypothesis `RHSExpr`'s own conditional remap theorem (Task 2) will require. -/
theorem traverseAxes_id_eq_nonlinMapUID_of_mask (f : UData → UData) (b : BoolExpr)
    (hb : BoolExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) b = BoolExpr.mapUID f b) :
    Nonlin.traverseAxes (f := Id) (AxisSpec.mapUID f) (Nonlin.softmax (some b)) = Nonlin.mapUID f (Nonlin.softmax (some b)) := by
  show Nonlin.softmax (Traversable.traverse (BoolExpr.traverseAxes (f := Id) (AxisSpec.mapUID f)) (some b))
    = Nonlin.softmax (some (BoolExpr.mapUID f b))
  simp only [Traversable.traverse, Option.traverse, Option.mapA_eq_mapM, Option.mapM_some, hb]
  rfl

-- ===== RHSExpr =====

/-- Local copy delegating to `specsSumExpr'` and `specsNonlin'` (both already-existing local
    copies), not re-derived through `specsFactor'`/`specsBool'` directly — mirrors production's
    private `specsRHS` (`Structural.lean:45-46`: `(r.body.terms.flatMap (fun t =>
    t.factors.flatMap specsFactor)) ++ specsNonlin r.nonlin`) one layer at a time. -/
private def specsRHS' (r : RHSExpr) : List AxisSpec := specsSumExpr' r.body ++ specsNonlin' r.nonlin

/-- `RHSExpr`'s AxisSpec-collecting-and-remap traversal: touches BOTH `body` (via
    `SumExpr.traverseAxes`) AND `nonlin` (via `Nonlin.traverseAxes`), `agg` passed through
    unchanged (a 3-constructor enum with no fields, genuinely axis-content-free). Matches
    `specsRHS`'s semantics (mask INCLUDED) and `RHSExpr.mapUID`'s semantics (mapUID always
    updates the mask's UIDs too — there is no production notion of "remap but leave the mask
    stale"). The first traversal in this series combining two independent sub-traversals via
    `<*>` rather than a single `List`. -/
def RHSExpr.traverseAxesWithMask [Applicative f] (g : AxisSpec → f AxisSpec) (r : RHSExpr) : f RHSExpr :=
  (fun body nonlin => { body := body, nonlin := nonlin, agg := r.agg }) <$>
    SumExpr.traverseAxes g r.body <*> Nonlin.traverseAxes g r.nonlin

/-- `RHSExpr`'s UID-collecting-ONLY traversal: touches ONLY `body`; `nonlin`/`agg` pass through
    unchanged. Matches `readAxisUIDs`'s deliberate exclusion of the mask (per-term contraction
    scoping must not see mask axes). NOT used for remap — remap always goes through
    `traverseAxesWithMask`, since there is no "skip the mask" remap semantics anywhere in
    production. -/
def RHSExpr.traverseAxesNoMask [Applicative f] (g : AxisSpec → f AxisSpec) (r : RHSExpr) : f RHSExpr :=
  (fun body => { body := body, nonlin := r.nonlin, agg := r.agg }) <$> SumExpr.traverseAxes g r.body

/-- Collect `AxisSpec`s (mask included): instantiating `traverseAxesWithMask` at
    `ConstL (List AxisSpec)` with `g := fun a => ⟨[a]⟩` should reproduce `specsRHS'`. -/
theorem traverseAxes_const_eq_specsRHS (r : RHSExpr) :
    (RHSExpr.traverseAxesWithMask (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r).run = specsRHS' r := by
  show (SumExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r.body).run ++
      (Nonlin.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r.nonlin).run
    = specsSumExpr' r.body ++ specsNonlin' r.nonlin
  rw [traverseAxes_const_eq_specsSumExpr r.body, traverseAxes_const_eq_specsNonlin r.nonlin]

/-- Collect UIDs (mask EXCLUDED): instantiating `traverseAxesNoMask` at `ConstL (List UID)`
    with `g := fun a => ⟨[a.uid]⟩` should reproduce the REAL production `readAxisUIDs`
    directly — no local copy needed, since `traverseAxesNoMask` never touches `nonlin`, this
    reduces immediately to `SumExpr`'s own already-proven UID-collecting theorem. -/
theorem traverseAxes_const_eq_readAxisUIDs (r : RHSExpr) :
    (RHSExpr.traverseAxesNoMask (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) r).run = readAxisUIDs r := by
  show (SumExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) r.body).run
    = r.body.terms.flatMap termAxisUIDs
  exact traverseAxes_const_eq_termAxisUIDsSumExpr r.body

/-- Remap, CONDITIONAL on TWO independent hypotheses: `r.body`'s own remap equality
    (the `SumExpr`-level conditional, itself gated on every `ProdTerm`/`Factor` inside it) and
    `r.nonlin`'s own remap equality (gated on `.iverson`/mask blocking, per
    `traverseAxes_id_eq_nonlinMapUID_of_mask`). Neither hypothesis is transitively re-derived
    here — each is taken flat, about the specific `r.body`/`r.nonlin` values, mirroring exactly
    how `ProdTerm`'s and `SumExpr`'s own conditional lemmas took a hypothesis about their
    immediate sub-structure rather than expanding it further. Given both, the `RHSExpr`-level
    equality follows directly — no induction needed, since there's no list at this level. -/
theorem traverseAxes_id_eq_rhsExprMapUID (f : UData → UData) (r : RHSExpr)
    (hbody : SumExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) r.body = SumExpr.mapUID f r.body)
    (hnonlin : Nonlin.traverseAxes (f := Id) (AxisSpec.mapUID f) r.nonlin = Nonlin.mapUID f r.nonlin) :
    RHSExpr.traverseAxesWithMask (f := Id) (AxisSpec.mapUID f) r = RHSExpr.mapUID f r := by
  show (fun body nonlin => ({ body := body, nonlin := nonlin, agg := r.agg } : RHSExpr))
      (SumExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) r.body) (Nonlin.traverseAxes (f := Id) (AxisSpec.mapUID f) r.nonlin)
    = { body := SumExpr.mapUID f r.body, nonlin := Nonlin.mapUID f r.nonlin, agg := r.agg }
  rw [hbody, hnonlin]

-- ===== LHSSlot =====

/-- Local copy of `Structural.lean`'s private `specsLHS`, for comparison only — NOT the
    source of truth. Keep byte-identical to `Structural.lean:52-53` by inspection. Unlike
    `Nonlin`'s `specsNonlin`, this is already a clean, exhaustive match with no documented
    wildcard hazard. -/
private def specsLHS' : LHSSlot → List AxisSpec
  | .free a => [a] | .freeNorm a => [a]
  | .iterAt a _ => [a] | .iterNext a => [a] | .affine e => specsIdx' e

/-- Extends the E1 prototype to `LHSSlot`: the simplest traversal shape in the series — 4 of 5
    arms apply `g` directly to a bare `AxisSpec` (no sub-traversal at all), the 5th (`.affine`)
    delegates entirely to the already-proven `IdxExpr.traverseAxes`.

    Deliberately OUT OF SCOPE: `lhsAxisUID?`/`freeAxisUIDs` (`Eval/Shape.lean:501-506`,
    `Eval/Contract.lean:29`) cannot be reproduced by any instantiation of this traversal — they
    are a classify-and-filter function (`.affine` maps to `none`, dropped entirely from the
    free-axis list), not a collector (which is what every instantiation of `traverseAxes`
    produces — for `.affine`, that means recursing into its `IdxExpr` and collecting those
    axes, which is NOT what `lhsAxisUID?` does). This is a different function shape, not a
    missing production counterpart. -/
def LHSSlot.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : LHSSlot → f LHSSlot
  | .free a     => LHSSlot.free <$> g a
  | .freeNorm a => LHSSlot.freeNorm <$> g a
  | .iterAt a n => (fun a' => LHSSlot.iterAt a' n) <$> g a
  | .iterNext a => LHSSlot.iterNext <$> g a
  | .affine e   => LHSSlot.affine <$> IdxExpr.traverseAxes g e

/-- Collect `AxisSpec`s: instantiating at `ConstL (List AxisSpec)` with `g := fun a => ⟨[a]⟩`
    should reproduce `specsLHS'`. -/
theorem traverseAxes_const_eq_specsLHS (s : LHSSlot) :
    (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run = specsLHS' s := by
  cases s with
  | free a => rfl
  | freeNorm a => rfl
  | iterAt a n => rfl
  | iterNext a => rfl
  | affine e =>
      show (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run = specsIdx' e
      exact traverseAxes_const_eq_specsIdx e

/-- Remap: instantiating `traverseAxes` at `Id` with `g := AxisSpec.mapUID f` should reproduce
    `LHSSlot.mapUID`. FULLY UNCONDITIONAL — the first time since `IdxExpr` itself — because
    `LHSSlot.mapUID` is flat/non-partial and its only non-trivial dependency,
    `IdxExpr.mapUID`, is already fully and unconditionally proven (`traverseAxes_id_eq_mapUID`,
    from the `IdxExpr` slice, which never touches `BoolExpr` and so never hits the `partial
    def`/zero-equation-lemmas wall every slice from `PredArith` onward has needed a hypothesis
    or block to work around). -/
theorem traverseAxes_id_eq_lhsSlotMapUID (f : UData → UData) (s : LHSSlot) :
    LHSSlot.traverseAxes (f := Id) (AxisSpec.mapUID f) s = LHSSlot.mapUID f s := by
  cases s with
  | free a => rfl
  | freeNorm a => rfl
  | iterAt a n => rfl
  | iterNext a => rfl
  | affine e =>
      show LHSSlot.affine (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) e) = LHSSlot.affine (IdxExpr.mapUID f e)
      rw [traverseAxes_id_eq_mapUID f e]

end LeanNCD

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
import LeanNCD.DSL.Traverse
import LeanNCD.Eval.Contract
import Mathlib.Control.Traversable.Instances

namespace LeanNCD

open LeanNCD.Eval (idxAxisUIDs predAxisUIDs boolAxisUIDs)

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

end LeanNCD

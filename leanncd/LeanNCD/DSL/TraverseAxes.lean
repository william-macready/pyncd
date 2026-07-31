-- LeanNCD/DSL/TraverseAxes.lean
--
-- One generic `traverseAxes` per AST node (van Laarhoven-style, generic over `Applicative`),
-- promoted verbatim from the E1 prototype (`test/DSL/TraverseAxesSpike.lean`, all eleven
-- slices, zero sorry/native_decide). Instantiated at `Id` it behaves as a remap (subsuming
-- `mapUID`); at a collecting applicative (`ConstL (List α)`) it behaves as a collector
-- (subsuming `specs*`/`*AxisUIDs`). See
-- docs/superpowers/specs/2026-07-17-e1-production-migration-specs-design.md.
import LeanNCD.DSL.Ast
import Mathlib.Control.Traversable.Instances

namespace LeanNCD

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

-- ── Reading the family: what `f` and `g` are ──────────────────────────────────────────────────
-- Every node's traversal has the shape `X.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : X → f X`.
-- The whole layer is two choices: the applicative `f` (the "mode" / effect) and the leaf action `g`
-- (what happens at each axis). The three production paths:
--
--   • Remap (rebuild the AST with uids substituted) — subsumes `X.mapUID`:
--       f := Id                        g := AxisSpec.mapUID φ   (φ : UData → UData)
--       result : X          — the same AST with every axis's uid remapped by φ.
--
--   • Collect AxisSpecs (gather every axis occurrence) — subsumes `specsX`:
--       f := ConstL (List AxisSpec)    g := fun a => ⟨[a]⟩
--       result : (…).run : List AxisSpec   — all axes, in traversal order.
--
--   • Collect UIDs (gather every axis's uid) — subsumes `*AxisUIDs`:
--       f := ConstL (List UID)         g := fun a => ⟨[a.uid]⟩
--       result : (…).run : List UID        — all axis uids, in traversal order.
--
-- `Id` returns the rebuilt value directly; `ConstL (List _)` ignores its second type parameter and
-- accumulates via the list monoid (`pure = []`, `seq = ++`), so the collected list is read off `.run`.
-- (The name projection `axisNames` rides on the AxisSpec collector rather than defining a fourth
-- `ConstL (List String)` / `g := fun a => ⟨[a.name]⟩` path — see the note at `TLProgram.axisNames`.)

def IdxExpr.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : IdxExpr → f IdxExpr
  | .axis a      => IdxExpr.axis <$> g a
  | .const n     => pure (IdxExpr.const n)
  | .scale c a   => IdxExpr.scale c <$> g a
  | .shift a n   => (fun a' => IdxExpr.shift a' n) <$> g a
  | .affine n xs =>
      IdxExpr.affine n <$> Traversable.traverse (fun (ca : Int × AxisSpec) => Prod.mk ca.1 <$> g ca.2) xs

def PredArith.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : PredArith → f PredArith
  | .embed e => PredArith.embed <$> IdxExpr.traverseAxes g e
  | .mul a b => PredArith.mul <$> PredArith.traverseAxes g a <*> PredArith.traverseAxes g b
  | .iabs a  => PredArith.iabs <$> PredArith.traverseAxes g a

def BoolExpr.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : BoolExpr → f BoolExpr
  | .rel op a b => BoolExpr.rel op <$> PredArith.traverseAxes g a <*> PredArith.traverseAxes g b
  | .and a b    => BoolExpr.and <$> BoolExpr.traverseAxes g a <*> BoolExpr.traverseAxes g b
  | .or a b     => BoolExpr.or <$> BoolExpr.traverseAxes g a <*> BoolExpr.traverseAxes g b
  | .not a      => BoolExpr.not <$> BoolExpr.traverseAxes g a
  | .ieq a b    => BoolExpr.ieq <$> PredArith.traverseAxes g a <*> PredArith.traverseAxes g b

def Factor.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : Factor → f Factor
  | .read nm es       => Factor.read nm <$> Traversable.traverse (IdxExpr.traverseAxes g) es
  | .iverson b        => Factor.iverson <$> BoolExpr.traverseAxes g b
  | .unaryFn op nm es => Factor.unaryFn op nm <$> Traversable.traverse (IdxExpr.traverseAxes g) es

def ProdTerm.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) (p : ProdTerm) : f ProdTerm :=
  (fun fs => { factors := fs }) <$> Traversable.traverse (Factor.traverseAxes g) p.factors

def SumExpr.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) (s : SumExpr) : f SumExpr :=
  (fun ts => { terms := ts }) <$> Traversable.traverse (ProdTerm.traverseAxes g) s.terms

def Nonlin.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : Nonlin → f Nonlin
  | .identity       => pure .identity
  | .pointwise pf   => pure (.pointwise pf)
  | .axiswise fn m  => Nonlin.axiswise fn <$> Traversable.traverse (BoolExpr.traverseAxes g) m

/-- `RHSExpr`'s AxisSpec-collecting-and-remap traversal: touches BOTH `body` (via
    `SumExpr.traverseAxes`) AND `nonlin` (via `Nonlin.traverseAxes`), `agg` passed through
    unchanged. Matches `specsRHS`'s semantics (mask INCLUDED) and `RHSExpr.mapUID`'s semantics
    (mapUID always updates the mask's UIDs too). -/
def RHSExpr.traverseAxesWithMask [Applicative f] (g : AxisSpec → f AxisSpec) (r : RHSExpr) : f RHSExpr :=
  (fun body nonlin => { body := body, nonlin := nonlin, agg := r.agg }) <$>
    SumExpr.traverseAxes g r.body <*> Nonlin.traverseAxes g r.nonlin

/-- `RHSExpr`'s UID-collecting-ONLY traversal: touches ONLY `body`; `nonlin`/`agg` pass through
    unchanged. Matches `readAxisUIDs`'s deliberate exclusion of the mask. -/
def RHSExpr.traverseAxesNoMask [Applicative f] (g : AxisSpec → f AxisSpec) (r : RHSExpr) : f RHSExpr :=
  (fun body => { body := body, nonlin := r.nonlin, agg := r.agg }) <$> SumExpr.traverseAxes g r.body

def LHSSlot.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : LHSSlot → f LHSSlot
  | .free a     => LHSSlot.free <$> g a
  | .freeNorm a => LHSSlot.freeNorm <$> g a
  | .iterAt a n => (fun a' => LHSSlot.iterAt a' n) <$> g a
  | .iterNext a => LHSSlot.iterNext <$> g a
  | .affine e   => LHSSlot.affine <$> IdxExpr.traverseAxes g e

def Stmt.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : Stmt → f Stmt
  | .assign nm ls r         => (fun ls' r' => Stmt.assign nm ls' r') <$>
      Traversable.traverse (LHSSlot.traverseAxes g) ls <*> RHSExpr.traverseAxesWithMask g r
  | .scatter nm ls r o      => (fun ls' r' => Stmt.scatter nm ls' r' o) <$>
      Traversable.traverse (LHSSlot.traverseAxes g) ls <*> RHSExpr.traverseAxesWithMask g r
  | .recurMorphism nm ax tc => (fun ax' => Stmt.recurMorphism nm ax' tc) <$> g ax

def Decl.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : Decl → f Decl
  | .tensor nm ax     => Decl.tensor nm <$> Traversable.traverse g ax
  | .predicate nm ax  => Decl.predicate nm <$> Traversable.traverse g ax
  | .linear nm ax b   => (fun ax' => Decl.linear nm ax' b) <$> Traversable.traverse g ax
  | .axis ax n        => (fun ax' => Decl.axis ax' n) <$> g ax
  | .iter ax n        => (fun ax' => Decl.iter ax' n) <$> g ax

def TLProgram.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) (p : TLProgram) : f TLProgram :=
  (fun decls stmts => ({ decls := decls, stmts := stmts } : TLProgram)) <$>
    Traversable.traverse (Decl.traverseAxes g) p.decls <*> Traversable.traverse (Stmt.traverseAxes g) p.stmts

end LeanNCD

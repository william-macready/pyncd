-- LeanNCD/DSL/Pipeline/Structural.lean
import LeanNCD.DSL.Pipeline.Types
import LeanNCD.DSL.Traverse
import LeanNCD.DSL.TraverseAxes
import LeanNCD.Exec.Uid
import Std.Data.HashMap
-- E1 traverseAxes migration (2026-07-16..17 — see
-- docs/superpowers/specs/2026-07-16-e1-traverseaxes-stmt-design.md): this is the ONLY
-- cross-layer import on this branch — DSL/Pipeline and Eval are otherwise deliberately
-- parallel, non-crossing layers (see LeanNCD.lean's own architecture note). It exists so
-- `Stmt.uids_eq` and the `specsX_map_uid_eq` lemmas below can state their RHSs using the real,
-- public `idxAxisUIDs`/`predAxisUIDs`/`boolAxisUIDs`/`termAxisUIDs` rather than duplicating their
-- logic by hand. TO REVERT: delete this import together with `Stmt.uids_eq` and the
-- `specsX_map_uid_eq` lemmas (search the E1 note above `Stmt.uids_eq` in this file).
import LeanNCD.Eval.Contract

namespace LeanNCD
open Std
-- (See the `LeanNCD.Eval.Contract` import above): needed by `Stmt.uids_eq` and the
-- `specsX_map_uid_eq` lemmas below.
open LeanNCD.Eval (idxAxisUIDs predAxisUIDs boolAxisUIDs termAxisUIDs)

/-! ## Axis collectors

Axis identity in tensor logic is name-based within program scope (§12.1): a name appearing
in multiple places denotes the same axis. The `specs*` family gathers every source `AxisSpec`
in program order via structural recursion. Most of these (`specsIdx`, `specsPred`, `specsBool`,
`specsFactor`, `specsLHS`, `specsNonlin`) are exhaustive matches, so Lean's totality check forces
every new constructor to be handled — nothing is silently dropped. The two public collectors below
are thin projections of one traversal: by name (`TLProgram.axisNames`, de-duplicated) or by uid
(`Stmt.uids`). -/

/-- Every `AxisSpec` occurring in an index expression (a bare axis, or the coordinate list of an
    affine combination). The `ConstL (List AxisSpec)` instantiation of `IdxExpr.traverseAxes`. -/
private def specsIdx (e : IdxExpr) : List AxisSpec :=
  (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run

/-- Every `AxisSpec` occurring in a predicate-arithmetic expression, gathered from its embedded
    index expressions. The `ConstL (List AxisSpec)` instantiation of `PredArith.traverseAxes`. -/
private def specsPred (e : PredArith) : List AxisSpec :=
  (PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run

/-- Every `AxisSpec` occurring in a boolean expression, gathered from its embedded predicate
    arithmetic. The `ConstL (List AxisSpec)` instantiation of `BoolExpr.traverseAxes`. -/
private def specsBool (e : BoolExpr) : List AxisSpec :=
  (BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run

/-- Every `AxisSpec` occurring in a nonlinearity's optional mask (`softmax`/`normalize`/
    `l2normalize`); `[]` for mask-free variants. The `ConstL (List AxisSpec)` instantiation of
    `Nonlin.traverseAxes`. -/
private def specsNonlin (n : Nonlin) : List AxisSpec :=
  (Nonlin.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) n).run

/-- Every `AxisSpec` occurring in a product factor (`read`'s index list, `iverson`'s boolean
    guard, or `unaryFn`'s index list). The `ConstL (List AxisSpec)` instantiation of
    `Factor.traverseAxes`. -/
private def specsFactor (x : Factor) : List AxisSpec :=
  (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) x).run

/-- Every `AxisSpec` occurring on the RHS of a statement: every factor of every term, PLUS the
    `nonlin` mask — mask INCLUDED, the mirror of `readAxisUIDs`'s mask-excluded `NoMask` traversal
    on the UID side. The `ConstL (List AxisSpec)` instantiation of `RHSExpr.traverseAxesWithMask`. -/
private def specsRHS (r : RHSExpr) : List AxisSpec :=
  (RHSExpr.traverseAxesWithMask (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r).run

/-- Every `AxisSpec` occurring in a single LHS slot: the bare axis for `free`/`freeNorm`/
    `iterAt`/`iterNext`, or the index expression's specs for `affine`. The `ConstL (List AxisSpec)`
    instantiation of `LHSSlot.traverseAxes`. -/
private def specsLHS (s : LHSSlot) : List AxisSpec :=
  (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run

/-- Every `AxisSpec` occurring in a declaration. The `ConstL (List AxisSpec)` instantiation of
    `Decl.traverseAxes`. -/
private def specsDecl (d : Decl) : List AxisSpec :=
  (Decl.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) d).run

/-- Every `AxisSpec` occurring in a statement: its LHS slots and RHS (`assign`/`scatter`), or its
    recur axis (`recurMorphism`). The `ConstL (List AxisSpec)` instantiation of
    `Stmt.traverseAxes`. -/
private def specsStmt (s : Stmt) : List AxisSpec :=
  (Stmt.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run

/-! ## `Const`-applicative monoid-hom fusion (map-`·.uid` naturality)

The lemmas below are pure facts relating the TWO `ConstL` instantiations of each node's
`traverseAxes`: mapping `(·.uid)` over the AxisSpec-collecting run (leaf action `fun a => ⟨[a]⟩`)
equals the UID-collecting run (leaf action `fun a => ⟨[a.uid]⟩`). They hold because
`List.map (·.uid)` is a monoid homomorphism on `(List, ++, [])` and `(fun a => ⟨[a]⟩)`
post-composed with `List.map (·.uid)` is `(fun a => ⟨[a.uid]⟩)`, so the `Const` applicative's
`++`-accumulation commutes with the hom — i.e. this is the `Const`-applicative naturality of that
monoid hom, applied per node.

They reference ONLY the two runs and `List.map` — no `specsX`/`*AxisUIDs` collector — so they
stand on their own: the bridge that sub-project 1's `specs*` (AxisSpec) side and sub-project 2's
`*AxisUIDs` (UID) side never had. With them, the UID proofs (`specsX_map_uid_eq`, `Stmt.uids_eq`)
are derived directly from the traversal, with no dependence on any hand-written structural shape.

Leaf-to-root; each recursive lemma reuses the earlier ones (the hom naturality composes
structurally, exactly as the spike's `traverseAxes_const_eq_*` pairs do per node). -/

/-- `IdxExpr` (leaf): bare-axis arms (`.axis`/`.scale`/`.shift`) are `[a].map (·.uid) = [a.uid]`
    and `.const` is `[]` — all `rfl`; `.affine` folds the coordinate list, pushing the map through
    each `Prod.mk`-repaired const action (`hmapAS`/`hmapUS` collapse the `Prod.mk` wrapping). -/
private theorem idxAxisUidFusion (e : IdxExpr) :
    ((IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run).map (·.uid)
      = (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run := by
  cases e with
  | axis a => rfl
  | const n => rfl
  | scale c a => rfl
  | shift a n => rfl
  | affine n xs =>
      -- Both runs re-pair each coordinate's `Int` half via `Prod.mk`; `ConstL` ignores its second
      -- type parameter, so `hmapAS`/`hmapUS` collapse both to the plain per-element const action
      -- the combined `core` folds over.
      have hmapAS : (fun (ca : Int × AxisSpec) => Prod.mk ca.1 <$> (⟨[ca.2]⟩ : ConstL (List AxisSpec) AxisSpec))
          = (fun ca => (⟨[ca.2]⟩ : ConstL (List AxisSpec) (Int × AxisSpec))) := rfl
      have hmapUS : (fun (ca : Int × AxisSpec) => Prod.mk ca.1 <$> (⟨[ca.2.uid]⟩ : ConstL (List UID) AxisSpec))
          = (fun ca => (⟨[ca.2.uid]⟩ : ConstL (List UID) (Int × AxisSpec))) := rfl
      have core : ∀ ys : List (Int × AxisSpec),
          ((Traversable.traverse (fun ca => (⟨[ca.2]⟩ : ConstL (List AxisSpec) (Int × AxisSpec))) ys).run).map (·.uid)
            = (Traversable.traverse (fun ca => (⟨[ca.2.uid]⟩ : ConstL (List UID) (Int × AxisSpec))) ys).run := by
        intro ys
        induction ys with
        | nil => rfl
        | cons hd tl ih =>
            show ([hd.2] ++ (Traversable.traverse (fun ca => (⟨[ca.2]⟩ : ConstL (List AxisSpec) (Int × AxisSpec))) tl).run).map (·.uid)
              = [hd.2.uid] ++ (Traversable.traverse (fun ca => (⟨[ca.2.uid]⟩ : ConstL (List UID) (Int × AxisSpec))) tl).run
            simp only [List.map_append, List.map_cons, List.map_nil, ih]
      show ((IdxExpr.affine n <$>
          Traversable.traverse (fun ca => Prod.mk ca.1 <$> (⟨[ca.2]⟩ : ConstL (List AxisSpec) AxisSpec)) xs :
          ConstL (List AxisSpec) IdxExpr).run).map (·.uid)
        = (IdxExpr.affine n <$>
          Traversable.traverse (fun ca => Prod.mk ca.1 <$> (⟨[ca.2.uid]⟩ : ConstL (List UID) AxisSpec)) xs :
          ConstL (List UID) IdxExpr).run
      rw [hmapAS, hmapUS]
      exact core xs

/-- `PredArith`: `.embed` delegates to `idxAxisUidFusion`; `.mul` pushes the map through the
    `++` of the two child runs (`List.map_append` + the IHs); `.iabs` is the single-child run. -/
private theorem predAxisUidFusion (e : PredArith) :
    ((PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run).map (·.uid)
      = (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run := by
  induction e with
  | embed e => exact idxAxisUidFusion e   -- cross-node delegation: embed's run IS the IdxExpr run
  | mul a b iha ihb =>
      show ((PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run ++
            (PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run).map (·.uid)
        = (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run ++
            (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) b).run
      rw [List.map_append, iha, ihb]
  | iabs a iha =>
      show ((PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run).map (·.uid)
        = (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run
      exact iha

/-- `BoolExpr`: `.rel`/`.ieq` delegate to `predAxisUidFusion` over the `++` of the two child runs;
    `.and`/`.or` use the IHs over the `++`; `.not` is the single-child run. -/
private theorem boolAxisUidFusion (e : BoolExpr) :
    ((BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run).map (·.uid)
      = (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run := by
  induction e with
  | rel op a b =>
      show ((PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run ++
            (PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run).map (·.uid)
        = (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run ++
            (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) b).run
      rw [List.map_append, predAxisUidFusion a, predAxisUidFusion b]
  | and a b iha ihb =>
      show ((BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run ++
            (BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run).map (·.uid)
        = (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run ++
            (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) b).run
      rw [List.map_append, iha, ihb]
  | or a b iha ihb =>
      show ((BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run ++
            (BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run).map (·.uid)
        = (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run ++
            (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) b).run
      rw [List.map_append, iha, ihb]
  | not a iha =>
      show ((BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run).map (·.uid)
        = (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run
      exact iha
  | ieq a b =>
      show ((PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) a).run ++
            (PredArith.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run).map (·.uid)
        = (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) a).run ++
            (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) b).run
      rw [List.map_append, predAxisUidFusion a, predAxisUidFusion b]

/-- `Factor`: `.read`/`.unaryFn` fold `IdxExpr.traverseAxes` over the index list (the `core`
    list-fold, using `idxAxisUidFusion` per element); `.iverson` cross-node-delegates to
    `boolAxisUidFusion`. -/
private theorem factorAxisUidFusion (x : Factor) :
    ((Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) x).run).map (·.uid)
      = (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) x).run := by
  have core : ∀ ys : List IdxExpr,
      ((Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ys).run).map (·.uid)
        = (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ys).run := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show ((IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) hd).run ++
            (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run).map (·.uid)
          = (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) hd).run ++
            (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
        rw [List.map_append, idxAxisUidFusion hd, ih]
  cases x with
  | read nm es =>
      show ((Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) es).run).map (·.uid)
        = (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) es).run
      exact core es
  | iverson b =>
      show ((BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run).map (·.uid)
        = (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) b).run
      exact boolAxisUidFusion b
  | unaryFn op nm es =>
      show ((Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) es).run).map (·.uid)
        = (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) es).run
      exact core es

/-- `ProdTerm`: folds `Factor.traverseAxes` over `t.factors` (the `core` list-fold, using
    `factorAxisUidFusion` per element). -/
private theorem prodTermAxisUidFusion (t : ProdTerm) :
    ((ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) t).run).map (·.uid)
      = (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) t).run := by
  show ((Traversable.traverse (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) t.factors).run).map (·.uid)
    = (Traversable.traverse (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) t.factors).run
  have core : ∀ ys : List Factor,
      ((Traversable.traverse (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ys).run).map (·.uid)
        = (Traversable.traverse (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ys).run := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show ((Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) hd).run ++
            (Traversable.traverse (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run).map (·.uid)
          = (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) hd).run ++
            (Traversable.traverse (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
        rw [List.map_append, factorAxisUidFusion hd, ih]
  exact core t.factors

/-- `SumExpr`: folds `ProdTerm.traverseAxes` over `s.terms` (the `core` list-fold, using
    `prodTermAxisUidFusion` per element). -/
private theorem sumExprAxisUidFusion (s : SumExpr) :
    ((SumExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run).map (·.uid)
      = (SumExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) s).run := by
  show ((Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) s.terms).run).map (·.uid)
    = (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) s.terms).run
  have core : ∀ ys : List ProdTerm,
      ((Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ys).run).map (·.uid)
        = (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ys).run := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show ((ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) hd).run ++
            (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run).map (·.uid)
          = (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) hd).run ++
            (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
        rw [List.map_append, prodTermAxisUidFusion hd, ih]
  exact core s.terms

/-- `Nonlin`: `.identity`/`.pointwise` collect `[]` (`rfl`); `.axiswise` with a `some b` mask
    cross-node-delegates to `boolAxisUidFusion`, `none` is `[]`. -/
private theorem nonlinAxisUidFusion (n : Nonlin) :
    ((Nonlin.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) n).run).map (·.uid)
      = (Nonlin.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) n).run := by
  cases n with
  | identity => rfl
  | pointwise pf => rfl
  | axiswise fn m =>
      cases m with
      | none => rfl
      | some b =>
          show ((BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run).map (·.uid)
            = (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) b).run
          exact boolAxisUidFusion b

/-- `LHSSlot`: bare-axis arms (`.free`/`.freeNorm`/`.iterAt`/`.iterNext`) are
    `[a].map (·.uid) = [a.uid]` (`rfl`); `.affine` cross-node-delegates to `idxAxisUidFusion`. -/
private theorem lhsAxisUidFusion (s : LHSSlot) :
    ((LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run).map (·.uid)
      = (LHSSlot.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) s).run := by
  cases s with
  | free a => rfl
  | freeNorm a => rfl
  | iterAt a n => rfl
  | iterNext a => rfl
  | affine e =>
      show ((IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run).map (·.uid)
        = (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run
      exact idxAxisUidFusion e

/-- `Stmt` (root of the statement layer): `.assign`/`.scatter` split into the LHS-slot list-fold
    (`coreLHS`, using `lhsAxisUidFusion`) and the RHS (`hRHS`, whose `traverseAxesWithMask` run is
    `SumExpr`'s body run `++` the `Nonlin` mask run — mask INCLUDED on both sides, so no `NoMask`
    asymmetry here); `.recurMorphism` is `[ax].map (·.uid) = [ax.uid]` (`rfl`). -/
private theorem stmtAxisUidFusion (s : Stmt) :
    ((Stmt.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run).map (·.uid)
      = (Stmt.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) s).run := by
  have coreLHS : ∀ ys : List LHSSlot,
      ((Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ys).run).map (·.uid)
        = (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ys).run := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show ((LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) hd).run ++
            (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run).map (·.uid)
          = (LHSSlot.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) hd).run ++
            (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
        rw [List.map_append, lhsAxisUidFusion hd, ih]
  -- The `RHSExpr` layer is not one of this block's nodes, but its `traverseAxesWithMask` run
  -- decomposes (defeq) into the `SumExpr` body run `++` the `Nonlin` mask run, so its fusion is
  -- exactly `sumExprAxisUidFusion` `++` `nonlinAxisUidFusion` — no separate RHSExpr lemma needed.
  have hRHS : ∀ r : RHSExpr,
      ((RHSExpr.traverseAxesWithMask (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r).run).map (·.uid)
        = (RHSExpr.traverseAxesWithMask (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) r).run := by
    intro r
    show ((SumExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r.body).run ++
        (Nonlin.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r.nonlin).run).map (·.uid)
      = (SumExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) r.body).run ++
        (Nonlin.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) r.nonlin).run
    rw [List.map_append, sumExprAxisUidFusion r.body, nonlinAxisUidFusion r.nonlin]
  cases s with
  | assign nm ls r =>
      show ((Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ls).run ++
          (RHSExpr.traverseAxesWithMask (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r).run).map (·.uid)
        = (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ls).run ++
          (RHSExpr.traverseAxesWithMask (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) r).run
      rw [List.map_append, coreLHS ls, hRHS r]
  | scatter nm ls r o =>
      show ((Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ls).run ++
          (RHSExpr.traverseAxesWithMask (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r).run).map (·.uid)
        = (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ls).run ++
          (RHSExpr.traverseAxesWithMask (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) r).run
      rw [List.map_append, coreLHS ls, hRHS r]
  | recurMorphism nm ax tc => rfl

/-- Every `AxisSpec` occurring anywhere in the program, in program order (decls then stmts).
    The `ConstL (List AxisSpec)` instantiation of `TLProgram.traverseAxes`. -/
private def TLProgram.axisSpecs (p : TLProgram) : List AxisSpec :=
  (TLProgram.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) p).run

/-- The ordered, de-duplicated list of axis names occurring anywhere in the program. -/
-- Design note — the name-collecting "fourth direction" of `traverseAxes`. It *could* be a first-class
-- instantiation, `g := fun a => ⟨[a.name]⟩` at `f := ConstL (List String)`:
--   ((TLProgram.traverseAxes (f := ConstL (List String)) (fun a => ⟨[a.name]⟩) p).run).eraseDups
-- We deliberately keep it as a projection of `axisSpecs` instead, for two reasons: (1) unlike the
-- `mapUID`/`specs*`/`*AxisUIDs` families E1 unified, name-collection was never a duplicated per-node
-- traversal — it's a one-liner over `axisSpecs` (itself the `ConstL (List AxisSpec)` instantiation), so
-- there is no duplication to remove and its correctness rides on `axisSpecs`'s certificate for free;
-- (2) `.eraseDups` is post-processing, not part of the traversal, so a direct instantiation would still
-- need it — it would add a fourth instantiation to maintain for no simplification.
def TLProgram.axisNames (p : TLProgram) : List String :=
  (p.axisSpecs.map (·.name)).eraseDups

/-! ## UID collectors (public — for tests and later phases) -/

/-- Every `AxisSpec.uid` reachable in a statement, in program order. -/
def Stmt.uids (s : Stmt) : List UID := (specsStmt s).map (·.uid)

-- E1 traverseAxes migration (2026-07-16..17 — see
-- docs/superpowers/specs/2026-07-16-e1-traverseaxes-stmt-design.md). `Stmt.uids_eq` (below)
-- relates the public `Stmt.uids` to the explicit per-node UID collectors; the six
-- `specsX_map_uid_eq` lemmas relate each private `specsX` AxisSpec-collector's `.map (·.uid)` to
-- its UID collector. Both are proved directly against `traverseAxes` via the `*AxisUidFusion`
-- lemmas above (Task B1's fusion re-derivation), not against any hand-written body. This is the
-- sole reason for the cross-layer `LeanNCD.Eval.Contract` import + `open` at the top of the file:
-- the statements below name the real public `idxAxisUIDs`/`predAxisUIDs`/`boolAxisUIDs`/
-- `termAxisUIDs` rather than duplicating their logic. NOTE — DO NOT retire as "unused": the six
-- `specsX_map_uid_eq` lemmas have no current consumer (the spike's `stmtUids` reconstruction was
-- retired with sub-project 2, and `Stmt.uids_eq` goes straight through fusion), and `Stmt.uids`
-- is the by-uid readout staged "for later phases" (see its section header, symmetric with the
-- by-name `TLProgram.axisNames`). They are FORWARD INFRASTRUCTURE for E1's collector/mapper
-- unification (see the E1 section in papers/restructure_suggestions.md): the `map_uid_eq`/
-- `*AxisUidFusion` lemmas are the kernel-checked proof that the AxisSpec- and UID-collection
-- `traverseAxes` instantiations agree node-for-node. Keep them.

private theorem specsIdx_map_uid_eq (e : IdxExpr) : (specsIdx e).map (·.uid) = idxAxisUIDs e := by
  -- Both sides are `ConstL` runs of `IdxExpr.traverseAxes` — `specsIdx` at `List AxisSpec`,
  -- `idxAxisUIDs` (post-migration) at `List UID` — so `idxAxisUidFusion` (the map-`(·.uid)`
  -- naturality of the `Const` applicative) IS this statement, up to unfolding both defs. This is
  -- the fusion-based re-derivation: no `specsIdx_eq_old` bridge, no dependence on either shape.
  exact idxAxisUidFusion e

private theorem specsPred_map_uid_eq (e : PredArith) : (specsPred e).map (·.uid) = predAxisUIDs e := by
  induction e with
  | embed e => exact specsIdx_map_uid_eq e
  | mul a b iha ihb =>
      show (specsPred a ++ specsPred b).map (·.uid) = predAxisUIDs a ++ predAxisUIDs b
      rw [List.map_append, iha, ihb]
  | iabs a iha =>
      show (specsPred a).map (·.uid) = predAxisUIDs a
      exact iha

private theorem specsBool_map_uid_eq (b : BoolExpr) : (specsBool b).map (·.uid) = boolAxisUIDs b := by
  induction b with
  | rel op a b =>
      show (specsPred a ++ specsPred b).map (·.uid) = predAxisUIDs a ++ predAxisUIDs b
      rw [List.map_append, specsPred_map_uid_eq, specsPred_map_uid_eq]
  | and a b iha ihb =>
      show (specsBool a ++ specsBool b).map (·.uid) = boolAxisUIDs a ++ boolAxisUIDs b
      rw [List.map_append, iha, ihb]
  | or a b iha ihb =>
      show (specsBool a ++ specsBool b).map (·.uid) = boolAxisUIDs a ++ boolAxisUIDs b
      rw [List.map_append, iha, ihb]
  | not a iha =>
      show (specsBool a).map (·.uid) = boolAxisUIDs a
      exact iha
  | ieq a b =>
      show (specsPred a ++ specsPred b).map (·.uid) = predAxisUIDs a ++ predAxisUIDs b
      rw [List.map_append, specsPred_map_uid_eq, specsPred_map_uid_eq]

private theorem specsFactor_map_uid_eq (x : Factor) :
    (specsFactor x).map (·.uid) = match x with
      | .read _ es => es.flatMap idxAxisUIDs
      | .iverson b => boolAxisUIDs b
      | .unaryFn _ _ es => es.flatMap idxAxisUIDs := by
  -- Fusion-based re-derivation (no `specsFactor_eq_old` bridge): `factorAxisUidFusion` turns
  -- `(specsFactor x).map (·.uid)` into the UID run; the `.read`/`.unaryFn` runs then fold to
  -- `es.flatMap idxAxisUIDs` (`hidx`), and `.iverson`'s run IS `boolAxisUIDs b` definitionally.
  have hidx : ∀ es : List IdxExpr,
      (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) es).run
        = es.flatMap idxAxisUIDs := by
    intro es
    induction es with
    | nil => rfl
    | cons hd tl ih =>
        -- head's run IS `idxAxisUIDs hd` (post-migration); tail closes by the IH.
        show idxAxisUIDs hd ++
            (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
          = idxAxisUIDs hd ++ tl.flatMap idxAxisUIDs
        rw [ih]
  show ((Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) x).run).map (·.uid) = _
  rw [factorAxisUidFusion x]
  cases x with
  | read nm es => exact hidx es
  | iverson b => rfl
  | unaryFn op nm es => exact hidx es

private theorem specsNonlin_map_uid_eq (n : Nonlin) :
    (specsNonlin n).map (·.uid) = match n with
      | .axiswise _ (some m) => boolAxisUIDs m | _ => [] := by
  cases n with
  | identity => rfl
  | pointwise pf => rfl
  | axiswise fn m => cases m with | none => rfl | some b => exact specsBool_map_uid_eq b

private theorem specsLHS_map_uid_eq (sl : LHSSlot) :
    (specsLHS sl).map (·.uid) = match sl with
      | .free a => [a.uid] | .freeNorm a => [a.uid]
      | .iterAt a _ => [a.uid] | .iterNext a => [a.uid]
      | .affine e => idxAxisUIDs e := by
  cases sl with
  | free a => rfl
  | freeNorm a => rfl
  | iterAt a n => rfl
  | iterNext a => rfl
  | affine e => exact specsIdx_map_uid_eq e

theorem Stmt.uids_eq (s : Stmt) : Stmt.uids s =
    match s with
    | .assign _ ls r =>
        ls.flatMap (fun sl => match sl with
          | .free a => [a.uid] | .freeNorm a => [a.uid]
          | .iterAt a _ => [a.uid] | .iterNext a => [a.uid]
          | .affine e => idxAxisUIDs e)
        ++ r.body.terms.flatMap termAxisUIDs
        ++ (match r.nonlin with
            | .axiswise _ (some m) => boolAxisUIDs m | _ => [])
    | .scatter _ ls r _ =>
        ls.flatMap (fun sl => match sl with
          | .free a => [a.uid] | .freeNorm a => [a.uid]
          | .iterAt a _ => [a.uid] | .iterNext a => [a.uid]
          | .affine e => idxAxisUIDs e)
        ++ r.body.terms.flatMap termAxisUIDs
        ++ (match r.nonlin with
            | .axiswise _ (some m) => boolAxisUIDs m | _ => [])
    | .recurMorphism _ ax _ => [ax.uid]
  := by
  -- Fusion-based re-derivation (drops the `specsStmt_eq_old` / `specsRHS_eq_old` bridges):
  -- `stmtAxisUidFusion` turns `Stmt.uids s = (specsStmt s).map (·.uid)` into the single
  -- UID-collecting run of `Stmt.traverseAxes`; the three `have`s reduce that run's list/option
  -- sub-traversals to the explicit UID collectors the statement spells out. Each head element's
  -- run IS the corresponding collector definitionally (post sub-project-2 migration), so the
  -- inductions close on the IH alone. Proved directly from the traversal — NOT via the spike's
  -- `traverseAxes_const_eq_stmtUids`, which is itself proved from this theorem (would be circular).
  have hLS : ∀ ls : List LHSSlot,
      (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ls).run
        = ls.flatMap (fun sl => match sl with
            | .free a => [a.uid] | .freeNorm a => [a.uid]
            | .iterAt a _ => [a.uid] | .iterNext a => [a.uid]
            | .affine e => idxAxisUIDs e) := by
    intro ls
    induction ls with
    | nil => rfl
    | cons hd tl ih =>
        show (LHSSlot.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) hd).run
            ++ (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
          = (match hd with
             | .free a => [a.uid] | .freeNorm a => [a.uid]
             | .iterAt a _ => [a.uid] | .iterNext a => [a.uid]
             | .affine e => idxAxisUIDs e)
            ++ tl.flatMap (fun sl => match sl with
                | .free a => [a.uid] | .freeNorm a => [a.uid]
                | .iterAt a _ => [a.uid] | .iterNext a => [a.uid]
                | .affine e => idxAxisUIDs e)
        rw [ih]
        -- each slot's run IS its arm: bare-axis slots are `[a.uid]`, `.affine` is `idxAxisUIDs e`.
        cases hd with
        | free a => rfl
        | freeNorm a => rfl
        | iterAt a n => rfl
        | iterNext a => rfl
        | affine e => rfl
  have hBody : ∀ ts : List ProdTerm,
      (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ts).run
        = ts.flatMap termAxisUIDs := by
    intro ts
    induction ts with
    | nil => rfl
    | cons hd tl ih =>
        -- head's run IS `termAxisUIDs hd` (post-migration); tail closes by the IH.
        show termAxisUIDs hd
            ++ (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
          = termAxisUIDs hd ++ tl.flatMap termAxisUIDs
        rw [ih]
  have hNonlin : ∀ n : Nonlin,
      (Nonlin.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) n).run
        = (match n with
           | .axiswise _ (some m) => boolAxisUIDs m | _ => []) := by
    intro n
    -- the mask run is `boolAxisUIDs m` when a mask is present, `[]` otherwise — all `rfl`.
    cases n with
    | identity => rfl
    | pointwise pf => rfl
    | axiswise fn m => cases m with | none => rfl | some b => rfl
  show ((Stmt.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run).map (·.uid) = _
  rw [stmtAxisUidFusion s]
  cases s with
  | assign nm ls r =>
      -- `Stmt.traverseAxes` for `.assign` is `traverse LHSSlot <*> traverseAxesWithMask`, whose run
      -- is `lhsRun ++ (bodyRun ++ nonlinRun)`; `hLS`/`hBody`/`hNonlin` reduce the three, then
      -- `← List.append_assoc` re-brackets to the statement's `(lhs ++ body) ++ nonlin` form.
      show (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ls).run
          ++ ((Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) r.body.terms).run
              ++ (Nonlin.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) r.nonlin).run)
        = _
      rw [hLS ls, hBody r.body.terms, hNonlin r.nonlin, ← List.append_assoc]
  | scatter nm ls r o =>
      show (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ls).run
          ++ ((Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) r.body.terms).run
              ++ (Nonlin.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) r.nonlin).run)
        = _
      rw [hLS ls, hBody r.body.terms, hNonlin r.nonlin, ← List.append_assoc]
  | recurMorphism nm ax tc => rfl

/-! ## The `assignUIDs` phase -/

/-- Mint a fresh UID that is guaranteed non-zero. `0` is E1's "unassigned" sentinel
    (every emitted `AxisSpec.uid` starts at `0`); the §12 post-condition requires assigned
    UIDs to be distinguishable from it. `freshUData` is strictly increasing, so at most the
    first mint can be `0` — mint once more in that case. -/
private def freshNonZero : FreshM UID := do
  let d ← freshUData
  if d.uid == 0 then return (← freshUData).uid else return d.uid

/-- Mint one fresh non-zero UID per distinct axis name, then relabel every `AxisSpec.uid`
    by keying on the axis's source name. Equal names ⇒ equal UID; distinct names ⇒ distinct. -/
def assignUIDs (p : TLProgram) : FreshM LabeledProgram := do
  let mut memo : HashMap String UID := {}
  for nm in p.axisNames do
    let u ← freshNonZero
    memo := memo.insert nm u
  let relabel : UData → UData := fun u =>
    match u.name with
    | some nm => match memo[nm]? with | some v => { u with uid := v } | none => u
    | none    => u
  let p' := TLProgram.mapUID relabel p
  return { decls := p'.decls, stmts := p'.stmts }

/-! ## The `resolveDecls` phase

Builds the `DeclEnv` and classifies tensor names as external inputs vs internally produced.
Per the §12.1 contract this phase is purely constructive: §12.1 example programs READ names like
`W`, `X`, `Q`, `K` with no `tensor` declaration, so an undeclared read is an external input — not
an error. `resolveDecls` therefore NEVER throws. -/

/-- The tensor names a stmt reads (from `.read`/`.unaryFn` factors; iverson reads nothing). -/
def Stmt.readNames (s : Stmt) : List String := s.readFactors.map (·.1)

/-- Build the declaration environment and classify external-input names.
    `extNames` = names READ in some stmt but never PRODUCED (never a stmt LHS). Never throws. -/
def resolveDecls (lp : LabeledProgram) : FreshM ResolvedProgram := do
  let env : DeclEnv := lp.decls.foldl (fun m d => match d with
    | .axis _ _ => m                  -- axis decls name an axis, not a tensor: keep them out of the env
    | .iter _ _ => m                  -- iter decls ALSO name an axis, not a tensor — same reason
    | _         => m.insert d.name d) {}
  let produced : List String := lp.stmts.map Stmt.lhsName
  let reads    : List String := lp.stmts.flatMap Stmt.readNames
  let extNames : Finset String :=
    reads.foldl (fun s n => if produced.contains n then s else insert n s) ∅
  return { decls := lp.decls, stmts := lp.stmts, env,
           extNames }

/-! ## The `reclassifyIterSlots` phase (between `resolveDecls` and `checkReadRanks`/`checkDtypes`/
`checkScatterNonlin`/`lowerArith` — MUST run before all four, since each of those inspects LHS slot
shape and would otherwise either silently skip a slot that should become `.iterNext` (`checkDtypes`'s
`iterAxisNotNat`) or silently misclassify it as a scatter (`checkScatterNonlin`/`lowerArith`'s
`slotsBecomeScatter`, which matches ANY `.affine` slot).

#5b: `l +1` and `l + 1` both elaborate to `LHSSlot.affine (IdxExpr.shift a 1)` now (Elab.lean) — the
only remaining signal for "is this really a scan recurrence, or an ordinary shifted write?" is
whether `a`'s axis is declared `iter`. An offset of exactly 1 is ALWAYS presumed a recurrence
attempt under this design (that's the whole point of accepting both spacings for THIS `IdxExpr`
shape); an offset other than 1 is never touched here and stays an ordinary shifted write,
ambiguity-free. NOT exhaustive over all surface spellings of "shift by 1": `1*l+1` elaborates to
the distinct shape `IdxExpr.affine 1 [(1, l)]` (the `num "*" ident "+" num` LHS-slot production),
which this reclassifier does not match at all — it passes through untouched even if `l` is
declared `iter`, and compiles to a different `ThreadedComposed` than `l+1`/`l + 1` would. That
still fails loud at EVAL time (a genuine size mismatch), never silently wrong — just an
unreclassified extra spelling, not a gap in the affine-shift case this phase actually handles. -/

/-- Every axis-UID declared via `iter` in this program. -/
def iterDeclUids (decls : List Decl) : List UID :=
  decls.filterMap (fun d => match d with | .iter ax _ => some ax.uid | _ => none)

/-- Reclassify one LHS slot: an `.affine (.shift a 1)` write becomes `.iterNext` iff `a` is
    declared `iter` (forcing its kind to `.nat` — `iter` carries no kind of its own, unlike
    `axis`, so the reclassifier is what fixes it; this is why `iterAxisNotNat` becomes
    unreachable for any `iter`-declared axis). Otherwise: reject. Every other slot shape passes
    through unchanged, including `.affine (.shift a n)` for any `n ≠ 1` (an ordinary shifted
    write — never ambiguous, never touched). -/
def reclassifyLHSSlot (iterUids : List UID) : LHSSlot → FreshM LHSSlot
  | .affine (.shift a 1) =>
      if a.uid ∈ iterUids then return .iterNext { a with kind := .nat }
      else throw (CompileError.scanAxisNotIter a.name)
  | sl => return sl

def reclassifyIterSlots (rp : ResolvedProgram) : FreshM ResolvedProgram := do
  let iterUids := iterDeclUids rp.decls
  let stmts' ← rp.stmts.mapM (fun s => match s with
    | .assign nm ls rhs      => return Stmt.assign nm (← ls.mapM (reclassifyLHSSlot iterUids)) rhs
    | .scatter nm ls rhs opt => return Stmt.scatter nm (← ls.mapM (reclassifyLHSSlot iterUids)) rhs opt
    | .recurMorphism _ _ _   => return s)
  return { rp with stmts := stmts' }

/-! ## The `checkReadRanks` phase

Validates that every `read nm idxExprs` in the program uses a number of index positions consistent
with `nm`'s declaration. Two cases:
- **Declared tensors** (`nm ∈ env`): `idxExprs.length` must equal the decl's axis count.
- **External tensors** (`nm ∈ extNames`): no declaration exists, so we check internal consistency —
  all reads of the same external name must agree on arity (first read wins as the expected rank).

`recurMorphism` stmts are invisible here (their reads are empty), consistent with how the
rest of the pipeline treats that escape hatch. -/

private def Decl.axisCount : Decl → Nat
  | .tensor _ ax | .predicate _ ax | .linear _ ax _ => ax.length
  | .axis _ _ => 0   -- axis decls are excluded from DeclEnv; never reached via env lookup
  | .iter _ _ => 0   -- iter decls are ALSO excluded from DeclEnv; never reached via env lookup

private def stmtReads (s : Stmt) : List (String × Nat) :=
  s.readFactors.map (fun (nm, es) => (nm, es.length))

/-- Will this LHS be lowered to a `scatter` (publishing its full slot-count rank)? True for an affine
    LHS (`Out[2*i,2*j]`) or a diagonal LHS with a repeated free axis (`Y[i,i]`). Shared by the
    read-rank guard (`stmtLhsRank`) and `lowerArith` so they agree on the published rank. -/
def slotsBecomeScatter (slots : List LHSSlot) : Bool :=
  slots.any (fun sl => match sl with | .affine _ => true | _ => false)
  || (let us := slots.filterMap (·.freeUID?)
      us.length ≠ us.eraseDups.length)

/-- The produced (published) rank of a stmt's LHS — what a reader's arity must match. A LHS that
    becomes a `scatter` (`slotsBecomeScatter`: affine `Out[2*i,2*j]` ⇒ 2, or diagonal `Y[i,i]` ⇒ 2)
    publishes its full placement rank (`ls.length`); otherwise it publishes the dedup'd free-axis
    count (what `tensorAxes` emits). Used to arity-check reads of produced-but-undeclared
    intermediates. -/
private def stmtLhsRank (s : Stmt) : Nat :=
  match s with
  | .assign _ ls _ | .scatter _ ls _ _ =>
      if slotsBecomeScatter ls then ls.length
      else (ls.filterMap (·.axisUID?)).eraseDups.length
  | .recurMorphism _ _ _ => 0

def checkReadRanks (rp : ResolvedProgram) : FreshM ResolvedProgram := do
  let reads : List (String × Nat) := rp.stmts.flatMap stmtReads
  -- declared tensors: check against DeclEnv
  for (nm, arity) in reads do
    if let some decl := rp.env[nm]? then
      let expected := decl.axisCount
      if arity != expected then throw (.rankMismatch nm expected arity)
  -- external tensors: check internal consistency (first read site establishes expected rank)
  let mut extRanks : HashMap String Nat := {}
  for (nm, arity) in reads do
    if nm ∈ rp.extNames then
      match extRanks[nm]? with
      | none   => extRanks := extRanks.insert nm arity
      | some r => if arity != r then throw (.rankMismatch nm r arity)
  -- produced-but-undeclared intermediates: no declaration justifies over-indexing, so a read whose
  -- arity ≠ the produced (dedup'd) rank is malformed (Track A #1). FAIL LOUD rather than route an
  -- ill-typed reindexing / silently broadcast at eval.
  let producedRank : HashMap String Nat :=
    rp.stmts.foldl (fun m s => m.insert s.lhsName (stmtLhsRank s)) {}
  for (nm, arity) in reads do
    unless rp.env.contains nm || decide (nm ∈ rp.extNames) do
      match producedRank[nm]? with
      | some r => if arity != r then throw (.rankMismatch nm r arity)
      | none   => pure ()
  return rp

/-! ## The `checkDtypes` phase

Two dtype invariants enforced after `checkReadRanks`:

**A — Axis-kind on LHS slots.**
- `iterAt`/`iterNext` slots must use a `nat`-kinded axis (scans iterate over discrete indices).
- `freeNorm` slots (the `m.`-marked softmax/normalize reduction axis) must use a `real`-kinded axis.

**B — Predicate outputs must have `identity` nonlinearity.**
A stmt writing to a `predicate`-declared tensor carries {0,1} values; applying relu/softmax/normalize
to such an output is a semantic error. Reading a predicate tensor on the RHS is intentionally valid
(the indicator-function pattern); only the output-nonlin combination is rejected.

`recurMorphism` stmts and `.affine`/`.free` slots are unconstrained and pass through. -/

private def isNat : AxisKind → Bool | .nat => true | _ => false
private def isReal : AxisKind → Bool | .real => true | _ => false

def checkDtypes (rp : ResolvedProgram) : FreshM ResolvedProgram := do
  for s in rp.stmts do
    -- Check A: axis kinds on LHS slots
    let slots : List LHSSlot := match s with
      | .assign _ ls _ | .scatter _ ls _ _ => ls
      | .recurMorphism _ _ _ => []
    for slot in slots do
      match slot with
      | .iterAt a _ | .iterNext a =>
          unless isNat a.kind do throw (.iterAxisNotNat a.name)
      | .freeNorm a =>
          unless isReal a.kind do throw (.normAxisNotReal a.name)
      | _ => pure ()
    -- Check B: predicate outputs must have identity nonlinearity and sum aggregation
    match s with
    | .assign nm _ rhs | .scatter nm _ rhs _ =>
        if let some (.predicate _ _) := rp.env[nm]? then
          unless rhs.nonlin == .identity do throw (.predicateNonlin nm)
          unless rhs.agg   == .sum       do throw (.predicateAgg nm)
    | .recurMorphism nm _ _ =>
        -- Audit finding #4 (probed 2026-07-30): `compile` accepted this and emitted
        -- `ops=[BrOp.scanPre]`, while `eval` reported "scanPre unsupported" — and `toBrBaseP`
        -- DISCARDED the supplied `ThreadedComposed` entirely (empty degree/weaves/reindexings, and
        -- the iteration axis dropped too). Accepted-then-partially-inspected-then-discarded is the
        -- worst of the three options, so reject it here, before it can become a look-alike primitive.
        -- Supporting it properly means one of: an opaque validated primitive whose semantics reach
        -- routing/realization/eval, or an inlined subgraph with explicit boundary ports. Its payload
        -- is also a required `EvalPlan` scan-step field (base plan + step plan), so the real fix
        -- belongs with that IR.
        throw (.unsupportedRecurMorphism nm)
  return rp

/-! ## The `checkScatterNonlin` phase

**Spike-3 Stage-0 policy (SHORT-TERM, not permanent):** a scatter write (an affine or diagonal
LHS — `slotsBecomeScatter`) may carry ONLY the `identity` nonlinearity; any other nonlinearity is
REJECTED here. Why: `evalScatter` (`Eval/Scatter.lean`) evaluates a scatter's RHS body but never
applied `rhs.nonlin` — so e.g. `Out[2*i] := relu(X[i])` used to compile and evaluate with the
`relu` silently dropped. Supporting a real nonlinear scatter later needs a semantic decision
(does the activation apply BEFORE collision-reduction, or AFTER the output is filled/reduced?)
that is deliberately out of scope now.

Runs here (pre-`lowerArith`), alongside `checkReadRanks`/`checkDtypes`, checking `r.nonlin ≠
Nonlin.identity`, NOT a match on `Nonlin`'s constructors — written this way so it
survived Spike 3a's restructuring of `Nonlin` unchanged. Checks BOTH shapes of the AST at
this point in the pipeline: an `.assign` whose LHS `slotsBecomeScatter` (the surface-compiled
case — `lowerArith`, Phase 4, is what reclassifies such an `.assign` into `Stmt.scatter`, and
that phase runs AFTER this one) and an already-`.scatter` stmt (the `recurMorphism`-style
escape hatch, §12.2 — a programmatic caller can build a `Stmt.scatter` directly, bypassing the
surface compiler entirely). -/
def checkScatterNonlin (rp : ResolvedProgram) : FreshM ResolvedProgram := do
  for s in rp.stmts do
    match s with
    | .assign nm ls rhs =>
        if slotsBecomeScatter ls && rhs.nonlin ≠ Nonlin.identity then
          throw (.unsupportedNonlinScatter nm)
    | .scatter nm _ rhs _ =>
        if rhs.nonlin ≠ Nonlin.identity then
          throw (.unsupportedNonlinScatter nm)
    | .recurMorphism _ _ _ => pure ()
  return rp

/-! ## The `lowerArith` phase (Phase 4 — affine index arithmetic)

E2a SCOPING DECISION (a deliberate divergence from §12.4): affine *reads* (e.g.
`X[i+p, 2*j+r]`) are LEFT IN PLACE here — the later `route` phase absorbs each read's affine
`IdxExpr` into the consuming step's `reindexings` field (exactly where stride-maps live in
`BrBase`, §2.3). So `lowerArith` emits NO separate Slice/Reindex intermediate steps. Its
real job is the affine-LHS → `Stmt.scatter` reclassification plus a
*conservative* `overlappingScatter` injectivity guard (a const LHS coord collapses a dimension
and so needs `reduce sum`; strided coords like upsample `2*i` are injective). -/

/-- A LHS slot that denotes an affine output coordinate (a Scatter write). Plain `free`
    axes and the scan slots (`iterAt`/`iterNext`) are NOT affine-scatter slots. -/
def LHSSlot.isAffine : LHSSlot → Bool
  | .affine _   => true
  | .free _     => false
  | .freeNorm _ => false
  | .iterAt _ _ => false
  | .iterNext _ => false

/-- Conservative non-injectivity test (E2a): a constant LHS coordinate collapses a
    dimension and so needs `reduce sum`; a strided coordinate (`scale`/general affine
    over an axis, e.g. upsample `2*i`) is injective. -/
def LHSSlot.collapses : LHSSlot → Bool
  | .affine (.const _) => true
  | _                  => false

def lowerArith (rp : ResolvedProgram) : FreshM LoweredProgram := do
  let stmts' ← rp.stmts.mapM (fun s => do
    match s with
    | .assign nm slots rhs =>
        -- Reclassify affine (Out[2*i,2*j]) OR diagonal (Y[i,i], a repeated free axis) LHS to a
        -- scatter that publishes its full placement rank — so declared/full-rank reads of it are
        -- sound (B1). `collapses` only guards affine `.const` dimension-collapse; a diagonal is
        -- injective (i ↦ (i,i)) so it passes.
        if slotsBecomeScatter slots then
          if slots.any LHSSlot.collapses then throw (CompileError.overlappingScatter nm)
          else return Stmt.scatter nm slots rhs { fill := 0, reduce := none }
        else return s
    | .scatter nm slots _ opts =>
        if (slots.any LHSSlot.collapses) && opts.reduce ≠ some "sum" then
          throw (CompileError.overlappingScatter nm)
        else return s
    | .recurMorphism _ _ _ => return s)   -- no affine LHS; passes through unchanged
  return { decls := rp.decls, stmts := stmts', env := rp.env,
           extNames := rp.extNames }

/-! ## The `finalizeScans` phase (Phase 5 — recurrence → Scan nodes)

A scan is a base case (`LHSSlot.iterAt`, the `l = 0` slot) plus a recurrence step
(`LHSSlot.iterNext`, the `l+1` slot). Statements for DIFFERENT tensor names that share the SAME
iteration-axis UID form a COUPLED scan (the §12.1 example: `G` and `H` both recur over `l`), so
they are grouped into ONE `ScanStmt.scan`. Validation: every recur step needs a matching base
step of the same name (else `missingBaseCase`); and a recur step may not read its iteration axis
"ahead" (`l+1` look-ahead on the RHS — else `causalityViolation`). -/

/-- All `IdxExpr`s read on the RHS of a stmt (concatenated per factor, in order). -/
def Stmt.rhsReads (s : Stmt) : List IdxExpr := s.readFactors.flatMap (·.2)

/-- Conservative causality check: does any RHS read reference iteration axis `u` with a
    strictly-positive look-ahead offset (`shift a n`, `n > 0`)? -/
def readsIterAhead (s : Stmt) (u : UID) : Bool :=
  s.rhsReads.any (fun
    | .shift a n => a.uid == u && n > 0
    | _          => false)

/-- Map slot-position → iteration axis, read from a step (`iterNext`) stmt. -/
def Stmt.stepAxisAt (step : Stmt) : Nat → Option AxisSpec := fun p =>
  step.iterInfo.findSome? (fun it => if it.isRecur && it.pos == p then some it.axis else none)

/-- Rewrite a base stmt's `iterAt` slots so each adopts the step's iteration axis at the SAME
    slot position (the E1 parser leaves base iter-axes as placeholders — `idxAxis ""` — so the
    slot's uid is the placeholder's, NOT the recurrence's). A base `iterAt` whose position has no
    matching step `iterNext` axis is left as-is. Positional recovery generalises the old single-axis
    `adoptBaseIterAxis` to multi-axis scans (each advancing slot of the step names one base slot). -/
def Stmt.adoptBaseIterAxes (base step : Stmt) : Stmt :=
  let remap : List LHSSlot → List LHSSlot := fun ls =>
    ls.zipIdx.map (fun (sl, p) =>
      match sl with
      | .iterAt _ n =>
          match step.stepAxisAt p with
          | some a => .iterAt a n
          | none   => sl
      | _ => sl)
  match base with
  | .assign nm ls r    => .assign  nm (remap ls) r
  | .scatter nm ls r o => .scatter nm (remap ls) r o
  | .recurMorphism _ _ _ => base

/-- Group `iterAt`/`iterNext` stmts by iteration-axis UID into (coupled) `ScanStmt.scan` nodes;
    pass everything else through as `ScanStmt.plain`. Validates base-case coverage and causality.

    PRE-PASS: each recurrence (`iterNext`) carries the real iteration axis (name + uid); each base
    case (`iterAt`) carries only the E1 placeholder axis (`idxAxis ""`). Before grouping, every base
    case adopts the iteration axis of a recurrence with the same tensor name, so base and recurrence
    land in the same UID group. -/
def finalizeScans (lp : LoweredProgram) : FreshM ScanProgram := do
  -- Recover each base case's iteration axes from the matching (same-name) step, BY SLOT POSITION.
  -- A base stmt has `iterAt` slots (no `iterNext`); its matching step has `iterNext` slots. Each
  -- base `iterAt` adopts the step's `iterNext` axis at the same slot position (multi-axis general).
  let stepFor (nm : String) : Option Stmt :=
    lp.stmts.find? (fun s => s.lhsName == nm && s.iterInfo.any (fun t => t.isRecur == true))
  let stmts0 := lp.stmts.map (fun s =>
    if s.iterInfo.any (fun t => t.isRecur == false) && !s.iterInfo.any (fun t => t.isRecur == true) then
      match stepFor s.lhsName with
      | some step => s.adoptBaseIterAxes step
      | none      => s
    else s)
  let lp := { lp with stmts := stmts0 }
  -- recurMorphism stmts convert directly to `.scanPre` (NOT grouped with iterAt/iterNext).
  let preNodes : List ScanStmt := lp.stmts.filterMap (fun s => match s with
    | .recurMorphism nm ax tc => some (ScanStmt.scanPre nm ax tc)
    | _                       => none)
  let nonPre     := lp.stmts.filter (fun s => match s with | .recurMorphism _ _ _ => false | _ => true)
  let iterStmts  := nonPre.filter (fun s => !s.iterInfo.isEmpty)
  -- DEPENDENCY ANALYSIS (the per-step-intermediate fix). Map each produced tensor name to the set
  -- of scan iteration-axis UIDs it (transitively) depends on: seed every scan-state name with ALL
  -- of its own iteration axes, then propagate through reads to a fixpoint. A NON-iter stmt whose LHS
  -- name acquires a nonempty set is a per-step *intermediate* of that scan — e.g. the transformer's
  -- Q/K/V/S/…, recomputed from the layer state every step — and belongs in the recurrence body. A
  -- non-iter stmt with the empty set is genuinely loop-invariant and stays `.plain` (evaluated once,
  -- the original behaviour). Bounded fixpoint: `dep` grows monotonically, capped by #stmts passes.
  let mut dep : HashMap String (List UID) := {}
  for s in nonPre do
    unless s.iterInfo.isEmpty do
      dep := dep.insert s.lhsName ((dep.getD s.lhsName [] ++ s.iterInfo.map (·.axis.uid)).eraseDups)
  for _ in List.range (nonPre.length + 1) do
    let mut changed := false
    for s in nonPre do
      let cur := dep.getD s.lhsName []
      let merged := (cur ++ s.readNames.flatMap (fun r => dep.getD r [])).eraseDups
      if merged.length != cur.length then
        dep := dep.insert s.lhsName merged
        changed := true
    unless changed do break
  -- CONNECTED COMPONENTS over iteration-axis UIDs: two iter-stmts are coupled iff their axis-sets
  -- share a UID (the §12.1 `G`/`H` coupled scan, and each axis of a genuine multi-axis scan). One
  -- `ScanStmt.scan` per component. Bounded union-find: repeated merge, capped by #stmts passes.
  let axSet : Stmt → List UID := fun s => (s.iterInfo.map (·.axis.uid)).eraseDups
  let mut comps : List (List UID) := iterStmts.map axSet
  for _ in List.range (iterStmts.length + 1) do
    comps := comps.foldl (fun acc c =>
      match acc.find? (fun d => d.any (fun u => c.contains u)) with
      | some d => (acc.erase d) ++ [(d ++ c).eraseDups]
      | none   => acc ++ [c]) []
  -- A non-iter intermediate whose scan-axis deps span more than ONE component is an unsupported
  -- cross-scan coupling (no §12.1 example needs it); fail loud. Within a single (possibly
  -- multi-axis) component it is a normal per-step intermediate.
  for s in nonPre do
    if s.iterInfo.isEmpty then
      let d := dep.getD s.lhsName []
      if !d.isEmpty && !comps.any (fun c => d.all (fun u => c.contains u)) then
        throw (CompileError.shapeMismatch
          s!"{s.lhsName}: per-step intermediate spans multiple scan components" "a single scan component")
  let mut nodes : List ScanStmt := []
  for comp in comps do
    -- membership tested against the ORIGINAL `nonPre` order so the recurrence body keeps source
    -- order (producers before consumers — exactly what `evalScan`'s step loop relies on).
    let inComp  : Stmt → Bool := fun s => (axSet s).any (fun u => comp.contains u)
    let isBase  : Stmt → Bool := fun s => inComp s && s.iterInfo.all (fun t => t.isRecur == false)
    let isState : Stmt → Bool := fun s => inComp s && s.iterInfo.any (fun t => t.isRecur == true)
    let isInter : Stmt → Bool := fun s => s.iterInfo.isEmpty &&
      (let d := dep.getD s.lhsName []; !d.isEmpty && d.all (fun u => comp.contains u))
    let baseStmts  := nonPre.filter (fun s => !s.iterInfo.isEmpty && isBase s)
    let stateRecur := nonPre.filter isState
    -- axis list in step slot order, from a representative step (each advancing slot ⇒ one axis).
    let axes : List AxisSpec := (stateRecur.head?.map (fun st =>
      ((st.iterInfo.filter (·.isRecur)).mergeSort (fun a b => a.pos ≤ b.pos)).map (·.axis))).getD []
    -- FAIL LOUD (design §5): every state recurrence in a component MUST advance over the
    -- component's FULL axis set. A heterogeneous coupling — e.g. `H` advancing over `{c}` coupled
    -- (via shared `c`) with `G` advancing over `{r,c}` — would drop the non-head axes when `axes`
    -- is taken from the head alone, and `evalScan` would silently mis-address the shorter tensor.
    -- Compare axis-UID SETS (order-independent) against the component's unioned axis set `comp`.
    for r in stateRecur do
      let radv := ((r.iterInfo.filter (·.isRecur)).map (·.axis.uid)).eraseDups
      unless radv.length == comp.length && comp.all (fun u => radv.contains u) do
        throw (CompileError.inconsistentScanAxes
          s!"{r.lhsName}: coupled scan statements advance over different axis sets (each must advance over the component's full axis set)")
    -- validation concerns only the genuine state recurrences: per-step intermediates have no base
    -- case and read the state at the current step, so neither check applies to them.
    for r in stateRecur do
      unless baseStmts.any (fun b => b.lhsName == r.lhsName) do
        throw (CompileError.missingBaseCase r.lhsName)
      for u in comp do
        if readsIterAhead r u then throw (CompileError.causalityViolation r.lhsName)
    -- FAIL LOUD (KG-scanprojection): an `isInter` statement (a per-step intermediate with no
    -- base case) whose OWN LHS references the component's iteration axis is ambiguous — it
    -- looks like the user wants a per-step read-out tracked across every `l`, but that's not
    -- materialized (only same-step scratch intermediates, which never reference `l` on their own
    -- LHS, are supported here). Reject rather than silently discard; the fully-general workaround
    -- is to write it as a separate top-level statement after the scan, reading the fully
    -- materialized state (see SS2 in the portfolio doc).
    for s in nonPre do
      if isInter s then
        if (s.slots.filterMap (·.axisUID?)).any (fun u => comp.contains u) then
          throw (CompileError.scanProjectionUnsupported s.lhsName)
    -- recurrence body = per-step intermediates ++ state recurrences, in source order.
    let recurStmts := nonPre.filter (fun s => isInter s || isState s)
    let repName := ((recurStmts.head?.orElse (fun _ => baseStmts.head?)).map Stmt.lhsName).getD ""
    -- ScanAffine (Prop 8.7): affine only for a genuine 1-axis component (multi-axis ⇒ sequential)
    -- whose every recurrence stmt (intermediates included) is identity-nonlin.
    let isAffine : Bool := axes.length ≤ 1 && recurStmts.all (fun s => Stmt.nonlinOf s == Nonlin.identity)
    nodes := nodes ++ [ ScanStmt.scan repName axes baseStmts recurStmts isAffine ]
  -- plain = non-iter stmts with NO scan dependency (loop-invariant; evaluated once).
  let plainStmts := nonPre.filter (fun s => s.iterInfo.isEmpty && (dep.getD s.lhsName []).isEmpty)
  return { decls := lp.decls, stmts := plainStmts.map ScanStmt.plain ++ preNodes ++ nodes,
           env := lp.env, extNames := lp.extNames }

end LeanNCD

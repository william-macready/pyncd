-- LeanNCD/DSL/Pipeline/Structural.lean
import LeanNCD.DSL.Pipeline.Types
import LeanNCD.DSL.Traverse
import LeanNCD.DSL.TraverseAxes
import LeanNCD.Exec.Uid
import Std.Data.HashMap
-- SPIKE EXCEPTION (E1 traverseAxes prototype, 2026-07-16 — see
-- docs/superpowers/specs/2026-07-16-e1-traverseaxes-stmt-design.md): this is the ONLY
-- cross-layer import on this branch — DSL/Pipeline and Eval are otherwise deliberately
-- parallel, non-crossing layers (see LeanNCD.lean's own architecture note). It exists solely
-- so `Stmt.uids_eq` below (also new, also spike-only) can state its RHS using the real,
-- public `idxAxisUIDs`/`boolAxisUIDs`/`termAxisUIDs` rather than duplicating their logic by
-- hand. TO REVERT: delete this import and the `Stmt.uids_eq` theorem (search "SPIKE EXCEPTION"
-- in this file) — nothing else in this file depends on either.
import LeanNCD.Eval.Contract

namespace LeanNCD
open Std
-- SPIKE EXCEPTION (see the `LeanNCD.Eval.Contract` import above): only needed by
-- `Stmt.uids_eq` below. TO REVERT: delete this line along with that import and theorem.
open LeanNCD.Eval (idxAxisUIDs predAxisUIDs boolAxisUIDs termAxisUIDs)

/-! ## Axis collectors

Axis identity in tensor logic is name-based within program scope (§12.1): a name appearing
in multiple places denotes the same axis. The `specs*` family gathers every source `AxisSpec`
in program order via structural recursion. Most of these (`specsIdx`, `specsPred`, `specsBool`,
`specsFactor`, `specsLHS`) are exhaustive matches, so Lean's totality check forces every new
constructor to be handled — nothing is silently dropped there. `specsNonlin` is the one
exception: it uses a wildcard fallback (`_ => []`), which is safe ONLY because every current
non-masked `Nonlin` variant genuinely contributes no axis specs. **Assumption that must hold for
any future `Nonlin` variant:** if it carries an optional mask (`Option BoolExpr`, like
`softmax`/`normalize`/`l2normalize`), it needs an explicit `some m => specsBool m` arm here —
otherwise the wildcard silently swallows that mask's axis specs (this bit `l2normalize` once
already; see the git history). The two public collectors below are thin projections of one
traversal: by name (`TLProgram.axisNames`, de-duplicated) or by uid (`Stmt.uids`). -/

-- SCAFFOLDING (E1 migration): four `specsX_old`/`specsX_eq_old` pairs remain below
-- (`specsIdx`, `specsFactor`, `specsRHS`, `specsStmt`). Each `_old` is the frozen pre-migration
-- body; each `_eq_old` bridges the traversal-derived def back to it, and is `rw`'d into by one
-- pre-existing UID proof (`specsIdx_map_uid_eq`, `specsFactor_map_uid_eq`, and `Stmt.uids_eq`'s
-- `hRHS`/top-level) that was written against the old structural shape. To eliminate them, the
-- dependent UID proofs must be re-derived directly against `traverseAxes` — a separate, reviewed
-- task. See docs/superpowers/specs/2026-07-17-e1-scaffolding-refactor-followup.md before touching.
-- (The four dead pairs — specsPred/specsBool/specsNonlin/specsLHS — were already removed.)

-- Frozen pre-migration body: the structural anchor `specsIdx_map_uid_eq` `rw`s back to via
-- `specsIdx_eq_old`; slated for deletion in Task 6 (see the SCAFFOLDING note above).
private def specsIdx_old : IdxExpr → List AxisSpec
  | .axis a => [a] | .const _ => [] | .scale _ a => [a]
  | .shift a _ => [a] | .affine _ xs => xs.map (·.2)

/-- Every `AxisSpec` occurring in an index expression (a bare axis, or the coordinate list of an
    affine combination). The `ConstL (List AxisSpec)` instantiation of `IdxExpr.traverseAxes`;
    `specsIdx_eq_old` certifies it equals the prior hand-written body. -/
private def specsIdx (e : IdxExpr) : List AxisSpec :=
  (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run

/-- Ports the spike's `traverseAxes_const_eq_specsIdx`: the leaf arms (`.axis`/`.const`/`.scale`/
    `.shift`) close by `rfl`; the `.affine` arm needs the `hmap`/`core` lemmas below to push the
    traversal's per-element `Prod.mk`-wrapping down to a plain `.map (·.2)`. -/
private theorem specsIdx_eq_old (e : IdxExpr) : specsIdx e = specsIdx_old e := by
  cases e with
  | axis a => rfl
  | const n => rfl
  | scale c a => rfl
  | shift a n => rfl
  | affine n xs =>
      -- The traversal re-pairs each `(Int × AxisSpec)` coordinate's `Int` half with the mapped
      -- `ConstL` value via `Prod.mk`; `ConstL` ignores its second type parameter, so this
      -- collapses definitionally to the plain per-element const action `core` is stated over.
      have hmap : (fun (ca : Int × AxisSpec) => Prod.mk ca.1 <$> (⟨[ca.2]⟩ : ConstL (List AxisSpec) AxisSpec))
          = (fun ca => (⟨[ca.2]⟩ : ConstL (List AxisSpec) (Int × AxisSpec))) := rfl
      -- The core list-map trick: traversing the coordinate list collects exactly `ys.map (·.2)`
      -- (the axis half of each pair) — the old `.affine` arm's body.
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

-- Frozen pre-migration body: the structural anchor `specsFactor_map_uid_eq` `rw`s back to via
-- `specsFactor_eq_old`; slated for deletion in Task 6 (see the SCAFFOLDING note above).
private def specsFactor_old : Factor → List AxisSpec
  | .read _ es => es.flatMap specsIdx | .iverson b => specsBool b
  | .unaryFn _ _ es => es.flatMap specsIdx

/-- Every `AxisSpec` occurring in a product factor (`read`'s index list, `iverson`'s boolean
    guard, or `unaryFn`'s index list). The `ConstL (List AxisSpec)` instantiation of
    `Factor.traverseAxes`; `specsFactor_eq_old` certifies it equals the prior hand-written body. -/
private def specsFactor (x : Factor) : List AxisSpec :=
  (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) x).run

/-- Ports the spike's `traverseAxes_const_eq_specsFactor` (built on
    `traverseAxes_const_eq_factorAxisUIDs`'s AxisSpec-side counterpart): `.read`/`.unaryFn` reduce
    to the `core` list-fold over `specsIdx`; `.iverson` cross-node-delegates to `specsBool`. -/
private theorem specsFactor_eq_old (x : Factor) : specsFactor x = specsFactor_old x := by
  have core : ∀ ys : List IdxExpr,
      (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ys).run
        = ys.flatMap specsIdx := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show specsIdx hd ++
            (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run
          = specsIdx hd ++ tl.flatMap specsIdx
        rw [ih]
  cases x with
  | read nm es =>
      show (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) es).run
        = es.flatMap specsIdx
      exact core es
  | iverson b =>
      -- Cross-node delegation to `specsBool` — plain `show`/`rw` can't see through the
      -- `Applicative`/`Traversable` instance layers here; `simp only [...]` unfolds both sides
      -- to the same `BoolExpr.traverseAxes` application, then `rfl` closes it.
      simp only [specsFactor, specsFactor_old, Factor.traverseAxes, specsBool]
      rfl
  | unaryFn op nm es =>
      show (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) es).run
        = es.flatMap specsIdx
      exact core es

-- Frozen pre-migration body: the structural anchor `Stmt.uids_eq`'s `hRHS` rewrites back to via
-- `specsRHS_eq_old`; slated for deletion in Task 6 (see the SCAFFOLDING note above).
private def specsRHS_old (r : RHSExpr) : List AxisSpec :=
  (r.body.terms.flatMap (fun t => t.factors.flatMap specsFactor)) ++ specsNonlin r.nonlin

/-- Every `AxisSpec` occurring on the RHS of a statement: every factor of every term, PLUS the
    `nonlin` mask — mask INCLUDED, the mirror of `readAxisUIDs`'s mask-excluded `NoMask` traversal
    on the UID side. The `ConstL (List AxisSpec)` instantiation of `RHSExpr.traverseAxesWithMask`;
    `specsRHS_eq_old` certifies it equals the prior hand-written body. -/
private def specsRHS (r : RHSExpr) : List AxisSpec :=
  (RHSExpr.traverseAxesWithMask (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r).run

/-- Ports the spike's `traverseAxes_const_eq_specsRHS`: the term/factor list-folds (`coreFactor`,
    `coreTerm`) mirror `specsFactor_eq_old`'s core lemma one layer up; the final step needs an
    explicit `rfl` after `rw [hbody]` (see the comment there) since the mask half of the traversal
    doesn't reduce under `rw`'s transparency. -/
private theorem specsRHS_eq_old (r : RHSExpr) : specsRHS r = specsRHS_old r := by
  have coreFactor : ∀ fs : List Factor,
      (Traversable.traverse (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) fs).run
        = fs.flatMap specsFactor := by
    intro fs
    induction fs with
    | nil => rfl
    | cons hd tl ih =>
        show specsFactor hd ++
            (Traversable.traverse (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run
          = specsFactor hd ++ tl.flatMap specsFactor
        rw [ih]
  have coreTerm : ∀ ts : List ProdTerm,
      (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ts).run
        = ts.flatMap (fun t => t.factors.flatMap specsFactor) := by
    intro ts
    induction ts with
    | nil => rfl
    | cons hd tl ih =>
        show (Traversable.traverse (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) hd.factors).run ++
            (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run
          = hd.factors.flatMap specsFactor ++ tl.flatMap (fun t => t.factors.flatMap specsFactor)
        rw [coreFactor hd.factors, ih]
  show (SumExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r.body).run ++
      (Nonlin.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r.nonlin).run
    = (r.body.terms.flatMap (fun t => t.factors.flatMap specsFactor)) ++ specsNonlin r.nonlin
  have hbody : (SumExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r.body).run
      = r.body.terms.flatMap (fun t => t.factors.flatMap specsFactor) := by
    show (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) r.body.terms).run
      = r.body.terms.flatMap (fun t => t.factors.flatMap specsFactor)
    exact coreTerm r.body.terms
  rw [hbody]
  -- rw's reducible-transparency close can't unfold specsNonlin; rfl (default) does
  rfl

/-- Every `AxisSpec` occurring in a single LHS slot: the bare axis for `free`/`freeNorm`/
    `iterAt`/`iterNext`, or the index expression's specs for `affine`. The `ConstL (List AxisSpec)`
    instantiation of `LHSSlot.traverseAxes`. -/
private def specsLHS (s : LHSSlot) : List AxisSpec :=
  (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run

/-- Every `AxisSpec` occurring in a declaration. The `ConstL (List AxisSpec)` instantiation of
    `Decl.traverseAxes`. -/
private def specsDecl (d : Decl) : List AxisSpec :=
  (Decl.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) d).run

-- Frozen pre-migration body: the structural anchor `Stmt.uids_eq`'s top-level proof rewrites back
-- to via `specsStmt_eq_old`; slated for deletion in Task 6 (see the SCAFFOLDING note above).
private def specsStmt_old : Stmt → List AxisSpec
  | .assign _ ls r => ls.flatMap specsLHS ++ specsRHS r
  | .scatter _ ls r _ => ls.flatMap specsLHS ++ specsRHS r
  | .recurMorphism _ ax _ => [ax]

/-- Every `AxisSpec` occurring in a statement: its LHS slots and RHS (`assign`/`scatter`), or its
    recur axis (`recurMorphism`). The `ConstL (List AxisSpec)` instantiation of
    `Stmt.traverseAxes`; `specsStmt_eq_old` certifies it equals the prior hand-written body. -/
private def specsStmt (s : Stmt) : List AxisSpec :=
  (Stmt.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run

/-- Ports the spike's `traverseAxes_const_eq_specsStmt`: the LHS-slot list-fold (`core`) mirrors
    `specsFactor_eq_old`'s core lemma one layer up; `.assign`/`.scatter` each need an explicit
    `rfl` after `rw [core ls]` (see the comments there) since `rw`'s reducible transparency can't
    unfold `specsRHS`; `.recurMorphism` closes directly by `rfl`. -/
private theorem specsStmt_eq_old (s : Stmt) : specsStmt s = specsStmt_old s := by
  have core : ∀ ys : List LHSSlot,
      (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ys).run
        = ys.flatMap specsLHS := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show specsLHS hd ++
            (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run
          = specsLHS hd ++ tl.flatMap specsLHS
        rw [ih]
  cases s with
  | assign nm ls r =>
      show (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ls).run ++
          (RHSExpr.traverseAxesWithMask (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r).run
        = ls.flatMap specsLHS ++ specsRHS r
      rw [core ls]
      -- rw's reducible-transparency close can't unfold specsRHS; rfl (default) does
      rfl
  | scatter nm ls r o =>
      show (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ls).run ++
          (RHSExpr.traverseAxesWithMask (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r).run
        = ls.flatMap specsLHS ++ specsRHS r
      rw [core ls]
      -- rw's reducible-transparency close can't unfold specsRHS; rfl (default) does
      rfl
  | recurMorphism nm ax tc => rfl

/-- Every `AxisSpec` occurring anywhere in the program, in program order (decls then stmts).
    The `ConstL (List AxisSpec)` instantiation of `TLProgram.traverseAxes`. -/
private def TLProgram.axisSpecs (p : TLProgram) : List AxisSpec :=
  (TLProgram.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) p).run

/-- The ordered, de-duplicated list of axis names occurring anywhere in the program. -/
def TLProgram.axisNames (p : TLProgram) : List String :=
  (p.axisSpecs.map (·.name)).eraseDups

/-! ## UID collectors (public — for tests and later phases) -/

/-- Every `AxisSpec.uid` reachable in a statement, in program order. -/
def Stmt.uids (s : Stmt) : List UID := (specsStmt s).map (·.uid)

-- SPIKE EXCEPTION (E1 traverseAxes prototype, 2026-07-16 — see
-- docs/superpowers/specs/2026-07-16-e1-traverseaxes-stmt-design.md): exposes `Stmt.uids`'s
-- value in terms of already-public UID-collectors (`idxAxisUIDs`/`boolAxisUIDs`/
-- `termAxisUIDs`), letting an outside caller (the E1 spike file, which cannot see the private
-- `specsStmt`/`specsLHS`/`specsRHS`/`specsNonlin`/`specsFactor`/`specsBool`/`specsPred` this
-- unfolds) relate `Stmt.uids` to its own `traverseAxes`-based reconstruction without
-- duplicating any of their logic by hand. The six helper lemmas below establish, layer by
-- layer, that each private `specsX` collector's `.map (·.uid)` coincides with the layer's
-- public UID collector where one exists (`idxAxisUIDs`, `predAxisUIDs`, `boolAxisUIDs`), or
-- else the corresponding inline UID match (for `Factor`/`Nonlin`/`LHSSlot`, which have no named
-- public collector) — each proved entirely from *inside* this file, where those private helpers
-- are visible, checked against their real bodies by the Lean kernel, not "by inspection."
-- TO REVERT: delete this comment block through `Stmt.uids_eq` below, and the
-- `LeanNCD.Eval.Contract` import + `open` above (search "SPIKE EXCEPTION" in this file) —
-- nothing else here depends on any of it.

private theorem specsIdx_map_uid_eq (e : IdxExpr) : (specsIdx e).map (·.uid) = idxAxisUIDs e := by
  -- Restore the old structural shape (`specsIdx_old`) the case split below matches, since
  -- `idxAxisUIDs` is itself hand-written against that same shape.
  rw [specsIdx_eq_old]
  cases e with
  | axis a => rfl
  | const n => rfl
  | scale c a => rfl
  | shift a n => rfl
  | affine n xs =>
      show (xs.map (·.2)).map (·.uid) = xs.map (·.2.uid)
      rw [List.map_map]
      rfl

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
  -- Restore the old structural shape (`specsFactor_old`) the case split below matches, since
  -- the RHS match is itself written against that same shape.
  rw [specsFactor_eq_old]
  cases x with
  | read nm es =>
      show (es.flatMap specsIdx).map (·.uid) = es.flatMap idxAxisUIDs
      rw [List.map_flatMap]
      congr 1
      funext e
      exact specsIdx_map_uid_eq e
  | iverson b =>
      show (specsBool b).map (·.uid) = boolAxisUIDs b
      exact specsBool_map_uid_eq b
  | unaryFn op nm es =>
      show (es.flatMap specsIdx).map (·.uid) = es.flatMap idxAxisUIDs
      rw [List.map_flatMap]
      congr 1
      funext e
      exact specsIdx_map_uid_eq e

private theorem specsNonlin_map_uid_eq (n : Nonlin) :
    (specsNonlin n).map (·.uid) = match n with
      | .softmax (some m) => boolAxisUIDs m | .normalize (some m) => boolAxisUIDs m
      | .l2normalize (some m) => boolAxisUIDs m | _ => [] := by
  cases n with
  | identity => rfl | relu => rfl | sigmoid => rfl | tanh => rfl | gelu => rfl | leakyrelu => rfl
  | softmax m => cases m with | none => rfl | some b => exact specsBool_map_uid_eq b
  | normalize m => cases m with | none => rfl | some b => exact specsBool_map_uid_eq b
  | l2normalize m => cases m with | none => rfl | some b => exact specsBool_map_uid_eq b

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
            | .softmax (some m) => boolAxisUIDs m | .normalize (some m) => boolAxisUIDs m
            | .l2normalize (some m) => boolAxisUIDs m | _ => [])
    | .scatter _ ls r _ =>
        ls.flatMap (fun sl => match sl with
          | .free a => [a.uid] | .freeNorm a => [a.uid]
          | .iterAt a _ => [a.uid] | .iterNext a => [a.uid]
          | .affine e => idxAxisUIDs e)
        ++ r.body.terms.flatMap termAxisUIDs
        ++ (match r.nonlin with
            | .softmax (some m) => boolAxisUIDs m | .normalize (some m) => boolAxisUIDs m
            | .l2normalize (some m) => boolAxisUIDs m | _ => [])
    | .recurMorphism _ ax _ => [ax.uid]
  := by
  have hRHS : ∀ r : RHSExpr, (specsRHS r).map (·.uid) =
      r.body.terms.flatMap termAxisUIDs
      ++ (match r.nonlin with
          | .softmax (some m) => boolAxisUIDs m | .normalize (some m) => boolAxisUIDs m
          | .l2normalize (some m) => boolAxisUIDs m | _ => []) := by
    intro r
    -- Restore the old structural shape (`specsRHS_old`) the `show` below matches, since the RHS
    -- match (`termAxisUIDs`/nonlin-mask arms) is itself written against that same shape.
    rw [specsRHS_eq_old]
    show ((r.body.terms.flatMap (fun t => t.factors.flatMap specsFactor)) ++ specsNonlin r.nonlin).map (·.uid)
      = r.body.terms.flatMap termAxisUIDs ++ (match r.nonlin with
          | .softmax (some m) => boolAxisUIDs m | .normalize (some m) => boolAxisUIDs m
          | .l2normalize (some m) => boolAxisUIDs m | _ => [])
    rw [List.map_append, specsNonlin_map_uid_eq]
    congr 1
    rw [List.map_flatMap]
    congr 1
    funext t
    show (t.factors.flatMap specsFactor).map (·.uid) = termAxisUIDs t
    rw [List.map_flatMap]
    congr 1
    funext x
    exact specsFactor_map_uid_eq x
  have hLS : ∀ ls : List LHSSlot, (ls.flatMap specsLHS).map (·.uid) =
      ls.flatMap (fun sl => match sl with
        | .free a => [a.uid] | .freeNorm a => [a.uid]
        | .iterAt a _ => [a.uid] | .iterNext a => [a.uid]
        | .affine e => idxAxisUIDs e) := by
    intro ls
    rw [List.map_flatMap]
    congr 1
    funext sl
    exact specsLHS_map_uid_eq sl
  show (specsStmt s).map (·.uid) = _
  -- Restore the old structural shape (`specsStmt_old`) the case split below matches, since the
  -- goal's RHS (the `Stmt.uids_eq` statement) is itself written against that same shape.
  rw [specsStmt_eq_old]
  cases s with
  | assign nm ls r =>
      show (ls.flatMap specsLHS ++ specsRHS r).map (·.uid) = _
      rw [List.map_append, hLS, hRHS, ← List.append_assoc]
  | scatter nm ls r o =>
      show (ls.flatMap specsLHS ++ specsRHS r).map (·.uid) = _
      rw [List.map_append, hLS, hRHS, ← List.append_assoc]
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
  let p' := TermTraversable.traverseUID relabel p
  return { decls := p'.decls, stmts := p'.stmts }

/-! ## The `resolveDecls` phase

Builds the `DeclEnv` and classifies tensor names as external inputs vs internally produced.
Per the §12.1 contract this phase is purely constructive: §12.1 example programs READ names like
`W`, `X`, `Q`, `K` with no `tensor` declaration, so an undeclared read is an external input — not
an error. `resolveDecls` therefore NEVER throws. -/

/-- The declaration's tensor name. (`axis` decls name an AXIS, not a tensor; `resolveDecls`
    skips them when building the tensor-keyed `DeclEnv`.) -/
def Decl.name : Decl → String
  | .tensor n _ => n | .predicate n _ => n | .linear n _ _ => n | .axis ax _ => ax.name

/-- The tensor name a stmt writes to (its LHS). -/
def Stmt.lhsName : Stmt → String
  | .assign n _ _ => n | .scatter n _ _ _ => n | .recurMorphism n _ _ => n

/-- The tensor names a stmt reads (from `.read` factors; iverson factors read nothing). -/
def Stmt.readNames : Stmt → List String
  | .assign _ _ r | .scatter _ _ r _ =>
      r.body.terms.flatMap (fun t => t.factors.filterMap (fun
        | .read nm _ => some nm
        | .iverson _ => none
        | .unaryFn _ nm _ => some nm))
  | .recurMorphism _ _ _ => []   -- recurMorphism reads not introspected (E2c)

/-- Build the declaration environment and classify external-input names.
    `extNames` = names READ in some stmt but never PRODUCED (never a stmt LHS). Never throws. -/
def resolveDecls (lp : LabeledProgram) : FreshM ResolvedProgram := do
  let env : DeclEnv := lp.decls.foldl (fun m d => match d with
    | .axis _ _ => m                  -- axis decls name an axis, not a tensor: keep them out of the env
    | _         => m.insert d.name d) {}
  let produced : List String := lp.stmts.map Stmt.lhsName
  let reads    : List String := lp.stmts.flatMap Stmt.readNames
  let extNames : Finset String :=
    reads.foldl (fun s n => if produced.contains n then s else insert n s) ∅
  return { decls := lp.decls, stmts := lp.stmts, env,
           extNames }

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

private def stmtReads (s : Stmt) : List (String × Nat) :=
  match s with
  | .assign _ _ r | .scatter _ _ r _ =>
      r.body.terms.flatMap (fun t => t.factors.filterMap (fun
        | .read nm es => some (nm, es.length)
        | .iverson _  => none
        | .unaryFn _ nm es => some (nm, es.length)))
  | .recurMorphism _ _ _ => []

/-- Will this LHS be lowered to a `scatter` (publishing its full slot-count rank)? True for an affine
    LHS (`Out[2*i,2*j]`) or a diagonal LHS with a repeated free axis (`Y[i,i]`). Shared by the
    read-rank guard (`stmtLhsRank`) and `lowerArith` so they agree on the published rank. -/
def slotsBecomeScatter (slots : List LHSSlot) : Bool :=
  slots.any (fun sl => match sl with | .affine _ => true | _ => false)
  || (let us := slots.filterMap (fun sl => match sl with | .free a => some a.uid | _ => none)
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
      else (ls.filterMap (fun
        | .free a | .freeNorm a | .iterNext a => some a.uid
        | .iterAt a _ => some a.uid
        | .affine _   => none)).eraseDups.length
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

private def isNat : AxisKind → Bool | .nat _ => true | _ => false
private def isReal : AxisKind → Bool | .real _ => true | _ => false

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

/-- The LHS slots of a statement. -/
def Stmt.slots : Stmt → List LHSSlot
  | .assign _ ls _ => ls | .scatter _ ls _ _ => ls | .recurMorphism _ _ _ => []

/-- The nonlinearity wrapping a stmt's step. A `recurMorphism` is pre-built (already-lowered),
    so it is affine-neutral (`identity`). Used by `finalizeScans` to detect ScanAffine (Prop 8.7):
    a scan whose every recurrence stmt is `identity`-nonlin carries no nonlinearity and is thus
    associative/parallel-prefix-able. This MUST be checked here (pre-`splitNonlins`), since
    `splitNonlins` later lifts nonlinearities out of `RHSExpr.nonlin` into separate steps. -/
def Stmt.nonlinOf : Stmt → Nonlin
  | .assign _ _ r => r.nonlin
  | .scatter _ _ r _ => r.nonlin
  | .recurMorphism _ _ _ => .identity

/-- All iteration slots of a stmt: `(uid, axis, isRecur, slot-position)` for each `iterAt`/`iterNext`.
    A 1-D scan yields a single-element list; multi-axis scans yield one entry per advancing slot. -/
def Stmt.iterInfo (s : Stmt) : List (UID × AxisSpec × Bool × Nat) :=
  s.slots.zipIdx.filterMap (fun (sl, i) => match sl with
    | .iterAt a _ => some (a.uid, a, false, i)
    | .iterNext a => some (a.uid, a, true, i)
    | _           => none)

/-- All `IdxExpr`s read on the RHS of a stmt. -/
def Stmt.rhsReads : Stmt → List IdxExpr
  | .assign _ _ r | .scatter _ _ r _ =>
      r.body.terms.flatMap (fun t => t.factors.flatMap (fun
        | .read _ es => es
        | .iverson _ => []
        | .unaryFn _ _ es => es))
  | .recurMorphism _ _ _ => []

/-- Conservative causality check: does any RHS read reference iteration axis `u` with a
    strictly-positive look-ahead offset (`shift a n`, `n > 0`)? -/
def readsIterAhead (s : Stmt) (u : UID) : Bool :=
  s.rhsReads.any (fun
    | .shift a n => a.uid == u && n > 0
    | _          => false)

/-- Map slot-position → iteration axis, read from a step (`iterNext`) stmt. -/
def Stmt.stepAxisAt (step : Stmt) : Nat → Option AxisSpec := fun p =>
  step.iterInfo.findSome? (fun (_, a, isRec, i) => if isRec && i == p then some a else none)

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
    lp.stmts.find? (fun s => s.lhsName == nm && s.iterInfo.any (fun t => t.2.2.1 == true))
  let stmts0 := lp.stmts.map (fun s =>
    if s.iterInfo.any (fun t => t.2.2.1 == false) && !s.iterInfo.any (fun t => t.2.2.1 == true) then
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
      dep := dep.insert s.lhsName ((dep.getD s.lhsName [] ++ s.iterInfo.map (·.1)).eraseDups)
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
  let axSet : Stmt → List UID := fun s => (s.iterInfo.map (·.1)).eraseDups
  -- The axis-UID of an LHS slot, if it has one (`.affine` slots contribute none) — used below to
  -- detect an unsupported in-scan per-step projection (§KG-scanprojection).
  let slotUID : LHSSlot → Option UID := fun sl => match sl with
    | .free a | .freeNorm a | .iterAt a _ | .iterNext a => some a.uid
    | .affine _ => none
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
    let isBase  : Stmt → Bool := fun s => inComp s && s.iterInfo.all (fun t => t.2.2.1 == false)
    let isState : Stmt → Bool := fun s => inComp s && s.iterInfo.any (fun t => t.2.2.1 == true)
    let isInter : Stmt → Bool := fun s => s.iterInfo.isEmpty &&
      (let d := dep.getD s.lhsName []; !d.isEmpty && d.all (fun u => comp.contains u))
    let baseStmts  := nonPre.filter (fun s => !s.iterInfo.isEmpty && isBase s)
    let stateRecur := nonPre.filter isState
    -- axis list in step slot order, from a representative step (each advancing slot ⇒ one axis).
    let axes : List AxisSpec := (stateRecur.head?.map (fun st =>
      ((st.iterInfo.filter (·.2.2.1)).mergeSort (fun a b => a.2.2.2 ≤ b.2.2.2)).map (·.2.1))).getD []
    -- FAIL LOUD (design §5): every state recurrence in a component MUST advance over the
    -- component's FULL axis set. A heterogeneous coupling — e.g. `H` advancing over `{c}` coupled
    -- (via shared `c`) with `G` advancing over `{r,c}` — would drop the non-head axes when `axes`
    -- is taken from the head alone, and `evalScan` would silently mis-address the shorter tensor.
    -- Compare axis-UID SETS (order-independent) against the component's unioned axis set `comp`.
    for r in stateRecur do
      let radv := ((r.iterInfo.filter (·.2.2.1)).map (·.1)).eraseDups
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
        if (s.slots.filterMap slotUID).any (fun u => comp.contains u) then
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

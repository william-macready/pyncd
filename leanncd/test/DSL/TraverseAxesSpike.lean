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
-- LHSSlot slice (simplest shape since IdxExpr): 4 of 5 arms apply `g` directly to a bare
-- `AxisSpec`, the 5th delegates to `IdxExpr.traverseAxes`; remap is FULLY UNCONDITIONAL, the
-- first time since IdxExpr itself; `lhsAxisUID?`/`freeAxisUIDs` are explicitly out of scope
-- (classify-and-filter, not a collector) — see
-- docs/superpowers/specs/2026-07-16-e1-traverseaxes-lhsslot-design.md.
-- Stmt slice (3 constructors; first production-file change on this branch): `.assign`/`.scatter`
-- combine a `List LHSSlot` traversal with `RHSExpr.traverseAxesWithMask`, conditional remap on
-- one hypothesis; `.recurMorphism` unconditional. `Stmt.uids` is public but built entirely from
-- `private` helpers Lean can't delta-reduce through even via the public wrapper — resolved by
-- adding `Stmt.uids_eq` plus six bridge lemmas to `Structural.lean` itself (marked
-- `SPIKE EXCEPTION`, revertible) — see
-- docs/superpowers/specs/2026-07-16-e1-traverseaxes-stmt-design.md.
-- Decl slice (flattest node in the series): no constructor wraps a nested AST type; remap is
-- FULLY UNCONDITIONAL. First slice calling `Traversable.traverse` directly on a bare
-- `List AxisSpec` (not through a node-level `traverseAxes`), surfacing that its own implicit
-- applicative parameter is named `m` not `f`, and that a direct `ConstL`-typed call needs an
-- explicit type ascription. No production-file change needed — `Decl` has no public wrapper
-- the way `Stmt.uids` did — see
-- docs/superpowers/specs/2026-07-17-e1-traverseaxes-decl-design.md.
-- TLProgram slice (FINAL — completes full AST coverage): combines a `List Decl` and a
-- `List Stmt` sub-traversal via `<$> ... <*>`; conditional remap on one `p.stmts` hypothesis
-- (`p.decls` needs none, `Decl`'s own remap is unconditional). At prototype time no named
-- `TLProgram.mapUID` existed, so the remap theorem targeted the `traverseUID` interface directly
-- (that interface and the prototype remap theorems were both retired in E1 sub-projects 3-4).
-- `TLProgram.axisNames` confirms the `Stmt.uids`-style privacy wall but
-- adds a `.eraseDups`/`.name`-projection step, scoped out as a non-goal — so no production-file
-- change was needed here either — see
-- docs/superpowers/specs/2026-07-17-e1-traverseaxes-tlprogram-design.md.
-- Production migration, sub-project 1 (2026-07-17): `ConstL` and all eleven
-- `NodeName.traverseAxes` definitions were promoted verbatim into
-- `LeanNCD/DSL/TraverseAxes.lean` and REMOVED from this file (they would otherwise conflict
-- with the now-identical production declarations, both in the `LeanNCD` namespace, once this
-- file's existing `import LeanNCD.DSL.Pipeline.Structural` transitively pulls in the new
-- production file). Every local `specsX'`/`*AxisUIDs'` comparison copy and every equivalence
-- theorem below is UNCHANGED — they now reference the production `traverseAxes` definitions
-- directly (verbatim-identical to what stood here before), not a local copy — see
-- docs/superpowers/specs/2026-07-17-e1-production-migration-specs-design.md.
import LeanNCD.DSL.Traverse
import LeanNCD.DSL.TraverseAxes
import LeanNCD.Eval.Contract
import LeanNCD.DSL.Pipeline.Structural
import Mathlib.Control.Traversable.Instances

namespace LeanNCD

/-- Local copy of `Structural.lean`'s private `specsIdx`, for comparison only — NOT the
    source of truth. Keep byte-identical to `Structural.lean:26-27` by inspection. -/
private def specsIdx' : IdxExpr → List AxisSpec
  | .axis a => [a] | .const _ => [] | .scale _ a => [a]
  | .shift a _ => [a] | .affine _ xs => xs.map (·.2)

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

/-- Local copy of `Structural.lean`'s private `specsPred`, for comparison only — NOT the
    source of truth. Keep byte-identical to `Structural.lean:30-31` by inspection. -/
private def specsPred' : PredArith → List AxisSpec
  | .embed e => specsIdx' e | .mul a b => specsPred' a ++ specsPred' b | .iabs a => specsPred' a

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

/-- Local copy of `Structural.lean`'s private `specsBool`, for comparison only — NOT the
    source of truth. Keep byte-identical to `Structural.lean:33-36` by inspection. -/
private def specsBool' : BoolExpr → List AxisSpec
  | .rel _ a b => specsPred' a ++ specsPred' b
  | .and a b => specsBool' a ++ specsBool' b | .or a b => specsBool' a ++ specsBool' b
  | .not a => specsBool' a | .ieq a b => specsPred' a ++ specsPred' b

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

/-- Local copy of `Structural.lean`'s private `specsFactor`, for comparison only — NOT the
    source of truth. Keep byte-identical to `Structural.lean:41-43` by inspection. -/
private def specsFactor' : Factor → List AxisSpec
  | .read _ es => es.flatMap specsIdx' | .iverson b => specsBool' b
  | .unaryFn _ _ es => es.flatMap specsIdx'

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

/-- Local copy of the inline `t.factors.flatMap specsFactor` fragment inside `Structural.lean`'s
    private `specsRHS` (`Structural.lean:45-46`), for comparison only — NOT the source of truth.
    No standalone `specsProdTerm` exists in production; keep this arm-for-arm identical to that
    fragment by inspection. -/
private def specsProdTerm' (t : ProdTerm) : List AxisSpec := t.factors.flatMap specsFactor'

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

/-- Local copy delegating to `specsProdTerm'` (the `ProdTerm` slice's own local copy), not
    re-derived through `specsFactor'` directly — mirrors `specsRHS`'s inline
    `r.body.terms.flatMap (fun t => t.factors.flatMap specsFactor)` fragment
    (`Structural.lean:45-46`) one layer at a time. -/
private def specsSumExpr' (s : SumExpr) : List AxisSpec := s.terms.flatMap specsProdTerm'

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

-- ===== Nonlin =====

/-- Independent hand-written reference for `Structural.lean`'s private `specsNonlin` — NOT the
    source of truth, and deliberately NOT defined as `= specsNonlin`/`Nonlin.traverseAxes` (that
    would make the theorem below tautological). The only axis specs a nonlinearity carries are
    those of an `.axiswise` mask; a production traversal that dropped the mask would fail here. -/
private def specsNonlin' : Nonlin → List AxisSpec
  | .axiswise _ (some m) => specsBool' m | _ => []

/-- Collect `AxisSpec`s: instantiating at `ConstL (List AxisSpec)` with `g := fun a => ⟨[a]⟩`
    should reproduce `specsNonlin'`. NO UID-collecting theorem exists for `Nonlin` — no
    production UID-collecting path ever touches the nonlin mask (see `RHSExpr`'s `NoMask`
    traversal in Task 2), so there is nothing to compare a UID-collecting theorem against. -/
theorem traverseAxes_const_eq_specsNonlin (n : Nonlin) :
    (Nonlin.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) n).run = specsNonlin' n := by
  cases n with
  | identity => rfl
  | pointwise pf => rfl
  | axiswise fn m =>
      cases m with
      | none => rfl
      | some b =>
          show (BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) b).run = specsBool' b
          exact traverseAxes_const_eq_specsBool b

-- ===== RHSExpr =====

/-- Local copy delegating to `specsSumExpr'` and `specsNonlin'` (both already-existing local
    copies), not re-derived through `specsFactor'`/`specsBool'` directly — mirrors production's
    private `specsRHS` (`Structural.lean:45-46`: `(r.body.terms.flatMap (fun t =>
    t.factors.flatMap specsFactor)) ++ specsNonlin r.nonlin`) one layer at a time. -/
private def specsRHS' (r : RHSExpr) : List AxisSpec := specsSumExpr' r.body ++ specsNonlin' r.nonlin

/-- Collect `AxisSpec`s (mask included): instantiating `traverseAxesWithMask` at
    `ConstL (List AxisSpec)` with `g := fun a => ⟨[a]⟩` should reproduce `specsRHS'`. -/
theorem traverseAxes_const_eq_specsRHS (r : RHSExpr) :
    (RHSExpr.traverseAxesWithMask (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r).run = specsRHS' r := by
  show (SumExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r.body).run ++
      (Nonlin.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r.nonlin).run
    = specsSumExpr' r.body ++ specsNonlin' r.nonlin
  rw [traverseAxes_const_eq_specsSumExpr r.body, traverseAxes_const_eq_specsNonlin r.nonlin]

-- ===== LHSSlot =====

/-- Local copy of `Structural.lean`'s private `specsLHS`, for comparison only — NOT the
    source of truth. Keep byte-identical to `Structural.lean:52-53` by inspection. Unlike
    `Nonlin`'s `specsNonlin`, this is already a clean, exhaustive match with no documented
    wildcard hazard. -/
private def specsLHS' : LHSSlot → List AxisSpec
  | .free a => [a] | .freeNorm a => [a]
  | .iterAt a _ => [a] | .iterNext a => [a] | .affine e => specsIdx' e

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

-- ===== Stmt =====

private def specsStmt' : Stmt → List AxisSpec
  | .assign _ ls r => ls.flatMap specsLHS' ++ specsRHS' r
  | .scatter _ ls r _ => ls.flatMap specsLHS' ++ specsRHS' r
  | .recurMorphism _ ax _ => [ax]

theorem traverseAxes_const_eq_specsStmt (s : Stmt) :
    (Stmt.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run = specsStmt' s := by
  have core : ∀ ys : List LHSSlot,
      (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ys).run
        = ys.flatMap specsLHS' := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) hd).run ++
            (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run
          = specsLHS' hd ++ tl.flatMap specsLHS'
        rw [traverseAxes_const_eq_specsLHS hd, ih]
  cases s with
  | assign nm ls r =>
      show (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ls).run ++
          (RHSExpr.traverseAxesWithMask (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r).run
        = ls.flatMap specsLHS' ++ specsRHS' r
      rw [core ls, traverseAxes_const_eq_specsRHS r]
  | scatter nm ls r o =>
      show (Traversable.traverse (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ls).run ++
          (RHSExpr.traverseAxesWithMask (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r).run
        = ls.flatMap specsLHS' ++ specsRHS' r
      rw [core ls, traverseAxes_const_eq_specsRHS r]
  | recurMorphism nm ax tc => rfl

-- ===== Decl =====

/-- Local copy of `Structural.lean`'s private `specsDecl`, for comparison only — NOT the
    source of truth. Keep byte-identical to `Structural.lean:64-66` by inspection. -/
private def specsDecl' : Decl → List AxisSpec
  | .tensor _ ax => ax | .predicate _ ax => ax | .linear _ ax _ => ax
  | .axis ax _ => [ax]

/-- Collect `AxisSpec`s: instantiating at `ConstL (List AxisSpec)` with `g := fun a => ⟨[a]⟩`
    should reproduce `specsDecl'`. The `core` lemma calls `Traversable.traverse` DIRECTLY on a
    `List AxisSpec` (not through a node-level `traverseAxes` wrapper, unlike every prior list
    traversal in this file) — the explicit `ConstL (List AxisSpec) AxisSpec` type ascription on
    the lambda is required because `ConstL` ignores its second type parameter, so Lean cannot
    infer the target element type from `⟨[a]⟩` alone. -/
theorem traverseAxes_const_eq_specsDecl (d : Decl) :
    (Decl.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) d).run = specsDecl' d := by
  have core : ∀ ys : List AxisSpec,
      (Traversable.traverse (fun a => (⟨[a]⟩ : ConstL (List AxisSpec) AxisSpec)) ys).run = ys := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show [hd] ++ (Traversable.traverse (fun a => (⟨[a]⟩ : ConstL (List AxisSpec) AxisSpec)) tl).run = hd :: tl
        rw [ih]
        rfl
  cases d with
  | tensor nm ax => exact core ax
  | predicate nm ax => exact core ax
  | linear nm ax b => exact core ax
  | axis ax n => rfl

-- ===== TLProgram =====

/-- Local copy built from the already-proven `specsDecl'`/`specsStmt'`, mirroring production's
    private `TLProgram.axisSpecs` (`Structural.lean:74-75`: `p.decls.flatMap specsDecl ++
    p.stmts.flatMap specsStmt`) one layer removed — NOT the source of truth. -/
private def specsProgram' (p : TLProgram) : List AxisSpec :=
  p.decls.flatMap specsDecl' ++ p.stmts.flatMap specsStmt'

/-- Collect `AxisSpec`s: instantiating at `ConstL (List AxisSpec)` with `g := fun a => ⟨[a]⟩`
    should reproduce `specsProgram'`. Two independent `core` induction lemmas — one folding
    `Decl.traverseAxes` over `p.decls` via the already-proven `traverseAxes_const_eq_specsDecl`,
    one folding `Stmt.traverseAxes` over `p.stmts` via the already-proven
    `traverseAxes_const_eq_specsStmt` — then combined. -/
theorem traverseAxes_const_eq_specsProgram (p : TLProgram) :
    (TLProgram.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) p).run = specsProgram' p := by
  have coreD : ∀ ds : List Decl,
      (Traversable.traverse (Decl.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ds).run
        = ds.flatMap specsDecl' := by
    intro ds
    induction ds with
    | nil => rfl
    | cons hd tl ih =>
        show (Decl.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) hd).run ++
            (Traversable.traverse (Decl.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run
          = specsDecl' hd ++ tl.flatMap specsDecl'
        rw [traverseAxes_const_eq_specsDecl hd, ih]
  have coreS : ∀ ss : List Stmt,
      (Traversable.traverse (Stmt.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) ss).run
        = ss.flatMap specsStmt' := by
    intro ss
    induction ss with
    | nil => rfl
    | cons hd tl ih =>
        show (Stmt.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) hd).run ++
            (Traversable.traverse (Stmt.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) tl).run
          = specsStmt' hd ++ tl.flatMap specsStmt'
        rw [traverseAxes_const_eq_specsStmt hd, ih]
  show (Traversable.traverse (Decl.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) p.decls).run ++
      (Traversable.traverse (Stmt.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) p.stmts).run
    = p.decls.flatMap specsDecl' ++ p.stmts.flatMap specsStmt'
  rw [coreD p.decls, coreS p.stmts]

end LeanNCD

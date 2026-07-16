# E1 — `traverseAxes` Prototype (BoolExpr slice) — Design

**Status:** approved 2026-07-15. Feeds `writing-plans`.

## Goal

Extend the E1 prototype (`test/DSL/TraverseAxesSpike.lean`, on branch
`worktree-e1-traverseaxes-prototype`, PR
[william-macready/pyncd#1](https://github.com/william-macready/pyncd/pull/1)) to `BoolExpr` —
completing the non-mutual, layered part of the AST below `Factor` (`IdxExpr` → `PredArith` →
`BoolExpr`).

**This slice introduces no new risk pattern**, unlike the `IdxExpr` → `PredArith` step (which
tested self-recursion and `<*>` for the first time). `BoolExpr.traverseAxes` is the same
self-recursive-`<*>`-plus-delegation shape as `PredArith.traverseAxes`, just with more
constructors (5 vs 3) and one more layer of composition (delegating to `PredArith.traverseAxes`
instead of `IdxExpr.traverseAxes`). It is a scaling/confirmation check, not a fresh experiment.

**Known prediction going in, not a fresh discovery if it recurs:** `BoolExpr.mapUID`
(`Traverse.lean`) is, like `PredArith.mapUID`, a `partial def` with genuine self-recursion
(`.and`/`.or`/`.not` call it again). The `PredArith` slice established that Lean generates zero
equation lemmas for such definitions — even non-recursive cases become unprovable. `BoolExpr`'s
remap theorem is expected to hit the identical wall for the identical reason.

## Scope

**In:** `BoolExpr.traverseAxes` (all 5 constructors: `.rel`, `.and`, `.or`, `.not`, `.ieq`); a
local `specsBool'` comparison copy (`specsBool` is `private` in `Structural.lean:33-36`);
collecting-direction theorems against `specsBool'` and `boolAxisUIDs` (public,
`Eval/Contract.lean:21-26`); a single quick confirming check on the remap theorem (not a
multi-attempt search — see "Effort policy" below).

**Out:** `Factor`/`LHSSlot`/`Stmt`/`Decl`/`TLProgram`. `Factor.iverson` wraps `BoolExpr`, but
`Factor` is a separate, larger node with its own new risk (the first type with a `.read`/
`.unaryFn` case carrying tensor names + index lists, not just bare axis occurrences) — deferred
to its own future slice. No production files touched.

## Effort policy for the remap theorem

Unlike the exploratory, up-to-6–8-attempt policy used for `PredArith`'s theorems (where the
outcome was genuinely unknown), `BoolExpr`'s remap theorem is now a **confirmation**, not an
open question: the mechanism (`partial def` + genuine self-recursion ⇒ zero equation lemmas,
even on non-recursive cases) is already established and understood. One fast check — attempt
`rfl` on the isolated `.rel` case (`BoolExpr.mapUID f (BoolExpr.rel op a b) = BoolExpr.rel op
(PredArith.mapUID f a) (PredArith.mapUID f b)`), or check whether `BoolExpr.mapUID.eq_1`
resolves — suffices. If it fails as predicted, comment the theorem out citing the `PredArith`
slice's finding; do not spend further search effort re-discovering the same wall.

## The traversal

```lean
private def specsBool' : BoolExpr → List AxisSpec
  | .rel _ a b => specsPred' a ++ specsPred' b
  | .and a b => specsBool' a ++ specsBool' b | .or a b => specsBool' a ++ specsBool' b
  | .not a => specsBool' a | .ieq a b => specsPred' a ++ specsPred' b

def BoolExpr.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : BoolExpr → f BoolExpr
  | .rel op a b => BoolExpr.rel op <$> PredArith.traverseAxes g a <*> PredArith.traverseAxes g b
  | .and a b    => BoolExpr.and <$> BoolExpr.traverseAxes g a <*> BoolExpr.traverseAxes g b
  | .or a b     => BoolExpr.or <$> BoolExpr.traverseAxes g a <*> BoolExpr.traverseAxes g b
  | .not a      => BoolExpr.not <$> BoolExpr.traverseAxes g a
  | .ieq a b    => BoolExpr.ieq <$> PredArith.traverseAxes g a <*> PredArith.traverseAxes g b
```

## Instantiations and equivalence theorems

```lean
theorem traverseAxes_const_eq_specsBool (e : BoolExpr) :
    (BoolExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run = specsBool' e

theorem traverseAxes_const_eq_boolAxisUIDs (e : BoolExpr) :
    (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run = boolAxisUIDs e
```

Two distinct proof shapes, both already validated by the `PredArith` slice:
- **`.and`/`.or`/`.not`** — genuine self-recursion (like `PredArith.mul`/`.iabs`): `show`+
  `rw [iha, ihb]` (or `iha` alone) using real induction hypotheses from `induction e`.
- **`.rel`/`.ieq`** — leaf composition of two `PredArith` sub-terms, not `BoolExpr`
  self-recursion (like `PredArith.embed`'s delegation to `IdxExpr`'s proven lemma): `show`+`rw`
  using the two already-proven `traverseAxes_const_eq_specsPred`/`traverseAxes_const_eq_predAxisUIDs`
  calls on the two `PredArith` arguments directly — no fresh induction needed for these cases.

The remap theorem (`traverseAxes_id_eq_boolMapUID`), attempted per the effort policy above,
expected to be commented out.

## File layout

- `test/DSL/TraverseAxesSpike.lean` (extend, not new) — append after the `PredArith` content.
  Already registered in `lakefile.toml`'s `Tests` globs — no new registration needed.

## Success criteria (the go/no-go bar)

**Go** (confirms the pattern generalizes across the full non-mutual layered stack):
- Both collecting-direction theorems close with genuinely sound proofs.
- The `.rel`/`.ieq` delegation to already-proven `PredArith` lemmas composes cleanly (no
  re-proving `PredArith`'s equivalence from scratch inside `BoolExpr`'s proofs).

**No-go** (would be a genuine surprise, not the predicted outcome):
- Structural fighting on `.and`/`.or`/`.not` (the same `<*>` pattern that already worked for
  `PredArith.mul`) — would suggest something about `BoolExpr`'s specific shape, not just
  self-recursion in general, is the problem.

**Not re-litigated:** the remap theorem's expected failure. A single confirming check, not an
open question.

## Risks / notes

- Same maintenance hazard as the prior slices' comparison copies: `specsBool'` must stay
  byte-identical to `Structural.lean:33-36`'s private `specsBool` by inspection.
- If the quick remap check unexpectedly *succeeds* (contrary to the prediction), that is itself
  a genuinely interesting finding worth a closer look — it would mean something about
  `BoolExpr.mapUID`'s specific compilation differs from `PredArith.mapUID`'s despite both being
  `partial def` with self-recursion, which would be worth understanding before concluding
  anything about `Factor`/`Stmt`'s own `mapUID` functions (also `partial`, not yet examined for
  self-recursion structure).

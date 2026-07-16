# E1 — `traverseAxes` Prototype (SumExpr slice) — Design

**Status:** approved 2026-07-16. Feeds `writing-plans`.

## Goal

Extend the E1 prototype (`test/DSL/TraverseAxesSpike.lean`, on branch
`worktree-e1-traverseaxes-prototype`, PR
[william-macready/pyncd#1](https://github.com/william-macready/pyncd/pull/1)) to `SumExpr` —
structurally identical to `ProdTerm` one layer up (`structure SumExpr where terms : List
ProdTerm`, versus `ProdTerm`'s `structure ProdTerm where factors : List Factor`). The `ProdTerm`
design doc predicted this slice would be "a near-mechanical repeat, not a fresh design
question" if `ProdTerm`'s conditional-lemma resolution worked cleanly — it did (reviewed clean,
"Ready to merge: Yes"), and this slice **confirms that prediction empirically**: every theorem
below was staged into the real codebase and built successfully during design, closing on the
first attempt with the exact same tactic sequences `ProdTerm`'s proofs used, substituting
`ProdTerm`/`ProdTerm.mapUID`/`ProdTerm.traverseAxes` for `Factor`'s equivalents throughout.

## Scope

**In:** `SumExpr.traverseAxes` (single-field composition, identical shape to
`ProdTerm.traverseAxes`); a local `specsSumExpr'` comparison copy defined as `s.terms.flatMap
specsProdTerm'` — reusing `ProdTerm`'s own local copy from the prior slice rather than
re-deriving through `Factor` a second time; two collecting-direction theorems — one against
`specsSumExpr'`, one against the bare expression `s.terms.flatMap termAxisUIDs` directly (decided
during scoping: no redundant named wrapper def, since `termAxisUIDs` is already real and
public — the theorem's RHS is simply that expression, not a call to some new
`sumExprAxisUIDs'`); one conditional remap lemma,
`traverseAxes_id_eq_sumExprMapUID_of_terms`, taking a hypothesis that every `ProdTerm` in
`s.terms` satisfies its own remap equality.

**Out:** `RHSExpr`/`LHSSlot`/`Stmt`/`Decl`/`TLProgram` — deferred to their own future slices.
No production files touched.

**One deliberate stylistic departure from every prior slice, decided during scoping:** the
UID-collecting theorem's RHS is a bare expression (`s.terms.flatMap termAxisUIDs`), not a named
function call. Every other collecting-direction theorem in the file (including `SumExpr`'s own
`specsSumExpr'` theorem two lines above it) compares against either a real production function
or a locally-defined comparison copy. This is a one-off exception, made because there is
genuinely no `SumExpr`-level named function in production to either copy or point at —
`readAxisUIDs` (`Eval/Contract.lean:43-44`) is built from exactly this expression but operates
on `RHSExpr`, one layer up, not `SumExpr` directly, and adding a `sumExprAxisUIDs'` def that
does nothing but restate `s.terms.flatMap termAxisUIDs` under a new name was judged not worth
the indirection.

## The traversal

```lean
def SumExpr.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) (s : SumExpr) : f SumExpr :=
  (fun ts => { terms := ts }) <$> Traversable.traverse (ProdTerm.traverseAxes g) s.terms
```

Identical in shape to `ProdTerm.traverseAxes` — one field, one line of composition, no
`cases`/`induction` on `SumExpr` needed.

## Instantiations and equivalence theorems

```lean
private def specsSumExpr' (s : SumExpr) : List AxisSpec := s.terms.flatMap specsProdTerm'

theorem traverseAxes_const_eq_specsSumExpr (s : SumExpr) :
    (SumExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run = specsSumExpr' s

theorem traverseAxes_const_eq_termAxisUIDsSumExpr (s : SumExpr) :
    (SumExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) s).run
      = s.terms.flatMap termAxisUIDs

theorem traverseAxes_id_eq_sumExprMapUID_of_terms (f : UData → UData) (s : SumExpr)
    (h : ∀ x ∈ s.terms, ProdTerm.traverseAxes (f := Id) (AxisSpec.mapUID f) x = ProdTerm.mapUID f x) :
    SumExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) s = SumExpr.mapUID f s
```

All three proofs are the `ProdTerm` slice's own proofs with `Factor`/`ProdTerm.mapUID`/etc.
mechanically substituted by `ProdTerm`/`SumExpr.mapUID`/etc. — same `show`+`have core`+induction
skeleton for the two collecting theorems (reusing `ProdTerm`'s already-proven collecting
theorems per element via `rw`), same `simp only [List.traverse_cons]` + `rw [hys hd
List.mem_cons_self, ih (fun x hx => hys x (List.mem_cons_of_mem hd hx))]` + `rfl` skeleton for
the conditional remap.

**This exact code has been verified end-to-end during design** (not just sketched by analogy) —
staged into the real `test/DSL/TraverseAxesSpike.lean`, built via `lake build
DSL.TraverseAxesSpike` and a full `lake build` (both green, 8609 jobs for the full build), then
reverted before writing this doc.

## Effort policy

None needed — all three theorems are pre-verified to close exactly as written. The
implementation task is transcription plus confirmation, not proof search.

## File layout

- `test/DSL/TraverseAxesSpike.lean` (extend, not new) — append after the `ProdTerm` section.
  Already registered in `lakefile.toml`'s `Tests` globs — no new registration needed.

## Success criteria (the go/no-go bar)

**Go:** all three theorems close exactly as pre-verified (already confirmed during design).

**No-go / interesting either way:** none anticipated — if the implementer's environment somehow
produces a different result than the pre-verification, that would itself be the finding (a
drift between design-time and implementation-time state), not a proof-search failure.

## Risks / notes

- `specsSumExpr'` must stay consistent with `specsProdTerm'` (which it delegates to, rather than
  re-deriving through `specsFactor'`) — if `specsProdTerm'` is ever changed, `specsSumExpr'`
  inherits that change for free, which is the intended DRY behavior, not a hazard.
- The bare-expression choice for the UID-collecting theorem (see Scope) is a precedent that a
  future slice might want to reconsider if it turns out to read poorly at scale — noted here so
  it isn't mistaken for an oversight later.
- This slice empirically confirms the `ProdTerm` design doc's prediction that the
  conditional-lemma pattern generalizes mechanically across identically-shaped
  record-wrapping-a-list nodes. `RHSExpr` (the next node up) is NOT identically shaped — it has
  three fields (`body : SumExpr`, `nonlin : Nonlin`, `agg : AggOp`), not one — so this same
  mechanical-repeat expectation should not be assumed for it without re-checking.

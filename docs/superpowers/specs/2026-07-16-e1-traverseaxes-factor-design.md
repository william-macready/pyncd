# E1 — `traverseAxes` Prototype (Factor slice) — Design

**Status:** approved 2026-07-16. Feeds `writing-plans`.

## Goal

Extend the E1 prototype (`test/DSL/TraverseAxesSpike.lean`, on branch
`worktree-e1-traverseaxes-prototype`, PR
[william-macready/pyncd#1](https://github.com/william-macready/pyncd/pull/1)) to `Factor` —
the node above `IdxExpr`/`PredArith`/`BoolExpr`, and the first to introduce a genuinely new
risk pattern rather than confirm the previous one.

**What's new here, unlike the BoolExpr slice (which was pure confirmation):** `Factor`'s
`.read`/`.unaryFn` cases carry a `String` tensor name (and, for `.unaryFn`, a `UnaryOp`) that
must pass through the traversal untouched, plus a `List IdxExpr` that needs a *traverse of
sub-traversals* — each list element gets its own full `IdxExpr.traverseAxes g` call, not a
bare per-element projection like `.affine`'s `List (Int × AxisSpec)` in the `IdxExpr` slice.
This is one layer of composition deeper than anything proved so far.

**What's expected to go differently on the remap side:** `Factor.mapUID`
(`DSL/Traverse.lean:47-50`) is a plain, non-`partial` `def` with no self-recursion (its cases
only delegate to `IdxExpr.mapUID`/`BoolExpr.mapUID`) — unlike `PredArith`/`BoolExpr.mapUID`,
which are `partial def` with genuine self-recursion and generate no equation lemmas. The
remap-direction theorem is attempted for real this time (full effort, not a quick
confirm-or-bail check), since the mechanism that blocked it twice does not apply here.

## Scope

**In:** `Factor.traverseAxes` (all 3 constructors: `.read`, `.iverson`, `.unaryFn`); a local
`specsFactor'` comparison copy (byte-identical to the private `specsFactor`,
`Structural.lean:41-43`); a local `factorAxisUIDs'` comparison copy — this one differs from
every prior local copy: there is no standalone `Factor → List UID` function in production
code today, only an inline match embedded inside `termAxisUIDs` (`Eval/Contract.lean:34-38`).
`factorAxisUIDs'` extracts that inline match into a standalone function purely for comparison
(it is not a copy of an existing named def, and must be flagged as such in its docstring so a
future reader doesn't go looking for a `factorAxisUIDs` in production and fail to find it).
Two collecting-direction theorems against `specsFactor'`/`factorAxisUIDs'`. One remap-direction
theorem against `Factor.mapUID`, attempted for real.

**Out:** `ProdTerm`/`SumExpr`/`RHSExpr`/`LHSSlot`/`Decl`/`Stmt`/`TLProgram` — deferred to their
own future slices, same granularity as the prior three. No production files touched.

## The traversal

```lean
def Factor.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : Factor → f Factor
  | .read nm es       => Factor.read nm <$> Traversable.traverse (IdxExpr.traverseAxes g) es
  | .iverson b        => Factor.iverson <$> BoolExpr.traverseAxes g b
  | .unaryFn op nm es => Factor.unaryFn op nm <$> Traversable.traverse (IdxExpr.traverseAxes g) es
```

`Traversable.traverse (IdxExpr.traverseAxes g) es` traverses the `List IdxExpr` using
`IdxExpr.traverseAxes g : IdxExpr → f IdxExpr` as the per-element action — a traverse whose
per-element action is itself a full sub-traversal (already proven, in both directions except
where blocked, at the `IdxExpr` level), rather than a direct call to `g`. `nm` (and `op`) are
carried through as plain arguments outside the `<$>`/`<*>` chain — the first case in this
prototype where a field must provably NOT be touched by the traversal.

## Instantiations and equivalence theorems

```lean
private def specsFactor' : Factor → List AxisSpec
  | .read _ es => es.flatMap specsIdx' | .iverson b => specsBool' b
  | .unaryFn _ _ es => es.flatMap specsIdx'

/-- Extracted from the inline match inside `termAxisUIDs` (`Eval/Contract.lean:34-38`) — NOT
    a copy of an existing standalone function; none exists in production. -/
private def factorAxisUIDs' : Factor → List UID
  | .read _ es => es.flatMap idxAxisUIDs | .iverson b => boolAxisUIDs b
  | .unaryFn _ _ es => es.flatMap idxAxisUIDs

theorem traverseAxes_const_eq_specsFactor (e : Factor) :
    (Factor.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) e).run = specsFactor' e

theorem traverseAxes_const_eq_factorAxisUIDs (e : Factor) :
    (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run = factorAxisUIDs' e

theorem traverseAxes_id_eq_factorMapUID (f : UData → UData) (e : Factor) :
    Factor.traverseAxes (f := Id) (AxisSpec.mapUID f) e = Factor.mapUID f e
```

**Collecting direction.** `.iverson` delegates directly to the already-proven `BoolExpr`
lemmas (`traverseAxes_const_eq_specsBool`/`traverseAxes_const_eq_boolAxisUIDs`) — no new proof
work. `.read`/`.unaryFn` need one new list-induction lemma per target (`AxisSpec`/`UID`)
showing that traversing `List IdxExpr` with `IdxExpr.traverseAxes g` at a `ConstL` applicative
collapses to `es.flatMap` of the already-proven `IdxExpr`-level equality — the same induction
shape as the `core` lemmas already proved for `.affine`'s `List (Int × AxisSpec)` in the
`IdxExpr` slice, but composing with a per-element *theorem* (`traverseAxes_const_eq_specsIdx`)
rather than a bare `⟨[a]⟩`-style projection. Concretely: prove
`∀ ys : List IdxExpr, (Traversable.traverse (IdxExpr.traverseAxes (f:=ConstL _) g) ys).run =
ys.flatMap (fun e => (IdxExpr.traverseAxes (f:=ConstL _) g e).run)` by list induction using
`ih`, then specialize the inner term via the already-proven `IdxExpr` theorem.

**Remap direction.** The same list-layer lemma is needed at `Id`:
`Traversable.traverse (IdxExpr.traverseAxes (f:=Id) (AxisSpec.mapUID f)) es = es.map
(IdxExpr.mapUID f)`, obtained by combining `List.traverse_eq_map_id` (used already in the
`IdxExpr` slice's own remap proof) with the already-proven `traverseAxes_id_eq_mapUID`
pointwise inside the list. This is the one genuinely new proof-engineering step in this
slice — no prior slice's remap attempt got far enough to need a list-layer composition,
since both were blocked by the `partial`/self-recursion wall before reaching it.

## Effort policy

Full attempt on the remap theorem, per the reasoning above (`Factor.mapUID` is non-`partial`
and non-self-recursive, so the blocking mechanism from the `PredArith`/`BoolExpr` slices does
not apply). If it still doesn't close after a reasonable attempt (the `List.traverse_eq_map_id`
+ pointwise-remap composition sketched above, plus the standard `cases`/`show`/`rw` idiom used
throughout this file), that is itself a new finding — not a predicted outcome — and should be
recorded as such rather than silently commented out like the prior two "expected failure"
cases.

## File layout

- `test/DSL/TraverseAxesSpike.lean` (extend, not new) — append after the `BoolExpr` section.
  Already registered in `lakefile.toml`'s `Tests` globs — no new registration needed.

## Success criteria (the go/no-go bar)

**Go:**
- Both collecting-direction theorems close with genuinely sound proofs, including the new
  list-of-sub-traversal lemma.
- `.iverson`'s delegation to the already-proven `BoolExpr` lemmas composes cleanly with no
  re-proving.
- The remap theorem closes (the hoped-for outcome, not merely the historical pattern).

**No-go / interesting either way:**
- If the list-of-sub-traversal collecting lemma needs real structural fighting beyond the
  induction shape above, that's a signal `Factor`'s composition (rather than self-recursion)
  is its own source of friction — worth a closer look before extrapolating to `ProdTerm`/`Stmt`.
- If the remap theorem does NOT close despite `Factor.mapUID` being non-`partial`, that
  contradicts the stated mechanism and should be understood (not just documented as "blocked
  again") before scoping `Stmt`'s own `mapUID` (also worth checking for `partial`/self-recursion
  before assuming its remap direction will behave like `Factor`'s).

## Risks / notes

- `specsFactor'` must stay byte-identical to `Structural.lean:41-43`'s private `specsFactor` by
  inspection, same maintenance hazard as the prior slices' comparison copies.
- `factorAxisUIDs'` has no production def to mirror byte-for-byte — it must be checked instead
  against the *inline* match inside `termAxisUIDs` (`Eval/Contract.lean:34-38`) for the same
  three-arm shape, and its docstring must say plainly that it's an extraction, not a copy, so a
  future reader doesn't search for a nonexistent `factorAxisUIDs` in production.

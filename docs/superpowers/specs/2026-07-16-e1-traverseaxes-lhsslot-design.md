# E1 — `traverseAxes` Prototype (LHSSlot slice) — Design

**Status:** approved 2026-07-16. Feeds `writing-plans`.

## Goal

Extend the E1 prototype (`test/DSL/TraverseAxesSpike.lean`, on branch
`worktree-e1-traverseaxes-prototype`, PR
[william-macready/pyncd#1](https://github.com/william-macready/pyncd/pull/1)) to `LHSSlot`.
Per the checkpoint's own explicit warning not to assume this node's shape without checking,
its actual definition was read before scoping: `inductive LHSSlot | free : AxisSpec → LHSSlot
| freeNorm : AxisSpec → LHSSlot | iterAt : AxisSpec → Int → LHSSlot | iterNext : AxisSpec →
LHSSlot | affine : IdxExpr → LHSSlot` (`DSL/Ast.lean:103-109`) — 5 constructors, 4 wrapping a
bare `AxisSpec` directly, one (`.affine`) wrapping an `IdxExpr`.

## Findings from checking production before assuming anything

**Good news: remap should be, and empirically was verified to be, fully unconditional for all
5 constructors** — the first time since `IdxExpr` itself. Every slice from `PredArith` onward
needed a conditional or partially-blocked remap theorem because something downstream touched
`BoolExpr` (whose `mapUID` is `partial def` with self-recursion, generating zero equation
lemmas). `LHSSlot.mapUID` (`DSL/Traverse.lean:59-64`) is non-partial and flat — its only
non-trivial dependency is `.affine`'s `IdxExpr.mapUID`, and `IdxExpr`'s own remap
(`traverseAxes_id_eq_mapUID`) is already fully, unconditionally proven (it was the very first
slice, and never touches `BoolExpr`). This was verified directly: the full theorem was staged
into the real codebase and closed on the first attempt, no hypothesis needed anywhere.

**A real scoping finding: `lhsAxisUID?`/`freeAxisUIDs` are out of scope, and not for the usual
reason.** Production's `specsLHS` (`Structural.lean:52-53`, private: `| .free a => [a] |
.freeNorm a => [a] | .iterAt a _ => [a] | .iterNext a => [a] | .affine e => specsIdx e`) is a
genuine axis-collector matching the natural traversal's semantics exactly — it recurses fully
into `.affine`'s `IdxExpr`, same as the traversal does. But the other LHSSlot-level production
function, `lhsAxisUID? : LHSSlot → Option UID` (`Eval/Shape.lean:501-506`: `.free a => some
a.uid | .freeNorm a => some a.uid | .iterAt a _ => some a.uid | .iterNext a => some a.uid |
.affine _ => none`), used by `freeAxisUIDs (slots : List LHSSlot) : List UID := slots.filterMap
lhsAxisUID?` (`Eval/Contract.lean:29`) to build an assignment's free-axis list, is **not a
collector at all** — it's a per-slot classifier ("does this slot correspond to a single
distinguished free axis, and which one"). Its answer for `.affine` is `none` (drop the slot
entirely from the free-axis list) — not "the axes referenced inside its `IdxExpr`," which is
what any instantiation of a uniform `LHSSlot.traverseAxes(g)` would naturally produce instead
(matching `specsLHS`, not `lhsAxisUID?`). No instantiation of one traversal can reproduce both
functions, because they disagree on what `.affine` contributes — not an applicative-instantiation
difference (like `RHSExpr`'s mask asymmetry was), but a genuine difference in what counts as
"this slot's axes" at all. This is a different function *shape* (classify-and-filter, not
fold), not a missing production counterpart — worth recording as a deliberate non-goal rather
than silently produced or silently skipped.

## Scope

**In:** `LHSSlot.traverseAxes` (5-arm match); a local `specsLHS'` comparison copy (byte-identical
to production's private `specsLHS`, which — unlike `Nonlin`'s wildcard — is already a clean,
exhaustive match with no documented hazard); one collecting-direction theorem against it; one
FULLY UNCONDITIONAL remap theorem covering all 5 constructors.

**Out:** `lhsAxisUID?`/`freeAxisUIDs` (see finding above — a different function shape, not
reproducible by any `traverseAxes` instantiation). `Stmt`/`Decl`/`TLProgram` — deferred to
their own future slices. No production files touched.

## The traversal

```lean
def LHSSlot.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : LHSSlot → f LHSSlot
  | .free a     => LHSSlot.free <$> g a
  | .freeNorm a => LHSSlot.freeNorm <$> g a
  | .iterAt a n => (fun a' => LHSSlot.iterAt a' n) <$> g a
  | .iterNext a => LHSSlot.iterNext <$> g a
  | .affine e   => LHSSlot.affine <$> IdxExpr.traverseAxes g e
```

The simplest traversal shape in the series so far: 4 of 5 arms apply `g` directly to a bare
`AxisSpec` (no sub-traversal at all — `IdxExpr`/`BoolExpr`/etc. never appear), and the fifth
delegates entirely to `IdxExpr.traverseAxes`, already fully proven in both directions.

## Instantiations and equivalence theorems

```lean
private def specsLHS' : LHSSlot → List AxisSpec
  | .free a => [a] | .freeNorm a => [a]
  | .iterAt a _ => [a] | .iterNext a => [a] | .affine e => specsIdx' e

theorem traverseAxes_const_eq_specsLHS (s : LHSSlot) :
    (LHSSlot.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run = specsLHS' s

theorem traverseAxes_id_eq_lhsSlotMapUID (f : UData → UData) (s : LHSSlot) :
    LHSSlot.traverseAxes (f := Id) (AxisSpec.mapUID f) s = LHSSlot.mapUID f s
```

**Collecting direction:** four arms close by plain `rfl` (a single `g`/`⟨[a]⟩` application, no
induction, no sub-traversal); `.affine` delegates directly to the already-proven
`traverseAxes_const_eq_specsIdx`.

**Remap direction:** the same four arms close by plain `rfl`; `.affine` delegates directly to
the already-proven, fully unconditional `traverseAxes_id_eq_mapUID`. No hypothesis, no
conditional lemma, no induction anywhere in this slice — the cleanest slice since `IdxExpr`.

**This exact code has already been verified to close, end-to-end, via a standalone staged
build during design** (not just sketched) — `lake build DSL.TraverseAxesSpike` and a full
`lake build` both succeeded (8609 jobs), then reverted before writing this doc.

## Effort policy

None needed — every theorem above is pre-verified to close exactly as written.

## File layout

- `test/DSL/TraverseAxesSpike.lean` (extend, not new) — append after the `RHSExpr` section.
  Already registered in `lakefile.toml`'s `Tests` globs — no new registration needed.

## Success criteria (the go/no-go bar)

**Go:** both theorems close exactly as pre-verified (already confirmed during design).

**No-go / interesting either way:** none anticipated for the code itself. The
`lhsAxisUID?`/`freeAxisUIDs` non-goal finding is itself the interesting result of this slice —
worth carrying forward explicitly when `Stmt` is scoped next, since `Stmt` is the node that
actually consumes `LHSSlot` lists and may have its own version of this "collector vs.
classifier" distinction to navigate.

## Risks / notes

- `specsLHS'` must stay byte-identical to `Structural.lean:52-53`'s private `specsLHS` by
  inspection — same maintenance hazard as every prior local copy.
- The `lhsAxisUID?` non-goal is worth stating plainly in the checkpoint/blockquote so a future
  reader doesn't wonder why no UID-collecting theorem exists for `LHSSlot` (same courtesy
  `Nonlin`'s slice extended for its own, differently-reasoned omission).
- `Stmt` (the next node up, wrapping `List LHSSlot` among other fields) has not been examined
  for its own risk shape — per the discipline established by `RHSExpr`'s own surprise, it
  should get the same "check before assuming" treatment, not an assumed continuation of this
  slice's pleasant simplicity.

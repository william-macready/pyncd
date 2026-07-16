# E1 — `traverseAxes` Prototype (ProdTerm slice) — Design

**Status:** approved 2026-07-16. Feeds `writing-plans`.

## Goal

Extend the E1 prototype (`test/DSL/TraverseAxesSpike.lean`, on branch
`worktree-e1-traverseaxes-prototype`, PR
[william-macready/pyncd#1](https://github.com/william-macready/pyncd/pull/1)) to `ProdTerm` —
the node above `Factor`, and the first non-inductive (record) type in the series.

**What's new here:** `ProdTerm` (`structure ProdTerm where factors : List Factor`) has a single
field, so its traversal needs no `cases`/`induction` on `ProdTerm` itself — the whole
definition is one line of composition. That simplicity surfaces a genuinely new problem on the
remap side: `ProdTerm.mapUID` (`DSL/Traverse.lean:52-53`) only calls `Factor.mapUID` over the
list, so an *unconditional* remap theorem (`∀ p : ProdTerm, ProdTerm.traverseAxes (f:=Id) g p =
ProdTerm.mapUID f p`) would need `Factor.traverseAxes (f:=Id) g x = Factor.mapUID f x` to hold
for *every* `x` in `p.factors` — including any `.iverson` factors, whose remap the `Factor`
slice already found blocked. Unlike `Factor`, where the block was cleanly per-constructor (two
theorems proved, one skipped), here the block is per-*list-element*: a `ProdTerm` can mix
`.read`/`.unaryFn`/`.iverson` factors freely, so there's no type-level split into a provable arm
and a blocked one. A single `.iverson` anywhere in the list sinks the equality for that
`ProdTerm`. This is the same `partial def`/zero-equation-lemmas wall as `PredArith`/`BoolExpr`,
reappearing through a `List` rather than through inductive case-splitting — not a fresh wall,
but a new manifestation of it.

**Resolution (decided during scoping):** rather than attempting an unconditional theorem (which
cannot close) or skipping the remap direction entirely (which proves nothing new), state a
**conditional lemma**: if every factor in `p.factors` individually satisfies its own remap
equality, the `ProdTerm`-level equality follows. This is a genuine theorem — it demonstrates the
traversal encoding composes correctly over `List` in the remap direction — without claiming
something false for the fully general case.

## Scope

**In:** `ProdTerm.traverseAxes` (the single-field composition); a local `specsProdTerm'`
comparison copy extracted from the inline `t.factors.flatMap specsFactor` fragment inside
`specsRHS` (`Structural.lean:45-46` — no standalone `specsProdTerm` exists in production, same
situation as `Factor`'s `factorAxisUIDs'`); two collecting-direction theorems — one against
`specsProdTerm'`, and one against the **real production `termAxisUIDs`**
(`Eval/Contract.lean:34-38`) directly. This is the first slice where the UID-collecting
comparison target is an actual public production function rather than a local copy or
extraction — `termAxisUIDs` already *is* "collect UIDs from a `ProdTerm`," so no local copy is
needed for that direction. One conditional remap lemma,
`traverseAxes_id_eq_prodTermMapUID_of_factors`.

**Out:** `SumExpr`/`RHSExpr`/`LHSSlot`/`Decl`/`Stmt`/`TLProgram` — deferred to their own future
slices, same granularity as before. No production files touched.

## The traversal

```lean
def ProdTerm.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) (p : ProdTerm) : f ProdTerm :=
  (fun fs => { factors := fs }) <$> Traversable.traverse (Factor.traverseAxes g) p.factors
```

No case-split: `ProdTerm` has exactly one constructor (an implicit record `mk`), so the whole
definition is `<$>` over a single `Traversable.traverse` call on the one field. Implementer's
choice whether to write the rebuild as `(fun fs => { factors := fs })` or the anonymous
constructor `(⟨·⟩)` — either compiles for a one-field structure; use whichever reads more
clearly in context, this is not a decision worth its own theorem.

## Instantiations and equivalence theorems

```lean
private def specsProdTerm' (t : ProdTerm) : List AxisSpec := t.factors.flatMap specsFactor'

theorem traverseAxes_const_eq_specsProdTerm (t : ProdTerm) :
    (ProdTerm.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) t).run = specsProdTerm' t

theorem traverseAxes_const_eq_termAxisUIDs (t : ProdTerm) :
    (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) t).run = termAxisUIDs t

theorem traverseAxes_id_eq_prodTermMapUID_of_factors (f : UData → UData) (p : ProdTerm)
    (h : ∀ x ∈ p.factors, Factor.traverseAxes (f := Id) (AxisSpec.mapUID f) x = Factor.mapUID f x) :
    ProdTerm.traverseAxes (f := Id) (AxisSpec.mapUID f) p = ProdTerm.mapUID f p
```

**Collecting direction.** Both theorems reduce to the same list-core-lemma shape used in the
`Factor` slice — a small induction on `p.factors` showing
`(Traversable.traverse (Factor.traverseAxes g) p.factors).run = p.factors.flatMap (fun x =>
(Factor.traverseAxes g x).run)`, rewritten pointwise via `Factor`'s *already-proven* collecting
theorems (`traverseAxes_const_eq_specsFactor`/`_factorAxisUIDs`) rather than re-deriving them.
`traverseAxes_const_eq_specsProdTerm` closes directly against `specsProdTerm'` this way. The
`termAxisUIDs` theorem needs one extra bridging fact first:
`termAxisUIDs t = t.factors.flatMap factorAxisUIDs'` — expected to be `rfl` or near-`rfl`, since
`factorAxisUIDs'` (defined in the `Factor` slice) was built specifically to mirror
`termAxisUIDs`'s inline per-`Factor` match arm-for-arm. Once that bridge holds, the same
list-core-lemma composed with `traverseAxes_const_eq_factorAxisUIDs` closes the theorem.

**Remap direction.** The conditional lemma is proved by induction on `p.factors`, applying the
hypothesis `h` pointwise at each `cons` step (a `List.map`-congruence-style argument: the head
uses `h` instantiated at that element via its membership proof, the tail recurses with `h`
restricted to the tail). This is genuinely new proof-engineering — no prior slice stated a
hypothesis-parameterized theorem — and is the real test of whether the encoding's remap
direction composes correctly over `List`.

## Effort policy

Full attempt on all three theorems. The conditional lemma's proof sketch (list induction +
pointwise hypothesis application) is a standard shape; if it doesn't close as sketched, that
would be a genuine surprise worth flagging, not a predicted outcome to silently comment out.

## File layout

- `test/DSL/TraverseAxesSpike.lean` (extend, not new) — append after the `Factor` section.
  Already registered in `lakefile.toml`'s `Tests` globs — no new registration needed.

## Success criteria (the go/no-go bar)

**Go:**
- Both collecting-direction theorems close with genuinely sound proofs, including the
  `termAxisUIDs` bridging fact.
- The conditional remap lemma closes via the sketched list-induction argument.

**No-go / interesting either way:**
- If either collecting theorem needs real structural fighting (surprising for such a thin
  single-field wrapper), that's worth a closer look before extrapolating to `SumExpr` (which has
  the identical `structure ... where terms : List ProdTerm` shape one layer up).
- If the conditional lemma's induction hits unexpected friction, that's a genuine finding about
  whether the "conditional lemma" resolution generalizes to `SumExpr`/`RHSExpr`'s own list
  fields, not just a `ProdTerm`-specific quirk.

## Risks / notes

- `specsProdTerm'` has no named production counterpart to mirror byte-for-byte — it must be
  checked against the *inline* fragment inside `specsRHS` (`Structural.lean:45-46`), same
  maintenance hazard as `Factor`'s `factorAxisUIDs'`.
- The `termAxisUIDs` bridge now chains through *two* local artifacts (`Factor`'s
  `factorAxisUIDs'` and this slice's own proof) to reach one real production function — an
  extra indirection worth getting right; if the bridging fact isn't `rfl`, double-check
  `factorAxisUIDs'`'s arms against `termAxisUIDs`'s inline match again before assuming a proof
  bug rather than a copy-drift bug.
- `SumExpr` (`structure SumExpr where terms : List ProdTerm`) is structurally identical to
  `ProdTerm` one layer up — if this slice's conditional-lemma resolution works cleanly, `SumExpr`
  should be a near-mechanical repeat, not a fresh design question.

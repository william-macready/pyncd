# E1 — `traverseAxes` Prototype (RHSExpr slice) — Design

**Status:** approved 2026-07-16. Feeds `writing-plans`.

## Goal

Extend the E1 prototype (`test/DSL/TraverseAxesSpike.lean`, on branch
`worktree-e1-traverseaxes-prototype`, PR
[william-macready/pyncd#1](https://github.com/william-macready/pyncd/pull/1)) to `RHSExpr` —
the node the checkpoint explicitly flagged as **not** structurally identical to `ProdTerm`/
`SumExpr` (`structure RHSExpr where body : SumExpr; nonlin : Nonlin; agg : AggOp := .sum`,
three fields, not one list-wrapping field). This is the first slice since `IdxExpr` to need
genuinely fresh design work rather than a mechanical continuation of the immediately preceding
slice.

## Scope decisions made during brainstorming

**Decision 1 — bundle `Nonlin` into this slice, not a separate one.** `Nonlin`
(`inductive Nonlin | identity | relu | sigmoid | tanh | gelu | leakyrelu | softmax (Option
BoolExpr) | normalize (Option BoolExpr) | l2normalize (Option BoolExpr)`, `DSL/Ast.lean:66-76`)
has never been touched by any prior slice — it's a required building block for `RHSExpr`, not
an optional detour. The user chose to tackle `RHSExpr` directly rather than spike `Nonlin` on
its own first.

**Decision 2 — two named functions, not one flagged function, for the mask asymmetry.**
Production has a documented, load-bearing semantic split: `specsRHS` (`Structural.lean:45-46`,
private) collects `AxisSpec`s **including** the nonlin mask's axes (`++ specsNonlin r.nonlin`),
while `readAxisUIDs` (`Eval/Contract.lean:43-44`, public) collects UIDs and **deliberately
excludes** the mask entirely (`rhs.body.terms.flatMap termAxisUIDs`, never touching
`rhs.nonlin`) — the original restructuring doc's own Spike 2b writeup already named this as a
distinction that must not be silently merged, suggesting "two named entry points... not a silent
flag default." A single, uniformly-defined `RHSExpr.traverseAxes(g)` cannot reproduce both
behaviors as different instantiations of the same underlying traversal, since mask-inclusion is
a structural choice, not something the `Applicative`/`g` parameter can express. Per the user's
choice: two separate functions, `RHSExpr.traverseAxesWithMask` and `RHSExpr.traverseAxesNoMask`,
rather than a `Bool` parameter.

**Crucially, `WithMask` and `NoMask` are not symmetric alternatives — they serve different,
non-overlapping directions:** `WithMask` is used for *both* AxisSpec-collecting (matches
`specsRHS`) *and* remap (matches `RHSExpr.mapUID`, which always updates the mask's UIDs — there
is no production notion of "remap but leave the mask stale"). `NoMask` is used *only* for
UID-collecting (matches `readAxisUIDs`'s deliberate exclusion). There is no `NoMask` remap
theorem, and none is needed.

## Scope

**In:**
- `Nonlin.traverseAxes` (the traversal, 9-arm exhaustive match — by construction, this closes
  off the wildcard hazard production's `specsNonlin` documents in its own module doc: "safe
  ONLY because every current non-masked `Nonlin` variant genuinely contributes no axis specs...
  this bit `l2normalize` once already").
- A local `specsNonlin'` comparison copy (byte-identical to production's private `specsNonlin`,
  `Structural.lean:37-39`) and one collecting-direction theorem against it. **No UID-collecting
  theorem for `Nonlin` is needed or included** — no UID-collecting path anywhere in this slice
  ever touches `nonlin` (see Decision 2), so there is nothing to compare against.
- One demonstration that the `Nonlin`-level remap hypothesis is satisfiable: a trivial `rfl` for
  the unmasked `.identity` case, and `traverseAxes_id_eq_nonlinMapUID_of_mask` showing a masked
  case's remap holds *given* its `BoolExpr`'s own remap holds.
- `RHSExpr.traverseAxesWithMask` and `RHSExpr.traverseAxesNoMask`.
- A local `specsRHS'` comparison copy, defined as `specsSumExpr' r.body ++ specsNonlin' r.nonlin`
  (delegating to both already-proven local copies from prior slices — DRY, not re-derived).
- Two collecting-direction theorems: `traverseAxes_const_eq_specsRHS` (against `specsRHS'`) and
  `traverseAxes_const_eq_readAxisUIDs` (against the **real, public production `readAxisUIDs`**
  directly — no local copy needed, since `traverseAxesNoMask` never touches `nonlin`).
- One remap theorem, `traverseAxes_id_eq_rhsExprMapUID`, conditional on **two** independent
  hypotheses (body's remap holds, nonlin's remap holds) — see below.

**Out:** `LHSSlot`/`Stmt`/`Decl`/`TLProgram` — deferred to their own future slices. No production
files touched.

## The traversals

```lean
def Nonlin.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : Nonlin → f Nonlin
  | .identity      => pure .identity
  | .relu          => pure .relu
  | .sigmoid       => pure .sigmoid
  | .tanh          => pure .tanh
  | .gelu          => pure .gelu
  | .leakyrelu     => pure .leakyrelu
  | .softmax m     => Nonlin.softmax <$> Traversable.traverse (BoolExpr.traverseAxes g) m
  | .normalize m   => Nonlin.normalize <$> Traversable.traverse (BoolExpr.traverseAxes g) m
  | .l2normalize m => Nonlin.l2normalize <$> Traversable.traverse (BoolExpr.traverseAxes g) m

def RHSExpr.traverseAxesWithMask [Applicative f] (g : AxisSpec → f AxisSpec) (r : RHSExpr) : f RHSExpr :=
  (fun body nonlin => { body := body, nonlin := nonlin, agg := r.agg }) <$>
    SumExpr.traverseAxes g r.body <*> Nonlin.traverseAxes g r.nonlin

def RHSExpr.traverseAxesNoMask [Applicative f] (g : AxisSpec → f AxisSpec) (r : RHSExpr) : f RHSExpr :=
  (fun body => { body := body, nonlin := r.nonlin, agg := r.agg }) <$> SumExpr.traverseAxes g r.body
```

`Nonlin.traverseAxes` is the first traversal in this series to use `Option`'s `Traversable`
instance rather than `List`'s (via `Traversable.traverse (BoolExpr.traverseAxes g) m` for
`m : Option BoolExpr`). `RHSExprWithMask` is the first traversal combining two genuinely
independent sub-traversals (`SumExpr` and `Nonlin`) via `<*>`, rather than a single `List`
traversal — a new composition shape, though not a new *risk*, since each sub-traversal is
already proven independently.

## Instantiations and equivalence theorems

```lean
private def specsNonlin' : Nonlin → List AxisSpec
  | .softmax (some m) => specsBool' m | .normalize (some m) => specsBool' m
  | .l2normalize (some m) => specsBool' m | _ => []

theorem traverseAxes_const_eq_specsNonlin (n : Nonlin) :
    (Nonlin.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) n).run = specsNonlin' n

theorem traverseAxes_id_eq_nonlinMapUID_of_mask (f : UData → UData) (b : BoolExpr)
    (hb : BoolExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) b = BoolExpr.mapUID f b) :
    Nonlin.traverseAxes (f := Id) (AxisSpec.mapUID f) (Nonlin.softmax (some b)) = Nonlin.mapUID f (Nonlin.softmax (some b))

private def specsRHS' (r : RHSExpr) : List AxisSpec := specsSumExpr' r.body ++ specsNonlin' r.nonlin

theorem traverseAxes_const_eq_specsRHS (r : RHSExpr) :
    (RHSExpr.traverseAxesWithMask (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) r).run = specsRHS' r

theorem traverseAxes_const_eq_readAxisUIDs (r : RHSExpr) :
    (RHSExpr.traverseAxesNoMask (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) r).run = readAxisUIDs r

theorem traverseAxes_id_eq_rhsExprMapUID (f : UData → UData) (r : RHSExpr)
    (hbody : SumExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) r.body = SumExpr.mapUID f r.body)
    (hnonlin : Nonlin.traverseAxes (f := Id) (AxisSpec.mapUID f) r.nonlin = Nonlin.mapUID f r.nonlin) :
    RHSExpr.traverseAxesWithMask (f := Id) (AxisSpec.mapUID f) r = RHSExpr.mapUID f r
```

**Nonlin's collecting theorem:** 6 trivial `rfl` cases (unmasked constructors: `pure .identity`
at `ConstL` reduces to `⟨[]⟩`, matching `specsNonlin'`'s wildcard `_ => []` case for those same
constructors), 3 masked cases each delegating to `BoolExpr`'s already-proven collecting theorem
via `Option`'s `Traversable` instance (`cases m with | none => rfl | some b => ...`, using the
already-proven `traverseAxes_const_eq_specsBool`).

**`RHSExpr`'s two collecting theorems:** `specsRHS`'s theorem is a direct `rw` composing the
already-proven `SumExpr` and `Nonlin` collecting theorems (no new induction needed — the
`<*>`-combination at `ConstL` reduces via the same instance-unfolding argument used throughout
this file). `readAxisUIDs`'s theorem is even simpler: since `traverseAxesNoMask` never touches
`nonlin`, the goal reduces immediately to `SumExpr`'s own already-proven UID-collecting theorem
— no new proof content at all beyond the reduction step.

**Remap — the two-hypothesis conditional.** `traverseAxes_id_eq_rhsExprMapUID` does *not*
transitively re-derive `SumExpr`'s or `Nonlin`'s own (further-conditional) remap obligations —
it takes each as a flat hypothesis about the specific `r.body`/`r.nonlin` values in question,
mirroring exactly how `ProdTerm`'s and `SumExpr`'s own conditional lemmas took a hypothesis
about their immediate sub-structure rather than expanding it. Given both hypotheses, the
`RHSExpr`-level equality follows by a direct `show`+`rw`, no induction needed (there's no list
at this level). `traverseAxes_id_eq_nonlinMapUID_of_mask` demonstrates the `Nonlin`-level
hypothesis is satisfiable for a masked constructor, given a `BoolExpr`; the unmasked
`.identity` case needs no hypothesis at all (closes by plain `rfl`) — the other 5 unmasked
constructors (`relu`/`sigmoid`/`tanh`/`gelu`/`leakyrelu`) are structurally identical and not
separately proved, since they add no new information.

**This exact code has already been verified to close, end-to-end, via a standalone staged
build during design** (not just sketched) — `lake build DSL.TraverseAxesSpike` and a full
`lake build` both succeeded (8609 jobs), then reverted before writing this doc.

## Effort policy

None needed — every theorem above is pre-verified to close exactly as written.

## File layout

- `test/DSL/TraverseAxesSpike.lean` (extend, not new) — append after the `SumExpr` section.
  Already registered in `lakefile.toml`'s `Tests` globs — no new registration needed.

## Success criteria (the go/no-go bar)

**Go:** all theorems close exactly as pre-verified (already confirmed during design).

**No-go / interesting either way:** none anticipated for the code itself. The one thing worth
re-examining after this slice lands is whether the "two named functions" resolution to the
mask asymmetry (Decision 2) is a one-off for `RHSExpr`, or whether a similar split will recur
at `LHSSlot`/`Stmt`/`TLProgram` — those nodes haven't been checked for an analogous asymmetry
yet.

## Risks / notes

- `specsNonlin'` must stay byte-identical to `Structural.lean:37-39`'s private `specsNonlin` by
  inspection — same maintenance hazard as every prior local copy.
- `specsRHS'` delegates to `specsSumExpr'`/`specsNonlin'` rather than re-deriving through
  `specsFactor'`/`specsBool'` directly — same DRY discipline as `SumExpr`'s own `specsSumExpr'`.
- The `RHSExpr.traverseAxesNoMask`/`WithMask` split is the first departure from this file's
  established "one traversal per node" pattern into "two traversals for one node." If this
  recurs at future slices, it may be worth a naming/documentation convention beyond what this
  slice establishes ad hoc.
- `LHSSlot`/`Stmt`/`Decl`/`TLProgram` remain open and unexamined for their own risk shapes —
  none should be assumed mechanical without checking first, per the pattern established by this
  slice itself (which was flagged in advance as needing fresh scoping, correctly).

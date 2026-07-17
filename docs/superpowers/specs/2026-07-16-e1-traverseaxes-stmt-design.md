# E1 — `traverseAxes` Prototype (Stmt slice) — Design

**Status:** approved 2026-07-16. Feeds `writing-plans`.

## Goal

Extend the E1 prototype (`test/DSL/TraverseAxesSpike.lean`, on branch
`worktree-e1-traverseaxes-prototype`, PR
[william-macready/pyncd#1](https://github.com/william-macready/pyncd/pull/1)) to `Stmt`.
Per the checkpoint's own caution not to assume this node's shape, its actual definition was
read before scoping: `inductive Stmt | assign : String → List LHSSlot → RHSExpr → Stmt |
scatter : String → List LHSSlot → RHSExpr → ScatterOpts → Stmt | recurMorphism : String →
AxisSpec → ThreadedComposed → Stmt` (`DSL/Ast.lean:116-121`) — 3 constructors. `.assign` and
`.scatter` are structurally near-identical (`.scatter` = `.assign` plus a trailing
`ScatterOpts`, untouched by axis logic); `.recurMorphism` is a genuine outlier — a "pre-built
morphism escape hatch" (§12.2) carrying one bare `AxisSpec` and an untouched `ThreadedComposed`
(the presentation-layer routing-DAG type, confirmed via grep to be unrelated to the AST/
traversal layer and correctly passed through unchanged).

## Findings from checking production before assuming anything

**Remap is unconditional for `.recurMorphism`, conditional-with-one-hypothesis for
`.assign`/`.scatter`.** `Stmt.mapUID` (`DSL/Traverse.lean:73-76`) is non-partial and flat:
`.assign`/`.scatter` each map `LHSSlot.mapUID` over their slot list and delegate to
`RHSExpr.mapUID` for the RHS; `.recurMorphism` only touches its bare `AxisSpec`. Since
`LHSSlot`'s own remap is already fully unconditional (previous slice) but `RHSExpr`'s remains
conditional on a hypothesis about its `body`/`nonlin` (inherited from the `BoolExpr`
`partial def` wall further down), `Stmt.assign`/`Stmt.scatter`'s remap theorems take that same
single `RHSExpr` hypothesis and re-use it unchanged — no new conditional surface, no
transitive re-derivation. `.recurMorphism` closes by plain `rfl`, no hypothesis at all.

**A new obstacle, not a new scoping question: `Stmt.uids` is built from *private* helpers,
invisible from the spike file even through the public function that calls them.**
`Stmt.uids (s : Stmt) : List UID := (specsStmt s).map (·.uid)` (`Structural.lean:84`) is public,
but `specsStmt` and everything it recurses through (`specsLHS`, `specsRHS`, `specsNonlin`,
`specsFactor`, `specsBool`, `specsPred`, `specsIdx`) are `private` to `Structural.lean`. Lean 4
`private` visibility means not just "unnameable from outside," but that **the elaborator cannot
delta-reduce through a private declaration from outside its declaring file, even via a public
wrapper that calls it** — confirmed empirically: `simp [Stmt.uids]` unfolds one layer then gets
stuck at an inaccessible `specsStmt✝`. This is a strictly harder wall than anything prior slices
hit (the `BoolExpr.mapUID partial def` wall blocks *equation lemmas*; this blocks *any* external
unfolding at all, private or not). The only fix is a new theorem stated *inside*
`Structural.lean` (where privates are mutually visible) whose *statement* uses only
already-public names, so the spike file can `rw` through it without ever seeing the private
layer.

**Resolution, approved by explicit user instruction ("Build it out now" for `Stmt.uids`, then
"add the import too... make sure these changes are well commented so that if necessary they can
be reverted in future" for the production-file theorem):** add `Stmt.uids_eq` to
`Structural.lean` — a theorem restating `Stmt.uids` in terms of the already-public
`idxAxisUIDs`/`boolAxisUIDs`/`termAxisUIDs` (from `LeanNCD.Eval.Contract`), proved via six new
private bridge lemmas (`specsIdx_map_uid_eq` through `specsLHS_map_uid_eq`) that each show one
private `specsX` collector's `.map (·.uid)` coincides with the layer's already-public UID
collector. This is the **first production-file change on this branch** — previously E1 had
touched only `test/DSL/TraverseAxesSpike.lean`. It requires a new cross-layer import
(`LeanNCD.Eval.Contract` into `LeanNCD.DSL.Pipeline.Structural`), breaking the deliberate
non-crossing layering between `DSL/Pipeline` and `Eval` noted elsewhere in the codebase's own
architecture comments, for the first time on this branch.

Because this exception to "spike touches only the test file" needs to survive scrutiny (and
possible reversal) independent of whether E1 itself is ever adopted, every part of it is marked
with a `-- SPIKE EXCEPTION (...)` comment explaining why it exists, plus a `TO REVERT:` line
giving the exact deletion instructions — searchable via the literal string `"SPIKE EXCEPTION"`
in `Structural.lean`. Nothing else in that file depends on the import, the `open`, or the new
theorem block; reverting is a pure deletion, no follow-on edits required.

**A smaller wrinkle found while proving `Stmt.uids_eq`: `Nonlin` never had a UID-collecting
theorem in the spike file, because no prior slice needed one.** `readAxisUIDs` (`RHSExpr`'s own
UID-collecting function) deliberately *excludes* the mask — that's the mask-inclusion asymmetry
already documented at the `RHSExpr` slice. But `specsStmt`/`Stmt.uids` are built from `specsRHS`,
which *includes* the mask. So closing `traverseAxes_const_eq_stmtUids` needs a genuinely new
lemma, `traverseAxes_const_eq_nonlinAxisUIDs`, proving `Nonlin.traverseAxes` at `ConstL (List
UID)` matches the mask-inclusive match expression — structurally identical to the existing
`traverseAxes_const_eq_specsNonlin` (same 9-constructor case split, same delegation to
`BoolExpr`'s corresponding theorem for the `some b` arms), just at the UID layer instead of the
`AxisSpec` layer.

## Scope

**In:** `Stmt.traverseAxes` (3-arm match, `.assign`/`.scatter` combining a `Traversable.traverse`
over `List LHSSlot` with `RHSExpr.traverseAxesWithMask` via `<*>`, `.recurMorphism` a bare `g`
application); a local `specsStmt'` comparison copy; one collecting-direction theorem against it;
a second collecting-direction theorem bridging to the real, public `Stmt.uids` via the new
`Stmt.uids_eq` production theorem; one unconditional remap theorem for `.recurMorphism`; two
conditional (one-hypothesis) remap theorems for `.assign`/`.scatter`. Also in scope: the new
`traverseAxes_const_eq_nonlinAxisUIDs` lemma (needed as a dependency, sits in the existing
`Nonlin` section of the spike file) and the `Stmt.uids_eq` production theorem plus its six
bridge lemmas in `Structural.lean`.

**Out:** `Decl`/`TLProgram` — deferred to their own future slices.

## The traversal

```lean
def Stmt.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : Stmt → f Stmt
  | .assign nm ls r         => (fun ls' r' => Stmt.assign nm ls' r') <$>
      Traversable.traverse (LHSSlot.traverseAxes g) ls <*> RHSExpr.traverseAxesWithMask g r
  | .scatter nm ls r o      => (fun ls' r' => Stmt.scatter nm ls' r' o) <$>
      Traversable.traverse (LHSSlot.traverseAxes g) ls <*> RHSExpr.traverseAxesWithMask g r
  | .recurMorphism nm ax tc => (fun ax' => Stmt.recurMorphism nm ax' tc) <$> g ax
```

`.assign`/`.scatter` combine two independent sub-traversals (a list traversal over `LHSSlot` and
a single `RHSExpr.traverseAxesWithMask` call) the same way `RHSExpr.traverseAxesWithMask` itself
combines `SumExpr`/`Nonlin` — via `<$> ... <*> ...`, not a single flat `List`. `.recurMorphism`
passes `nm`/`tc` through untouched, matching `Stmt.mapUID`'s own treatment.

## Instantiations and equivalence theorems

```lean
private def specsStmt' : Stmt → List AxisSpec
  | .assign _ ls r => ls.flatMap specsLHS' ++ specsRHS' r
  | .scatter _ ls r _ => ls.flatMap specsLHS' ++ specsRHS' r
  | .recurMorphism _ ax _ => [ax]

theorem traverseAxes_const_eq_specsStmt (s : Stmt) :
    (Stmt.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) s).run = specsStmt' s

theorem traverseAxes_const_eq_stmtUids (s : Stmt) :
    (Stmt.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) s).run = Stmt.uids s

theorem traverseAxes_id_eq_stmtMapUID_recurMorphism (f : UData → UData) (nm : String)
    (ax : AxisSpec) (tc : ThreadedComposed) :
    Stmt.traverseAxes (f := Id) (AxisSpec.mapUID f) (Stmt.recurMorphism nm ax tc)
      = Stmt.mapUID f (Stmt.recurMorphism nm ax tc)

theorem traverseAxes_id_eq_stmtMapUID_assign (f : UData → UData) (nm : String)
    (ls : List LHSSlot) (r : RHSExpr)
    (hr : RHSExpr.traverseAxesWithMask (f := Id) (AxisSpec.mapUID f) r = RHSExpr.mapUID f r) :
    Stmt.traverseAxes (f := Id) (AxisSpec.mapUID f) (Stmt.assign nm ls r)
      = Stmt.mapUID f (Stmt.assign nm ls r)

theorem traverseAxes_id_eq_stmtMapUID_scatter (f : UData → UData) (nm : String)
    (ls : List LHSSlot) (r : RHSExpr) (o : ScatterOpts)
    (hr : RHSExpr.traverseAxesWithMask (f := Id) (AxisSpec.mapUID f) r = RHSExpr.mapUID f r) :
    Stmt.traverseAxes (f := Id) (AxisSpec.mapUID f) (Stmt.scatter nm ls r o)
      = Stmt.mapUID f (Stmt.scatter nm ls r o)
```

**Collecting direction (`specsStmt'`):** an inline `core` induction lemma over `List LHSSlot`
(re-deriving the list-traversal fold via the already-proven per-element
`traverseAxes_const_eq_specsLHS`), then per-constructor `show`/`rw` steps delegating to `core`
and the already-proven `traverseAxes_const_eq_specsRHS`; `.recurMorphism` closes by `rfl`.

**Collecting direction (`Stmt.uids`, via `Stmt.uids_eq`):** `rw [Stmt.uids_eq]` first turns the
goal into one stated purely over public UID-collectors, then the same `core`/`show`/`rw` shape
as above, with the `.assign`/`.scatter` cases needing an explicit `have hr : (RHSExpr...).run =
... := by ...` (not `congr 1`, which splits an `A ++ B = (A ++ C) ++ D` goal along the wrong
associativity) followed by `rw [core ls, hr, ← List.append_assoc]; rfl`. The `core` induction's
`cons` case needs a trailing `rfl` after `rw [ih]` in every arm (`free`/`freeNorm`/`iterAt`/
`iterNext`), since the match arms don't auto-close via `rw`'s implicit `rfl` alone once nested
under a `List.flatMap` lambda — an artifact of the goal's `match ... with` not being on the
outermost spine the way the earlier `IdxExpr`-only cases were.

**Remap direction:** `.recurMorphism` is a plain `rfl`, no hypothesis. `.assign`/`.scatter` each
need a `core` list-lemma (via `List.traverse_cons` + the already-unconditional
`traverseAxes_id_eq_lhsSlotMapUID`) plus the caller-supplied `RHSExpr` hypothesis `hr`, mirroring
the shape every conditional remap theorem has taken since `ProdTerm`.

**This exact code (including the `traverseAxes_const_eq_nonlinAxisUIDs` lemma and the
associativity/`rfl` fixes above) has already been verified to close, end-to-end, via a
standalone staged build during design** — `lake build DSL.TraverseAxesSpike` (8487 jobs) and a
full `lake build` (8609 jobs) both succeeded, then the spike-file scratch edit was reverted
(`git show HEAD:... > test/DSL/TraverseAxesSpike.lean`) before writing this doc. The
`Structural.lean` production changes were left in place (uncommitted, verified) — see below.

## Production-file change (SPIKE EXCEPTION)

`LeanNCD/DSL/Pipeline/Structural.lean` gains, all marked with `-- SPIKE EXCEPTION` comments
carrying `TO REVERT:` instructions (search the literal string `"SPIKE EXCEPTION"` in that file):

1. `import LeanNCD.Eval.Contract` — the only cross-layer import on this branch.
2. `open LeanNCD.Eval (idxAxisUIDs predAxisUIDs boolAxisUIDs termAxisUIDs)` — right after
   `namespace LeanNCD` / `open Std`.
3. Six new `private` bridge lemmas (`specsIdx_map_uid_eq`, `specsPred_map_uid_eq`,
   `specsBool_map_uid_eq`, `specsFactor_map_uid_eq`, `specsNonlin_map_uid_eq`,
   `specsLHS_map_uid_eq`) and one new public theorem, `Stmt.uids_eq`, placed immediately after
   the existing (unmodified) `def Stmt.uids`.

All seven are proven, no `sorry`, verified via both a standalone module build
(`lake build LeanNCD.DSL.Pipeline.Structural`, 8486 jobs) and a full project build (8609 jobs).
Reverting is a pure deletion: remove the import, the `open` line, and the SPIKE EXCEPTION
comment block through `Stmt.uids_eq` — nothing else in the file depends on any of it.

## Effort policy

None needed — every theorem above is pre-verified to close exactly as written (including the
production-file additions).

## File layout

- `test/DSL/TraverseAxesSpike.lean` (extend, not new) — append after the `LHSSlot` section; add
  `import LeanNCD.DSL.Pipeline.Structural` to the import list (needed to see `Stmt.uids`/
  `Stmt.uids_eq`); add `traverseAxes_const_eq_nonlinAxisUIDs` to the existing `Nonlin` section
  (it is a dependency of the new `Stmt` UID-collecting theorem, not itself part of `Stmt`, but
  has no other home).
- `LeanNCD/DSL/Pipeline/Structural.lean` (production, modify) — the SPIKE EXCEPTION block
  described above.

## Success criteria (the go/no-go bar)

**Go:** all Lean code above closes exactly as pre-verified (already confirmed during design, both
module-level and full-project builds green).

**No-go / interesting either way:** the `Stmt.uids` privacy wall and its resolution are
themselves the interesting result of this slice — the first time E1 has needed to touch
production code, and the first time a slice's own "collecting direction against the real
production function" step required more than reading a private definition and copying it
locally. Worth carrying forward explicitly to any future slice (`Decl`/`TLProgram`) that might
hit the same wall, and worth flagging prominently at any eventual go/no-go decision on E1 as a
whole, since adopting E1 in earnest would need a principled answer to "how much private-function
surface must become public (or get bridge theorems) to let a single traversal replace the
hand-written families" rather than one-off spike exceptions per node.

## Risks / notes

- `specsStmt'` must stay byte-identical to `Structural.lean`'s private `specsStmt` by
  inspection — same maintenance hazard as every prior local copy.
- The `Stmt.uids_eq` production theorem is the first departure from "E1 touches only the test
  file." It is deliberately isolated (one file, one clearly marked block, verified revertible)
  so it does not entangle E1's exploratory status with the rest of the codebase — but any future
  slice that wants to reach another private-and-public-wrapped production function should expect
  to repeat this pattern, not assume it was a one-time cost.
- `ThreadedComposed` (the presentation-layer routing-DAG type carried by `.recurMorphism`) is
  confirmed unrelated to the AST/traversal layer and is passed through untouched by
  `Stmt.traverseAxes`, matching `Stmt.mapUID`'s own treatment — no traversal logic was needed
  for it, and none should be added.
- `Decl`/`TLProgram` (the final two slices) have not been examined for their own risk shape —
  per the discipline this slice itself just reinforced, they should get the same "check before
  assuming" treatment, including an explicit check for whether either depends on any other
  private-and-wrapped production function the way `Stmt.uids` did.

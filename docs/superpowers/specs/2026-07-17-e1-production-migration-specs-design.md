# E1 Production Migration — Sub-project 1: `specs*` family — Design

**Status:** approved 2026-07-17. Feeds `writing-plans`.

## Goal

E1 (the `traverseAxes` prototype in `leanncd/test/DSL/TraverseAxesSpike.lean`, eleven slices,
now merged) tested whether one generic `NodeName.traverseAxes` function per AST node can
subsume three separately hand-maintained production families: `mapUID` (remap, in
`DSL/Traverse.lean`), the private `specs*` collectors (in `DSL/Pipeline/Structural.lean`), and
the public `*AxisUIDs` collectors (in `Eval/Contract.lean`). The prototype succeeded — zero
`sorry`/`native_decide` across all eleven nodes, one contained production-file exception
(`Stmt.uids_eq`) — and the decision has been made to act on it: migrate production to use
`traverseAxes`-based implementations in place of the three hand-written families.

Given the scale, this migration is decomposed into three sub-projects, safest-first: **`specs*`
(this doc) → `*AxisUIDs` → `mapUID`**. `specs*` goes first because every function in it is
`private` with zero external callers (confirmed by a full-tree grep before scoping — see
Findings) — the lowest-risk possible target, and a chance to validate the migration *pattern*
itself (see below) across all eleven nodes before anything public-facing changes.

## Findings from researching the actual blast radius before assuming scope

**The core three families have a much smaller blast radius than their scale might suggest.**
`mapUID` has exactly one production call site in total (`Structural.lean:267`, inside
`assignUIDs`, via `TermTraversable.traverseUID` — never called by name per-node anywhere else
in production). All nine `specs*` functions plus `TLProgram.axisSpecs` are `private def` in
`Structural.lean` — by construction, zero call sites outside that file. `*AxisUIDs` has a small,
well-understood set of callers (`Eval/Scatter.lean`, internal use within `Eval/Contract.lean`,
and `lhsAxisUID?`/`freeAxisUIDs` feeding `Eval/Eval.lean`, `Eval/Scan.lean`, `Eval/Shape.lean`).

**A real trap to fence off: a second, independent axis-collector ecosystem exists in
`DSL/Pipeline/Lowering.lean`, unrelated to E1's three families.** `Lowering.lean:226` defines
`idxAxes : IdxExpr → List AxisSpec` — a byte-for-byte structural duplicate of `specsIdx`
(`Structural.lean:37`), kept in sync by hand today, used at `Lowering.lean:388`. The same file
also hosts `Stmt.lhsAxes`, `dedupByUid`, `tensorAxes`, `ScanStmt.stepRetainedAxes`,
`ScanStmt.stepDegAxesMulti` — a whole secondary collector cluster feeding `RouteSpec.lean`'s
correctness proofs (`Nodup`-uid theorems like `dedupByUid_uid_nodup`). None of this is part of
E1's three canonical families, and none of it is in scope for this migration — but a naive
"unify everything with a similar name" pass would either wrongly sweep it in or leave `idxAxes`
inconsistent with a newly-migrated `specsIdx`. Explicitly fenced off (see Non-goals).

**A genuine, documented risk if matching logic changes: `specsNonlin`'s wildcard fallback.**
`Structural.lean:22-35`'s own module doc states most `specs*` functions are exhaustive matches
(Lean's totality checker forces new constructors to be handled) *except* `specsNonlin`, which
uses `_ => []` — safe today only because every current non-masked `Nonlin` variant contributes
no axes, with an explicit warning that this "bit `l2normalize` once already." E1's own
`Nonlin.traverseAxes` (already proven in the spike) is a 9-arm *exhaustive* match with no
wildcard — migrating `specsNonlin` to be `(Nonlin.traverseAxes ...).run` therefore *closes* this
documented hazard by construction, not just preserves it. Worth calling out as a genuine
improvement, not merely a risk to manage.

**Mathlib ships a `Const` functor (`Mathlib.Control.Functor`) but it needs a `Monoid`/
`Multiplicative` wrapper to get an `Applicative` instance for `List α`** — exactly the ceremony
the original E1 design deliberately avoided in favor of a 5-line custom `ConstL`. Promoting the
spike's own `ConstL` into production (rather than adopting Mathlib's `Const` + `Multiplicative
(List α)`) keeps this consistent with the already-approved E1 design direction, not a new
decision being made here.

**Two corrections found only by staging the full migration and building, not by design-level
reasoning alone** (both already fixed and verified; see Migration Pattern and File Layout below
for the corrected shape):

1. **The spike file's own `ConstL`/`traverseAxes` definitions conflict with the newly-promoted
   production ones and must be removed from the spike file.** The spike file already imports
   `LeanNCD.DSL.Pipeline.Structural` (added during the `Stmt` slice, for `Stmt.uids_eq`); once
   `Structural.lean` imports the new `LeanNCD/DSL/TraverseAxes.lean`, the spike's *own* copies of
   `ConstL` and all eleven `NodeName.traverseAxes` (both now in the `LeanNCD` namespace, both
   byte-identical) collide — `error: 'LeanNCD.ConstL' has already been declared`, and the same
   for every `traverseAxes`. The fix is simple and was verified end-to-end: delete the spike's
   own copies (12 blocks: `ConstL` + its two instances, and each of the eleven `def
   NodeName.traverseAxes`); every local `specsX'`/`*AxisUIDs'` comparison copy and every
   equivalence theorem below them is left completely unchanged — they now resolve
   `NodeName.traverseAxes` to the production definition (verbatim-identical text), so no theorem
   proof needed to change.
2. **The pre-existing `Stmt.uids_eq` "SPIKE EXCEPTION" machinery (already in `Structural.lean`,
   landed during the `Stmt` slice) directly pattern-matches through several `specsX`'s OLD
   structural shape, and breaks once that `specsX` is redefined via `traverseAxes` — this changes
   the migration pattern itself** (see Migration Pattern below): the blanket "always delete
   `specsX_old`/`specsX_eq_old` once done" rule from the original design does NOT hold for every
   function. Eight of the ten do have this dependency (`specsIdx`, `specsPred`, `specsBool`,
   `specsNonlin`, `specsFactor`, `specsRHS`, `specsLHS`, `specsStmt`) and must keep their `_old`/
   `_eq_old` pair permanently, with one added `rw [specsX_eq_old]` line in whichever pre-existing
   theorem broke. Only two (`specsDecl`, `TLProgram.axisSpecs`) are genuinely transitional and
   get deleted at the end, exactly as originally planned.

## Scope

**In:** a new file `LeanNCD/DSL/TraverseAxes.lean` holding `ConstL` (promoted verbatim from the
spike, with its `Functor`/`Applicative` instances) and all eleven `NodeName.traverseAxes`
definitions (also promoted verbatim — these are the exact definitions the spike already built
and verified module-by-module across eleven slices). Migration of all 9 `specs*` functions
(`specsIdx`, `specsPred`, `specsBool`, `specsNonlin`, `specsFactor`, `specsRHS`, `specsLHS`,
`specsDecl`, `specsStmt`) plus `TLProgram.axisSpecs` (10 total) in `Structural.lean` to be
defined via `traverseAxes` instantiated at `ConstL (List AxisSpec)`, each verified against its
real prior body via a kernel-checked equality theorem (see Migration Pattern) before the old
body is deleted.

**Out:** `Lowering.lean`'s `idxAxes`/`Stmt.lhsAxes`/`dedupByUid`/`tensorAxes`/
`ScanStmt.stepRetainedAxes`/`ScanStmt.stepDegAxesMulti` — a separate ecosystem, not touched.
`*AxisUIDs` and `mapUID` families — later sub-projects. `TLProgram.axisNames`'s `.eraseDups`/
`.name`-projection — stays hand-written on top of the migrated `axisSpecs`, unchanged (E1's own
non-goal for this function carries over unmodified — `axisSpecs` itself is in scope, `axisNames`
built on top of it is not, since nothing about `axisNames` changes: it still calls
`axisSpecs.map (·.name) |>.eraseDups`, just against the migrated `axisSpecs`).
`Stmt.uids_eq`/the six bridge lemmas/the `SPIKE EXCEPTION` markers in `Structural.lean` —
untouched by this sub-project; whether/when to clean those up is a separate decision (they
remain correct regardless of this migration, since `specsStmt`'s *external* behavior is
preserved exactly by the kernel-checked equality proof below).

## Migration pattern (applied to all 10 functions; step 5 differs by function — see below)

For each `specsX` (leaf-to-root order: `specsIdx` → `specsPred` → `specsBool` → `specsNonlin` →
`specsFactor` → (`specsProdTerm`/`specsSumExpr` are inlined, no standalone function — see note
below) → `specsRHS` → `specsLHS` → `specsDecl` → `specsStmt` → `TLProgram.axisSpecs`):

1. Rename the current body to `specsX_old` (keep `private`) — including renaming any
   self-recursive calls inside that body to `specsX_old` too (cross-function calls, e.g.
   `specsPred`'s own call to `specsIdx`, stay unrenamed — they now resolve to whichever version
   of `specsIdx` is current at that point in the file, which is exactly the point: once `specsIdx`
   is migrated, `specsPred_old`'s `.embed` arm calls the *new*, `traverseAxes`-derived `specsIdx`).
2. Define `specsX := (NodeName.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)
   x).run` — the collecting-direction instantiation, identical in shape to every
   `traverseAxes_const_eq_specsX` theorem already proven in the spike.
3. Prove `private theorem specsX_eq_old (x : NodeType) : specsX x = specsX_old x`. The proof
   shape mirrors the spike's own `traverseAxes_const_eq_specsX` (same induction/case structure),
   but is NOT always a mechanical rename — leaf cases that used to need a real lemma (spike's
   `exact traverseAxes_const_eq_specsIdx e`, comparing against a hand-copied local) often close by
   plain `rfl` now, since `specsIdx` IS `(IdxExpr.traverseAxes ...).run` by definition, not merely
   proven-equal to it. Cases that cross into a *different* node's traversal (e.g. `BoolExpr`'s
   `.rel`/`.ieq` arms delegating to `PredArith`, or `Nonlin`'s masked arms delegating to
   `BoolExpr`) do NOT close via a plain `show`/`rw` the way same-node self-recursive cases do —
   `show` cannot always find the needed defeq through the `Applicative`/`Traversable` instance
   layers. Use `simp only [specsX, specsX_old, NodeName.traverseAxes, <the delegated-to specsY>]`
   followed by `rfl` for these; the exact simp sets are given per-function in the plan.
4. Build (`lake build`), confirm the theorem closes and the full test suite (particularly
   `test/DSL/Pipeline/StructuralTest.lean`, which exercises `assignUIDs`/`resolveDecls`/
   `checkReadRanks` end-to-end) stays green.
5. **Delete `specsX_old`/`specsX_eq_old`, UNLESS `specsX` is one of the eight functions the
   pre-existing `Stmt.uids_eq` "SPIKE EXCEPTION" machinery reaches into (`specsIdx`, `specsPred`,
   `specsBool`, `specsNonlin`, `specsFactor`, `specsRHS`, `specsLHS`, `specsStmt`)** — discovered
   only by staging the real migration and rebuilding (see Findings above). For those eight,
   `specsX_old`/`specsX_eq_old` are KEPT PERMANENTLY, and the ONE pre-existing theorem that broke
   gets a single added `rw [specsX_eq_old]` line (at the very start of its proof, before whatever
   `cases`/`induction` it already did) — everything else in that theorem's proof is unchanged,
   since it was written against the old structural shape and `specsX_old` still has that exact
   shape. Only `specsDecl` and `TLProgram.axisSpecs` — untouched by that machinery — get the
   original clean "prove once, delete `_old`, done" treatment.

**Exactly which pre-existing theorem needed the one-line fix, per function** (all in
`Structural.lean`, all already there before this sub-project, none of them new):

- `specsIdx` → `specsIdx_map_uid_eq` (`rw [specsIdx_eq_old]` right after `by`, before `cases e with`).
- `specsFactor` → `specsFactor_map_uid_eq` (same shape, before its `cases x with`).
- `specsRHS` → `Stmt.uids_eq`'s own internal `hRHS` `have` (one `rw [specsRHS_eq_old]` right
  after `intro r`, before its existing `show`).
- `specsStmt` → `Stmt.uids_eq`'s own top-level proof (one `show (specsStmt s).map (·.uid) = _`
  then `rw [specsStmt_eq_old]`, inserted right before its existing `cases s with`).
- `specsPred`, `specsBool`, `specsNonlin`, `specsLHS` → their own `specsX_map_uid_eq` lemmas
  needed NO fix at all — those proofs were already written in a "layer-preserving" style
  (`show (specsX a ++ specsX b).map (·.uid) = ...` rather than fully unfolding to raw list
  operations), which stays valid under the new `traverseAxes`-derived definition unchanged. Only
  the two *leaf-level* structural-match theorems (`specsIdx_map_uid_eq`, `specsFactor_map_uid_eq`)
  and the two whose own `Stmt.uids_eq`-inlined reasoning fully unfolded the raw body
  (`specsRHS`/`specsStmt`, both inside `Stmt.uids_eq` itself, not a separate named lemma) needed
  the fix — worth noting for future sub-projects: this pattern (only leaf/fully-unfolded proofs
  break, layer-preserving proofs survive unchanged) is likely to recur.

**Note on `ProdTerm`/`SumExpr`:** neither has a standalone `specs*` function today — their axis
collection is inlined directly inside `specsRHS`'s body (`t.factors.flatMap specsFactor` for
`ProdTerm`, an implicit flatMap-over-terms for `SumExpr`). This sub-project does not introduce
new standalone functions for them; `specsRHS`'s own migration (step above) replaces the whole
inlined expression with `(RHSExpr.traverseAxesWithMask ...).run`, which internally already
composes `SumExpr.traverseAxes`/`ProdTerm.traverseAxes` — matching production's own current
"no standalone function" shape, just re-deriving it from the traversal instead of by hand.

## Effort policy

Every `specsX_eq_old` proof is a straightforward retargeting of an already-verified spike
theorem — expect this to be transcription plus confirmation for every node except possibly
`specsRHS` (mask-inclusion asymmetry, already handled by the spike's `traverseAxesWithMask`)
and `specsNonlin` (9-arm exhaustive match, already handled by the spike's `Nonlin.traverseAxes`).
No new proof search should be needed; if any single node's `specsX_eq_old` doesn't close on the
first attempt, treat that as a genuine surprise worth stopping and understanding, not something
to force through.

## File layout

- `LeanNCD/DSL/TraverseAxes.lean` (new) — `ConstL` + all eleven `NodeName.traverseAxes`
  definitions, promoted verbatim from `test/DSL/TraverseAxesSpike.lean`.
- `LeanNCD/DSL/Pipeline/Structural.lean` (modify) — 10 functions migrated per the pattern above.
  Net line count grows, not shrinks: 8 of the 10 functions keep a permanent `_old`/`_eq_old` pair
  (see Migration Pattern's step 5 correction above) plus one added `rw` line in a pre-existing
  theorem; only `specsDecl` and `TLProgram.axisSpecs` end up as a clean same-signature
  replacement with nothing left over.
- `test/DSL/TraverseAxesSpike.lean` (modify) — NOT the "no changes" claim originally assumed.
  This file's own `ConstL` and all eleven `NodeName.traverseAxes` definitions must be DELETED
  (12 blocks) — they now collide with the newly-promoted production declarations, both in the
  `LeanNCD` namespace, once this file's existing `import LeanNCD.DSL.Pipeline.Structural`
  transitively pulls in the new production file (see Findings above). Every local
  `specsX'`/`*AxisUIDs'` comparison copy and every equivalence theorem is otherwise UNCHANGED —
  they now resolve `NodeName.traverseAxes` to the verbatim-identical production definition
  instead of a local one, so no proof text changes, only the 12 now-redundant definition blocks
  are removed.

## Success criteria (the go/no-go bar for this sub-project)

**Go:** all 10 `specsX_eq_old` theorems close (kernel-checked, not "by inspection"), the old
bodies are deleted, `specsNonlin`'s wildcard hazard is closed by construction, and the full test
suite (`lake build` including `StructuralTest.lean`) stays green throughout every step — not
just at the end.

**No-go / interesting either way:** if any single node's equality theorem fails to close, that
is real information about a discrepancy between the spike's understanding of the node and its
actual current production behavior — worth investigating fully (not working around) before
proceeding to that node's family-2/family-3 migration in later sub-projects, since the same
discrepancy would recur there.

## Risks / notes

- `specsX_old`/`specsX_eq_old` are transitional ONLY for `specsDecl` and `TLProgram.axisSpecs` —
  for the other eight, they are permanent, load-bearing internal helpers the pre-existing
  `Stmt.uids_eq` machinery now depends on (see Migration Pattern's step 5 correction). Do not
  "clean these up" reflexively in a later pass without re-confirming, for each one, that nothing
  still reaches through it the way `specsIdx_map_uid_eq`/`specsFactor_map_uid_eq`/`Stmt.uids_eq`
  itself do today.
- This sub-project does NOT touch `Stmt.uids_eq`'s own *content* or the `SPIKE EXCEPTION` markers
  already in `Structural.lean` — only adds the minimum `rw [specsX_eq_old]` needed to keep it
  compiling. It continues to describe a genuine, still-relevant fact (Lean can't delta-reduce
  through `specsStmt`'s privacy from outside the file), independent of whether `specsStmt`'s
  *body* is hand-written or `traverseAxes`-derived.
- The spike file's own duplicate `ConstL`/`traverseAxes` definitions must be deleted as part of
  this sub-project (see Findings and File Layout above) — this was not anticipated by the
  original design and was found only by staging the real migration and rebuilding the whole
  project, not by reasoning about `Structural.lean` in isolation. Any future sub-project that
  promotes more spike content into production should expect the same check.
- `TLProgram.axisSpecs`'s migration happens last (it depends on `specsDecl`/`specsStmt` both
  already being migrated) — the dependency order given above is load-bearing, not arbitrary.
- Future sub-projects (`*AxisUIDs`, `mapUID`) will consume the same `LeanNCD/DSL/TraverseAxes.lean`
  file created here — this sub-project is the one time that file gets created; later sub-projects
  only add to it (new instantiations of already-existing `traverseAxes` definitions), they don't
  need to re-derive it.

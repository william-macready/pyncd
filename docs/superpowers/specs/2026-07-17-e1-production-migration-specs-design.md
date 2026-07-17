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

## Migration pattern (applied identically to all 10 functions)

For each `specsX` (leaf-to-root order: `specsIdx` → `specsPred` → `specsBool` → `specsNonlin` →
`specsFactor` → (`specsProdTerm`/`specsSumExpr` are inlined, no standalone function — see note
below) → `specsRHS` → `specsLHS` → `specsDecl` → `specsStmt` → `TLProgram.axisSpecs`):

1. Rename the current body to `specsX_old` (keep `private`).
2. Define `specsX := (NodeName.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)
   x).run` — the collecting-direction instantiation, identical in shape to every
   `traverseAxes_const_eq_specsX` theorem already proven in the spike.
3. Prove `private theorem specsX_eq_old (x : NodeType) : specsX x = specsX_old x` — using the
   exact proof steps the spike already verified for `traverseAxes_const_eq_specsX`, just
   retargeted from the spike's hand-copied `specsX'` local to the *real* `specsX_old`. This is
   strictly stronger than anything the spike itself could check: the spike could only compare
   against hand-copied locals "by inspection" (except `Stmt.uids`, which got a real bridge
   theorem) — here the kernel checks new-equals-old for every function, not just one.
4. Build (`lake build`), confirm the theorem closes and the full test suite (particularly
   `test/DSL/Pipeline/StructuralTest.lean`, which exercises `assignUIDs`/`resolveDecls`/
   `checkReadRanks` end-to-end) stays green.
5. Delete `specsX_old` and the `specsX_eq_old` theorem.

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
- `LeanNCD/DSL/Pipeline/Structural.lean` (modify) — 10 functions migrated per the pattern above;
  net effect after each function's full cycle (rename → redefine → prove → delete) is a
  same-signature, same-behavior replacement, not a growing file (the transitional `_old` bodies
  and bridge theorems are deleted, not left in place).
- `test/DSL/TraverseAxesSpike.lean` — NOT deleted or modified. It remains the E1 record/prototype
  (per the established pattern of keeping every prior slice's spike code as historical record);
  its own local `specsX'` copies and equivalence theorems are independent of production's new
  `specsX` and continue to pass unchanged, since nothing about the spike file's own definitions
  changes here.

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

- `specsX_old`/`specsX_eq_old` are explicitly *transitional* — they should not survive past this
  sub-project's own completion. If time pressure tempts leaving one in place "to be safe," that
  defeats the purpose (the whole point is a kernel-checked one-time proof, then a clean deletion,
  not a permanently-duplicated implementation).
- This sub-project does NOT touch `Stmt.uids_eq`/the `SPIKE EXCEPTION` markers already in
  `Structural.lean` — they continue to describe a genuine, still-relevant fact (Lean can't
  delta-reduce through `specsStmt`'s privacy from outside the file), independent of whether
  `specsStmt`'s *body* is hand-written or `traverseAxes`-derived.
- `TLProgram.axisSpecs`'s migration happens last (it depends on `specsDecl`/`specsStmt` both
  already being migrated) — the dependency order given above is load-bearing, not arbitrary.
- Future sub-projects (`*AxisUIDs`, `mapUID`) will consume the same `LeanNCD/DSL/TraverseAxes.lean`
  file created here — this sub-project is the one time that file gets created; later sub-projects
  only add to it (new instantiations of already-existing `traverseAxes` definitions), they don't
  need to re-derive it.

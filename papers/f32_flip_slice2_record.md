# F32 flip slice 2: authoring record (stub)

Record for `leanncd/docs/superpowers/plans/2026-10-04-f32-flip-slice2.md`. The live plan carries no
authoring history; this file does. Execution close-out is appended here at merge time.

## Authoring (dispatch b: plan written from artifacts only)

- Inputs read: `.claude/skills/slice-plan/SKILL.md`; `papers/f32_flip_files/RESULTS.md`,
  `plan_modules.md`, `patches/` (names and touched files only), `papers/f32_flip_slice2_log.md`; the
  SLICE 1 and SLICE 2 bullets of memory `f32-default-flip-decisions.md`; headings of
  `2026-09-12-lhs-scatter-in-scans.md`; `papers/f32_evalplan.md` section 1.4 item 5.
- Cost: about 33 tool calls, no builds, no Lean code in the plan (so `check-snippet.sh` not run).
  Token total not measured by `token-report.py` (target <= ~50M for authoring; unmeasured).
- Verified when: every file path named in the plan checked with `ls` at authoring (all present on the
  branch `f32-flip-slice2-proto`, tip `0e1153a` before this commit); the patch names are from
  `ls papers/f32_flip_files/patches`; `defaultTargets = ["LeanNCD", "Tests"]` from `leanncd/lakefile.toml`;
  `DifferentialTest` guard text (`total == 3832 && accepted == 3832 && rejCounts.isEmpty`) by `rg`;
  `explicitF64` users under `leanncd/test` by `rg -l`; stale-default prose hits by `rg` over
  `leanncd/LeanNCD`, `leanncd/AGENTS.md`, `leanncd/test`.
- NOT verified: that patches 0001-0007 `git apply` in order onto `574a633` (first implementer action);
  the 8676 / 11 baseline (carried from memory `f32-default-flip-decisions`, slice-1 record); the
  277 failing-assertion total and per-module counts (prototype artifacts only, not re-measured); the
  contents of CompileTest, ScanCompileTest, ScatterCompileTest, Adapter*Test, DifferentialTest beyond
  grepped identifiers; AGENTS.md injected-section sizes; the Task 3 "probably one helper" claim.
- Deliberate omissions: no mutation manifest (no builds, so no observed `expect` strings; Task 8 runs a
  flip-reversal check instead); no failing-line numbers copied from the prototype artifacts.

## Execution close-out (2026-10-07)

Executed on branch `f32-flip-slice2` (off main `44296ad`; the plan's stated base `574a633` was 11 docs/semantics
commits behind, none touching the patched files: all eight patches passed `git apply --check` and applied, no
adaptation). 28 commits, `7eaf490`..`217eebf`.

**Measured (controller-run).**
- Full default build, final tree: `Build completed successfully (8677 jobs)`, 11 `warning:` lines. Baseline
  8676 / 11: the +1 job is the new `Eval.Plan.DefaultF32Test` module; warnings unchanged.
- `DifferentialTest` guards held (compile-time `#guard`s): sweep `total=3832 accepted=3832 rejected=0`, scan
  corpus `total=17 accepted=17 unsupportedNonlin=0 unsupportedAgg=0`. Gen's corpus not touched.
- Production diff vs main: the four flips plus docstrings/comments in `DSL/Ast.lean`, `Eval/Plan/Signature.lean`,
  `Eval/Plan/Compile.lean`, `Eval/Plan/Error.lean` (verified by a `-U0` diff).
- Flip-reversal check (Task 8 step 3): flips #1-#3 reverted together (files checked out from `44296ad`):
  `DSL.Pipeline.StructuralTest` FAILS ("untyped-plus-predicate graph: expected .ok .float32, got float64");
  `Eval.Plan.SignatureTest` FAILS on six pins (`dtypeOfDecl` / `storageConstraintOfDecl` for `.tensor` and
  `.linear`, the `conversionInputs` pin, and the `ofDenseInputs32ForDecls [.tensor "X"]` acceptance);
  `Eval.Plan.DefaultF32Test` FAILS with both `plain` and `undeclared` variants (storageKindMismatch / float64
  plans), as predicted with flip #1 also reverted (the failure-count line was truncated in the output, so no
  observed N for this combined run). Files restored, tree clean. Per-task mutations (`dtypeOfDecl` revert):
  CompileTest 15 failures, ScanCompileTest 8, DefaultF32Test 12 of 12 `undeclared` variants; `storageConstraintOfName?`
  undeclared arm back to `.float64`: CompileTest 5 failures. AdapterTest, Adapter32Test and DifferentialTest are
  insensitive to the default by construction (explicit f64).
- Tokens (`token-report.py`, this session, before the final review fixes' last build): 64.5M cumulative input,
  inside the 175M budget; no dispatch exceeded the 250k context peak (max 198k, Task 4a).

**Dispatches** (harness turns): T1 53, T2 37, T3 34, T4a 66, T4b 49, T5a 46, T5b 72, T6a 55, T6c 62, T6b 32,
T7 28, fixer 9, review A 55, review B 28. Turn-cap (~60) overruns: T4a, T5b, T6c (build waits and
mutation-harness steps); by raw tool-call count T4a, T5a, T5b, T6a, T6c also exceeded their briefs. Surfaced.

**Deviations from the plan.**
- Per-task reviews were batched into one two-lens final review (A: Opus, B: Sonnet; findings in
  `papers/f32_flip_slice2_review_A.md` and `_B.md`): no Critical, no Important, three Minor (A) + six Minor (B).
  Fixed in `217eebf`: stale `InputSignature.ofDenseInputs` docstring, a `Gen.lean` line-number reference, stray
  whitespace in CompileTest, stale `retag32` docstring.
- T6b also fixed `experiments/jax_bridge/EvalPlanAffineSmoke32.lean` (`retag32`), not listed in the plan: a real
  flip casualty (it failed `storageKindMismatch "B" float32 float64` on the flipped tree). Outputs are now declared
  by `explicitF64`, so its sampled corpus slice may differ slightly; the driver exits 0 (compile/run of the Lean side only).
- T5b: eight malformed-LHS rejection fixtures run all-f32 (`rejF32`, `rejSigF32`) instead of f64-declared: no f64
  declaration of `S` reaches their pinned error (every rank gives `rankMismatch`). Pins byte-identical (review B2).
- T7 also fixed a stale comment in `NonlinCompileTest` and trimmed `leanncd/AGENTS.md` Patterns (was ~4.8k chars)
  before editing, per slice-plan section 5; it is probably still over ~3k (estimate, not measured).
- Importing `Eval.ExplicitF64` makes `bias` a keyword: 37 `bias :=` literals in ScanCompileTest are `«bias» :=`.
- Correction to the 5a notes: the "observed `scatterOrAffineLhs`" for `capabilityBeforeInputScatter` under a declared
  f64 `S` was misattributed (review A3): declaring `S` at first-write rank trips Step 0 `checkReadRanksIn`
  (`rankMismatch`) before capability preflight, and `capabilityPreflight` decides `multiAxisScatterLhs` from the
  index expression alone. Not a production inconsistency.

**Parked (Rule 14), with cost.**
- Direct `Eval.evalScatter` has no f32 refusal (`rejectUnsupportedStorage`): pre-existing for explicit `f32`, now
  reaching every default scatter in direct callers with `decls = []` (ScatterTest, ScatterNonlinRejectTest);
  production callers refuse first. About 1 small Direct-path dispatch.
  **CLOSED** by the commit `fix(leanncd): evalScatter refuses binary32 names` (guard at the entry; ScatterTest and
  ScatterNonlinRejectTest callers re-spelled with explicit `f64` declarations).
- Dead fallbacks in `Compile.lean` still say `.f64` (the `.state si` arm, `compiled.stateSigs.getD`): verified dead
  by review A, no behaviour difference; about 0.2 dispatch if wanted for consistency.
- `PropertyOracle/ScanUnroll.lean` public `schedOfCase` is unwrapped (site table S cell); about 1 small dispatch.
- CompileTest rejection fixtures keep a plain `.tensor "Y"` (now f32) beside an explicit-f64 `X`; their pinned errors
  fire first, so they are not vacuous (review B).
- Everything in the plan's section 1 "Deliberately NOT done" table (bool-only defaults, binary32 `einsumOnly`, mixed
  precision, unprobed nonlinearities, bridge/JSON/legacy paths) is unchanged.

Nothing was pushed. Branch `f32-flip-slice2-proto` (local plus an origin backup) is kept until the merge.

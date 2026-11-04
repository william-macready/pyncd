# JAX pointwise and axiswise plan: authoring record

Non-live evidence for [`jax_nonlin_plan.md`](jax_nonlin_plan.md). The plan is the binding document;
this file records how it was authored, what was checked by command, what was not, the discrepancies
found, the decisions already taken and the decisions still open. Authored 2026-11-04 by one plan-writer
dispatch against the prototype worktree `<repo>/.claude/worktrees/jax-pointwise-plan` (branch
`worktree-jax-pointwise-plan`, base local `main` `f2616f54fd3a6eccc18a9d09d2870ced37ced5fa`, tip
`f66bbf1bd622c2b38bb6faca827af5d0efb44f5b`). Nothing was built or run; no code, patch or manifest was
changed. Two files were written: the plan and this record.

## Authoring process

- Template: `jax_scatter_plan.md` (read in full), the headings of `jax_scatter_plan_record.md` and
  `jax_scatter_record.md`, `jax_scatter_execution_brief.md` (read in full). The 11-section layout, the
  execution contract, the BLOCKED/STOP wording, the shell rules, the Rule 6 budgets, the stop point and
  the final-message checklist were reused with slice-specific values substituted.
- Values came from `jax_nonlin_files/FINDINGS.md` (read in full) or from commands run in this pass
  (listed below). No patch body was read in full; per-task descriptions rely on each commit's file
  statistics, FINDINGS, the T5 fixture diff and the new guard section of `EvalPlanCodegen.lean`.
- Tool calls used: 42 (the brief allowed about 40; the overrun is stated in the final message).

## Checked at authoring (by command, this dispatch)

- `git log --oneline f2616f54..HEAD` shows exactly the six commits T1 `e6c93834`, T2 `465aabbb`, T3
  `3efb82ef`, T4 `0893a66c`, T5 `5b6933ac`, T6 `f66bbf1b`, oldest first, with the subjects the plan
  uses. `HEAD~6` is `f2616f54fd3a6eccc18a9d09d2870ced37ced5fa`.
- File lists and line statistics per commit (`log --stat`): T1 2 files +157 -2; T2 5 files +644; T3 2
  files +126 -9; T4 1 file +21 -12; T5 2 files +51 -1; T6 6 files +56 -7. The union is 12 distinct files
  (10 under `leanncd/`, 2 under `papers/`).
- Every (task, file) blob after its owning commit and the 12 blobs at HEAD, by `git rev-parse
  <commit>:<path>`. At HEAD each file equals the blob of the LAST task that touched it (the plan's
  section 6 states this; the two tables agree row by row). `EvalPlanCodegen.lean` and `Nonlin.lean` have
  identical blobs at T1 and HEAD, which is what makes the Lean manifest valid from T1.
- `mutation-manifest.sh --check` on the Lean manifest printed: `manifest OK: 8 entries, 8 selected, every
  old-string unique`.
- Manifest entries counted with `python3 -I`: Lean 8 (`JN-T1-01..08`, all task T1, target
  `JaxExperiment`); Python 17 (`JN-P-01..15` task field T2, `JN-P-16..17` task field T3; every entry has
  `verifier` = `evalplan_nonlin_smoke`; `JN-P-11`, `JN-P-12` run binary64 only, `JN-P-15` binary32 only,
  the other 14 both).
- Existence (`ls`): the six patch files, FINDINGS, `lake-build.sh`, `mutation-manifest.sh`,
  `prepare-worktree.sh`, `setup-python.sh`, the four `run-evalplan-*.sh` older verifiers,
  `EvalPlanAffineCorpus.lean`, and `jax_scatter_mutations_python.json`.
- Step-kind enumeration in `EvalPlanCodegen.lean` (`rg -n "\.pointwise|\.axiswise|\.scatter|\.scan"` and
  a definition listing) and in `Executable.lean` (`rg` plus the `stepTiedToPreparedStep` body): the
  only code that matches on a plan step kind is `renderAffineNodesArray`, `lowerPlan` and
  `lowerCheckPlanToCandidate` in the codegen file and the wildcard in `stepTiedToPreparedStep`. The new
  guard section 11 of the codegen file was read in full.
- Value-grep: 74 hit lines in 41 files (the plan's section 9 command, run verbatim).
- The T5 diff of `EvalPlanNonlinSmoke.lean` shows three new fixtures per precision (`aw_neglarge`,
  `causal_big`, `relu_nan` and their `32` clones).

## Discrepancies

1. **Fixture count at T3.** The brief said T3's verify prints "its 15-fixture line". Measured: T5 adds
   3 fixtures per precision, so 15 is the count at the T5 tip; the count at T3 is 12 per precision and at
   T2 is 11. The plan writer inferred both; the controller then MEASURED them from the committed driver
   text (`git grep -c` of the `fixture64` call lines at each commit: 11 at T2, 12 at T3, 15 at T5, and
   +7 `#guard` lines in `EvalPlanCodegen.lean`, 74 to 81). The printed verifier line was observed only at
   the tip. The plan pins 15 at T5 and treats the T2/T3 counts as recorded, not gated.
2. **Order of the scatter manifest and the scatter verifier.** The brief's final order put the scatter
   Python manifest before `run-evalplan-scatter.sh`. The scatter plan states that the Python manifest
   needs the verifier run first, to create the generated modules in `jax_bridge/.cache`. In a fresh
   worktree the cache would be absent, so the plan runs `run-evalplan-scatter.sh` (step 6) before the
   scatter manifest (step 7). Judgement call; the end state the brief asked for is the same.
3. **T4 verify.** The brief allowed the scatter manifest "after T5 also fine". The plan defers it to the
   final order (it needs the scatter verifier's cache) and gives T4 a syntax check only.
4. **Commit hashes.** FINDINGS lists short hashes for T4 to T6 and notes T4 and T6 were amended. The
   plan quotes the full hashes measured on the branch; they are evidence only (the executor's commits
   will have different hashes; blobs, not commits, are the gates).
5. **FINDINGS numbers confirmed, none contradicted.** The `--check` line, the 8 and 17 counts, the six
   commits, the 12-file count and the Lean-manifest-valid-from-T1 claim all matched.
6. **Not a discrepancy but worth knowing.** The T6 value-grep hit `papers/predicate_boolean_backend_parity.md`
   still matches because the original sentence remains with the appended supersession note.

## Not verified

- No build, verifier, manifest run or corpus run was performed in this pass; every "Reported" value is
  FINDINGS'. `git apply --check` of the patch files against `f2616f54` was not run (the prototype
  controller replayed them with `patch -p1 --fuzz=0` and matched all 12 hashes).
- The exact text of T1's `renderPointwiseNode`/`renderAxiswiseNode` bodies, T2's runtime and verifier,
  T3's Lean fixture and T6's prose were not read in full; the plan describes them from statistics,
  FINDINGS and the guard section.
- Whether the "relu signed zero" pin line prints in both precisions or only in binary64.
- Whether the Lean mutation manifest and the nonlin Python manifest run in reasonable time (no duration
  is recorded in FINDINGS); the plan says "background".
- Whether `run-evalplan-nonlin.sh` leaves the scatter driver's `.cache` modules intact (the plan avoids
  the question by ordering).
- Whether any existing guard covers `.scan` on the `affineReference` render door or on `lowerPlan`
  (silent-cell rows 4 and the scan row of the matrix in plan section 8).
- Whether a pointwise or axiswise step under non-real storage (tropical, Boolean) is refused by the
  inherited plan-level `requireModeStorage` gate (plan section 8 row 8); not measured.
- The 5 `all five` / `All five` lines that sit in documents about other counts were not read.

## Decisions already taken (owner, from the brief and FINDINGS; not reopened)

D1 render-only (einsumOnly, evidence door, scan and unary reads stay refused); D3 the mask is evaluated
in Lean into a static `include` table, with one additive public wrapper in `Nonlin.lean`; D4 no support
gate (the checker already ran under the plan's own `tensorSigs`; `Executable.lean` untouched); tolerance
accepted instead of exactness, constants chosen before the full measurement and unchanged since
(binary64 `rtol 1e-12`/`atol 1e-14`, binary32 `rtol 1e-5`/`atol 1e-6`); relu bit-exact in EAGER only;
GPT executes in a fresh worktree `jax-pointwise-exec` and stops at READY FOR WHOLE-BRANCH REVIEW; nothing
is pushed; the prototype branch is never merged. Process weight: Full path, six patches.

## Silently-ignored or unpinned cells (candidates for a later defect slice)

Not created by this slice; no guard or mutant of the package kills a regression in any of them:
1. `renderAffineNodesArray` `.scan` arm (affineReference render door): throws today, nothing fails if it
   is changed. The only scan guard is on the evidence door.
2. `lowerPlan` (einsum) `.scan`: same shape; whether any guard hits it was not verified.
3. `stepTiedToPreparedStep` wildcard (`Executable.lean`): refuses any non-assign step through `_ => false`;
   reachable only through a hand-built candidate.
4. Plan-level storage gate for pointwise/axiswise plans under non-real storage: not measured.
5. Runtime unknown pointwise/axiswise `fn` raises `ValueError`; no mutant, and it is not verified that a
   fixture reaches it.
6. Benign and carried: `assignPlans` in `EvalPlanAffineCorpus.lean` drops non-assign steps; `run_assign`
   is assign-only. Both listed in the scatter plan as benign.

## Value-grep result (74 lines, 41 files) and classification

See the plan's section 9 table. The plan writer listed `papers/boolean_predicate_output_evalplan.md`
("JAX explicitly rejects Boolean, tropical, unary, contextful, Iverson, nonlinear, and scan") as a (c)
candidate without reading its context; the controller read it (it is an instruction inside an old plan,
under "Update current-state docs to say:") and reclassified it (a) history. The independent review then
found the one real stale-live sentence, `papers/jax_evalplan_architecture.md` (wrapped over three lines,
so invisible to the line-based grep; the plan now carries a multi-line pattern for it). Borderline
`papers/f32_evalplan.md` ("no JAX scan, scatter, nonlinearity ... exists", carries a historical-baseline
note that names scatter but not pointwise/axiswise). Already updated by T6 (b):
`papers/predicate_boolean_backend_parity.md` JAX row; Plan `AGENTS.md`, `README.md`,
`f32_jax_evalplan.md` no longer match. "five drivers": zero hits, the only driver-count prose is in
`check-lean-drivers.sh` and says "six" at the tip. About 60 other hits are "all five" in unrelated
history; they were classified by file name and matched phrase only.

## Open decisions for the owner

1. **Brief.** No execution brief was written (only two files were asked for). The plan's section 1
   carries the preamble and rules, so a brief equivalent to `jax_scatter_execution_brief.md` is a short
   copy with names substituted; the owner or controller supplies it.
2. **Stale-live sentence.** RESOLVED by the controller: it edits `papers/jax_evalplan_architecture.md`
   (the wrapped sentence) and extends the `papers/f32_evalplan.md` note after the slice lands. The
   executor reports and does not edit (Rule 14); about 0.5 dispatch.
3. **Unpinned cells above.** Whether to add guards for the scan render door (a one-line `#guard` on the
   `affineReference` door with a scan plan) and for the non-real storage gate on pointwise/axiswise
   plans; small, Direct-path sized. Not in this package.
4. **Package commit.** Land the package (plan, record, FINDINGS, patches, two manifests) on `main`
   before the executor starts (Pre-flight A step 2 requires it); the commit subject is not pinned.
5. **Lean manifest timing.** RESOLVED after the independent review: the plan runs the Lean manifest
   once, right after T1's build (dispatch 1), not in the final order, because T2 to T6 never touch
   `EvalPlanCodegen.lean` and the final hash check covers it; this keeps dispatch 2 under budget.
6. **Corpus.** First measurement after this slice; if it fails the plan stops and reports (no repair).

## Final blob table at authoring (HEAD `f66bbf1b`, for the controller to diff with `git rev-parse HEAD:<path>`)

Identical to the plan's section 6; not repeated here to avoid two copies drifting.

## Controller verification and independent plan review (2026-11-04)

Controller, before the review (all run by the controller): the six patches replay onto base `f2616f54`
with `patch -p1 --fuzz=0` and 12 of 12 touched files hash identically to the tip (repeated after the
T6 amend); all 30 blob rows in plan sections 5 and 6 equal `git rev-parse <commit>:<path>` (script in the
controller's scratchpad); the T2/T3/T5 fixture counts (11, 12, 15 per precision) and the seven new
`#guard`s (74 to 81) measured from committed text; full build 8844 jobs; nonlin differential 15 + 15;
Python manifest 17/17 and Lean manifest 8/8 (with the recorded `expect` strings); scatter manifest 16/16
with the T4 runner.

Independent reviewer (one lens, fidelity and cold-executability; read-only): verdict **READY WITH FIXES**,
no blocker; it made about 50 tool calls against a 40-call cap (Rule 6 breach, stated by the reviewer). The
plan writer also breached (44 against 40). Findings and adjudication:

| ID | Severity | Finding | Adjudication |
| --- | --- | --- | --- |
| F1 | MAJOR | one real stale-live sentence in `papers/jax_evalplan_architecture.md`, wrapped over lines, invisible to the line grep; plan said the list was empty | FIXED in plan section 9 (table row, multi-line `rg -U` pattern tested against the real file, list updated); the controller edits the paper after landing |
| F2 | MAJOR | "the executor's own new files are excluded by the globs" is false (`EvalPlanNonlinSmoke.lean:142` is one of the 74) | FIXED (stated as class (a)) |
| F3 | MAJOR | Pre-flight A step 1 not evaluable ("or a descendant", contradictory "continue only if... otherwise do not stop yet") | FIXED (`merge-base --is-ancestor`, name-status diff, worktree HEAD equals `main`) |
| F4 | MAJOR | apply/commit commands never given literally; `prepare-worktree.sh` cannot be run "from inside" under the shell rules | FIXED (literal 5-step procedure in section 5; cwd instruction in section 1; rerun guard for an existing branch) |
| F5 | MAJOR | section 8 overstated the mutation pins for the unmasked axiswise path (`JN-T1-03/04/07` die on the masked guard) | FIXED (row 2 and the matrix cell now say no Lean mutant targets the unmasked branch) |
| F6 | MINOR | `JN-T1-06`'s `expect` line 2278 looks wrong | FIXED (explained: line number in the mutated file) |
| F7 | MINOR | plan left resolvable fact open (the four pin lines print once per precision) | FIXED |
| F8 | MINOR | section 10 lacked slots for final steps and several verify outputs | FIXED (item 3 expanded, new 3b) |
| F9 | MINOR | README stat `+44` should read `+43 -1`; `JN-P-16/17` task label; no rerun guard | FIXED |
| F10 | MINOR | dispatch 2 budget tight (about 45 to 55 turns) | FIXED: the Lean manifest moves to dispatch 1 right after T1's build (not repeated), the final order drops it, and a dispatch stops at a boundary near 55 turns |

Not verified by the reviewer and not by anyone yet: the job counts and timings that need a build, the
`check-lean-drivers.sh` "six" line, the corpus after this slice, any GPU run.

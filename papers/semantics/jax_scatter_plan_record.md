# JAX scatter plan: authoring record

Evidence for [the plan](jax_scatter_plan.md). Not live: kept out of the plan so the plan stays short.
Source of every value below: [`jax_scatter_files/FINDINGS.md`](jax_scatter_files/FINDINGS.md) and the
files on disk, re-checked at authoring (see "Checked at authoring").

## Authoring process

1. **Prototype dispatch 1** (explore and prototype, T1 to T5): about 100 tool calls and about 240k
   subagent tokens; peak context not measured. It could not write its own findings file (the harness
   blocked it), so the controller transcribed its report into `FINDINGS.md`. It found one surviving
   mutant (`JS-T1-05`) and added T3 to kill it.
2. **Prototype dispatch 2** (T6, fast mode): about 57 tool calls and about 125k subagent tokens. It
   could not commit (git was refused in its session); the controller committed the code and cut
   `T6-fast-mode.patch`.
3. **Plan dispatch** (this one): reads only on-disk artifacts, changes no code, writes the plan and this
   record. Budget set by the controller: at most about 40 turns, context peak at most about 200k.
4. The controller then verified the prototype independently (list below).

**Rule 6 breach.** Prototype dispatch 1 made about 100 tool calls against the 60-turn cap and reported
it; dispatch 2 stayed under the cap with no slack (57 calls). The plan therefore splits execution into
two dispatches (plan section 1) and tells an executor to stop at a task boundary when it nears 60 turns.
Authoring token cost across the three dispatches is not measured as a single figure here; the
prototype's own figures are the two above.

## Controller verification (copied from FINDINGS, "Controller verification")

Run in the worktree after T6, observed:

- `lake-build.sh ... LeanNCD Tests JaxExperiment`: `Build completed successfully (8844 jobs)`
  (measured at the T5 tip; T6 changes no Lean file).
- `mutation-manifest.sh --check ... jax_scatter_mutations_post.json`: `manifest OK: 6 entries`; full
  run `6/6 cycles passed`.
- `run-evalplan-scatter.sh`: 10 f64 + 5 f32 ordered bit-identical; fast-mode lines as in the plan.
- `run-evalplan-affine.sh`, `run-evalplan-affine32.sh` (re-run after T6): pass, final lines unchanged
  (`... Dense agreement passed`; `56 binary32 fixtures, 160 eager/jit output checks`).
- `run-evalplan-affine-corpus.sh` (3,832 cases, about 10+ min): passed at the T5 tip
  (`full Wave C affine corpus -> ordered JAX reference -> Dense agreement passed`). **Not re-run after
  T6** (the runtime change is additive with an `ordered` default); the plan makes the executor re-run it.
- `mutation_python_manifest.py ... jax_scatter_mutations_python.json`: 16/16 PASS.
- Patch chain: T1 to T7 applied in order with `git apply` onto a throwaway worktree at base `2cf92209`;
  the 11 touched files hash identically to the branch tip (0 mismatches).

## Git-guard note

In the controller's session, and in this plan dispatch, a worktree-isolation guard refuses plain
`git ...` and `rtk git ...` and any command it cannot prove stays inside the worktree (compound
commands, `$(...)`, pipes, globs and computed arguments next to a git-looking word). `/usr/bin/git`
with plain, non-compound commands works and targets the worktree. The plan's commands use
`git -C <worktree>` in B5c style; an executor whose environment has no such guard is unaffected.

## Checked at authoring (this dispatch)

- Every path the plan names was `ls`-checked (27 paths: the six patches, FINDINGS, both manifests, the
  scripts, the 11 touched files' directories, and the six papers named in plan section 9).
- Full blob hashes for all 16 post-apply (task, file) rows were read from
  `git log --raw --no-abbrev 2cf92209..a76b6b01` (one run); every 8-character prefix in FINDINGS equals
  the prefix of the real blob. The plan carries the full 40-hex values.
- `git apply --check -R` passes for `T6-fast-mode.patch` and `T4-python-mutation-runner.patch` against
  the branch tip, i.e. the tip carries those post-images. T1, T2, T3 and T5 cannot be reverse-checked
  at the tip (later patches touch the same files); the controller's chain replay is the evidence for
  them, and the blob rows above cover their post-images.
- Counts re-derived from the manifests on disk: Lean manifest 6 entries (`JS-T1-01..06`); Python
  manifest 16 entries (`JS-T2-01..07` = 7, `JS-T6-01..09` = 9). `RTOL` literal in
  `evalplan_scatter_smoke.py` is `{"float64": 1e-12, "float32": 1e-5}`. `JaxExperiment` globs only
  `EvalPlanCodegen`, so the new driver adds no library job.
- Identifiers cited in the plan were `rg`-checked at the tip: `checkJaxScatterSupport`,
  `renderScatterNode`, `requireJaxScatterSupport`, `JaxCodegenError.scatterPlacementOutOfRange`,
  `b5ScatterRejectedBeforeEmission`, `b5ScatterPrepared`, `routeUnsupportedMultiWriter`,
  `stepTiedToPreparedStep`, `_run_scatter_node`, `_exec_node`, `SCATTER_MODES`.
- The verifier's printed lines (fixture count, collision order, signed-zero and gradient pins, the
  fast-mode lines) were read from `evalplan_scatter_smoke.py`; the signed-zero/gradient lines are
  inside an `if _DT == "float64"` block, hence binary64 only (plan T2 and T6 say so).
- The stale-doc value-grep from plan section 9 was run: 183 hit lines.

## Discrepancies

1. **Build job count.** FINDINGS' executor table reports `8843 jobs` (dispatch), its controller section
   reports `8844 jobs` (at the T5 tip). The records of F3-a and F3-b1 give 8844 for the base (`main`
   before this slice), and the slice adds no library module. The plan uses **8844** and tells the
   executor to state any other count rather than accept it silently. Not resolved by measurement here
   (no build was run in this dispatch).
2. **Stale doc not in FINDINGS' list.** FINDINGS lists two papers as stale. The authoring grep found,
   in addition: the B5 bullet of `leanncd/LeanNCD/Eval/Plan/AGENTS.md` (a live Intent Layer node that
   says the JAX codegen fixture requires prepared scatter nodes to refuse before emission; only the
   einsum refusal still holds), and candidates in
   `papers/semantics/additive_production_decision_note.md`, `papers/semantics/additive_b5_design.md`
   and `papers/f32_evalplan.md`. None are edited (plan section 9); see open decision 1.
3. **Hash width.** FINDINGS gives 8-character blob prefixes only; the plan gives full hashes (prefixes
   agree, see above). No mismatch.
4. **Header cosmetics.** `T1..T5` patch headers read `[PATCH n/5]` and `T6` reads `[PATCH]` (format-patch
   artefacts); `git apply` ignores them. No effect.
5. **Dispatch-1 mutation count wording.** FINDINGS says the Python manifest has 7 entries (dispatch 1)
   and 16 (controller, after T6); both are right at their time. The plan uses 16 (7 + 9).
6. **Leftover files in the prototype worktree.** `leanncd/experiments/jax_bridge/.cache` there holds
   `gen_scatter32.py` and `gen_scatter64.py`, which the committed scripts do not generate (their
   outputs are `generated_evalplan_scatter_smoke64.py` / `32.py`). Gitignored, not in any patch;
   irrelevant to a fresh executor worktree. Recorded only because it is on disk.

## Not verified

- The patches were not replayed here with a build; the controller replayed the chain on a throwaway
  worktree and matched all 11 hashes, but that replay did not build. The executor's apply checks,
  hash table, builds and manifests are the gates.
- **The 3,832-case corpus after T6** (see above): the executor must run it.
- **No GPU or non-CPU XLA run.** Fast mode's tolerance path is exercised only synthetically (the 1e-3
  perturbation self-test); on this CPU even colliding fixtures are bit-identical in fast mode, so
  `RTOL` has never been exercised by a real difference.
- The Python mutation `expect` strings are generic `AssertionError` source lines, so a mutant dying for
  the wrong reason would not be detected by them (plan section 7 lists the caveats).
- `JS-T6-03/04/05` are killed only by the jaxpr `scatter-add` presence check, by construction.
- Plan section 3's descriptions of the fold and gate are paraphrases of FINDINGS and of the patch
  prologues, not re-derived from running code in this dispatch.

## Independent plan review (one lens: fidelity and cold-executability), 2026-11-03

A fresh reviewer replayed T1 to T7 onto a throwaway worktree at base `2cf92209` (every `apply --check`
and `apply` passed; every blob and `--stat` figure matched the plan) and read the plan as a cold
executor. Verdict READY WITH FIXES; 12 findings, all adjudicated:
- Pre-flight order and undefined `<repo>`: FIXED (split into Pre-flight A and B, placeholders defined,
  `git -C <repo> worktree add`, STOP when the package has not landed).
- Stale "through T6", "six commit subjects", "after T6" heading: FIXED.
- **T1 carried a stray whitespace edit** to the private `jaxSupportOk` signature in `Executable.lean`
  while the plan said "purely additive": FIXED in the patch (hunk line restored; counts in the hunk
  header unchanged; T1 now +187 -34; Executable.lean blob `205decd661a6...`). Rebuilt green at 8844
  jobs and re-replayed T1 to T7 with 0 blob mismatches. The prototype branch got a matching revert
  commit so its tip equals the replay.
- No review gate before merge (Rule 13): FIXED. The executor now stops at "READY FOR WHOLE-BRANCH
  REVIEW" and does not merge; the owner's controller reviews and merges.
- `--out` results file would dirty the worktree: FIXED (do not pass `--out`).
- Value-grep count 183 vs 184, missing offline-pip STOP, row 6 arm text, "package unavailable" STOP:
  FIXED.
- Not changed: record and FINDINGS sentences that still describe the original T1 to T6 numbering
  (non-live history; FINDINGS has the T1 blob note).
Not verified by the reviewer: any Lake build or Python run. The controller re-ran the full build after
the T1 fix (8844 jobs, green) and re-ran the Lean mutation manifest (`6/6 cycles passed`, every file
restored byte-identically). The Python verifiers were not re-run after the fix: it touches no Python.

## Open decisions for the owner

1. **RESOLVED by the controller after this dispatch: the stale B5 bullet in
   `leanncd/LeanNCD/Eval/Plan/AGENTS.md`** (Discrepancy 2) is now fixed by patch T7
   (`T7-agents-stale-bullet.patch`, also adds `run-evalplan-scatter.sh` to the JAX run row), so the
   plan has seven patches and the final `AGENTS.md` blob is `ffe68114...`. The three papers stay
   unedited.
2. **RESOLVED by the controller: how the package reaches the executor.** The prototype branch
   `worktree-jax-scatter-plan` also carries the prototype CODE commits (T1 to T7 already applied under
   `leanncd/`), so it must NOT be merged to `main`: the executor's patches would no longer apply.
   Only the package files (plan, record, `jax_scatter_files/`, `jax_scatter_patches/`, the two
   mutation manifests) are landed on local `main`, as one docs-only commit. The prototype branch is
   kept as evidence until the slice lands, then deleted. The plan's path-limited `git checkout`
   fallback therefore normally has nothing to do.
3. **Execution split.** Plan section 1 suggests two dispatches (T1 to T3 plus Lean mutations; T4 to T7
   plus verifiers and record). Say if you want one.
4. **Corpus run.** It costs 10+ minutes of wall clock and must be serial with everything else; the plan
   makes it mandatory. Drop it only by editing the plan.
5. **Parked items** (plan section 4) have no owner; the evidence-path item (about 3 dispatches, touches
   core `Executable.lean`) is the only one that is a real feature gap rather than hygiene.

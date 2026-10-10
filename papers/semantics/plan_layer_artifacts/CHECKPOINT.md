# Checkpoint: Part V Plan-layer slice 1

Written 2026-10-10. Read this first when resuming. Companion memory note:
`part-v-plan-layer-slice1.md` in the Claude project memory directory.

## 1. Where everything is

| Thing | Location / value |
| --- | --- |
| Prototype worktree | `/Users/williammacready/code/python/pyncd/.claude/worktrees/plan-layer-slice1` |
| Prototype branch | `worktree-plan-layer-slice1`, verified code HEAD `11dd4c17` (this file is the only commit after it) |
| Prototype base | `3d721f96` (stale: local `main` is now `3ddea62b`) |
| Local `main` | `3ddea62b`, 14 commits ahead of `origin/main`, **not pushed** |
| Notes (read in order) | `a1_notes.md`, `a2_notes.md`, `a3a_notes.md`, `a3b_notes.md` in this directory |
| Not mine, do not touch | worktrees `pyncd.worktrees/close-raw-source-admission-proof*` and the other `agents/*` worktrees (another session's Track 1 work) |

Nothing from this slice is merged to `main` or pushed. No agents or builds were
running at the checkpoint.

## 2. What is done (verified)

Prototype phases A1, A2, A3a and A3b are complete. I verified the final state
myself: tree clean, full default build green (8,780 jobs), and no `sorry`,
`axiom`, `native_decide` or `admit` in any Plan file.

- Library: 8 modules under `leanncd/LeanNCD/Semantics/Plan/` (about 2,000 lines): `Syntax`, `Batch`, `Memory`, `Step`, `Simulation`, `Validity`, `Run`, `Correctness`, plus the `Plan.lean` aggregator.
- Tests: 9 modules `leanncd/test/Semantics/Plan*Test.lean` and `PlanFixtures.lean` (about 750 lines), all listed by module name in the lakefile `Tests` globs.
- Headline results: `batch_execution` (Lemma 32.1), `step_R` and `step_failed` (simulation and failure matching), `checkPlan_sound`, `run_R`, `terminal_adequacy` (Lemma 31.2), and `done_correct`, `failed_correct`, `done_or_failed`, `done_of_model`, `done_iff_model` (Theorem 31.3 a, b, c). `cov1_of_cov2_pubOrder` proves defect N6.
- Slice-1 profile: singleton commands, transactional failure, single sort Q, dense non-reused buffers, explicit `initZero`, no implementation errors.

## 3. Decisions waiting for the user

1. **Go or no-go on patch emission** (recommended: go).
2. **Task partition** (proposed): T1 `Syntax` + `Batch`; T2 `Memory`; T3 `Step` + `Simulation`; T4 `Validity` + `Run` + `Correctness`; T5 `Plan.lean`, `Semantics.lean` import, lakefile globs, all test modules.
3. **Keep or drop `checkCov1Complete`** in `checkPlan` (sound to drop given N6; the prototype kept it because `missingOcc` reports it first).
4. **Pushing `main`** (14 commits ahead, including other sessions' work). Push only on request.

## 4. Pre-flight before continuing

1. Run `ListAgents` (must show none) and `/usr/bin/git -C <worktree> status --short` (must be empty).
2. **Base drift.** `main` moved after the prototype's base (another session landed raw-source admission: new `Source/Raw*` modules, `DSL/Pipeline/Structural.lean`, a lakefile glob line, AGENTS edits). A dry-run `git merge-tree --write-tree main worktree-plan-layer-slice1` was clean (no conflicts). Before emitting patches: in the prototype worktree run `/usr/bin/git -C <worktree> rebase main`, resolve any trivial conflict in `leanncd/lakefile.toml` or `leanncd/LeanNCD/Semantics.lean` (keep both sides' lines), then rebuild fully with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd` and re-run the `sorry` grep. Record the new HEAD in the memory note.
3. `main` also moved the Semantics `AGENTS.md`; the Plan node must be added fresh in the execution session, not carried in the patches.

## 5. Next dispatch: patch emission (ready to paste)

Use model `opus`, background, preamble from `.claude/skills/new-slice/SKILL.md`
("Subagent brief preamble"), budget by harness tool uses (aim 55, stop 65).

> Goal: turn the compiled prototype on branch `worktree-plan-layer-slice1` (rebased on current main) into five per-task patches that replay exactly. Follow the pattern in `papers/semantics/coordinate_ranks_finite_measure_artifacts/emit-patches.py` and `computable_reference_executor_artifacts/` (read both first). Tasks: T1 `Plan/Syntax.lean` + `Plan/Batch.lean`; T2 `Plan/Memory.lean`; T3 `Plan/Step.lean` + `Plan/Simulation.lean`; T4 `Plan/Validity.lean` + `Plan/Run.lean` + `Plan/Correctness.lean`; T5 `Plan.lean`, `Semantics.lean` import, `lakefile.toml` globs, `test/Semantics/Plan*Test.lean`, `PlanFixtures.lean`. Build intermediate trees in a SCRATCH worktree (never the prototype worktree), one commit per task from the final file contents, and build each with a module-level target to prove it compiles alone; if a file depends on a later task, move it later and record why. Emit `papers/semantics/plan_layer_patches/0N-*.patch` plus `manifest.json` (sha256, files, symbols), a replay check that applying all patches in order to the base gives a tree byte-identical to the prototype HEAD for the shipped paths, and `plan_layer_artifacts/evidence.json` + `emit-patches.py`. Do not edit proofs. Report tool-use count, build results per task, and any boundary you had to move.

## 6. After that

1. **Phase B (fresh dispatch):** write the plan (at most about 800 lines, no transcribed code) from the notes and patches only: rationale, decisions, the section 2 audit (case by class tables for the checks and kernels), fixture and mutation lists (the consolidated table is in `a3b_notes.md`, with observed `expect` text), prose edits. Ship `plan_layer_mutations_post.json` for `leanncd/scripts/mutation-manifest.sh` and a separate record.
2. **Two review lenses:** soundness (R, validity, theorem hypotheses) and spec-Lean fidelity.
3. **Execute** on a fresh worktree from current `main` (`new-slice`): apply patches, controller runs the mutation manifest and the full build, merge locally.
4. **Docs sweep** using the SPEC RESTATEMENT DRAFT in `a3b_notes.md`: restate relation R, Definition 31.1 (per command prefix, safety / progress / terminal), Lemma 31.2 and Theorem 31.3 in the spec; add proof-status rows (Lemma 31.2, Theorem 31.3, Lemma 32.1); add a new section to the Lean path doc and regenerate its TOC; add a `Plan/AGENTS.md` node (injected sections at most about 3k characters). Spec findings to apply: D1 to D3, D6, D10, N1 to N8, D5 (transactional failure snapshot differs from the executor; the failure case compares fails and no-model only).

## 7. Lessons and warnings

- Harness tool uses ran about 20 percent over what agents self-reported (A1 102, A2 147, A3a-finish 64, A3b 78). Budget by tool uses.
- After stopping an agent, always run `git status`: one was killed mid-mutation and left a mutated `Validity.lean` (restored with `git checkout`).
- Inside `Program.Plan`, bare `consume`/`publish` resolve to the noncomputable `Program` versions; write `Executor.consume` and `Executor.publish`. Force `List.decidableBAll` for bounded quantifiers. `prefix` is a Lean keyword (use `prefixAnn`). `Layout` is already taken (the spec's layout view is `SlotView`).
- Do not merge the prototype branch directly: the process is patches, plan, execution on a fresh worktree.
- The spec is a protected input until the docs sweep. Do not push without an explicit request.

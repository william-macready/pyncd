# Brief: Part V buffer reuse and aliasing (Plan layer, slice 4)

Status: brief for an agent starting the slice. Facts checked against `main` at `42102087` (2026-10-11).
Audience: a coding agent with no memory of this project. Design questions below are recommendations to
confirm with the repo owner (William), not decisions.

## Your task and first deliverable

- **Task:** make a physical storage slot reusable by a different logical address once its previous occupant is retired.
- **Path:** this is a Full-path change, because it changes `Memory`, `place`, `R` and `Valid` interfaces.
- **First deliverable:** don't write code first. Read the files below, run a short design discussion with William (the repo owner) one question at a time, then write a design spec for him to approve.
- **Spec template:** `docs/superpowers/specs/2026-10-11-buffer-retirement-design.md`.
- **Decisions below:** every item in "Design questions" is a recommendation to confirm with William, not a decision.

## Project in three sentences

`leanncd/` is a Lean 4 + Mathlib formalization of a tensor-equation language (paths below are relative to the repo root). Part V of the spec, `papers/semantics/tensor_logic_semantics.md` (Sections 29-34), defines execution plans (commands over concrete memory) and proves they refine a reference machine. Slices 1-3 are done and pushed: plans of `acc`, `pub`, `initZero` and `retire` commands, fused commands (by expansion), and a fault-oracle wrapper.

## State of the tree

- **Branch:** `main` at `42102087`, pushed and clean.
- **Build:** `bash leanncd/scripts/lake-build.sh <absolute path to leanncd>` ends with `Build completed successfully (8793 jobs).`
  - It prints four pre-existing `declaration uses sorry` warnings, listed in `leanncd/SORRY_INVENTORY.md`.
  - Never run `lake` from the repo root.
- **Code:** `leanncd/LeanNCD/Semantics/Plan/` has 11 modules, about 3500 lines.
- **Tests:** `leanncd/test/Semantics/Plan*Test.lean` holds 281 fixtures by the `rg -c` method: 149 `#eval check` rows plus 132 `example`/`theorem` items.
- **Mutation manifests:** four of them, in `papers/semantics/plan_layer*_mutations_post.json`, with 20, 15, 9 and 10 cycles.

## What exists that you build on

- **Retirement:** `Ann.retire` clears slots. `Pub` is the logical published set, and `Live = Pub \ Ret` is the readable set.
- **Plan checker:** `Valid` and the computable `checkPlan`, with `checkPlan_iff : checkPlan = true ↔ Valid`.
- **`R` fields:** `R` (in `Memory.lean`) has fields `reach`, `pending`, `published`, `pubSlot`, `accSlot`, `retain`, `dead` and `retPub`.
  - `dead` says a retired slot holds `none`.
  - Reuse is expected to reshape `R`.
- **Regression net:** concrete retire plans have `R` instantiated at every command boundary (`PlanRetireTest.lean`, section 9, plus `chainMem`).
- **Existing fixture donors:**
  - `rtInitAfter` has an `initZero` after a retire. It is the natural reuse fixture, once the new address is assigned the retired address's physical slot.
  - `rtChain`, `rtMulti` and `rtFusedOk` cover retire shapes.

## Why the current code cannot reuse a slot

`Memory.lean` defines three things:

1. `Slot σ := (t : σ.Tensor) × Fin (canonicalLayout ...).count`. A slot belongs to a tensor.
2. `place : Address σ → Slot σ`, global and injective (`place_injective`).
3. `Memory K σ := (ξ : Slot σ) → Option (K (σ.signature ξ.1).sort)`. The value sort of a slot is its tensor's sort.

Every kernel writes or reads through `place`, and the injectivity lemmas (`place_injective`, `slotView_injective`) are load-bearing in the step proofs. There are about 40 uses of `place` across `Memory`, `Step`, `Simulation` and `Run`, and a few dozen in tests.

Reuse needs a physical buffer notion separate from tensors, as spec 30.1 says ("a finite buffer collection with capacities").

## Spec sections to read first

- **30.2:** resource views. It requires the layout view λ to be injective on its domain, and says "more permissive aliasing needs a separate justification".
- **30.3:** storage changes. It covers retirement and reuse, and "matching printed axis names or equal extents is not a layout proof". Its last paragraph says reads of old contents must precede an overlapping write, or a snapshot is needed.
- **30.4, 31.1:** the refinement relation and the validity clause table.
- **33.2-33.4:** the two-buffer scan example, full-history retention, and in-place snapshots. These are later slices, not this one.

## Design questions, each with a recommendation

1. **Physical buffers and placement.**
   - Recommend explicit `Buffer` values (an id, a sort and a capacity) plus a per-plan `placeOf : DefAddr → (buffer, index)`.
   - The Memory domain becomes (buffer, index).
   - The current profile is the special case "one buffer per tensor, canonical placement", so every existing theorem and fixture must stay an instance of it.
2. **Where placement lives.**
   - Recommend a static per-plan assignment, with the existing pc-dependent `SlotView` deciding which resources are represented.
   - The alternative is dynamic alloc and relocate commands, which is heavier and belongs with copy/relocate.
3. **Safety condition.**
   - Recommend a new `Valid` clause: at every pc the layout view is injective on its domain, meaning live addresses plus materialised accumulators.
   - It must be computable, with a `checkPlan_iff` that stays exact. This replaces the global `place_injective`.
4. **`dead` generalised.**
   - Today `dead` says a retired address's slot is `none`, which breaks once the slot is reassigned.
   - Recommend an invariant "every slot not in the image of the layout view holds `none`".
   - Verify this against `Start`, `execInit`, `execAcc` and `execRet` before committing to it.
5. **Types.** A buffer's sort must match its addresses' tensor sorts, and the index must fit the capacity. Decide whether this is enforced by dependent types or by a validity clause. `PlanMultiSortTest` (ℤ and ℚ) exercises sorts.
6. **Kernels.**
   - Keep them non-in-place. `execAcc` already scans on the read view and commits afterwards, so reads precede writes.
   - Leave in-place updates to the 33.4 slice.
7. **Outputs and inputs.** Outputs are never retired, so never reused. Inputs have separate storage and are never retired.

## Suggested first slice and acceptance

- **Scope:**
  - Reuse across addresses of the same sort.
  - Static placement.
  - The new safety clause and its checker.
  - `step_R` and the `*_correct` theorems carried over.
  - Fused and `Faults` parity by expansion, as before.
- **Acceptance fixtures:**
  - `rtInitAfter` under a placement that aliases the new address (point 2) to the retired one (point 0) is valid, runs `done`, decodes correctly, and has `R` at every boundary.
  - Its rejecting twin aliases point 2 to a still-live point 1. The checker must reject it, and you should observe what the run does rather than assuming.
- **Explicitly out of scope:**
  - The spec 33.2 scan example. No history program exists among the Part V fixtures, so building one is its own task.
  - Copy and relocate, in-place kernels, retiring inputs, and concrete implementation-error sources.

## Rules of the repo

- **Process:** read `CLAUDE.md` and `leanncd/AGENTS.md`. Process notes are in `.claude/skills/slice-plan/SKILL.md` and `.claude/skills/new-slice/`; `papers/semantics/plan_layer_slice3_plan.md` and its record show the pattern.
- **Authoring order:** prototype and compile, emit per-task patches, then write the plan from those artifacts.
- **Worktree:** work in a git worktree off local `main`. `bash .claude/skills/new-slice/prepare-worktree.sh` fast-forwards it and syncs `.lake`, so Mathlib never cold-builds.
- **Shipping:** merge locally with `--no-ff` after a green build and review. **Do not push unless William asks.** No force operations.
- **Scope:** do not widen scope. Park side issues with a one-line cost note.
- **Spec edits:** restatements go in the "As formalized" paragraphs and the proof-status rows. Do not rewrite the general contract text.
- **Review:** run a fresh review with two lenses, soundness and spec-to-Lean fidelity, before merging. Every review so far found at least one false sentence in the docs.

## Pitfalls

- **Manifests carry line numbers.** The manifests mutate `Batch`, `Faults`, `Fusion`, `FusionCorrectness`, `Memory`, `Simulation`, `Step`, `Syntax` and `Validity`. Their `expect` strings hold `File.lean:L:C`.
  - Any edit that changes a line count in those files means re-running the manifests unfiltered and repairing only the locations.
  - `mutation-manifest.sh --check` is free. The `--task` filter works.
- **Mutants die at library proofs, not at fixtures.** To check that a fixture row discriminates, temporarily `sorry` the broken proofs, build the test module, and restore with `git checkout --`.
- **Nets need the right steps.** `dead` and `retPub` are trivially true until something is retired. For aliasing, the checks must exercise writes into a reused slot, not just boundaries before it.
- **Rationals and `rfl`.** Kernel `rfl` cannot normalise rational sums like `3 + 1`. Use `#eval check` rows for arithmetic and `rfl` only for `none` or literal values.
- **Stale claims.** Two inherited "still open" claims this month were already fixed. Re-check against the tree before acting on any list of known gaps.
- **Library pitfalls.** See the Pitfalls section of `leanncd/LeanNCD/Semantics/Plan/AGENTS.md`. Examples: write `Executor.consume` inside `Program.Plan`, force `List.decidableBAll`, and `prefix` is a keyword (use `prefixAnn`).

## Definition of done

- **Build:** full build green, with no new `sorry`, `admit`, `axiom` or `native_decide` in the Plan files.
- **Axioms:** `#print axioms` on new theorems shows only `propext`, `Classical.choice` and `Quot.sound`.
- **Manifests:** all four old manifests pass, and a new manifest covers the new clause.
- **Docs and memory:** docs updated, with counts re-measured, and `Plan/AGENTS.md` updated.
- **Report:**
  - What changed.
  - What was verified and how.
  - Anything skipped, with the reason.
  - Deviations from the approved design.

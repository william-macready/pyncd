# Additive collection, slice 1 (S1): implementation plan

Status: prototype complete; this plan executes it by applying the verified per-task patches.
Base: local `main` at `b0d37f2f` (decision note + spec amendments landed, no code).
Branch / worktree: `worktree-additive-collection-slice1` at
`/Users/williammacready/code/python/pyncd/.claude/worktrees/additive-collection-slice1`
(Lean project `<wt>/leanncd`). The prototype chain `proto-additive-slice1-p1` -> `-p2a` -> `-p2b`
(tip `13ce43d5`) is the compiled source of every patch; do not merge it.
Rationale: `papers/semantics/additive_production_decision_note.md` (§B, §C, §E, §F).
Authoring-verification evidence (patch replay, manifest check, budget, claim greps) is in
`papers/semantics/additive_collection_slice1_record.md`, not here.
Artifacts (observed values, audits, doc sweep, patches):
`papers/semantics/additive_collection_slice1_artifacts/` (`p1_`, `p2a_`, `p2b_` `findings.md` /
`observed.md`, `p2b_docsweep.md`, `p1_patches/`, `p2a_patches/`, `p2b_patches/`).

## 0. Goal, process weight, fixed decisions

**Goal.** A tensor written by several plain statements is the sum (predicate: OR) of the writers'
values, not the last write, in every production entry:
1. a desugar `desugarMultiWriters` renames writer `k` of `T` to a private `T#k` and inserts one sum
   collector `T := T#1 + ... + T#n` after the last writer (`DSL/Pipeline/Collect.lean`);
2. readiness is all-writers, so a reader waits for every writer (`eligible`, `topoSortFuel`,
   `isTopoOrdered`, hence `schedule`);
3. the reference evaluator, the checked plan (`prepareEvalPlan`) and `route` all consume the collected
   schedule; private names are hidden from `evalScheduled` env and from `materializedNames`;
4. a supplied input naming a defined tensor is an error in both backends (decision B3);
5. the source oracle's `crossStatementOverwrite` refusal is deleted; F14/F15/D10 become value-compared.

**Process weight: Full.** New capability (additive collection) with a soundness surface across the
reference evaluator, the checked plan, `route` (and `Bridge/Agreement.lean`'s plumbing lemma) and the
differential oracle; 8 tasks, 7 prototype patches, 30 mutation cycles.

**Fixed decisions (do not reopen).**
- Overwrite is removed, not kept as an option. No flag.
- Collection is `collectDefinitions` (= `desugarMultiWriters` + an `isTopoOrdered` assertion) for
  `validateScheduled`; `route` calls `desugarMultiWriters` directly (landed deviation, §4 T6).
- The algebra comes from the destination: slice 1 admits `agg = .sum` (real or predicate) only.
- B3: a supplied input naming a defined tensor (private `T#k` and scan scratch included) is an
  error in both backends (`EvalError.inputIsDefined`, `InputBindingError.inputIsDefined`).
- Out-of-range writes are NOT in this slice (S3).

**User constraints.**
- **f32 is the DEFAULT dtype.** A plain/undeclared tensor is f32. The reference evaluator is f64-only,
  so evaluator fixtures use `TLProgram.explicitF64`. Every checked-plan fixture exists in an f64
  version AND an f32 version (declared `tensor f32` and undeclared); structural fixtures are
  dtype-neutral unless noted per task.
- **Models.** Sonnet 5.5 high for implementers and per-task reviewers. Opus 5.5 high only for deep
  reasoning: **T6 (route + Agreement statement) implementer and its review, and both final
  whole-branch reviews.** Clean tasks get a mid-tier (Sonnet) per-task review.

## 1. Execution protocol

**Brief preamble (copy verbatim into EVERY brief):**

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command, no pipelines into git.
> Use absolute paths and `/usr/bin/git -C <worktree>`. Build only with
> `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`; never run `lake` from
> the worktree root. Use the Read tool for file windows and `rg -n` for search. Stage files by
> explicit path; never commit `.claude/settings.json`. Stay within the stated turn and context
> budget and say so in the report if you breach it.

Plus per brief: "Budget: <= ~60 turns, context peak <= ~250k; run builds that may exceed 2 minutes
with `run_in_background` and wait for the notification; window-read (40-60 lines around each symbol),
do not whole-file-read any file over ~20k characters; do NOT run the full `Tests` target."

**Per-task loop** (the same for T1-T7; the patch is the compiled prototype text, so the implementer
does not rewrite it):
1. `/usr/bin/git -C <wt> apply --check --exclude=papers/semantics/additive_collection_slice1_artifacts/p1_findings.md <patch>`
   (the exclude is needed only for `p2a_patches/0001`, which also edits an artifact file that is
   already in its final form on this branch; it is harmless for the others).
2. Same command without `--check`. If it does not apply cleanly, STOP and report (a base mismatch;
   do not hand-merge).
3. Build the task's targets (below) with `lake-build.sh`; run in the background when a task touches
   `Exec/Uid.lean` or `Eval/Plan/Prepared.lean` (see the rebuild column of the risk table).
4. Read the patch's production hunks and the task's fixtures (windows) and tick the task's checklist.
5. Stage the files the patch touched by explicit path (`git -C <wt> apply --stat` lists them), commit
   with the task's message, ending with
   `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`.
6. Report: commit hash, targets built, turn/context usage. Write the ledger line before the next dispatch.

**Controller steps per task (not the implementer):** run
`bash <wt>/leanncd/scripts/mutation-manifest.sh --task <Tn> <wt>/leanncd <wt>/papers/additive_collection_slice1_mutations_post.json`
and read the table; a mutation that does not fail with its `expect` strings is a finding, never a pass.

**Reviews.** Per task: one mid-tier review of the task's commit diff plus the case x class table below
(reviewer appends findings to `papers/semantics/additive_collection_slice1_review_<Tn>.md` as it goes;
windows of 40-60 lines). ONE final whole-branch review with TWO lenses, both Opus:
(a) soundness/semantics against spec §19.2 and decision note §C (collector = single-statement
collection summed; nonlinearity per writer; readiness; hiding completeness; B3 parity);
(b) regression / "wrongly rejects valid programs", including the f32 path (default-f32 undeclared
multi-writer programs, predicate sets, single-writer identity, scans).
One fix dispatch per finding group, given only the relevant plan section.

**Finish (Rule 13).** Controller runs the full manifest unfiltered (not `--check`) and the full
`lake-build.sh <wt>/leanncd Tests` itself (background; the prototype's full `Tests` took ~25 minutes).
Then `ExitWorktree` keep, `git -C <primary> merge --no-ff worktree-additive-collection-slice1`, confirm
`git diff --stat main worktree-additive-collection-slice1` is empty, remove the worktree, `git branch -d`.
Do NOT push; say that `main` is ahead of `origin/main`.

## 2. Global constraints (exact values)

**Admitted by slice 1.** A name with >= 2 writers, every writer a plain `.assign` with only bare
`.free`/`.freeNorm` slots, the same axis UID at each position as writer 1, `agg = .sum` (real) or
a predicate destination (collector ORs through `Combine.bool`). Each `T#k` keeps its own nonlinearity;
the collector is the identity nonlinearity. Names: `T#k`, `k` 1-based in schedule order.

**Deliberately NOT done (owner):**

| Item | Behaviour in slice 1 | Owner |
|---|---|---|
| scatter / affine-slot multi-writer | rejected `multiWriterScatter T` | S3 |
| `max`/`min` (non-sum) multi-writer | rejected `multiWriterAlgebra T` | S3 |
| plain + scan, or scan + scan, writers of one name | rejected `multiWriterScan T` (note §C.9 said "do nothing"; see §9) | parked (scan collection) |
| oracle for affine write slots, tropical carriers | not touched | S2 |
| out-of-range write errors, `CollisionReduce`/fill deletion, max-plus tensor product | not touched | S3 |
| explicit roles / declared shapes beyond the UID agreement check, `multiWriterNeedsDeclaredShape` | not built | S3 / unscheduled |
| prepare-time B3 refusal of an `InputSignature` entry naming a defined tensor | NOT done: B3 is run-time only on the checked side | PARKED: one small Direct-path dispatch (new `InputSignatureError` arm + f64/f32 fixtures), ~1 dispatch |
| `buildNameToStep` last-wins for a direct `routeCore` caller with a multi-writer schedule | unchanged (unreachable from `route`/`compile`) | PARKED: one guard + fixture, ~1 dispatch |
| JAX runtime (`experiments/jax_bridge/evalplan_affine_runtime.py`) on collected plans | UNPROBED (`EvalPlanCodegen` emits public outputs only; builds green) | PARKED: ~1 probe dispatch |
| `.plain (.recurMorphism ..)` writers in a multi-writer set | skipped by the collector (every entry rejects the escape hatch on its own terms); no fixture | PARKED: 1 fixture, Direct path |
| hand-built `.assign` with an affine slot inside a multi-writer set (`slotsBecomeScatter` arm of `checkWriterGroup`) | rejected `multiWriterScatter`; surface programs reach the `.scatter` arm only; NO fixture | PARKED: 1 hand-built fixture (donor: C8's `copyStmt`) |
| reference-evaluator f32 fixture for a multi-writer program | observed in a probe only (`unsupportedDtype` naming the external `A`, never `T#k`); not shipped | PARKED: 1 fixture |

## 3. Risk table (counts, not line counts)

| Task | Patch | Prod lines | Fixtures new / migrated | Mutation cycles | Rebuild trigger | Model | Turn risk |
|---|---|---|---|---|---|---|---|
| T1 collector module | `p1/0001` | ~150 (+12 Uid) | 11 ids (16 guards) / 0 | 7 | **`Exec/Uid.lean` (whole library)** | Sonnet | low |
| T2 all-writers readiness | `p1/0002` | ~20 | 6 (6 guards) / 1 (G21, 8 cases) | 2 | `ScheduledValidation.lean` (Pipeline + Eval chain) | Sonnet | low |
| T3 evaluator, B3, shape | `p1/0003` | ~55 | 17 ids (19 guards) / 3 | 6 | `ScheduledValidation.lean`, `Eval/Error.lean` | Sonnet | low |
| T4 `multiWriterScan` | `p2a/0001` | ~25 (+3 Uid) | 3 ids (4 guards) / 0 | 3 | **`Exec/Uid.lean` again** | Sonnet | low |
| T5 checked plan hiding + B3 | `p2a/0002` | ~60 | ~20 ids, 73 guards/examples / ~9 | 8 | **`Eval/Plan/Prepared.lean`, `Error.lean`** (all `Eval.Plan.*`) | Sonnet | **>60-turn risk: split** |
| T6 route + Agreement | `p2b/0001` | ~65 (proof 43) | 7 ids (8 guards) / 0 | 2 | `Lowering.lean`, `Bridge/Agreement.lean` | **Opus** | medium |
| T7 oracle profile lift | `p2b/0002` | ~10 | 1 new + 3 flipped / 0 | 2 | `Semantics/Source/NumericalProfile.lean` (Semantics only) | Sonnet | low |
| T8 documentation | none (edits) | 0 | 0 / 0 | 0 | none | Sonnet | low |

Rebuild count: **2 whole-library rebuilds (T1, T4: `Exec/Uid.lean`), 1 large (T5: `Prepared.lean` /
`Error.lean`)**, 3 medium. The prototype dispatches breached their turn caps (harness counts P1 110, P2a
128, P2b 87 against 60) mostly on rebuild chains, 25-minute full `Tests` runs and harness refusals;
this plan avoids that by shipping patches (no rewriting), forbidding the full `Tests` target in
implementer briefs, and putting mutation cycles and `Tests` on the controller. Expected
implementer turns per task: 15-30.

Totals: 68 new/flipped fixtures, ~12 migrated, 30 mutation cycles (24 observed in the prototype, 6 added
by the plan author for fixtures the prototype left unkilled). At authoring 18 of the 30 were run and passed; the
other 12 (A3-M1..M5, A4-M2/M3, A5-M2/M4/M5/M7/M8) are `--check`-validated only (record §2).

## 4. Tasks

For every task: the patch is in `papers/semantics/additive_collection_slice1_artifacts/<dir>/`.
Locate symbols with `rg -n '<identifier>' <file>` and read 40-60-line windows; never whole-file-read
`Compile.lean`, `Lowering.lean`, `Structural.lean`, `Agreement.lean`, `tensor_logic_semantics.md`.
Prototype commit messages are NOT reused (they name "proto"); use the messages below.

### T1. Collector module (patch `p1_patches/0001-proto-P1-T1-collectDefinitions-desugar-module-Collec.patch`)

Commit: `feat(dsl): additive collection desugar (desugarMultiWriters) with structural tests`

Files (all `ls`-verified): `leanncd/LeanNCD/DSL/Pipeline/Collect.lean` (NEW, imports `RouteFragments`
only), `leanncd/LeanNCD/Exec/Uid.lean` (4 `CompileError` constructors), `leanncd/LeanNCD.lean`
(+ `import LeanNCD.DSL.Pipeline.Collect`), `leanncd/lakefile.toml` (+ `DSL.Pipeline.CollectTest` glob),
`leanncd/test/DSL/Pipeline/CollectTest.lean` (NEW), `leanncd/LeanNCD/DSL/AGENTS.md` (1 Code Map row).

Symbols (`identifier @ file`):
`collectorName`, `Decl.cloneAs`, `WriterGroup`, `writerGroups`, `checkWriterGroup`, `collectorStmt`,
`desugarMultiWriters` @ `LeanNCD/DSL/Pipeline/Collect.lean`;
`CompileError.multiWriterScatter | multiWriterAlgebra | writerShapeMismatch | reservedNameCollision`
@ `LeanNCD/Exec/Uid.lean`; reused: `routeWrites`, `routeNameInventory` @ `DSL/Pipeline/RouteFragments.lean`,
`producerSlots`, `slotsBecomeScatter`, `LHSSlot.toReadIdx` @ `DSL/Ast.lean`.

Fixtures (donors; observed values in `p1_observed.md`): C1 (donor F14 `multiDefinition`; dests
`[Y#1,Y#2,Y]`), C2 (clone C1 + third writer + reader), C3 (identity, accept-neighbour of C1), C4
(clone C1, `predicate Y`: three `.predicate` decls), C4b (clone C4, `tensor f64 Y`: element types
`[f64,f64,f64]`), C5 (scatter `S[2*i]`/`S[2*i+1]` -> `multiWriterScatter "S"`), C6 (clone C1,
`maxreduce` -> `multiWriterAlgebra "Y"`), C7 (clone C1, writer 2 on axis `j` ->
`writerShapeMismatch "Y" 2 0`), C7b (accept-neighbour: both on `i`), C8 (hand-built
`[Y#1:=A, Y:=B, Y:=C]` -> `reservedNameCollision "Y#1"`), C8b (accept-neighbour: rename to `Q`).
f64/f32: C4/C4b cover predicate and f64-declared clones; the declared-f32 clone is pinned in T5.

**Sibling audit (§2) — "writers of a name" / "what a statement writes".** Deliverable: this table
reproduced in the review file with a verdict per cell. Classes: R required-to-change, F forbidden,
S silently-ignored-today.

| Function @ file | Single | Multi plain | Multi incl. scatter | Plain + scan | Post-slice state |
|---|---|---|---|---|---|
| `ScanStmt.writes/outputs/reads` @ ScheduledValidation | F | F | F | F | unchanged; `publications` added beside (T2) |
| `routeWrites/Outputs/Reads` @ RouteFragments | F | F | F | F | reused by the collector |
| `eligible`/`topoSortFuel`/`isTopoOrdered` | F | **R** (was any-writer: S) | R | R | T2 |
| `orderedExternalNames`, `externalReadNames` | F | F (`T#k` are written) | F | F | none |
| `scheduleStorage*`, `scheduleFloat32Name?` | F | F (clones carry storage) | F | F | none |
| `checkReadRanksIn` `producedRank` @ Structural | F | **S** (last writer's rank; runs on the ORIGINAL program, a reader can report `rankMismatch` before `writerShapeMismatch`) | S | S | accepted, documented |
| `checkPredicateOutput`, `stmtLhsRank`, `finalizeScans` | F | F | F | F (`duplicateScratchProducer`) | none |
| `buildNameToStep`, `routableInOrder` @ Lowering | F | **S** until `route` collects (T6) | S | S | T6; still S for direct `routeCore` callers (parked) |
| `scatterOutputShapes` @ Eval/SizeInfer | F | F | **S** (last scatter's extent) | F | rejected before it runs |
| `evalScheduled` env fold | F | **R** (T3) | R (rejected) | S -> R (`multiWriterScan`, T4) | T3/T4 |
| `slotOf`, `materializedNames` push sites, `unpack` fold @ Eval/Plan | F | S/R (T5) | — | — | T5 |
| `checkStructure` @ Semantics/Source/NumericalProfile | F | **R** (T7) | F | — | T7 |

Cycles (7, `--task T1`, all in `Collect.lean`, target `DSL.Pipeline.CollectTest`): A1-M1 numbering,
A1-M2 no clones, A1-M3 scatter admitted, A1-M4 algebra admitted, A1-M5 UID mismatch admitted, A1-M6
inventory freshness dropped, A1-M7 single-writer collected (identity). A1-M1/M2 observed in the prototype;
A1-M3..M7 were added for fixtures C5-C8/C3 that had no individual kill.
Targets to build: `LeanNCD DSL.Pipeline.CollectTest`. Review: mid-tier.

### T2. All-writers readiness (patch `p1_patches/0002-proto-P1-T2-all-writers-readiness-in-eligible-topoSo.patch`)

Commit: `feat(dsl): all-writers readiness in eligible/topoSortFuel/isTopoOrdered`

Files: `leanncd/LeanNCD/DSL/Pipeline/ScheduledValidation.lean`, `leanncd/test/DSL/Pipeline/CollectTest.lean`
(readiness section), `leanncd/test/DSL/Pipeline/RouteFragmentCorpusTest.lean` (G21 migration),
`leanncd/LeanNCD/DSL/AGENTS.md` (one paragraph).
Symbols: `ScanStmt.publications`, `eligible`, `topoSortFuel`, `isTopoOrdered` @
`LeanNCD/DSL/Pipeline/ScheduledValidation.lean`; `schedule` @ `DSL/Pipeline/Lowering.lean` (changes only
through `topoSort`). Rule: a read is ready when `emitted.count r` equals the number of NODES writing `r`;
`publications = outputs.eraseDups` because a 2-D scan lists its state twice (`[G, G]`) yet is one writer.
Fixtures (observed `p1_observed.md`): R1 (`T:=A; U:=T; T:=B` schedules to `[T,T,U]`), R2 (hand-built
reader-between order is not topo-ordered) with accept-neighbour R2b, R3 (self-read of a multi-writer
name: `cyclicDataflow "schedule: cyclic dataflow"`) with accept-neighbour R3b, R4 (two-face scan,
`outputs = [G,G]`, plain reader ready; donor RC10 in `test/Eval/Portfolio/RecurrenceTest.lean` plus a
column face). Migration: `RouteFragmentCorpusTest` G21 (8 `%nl0` collision cases) now fails earlier at
`schedule` with `cyclicDataflow "schedule: cyclic dataflow"` instead of `routeCore: cyclic dataflow
(topoSort fallback)`. The patch edits the expected OLD-leg payload in `collisionTransition`; the NEW leg must
still accept and route all 8 (G21 asserts rejection-to-acceptance, `wellFormedDom` and an acset round trip), so
the review checks that the new leg did not start rejecting.
Cycles (2): A2-M1 any-writer readiness restored; A2-M2 `publications` without `eraseDups` (R4).
Targets: `LeanNCD DSL.Pipeline.CollectTest DSL.Pipeline.RouteFragmentCorpusTest`. f64/f32: dtype-neutral.
**Audit rule for the reviewer:** R2 must be checked in both directions (R2 false, R2b true); a fixture
where both readiness rules coincide pins nothing.

### T3. Evaluator integration, B3, shape check (patch `p1_patches/0003-proto-P1-T3-collectDefinitions-in-validateScheduled-.patch`)

Commit: `feat(eval): collect multi-writer tensors in validateScheduled/evalScheduled; hide private names; reject supplied defined inputs (B3)`

Files: `leanncd/LeanNCD/DSL/Pipeline/ScheduledValidation.lean`, `leanncd/LeanNCD/Eval/Error.lean`,
`leanncd/LeanNCD/Eval/Eval.lean`, `leanncd/lakefile.toml` (+ `Eval.CollectEvalTest`),
`leanncd/test/Eval/CollectEvalTest.lean` (NEW), `leanncd/test/Eval/Plan/ContractTest.lean`,
`leanncd/test/Eval/Plan/CompileTest.lean` (ordered twin), `leanncd/LeanNCD/DSL/AGENTS.md`.
Symbols: `collectDefinitions`, `CheckedScheduledProgram` (field `privateNames`), `validateScheduled` @
`ScheduledValidation.lean`; `EvalError.inputIsDefined` @ `Eval/Error.lean`; `evalScheduled` @ `Eval/Eval.lean`
(B3 check after the f32 refusal and before size inference; erasure of `privateNames` in the result env).
`validateScheduled` runs the source checks on the ORIGINAL program and rebuilds `declEnv`/`explicitSizes`/
`extNames` from the COLLECTED one; `program` is the collected schedule (so `prepareEvalPlan` compiles it).
Fixtures (all `explicitF64`, bit-exact; `p1_observed.md`): V1 `Y:=A;Y:=B` = [7,13] (donor F14), V2 =
[12,22] (donor F15), V3 `Y:=X;Y:=X` = 2X, V4/V4' predicate OR (`[1,1]`, count would be `[2,1]`), V5/V5r
non-integral source-order fold (bits 4603579539098121012 vs ...011), V6 reader between writers sees both,
V7 `relu(A)+relu(B)` (not `relu(A+B)`), V8 single-writer accept-neighbour (keys `[A,B,Y]`), J1 cyclic
self-read, J2 shape mismatch (old: silent truncation), J3 scatter (old `[0,10,0,20]`), J4 max, J5 supplied
`Y` rejected with accept-neighbour J5b (unrelated `Unused` passes through). Migrated: `ContractTest`
`repeatAssignProg` (Y=Z=[101,202]; the "true overwrite" mutation inverts), `CompileTest` ordered twin
(`topologyInputs.erase "Z"` for the direct reference run).
Sibling audit: the T1 table rows `evalScheduled`, `scatterOutputShapes`, `checkReadRanksIn` apply; in
addition the **B3 case x class table**: supplied name in {external input, defined plain output, private
`T#k`, collector output, scan scratch} x entry {`evalScheduled`}: required reject for the last four,
forbidden to reject the first (J5b); scan scratch is covered in T5 (the checked side mirrors it).
Cycles (6): A3-M1 reversed numbering (V5/V5r), A3-M2 no clones, A3-M3 collector `max`, A3-M4 last-wins
regression (also kills J2-J4), A3-M5 hiding removed, A3-M6 B3 removed (added by the plan author).
Targets: `LeanNCD Eval.CollectEvalTest Eval.Plan.ContractTest Eval.Plan.CompileTest`. f64/f32: the
reference is f64-only; f32 behaviour is T5's.

### T4. `multiWriterScan` (patch `p2a_patches/0001-proto-P2a-T0-multiWriterScan-rejection-in-desugarMul.patch`)

Commit: `feat(dsl): reject multi-writer names that include a scan node (multiWriterScan)`

Files: `Collect.lean`, `Exec/Uid.lean` (+1 constructor), `test/DSL/Pipeline/CollectTest.lean`,
`DSL/AGENTS.md` (one row sentence). The patch also edits `p1_findings.md` (artifact): apply with the
`--exclude` flag from §1.
Symbols: `scanWriterConflict?`, `desugarMultiWriters` (first statement), `writerGroups` @ `Collect.lean`;
`CompileError.multiWriterScan` @ `Exec/Uid.lean`.
Fixtures (hand-built from R4's scan; the surface cannot reach them): C9 plain `G` + scan, C9b scan +
scan, accept-neighbour C9c (one scan writer of `G` plus an unrelated plain `T`: accepted, generated `[]`).
Reachability: `routeWrites` dedups, so one scan writing `G` in both halves is ONE writer.
Sibling note: `Uid.lean` is touched a second time here (full-library rebuild); do not fold it into T1 (the
patch order is fixed).
Cycles (3): A4-M1 check never fires; A4-M2 scan-vs-scan dropped; A4-M3 `length >= 1` (false rejection of C9c).
Targets: `LeanNCD DSL.Pipeline.CollectTest DSL.Pipeline.RouteFragmentCorpusTest DSL.Pipeline.RouteWeaveTest
DSL.Pipeline.ScanAffineTest Eval.ScanTest Eval.CollectEvalTest Eval.Portfolio.RecurrenceTest` (all but the
first guard that scan programs are not falsely rejected; this is the target list the prototype ran green).

### T5. Checked plan hides private names + B3 (patch `p2a_patches/0002-proto-P2a-T1-T2-checked-plan-hides-private-names-B3-.patch`)

Commit: `feat(eval-plan): checked plan hides collector private names and rejects supplied defined inputs`

**>60-turn risk** (the prototype's P2a dispatch ran 128 turns; the patch is 56K with 364 new fixture
lines). Run as TWO dispatches using `.claude/skills/slice-plan/split-handoff-template.md`:
- **Phase 1 (production commit).** Apply only the production hunks:
  `git apply --include=leanncd/LeanNCD/Eval/Plan/Adapter.lean --include=leanncd/LeanNCD/Eval/Plan/Compile.lean --include=leanncd/LeanNCD/Eval/Plan/Error.lean --include=leanncd/LeanNCD/Eval/Plan/Prepared.lean --include=leanncd/LeanNCD/Eval/Plan/AGENTS.md --include=leanncd/LeanNCD/DSL/AGENTS.md <patch>`;
  build `LeanNCD` (background). Commit `feat(eval-plan): hide collector private names from PlanBindings; B3 in pack/unpack`
  (only `LeanNCD` is green at this commit; the migrated tests are not yet in).
- **Phase 2 (fixtures + cycles handoff).** Apply the remainder (`git apply <patch>` fails on the
  already-applied hunks, so use `--exclude` for the six phase-1 paths), build the test targets, commit
  `test(eval-plan): additive-collection fixtures (f64+f32) and migrated repeat-assignment cases`.
  Phase-2 `identifier @ file` list: `h1`/`h2`/`h3`/`h4`, `verdict64`, `verdict32`, `plan64`, `plan32`,
  `prepared64`, `prepared32`, `unpack32Keys` @ `test/Eval/Plan/CollectPlanTest.lean` (NEW);
  `repeatPrepared`, `repeatPredPrepared`, `repeatPredBadSlot`, `repeatPredTrailingBadSlot`,
  `repeatPredMissingPublication`, `singleWriterPrepared`, the ordered twin @ `test/Eval/Plan/CompileTest.lean`;
  the repeated-assignment case @ `test/Eval/Plan/DifferentialTest.lean`; fixture 4 @
  `test/Eval/Plan/Adapter32Test.lean`; glob @ `lakefile.toml`. The phase-2 dispatch reads only these.

Files (verified): `Eval/Plan/Adapter.lean`, `Compile.lean`, `Error.lean`, `Prepared.lean`,
`Eval/Plan/AGENTS.md`, `DSL/AGENTS.md`, `lakefile.toml`, `test/Eval/Plan/{CollectPlanTest (NEW),CompileTest,DifferentialTest,Adapter32Test}.lean`.
Symbols: `PlanBindings` (fields `privateSlots`, `definedNames`), `checkPreparedBindings`,
`rawPublicationSlots` @ `Eval/Plan/Prepared.lean`; `prepareEvalPlan` Step F (`isPrivate` partition) @
`Eval/Plan/Compile.lean`; `PreparedBindingsError.privateSlotUnpublished`,
`InputBindingError.inputIsDefined` @ `Eval/Plan/Error.lean`; `firstDefinedInput?`, `packBodyOf`,
`unpackBodyOf` @ `Eval/Plan/Adapter.lean`. Hiding is ONE partition at Step F (not at each push site):
a new publication site must push into `materializedAcc` unconditionally.
Fixtures (donors; `p2a_observed.md`): **f64 and f32 pairs** H1 (`Y:=A;Y:=B`: f64 `explicitF64`, f32
declared `tensor f32`, f32 undeclared; keys `[A,B,Y]`, `materializedNames == #["Y"]`, `privateSlots.size == 2`,
signatures `#[("Y",f64|f32)]`; accept-neighbour H1s single writer: `privateSlots == #[]`), H2 (order:
inputs 0.1/0.3/0.4 chosen because the two fold orders differ in BOTH precisions: f64 bits
4605380978949069210 vs reversed ...209; f32 1061997773 vs ...774; `0.1,0.2,0.3` folds equal in f32 and is NOT
used), H3 (predicate OR f64 and f32), H4 (no `mixedStorageKinds`-style conflict from `T#k`: f64 and f32
declared both prepare), B3.1/B3.2/B3.3 (supplied `Y`, `Y#1`, both, scan scratch `T`; observers ref, run,
unpack, pack for f64 and run, unpack32, pack32 for f32; first defined name in write order; accept-neighbours
without the name and with `Unused`). Migrated: the `CompileTest` repeat block (`["Y","Z"]`, `tensorSigs.size
== 6`, `slotOutOfRange 99 6`/`7 6`, new hidden-slot checks), `DifferentialTest` repeated assignment (plan
Y=Z=[101,202] equals `evalScheduled`, env size 4), `Adapter32Test` fixture 4 (`["Y","Z"]`, bits of 101/202).
Note: `mixedStorageKinds` is not an identifier; the observed form is `CapabilityError.unsupportedDtype
"<name>: mixed f32/f64 storage in one schedule"`.
**Sibling audit (checked side).** Reproduce `p2a_findings.md` (a) in the review file; required deliverable
cells: `materializedAcc` push sites R (via Step F), `checkPreparedBindings` R, `unpack/unpack32/unpackBodyOf`
R (B3), `pack/pack32/packBodyOf` R (B3), `InputSignature.ofDenseInputs*`/Step B **S: a signature entry naming a
defined tensor is silently ignored at prepare (PARKED, §2)**, hand-built `PlanBindings` literals in
`experiments/jax_bridge/EvalPlanCodegen.lean` F (new fields default to `#[]`).
Cycles (8): A5-M1 no partition; A5-M2 `privateSlots` ignored; A5-M3 `privateSlotUnpublished` dropped; A5-M4
no clones (f64-declared fixtures); A5-M5 clone of a typed tensor always f64 (f32-declared storage conflict:
the only kill of the declared-f32 clone path); A5-M6 `packBodyOf` B3 removed (direct pack observers only);
A5-M7 `unpackBodyOf` B3 removed; A5-M8 `definedNames` public-only. The pack door is invisible through the
composite `runPreparedDense`, so direct `pack`/`pack32` observers carry it.
Targets: `LeanNCD Eval.Plan.CollectPlanTest Eval.Plan.CompileTest Eval.Plan.Adapter32Test
Eval.Plan.DifferentialTest` (background; includes the 3,832-case differential sweep) and `JaxExperiment`
(`EvalPlanCodegen` builds `PlanBindings` literals).
Review: mid-tier; checklist item: no `File.lean:NNN` was added to AGENTS.md (identifiers only).

### T6. `route` collects before physicalization; Agreement statement change (patch `p2b_patches/0001-proto-P2b-T3-route-collects-multi-writer-tensors-bef.patch`) — **Opus**

Commit: `feat(dsl): route collects multi-writer tensors before physicalization; extend compile_eq_physical_route`

Files: `DSL/Pipeline/Lowering.lean` (`route`), `Bridge/Agreement.lean`, `DSL/Pipeline/ScheduledValidation.lean`
(a docstring), `test/DSL/Pipeline/CollectTest.lean` (route section), `test/Bridge/AcsetCodecTest.lean` (fixture 10).
Symbols: `route`, `routeCore`, `buildNameToStep`, `routableInOrder` @ `Lowering.lean`;
`compile_eq_physical_route`, `compile_wellFormed` @ `Bridge/Agreement.lean` (window-read ~40 lines around
each, plus the module docstring); `physicalizeForRoute`, `routeNameInventory`, `PhysicalRouteProgram` @
`RouteFragments.lean` (read-only).
Decisions to verify against the patch (Rule 7; each landed deviation is argued in `p2b_findings.md`):
1. **`route` calls `desugarMultiWriters`, not `collectDefinitions`.** The wrapper's `isTopoOrdered` assertion
   moved the payload of three `RouteFragmentDiagnosticTest` pins (cyclic hand-built schedule must report
   `routeCore`'s `cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)"`). `routeCore`'s
   `routableInOrder` stays the single topology gate; on collected schedules it and `isTopoOrdered` agree.
2. **Route does NOT hide `T#k`**: `ThreadedComposed` carries no tensor names; the private steps are anonymous
   internal steps like the nonlinear producer/consumer split; hiding would delete steps and change the morphism.
3. **Agreement statements:** `compile_eq_physical_route` CHANGED (existential gains `collected` and
   `privateNames`, conjunct `desugarMultiWriters logical = .ok (collected, privateNames)`, physicalization
   conjunct over `collected`); `compile_wellFormed` statement UNCHANGED (only its `obtain` pattern grew two
   binders); `test/Bridge/AgreementTest.lean` (pins its exact type) must stay green; no other lemma mentions
   `physicalizeForRoute` over the logical schedule (verify with `rg -n 'physicalizeForRoute' LeanNCD`).
4. The collector is an `.assign` with `agg := .sum` and identity nonlinearity, so `toBrBaseP` labels it
   `.contract`; a private nonlinear writer keeps its split (RT5).
Fixtures (`p2b_observed.md`; programs over `axis i : ℕ = 2`, undeclared = default f32 except RT3 which
declares `tensor f64 Y(i)`, so the f32/f64 pair is RT1/RT3): RT1 `Y:=A; U:=Y; Y:=B` and RT2 (clone RT1,
reader after both) both route to `collectedRoute` = 4 x `contract`, routing `[[e0],[e1],[i0 0,i1 0],[i2 0]]`
(before the change: 3 steps, reader wired to the LAST writer only, step 0 dead), RT3 (clone RT1 + decl),
RT4 accept-neighbour `Y:=A; U:=Y; S:=B` (3 steps, unchanged), RT5 `Y:=relu(A); Y:=B; U:=Y` (5 steps incl. the
relu split), RT6 three writers + relu reader (6 steps). Acset fixture 10 (clone fixture 8: round trip of
RT5's program, plus the `steps.length = 5` guard; the round-trip guard is a codec witness, the length guard is
the pin). Side finding: a `tensor f64 T(i)` declaration does not parse inside `tlprog!`; fixtures use `Y`.
**Sibling audit (route/oracle side).** Reproduce `p2b_findings.md` (a): `route` R, `buildNameToStep` F
after `route` (still S for direct `routeCore` callers: PARKED), `routableInOrder` F, `toBrBaseP` F (observed),
`routeNameInventory`/`routeNamesFresh` F (inventory from the collected program), `physicalizeForRoute` R
(caller change only), `PhysicalRouteProgram.logical` now holds the COLLECTED schedule (field name unchanged;
`fragmentCount` counts collected statements; documented in T8), `AcsetCodec` F.
Cycles (2): A6-M1 route skips collection (RT1/2/3/5/6 and the acset length guard fail, RT4 passes);
A6-M2 route calls `collectDefinitions` (the three `RouteFragmentDiagnosticTest` pins fail).
Targets: `LeanNCD LeanNCD.Bridge.Agreement Bridge.AgreementTest Bridge.AcsetCodecTest DSL.Pipeline.CollectTest
DSL.Pipeline.RouteFragmentDiagnosticTest DSL.Pipeline.RouteFragmentCorpusTest DSL.Pipeline.RouteWeaveTest
DSL.Pipeline.LoweringTest DSL.Pipeline.StructuralTest DSL.Pipeline.RecurMorphismTest
DSL.Pipeline.ScanAffineTest`.
Review: Opus (statement change of a theorem the bridge depends on; confirm the proof is the added `rcases`
only and that `compile_wellFormed` still states the same type).

### T7. Oracle profile lift and F14/F15/D10 flip (patch `p2b_patches/0002-proto-P2b-T4-lift-the-oracle-multi-definition-refusa.patch`)

Commit: `feat(semantics): lift the oracle multi-definition refusal; value-compare F14/F15/D10`

Files: `leanncd/LeanNCD/Semantics/Source/NumericalProfile.lean`,
`leanncd/test/Semantics/SourceDifferentialPolicyTest.lean`,
`leanncd/test/Semantics/SourceDiagnosticAdmissionTest.lean`.
Symbols: `checkStructure`, `StructuralCondition` (now `usedDType` only; `crossStatementOverwrite` deleted),
`SharedFragment.definitions` (lists every (declaration, origin) pair; may repeat a declaration) @
`NumericalProfile.lean`; `valueCompared` (replaces `overwriteRefusal`, whose only users were F14/F15),
`F13`, `F14`, `F14f32`, `F15` @ `SourceDifferentialPolicyTest.lean`; `D10`, `D12` @
`SourceDiagnosticAdmissionTest.lean`.
Fixtures (`p2b_observed.md`): F14 now `fourLegParity`, definitions `[(3,out 0),(3,out 1)]`, legacy and
checked bits [7,13]; F15 three origins, reversed permutation `.ok`, bits [12,22]; D10 `acceptedNonshared`
scalar `Y:=A; Y:=A`, A=3 -> 6 on all legs; **F14f32 NEW (f32 neighbour of F14)**: classification UNCHANGED
by the lift (`knownContractDifference (usedDType (output, decl 3, statement 0) "Y" .f32)`, because the
output dtype check fires on statement 0 before a second definition is seen). Accept-neighbours already
present: F13 `f64Neighbor`, D12 `explicitF64Neighbor` (single definition; expected bits stay 3, NOT 6; a
global replace of D10's value breaks D12 — edit D10 only).
Cycles (2): A7-M1 refusal re-added through `usedDType` (F14, F15, D10 fail; F13/F14f32/D11/D12 pass);
A7-M2 output dtype check removed (F13 and F14f32 fail; F14/F15 pass).
Targets: `LeanNCD Semantics.SourceDifferentialPolicyTest Semantics.SourceDiagnosticAdmissionTest
Semantics.SourceDifferentialGeometryTest`.

### T8. Documentation (edits as commands; no heavyweight dispatch; no fixtures, no cycles)

Commit: `docs: record additive collection slice 1 as landed (path doc, gap audit, spec remarks, AGENTS)`

Inputs: `p2b_docsweep.md` (FALSE rows, ADDITIONS, STILL TRUE, HISTORICAL). Edit by heading/identifier,
never by line number. One Sonnet dispatch, ~30 turns, windows only.

**(a) Edit list (FALSE rows in `p2b_docsweep.md`, proposed text there):**
`papers/semantics/lean_executable_semantics_path.md` (6 rows: Numerical profile bullet, Known contract
differences bullet and its "Planned alignment" paragraph, §5.1 "Beyond the bounded source fragment", the
§5.1 decision-note paragraph, the §5.1 gap-audit paragraph); `papers/semantics/tensor_logic_semantics.md`
(2 remarks, below); `papers/semantics/tensor_logic_semantic_gap_audit.md` (status update);
`leanncd/LeanNCD/Semantics/AGENTS.md` (source differential paragraph + the ADDITION: `StructuralCondition`
has only `usedDType`); `leanncd/LeanNCD/Semantics/Source/NativeLegs.lean` (`runNative` doc);
`leanncd/LeanNCD/Eval/Plan/Prepared.lean` (`PlanBindings` first paragraph and `materializedWith` doc);
`leanncd/LeanNCD/Eval/Plan/Adapter.lean` (`unpack` doc); `leanncd/test/Eval/Plan/ExecutableTest.lean`
and `leanncd/test/Eval/Plan/CompileTest.lean` (two comments); `papers/jax_evalplan_architecture.md`
(§2.1 and Appendix A); `papers/f32_evalplan.md` (Task 4 fixture item 4). ADDITIONS: `leanncd/LeanNCD/DSL/AGENTS.md`
(route runs `desugarMultiWriters`, not `collectDefinitions`; private `T#k` steps stay in the routed diagram);
`leanncd/LeanNCD/DSL/Pipeline/RouteFragments.lean` ("The checked package (§2.2)" note: schedule is collected
first; `PhysicalRouteProgram.logical` holds the COLLECTED schedule).
Found by the plan author (not in the sweep): `leanncd/LeanNCD/Eval/AGENTS.md` row `evalScheduled`
(`Eval.lean`) lists the check order and omits collection, B3 and erasure -> add "collection
(`collectDefinitions`) inside `validateScheduled`; after the f32 refusal, B3 (`EvalError.inputIsDefined`);
the reported env omits `privateNames`"; `leanncd/test/DSL/Pipeline/CollectTest.lean` header comment says
values are checked in `test/Eval/EntryTest.lean`: the file is `test/Eval/CollectEvalTest.lean`.

**(b) Decision-note §D `[~]` items (from the note's checklist):**
- `lean_executable_semantics_path.md` L959-975 / L1304-1312 -> mark `[x]`, covered by (a).
- Gap audit: full rewrite now that production is additive: in `tensor_logic_semantic_gap_audit.md` change
  the "Established baseline: multiple LHS definitions are not additive" status update to "closed for the
  plain bare-slot sum fragment by slice 1 (`collectDefinitions`); scatter, max/min, scan and tropical closure
  at S3; F03 and W07 stay open"; mark the G04 rows (the checklist table row and the disposition-table row)
  and F01 "closed for the slice-1 fragment" with a pointer to the landed identifiers (`desugarMultiWriters`,
  `collectDefinitions`, `ScanStmt.publications`, `PlanBindings.privateSlots`). Keep the audited-code findings
  as historical text, prefixed "as audited before slice 1".
- **Spec remarks** in `tensor_logic_semantics.md` (headings "Remark (current production pipeline)" and
  "Remark (production readiness)"; values from `p2b_docsweep.md`): replace "the pipeline currently replaces
  the supplied value silently, and enforcing the rejection is part of the planned alignment" with "both
  backends reject such an input (`EvalError.inputIsDefined` / `InputBindingError.inputIsDefined`)"; replace
  "The scheduler currently releases a reader after the first of several writers; correcting this is part of
  the planned alignment recorded in the decision note" with "A reader of a tensor with several writers waits
  for every writer (all-writers readiness)". Update the note's own status paragraph after the `[~]` items
  (the "carry only a planned, not landed pointer" sentence).
- Decision note §C: append a "Landed as" paragraph listing the deviations: `collectDefinitions` is the
  wrapper in `ScheduledValidation.lean` and `route` calls `desugarMultiWriters`; readiness counts nodes via
  `ScanStmt.publications`; plain + scan and scan + scan are rejected `multiWriterScan` (not "do nothing");
  `PlanBindings.privateSlots`/`definedNames` and `PreparedBindingsError.privateSlotUnpublished`; B3 is
  `EvalError.inputIsDefined` and `InputBindingError.inputIsDefined`, run-time only on the checked side.

**(c) Value-grep sweep (commands, run from the worktree root; `-U` because the prose is line-wrapped).
"Before" is the count measured on the patched tree at authoring (nonzero, so the grep is not vacuous);
"after" must be 0 unless noted:**
```sh
rg -U -c 'one definition per left-hand side|Planned alignment \(decided|not landed' papers/semantics/lean_executable_semantics_path.md   # before 2
rg -U -c 'The change is planned and not implemented' papers/semantics/tensor_logic_semantic_gap_audit.md   # before 2
rg -U -c 'currently\s+replaces the supplied value|currently releases a\s+reader after the first' papers/semantics/tensor_logic_semantics.md   # before 2
rg -U -c 'Production overwrites when several statements|`\[2,4\]` against' papers/semantics/lean_executable_semantics_path.md   # before 2
rg -U -c 'reassigned twice appears\s+twice|written twice by the\s+schedule appears\s+twice' leanncd/LeanNCD/Eval/Plan/Prepared.lean leanncd/LeanNCD/Eval/Plan/Adapter.lean   # before 2 + 1
rg -n 'crossStatementOverwrite' leanncd papers/semantics/lean_executable_semantics_path.md leanncd/LeanNCD/Semantics/AGENTS.md   # after: only the 2 history comments in test/Semantics/SourceDifferentialPolicyTest.lean
rg -c 'EntryTest' leanncd/test/DSL/Pipeline/CollectTest.lean   # before 1
rg -U -c 'known\s+production\s+contract\s+difference' leanncd/LeanNCD/Semantics/AGENTS.md   # before 1
```
Remaining `crossStatementOverwrite` hits under `papers/semantics/source_correspondence_*` are dated records
(outside the paths above; list them in the commit body). Then the repo-wide stale-value grep (REQUIRED
because a capability boundary moved):
`rg -n -l 'crossStatementOverwrite|last-write-wins|last write wins|last-wins' leanncd papers .claude --glob '!**/.lake/**' --glob '!papers/semantics/additive_collection_slice1_artifacts/**'`
and classify every hit as unrelated (scatter/scan/declaration last-wins, listed in the docsweep "Excluded"
and "STILL TRUE" sections), historical (dated records: add at most a one-line "superseded by additive
collection slice 1" banner), or fixed. Report the table in the commit body.
Review: none beyond the final whole-branch review (docs only).

## 5. Per-task acceptance (every task)

- Patch applied cleanly; `git diff --stat` equals the patch's `--stat`.
- Task targets green; no `sorry`/`admit`/`axiom`/`native_decide` added (`rg -n` over the diff).
- Controller manifest run for the task: every cycle fails with its `expect` strings and is restored
  (sha256 check inside the script) and the restored build passes.
- No `File.lean:NNN` in anything the task ships (`rg -n '\.lean:[0-9]+' <changed .md/.lean files>` = 0; test
  `#guard` positions are never written into docs).
- Ledger line written (commit hash, targets, turns, context).

## 6. Discoverability and AGENTS.md trim (checked at authoring; details in the record)

- New module `LeanNCD/DSL/Pipeline/Collect.lean` is imported by `leanncd/LeanNCD.lean` (patch T1) and by
  `ScheduledValidation.lean`; reachable from a plain `import LeanNCD`. Mentioned in `DSL/AGENTS.md` (Code Map
  row, T1) and `Eval/Plan/AGENTS.md` / `DSL/AGENTS.md` consumer paragraph (T5).
- New test modules `DSL.Pipeline.CollectTest`, `Eval.CollectEvalTest`, `Eval.Plan.CollectPlanTest` are in the
  `lakefile.toml` `Tests` globs (T1/T3/T5), so they run in the default `Tests` target.
- AGENTS.md trim: the edited nodes' injected sections stay under ~3k characters (Pitfalls: DSL ~1.8k,
  Eval/Plan ~1.9k, both unchanged in size by the patches). The edited Contracts/consumer paragraphs are
  larger than that (~7k each) but are not injected sections; T8 adds ~0.4k to `Eval/AGENTS.md`'s table row.
  Flag if the hook is found to inject `Contracts`.

## 7. Budget (CLAUDE.md Rule 6)

- Per dispatch: <= ~60 turns, context peak <= ~250k (briefs say so; breaches reported).
- Slice execution target <= ~175M cumulative input tokens. Estimate (NOT measured): 7 patch tasks ~55M,
  7 per-task reviews ~20M, two Opus final reviews ~20M, T8 ~6M, controller (manifests, two `Tests` builds,
  fixes) ~25M = ~125M. The close-out records the measured total via
  `python3 .claude/skills/slice-plan/token-report.py <session-id>` and explains any overrun.
- Slice authoring target <= ~50M. **Overrun, stated plainly:** measured before this write-up dispatch,
  the three prototype dispatches and the docsweep cost 60.8M (P1 18.7M, P2a 26.4M, P2b 12.8M, docsweep
  2.9M); this write-up dispatch measured 19.8M (95 turns, context peak 300k: it breached the 60-turn and 250k caps,
mostly waiting on mutation-cycle builds it chose to run for validation); total ~80.6M against ~50M. Causes: three prototype
  dispatches each past their turn cap (harness turns 110 / 128 / 87 against a self-reported ~75 / ~140 / ~75;
  context peaks 259k / 312k / 221k), 25-minute full `Tests` runs waited on in 10-minute blocks, and rebuild
  chains after every `Exec/Uid.lean`/`Prepared.lean` edit. The earlier design and decision-note dispatches
  (9.2M + 12.5M) are not counted here.

## 8. Parked and unprobed (restated from §2 with cost lines)

PARKED (each a Direct-path dispatch, ~1 each): prepare-time B3 for `InputSignature` entries; direct-`routeCore`
`buildNameToStep` guard; `.recurMorphism`-writer fixture; hand-built affine-slot `.assign` fixture;
reference-evaluator f32 refusal fixture. UNPROBED: JAX runtime on collected plans. Also noted, not parked:
`producedRank` (`checkReadRanksIn`) is still last-wins, masked by `writerShapeMismatch` except that a reader
may report `rankMismatch` first.

## 9. Decisions needed from the user (only the genuinely open)

1. **Ratify the landed deviations from decision note §C.** (a) `route` calls `desugarMultiWriters`, not
   `collectDefinitions` (kept the more tested single-gate pattern); (b) plain + scan and scan + scan writers
   are rejected `multiWriterScan` where §C.9 said the desugar "does nothing" (this was a controller-level
   answer, not the user's); (c) `PlanBindings` gained `privateSlots` and `definedNames`,
   `PreparedBindingsError` gained `privateSlotUnpublished`. Recommendation: accept all three; T8 records them.
2. **Schedule or leave parked:** the five items in §8. Recommendation: leave parked; schedule the
   prepare-time B3 refusal (the only item where a run-time-only check can disagree with a prepare-time
   expectation) with S2.

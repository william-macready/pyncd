# Additive collection, slice 1: authoring-verification record

Not the live plan (`additive_collection_slice1_plan.md`). Evidence that the plan's patches replay, its
manifest is valid and was run against the patched tree, and its prose claims were diffed or grepped.
Written 2026-10-15 by the write-up dispatch (slice-plan §6, second dispatch). The execution close-out
(measured totals, review outcomes, merge hash) is appended below by the controller.

## 1. Patch replay onto the base (`b0d37f2f`)

Throwaway worktree `scratch-apply` (branch `scratch-apply` from `b0d37f2f`, removed afterwards). Patches
applied in task order with `git apply` (no `am`, so no prototype commit messages); each was
`apply --check --stat` first, then applied:

```text
p1_patches/0001  6 files, +312 -1   (Collect.lean NEW, Uid.lean, LeanNCD.lean, lakefile.toml, CollectTest NEW, DSL/AGENTS.md)
p1_patches/0002  4 files, +84 -11   (ScheduledValidation.lean, CollectTest, RouteFragmentCorpusTest, DSL/AGENTS.md)
p1_patches/0003  8 files, +233 -22  (ScheduledValidation.lean, Eval/Error.lean, Eval/Eval.lean, lakefile, CollectEvalTest NEW, ContractTest, CompileTest, DSL/AGENTS.md)
p2a_patches/0001 4 files, +43 -5    (Collect.lean, Uid.lean, CollectTest, DSL/AGENTS.md)  -- needs --exclude=papers/semantics/additive_collection_slice1_artifacts/p1_findings.md
p2a_patches/0002 11 files, +538 -62 (Eval/Plan/{Adapter,Compile,Error,Prepared}.lean, 2 AGENTS.md, lakefile, 4 test files, CollectPlanTest NEW)
p2b_patches/0001 5 files, +145 -20  (Agreement.lean, Lowering.lean, ScheduledValidation.lean, AcsetCodecTest, CollectTest)
p2b_patches/0002 3 files, +52 -29   (NumericalProfile.lean, SourceDiagnosticAdmissionTest, SourceDifferentialPolicyTest)
```

Finding: `p2a_patches/0001` also edits `p1_findings.md` (an artifact the prototype changed in the same
commit). That file is already in its final form on the slice branch, so the plan applies the patch with
`--exclude=papers/semantics/additive_collection_slice1_artifacts/p1_findings.md`. All other patches apply
without it.

Commands (absolute paths abbreviated; run in the order above):

```sh
git -C <scratch> apply --check --stat <patch>        # then
git -C <scratch> apply [--exclude=<p1_findings.md>] <patch>
git -C <scratch> add -A leanncd
git -C <scratch> commit -q -m "scratch: patches applied in order"
git -C <scratch> diff --stat scratch-apply proto-additive-slice1-p2b -- leanncd     # output: EMPTY
git -C <scratch> diff --stat b0d37f2f scratch-apply -- leanncd                      # 27 files changed, 1395 insertions(+), 138 deletions(-)
```

Result: the replayed `leanncd/` tree is byte-identical to `proto-additive-slice1-p2b`.

T5 split check (second throwaway worktree `scratch-split`): after patches 1-4, the phase-1 command of plan §4 T5
(`--include` of the six production/AGENTS paths) printed `6 files changed, 60 insertions(+), 4 deletions(-)` and
applied; the complement (`--exclude` of the same six) printed `5 files changed, 478 insertions(+), 58 deletions(-)`
and applied; after the two p2b patches the tree again diffed EMPTY against `proto-additive-slice1-p2b`
(`git diff --stat scratch-split proto-additive-slice1-p2b -- leanncd`). Both worktrees and branches were removed.

## 2. Mutation manifest

`papers/additive_collection_slice1_mutations_post.json`: 30 cycles. 24 derive from the recorded prototype
mutations (the observed failure text in `p1_observed.md`, `p2a_observed.md`, `p2b_observed.md`); 6 were added by
the plan author because the prototype left a fixture without an individual kill (labels end `UNOBSERVED in the
prototype`: A1-M3 scatter, A1-M4 algebra, A1-M5 UID mismatch, A1-M6 freshness, A1-M7 identity, A3-M6 B3 in the
reference evaluator).

Format notes (what could not be expressed as in the prototype):
- The prototype recorded mutations by description, not as old/new text; every `old`/`new` here was written
  against the patched source and checked unique.
- `expect` strings are the guard POSITIONS from the observed failures (`CollectTest.lean:57:0`), not the
  expression text. Lean prints the elaborated expression (observed: `r3.compileToScheduled.run 0` prints as
  `EStateM.run r3.compileToScheduled 0`), so expression fragments are an unreliable match, while a
  position names the failing guard exactly. Positions are stable across tasks because every later patch
  APPENDS to `CollectTest.lean`, and the other files are each created or finally edited by one task.
  `File.lean:NNN` therefore appears in the manifest only (as in the existing manifests), never in shipped prose.
- Where the observed text recorded no position (the AcsetCodecTest length guard), the position was
  taken from the file (`AcsetCodecTest.lean:97:0`) and then confirmed by the run below.
- Multi-line `Expression` messages need no special handling because only the position is matched.

`--check` (base tree + patches applied, unfiltered):

```text
bash <wt>/leanncd/scripts/mutation-manifest.sh --check <scratch-apply>/leanncd <wt>/papers/additive_collection_slice1_mutations_post.json
manifest OK: 30 entries, 30 selected, every old-string unique
```

Cycle runs (not just `--check`), in `scratch-apply` with a copy-on-write clone of the donor `.lake`
(`cp -Rc`; the patched tree built up to date in seconds):
- Subset, label prefixes `A1-M3 A1-M4 A1-M5 A1-M6 A1-M7 A3-M6 A4-M1 A6-M1 A6-M2`: `9/9 cycles passed`
  (each: broke, file byte-identical, expected failure seen, restored build green).
- Interrupted full run (unfiltered): stopped after 5 PASS verdicts (A1-M1 .. A1-M5) because each cycle took ~3.5
  minutes (~100 minutes for all 30); the scratch tree was verified clean (`git status --short` empty) afterwards.
- Second subset, prefixes `A7-M1 A7-M2 A2-M1 A2-M2 A5-M1 A5-M3 A5-M6`: `7/7 cycles passed`.
- **Run at authoring: 18 of 30 cycles, all PASS** (A1-M1..M7, A2-M1/M2, A3-M6, A4-M1, A5-M1/M3/M6, A6-M1/M2,
  A7-M1/M2). **NOT run (12), validated by `--check` only (old-string uniqueness), with `expect` positions transcribed
  from the observed prototype failures:** A3-M1..M5, A4-M2/M3, A5-M2/M4/M5/M7/M8. The controller's unfiltered
  `mutation-manifest.sh` run in the finishing sequence is the gate for these; a position that does not appear is a
  manifest defect to repair from the observed log, not a pass.

## 3. Budget numbers (`token-report.py fa7fa04d-bd88-46a9-8f0e-ede698d860eb`)

```text
controller                    26.3M ctx  peak 386k  turns 106
Prototype slice 1 part 1      18.7M ctx  peak 259k  turns 110
Prototype slice 1 part 2a     26.4M ctx  peak 312k  turns 128
Prototype slice 1 part 2b     12.8M ctx  peak 221k  turns  87
Docsweep triage for slice 1    2.9M ctx  peak 128k  turns  38
Write slice 1 plan (this)     19.8M ctx  peak 300k  turns  95   (measured at the last cycle run; ~0.5M more while committing)
(earlier, not slice authoring) Design additive-semantics fix 9.2M; Draft additive decision note 12.5M
```

Slice-authoring dispatches before this one: 60.8M; with this write-up ~80.6M, against the ~50M target. The overrun is stated in plan §7 with its
cause. Self-reported prototype turn counts (~75, ~140, ~75) differ from the harness counts (110, 128, 87): P1 and
P2b were understated, P2a overstated; all three exceeded the 60-turn cap, and P1/P2a exceeded the 250k context peak.

## 4. Prose claims verified (grep / diff, not asserted)

| Plan claim | Check | Result |
|---|---|---|
| `Collect.lean` reachable from `import LeanNCD` | `rg -n 'DSL.Pipeline.Collect' leanncd/LeanNCD.lean` (patched tree) | line `import LeanNCD.DSL.Pipeline.Collect` between `RouteFragments` and `Lowering` |
| New test modules registered | `rg -n 'CollectTest\|CollectEvalTest\|CollectPlanTest' leanncd/lakefile.toml` | all three present in the `Tests` globs |
| AGENTS.md mentions the module | `rg -n 'Collect.lean' leanncd/LeanNCD/DSL/AGENTS.md` | Code Map row (T1 patch) |
| `Eval/AGENTS.md` `evalScheduled` row omits collection | `rg -n 'collect\|Collect' leanncd/LeanNCD/Eval/AGENTS.md` | no match: the T8 addition is real |
| `CollectTest` header cites the wrong evaluator test | `rg -n 'EntryTest' leanncd/test/DSL/Pipeline/CollectTest.lean`; `ls leanncd/test/Eval/EntryTest.lean` | cites `test/Eval/EntryTest.lean`; that file exists but the values are in `CollectEvalTest.lean` |
| No other lemma mentions `physicalizeForRoute` over the logical schedule | `rg -l 'physicalizeForRoute' leanncd/LeanNCD leanncd/test` | only `Bridge/Agreement.lean` among Bridge files; `DSL/Compile.lean` and `DSL/Ast.lean` mention it in docstrings only |
| G21 new leg still accepts | read `collisionTransition` in `RouteFragmentCorpusTest.lean` | old leg must be `cyclicDataflow "schedule: cyclic dataflow"`, new leg `some new` with `wellFormedDom` and an acset round trip |
| B3 runs after the f32 refusal and before size inference | read the `Eval.lean` hunk of `p1/0003` | confirmed |
| Pitfalls sections under ~3k chars | `awk 'NR>=<pitfalls line>' <AGENTS.md> \| wc -c` | DSL ~1.8k, Eval/Plan ~1.9k (unchanged by the patches); edited Contracts / consumer sections are ~7.8k / ~7.1k / ~1.5k and are not injected sections |
| module names in plan target lists | `rg -o '"...Test"' leanncd/lakefile.toml` | corrected `DSL.Pipeline.{Lowering,Structural,RecurMorphism,ScanAffine}Test` (the first draft said `DSL.*`) |
| value-grep patterns in T8 are not vacuous | `rg -U -c` on the patched tree (plan §4 T8 (c)) | each "before" count nonzero (2,2,2,2,2+1,1,1); the first draft's single-line patterns missed wrapped prose and were replaced |
| Guard counts per task | `rg -c '^\+#guard\|^\+example\|^\+theorem' <patch>` | T1 16, T2 6, T3 19, T4 4, T5 73 (+3 removed), T6 8, T7 1 (+ `def` fixtures) |

Patch sizes behind the plan's risk table: production lines are the `leanncd/LeanNCD/` hunks of each patch's
`--stat`; the T5 patch is 56K (364 new lines of `CollectPlanTest.lean`).

## 5. Authoring-checklist items not (fully) satisfied

- "Every Lean block compiled via `check-snippet.sh`": the plan contains no Lean blocks (code ships as patches that were
  compiled in the prototype and replayed here byte-identically). The manifest's `old`/`new` texts were compiled by the
  cycle runs, not by `check-snippet.sh`.
- "Every regression fixture mutation-tested": 24 cycles come from the prototype; 6 were added here and run. NOT
  covered by any cycle (listed in plan §2 PARKED): the `.recurMorphism` writer skip in `writerGroups`; the hand-built
  affine-slot `.assign` arm of `checkWriterGroup`; per-arm cycles for `Decl.cloneAs` (A1-M2/A5-M5 remove or break
  cloning wholesale or for `.typedTensor`; the `.tensor`, `.linear`, `.typedLinear` arms have no per-arm cycle and
  no fixture that declares them); `scanWriterConflict?`'s `.scanPre` arm (no fixture builds a `.scanPre` node).
  These were not probed; they are stated, not asserted covered.
- T8 documentation edits and the value-grep "after" counts are not yet run: they are the task's work.
- Authoring ran as two dispatches (prototype parts, then this write-up), as the skill requires; the prototype itself
  was three dispatches plus a docsweep.
- The patches' trailers name `Claude Opus 5.5` (prototype authorship); the plan gives each task a fresh commit message
  ending with the harness's attribution line, so those trailers are not reused.

## Close-out (execution, 2026-10-17)

Landed on `worktree-additive-collection-slice1` (final tip `cf6b7d92`; base `b0d37f2f`, plan commit `5977af03`):
T1 `afe25920`, T2 `17f7fb68`, T3 `89ddeb99`, T4 `38457b93`, T5 `193efadf` + `7a6a1dfb`, T6 `b1e32963`, T7 `d230946a`,
fix groups 1-3 `f4bfb667`, `f493a5e0`, `7fa81ec1`, T8 docs `1088b200`, fix group 4 (final reviews) `cf6b7d92`.

Verification by the controller (not by implementers):
- Per task: the manifest cycles of the task (T1 7, T2 2, T3 6, T4 3, T5 8, T6 2, T7 2) all PASS, each file byte-identical after.
- Full unfiltered manifest on the final tip: **31/31 cycles PASS** (the 30 planned plus `A3-M7`, added by fix group 2 under
  task id `FG2`; 21 `expect` positions were re-pointed by fix group 4 after earlier fix groups inserted fixtures).
- Full `lake-build.sh ... Tests` on the final tip: **Build completed successfully (8799 jobs)**, also green on `1088b200`.
- Reviews: per-task (T1-T6) and two final whole-branch lenses (a semantics, b regression), all APPROVE WITH MINORS, 0 Critical;
  the only Major (stale manifest positions) was a process defect, fixed. Review files: `additive_collection_slice1_review_*.md`.

Deviations from the plan and decision note, ratified by the user 2026-10-15: `route` calls `desugarMultiWriters` (not
`collectDefinitions`); plain+scan and scan+scan writers are rejected `multiWriterScan`; `PlanBindings.privateSlots`/`definedNames`
and `PreparedBindingsError.privateSlotUnpublished`. Later in execution: `collectorOwner` maps a private clone back to its public
tensor in both backends' dtype errors; summation is in SCHEDULE order (a writer reading a later-defined tensor moves behind
later writers; both backends agree bit for bit).

Measured token cost (`token-report.py` on the controller session, which includes design and authoring):
- Whole session 260.9M (controller 90.4M, peak context 619k; the controller's figure is not split by phase).
- Slice-authoring dispatches (3 prototype dispatches + docsweep + plan write-up): 82.4M against the ~50M target: **overrun**.
  Causes: prototype dispatches ran 87-128 harness turns (cap 60) on rebuild chains and 25-minute full `Tests` runs; the
  write-up dispatch ran 101 turns.
- Execution dispatches: implementers 23.1M (T8 alone 11.0M), per-task and final reviews 27.2M, fix groups 16.0M = 66.3M.
  Upper bound for execution including the whole controller figure: 66.3M + 90.4M = 156.7M, under the 175M cap
  (the 125M estimate in the plan §7 cannot be compared exactly because the controller is not split by phase).
- Turn-cap breaches: T7 (62 harness turns vs 40, polled an ~80 min build), T8 (91 vs 45, builds + large log read),
  fix group 4 (55 vs 50). Implementers on T1-T6 stayed within caps. Context-peak breaches: controller 619k.

Parked (unchanged from plan §8, plus review follow-ups; prepare-time B3 refusal CLOSED later, see below): `buildNameToStep` last-wins for direct
`routeCore` callers; `PlanBindings.privateSlots` hardening; JAX runtime on collected plans (unprobed); unpinned paths
(`.recurMorphism` writer skip, hand-built affine-slot `.assign` arm, `Decl.cloneAs` per-arm cycles); scan+scan on one state name
from surface code not constructed; routed collector step reads as a product (routed steps keep no term structure; pre-existing).
Prepare-time B3 landed after this slice on the Direct path: `InputSignatureError.definedName`, checked first in `prepareEvalPlan`
Step B in schedule write order (commit message of the B3 commit lists fixtures and hand mutations).
Next slices: S2 oracle extension (affine write slots, exact tropical carriers; see `oracle_extension_s2_design.md`),
S3 scatter-collision ⊕, tropical sorts, out-of-range write error, deletion of `CollisionReduce`/`fill`.

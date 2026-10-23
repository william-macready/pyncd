# S3b: production tropical sorts become max-plus and min-plus: implementation plan

Status: prototyped (P1-P8), replayed in order onto the slice tip and verified (design §9); this plan EXECUTES 16 ready-made patches.
Base: slice branch `worktree-additive-s3b-tropical-flip` (tip `ac6651f8` at authoring; its `leanncd/` tree equals local `main` `740bd4f8`:
`git diff --stat main -- leanncd` is empty, checked 2026-10-23). Worktree: `/Users/williammacready/code/python/pyncd/.claude/worktrees/additive-s3b-tropical-flip`
(`<wt>` below; Lean project `<wt>/leanncd`). This branch IS the execution branch: plan, record, patches, manifest are committed on it.
Rationale: `papers/semantics/additive_s3b_design.md` (§9 supersedes §4), audit `additive_s3b_audit.md` (read-only, base `740bd4f8`; §8c is partly wrong, see §2),
decision note `additive_production_decision_note.md` (§A, §F). Prototype evidence: `papers/semantics/additive_s3b_artifacts/p1..p8_findings.md`,
`manifest_report.md`, `manifest_table_run1.md`, `manifest_table_run2.md`; ledger `additive_s3b_ledger.md`. Scratch branches `proto-s3b-p1..p8`
(tips `c9c8f537`, `398d197b`, `281a1719`, `ccf9f745`, `6b0cb23b`, `3476f129`, `7473023d`, `43e86c5d`; do not merge them, they hold the complete prototype at `proto-s3b-p8`).
Patches: `<wt>/papers/semantics/additive_s3b_files/patches/` (`leanncd/` paths only, `T<k>-NN-slug.patch`, 16 files).
Manifest: `<wt>/papers/additive_s3b_mutations_post.json`, 48 entries (`task` field `T1`..`T8`: T1 6, T2 6, T3 6, T4 7, T5 9, T6 7, T7 2, T8 5; manifest_report). Record: `papers/semantics/additive_s3b_record.md` (skeleton, the executor fills it).

## 0. Goal, process weight, fixed decisions

**Goal.** The spec's tropical sorts are semirings: max-plus (⊕ = max, ⊗ = +, 0_K = -inf, 1_K = 0) and min-plus (⊕ = min, ⊗ = +, 0_K = +inf, 1_K = 0).
Production implemented (max or min, ×, ∓inf, 1.0): a valid collection monoid but not a semiring. After this slice, production (reference evaluator,
checked plan f64 and f32) computes the semirings and bit-agrees with the S2b oracle wherever the oracle can express the program
(`fourLegParity`). This is a MEANING CHANGE to existing programs (decision note §A10): every changed expectation is recorded old -> new with its reason
(record §2), no test is weakened. Anti-goals: a silently changed expected value; a max-plus-only fix with an untested min-plus twin; a padded-0.0 behaviour
surviving in a tropical statement; the known-difference apparatus left describing divergences that no longer exist.

**Process weight: Full** (`slice-plan` §0). A soundness surface (a new algebra in both production backends, with three new REJECTIONS that can wrongly reject valid
programs), a meaning change to existing programs, 8 code tasks plus a docs task, 16 patches, 48 mutation cycles. Nothing here fits the Direct path.
Execution is patch application; no task re-derives code.

**Fixed decisions (do not reopen; user 2026-10-22, design §2; the author's calls are marked and logged in record §3).**
1. Sort table: statement sort `S(stmt)` = bool if the destination is declared `predicate`; else max-plus if `agg = max`; min-plus if `agg = min`; else real.
   A tensor's sort is DERIVED from its writers' annotation (no declaration syntax; user confirmed). Never-written input: real (bool if `predicate`).
2. Ops: ⊗ real `×`, bool `min`, tropical `+`; ⊕ real `+`, bool `max`, max-plus NaN-propagating `max`, min-plus NaN-propagating `min`; (-inf)+(+inf) is IEEE NaN.
3. `real -> bool` reads keep their behaviour (identity); rejecting them is parked. `ScalarBinOp.max/min` are NaN-propagating in both backends for every algebra including bool.
4. A sort-neutral writer of a tropical tensor pads OOB bare reads with the TENSOR's 0_K; in S3b-i the only such writer is a scan base (or other neutral scan statement).
5. `OutOfBoundsPolicy.zeroPad` keeps its name (doc rewritten). Mixed-sort programs get production-only coverage. Scan-local scatter keeps overwriting (parked F3).
6. real<->tropical casts are the identity; bool -> tropical casts (false 0_K, true 1_K); tropical -> bool and max-plus <-> min-plus are REJECTED.
7. The landed shape (design §9, supersedes §4; author's call, observed): NO `algebras` map reaches either backend (casts use local facts); scan state sort and neutral writers use ONE
   mechanism (`scanStateStmts` rewrites each neutral statement's `agg`); neutral writers are decided by SHAPE only; the type is `SortAlgebra` (`LeanNCD.Algebra` is a class); route stays semantics-free.
8. Slice name "S3b" = the flip for single-writer programs; tropical multi-writer collection and writer agreement are S3b-ii, planned after this lands (Rule 13).

**Models.** Sonnet 5.5 high for implementers and per-task reviewers; Opus 5.5 high for the two final reviews (feedback: model selection).

## 1. Execution protocol

**Patches, in TASK order (all 16; the list is also the dependency order: each patch builds on the previous ones).**

| # | Patch | Task | # | Patch | Task |
|---|---|---|---|---|---|
| 1 | `T1-01-production` | T1 | 9 | `T5-01-production` | T5 |
| 2 | `T1-02-tests` | T1 | 10 | `T5-02-tests` | T5 |
| 3 | `T2-01-production` | T2 | 11 | `T6-01-production` | T6 |
| 4 | `T2-02-tests` | T2 | 12 | `T6-02-tests` | T6 |
| 5 | `T3-01-production` | T3 | 13 | `T7-01-production` | T7 |
| 6 | `T3-02-tests` | T3 | 14 | `T7-02-tests` | T7 |
| 7 | `T4-01-production` | T4 | 15 | `T8-01-scan-oracle` | T8 |
| 8 | `T4-02-tests` | T4 | 16 | `T8-02-duality-property` | T8 |

For each patch `P` (full name `<wt>/papers/semantics/additive_s3b_files/patches/<name>.patch`), two plain commands:
`/usr/bin/git -C <wt> apply --check --index P`, then `/usr/bin/git -C <wt> apply --index P`. `git apply` is atomic: a failed check leaves the tree untouched.
**STOP on any check failure**: report the patch, the failing hunk and `git status`; do not hand-merge, do not edit the patch. (Authoring check on this tip: `T1-01` passes `--check --index`; the later patches
were verified by the in-order replay, design §9, tree identical to `proto-s3b-p8`.) **Check and apply ONE patch per `git apply` call, in the table's order.** Passing several patches to one `--check` call fails
spuriously on any file two patches touch (plan review F11, observed 2026-10-23: `apply --check T1-01 T2-01` in one call reports `patch failed: leanncd/LeanNCD/Eval/Plan/Check.lean`), so that failure is not evidence of a base mismatch and
must not trigger the STOP. The series was verified by a blob-id chain (each hunk's preimage `index` equals the previous patch's postimage or the base blob): base `740bd4f8` + the 16 patches = `proto-s3b-p8` under `leanncd/`. Pre-flight: `/usr/bin/git -C <wt> diff --stat main -- leanncd` must print nothing.
If a check fails in T1/T2 (largest test migrations, ~30k bytes each) or T7-01: the only legitimate causes are a base mismatch or an earlier task not applied exactly; compare the previous commit's
tree with `proto-s3b-pK` (`/usr/bin/git -C <wt> diff --stat proto-s3b-pK -- leanncd`, K = the previous task's prototype) and report; the controller decides.

**Per task.**
1. Apply the task's patches in order (`--check` then `--index`). For T7 apply BOTH patches before building (T7-01 alone leaves `Semantics.SourceSortedDifferentialTest` not compiling: it names the deleted constructors).
2. Build ONCE in the background: `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd Tests` (full; the prototypes measured the known-red sets and job counts on the full `Tests` target, so the executor compares
   like with like). Wait for the notification; no polling. Never end a turn while a build you started is running. Lesson from authoring: an interim `completed` notice can arrive while a build still runs: check
   `ps` and `git log` before acting on it. Never Read a build log: use `rg -n "error|✖|jobs"` on it (a whole-log read cost P1 ~35k context).
3. Compare the red-target list with the task's KNOWN-RED set (table below) EXACTLY, and the job count with the measured count. Any other red target, any other count, any other `#guard_msgs` site SET is a
   finding: STOP and report, do not fix by editing a patch. The `SourceSortedDifferentialTest` (SSDT) check compares the EXACT failing-line set, not a count (a count can stay 19 while one site is fixed and another breaks):
   extract with `rg -o "SourceSortedDifferentialTest.lean:[0-9]+" <log>` (dedup by line number; the locator format is as quoted in the findings, adapt the pattern if the log prints it differently, the line SET is the check). The set must EQUAL
   the lines recorded in `additive_s3b_artifacts/p1_findings.md` (b) for T1-T2 (`104,106,191,193,196,242,262,264,266,269,272`, 11 lines) and in `p3_findings.md` (b) for T3-T6 (`104,106,108,188,191,193,196,201,204,206,209,227,228,242,262,264,266,269,272`, 19 lines).
   SSDT is not edited before T7, so its line numbers are stable T1..T6. For T4-T6 only the COUNT 19 is recorded in the findings (p4, p5, p6), not the lines: equality with p3's set there is expected, not previously observed (UNVERIFIED line by line; a difference is a finding to classify).
   GN4 (T1-T4): `rg -n "GnnScatterTest.lean:" <log>` shows only the GN4 site. These are build-log locators for the controller, not shipped text (the line-number ban applies to committed documents).
4. Read the task's production hunks and the fixture groups named in §4 in 40-60 line windows (`rg -n` for the symbols, then windows); tick the task checklist and the §3 rows it owns.
5. ONE commit per task (the staged patches plus any added files; `.claude/settings.json` is never staged; no pushing). Message style `feat(eval): S3b Tn <what>` (given per task) with the trailer
   `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>` as a second `-m`.
6. Report: commit hash, build target, jobs, red list, turns, context peak (Rule 6: <= ~60 turns, <= ~250k per dispatch; say so if breached).

**Known-red sets and measured full-`Tests` job counts (measured by the prototypes, findings (b)/(c); base 8823 from the B6 record, main `8cf5052a`, not re-run here).**

| After task | Red targets (and nothing else) | `Tests` jobs | Notes |
|---|---|---|---|
| base | none | 8823 | LeanNCD library alone 8614 |
| T1 | `Eval.Portfolio.GnnScatterTest` (GN4 observed `[4,5,4,5]`), `Semantics.SourceSortedDifferentialTest` (11 error sites) | 8823 | GN4 -> T5; SSDT -> T7 |
| T2 | same two (SSDT 11 sites) | 8823 | |
| T3 | same two; SSDT now 19 error sites (8 new `tropicalScatterFill` rows) | 8823 | |
| T4 | same two, SSDT 19 sites | 8823 | |
| T5 | `Semantics.SourceSortedDifferentialTest` only (19 sites); GN4 green with its ORIGINAL expectation | 8824 | +1: `Eval.Plan.BoolCastTest` |
| T6 | `Semantics.SourceSortedDifferentialTest` only (19 sites) | 8824 | RC10 flips in this task |
| T7 | none (first fully green tip since T1) | 8824 | sweep counts unchanged: 3832/3832/0 rejected, scan corpus 17/17 |
| T8 | none | 8825 | +1: `Eval.Plan.DualityTest` |

The two inherited reds are expected failures of the stated test only; a task that turns a target red outside this table is wrong. The `lakefile.toml` `Tests` glob gains `Eval.Plan.BoolCastTest` (T5-02) and `Eval.Plan.DualityTest` (T8-02).

**Controller steps per task (not the implementer), after the task's commit.** `bash <wt>/leanncd/scripts/mutation-manifest.sh --task <Tn> <wt>/leanncd <wt>/papers/additive_s3b_mutations_post.json`
and read the table. A mutation that does not fail with its `expect` strings is a FINDING (missing fixture, equivalent mutant or bad mutation text), never a pass. Know what was and was not observed
(manifest_report (b)): of the 48 entries only FIVE (T3-M3, T4-M3c, T6-M8, T7-M1, T8-M1) were observed with `expect` enforced (run 2); the other 43 were observed to break the build in run 1 with empty `expect`,
and their `expect` strings were checked by string match against run-1 output (`verify_expect.py`, 0 missing) and for existence at each entry's task tip (`tipexpect.py`). The per-task run is therefore the
FIRST enforced run for 43 entries: a failing `expect` there is most likely a stale string, not a surviving mutant; classify before acting.
**Serialization (shared worktree).** The cycles run IN the slice worktree and edit it: `mutation-cycle.sh` mutates a file under `<wt>/leanncd`, builds, restores it and rebuilds, and has no dirty-tree or lock check
(`rg -n "dirty|status|clean" <wt>/leanncd/scripts/mutation-cycle.sh` finds nothing but exit-status handling). So: never overlap a manifest run with patch application, an implementer, a reviewer's build, or any other build in `<wt>`.
After `--task Tk` prints its summary table (every row PASS, or each non-PASS classified), the controller confirms `/usr/bin/git -C <wt> status --short` is EMPTY (apart from `.claude/settings.json` and untracked review/ledger files, which are named)
BEFORE applying T(k+1)'s first patch. A non-empty status after a run means a mutated file was not restored: restore it from the task commit (`git checkout -- <file>`) and record the event as a finding; do not start the next task on that tree.
Cost, measured (manifest_report (e)): run 1 was 53 cycles = 106 builds in about 2.5-3 hours, i.e. about 3 minutes per cycle averaged over ALL of them, and it INCLUDED every plan-root mutation (`DSL/Ast.lean`: T4-M7b, T6-M7, T6-M8, T8-M5;
`Eval/Contract.lean`: T1-M1, T2-M6, T8-M3; `Eval/Plan/Dense.lean`: nine entries, counted from the manifest's `file` field; the review said eight); run 2 was five cycles in about 15 minutes. (An earlier brief said one near-root cycle took over an hour; no artifact records that and the recorded run contradicts it as a typical figure: it is not used here.)
Hence: run `--task` filtered, once per task, never the full manifest per task; per-task cycle counts are in §4. Do not re-run the full manifest at the end unless a fix dispatch touched production (then re-run the tasks whose `file`s it touched).

**Expected wall time (serial; arithmetic stated so it can be checked).** Full `Tests` builds: 8 (one per task T1-T8) + 1 (after T9, §5) = 9; the only full-build figure on record is about 25 minutes (S2b, §5; not measured for S3b, and a change near the plan root costs more than a leaf test change),
so 9 x 25 = 225 min. Cycles: 48 entries x about 3 min = 144 min. Per task (build + cycles x 3 min): T1 25+18 = 43, T2 25+18 = 43, T3 25+18 = 43, T4 25+21 = 46, T5 25+27 = 52, T6 25+21 = 46, T7 25+6 = 31, T8 25+15 = 40, then the final build 25;
total 43+43+43+46+52+46+31+40+25 = 369 min, about 6.2 hours of serial build and cycle time, to be planned as 6-7 hours (waits, a classified finding or a fix dispatch add to it). Reviews (8 mid-tier, 2 final) are on top. Do not start T1 expecting less.

**Deferral order if time is short.** NEVER skip a task's full `Tests` build or its known-red comparison (§1 steps 2-3), and never skip the final full build. Cycles run UNFILTERED (all of the task's entries) for the evidence the slice rests on:
T1 (constants and the ⊗ = `+` flip), T2 (padding, Iverson, empty folds), T3 except T3-M3, T4 except T4-M3c (the three rejections' accept-neighbour fixtures), T5 except T5-M11, T6 except T6-M8 and T6-M12 (scan init), T8-M3 and T8-M5 (production-level entries).
Defer in THIS order (first listed is deferred first), recording EVERY deferral as `skipped` in record §4 (never silently omitted, Rule 12):
(1) the three sampled extras `T7-M5`, `T5-M11`, `T6-M12` (the manifest report does not label any entry "probable cut"; these three are chosen because each has an independent raw-plan or carrier-level fixture, `BoolCastTest` raw `#guard`s, `ScanCompileTest` raw-plan guards, `SourceOracleCarrierTest`);
(2) the five entries already observed with `expect` ENFORCED in run 2 at the final tip: `T3-M3`, `T4-M3c`, `T6-M8`, `T7-M1`, `T8-M1` (the per-task run would only repeat them at an earlier tip);
(3) `T8-M4` (test-side oracle) and `T8-M6` (f32 min-plus identity; also killed by the pre-existing `Adapter32Test` fixture 9). That is at most 10 of 48 cycles (about 30 minutes): the deferral order buys little, so prefer waiting to skipping. The reviewer's variant of this order
(never skip `T4-M1..M7b`, `T5-M4b`, `T5-M5`, `T5-M11`, `T6-M11`, `T6-M12`) differs only on `T5-M11`/`T6-M12`, which the controller brief put in the sampled set; the choice is recorded here, not hidden.

**Reviews.** Per task ONE mid-tier review of the commit diff plus the §3 rows the task owns, findings appended as it goes to `papers/semantics/additive_s3b_review_<Tn>.md` (40-60 line windows). Final: TWO Opus lenses (§5).
One fix dispatch per finding group, given only its plan sections. Model: Sonnet 5.5 high.

**Lessons from authoring (apply them).** (a) Every prototype exceeded the 60-call cap (harness counts 96 to 149, ledger), so no execution task re-derives anything: apply patches. (b) Hand mutations were the cost driver
(P1, P2): nobody hand-writes a cycle during execution; use the manifest. (c) A parallel launch needs usage headroom; reviewers append findings as they go. (d) A tool path containing `test/Eval` can make `rg` refuse
in this harness: search from `leanncd/test` with `--glob "**/Eval/**"` (p3 (g)). (e) Each Edit to an AGENTS.md echoes its hook text (the largest avoidable cost in P5/P6): batch doc edits in T9.
(f) `bias` is a reserved token under `import LeanNCD.Eval.Entry`; in a hand-written test use `AffineMap.mk` (p5 (a)3). (g) In `tlprog!`, `Out[i + 1] := ...` is a scan advance (`scanAxisNotIter`); use `Out[2 * i + 1]` for an affine scatter (p8 (a)4).

## 2. Global constraints (exact values)

**Sort and constants (design §3; observed in findings; each row's code site grep-verified at `proto-s3b-p8`).**

| Quantity (statement of sort K) | real | bool | max-plus | min-plus |
|---|---|---|---|---|
| ⊗ of a term's factors | `*` | `minNaN` | `+` | `+` |
| 1_K (empty product, true Iverson) | 1.0 | 1.0 | 0.0 | 0.0 |
| ⊕ (contracted coordinates, terms, scatter collisions) | `+` | `maxNaN` | `maxNaN` | `minNaN` |
| 0_K (empty sum, zero-extent reduction, unwritten scatter cell, unwritten scan-state cell, false Iverson, OOB bare read) | 0.0 | 0.0 | -inf | +inf |
| OOB read under a `unaryFn` | 0.0 (the primitive takes REAL input, the result is read back by the identity); in every sort | | | |
| collision | `+` (S3a) | `max` (S3a; checked layer still refuses a top-level predicate scatter, `predicateScatterDest`) | `maxNaN` | `minNaN` |

f32 constants are bit patterns: ⊗ identity (tropical 1_K) `0x00000000`; real ⊗ identity `0x3f800000`; max-plus 0_K `0xff800000`; min-plus 0_K `0x7f800000` (`admittedAlgebraF32Max`/`Min` in `Eval/Plan/Check.lean`;
the checked scan worker takes `+0` and these two for `StateInit`). f64 constants: `Float.toBits 0.0` (⊗), `-1.0/0.0`, `1.0/0.0`.

**Statement-sort rule and neutral writers.** A statement is SORT-NEUTRAL (`Stmt.isSortNeutral` @ `DSL/Ast.lean`) iff it has one term, one factor that is a `read` or `unaryFn`, and every index variable of that read lies on
the LHS (no contracted axis). A neutral statement has no sort of its own (`Stmt.ownAlgebra?` is `none`; a `predicate` destination is `bool` whatever the shape); its annotation is IGNORED. Consequence, PARKED and pinned
(`parkedAllNeutralScanState` @ `test/Eval/Plan/DualityTest.lean`): a scan state all of whose statements are neutral evaluates REAL even when annotated `maxreduce` (`M = [[4,4],[0,0]]` on both backends; the alternative
would be `[[4,4],[-inf,-inf]]`). Within a scan, EVERY neutral statement (scratch included) is evaluated in its destination's sort (`scanStateStmts`), consistent with `algebraOf` (p6 (a)3); observable only for an annotated neutral scratch
statement with an OOB bare read, and no fixture does that (parked, see below). A top-level single-writer name's entry is its own statement's sort (neutrality matters only inside a scan state).

**Cast table** (source sort of a bare `read` factor vs statement sort K): full table is §3(i). Values realised: bool -> real 0/1; bool -> max-plus false -inf, true 0.0; bool -> min-plus false +inf, true 0.0; truth is "stored value != 0"
(`ScalarKernelOps.isTrue`, reference `boolReadCast`); everything else identity; REJECTED (`CompileError.sortCastUnsupported dest src`): tropical -> bool, max-plus <-> min-plus. The OOB pad is never cast; a read under `unaryFn` is neither cast nor rejected.

**Rejections and where they live** (design §3 with its P4 correction; entry map is §3(iii)): `tropicalNonlin` (a tropical destination with `nonlin != identity`, statements incl. scatter) from `checkTropicalOutput` @
`DSL/Pipeline/Structural.lean`, called from BOTH `checkDtypes` (source/surface pipeline) and `checkScheduledDtypes`; `scanStateAlgebraMismatch` (two non-neutral statements of one scan state disagree) and `sortCastUnsupported`
from `scheduleAlgebras`/`checkSortCasts` @ `DSL/Pipeline/ScheduledValidation.lean`, run by `validateScheduled` only. Observed precedence in `validateScheduled`: `buildDeclEnv` -> `checkScheduledReadRanks` -> per-statement loop over the
whole schedule (axis kinds, `checkPredicateOutput`, `checkTropicalOutput`; source order, scan `base ++ recur`) -> `scheduleAlgebras` (scan agreement, every scan node) -> `checkSortCasts` -> topology (`cyclicDataflow`) -> collection
(`multiWriter*`). Plan level (raw plans, no source): `PlanError.castNotAdmitted termIndex factorIndex` (cast flag needs a `.bool` source, `unary = none`, tropical algebra) and `ScanPlanError.stateInitNotAdmitted stateIndex init dtype`
(a `negInf`/`posInf` init on a `.bool` state). `route` of a direct `ScheduledProgram` stays semantics-free (no new rule; `LoweringTest` AGG1/AGG2 and `RouteFragmentCorpusTest` `aggregate` are UNCHANGED).

**New and changed identifiers (each `git grep`-verified at `proto-s3b-p8`; identifiers only, no line numbers).**

| Identifier | File | Task |
|---|---|---|
| `SortAlgebra` (`real|bool|maxPlus|minPlus`), `AggOp.algebra`, `SortAlgebra.stateAgg`, `DeclEnv.declAlgebra`, `Stmt.algebra` | `LeanNCD/DSL/Ast.lean` | T4 (`stateAgg` T6) |
| `Stmt.isSortNeutral` (T4, here from the start); `Stmt.ownAlgebra?` (T4 in `ScheduledValidation.lean`, MOVED here in T6); `scanStateSorts`, `scanStateAlgebra`, `Stmt.withAgg`, `scanStateStmts` | `LeanNCD/DSL/Ast.lean` | T4 / T6 |
| `scheduleAlgebras`, `checkSortCasts`, `CheckedScheduledProgram.algebras` field, `CheckedScheduledProgram.algebraOf`, `validateScheduled` | `LeanNCD/DSL/Pipeline/ScheduledValidation.lean` | T4 |
| `checkTropicalOutput` (called from `checkDtypes` and `checkScheduledDtypes`) | `LeanNCD/DSL/Pipeline/Structural.lean` | T4 |
| `CompileError.tropicalNonlin`, `.scanStateAlgebraMismatch`, `.sortCastUnsupported` | `LeanNCD/Exec/Uid.lean` | T4 |
| `maxNaN`, `minNaN`, `maxNaN32`, `minNaN32` (shared scalar helpers) | `LeanNCD/Eval/Error.lean` | T1 |
| `Combine.tropical`, `Combine.max`, `Combine.min`, `Combine.bool` (now `⟨minNaN, maxNaN, 0.0, 1.0⟩`), `boolReadCast` | `LeanNCD/Eval/Contract.lean` | T1 (`boolReadCast` T5) |
| `gather zero one ...` and `gatherRead` with a `pad` parameter (T2); `gatherCast` (core) with `gather` as its identity-cast wrapper (kept for `GatherTest`) and `gatherRead`'s trailing `cast` (T5) | `LeanNCD/Eval/Gather.lean` | T2 / T5 |
| private `tropicalAlgebra`, `tropicalAlgebraF32`; `admittedAlgebraMax/Min/F32Max/F32Min` keep their names | `LeanNCD/Eval/Plan/Check.lean` | T1 |
| `ScalarKernelOps.isTrue` (added), `ScalarKernelOps.one` (deleted), `gatherFactorWith` pad/one parameters | `LeanNCD/Eval/Plan/Dense.lean` | T2, T5 |
| `ReadPlan.boolToTropical : Bool := false` | `LeanNCD/Eval/Plan/Kernel.lean` | T5 |
| `PlanError.castNotAdmitted` | `LeanNCD/Eval/Plan/Error.lean` | T5 |
| `StateInit` (`zero|negInf|posInf`), `StateSlot.initValue : StateInit := .zero` | `LeanNCD/Eval/Plan/RawStep.lean` | T6 |
| `ScanPlanError.stateInitNotAdmitted` | `LeanNCD/Eval/Plan/Scan.lean` | T6 |
| `DenseTensor.approxEq` treats equal values (incl. equal infinities) as equal; NaN stays unequal | `LeanNCD/Eval/Tensor.lean` | T2 |
| DELETED: `EvalError.scatterFillNotIdentity`, `CapabilityError.scatterOptsNotAdmitted`, `checkScatterAgg`, `scatterAggOrFail`, the `boolDest` special case of `evalScatter`; oracle `scatterPolicy` refusal; `SortedClassification.knownContractDifference`; conditions `tropicalMultiFactor`, `tropicalScatterFill`, `unexplainedAgree`, `confirmsSorted` | `Eval/{Error,Eval,Scatter}`, `Eval/Plan/{Error,Compile}`, `Semantics/Source/{Adapter,Admission,NumericalProfile,SortedDifferential}` | T3, T7 |

Verified absent at `proto-s3b-p8`: `git grep` of every deleted name over `leanncd/LeanNCD` finds them only in `.md` files (T9 fixes those) and `Semantics/Source/Differential.lean` keeps the REAL harness's
`Differential.Classification.knownContractDifference` (a different type; not deleted). No Lean source outside tests names a deleted constructor; historical comments in tests keep the names as history.
No exhaustive `match` over `CompileError`, `PlanError`, `ScanPlanError` exists, so the new constructors forced no other edit (p4 (a)5, p5, p6 (a)5).

**Test modules.** NEW: `Eval.Plan.BoolCastTest` (T5-02 creates, 261 lines added; T6-02 adds its T6 section), `Eval.Plan.DualityTest` (T8-02, 260 lines). Both registered in `leanncd/lakefile.toml` (`Tests` glob list, beside
`Eval.Plan.CompileTest` / `Eval.Plan.DifferentialTest`). Counts: job counts above; sweep counts that must NOT move: DifferentialTest sweep total=3832 accepted=3832 rejected=0, scan corpus 17/17 (T1..T7); `SourceSortedDifferentialTest` red error sites 11 (T1-T2) then 19 (T3-T6).
DualityTest pins (ONE `#guard`, over `runAll`, pins all the counts below, all three backends identical; the file's 12 `#guard`s are that one, five `dualEqOf` self-tests, four grid pins and two `parkedAllNeutralScanState` pins, checked at `proto-s3b-p8`): `enumPrograms` 3832 (all dual, 0 refused, 0 skipped; 3754 distinguished from the all-`sum` run), `enumScanCases` 17 (13 checked and distinguished, 4 skipped: template 2 `relu`),
`tropicalUnwrittenScanCases` 2 (both dual and distinguished), top-level scatters 2 (both dual and distinguished). The 78 sweep programs whose max result coincides with the real result are a count (3832-3754), the reason was not investigated (p8 (f)).

**Corrections to the audit and design that the plan relies on (read before trusting those documents).**
- Audit §8c ("become rejections": `CompileTest` pointwise `.relu`+`.max`, `StructuralTest`, `SourceRawCorrespondenceTest`) is NOT borne out: p4 (b) observed no pre-existing test flipped by the new rejections; `LoweringTest` AGG1/AGG2 and
  `RouteFragmentCorpusTest` `aggregate` are unchanged by design. The reason the `CompileTest`/`StructuralTest`/`SourceRawCorrespondenceTest` rows did not flip is UNVERIFIED (p4 did not trace them). Only execution-entry tests can flip.
- Audit §8f.1 holds: `MaxReduceTest` does not change value (it passes its own `mul` to `evalAssignWith`). Audit §8d refusal pins that flipped: three `ScanTest` shape-1 rejections, two `CompileTest` f32 scatter rejections, the `SourceSortedDifferentialTest` known-difference rows,
  the `DifferentialTest` classifier arm (removed), and `SourceAdmissionAffineTest`/`SourceSortedAuditTest` refusals (record §2).
- p1 (f)1: the all-negative-B row no longer separates the -inf seed; the load-bearing fixture needs NEGATIVE A too (`storeNegA_NegB`, both f64 and f32). p1 (f)3: single-factor tropical statements are not bitwise unchanged (`0.0 + v` normalises `-0.0`); no fixture feeds -0.0.
- Design §4's per-backend `algebras` map and `ReadPlan.cast` are superseded by §9 (`ReadPlan.boolToTropical`); p4 (f)'s remark that the backends need the map was an over-estimate (p5 (a)1). p1 (h) said `gather` has one caller; p2 (e)5 corrects it (two production callers: `evalAssignSeeded`, `evalScatter`).
- Lake/Lean version: p1 says Lean 4.35, p2 observed 4.30.0 from `lake-build.sh` (behaviour-irrelevant; the toolchain pin decides).

### Deliberately NOT done, with owner (Rule 14)

| Item | Owner / disposition |
|---|---|
| Tropical multi-writer collection and the writer-agreement rule (A4); `multiWriterAlgebra` stays the only refusal (`CollectTest` C6/C6b/C6c, `CollectEvalTest` J4 keep their constructors; min twins added in T8) | S3b-ii: its own slice; plan only after this lands (Rule 13); ~1 slice |
| Multi-writer scatter B5 | parked (decision note); own slice |
| F3: scan-local scatter overwrite on collision | parked; unchanged code path (`writeScanStmtSlice`) |
| `real -> bool` rejection (decision 1) | parked; pinned as ACCEPTED by T4-M3d and the "predicate reads real" accept fixture; ~1 Direct item |
| `OutOfBoundsPolicy.zeroPad` rename | parked; doc rewritten only (decision 4) |
| Oracle per-tensor sorts; oracle coverage of casts, Iverson values and padding (these are hand-valued, production-only) | later follow-up (design §2.5); ~1 slice |
| JAX/Python tropical execution (`Executable` gate `a.algebra == realAlgebra` stays) | unowned; `leanncd/experiments/jax_bridge/README.md` unchanged. `Executable.lean` refuses every scan step and every non-real algebra, so the new `ReadPlan.boolToTropical` and `StateSlot.initValue` fields (ignored by JAX codegen) cannot reach JAX (review F13, not re-traced here). `JaxExperiment` is outside `Tests`: one explicit `lake-build.sh <wt>/leanncd JaxExperiment` at the final build would confirm it still compiles (§5) |
| All-neutral scan state with a tropical annotation evaluates REAL (decision needed: does a neutral annotation vote for the sort?) | design-note decision for a later slice; pinned by `parkedAllNeutralScanState`; flipped by mutation T8-M5 |
| Annotated NEUTRAL scratch statement in a scan evaluates in its state's sort (consistent with `algebraOf`), no fixture | parked; ~1 Direct fixture (raw `ScheduledProgram`, donor `scratchMaxSched`) |
| Contracted-axis condition of the neutral-writer definition has no dedicated fixture (only indirectly by "scan base max / recurrence min"; T4-M4b was killed by the same fixtures as T4-M2, then dropped as non-independent) | parked; ~1 Direct fixture (manifest_report (a)) |
| Bool STATE read by a tropical scan step is cast (reference `isPredicateDest` on the state name; plan: capture-slot dtype) but no fixture exercises it (p5 (a)4, (d)) | parked; ~1 Direct fixture; the scan fixtures read bool EXTERNALS |
| Multi-writer SOURCE name read by a bool statement: the cast check sees the declaration (real), not the tropical sort. UNREACHABLE for plain `.assign`/`.scatter` writer sets: `validateScheduled` always runs `collectDefinitions` -> `desugarMultiWriters`, and `checkWriterGroup` throws `multiWriterScatter` (scatter-shaped writer), then `multiWriterAlgebra` (any `.assign` writer with `agg != .sum`), and `scanWriterConflict?` throws `multiWriterScan` for a scan-node writer first; the steps before collection can only add an EARLIER refusal. Only WHICH refusal wins is unpinned (no fixture), not soundness (checked by `git grep` at `proto-s3b-p8`). Residual, not traced: `writerGroups` skips a name with a `.recurMorphism` writer (its doc says every entry rejects that escape hatch on its own terms) | parked; fold the order of refusals into S3b-ii (it rewrites multi-writer algebra handling) |
| (p8 (c) parks "ScatterDense32Test has no tropical fixture at all": FALSE at `proto-s3b-p8`: it has a pre-existing max scatter row and fixture 1.6c (max AND min collision, bits), added by T3; checked by `git grep`) | NOT parked: no action |
| `T5-M8` / `T5-M10` (cast flag at the scan-STEP and plain callers of `residualizeAssignment`) were pruned and never run, so the step-caller flag has no killing observation (C24) | parked; one manifest entry (T5-M8, `Eval/Plan/Compile.lean`, target `Eval.Plan.BoolCastTest`), ~1 Direct item; manifest NOT edited here |
| Cast under a contracted axis has no fixture of its own (manifest_report: cast fixtures are bare reads over the output axes and `[j]`) | parked; ~1 Direct fixture |
| Grid scan cases not registered in `DifferentialTest`'s three-way (compiled plan, legacy, independent) leg | parked; one more list entry (p8 (d)) |
| Single-factor `-0.0` through a tropical statement is normalised to `+0.0` (bit pattern differs, value equal) | accepted; flag if a later bit-exact f32 fixture feeds `-0.0` |
| `Eval/Plan/AGENTS.md` pitfall "Don't delete producer-less constructors" conflicts with T7's deletions | RESOLVED in T9 by scoping the pitfall to the named constructors |
| Stale S2a/S2b manifests (`additive_s2a/s2b_mutations*.json`) mention divergences removed here | not edited (records); listed in the record |
| GN4 itself does not discriminate a cast of false to 0.0 unless the masked row would win (p8 (c)); `GN4m` was added for that | done in T8 |

## 3. Sibling audit (case x class): deliverables of T4, T5, T6, T8

Classes: R required refused, A required accepted, V value required, **S silently ignored (no fixture or code path forces it)**. Every S cell is a candidate instance N+1 and is either pinned by a named fixture
or parked in §2. Ids are the row ids the per-task reviewer ticks.

**(i) Cast table: bare `read` source sort x statement sort K** (`checkSortCasts`; the destination's entry in `algebraOf` is K).

| Id | Source -> K | Class | Behaviour | Pinned by |
|---|---|---|---|---|
| C1 | real -> real | A | id | existing portfolio |
| C2 | real -> bool | A (S by design, decision 1) | id | T4 accept "predicate reads real"; T4-M3d |
| C3, C4 | real -> max-plus / min-plus | A | id | T4 accept "max-plus reads predicate+real+max-plus"; T5 c2, c3 |
| C5 | bool -> real | V | 0/1 (reference bit-identical: unobservable there) | T5 c1 (plan f64/f32) |
| C6 | bool -> bool | A | id | existing |
| C7 | bool -> max-plus | V | false -inf, true 0.0 | T5 a1 (donor GN4, negative X), f1; T5-M1/M2/M3; GN4 |
| C8 | bool -> min-plus | V | false +inf, true 0.0 | T5 a2, f2 |
| C9, C13 | max-plus / min-plus -> real | A | id | T4 accept "real reads tropical"; T3/T7 rows |
| C10 | max-plus -> bool | R `sortCastUnsupported` | | T4 "predicate reads a max-plus tensor"; T4-M3b |
| C14 | min-plus -> bool | R | | T4 "predicate reads a min-plus tensor"; T4-M3b |
| C11, C16 | tropical -> same tropical | A | id | T4 accept "min-plus reads min-plus", contracted max base + max recur |
| C12, C15 | max-plus <-> min-plus | R | | T4 "max-plus statement reads a min-plus", reverse; T4-M3c |
| C17 | read under `unaryFn` (any source) | S by design: real input, no cast, no rejection | | T4 accept "`unaryFn` read of min-plus in a max-plus statement"; T4-M5; T5 b1/b2 (`sqrt`, cast under unary would be a domain error); T5 raw guard (unary rejects `castNotAdmitted`) |
| C18 | Iverson factor | S by design (reads no tensor) | | T2 Iverson rows |
| C19 | OOB pad of a cast read | A: NOT cast | | T5 g1/g2 (`axis i : ℕ = 3` needed); T5-M6 |
| C20 | destination with no map entry (multi-writer name) | S: not cast-checked | backstop `multiWriterAlgebra` | T4 fixture "W written twice by max reading min-plus N" -> `multiWriterAlgebra "W"` (both entries) |
| C21 | multi-writer SOURCE name read by a bool statement | R (backstop, total for plain writer sets): refused by collection on every ordering | `multiWriterScatter` / `multiWriterAlgebra` (`checkWriterGroup`) or `multiWriterScan` (`scanWriterConflict?`); which one wins is unpinned; a name with a `.recurMorphism` writer is skipped by `writerGroups` (not traced) | parked (§2): order of refusals only |
| C22 | neutral scan base: pad and cast key follow the STATE's sort | V | | T6 c1/c2 (OOB `X0[j+1]`), d1/d2 (neutral base bare-reading `predicate P`); T6-M7 |
| C23 | bool STATE read by a tropical scan step | **S, unpinned** | cast applied (both backends) | parked (§2) |
| C24 | scatter compute half, scan base, scan step and plain callers of `residualizeAssignment` (each passes `isBoolSlot`: four call sites at `proto-s3b-p8`) | V | cast on all four callers | T5 d1/d2 (scatter), d3/d4 (scan base + step), a1/a2 (plain). Cycles exist for TWO callers only: T5-M7 (scan base), T5-M9 (scatter). The scan-STEP and plain caller cycles (T5-M8, T5-M10) were pruned and never run (manifest_report (c)): the claim that d1..d4 cover all four callers is asserted, not observed; the step-caller flag has no killing observation (plain is covered indirectly by a1/a2 and GN4 through the shared Dense path, which is not the caller flag). Parked: one cycle for T5-M8, ~1 Direct item |
| C25 | plan checker | R | `castNotAdmitted 0 0` for non-bool source, real algebra, unary read; accepts with cast and neighbours | T5 raw `#guard`s (7); T5-M11 |

Statement-level `tropicalNonlin` cells: relu/softmax on `.max` and `.min` rejected (statements and scatter; axiswise softmax pinned); relu+sum and identity+max/min accepted; predicate relu+max stays `predicateNonlin`, predicate identity+max stays `predicateAgg`
(order unobservable between `predicateNonlin` and `tropicalNonlin` because `Stmt.algebra` is predicate-aware: T4-M7 was an EQUIVALENT mutant, replaced by T4-M7b). Scan agreement: base max / recur min and base real / recur max reject; neutral sum base + max recur
(max-plus), neutral max base + min recur (min-plus: the neutral base's annotation is ignored), contracted max base + max recur, all-real accept; a per-statement violation on a later statement beats an earlier scan mismatch; scan mismatch beats an earlier cast violation.
`ScanStmt.scanPre` (the `recurMorphism` escape hatch) carries a pre-built morphism with no `agg`: it has no sort and no cell here (`sourceStmts` is empty for it).

**(ii) Constants, padding and identity sites (audit §1), disposition.**

| Id | Site | Disposition |
|---|---|---|
| K1 | reference `gatherRead`/`gather` OOB pad | CHANGED T2 (bare: statement 0_K via `gather zero one`; unary keeps 0.0); cast param T5 |
| K2 | reference Iverson in `gather` | CHANGED T2 (1_K / 0_K) |
| K3-K4 | `evalAssignSeeded` accumulators, `Combine` records | CHANGED T1 (`Combine.tropical`; NaN-propagating) |
| K5 | `evalAssign` real default | UNCHANGED by design (real only) |
| K6-K8 | `evalScatter` fill, per-source value, collision fold, `boolDest` | CHANGED T3 (fill `unit0`, fold `combine`, `boolDest` deleted; predicate collisions unchanged because `Combine.bool.combine` is `maxNaN`) |
| K9 | scan state init in `Eval/Scan.lean` | CHANGED T6 (state's `unit0` via `scanStateAlgebra`) |
| K10 | defensive `getD` default for a missing state (shape `[]`) | UNCHANGED by design (unreachable as data) |
| K11 | `writeScanStmtSlice` overwrite on collision | UNCHANGED (F3 parked) |
| K12 | `ScalarKernelOps.zero/one` | CHANGED T2: `one` deleted (dead), `zero` kept as the carrier's real 0 (unary pad); `isTrue` added T5 |
| K13 | `gatherFactorWith` pad | CHANGED T2 (bare: decoded `reduceId`; unary: `ops.zero`; store-slot-missing branch unreachable via `validateStore`, pads like OOB); cast T5 |
| K14 | plan Iverson arm | CHANGED T2 (true -> decoded `factorId`, false -> decoded `reduceId`) |
| K15 | factor/reduce fold seeds | UNCHANGED code (empty product, empty sum, zero-extent reduction fall out of K17) |
| K16 | `runDenseScatterWith` fill/fold | UNCHANGED code (already algebra-generic since S3a); only the guard went (T3) |
| K17-K18 | `admittedAlgebra*` constants and tables | CHANGED T1 (`factorOp := .add`, `factorId` 0.0 / `0x00000000`; reduce ids unchanged) |
| K19 | `OutOfBoundsPolicy.zeroPad` name | UNCHANGED by design (doc rewritten T1/T2) |
| K20 | `Plan/Scan.lean` state init | CHANGED T6 (`StateInit`, worker takes `zero negInf posInf`) |
| K21 | `Compile.lean` algebra selection from `agg` | UNCHANGED selection rule; T3 deletes `scatterAggOrFail`; T5 passes `isBoolSlot` into `residualizeAssignment`; T6 applies `scanStateStmts` in `compileScan` and fills `initValue` |
| K22 | `Executable.lean` JAX gate `a.algebra == realAlgebra` | UNCHANGED by design (tropical stays refused; grep-verified present) |
| K23 | abstract machine `Semantics/Plan/*` | UNCHANGED (parametric over `ScalarOps (K s)`) |
| K24 | `ScalarBinOp.min/max` arms (`floatOps`, `float32Ops`) and `Combine.bool` | CHANGED T1 (NaN-propagating; differs on non-binary NaN only) |
| K25 | `DenseTensor.approxEq` | CHANGED T2 (equal infinities equal; needed for RC10's -inf cell) |
| K26 | oracle (`Semantics/Source/*`) | CHANGED T7 (admits tropical scatter; non-sum carrier legs needed no change: `termFiber`/`contribution` are `Semiring K`-generic) |

**(iii) Rejection placement: entry x rule** (grep-verified at `proto-s3b-p8`: `checkTropicalOutput` has exactly the two call sites; `validateScheduled` is called by `evalScheduled` and `prepareEvalPlan` Step 0).

| Id | Entry | `tropicalNonlin` | `scanStateAlgebraMismatch` | `sortCastUnsupported` | Pinned by |
|---|---|---|---|---|---|
| R1 | surface `compile` (`checkDtypes`) | rejects | accepts (S: not run) | accepts (S: not run) | T4 StructuralTest (`checkDtypes`, `TLProgram.compile`) |
| R2 | `compileToScheduled` (its chain runs `checkDtypes`, NOT `validateScheduled`) | rejects (via `checkDtypes`) | accepts (S: not run) | accepts (S: not run) | T4 surface fixture: `compileToScheduled` accepts the cast program and execution rejects `sortCastUnsupported "Y" "M"` (the only observed acceptance, p4 (d)); `tropicalNonlin` at this entry is the same as R1 (StructuralTest `checkDtypes` rows). Verified at `proto-s3b-p8`: `compileToScheduled` = `... >=> checkDtypes >=> ...`; `checkTropicalOutput` has exactly two call sites, inside `checkDtypes` and inside `checkScheduledDtypes` (called by `validateScheduled`). Correction of an earlier draft that said this entry accepts `tropicalNonlin` (review F1) |
| R3 | `evalScheduled` / `TLProgram.eval` (`validateScheduled`) | rejects | rejects | rejects | T4 parity helpers (both entries) |
| R4 | `prepareEvalPlan` Step 0 (`validateScheduled`) | rejects | rejects | rejects | same fixtures (both entries; also `checkScheduledDtypes`) |
| R5 | direct-schedule `route` | accepts (semantics-free) | accepts | accepts | S by design; `LoweringTest` AGG1/AGG2, `RouteFragmentCorpusTest` `aggregate` unchanged and green |
| R6 | surface `route` = `TLProgram.compile` / `tl!{...}` (= `compileToScheduled >>= route`) | rejects via `checkDtypes` | accepts (S: not run) | accepts (S: not run) | the SAME entry as R1 (verified: `TLProgram.compile` in `DSL/Compile.lean` runs `checkDtypes` then `schedule; route`, and `tl!` calls it); no separate fixture needed. A bare `route` on a `ScheduledProgram` is R5 |
| R7 | raw checked plan (`checkAssign`, `checkPlan`) | n/a | n/a | n/a | `castNotAdmitted`/`stateInitNotAdmitted` raw `#guard`s (T5, T6) |
| R8 | JAX/Python `Executable` | tropical refused wholesale | | | unchanged (K22) |

Every S above (the scan-agreement and cast cells of R1, R2 and R6, and every R5 cell) is by design (the cast and scan rules need the schedule-level map, which only `validateScheduled` builds; route is semantics-free) and is pinned by the stated fixture. The `tropicalNonlin` rule has NO S cell at R1, R2, R3, R4, R6: every entry that runs `checkDtypes` or `validateScheduled` rejects it; only R5 (direct-schedule `route`) accepts it, by design.

**(iv) Fixtures with twins** (p8 (c) table; max-plus fixture needs a min-plus twin from negated data).

| Id | Fixture | Twin | Disposition |
|---|---|---|---|
| W1 | ConvPoolTest max-pool, exp-pool | min twins `CV5od`, `CV5ud` | exists |
| W2 | GnnScatterTest GN4 | `GN4m` (masked row would win under a wrong cast) | ADDED T8 |
| W3 | ClassicalMLTest CM3 | none | intentional: Bellman-max, no min analogue; construct covered by the property |
| W4 | EvalExamplesTest `Peak[]` | `Trough[]` | ADDED T8 (rank-0 output is outside the property) |
| W5 | MaxReduceTest parse | `minreduce` -> `.min` | ADDED T8; `evalAssignWith (·*·) floatMax ..` rows intentionally have no twin (legacy harness with explicit algebra parameters) |
| W6 | Adapter32Test fixture 9 | max/min | exists |
| W7 | ScatterDenseTest F4, TropCollide | min rows | exists |
| W8 | ScatterDense32Test | pre-existing max row (donor `maxScatter`) + fixture 1.6c (max and min collision, bits) added T3 | covered (p8 (c) said otherwise: contradicted by `git grep`) |
| W9 | CollectTest C6/C6b/C6c, CollectEvalTest J4 | `c6min`, `c6bm`, `c6cm`, `J4m` | ADDED T8 |
| W10 | ScanGen template 5 | exists (`useMax`); template 7 (`templateTropGrid`) new, both sorts | T8 |
| W11 | DifferentialTest tropical rows, sweep | exist | exists |
| W12 | RecurrenceTest RC10 | `RC10m` | ADDED T6 |

## 4. Tasks

Lake targets are `LeanNCD`, `LeanNCD.<Module>` and `<Test module>` as in `lakefile.toml`; per task the executor builds the FULL `Tests` target (§1) and compares with §1's table. Symbols are `identifier @ file`; read windows of 40-60 lines, never a whole file
over ~20k characters. Fixture counts are `rg -c "^\+#guard"` over the patch (top-level `#guard*` lines added; fixtures written as `assertAgree`/`example` blocks are not counted: findings tables list them). Cycle labels are the manifest's.

Risk table (author-estimated for EXECUTION; the prototypes ran as single dispatches of 96-149 harness calls, execution applies patches):

| Task | Patches (bytes) | Added `#guard*` | Cycles | Estimate | Cap, split |
|---|---|---|---|---|---|
| T1 | 15.8k + 29.7k | 47 | 6 | <= 35 turns | no split; largest test migration, read hunks by fixture group |
| T2 | 17.5k + 32.2k | 65 | 6 | <= 40 turns | no split; largest tests patch (7 files) |
| T3 | 18.1k + 27.4k | 12 | 6 | <= 35 turns | no split |
| T4 | 13.3k + 16.8k | 22 | 7 | <= 30 turns | no split |
| T5 | 18.9k + 14.8k | 7 (+ BoolCastTest fixtures) | 9 | <= 35 turns | no split; most cycles |
| T6 | 17.0k + 11.0k | 7 | 7 | <= 30 turns | no split |
| T7 | 23.6k + 20.2k | 6 + 26 | 2 | <= 40 turns | no split; deletions touch 11 files; apply both patches before building |
| T8 | 7.0k + 21.6k | 3 + 16 | 5 | <= 30 turns | no split |
| T9 | none | n/a | n/a | <= 40 turns | commands; single dispatch, two commits: comments-only Lean (7 files), then docs (12 docs) |

No task needs splitting (`slice-plan` §5: patches ship). If a task's turns exceed ~60 or context ~250k, say so in the report (Rule 6); the likely cost is reading, not applying.

### T1. Shared tropical definitions, NaN-propagating max/min, (x) = (+) flip, test migration

Patches: `T1-01-production`, `T1-02-tests`. Prototype commits `a8fed5ff`, `c9c8f537`.
Files (apply --stat): production `leanncd/LeanNCD/Eval/{Contract,Error}.lean`, `Eval/Plan/{Check,Compile,Dense,Types}.lean` (+93/-48); tests `leanncd/test/Eval/ContractTest.lean`, `test/Eval/Plan/{KernelDense32Test,KernelDenseTest}.lean`,
`test/Eval/Portfolio/{GnnScatterTest,RecurrenceTest,TropicalTest}.lean` (+284/-56).
Symbols: `maxNaN`, `minNaN`, `maxNaN32`, `minNaN32` @ `Eval/Error.lean` (shared scalar oracle: reachable from `Contract.lean` directly and from `Plan/Dense.lean` through `Plan.Error`); `Combine.tropical`, `Combine.max/min/bool` @ `Eval/Contract.lean`;
`tropicalAlgebra`, `tropicalAlgebraF32`, `admittedAlgebraMax/Min/F32Max/F32Min` @ `Eval/Plan/Check.lean`; `floatOps`, `float32Ops` min/max arms @ `Eval/Plan/Dense.lean`.
Commit message: `feat(eval): S3b T1 tropical sorts are max-plus and min-plus: shared definitions, NaN-propagating max/min, migrated expectations`.
Fixtures and donors (p1 (a), (e)): ContractTest `#guard` block (Combine max/min mul/unit pins, real accept-neighbour, duality of mul/combine/unit0, NaN guards f64 and f32; donor TR3/TR7 semantics); TropicalTest TR3d, TR7d, TR5, TR5d (twins),
TR9, TR9d (single-factor accept neighbours; donors TR3, TR7); KernelDenseTest migrated rows + twins + load-bearing `storeNegA_NegB` ([-11,-101,-1001,-10001] under max-plus) + constants pins + NaN plan rows; KernelDense32Test fixtures 7, 7b, 7c, 8, 8b, 8c + pins + NaN rows;
RecurrenceTest RC5, RC7, RC10 migrated; GnnScatterTest deferral comment. Migrated values: record §2 (T1 rows).
Cycles (6, `--task T1`): `T1-M1` reference `Combine.tropical` uses `*`; `T1-M2` / `T1-M3` plan f64 / f32 tropical `factorOp` back to `.mul`; `T1-M4` `maxNaN` loses NaN propagation; `T1-M5` `minNaN32` loses it; `T1-M6` plan f64 `floatOps` min arm bypasses `minNaN`.
Known-red: GN4 + SSDT (11 sites); 8823 jobs. §3 rows: K3, K4, K17, K18, K24; W12 later.
Checklist: (a) `maxNaN` etc. are defined once and used by `Combine.bool`, `Combine.max/min`, `floatOps`, `float32Ops` (grep the five names); (b) `admittedAlgebraMax/Min/F32Max/F32Min` keep their names (ExecutableTest pins them by name); (c) `oobMaxPlan` and f32 fixture 9 are UNCHANGED here (T2 flips them);
(d) RC10 reads `[2,0,5,5]` in this task (T6 flips the cell); (e) GN4 remains red, expectation untouched; (f) TR5 is a value test, header comment of TropicalTest rewritten; (g) no pre-existing expectation outside the old -> new table changed.
Reviewer lens: is `(+, max, -inf, 0)` really what both backends compute, f64 and f32? Does any `Max.max`/`Min.min` survive on a path a tropical or bool statement reaches?

### T2. Padding, Iverson and empty folds from the algebra; `approxEq`

Patches: `T2-01-production`, `T2-02-tests`. Prototype commits `e81e8919`, `398d197b`.
Files: production `leanncd/LeanNCD/Eval/AGENTS.md`, `Eval/{Contract,Gather,Scatter,Tensor}.lean`, `Eval/Plan/{Check,Compile,Dense,Types}.lean` (+58/-46); tests `leanncd/test/Eval/{ContractTest,GatherTest,TensorTest}.lean`, `test/Eval/Plan/{KernelDense32Test,KernelDenseTest}.lean`,
`test/Eval/Portfolio/{ConvPoolTest,TropicalTest}.lean` (+356/-20).
Symbols: `gatherRead` (new `pad` parameter), `gather` (now `gather zero one ...`) @ `Eval/Gather.lean` (`gatherCast` is introduced by T5, not here); `gatherFactorWith`, `denseValueAtWith`, `ScalarKernelOps` @ `Eval/Plan/Dense.lean`; `DenseTensor.approxEq` @ `Eval/Tensor.lean`.
Commit message: `feat(eval): S3b T2 padding, Iverson and empty folds take the statement's 0_K/1_K in both backends; approxEq compares equal infinities`.
Fixtures and donors (p2 (d)): KernelDenseTest `oobMaxPlan` migrated + `oobMinPlan` twin + `oobRealPlan` + `oobBoolPlan`; `unaryPlan .exp 1` under max/min; Iverson rows maxTrue/maxFalse/minTrue/minFalse (donors `truePredPlan`/`falsePredPlan`) and `lePredPlan` `[i<=j]` max + min twin + real neighbour
(a coordinate-dependent mask is needed: under the OLD constants a false tropical Iverson contributed 0.0, the same as a true one); empty product / empty sum / zero-extent plans (`efpPlan`/`etaPlan`/`zerdPlan`, both sorts); KernelDense32Test equivalents in bits (fixture 9 + min twin + real + bool, 2.3b, 10b);
GatherTest block (bare pad max/min, unary pad, Iverson true/false, real/bool rows; the 4 existing calls migrated to `gather 0.0 1.0 env ...`); ConvPoolTest CV5o/CV5od (pad), CV5r, CV5b (neighbours), CV5u/CV5ud (unary under exp; donor CV5 maxpool);
TropicalTest TR10/TR10d (Iverson mask), TR10e/TR10ed (all-false row = -inf/+inf); ContractTest empty product/sum/zero-extent x max/min/real; TensorTest `approxEq` inf/-inf/NaN guards.
Cycles (6, `--task T2`): `T2-M1` plan bare pad -> `ops.zero`; `T2-M2` plan unary pad -> `pad`; `T2-M3` plan Iverson false -> `ops.zero`; `T2-M4` plan Iverson true -> decoded real one; `T2-M5` reference gather bare pad -> 0.0; `T2-M6` reference `Combine.tropical` (unit0, unit1) -> (0.0, 1.0).
Known-red: GN4 + SSDT (11 sites); 8823. §3 rows: K1, K2, K12, K13, K14, K25.
Checklist: (a) only `oobMaxPlan` ([0,0] -> [-1,-3]) and f32 fixture 9 (bits `[3212836864, 3225419776]`) changed value; (b) `ScalarKernelOps.one` is gone, `zero` stays; (c) the pad has two values inside `gatherFactorWith` (bare: decoded `reduceId`; unary: `ops.zero`); (d) `approxEq` compares NaN unequal; `evalEqB` needs no change;
(e) `Eval/AGENTS.md` hunk is one line (do not expand it here: T9).
Reviewer lens: every `Iverson`/pad site has the statement's constants in BOTH backends and BOTH carriers; the unary exemption is intentional (design §3).

### T3. Top-level tropical scatter accepted

Patches: `T3-01-production`, `T3-02-tests`. Prototype commits `1fdec319`, `281a1719`.
Files: production `leanncd/LeanNCD/Eval/{AGENTS.md,Error,Eval,Scatter}.lean`, `Eval/Plan/{Compile,Dense,Error}.lean` (+27/-64); tests `leanncd/test/Eval/{ScanTest,ScatterTest}.lean`, `test/Eval/Plan/{CompileTest,DifferentialTest,ScatterCompileTest,ScatterDense32Test,ScatterDenseTest}.lean` (+307/-39).
Symbols: `evalScatter` @ `Eval/Scatter.lean` (init `c.unit0`, fold `c.combine`, `boolDest` special case gone); `checkScatterAgg` @ `Eval/Eval.lean` (deleted), `scatterAggOrFail` @ `Eval/Plan/Compile.lean` (deleted); `runDenseScatterWith` @ `Eval/Plan/Dense.lean` (unchanged code, doc rewritten).
`EvalError.scatterFillNotIdentity` and `CapabilityError.scatterOptsNotAdmitted` lose their producers here and are DELETED in T7 (their constructor docs say so); the `DifferentialTest` classifier arm stays until then (exhaustive match).
Commit message: `feat(eval): S3b T3 top-level maxreduce/minreduce scatter accepted: 0_K fill, (+) collisions, guards deleted`.
Fixtures and donors (p3 (d)): ScatterTest `S3b max/min collision` (X=[[5,1],[3,7],[2,4]] -> [5,-inf,7,-inf,4,-inf]; donor S3a sum-collision), NaN rows (f64 only), multi-factor 101/107/104 + twin, `s3bRun` helper;
ScatterDenseTest fixture 7 (collision `[-inf,101,102,103]`, twin `[+inf,-101,-102,-103]`; donor fixture 6), F4 (direct `evalScatter` with a contracted `j` and an empty fibre vs raw checked plan; plus real neighbour sums, fixture 8); ScatterDense32Test fixture 1.6c (bits);
ScatterCompileTest S11 max/min (reference AND checked plan through `assertScatterParity`; donor S10), S12; DifferentialTest `scatterAgreesWith` over `maxScatterProg`/`minScatterProg`; ScanTest shape 1 max/min/joined flipped from rejection to values
(`[-1,-inf,-2,-inf,-3,-inf]`, `[1,+inf,2,+inf,3,+inf]`, `[10,5,2]` and the negated min twin); CompileTest f32 `Out[2*i]` .max/.min accepted (algebra == `admittedAlgebraF32Max/Min`, `destShape #[6]`); ScatterTest 4g min twin.
Cycles (6, `--task T3`; `T3-M4` is absent by design, its text duplicates T1-M1): `T3-M1` reference fold `combine` -> `+`; `T3-M2` reference init `unit0` -> 0.0; `T3-M3` max-plus fold -> non-NaN `Max.max` (observed to fail exactly `S3b NaN must propagate through the collision fold`);
`T3-M5` checked worker fill `reduceId` -> `ops.zero`; `T3-M6` checked worker fold -> overwrite; `T3-M7` compile: scatter step algebra ignores `agg`.
Known-red: GN4 + SSDT (19 sites, 8 new `tropicalScatterFill` rows; one shows the native leg `BindingIssue.shape [7] vs [8]`, fixed in T7); 8823. §3 rows: K6, K7, K8, K16, K21 (partial), W7, W8.
Checklist: (a) no guard remains (`rg -n "scatterAggOrFail|checkScatterAgg" leanncd/LeanNCD --glob "*.lean"` finds none); (b) a top-level PREDICATE scatter is still refused by the checked layer (`predicateScatterDest`), so predicate collision = OR exists on the reference side only (ScatterTest S3a, unchanged);
(c) scan-local scatter still overwrites (`ScanTest` scan-local max scatter `#[3,7]` unchanged, observed); (d) `ScatterDenseTest`/`ScatterDense32Test`/`ScatterCheckTest` raw plan VALUES unchanged (checked worker was already algebra-generic); `ScatterDenseTest` has a comment rewritten, `ScatterDense32Test` gains fixture 1.6c, `ScatterCheckTest` is NOT edited by any patch (its stale "max-product" wording is fixed by T9, step 8b); (e) enumPrograms sweep count unchanged (no scatter in it).
Reviewer lens: ⊕ collision on a cell AND the unwritten cell's 0_K, f64 and f32, reference and plan agree; no refusal pin left asserting a deleted guard.

### T4. `SortAlgebra`, `algebraOf`, the three rejections

Patches: `T4-01-production`, `T4-02-tests`. Prototype commits `041bfe0c`, `ccf9f745`.
Files: production `leanncd/LeanNCD/DSL/Ast.lean`, `DSL/Pipeline/{ScheduledValidation,Structural}.lean`, `Exec/Uid.lean` (+163/-1); tests `leanncd/test/DSL/Pipeline/StructuralTest.lean`, `test/Eval/Plan/CompileTest.lean` (+273).
Symbols: `SortAlgebra`, `AggOp.algebra`, `DeclEnv.declAlgebra`, `Stmt.algebra` @ `DSL/Ast.lean`; `scheduleAlgebras`, `checkSortCasts`, `CheckedScheduledProgram.algebras/algebraOf`, `validateScheduled` @ `DSL/Pipeline/ScheduledValidation.lean`; `checkTropicalOutput`, `checkScheduledDtypes`, `checkDtypes` @ `DSL/Pipeline/Structural.lean`;
`CompileError.tropicalNonlin/scanStateAlgebraMismatch/sortCastUnsupported` @ `Exec/Uid.lean`. The type is `SortAlgebra`, NOT `Algebra` (class clash fails only at the `LeanNCD` aggregate, p4 (a)1): never rename it back.
Commit message: `feat(dsl): S3b T4 SortAlgebra, algebraOf and the tropicalNonlin, scanStateAlgebraMismatch and sortCastUnsupported rejections`.
Fixtures and donors (p4 (d)): CompileTest section "S3b T4" (donors `predSchedWith`, `assertPredicateParity`, `scanPredSchedWith`, `assertScanPredicateParity`; every case runs through both entries): tropicalNonlin relu+max, relu+min, softmax+max, first-violation order, accepts (relu+sum, max+identity),
predicate relu+max stays `predicateNonlin`; scan agreement rejects/accepts (list in §3(i)) with `algebraOf "S"` pins; casts (reject 4, accept 5 executed, precedence 2); multi-writer `W` -> `multiWriterAlgebra "W"`; map pins (single-writer max/min/sum, written predicate, UNWRITTEN predicate = bool, unwritten input real with no entry, two-writer name no entry, `algebraOf` = real);
surface `tlprog!` M/Y fixture; StructuralTest (donor fixture 6): `checkDtypes` rejects relu/softmax on max/min, accepts relu+sum and max/min+identity, predicate cases, programmatic `TLProgram.compile` -> `tropicalNonlin "M"`.
Cycles (7, `--task T4`): `T4-M1` `tropicalNonlin` removed from `checkScheduledDtypes`; `T4-M2` `scanStateAlgebraMismatch` removed; `T4-M3b` tropical -> bool accepted; `T4-M3c` max-plus <-> min-plus accepted; `T4-M3d` real -> bool also rejected (breaks parked decision 1);
`T4-M5` `unaryFn` exemption removed; `T4-M7b` `Stmt.algebra` ignores the predicate declaration. (T4-M4, the neutral-writer exemption, is not manifest-stateable for both tips: at this tip its text lives in `ScheduledValidation.lean`, after T6 in `DSL/Ast.lean`; T8-M5 covers the behaviour at the final tip.)
Known-red: GN4 + SSDT (19); 8823. §3 rows: C2, C10-C12, C14-C17, C20, R1-R6, plus the scan-agreement and nonlin cells.
Checklist: (a) the cast check skips a destination with no map entry; a predicate multi-writer name DOES have an entry (every `predicate` declaration is inserted first); (b) neutral writers are decided by shape only: neutral max base + recur min is ACCEPTED (min-plus), so the "base max / recur min" reject fixture's base contracts an axis;
(c) `checkTropicalOutput` has exactly two call sites; (d) observed precedence is in §2 and pinned by three order fixtures; (e) `route`/`RouteFragments` untouched: `/usr/bin/git -C <wt> diff --stat HEAD~1 -- leanncd/LeanNCD/DSL/Pipeline/RouteFragments.lean leanncd/LeanNCD/DSL/Pipeline/Lowering.lean` prints nothing (`physicalizeOne` and `splitNonlins` are functions in those files, not files); (f) no pre-existing test flipped.
Reviewer lens: false rejections: can any valid single-sort, bool-source or scan program now be refused? Compare each reject fixture with its nearest accept neighbour.

### T5. bool -> tropical read cast, both backends

Patches: `T5-01-production`, `T5-02-tests`. Prototype commits `84c9455c`, `6b0cb23b`.
Files: production `leanncd/LeanNCD/Eval/{Contract,Gather,Scatter}.lean`, `Eval/Plan/{Check,Compile,Dense,Error,Kernel}.lean` (+79/-20); tests `leanncd/lakefile.toml`, `test/Eval/Plan/BoolCastTest.lean` (NEW, 261 lines), `test/Eval/Portfolio/GnnScatterTest.lean` (+265/-6).
Symbols: `boolReadCast` @ `Eval/Contract.lean`; `gatherRead` trailing `cast`, `gatherCast` @ `Eval/Gather.lean`; `ReadPlan.boolToTropical` @ `Eval/Plan/Kernel.lean`; `ScalarKernelOps.isTrue`, `gatherFactorWith` @ `Eval/Plan/Dense.lean`; `residualizeAssignment` (new `isBoolSlot` parameter, no default) @ `Eval/Plan/Compile.lean`;
`PlanError.castNotAdmitted` @ `Eval/Plan/Error.lean`, rule in the assign checker @ `Eval/Plan/Check.lean`. Reference "tropical statement" = `agg != .sum`; bool source = `isPredicateDest decls src`; plan: slot signature dtype `.bool`.
Commit message: `feat(eval): S3b T5 bool -> tropical read cast in both backends (ReadPlan.boolToTropical, PlanError.castNotAdmitted)`.
Fixtures and donors (p5 (d); all three-way: reference, plan f64, plan f32, via the BoolCastTest harness): a1/a2 bare read max/min (donor GN4, negative X); f1/f2 all-false row -inf/+inf; b1/b2 under `sqrt` (a cast under a unary would be `sqrt(-inf)`, a domain error); c1 bool -> real, c2/c3 real -> max/min neighbours;
g1/g2 OOB pad not cast; d1/d2 scatter compute half (donor S11), d3/d4 scan base + step (donor RC10, 1-D, all cells written); e: 7 raw-plan `#guard`s (2 accepts with cast, 2 accept neighbours, 3 `castNotAdmitted 0 0`: non-bool source, real algebra, unary read). GN4 flips green with its original expectation `[[3,4],[3,4]]`.
Not authored: a `GatherTest` guard on `gatherCast` directly; a bool-STATE-read scan fixture (§2).
Cycles (9, `--task T5`): `T5-M1` cast removed in the reference gather; `T5-M2` cast removed in plan `Dense`; `T5-M3` truth convention flipped (plan); `T5-M4b` cast applied under unary (plan compile); `T5-M5` cast applied for real statements (tropical guard dropped);
`T5-M6` cast applied to the OOB pad (reference); `T5-M7` cast field not filled: scan base caller; `T5-M9` not filled: scatter caller; `T5-M11` checker `castNotAdmitted` rejection removed. (T5-M5b is an equivalent mutant: reference casting REAL sources is bit-identical; not in the manifest.)
Known-red: SSDT (19) only; 8824 (BoolCastTest). §3 rows: C5, C7, C8, C17, C19, C24, C25, W2 (later).
Checklist: (a) `ReadPlan` literals in tests compile unedited (default `false`; 99 `oobPolicy` lines over 16 files untouched); (b) truth is `stored != 0` (differs from `== 1.0` only on non-0/1 values); (c) the cast is for BARE reads under a tropical statement only; (d) GN4's expectation unchanged and green;
(e) `lakefile.toml` gains `Eval.Plan.BoolCastTest` in the `Tests` globs.
Reviewer lens: the cast is applied on every caller (plain, scan base, scan step, scatter) and never to the pad, a unary read, or a real statement.

### T6. Scan state init at 0_K; neutral writers adopt the state's sort

Patches: `T6-01-production`, `T6-02-tests`. Prototype commits `83102c7b`, `3476f129`.
Files: production `leanncd/LeanNCD/DSL/Ast.lean`, `DSL/Pipeline/ScheduledValidation.lean`, `Eval/Plan/{Compile,RawStep,Scan}.lean`, `Eval/Scan.lean` (+106/-25); tests `leanncd/test/Eval/Plan/{BoolCastTest,ScanCompileTest}.lean`, `test/Eval/Portfolio/RecurrenceTest.lean` (+174/-5).
Symbols: `Stmt.ownAlgebra?` (moved), `scanStateSorts`, `scanStateAlgebra`, `SortAlgebra.stateAgg`, `Stmt.withAgg`, `scanStateStmts` @ `DSL/Ast.lean` (so `Eval/Scan.lean` can reach them; no import cycle); `evalScan` @ `Eval/Scan.lean` (state init `unit0` of the state's sort);
`StateInit`, `StateSlot.initValue` @ `Eval/Plan/RawStep.lean`; `ScanPlanError.stateInitNotAdmitted` (rule in `checkScanCore`), `runDenseScanWith` (takes `zero negInf posInf`; f32 `0xff800000`/`0x7f800000`) @ `Eval/Plan/Scan.lean`; `compileScan` @ `Eval/Plan/Compile.lean`.
Commit message: `feat(eval): S3b T6 scan state starts at its sort's 0_K; sort-neutral writers adopt the state's sort (StateInit)`.
Fixtures and donors (p6 (d)): BoolCastTest section "S3b T6" (donors RC10, `scanMax`, the T5 harness): a1/a2 `stateMax`/`stateMin` (RC10 shape `[2,-inf,5,5]` / `[-2,+inf,-5,-5]`), b `stateSum` keeps 0 (`[2,0,5,8]`), c1/c2 neutral base with OOB `X0[j+1]` (`axis j : ℕ = 3`:
`[-2,-2,-3,-3,-inf,-inf]` / `[2,2,3,3,+inf,+inf]`), d1/d2 neutral base bare-reading `predicate P` (`[0,0,-inf,-inf,0,0]` / `[0,0,+inf,+inf,0,0]`), f1-f3 compiled-plan probe `scanInits` (`#[.negInf]`, `#[.posInf]`, `#[.zero]`); ScanCompileTest (e) raw schedule `scratchMaxSched`
(max-plus scratch `T`, state `S` stays real) and (g) raw-plan guards for `stateInitNotAdmitted` (accept zero/negInf/posInf on f64; reject negInf/posInf on a bool state; neighbours); RecurrenceTest RC10 flipped and `RC10m` added. Scratch cannot be written in the surface (`scanProjectionUnsupported`): raw schedules only.
Cycles (7, `--task T6`): `T6-M1` reference state init back to zeros; `T6-M2` plan f64 init back to 0.0; `T6-M7` neutral writers forced real (pad and cast key lose the state's sort, both backends); `T6-M8` state sort leaks from scratch/other names; `T6-M9` compile: max-plus state gets zero init;
`T6-M11` checker `stateInitNotAdmitted` rule removed; `T6-M12` rule rejects tropical init on every state, not only bool. (T6-M5 reference-only is subsumed by M7: the cast key cannot be mutated apart from the pad: one mechanism.)
Known-red: SSDT (19); 8824. §3 rows: K9, K20, K21, C22, W12, plus the parked all-neutral cell.
Checklist: (a) NO new parameter reaches `evalScan`/`compileScan` (signatures unchanged: the annotation rewrite is the mechanism); (b) no raw-plan `StateSlot` literal in any test needed an edit (default `.zero`); (c) RC10 expectation is `[2,-inf,5,5]` (T1 had `[2,0,5,5]`);
(d) the rewrite applies to every neutral statement of the scan, scratch included (§2 parked cell); (e) `buildDeclEnv` runs a second time in `evalScan` and throws `.compile` on failure exactly as the existing storage guard does.
Reviewer lens: state sort derived from ALL statements that write it, not from the base's own annotation (RC10's base is neutral with `agg = sum`); unwritten cell = 0_K on both backends and in f32.

### T7. Oracle admits tropical scatter; delete the divergence apparatus and two constructors

Patches: `T7-01-production`, `T7-02-tests`. Prototype commits `250c3445`, `7473023d`. Build only after BOTH patches are applied.
Files: production `leanncd/LeanNCD/Eval/{Error,Scan}.lean`, `Eval/Plan/Error.lean`, `Semantics/Source/{Adapter,Admission,Differential,NumericalProfile,SortedDifferential}.lean` (+33/-157) INCLUDING deletion-forced test edits `leanncd/test/Eval/Plan/DifferentialTest.lean`,
`test/Semantics/{SourceAdmissionAffineTest,SourceSortedAuditTest}.lean`; tests `leanncd/test/Semantics/SourceSortedDifferentialTest.lean` (+109/-125).
Symbols: `admitAffineStatement` (one arm for `.assign` and `.scatter`, the sorted flag erases the agg) @ `Semantics/Source/Admission.lean`; the deleted names in §2; `scatterExtentOverridesDeclared`/`multiWriterScatter`/`usedDType` and `Differential.Classification.knownContractDifference` stay (REAL harness).
Commit message: `refactor(semantics): S3b T7 oracle admits tropical scatter; the known-difference apparatus and two error constructors are deleted`.
Fixtures and donors (p7 (d)), `SourceSortedDifferentialTest` section "S3b T7 parity rows": (a) `collide max/min` (donor ScatterCompileTest S11): `[-3,-inf,7,-inf,17,-inf,27,-inf]` / `[-5,+inf,5,+inf,15,+inf,25,+inf]`; (b) `contract max/min` `[97,107,117,127]` / `[-4,6,16,26]` (max-times would be `-5,50,1500,2500`);
(c) `zeroY max/min` `[0,0,0,0]`; (d) `product max/min [-1,-2,-3,-4]` `[99,98,97,96]` / `[0,-1,-2,-3]`; each is `yCore` value plus `classOf == fourLegParity`. Strided snapshots declare `k` extent 8 (production's derived extent; the `yCore (strided ..)` rows gain a trailing `±inf`). Sites old -> new: record §2 (T7 rows).
Removed as dead (programs kept as parity rows): the `fills`, `multi`, same-first-mismatch and `unexplained` confirmer guards. `SourceSortedAuditTest` row 7 stays `writeOutOfRange` (its program writes `Y[2a]` over `a`) plus a new in-range twin over `k` refused `sortSelection (mixedSorts ..)`; row 9 flips to `selected (bareScatter .max/.min) == "maxPlus"/"minPlus"`.
Cycles (2, `--task T7`): `T7-M1` sorted tropical scatter refused again (admission refuses `nonSum`); `T7-M5` oracle empty-fibre total starts at 1_K (real 0 in a tropical carrier). Oracle/Core legs needed NO change for a non-sum carrier (no cycle).
Known-red: none; 8824, sweep 3832/3832/0, scan corpus 17/17. §3 rows: K26, plus the deleted-name greps.
Checklist: (a) `rg -n "scatterPolicy|scatterFillNotIdentity|scatterOptsNotAdmitted|tropicalMultiFactor|tropicalScatterFill|unexplainedAgree|confirmsSorted" leanncd/LeanNCD --glob "*.lean"` finds nothing; (b) the REAL harness `knownContractDifference` still exists; (c) unsorted entries still refuse `max`/`min`
(`nonSum`; existing unsorted rows); (d) historical comments naming the deleted constructors remain in tests as history only (ScanTest, DifferentialTest, CompileTest, the new T7 prose); (e) the `Eval/Plan/AGENTS.md` pitfall conflict is NOT resolved here: T9.
Reviewer lens: with the masking gone, any divergence is a real `nativeDiscrepancy`/`nativeFailure`: is any condition still masking one? Does the sorted flag still refuse a mixed-sort program?
If `git apply --check` fails on T7-01: the deleted names touch 11 files, so a base mismatch shows up here first; do not hand-merge.

### T8. Duality property, scan oracle on tropical states, twins, parked pin

Patches: `T8-01-scan-oracle`, `T8-02-duality-property`. Prototype commits `2103edb7`, `43e86c5d`. TESTS ONLY.
Files: `leanncd/test/Eval/PropertyOracle/{ScanGen,ScanOracle,ScanUnroll}.lean` (+74/-2); `leanncd/lakefile.toml`, `test/DSL/MaxReduceTest.lean`, `test/DSL/Pipeline/CollectTest.lean`, `test/Eval/{CollectEvalTest,EvalExamplesTest}.lean`, `test/Eval/Plan/DualityTest.lean` (NEW, 260 lines), `test/Eval/Portfolio/GnnScatterTest.lean` (+331/-1).
Symbols: `templateTropGrid`, `tropicalUnwrittenScanCases` @ `test/Eval/PropertyOracle/ScanGen.lean` (OUT of `enumScanCases`, whose length 17 is pinned in five places); `localStateAgg` @ `ScanUnroll.lean` (test-side: derives the state's agg from the statements' annotations and calls none of `scanStateAlgebra`, `scanStateSorts`, `stateAgg`,
`StateSlot.initValue`: no circularity); `dualEqOf`, `parkedAllNeutralScanState` @ `DualityTest.lean`.
Commit message: `test(eval): S3b T8 negation-duality property, scan oracle on tropical states, twins and the parked all-neutral pin`.
Statement of the property (p8 (b)): for each program P (every statement `agg := .max`) and P' (every statement `.min`, inputs negated), `result(P', -x) = -result(P, x)` cell for cell (IEEE `==`: `+0 = -0`, equal infinities equal, NaN fails), same keys and shapes; refusal symmetric; on the reference (f64), the plan f64 and the plan f32 (inputs declared f32).
It tropicalises `enumPrograms` because that sweep has no max aggregation (Rule 14 deviation, surfaced in p8 (a)3). It cannot express predicate programs, nonlinear programs or the Source differential; a mirror-symmetric, negation-fixed bug (a wrong constant 0.0 in both sorts) cannot be caught by it: hand fixtures catch those (T8-M3).
Test-side oracle bug found by the property work (audit §8f.4 confirmed): `ScanUnroll` built the zero leaf and the base merge with the default `agg := .sum`, so an unwritten tropical cell came out as the real 0 (legacy `[2,-inf,5,5]` vs unrolling `[2,0,5,5]`); fixed in T8-01. NO production bug was found.
Twins added: `GN4m`, `Trough[]`, `minreduce` parse, `c6min`, `c6bm`, `c6cm`, `J4m`. Parked pin: `parkedAllNeutralScanState` (`M[j,0] := maxreduce(X0[j+1])`, `M[j,l+1] := maxreduce(M[j,l])`, X0 = [3,4], L = 2: `[[4,4],[0,0]]` on reference and plan).
Cycles (5, `--task T8`): `T8-M1` PRODUCTION min-plus scan state starts at -inf in the checked plan (caught by `RC10m` AND the duality grid min case; `DUALITY VIOLATED on checked plan f64`); `T8-M3` PRODUCTION predicate read casts false to 0.0 in BOTH tropical sorts (caught ONLY by the BoolCastTest hand fixtures and GN4m);
`T8-M4` ORACLE test-side unrolling zero leaf/merge back to the real sum; `T8-M5` PRODUCTION a neutral writer votes for the state's sort (flips the parked pin); `T8-M6` PRODUCTION binary32 min-plus reduce identity is -inf (caught by the plan32 leg and Adapter32Test fixture 9 min).
Known-red: none; 8825 (DualityTest). §3 rows: C-table pins (all), W2, W4, W5, W9, W10.
Checklist: (a) ONE `#guard` in DualityTest (over `runAll`) pins the counts in §2 on all three backends; the other eleven are the `dualEqOf` self-tests, the grid pins and the parked pin; (b) `dualEqOf` guards (equal-not-negated fails; -inf/+inf and signed zero pass; NaN fails); (c) the 4 skipped scan cases are template 2 (`relu`), reported not hidden; (d) no file under `LeanNCD/` is edited by T8 (`git diff --stat HEAD~1 -- leanncd/LeanNCD` empty);
(e) the grid cases are not in `enumScanCases` (its length stays 17).
Reviewer lens: non-vacuity (`distinguished` pinned: a sum-only program is its own negation dual), tester tested, no circularity with production state init.

### T9. Documentation sweep and a comments-only Lean commit (no patch; commands)

Run after T8 and the T8 full `Tests` green. TWO commits, in this order. **(A)** a COMMENTS-ONLY Lean commit (step L): the ONE T9 commit that touches `.lean` files; it must not change code. **(B)** the docs commit (steps 0-12, markdown only).
Build: the §5 full `Tests` build runs on commit (A) and verifies it (the full target builds the library and every test module; the five touched test modules are in the `Tests` globs, checked in `lakefile.toml`); one build serves both T9 and §5, expected 8825 jobs (a comment edit cannot move the count).
Markdown edits (B) do not touch the build and may proceed while it runs, but no other build or mutation run may (§1 serialization). Each hit is updated, or recorded unchanged with the reason. Records keep their dated counts.
No `File.lean:NNN` citations in anything T9 writes (identifiers only). Batch the edits per file (each Edit echoes the AGENTS hook text).

**Step L: Lean docstrings and test headers that still state the old algebra (review F7; found by `git grep` at `proto-s3b-p8`, EXACT old text and new text; comments only).** Edit each, nothing else in the file:

| File (under `leanncd/`) | Old text | New text |
|---|---|---|
| `LeanNCD/Eval/Contract.lean` (docstring of `evalAssignDtypedSeeded`) | ``    `agg = .max` ⇒ tropical `(×, max, −∞)`;`` | ``    `agg = .max` ⇒ max-plus `(+, max, −∞)`; `agg = .min` ⇒ min-plus `(+, min, +∞)`;`` |
| `LeanNCD/DSL/Target.lean` (`BrOp.maxreduce`) | `-- tropical max contraction (×, max, −∞)` | `-- max-plus contraction (+, max, −∞)` |
| `LeanNCD/DSL/Target.lean` (`BrOp.minreduce`) | `-- tropical min contraction (×, min, +∞)` | `-- min-plus contraction (+, min, +∞)` |
| `test/Eval/Plan/Scatter32OracleTest.lean` (module doc, item 1) | ``   Step D's scatter branch, or `scatterAggOrFail`;`` (`scatterAggOrFail` was deleted in T3) | ``   Step D's scatter branch;`` |
| same (module doc, last "cannot catch" item) | ``and any tropical destination (source syntax admits only`` + newline + ``sum-product scatter, whose unwritten cells are `0`).`` | ``and any tropical destination (a top-level max/min scatter is accepted since S3b T3, unwritten cells `-inf`/`+inf`: `ScatterCompileTest` S11, `ScatterDense32Test` fixture 1.6c; every case here is real sum-product, whose unwritten cells are `0`).`` (two lines) |
| `test/Eval/Plan/ScatterCheckTest.lean` | `/- Acceptance 4: tropical max-product, whose` | `/- Acceptance 4: tropical max-plus, whose` |
| `test/Eval/Plan/ScatterDenseTest.lean` | ``1's placement under tropical max-product, whose `reduceId` is `-∞`.`` | ``1's placement under tropical max-plus, whose `reduceId` is `-∞`.`` |
| `test/Eval/Plan/ScatterDense32Test.lean` (heading of Fixture 1.5) | the words `max-product's` (before `-∞`) | the words `max-plus's` |
| `test/Eval/Plan/ExecutableTest.lean` | `-- Tropical binary32 max-product over the same all-f32 table:` | `-- Tropical binary32 max-plus over the same all-f32 table:` |

(The first four rows of this table were found by the plan review; ScatterDenseTest, ScatterDense32Test, ExecutableTest and the `minreduce` line were found by a wider grep while fixing it. The values pinned by those tests do not change.)
Find any others with `rg -n "max-times|min-times|max-product|min-product|\(×, ?max|\(×, ?min|scatterAggOrFail|checkScatterAgg|scatterFillNotIdentity|scatterOptsNotAdmitted|tropicalMultiFactor|tropicalScatterFill|confirmsSorted|unexplainedAgree|admits only" leanncd/LeanNCD leanncd/test --glob "*.lean"` (search from `leanncd`; if `rg` refuses a path with `test/Eval`, use `--glob "**/Eval/**"`, §1 lesson (d)). After the edits every remaining hit is classified: a present-tense claim is rewritten;
a dated history comment is kept. KEEP list at `proto-s3b-p8` (checked): the "before S3b-i, max-times" comments in `KernelDenseTest`, `KernelDense32Test`, `RecurrenceTest`, `TropicalTest`, the "max-times would give" prose in `SourceSortedDifferentialTest`, the comments naming the deleted constructors in `ScanTest`, `CompileTest`, `DifferentialTest`, and the still-true "slice 1 admits only `.sum`" multi-writer comments (`Collect.lean`, `CollectEvalTest`); `Eval/Scan.lean`'s "a collision OVERWRITES" is scan-local and unchanged.
Verification, before committing (A): `/usr/bin/git -C <wt> diff --stat -- leanncd` lists exactly the seven files above and nothing else; `/usr/bin/git -C <wt> diff -U0 -- leanncd` shows only comment lines (every `+`/`-` line is a `--` line, a line inside a `/-- ... -/` or `/-! ... -/` block, or a constructor trailing comment: read all of them, there are about eight hunks); no `def`, `theorem`, `#guard` or expression line appears in it.
After the full build: green, 8825 jobs, the same red list as T8 (none). Commit: `docs(eval): S3b T9 comments-only: tropical docstrings and test headers state max-plus/min-plus (no code change)`.

**Steps 0-13 (docs commit (B)).**
0. Locate: `rg -n "tropicalMultiFactor|tropicalScatterFill|Production multiplies|scatterPolicy|scatterFillNotIdentity|scatterOptsNotAdmitted|scatterAggOrFail|checkScatterAgg|confirmsSorted|unexplainedAgree|max-times|max-product|min-product|multi-factor|unit1 = 1\.0|min, max, 0\.0, 1\.0" leanncd papers --glob "*.md"`
   (p7 (g) listed 28 files; LIVE ones are the ones below, everything else is a dated record: leave it, add one pointer from the decision note).
1. `leanncd/LeanNCD/Semantics/AGENTS.md` (Source section, tropical carriers; not hook-injected): tropical programs now reach `fourLegParity` (production is max-plus/min-plus); delete the sentences on `tropicalMultiFactor`, `tropicalScatterFill`, `scatterPolicy`, `confirmsSorted`, `unexplainedAgree`, "Production multiplies where tropical `⊗` adds", "first listed condition that confirms wins"
   and "`knownContractDifference` is produced only by these" (the REAL harness keeps `Differential.Classification.knownContractDifference` with `multiWriterScatter`/`scatterExtentOverridesDeclared`/`usedDType`); add: oracle admits tropical `.scatter` (sorted flag erases the agg), strided snapshots declare extent 8, the duality property and BoolCastTest as production-only coverage.
2. `leanncd/LeanNCD/Eval/AGENTS.md` (Patterns/Pitfalls are hook-injected, 1406 characters measured at base): (a) the Patterns bullet "`Combine`'s factor-product fold starts from `unit1`": old "All four current values have `unit1 = 1.0`, but not all use ordinary multiplication — `Combine.bool` is `⟨min, max, 0.0, 1.0⟩`" is STALE; new: `unit1` is `1.0` for real and bool and `0.0` for the two tropical `Combine`s (⊗ is `+`), and `Combine.bool` is `⟨minNaN, maxNaN, 0.0, 1.0⟩`;
   (b) the `evalAssignDtypedSeeded`/`Combine` row: tropical = max-plus `(+, max, −∞, 0)` / min-plus `(+, min, +∞, 0)`, NaN-propagating, plus `boolReadCast`; (c) one clause: scatter `Combine` by `rhs.agg` with 0_K fill, scan state init at the state's 0_K, the bool -> tropical cast; (d) a pointer "sorts (`SortAlgebra`, `algebraOf`): `DSL/AGENTS.md`", NOT a second description. T2 and T3 already edited the out-of-range-read pitfall (now `.ok pad`) and the `checkScatterAgg` sentence in this file: re-read them, do not duplicate.
3. `leanncd/LeanNCD/DSL/AGENTS.md` (review F5; the node that covers `Ast.lean`, `Pipeline/Structural.lean`, `Pipeline/ScheduledValidation.lean`; 21128 characters; only its Pitfalls section, 1790 characters, is hook-injected, so put these in the file-map rows and Contracts, not Pitfalls):
   (a) the `Ast.lean` row (AST types ...) gains `SortAlgebra`, `AggOp.algebra`, `Stmt.algebra`/`isSortNeutral`/`ownAlgebra?`, `scanStateAlgebra`/`scanStateStmts` (sort-neutral writers adopt the state's sort);
   (b) the `Structural.lean` row ("predicate-output checks") gains `checkTropicalOutput` (`tropicalNonlin`, called from `checkDtypes` AND `checkScheduledDtypes`);
   (c) the `ScheduledValidation.lean` row ("Whole-schedule validation ...") gains `scheduleAlgebras`, `checkSortCasts`, `CheckedScheduledProgram.algebras`/`algebraOf` (`scanStateAlgebraMismatch`, `sortCastUnsupported`);
   (d) the Contracts bullet "`prepareEvalPlan` and `evalScheduled` are the two public preparation/execution boundaries. Both require `validateScheduled`" gains the observed precedence (§2) and: `compile`, `compileToScheduled` and the surface `route` run `checkDtypes` (so they REJECT `tropicalNonlin`) but not the two schedule-level rules, which only `validateScheduled` enforces; a direct-`ScheduledProgram` `route` runs none of the three.
4. `leanncd/LeanNCD/Eval/Plan/AGENTS.md` (Pitfalls hook-injected, 1942 characters at base; re-measure after, step 11): the "Why was a source scatter rejected?" row: old "a `max`/`min` agg (`scatterAggOrFail`, reusing `scatterOptsNotAdmitted "{nm}: fill"`), " is deleted (max/min is no longer rejected); the `ScalarDType.bool` item gains `ReadPlan.boolToTropical`/`castNotAdmitted`; add `StateSlot.initValue`/`stateInitNotAdmitted`;
   the padded-0 tropical wording (a value-grep for "padded"/"pad" in this file found none at base: record "none" if it still finds none); the pitfall "Don't delete producer-less constructors (`dtypeMismatch`, `unaryNotAdmittedForStorage`, …) — they are retained on purpose" is SCOPED to those named constructors: add "(exception: `scatterFillNotIdentity` and `scatterOptsNotAdmitted` were deleted with their last consumer in S3b T7, as their docs promised)".
5. `leanncd/AGENTS.md` (Patterns + Global Pitfalls are hook-injected: 439 + 2545 = 2984 characters at base, measured by splitting at the `^#{2,3} ` headings; the review measured 2953 by a slightly different slice; limit about 3000, so about 20-50 characters of headroom): put NOTHING in those two sections without an equal trim. It has no slice-status line today (a search for `S2b`, `S3a`, `B6` finds none): do not add one; the S3b pointer to the record goes in the non-injected `### Subsystems` list.
   Edits: the "Small subsystems" entry `Exec/` (`Uid.lean` — `CompileError` variants) gains "incl. the S3b sort rejections `tropicalNonlin`/`scanStateAlgebraMismatch`/`sortCastUnsupported`, raised from `DSL/`"; the JAX-rejects-tropical sentence is unchanged (the `Executable` gate is unchanged: `a.algebra == realAlgebra`), record "checked, no change".
   `leanncd/docs/test_portfolio.md` (section "Tropical / max-times", and the hits found by step 0): max-plus/min-plus values and the new test modules.
   NO change, reason recorded: `Algebra/`, `Base/`, `Acset/`, `Bridge/`, `Semantics/Plan/` AGENTS.md (no file they cover is in `git diff --stat main proto-s3b-p8 -- leanncd`).
6. `papers/max_min_aggregation.md`, `papers/backend_missing_functionality.md`: replace the (max, x) description with the semiring, mark the multi-factor, scatter-fill and padded-0 gaps CLOSED with the S3b record link; list S3b-ii (multi-writer) and the parked items as still open.
7. Decision note `papers/semantics/additive_production_decision_note.md`: A10 corrections (MaxReduceTest does NOT change; the plan-level fixtures `KernelDenseTest`, `KernelDense32Test` and the refusal pins that DID flip, per §2/record §2); the S3 row and any S3b rows: "S3b LANDED" with the merge hash AFTER the merge; add a pointer to the plan/record.
8. Spec/path docs: `papers/semantics/lean_executable_semantics_path_part_4.md` (tropical/S2b paragraph: production now computes the semirings; casts; rejections; link record) and `_part_5.md` (remaining-work lists: S3b production sorts, casts, constants now landed; S3b-ii, B5, F3 remain); `lean_executable_semantics_path.md` is an index (0 hits for `S3b|tropical|max-plus` verified): record "no change".
   Gap audit `papers/semantics/tensor_logic_semantic_gap_audit.md` (5 hits for `S3b|tropical|max-plus`): one sentence per G04/F01 row. Run `rg -n "S3b|tropical|max-plus" papers/semantics --glob "lean_executable_semantics_path_part_*.md" --glob "tensor_logic_semantic_gap_audit.md"` and use its hits, not these counts.
9. Stale-doc lists from the findings: p3 (f)3 (`Semantics/AGENTS.md`, `NumericalProfile.lean`, `Admission.lean`, `SortedDifferential.lean` comments: the Lean ones were edited by T7-01; verify with the step 0 grep and the step L grep), p6/p7 (g) lists; `Eval/Scan.lean` docstring naming `scatterFillNotIdentity` (T7-01 edits `Eval/Scan.lean`: verify). A Lean docstring hit that is still present-tense is added to step L's commit (A), not edited in (B).
10. Value-greps for numbers that moved: `rg -n "8823|8824|8825" leanncd papers --glob "*.md"` (a hit in a live doc is updated to the measured count; records keep theirs); `rg -n "19 sites|19-site|19 error" leanncd papers --glob "*.md"`; `rg -n "17/17|3832" leanncd papers --glob "*.md"`
    (the 17/3832 sweep counts did NOT move: confirm any doc quoting them is still right); `rg -n "11 error sites" papers --glob "*.md"`; and the stale-phrase grep of step L over `*.md` already done in step 0.
11. Ban-grep: `rg -n "[A-Za-z0-9_]+\.lean:[0-9]+" <each file T9 touched, including the seven Lean files>`; every hit must be pre-existing (compare with `git diff -U0`), none introduced. Also `rg -n "merge pending" papers leanncd` after the merge hash lands (S2b audit): no live hit may remain.
12. AGENTS hook-injection size: for each edited AGENTS.md (`Semantics`, `Eval`, `Eval/Plan`, `DSL`, `leanncd`), measure the characters in its sections whose heading matches Pitfalls/Checks/Patterns/Context (`rg -n "^#{2,3} " <file>` for the ranges, then `python3 -I -c` slicing at those headings, or Read the ranges). Base values: `Eval` 1406, `Eval/Plan` 1942, `DSL` 1790, `Semantics` 0, `leanncd` 2984; limit about 3k characters of hook-injected text per edit; trim BEFORE adding if a file would exceed it (`leanncd/AGENTS.md` has no room, step 5).
13. Discoverability: `SortAlgebra`/`algebraOf` are named in `DSL/AGENTS.md` (the node a reader opening `DSL/` sees) with a pointer from `Eval/AGENTS.md` and `Semantics/AGENTS.md`; the two new test modules and the record are named in `leanncd/docs/test_portfolio.md` and the AGENTS rows above. Commit (B): `docs(semantics): S3b T9 docs sweep`. The decision note and path-doc "landed (merge <hash>)" sentences are completed in a later docs commit on `main` after the merge (as S2b did).
Cycles: none. Checklist: twelve live docs edited or "no change, reason" recorded (five AGENTS nodes, `test_portfolio.md`, two `papers/` docs, the decision note, path parts 4 and 5, the gap audit); the seven Lean files edited as comments only, `git diff` shows comment lines only, full `Tests` green on commit (A); steps 10-11 greps clean; size check done; the pitfall conflict resolved.

## 5. Final reviews and merge (Rule 13)

**Budget (Rule 6).** Slice execution target <= ~175M cumulative input tokens (`python3 .claude/skills/slice-plan/token-report.py <session-id>`); this slice should come in far lower (15 of 16 work packages are patches; the dominant costs are the builds and the filtered cycles).
AUTHORING COST: recorded as `TBD by the controller` in the record (target <= ~50M; prototypes ran 96-149 harness calls each, ledger).

After T9's comments-only Lean commit (A) (the docs commit (B) is markdown and needs no rebuild): the controller runs full `lake-build.sh <wt>/leanncd Tests` in the background (about 25 minutes per full build in S2b), expecting **8825 jobs**, Build completed successfully, `Semantics.AxiomAudit` printing only `propext`, `Classical.choice`, `Quot.sound` (record the constant count, which moves because T7 deletes Semantics declarations).
`JaxExperiment` is outside `Tests`: run one explicit `lake-build.sh <wt>/leanncd JaxExperiment` after it (review F13: expected to still compile; `Executable.lean` is untouched and refuses tropical wholesale) and record the result.
Filtered manifest runs per task were already done after each commit (§1, 48 cycles; first run took ~2.5-3 hours for 53 cycles). Re-run only the tasks a fix dispatch touched.
Then TWO Opus whole-branch reviews in parallel (check usage headroom first), each appending to `papers/semantics/additive_s3b_review_final_<lens>.md`:
(a) semantic table fidelity: constants, casts, scatter, scan init, NaN, f32: each §2 row against both backends and f32 bit patterns; the cast table and truth convention; ⊕ on collisions and 0_K on unwritten cells; scan init and the neutral-writer rule (including the parked cells); NaN propagation on every `max/min` path; every migrated expectation in record §2 re-derived from the semantics, not from the code;
(b) false rejections and regressions: the three new rejections against their accept neighbours (can a valid program be refused? each §3(iii) entry), the multi-writer refusal pins, route/surface behaviour (route stays semantics-free), the deleted constructors and the oracle apparatus (does any remaining condition mask a native divergence?), `git diff --stat main -- leanncd/test` for weakened tests, docs and AGENTS rows vs the code.
One fix dispatch per finding group (own plan sections only). Mid-tier per-task reviews are already done (§1).

Merge: `ExitWorktree` keep, then `/usr/bin/git -C /Users/williammacready/code/python/pyncd merge --no-ff worktree-additive-s3b-tropical-flip` (local `main` only; Rule 13: gate = full `Tests` green AND the final reviews clean or adjudicated), confirm
`git diff --stat main worktree-additive-s3b-tropical-flip` is empty, remove the worktree, `git branch -d` the slice branch. Do NOT push; say `main` is ahead of `origin/main`. Then the post-merge docs commit with the merge hash (T9 step 13; `rg -n "merge pending" papers leanncd` clean).
Scratch branches `proto-s3b-p1..p8` are deleted ONLY after the merge and only with the user's OK, which the record notes (they are scratch; tips listed at the top and in the ledger; `-D` is needed because they are unmerged).

## 6. Parked (one line each; cost and owner in the §2 table)

S3b-ii tropical multi-writer collection and writer agreement (~1 slice); B5 multi-writer scatter; F3 scan-local overwrite; `real -> bool` rejection (~1 Direct); `zeroPad` rename; oracle per-tensor sorts and cast/Iverson/padding coverage; JAX/Python tropical;
all-neutral scan state decision (pinned); annotated neutral scratch, contracted-axis neutral condition, bool state read, multi-writer source cast and contracted-axis cast fixtures (each ~1 Direct fixture); grid cases in the DifferentialTest three-way leg; stale S2a/S2b manifests.

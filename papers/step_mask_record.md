# Step-aware `where` masks, Lean side: slice record

Plan: `leanncd/docs/superpowers/plans/2026-11-26-step-aware-where-masks-lean.md` (gitignored, kept in the
primary checkout). Prototype record: `papers/step_mask_files/proto_report.md`, `proto_report2.md`. Scope and
owner decisions: `papers/semantics/jax_step_mask_scope.md`. Executed 2026-11-26/27 on branch
`worktree-step-mask`, base `aafb09a7`. Controller: Claude (subagent-driven). Nothing was pushed.

## What landed

Inside a scan, a `where` mask in a recurrence body (a state step statement or a per-step intermediate)
sees the LIVE scan coordinate(s) on the source guard (`finalizeScans`, `stepScanAxes`), the reference
evaluator (`maskContext := seed` in the step loop only), the checked plan (`RawAxiswisePlan.maskContextRank`,
error `maskContextRankMismatch`), the dense workers (`runDenseAxiswiseAt`/`...At32`, binary64 and binary32) and
the unrolled differential (`maskSubst`'s `step` flag). Base-statement masks over the pinned scan axis, contracted
and unbound mask axes stay refused. The JAX renderer refuses rank > 0 with `axiswiseContextMask` (JAX support is
the next slice). The rank is set only when the mask mentions an iteration axis of its OWN scan, so every
existing JAX fixture is unchanged.

## Commits (branch order)

| Commit | What |
|---|---|
| `071fdde2` | production patch 0001 + four comment edits (8 files, +144/-65) |
| `e066c296` | test patch 0002 (6 files, +280/-50 with three comment edits; applied with `--exclude=papers/step_mask_files/expected_step_mask.py`, owner ruling, the script already existed byte-identical) |
| `aab66054` | T2b: pin A (two-axis context order) and pin B (earlier scan's axis, rank 0), script additions, manifest M6 |
| `e3556269` | docs sweep (8 markdown files) |
| `89386841` | review fix D: three sentences that said `seededAxisZero` still pins coordinate 0, AGENTS.md, two session briefs |
| `d70751b4` | review fix L1: negative pin `maskStepEarlierScanAxis` (+ accept neighbour), manifest M7 |
| `04a49117` | review fix L2: comment-only fixes in `Uid.lean`, `Compile.lean`, `Nonlin.lean` |

## Measured builds (wall seconds)

| Build | Jobs | Wall | Note |
|---|---|---|---|
| T1 `LeanNCD` library | 8615 | NOT measured | the implementer's clock jumped (machine slept); dispatch duration 5.9M ms is not a build time |
| T1 `JaxExperiment` | 8526 | under 60 (about 24 read) | start reading taken after launch |
| T2 targeted, 4 modules | 8527 | 109 | overlapped the implementer's python run |
| T2 targeted, 2 modules | 8534 | 93 | |
| T2b `NonlinCompileTest` | 8521 | 27.9 | |
| T2b M6 cycle (mutate, build, restore, rebuild) | | 113.8 | |
| fix L1 `StructuralTest` | 8494 | 71 | |
| full `Tests JaxExperiment`, cold, at `aab66054` | **8846** | **1218** (20.3 min) | controller clock, background; before the fix wave |
| manifest replay (job A), 6 entries | | about 20 min total | contended with jobs B and C; per-entry times not logged by the script (killer-module builds 16-43 s each in the log) |
| `IndexedExecutionExperiment` (job B), second worktree at `e3556269` | **8729** | at most about 2200 (37 min) | contended; standard axioms only, no `sorryAx` |
| fix L1 M7 cycle | | about 2 min (run twice, see below) | |

Library 8615, `JaxExperiment` 8526 and `Tests JaxExperiment` 8846 match the plan. Merged-tree build: see the
"Merge" section at the end (written after the merge).

## Final gates

- Full `Tests JaxExperiment` at `aab66054`: green, 8846 jobs (later commits are one test module, markdown and
  comments; the merged-tree build re-covers them).
- Drivers: `check-lean-drivers.sh` printed "all eight drivers ran clean" (Lean side only; the Python/JAX verifiers were NOT run).
- Mutation manifest replay: 6/6 PASS (M1-M6), each killed in its killer module, restored hash equal, restored
  build green, `git diff --stat` empty afterwards. M7 (added in fix L1) was run separately: PASS, killed at the
  new negative pin, restored; whole-file `--check`: 7 entries OK before and after the comment edits. The M7 entry
  was run twice (a placeholder `expect` first, because the log prints only `Expression`); the final
  `expect` substring `compileErrOf maskStepEarlierScanAxis` was confirmed by the manifest verdict, not seen in
  the console. M6's `expect` (`diffEqB stepMaskGrid stepMaskGridIn`) was likewise confirmed only by the manifest PASS.
- Byte-identical gate: `EvalPlanNonlinSmoke` output at the base (primary checkout) and at the tip
  (step-mask worktree): `cmp` g64.py (65 fixtures, 2.5 MB) and g32.py (56 fixtures, 2.3 MB) both identical.
  The nonlin Python runner (65 / 56 "fixtures within") was NOT run.
- Pin values: every Lean pin value agrees with `papers/step_mask_files/expected_step_mask.py` (plain Python,
  `math` only) except Lean-only pins named in `proto_report2.md` (b): `seededAxisZero` (`[1,3,0.25,0.75,0,0]`),
  and the block runs (`[1,0,0]` at ctx 0, `[0.2689414213699951, 0.7310585786300049, 0]` at ctx 1) were checked
  against the script's output. DifferentialTest sweep 3832/3832 accepted, scan corpus 17/17.

## New pins (T2b and fix L1)

- Pin A, `stepMaskGrid`: two scan axes of extents 3 and 4, step mask `r <= c`; plan == reference == script
  (`G[2,3,4]`); the value differs under a swapped `(c, r)` context order (M6 kills that mutant). Rank 2.
- Pin B, `stepMaskGridIn` family: a later scan's mask over the earlier scan's axis `t` as a free state axis
  reads the real coordinate and carries rank 0 (`stepMaskRanks`, helper in `NonlinCompileTest`).
- Negative pin, `maskStepEarlierScanAxis`: a step statement whose mask names an earlier scan's axis that is NOT
  one of its own output axes is refused with `.maskAxisNotOutput "Z" "t"`; accept neighbour
  `maskStepOwnAxisSameShape`. A mutant widening `stepScanAxes` (`comps.flatten`) is killed (M7).

## Review dispositions

T1 review (Opus, read-only, `papers/step_mask_files/review_t1.md`): 0 Critical, 0 Important, 4 Minor; items
(i)-(v) all VERIFIED.
- M1 (unrolled oracle still read 0; tests red at 071fdde2): expected, fixed by patch 0002.
- M2 (checker admits `maskContextRank > 0` with `mask = none`; hand-built plans only; JAX refuses loudly): CLOSED in `d6ee524f` (maskless plan with a context rank is refused).
- M3 (stale Lean comments): first PARKED (build-time rule), then fixed in `04a49117` once a Lean fix wave existed.
- M4 (reference vs plan output bases differ for a hand-built own-axis `.free` slot; pre-existing): CLOSED in `d6ee524f` (the reference now refuses a seeded `.free` slot).

Final review lens A, wrongly accepts (Opus): 0 Critical, 0 Important, 4 Minor. The coordinate question is settled:
all legs read the step coordinate 0..L-2, not the written index. m1 (no negative pin): FIXED (`d70751b4`).
m2 (gate admits rank > 0): PARKED. m3 (rank without mask): CLOSED in `d6ee524f`. m4 (per-step-intermediate and kv
programs two-way only): CLOSED in `01ea66f7` (the independent unroller declares scratch axes, so `stepMaskInter`,
`kvMaskCausal`, `kvMaskWindow` are now three-way).

Final review lens B, breaks existing (Opus): 0 Critical, 1 Important, 11 Minor. No flipped pin weakened;
rank-0 plans unchanged; strict `stateReadCausal` and the Indexed profile untouched.
- I1 (three sentences claimed `seededAxisZero` still pins coordinate 0): FIXED (`89386841`).
- M1, M7 (stale prose, un-annotated brief trap): FIXED (`89386841`). M2, M3, M4 (Lean comments): FIXED (`04a49117`).
- M6 (no negative pin): FIXED (`d70751b4`). M8 (dangling `step_mask_record.md` pointer): resolved by this file.
- M5 (gate/renderer disagreement), M9 (Python corpus not run): PARKED / stated.
- M10 (`evalStmtSliceSeededF64` drops `maskContext`): CLOSED in `01ea66f7` (the F64 wrapper forwards `maskContext`).
- M11 (`seededAxisZero` value hand-derived; `baseParity` expected decorative): CLOSED in `01ea66f7` (`baseParity`
  decorative tensor removed; `seededAxisZero` now in `expected_step_mask.py`).

## Rulings (controller)

1. Patch 0002 contains the already-present script; applied with `--exclude` (owner approved).
2. No separate task review of T2 (the plan assigns reviews to T1 and the final two-lens review); cost if wrong
   was a test-side defect surfacing at the final review: it did not.
3. Lean comment fixes (T1 M3, lens-B M2/M3/M4) were parked until a Lean fix wave existed, then made together with the
   test pin; verified per file with `lean-file.sh` and by `--check`, with no extra worktree rebuild (the mandatory
   merged-tree build covers them). The fix-wave production edits are comments only; the manifest replay ran on the
   tree before them.
4. Worktree B was created in the session scratchpad (the sandbox refuses `git worktree add` outside the session
   worktree) with `prepare-worktree.sh --base worktree-step-mask`.

## Harness-counted tool calls per dispatch (Rule 6: about 60 calls, 250k context)

| Dispatch | Model | Harness tool calls | Subagent tokens | Agent self-report |
|---|---|---|---|---|
| T1 implement | Sonnet | 31 | 76k | about 30 |
| T1 review | Opus | 24 | 142k | about 20 |
| T2 implement | Sonnet | 31 | 74k | about 26 |
| T2b | Opus | 52 | 143k | about 37 |
| T3 docs sweep | Sonnet | 36 | 111k | 36 |
| Final review A | Opus | 49 | 215k | about 30 |
| Final review B | Opus | 38 | 189k | about 30 |
| Fix D | Sonnet | 16 | 75k | about 14 |
| Fix L | Sonnet | 52 | 91k | about 40 |

No dispatch exceeded about 60 calls or 250k by the harness count; the agents' own counts under-reported by up
to 15 calls (T2b, Fix L, both reviewers). Total subagent tokens about 1.1M (output of the harness `usage`, not
the cumulative-input measure of `token-report.py`, which was not run).

## Parked (one-line cost each)

| Item | Cost |
|---|---|
| JAX slice: stacked step-major include tables, lift `axiswiseContextMask`, `kv_cache` natural-spelling and sliding-window fixtures, `checkJaxScanSupport` gate check (the gate currently admits a step-aware axiswise node; the renderer refuses it loudly) | its own Full plan, about 4-6 dispatches |
| CLOSED `d6ee524f`: `checkAxiswiseCore` admits `maskContextRank > 0` with `mask = none` (hand-built only) | was 1 dispatch + production rebuild |
| CLOSED `d6ee524f`: reference/plan output-basis difference for a hand-built own-axis `.free` slot (pre-existing) | was about 1 dispatch audit |
| CLOSED `01ea66f7`: `evalStmtSliceSeededF64` (test helper) does not forward `maskContext` | was 1 line |
| CLOSED `01ea66f7`: independent unroller on the per-step-intermediate program `Pa[j.] := softmax(where j <= l)(S[j, l])` (`output axis has no inferable size`); and the kv programs are not three-way | was about 1 dispatch audit |
| `Kh[k, s]` free-axis causality proof | 2-3 dispatches |
| Python nonlin verifier on this change: run 2026-11-27 on the gate outputs (see Follow-up); JAX verifiers not run | 1 command if the Python env is linked |
| CLOSED `01ea66f7`: `seededAxisZero` value and `baseParity` expected not in `expected_step_mask.py` | was trivial |

## Survivors of the old-rule grep (`coordinate 0|reads 0|non-seeded output basis|Slice 5.3|maskOverScanAxis|seeded scan axis`)

The docs sweep agent's list was not exhaustive (the harness elided lines); lens B re-ran the grep independently
and its only findings were the I1/M1/M3/M7 items fixed above. Remaining hits are history already annotated
(`jax_scan_record.md` sections 26 and earlier, session briefs) or sentences that are still true for base and
top-level masks.

## Merge

Merged to local `main` with `--no-ff` as `34c50879` (branch tip `572fcfd6`; `git diff --stat main worktree-step-mask`
empty at the time). Merged-tree `lake-build.sh Tests JaxExperiment` in the primary checkout: **Build completed
successfully (8846 jobs)**, 1314 s (21.9 min, controller clock, background); no errors. Branch
`worktree-step-mask`, second worktree branch `worktree-step-mask-b`, prototype branch `proto-step-mask` and their
worktrees removed. Executor logs archived under `.superpowers/sdd/2026-11-26-step-aware-where-masks-lean/` in the
primary checkout (gitignored). **Nothing was pushed**: local `main` is ahead of `origin/main`.

## Follow-up 2026-11-27: parked minors

Commits `d6ee524f` (maskless-rank refusal; reference refusal of a seeded `.free` slot) and `01ea66f7` (F64 wrapper forwards `maskContext`; independent unroller declares scratch axes; `baseParity` removed; `seededAxisZero` in `expected_step_mask.py`) close the items marked CLOSED above.

- Item 2 (`maskContextRank > 0` with `mask = none`) turned out wider than described. The plan always refused first; the real defect was the REFERENCE accepting, and sometimes silently miscomputing, any statement with a `.free`/`.freeNorm` slot on a seeded axis, including the source-reachable program `S[j, 0, l] := X[j, l]; S[j., l+1, l] := ...`. Fixed by a new refusal `EvalError.scanSeededAxisAsOutput` in `checkScanStructure`.
- Behaviour note: a scan with an iteration axis of extent <= 1 that carried a `.free` slot on it used to give a base-only value on the reference and is now refused (the plan refused it already).
- The Python nonlin verifier was run on the gate outputs: 65 float64 / 56 float32 fixtures within tolerance, exit 0.
- Four hand mutants KILLED and restored: M-a maskless rank, M-b step arm of the reference refusal, M-c F64 forwarding, M-d scratch axis declarations.
- Full `Tests JaxExperiment` green, 8846 jobs in 995 s.
- Still parked: pin the source-reachable SRC program through the reference as `tlprog!` text (about 8 test lines, 1 small dispatch); `ScanUnroll.lean` header lines 38-39 are stale ("a mask zeros seeded scan axes", pre-existing).

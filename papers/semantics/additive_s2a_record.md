# S2a authoring record (affine write slots)

Companion to `additive_s2a_plan.md`. The plan holds only what execution needs; this file holds how it was authored,
what was measured, and what is not fully verified. Authored 2026-10-18 by the write-up dispatch.

## 1. Authoring cost (measured)

Command: `python3 .claude/skills/slice-plan/token-report.py 640a51a0-a008-4f14-9402-654cb92252c0`, output pasted
verbatim (taken while this write-up dispatch was still running, so its own row, "S2a plan write-up from artifacts",
is a partial count and the TOTAL grows by this dispatch's remainder):

```
## session 640a51a0-a008-4f14-9402-654cb92252c0
    28.2M ctx  peak  351k  turns  134  out  130k  (controller)
     3.6M ctx  peak  143k  turns   34  out    3k  P3 differential legs and known-difference conditions
     0.6M ctx  peak   67k  turns   13  out    0k  S2a plan write-up from artifacts
     6.2M ctx  peak  169k  turns   52  out    2k  P2a admission arms for affine writes
     2.8M ctx  peak  121k  turns   30  out    4k  P2c mutation cycles for T1 and T2 fixtures
     3.5M ctx  peak  102k  turns   44  out    4k  P0 probe declared-vs-derived scatter extent
    10.6M ctx  peak  195k  turns   77  out    4k  P1 generalise AdmittedOutput destination proofs
     4.1M ctx  peak  167k  turns   35  out    2k  P2b oracle affine destinations and parity
     3.6M ctx  peak  116k  turns   42  out    2k  B3 prepare-time defined-input guard
     7.0M ctx  peak  175k  turns   60  out    4k  P3b finish differential fixtures and conditions
    70.1M ctx  TOTAL
```

Against the ~50M authoring target (Rule 6): 70.1M total is over. Not all of it is authoring: the controller row
(28.2M, peak 351k, 134 turns) includes the brainstorming of the design note, and the B3 row (3.6M) is the separate
Direct-path change landed in the same session. Excluding B3 the figure is 66.5M; excluding the controller's
brainstorming (not separately measurable here) it would be lower, but the split is not measured, so no claim is made
beyond: the target was breached by about 16M, with the controller context peak (351k) the biggest single driver.
Rule 6's per-dispatch limit (peak <= ~250k, <= ~60 turns): every dispatch peaked under 250k; P1 (77 turns) and
P3+P3b (94 turns combined; 34 and 60 individually) exceed or sit at 60 turns, and the controller itself exceeded the
peak limit (351k).

## 2. Dispatch table

| Dispatch | Model | Harness turns (token-report) | Self-reported calls | Peak ctx | Notes |
|---|---|---|---|---|---|
| P0 probe (extent) | Sonnet 5.5 | 44 | not recorded in findings | 102k | probe only, no production edit |
| P1 core generalisation | Sonnet 5.5 | 77 | 104 (per controller brief) | 195k | self-report higher than the harness count |
| P2a admission | Sonnet 5.5 | 52 | ~60 in `p2a_findings.md`; 75 per controller brief | 169k | findings and brief disagree |
| P2b oracle + parity | Sonnet 5.5 | 35 | 74 per controller brief | 167k | harness count about half the brief |
| P3 differential legs | Sonnet 5.5 | 34 | ~57 in `p3_findings.md` (INCOMPLETE stop at the limit) | 143k | |
| P3b finish | Sonnet 5.5 | 60 | ~80 in `p3b_findings.md` (admitted budget breach of ~55) | 175k | ~15 calls polling the 25-minute `Tests` build |
| P2c mutation cycles | Sonnet 5.5 | 30 | ~33 in `p2c_findings.md` | 121k | cycles ran as scripts |
| P2d survivor fixtures | (inside the controller session, not a separate row) | n/a | n/a | n/a | commits `6d35f5cd`, `ddbd82c5` |
| Write-up (this) | Sonnet 5.5 | partial (13 at the time of the report) | about 56 harness calls counted by this dispatch | n/a | budget was ~55: slight breach, see §7 |

The model column is from the controller's brief (Sonnet 5.5 for all dispatches: the findings files do not record the
model). Self-reports differ from harness counts in both directions (P1: 104 vs 77; P2b: 74 vs 35; P3b: ~80 vs 60); the
harness count is the one used in the plan's risk table, with the self-report alongside.

## 3. Survivors found and closed

P2c ran 13 cycles on the T1/T2 fixtures: 2 SURVIVED, 4 were proof-only kills, 7 guard kills.
- `T2-M1` (range-error slot forced to 0): every out-of-range fixture failed at slot 0, so blame at `some 0` was
  indistinguishable from `some bad`. Closed by `6d35f5cd` (P2d fixture: `Y` over `[a, k]`, `|k| = 2`, write
  `[.free a, .affine (.shift a 1)]` refused `writeOutOfRange` at slot 1, accept-neighbour `|k| = 3`). Manifest
  entry `T2-M1 range-error slot forced to 0` expects `SourceAdmissionAffineTest.lean:148:0`.
- `T2-M10` (rank check removed): no fixture wrote a number of slots different from the destination rank. Closed by a
  rank-1 `Y` written with two slots, `.rank 1 2` at slot 1. Manifest entry `T2-M10 rank check removed` expects
  positions 157 and 159 of the same file.
- The patch for those fixtures is `T2-03-survivor-fixtures.patch` (the original commit also touched the P2d mutation draft;
  that part is not shipped as a patch because the manifest ships separately).
- P3b `M7` (legacy `phase == scheduledEvaluation` check removed) SURVIVED and is an EQUIVALENT mutant (`scatterCollision`
  is only raised during evaluation); the redundant check was removed from the code (`T4-06`) instead of adding a fixture.
  Not in the manifest (the manifest requires killed mutants).

## 4. Prototype deviations from the design note

1. **Separate admission entry instead of a flag.** The design recommended `admitSourceWith (allowAffine : Bool)`.
   The prototype added `admitSourceAffine` and left `admitSource`, `admitStatement`, `StatementFields`,
   `admitStatement_fields`, `admitSource_fields`, `admitRawSource` and every raw/provenance theorem byte-for-byte
   unchanged. Reason: those proofs unfold with `simp only`/`split`; a flag adds an `if` and changes them for no gain.
   Cost: `admitAffineWrite` duplicates ~15 lines of `admitStatement`'s `.assign` arm; `admitSourceAffine` duplicates
   the 4-line `admitSource`. Consequence: no `admitSourceAffine_originals`, so `IdentifiedSource` over the affine
   entry uses a runtime `Nodup` check with a misleading cause (`Provenance.admitIdentifiedSourceAffine`).
2. **`IsBare` is a witness**, not `shape = signature axes and dest = id`: the only consumer needs a `Slots` at the
   signature shape so `RawOutputSlots.coordinate` applies; the structural equation exists as `admitOutput_identity`
   with `isBare_of_identity`.
3. **Forms as data plus a `FormsSpec` Prop**, not a stored proof field: a field would break
   `{ o with tensor := t, dest := d }` retargeting in `SourceAffineDestinationTest`. `FormsSpec` is proved for each of
   the two output builders only; NOT lifted to statements/sources.
4. **Oracle independence by construction**, not by test (a `dest`-based oracle is equal by `FormsSpec`).
5. **Conditions after native legs**: the new differential conditions are decided after the native legs and only when
   `confirms` holds, stricter than `usedDType` (which is decided before any native leg is read and can still mask).
6. **Task mapping reorders the prototype's chronology**: `b6e39e58` (NativeLegs switch, prototype P2a) ships in T4, and
   `6d35f5cd` (P2d, chronologically last) ships in T2. The 17-patch chain was applied in task order on a clean branch at
   `6fad5161` and equals `proto-s2a-p3` for `leanncd/`; intermediate task states were not separately built.

## 5. What P0 and P3b observed about production (key rows)

P0 (`p0_extent_probe.md`; reference evaluator and checked plan agree in every variant; the pre-collection evaluator was
not probed; `reduce := sum` is not expressible from surface syntax):

| variant | reference | checked plan |
|---|---|---|
| `S(k)` declared `k = 6` or `7` (too small), `S[2*i] := X[i]`, `|i| = 4` | ok, `S` shape `[8]`, full values | same |
| `k = 8` / `k = 9` / `k` unpinned | ok, shape `[8]` (NOT 9) | same |
| consumer `Z[k] := S[k]`, `k = 6` / `9` | ERROR `axis size conflict ... 6 vs 8` / `9 vs 8` | prepare ERROR `shape` |
| constant slot `S[3] := W[j]` | ERROR `evalScan: scan node has no iteration axis` (unrelated; inconclusive) | prepare ERROR `capability` |

P3b (`p3_observed.md`, 17 rows; headline in `p3b_findings.md`): (a)(b)(c) four-leg parity; (d)(d') legacy sums like the
oracle but the checked plan refuses multi-axis and constant affine slots by capability; (e)(f) production collides
(legacy `evalScatter` collision, checked runtime `scatterCollision` or capability refusal); (g) refuses at COMPILE with
`scanAxisNotIter "a"`, not a `multiWriterScatter`; (h6) oracle `writeOutOfRange`; (h9) both native legs value with shape
issues 9 vs 8; (i) constant slot under assign fails at compile with `overlappingScatter` whatever the RHS (P0's scan
error did not reproduce; cause undetermined).

## 6. Authoring-checklist items NOT fully satisfied (`slice-plan` SKILL checklist)

- **No Lean blocks exist in the plan.** All code ships as mechanically generated patches; the "every Lean block compiled
  via `check-snippet.sh`" and "reformatted blocks re-verified" items are vacuous, and the substitute is the patch replay
  (17/17 applied, empty diff against `proto-s2a-p3` for `leanncd/`) plus the prototype's full `Tests` (8818 jobs green)
  measured by the controller at the prototype tip. The write-up dispatch did NOT build anything.
- **Fixture values:** observed from real runs by the prototype authors (hand values in `p2b_findings.md` §3 were
  computed AND observed). This dispatch re-observed nothing.
- **T1 `#guard`s were only measured through proof-kills.** P1's three mutation cycles all broke a theorem before any
  fixture ran, so the T1 `#guard`s are UNMEASURED, not shown weak (`p2c_findings.md` finding 3; proof-only kills also
  for `T2-M2` and `T2-M7`). Guard-level evidence would need a test-side mutation, which was excluded.
- **Manifest `expect` strings** are observed positions at the final test-file state; `mutation-manifest.sh --check`
  (run on the applied tree) only proves old-strings are unique (output: `manifest OK: 28 entries, 28 selected, every
  old-string unique`); the `expect` strings are NOT re-verified by this dispatch (running 28 cycles was out of scope).
  Cycles (i), (iii), (vi) of P2b and M6 of P3 printed 10 positions: truncation possible.
- **Intermediate task builds** (T1 alone, T1+T2, T1..T3) were not built by the author: only the final tree.
- **Doc sweep (T5)** is written as commands, not run; the numbers 8814/8818 come from `p2a_findings.md`/`p3b_findings.md`
  and the controller brief, not from a fresh grep of the docs.
- **§3 sibling audit** is derived from the findings files plus one `rg` listing of `admitSource`/`admitSourceAffine`
  callers and of the field accessors; the listing was truncated by the tool for two files (a tail was not read), so the
  table may miss a consumer; T2 and T4 reviewers are told to re-run `rg` per file and record additions.
- Authoring budget (Rule 6): breached (§1).

## 7. This dispatch

Harness tool calls: about 56 (budget ~55), a slight breach; two or three of them were duplicated reads/greps.
Deliverables: plan, manifest, this record, 17 patches, artifacts and design note brought over from `proto-s2a-p3`,
one commit. Nothing was built by this dispatch.

## 8. Parked list

S2b tropical carriers; S3a/S3b; affine READ slots; raw-parse theorem for affine statements; checked-plan capability
refusals of multi-axis/constant affine slots (not conditions); `usedDType` masking (pre-existing); misleading
`.duplicateTensor` in `admitIdentifiedSourceAffine`; `multiWriterScatter` vs observed `scanAxisNotIter`; constant-slot
`overlappingScatter` (cause undetermined); scatter parity fixture on the oracle leg; JAX unprobed; `admitAffineWrite`
duplicated body; no statement/source-level `FormsSpec` theorem; no `admitSourceAffine_originals`; no all-`.const` write
admission fixture; empty-contracted-fiber limitation for non-bare rows; the renderer does not print
`ComparisonRun.conditions`. Prototype scratch branches `proto-s2a-p0`, `-p1`, `-p2a`, `-p2b`, `-p3` (and `-p2c`/`-p2d`
if present) remain: ask before `git branch -D`.

## 9. Controller verification of the T1..T3 task state (2026-10-18)

After the write-up, the controller applied the first 11 patches (`T1-01` .. `T3-03`) with `git apply --index` on the slice
branch (clean at the plan commit), built the targets below, and restored the branch with `git reset --hard HEAD`
(discarding only that patch application). All `Build completed successfully`:

| Target | Jobs |
|---|---|
| `Semantics.SourceOracleAffineTest` | 8520 |
| `Semantics.SourceDifferentialTest` (existing differential tests unaffected by T1..T3) | 8564 |
| `Semantics.SourceAdmissionAffineTest` | 8508 |
| `Semantics.SourceAffineDestinationTest` | 8520 |
| `Semantics.SourceRawCorrespondenceTest` (the one forced test edit) | 8523 |
| `Semantics.AxiomAudit` | 8584 |

This closes the "reordered patches never built together" gap for T1..T3. The T4 state is the prototype tip (full `Tests`
8818 jobs, `AxiomAudit` standard axioms only). Task states T1 alone and T1+T2 alone were not built separately.

## 10. Independent plan review (2026-10-18) and disposition

Review file: `papers/semantics/additive_s2a_review_plan.md` (one Opus reviewer, two lenses; 0 Critical, 2 Major, 8 Minor,
1 Question; 53 harness tool calls, 209k subagent tokens). The controller read the evidence for both Majors (the quoted
`confirms` predicates; the `fD`/`fD'` guards asserting only `nativeFailure`) and agrees with both.

| Finding | Severity | Disposition |
|---|---|---|
| F1 `confirms` is cause-only (a same-kind failure from another statement is absorbed; the `fMask` fixture differs only in error kind) | Major | CLOSED where the native error carries a tensor identity: `T4-08` (A1, prototyped, `proto-s2a-p4` `1b90ad0e`): legacy collision and the checked preparation refusal origin-bound; checked runtime collision and multi-writer `scanAxisNotIter` stay cause-only (no identity in the error); negative fixtures `fOriginL`/`fOriginC` + 2 cycles; residuals in plan §2 |
| F4 the slice's purpose (collision-sum reference) has no assertion behind it | Major | CLOSED: `T4-07` (A2, prototyped, `820bebab`): legacy-vs-oracle exact-bit guards for `fD`/`fD'` (legacy only) with hand values and collision-free neighbours; 2 oracle cycles; plan §0 goal reworded |
| F2 independence is from `dest` only; `idxAffineForm` is shared | Minor | Plan §0 bullet extended; the `.shift` value fixtures already exist (oracle fixtures 4 and 7), only a hand-valued negative-coefficient fixture is parked; the legacy leg does not share `idxAffineForm` (`Eval.evalIdx`), the checked-plan and oracle legs do |
| F3 `retarget` builds `forms`/`dest`-disagreeing outputs | Minor | Plan §0 bullet extended (no production code builds such an output; tests do: T1's `retarget`, and T3's `SourceOracleAffineTest.tampered`, which deliberately passes tampered forms to `Oracle.run`) |
| F5 §3 cells wrong/omitted | Minor | Cells corrected, rows added |
| F6 T4 split labels, cycle owner inconsistent | Minor | Plan §4: three dispatches, cycles always the controller's |
| F7 job-count statement | Minor | Plan §2 cites the measured series (2, 1, 1, 0 increments, the zero is unexplained); the executor greps the four module names in the final log |
| F8 guards killed by no cycle; `T2-M9` expect subset | Minor | Plan T2 text and §2 row; stricter-range cycle parked |
| F9 detection/confirmation limits | Minor | §2 rows |
| F10 T5 master-plan clause | Minor | T5 step 5 rewritten (no such doc for this lineage) |
| F11 bare-slot `rejectCollisions` with a contracted axis unprobed | Question | PROBED by A1: production rejects it (legacy `evalScatter Z: collision`, checked runtime `scatterCollision`); the oracle sums, `detectConditions` skips it: classifies `nativeFailure`, pinned `fF11`; detection parked (~1 dispatch) |

Not adjudicated by anyone: the unexplained 0-job increment for the T4 module (F7). Settled by A1: the checked-plan
runtime collision and the multi-writer `scanAxisNotIter` carry no tensor identity.

## 11. Review-driven additions A2/A1 and the final verification (2026-10-18)

Prototyped on `proto-s2a-p4` (from `proto-s2a-p3`): A2 (`820bebab`, Sonnet, 45 harness tool calls, self-reported 35;
`p4a2_findings.md`) then A1 (`1b90ad0e`, Opus, 57 calls, self ~46; `p4a1_findings.md`); patches regenerated as `T4-07`
and `T4-08` (`git diff <hash>^ <hash> -- leanncd`), manifest merged to 32 entries (unique labels).
Controller verification at the combined tip:

| Check | Result |
|---|---|
| Full `lake-build.sh <wt>/leanncd Tests` on `proto-s2a-p4` (`3a78e5ed`) | Build completed successfully, 8818 jobs; no `sorryAx`/`ofReduceBool` in the log |
| `Semantics.AxiomAudit` | 6621 constants under `LeanNCD.Semantics`, standard axioms only |
| All 19 patches `git apply --index` in task order on a clean slice branch; `git diff --cached --stat proto-s2a-p4 -- leanncd` | empty |
| `mutation-manifest.sh --check` (no filters) on the applied tree, 32-entry manifest | `manifest OK: 32 entries, 32 selected, every old-string unique` |
| `mutation-manifest.sh --task T4` on the applied tree | 10/10 PASS (every cycle broke the build, restored byte-identically, restored build green, expected failure seen) |

The T1..T3 state (11 patches) was verified earlier (§9). T2/T3 cycles were not re-run by the controller after the
patches were regenerated; they were run in the prototype and their `old` strings are unchanged by T4-07/T4-08
(`--check` passes).

### Authoring cost (token-report, session 640a51a0, after A1/A2 and the review)

| Item | Cumulative input |
|---|---|
| Controller (brainstorming, B3 orchestration, all polling and verification; context peak 469k) | 55.8M |
| S2a authoring dispatches: P0 3.5, P1 10.6, P2a 6.2, P2b 4.1, P2c 2.8, P3 3.6, P3b 7.0, write-up 1.7, plan review 5.6, A2 2.1, A1 3.6 | 50.8M |
| B3 dispatch (not S2a) | 3.6M |
| Session total | 110.3M |

Against the ~50M authoring target (CLAUDE.md Rule 6): the dispatches ALONE reach it (50.8M) and with the whole controller
figure the S2a authoring is about 106.6M (B3's dispatch excluded; the controller figure also covers brainstorming and B3,
which cannot be separated). That is an OVERRUN of about 2x. The largest items: P1 (the proof generalisation, 10.6M), the
controller's own polling and long tool outputs (469k peak), and the two review-driven prototype rounds (A1 + A2 + review =
11.3M). Lessons: several dispatches ended while a long build ran and needed re-notification; every prototype dispatch
overran its harness turn budget (self-reports understate by ~30%); the controller should not poll builds with loops.

## 12. Execution (2026-10-18)

Branch `worktree-additive-s2a-affine-write-slots`. Dispatches so far, in order (guard counts are of the final tree).

| Dispatch | Commit | Model / size | Outcome |
|---|---|---|---|
| T1 implementer | `1a8b49a7` | Sonnet, ~28 turns | `AdmittedOutput` generalised (`shape`, `dest`, `slots`, `forms`), `IsBare` witness |
| T1 review | none | Opus | APPROVE |
| T1 mutation cycles | none | controller | 3/3 (all proof kills) |
| T2 implementer | `8cbdacb1` | Sonnet 5.5 | `admitSourceAffine` admits affine writes and policy-checked scatter |
| T2 review | none | Sonnet | ACCEPT WITH CHANGES |
| T2 fix | `c9c86181` | Sonnet 5.5 | +18 guards (negative/mixed-sign image, bare-slot `scatterPolicy`, `freeNorm`/scan refusal), 28 to 46; 3 hand mutations all killed |
| T2 mutation cycles | none | controller | 10/10 |
| T3 implementer | `801d4edf` | Sonnet 5.5 | oracle evaluates write forms; `Observation` derives affine occurrences |
| T3 review | none | Sonnet 5.5 | APPROVE |
| T3 mutation cycles | none | controller | 9/9 |
| T4 implementer (all 8 patches) | `78cecd9d` (T4-A), `7cf28ba2` (T4-B), `e54795e9` (T4-C) | Sonnet 5.5 | one dispatch in three stage commits instead of the plan's three dispatches (deviation; patch application only) |
| T4 A+B review | none | Sonnet | ACCEPT WITH FINDINGS: Major = extent-condition masking (verified, documented, not fixed: plan §2) |
| T4-C review | none | Opus | APPROVE, 2 Minor (plan §2) |
| T4 mutation cycles | none | controller | 10/10 (total 32/32) |
| T5 documentation sweep | the commit titled `docs(semantics): S2a documentation sweep and execution record (T5)` | Sonnet | docs only plus one docstring qualification in `Differential.lean` |

Final guard counts: `SourceAffineDestinationTest` 3, `SourceAdmissionAffineTest` 46, `SourceOracleAffineTest` 16,
`SourceDifferentialScatterTest` 38. The 32-cycle manifest is unchanged (no cycles were added by the T2 fix).

Incident: one garbled T2-fix dispatch was stopped before it acted.

| Item | Result |
|---|---|
| Final full build (`Tests`), run twice: at `42013f71` (before the final-review doc fixes) and at `da90ebfb` (after; the fixes touched two Lean docstrings/comments) | both: 8818 jobs, Build completed successfully, 0 `error`, 0 `sorryAx`/`ofReduceBool`; `Semantics.AxiomAudit`: 6621 constants under `LeanNCD.Semantics`, standard axioms only. In the first log only `SourceOracleAffineTest` and `SourceAffineDestinationTest` print a fresh `Built` line; the other two new test modules were already up to date from the per-task builds and cycle restores (the job total is the check, plan §2) |
| Unfiltered mutation manifest at `42013f71` | 32/32 cycles passed, exit 0, Lean tree clean afterwards (not re-run at `da90ebfb`: that commit changed only comments/docstrings and prose) |
| Final whole-branch reviews (two Opus lenses) | (a) proofs: approve, 0 Critical/Major, 1 behavioural Minor (parked, below), 2 wording Minors + 1 nit (fixed in `da90ebfb`); (b) regression/differential: approve, 0 Critical/Major, 3 documentation Minors (fixed in `da90ebfb`). Files `additive_s2a_review_final_A.md`, `additive_s2a_review_final_B.md` |
| Merge to local `main` | pending (controller; merge hash recorded in the controller's closing note) |

Parked by the final whole-branch review (lens a, finding 1; behavioural minor, deliberately NOT fixed in S2a; plan §2
row, owner unowned): the bare test is `forms == indices.map WriteForm.single` in `normalizeOracleContribution`,
`NumericalProfile.checkFiber` and `Differential.nonBareWrite`. An affine-admitted write that is single-axis
coefficient-1 but into a WIDER destination (e.g. `Y[a+0]`, `|a|=2`, `|Y|=9`, admitted, pinned by
`SourceAdmissionAffineTest` fixture (g)) looks bare, so the oracle invents occurrences for the unwritten cells and the
differential reports `referenceDiscrepancy` (loud, wrong blame; the extent condition is skipped too); untested. Fix:
also require destination extents equal support extents (or record the admission path on the output); touches those
three functions, one fixture appended at file end, one cycle; ~1-2 dispatches, Rule 14: parked.

Measured execution cost (Rule 6, `token-report.py` on the execution session, cumulative input tokens, target <= ~175M):
**43.6M** in total: controller 11.9M (peak context 203k, 83 turns), implementers 9.8M (T1 1.7, T2 1.5, T2 guard fix 2.2,
T3 1.8, T4 2.6; the zero-cost line in the report is the stopped garbled dispatch), reviews 14.6M (T1 Opus 1.0, T2 1.2,
T3 0.9, T4 A+B 2.1, T4-C Opus 1.4, final A 4.2, final B 3.8, of which Opus 10.4M), T5 docs 2.5M, final-review fix 4.8M.
Dispatch budget (Rule 6: peak <= ~250k and <= ~60 turns): all dispatches stayed under 250k peak context; the final-review fix
dispatch ran 54 harness turns per the report but 83 tool calls by its own count, over its stated 35-turn budget (self-matching
`pgrep` monitors that never fired and repeated build polling), still under the 60-turn Rule 6 cap. No other dispatch exceeded
its budget. Deviations from the plan: T1 and T4 each ran as one dispatch instead of the planned splits (patch application, not
prototyping); T4 committed in three stages. Unmeasured: the plan's execution-cost hope was never quantified; 43.6M is the first measurement.

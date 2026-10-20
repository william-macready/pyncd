# S2b authoring record (tropical carriers)

Live plan: `additive_s2b_plan.md`. This file holds authoring-verification records only. Execution and close-out records are
appended to it at execution time (sections 5 onward).

## 1. Authoring cost

- Prototype dispatches P1 and P2: see `additive_s2b_artifacts/p1_findings.md`, `p2_findings.md` (cost not recorded by those dispatches).
- Authoring dispatch A (patches, chain verification, plan, record): context peak and turns reported by the dispatch; measured cost:
  PLACEHOLDER (controller: `python3 .claude/skills/slice-plan/token-report.py <session-id>`).
- Authoring dispatch B (mutation manifest with observed `expect` strings), reviews, fixes: PLACEHOLDER.
- Target (Rule 6): authoring <= ~50M. Actual: PLACEHOLDER.

## 2. Patch inventory (generated mechanically from the prototype commits)

| Patch | Source | Notes |
|---|---|---|
| `T1-01-oracle-carrier-generic.patch` | `git diff 5e9bfdf0 131bc192` on `Carrier.lean`, `Oracle.lean` | P1 findings file, P1 test file and the P1 lakefile line are excluded here (test and glob are in T1-03) |
| `T1-02-extval-observe-selection.patch` | `git diff 131bc192 4dfa0fc5` on `Source/` | `ExtVal`, `observe`, `admits`, `Sorted`, `selectCarrier`, V-generic `compareTensors`, `observeTensorsAt` |
| `T1-03-carrier-oracle-fixtures.patch` | P2 form of `SourceOracleCarrierTest.lean` + lakefile glob | `4dfa0fc5` leaves this test uncompilable (the carrier record changed), so the test is regrouped into T1 |
| `T1-04-selection-audit-fixtures.patch` | new (A1-A3) | |
| `T2-01-sorted-admission-selection.patch` | `git diff 4233ba57 3a9f3044` on `Admission.lean`, `Adapter.lean` | |
| `T2-02-sorted-native-legs.patch` | same, `NativeLegs.lean` | |
| `T2-03-sorted-admission-fixtures.patch` | Q6 rows of the P2 `SourceSortedDifferentialTest.lean`, split at the admission boundary + lakefile glob | |
| `T2-04-sorted-admission-audit-fixtures.patch` | new (A4-A7), new module `SourceSortedAuditTest` | |
| `T3-01-generic-core-leg.patch` | `git diff 4dfa0fc5 4233ba57` (`Program.lean`, `Schedule.lean`) | |
| `T3-02-core-leg-fixtures.patch` | Q5 rows of the P2 test + a local `yCore` helper | |
| `T4-01-sorted-differential.patch` | `git diff 3a9f3044 300d8e19` on `SortedDifferential.lean` | |
| `T4-02-sorted-differential-fixtures.patch` | final P2 test relative to the T3 state | |
| `T4-03-source-aggregator-import.patch` | new, one line in `LeanNCD/Semantics/Source.lean` | |
| `T4-04-tropical-bits-pin.patch` | new (`±inf` bits vs `Float.toBits`) | |

## 2b. Chain verification (authoring dispatch A, 2026-10-19)

Scratch branches (all kept; ask before `-D`): `proto-s2b-p4` (T1..T4 states built per task, one scratch commit each; tree equals
`proto-s2b-p2`), `proto-s2b-p4b` (the ten prototype-derived patches applied with `git apply --index` in task order onto
`e937e895`), `proto-s2b-p5` (p4 plus the four new patches, built), `proto-s2b-p5b` (all 14 patches in nominal order).

| Check | Result |
|---|---|
| `git diff --stat proto-s2b-p2 proto-s2b-p4 -- leanncd` | EMPTY |
| `git diff --stat proto-s2b-p2 proto-s2b-p4b -- leanncd` (ten patches, applied from the base) | EMPTY |
| `git diff --stat proto-s2b-p5 proto-s2b-p5b -- leanncd` (14 patches in nominal order vs the built tree) | EMPTY |
| `git diff --stat proto-s2b-p2 proto-s2b-p5b -- leanncd` | 5 files, +89, 0 deletions: `Source.lean` +1, `lakefile.toml` +1, `SourceOracleCarrierTest` +8, `SourceSortedAuditTest` new (74), `SourceSortedDifferentialTest` +5 (the four new patches only) |
| T1 build `LeanNCD Semantics.SourceOracleCarrierTest` | green, 8616 jobs |
| T2 build `Source.Admission Source.Adapter Source.NativeLegs Semantics.SourceSortedDifferentialTest Semantics.SourceAdmissionAffineTest Semantics.SourceAdmissionAcceptanceTest` | green, 8557 jobs |
| T3 build `Source.Program Source.Schedule Source.Observation Semantics.SourceSortedDifferentialTest LeanNCD` | first attempt FAILED (my T3-02 hand-off test lacked `open Debug`; `Unknown identifier observeTensorsAt` plus abort cascade); fixed in the patch, rebuilt green, 8614 jobs |
| Full `LeanNCD Tests` on p4 (T4 state) | green, 8823 jobs; `Tests` alone 8822; AxiomAudit 6826 constants, standard axioms only |
| Audit patches T1-04, T2-04, T4-03, T4-04: `LeanNCD` + the three touched test modules on p5 | green first time, 8619 jobs (every audit `#guard` held without edits) |
| Full `Tests` on p5 (14 patches) | green, 8823 jobs; AxiomAudit 6997 constants |

Not run by the author: the mutation manifest (dispatch B), any mutation of the audit fixtures, a `check-snippet.sh` pass (the
audit blocks were compiled as real test modules, which is stronger), the Core-leg-without-admission apply order.

## 2c. Fixture values value-grepped

Every number and rendering quoted in plan §2 (the six Core cells, four 64-bit patterns, `1048577`, the two `legacy evalPlain`
message fragments, the `mixedSorts` rendering, the oracle-level rows) was found with `rg -c -F` in
`SourceSortedDifferentialTest.lean` or `SourceOracleCarrierTest.lean` on the final tree (all 20 greps returned one hit).

## 3. Deviations from the prototype artifacts

1. Task order: admission is T2 and the Core leg T3 (the prototype findings label them the other way round), so each task owns
   fixtures it can fail on. The two groups touch disjoint files; the admission patches were `git apply --check`ed against the T1
   state without the Core-leg patch (the converse was not checked; the shipped order was built and replayed).
2. The prototype commit boundaries do not build per task: `4dfa0fc5` changes the `Carrier` record without updating
   `SourceOracleCarrierTest`; `300d8e19` adds the differential test whose Q6 rows need only admission and whose Q5 rows need
   the Core leg. The test files were regrouped by task (T1-03, T2-03, T3-02, T4-02), final text identical to the prototype's.
3. Additions that are NOT in the prototype (each compiled in the authoring chain): audit fixtures A1-A7, the `±inf` bits pin,
   the `Source.lean` aggregator import.
4. NOT prototyped: T4B (structural conditions `tropicalMultiFactor`, `tropicalScatterFill` and their confirmers). The P2
   observations (§2 of the plan) define the target outcomes; the checked leg's preparation cause was not captured.

## 4. Mutation manifest

`papers/additive_s2b_mutations_post.json` (authoring dispatch B, 2026-10-20): 9 cycles, 9/9 pass in the real run (all
mutate, build-fail with the observed `expect` file:line strings, restore byte-identical, restored build green). Method: scratch
branch `proto-s2b-m` (all 14 patches applied, one build of `LeanNCD Tests`, exit 0), then one manifest run without
`expect` to observe failure positions, `expect` copied from that output, then the full run again. Per task: T1 2 (`pickName`
rows, lines 123 and 126 of `SourceOracleCarrierTest`), T2 3 (`SourceSortedDifferentialTest` admission rows 71-75 for the
rewrite and `sortKeys` cycles; `SourceSortedAuditTest` 56/62/63 and row 80 for the scatter guard), T3 2 (Core rows 85-105; the
two cycles kill the same rows), T4A 2 (envelope-trip row 111; bits pin 121-122). Observations: `T2-M1` and `T2-M3` are killed
by the same rows (they differ only in where the sort is lost); `T3-M1`/`T3-M2` likewise. The `±inf`-bits cycle `T4-M2` is
killed only by the T4-04 pin, as the plan says. Dropped per the plan: the registry cycle (not fixture-killable) and any
`MaxPlus` instance/`observe` cycle (pinned by `#guard`/`#guard_msgs`). DEFERRED: T4B has no cycles (`tropicalMultiFactor`,
`tropicalScatterFill` confirmers are not prototyped; `T4-M3..M5` are authored by the T4B dispatch after the observed causes).

## 5. Execution record (2026-10-20; T1 to T4A and the T5 docs sweep; T4B, final reviews and merge still open)

Executed inline by the controller (patch application, not prototyping); per-task Sonnet reviews read the commit through `git show`.
Ledger with every step: `additive_s2b_ledger.md`. Reviews: `additive_s2b_review_T1.md` .. `_T4A.md`.

| Task | Commit | Build (jobs) | Cycles | Review |
|---|---|---|---|---|
| T1 | `3bda8f69` | 8616, green | 2/2 PASS | accepted with changes, 0 Critical/Major |
| T2 | `8b11ff79` | 8558, green | killed by the intended rows; manifest verdict as written FAIL (see 5.1) | approve |
| T3 | `a56bc89a` | 8614, green | killed by all six Core rows; manifest verdict as written FAIL (see 5.1) | approve |
| T4A | `79524517` + label cleanup `8e70b349` | full `LeanNCD Tests` 8824, green; AxiomAudit 6997 constants, standard axioms only | 2/2 PASS | approve |

Deviation: T4A was built once on the post-cleanup state (the cleanup is docstring text only) instead of twice; the patch-only
commit `79524517` was therefore not built on its own.

### 5.1 Plan defects found during execution (not code defects)

1. **Per-task manifest `expect` strings are final-tree line numbers.** `SourceSortedDifferentialTest.lean` grows across T2, T3 and
   T4, so `--task T2` and `--task T3` run on a shorter file and report FAIL although every mutation breaks the build at the
   intended rows and restores byte-identical (T2: constant offset 15; T3: rows separated by T4A content). They are authoritative
   only after T4A. RESOLVED: re-run on the T4A-state tree (2026-10-20), `--task T2` is 3/3 PASS and `--task T3` is 2/2 PASS
   (restored byte-identical, tree clean), so the per-task verdicts in the table above read PASS on the final test file. Parked improvement: key `expect` on row text.
2. **Plan §0 / T1 note: "the `MaxPlus` instance and `observe` fields are pinned by the max/min `#guard` and `#guard_msgs` rows" is
   false for `observe`.** Those rows render through `Repr`; nothing calls `.observe` or `observeTensorsAt` until the T3 Core
   rows (`T3-M2`).
3. **Plan T2 cycle `T2-M2` wording ("tropical scatter admitted") is wrong.** The `.scatter` arm never rewrites `rhs`, so without
   the guard a tropical scatter is still refused, but as `nonSum` instead of `scatterPolicy`; Q6 row 6 and audit `A5` kill it
   because they assert the cause.
4. **T3-01 deleted ten real names** (`sourceValuations_nodup/_complete`, `sourceOccurrences_nodup/_complete`,
   `sourceOccurrenceKeys`, `sourcePublicationKeys` and their `_nodup/_complete`) instead of restating them at the real registry;
   no Lean consumer exists (`git grep`), one doc citation was fixed in the T5 sweep (path part 4, schedule paragraph).
5. T2-01 adds a private helper `stmtAgg` in `Admission.lean` that the plan's symbol list does not name.

### 5.1b Parked items picked up during execution (user-requested, 2026-10-20)

- T1 review F1-F3, F5, F6: 15 closing guards appended to `SourceOracleCarrierTest` (`observe` of all three carriers, `minPlus`
  and `real` selection, the toy's `ofRat`/`observe`/algebra) and the `Carrier.lean` docstrings (commit `8041a187`); T1 cycles still 2/2.
- `sortSelection` origin locator: `selectionOffender` (`Admission.lean`) blames the first statement that makes selection fail
  (`mixedSorts`: first aggregation differing from statement 0, `mixedElementTypes`: first element type differing, `noCarrier`:
  first with the unadmitted key; none for an empty program, which keeps the empty origin). Test first (four origin guards plus an
  admitted-program guard appended at the end of `SourceSortedAuditTest`, red against the empty origin, then green); three
  mutants each killed by exactly one intended guard and registered as manifest cycles `T2-M4..M6` (manifest is now 12 cycles).

### 5.2 Parked review findings (Rule 14; none fixed except those listed in 5.1b)

T1: no `minPlus` selection row until T2 Q6; `OrAnd` rows weak as regression (nonzero inputs); `(WithBot ℚ)ᵒᵈ` instance is an
unscoped orphan (sound); `runWith` never reads `admits` (the guard is `admitSourceSorted`); `selectCarrier []` docstring versus
`pick .sum .f64` with a custom table. T2: `sortKeys` `getD .sum` fallback unreachable today; Q6 row 5 asserts `isSome = false` only.
T3: five real names and `elaborateSource` became `abbrev` (no simp/unfold/decide uses today); no Core-vs-oracle parity row until
T4A. T4A: `compareSortedSource` puts `.unavailable` before mismatch arms (never parity); `compareBindings` walks production
bindings and relies on `NativeLegs` for missing/extra outputs; no row compares a `±inf` cell against production bits.

### 5.3 T5 docs sweep (commit `d6d4691f`)

Edited: Semantics AGENTS node (S2b paragraph), path part 4 (`admitSourceSorted` sentence, "Tropical carriers (S2b)" paragraph, schedule
citation to the `...At_*` forms), path part 5 (remaining-work sentence), gap audit (G04 row, F01 paragraph). Each carries "merge
pending" for S2b; replace it with the merge hash after the merge (`rg -n "merge pending" papers leanncd`). The text says there is NO
known-difference condition for the tropical divergences: T4B must update those sentences (AGENTS, path part 4) when it lands.
Recorded unchanged: sweep items 1 (no 8818/8822/8823 in the named files), 6 (no docstring says the oracle is sum-only; the only
`nonSum` mentions are the two refusal sites), 7 (no `8818 jobs` hit outside the S2b files; other `accepted ==` hits are unrelated
historical corpus gates), 9 (no anchor into a split-out section introduced by this slice; the anchors `#proof-status-and-numbered-results` and `#notation-color-key` were checked and their headings exist in
`tensor_logic_semantics.md`; one anchor inside `plan_layer_artifacts/wb_review_fidelity.md` was not checked), path parts 1-3 and 6, path introduction file and `README.md` (no hits). Spec 4b: the
introduction paragraph about the bounded source layer and the 2026-10-10 snapshot is NOT changed (S2a/S2b extend only the executed
oracle and differential, not the proved fragment); a reviewer may still ask for the one added sentence. Decision note: its only
spec mention is a checked task line, not a section link, so no change. NOT YET DONE (post-merge by plan): design note §7 status
line and the decision note S2 row ("landed" with the merge hash). Parked stale wording ("landed on local main", S2a was pushed):
`leanncd/AGENTS.md:219`, `lean_executable_semantics_path_part_5.md:18`, `additive_production_decision_note.md` S2 row (rewritten at
merge), `oracle_extension_s2_design.md` lines 3 and 135 (rewritten at merge).

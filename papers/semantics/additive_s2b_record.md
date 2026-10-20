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

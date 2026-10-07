# Expression/readiness execution verification

## Status and scope

The [verified plan](expression_readiness_plan.md) was replayed without redesign
in the fresh `expression-readiness-exec` worktree. All controller validation
gates passed; both final whole-branch review lenses are clean.

This is the structurally admitted expression/readiness semantic presentation,
not a production evaluator replacement or a source-syntax checker. The plan's
supplied-premise boundaries and explicit exclusions remain in force.

## Preparation and guarded replay

- Execution started from published local `main`, `61e43a4`.
- The repository `new-slice` preparation script selected the primary checkout
  as cache donor: 8,101 built Mathlib oleans / 8,094 sources, with 199 project
  oleans. The controller refreshed `LeanNCD` successfully before execution.
- Preparation's generated untracked SDD ledger was retained in controller
  session artifacts, outside the source tree. Clean status, rehearsal ancestry
  (`44296ad`), and the plan's exact protected source/specification diff guard
  then passed before patch 00.
- All four ordered `git apply --check` operations passed against the actual
  execution source. Patches 00, 01, 02, and the entire 03 were applied unchanged.
- An immutable blob-hash comparison against each patch's final index confirmed
  exact replay across all 15 delivered paths at `64e3aa5`. The branch's code,
  configuration, and guidance change set exactly matched those patch paths.
- No protected-input differences, patch conflicts, passive ports, or rebases
  were encountered.
- Neither `f32-flip-slice2-proto` nor `f32-flip-slice2`, nor their worktrees,
  was modified, rebased, built in, or removed.

| Checkpoint | Commit | Controller acceptance |
| --- | --- | --- |
| Preflight | `67d3288` | Original Patterns preserved verbatim in the reference; named hook sections measured 2,882 characters. |
| T1 | `f42f3db` | Open sorts, complete function arrays, checked layout, signed ranked coordinates, rejection-excluding admission, and product binders. |
| T2 | `3ab9b2a` | Strict clauses, independent equivalences, selected-sort additive hypotheses, locality of values and undefinedness, and witness-only complete extension. |
| T3 | `64e3aa5` | Discriminating constructions, structural admission controls, native checked-API reuse, narrow existing seam, and public/default discovery. |

## Controller validation

| Required check | Observed result |
| --- | --- |
| Prepared-source `LeanNCD` refresh | Passed, 8,546 jobs. |
| T1 `LeanNCD.Semantics.Expr` | Passed, 2,944 jobs. |
| T2 `LeanNCD.Semantics` | Passed, 2,948 jobs. |
| T3 `Semantics.ExpressionTest`, `Semantics.NativeTest`, `Semantics.ContractTest` | Passed, 8,555 jobs. |
| Fixture inventory | 23 + 8 + 5 guards and 10 + 1 theorem fixtures: 36 guards + 11 theorems = 47 assertions. |
| Local semantic guidance | 2,642 characters total. |
| Manifest schema and unique anchors | Passed, 27 entries, all verification task 3. |
| Actual controller mutation suite | **27/27 passed**, each with intended failure, restored green build, expected failure text, and byte-identical restored source. |
| Post-mutation tracked-source diff | Empty. |
| Full default build | Passed, **8,686 jobs**, including all three semantic test modules and indirect old-spike coverage. |

The [controller mutation results](expression_readiness_execution_mutation_results.md)
are published separately from the task code commits. The suite comprises 11
implementation/proof mutations, 5 structural admission contrast controls, and
11 fixture/registry/metadata perturbations. These are not 27 implementation
regressions or exhaustive mutation coverage of every assertion.

Observed expression values:
`[some 9, some 7, none, some 0, none, some 13, some 14, some 6, none, some 42, some 28]`.
Readiness observations: `["notReady", "undefined", "notReady"]`.
Native rounding bit observations: binary64 `4607182418800017408`, binary32 `0`.

Printed new theorem dependencies were restricted to `propext`, `Quot.sound`,
and, where needed, `Classical.choice`; no `sorryAx` or added axioms appeared.
Existing dependency warnings, including the pre-existing categorical `sorry`
warnings, remained visible and were not fixed or hidden.

The documentation value-grep classified the spike's original 8,676-job count
and the authoring 8,686-job count as explicitly historical. Current semantic
guidance and the historical spike record qualify indirect default-test
coverage. Unrelated non-default backend/scatter-policy matches were retained.
Production evaluator siblings and the old spike implementation are unchanged.

## Final whole-branch reviews

Both reviewers inspected immutable `61e43a4..64e3aa5`, including all candidate
modules and fixtures, rather than transient controller mutation files.

1. **Semantic/proof fidelity: clean.** Covered specification mapping and
   exclusions, strictness/emptiness, independent clause proofs, exact additive
   hypotheses, values and undefinedness, whole-array/all-operand obligations,
   complete-extension witness versus runtime fallback, and discriminatory
   fixtures.
2. **Types/backend/categorical/reuse: clean.** Covered sort/shape/declaration
   admission, bounded coordinates and metadata scope, native checked API reuse
   and precision, exact noncomputable Complex, the narrow actual `StMat` seam,
   public/default discovery, unchanged siblings, and historical qualification.

There were no findings requiring fixes or adjudication. Detailed incremental
review notes and complete mutation/targeted/full-build logs are retained in
the controller's persistent session artifacts.

## Budget and integration

The repository token-report tool returned no matching transcript for this SDK
session. A measured aggregate total and exact peak-context meter are therefore
unavailable; missing telemetry is not evidence of compliance with the 175M
slice ceiling.

Reviewer-reported estimates: semantic lens 12 of approximately 60 turns with
peak context below 100k; boundary lens approximately 12 tool rounds with
context below 60k. These are estimates, not aggregate token measurements.
No observed dispatch-budget breach was reported.

Only the validated execution branch is approved for local integration into
`main`. The controller records the actual merge and own-worktree/branch cleanup
in its session ledger. No remote push is authorized or performed.

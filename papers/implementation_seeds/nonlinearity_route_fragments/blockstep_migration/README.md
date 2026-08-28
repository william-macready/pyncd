# Task 3 `BlockStep` migration seed

This directory contains the current-tree rehearsal for Task 3 of
`papers/nonlinearity_split_pair_direct_lowering.md`, run at `main` commit `d8ef77b` on 2026-08-27.
It is an executable implementation seed and report, not a production dependency. No production Lean
file or production test was changed.

## Artifact

- `BlockStepMigrationSeed.lean`
  - introduces local `BlockStep.assign`/`.pointwise`/`.axiswise` constructors and the
    `RawPlanBlock.steps` field;
  - supplies source, destination, and optional-context accessors;
  - checks steps through production `checkStepGraph`, with assignment provenance required for every
    nonlinear source after ordinary range/availability checks;
  - dispatches checked steps to `runDenseAssignAt`, `runDensePointwise`, and `runDenseAxiswise`;
  - wraps compiler-produced assignment blocks as `.assign`;
  - checks scan causality only for `.assign` steps and reports the original block-step index;
  - contains all nine donor-derived fixtures and six disabled mutation toggles.

The seed imports production code but is not imported by `LeanNCD`, `Tests`, or any production module.

## Audited migration inventory

The prior **47 occurrences on 46 code lines** remains exact. The current-tree audit classified every
line returned by the same plain `assignments` search that reports 54:

| Migration file | Genuine code lines | Genuine field occurrences | Incidental matches |
|---|---:|---:|---:|
| `LeanNCD/Eval/Plan/RawStep.lean` | 1 | 1 | 0 |
| `LeanNCD/Eval/Plan/Block.lean` | 2 | 2 | 1 |
| `LeanNCD/Eval/Plan/Scan.lean` | 2 | 2 | 0 |
| `LeanNCD/Eval/Plan/Compile.lean` | 2 | 2 | 4 |
| `test/Eval/Plan/BlockTest.lean` | 4 | 4 | 0 |
| `test/Eval/Plan/ScanTest.lean` | 25 | 26 | 3 |
| `test/Eval/Plan/ScanCompileTest.lean` | 10 | 10 | 0 |
| **Total** | **46** | **47** | **8** |

The naive result is 54 matching lines: 46 genuine code lines plus eight comments/docstrings. The
occurrence count is one greater than the genuine-line count because `ScanTest.lean` has one genuine
record-update line containing both `assignments :=` and `stepBlock.assignments`. Task 1 and Task 2
therefore did not change Task 3's audited rename inventory.

## Fixture provenance and observed outcomes

Every row below is executable in `BlockStepMigrationSeed.lean`; the stated result came from a direct
successful `lake env lean` run.

| # | Donor and single relevant change | Exact observed outcome |
|---:|---|---|
| 1 | `BlockTest.stepBlock`; add slot 2 and append ReLU from assignment destination 1 | accepted; `ctx = 0` produced `#[1.000000, 0.000000, 3.000000]` |
| 2 | `BlockTest.stepBlock`; add slot 2 and append axiswise normalize from assignment destination 1 | accepted; produced `#[0.166667, 0.333333, 0.500000]` |
| 3 | `BlockTest.forwardReadBlock`; replace its first operation with pointwise reading unproduced slot 1 | rejected with `wiring (invalidForwardRead 0 0 0 1)` |
| 4 | Restore assignment production of slot 1, append pointwise to slot 2, then retain an assignment to slot 2 | rejected with `wiring (duplicateDestination 2 1 2)` |
| 5 | `ScanTest.stepBlockLookAheadG`; replace assignment with pointwise directly sourcing captured state slot 0 | rejected by block checking with `nonlinearSourceNotLocalAssignment 0 0` |
| 6 | `ScanTest.stepBlockLookAheadG`; insert pointwise from captured slot 0 to slot 2 and make the look-ahead assignment read slot 2 | rejected by block checking with `nonlinearSourceNotLocalAssignment 0 0`; laundering never reaches scan causality |
| 7 | Fixture 1; append axiswise normalize sourcing pointwise result slot 2 | rejected with `nonlinearSourceNotLocalAssignment 2 2` |
| 8 | `ScanTest.deepHistoryScan`; retain the causal `bias = -2` assignment and append scalar ReLU from its destination | accepted by block provenance and scan causality |
| 9 | `ScanTest.stepBlockLookAheadG`; append scalar ReLU after the look-ahead assignment | block provenance accepted; scan checking rejected the assignment at original block-step index 0 with `causalityFailure 0 0 0 0` |

The compiler-wrapping guard additionally confirms every element of a compiler-style assignment block
becomes `.assign`; the rehearsal does not admit nonlinear scan source lowering.

## Mutation cycles

Each toggle was changed from `false` to `true`, the direct seed command was run and observed to fail,
then the toggle was restored to `false` and the same command was observed to pass.

| Mutation | Observed failing assertion | Defect detected |
|---|---|---|
| Remove pointwise Dense dispatch | `fixture 1 wrong result: #[]` | checked pointwise result was not stored |
| Remove axiswise Dense dispatch | `fixture 2 wrong result: #[]` | checked axiswise result was not stored |
| Route nonlinear nodes through assignment checking | fixtures 1 and 2 rejected with `wiring (nodeError 1 (destinationShapeMismatch #[] #[2, 3]))`; dependent fixture guards also failed | nonlinear nodes used `checkAssign` instead of their existing local checkers |
| Remove the shared preceding-local-assignment guard | fixture 7, fixture 5, and fixture 6 guards each “did not evaluate to `true`” because all three malformed blocks were accepted | nonlinearity-from-capture and nonlinearity-from-nonlinearity provenance became admissible |
| Revert look-ahead causality filtering | fixture 9's exact `causalityFailure 0 0 0 0` guard “did not evaluate to `true`” because the scan was accepted | positive-bias history read bypassed causality |
| Revert deep-history causality filtering | fixture 8's `.ok` guard “did not evaluate to `true`” because the causal negative-bias scan was rejected | valid deep-history reads were treated as noncausal |

The restored file passed after every cycle.

## Transplant map and order

1. **`LeanNCD/Eval/Plan/RawStep.lean`**: transplant `BlockStep` and its accessors; change
   `RawPlanBlock.assignments` to `steps`.
2. **All seven migration files**: apply the audited 47-occurrence field migration. Wrap every existing
   assignment literal/array element in `.assign`; update structural assertions by extracting the
   nested assignment.
3. **`LeanNCD/Eval/Plan/Block.lean`**: transplant `CheckedBlockStepEvidence`, the nonlinear error
   wrappers, and the provenance error. Keep `checkStepGraph` unchanged. Build its `WiringNode`s in
   block-step order and snapshot only preceding `.assign` destinations for nonlinear `sourceCheck`.
4. **`LeanNCD/Eval/Plan/Block.lean`**: replace the assignment-only execution loop with exhaustive
   checked-step dispatch to the three existing Dense workers.
5. **`LeanNCD/Eval/Plan/Compile.lean`**: map `baseAssigns` and `stepAssigns` through `.assign`; do not
   add nonlinear scan lowering in Task 3.
6. **`LeanNCD/Eval/Plan/Scan.lean`**: after block checking, causality-walk only `.assign` payloads.
   Enumerate the unfiltered `steps` array so `causalityFailure.stmtIndex` remains a block-step index.
7. **Tests**: transplant the nine fixtures. Pattern-match `Except` because checked blocks have no
   `BEq`; pattern-match `.assign` before assignment-field assertions.

## Limitations

- The artifact uses local types because the spike was forbidden from modifying tracked production
  files. Its scan adapter delegates unchanged structural geometry/capture/write validation to the
  production scan checker after replacing local nonlinear steps with shape-preserving assignment
  stand-ins. It then runs the rehearsed assignment-only causality traversal itself. Production must
  transplant the logic into the real types rather than import or retain this adapter.
- The direct seed command is the executable prototype gate. The named Lake test targets and aggregate
  targets do not import the seed; they prove the unchanged production tree remains green.
- The seed deliberately covers Task 3 only. It does not admit compiler-produced nonlinear scan
  sources, allocate nonlinear scratch/publication slots, or implement Task 4.

## Effort estimate

Retain the original estimate of **1.5-2 focused engineer-days**. The audited blast radius, import
graph, and six mutation classes are unchanged. Current outer-plan nonlinearity support provides clear
checker/worker precedent, while the only care-heavy work remains the 47-occurrence fixture migration,
nested checked-step assertions, and causality-index preservation. Task 1 and Task 2 introduced no new
Task 3 migration site.

## Verification

Run from the repository root:

```bash
cd leanncd
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/blockstep_migration/BlockStepMigrationSeed.lean
"$HOME/.elan/bin/lake" build Eval.Plan.BlockTest Eval.Plan.NonlinCheckTest Eval.Plan.ScanTest Eval.Plan.ScanCompileTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

Observed on 2026-08-27 at `d8ef77b`:

| Command | Result | Jobs |
|---|---|---:|
| Direct seed | pass; nine fixtures and compiler-wrapping guard | n/a |
| Four targeted modules | pass | 8,511 |
| `Tests` | pass | 8,657 |
| `LeanNCD` | pass, with only existing repository warnings | 8,543 |

The request supplied 8,659 as the last-known baseline for both aggregate commands. The fresh
standalone observations are therefore `Tests: -2` and `LeanNCD: -116`. This is not a prototype-added
job delta—the seed is outside both Lake target graphs and production is unchanged. The discrepancy is
recorded rather than replacing measured output with the stated baseline.

## Prohibition

Production Lean files and tests must not import this seed. Copy reviewed declarations into the
mapped production modules, remove the donor-only scan adapter, restore the production namespaces, and
then run Task 3's mutation cycles against the actual production implementation.

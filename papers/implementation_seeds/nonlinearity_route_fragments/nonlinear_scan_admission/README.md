# Task 4 nonlinear scan admission seed — stopped in Phase 2

This directory is a current-tree rehearsal for Task 4 of
`papers/nonlinearity_split_pair_direct_lowering.md` (§1.2 and §3.6). It is outside Lake's target
graph and contains the only two files created by this rehearsal.

- **Base commit:** `2e1b8e8`
- **Date:** 2026-08-27
- **Status:** **STOPPED AT THE PHASE-2 BOUNDARY. MULTIPLE REQUIRED SOURCE PROGRAMS WERE NOT
  RECOVERED.**

## Ordered phase status

| Phase | Status | Evidence |
|---|---|---|
| 1 — `retainedAxisPos` | EXECUTED | Three guards cover leading, interleaved, and trailing local-axis positions. |
| 2 — recover and reproduce source programs | STOPPED | Exact donors were inspected; only donor candidates survive, not the six spike source/input pairs. |
| 3 — independent-unroller change | **NOT EXECUTED** | No unroller was cloned and no `.freeNorm` oracle change was implemented. |
| 4 — nonlinear `compileScan` | **NOT EXECUTED** | No lowering, slot allocation, or publication logic exists here. |
| 5 — negative/write-safety fixtures | **NOT EXECUTED** | No fixtures 14–19 were built. |
| 6 — differential/corpus rebaseline | **NOT EXECUTED** | No `13/0/4` claim was made. |
| 7 — mutations/closure | **NOT EXECUTED** | No mutation hooks or completion claim exists. |

This is the mandated stop. It is not a partial Phase-3 implementation and contains no transplant
claim.

## Artifact

`NonlinearScanAdmissionSeed.lean` contains only:

1. the Phase-1 `retainedAxisPos` rehearsal;
2. a faithful local clone of private `DSL/Pipeline/ScanAffineTest.reluScan` source syntax;
3. direct references to the public donors required by §3.6;
4. legacy `evalScheduled` executions of the three public `ScheduledProgram` donors that also retain
   their exact donor inputs;
5. an explicit Phase-2 stop message.

It contains no independent scan unroller, oracle implementation, nonlinear Plan lowering,
allocation/publication helper, or mutation toggle.

## Phase 2 source-recovery findings

The governing requirement is a recovered **source construction and inputs**, executed through legacy
`evalScheduled`. Matching a retained output by inventing a program or fitting inputs is not recovery.
Under that standard, none of the six §3.6 recorded-value groups is reproduced here.

### Exact named donors

| Required donor | Exactly recovered evidence | What it does not recover |
|---|---|---|
| private `ScanAffineTest.reluScan` | Source syntax was cloned byte-for-byte: `S[j,0] := X[j]`; `S[j,l+1] := relu(S[j,l] · A[j,k])`. It compiles to a logical schedule. | The donor defines no inputs. Assigning values chosen to hit groups 1 or 3 would be fitting. |
| public `ScanCompileTest.coupledSched` / `coupledInputs` | Reused directly and executed through legacy `evalScheduled`; raw values are below. | It is a linear, two-iteration-axis structural donor, not the missing scalar nonlinear/linear coupled source for group 6. |
| public `ScanCompileTest.scratchSched` / `scratchInputs` | Reused directly and executed through legacy `evalScheduled`; raw value is below. | It has one linear scratch and produces `[1,2,6]`; it is not group 5's missing nonlinear scratch→scratch→state source. |
| public `ScanCompileTest.multiBaseSched` / `multiBaseInputs` | Reused directly and executed through legacy `evalScheduled`; raw value is below. | It is a linear multiple-base-write donor, not the missing nonlinear-base group 4 source. |
| `NonlinCompileTest.sampleMask` | Exact mask expression is checked in the seed. | It is an expression fragment, not a `TLProgram`/`ScheduledProgram`, and cannot be run through `evalScheduled` alone. |
| `NonlinDenseTest.axiswisePlan` | Exact axis position/function are checked in the seed. | It is Plan IR using `.normalize`, not a legacy source program and not group 2's missing interleaved-softmax recurrence. |
| Task-1 `RouteWeaveTest.freeNormAxiswiseProg` | Exact public source compiles and retains one logical statement. | It is a top-level normalization with no scan and no inputs; it is not the group-2 source. |

Task 1's private `f8AxiswiseScan` was also inspected. It is a normalization self-scan with no inputs,
not the recorded interleaved softmax source/input pair. It was therefore not copied.

### Six recorded groups

| # | Recorded group | Recovery result |
|---:|---|---|
| 1 | leading pointwise `[2,3,20,300,200,30000]` | ReLU source-shape donor survives; exact spike inputs/source orientation do not. **Not reproduced.** |
| 2 | interleaved axiswise history ending `[..., .991521, .008479]` | No source/input pair survives. **Not reproduced; Phase-2 stop trigger.** |
| 3 | leading persistent nonlinear `[1,0,0,2,6,18]` | ReLU source-shape donor survives without inputs. **Not reproduced.** |
| 4 | nonlinear base `[0,3,0,3]` | Only the linear `multiBaseSched` structural donor survives. **Not reproduced.** |
| 5 | scratch→scratch→state `[1,5,5,2,0,0]` | Only the one-scratch linear `scratchSched` donor survives. **Not reproduced.** |
| 6 | coupled `G=[1,0,0]`, `H=[1,1,0]` | Exact public coupled donor is a different linear, two-axis program. **Not reproduced.** |

### Retained-history audit

- Registered worktrees were searched for the exact group-2 value and “interleaved axiswise.” Matches
  were only the design record and superseded drafts of this seed.
- Reachable refs/history were searched commit-by-commit. Matches were versions of
  `papers/nonlinearity_split_pair_direct_lowering.md`, not a source fixture.
- Every Git blob, including unreachable objects, was scanned for exact float
  `9915205505990216`: 82 blobs matched, classified as 71 design-record versions and 11 superseded
  seed drafts. No original spike source blob was found.
- The retained session store had no turn containing the exact float or “interleaved axiswise.”

This establishes “not recoverable from retained evidence,” not mathematical impossibility.

## Direct seed output

Command, from `leanncd/`:

```bash
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/nonlinear_scan_admission/NonlinearScanAdmissionSeed.lean
```

Raw observed output:

```text
PHASE 1 COMPLETE: retainedAxisPos guards passed
PHASE 2 exact public donor coupledSched: G shape [3, 2, 3] = #[1.000000, 0.000000, 0.000000, 2.000000, 0.000000, 0.000000, 0.000000, 1.000000, 0.000000, 0.000000, 2.000000,
  0.000000, 0.000000, 0.000000, 1.000000, 0.000000, 0.000000, 2.000000]
PHASE 2 exact public donor coupledSched: H shape [3, 3] = #[7.000000, 0.000000, 0.000000, 0.000000, 10.000000, 0.000000, 0.000000, 0.000000, 13.000000]
PHASE 2 exact public donor scratchSched: S shape [3] = #[1.000000, 2.000000, 6.000000]
PHASE 2 exact public donor multiBaseSched: dp shape [3, 3] = #[1.000000, 2.000000, 3.000000, 7.000000, 1.000000, 2.000000, 0.000000, 7.000000, 1.000000]
PHASE 2 STOP: exact source-program/input pairs for multiple §3.6 groups were not recovered
PHASES 3–7 NOT EXECUTED
```

These are donor-candidate observations only, not substitutions for the six required records.

## Required baseline and gates

The exact required baseline command is:

```bash
lake build Eval.Plan.BlockTest Eval.Plan.NonlinCheckTest Eval.Plan.ScanTest Eval.Plan.ScanCompileTest
```

Raw observed output:

```text
Build completed successfully (8511 jobs).
```

Aggregate gates:

```bash
lake build Tests
```

```text
Build completed successfully (8657 jobs).
```

```bash
lake build LeanNCD
```

```text
Build completed successfully (8543 jobs).
```

The earlier draft's 8525/8505 commands were different exploratory module sets. They are not
replacement gates and are not used to characterize the required 8511 baseline.

## Required later tables — not executed

| §3.6 requirement | Status |
|---|---|
| Positional/execution fixtures 1–5 | **NOT EXECUTED** beyond Phase-1 position arithmetic |
| Publication/dependency fixtures 6–10 | **NOT EXECUTED** |
| Base fixtures 11–13 | **NOT EXECUTED** |
| Negative/write-safety fixtures 14–19 | **NOT EXECUTED** |
| Independent-oracle six-group table | **NOT EXECUTED** |
| 9 production + 4 oracle mutation cycles | **NOT EXECUTED** |
| Three-way legacy/Plan/oracle comparison | **NOT EXECUTED** |
| Corpus rebaseline to 13/0/4 | **NOT EXECUTED** |
| Phase-7 closure/completion | **NOT EXECUTED** |

## Limitations

- This artifact proves only the Phase-1 helper cases and the raw behavior of three unchanged public
  donor schedules under legacy evaluation.
- It does not prove any recorded spike value, nonlinear scan admission, independent-oracle
  agreement, Plan execution, publication/write safety, diagnostics, or mutation sensitivity.
- The ReLU and top-level axiswise source donors lack retained inputs; the other exact donors have
  different semantics from the six recorded groups.
- No program or input was reverse-engineered from the recorded floats.
- Production and existing tests are untouched; the seed is imported by nothing.

## Task 4 estimate

The plan's **3–4 focused engineer-days** within the broader 13–18 day effort remains appropriate.
This rehearsal settles the small `retainedAxisPos` helper but does not reduce the main work:
recovering/re-authorizing exact semantic fixtures, implementing nonlinear scan block allocation and
result-only publication, extending the independent oracle, exercising 13 mutation cycles, and
running two focused reviews.

Until authentic source/input pairs are recovered or the governing plan explicitly replaces the six
recorded fixtures, Task 4 must remain stopped at Phase 2.

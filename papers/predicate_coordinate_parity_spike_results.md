# Predicate coordinate-parity spike: measured results

## Result

**Recommendation: REVISE** for Slice 5. The architecture is supported, but the fixture/oracle plan
must be revised around one mask case that the original spike did not measure:

- **Factor policy — confirmed:** `context ++ output ++ per-term reduction` in first-encounter order, UID identity, and base-pin substitution in every affine leaf.
- **Mask policy — partially confirmed:** source seeds become zero, while eliminated non-seeded plain
  `.free` slots become their enumerated coordinates. A follow-up adjudication proved that an
  eliminated `.freeNorm` slot is source-reachable, but did not close its backend parity obligation.

The spike needed no `FactorPlan` or `RawAxiswisePlan` mask field, did not widen admission, and left `TermPlan.factors` unchanged. Temporary code was committed for audit and then reverted.

The follow-up compiled this exact source program successfully, despite the occurrence-local kinds
sharing one UID:

```text
iter r = 2, c = 2
tensor Z(r)
G[r.,0] := normalize(where r != 0)(Z[r])
G[r+1,c+1] := G[r,c]
```

With `Z = [1,3]`, source evaluation produced shape `[2,2]` and data `[0,0,1,0]`. `assignUIDs`
shares the UID while preserving the occurrence-local kind, so `checkDtypes` accepts the `.freeNorm`
occurrence as real and the `.iterNext` occurrence as nat. T2-F5's retained `.freeNorm` therefore
does not close this eliminated-`.freeNorm` case.

## Setup and checkpoints

| Item | Evidence |
|---|---|
| Worktree / branch | `/Users/williammacready/code/python/pyncd.worktrees/predicate-coordinate-parity-spike`; `agents/predicate-coordinate-parity-spike` |
| Task 0 / local `main` | `8f8981e` |
| Cache | Exact donor `/Users/williammacready/code/python/pyncd`; plain `rsync -a` warm start; 8,101 `.olean` files / 8,094 sources, reported 100%; no cold build |
| Project refresh | `cd leanncd && "$HOME/.elan/bin/lake" build LeanNCD`, exit 0; time/job count not recorded |
| Default baseline | `cd leanncd && "$HOME/.elan/bin/lake" build`, exit 0, 8,659 jobs; time/warnings not recorded |
| Temporary commits | Task 1 `93d2d4f4fca07a2dc0a20952011c8a3e2fc425e5`; Task 2 `8eef26cf2e066c19cee6aa80c6e8d3d33b35c092` |
| Reviews | Both supplied independent reviews were CLEAN |
| Post-revert default at `cd497c6` | `cd leanncd && "$HOME/.elan/bin/lake" build`, exit 0; `Build completed successfully (8659 jobs)`; `real 6.46`, `user 3.52`, `sys 4.94`; 11 replayed pre-existing warnings |

Task 1 command (`C1`) exited 0 with 8,536 jobs; differential replay was 3,832/3,832 accepted and scan corpus 17/17:

```sh
cd leanncd && "$HOME/.elan/bin/lake" build \
  LeanNCD.Eval.Plan.Kernel LeanNCD.Eval.Plan.Compile \
  LeanNCD.Eval.Plan.Dense Eval.Plan.PredicateCoordinateSpikeTest \
  Eval.Plan.DifferentialTest
```

Task 2 command (`C2`) exited 0 with 8,539 jobs and retained those replay counts:

```sh
cd leanncd && "$HOME/.elan/bin/lake" build \
  LeanNCD.Eval.Nonlin LeanNCD.Eval.Plan.Nonlin Eval.NonlinTest \
  Eval.Plan.NonlinDenseTest Eval.Plan.PredicateCoordinateSpikeTest \
  Eval.Plan.ScanCompileTest Eval.PropertyOracle.ScanUnroll \
  Eval.PropertyOracle.ScanOracle
```

Total elapsed times were not recorded. Repeated `Gen.lean` cap messages were informational; no restored-target warning was recorded.

## Ten measured fixtures

### Factor policy

| ID | Donor / delta | Observed values | Structure |
|---|---|---|---|
| T1-F1 | `Portfolio/RelationalTest` RL1 copied exactly: `I[i,j] := [i=j]`, no inputs, `[3,3]` | Source/positional `[1,0,0,0,1,0,0,0,1]` (identity) | Initial/residual basis `[1101,1102]` (`[i,j]`); rows select `i`,`j` |
| T1-F2 | `Portfolio/RecurrenceTest` RC3 copied exactly | Source `[1,3,6]`; at `[i,j]=[0,1]`/`[1,0]`: `false`/`true` | Basis `[1201,1202]` (`[i,j]`), output before reduction |
| T1-F3 | `CompileTest.multiReductionSched`; append `[j < k]` last | At `[i,j,k]=[0,0,1]`/`[0,1,0]`: `true`/`false`; Iverson stayed last | Basis `[1,2,3]` (`[i,j,k]`), reductions `j,k` |
| T1-F4 | Exact `DifferentialTest.sameAxisNameSched`; append context-`l` `<` output-`l` | At `[context l,output l]=[0,1]`: `true` | Same-name UIDs remained `[3101,3102]`; rows `#[1,0]`,`#[0,1]` |
| T1-F5 | Second base assignment of `ScanCompileTest.multiBaseSched`; append `abs(r*(r-2))=1` with pin `r:=1` | At `#[]`: `true` | Initial/residual `[r.uid]`/`[]`; `(coeffs,bias)` leaves `([],1),([],-1),([],1)` |

The width guard observed `.affineWidthMismatch 2 1`, never truncation/defaulting. A mask spot check used local basis `[i]`; absent `j` became zero, making `[i=j]` at local coordinate `2` false.

### Mask/callback and scan rewrites

| ID | Donor / delta | Observed values | Structure |
|---|---|---|---|
| T2-F1 | `Portfolio/NormTest` NM4 unchanged | Source/adapter `[0,.4,.6,0,.5,.5]` | Full local coordinate fed an **included?** callback |
| T2-F2 | NM4; only `normalize`→`softmax`, excluded `A[0,0]` `1`→`1000` | Source/adapter `[0.000000,0.268941,0.731059,0.000000,0.500000,0.500000]` | Excluded `1000` did not enter maximum |
| T2-F3 | `ScanCompileTest.maskedAxiswiseRecur`; only mask→`l=0` | Source/adapter/unroll `[1,3,.25,.75,.25,.75]` | Two masks `(0=0)`; seeded `l` absent |
| T2-F4 | `ScanCompileTest.okBase` + `badIverson "S" nextL`; predicate→`l=0` | Source/unroll `[1,1,0]` | Iversons `(0=0)`,`(1=0)`; `l` absent |
| T2-F5 | `ScanGen.template6`; retained extent-two `.freeNorm i` on `G/Z/A`, base `normalize(where r!=0)`, nonzero `Z` | Shape `[2,2,2]`; source/unroll `[0,0,0,0,.25,1,.75,1]` | The eliminated non-seeded scan coordinate was `.free r`, while `c` was seeded; base masks `(0!=0)`,`(1!=0)` and absent `r,c` therefore do not evidence eliminated `.freeNorm`. The retained `.freeNorm i` does not close the eliminated-`.freeNorm` case |

The exact T2-F2 representation was additionally measured with:

```sh
printf '#eval repr (#[0.0, 1/(1+Float.exp 1.0), Float.exp 1.0/(1+Float.exp 1.0), 0, 0.5, 0.5] : Array Float)\n' |
  "$HOME/.elan/bin/lake" env lean --stdin
```

It printed `#[0.000000, 0.268941, 0.731059, 0.000000, 0.500000, 0.500000]`.

## Eleven mutation fail/restore/pass observations

Every mutation was visible in the diff against its temporary tree. The ledger records the exact
M1-M4 command (`S1`) as:

```sh
cd leanncd && "$HOME/.elan/bin/lake" build Eval.Plan.PredicateCoordinateSpikeTest
```

Each `S1`/`C2` failure below exited 1; after restoration to the named tree, the identical command
exited 0 and reproduced the fixture values above. Mutation/replay elapsed times were not recorded.

| ID | Tree / command | Failing diagnostic and values | Restore / pass |
|---|---|---|---|
| M1 | `93d2d4f`; S1; `context++reduction++output` | T1-F2 `basis: [1202,1201]`; T1-F3 `[2,3,1]` | `93d2d4f`; S1 exit 0 |
| M2 | `93d2d4f`; S1; reverse reductions | T1-F3 `basis: [1,3,2]` | `93d2d4f`; S1 exit 0 |
| M3 | `93d2d4f`; S1; name-based densification | T1-F4 `UID basis: [3102,3102]` | `93d2d4f`; S1 exit 0; rows `#[1,0]`,`#[0,1]` |
| M4 | `93d2d4f`; S1; bypass pins | T1-F5 leaves `#[1],0`, `#[1],-2`, `#[0],1` | `93d2d4f`; S1 exit 0; empty rows/biases `1,-1,1`, true |
| M5 | `8eef26c`; C2; `masked := included c` | T2-F1 source/adapter `[1,0,0,1,0,0]`; full replay also failed other mask users | `8eef26c`; C2 exit 0, 8,539 jobs; `[0,.4,.6,0,.5,.5]` |
| M6 | `8eef26c`; C2; masked values enter max | T2-F2 source/adapter `#[0.000000,0.000000,0.000000,0.000000,0.500000,0.500000]` | `8eef26c`; C2 exit 0; exact values above |
| M7 | `8eef26c`; C2; mask basis `[i]`→`[l,i]` | T2-F3 adapter `.affineWidthMismatch 2 1` | `8eef26c`; C2 exit 0; source/adapter parity |
| M8 | `8eef26c`; C2; seeded zero→live `sigma` | T2-F3 source `#[1,3,.25,.75,.25,.75]`, independent `#[1,3,.25,.75,0,0]` | `8eef26c`; C2 exit 0; both later rows `.25,.75` |
| M9 | `8eef26c`; C2; leave Iverson unchanged | T2-F4 source `#[1,1,0]`, independent `#[1,1,1]` | `8eef26c`; C2 exit 0; `(0=0),(1=0)` |
| M10 | `8eef26c`; C2; leave masks unchanged | T2-F3 reached structural failure with two live `axis l (uid 42502)=0` masks; replay also had T2-F5 source `#[0,0,0,0,.25,1,.75,1]` vs independent `#[0,0,0,0,0,1,0,1]` | `8eef26c`; C2 exit 0; `(0=0),(0=0)`, no seeded UID |
| M11 | `8eef26c`; C2; eliminated `.free r`→zero | T2-F5 source `#[0,0,0,0,.25,1,.75,1]`, independent `#[0,0,0,0,0,1,0,1]` | `8eef26c`; C2 exit 0; `(0!=0),(1!=0)` |

The supplied independent reviewers were CLEAN. M10 proves value parity alone cannot prove recurrence-mask rewriting: a missing seeded UID accidentally behaves as zero, so the structural no-UID check is load-bearing.

## Precise `ScanUnroll` independence audit

The audit ran while Task 2 existed. After stripping Lean line/nested-block comments, direct imports were exactly:

```text
import Eval.PropertyOracle.Compare
import Eval.PropertyOracle.ScanGen
```

The only `eval[A-Z]...` identifier was `evalScheduled` (three code occurrences). There were no code references to:

```text
lowerFactorPredicate lowerMaskPredicate
evalPosAffine evalPosPredArith evalPosBool evalPosIverson
runDenseScan prepareEvalPlan runPreparedDense evalScan writeRowKinds applyAffine
writeSliceAtMulti sliceTensorAtMulti residualizeAssignment substitutePins
```

The oracle was therefore independent of checked predicate lowering, positional evaluation, checked preparation/execution, and checked/source scan-worker helpers. It recursively rewrote source `PredArith`/`BoolExpr` with its own `substIdx`, produced only `ScanStmt.plain` assignments, evaluated that scan-free program with source `evalScheduled`, and reconstructed history itself. Precisely, it was **not** independent of the source AST, `evalScheduled`, or its existing independent substitution/geometry machinery. `Compare`/`ScanGen` transitively exposed source evaluation; there was no direct checked-plan import.

## Exclusions, risks, and disposition

- JAX was excluded as planned. `JaxExperiment` was known pre-existing red; no JAX repair or gate was attempted.
- Production integration must still add the real plan representation while preserving current admission boundaries.
- Ten discriminating fixtures are not a broad property proof over arbitrary nested predicates, mixed pins, or richer scan geometry.
- The oracle shares source AST and `evalScheduled`; it is an independent rewrite/execution shape, not separately specified semantics.
- The follow-up source counterexample proves that an eliminated `.freeNorm` is reachable. Because an
  axiswise operation couples the per-coordinate leaves, Slice 5 explicitly leaves grouped
  `ScanUnroll` support out of scope: the oracle must reject this fragment, while Task 5.3 pins it
  independently with source/checked/hand-expected parity and a mutation that zeroes the eliminated
  coordinate.
- No performance conclusion is available because total timings were not recorded.
- Boolean tensors/dtypes/algebra, corpus expansion, and JAX remain out of scope.

The measurements support the architecture and the confirmed portions of the policies, but the
fixture/oracle plan in `papers/predicate_boolean_backend_parity.md` must be revised before Slice 5.

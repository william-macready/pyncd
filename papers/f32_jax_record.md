# F32-JAX record (plan: `papers/f32_jax_evalplan.md`; base `559311a`)

Task 1 (storage-keyed gates and the `orderedReference32` label). Task 2 appends its own section
and the Python cells of Tables A and B.

## 1. Build job counts (Task 1 tree)

| Command | Jobs | Plan | Result |
|---|---|---|---|
| `lake build` (patch applied, before the step 3 prose edits) | 8,673 | 8,673 | green |
| `lake build JaxExperiment` (same tree) | 8,514 | 8,514 | green |
| `lake env lean spikes/AxisABoundaryProbe.lean` | exit 0, 0 `error` lines | 0 errors | green |
| `lake build JaxExperiment Eval.Plan.ExecutableTest` (after step 3 edits) | 8,515 | green | green |

The last row's count is the union of two targets' closures, not a replacement for the two
full-build counts. `wc -l` on `experiments/jax_bridge/EvalPlanCodegen.lean` was 1991 and on
`test/Eval/Plan/ExecutableTest.lean` 1887, before and after step 3.

## 2. Mutation manifest (`mutation-manifest.sh --task 1`, 15 cycles, run on the patched tree before step 3)

| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| J1 (einsumStorageAdmitted admits float32) | yes | yes | yes | PASS |
| J2 (jaxRealCarrier float32 arm reverted to binary64) | yes | yes | yes | PASS |
| J3 (destination dtype check widened to admit bool) | yes | yes | yes | PASS |
| J4 (algebra check widened to any binary32 algebra) | yes | yes | yes | PASS |
| J5 (unary check skipped for float32 evidence) | yes | yes | yes | PASS |
| J6 (affine kernel label hardcoded to orderedReference64) | yes | yes | yes | PASS |
| J7 (aggregation not keyed off storage kind) | yes | yes | yes | PASS |
| J8 (einsumOnly mode admits every storage kind) | yes | yes | yes | PASS |
| J9 (lowerAssign standalone storage gate deleted) | yes | yes | yes | PASS |
| J10 (loweringToEinsumCandidate storage gate deleted) | yes | yes | yes | PASS |
| J11 (affineReference refuses float32) | yes | yes | yes | PASS |
| J12 (lowerCheckPlanToCandidate aggregates under binary64) | yes | yes | yes | PASS |
| J13 (bool source admitted under float32 evidence) | yes | yes | yes | PASS |
| J14 (context check skipped for float32 evidence) | yes | yes | yes | PASS |
| J15 (affine Iverson rejection dropped) | yes | yes | yes | PASS |

15/15 cycles passed.

## 3. Step 3 re-runs (after the prose edits)

`mutation-manifest.sh leanncd papers/f32_jax_mutations_post.json J12 J15 J3`:

| Mutation | Cycle | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| J3 (destination dtype check widened to admit bool) | yes | yes | yes | PASS |
| J12 (lowerCheckPlanToCandidate aggregates under binary64) | yes | yes | yes | PASS |
| J15 (affine Iverson rejection dropped) | yes | yes | yes | PASS |

3/3 cycles passed.

## 4. Step 4: value-grep of the Lean tree

`rg -n "requireFloat64Plan|JaxExecutableValidationError.unsupportedStorageKind|reference64-only" leanncd/LeanNCD leanncd/experiments leanncd/test leanncd/spikes`
gave exactly three hits, all allowed:

- `EvalPlanCodegen.lean`, `requireModeStorage`'s docstring ("it was `requireFloat64Plan`");
- `EvalPlanCodegen.lean`, the re-pointed fixtures 22-25 header ("Before slice F32-JAX this backend
  was reference64-only");
- `ExecutableTest.lean`, the fixture-1 docstring's historical narration ("backend's
  reference64-only policy"), immediately followed by "Slice F32-JAX then ADMITTED this assignment".

`JaxExecutableValidationError` now has exactly three constructors (`aggregationMismatch`,
`invalidBindings`, `invalidCandidate`).

## 5. Sibling-door audit, re-derived against the tree (plan §4)

Each cell was checked by opening the named door with `rg -n` (no line numbers cited here). "Fix"
names the fixture; "J" the mutation cycle that kills a regression of it. `EPC` = `EvalPlanCodegen.lean`,
`ET` = `ExecutableTest.lean`. **No SI cell found.**

### Table A: case × door (Lean-side cells; Python cells are appended by Task 2)

| Case | f32 einsum | f32 affine | Evidence in tree |
|---|---|---|---|
| assign-only valid | **F** `unsupportedStorageKind .float32`: plan doors (`generateForward`, `generateNamed .einsumOnly`, `renderInputConstants`, `lowerPlan`), EPC fixtures 22 and 25 (J8); standalone doors `lowerAssign`/`loweringToEinsumCandidate`, EPC fixture 22 (J9, J10); validator door `einsumStorageAdmitted` in `validateEinsum`, ET einsum-kernel guard (J1) | **R `orderedReference32`**: `renderAffinePlanNamed`, `renderAffinePlanPositional`, `generateNamed .affineReference`, `lowerCheckPlanToCandidate` (+ `validateAndConstructExecutable`) in EPC fixture 22 (J11, J12); `renderAffineAssign`/`loweringToAffineTableCandidate` standalone in EPC fixture 22; kernel label in ET `validateAndConstructKernel ... .orderedReference32` guard (J2, J6) | verified |
| bool destination | F storage (plan-level einsum gate precedes support) | **F `destinationDType 7 2 .bool`**, ET `f32BoolDestAssign` (J3) | verified |
| bool source | F storage (EPC `f32BoolSourcePrepared?`, `generateNamed .einsumOnly`) | **F `unsupportedSourceDType 0 0 0 .bool`** at `generateNamed .affineReference`, `renderAffinePlanPositional`, `lowerCheckPlanToCandidate`, EPC `f32BoolSourcePrepared?` (J13) | verified |
| unary read | F storage | **F `unaryFactor 7 0 0`**, ET (J5) | verified |
| tropical algebra | F storage | **F `unsupportedAlgebra 7 admittedAlgebraF32Max`**, ET (J4) | verified |
| Iverson factor | F storage (EPC `f32IversonPrepared?`) | **F `iversonFactor 0 0 1`** at `generateNamed .affineReference`, `lowerCheckPlanToCandidate`, EPC `f32IversonPrepared?` (J15) | verified |
| contextful | **F storage** at `lowerAssign`, `loweringToEinsumCandidate`, EPC `f32CtxAssign` | **F `unsupportedContext 0 #[2]`** at `renderAffineAssign`, `loweringToAffineTableCandidate`, EPC `f32CtxAssign` (J14) | verified |
| zero-pad label-extent mismatch | **F storage** at `lowerAssign`, EPC `f32PadAssign` (storage precedes `labelExtentMismatch`) | **R**, kernel `orderedReference32`, EPC `f32PadAssign` (J6) | verified |
| zero-step plan | **F storage**, plan-level only: EPC fixture 25 (J8) | **R `orderedReference32`**: EPC fixture 23 (`lowerCheckPlanToCandidate`, J12) and ET fixture 23 (`validateAndConstructExecutable (emptyPlanCandidate p)`, J7); ET `aggregateEvidenceList .float32 #[]` | verified |
| positional route | F storage (`lowerPlan`, EPC fixtures 22) | **R** `renderAffinePlanPositional`, EPC fixtures 22 and 25 (J11) | verified (Python exactness: Task 2) |
| standalone-assign route | F storage (`lowerAssign`, per fixture) | **R**, kernel `orderedReference32`, EPC fixture 22 and `f32PadAssign` (J2, J6) | verified (Python exactness: Task 2) |

Also verified: EPC fixture 24 (`f32BadBindingPrepared?`) reaches `invalidBindings (.materializedSlot (.slotOutOfRange 99 2))`
under f32, the same as its binary64 control, so binding validation is not skipped; ET fixture 24 says the same
through `validateAndConstructExecutable`.

### Table B: binary64 literals the f32 path now reaches

| Site | Reached by f32? | Class | State in tree | Pin |
|---|---|---|---|---|
| `.f64` / `admittedAlgebra` @ `jaxAssignSupported` | yes | fixed -> `jaxRealCarrier kind` | the only literals are inside `jaxRealCarrier`, two arms, no wildcard | J2-J5, J13 |
| `.orderedReference64` @ `candidateEvidenceLabel` | yes | fixed -> `orderedReferenceFor` | `.affineTable k => orderedReferenceFor k.semanticAssignment.storageKind` | J6 |
| `.orderedReference64` @ `aggregateEvidenceList` | yes (zero-step) | fixed, keyed by `kind` | takes `kind`, compares against `orderedReferenceFor kind` | J7, J12 |
| `storageKind == .float64` @ `validateAndConstructExecutable` | yes | deleted | no `storageKind ==` test remains in `Executable.lean`; `JaxExecutableValidationError.unsupportedStorageKind` gone | ET fixtures 23/24, J7 |
| `requireFloat64Plan` x7 | yes | fixed -> `requireModeStorage mode` | 9 call sites of `requireModeStorage` in EPC (7 re-pointed, 2 new einsum doors); `requireFloat64Plan` appears only in a docstring | J8, J11 |
| none @ `lowerAssign` / `loweringToEinsumCandidate` | yes | added einsum door | both open with `requireModeStorage .einsumOnly assign.storageKind` / `checked.storageKind` | J9, J10 |
| `Float.toBits` @ `pyTensorEntry` / `renderInputConstants` | no | (c): `renderInputConstants` is behind `requireModeStorage .einsumOnly`, which refuses f32 | EPC fixtures 22 and 25 assert the `renderInputConstants` refusal; `pyTensorEntry` has no f32 caller in Task 1 | EPC fixtures 22/25 |
| `runDenseAssign` @ `buildAssignFixture` | f32 fails loud | (c): binary64-only helper | see observation below | plan §1.4 |
| rendered `affineReference` plan DATA carries no storage-kind tag | yes | (c), not fixed (plan §4 Table B, last row) | unchanged: no tag in `renderAffinePlanNamed` output; `renderAffineTerm` and `requireNoIverson` are dtype-free | caller-convention gap |
| `jnp.float64` / `int64` constants @ runtime | yes | Task 2 | `evalplan_affine_runtime.py` still has its binary64 literals at this commit, as expected before Task 2 parametrizes it | Task 2 (P1-P6) |

Observation (no stop): `buildAssignFixture` calls the binary64 `checkAssign sigs a` first, so an f32
table fails with "check failed" (`dtypeNotAdmitted`) before it would reach "Dense run failed" as the plan's
Table B row says. Either way it fails loud in Lean before any Python, so the cell is still (c) and not reachable
silently; only the wording of the plan's row is slightly off.

Doors opened with no diff showing them: `validateAffineTable` (via `jaxSupportOk`; carrier-keyed, no other
literal), `requireNoIverson` and `renderAffineTerm` (no dtype literal), `einsumTermLabelExtents` (reached only
after `requireModeStorage` in `lowerAssign`), `buildAssignFixture` (above). The Python smoke/corpus/scaling
callers are Task 2's.

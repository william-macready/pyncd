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
| bool destination | no dedicated fixture; F by gate order (`requireModeStorage` precedes `requireJaxSupport`) and redundantly by the support policy; the generic gate is pinned by J8/J9 on fixture 22 | **F `destinationDType 7 2 .bool`**, ET `f32BoolDestAssign` (J3) | verified |
| bool source | F storage (EPC `f32BoolSourcePrepared?`, `generateNamed .einsumOnly`; J8) | **F `unsupportedSourceDType 0 0 0 .bool`** at `generateNamed .affineReference`, `renderAffinePlanPositional`, `lowerCheckPlanToCandidate`, EPC `f32BoolSourcePrepared?` (J13) | verified |
| unary read | no dedicated fixture; F by gate order (`requireModeStorage` precedes `requireJaxSupport`) and redundantly by the support policy; the generic gate is pinned by J8/J9 on fixture 22 | **F `unaryFactor 7 0 0`**, ET (J5) | verified |
| tropical algebra | no dedicated fixture; F by gate order (`requireModeStorage` precedes `requireJaxSupport`) and redundantly by the support policy; the generic gate is pinned by J8/J9 on fixture 22 | **F `unsupportedAlgebra 7 admittedAlgebraF32Max`**, ET (J4) | verified |
| Iverson factor | F storage (EPC `f32IversonPrepared?`, `generateNamed .einsumOnly`; J8) | **F `iversonFactor 0 0 1`** at `generateNamed .affineReference`, `lowerCheckPlanToCandidate`, EPC `f32IversonPrepared?` (J15) | verified |
| contextful | **F storage** at `lowerAssign` (J9), `loweringToEinsumCandidate` (J10), EPC `f32CtxAssign` | **F `unsupportedContext 0 #[2]`** at `renderAffineAssign`, `loweringToAffineTableCandidate`, EPC `f32CtxAssign` (J14) | verified |
| zero-pad label-extent mismatch | **F storage** at `lowerAssign`, EPC `f32PadAssign` (storage precedes `labelExtentMismatch`; J9) | **R**, kernel `orderedReference32`, EPC `f32PadAssign` (guard not in J6's targets; the shared label is killed by J6 through ET's `f32DestAssign` kernel guard) | verified |
| zero-step plan | **F storage**, plan-level only: EPC fixture 25 (J8) | **R `orderedReference32`**: EPC fixture 23 (`lowerCheckPlanToCandidate`, J12) and ET fixture 23 (`validateAndConstructExecutable (emptyPlanCandidate p)`, J7); ET `aggregateEvidenceList .float32 #[]` | verified |
| positional route | F storage (`lowerPlan`, EPC fixture 22; J8) | **R** `renderAffinePlanPositional`, EPC fixtures 22 and 25 (J11) | verified (Python exactness: Task 2) |
| standalone-assign route | F storage (`lowerAssign`, per fixture: EPC fixture 22 standalone, `f32CtxAssign`, `f32PadAssign`; J9; `loweringToEinsumCandidate` on fixture 22 and `f32CtxAssign`; J10) | **R**, kernel `orderedReference32`, EPC fixture 22 and `f32PadAssign` (J2, J6) | verified (Python exactness: Task 2) |

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

Fix round 1 (reviewer finding): the plan's section 4 sentence "No SI cell, and no gap left. Every f32 cell
names a dedicated fixture and a mutation that kills it" is overstated for three cells: the f32-einsum
cells for bool destination, unary read and tropical algebra have no dedicated einsum-door fixture. The
`f32BoolDestAssign`, unary and `admittedAlgebraF32Max` guards in ET test only `checkJaxAssignSupport`.
They are not SI (the einsum doors refuse by gate order, redundantly by the support policy), and the
generic gate is pinned by J8/J9 on fixture 22. J-cycle attribution above was read off the per-cycle
mutated-build logs of the step 2 manifest run: J8 fails EPC fixtures 22 (plan-level and standalone), 25,
`f32BoolSourcePrepared?`, `f32IversonPrepared?`, `f32CtxAssign` and `f32PadAssign`; J9 fails fixture 22
standalone, `f32CtxAssign` and `f32PadAssign`; J10 fails fixture 22 standalone and `f32CtxAssign`; J1
fails ET's f32 einsum-kernel guard (the validator door).

Observation (no stop): `buildAssignFixture` calls the binary64 `checkAssign sigs a` first, so an f32
table fails with "check failed" (`dtypeNotAdmitted`) before it would reach "Dense run failed" as the plan's
Table B row says. Either way it fails loud in Lean before any Python, so the cell is still (c) and not reachable
silently; only the wording of the plan's row is slightly off.

Doors opened with no diff showing them: `validateAffineTable` (via `jaxSupportOk`; carrier-keyed, no other
literal), `requireNoIverson` and `renderAffineTerm` (no dtype literal), `einsumTermLabelExtents` (reached only
after `requireModeStorage` in `lowerAssign`), `buildAssignFixture` (above). The Python smoke/corpus/scaling
callers are Task 2's.

## 6. Task 2 phase 1: runtime parametrization, binary32 harness, evidence runs

Environment: Python 3.13.12, JAX/JAXlib 0.10.0, NumPy 2.5.2, CPU (`setup-python.sh` run fresh in this
worktree; `.cache/` is gitignored). The patch `papers/f32_jax_files/task2.patch` applied cleanly (4 files,
563 insertions, 22 deletions). One comment fix after applying: the header of `run-evalplan-affine32.sh`
now reads "the 7 named fixtures (6 spike + `termSum64`), 8 standalone-assign and 2 positional fixtures,
plus every STRIDE-th PropertyOracle corpus case".

### 6.1 Build and binary64 preservation (all as observed in the prototype)

- `lake build`: 8,673 jobs; `lake build JaxExperiment`: 8,514 jobs. Both unchanged (no new Lake module).
  `EvalPlanAffineSmoke32.lean` has no Lake target; it is typechecked by `run-evalplan-affine32.sh` only
  (the script's own `lake build` prints 8,671 jobs for its three targets).
- `run-evalplan-affine.sh` before the patch (baseline) and after it both pass. The generated
  `.cache/generated_evalplan_affine_smoke.py` is `cmp`-identical across the two runs, 11,509 bytes.
- `run-evalplan.sh` passes ("Lean checked plan -> generated jnp.einsum -> JAX evaluation smoke test
  passed").
- `run-evalplan-affine-corpus.sh` (binary64, full corpus): `source_cases=3832 eager_mismatches=0
  feature_masks=45 jit_cases=65 (corpus_representatives=45, curated=20)`, `artifact_bytes=3424195
  generation_seconds=18.627 eager_seconds=508.287 jit_seconds=5.415`. Counts and bytes match the
  recorded values exactly; timings differ naturally (observed in the prototype: 26.8 / 575.8 / 6.4 s).

### 6.2 Binary32 stride-100 run (`./run-evalplan-affine32.sh`, defaults `100 1`)

```
Generated ...generated_evalplan_affine_smoke32.py: 7 named + 8 assign + 2 positional + 39 corpus (stride 100 of 3832)
known XLA CPU divergence reproduced exactly: f32Identity positions [1, 2]
kinds={'named': 46, 'assign': 8, 'positional': 2} eager_checks=80 jit_checks=80 (jit_stride=1) eager_seconds=7.971 jit_seconds=2.376
56 binary32 fixtures, 160 eager/jit output checks: bit-identical to the Lean binary32 reference except the pinned KNOWN_DIVERGENT positions (x64 disabled)
```

### 6.3 Python mutation cycles P1-P6 (`papers/f32_jax_files/python_mutations.py`, run against the stride-100 module)

The driver prints `(returncode, last line)` and has no verdict exit code; each row was checked by hand
against the plan. Every mutant has returncode 1; the unmutated and restored runs have returncode 0.

| Mutant | (returncode, last line) |
|---|---|
| unmutated | `0`, `56 binary32 fixtures, 160 eager/jit output checks: bit-identical to the Lean binary32 reference except the pinned KNOWN_DIVERGENT positions (x64 disabled)` |
| P1 reduction via `jnp.sum(mat, axis=1)` | `1`, `AssertionError: reduction64 eager Y: not bit-identical at 0: 0x41f80000 vs 0x00000000` |
| P2 term sum via `jnp.sum(stacked, axis=0)` | `1`, `AssertionError: termSum64 eager Y: not bit-identical at 0: 0x41f80000 vs 0x00000000` |
| P3 factor product reversed | `1`, `AssertionError: factorProduct3 eager Y: not bit-identical at 1: 0xbf5b3ca1 vs 0xbf5b3ca5` |
| P4 `_require_dtype` input check off | `1`, `AssertionError: float32 dtype accepted float16 inputs` |
| P5 zero-pad mask ignored | `1`, `AssertionError: f32Pad eager result: not bit-identical at 2: 0x40a00000 vs 0x00000000` |
| P6 positional nodes reversed | `1`, `TypeError: reshape requires ndarray or scalar arguments, got <class 'NoneType'> at position 0.` |
| restored | `0`, the same `56 binary32 fixtures, 160 ...` line as unmutated |

The P6 line is the brief's string followed by the library's own suffix ` at position 0.`.

P2 is real, not an equivalent mutant: XLA CPU sums a stacked axis sequentially up to 32 terms and in
blocks at 64, so only `termSum64` kills it. Every other fixture (including the standalone-assign
`f32TermOrder`) passes under P2; see the attribution probe below.

Per-fixture attribution probe (scratch script, not committed; eager only, the 8 standalone-assign and 2
positional fixtures of the same generated module, one run per mutant). It exists because the driver stops at
the first failing fixture and the named fixtures run first, so the table above says nothing about which
assign/positional fixture would fail:

| Mutant | assign/positional fixtures that fail | all others |
|---|---|---|
| P1, P2, P4 | none (killed only by the named fixtures `reduction64`, `termSum64`, and the dtype probes in `main`) | pass |
| P3 | `f32FactorOrder`: `result: not bit-identical at 0: 0xc81f7053 vs 0xc81f7054` | pass |
| P5 | `f32Pad`: `result: not bit-identical at 2: 0x40a00000 vs 0x00000000` | pass |
| P6 | `f32ProductChain`: `TypeError: reshape requires ndarray or scalar arguments, got <class 'NoneType'> at position 0.`; `f32ReductionGraph` passes under reversal | pass |

### 6.4 THE EVIDENCE GATE: full corpus, stride 1, JIT on every case (`./run-evalplan-affine32.sh 1 1`)

Every fixture is JIT-checked, unlike the binary64 runner's 45 representatives. That is deliberate: the
measured cost (about 3 min of JIT) is acceptable, and a per-case JIT claim is strictly stronger than a
representative sample. The runner keeps `JIT_STRIDE`, so a routine run may sample, but this slice's
evidence claim is this run.

```
Generated ...generated_evalplan_affine_smoke32.py: 7 named + 8 assign + 2 positional + 3832 corpus (stride 1 of 3832)
known XLA CPU divergence reproduced exactly: f32Identity positions [1, 2]
kinds={'named': 3839, 'assign': 8, 'positional': 2} eager_checks=5873 jit_checks=5873 (jit_stride=1) eager_seconds=530.213 jit_seconds=190.982
3849 binary32 fixtures, 11746 eager/jit output checks: bit-identical to the Lean binary32 reference except the pinned KNOWN_DIVERGENT positions (x64 disabled)
```

- 3,849 fixtures = 3,832 corpus + 7 named + 8 standalone-assign + 2 positional; 11,746 checks (5,873 eager
  + 5,873 JIT); 0 mismatches outside the pinned `f32Identity [1, 2]`.
- Generated module `.cache/generated_evalplan_affine_smoke32.py`: 3,657,456 bytes (`wc -c`).
- Wall-clock for the whole script, including the three `lake build`s and generation: 784 s (about 13 min).
  Eager 530.2 s, JIT 191.0 s (prototype: 524.8 s and 190.7 s). Timings are recorded, not matched.

### 6.5 Python cells of Table A (the `verified (Python exactness: Task 2)` rows)

| Row | Python outcome | Fixture | P-cycle |
|---|---|---|---|
| positional route | bit-identical to the Lean binary32 reference, eager and JIT, in the 56-fixture and the 3,849-fixture runs (`kinds` shows `'positional': 2`) | `f32ProductChain`, `f32ReductionGraph` | P6 kills `f32ProductChain` (`TypeError: reshape requires ndarray or scalar arguments, got <class 'NoneType'> at position 0.`). `f32ReductionGraph` is not killed by P6. |
| standalone-assign route | bit-identical, eager and JIT, for all 8 (`'assign': 8`); `f32Identity` matches except the pinned KNOWN_DIVERGENT positions [1, 2] | `f32Identity`, `f32ReductionRounding`, `f32MultiplicationRounding`, `f32FactorOrder`, `f32Efp`, `f32Zerd`, `f32TermOrder`, `f32Pad` | P3 kills `f32FactorOrder`; P5 kills `f32Pad`. P1 and P2 do not kill any standalone-assign fixture; they are killed only by the named `reduction64` and `termSum64`. |
| zero-pad label-extent mismatch | bit-identical to the Lean reference, eager and JIT; the padded cell (index 2) is `0x00000000`, and the mutant shows the unpadded gather value `0x40a00000` there | `f32Pad` | P5 (mask ignored): `f32Pad eager result: not bit-identical at 2: 0x40a00000 vs 0x00000000` |

Table B, last row (`jnp.float64` / `int64` constants at runtime): now resolved. `evalplan_affine_runtime.py`
takes `dtype` (default `jnp.float64`, so every existing caller is unchanged), `_require_dtype` never casts
(P4 kills its removal), and the float32 path runs with `jax_enable_x64` disabled (asserted in
`evalplan_affine_smoke32.py`).

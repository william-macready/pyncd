# Lean-JAX bridge experiments

This directory holds six isolated experiment runners, none of which changes LeanNCD's dependencies
or toolchain:

- **`run.sh`**: upstream `NetSpec` -> generated JAX. Evaluates the
  [`lean4-mlir`](https://github.com/brettkoonce/lean4-mlir) JAX bridge, an upstream code
  generator that never runs LeanNCD's own Tensor Logic pipeline.
- **`run-evalplan.sh`**: Tensor Logic -> checked LeanNCD plan -> generated `jnp.einsum` -> JAX.
  Runs a Tensor Logic fixture through LeanNCD's own `compileToScheduled` / `prepareEvalPlan` /
  `CheckedEvalPlan` pipeline (see `docs/superpowers/plans/2026-08-10-jax-evalplan-smoke.md`), then
  through a narrow experimental Lean code generator (`EvalPlanSmoke.lean`) that emits a Python
  module containing a real `jnp.einsum` call.
- **`run-evalplan-affine.sh`**: curated source, checked-kernel, and positional-graph fixtures ->
  checker-produced affine lookup tables -> the ordered JAX reference runtime.
- **`run-evalplan-affine-corpus.sh`**: all 3,832 `PropertyOracle.enumPrograms` cases through the same
  affine reference, with eager full-output comparison and JIT feature representatives.
- **`run-evalplan-affine32.sh`**: the binary32 counterpart (slice F32-JAX): named, corpus,
  standalone-assign and positional fixtures retagged `.float32` through the same ordered runtime
  (`dtype=jnp.float32`, x64 disabled), compared bit for bit with the Lean binary32 reference.
- **`run-scaling-probe.sh`**: one mid-sized (64x64, 4,096-coordinate) contraction through the same
  affine reference, measured against native `jnp.einsum` computing the same contraction — not a
  permanent test, a one-off measurement for `papers/jax_evalplan_architecture.md` §7.6 row 2.

Plus one Lean-only check, not a runner:

- **`check-lean-drivers.sh [STRIDE]`**: builds `LeanNCD JaxExperiment Tests`, then runs the four Lean
  generators (`EvalPlanSmoke`, `EvalPlanAffineSmoke`, `EvalPlanAffineCorpus`, `EvalPlanAffineSmoke32`)
  into a temp directory and fails if any exits non-zero. No Python, no JAX. The drivers are outside every
  Lake target, and a change to a precision default or to an `InputSignature` constructor breaks them at
  RUN time (a typed `prepareEvalPlan` rejection), so only running them catches it. Run it after such a
  change; the F32 default flip broke all four silently.

## `run.sh`: upstream `NetSpec` bridge

The upstream bridge is a code generator, not an in-process Lean/Python FFI:

1. [`BridgeSmoke.lean`](./BridgeSmoke.lean) defines a small `NetSpec`.
2. Upstream `JaxCodegen.generate` emits a Python module.
3. [`smoke.py`](./smoke.py) imports that module and checks eager evaluation,
   `jax.jit`, and `jax.grad`.

The runner pins upstream commit
`4f91e2a32d7eda0fc44f02a4b04c2fa0e5f59dab`. Its Lean 4.32.2 project is
cloned under the ignored `.cache/` directory, keeping it separate from
LeanNCD's Lean 4.30.0 project.

### Run

From this directory:

```bash
./setup-python.sh
./run.sh
```

`setup-python.sh` creates an isolated CPU-only Python environment and installs
JAX 0.10.0 from the fully pinned [`requirements-cpu.txt`](./requirements-cpu.txt).
It uses Python 3.11-3.13 when available, otherwise it falls back to an installed
`conda` to create Python 3.12. The macOS system Python 3.9 is too old for JAX
0.10.0.

Set `PYTHON` to use an existing JAX environment instead:

```bash
PYTHON=/path/to/python ./run.sh
```

The first run fetches the pinned upstream repository and its Lean dependencies.
Later runs reuse everything under `.cache/`.

### Scope

This spike establishes that a Lean-authored network specification can reach
JAX execution and autodiff. It does not yet translate LeanNCD's tensor-logic
IR into upstream `NetSpec`. The checked-`EvalPlan` experiment below tests a
direct LeanNCD-to-JAX path instead of adding that adapter.

## `run-evalplan.sh`: checked `EvalPlan` -> `jnp.einsum` bridge

Unlike `run.sh`, this path never leaves LeanNCD's own project or toolchain, and never touches
upstream `NetSpec`:

1. [`EvalPlanSmoke.lean`](./EvalPlanSmoke.lean) compiles a Tensor Logic affine fixture
   (`Y[i] := W[i, j] · x[j] + b[i]`) with `compileToScheduled`, prepares it with
   `prepareEvalPlan`, runs it with `runPreparedDense`, and generates a Python module from the
   resulting `PreparedPlan` — reading only checker-produced positional data and source-name
   bindings, never source syntax or axis UIDs. It also confirms an affine-shift fixture
   (`Y[i] := A[i + 1]`) is rejected by a typed codegen error before any Python is emitted for it.
   Every named codegen entry first validates the prepared binding sidecar against the raw plan's
   exact publication slots; raw IR cannot authenticate the user-visible names themselves.
2. [`evalplan_smoke.py`](./evalplan_smoke.py) enables `jax_enable_x64`, reconstructs inputs and
   the independent Dense-computed expected output from the emitted `Float.toBits` payloads,
   AST-asserts the generated module contains a real `jnp.einsum("ab,b->a", ...)` call, and checks
   eager/`jax.jit` output is bit-identical to Dense and `jax.grad(sum(Y), W) == [[5], [5]]`.

### Run

From this directory:

```bash
./setup-python.sh
./run-evalplan.sh
```

`run-evalplan.sh` reuses the same experiment Python environment as `run.sh` (`.cache/python/bin/python`,
or `PYTHON` if set) and never invokes `run.sh` or clones/builds upstream `lean4-mlir`. It builds
`LeanNCD` (through Elan, from LeanNCD's own Lean 4.30.0 project root) before `lake env lean --run`,
so the generator never runs against stale `.olean`s, then generates
`.cache/generated_evalplan_smoke.py` and runs `evalplan_smoke.py` on it.

### Scope

This spike is a feasibility check that one real, scan-free Tensor Logic program can travel
through LeanNCD's own checked-plan boundary and execute as generated JAX. It is not a production
JAX backend: it accepts only projection-only affine `einsum` contractions in `f64`/`reference64`
mode, with no context positions, scans, or nonlinearities. See
`docs/superpowers/plans/2026-08-10-jax-evalplan-smoke.md` for the full exit criteria and
non-goals.

## Ordered affine reference and full corpus

`EvalPlanCodegen.lean`'s explicit `affineReference` mode emits static safe-index/mask tables built
from the same coordinate primitives as Dense. `evalplan_affine_runtime.py` interprets those tables
with ordered factor, reduction, and term folds; it does not use `einsum` or a tree reduction.

`run-evalplan-affine.sh` checks 20 curated fixtures eagerly and under JIT. These supply semantics
outside the generated grammar: negative-coordinate invalidity, zero-coefficient rows, zero extents,
empty factors, and empty terms. `run-evalplan-affine-corpus.sh` explicitly builds `LeanNCD`, `Tests`, and the
non-default `JaxExperiment` target, then generates and checks every corpus case and every
materialized output. The generated `.cache/` artifacts remain ignored.

Measured on the JAX CPU backend, 2026-08-10 and re-measured 2026-08-12:

- 3,832 source/eager cases, zero mismatches (both runs; normal-range inputs only — see
  the subnormal/signed-zero limit below);
- 45 distinct generated feature masks and 65 JIT checks (45 representatives + 20 curated);
- 3,424,195-byte generated module (identical size on both runs; the runner records `artifact_bytes`
  only, so this is consistent with a deterministic generator but does not prove it — no digest is kept);
- of that module, the `safe_index`/`mask` literals are 571,459 bytes (~17%) across 28,106 literals;
  the rest is per-case keys, input tensors, and expected outputs, ~894 bytes per case;
- 13.482 s / 685.535 s / 7.317 s generation, eager, JIT+curated on 2026-08-10;
- 13.214 s / 661.263 s / 7.056 s on 2026-08-12.

The 2026-08-12 re-measurement followed a driver repair. Wave F F1 added `TermPlan.contextPos` and
`AssignPlan.contextShape`, and the hand-built plan literals in `EvalPlanAffineSmoke.lean` were
positional anonymous constructors of the pre-F1 arity, so they stopped compiling. Because the drivers
belong to no Lake target (`JaxExperiment` globs only `EvalPlanCodegen`), `lake build` stayed green and
both affine runners were silently unrunnable. The literals now use named-field syntax like the
`KernelDenseTest` fixtures, which survives field additions. **Run the runners after any change to
`Eval/Plan` types — a green `lake build` does not typecheck these drivers.**

**Current driver status (2026-09-04, whole-branch review finding 3).** `lake env lean` elaborates
`EvalPlanSmoke.lean`, `ScalingProbe.lean`, `EvalPlanAffineCorpus.lean`, and — as of this fix —
`EvalPlanAffineSmoke.lean`; the corpus driver's five stale `CheckedPlanStepEvidence.plan`
projections were repaired by Task 4.5 and it regenerates the 3,832-case module at exactly
3,424,195 bytes, unchanged. `EvalPlanAffineSmoke.lean` did NOT elaborate between Slice 5.4 and this
fix: `renderAffinePlanNamed`/`renderAffinePlanPositional` became `Except`-returning when the located
Iverson rejection landed, and the driver still string-appended their results (two `HAppend String
(Except JaxCodegenError String)` failures). Both call sites now unwrap the `Except` and throw
`IO.userError` naming the fixture and the `affineReference` boundary (named `PreparedPlan` /
positional `CheckedEvalPlan`) that rejected — a render rejection aborts generation loudly instead of
being stringified into the emitted Python. Re-measured 2026-09-04: `lake env lean --run
EvalPlanAffineSmoke.lean <out>` regenerates the 20-fixture curated module (11,509 bytes; the Python
verifier leg was not re-run, so no new eager/JIT timings are recorded here). `BridgeSmoke.lean`
needs the upstream `Jax` module fetched by `run.sh` and does not elaborate standalone.

### Binary32 (`orderedReference32`, slice F32-JAX)

`affineReference` also runs binary32 plans, under its own label `orderedReference32`. The scope is
the same as binary64's: assign-only and context-free, with the rejection table below unchanged.
`einsumOnly` stays binary64-only and refuses every `.float32` plan: the codegen doors with
`unsupportedStorageKind .float32`, the validator door (`validateEinsum`) with `invalidCandidate`: a spike (`papers/f32_jax_spike_results.md`) found `jnp.einsum`
diverging from the Lean binary32 left fold by up to 122 ULP on a 64x64 contraction, identically
eager and under `jit`, while the affine tables matched exactly.

`evalplan_affine_runtime.py` is one parametrized implementation: `dtype` defaults to `jnp.float64`,
so every binary64 caller is unchanged; `_require_dtype` checks the inputs and never casts; the
float32 path runs with `jax_enable_x64` disabled (asserted in `evalplan_affine_smoke32.py`). The
binary64 curated module is `cmp`-identical (11,509 bytes) and the 3,832-case corpus still gives zero
mismatches at 3,424,195 bytes (normal-range inputs only, like every claim here; see the
subnormal/signed-zero limit below).

`EvalPlanAffineSmoke32.lean` and `evalplan_affine_smoke32.py` exercise four routes: the named
`PreparedPlan` route (7 fixtures: the 6 spike fixtures plus `termSum64`), the corpus route (all
`enumPrograms` cases retagged `.typedTensor .f32`), the standalone-assign route (8 fixtures,
including `f32Identity` and the zero-pad `f32Pad`) and the positional-plan route (2 fixtures,
`f32ProductChain` and `f32ReductionGraph`). Measured, stride 1 with JIT on every case
(`./run-evalplan-affine32.sh 1 1`; Python 3.13.12, JAX/JAXlib 0.10.0, NumPy 2.5.2, CPU):

- 3,849 fixtures (3,832 corpus + 7 named + 8 standalone-assign + 2 positional), 11,746 eager/JIT
  output checks (5,873 each), bit-identical to the Lean binary32 reference except the pinned
  `KNOWN_DIVERGENT` positions of `f32Identity` (`[1, 2]`, the subnormal/signed-zero limit below);
- 3,657,456-byte generated module; 530.2 s eager and 191.0 s JIT.

**This is structural coverage, not proof of fold-order fidelity.** The generator's inputs are the
integers 1-4, whose products and sums are exact in binary32, so a reassociated fold would agree on
all 3,832 corpus cases. Fold-order fidelity rests on the magnitude and cancellation fixtures
(`reduction64`, `termSum64`, `factorProduct3`, `contraction64x64`); the Python mutation cycles P1-P3
are killed by `reduction64`, `termSum64` and `factorProduct3` respectively.

JIT is checked on every case, unlike the binary64 corpus runner's 45 representatives. The measured
cost (about 3 minutes of JIT) is acceptable and a per-case claim is strictly stronger than a sample.
`./run-evalplan-affine32.sh [STRIDE [JIT_STRIDE]]` keeps both knobs: the defaults are `100 1` (a
39-case corpus sample, every case JIT-checked), and `1 1` is the full-corpus run above.

### What this backend REJECTS (Task 4.5, 2026-09-03)

The checked Dense backend admits several semantics this experimental JAX backend implements no
rendering for. They are now rejected with a located, typed `JaxCodegenError` **before** any Python is
emitted, any candidate is built, or any `ExecutionEvidence` label exists — never silently stamped with a reference
label (`orderedReference64`/`orderedReference32`):

| Assignment feature | Dense checked plan | JAX render | JAX candidate evidence |
|---|---|---|---|
| `f64`, real algebra, plain read | required | required | required |
| `f64`, tropical max/min (`admittedAlgebraMax`/`Min`) | required | forbidden (`unsupportedAlgebra`) | forbidden |
| `bool` destination, Boolean algebra | required | forbidden (`unsupportedDestDType`) | forbidden |
| `bool` source into a real destination | required | forbidden (`unsupportedSourceDType`) | forbidden |
| unary read (`ReadPlan.unary`) | required | `affineReference`: required (opt-in `allowUnary`, tolerance-compared, unchecked domain precondition); `einsumOnly` and the candidate conversions: forbidden (`unaryFactor`) | forbidden |
| Iverson factor | required | forbidden (`iversonFactor`, original all-factor index) | forbidden |
| contextful assignment (`AssignPlan.contextShape` non-empty) | required | forbidden (`unsupportedContext`) | forbidden |
| zero-padded read shorter than its iteration basis | required | `einsumOnly` forbidden (`labelExtentMismatch`); `affineReference` required | einsum forbidden, affine required |

Every row holds unchanged under a `.float32` plan for `affineReference` (same located errors), and
under `einsumOnly` every binary32 plan is refused first with `unsupportedStorageKind .float32`.

**There is no JAX Boolean execution and none is planned here** — this is a fail-loud support
boundary, not a semantic gap in the checked backend, which executes all eight rows correctly. The
last row is the only mode-SPLIT one (whole-branch review): see the label-extent paragraph below.

The contextful row is the Task 4.5 CLOSURE finding, and it is about a runtime parameter rather than
a dtype or an algebra: a checked assignment with a non-empty `contextShape` denotes a FAMILY of
results indexed by a context coordinate (`runDenseAssignAt` binds it at every term's `contextPos`),
and neither lowering here has a kernel parameter for that coordinate. Neither noticed its absence
either: `einsumOnly` treated a context position as an ordinary subscript label and CONTRACTED it
away (`Y[] := X[l]` rendered as `a->`), and `affineReference` emitted its terms with no
`context_pos` key at all — while Dense returns `10` at context `0` and `20` at context `1` for the
same plan. Both were being stamped with evidence, `orderedReference64` for the affine one. **JAX
assignment kernels support only CONTEXT-FREE assignments**; adding a context parameter or runtime
support was explicitly not attempted. Note that `checkPlan` already refuses a contextful TOP-LEVEL
step (`topLevelContextNotEmpty`), so this reaches the backend only through the standalone
`CheckedAssignPlan` entries — which is exactly where the gate now sits.

Three further restrictions are `einsumOnly`-ONLY, and are structural rather than about dtypes or
algebra: a term must have at least one factor (`emptyTerm`), its iteration rank must fit the 26-letter
subscript alphabet (`rankTooLarge`), and every iteration position must be covered by some factor's
projection (`uncoveredPosition`). `affineReference` renders all three shapes, which is why the curated
affine corpus can and does contain empty-factor/empty-term cases. `Executable.lean`'s `validateEinsum`
mirrors exactly these preconditions (`einsumTermRenderable`, sharing `einsumLabelLimit` with
`labelTable` through a `#guard`), so an einsum candidate is certified only if `lowerAssign` really
renders it — before the Task 4.5 re-review it could be certified and then rejected at emission.

A fourth `einsumOnly`-only restriction is about MEANING rather than structure: label extents. A
zero-padded read whose source extent is smaller than its own iteration extent (say
`sourceShape = #[2]` against `iterationShape = #[3]`) is a checked, Dense-executable assignment whose
einsum string, `a->a`, is perfectly well-formed — but `jnp.einsum` takes label `a`'s extent from the
operand, so the rendered kernel returns two elements where Dense returns three (the third the zero
pad). It is a DIFFERENT function. The Task 4.5 re-review closed this at the evidence boundary only
(`validateEinsum` refused to certify it while `lowerAssign` still rendered it — the one deliberate
validator/emitter disagreement); the whole-branch review ruled that insufficient, because
`lowerAssign` is itself a public entry and `generateForward`/the plan renderers reach emitted Python
through it. Both sides now reject, through the SAME recomputation: `Executable.lean`'s public,
located `einsumTermLabelExtents` decides, `validateEinsum` consumes its `Bool` view, and this
emitter maps its `.mismatch` verdict to the located `labelExtentMismatch` (node, term, factor, source
dimension, iteration position, and both extents). `affineReference` renders and validates it either
way — its tables carry the zero-pad mask explicitly — so the restriction stays einsum-scoped.

The gate is `LeanNCD.Eval.Plan.checkJaxAssignSupport`, applied in declared order (destination dtype,
algebra, context shape, then factors in original term/factor order: source dtype before unary) — the
same coarse order `checkAssign` itself uses, which is why the context check sits between the algebra
and the factors. A contextful assignment with a Boolean destination or a tropical algebra therefore
reports THAT, and one with a Boolean source or a unary read reports the CONTEXT; both directions are
pinned by fixtures. `contextPos`/`contextShape` disagreement is never conflated with the context
rejection — `checkAssign` rejects it first as `contextProjectionMismatch`, so no `CheckedAssignPlan`
for it exists to reach the gate. Signature-context
ownership follows the completed spike's selection (GO B,
`papers/jax_signature_evidence_ownership_spike_results.md`): a STANDALONE entry — `lowerAssign`,
`renderAffineAssign`, `buildAssignFixture`, both candidate conversions, both candidate validators,
`validateAndConstructKernel` — takes one explicit complete `Array TensorSignature` and treats it as
its semantic authority, re-running `checkAssign` under it (a structurally incompatible table is
rejected as `invalidSignatureContext`). A PLAN-level entry — `lowerPlan`, `generateForward`, both
plan renderers, `generateNamed`, `lowerCheckPlanToCandidate` — takes no such parameter and derives
`PreparedPlan.plan.raw.tensorSigs`, so no caller can substitute a same-shape all-real table.
Rejections at a plan level carry the real outer step index, not `0`.

Generated cases cover nonzero bias, non-unit/multi-axis coefficient rows, multiple factors/terms,
reduction domains, multiple graph nodes, and internal reads. Curated cases uniquely supply
negative-coordinate invalidity, zero-coefficient rows, zero extents, empty factors, and empty terms.
These are empirical results for the measured CPU platform, not a proof about every XLA
platform, and they hold for normal-range values only, in both precisions. XLA's CPU backend
flushes subnormal operands and results of arithmetic to zero (eager and under `jax.jit`;
`--xla_cpu_enable_fast_math=false` does not change it), and under `jax.jit` it simplifies the
reduction seed `+0 + x` to `x`, so a `-0` survives where the ordered left fold returns `+0`.
Neither corpus contains a subnormal or a `-0` input, which is why neither run sees it; the
binary32 standalone fixture `f32Identity` (`[+0, -0, least subnormal]`) does, and
`evalplan_affine_smoke32.py` pins that divergence exactly (`KNOWN_DIVERGENT`) instead of
excluding it. `orderedReference64` and `orderedReference32` carry the same limit. It is not
fixed: that would mean defeating XLA's flush-to-zero and its algebraic simplifier, and no XLA
flag that does either was found.

### Scatter steps (ordered mode, JAX scatter slice)

A prepared plan whose steps include a `.scatter` (a source statement with a non-plain LHS slot such
as `Y[2*i]`, `Y[a+b]`, `Y[i, =2]`, and every B5 multi-writer group, whose writers are scatters into
private slots feeding one collector assignment) now renders and runs under `affineReference`, in both
precisions. `renderScatterNode` emits the compute half's tables (a SOURCE-shaped tensor) plus
`"kind": "scatter"`, `"dest_shape"` and a static `"dest_flat_index"` table: one destination offset per
source coordinate, in the dense worker's `allCoords` order, computed in Lean by the worker's own
`applyAffine`/`inBoundsPerDim`/`flatIndex`. The runtime (`_run_scatter_node`) starts the destination at
`reduceId` (`0`) and adds the source values one at a time in table order (`fori_loop`), the exact left
fold of `runDenseScatter`/`runDenseScatter32`, so colliding float writes are BIT-identical to Lean.
An out-of-range placement is unreachable for a checked plan (`scatterRangeViolation`); the codegen
still refuses it (`scatterPlacementOutOfRange`) rather than emit the index.

**Fast mode** (`scatter_mode="fast"` on `run_named` / `run_plan_positional`; default `"ordered"`, an
unknown value raises `ValueError`) swaps ONLY the placement fold for one vectorised
`zeros.at[dest_flat_index].add(source, mode="promise_in_bounds")` (XLA scatter-add) over the same static
table and the same ordered compute half, so it needs no Lean change and works under `jax.jit` and
`jax.grad`. Exactness: it is bit-identical to ordered mode and to Lean when no two source coordinates
share a destination cell (all collision-free fixtures, both precisions, eager and jit, including signed
zero: `0 + (-0.0)` is `+0.0`), or when every partial sum is exactly representable. With colliding
writes XLA's accumulation order is unspecified, so the result is only guaranteed within rounding; the
verifier compares fixtures whose scatter TABLE collides (`multi`, `contract`; the `b5Overlap` writers
write private slots and its collision is in the ordered collector assign) within a scale-relative
`RTOL` (`1e-12` binary64, `1e-5` binary32), and against random well-conditioned inputs (fast vs ordered).
On this CPU backend those fixtures (including the `1e16`/`2^24` ordering pins) and 200 random trials per
fixture were nonetheless bit-identical to ordered/Lean (XLA CPU applies updates in order): an
observation that proves nothing about other backends or a future XLA. The static table is range-checked at trace time (`ValueError`), because JAX's default
for a scatter would silently DROP an out-of-range update; with the check, `promise_in_bounds` is a fact.
The verifier tells the folds apart by counting `scatter-add` primitives in the traced program (default
and ordered: none; fast: one per non-empty scatter node), since results alone cannot.

| Still refused | Where |
| --- | --- |
| scatter under `einsumOnly` | `unsupportedStep` (einsum is a gather; no scatter form) |
| scatter in the evidence path | `lowerCheckPlanToCandidate` / `JaxExecutableWellFormed`: `unsupportedStep` (no `ExecutionEvidence` for a scatter) |
| tropical, Boolean, contextful or unary-read scatter | the compute-half gate (`checkJaxScatterSupport`): `unsupportedAlgebra` etc. |
| scan under `einsumOnly`, the candidate conversions or the evidence path | `unsupportedStep` (`affineReference` itself lowers single-axis real scans; see "Scan (affineReference)") |

Run: `./run-evalplan-scatter.sh` (generates `EvalPlanScatterSmoke.lean`'s binary64 + binary32
fixtures, then `evalplan_scatter_smoke.py float64|float32`: eager and jit bit comparison, a pinned
collision-order case, a signed-zero case, a gradient). Mutation record for the Python half:
`mutation_python_manifest.py` (`papers/semantics/jax_scatter_mutations_python.json`).

### Pointwise and axiswise steps (tolerance-compared, JAX pointwise slice)

A prepared plan whose steps include a `.pointwise` (`relu`, `sigmoid`, `tanh`, `gelu`, `leakyrelu`) or an
`.axiswise` (`softmax`, `normalize`, `l2normalize`, with or without a `where` mask) step now renders and
runs under `affineReference`, in both precisions; with the assignments JAX already ran, a single-layer
transformer (attention, causal softmax, `normalize`, relu feed-forward) runs end to end. `renderPointwiseNode`
emits `"kind": "pointwise"`, the source and destination slots, the shape and the function name;
`renderAxiswiseNode` adds `"axis_pos"` and, for a MASKED step only, a static `"include"` table: one `0`/`1`
per coordinate in row-major order, decided in Lean by the dense worker's own predicate
(`axiswiseIncludedPredicate`, a delegation to the worker's mask handling), so the runtime never sees a
predicate. A mask the worker refuses is unreachable for a checked plan (`maskWidthMismatch`); the codegen
still refuses it (`axiswiseIncludeRefused`) rather than emit an unmasked table. There is no separate support
gate: `checkPlan` already ran the nonlinearity checkers under the plan's own signature table, and these
steps have no compute half to grade.

The runtime mirrors `LeanNCD.Eval.Nonlin` operation for operation: relu is `where(0 <= x, x, 0)` (Lean's
`max 0 x`, so `relu(NaN)` is `+0`; never `jnp.maximum`), row sums and the softmax row maximum are sequential
left folds (`fori_loop` over the row axis, vectorised across rows) over the UNMASKED entries, an all-masked
row and a zero-sum or all-zero row are exactly zero, and the binary32 constants are the exact bit patterns of
Lean's. Unlike scatter, the result is NOT bit-identical to Lean: `exp`, `tanh` and `pow` come from XLA, not
from Lean's libm, so the verifier compares within `rtol`/`atol` (`1e-12`/`1e-14` binary64, `1e-5`/`1e-6`
binary32), measured, not guessed. On this CPU backend `normalize`, `l2normalize`, `sigmoid`, `leakyrelu` and
`relu` were bit-identical to Lean in both precisions and so was binary32 `softmax`; binary64 `softmax`,
`tanh` and `gelu` differed by at most a few ulps (binary32 `gelu`: up to `2.5e-5` relative, at outputs near
`4e-3`, which the absolute tolerance covers). An observation about this backend, not a guarantee. Relu is bit-exact
in eager mode only: the surface language emits an assignment copy before a pointwise step and XLA drops
that copy's `+0` seed under `jax.jit` (the pitfall above), so a jit run can flip the sign of a zero.

| Still refused | Where |
| --- | --- |
| pointwise or axiswise under `einsumOnly` | `unsupportedStep` (no einsum form) |
| pointwise or axiswise in the evidence path | `lowerCheckPlanToCandidate` / `JaxExecutableWellFormed`: `unsupportedStep` (no `ExecutionEvidence`) |
| an inline unary read (`sqrt`, `exp`, `log`, `sin`, `cos`, reciprocal `/`) under `einsumOnly`, the candidate conversions or the evidence path | the assignment gate's default (`checkJaxAssignSupport`): `unaryFactor`; only `affineReference` assignment rendering opts in (`allowUnary`), and scatter's compute half stays refused |

**Unary reads (`affineReference` only).** An inline unary read renders as a `"unary"` key on its factor record, and the runtime applies the function AFTER the zero-pad gather (`_apply_unary` in `evalplan_affine_runtime.py`), as Dense does: an out-of-bounds `exp` read is `exp(0) = 1`, and a zero-extent source gives the same. The result is compared within the nonlinearity tolerances, not bit for bit.

**Domain errors are an unchecked precondition (decision B1, 2026-11-04).** Lean rejects `log` of `v <= 0`, `sqrt` of `v < 0` and reciprocal of `0` with a typed unary-domain error. This backend lowers to plain `jnp` ops, checks nothing, and promises nothing on such inputs (neither NaN nor an error): it agrees with Lean only where Lean returns ok. Do not read "NaN on bad input" into it. Lean's `relu(NaN)` is `+0` and `exp(log 0) = exp(-inf) = 0` is finite, so a violation can come out as an ordinary-looking number. Lean-error inputs are out of contract and are excluded from the differential comparison; the Lean side of the boundary is pinned by `domainPins` in `EvalPlanNonlinSmoke.lean` (`log(0.0)`, `log(-1.0)`, `sqrt(-4.0)` and `recip(0.0)` are typed errors in Dense, binary64 and binary32). The motivating use is a LayerNorm with `eps` (`sqrt(v + eps)`, then division): its `sqrt` argument is at least `eps` and its divisor is non-zero by construction (fixture `unary_ln`). Fixtures: `unary_exp_oob`, `unary_ops`, `unary_mix`, `unary_red`, `unary_ln`, `unary_empty`.

Run: `./run-evalplan-nonlin.sh` (generates `EvalPlanNonlinSmoke.lean`'s binary64 + binary32 fixtures, then
`evalplan_nonlin_smoke.py float64|float32`: 34 binary64 and 26 binary32 fixtures (22 + 22 before the scan
slice; the added ones are listed under "Scan (affineReference)" below), eager and jit, including the
single-layer transformer with every materialized output compared (and the same layer with a real RMSNorm,
`transformer_rms`: 20 plan nodes, 4 unary factors, with a unit-mean-square pin on the norm outputs that Lean/JAX
agreement alone would not catch), a pinned reduction-order case, rows that
pin the softmax maximum, relu over a NaN, unknown function names refused, a `jit(grad)` finite check, and the
six unary-read fixtures above). Mutation records:
`papers/semantics/jax_nonlin_mutations_post.json` (Lean render, `mutation-manifest.sh`) and
`papers/semantics/jax_nonlin_mutations_python.json` (runtime and verifier, `mutation_python_manifest.py`,
which takes a per-entry `verifier`).

### Scan (affineReference)

A prepared plan with a `.scan` step runs under `affineReference` (both precisions at the Lean level; the
fixtures below say which are exercised) through `jax.lax.scan` over the step axis. Scope: ONE scan axis
(`historyExtents.size == 1`) and real (zero-initialised) states. The shared gate is `checkJaxScanSupport`
(with `jaxScanSingleAxis`) in `LeanNCD/Eval/Plan/Executable.lean`; its step-block assignments go through the
assign gate's private `allowContext` opt-in, because the outer gate still refuses contextful assigns. The
emitter is `renderScanNode` in `EvalPlanCodegen.lean`; the record contract it emits (one scan record per
`.scan` node) is in that function's doc comment, which is the source of truth. The runtime is
`_run_scan_node` in `evalplan_affine_runtime.py`: the base block runs once outside the scan, the carry is the
complete state tensors, and step-major stacked affine tables are closed over and indexed by the traced step
counter. Stacked tables are as large as an unrolled program's; the gain is one traced body, so trace and
compile size do not grow with the layer count.

Refused, each with a located error: a multi-axis scan (`scanMultiAxis` at the gate, `unsupportedScanAxes` at
the emitter), a tropical or otherwise non-real state (`scanNonRealState` / `unsupportedScanState`), a Boolean
scratch tensor inside a scan (`unsupportedDestDType`), a state write outside the complete state
(`scanWriteOutOfRange`), a step-block context position other than `#[0]` (`scanContextPos`), and two
coordinates of one write landing on one offset (`scanWriteCollision`; the runtime scatter `.at[idx].set` is
unspecified for duplicates). An Iverson (predicate) factor inside a scan block assignment passes the gate and is
refused by the emitter with `iversonFactor`, located by the outer node index with block-relative term and factor
indices, exactly as for an outer assignment; no test pins the scan case. `einsumOnly`, both candidate
conversions and the evidence path still refuse a scan with `unsupportedStep`.

Fixtures (in `run-evalplan-nonlin.sh`'s differential): `transformer_scan` / `transformer_scan32`, a two-layer
STANDARD pre-norm transformer as a scan over the layer axis with untied per-layer weights and gains
(per layer: RMSNorm with gain `G1[l, m]`, attention scaled by `Sc[]` with a causal mask, residual add, RMSNorm
with gain `G2[l, m]`, gelu MLP, residual add), and
`transformer_unrolled` / `transformer_unrolled32`, the same model as two flat layers. The unrolled pair is the
oracle: scan H layers 1 and 2 equal unrolled H1 and H2 bit for bit on CPU in binary64 (eager and jit) and in
binary32 jit; the binary32 EAGER layer 2 comparison allows rtol 2.4e-7, atol 0 (between 2 and 4 ulps; observed maximum absolute difference 2.4e-7; see the deviation in section 11 of the record). Eight donor scans from `Eval.Plan.ScanCompileTest` (list `scanSurvey64`, binary64
only, flag `linear_ok`) are listed in `papers/semantics/jax_scan_fixture_survey.md`. Slice record:
`papers/semantics/jax_scan_record.md`.

`transformer_head` / `transformer_head32` append a head to the two-layer scan: a final RMSNorm with gain `Gf[m]` of the residual stream
`H[q, m, 2]` (`Ssf`, `Vef`, `Sdf`, `Hf[q, m] := H[q, m, 2] / Sdf[q] · Gf[m]`; nothing is added back), an unembedding `Logits[q, v] := W_U[v, m] · Hf[q, m]` over a vocabulary axis of
extent 5 (differs from every other extent), and a softmax over `v`. The head is written in the same program as
the scan: `finalizeScans` classifies a scan-dependent statement by role. A statement that does not feed the
recurrence (here `Ssf[q] := H[q, m, 2] · H[q, m, 2] · Inv[m]` and everything after it) is a post-scan consumer and becomes a
plain node AFTER the scan node, where the iteration axis is an ordinary axis; a statement that feeds the
recurrence (every statement of the layer body) is a per-step intermediate. The
verifier recomputes the head (norm, `Logits` and the vocabulary softmax) in numpy from the fixture's inputs and
Lean's `H` slice 2 (not from the head's own outputs), and checks that the head's inputs and `H` are bit-identical
to `transformer_scan`'s. Details and the mutation checks: the "Head fixture" section of `papers/semantics/jax_scan_record.md`.

`transformer_window`, `transformer_strict` and `transformer_sink` (each with a `32` sibling) are the standard scan with only the
mask changed and q = s = 5, so the causal mask above is the mask of `transformer_scan` / `transformer_head`, not of every transformer fixture:
`transformer_window` masks with `s ≤ q ∧ q - s < 2` (subtraction in a predicate term, conjunction), `transformer_strict` with `s < q` (query row 0
attends nothing: a fully masked row inside the scan, expected all zero), `transformer_sink` with `s ≤ q ∧ (s = 0 ∨ q - s < 2)`
(disjunction, equality with a constant). Each is checked against a numpy model whose mask is written from the English definition, and by a receptive-field
pin (rows unreachable from a perturbed position stay bitwise identical on the eager runtime). Observed numbers and the mutation table: section 12 of
`papers/semantics/jax_scan_record.md`.

`transformer_mqa` / `transformer_mqa32` are the standard two-layer scan with multi-query attention: the key and value projections drop the head axis
(`K[s, k] := W_K[l, k, m] · N1[s, m]`, `V[s, k] := W_V[l, k, m] · N1[s, m]`, weights `[l, k, m]`), only `Q[q, h, k]` keeps `h`, so the head-free `K` is
broadcast into the masked softmax and the head-free `V` back into the attention output, inside the scan (the standard fixtures carry `h` on Q, K and V; this is the
one that does not). Same mask, extents and every other input as `transformer_scan`. Checked against a numpy model with head-free K and V, and against the
STANDARD multi-head plan run on the same weights replicated over `h` (bitwise equal on the eager runtime). Observed numbers, the binary32 headroom, why the
head-free weights are head 1's slices, and the mutation table: section 13 of `papers/semantics/jax_scan_record.md`.

`scan_postrole` / `scan_postrole32` run six post-scan statements with the scan axis as an ordinary axis through
both backends (`iter l = 4`, `S[j,l] = X[j]·G[j]^l`): a sum over `l` against an external tensor
(`Ysum := S[j,2]·V[l]`), a free read of the state summed over `l` (`Yfree := S[j,l]·V[l]`, NOT the per-step
reading), a read-out table, a broadcast, a masked softmax over `l`, and a count over `l` (`Zc := S[j,2]·M[l]`).
The bridge has no lowering for predicate (Iverson) factors (`iversonFactor`), so the count uses an input mask
`M`; the Iverson form is pinned on the Lean backends in `Eval.Plan.ScanCompileTest`. Every pin recomputes from
the fixture's inputs in numpy, never from a view's own outputs.

Run: `./run-evalplan-nonlin.sh` (and `./run-evalplan-scatter.sh`) first. The generated `.cache` modules go
stale, and a Python mutation manifest runs against whatever is there. Then, from the repository root:
`leanncd/experiments/jax_bridge/mutation_python_manifest.py papers/semantics/jax_scan_mutations_python.json`
(runtime, 6 entries) and `leanncd/scripts/mutation-manifest.sh leanncd papers/semantics/jax_scan_mutations_post.json`
(Lean gate and emitter, 11 entries; add `--check` first to validate the pins without building).

## Scaling probe

`run-scaling-probe.sh` measures one mid-sized contraction — `Y[i] := Σⱼ W[i,j]·x[j]`, `i,j` both
ranging over 64, a 4,096-coordinate iteration domain, 1,024× the corpus's maximum of four — against
native `jnp.einsum` computing the same contraction. Not a permanent test: this converts
`papers/jax_evalplan_architecture.md` §5.4's affine-table scaling risk from code inspection into a
measurement (§7.6 row 2).

Measured on the JAX CPU backend, 2026-08-13 (JAX/JAXlib 0.10.0):

- 177,547-byte generated artifact from this one fixture — about 5% of the entire 3,832-case corpus's
  3,424,195 bytes;
- 34 µs affine-table JIT steady-state call (median of 20) versus 7 µs for native `jnp.einsum`, about
  4.9× slower — measured with `.block_until_ready()` inside the timed region, since unblocked JAX
  dispatch understates completion time;
- 340 ms / 15 ms first-call (eager) times for the affine path and native `jnp.einsum` respectively —
  both pay real XLA compilation on first call (`jax.lax.fori_loop`/`jax.vmap` compile their bodies
  even outside an outer `jax.jit`), so this gap overstates the steady-state one.

## Verified environment and commands

The completed smoke plan was verified on 2026-08-10 with:

- Lean 4.30.0 (`d024af099ca4bf2c86f649261ebf59565dc8c622`);
- Python 3.13.5;
- JAX/JAXlib 0.10.0;
- NumPy 2.5.2; and
- the JAX CPU backend.

The final validation commands were:

```bash
cd leanncd/experiments/jax_bridge
./run-evalplan.sh
./run-evalplan-affine.sh
./run-evalplan-affine-corpus.sh
./run.sh

cd ../..
"$HOME/.elan/bin/lake" build
```

All four experiment runners passed, and the complete Lean build finished with 8,642 jobs.

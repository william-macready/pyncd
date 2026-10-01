# F32-JAX feasibility spike results

Per `papers/f32_evalplan.md` §1.4 point 4: before any F32-JAX implementation plan is written, this
spike checks whether `jnp.float32` execution can agree BIT-FOR-BIT with the Lean checked binary32
left-fold reference, for the context-free assignment-only fragment the existing experimental JAX
bridge (`experiments/jax_bridge`) already covers. This is a disposable feasibility spike, not a
slice: no production file is changed permanently, and no implementation plan is written here.

## 1. Baseline

- Branch: `worktree-f32-jax-spike`.
- Base commit (local `main`, fast-forwarded): `ce0faf433a9873574587e8b06b4b173331f1bf57` (`ce0faf4`,
  "Merge branch 'worktree-f32c-scans-plan': F32-C native binary32 scans").
- `"$HOME/.elan/bin/lake" build` (full default build), measured BEFORE any edit: exit 0, **8,673
  jobs**.
- `"$HOME/.elan/bin/lake" build JaxExperiment`, measured BEFORE any edit: exit 0, **8,514 jobs**
  (confirms fixtures 22-25 — the gate's own pinned f32-rejecting behavior — pass at baseline).
- Mathlib cache: warm (per the prepared worktree); every build above replayed in single-digit-to-
  low-double-digit seconds with no module recompiling from source, consistent with a 100%-synced
  `.lake`.
- Python: a fresh, isolated install via `experiments/jax_bridge/setup-python.sh` (no prior
  `.cache/python` existed in this worktree) — **Python 3.13.12, JAX 0.10.0, jaxlib 0.10.0, NumPy
  2.5.2**, CPU backend (`jax.devices() == [CpuDevice(id=0)]`). Same pinned versions
  `requirements-cpu.txt` already specifies for every other `jax_bridge` driver.

## 2. Harness mutations and their restoration

The brief's framing — that `EvalPlanCodegen.lean`'s single-line `requireFloat64Plan` gate is "the
ONLY thing standing between this backend and an f32 plan" — is **incomplete**, discovered by running
the actual code rather than assuming it. There are two INDEPENDENT gates, and both had to be
temporarily inverted to reach real rendering for an f32 assignment:

1. **The plan-level storage gate** (`experiments/jax_bridge/EvalPlanCodegen.lean`,
   `requireFloat64Plan`) — exactly as the brief describes, and the only gate that lives in the
   experimental, non-default module.
2. **The per-node JAX support policy** (`LeanNCD/Eval/Plan/Executable.lean`, private
   `jaxAssignSupported`, reached through the public `checkJaxAssignSupport`) — a PRODUCTION file,
   independent of the storage gate, that separately requires every assignment's destination AND
   source dtype to be exactly `.f64`. This is pinned by a default-build test
   (`test/Eval/Plan/ExecutableTest.lean`, "f32 slice Task 5, fixture 1": `destinationDType 7 2 .f32`)
   — i.e. production code and a default-build test deliberately assert f32 rejection here too, as a
   second, independent door. Without inverting this gate as well, `generateNamed` fails immediately
   with `unsupportedDestDType`/`unsupportedSourceDType` for every real fixture, before either
   rendering mode is reached at all.

Both gates, and the two pinned-fixture blocks that assert their f32-rejecting behavior, were
restored to their exact original text (confirmed by `git diff --exit-code -- leanncd`, see below)
before this results file was committed. This deviates from the letter of "do not touch any
production `LeanNCD/` file" in a temporary, fully-reverted, build-confirmed way — flagged here
explicitly for the orchestrating session's review, following this repo's own precedent
(`papers/jax_signature_evidence_ownership_spike_results.md`'s Task 1 harness, which similarly
mutated a production checked-source gate for the duration of that spike and reverted it the same
way).

| Mutation | File | Observed effect while active | Restore confirmed |
|---|---|---|---|
| `requireFloat64Plan`: accept `.float32` alongside `.float64` | `experiments/jax_bridge/EvalPlanCodegen.lean` | All 7 call sites (`lowerPlan`, `generateForward`, `renderInputConstants`, `renderAffinePlanPositional`, `renderAffinePlanNamed`, `generateNamed`, `lowerCheckPlanToCandidate`) stop rejecting an f32 `CheckedEvalPlan` at the plan level | Yes — exact text restored; see below |
| Fixtures 22-25 (the gate's own f32-rejection pins) temporarily wrapped in a block comment | same file | Without this, the shim above makes every one of these `#guard`s reduce to `false` (e.g. `codegenErr (generateForward p) == some (.unsupportedStorageKind .float32)` becomes `none == some ..`), which is a compile-time failure, not a silent pass | Yes — comment wrapper removed, fixtures restored verbatim |
| `jaxAssignSupported`: accept `.f32` alongside `.f64` at both the destination-dtype and source-dtype checks, and accept `admittedAlgebraF32` alongside `admittedAlgebra` | `LeanNCD/Eval/Plan/Executable.lean` | Per-node JAX support policy stops rejecting an f32 assignment's destination/source/algebra, so `checkJaxAssignSupport` (called by both `EvalPlanCodegen` rendering paths) no longer blocks an f32 node | Yes — exact text restored; see below |
| "f32 slice Task 5, fixture 1" (the pinned `destinationDType 7 2 .f32` rejection, 5 `#guard`s) temporarily wrapped in a block comment | `test/Eval/Plan/ExecutableTest.lean` | Without this, the shim above makes this block's `#guard`s fail to compile the same way | Yes — comment wrapper removed, fixtures restored verbatim |

Restore confirmation (after both shims reverted and both fixture blocks un-wrapped):

- `/opt/homebrew/bin/git diff --exit-code -- leanncd`: **exit 0** (byte-identical to `ce0faf4`).
- `/opt/homebrew/bin/git status --porcelain=v1 --untracked-files=all` (after deleting the scratch
  driver/runner below): empty.
- `"$HOME/.elan/bin/lake" build JaxExperiment Eval.Plan.ExecutableTest`: exit 0, **8,515 jobs**
  (fixtures 22-25 and the `ExecutableTest` f32-rejection fixture both pass again).
- `"$HOME/.elan/bin/lake" build` (full default build): exit 0, **8,673 jobs** — identical job count
  to the pre-edit baseline.

## 3. Spike harness (disposable, deleted after use)

Two scratch files were written, used, and then deleted — never committed:

- `experiments/jax_bridge/F32Spike.lean`: compiled each fixture's `tensor f32` TL source through
  `compileToScheduled` → `InputSignature.ofDenseInputs32ForDecls` → `prepareEvalPlan` →
  `runPreparedDense32` (the Lean binary32 reference, mirroring `Adapter32Test.prepare32`), then
  called `generateNamed .einsumOnly` and `generateNamed .affineReference` (through the two shims
  above) to get both modes' generated Python for the SAME prepared plan. It rendered its own
  disposable `Float32.toBits`/`UInt32`-bit Python literal helper (`pyUInt32ListLit`/
  `pyTensorEntry32`) rather than touching the f64-only production renderer, per the brief.
- `experiments/jax_bridge/.cache/f32_spike_runner.py`: loaded the generated fixtures, reconstructed
  inputs from `UInt32` bits into `jnp.float32` arrays, ran `einsumOnly`'s generated `forward(inputs)`
  function (`exec`'d with `jnp` in scope) and a disposable `affineReference` f32 runtime (a float32,
  no-x64 port of `evalplan_affine_runtime.py`'s ordered `fori_loop`/`vmap` folds — ported rather than
  reusing the committed module because that module hardcodes `jnp.float64` and asserts
  `jax_enable_x64`), eager and under `jax.jit`, and compared bits exactly. **`jax_enable_x64` was
  never enabled in this process** — asserted at the top of the runner — so this is genuine binary32
  execution throughout, not a narrowed binary64 run.

Both files were deleted once the results below were extracted; the only path this spike adds to
`git status` is this results document.

## 4. Fixtures and results

All six fixtures are single-assignment `tensor f32` TL programs. "Lean ref" is
`runPreparedDense32`'s exact `Float32.toBits` output — the ground truth every column is checked
against. Both rendering modes were generated from the SAME `PreparedPlan` per fixture, so a
mismatch is attributable to the mode's execution, not to a different plan.

| # | Fixture | Construction | einsum eager | einsum jit | affine eager | affine jit |
|---|---|---|---|---|---|---|
| 1 | `baseline` | `axis i:2, j:1; tensor f32 W(i,j), x(j), b(i), Y(i); Y[i] := W[i,j]·x[j] + b[i]`. `W=[2.0,3.0]` shape `[2,1]`, `x=[5.0]`, `b=[1.0,1.0]`. Harness/bit-roundtrip sanity check (same shape as `EvalPlanSmoke.affineProg`). | MATCH | MATCH | MATCH | MATCH |
| 2 | `reduction64` | `axis k:64; tensor f32 A(k), B(k), Y(); Y[] := A[k]·B[k]`. `A = [2^24, 1.0×62, -2^24]`, `B = [1.0]×64` — the proven binary32 cancellation trap (`Adapter32Test` fixture 8, extended from extent 3 to 64): a strict left fold lands on exactly `0.0`. | MATCH | MATCH | MATCH | MATCH |
| 3 | `termSum4` | `axis i:4; tensor f32 A(i),B(i),E(i),D(i),Y(i); Y[i] := A[i] + B[i] + E[i] + D[i]`, constant per `i`: `A=2^24, B=1, E=1, D=-2^24`. Same cancellation trap spread across 4 SEPARATE terms (not one reduction) — a strict left fold gives `0`; grouping `(A+D)+(B+E)` first gives `2`. | MATCH | MATCH | MATCH | MATCH |
| 4 | `factorProduct3` | `axis i:2, j:8; tensor f32 A(i,j), B(i,j), E(j), Y(i); Y[i] := A[i,j]·B[i,j]·E[j]`. Generic irregular decimals (`A[n]=n·0.0137+0.41`, `B[n]=n·0.0091+1.07`, `E[j]=±(j·0.273+0.53)`), reduced over `j`. | **MISMATCH** | **MISMATCH** | MATCH | MATCH |
| 5 | `mixedMagnitude` | `axis k:16; tensor f32 A(k), Y(); Y[] := A[k]`. `A` alternates `10000.0`/`0.0001` across 16 elements — 8 orders of magnitude in one reduction. | MATCH | MATCH | MATCH | MATCH |
| 6 | `contraction64x64` | `axis i:64, j:64; tensor f32 W(i,j), x(j), Y(i); Y[i] := W[i,j]·x[j]`. `W[n]=n·0.00031+0.17` (4,096 values), `x[n]=±(n·0.013+0.2)` — same scale as `run-scaling-probe.sh`, varied (not all-ones) data. | **MISMATCH** | **MISMATCH** | MATCH | MATCH |

Mismatch detail (hex/ULP; "ULP" is a spacing-based approximation, `|actual-expected| / np.spacing(expected)`, reported with sign):

**Fixture 4 (`factorProduct3`), expected (Lean reference) bits `[3207259276, 3210427557]`:**

- `einsum` eager AND jit (byte-identical to each other): bits `[3207259274, 3210427556]`, ULP
  distance `[-2.0, -1.0]`.
- `affine` eager and jit: bits `[3207259276, 3210427557]` — exact match.

**Fixture 6 (`contraction64x64`), 64 output elements:**

- `einsum` eager and jit (byte-identical to each other) diverge from the Lean reference at ALL 64
  positions except index 37 (ULP 0 there by coincidence); ULP distances range from **-1 to -122**
  (e.g. index 0: expected bits `3181742441`, actual `3181742432`, ULP `-9.0`; index 49 — the largest
  divergence observed: expected `3203953222`, actual `3203953344`, ULP `-122.0`).
- `affine` eager and jit: exact match at all 64 positions.

For both mismatching fixtures, **eager and `jax.jit` produce byte-identical (wrong) results** — the
divergence is not a `jax.jit`-specific fusion artifact; it is baked into `jnp.einsum`'s own
reduction/contraction lowering on this CPU backend regardless of execution mode, even with
`optimize=False` (the generated code already passes this — `opt_einsum`'s path selection is a
different knob from XLA's own per-operand reduction strategy). Fixture 2 (`reduction64`, a 64-length
two-factor dot product using the SAME `2^24` cancellation trap as fixture 3) matched under
`einsumOnly` — XLA evidently lowers a plain full 1D reduction (`"a,a->"`) on this small size to a
strictly sequential accumulation that happens to agree with the left fold, whereas the row-wise
64×64 matrix-vector contraction (`"ij,j->i"`) and the 3-operand product-then-reduce (`"ij,ij,j->i"`)
do not. Divergence is real but NOT uniform across einsum shapes — exactly the kind of shape/kernel-
dependent behavior the brief anticipated as the risk.

`affineReference` matched bit-for-bit on all 6 fixtures × both exec modes (12/12), including both
fixtures that broke `einsumOnly`. This is unsurprising given its design (`evalplan_affine_runtime.py`
/ this spike's f32 port use explicit `jax.lax.fori_loop`/`jax.vmap` ordered folds, never `jnp.einsum`
or a tree reduction), but it had not previously been measured under genuine binary32 (only f64).

## 5. Verdict: **GO, restricted to `affineReference`; NO-GO for `einsumOnly`**

Bit-exact binary32 JAX agreement with the Lean checked left-fold reference IS attainable for this
backend's covered fragment (context-free assignment-only), but **only through the `affineReference`
rendering mode**. `einsumOnly` — the mode that emits a real `jnp.einsum` call — disagreed with the
Lean reference on 2 of 6 fixtures (both involving a nontrivial multi-element reduction and/or a
3-operand product), with divergence up to 122 ULP on the 64×64 contraction, identically under eager
and `jax.jit`. This confirms the brief's stated risk precisely: XLA's own reduction-order/fusion
choice for `jnp.einsum` differs from the checked backend's strict left fold once the contraction is
large or multi-operand enough for XLA to choose a different algorithm, even with `optimize=False`.

## 6. Design implication for F32-JAX

**If F32-JAX is scoped to `affineReference` only**, its plan can mirror F32-B/C/D's exact-match
evidence-label pattern directly: an `orderedReference32`-style label asserting bit-for-bit agreement
with the Lean binary32 left fold, exactly as `orderedReference64` does today, with no tolerance
machinery needed. This spike's 12/12 result (6 fixtures × eager/jit) is a reasonable, if not
exhaustive, basis for that claim; a real plan should still widen the corpus (more shapes/magnitudes)
before committing to a zero-sorry exact-match label, the same way the existing `affineReference`
corpus (3,832 f64 cases) now backs the f64 claim.

**If F32-JAX is also expected to cover `einsumOnly`** (e.g. because a future consumer wants a real
`jnp.einsum` call rather than static lookup tables, for performance or interop reasons), it CANNOT
reuse an exact-match evidence label for that mode. The two fixtures that diverged here were not
contrived edge cases — a 3-operand product-then-reduce and an ordinary 64×64 matrix-vector
contraction are exactly the shapes a real workload would use — so this is not a tail risk to note and
move past. A plan covering `einsumOnly` would need either: (a) a SEPARATE, weaker evidence label
(e.g. `orderedReference32WithinTolerance`, parametrized by a ULP or relative-error bound, observed
here to need at least ~122 ULP of headroom for a 64-wide reduction — likely more at larger scale) and
a defined comparison procedure, with `einsumOnly` candidates routed to that label while
`affineReference` candidates keep the exact one; or (b) restricting `einsumOnly`'s f32 admission to
shapes verified not to trigger XLA's divergent path (brittle, re-litigated per shape/platform/XLA
version, and not recommended). Given `affineReference` already measures ~5× slower than native
`jnp.einsum` on the one mid-sized contraction probed (`run-scaling-probe.sh`, binary64), a future plan
should state explicitly which of these two costs — the performance gap, or giving up exact-match
evidence for `einsumOnly` — F32-JAX's consumer actually needs it to pay, rather than defaulting to
`affineReference` alone.

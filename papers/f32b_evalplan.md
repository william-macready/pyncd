# Native binary32 unary factors and nonlinearities (slice F32-B)

**Status: IMPLEMENTATION PLAN — authored 2026-09-23, not started.** No Lean source file has been
changed by this plan. It is the first follow-on to the completed f32 slice
([`f32_evalplan.md`](f32_evalplan.md), "F32-A" below), and item 1 of that plan's §1.3 deferred list
and §1.4 recommended order. Read [`f32b_evalplan_handoff.md`](f32b_evalplan_handoff.md) before
executing it.

Read §1.1 before anything else. It fixes what an `f32` nonlinearity *means* here and records one
measured fact about the platform maths library that §1.3 of F32-A did not anticipate. That fact
shapes every numerical fixture in this plan, and it is the part most likely to be misread from a
summary.

## 1. Decision and slice boundary

### 1.1 The semantic decision

F32-A §1.1 fixed the contract: an `f32` signature means IEEE-754 binary32 storage and an
independently rounded binary32 result at every primitive operation. It never means running the
binary64 worker and rounding only the output. This slice carries that contract unchanged into the
three operation families F32-A rejected:

- **inline unary factors:** `log`, `exp`, `sin`, `cos`, `sqrt`, and `recip` on a read;
- **the five pointwise nonlinearities:** `relu`, `sigmoid`, `tanh`, `gelu`, `leakyrelu`;
- **the three axiswise row algorithms:** `softmax`, `normalize`, `l2normalize`, masked or not.

Concretely:

1. **Same operation tree, native primitives.** Each binary32 function evaluates the *same* formula,
   with the same association and the same fold orders, as its binary64 counterpart in
   `Eval/Nonlin.lean`. Every primitive in it is a native `Float32` operation. Examples:
   `sigmoid x = 1 / (1 + exp(-x))`, and `gelu`'s cube is `Float32.pow x 3` because `geluT`'s
   `x^3` elaborates to `Float.pow x 3.0` (verified, §8). The two carriers share one written
   formula (§3.1), so they cannot drift apart.
2. **Constants are exact binary32 bit patterns.** They are never binary64 constants narrowed at
   use. For `gelu` these are `0x3f4c422a` (√(2/π)) and `0x3d372713` (0.044715). For
   `leakyrelu` it is `0x3c23d70a` (0.01). Each equals both the nearest binary32 to its decimal
   literal and the narrowing of the binary64 literal (both computed, §8).
3. **Transcendentals are the platform's binary32 libm routines.** These are `expf`, `logf`,
   `sinf`, `cosf`, `tanhf`, `sqrtf`, and `powf`, which Lean 4.30 exposes as `Float32.exp` and so
   on (`@[extern "expf"]` etc. in `Init/Data/Float32.lean`). `recip` is native binary32 division,
   `1 / x`. No `Float32` reciprocal extern exists, and none is needed.
4. **The domain rules are the binary64 ones.** `log` rejects `v ≤ 0`, `sqrt` rejects `v < 0`, and
   `recip` rejects `v == 0`. Each comparison is IEEE binary32 comparison. So `sqrt(-0) = -0` is
   admitted, `log(NaN)` passes through as NaN, and `recip` rejects both zeros. The same verdict at
   every boundary value is itself a fixture (Task 1 fixture 1.6).

**The measured fact that constrains the fixtures.** On the authoring platform
(`arm64-apple-darwin`, macOS 26.6.2 system libm), the binary32 routines are *not* correctly
rounded. Computing the same primitive in binary64 and narrowing once *is* correctly rounded,
except for double-rounding cases with probability about 2⁻²⁹. Over 1,813,754 binary32 inputs in
[2⁻⁴, 2⁴) (every 37th bit pattern), native and binary64-then-narrow disagreed this often:

| Primitive | `exp` | `log` | `sin` | `cos` | `tanh` | `sqrt` | `recip` (`1/x`) |
|---|---:|---:|---:|---:|---:|---:|---:|
| Disagreements | 10,955 | 265 | 31,283 | 16,528 | 27,882 | **0** | **0** |

`sqrt` and division are correctly rounded in both carriers. The zero counts match the known result
that double rounding is harmless for +, −, ×, ÷, and √ when the wider precision has at least
2p+2 bits; binary64 has 53 ≥ 2·24+2. Three consequences follow, and the plan is built around them:

- **Composites are where binary32 is observable, and portably so.** In `sigmoid`, `gelu`,
  `leakyrelu`, `softmax`, `normalize`, and `l2normalize`, the difference from widen-compute-narrow
  comes from rounding the *intermediate* +, ×, and ÷ results in binary32. IEEE-754 fixes those
  roundings exactly. Every native-versus-narrowed composite discriminator below was chosen so
  that each libm step it contains has a true result within at most 0.018 binary32 ulp of a
  representable value (§2.6). A libm with error below about 0.48 ulp there must return the same
  value. The one fold-order row has a worst margin of 0.062. So these fixtures should not depend
  on the platform libm.
- **A lone transcendental is observable only through the libm's own rounding error.** It follows
  that no portable value fixture can tell native `expf` from correctly rounded
  binary64-then-narrow. Such fixtures are therefore *witness* fixtures (§3.6). They are relational:
  the implementation must equal the native routine. They also check a precondition: at least one
  lane must be one where native and narrowed binary64 differ on the running platform. If an OS
  update makes the libm correctly rounded on all four lanes, the fixture fails loudly and names
  that cause; it does not pass vacuously.
- **For `sqrt` and `recip`, native and binary64-then-narrow are the same function**, so no value
  fixture can distinguish them. What pins native use there is the code (`Float32.sqrt`,
  `Float32.ofBits 0x3f800000 / v`) and the fixed bits of correctly rounded results.

**Why native rather than per-primitive binary64-then-narrow.** Narrowing a *single* binary64
primitive gives a correctly rounded binary32 primitive. Under the letter of F32-A §1.1 that is
arguably still "an independently rounded binary32 result at that operation", and it is more
accurate and more portable than `expf`. This plan nevertheless uses native routines, for three
reasons:

- F32-A §1.3 names native `Float32.log/exp/sin/cos/sqrt` as this slice's content;
- binary32 frameworks (XLA, PyTorch) evaluate native binary32 transcendentals, which matters for
  F32-JAX;
- the per-primitive-narrowing path invites the fused widen-the-whole-formula implementation, which
  *is* false f32 and which the composite fixtures reject.

This is a real design choice, not a settled fact. It is recorded as open question Q1 (§9). If the
user chooses correctly rounded binary32 transcendentals instead, only the `exp`/`tanh`/`pow`
fields of §3.1's binary32 record and the `exp`/`log`/`sin`/`cos` arms of §3.2's `applyChecked32`
change. The witness fixtures
then invert, and every composite fixture keeps its values.

### 1.2 Exact admitted fragment

The storage rules, graph homogeneity, Boolean-tag rules, and every F32-A admission stay as they
are. This slice adds only the following, and only in a `.float32` graph:

| Construct | Source form (all tensors `tensor f32`) | Checked form | Worker |
|---|---|---|---|
| inline unary factor, top-level plain assignment | `Y[i] := exp(A[i + 1])`, `X[i] / Z[i]` (`recip`) | `ReadPlan.unary := some op` under `checkAssignF32` | `runDenseAssignAt32` via `float32Ops.applyUnary` |
| pointwise nonlinearity, top-level plain assignment | `H[i] := sigmoid(W[i, j] · x[j])` | `.assign` (internal f32 slot) then `.pointwise` | `runDensePointwise32` via `runDensePlan32` |
| axiswise nonlinearity (optional mask), top-level plain assignment | `A[q, s.] := softmax(where s ≤ q)(Q[q, d] · K[s, d])` | `.assign` then `.axiswise` | `runDenseAxiswise32` via `runDensePlan32` |
| raw checked plans | hand-built `RawEvalPlan` with `.f32` signatures | `checkPlan` dispatches `checkPointwiseF32`/`checkAxiswiseF32` by storage kind | same |

Every slot a binary32 nonlinearity reads or writes must be `.f32`. A Boolean slot is still rejected
at a nonlinearity, as in binary64 (`dtypeNotAdmitted`). A predicate destination still cannot carry a
nonlinearity (`checkPredicateOutput`). Inline unary factors may appear in any term of a plain
assignment, with or without a nonlinearity on the same statement. The F32-A attention example
`softmax(where s ≤ q)(Q[q, d] · K[s, d])` runs natively in binary32 once every tensor it names is
declared `tensor f32` (Task 4 fixture 4.5).

### 1.3 Explicitly deferred — unchanged from F32-A §1.3

This slice does **not** admit any of the following. Each stays rejected by its existing F32-A
diagnostic:

- **F32-C:** every scan form, including a nonlinearity or unary factor inside a scan `base`/`recur`
  block, and scan-local scatter. Still `unsupportedDtype "{nm}: f32 scan"` at Step 0c and
  `f32UnsupportedStep i .scan` at `checkPlan`.
- **F32-D:** top-level scatter, including one whose RHS carries a unary factor or a nonlinearity.
  Still `"{nm}: f32 scatter"` and `f32UnsupportedStep i .scatter`.
- **F32-E:** mixed-precision conversions. There are none, by the single-real-precision invariant.
- **F32-JAX:** the plan-level `.float64` gate at all eight JAX doors is unchanged, and an f32 plan
  never reaches a per-step check there.
- **Complex-A/B.**
- **Two items F32-A §1.4 offered but this plan deliberately excludes:** the optional `f64` source
  keyword and the default flip (open question Q2, §9).

This plan's audit surfaced two existing F32-C obligations. They are named here so that F32-C's
plan cannot miss them:

- `compileScan`'s nonlinear base/step arms still publish their result slot as a literal `.f64`;
- the scan nonlinear block steps are Float-checked (`checkPlanBlock` admits only `.float64`).

Both are unreachable for binary32 today, because Step 0c rejects every f32 scan (§3.5, table B).

### 1.4 Contracts inherited without change

These carry over from F32-A unchanged:

- storage kind is derived from the complete signature table;
- evidence records the kind it was checked for;
- every carrier-specific door checks that kind *first*;
- Boolean is a tag over the graph's real carrier;
- the legacy evaluator permanently refuses any f32 schedule, so there is no legacy oracle for any
  fixture in this plan;
- the 3,832-case and 17-case differential corpora are binary64 reference gates, not f32 evidence.

## 2. Re-derived current boundary

Everything below was measured on `main` at `6a53ce7` by reading the named functions or running
compiled probes through `check-snippet.sh`. None of it is copied from F32-A's §2, which describes
the tree before F32-A.

### 2.1 Source admission and compiler emission

- `checkF32Stmt` (`Eval/Plan/Compile.lean`) rejects, in order within a plain assignment:
  - a pointwise or axiswise nonlinearity, as `"{nm}: f32 nonlinearity"`;
  - then any `.unaryFn` factor, as `"{nm}: f32 unary factor {ti}:{fi}"`, where `fi` is the
    original all-factor index.

  Scatter is `"{nm}: f32 scatter"`. `f32CapabilityCheck` rejects `.scan`/`.scanPre` as
  `"{nm}: f32 scan"`.

  Observed: the f32 attention program above prepares to
  `.capability (.unsupportedDtype "A: f32 nonlinearity")`, and `E[i] := exp(A[i + 1])` to
  `"E: f32 unary factor 0:0"`.
- The unary lowering in `residualizeAssignment` is carrier-free. It emits the same `ReadPlan` with
  `unary := some op`.
- **The plain-assignment nonlinear arms in `prepareEvalPlan` Step D hard-code binary64.** Both the
  `.pointwise` and `.axiswise` arms:
  - push their internal preactivation signature and their published signature as literal
    `dtype := .f64`;
  - emit the preactivation `.assign assignPlan` with `residualizeAssignment`'s default
    `algebraForAgg agg`, which is the binary64 table.

  That is six sites. The `.identity` arm and the scatter arm already use
  `dtypeOfDecl (declEnv[nm]?)` and `algebraForDest`. The `.pointwise` arm's own comment ("Always
  `f64`: a predicate destination can never reach this branch") stops being true as soon as an f32
  destination can reach it.
- `compileScan`'s nonlinear arms use `destDtype` for the preactivation slot and `algebraForDest`
  for its algebra (nonlinearity plan Task 4.4). Its result slots are still literal `.f64`, which
  its comment records was a deliberate, mutation-tested choice.

### 2.2 Checked layer

- `checkAssignCore` (`Check.lean`) rejects an inline unary read in a `.float32` graph as
  `PlanError.unaryNotAdmittedForDtype ti fi .f32`. This is the last clause of the factor loop, at
  the original all-factor index. `KernelCheckTest` fixture 4 pins index 1 behind an Iverson.
- `checkNonlinIO` (`Plan/Nonlin.lean`) requires `destSig.dtype == .f64` and
  `srcSig.dtype == .f64` literally. `CheckedPointwisePlan` and `CheckedAxiswisePlan` store only
  `raw`, with no storage kind, under `private mk ::`.
- `checkPlan` (`EvalPlan.lean`) runs a capability pass in a `.float32` graph. That pass refuses
  `.pointwise`, `.axiswise`, `.scatter`, and `.scan` as `f32UnsupportedStep ni kind`, at the
  original outer index. `localCheck` dispatches `.assign` by storage kind, and `.pointwise`/
  `.axiswise` always to the Float checkers.
- `checkPlanBlock` (`Block.lean`) derives a block's kind first and admits only `.float64`
  (`storageKindNotAdmitted`). It calls `checkPointwise`/`checkAxiswise` and the Float workers.

### 2.3 Workers

- `runDensePointwise`/`runDenseAxiswise` take `Array DenseTensor` and carry **no storage-kind
  guard**. Their first statement is `validateNonlinSource`, and they delegate to
  `PointwiseFn.apply`/`AxiswiseFn.applyCore`. They are reachable from `runDensePlan`, which guards
  `.float64` at plan level, and from `runDenseBlock`, where Float evidence is guaranteed by
  `checkPlanBlock`. Once a binary32 checker exists, their lack of a guard would be an F32-A §3.5
  family member (§3.5).
- `runDensePlan32` (`Dense32.lean`) refuses every non-`.assign` evidence arm as
  `storageKindMismatch .float32 .float64`.
- `float32Ops.applyUnary` (`Dense.lean`, private) refuses unconditionally with
  `unaryNotAdmittedForStorage .float32 op slot`. This is unreachable, because `checkAssignF32`
  rejects unary first. `floatOps.applyUnary` wraps `UnaryOp.applyChecked`, carrying the payload
  `unaryDomain dop (Float.toBits x) slot`.
- `gatherFactorWith` applies `unary` *after* the out-of-bounds zero-pad, and is shared by both
  carriers. So a padded read contributes `f(0)`, and its domain payload is the padded `+0`.

### 2.4 The math module

`Eval/Nonlin.lean` is the single home of every nonlinearity formula for *both* backends. The legacy
`applyNonlin` and the checked workers call the same `PointwiseFn.apply`/`AxiswiseFn.applyCore`. It
is entirely `Float`-typed:

- `reluT`: `max 0.0 x`. Lean's `maxOfLe` returns `y` when `x ≤ y`, so `relu(-0) = -0` and
  `relu(NaN) = +0`, observed.
- `sigmoidT`: `1.0 / (1.0 + Float.exp (-x))`.
- `tanhT`: `Float.tanh`.
- `geluT`: `0.5 * x * (1.0 + Float.tanh (0.7978845608028654 * (x + 0.044715 * x^3)))`, where `x^3`
  is `Float.pow x 3.0`, verified with `pp.explicit`.
- `leakyReluT`: `if x ≥ 0.0 then x else 0.01 * x`.
- `perRowCore`/`rowsAlong` (private) implement the row engine.
- `softmaxT` excludes masked entries from both the row maximum and the sum, and sends an
  all-masked row to zeros.
- `normalizeT`/`l2normalizeT` send a zero-sum row to zeros.

Every nonlinearity is total. There is no nonlinearity domain error in either carrier, so the only
domain-error surface in this slice is the unary factor.

### 2.5 Diagnostics and payloads

- `UnaryDomainOp` (`log`/`sqrt`/`recip`) and `UnaryOp.applyChecked : UnaryOp → Float → Except
  UnaryDomainOp Float` live in `Eval/Error.lean`.
- `PositionalInputError.unaryDomain (op) (valueBits : UInt64) (slot)` is the checked binary64
  payload. It uses a bit field because a `Float` field would break `DecidableEq`
  (`unary_factor_functions.md`).
- `PlanRunCause.execution` wraps it at the named adapter. `runPreparedDenseOf` preserves warnings
  there. Observed on the binary64 twin of Task 2 fixture 2.11: `.execution (.unaryDomain .log 0
  0)` with 1 warning.
- **A stale claim found here.** `AdapterTest.lean`'s comment says `PlanRunCause.execution` is
  "unreachable through the full runPreparedDense pipeline". Its Check 16 comment says the same, and
  so does `Adapter32Test.lean`'s fixture 7 preamble ("No `PlanRunCause.execution` fixture is
  claimed"). The reasoning is that pack's own validation rules out every `PositionalInputError`
  once pack succeeds. That is false already in binary64. A domain violation is a runtime value
  fact that pack cannot see: the binary64 twin above reaches `.execution (.unaryDomain .log 0 0)`
  after a successful pack. Check 16's `run_cmd` loop itself is sound, because its scan programs
  carry no unary factor; only the general prose is wrong. No fixture anywhere asserts the warnings
  of an `.execution` failure.

### 2.6 Native binary32 evidence and discriminating values

Every value below was observed from a compiled probe. "Narrowed" means computing in binary64 and
rounding the result once, which is exactly what widening a tensor, calling today's Float function,
and narrowing it produces. "Margin" is the distance of the binary64-computed true value of a libm
step from the nearest binary32, in binary32 ulps.

| Discriminator | Native binary32 bits | Narrowed binary64 bits | libm margins |
|---|---|---|---|
| `sigmoid` at `0.7f` (`1060320051`) and at `1058161516` | `1059786330`, `1059297860` | `1059786331`, `1059297859` | `exp`: 0.0069, 0.018 |
| `gelu` at `-1.1875` (`3214409728`) | `3188661568` | `3188661569` | `powf` exact (19³/16³); `tanh` 0.0135 |
| `leakyrelu` at `-1.25` (`3214934016`) | `3159149772` | `3159149773` | none (one ×) |
| `softmax` row `[0, 0, 2.5]` | `[1032873795, 1032873795, 1062987311]` | `[1032873796, 1032873796, 1062987311]` | `exp(-2.5)` 0.018, `exp(0)` exact |
| `normalize` row `[2²⁴, 1, 1]` | `[1065353216, 864026624, 864026624]` | `[1065353214, 864026622, 864026622]` | none |
| `l2normalize` row `[4097, 4097]` | `[1060439284, 1060439284]` | `[1060439283, 1060439283]` | `sqrtf` is correctly rounded |
| `normalize` along axis 1 of `[[2²⁴, 1], [1, 1]]` | `[1065353216, 864026624, 1056964608, 1056964608]` | `[1065353215, 864026623, 1056964608, 1056964608]` | none |
| masked causal softmax, 3×3 scores rows `[0, 0, 2.5]`, mask `s ≤ q` | `[1065353216, 0, 0, 1056964608, 1056964608, 0, 1032873795, 1032873795, 1062987311]` | same, with `…796, …796` in row 2 (observed end to end through the binary64 pipeline) | as `softmax` |

Order and masking discriminators:

- `softmax` over `[0, 0, 0.75, 2.5]` gives native left fold `[1031490512, 1031490512, 1040514973,
  1061115551]`. A right-fold sum gives `[1031490511, 1031490511, 1040514972, 1061115550]`, and
  narrowing agrees with native here. Its worst `exp` margin is 0.062. The row `[0, 0, 2.5]` does
  **not** separate fold orders (both folds give its native bits, observed), which is why it is not
  the fold-order fixture.
- `normalize [2²⁴, 1, 1]` separates fold orders too: its right fold equals the narrowed values.
- `softmax` over `[1000, 0, 2.5]` with position 0 masked gives `[0, 1033591688, 1064080527]`,
  against narrowed `[0, 1033591689, 1064080527]` (`exp(-2.5)` margin 0.018). If masked entries
  were admitted to the row maximum, every `exp` would underflow and the row would collapse to
  `[0, 0, 0]`, observed. An earlier candidate, `[1000, 2, 3]`, was rejected because its
  `exp(-1)` step has margin 0.307.
- An all-masked row is all `+0` for every axiswise function.

Semantic lanes, identical in both carriers:

- `relu(-0) = -0` (`2147483648`) and `relu(NaN) = +0`;
- `sigmoid(-0) = 0.5`, `tanh(-0) = -0`, `gelu(-0) = -0`, and `leakyrelu(-0) = -0`.

Portable unary lanes, where native equals narrowed and bits are correctly rounded or exact:

| Op | Inputs | Output bits |
|---|---|---|
| `log` | `[1, 2, 4, 8]` | `[0, 1060205080, 1068593688, 1074075026]` (margins ≤ 0.032) |
| `sqrt` | `[1, 2, 4, 8]` | `[1065353216, 1068827891, 1073741824, 1077216499]` |
| `recip` | `[1, 2, 4, 8]` | `[1065353216, 1056964608, 1048576000, 1040187392]` |
| `exp` | `[3.0, -2.5, -0.25, 0]` | `[1101049646, 1034427438, 1061642109, 1065353216]` (margins 0.018, 0.018, 0.041, exact) |

libm witness lanes, where native ≠ narrowed on this platform. Each is four binary32 inputs with
their native outputs, and all four lanes differ from narrowed by one ulp:

| Op | Input bits | Native output bits |
|---|---|---|
| `exp` | `1048801280, 1049583616, 1051496448, 1051680768` | `1067808354, 1068064150, 1068715284, 1068780010` |
| `log` | `1065353222, 1065353236, 1065353244, 1065353288` | `893386747, 908066803, 912261095, 923795415` |
| `sin` | `1048809472, 1048829952, 1048854528, 1048985600` | `1048714903, 1048734709, 1048758472, 1048885130` |
| `cos` | `1050177536, 1058869248, 1060933632, 1062293504` | `1064615103, 1062293444, 1061004150, 1060050850` |
| `tanh` | `1048600576, 1048842240, 1049923584, 1049960448` | `1048281192, 1048655277, 1049659241, 1049693157` |

Domain payload bits:

- `-4.0f` is `3229614080`, `-9.0f` is `3239051264`, and `-0` is `2147483648`.
- Over `[1, -4, -9, 4]`, `sqrt` stops at the first violation, `-4` (observed through `mapM` over
  `applyChecked32`).

### 2.7 Inherited F32-A gaps, re-derived

Each was re-checked against the tree rather than restated:

- `checkAssignCore`'s f32 source clause still reports `dtypeMismatch .f32 dt` with no slot
  locator. Unchanged here.
- `PlanStep.kind` still has no production caller: its only producer-side mention is its own
  definition and a doc comment.
- `runDensePlan32` still duplicates `runDensePlan`'s input-validation loop.
- `AdapterTest` fixture 21's guard-vs-`checkPreparedBindings` gap was recorded as deferred by
  F32-A §6.5.5. **Not re-derived here.** This plan neither touches nor relies on that fixture.

This plan closes none of these and relies on none of them. `runDensePlan32`'s refusing
`.pointwise`/`.axiswise` arms are the one inherited item this slice *does* change (Task 3).

## 3. Architecture

**How the Lean blocks in this plan are organized.** Every Lean block in this plan is one continuous
probe file, in document order. It imports `LeanNCD.Eval.Plan.Nonlin` from today's tree and
compiles beside it. Names that would collide with existing module definitions live in namespace
`F32BPlan`; the three genuinely new public names (`PointwiseFn.apply32`, `AxiswiseFn.applyCore32`,
`UnaryOp.applyChecked32`) keep their real names. The implementer transcribes each block into the
module named above it and drops the `F32BPlan` wrapper. §8 gives the extraction command and the
compile result.

### 3.1 One formula per function, two carriers (`Eval/Nonlin.lean`)

Add a **private** `NonlinScalarOps α` record with a binary64 and a binary32 instance. This mirrors
F32-A's private `ScalarKernelOps` in `Dense.lean`: the record is data passed to a formula, not a
typeclass. Write each formula once over the record, generalize the private `perRowCore` over the
carrier, and expose exactly two new public entries, `PointwiseFn.apply32` and
`AxiswiseFn.applyCore32`. The existing public Float entries keep their names and signatures, but
their bodies become the Float instantiation:

- `PointwiseFn.apply`, `AxiswiseFn.applyCore`, `AxiswiseFn.apply`, and `applyNonlin`;
- `reluT`, `sigmoidT`, `tanhT`, `geluT`, `leakyReluT`, `softmaxT`, `normalizeT`, and
  `l2normalizeT`.

Why generalize rather than add parallel Float32 functions: there are exactly two real call sites
per formula, the two carriers. The alternative is eight duplicated formula bodies whose operation
trees must agree by inspection. The cost is that the refactor passes through today's binary64
formulas. The shared Float code has no independent oracle, since the legacy and checked backends
and the scan-unroll oracle all call these same functions. That is why Task 1's first fixture is a
golden binary64 bit table captured from the **pre-refactor** tree (fixture 1.1, values in block 5
below, verified against today's functions).

```lean
import LeanNCD.Eval.Plan.Nonlin
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan

namespace F32BPlan

/-- One carrier's scalar runtime for the nonlinearity formulas: every scalar operation and
    constant the eight functions of `Eval/Nonlin.lean` use, and nothing else. -/
private structure NonlinScalarOps (α : Type) where
  zero : α
  one : α
  half : α
  three : α
  geluScale : α
  geluCubic : α
  leakSlope : α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  neg : α → α
  max : α → α → α
  le : α → α → Bool
  beq : α → α → Bool
  exp : α → α
  tanh : α → α
  sqrt : α → α
  pow : α → α → α

/-- Binary64: every constant is the literal today's formulas spell, so the Float instantiation is
    the current behavior verbatim (the `3` is the `OfNat Float 3` that `x^3` elaborates to). -/
private def floatNonlinOps : NonlinScalarOps Float :=
  { zero := 0.0, one := 1.0, half := 0.5, three := 3
  , geluScale := 0.7978845608028654, geluCubic := 0.044715, leakSlope := 0.01
  , add := fun a b => a + b, sub := fun a b => a - b, mul := fun a b => a * b
  , div := fun a b => a / b, neg := fun a => -a, max := fun a b => max a b
  , le := fun a b => decide (a ≤ b), beq := fun a b => a == b
  , exp := Float.exp, tanh := Float.tanh, sqrt := Float.sqrt, pow := fun a b => a ^ b }

/-- Binary32: every constant is an exact bit pattern, and every operation is a native `Float32`
    primitive (`expf`/`tanhf`/`sqrtf`/`powf` for the four transcendentals). -/
private def float32NonlinOps : NonlinScalarOps Float32 :=
  { zero := Float32.ofBits 0x00000000, one := Float32.ofBits 0x3f800000
  , half := Float32.ofBits 0x3f000000, three := Float32.ofBits 0x40400000
  , geluScale := Float32.ofBits 0x3f4c422a, geluCubic := Float32.ofBits 0x3d372713
  , leakSlope := Float32.ofBits 0x3c23d70a
  , add := fun a b => a + b, sub := fun a b => a - b, mul := fun a b => a * b
  , div := fun a b => a / b, neg := fun a => -a, max := fun a b => max a b
  , le := fun a b => decide (a ≤ b), beq := fun a b => a == b
  , exp := Float32.exp, tanh := Float32.tanh, sqrt := Float32.sqrt, pow := Float32.pow }

end F32BPlan
```

```lean
namespace F32BPlan

variable {α : Type}

/-- The five pointwise formulas, each written ONCE. Operation tree and association are exactly
    today's `reluT`/`sigmoidT`/`tanhT`/`geluT`/`leakyReluT` bodies. -/
private def pointwiseWith (o : NonlinScalarOps α) : PointwiseFn → α → α
  | .relu      => fun x => o.max o.zero x
  | .sigmoid   => fun x => o.div o.one (o.add o.one (o.exp (o.neg x)))
  | .tanh      => fun x => o.tanh x
  | .gelu      => fun x => o.mul (o.mul o.half x) (o.add o.one (o.tanh (o.mul o.geluScale
                    (o.add x (o.mul o.geluCubic (o.pow x o.three))))))
  | .leakyrelu => fun x => if o.le o.zero x then x else o.mul o.leakSlope x

private def softmaxRowWith (o : NonlinScalarOps α) (entries : List (α × Bool)) : List α :=
  let unmasked := entries.filterMap (fun (x, m) => if m then none else some x)
  let m := match unmasked with
    | []      => o.zero
    | x :: xs => xs.foldl (fun a b => o.max a b) x
  let es := entries.map (fun (x, masked) => if masked then o.zero else o.exp (o.sub x m))
  let s := es.foldl o.add o.zero
  (entries.zip es).map (fun ((_, masked), e) =>
    if masked || o.beq s o.zero then o.zero else o.div e s)

private def normalizeRowWith (o : NonlinScalarOps α) (entries : List (α × Bool)) : List α :=
  let s := entries.foldl (fun a (x, masked) => if masked then a else o.add a x) o.zero
  entries.map (fun (x, masked) => if masked || o.beq s o.zero then o.zero else o.div x s)

private def l2normalizeRowWith (o : NonlinScalarOps α) (entries : List (α × Bool)) : List α :=
  let s := o.sqrt (entries.foldl
    (fun a (x, masked) => if masked then a else o.add a (o.mul x x)) o.zero)
  entries.map (fun (x, masked) => if masked || o.beq s o.zero then o.zero else o.div x s)

private def axiswiseRowWith (o : NonlinScalarOps α) : AxiswiseFn → List (α × Bool) → List α
  | .softmax     => softmaxRowWith o
  | .normalize   => normalizeRowWith o
  | .l2normalize => l2normalizeRowWith o

/-- PROBE-ONLY copy of the module's existing private `rowsAlong`, which is shape-only and is reused
    unchanged; the module does not gain a second copy. -/
private def rowsAlong (axisPos : Nat) (shape : List Nat) : List (List (List Nat × Nat)) :=
  let coords := DenseTensor.allCoords shape
  let keyed := coords.map (fun c => (c.eraseIdx axisPos, c, DenseTensor.flatIdx shape c))
  let keys := (keyed.map (·.1)).foldl
    (fun acc k => if acc.contains k then acc else acc ++ [k]) []
  keys.map (fun k =>
    (keyed.filter (fun e => e.1 == k)).map (fun e => (e.2.1, e.2.2)))

/-- Today's `perRowCore`, generalized over the carrier. The element type is the only change; the
    unreachable `getD` default becomes the carrier's own zero. -/
private def perRowCoreWith (o : NonlinScalarOps α) (axisPos : Nat) (included? : List Nat → Bool)
    (f : List (α × Bool) → List α) (t : DenseTensorOf α) : DenseTensorOf α :=
  let rows := rowsAlong axisPos t.shape
  rows.foldl (fun acc row =>
    let entries : List (α × Bool) := row.map (fun (c, fi) =>
      let x := acc.data.getD fi o.zero
      (x, ! included? c))
    let ys := f entries
    ((row.zip ys).foldl (fun (cur : DenseTensorOf α) ((_, fi), y) =>
      ⟨cur.shape, cur.data.set! fi y⟩) acc))
    t

/-- The binary32 pointwise entry (new, public). -/
def _root_.LeanNCD.PointwiseFn.apply32 (pf : PointwiseFn) (t : DenseTensor32) : DenseTensor32 :=
  ⟨t.shape, t.data.map (pointwiseWith float32NonlinOps pf)⟩

/-- The binary32 axiswise entry (new, public): the same row engine and the same `included?`
    contract as `AxiswiseFn.applyCore`. There is deliberately no `AxiswiseFn.apply32` source-mask
    wrapper: the legacy evaluator never executes binary32. -/
def _root_.LeanNCD.AxiswiseFn.applyCore32 (fn : AxiswiseFn) (axisPos : Nat)
    (included? : List Nat → Bool) (t : DenseTensor32) : DenseTensor32 :=
  perRowCoreWith float32NonlinOps axisPos included? (axiswiseRowWith float32NonlinOps fn) t

/-- PROBE NAMES for the new bodies of the module's existing Float entries: `PointwiseFn.apply`
    becomes `applyFloat`'s body, `AxiswiseFn.applyCore` becomes `applyCoreFloat`'s, and the public
    `reluT` … `l2normalizeT` become one-line Float instantiations. -/
def applyFloat (pf : PointwiseFn) (t : DenseTensor) : DenseTensor :=
  ⟨t.shape, t.data.map (pointwiseWith floatNonlinOps pf)⟩

def applyCoreFloat (fn : AxiswiseFn) (axisPos : Nat) (included? : List Nat → Bool)
    (t : DenseTensor) : DenseTensor :=
  perRowCoreWith floatNonlinOps axisPos included? (axiswiseRowWith floatNonlinOps fn) t

end F32BPlan
```

`AxiswiseFn.apply` (the source-mask wrapper) and `resolveNonlin`/`applyNonlin` are unchanged apart
from calling the rewritten Float entries. Nothing in the legacy evaluator gains a binary32 path.

### 3.2 The binary32 domain home and its payload

`UnaryOp.applyChecked32` goes in `Eval/Error.lean`, directly beside `applyChecked`, so the domain
rules for both carriers are read together:

```lean
/-- The binary32 sibling of `UnaryOp.applyChecked`, beside it in `Eval/Error.lean`: the SAME
    domain predicates (`log` rejects `≤ 0`, `sqrt` rejects `< 0`, `recip` rejects `== 0`), each
    evaluated with IEEE binary32 comparison, and native `Float32` math. Reuses `UnaryDomainOp`. -/
def _root_.LeanNCD.UnaryOp.applyChecked32 :
    LeanNCD.UnaryOp → Float32 → Except LeanNCD.Eval.UnaryDomainOp Float32
  | .log,   v => if v ≤ Float32.ofBits 0x00000000 then .error .log else .ok (Float32.log v)
  | .sqrt,  v => if v < Float32.ofBits 0x00000000 then .error .sqrt else .ok (Float32.sqrt v)
  | .exp,   v => .ok (Float32.exp v)
  | .sin,   v => .ok (Float32.sin v)
  | .cos,   v => .ok (Float32.cos v)
  | .recip, v =>
      if v == Float32.ofBits 0x00000000 then .error .recip
      else .ok (Float32.ofBits 0x3f800000 / v)
```

`float32Ops.applyUnary` becomes
`(op.applyChecked32 x).mapError (fun dop => .unaryDomain32 dop x.toBits slot)`, mirroring
`floatOps.applyUnary` line for line.

**The payload.** Add one constructor, `PositionalInputError.unaryDomain32 (op : UnaryDomainOp)
(valueBits : UInt32) (slot : TensorSlot)`, directly after `unaryDomain`. `DecidableEq, BEq, Repr,
Inhabited` still derive. This was checked in a probe mirroring the constructor order: the first
constructor is inhabited, and `UnaryDomainOp` itself has no `Inhabited`. Two alternatives were
rejected:

- **Reuse `unaryDomain` with the bits zero-extended.** This is false. Binary32 `-4.0` is
  `0xC0800000`, and zero-extended that is a positive binary64 subnormal. The payload would name a
  value that was never gathered.
- **Widen `unaryDomain`'s field to `ScalarConst`.** This changes a live binary64 constructor's type,
  which ripples through `KernelDenseTest` and every consumer that matches on it. It gives
  `ScalarConst.bool` a meaningless domain-value inhabitant. And it buys generality for a complex
  carrier that does not exist yet. Complex-A will need two-component payloads anyway.

The resulting three-tier picture:

| Tier | binary64 | binary32 (this slice) |
|---|---|---|
| shared domain rule | `UnaryOp.applyChecked : Float → Except UnaryDomainOp Float` | `UnaryOp.applyChecked32 : Float32 → Except UnaryDomainOp Float32` (same `UnaryDomainOp`) |
| legacy evaluator | `EvalError.unaryDomain op value ctx` | n/a — any f32 schedule is `EvalError.unsupportedDtype` before evaluation |
| checked worker | `PositionalInputError.unaryDomain op (UInt64 bits) slot` | **`PositionalInputError.unaryDomain32 op (UInt32 bits) slot`** |
| named adapter | `PlanRunCause.execution (.unaryDomain …)`, warnings kept | `PlanRunCause.execution (.unaryDomain32 …)`, warnings kept |
| JAX | unary read rejected before evidence (`checkJaxAssignSupport`) | f32 plan rejected at plan level before any step |

Producers this slice retires. The constructors are **retained**, and none is deleted (F32-A's
rule):

- `PlanError.unaryNotAdmittedForDtype` becomes producer-less.
- `PositionalInputError.unaryNotAdmittedForStorage` becomes producer-less. A future carrier without
  unary math, such as Complex-A before its transcendentals, can revive it.
- The `CapabilityError.unsupportedDtype` payload shapes `"{nm}: f32 nonlinearity"` and
  `"{nm}: f32 unary factor {ti}:{fi}"` stop being produced. The constructor itself stays live for
  mixed storage, scan, and scatter, so `CapabilityError`'s 10 live / 16 / 6 producer-less count is
  **unchanged**.
- `PlanStepError.f32UnsupportedStep i .pointwise`/`.axiswise` stop being produced; `.scatter`/`.scan`
  stay live.

### 3.3 Checked nonlinearity evidence and workers (`Plan/Nonlin.lean`)

This repeats F32-A Task 2 and 3's assignment pattern for the two nonlinearity kinds:

- evidence records its storage kind;
- one private checker core is parameterized by kind, with `checkPointwise`/`checkAxiswise` kept
  exactly as today's `.float64` behavior and `checkPointwiseF32`/`checkAxiswiseF32` as siblings;
- every worker checks the kind as its **first** statement.

`checkNonlinIO` stays public as `checkNonlinIOCore .float64`. The existing `NonlinCheckTest` row
fixtures therefore keep compiling unchanged.

```lean
namespace F32BPlan

/-- Evidence gains the storage kind it was checked FOR, exactly as `CheckedAssignPlan` did. -/
structure CheckedPointwisePlan where private mk ::
  raw : RawPointwisePlan
  storageKind : LeanNCD.StorageKind
  deriving Repr

structure CheckedAxiswisePlan where private mk ::
  raw : RawAxiswisePlan
  storageKind : LeanNCD.StorageKind
  deriving Repr

/-- The one real dtype a nonlinearity slot may carry, per graph carrier. -/
private def nonlinDtypeFor : LeanNCD.StorageKind → ScalarDType
  | .float64 => .f64
  | .float32 => .f32

/-- Today's `checkNonlinIO` body with its two `.f64` literals replaced by `nonlinDtypeFor kind`.
    Public `checkNonlinIO` stays, as `checkNonlinIOCore .float64`. -/
private def checkNonlinIOCore (kind : LeanNCD.StorageKind) (sigs : Array TensorSignature)
    (sourceSlot destinationSlot : TensorSlot) (shape : Array Nat) :
    Except NonlinPlanError (TensorSignature × TensorSignature) := do
  let destSig ← match sigs[destinationSlot]? with
    | some s => pure s
    | none => throw (.slotOutOfRange destinationSlot sigs.size)
  let srcSig ← match sigs[sourceSlot]? with
    | some s => pure s
    | none => throw (.slotOutOfRange sourceSlot sigs.size)
  unless destSig.dtype == nonlinDtypeFor kind do
    throw (.dtypeNotAdmitted destinationSlot destSig.dtype)
  unless srcSig.dtype == nonlinDtypeFor kind do
    throw (.dtypeNotAdmitted sourceSlot srcSig.dtype)
  unless srcSig.dtype == destSig.dtype do
    throw (.dtypeMismatch destSig.dtype srcSig.dtype)
  unless srcSig.shape == shape do
    throw (.sourceShapeMismatch shape srcSig.shape)
  unless destSig.shape == shape do
    throw (.destinationShapeMismatch shape destSig.shape)
  return (srcSig, destSig)

private def checkPointwiseCore (kind : LeanNCD.StorageKind) (sigs : Array TensorSignature)
    (p : RawPointwisePlan) : Except NonlinPlanError CheckedPointwisePlan := do
  let _ ← checkNonlinIOCore kind sigs p.sourceSlot p.destinationSlot p.shape
  return CheckedPointwisePlan.mk p kind

def checkPointwise (sigs : Array TensorSignature) (p : RawPointwisePlan) :
    Except NonlinPlanError CheckedPointwisePlan :=
  checkPointwiseCore .float64 sigs p

def checkPointwiseF32 (sigs : Array TensorSignature) (p : RawPointwisePlan) :
    Except NonlinPlanError CheckedPointwisePlan :=
  checkPointwiseCore .float32 sigs p

private def checkAxiswiseCore (kind : LeanNCD.StorageKind) (sigs : Array TensorSignature)
    (a : RawAxiswisePlan) : Except NonlinPlanError CheckedAxiswisePlan := do
  let _ ← checkNonlinIOCore kind sigs a.sourceSlot a.destinationSlot a.shape
  unless a.axisPos < a.shape.size do
    throw (.axisPositionOutOfRange a.axisPos a.shape.size)
  match a.mask with
  | none => pure ()
  | some m => match m.affineWidths.find? (· != a.shape.size) with
      | some w => throw (.maskWidthMismatch a.shape.size w)
      | none => pure ()
  return CheckedAxiswisePlan.mk a kind

def checkAxiswise (sigs : Array TensorSignature) (a : RawAxiswisePlan) :
    Except NonlinPlanError CheckedAxiswisePlan :=
  checkAxiswiseCore .float64 sigs a

def checkAxiswiseF32 (sigs : Array TensorSignature) (a : RawAxiswisePlan) :
    Except NonlinPlanError CheckedAxiswisePlan :=
  checkAxiswiseCore .float32 sigs a

/-- Today's `validateNonlinSource`, generalized over the carrier. -/
private def validateNonlinSourceOf {α : Type} (sourceSlot : TensorSlot) (shape : Array Nat)
    (store : Array (DenseTensorOf α)) : Except PositionalInputError (DenseTensorOf α) := do
  match store[sourceSlot]? with
  | none => throw (.missingSlot sourceSlot store.size)
  | some d =>
      unless d.shape == shape.toList do
        throw (.shapeMismatch sourceSlot shape d.shape)
      unless d.data.size == shape.toList.foldl (· * ·) 1 do
        throw (.storageMismatch sourceSlot d.shape d.data.size)
      pure d

/-- Today's mask-width re-check and `included?` construction, lifted out of `runDenseAxiswise` so
    both axiswise workers share it rather than carrying two copies. -/
private def axiswiseIncluded (a : RawAxiswisePlan) :
    Except PositionalInputError (List Nat → Bool) := do
  match a.mask with
  | none => pure ()
  | some m => match m.affineWidths.find? (· != a.shape.size) with
      | some w => throw (.predicateWidthMismatch a.shape.size w)
      | none => pure ()
  return fun coord => match a.mask with
    | none => true
    | some m => (evalPosBool (coord.map (Int.ofNat ·)) m).toOption.getD true

/-- The storage-kind guard is the FIRST statement, before the store is looked at. -/
def runDensePointwise (c : CheckedPointwisePlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  unless c.storageKind == .float64 do
    throw (.storageKindMismatch .float64 c.storageKind)
  let src ← validateNonlinSourceOf c.raw.sourceSlot c.raw.shape store
  return c.raw.fn.apply src

def runDensePointwise32 (c : CheckedPointwisePlan) (store : Array DenseTensor32) :
    Except PositionalInputError DenseTensor32 := do
  unless c.storageKind == .float32 do
    throw (.storageKindMismatch .float32 c.storageKind)
  let src ← validateNonlinSourceOf c.raw.sourceSlot c.raw.shape store
  return c.raw.fn.apply32 src

def runDenseAxiswise (c : CheckedAxiswisePlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  unless c.storageKind == .float64 do
    throw (.storageKindMismatch .float64 c.storageKind)
  let src ← validateNonlinSourceOf c.raw.sourceSlot c.raw.shape store
  let included? ← axiswiseIncluded c.raw
  return c.raw.fn.applyCore c.raw.axisPos included? src

def runDenseAxiswise32 (c : CheckedAxiswisePlan) (store : Array DenseTensor32) :
    Except PositionalInputError DenseTensor32 := do
  unless c.storageKind == .float32 do
    throw (.storageKindMismatch .float32 c.storageKind)
  let src ← validateNonlinSourceOf c.raw.sourceSlot c.raw.shape store
  let included? ← axiswiseIncluded c.raw
  return c.raw.fn.applyCore32 c.raw.axisPos included? src

end F32BPlan
```

In `EvalPlan.lean`, `checkPlan`'s `.float32` capability pass changes its `.pointwise`/`.axiswise`
arms to `pure ()`, still matched arm by arm, and its `localCheck` dispatches those two arms by
`storageKind`, exactly as `.assign` already does. In `Dense32.lean`, `runDensePlan32`'s
`.pointwise`/`.axiswise` arms become real, calling `runDensePointwise32`/`runDenseAxiswise32`; the
`.scatter`/`.scan` arms keep refusing. `runDensePlan`, `checkPlanBlock`, `runDenseBlock`, and
`checkScanPlan` are unchanged: they only ever see `.float64` nonlinearity evidence, and now the
Float workers' own guards back that up as well.

**Guards before admission.** This is F32-A's Task 2 ordering discipline. Within Task 3, the four
worker guards and their order fixtures are written before `checkPointwiseF32`/`checkAxiswiseF32`
can produce evidence. Both land in one commit, so no committed state exists in which binary32
nonlinearity evidence can reach an unguarded Float worker.

### 3.4 Compiler emission (`Eval/Plan/Compile.lean`)

- `checkF32Stmt`'s plain-assignment arm loses both rejections. Task 2 removes the unary factor
  loop, and Task 4 removes the nonlinearity match. The arm is then `pure ()`, and the function keeps
  only its scatter arm and its `recurMorphism` arm. `f32CapabilityCheck` is unchanged.
- `prepareEvalPlan` Step D, `.pointwise` and `.axiswise` arms (Task 4):
  - compute `let destDtype := dtypeOfDecl (declEnv[nm]?)` once;
  - push it as the dtype of **both** the internal preactivation slot and the published slot;
  - emit the preactivation step as
    `.assign { assignPlan with algebra := algebraForDest destDtype rhs.agg }`.

  For every binary64 program this is byte-identical. The preactivation algebra is the same because
  `algebraForDest .f64 agg = algebraForAgg agg` by definition. The dtype is the same because a
  non-predicate name's `dtypeOfDecl` is `.f64`, and a predicate cannot reach these arms. The claim
  is pinned by Task 4 fixture 4.4. Replace the arm's "Always `f64`" comment with the reason
  `destDtype` is correct.
- `compileScan` is **not** touched. Its result-slot literals are an F32-C obligation (§1.3,
  §3.5 table B).

### 3.5 Sibling audits: two recurring defect families

This slice creates new members of two families that earlier slices each hit at the most expensive
review tier. Both tables are **deliverables** — Task 3 completes table A's worker and checker
columns, Task 4 completes table B, and Task 5 re-verifies both cell by cell against the final
source. Every cell is classified as **required** (must execute), **forbidden** (must fail loud,
with the fixture that pins it), or **(c)** (silently defaulted or ignored, and safe only because of
a guard elsewhere). Every (c) cell names that guard and the later slice that inherits it.

**Table A — checked evidence reaching a wrong-precision worker** (F32-A §3.5's family). New members:
the binary32 nonlinearity evidence and unary-factor evidence.

| Checked case | Source gate (Step 0c/A) | `checkPlan` / direct checkers | Float workers | binary32 workers | Named adapters | JAX | Legacy |
|---|---|---|---|---|---|---|---|
| f32 pointwise, top-level | **required** — admitted by Task 4 (fixture 4.2) | **required** — `checkPointwiseF32` via `checkPlan` (3.10); Float `checkPointwise` on an f32 table is `dtypeNotAdmitted 1 .f32` (3.2) | **forbidden** — `runDensePointwise`'s first-statement guard, `storageKindMismatch .float64 .float32` before `missingSlot` (3.4, M1) | **required** — `runDensePointwise32` via `runDensePlan32` (3.7) | **required** — unchanged cores at `α := Float32`; `pack`/`unpack`/`runPreparedDense` refuse `.float32` as today (4.6) | **forbidden** — plan-level gate first, unchanged | **forbidden**, permanently |
| f32 axiswise (masked/unmasked) | **required** (4.1, 4.5) | **required** (3.10); Float `checkAxiswise` refuses (3.2) | **forbidden** — `runDenseAxiswise`'s guard (3.4, M2) | **required** — `runDenseAxiswise32` (3.8, 3.9) | **required** (4.5, 4.7) | **forbidden** | **forbidden** |
| f32 inline unary | **required** — Task 2 (2.8) | **required** — `checkAssignF32` admits it (2.1) | **forbidden** — `runDenseAssignAt`'s existing `.float64` guard (F32-A T2 fixture 18) | **required** — `float32Ops.applyUnary` via `applyChecked32` (2.2–2.4) | **required** (2.10) | **forbidden** | **forbidden** |
| f32 unary domain violation | n/a (runtime) | n/a | n/a | **required failure** — `unaryDomain32 op bits slot` (2.5–2.7) | **required failure** — `.execution (.unaryDomain32 …)`, warnings kept (2.11, M6) | n/a | n/a |
| f64 pointwise/axiswise in f64 graph | unchanged | **required** — Float checkers, `.float64` evidence (3.1 control) | **required** — guard passes (existing `NonlinDenseTest`, `BlockTest`, scan corpus) | **forbidden** — `…32` guards, `storageKindMismatch .float32 .float64` before `missingSlot` (3.5, M3/M4) | unchanged | unchanged policy | unchanged |
| Bool slot at an f32 nonlinearity | n/a from source (`checkPredicateOutput`) | **forbidden** — `dtypeNotAdmitted slot .bool` (3.2 row sweep) | — | — | — | — | — |
| f32 nonlinearity/unary inside a scan block | **forbidden** — Step 0c `"{nm}: f32 scan"` (existing 15(d)) | **forbidden** — `f32UnsupportedStep i .scan`; `checkPlanBlock` `storageKindNotAdmitted .float32` | **(c)** — `runDenseBlock` calls the Float nonlinearity workers; safe because `checkPlanBlock` never admits `.float32` and those workers now guard too. **F32-C** | none | none | **forbidden** | **forbidden** |
| f32 unary/nonlinearity in a top-level scatter | **forbidden** — `"{nm}: f32 scatter"` (existing 15(c)) | **forbidden** — `f32UnsupportedStep i .scatter` | **(c)** — `runDenseScatter` gathers through the Float `denseValueAt` only; safe because `checkPlan` refuses the step kind. **F32-D** | none | none | **forbidden** | **forbidden** |

Doors to open during the audit even when they are absent from a task diff:

- workers: `runDensePointwise`, `runDenseAxiswise`, `runDensePointwise32`, `runDenseAxiswise32`,
  `runDenseAssignAt`, `runDenseAssignAt32`, `runDensePlan`, `runDensePlan32`, `runDenseBlock`,
  `runDenseScan`, `runDenseScatter`;
- checkers: `checkPlan`, `checkPlanBlock`, `checkScanPlan`;
- adapter cores: `packBodyOf`, `unpackBodyOf`, `runPreparedDenseOf`;
- JAX: all eight `requireFloat64Plan`/`unsupportedStorageKind` doors;
- legacy: `evalScheduled`'s `scheduleFloat32Name?`.

**Table B — a hard-coded binary64 dtype or algebra at an arm a binary32 program can now reach.**
This is the family `DifferentialTest`'s comment on the plain call site names ("A regression
hardcoding `admittedAlgebra` at the plain call site would escape all of those"), and the family
F32-A Task 4 fixture 9 pinned, one site at a time. Every site in `Compile.lean` and the nonlinearity checker:

| Site | Reachable by f32 after this slice? | Class | Pin |
|---|---|---|---|
| plain `.identity` arm: `destDtype` + `algebraForDest` | yes | **required**, already correct (F32-A) | F32-A T2 fixture 11 |
| plain `.pointwise` arm: 2 × `dtype := .f64` + preactivation `algebraForAgg` | **yes** | **fixed by Task 4** | 4.2, M1/M2 |
| plain `.axiswise` arm: same 3 sites | **yes** | **fixed by Task 4** | 4.1, M3/M4 |
| `residualizeAssignment`'s default `algebraForAgg agg` | only through the arms above, which override it | **(c)** — overridden at every top-level call site after Task 4; scan call sites override it with `algebraForDest` already | 4.1–4.4 |
| `.plain (.scatter …)` arm; `scatterFillOrFail`'s `.f32 _ => false` | no — Step 0c scatter arm | **(c)**, guarded by Step 0c. **F32-D** | existing CompileTest 15(c), FW2 |
| `compileScan` base/step nonlinear result slots, literal `.f64` | no — Step 0c scan arm | **(c)**, guarded by Step 0c. **F32-C** must switch both to `destDtype` | existing CompileTest 15(d) |
| `compileScan` `stateDtypes.getD si .f64` / `resolveSource` `getD … .f64` defaults | no | **(c)** totality formalities; the keys are validated before use | — |
| `checkNonlinIO`'s two `.f64` literals | yes | **fixed by Task 3** (`nonlinDtypeFor kind`) | 3.1, 3.2, M5 |
| `floatOps`/`float32Ops` `decodeConst` cross-tag arms | yes (fail-loud) | **forbidden**, unchanged by this slice | not re-pinned here |

### 3.6 The libm witness pattern

A witness fixture (block 5's `witness`) asserts two things. First, the implementation equals the
native binary32 routine, bit for bit, on every lane. Second, at least one lane is one where that
native routine differs from binary64-then-narrow *on the running platform*. The second check is
what stops the fixture being tautological. If a lane set stops separating the two, the fixture
fails with a message naming exactly that, and the remedy is re-running the §8 witness search
(four lanes per op took well under a minute). Witness fixtures are the **only** fixtures in this
plan whose inputs depend on the platform libm, and they are labeled as such in the test files.
Every other value fixture uses portable lanes (§1.1).

## 4. Implementation tasks

Task boundaries are chosen so that each task can be rejected, or rolled back, on its own:

- **Task 1:** the math core, which is pure computation;
- **Task 2:** the unary factor vertical slice;
- **Task 3:** checked nonlinearity evidence and workers;
- **Task 4:** compiler emission and the named end-to-end;
- **Task 5:** capability documentation and close-out.

Every mutation cycle runs through `leanncd/scripts/mutation-cycle.sh`, and each records its failing
fixture and restored pass. The counting convention is F32-A's: one mutation observed across
several fixtures is one cycle; "independently" applied to an enumerated list counts one per item.

### Task 1 — Binary32 math core and the binary64 behavior-preservation gate

**Files**

- `leanncd/LeanNCD/Eval/Nonlin.lean`
- `leanncd/LeanNCD/Eval/Error.lean`
- `leanncd/test/Eval/NonlinTest.lean`
- new `leanncd/test/Eval/Nonlin32Test.lean`
- `leanncd/lakefile.toml` (register `Eval.Nonlin32Test` in `Tests`' `globs`)
- `leanncd/LeanNCD/Eval/AGENTS.md`. Update the `Nonlin.lean` "Find It Fast" row and the "Add a new
  nonlinearity" entry point: a new function is now one `pointwiseWith`/`axiswiseRowWith` arm plus
  any new constant in **both** instances, not a `*T` body.

**Implementation**

1. **Before editing anything**, add fixture 1.1 to `NonlinTest.lean` and build it green against the
   unmodified tree. The golden table is only evidence if it was captured from the code it protects.
2. Add block 1's record and instances, and block 2's formulas, `perRowCoreWith`, and the two public
   entries, to `Eval/Nonlin.lean`. Keep `rowsAlong` as-is; the block 2 copy is probe-only.
3. Re-express every public Float entry named in §3.1 as the Float instantiation. Their signatures
   are unchanged, so no caller moves.
4. Add block 3's `UnaryOp.applyChecked32` beside `applyChecked`, and extend `applyChecked`'s doc
   comment to name its sibling.
5. Add fixtures 1.2–1.8 to `Nonlin32Test.lean`. Label fixture 1.8 as a platform libm witness.

**Numbered fixture groups: 8; planned mutation cycles: 16**

Block 5 gives fixture 1.1's golden table, which was verified against *today's* functions and against
the probe's Float instantiation, and fixture 1.8's witness helper with its five `run_cmd`s:

```lean
namespace F32BPlan

/-- Exact-bits comparison with one allowance: a NaN lane matches any NaN, because IEEE-754 does not
    fix the payload a NaN-producing primitive returns. Every other lane — including `-0` — is
    compared bit for bit. -/
def sameBits64 (xs : Array Float) (bits : Array UInt64) : Bool :=
  xs.size == bits.size && (xs.zip bits).all fun (x, b) =>
    if x.isNaN then (Float.ofBits b).isNaN else x.toBits == b

/-- Task 1 fixture 1.1's shape: the golden lanes captured from the PRE-refactor tree. Checked here
    against both today's `PointwiseFn.apply` and the probe's Float instantiation. -/
def goldenPts : DenseTensor := ⟨[5], #[-1.25, -0.0, 0.7, 2.0, 0.0 / 0.0]⟩
def goldenPointwise : List (PointwiseFn × Array UInt64) :=
  [ (.relu,      #[0, 9223372036854775808, 4604480259023595110, 4611686018427387904, 0])
  , (.sigmoid,   #[4597191638388367573, 4602678819172646912, 4604193719948776566,
                   4606108734329616841, 9221120237041090560])
  , (.tanh,      #[13829187916169686510, 9223372036854775808, 4603618880536915601,
                   4606858408046085076, 9221120237041090560])
  , (.gelu,      #[13817306155275007250, 9223372036854775808, 4602954170467180171,
                   4611481544619399846, 9221120237041090560])
  , (.leakyrelu, #[13801731418039622042, 9223372036854775808, 4604480259023595110,
                   4611686018427387904, 9221120237041090560]) ]
#guard goldenPointwise.all fun (pf, bits) => sameBits64 (pf.apply goldenPts).data bits
#guard goldenPointwise.all fun (pf, bits) => sameBits64 (applyFloat pf goldenPts).data bits

def goldenRow : DenseTensor := ⟨[3], #[0.5, 1.0, 2.5]⟩
def maskPos1 (c : List Nat) : Bool := c != [1]
def goldenAxiswise : List (AxiswiseFn × Array UInt64 × Array UInt64) :=
  [ (.softmax,
      #[4591843061051816868, 4595085808842274168, 4604805641613501230],
      #[4593253896426369454, 0, 4606108734329616841])
  , (.normalize,
      #[4593671619917905920, 4598175219545276416, 4603804719079489536],
      #[4595172819793696085, 0, 4605681218924227243])
  , (.l2normalize,
      #[4595745948572889240, 4600249548200259736, 4606397629898218687],
      #[4596233848715572764, 0, 4607007505076573091]) ]
#guard goldenAxiswise.all fun (fn, all, masked) =>
  sameBits64 (fn.applyCore 0 (fun _ => true) goldenRow).data all &&
  sameBits64 (fn.applyCore 0 maskPos1 goldenRow).data masked
#guard goldenAxiswise.all fun (fn, all, masked) =>
  sameBits64 (applyCoreFloat fn 0 (fun _ => true) goldenRow).data all &&
  sameBits64 (applyCoreFloat fn 0 maskPos1 goldenRow).data masked

/-- Task 1 fixture 1.8's shape (the libm WITNESS pattern, §3.6): the implementation must equal the
    native binary32 routine on every lane, AND at least one lane must be one where the native
    routine differs from binary64-then-narrow — otherwise the fixture could not tell the two
    apart, and it says so instead of passing. -/
def witness (label : String) (impl native : Float32 → Float32) (wide : Float → Float)
    (lanes : List UInt32) : Lean.Elab.Command.CommandElabM Unit := do
  let x (b : UInt32) := Float32.ofBits b
  unless lanes.any (fun b => (native (x b)).toBits != (wide (x b).toFloat).toFloat32.toBits) do
    throwError s!"{label}: no lane separates native binary32 from binary64-then-narrow on this \
platform's libm; choose new witness lanes (the fixture would otherwise pin nothing)"
  unless lanes.all (fun b => (impl (x b)).toBits == (native (x b)).toBits) do
    throwError s!"{label}: implementation is not the native binary32 routine"

def viaChecked32 (op : UnaryOp) (v : Float32) : Float32 :=
  (op.applyChecked32 v).toOption.getD (Float32.ofBits 0x7fc00000)

def expLanes : List UInt32 := [1048801280, 1049583616, 1051496448, 1051680768]
def logLanes : List UInt32 := [1065353222, 1065353236, 1065353244, 1065353288]
def sinLanes : List UInt32 := [1048809472, 1048829952, 1048854528, 1048985600]
def cosLanes : List UInt32 := [1050177536, 1058869248, 1060933632, 1062293504]
def tanhLanes : List UInt32 := [1048600576, 1048842240, 1049923584, 1049960448]
def tanh32 (v : Float32) : Float32 := (PointwiseFn.tanh.apply32 ⟨[1], #[v]⟩).data[0]!

run_cmd witness "exp" (viaChecked32 .exp) Float32.exp Float.exp expLanes
run_cmd witness "log" (viaChecked32 .log) Float32.log Float.log logLanes
run_cmd witness "sin" (viaChecked32 .sin) Float32.sin Float.sin sinLanes
run_cmd witness "cos" (viaChecked32 .cos) Float32.cos Float.cos cosLanes
run_cmd witness "tanh" tanh32 Float32.tanh Float.tanh tanhLanes

end F32BPlan
```

1.1 **binary64 golden table.** Donor: `NonlinTest`'s `t1` helper. Block 5's `goldenPointwise`
covers the 5 functions × lanes `[-1.25, -0, 0.7, 2.0, NaN]`. `goldenAxiswise` covers the
3 functions × row `[0.5, 1, 2.5]`, unmasked and with position 1 masked. Compare by bits with
`sameBits64` (a NaN lane matches any NaN). All 43 values were observed from today's tree.

1.2 **binary32 pointwise lanes.** Donor: 1.1's structure retagged. Apply `PointwiseFn.apply32` to
lanes `L = [1060320051 (0.7f), 1058161516, 3214409728 (-1.1875), 3214934016 (-1.25), 2147483648
(-0), 2143289344 (NaN), 1073741824 (2.0)]` for all five functions.
- Every lane is compared *relationally* with a test-local direct formula (1.3's functions).
- Four discriminating lanes are hardcoded with their narrowed contrast: `sigmoid` lanes 0–1 and
  `gelu` lane 2 (values in §2.6), and `leakyrelu` lane 3, `3159149772` against narrowed
  `3159149773`.
- The semantic lanes are hardcoded: `relu` gives `[…, 0, 0, 2147483648, 0, …]` for lanes 2–5,
  i.e. `relu(-0) = -0` and `relu(NaN) = +0`; and `-0` passes through `tanh`, `gelu`, and
  `leakyrelu` while `sigmoid(-0) = 1056964608`.
- NaN lanes are asserted with `isNaN`.

1.3 **independent-formula sweep.** Donor: none (new). On a 64-point grid `(i − 32)/8 + 1/16`,
`i < 64`, `PointwiseFn.apply32 pf` equals, bit for bit, a direct formula written in the test file
*without* the record. For example, `sig32 x := 1.0 / (1.0 + Float32.exp (-x))`, and `gelu32` spells
the two constants' bits literally. All five functions pass in the authoring probe.

1.4 **binary32 axiswise discriminators.** Donor: 1.1's `goldenRow` shape. Assert §2.6's `softmax
[0, 0, 2.5]`, `normalize [2²⁴, 1, 1]`, and `l2normalize [4097, 4097]` native bits, each with its
narrowed contrast.

1.5 **axiswise order and masking.** Donor: 1.4.
- `softmax [0, 0, 0.75, 2.5]` gives its native left-fold bits.
- `softmax [1000, 0, 2.5]` with position 0 masked gives `[0, 1033591688, 1064080527]`.
- An all-masked 2-lane row gives `[0, 0]` for all three functions.

1.6 **unary domain parity.** Donor: none (new). For all six ops and the nine boundary bit patterns
`0x00000000, 0x80000000, 0x00000001, 0x80000001, 0x3f800000, 0xbf800000, 0x7f800000, 0xff800000,
0x7fc00000`, check that `(op.applyChecked32 v).toBool == (op.applyChecked v.toFloat).toBool`.
Passes in the authoring probe.

1.7 **portable unary values.** Donor: `KernelDenseTest.unaryPow2Store`'s inputs. §2.6's `log`,
`sqrt`, `recip`, and `exp` lanes through `applyChecked32`.

1.8 **libm witnesses (platform).** Donor: block 5. `witness` for `exp`, `log`, `sin`, and `cos`
through `applyChecked32`, and for `tanh` through `PointwiseFn.apply32`, on §2.6's lanes. Record the
observed native bits in a comment only. Asserting them would pin this libm's exact rounding error,
which the relational form deliberately avoids.

Mutations and expected observations. The wrong values for M1, M2, M3, M4, M7, M8, M12a (`exp`),
and M13 were observed at authoring time, on the plan probe (§8) or by a direct probe. The other
cycles are completion gates, and their predicted observations must be confirmed when the task
runs.

- **M1.** Swap `relu`'s arguments in `pointwiseWith` (`o.max x o.zero`). Fixture 1.1's relu `-0`
  lane becomes `+0` and its NaN lane becomes NaN, so it fails; 1.2 also fails. Observed on the
  probe.
- **M2.** Make `normalizeRowWith` sum masked entries too. 1.1's masked `normalize` lanes become
  `[4593671619917905920, 0, 4603804719079489536]` (observed) and fail.
- **M3.** Drop `softmax`'s max-subtraction (`o.exp x`). 1.1's softmax lane 0 becomes
  `4591843061051816869` (observed) and fails.
- **M4.** Let `softmax`'s row maximum include masked entries. 1.5's masked row becomes `[0, 0, 0]`
  (observed) and fails. 1.1 cannot see this mutation, because its masked entry is not the row
  maximum, which is why 1.5 exists.
- **M5.** Implement `PointwiseFn.apply32` as widen, then `PointwiseFn.apply`, then narrow. 1.2's
  four discriminating lanes return their narrowed bits and fail.
- **M6.** Implement `AxiswiseFn.applyCore32` the same way. All three 1.4 rows return narrowed bits
  and fail.
- **M7, M8** (two cycles). Fold the `softmax` sum, then independently the `normalize` sum, with
  `foldr`. 1.5's fold-order row fails; 1.4's `normalize` row returns
  `[1065353214, 864026622, 864026622]` (observed) and fails.
- **M9.** Swap `geluScale` and `geluCubic` in `float32NonlinOps`. The 1.2 `gelu` lanes and 1.3's
  `gelu` sweep fail.
- **M10.** `log` domain test `v < 0`. 1.6 fails at `+0` and `-0`.
- **M11.** `sqrt` domain test `v ≤ 0`. 1.6 fails at `+0` and `-0`.
- **M12a–d** (four cycles). `applyChecked32 .exp`/`.log`/`.sin`/`.cos` independently computed as
  `(Float.op v.toFloat).toFloat32`. That op's 1.8 witness fails with "implementation is not the
  native binary32 routine". The `exp` case was observed on the probe.
- **M13.** `float32NonlinOps.tanh := fun x => (Float.tanh x.toFloat).toFloat32`. 1.8's `tanh`
  witness fails. Observed on the probe. 1.2 cannot see it, because its `tanh` lanes agree with
  narrowing.

### Task 2 — Checked binary32 inline unary factors, end to end

**Files**

- `leanncd/LeanNCD/Eval/Plan/Error.lean`: `unaryDomain32`; doc updates to
  `unaryNotAdmittedForStorage` and `unaryNotAdmittedForDtype`, which are now producer-less.
- `leanncd/LeanNCD/Eval/Plan/Dense.lean`: `float32Ops.applyUnary`, and its doc comment.
- `leanncd/LeanNCD/Eval/Plan/Check.lean`: delete the `.float32` inline-unary clause and its comment.
- `leanncd/LeanNCD/Eval/Plan/Compile.lean`: `checkF32Stmt`'s factor loop and its doc comment.
- `leanncd/LeanNCD/Eval/Plan/Adapter.lean`: M6's mutation site only (`runPreparedDenseOf`'s
  `.execution` arm). No production edit.
- `leanncd/test/Eval/Plan/KernelCheckTest.lean`
- `leanncd/test/Eval/Plan/KernelDense32Test.lean`
- `leanncd/test/Eval/Plan/CompileTest.lean`
- `leanncd/test/Eval/Plan/Adapter32Test.lean`
- `leanncd/test/Eval/Plan/AdapterTest.lean`: fixture 2.11's binary64 half, plus the two stale
  "`.execution` is unreachable" comments (§2.5).
- `leanncd/LeanNCD/Eval/AGENTS.md`: the `Dense.lean` row's `Float32` unary sentence, and the
  `Error.lean` row.

**Implementation**

1. Add `PositionalInputError.unaryDomain32` (§3.2), and make `float32Ops.applyUnary` real.
2. Delete `checkAssignCore`'s `.float32` unary clause. `kind` then varies the policy at three
   clauses, not four; update the core's doc comment accordingly.
3. Delete `checkF32Stmt`'s factor loop. The nonlinearity match stays until Task 4.
4. Flip or re-point every existing fixture this admits, as listed below. Do not delete the retired
   constructors.
5. Correct the three stale "`PlanRunCause.execution` is unreachable" passages (§2.5) in
   `AdapterTest.lean` (above its `PlanRunCause.execution` `#guard`, and Check 16's preamble) and in
   `Adapter32Test.lean` (fixture 7's preamble). The accurate statement: pack rules out every
   *shape/arity/storage* cause, but not a runtime domain violation. Fixture 2.11 pins that in both
   carriers.

**Numbered fixture groups: 11; planned mutation cycles: 6**

2.1 Donor: `KernelCheckTest` fixture 4 (`unaryF32Plan`). Flip it to acceptance, with `.float32`
evidence, for all six ops. Keep the binary64 control.

2.2 Donor: `KernelDenseTest.unaryPlan op 0` with `unarySigs` retagged `.f32` and
`admittedAlgebraF32`, over `unaryPow2Store` as bits. Assert §2.6's `log`, `sqrt`, and `recip` lanes
through `KernelDense32Test.run32`.

2.3 Pad-then-apply. Donor: `unaryPlan .exp 1` retagged, store `[0, 3.0, -2.5, -0.25]`. Expected
`[1101049646, 1034427438, 1061642109, 1065353216]`. The last lane is out of bounds, so it is
`exp(+0) = 1`.

2.4 Worker witnesses (platform). Donor: `unaryPlan op 0` retagged, store = §2.6's four witness
lanes for each of `exp`, `log`, `sin`, `cos`. Use block 5's `witness` pattern: run the four-lane
plan once through `run32`, compare each output lane with the native routine, and keep the same
precondition that at least one lane separates native from binary64-then-narrow.

2.5 Domain payloads. Donors: `unarySqrtBadStore`, `unaryRecipBadStore`.
- `sqrt` over `[1, -4, -9, 4]` gives `.unaryDomain32 .sqrt 3229614080 0`. The first violation wins,
  not `-9`'s `3239051264`.
- `recip` over `[2, 0, 4, 8]` gives `.unaryDomain32 .recip 0 0`.
- `recip` over `[2, -0, 4, 8]` gives `.unaryDomain32 .recip 2147483648 0`. The payload is the
  gathered value's *own* bits, sign included.

2.6 Donor: `unaryPlan .log 1` retagged, over `unaryPow2Store`. Expected
`.unaryDomain32 .log 0 0`: lane 3 reads the padded `+0`. An apply-before-pad reading would report
no error at all.

2.7 Slot locator. Donor: `unaryPlan .sqrt 0` with `sourceSlot := 1` and `destinationSlot := 2`,
over a three-entry `.f32` table whose slot 0 is an unread `#[4]` input. Store `[_, [1, -4, 4, 9],
_]`. Expected `.unaryDomain32 .sqrt 3229614080 1`, so slot `1` is distinguishable from a constant
`0`.

2.8 Donor: CompileTest fixture 15(b) (`f32UnaryProg`). Flip it to acceptance:
- `storageKind .float32`;
- one `.assign` step whose factor 1 is a read with `unary = some .log`, and whose factor 0 is the
  Iverson;
- algebra `admittedAlgebraF32`.

2.9 Re-point CompileTest fixture 17. Its unary-then-nonlinearity pair no longer has two
rejections. Build `[f32ScatterProg's statement; f32ScanProg's scan]` with the union of their
declarations. Rename the scan's external `X` to `Xs`, in its declaration, its read, and
`extNames`, because the two donors both declare an `X`. It must report `"Y: f32 scatter"`, and the
reversed statement order must report `"S: f32 scan"`. The two subcases distinguish source order
from either category priority. Both results were observed on today's tree with
`f32IdentitySig` as the signature: Step 0c runs before Step B, so the signature is never
consulted. This fixture can therefore be written and made green *before* Task 2's code change.

2.10 End-to-end witness (platform). Donor: `DifferentialTest`'s `E[i] := exp(A[i + 1])` shape, as
an `Adapter32Test` `tlprog!` with `tensor f32 A(i), E(i)` and `axis i : ℕ = 3`. Input `A = [0,
1048801280, 1049583616]`. `E` must equal the native `Float32.exp` of lanes 1–2 followed by
`1065353216`, which is observed `[1067808354, 1068064150, 1065353216]`. The precondition compares
it against the binary64 twin through `runPreparedDense`, observed narrowed as
`[1067808353, 1068064151, 1065353216]`. The materialized dtype is `.f32`.

2.11 End-to-end domain error, both carriers. Donor: 2.10 with `log` and `A = [1, 2, 4]`.
- **binary32 half** (`Adapter32Test`): `runPreparedDense32` fails with cause
  `.execution (.unaryDomain32 .log 0 0)` and exactly one warning (`paddedAccess`), equal to
  `prepared.warnings`.
- **binary64 half** (`AdapterTest`): the plain-`tensor` twin through `runPreparedDense` fails with
  `.execution (.unaryDomain .log 0 0)` and the same single warning, as already observed at
  authoring time. `AdapterTest` has no `TLProgram`-to-`PreparedPlan` helper; its fixtures inline
  `compileToScheduled` and `prepareEvalPlan` (as `warnProg`'s does), so follow that pattern or add
  a private binary64 twin of `Adapter32Test`'s private `prepare32`.

These are the first fixtures anywhere that pin warnings on an `.execution` failure. The binary64
half also turns the corrected comment of implementation step 5 into an observation.

Mutations:

- **M1.** Make `float32Ops.applyUnary` go through `op.applyChecked x.toFloat` and narrow. Fixtures
  2.4 and 2.10 fail.
- **M2.** Payload bits constant `0`. 2.5's `sqrt` case fails.
- **M3.** Payload bits of `Float32.abs x`. 2.5's `recip(-0)` case fails, while the `sqrt` case
  still passes, so the sign lane is load-bearing.
- **M4.** Payload slot constant `0`. 2.7 fails.
- **M5.** Traverse top-level statements in reverse in `f32CapabilityCheck`. 2.9's first subcase
  reports the scan and fails.
- **M6.** `runPreparedDenseOf` throws `.execution` with `warnings := []`. Both halves of 2.11 fail,
  because the runner is shared.

Pad-then-apply (fixtures 2.3 and 2.6) is shared `gatherFactorWith` code whose mutation cycle already
lives in the binary64 suite (`KernelDenseTest`'s `exp`-bias-1 fixture). A mutation there fails the
binary64 sibling first and masks the importing binary32 module. That is F32-A §6.5's M3/M11
situation, so no masked cycle is planned. 2.3 and 2.6 are regression pins on the shared path.

### Task 3 — Checked binary32 pointwise and axiswise

**Files**

- `leanncd/LeanNCD/Eval/Plan/Nonlin.lean`: block 4. Also rewrite the module doc and the
  `runDensePointwise`/`runDenseAxiswise` doc comments to state the guard.
- `leanncd/LeanNCD/Eval/Plan/EvalPlan.lean`: the `checkPlan` capability pass and dispatch; the
  `PlanStepError.f32UnsupportedStep` doc, which now names F32-C/F32-D only.
- `leanncd/LeanNCD/Eval/Plan/Dense32.lean`: the `runDensePlan32` arms and its "Assignment-only"
  doc.
- `leanncd/LeanNCD/Eval/Plan/Block.lean`: read-only audit target (table A). No edit is expected.
- `leanncd/test/Eval/Plan/NonlinCheckTest.lean`
- `leanncd/test/Eval/Plan/NonlinDenseTest.lean`
- new `leanncd/test/Eval/Plan/NonlinDense32Test.lean`, which imports `LeanNCD.Eval.Plan.Dense32`,
  `Eval.Plan.NonlinDenseTest`, and `Eval.Plan.KernelDense32Test`
- `leanncd/test/Eval/Plan/GraphCheckTest.lean`
- `leanncd/lakefile.toml` (register `Eval.Plan.NonlinDense32Test`)
- `leanncd/LeanNCD/Eval/AGENTS.md`: the `Nonlin.lean` plan row, `Dense32.lean` row, and
  `EvalPlan.lean` row.

**Implementation**

1. Write the four worker guards and fixtures 3.4 and 3.5 first (§3.3, "Guards before admission").
2. Add block 4: the evidence field, the cores, and the F32 checkers and workers.
3. Make `checkPlan` and `runDensePlan32` dispatch by storage kind (§3.3).
4. Complete table A's checker and worker columns and table B's `checkNonlinIO` row from the
   implemented call graph, and record the result in the task report.

**Numbered fixture groups: 11; planned mutation cycles: 11**

Block 6 gives the shapes of fixtures 3.4 and 3.2's extra row, compiled against block 4's probe
definitions:

```lean
namespace F32BPlan

/-- Task 3 fixture 3.4's shape: binary32 evidence handed to the binary64 worker with an EMPTY
    store must report the storage kind, not `missingSlot 0 0` — the guard's ORDER, not only its
    existence. -/
def sigs32 : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f32 }, { shape := #[3], dtype := .f32 } ]
def sigmoid3 : RawPointwisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[3], fn := .sigmoid }

#guard match checkPointwiseF32 sigs32 sigmoid3 with
  | .ok c => match runDensePointwise c #[] with
      | .error (.storageKindMismatch .float64 .float32) => true
      | _ => false
  | .error _ => false

-- ... and the binary32 worker runs the same evidence natively (lanes 0.7f, bits 1058161516, -1.25).
#guard match checkPointwiseF32 sigs32 sigmoid3 with
  | .ok c => (runDensePointwise32 c
      #[⟨[3], #[1060320051, 1058161516, 3214934016].map Float32.ofBits⟩]).toOption.map
        (·.data.map Float32.toBits) == some #[1059786330, 1059297860, 1046743937]
  | .error _ => false

-- Task 3 fixture 3.2's extra row: an f64 source in a direct binary32 check is refused at the
-- SOURCE slot (the destination guard ran first and passed).
#guard match checkPointwiseF32
    #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f32 } ] sigmoid3 with
  | .error (.dtypeNotAdmitted 0 .f64) => true
  | _ => false

end F32BPlan
```

3.1 Donor: `NonlinCheckTest.baselineSigs`/`baselinePointwise`/`baselineAxiswise`, retagged `.f32`.
The F32 checkers accept, with `storageKind .float32`. Control: the Float checkers on the
untouched baseline record `.float64`.

3.2 Row sweep. Donors: every existing `NonlinCheckTest` row fixture — rows 1–2 (slot range, both
kinds), 3–4 (`sourceBoolSigs`/`destBoolSigs`), 6–7 (shape), 8 (axis position), and the mask-width
fixture — with `.f64` signatures retagged `.f32` and `.bool` left alone. Each must give the same
constructor and payload through the F32 checkers. Also:
- block 6's f64-source row, `dtypeNotAdmitted 0 .f64`;
- the Float checkers on the retagged baseline, `dtypeNotAdmitted 1 .f32`, which shows the legacy
  entry was not widened.

3.3 Privacy. `#check_failure (⟨baselinePointwise, .float32⟩ : CheckedPointwisePlan)` and its
axiswise sibling, in `NonlinCheckTest`. This works only across modules: in the same file the
private constructor is visible, which the authoring probe confirmed. The authoring check against
today's one-field `CheckedPointwisePlan` observed "Constructor … is marked as private" (§8).

3.4 Float-worker guard order. Donor: `NonlinDenseTest.pwErrOf`/`axErrOf`, fed 3.1's binary32
evidence. With an empty store it must give `storageKindMismatch .float64 .float32`, not
`missingSlot 0 0`; the same holds with a well-formed Float store. Block 6's first guard is this
fixture's shape.

3.5 Binary32-worker guard order. Donor: `NonlinDenseTest.probePointwise`/`probeAxiswise` through
the Float checkers on `oneNodeSigs`/`axiswiseSigs`, handed to `runDensePointwise32`/
`runDenseAxiswise32` with an empty store. It must give `storageKindMismatch .float32 .float64`.

3.6 Runtime trust boundary. Donor: `pwErrOf`/`axErrOf`'s missing, shape, storage, and well-formed
cases, re-expressed over `DenseTensor32` stores and 3.1's evidence. Same payloads.

3.7 Graph pointwise discriminator. Donor: `NonlinDenseTest.pointwisePlan`, with signatures `.f32`,
`idNode` given `admittedAlgebraF32`, and `fn := .sigmoid`. Run through
`EvalPlan32Test.runGraph32`/`bitsAt` with `X = [1060320051, 1058161516]`. Slot 2 must be
`[1059786330, 1059297860]`, against narrowed `[1059786331, 1059297859]`.

3.8 Graph axiswise discriminator. Donor: `NonlinDenseTest.axiswisePlan` (normalize along axis 1,
`#[2, 2]`) retagged, with `X = [[2²⁴, 1], [1, 1]]`. Slot 2 must be
`[1065353216, 864026624, 1056964608, 1056964608]`, against narrowed
`[1065353215, 864026623, 1056964608, 1056964608]`. This also pins row grouping along a non-leading
axis in binary32.

3.9 Masked axiswise. Donor: `NonlinDenseTest.probeAxiswiseMasked`/`maskExcludeCol0` retagged, over
`[[1, 3], [2, 2]]`. Expected `[0, 1065353216, 0, 1065353216]`.

3.10 Donor: GraphCheckTest fixture 8 (`f32PointwisePlan`) and fixture 16's axiswise case
(`f32AxiswisePlan`). Flip both to acceptance with `.float32`. The fixture 16 scatter and scan cases
stay rejections.

3.11 Re-point `f32UnsupportedStepOrder`. Donor: its own `[assign, pointwise]` plus a scatter shaped
like fixture 16's `f32Scatter`, renumbered to read the pointwise destination and write a fresh
`.f32` slot. The plan is `[assign, pointwise, scatter]` and must give
`f32UnsupportedStep 2 .scatter`. `checkPlan`'s capability pass runs before any wiring or local
check, so the result does not depend on the scatter's geometry; build it well-formed anyway. The
two wrong readings give different indices: a pass over not-yet-admitted kinds only would report 0,
and one over assignments only would report 1.

Mutations:

- **M1–M4** (four cycles, independently). Move each of `runDensePointwise`'s, `runDenseAxiswise`'s,
  `runDensePointwise32`'s, and `runDenseAxiswise32`'s guards after `validateNonlinSourceOf`. The
  empty-store half of 3.4 or 3.5 reports `missingSlot 0 0` and fails. `runDensePointwise` was
  observed on the probe. Relocation rather than deletion is the cycle, because it is the reading a
  presence-only check misses; deletion also fails both halves.
- **M5.** `nonlinDtypeFor .float32 := .f64`. 3.1 and 3.2 fail.
- **M6, M7** (two cycles). `checkPlan`'s `.float32` pointwise, then independently axiswise, dispatch
  goes to the Float checker. 3.7 or 3.8 fails with `.nonlin 1 (.dtypeNotAdmitted 2 .f32)`, and 3.10
  fails.
- **M8, M9** (two cycles). `runDensePointwise32`, then `runDenseAxiswise32`, via widen → Float
  worker math → narrow. 3.7 or 3.8 returns its narrowed bits and fails.
- **M10.** The capability pass locates over a filtered step list. 3.11 reports 0 and fails.
- **M11.** Remove `private` from `CheckedPointwisePlan`'s constructor. 3.3's `#check_failure`
  fails.

### Task 4 — Compiler emission and the named binary32 nonlinearity boundary

**Files**

- `leanncd/LeanNCD/Eval/Plan/Compile.lean`: `checkF32Stmt`'s nonlinearity match, the Step D
  `.pointwise`/`.axiswise` arms, and those arms' comments.
- `leanncd/test/Eval/Plan/CompileTest.lean`
- `leanncd/test/Eval/Plan/NonlinCompileTest.lean`
- `leanncd/test/Eval/Plan/Adapter32Test.lean`
- `leanncd/LeanNCD/Eval/AGENTS.md`: the "Run a checked BINARY32 plan by name" entry point, which now
  covers nonlinearities and unary factors.

**Implementation**

1. §3.4's three Step D edits in each nonlinear arm, and removal of the nonlinearity match in
   `checkF32Stmt`.
2. Complete table B from the implemented source and record it in the task report.

**Numbered fixture groups: 7; planned mutation cycles: 5**

4.1 Donor: CompileTest fixture 15(a) (`f32AxiswiseProg`). Flip it to acceptance:
- `storageKind .float32`;
- signature dtypes `[f32, f32, f32]` (X, the internal preactivation slot, Y);
- step kinds `[assign, axiswise]`, with step 0's algebra `admittedAlgebraF32`;
- materialized `Y` at slot 2.

4.2 Donor: `f32IdentitySched` with `nonlin := .pointwise .relu`. The same claims, with a pointwise
step.

4.3 Donor: CompileTest fixture 14 (`f32BadOrderProg`: `relu` over `log`). Flip it to acceptance:
- step 0's factor 0 is a read with `unary = some .log`;
- step 1 is `.pointwise .relu`;
- every signature is `.f32`.

The nonlinearity-before-factor *order* claim it used to pin no longer has two rejections to order,
and the fixture's comment should say so.

4.4 Binary64 byte-identity. Donors: `identitySched` with `nonlin := .pointwise .relu`, and
`NonlinCompileTest.axiswiseSched`, both binary64. The preactivation step's algebra is exactly
`admittedAlgebra` and every signature is `.f64`. The existing Section 3 isolated-prepared pins in
`NonlinCompileTest` stay unchanged.

4.5 End-to-end causal attention. Donor: `EvalExamplesTest`'s masked-attention program, with `axis q
: ℕ = 3`, `axis d : ℕ = 1`, and `tensor f32 Q(q, d), K(s, d), A(q, s)`. `Q = [1, 1, 1]` and
`K = [0, 0, 2.5]`, so every score row is `[0, 0, 2.5]`. Through `prepare32` and
`runPreparedDense32`, `A` must be §2.6's 3×3 native bits. The binary64 twin through
`runPreparedDense` must give the observed narrowed row 2 `[1032873796, 1032873796, 1062987311]`.
The materialized dtypes are `[("A", .f32)]`.

4.6 End-to-end sigmoid. Donor: `NonlinCompileTest`'s sigmoid program with `axis i : ℕ = 2`, `axis
j : ℕ = 1`, and `tensor f32 W(i, j), x(j), H(i)`. `W = [1060320051, 1058161516]` and `x = [1]`.
`H` must be `[1059786330, 1059297860]`; the binary64 twin was observed as
`[1059786331, 1059297859]`. Also assert that `runPreparedDense` refuses the f32 prepared plan with
`storageKindMismatch .float64 .float32`, which is table A's Float-adapter cell for a nonlinear plan.

4.7 End-to-end normalize. Donor: `NonlinCompileTest`'s normalize program, with `axis q : ℕ = 1` and
`tensor f32 A(q, s), Y(q, s)`. `A = [[2²⁴, 1, 1]]` must give
`[1065353216, 864026624, 864026624]`; the binary64 twin was observed as
`[1065353214, 864026622, 864026622]`.

Mutations:

- **M1.** In the `.pointwise` arm, keep the *published* slot's literal `.f64`, which is exactly
  `compileScan`'s current shape. 4.2 fails with `.invalidPlan (.assign (.mixedStorageKinds …))`.
- **M2.** In the `.pointwise` arm, keep the preactivation step's `algebraForAgg`. 4.2 fails with
  `.invalidPlan (.assign (.nodeError 0 (.algebraNotAdmitted admittedAlgebra)))`.
- **M3, M4.** The same two mutations in the `.axiswise` arm. 4.1 fails.
- **M5.** Select `algebraForAggF32 rhs.agg` unconditionally for the preactivation step. 4.4's
  binary64 twin fails under `checkAssign` as `algebraNotAdmitted`, so the change is not byte-safe
  for binary64.

### Task 5 — Capability documentation, final audit, and close-out

**Files**

- `leanncd/LeanNCD/Eval/AGENTS.md`
- `papers/backend_missing_functionality.md`
- `papers/wave_f_capability_manifest.md`
- `papers/unary_factor_functions.md`: its banner states binary32 unary is rejected.
- `papers/eval_ir.md`: if the sweep finds an f32 nonlinearity or unary claim.
- `papers/f32_evalplan.md`: §1.3 item 1 and §1.4 item 1 get a one-line "landed by
  `f32b_evalplan.md`" status pointer only. The record is not otherwise edited.
- `papers/f32b_evalplan.md`: the close-out.
- `papers/f32b_evalplan_handoff.md`: a completed-record banner.
- Read-only re-audit targets: `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean` and
  `leanncd/LeanNCD/Eval/Plan/Executable.lean`.

**Implementation**

1. Re-verify tables A and B cell by cell against final source, and mark them complete.
2. Split `backend_missing_functionality.md`'s "Binary32 beyond the assignment fragment" row: unary
   and nonlinearity move to "Already closed", while scans, scan-local scatter, and top-level
   scatter stay. Re-derive the `CapabilityError` count from the enum and its throw sites (expected
   unchanged at 10 / 16 / 6). Record the new producer-less constructors (§3.2) and the new live
   `unaryDomain32`.
3. Add §1.1's libm finding to `backend_missing_functionality.md`, beside the F32-JAX row. It
   changes what bit-exact parity with XLA can mean for transcendentals.
4. Run §6.3's sweep. Change this plan's status to a completed record and append §6.5 (observed
   results).

**Numbered fixture groups: 0; planned mutation cycles: 0.** The deliverables are the two completed
audit tables, the sweep classification, and the value-grep record (§6.3). A reviewer can reject
this task while approving Task 4, which is why it is separate.

## 5. Dependency graph and risk sizing

Task 1 is the only root. Tasks 2 and 3 each depend only on Task 1: Task 2 needs `applyChecked32`,
and Task 3 needs `apply32`/`applyCore32`. They share no production or test file, so they can land
in either order. Their only shared files are `Eval/AGENTS.md`, where they touch different rows, and
`lakefile.toml`, which only Task 3 edits among the two.
Task 4 depends on Tasks 2 and 3, because its end-to-end fixtures exercise both the checked
nonlinearity path and inline unary. Task 5 depends on Task 4.

| Task | Main reviewer question | Fixture groups | Mutation cycles | Risk |
|---|---|---:|---:|---|
| 1 — math core | Is every binary64 formula bit-identical after the refactor, is every binary32 formula the same operation tree with native primitives and exact constants, and do the witnesses actually discriminate? | 8 | 16 | **High.** Numerical truthfulness, plus a refactor of shared binary64 code that has no independent oracle other than fixture 1.1 |
| 2 — unary | Is the payload the gathered value's own bits at its own slot, and does a domain failure keep its warnings through the named runner? | 11 | 6 | Moderate. Small production diff, but four locator/payload fixtures, each with a distinguishing construction, plus the first `.execution` warnings pin |
| 3 — checked nonlinearity | Can binary32 nonlinearity evidence reach a Float worker, or Float evidence a binary32 worker, and does each guard precede the store check? | 11 | 11 | **High.** New members of F32-A's §3.5 family; four order-pinning guard cycles; the table A deliverable |
| 4 — compiler + named | Does every nonlinear arm stop hard-coding binary64 while staying byte-identical for binary64 programs? | 7 | 5 | Moderate–high. Table B's family, three end-to-end discriminators, one byte-identity pin |
| 5 — docs/audit | Are the capability claims and the two audit tables re-derived from source, not restated? | 0 | 0 | Moderate. The sweep plus stale-value grep, the tier that has historically hidden stale claims |
| **Total** | | **37** | **38** | |

Task 1 is not split. Its binary64 refactor and binary32 instance are the same edit: the generic
formula *is* both. A reviewer cannot approve one while rejecting the other. Task 2 is not merged
into Task 3: they touch disjoint files and different failure families.

## 6. Validation

### 6.0 Review cadence

This is F32-A §6.0, unchanged. After each task, and before its dependents:

1. Commit it as one reviewable unit.
2. Run an independent review against its Files, Implementation, fixtures, mutation observations,
   and the reviewer question in §5.
3. For Tasks 3 and 4, inspect the unchanged doors listed under table A.
4. Resolve or adjudicate every finding, re-run the affected cycles, and get a clean re-review.

Model tier: mid-tier reviewers are adequate for Tasks 2 and 5. Tasks 1 and 3 get a strong reviewer,
because numerics and door order are where the recurring defects live.

### 6.1 Per-task targeted commands

Run from `leanncd/`. `lake` is not on `PATH`, so every command is
`"$HOME/.elan/bin/lake" build <targets>`. Build an edited module before `lake env lean`-checking
anything that imports it (`leanncd/AGENTS.md`).

| Task | Targets |
|---|---|
| 1 | `LeanNCD.Eval.Nonlin Eval.NonlinTest Eval.Nonlin32Test Eval.Plan.NonlinDenseTest Eval.Plan.NonlinCompileTest Eval.Portfolio.NormTest Eval.Portfolio.FeedforwardTest Eval.Portfolio.AttentionTest Eval.Portfolio.GenerativeTest Eval.EvalExamplesTest` |
| 2 | `Eval.Plan.KernelCheckTest Eval.Plan.KernelDenseTest Eval.Plan.KernelDense32Test Eval.Plan.CompileTest Eval.Plan.AdapterTest Eval.Plan.Adapter32Test Eval.EntryTest` |
| 3 | `Eval.Plan.NonlinCheckTest Eval.Plan.NonlinDenseTest Eval.Plan.NonlinDense32Test Eval.Plan.GraphCheckTest Eval.Plan.GraphDenseTest Eval.Plan.BlockTest Eval.Plan.ScanTest Eval.Plan.EvalPlanTest Eval.Plan.EvalPlan32Test` |
| 4 | `Eval.Plan.CompileTest Eval.Plan.NonlinCompileTest Eval.Plan.AdapterTest Eval.Plan.Adapter32Test` |
| 5 | `Eval.Plan.ExecutableTest JaxExperiment` (re-audit only), then the §6.4 full gate |

Mutation example, in the shape `leanncd/AGENTS.md` prescribes:

```bash
bash leanncd/scripts/mutation-cycle.sh 'T1-M1 (relu argument order)' \
  /path/to/worktree/leanncd LeanNCD/Eval/Nonlin.lean \
  '| .relu      => fun x => o.max o.zero x' '| .relu      => fun x => o.max x o.zero' \
  Eval.NonlinTest Eval.Nonlin32Test
```

A build failure unrelated to the named fixture does not count as a successful mutation.

### 6.2 Existing regression gates

Before each task lands, build:

- `Eval.Plan.DifferentialTest`
- `Eval.PropertyOracleTest`
- `Eval.PropertyOracleScanTest`
- `Eval.Portfolio.Harness`
- `DSL.Pipeline.RouteFragmentCorpusTest`

Their corpus lines must stay exactly as re-observed on `main` at authoring time:

```
DifferentialTest sweep: total=3832 accepted=3832 rejected=0 categories=[]
DifferentialTest scan corpus: total=17 accepted=17 unsupportedNonlin=0 unsupportedAgg=0
```

**The corpora are not extended.** They are binary64 reference gates, and the legacy evaluator
refuses every f32 schedule, so no f32 case could be differential there. They do matter more than
usual for Task 1: the 17-case scan corpus contains nonlinear scans, and all three of its legs run
the rewritten Float formulas. Fixture 1.1 is the independent pin those three shared legs cannot
provide.

### 6.3 Documentation and stale-value sweep

1. Search case-insensitively, repo-wide, for `f32`/`binary32`/`F32-B` and for the retired payload
   words `f32 nonlinearity`, `f32 unary factor`, `unaryNotAdmittedForDtype`, and
   `unaryNotAdmittedForStorage`. Classify each current-document hit.
2. Value-grep for the boundary values this slice moves: `assignment-only`, `assignment fragment`,
   `identity nonlinearity`, `f32UnsupportedStep 0 .pointwise`, and `"f32 nonlinearity"`. Search
   the whole repository, not just edited files (`slice-plan` §1).
3. Re-derive the `CapabilityError` live/producer-less count from source (expected 10 / 16 / 6,
   unchanged). If it has moved, the plan is wrong: stop and find out why.
4. Ship no `File.lean:NNN` citation in any shipped text. Use identifiers only.

### 6.4 Full gate and independent final reviews

Run a full `"$HOME/.elan/bin/lake" build` from `leanncd/`, with `JaxExperiment` already passing
separately. Then run two whole-branch reviews with different lenses:

1. **Numerical lens.** Trace every binary32 value from input bits through each primitive to the
   materialized bits. Hunt for a `Float` conversion, a binary64 constant, a changed association or
   fold order, and a witness whose precondition would pass vacuously. Independently recompute
   §2.6's discriminators.
2. **Boundary lens.** Cover the whole diff plus the unchanged doors in table A. Check every
   locator/order fixture's construction, both audit tables, and every retired producer. Confirm
   that no scan or scatter path acquired binary32 evidence.

The slice is complete only when both reviews are clean or every finding is adjudicated.

## 7. Success criteria and stop conditions

Done means all of the following are observed:

- `A[q, s.] := softmax(where s ≤ q)(Q[q, d] · K[s, d])`, with every tensor `tensor f32`, prepares
  to `.float32` evidence. On §4.5's inputs it materializes exactly `[1065353216, 0, 0, 1056964608,
  1056964608, 0, 1032873795, 1032873795, 1062987311]`, while its binary64 twin gives row 2 as
  `[1032873796, 1032873796, 1062987311]`.
- The pointwise discriminators give native bits different from their narrowed twins:
  - `sigmoid(0.7f)` is `1059786330` against `1059786331`;
  - `gelu(-1.1875)` is `3188661568` against `…569`;
  - `leakyrelu(-1.25)` is `3159149772` against `…773`.
- The axiswise discriminators give native bits different from their narrowed twins:
  - `normalize [2²⁴, 1, 1]` is `[1065353216, 864026624, 864026624]` against
    `[1065353214, 864026622, 864026622]`;
  - `l2normalize [4097, 4097]` is `1060439284` per lane against `…283`.
- Every binary64 golden lane of fixture 1.1 is unchanged after the refactor, and both corpora print
  3832/3832 and 17/17.
- A binary32 domain violation is `unaryDomain32 op bits slot` carrying the gathered value's own
  bits (`recip(-0)` gives `2147483648`) and its own slot. Through `runPreparedDense32` it is
  `.execution (…)` with the preparation's warnings.
- Binary32 nonlinearity evidence at a Float worker, and Float evidence at a binary32 worker, both
  fail as `storageKindMismatch` *before* any store check.
- Every f32 scan and scatter form keeps its F32-A rejection. No f32 plan reaches a JAX candidate,
  and the legacy evaluator still refuses every f32 schedule.
- All 37 fixture groups pass. All 38 mutation cycles record fail and restored-pass observations.
  Every witness fixture's precondition holds on the build platform.
- Tables A and B are complete with no pending cell. The documentation sweep is complete. Two final
  reviews are clean or adjudicated.

Stop and revise the plan, rather than improvise, if any of these happens:

- the platform no longer reproduces a *portable* value in §2.6, since the argument for those lanes
  is wrong if it does not;
- fixture 1.1 cannot be kept green, which means the generic formula is not the existing binary64
  formula;
- a binary32 nonlinearity needs a different operation tree from its binary64 counterpart to be
  reasonable (that is a semantic decision, not an implementation detail);
- any path lets binary32 evidence into scan, scatter, or JAX code;
- the user answers Q1 in favor of correctly rounded transcendentals.

## 8. Authoring verification record

Unless marked, every claim below was measured at authoring time. The probe files lived in the
session scratchpad and were compiled through `bash .claude/skills/slice-plan/check-snippet.sh`,
which writes into gitignored `leanncd/spikes/` and removes the file afterwards.

- **Plan Lean blocks.** The six ```` ```lean ```` blocks of this document, concatenated in order,
  form one file that compiles against `main`. That file includes block 5's golden `#guard`s against
  today's `PointwiseFn.apply`/`AxiswiseFn.applyCore`, all five witness `run_cmd`s, and block 6's
  order guard. Each block was embedded into this document mechanically, from the exact files
  compiled, not retyped. Re-check from the repository root with:

  ```bash
  awk '/^```lean$/{f=1;next} /^```$/{f=0} f' papers/f32b_evalplan.md \
    | bash .claude/skills/slice-plan/check-snippet.sh -
  ```
- **Authoring-time mutation cycles on that probe.** Each failed at the named fixture, and the
  unmutated file compiled:
  - `float32NonlinOps.tanh` narrowed from binary64 fails the `tanh` witness ("implementation is not
    the native binary32 routine");
  - `relu` with swapped arguments fails the probe's Float golden `#guard`;
  - `runDensePointwise`'s guard moved after `validateNonlinSourceOf` fails block 6's order guard;
  - `applyChecked32 .exp` narrowed from binary64 fails the `exp` witness.
- **Earlier design probe.** A 2-D and masked variant of the design probe also guarded bit identity
  between the generic Float instantiation and today's functions:
  - 10 pointwise lanes, including ±0, NaN, and ±∞, for all five functions;
  - all three axiswise functions on a `[2, 3]` tensor along axis 0 and axis 1, masked and unmasked.
- **Expressions verified with `pp.explicit`.**
  - `geluT`'s `x^3` is `HPow Float Float` through `instPowOfHomogeneousPow`, i.e. `Float.pow x 3.0`.
    The binary32 `x ^ 3` elaborates the same way to `Float32.pow`.
  - `Max Float`/`Max Float32` are both `maxOfLe` (`Init/Data/Float.lean`,
    `Init/Data/Float32.lean`). Observed: `max 0 (-0) = -0` and `max 0 NaN = +0` in both carriers.
- **Constants.** `(0.7978845608028654 : Float32).toBits`, and the narrowing of the binary64
  literal, are both `1061962282` (`0x3f4c422a`). `0.044715` gives `1027024659` (`0x3d372713`) both
  ways, and `0.01` gives `1008981770` (`0x3c23d70a`) both ways. The hex equalities were checked by
  `#eval`.
- **libm statistics and witness lanes.**
  - The §1.1 counts come from one scan of every 37th bit pattern in `[0x3d800000, 0x41800000)`.
  - The witness lanes come from scans with stride `0x1000` from `0x3e800000` (`exp`/`sin`/`cos`/
    `tanh`) and stride 1 from `0x3f800001` (`log`).
  - Every discriminator was found by search. Its margins were computed from binary64 proxies, with
    `libm == correctly rounded` confirmed at each composite's libm steps.
- **Platform.** `System.Platform.target = "arm64-apple-darwin24.6.0"`. The host is macOS 26.6.2
  (build 25G83), arm64. Witness lanes are specific to this libm (§3.6).
- **End-to-end observations through the real pipeline** (`compileToScheduled`, the
  declaration-aware signature constructor, `prepareEvalPlan`, `runPreparedDense`, on `main`):
  - The f32 attention, sigmoid, normalize, `exp`, and `relu(log(·))` programs are rejected today
    with the §2.1 payloads.
  - Their binary64 twins produce the narrowed values quoted in Tasks 2 and 4.
  - The binary64 `log(A[i + 1])` twin fails with `.execution (.unaryDomain .log 0 0)` and 1
    warning.
- **The binary32 end-to-end expectations are composed values, not pipeline observations.** The
  binary32 pipeline for Tasks 2–4 does not exist yet, so those expected bits were composed in the
  design probe from the same native operations the plan specifies. This is F32-A's method. The
  3×3 attention bits came from the probe's `AxiswiseFn.applyCore32` over the masked row engine.
- **Corpus lines.** Re-observed by `lake build Eval.Plan.DifferentialTest -v` on `main`: 3832/3832
  and 17/17 (8525 jobs).
- **Privacy.** `#check_failure (⟨pw⟩ : CheckedPointwisePlan)` from a separate module against
  today's tree reported "Constructor for `LeanNCD.Eval.Plan.CheckedPointwisePlan` is marked as
  private". Inside the probe file itself the same check "unexpectedly succeeds", as Lean privacy
  predicts, which is why fixture 3.3 lives in a test module.
- **Payload deriving.** A mirror inductive (`missingSlot` first, then `unaryDomain` with `UInt64`
  and `unaryDomain32` with `UInt32`) derived `DecidableEq, BEq, Repr, Inhabited`. With
  `unaryDomain` first, `Inhabited` failed, because `UnaryDomainOp` has no `Inhabited`. So the
  constructor position in the real enum, after `missingSlot`, is what makes the derivation work.
- **Paths.** Every existing path in the Files lists was verified with `ls`/`test -e`. The two new
  test files' parent directories exist.
- **Donor names.** Each was read in its file before being cited: `KernelDenseTest.unaryPlan`/
  `unarySigs`/`unaryPow2Store`/`unarySqrtBadStore`/`unaryRecipBadStore`,
  `KernelCheckTest.unaryF32Plan`, `NonlinCheckTest.baseline*` and the row fixtures,
  `NonlinDenseTest.pointwisePlan`/`axiswisePlan`/`pwErrOf`/`axErrOf`/`probe*`/`maskExcludeCol0`,
  `GraphCheckTest.f32PointwisePlan`/`f32UnsupportedStepOrder`/`f32AxiswisePlan`/`f32Scatter`,
  `CompileTest` fixtures 14/15/17 and `f32IdentitySched`/`f32IdentitySig`, `EvalPlan32Test.runGraph32`/
  `bitsAt`, `KernelDense32Test.t32`/`run32`/`bitsOf`, and `Adapter32Test.prepare32`.
- **Prose claims checked against functions.**
  - "`compileScan` already uses `destDtype`/`algebraForDest` for the preactivation": read.
  - "the plain arms use `residualizeAssignment`'s `algebraForAgg`": read at both call sites.
  - "`runDenseBlock` calls the Float nonlinearity workers": read.
  - "`checkPlanBlock` admits only `.float64`": read.
  - "`gatherFactorWith` is shared by both carriers": read.
- **Inherited claims re-derived.** §2.7's four F32-A gaps, the `CapabilityError` 10/16/6 count
  (from the enum's doc and `Compile.lean`'s three throw sites, which this plan does not move), and
  F32-A §1.4's F32-B description.
- **`.execution` reachability.** Grepping `test/` for `.execution` found only the three "unreachable"
  passages quoted in §2.5 and one constructor-equality `#guard`. The counterexample
  `.execution (.unaryDomain .log 0 0)` with 1 warning was observed through the real binary64
  pipeline.
- **Not verified, and stated as such:**
  - the Figueroa double-rounding citation is from memory; the measured zero counts are the
    evidence relied on;
  - no glibc or other libm was available, so "portable" means "every libm step at most 0.018 ulp
    from representable", not "observed on a second platform".

## 9. Open questions for the user

- **Q1 — native libm or correctly rounded binary32 transcendentals?** §1.1 chooses native `expf`,
  `logf`, `sinf`, `cosf`, `tanhf`, and `powf`, following F32-A §1.3's wording. The measured
  alternative, per-primitive binary64-then-narrow, is correctly rounded, more portable, and more
  accurate, and is arguably still binary32 per primitive under F32-A §1.1. It differs from native
  on up to 1.7% of inputs, by one ulp. Either is implementable, and only §3.1's record fields and
  §3.2's function change. The choice also affects what F32-JAX can later claim against XLA.
- **Q2 — fold the `f64` source keyword in?** F32-A §1.4 suggested it could ride along with F32-B.
  This plan excludes it: it touches `Decl`/`TensorElementType` exhaustiveness (F32-A Task 1's
  largest surface) and has no failure mode shared with this slice. It fits better as the first task
  of the default-flip slice, or as its own tiny slice.
- **Q3 — witness fixtures in the default build.** They are platform-specific by construction
  (§3.6). This plan keeps them in the default `Tests` target, with a loud, self-explaining failure.
  The alternative is a separate non-default target, at the cost of their protection not running on
  a bare `lake build`.

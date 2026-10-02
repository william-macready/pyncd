# F32-JAX prototype notes (NOT a plan)

Explore + prototype half of authoring F32-JAX (`slice-plan` §6a). A fresh dispatch writes
`papers/f32_jax_evalplan.md` from this file, the patches in `papers/f32_jax_files/`, and
`papers/f32_jax_mutations_post.json`. Base: `9b27008` (local `main`, includes
`papers/f32_jax_spike_results.md`). Scope, fixed by the brief and not reopened here:
**assign-only, context-free, `affineReference` only, binary32**; `einsumOnly` stays f32-refused with
no tolerance label; scans, nonlinearities, and scatter are untouched in every precision.

## 0. Bottom line

- The prototype works end to end through the PRODUCTION gates (no shim). Evidence run (stride 1,
  §3): the 7 named spike/discriminator fixtures, 8 standalone-assign and 2 positional binary32
  fixtures, and ALL 3,832 `enumPrograms` cases retagged binary32 → `orderedReference32` from
  `validateAndConstructExecutable` (named) / `validateAndConstructKernel` (assign), an `einsumOnly`
  refusal for every one, and the shared ordered runtime bit-identical to the Lean binary32 reference
  eager AND under `jax.jit` with x64 DISABLED — **3,849 fixtures, 11,746 output checks
  (5,873 eager + 5,873 jit), 0 mismatches** outside the one pinned known divergence (§3.1).
- **One real, inherited platform finding (§3.1, decision §9.1):** XLA CPU does not honour two IEEE
  behaviours the checked left fold does, in BOTH precisions: it flushes subnormal operands/results
  of arithmetic to zero (eager and jit; `--xla_cpu_enable_fast_math=false` does not change it), and
  under `jax.jit` it simplifies the reduction seed `+0 + x` to `x` (a `-0` input survives where the
  fold gives `+0`). The existing `orderedReference64` claim has the same gap — the binary64 corpora
  simply contain no subnormal or `-0` value. The prototype pins the one affected fixture
  (`f32Identity`) as an EXACT known divergence rather than excluding it silently.
- Binary64 is unchanged: the 20-fixture curated module regenerates **byte-identical** (11,509
  bytes, `cmp` clean), its eager+JIT output bits from the old and new runtime are byte-identical
  (md5 `23b8d0b31741f945eb21d2961608e2b1` both), and the 3,832-case f64 corpus passes (0
  mismatches, 3,424,195 bytes — unchanged).
- There are **THREE** f32-rejecting gates, not the spike's two. The third is production
  `validateAndConstructExecutable`'s plan-level `unless candidate.source.plan.storageKind ==
  .float64` (`JaxExecutableValidationError.unsupportedStorageKind`) — the spike never called the
  executable validator. The prototype REMOVES it (user ruling: remove, §2.3).
- Mutant P2 (term sum by `jnp.sum`) is NOT equivalent: XLA CPU sums a stacked term axis
  sequentially up to 32 terms and in blocks at 64 — the new 64-term `termSum64` fixture kills it.
- Every previously uncovered f32 cell now has a dedicated fixture (§5). 15 Lean + 6 Python mutation
  cycles, all killed (§6).
- Recommendation: **one slice, two tasks** (§8).

## 1. Verified code claims (`identifier @ file`)

### 1.1 Gate 1 — the experimental plan-level storage gate

`requireFloat64Plan @ experiments/jax_bridge/EvalPlanCodegen.lean` (re-verified name; body
`if c.storageKind == .float64 then .ok () else .error (.unsupportedStorageKind c.storageKind)`).
Its 7 call sites, classified by reading each body:

| Call site | Path | Why |
|---|---|---|
| `lowerPlan` | einsumOnly | iterates `lowerAssign` (emits `jnp.einsum`) |
| `generateForward` | einsumOnly | → `generateForwardChecked` → `lowerPlan` |
| `renderInputConstants` | einsumOnly (einsum smoke helper) | emits `INPUT_BITS` via `Float.toBits` — binary64 payload, consumer is `EvalPlanSmoke.lean`/`evalplan_smoke.py` |
| `renderAffinePlanPositional` | affineReference | → `renderAffineNodesArray` → `renderAffineNode` |
| `renderAffinePlanNamed` | affineReference | same |
| `generateNamed` | BOTH (dispatcher) | `match mode` → `generateForward` / `renderAffinePlanNamed` |
| `lowerCheckPlanToCandidate` | affineReference | calls only `loweringToAffineTableCandidate` (einsum candidate deliberately not wired) |

Entries with NO plan gate (standalone; take `sigs` + a `CheckedAssignPlan`, rely on gate 2 only):
`lowerAssign` (einsum), `loweringToEinsumCandidate` (einsum), `renderAffineAssign` (affine),
`loweringToAffineTableCandidate` (affine), `buildAssignFixture` (affine; also runs the binary64
`runDenseAssign`, so an f32 assignment fails loud there as "Dense run failed" — f64-only helper).

**Consequence that drives the design:** the einsum/affine split is clean at the entry level (no
entry serves both except the `generateNamed` dispatcher), so the single gate CAN become mode-aware.
But relaxing gate 2 opens the two standalone einsum entries, which have no plan gate at all —
they need their own per-assignment refusal (the "currently-missing door" of brief item 6).

### 1.2 Gate 2 — the production per-node support policy

`jaxAssignSupported @ LeanNCD/Eval/Plan/Executable.lean` (private), reached only via public
`checkJaxAssignSupport`, which first re-runs `checkAssign`/`checkAssignF32` selected from
`CheckedAssignPlan.storageKind` (that dispatch already existed — F32 Task 5). Checks, in order:
destination `dtype == .f64` → `algebra == admittedAlgebra` → `contextShape.isEmpty` → per factor
(original term/factor order): Iverson skipped (owned by `requireNoIverson`/`renderAffineTerm`),
source `dtype == .f64`, `unary.isNone`. Callers: `jaxSupportOk` (→ `validateAffineTable`,
`validateEinsum`), `validateAndConstructKernel`, and `requireJaxSupport @ EvalPlanCodegen.lean`
(every codegen entry). Pinned f32-rejection: `ExecutableTest` "f32 slice Task 5, fixture 1".

### 1.3 Gate 3 — the production executable storage gate (missed by the spike)

`validateAndConstructExecutable @ LeanNCD/Eval/Plan/Executable.lean`: first statement
`unless candidate.source.plan.storageKind == .float64 do throw (.unsupportedStorageKind …)`.
Pinned by `ExecutableTest` "f32 slice Task 2, fixtures 23 and 24" (zero-step f32 candidate; and
the gate preceding `invalidBindings`). Its stated reason: `aggregateEvidenceList #[]` was
`orderedReference64`, so a zero-step f32 plan would otherwise get a reference64 claim.

### 1.4 Evidence

`ExecutionEvidence @ Executable.lean` is a plain 2-constructor inductive tag (`orderedReference64`,
`optimizationExperiment`) — no proof content in the label itself. Proof content lives in the
carriers: `JaxKernel.aligned : candidateEvidenceLabel candidate = evidence` (private ctor, label
derived only inside `validateAndConstructKernel`) and `JaxExecutableCandidate.aggregated : evidence
= aggregateEvidenceList (steps.map (·.evidence))`, restated in `JaxExecutableWellFormed`, its
`Decidable` instance, and the `decide` check in `validateAndConstructExecutable`. The Python side
checks no label; it checks bits.

## 2. Design as prototyped (patches carry the code)

### 2.1 Gate 2: storage-keyed real carrier (item 2)

New private `jaxRealCarrier : StorageKind → ScalarDType × ContractionAlgebra` (`.float64 ↦ (.f64,
admittedAlgebra)`, `.float32 ↦ (.f32, admittedAlgebraF32)`, no wildcard). `jaxAssignSupported`
gains a `kind` argument (passed `checked.storageKind` by `checkJaxAssignSupport`) and compares
destination dtype, algebra, and source dtype against that pair. Chosen over "accept `.f64 ∨ .f32`
symmetrically" because the symmetric form would accept an `f64` slot under `.float32` evidence if
the `checkAssignF32` re-run were ever weakened — keying makes the policy self-standing. Bool
dest/source, tropical (incl. `admittedAlgebraF32Max/Min`), unary, context: unchanged refusals under
both kinds; fixtures in §5 pin each f32 cell. Reuse note: `nonlinDtypeFor @ Nonlin.lean` is the
same `StorageKind → ScalarDType` map but private there; not shared (would widen Nonlin's API for a
2-line function) — the plan-writer may rule otherwise.

### 2.2 Gate 1: mode-aware (item 1)

`LoweringMode` moves from §7 to §1 of `EvalPlanCodegen.lean`. `requireFloat64Plan` is replaced by
`requireModeStorage (mode) (kind)` over `modeAdmitsStorage : LoweringMode → StorageKind → Bool`
(`.einsumOnly, k ↦ einsumStorageAdmitted k`; `.affineReference` ↦ true for both kinds, no
wildcard). Each of the 7 sites passes its own mode (table in §1.1); `generateNamed` passes `mode`.
The SAME error, `unsupportedStorageKind kind`, is kept for einsum refusals, so the einsum halves of
fixtures 22/25 are unchanged. NEW per-assignment calls `requireModeStorage .einsumOnly
checked.storageKind` at the top of `lowerAssign` and `loweringToEinsumCandidate` — the dedicated
einsum door.

`einsumStorageAdmitted : StorageKind → Bool` is PRODUCTION (`Executable.lean`) and conjoined into
`validateEinsum`, so an f32 einsum kernel is refused (`invalidCandidate`) and the documented
invariant "`validateEinsum` acceptance implies `lowerAssign` renders" stays true — the same
shared-recomputation pattern as `einsumTermLabelExtents`/`einsumLabelLimit`.

Rejected alternative: keep gate 1 mode-agnostic and accept f32 everywhere, adding a check only
inside the einsum emitter. Rejected because a zero-step f32 plan under `generateForward` has no node
for an emitter check to see — the einsum plan-level door must stay plan-level.

### 2.3 Evidence: `orderedReference32` from the same code path (item 3)

- `ExecutionEvidence` gains `orderedReference32`.
- New public `orderedReferenceFor : StorageKind → ExecutionEvidence` (no wildcard) — the one place
  a storage kind selects a reference label.
- `candidateEvidenceLabel`: `.affineTable k ↦ orderedReferenceFor k.semanticAssignment.storageKind`
  (`aligned := rfl` still closes).
- `aggregateEvidenceList (kind) (evs)`: `if evs.all (· == orderedReferenceFor kind) then
  orderedReferenceFor kind else .optimizationExperiment`. Zero-step f32 ⇒ `orderedReference32`;
  a cross-kind label ⇒ `optimizationExperiment` (pinned). Signature change: every caller passes the
  plan's kind — `JaxExecutableCandidate.aggregated` (`source.plan.storageKind`; field order allows
  it), `JaxExecutableWellFormed`, its `Decidable` instance, `validateAndConstructExecutable`,
  `lowerCheckPlanToCandidate`, 9 `ExecutableTest` literals, `spikes/AxisABoundaryProbe.lean`
  (not in any Lake target; `lake env lean` elaborates it clean after the edit).
- Gate 3 removed, and `JaxExecutableValidationError.unsupportedStorageKind` with it (orphaned by
  the removal). Soundness argument: a candidate claiming the other kind's label cannot satisfy
  `aggregated`; a step kernel validated under the wrong kind cannot exist because
  `stepTiedToPreparedStep` requires `signatureContext == prepared.plan.raw.tensorSigs` and the
  kernel's own `checkJaxAssignSupport` re-run uses its own kind's checker over that table. (Not
  added: a `storageKind` conjunct in `stepTiedToPreparedStep` — redundant by that argument; the
  plan-writer may want it as belt-and-braces; the user ruled "remove", §9.)

### 2.4 Python runtime: one parametrized implementation (item 4)

`evalplan_affine_runtime.py` parametrized, not forked: `run_assign`/`run_plan_positional`/
`run_named` take `dtype=jnp.float64` (default keeps every existing caller unchanged); `_run_term`/
`_run_node` thread it; every constant/accumulator is `dtype(0.0)`/`jnp.zeros|ones(…, dtype)`. New
`_require_dtype` refuses an unsupported dtype and any input of a different dtype (never casts), and
calls `require_x64()` only for float64. Safe indices use int64 under x64 (binary64 path unchanged)
and int32 otherwise, so a float32 caller needs no x64. Diff is ~40 lines; the f64 path stayed
byte-identical (§0), so the fork fallback was not needed.

### 2.5 Binary32 harness (new, Task 2)

- `pyUInt32ListLit`, `pyTensorEntry32 @ EvalPlanAffineSmoke32.lean` (local to the driver, its only
  caller — kept out of `EvalPlanCodegen.lean` so Task 2 does not shift Task 1's line-anchored
  mutation expects): `Float32.toBits` payloads plus a `"dtype": "float32"` tag (binary64 entries
  stay untagged, byte-identical).
- `experiments/jax_bridge/EvalPlanAffineSmoke32.lean` (driver, no Lake target). Four routes:
  - **named** (`buildNamedFixture32`, the `Adapter32Test.prepare32` pipeline): per fixture asserts
    `generateNamed .einsumOnly` = `.error (.unsupportedStorageKind .float32)` and
    `validateAndConstructExecutable` evidence = `orderedReference32`, then renders
    `renderAffinePlanNamed`. Fixtures: the 6 spike fixtures + `termSum64` (built from the AST:
    `A + 62×B + D`, `A = 2^24`, `B = 1`, `D = -2^24`; one node, 64 terms; reference `0`).
  - **corpus** (`retag32`): `.tensor` ↦ `.typedTensor .f32`, a binary32 decl for every undeclared
    statement output (over its `.free` LHS axes), undeclared extra inputs dropped (the shared
    `inputEnv` carries `P` for programs that never declare it — otherwise
    `storageKindMismatch "P"`), inputs via `Float.toFloat32` (values 1–4, exact). CLI arg 2 = stride.
  - **standalone assign** (`buildAssignFixture32`, the binary32 counterpart of `buildAssignFixture`
    over `checkAssignF32` + `runDenseAssign32` — did not exist; ~25 lines): asserts the standalone
    einsum door (`lowerAssign`) refuses and the affine kernel validates as `orderedReference32`.
    Fixtures, all reused: `KernelDense32Test.{f32Identity, f32ReductionRounding,
    f32MultiplicationRounding, f32FactorOrder, f32Efp, f32Zerd, f32TermOrder}` + `f32Pad`
    (`EvalPlanCodegen.f32PadSigs/f32PadAssign`, source `[5, 7]` into a 3-wide zero-padded read).
  - **positional** (`buildPositionalFixture32`, over `runDensePlan32`): asserts `lowerPlan` refuses,
    renders `renderAffinePlanPositional`. Fixtures: `EvalPlan32Test.{f32ProductChain,
    f32ReductionGraph}` (the first has a dependent second node).
- `evalplan_affine_smoke32.py`: asserts x64 disabled, rebuilds `np.uint32` bits (an empty
  destination placeholder becomes zeros, as in the f64 smoke), runs `rt.run_named` /
  `rt.run_assign` / `rt.run_plan_positional` with `dtype=jnp.float32`, eager + `jax.jit`, exact bit
  compare; `KNOWN_DIVERGENT = {"f32Identity": {1, 2}}` (§3.1) requires every OTHER position exact
  and the listed positions to diverge exactly as observed (fails loud if XLA ever stops). Also pins
  that the binary64 default refuses binary32 inputs (x64 gate) and that `dtype=float32` refuses
  float16. Optional arg 2 = JIT stride over corpus cases (non-corpus fixtures always JIT).
- `run-evalplan-affine32.sh [STRIDE [JIT_STRIDE]]` (defaults 100, 1).

## 3. Observed values

- Builds: base `lake build` **8,673 jobs**, `lake build JaxExperiment` **8,514**; identical after
  each patch (§7) — no new Lake modules.
- `factorProduct3` Lean binary32 reference bits `[3207259276, 3210427557]` — identical to the
  spike's; the affine runtime matches eager and jit.
- `termSum64`: one node, 64 terms (the compiler does not split or deduplicate them); reference
  `[0, 0, 0, 0]`; runtime matches.
- **Binary32 evidence run, stride 1, JIT on every case** (`run-evalplan-affine32.sh 1 1`):
  `7 named + 8 assign + 2 positional + 3832 corpus`; `kinds={'named': 3839, 'assign': 8,
  'positional': 2}`; `eager_checks=5873 jit_checks=5873`; **0 mismatches**; `f32Identity`'s known
  divergence reproduced exactly at positions `[1, 2]`; Python eager **524.8 s**, JIT **190.7 s**;
  generated module **3,657,456 bytes**; the Lean generation leg was not separately timed (the f64
  corpus's is 13–27 s; this driver additionally validates an executable and an einsum refusal per
  case). Whole script incl. the three `lake build`s: ~13 min wall-clock.
- Stride-100 run (56 fixtures: 46 named, 8 assign, 2 positional): 160 output checks, eager 8.1 s,
  JIT 2.4 s; module 182,617 bytes before `termSum64`/assign/positional were added.
- Binary64 corpus (3,832, `run-evalplan-affine-corpus.sh`, parametrized runtime):
  `source_cases=3832 eager_mismatches=0 feature_masks=45 jit_cases=65`, `artifact_bytes=3424195`
  (unchanged), generation 26.8 s / eager 575.8 s / JIT 6.4 s.
- `retag32` failure modes observed before its two fixes: `InputSignatureBuildError.
  storageKindMismatch "P" .float32 .float64`, then `CapabilityError.unsupportedDtype "Y: mixed
  f32/f64 storage in one schedule"` — the generator is not reusable verbatim (no `Gen.lean` change,
  ~15 lines in the driver).
- Fixture 22 pins that the f32 and f64 `renderAffinePlanNamed` strings of the same one-node plan
  are EQUAL — the tables are dtype-free; the binary32 claim rests entirely on the runtime.

### 3.1 XLA CPU subnormal flush and signed-zero simplification (inherited, both precisions)

Found by the first standalone-assign fixture, `f32Identity` (`Y[i] := X[i]` over `[+0, -0, least
subnormal]`; Lean reference `[+0, +0, 0x00000001]` — the reduction fold seeds `+0`, and
`+0 + -0 = +0`):

| Probe (JAX 0.10.0, CPU) | Observed |
|---|---|
| f32 `jit(a*b)(subnormal, 1)`, eager `a*b`, `jit(a+b)(subnormal, 0)` | all `0` (flushed) |
| f32 gather only (`a[idx]`, no arithmetic) | subnormal preserved |
| f64 `jit(a*b)(subnormal, 1)` | `0` (flushed) |
| `XLA_FLAGS=--xla_cpu_enable_fast_math=false`, f32 `jit(a*b)` | still `0` |
| f32 runtime, `f32Identity` | eager diverges at pos 2 (flush); jit diverges at pos 1 (`-0`, the `+0 + x → x` simplification) and pos 2 |
| f64 runtime, same three values as binary64 | eager `[0, 0, 0]` (pos 2 flushed); jit `[0, 0x8000000000000000, 0x1]` (pos 1 `-0` kept; pos 2 survives only because jit simplified `1·x` and `0+x` away) |

So the ordered runtime is bit-exact only on values whose fold never produces or consumes a
subnormal, and (under jit) never relies on `+0 + -0 = +0`. **This is not binary32-specific**: the
existing `orderedReference64` claim has the identical gap; its corpora never contain such values.
Pinned, not hidden: `KNOWN_DIVERGENT` in `evalplan_affine_smoke32.py`. Not fixed (out of scope; a
fix would have to defeat XLA's FTZ/DAZ and its algebraic simplifier). Decision §9.1.

## 4. Corpus coverage

The full 3,832-case retagged corpus runs through the mechanism (§3) with no generator change.
Sizing for the plan: measured above — ~9 min eager + ~3 min JIT-every-case
Python, ~3.7 MB module; no generator change. **JIT decision (stated, observed):** the prototype JIT-checks
EVERY corpus case (`JIT_STRIDE=1`), unlike the f64 runner's 45 feature representatives, because
the cost was measured acceptable (above) and per-case JIT is the stronger claim; the runner keeps a
`JIT_STRIDE` argument so a routine run can sample. **Caveat for the plan:** the generator's inputs
are small integers (1–4) whose products and sums are exact in binary32, so the corpus proves
plumbing/structure coverage, NOT fold-order fidelity; fold-order fidelity rests on `reduction64`,
`termSum64`, `factorProduct3`, `contraction64x64` (they kill P1–P3 below).

## 5. Sibling-door audit

Cells: R = required (renders / candidate validates), F = forbidden (located typed error before any
Python/candidate/evidence), S = silently ignored. "after" = with the prototype. Every f32 cell names
its dedicated fixture (`@ file`; `EvalPlanCodegen` = `experiments/jax_bridge/EvalPlanCodegen.lean`,
"F32-JAX: the remaining binary32 cells" block unless noted) and the mutation that kills it.

| Case | f64 einsum | f64 affine | f32 einsum (before → after) | f32 affine (before → after) |
|---|---|---|---|---|
| assign-only valid | R (`optimizationExperiment` if kernelized) | R `orderedReference64` | F storage → **F `unsupportedStorageKind .float32`** at every door: plan (`requireModeStorage`, fixture 22/25, J8), standalone (`lowerAssign`/`loweringToEinsumCandidate`, fixture 22, J9/J10), validator (`einsumStorageAdmitted`, `ExecutableTest`, J1) | F storage → **R `orderedReference32`** (fixture 22, `ExecutableTest`, J2/J6/J11/J12; Python: every named/assign/positional fixture) |
| bool destination | F `unsupportedDestDType` | F same | F → F storage | F → **F `destinationDType 7 2 .bool`** (`ExecutableTest` `f32BoolDestAssign`, J3) |
| bool source | F `unsupportedSourceDType` | F same | F → F storage (`f32BoolSourcePrepared?`) | F → **F `unsupportedSourceDType 0 0 0 .bool`** at `generateNamed`, `renderAffinePlanPositional`, `lowerCheckPlanToCandidate` (`f32BoolSourcePrepared?`, J13) |
| unary read | F `unaryFactor` | F same | F → F storage | F → **F `unaryFactor 7 0 0`** (`ExecutableTest`, J5) |
| tropical algebra | F `unsupportedAlgebra` | F same | F → F storage | F → **F `unsupportedAlgebra 7 admittedAlgebraF32Max`** (`ExecutableTest`, J4) |
| Iverson factor | F `iversonFactor` | F same | F → F storage (`f32IversonPrepared?`) | F → **F `iversonFactor 0 0 1`** at `generateNamed` and `lowerCheckPlanToCandidate` (`f32IversonPrepared?`, J15 — dtype-blind check, so the f64 donor dies too) |
| contextful | F `unsupportedContext` | F same | F → **F storage** at `lowerAssign`, `loweringToEinsumCandidate` (`f32CtxAssign`) | F → **F `unsupportedContext 0 #[2]`** at `renderAffineAssign`, `loweringToAffineTableCandidate` (`f32CtxAssign`, J14) |
| zero-pad label-extent mismatch | F `labelExtentMismatch` | R | F → **F storage** (precedes `labelExtentMismatch`; `f32PadAssign`) | F → **R**, kernel `orderedReference32` (`f32PadAssign`); Python bit-exact via the assign route (`f32Pad`; P5) |
| zero-step plan | R | R `orderedReference64` | F storage → **F storage** (plan-level only; fixture 25) | F storage → **R `orderedReference32`** (fixture 23, both `ExecutableTest` and `EvalPlanCodegen`; J7) |
| positional route | R | R | F → F storage (`lowerPlan`, asserted per fixture by `buildPositionalFixture32`) | F → **R**, Python bit-exact (`f32ProductChain`, `f32ReductionGraph`; P6) |
| standalone-assign route | R | R | F → F storage (`lowerAssign`, asserted per fixture by `buildAssignFixture32`) | F → **R**, kernel `orderedReference32`, Python bit-exact on 7 of 8; `f32Identity` = the §3.1 known divergence |

No **S** cell found. The door that needed its OWN reason (f32 einsum, standalone entry) is pinned by
fixture 22's standalone guard (refused while `requireJaxSupport` on the SAME assignment is `.ok`)
and J9/J10, plus `ExecutableTest`'s einsum-kernel refusal (J1) with its f64 control. The
`f32Identity` cell is the one place the runtime is NOT bit-exact; it is pinned as exact divergence,
not ignored.

## 6. Mutation-cycle log

Lean cycles: `papers/f32_jax_mutations_post.json`, all task `1`, run by
`leanncd/scripts/mutation-manifest.sh`: **15/15 PASS** (mutated build fails, file restored
byte-identical, restored build green). `expect` strings are the observed first error locators
(line-anchored, like F32-C's) on the Task-1 tree; a plan that edits these fixture regions must
re-observe them. Final verification run on the Task-1-only tree (`git apply task1.patch` onto base): all 15 PASS with these expects, manifest exit 0.

| Cycle | Mutation | Observed first failure |
|---|---|---|
| J1 | `einsumStorageAdmitted .float32 => true` | `ExecutableTest.lean:1827:0: Expression` (f32 einsum kernel refusal) |
| J2 | `jaxRealCarrier .float32 ↦ (.f64, admittedAlgebra)` | `ExecutableTest.lean:1806:0` (support), `:1815:0` (`orderedReference32` kernel) |
| J3 | dest check `… \|\| dtype == .bool` | `ExecutableTest.lean:586:0` (pre-existing f64 bool-dest fixture; the f32 one fails too) |
| J4 | algebra check also admits `admittedAlgebrasF32` | `ExecutableTest.lean:1870:0` (f32 tropical refusal) |
| J5 | unary check skipped for `.float32` | `ExecutableTest.lean:1878:0` (f32 unary refusal) |
| J6 | affine label hardcoded `.orderedReference64` | `ExecutableTest.lean:1815:0` |
| J7 | aggregation compares against `.orderedReference64` | `ExecutableTest.lean:86:0`, `:87:0` (f32 aggregate guards) |
| J8 | `.einsumOnly, _ => true` | `EvalPlanCodegen.lean:1785:0`, `:1798:0` (fixture 22 einsum doors) |
| J9 | `lowerAssign` storage gate deleted | `EvalPlanCodegen.lean:1797:0` (fixture 22 standalone guard) |
| J10 | `loweringToEinsumCandidate` storage gate deleted | `EvalPlanCodegen.lean:1797:0` |
| J11 | `.affineReference, .float32 => false` | `EvalPlanCodegen.lean:1813:0`, `:1833:0` |
| J12 | `lowerCheckPlanToCandidate` aggregates under `.float64` | `EvalPlanCodegen.lean:770:25: Type mismatch` — `aggregated := rfl` itself refuses it: the keying is enforced by the candidate's proof field, at compile time |
| J13 | source check admits `bool` under `.float32` only | `EvalPlanCodegen.lean:1938:0` (`f32BoolSourcePrepared?`) — ONLY the f32 fixture fails |
| J14 | context check skipped under `.float32` only | `EvalPlanCodegen.lean:1964:0` (`f32CtxAssign`) — ONLY the f32 fixture fails |
| J15 | `renderAffineTerm`'s Iverson `throw` → `pure ()` | `EvalPlanCodegen.lean:1137:0` (f64 donor), `:1951:0` (`f32IversonPrepared?`) |

Python (`papers/f32_jax_files/python_mutations.py`, on a temp COPY of the runtime; harness = the
stride-100 binary32 module, 56 fixtures):

| Mutant | Observed |
|---|---|
| unmutated / restored | pass, 56 fixtures, 160 checks |
| P1 per-row `fori_loop` reduction → `jnp.sum(mat, axis=1)` | FAIL `reduction64 eager Y: not bit-identical at 0: 0x41f80000 vs 0x00000000` |
| P2 term `fori_loop` → `jnp.sum(stacked, axis=0)` | FAIL `termSum64 eager Y: not bit-identical at 0: 0x41f80000 vs 0x00000000` (survived before `termSum64`; see P2 probe below) |
| P3 factor product order reversed | FAIL `factorProduct3 eager Y: not bit-identical at 1: 0xbf5b3ca1 vs 0xbf5b3ca5` |
| P4 `_require_dtype` input check disabled | FAIL `float32 dtype accepted float16 inputs` |
| P5 zero-pad mask ignored (`padded = gathered`) | FAIL `f32Pad eager result: not bit-identical at 2: 0x40a00000 vs 0x00000000` |
| P6 positional nodes run in reverse order | FAIL `TypeError: reshape requires ndarray or scalar arguments, got <class 'NoneType'>` (the dependent node reads an unwritten slot — a crash, not a bit mismatch) |

**P2 probe** (`[2^24, 1×(n−2), −2^24]` stacked on axis 0, f32, widths 1/4/64): `jnp.sum` equals
the sequential fold for n ∈ {4, 5, 8, 9, 16, 17, 32} and DIVERGES for n = 64 (`31` vs `0`) and
n = 128 (`95` vs `0`), eager and jit alike. So XLA CPU reduces a stacked axis sequentially up to 32
and in blocks beyond; P2 is a real mutant, killed only by a ≥ 64-term fixture.

## 7. Patches (`papers/f32_jax_files/`)

Both apply in order onto `9b27008`; verified by reversing both to an empty `git diff`, then
`git apply task1.patch` (build + full 15-cycle manifest on that tree) and `git apply task2.patch`
(build + runners).

| Patch | Files | Build after applying (jobs) | Other gates observed |
|---|---|---|---|
| `task1.patch` | `LeanNCD/Eval/Plan/Executable.lean`, `LeanNCD/Eval/Plan/EvalPlan.lean` (doc), `LeanNCD/Eval/Plan/AGENTS.md` (Contracts bullet), `test/Eval/Plan/ExecutableTest.lean`, `experiments/jax_bridge/EvalPlanCodegen.lean`, `spikes/AxisABoundaryProbe.lean` | `lake build` **8,673**; `lake build JaxExperiment` **8,514** (both equal to base — no new modules) | `lake env lean spikes/AxisABoundaryProbe.lean`: 0 errors; manifest J1–J15 (§6) |
| `task2.patch` | `experiments/jax_bridge/evalplan_affine_runtime.py`, new `EvalPlanAffineSmoke32.lean`, `evalplan_affine_smoke32.py`, `run-evalplan-affine32.sh` (mode 755) | **8,673** / **8,514** | `run-evalplan-affine32.sh` (stride 100): 56 fixtures / 160 checks pass, known divergence reproduced; stride-1 run §3; `run-evalplan-affine.sh` pass + module `cmp`-identical to base; `run-evalplan.sh` pass; f64 corpus 3,832/0 mismatches; Python cycles P1–P6 killed (re-run on this tree) |

`python_mutations.py` is the Python cycle driver (not part of either patch; run from the repo root
after both patches and `./run-evalplan-affine32.sh`). The README/doc sweep is NOT in the patches
(only the AGENTS.md Contracts bullet, since it describes Task 1's code).

## 8. Task breakdown recommendation

**One slice, two tasks** (smaller than F32-C; no phase split needed for Task 1).

- **Task 1 — gates + evidence label (Lean, atomic).** `Executable.lean`, `EvalPlan.lean` (doc),
  `AGENTS.md` Contracts bullet, `ExecutableTest.lean`, `EvalPlanCodegen.lean` (gates + all
  `#guard` fixtures incl. the "remaining binary32 cells" block), `spikes/AxisABoundaryProbe.lean`.
  Must be ONE commit: relaxing gate 2 without the codegen per-assignment einsum gate would open
  `lowerAssign` to binary32 for one commit, and the `aggregateEvidenceList` signature change breaks
  `EvalPlanCodegen` until it is updated. Fixtures: `ExecutableTest` 4 new aggregate guards + 2
  re-pointed (23, 24) + 4 re-pointed/new Task-5 guards + 3 f32 refusals; codegen 4 re-pointed
  fixture blocks (22–25) + 4 new cell blocks (bool source, Iverson, context, zero-pad). **15 Lean
  mutation cycles (J1–J15), ~45 min of manifest wall-clock.**
- **Task 2 — runtime + binary32 harness + evidence run + docs.** `evalplan_affine_runtime.py`,
  `EvalPlanAffineSmoke32.lean`, `evalplan_affine_smoke32.py`, `run-evalplan-affine32.sh`; gate =
  f64 curated byte-identity + f64 corpus + binary32 stride-1 run (§3); 6 Python cycles (P1–P6).
  Docs (as commands): `experiments/jax_bridge/README.md` (REJECTS table gains f32 columns; the
  "reference64-only" claims; the §3.1 limitation for BOTH labels), `papers/backend_missing_functionality.md`,
  `papers/f32_evalplan.md` §1.3 point 5 / §1.4 point 4 completion blockquote,
  `papers/jax_evalplan_architecture.md`. Value-grep: `orderedReference64`, `reference64-only`,
  `requireFloat64Plan`, `unsupportedStorageKind`, `jnp.float64`, `3,832`.

Reviewer test: a reviewer could approve Task 1's label/gates while rejecting Task 2's harness or its
§3.1 handling, so the split is real.

## 9. Decisions

Ruled by the user (2026-10-01), all three as recommended:

- **Gate 3: removed** (with its error constructor), §2.3.
- **Evidence size: full 3,832 retagged run + magnitude/cancellation fixtures**, §3/§4 — done;
  `termSum64` added for P2.
- **Every uncovered f32 cell gets a dedicated fixture**, §5 — done.

Still open:

1. **§3.1 subnormal / signed-zero divergence (NEW, the one that matters).** Bit-exactness of the
   ordered runtime is false on XLA CPU for subnormal values (eager and jit) and for `-0` reaching a
   `+0`-seeded fold under jit — in BOTH precisions, so the existing `orderedReference64` label's
   stated claim is already broader than what is measured. Options: (a) scope both labels' claims
   in their docs to "values whose fold neither produces nor consumes a subnormal, and (jit) no
   `+0 + -0`", keeping `KNOWN_DIVERGENT` as the pinned witness (prototype's choice, no code beyond
   the pin); (b) make the runtime/Lean refuse or flag subnormal inputs (cannot cover intermediates);
   (c) a separate slice to defeat FTZ/the simplifier (no XLA flag found that does). Needs a user
   ruling; it also touches the binary64 backend's documentation, which is outside this slice's
   stated scope.
2. `renderInputConstants` stays binary64-only (einsum smoke helper; `Float.toBits`), gated as
   `.einsumOnly`. If the plan wants it labelled dtype-specific rather than mode-specific, it needs
   its own gate; the prototype treats "einsum smoke helper" as the deciding property.
3. Reuse of `nonlinDtypeFor @ Nonlin.lean` (private) for `jaxRealCarrier`'s dtype half — not done
   (§2.1); plan-writer's call.

## 10. Authoring cost of this dispatch

Not measured with `token-report.py` from inside the dispatch. Rough self-count: ~95 tool calls for
the first pass plus ~45 for the follow-up (decisions §9), well past CLAUDE.md Rule 6's ~60-turn
dispatch cap (flagged, not hidden). Most of the overrun was waiting rather than work: the Lean
mutation manifest runs ~3 min per `ExecutableTest` cycle (~45 min for all 15), the f64 corpus
~10 min, the f32 stride-1 corpus ~13 min, and the session's command guard rejected several
compound shell commands, each costing a retry turn. A plan-writer re-running cycles should budget
~45 min for the manifest alone.

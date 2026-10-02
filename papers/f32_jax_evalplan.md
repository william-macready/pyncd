# F32-JAX: binary32 `affineReference` on the experimental JAX backend — implementation plan

**Status:** authored 2026-10-01 on branch `worktree-f32-jax-plan` from local `main` at `9b27008`.
Not executed. Fulfils `papers/f32_evalplan.md` §1.3 item 5 and §1.4 item 4.

**Companions** (all in `papers/`, all authoring-time artifacts. Read them, do not regenerate them):

- `f32_jax_spike_results.md`: the feasibility spike. **GO** for `affineReference` (bit-exact, 12/12
  eager+jit); **NO-GO** for `einsumOnly` (up to 122 ULP on a 64×64 contraction).
- `f32_jax_prototype_notes.md`: the explore+prototype record. Every value below was observed
  there, on the real module split and namespace, through the production gates (no shim).
  §3 holds observed values, §5 the audit, §6 the mutation log, §9 the decisions.
- `f32_jax_files/task1.patch`, `f32_jax_files/task2.patch`: every CODE change in this slice. Both
  were generated from the prototype tree and apply cleanly in order onto `9b27008` (re-checked by
  this write-up dispatch with `git apply --check`). Their file sets are disjoint. **Apply them; do
  not retype them.**
- `f32_jax_mutations_post.json`: 15 Lean cycles J1–J15, all `"task": "1"`, all PASS on the
  Task-1-only tree. `mutation-manifest.sh --check` reports `manifest OK: 15 entries, 15 selected,
  every old-string unique`. There is no `f32_jax_mutations.json`: §2 explains why no pre-existing-code
  gate is needed.
- `f32_jax_files/python_mutations.py`: the Python cycle driver, P1–P6 (Task 2).

**This plan holds** rationale, decisions, the §4 audit, fixtures, and every prose/docstring edit the
patches do NOT carry. **It does not hold transcribed code.** It contains no Lean code block, so there
is nothing here for `check-snippet.sh`. A fresh `papers/f32_jax_record.md` starts at Task 1's commit
and holds the execution-time measurements: manifest tables, the re-derived §4 audit, run outputs,
job counts and the close-out. This plan never holds them.

**How to read code during execution.** Every task lists its symbols as `identifier @ file`. Run
`rg -n <identifier> <file>` and read a ~40–60-line window. **Never read whole**:
`EvalPlanCodegen.lean` (~2,000 lines), `ExecutableTest.lean` (~1,900 lines), `Executable.lean`
(~870 lines), `README.md` (17k), `jax_evalplan_architecture.md` (143k), `eval_ir.md` (56k).
Long-running commands (the manifest takes ~45 min, the full binary32 run ~13 min, the binary64
corpus ~10 min) go in `run_in_background`.

---

## 1. Scope

### 1.1 Admitted by this slice

**Assign-only, context-free, binary32 plans through the `affineReference` lowering**, end to end:

- the production validators (`validateAndConstructKernel`, `validateAndConstructExecutable`);
- every `affineReference` codegen door in `EvalPlanCodegen.lean`;
- the shared ordered Python runtime, under a new evidence label, `ExecutionEvidence.orderedReference32`.

That label claims bit-exact agreement with the checked binary32 left fold (`runPreparedDense32`).
It is a separate claim from `orderedReference64`, never a reinterpretation of it. The fragment is
exactly the one the binary64 JAX backend already covers, so that backend now runs it in both
precisions.

### 1.2 Still refused, unchanged (owner in brackets)

| Construct | Where it is refused | Owner |
|---|---|---|
| binary32 under `einsumOnly` (any plan, any assignment, zero-step included) | `requireModeStorage .einsumOnly` at every einsum door; `einsumStorageAdmitted` in `validateEinsum` | **closed decision, no owner** (§6 item 2) |
| Boolean dest/source, tropical algebra, unary read, Iverson factor, contextful assignment | `checkJaxAssignSupport` / `requireNoIverson` / `renderAffineTerm`, unchanged under both kinds | permanent fail-loud boundary (README "What this backend REJECTS") |
| scan, scatter, pointwise/axiswise steps on JAX | `JaxExecutableWellFormed` / `lowerCheckPlanToCandidate` (`unsupportedStep`), in every precision | not this slice; no JAX scan/scatter/nonlinearity exists in either precision |
| mixed f32/f64 | Step 0b | F32-E (contingent) |

**`einsumOnly` binary32 is NOT deferred-but-planned.** It is refused, with no tolerance label, as a
closed decision for this slice. The spike showed `jnp.einsum` is not bit-exact in binary32. A
tolerance-based label (`orderedReference32WithinTolerance`-style) would be new evidence machinery
with its own comparison procedure, and no consumer has asked for it. If one ever does, it gets its
own spike and slice. This plan is not a placeholder for it.

### 1.3 Carry-forward from the master plan and the spike (re-derived, not inherited)

`f32_evalplan.md` §1.4 point 4 asked for a feasibility spike first; it returned GO for affine and
NO-GO for einsum. The spike described **two** f32-rejecting gates; the prototype found **three**
(prototype notes §1):

1. `requireFloat64Plan @ EvalPlanCodegen.lean`, with 7 call sites that split cleanly by mode.
   Einsum-only: `lowerPlan`, `generateForward`, `renderInputConstants`. Affine-only:
   `renderAffinePlanPositional`, `renderAffinePlanNamed`, `lowerCheckPlanToCandidate`. Plus the
   dispatcher `generateNamed`.
2. `jaxAssignSupported @ Executable.lean` (private, behind `checkJaxAssignSupport`), which
   hard-codes `.f64` and `admittedAlgebra`.
3. `validateAndConstructExecutable @ Executable.lean`'s plan-level `storageKind == .float64` check,
   with its own error `JaxExecutableValidationError.unsupportedStorageKind`. The spike never called
   this validator, which is why it missed this gate.

### 1.4 Known gaps (non-blocking, owned here rather than hidden)

- **The corpus run is structural coverage, not proof of fold-order fidelity.** The generator's
  inputs are the integers 1–4. Their products and sums are exact in binary32, so a reassociated fold
  would agree on all 3,832 cases. Fold-order fidelity rests on the magnitude/cancellation fixtures:
  `reduction64`, `termSum64`, `factorProduct3` and `contraction64x64`, which kill P1–P3 (§5 Task 2).
  The plan's own evidence claim must say this; README text is in Task 2 phase 2.
- **Subnormal and signed-zero values are not bit-exact on XLA CPU, in either precision** (§3.6).
  This is pinned as an exact known divergence (`KNOWN_DIVERGENT`), documented for both labels, and
  not fixed.
- **Two helpers stay binary64-only.** `renderInputConstants` is the einsum smoke's constants
  helper with a `Float.toBits` payload, so it takes the `.einsumOnly` gate; this settles prototype
  §9 open item 2 on "einsum helper", not "dtype-specific". `buildAssignFixture` runs
  `runDenseAssign`, so f32 fails loud there ("Dense run failed"); its binary32 counterpart is the
  driver-local `buildAssignFixture32` (Task 2).

### 1.5 One slice, two tasks (adopted from prototype §8)

| Task | Deliverable | Diff (`git apply --stat`) | Fixtures | Mutation cycles |
|---|---|---|---|---|
| 1 | gates 1 and 2 storage-keyed, gate 3 removed, `orderedReference32` + `orderedReferenceFor` + keyed aggregation, every Lean fixture | 6 files, +404/−138 | `ExecutableTest`: 9 new `#guard` lines (4 aggregate, 5 policy/kernel), fixtures 23/24 and the "Task 5" block re-pointed, 12 `aggregateEvidenceList` call sites re-threaded; `EvalPlanCodegen`: 7 new `#guard` lines, fixtures 22–25 re-pointed | **15** Lean (J1–J15), ~45 min wall-clock |
| 2 | parametrized runtime, binary32 harness (4 routes), full-corpus evidence run, doc sweep (both precisions' caveat) | 4 files, +563/−22 | 7 named + 8 standalone-assign + 2 positional + 3,832 corpus = **3,849** Python fixtures | **6** Python (P1–P6) |

**Reviewer test.** A reviewer could approve Task 1's label and gates while rejecting Task 2's
harness, its evidence claim, or its handling of the XLA finding. So the split is real.

**Task 1 must be ONE commit.** If gate 2 were relaxed without the new standalone einsum door,
`lowerAssign` would accept binary32 for one commit. And the `aggregateEvidenceList` signature
change breaks `EvalPlanCodegen.lean` until its call sites are updated.

Task 2 runs as **two dispatches** (§5): phase 1 is code plus evidence, phase 2 is the doc sweep.
This is a dispatch-budget split (`slice-plan` §5), not a third task. The doc sweep is pure
commands.

---

## 2. Global constraints (exact values)

- **Scope is exact:** assign-only, context-free, `affineReference`-only, `.float32`. **Untouched in
  every precision:** scans, nonlinearities, scatter, and every non-JAX backend. The patches edit no
  file outside the 10 they list.
- **Storage-keyed, with no wildcard arm**, in all four new functions: `orderedReferenceFor`,
  `jaxRealCarrier`, `einsumStorageAdmitted` and `modeAdmitsStorage`. A later carrier fails to
  compile until it decides.
- **`orderedReferenceFor` is the ONE place a storage kind selects a reference label.** It is shared
  by the per-kernel label (`candidateEvidenceLabel`) and the plan fold (`aggregateEvidenceList`).
  Do not add a second selection.
- **Einsum emitter and validator share one predicate.** `modeAdmitsStorage .einsumOnly` defers to
  production `einsumStorageAdmitted`, the same predicate `validateEinsum` conjoins. This keeps
  the documented "`validateEinsum` acceptance implies `lowerAssign` renders" invariant true, in the
  same shared-recomputation pattern as `einsumTermLabelExtents`/`einsumLabelLimit`.
- **The JAX error vocabulary is kept.** Einsum refusals keep `JaxCodegenError.unsupportedStorageKind
  .float32`, so the einsum halves of fixtures 22/25 are unchanged.
  `JaxExecutableValidationError.unsupportedStorageKind` is **deleted**. It is orphaned by gate 3's
  removal (§3.3), and unlike the closed-family constructors in `Error.lean`, its only producer was
  the gate itself. A producer-less constructor in a 4-constructor validator error type would be
  dead code, not part of a retained family.
- **Binary64 behaviour is preserved bit for bit:**
  - the curated affine module is `cmp`-identical (11,509 bytes);
  - the 3,832-case corpus has 0 mismatches at 3,424,195 bytes;
  - `run-evalplan.sh` passes;
  - no pre-existing binary64 `#guard` is edited except where the patch visibly re-points it.

  No pre-existing-code manifest is needed. J3's first failure is the PRE-EXISTING binary64
  Boolean-destination fixture, and J15 kills the binary64 Iverson donor, so the binary64 refusal
  surface is already mutation-pinned.
- **The Python runtime stays one parametrized implementation.** `dtype=jnp.float64` is the default,
  so every existing caller is unchanged. Do not fork it. `_require_dtype` never casts. Float32
  needs no x64.
- **Values are exact bit patterns.** In Lean they go through `Float32.toBits`; in Python through
  `np.uint32` bits. Every value in this plan is OBSERVED (prototype §3). If the real run differs,
  STOP (§8); do not edit the expectation.
- **No `File.lean:NNN`** in anything you ship. Cite identifiers. The ONE exception is the
  manifest's own `expect` strings, which are line-anchored by design (next bullet).
- **Line-anchored expects:** J1–J15's `expect` strings cite `ExecutableTest.lean:<line>` and
  `EvalPlanCodegen.lean:<line>` on the Task-1 tree. **Any prose edit to those two files must keep
  their line count unchanged.** Task 1 step 3's edits do; the edits were applied, `wc -l` stayed
  1,991, `lake build JaxExperiment Eval.Plan.ExecutableTest` was green, and J12/J15 were re-run and
  PASSED by this write-up dispatch. `Executable.lean` is not line-anchored: no expect cites it.
- **Build:** `"$HOME/.elan/bin/lake" build` gives **8,673 jobs** and `lake build JaxExperiment`
  gives **8,514**. Both equal the base, because neither patch adds a Lake module. The new
  `EvalPlanAffineSmoke32.lean` is a driver with no Lake target, like every other driver in
  `jax_bridge`. **A green `lake build` does not typecheck it; only `run-evalplan-affine32.sh` does**
  (README's standing warning).

---

## 3. Design (as prototyped; the patches carry the code)

### 3.1 Gate 2: a storage-keyed real carrier (`Executable.lean`, Task 1)

New private `jaxRealCarrier` maps `.float64` to `(.f64, admittedAlgebra)` and `.float32` to `(.f32,
admittedAlgebraF32)`. `jaxAssignSupported` gains a `kind` argument and compares destination dtype,
algebra and source dtype against that pair. `checkJaxAssignSupport` passes `checked.storageKind`,
the field that already selects its `checkAssign`/`checkAssignF32` re-run (F32 Task 5).

**Why keyed, not "accept `.f64 ∨ .f32`":** the symmetric form would accept an `f64` slot under
`.float32` evidence if the re-run were ever weakened. Keying makes the policy self-standing. `bool`
is neither carrier's real dtype, and the tropical algebras (including `admittedAlgebraF32Max`/`Min`)
are neither carrier's sum-product, so every existing refusal holds under both kinds, at its original
locator.

**Reuse decision (prototype §9 open item 3, settled here):** `nonlinDtypeFor @ Nonlin.lean` is the
same `StorageKind → ScalarDType` half, but private, and it is the only other such map in
`LeanNCD/`. It is not shared, for two reasons. `jaxRealCarrier` pairs the dtype with an algebra
that Nonlin does not need. And sharing would mean promoting a private helper into Nonlin's public
API, or into a common module, for a 2-arm match, which the prototype never built or verified.
Flagged as a cleanup candidate if a third `StorageKind → ScalarDType` caller appears (§6 item 4).

### 3.2 Gate 1: mode-aware, plus a dedicated standalone einsum door (`EvalPlanCodegen.lean`, Task 1)

- `LoweringMode` moves from §7 to §1 of the file, so the gate can name it.
- `requireFloat64Plan` is replaced by `requireModeStorage (mode) (kind)` over `modeAdmitsStorage`.
  Each of the 7 sites passes its own mode (§1.3 list), and `generateNamed` passes `mode`.
- **The new door:** `lowerAssign` and `loweringToEinsumCandidate` open with
  `requireModeStorage .einsumOnly checked.storageKind`. Before this slice, these two standalone
  einsum entries had no plan gate and relied on gate 2 alone. Once gate 2 admits binary32, this
  call is the ONLY thing keeping a binary32 assignment out of `jnp.einsum`. Fixture 22 pins it:
  the assignment is refused while `requireJaxSupport` on the SAME assignment is `.ok`. J9 and J10
  pin it as well.
- **Rejected alternative:** keep gate 1 mode-agnostic and check only inside the einsum emitter. A
  zero-step f32 plan under `generateForward` has no node for an emitter check to see, so the
  plan-level einsum door must stay plan-level.

### 3.3 Evidence: `orderedReference32`, and why gate 3 is provably redundant (Task 1)

**What changes.** `ExecutionEvidence` gains `orderedReference32`. `candidateEvidenceLabel` maps
`.affineTable k` to `orderedReferenceFor k.semanticAssignment.storageKind`, and the private
`JaxKernel` constructor's `aligned := rfl` still closes. `aggregateEvidenceList` takes `kind` first
and returns `orderedReferenceFor kind` iff every step carries it, else `.optimizationExperiment`.
Every caller passes the plan's kind:

- `JaxExecutableCandidate.aggregated`, as `source.plan.storageKind` (the field order allows it);
- `JaxExecutableWellFormed` and its `Decidable` instance;
- `validateAndConstructExecutable` and `lowerCheckPlanToCandidate`;
- 12 `ExecutableTest` sites (3 `testAggregate*` literals and 9 candidate constructions, counted
  against the patch);
- `spikes/AxisABoundaryProbe.lean`, which is in no Lake target; `lake env lean` elaborates it clean.

**Gate 3 is removed, and here is why it is redundant.** Its own docstring gave one reason for
existing: `aggregateEvidenceList #[]` was `orderedReference64`, so a zero-step `.float32` candidate
would otherwise get a reference64 claim. The proof fields already carry the plan's kind, so the
argument from them covers every case:

1. **The executable's evidence is the plan-kind fold, by construction.**
   `JaxExecutableCandidate.aggregated` (a proof field) and the `decide` check in
   `validateAndConstructExecutable` both force
   `evidence = aggregateEvidenceList source.plan.storageKind (steps.map (·.evidence))`.
   `aggregateEvidenceList k` returns only `orderedReferenceFor k` or `.optimizationExperiment`.
   **So an executable's reference claim, if it has one, is always its own plan's kind.**
   - A zero-step `.float32` plan folds to `orderedReference32`, its truthful claim. This is the
     exact case gate 3 existed for. It is pinned by `ExecutableTest` fixture 23, `EvalPlanCodegen`
     fixture 23, and J7.
2. **A step cannot carry the plan's label while being validated under the other kind.**
   - A step kernel's label is derived only inside `validateAndConstructKernel`, from its own
     `semanticAssignment.storageKind` (the private constructor's `aligned`).
   - `stepTiedToPreparedStep` requires the kernel's `signatureContext ==
     prepared.plan.raw.tensorSigs`.
   - The kernel's own `checkJaxAssignSupport` re-ran its kind's checker over that table.

   So a kernel stamped with the other kind's label cannot be tied to this plan. If it somehow were,
   point 1 still folds it to `.optimizationExperiment`, never to a reference claim. That is pinned
   by the cross-kind guards `aggregateEvidenceList .float32 #[.orderedReference64]` and
   `.float64 #[.orderedReference32]`, both giving `.optimizationExperiment`.
3. **The keying is enforced at compile time, not only at validation.** J12 mutates
   `lowerCheckPlanToCandidate` to aggregate under `.float64`. The build fails at the candidate's
   `aggregated := rfl` with a `Type mismatch`. A candidate builder that ignores the plan's kind does
   not typecheck.

**Not added:** a `storageKind` conjunct in `stepTiedToPreparedStep`. Point 2 shows it is redundant,
and the user ruled "remove", not "replace". Fixture 24 is re-pointed: the zero-step f32 plan with a
bad binding now REACHES `checkPreparedBindings` and reports the same located
`invalidBindings (.materializedSlot (.slotOutOfRange 99 2))` as its binary64 control. Binding
validation is not skipped for binary32.

### 3.4 Python runtime: one implementation, parametrized (`evalplan_affine_runtime.py`, Task 2)

`run_assign`, `run_plan_positional` and `run_named` take `dtype=jnp.float64`, and `_run_term`/
`_run_node` thread it. Every constant and accumulator is `dtype(0.0)` or `jnp.zeros|ones(…, dtype)`.
New `_require_dtype` refuses an unsupported dtype and any input of a different dtype, never casting,
and calls `require_x64()` only for float64. Safe indices are int64 under x64 (the binary64 path is
unchanged) and int32 otherwise, so float32 never needs x64. The diff is ~40 lines, and the binary64
path is byte-identical (§2), so no fork is needed.

### 3.5 The binary32 harness (Task 2)

**`EvalPlanAffineSmoke32.lean`** is a driver with no Lake target. Its local `pyUInt32ListLit` and
`pyTensorEntry32` emit `Float32.toBits` payloads with a `"dtype": "float32"` tag. They are kept out
of `EvalPlanCodegen.lean` on purpose: putting them there would shift Task 1's line-anchored
expects. It has four routes:

| Route | Builder | Asserts per fixture before rendering | Fixtures |
|---|---|---|---|
| named | `buildNamedFixture32` (the `prepare32` pipeline) | `generateNamed .einsumOnly` refuses `unsupportedStorageKind .float32`; `validateAndConstructExecutable` evidence is `orderedReference32` | the 6 spike fixtures plus `termSum64` (one node, 64 terms `A + 62×B + D`, `A = 2^24`, `B = 1`, `D = −2^24`; reference `0`) |
| corpus | `retag32` | as named | all 3,832 `enumPrograms` cases retagged `.typedTensor .f32` |
| standalone assign | `buildAssignFixture32` (new, over `checkAssignF32` + `runDenseAssign32`) | `lowerAssign` refuses; the affine kernel validates as `orderedReference32` | `KernelDense32Test.{f32Identity, f32ReductionRounding, f32MultiplicationRounding, f32FactorOrder, f32Efp, f32Zerd, f32TermOrder}` + `f32Pad` (`EvalPlanCodegen.f32PadSigs/f32PadAssign`) |
| positional | `buildPositionalFixture32` (over `runDensePlan32`) | `lowerPlan` refuses | `EvalPlan32Test.{f32ProductChain, f32ReductionGraph}` (the first has a dependent second node) |

`retag32` makes two adjustments, each forced by a failure observed in the prototype: it declares
every undeclared statement output as binary32 over its `.free` LHS axes, and it drops undeclared
extra inputs. Without them the run fails with `storageKindMismatch "P" .float32 .float64` and then
`unsupportedDtype "Y: mixed f32/f64 storage in one schedule"`. No `Gen.lean` change is needed.

**`evalplan_affine_smoke32.py`** asserts x64 is DISABLED, rebuilds the `np.uint32` bits, and runs
eager plus `jax.jit` with `dtype=jnp.float32`, comparing bits exactly. It pins
`KNOWN_DIVERGENT = {"f32Identity": {1, 2}}` (§3.6): every other position must be exact, and the
listed positions must diverge exactly as observed, so it fails loud if XLA ever stops diverging. It
also pins two refusals: the binary64 default refuses binary32 inputs (the x64 gate), and
`dtype=float32` refuses float16.

**`run-evalplan-affine32.sh [STRIDE [JIT_STRIDE]]`** defaults to `100 1`. Non-corpus fixtures are
always JIT-checked.

### 3.6 The XLA CPU subnormal / signed-zero finding: both precisions, documented, not fixed

**How it was found.** The first standalone-assign fixture, `f32Identity`, maps
`Y[i] := X[i]` over `[+0, −0, least subnormal]`. The Lean reference gives `[+0, +0, 0x00000001]`:
the fold seeds `+0`, and `+0 + −0 = +0`. Prototype §3.1 then probed XLA directly (JAX 0.10.0, CPU),
and the orchestrating session independently reproduced the result in both precisions, eager and
jit:

| Behaviour | f32 | f64 | When |
|---|---|---|---|
| flushes subnormal operands/results of ARITHMETIC to zero (a bare gather preserves them) | yes | yes | eager and jit; `XLA_FLAGS=--xla_cpu_enable_fast_math=false` does not change it |
| simplifies the reduction seed `+0 + x` to `x` (a `−0` survives where the fold gives `+0`) | yes | yes | jit only |

**This is not binary32-specific.** The already-shipped `orderedReference64` claim has the same gap.
It was never exercised because no binary64 fixture or corpus input is a subnormal or `−0`. The
corpus inputs are the integers 1–4, and a grep of the binary64 affine drivers and verifiers finds
no `-0.0`, `0x8000000000000000`, `5e-324` or `ofBits` literal.

**Decision (user ruling): option (a).** Both labels' documentation is scoped to normal-range
values, with the jit signed-zero clause; `KNOWN_DIVERGENT` stays as the pinned witness; no code
beyond the pin. Rejected alternatives:

- **(b) refuse or flag subnormal inputs.** It cannot cover intermediates: a product of normals can
  be subnormal.
- **(c) a separate slice to defeat XLA's flush-to-zero and its algebraic simplifier.** No XLA flag
  that does either was found, and (a)'s scoping already stops either label from over-claiming.

The doc fix covers BOTH precisions in this slice (Task 2 phase 2). Fixing only the new label would
leave the old label's identical over-claim standing.

---

## 4. Sibling-door audit (skill §2): every JAX door after this slice

This is the authoring-time snapshot, from prototype §5. **Task 1 step 5 re-derives it cell by cell
against the tree and appends the result to `f32_jax_record.md`. Task 2 phase 1 step 6 appends the
Python cells.**

- **R** = required (renders, or the candidate validates).
- **F** = forbidden (a located typed error before any Python, candidate or evidence).
- **(c)** = correct only because an upstream check holds.
- **SI** = silently ignored.

**Table A: case × door**

| Case | f64 einsum | f64 affine | f32 einsum (after) | f32 affine (after) |
|---|---|---|---|---|
| assign-only valid | R (`optimizationExperiment`) | R `orderedReference64` | **F `unsupportedStorageKind .float32`** at plan doors (fixture 22/25, J8), standalone doors (fixture 22, J9/J10), validator `einsumStorageAdmitted` (`ExecutableTest`, J1) | **R `orderedReference32`** (fixture 22, `ExecutableTest`, J2/J6/J11/J12; Python every route) |
| bool destination | F | F | F storage | **F `destinationDType 7 2 .bool`** (`ExecutableTest` `f32BoolDestAssign`, J3) |
| bool source | F | F | F storage (`f32BoolSourcePrepared?`) | **F `unsupportedSourceDType 0 0 0 .bool`** at `generateNamed`, `renderAffinePlanPositional`, `lowerCheckPlanToCandidate` (J13: ONLY the f32 fixture fails) |
| unary read | F | F | F storage | **F `unaryFactor 7 0 0`** (`ExecutableTest`, J5) |
| tropical algebra | F | F | F storage | **F `unsupportedAlgebra 7 admittedAlgebraF32Max`** (`ExecutableTest`, J4) |
| Iverson factor | F | F | F storage (`f32IversonPrepared?`) | **F `iversonFactor 0 0 1`** at `generateNamed`, `lowerCheckPlanToCandidate` (J15; dtype-blind, so the f64 donor dies too) |
| contextful | F | F | **F storage** at `lowerAssign`, `loweringToEinsumCandidate` (`f32CtxAssign`) | **F `unsupportedContext 0 #[2]`** at `renderAffineAssign`, `loweringToAffineTableCandidate` (J14: ONLY the f32 fixture fails) |
| zero-pad label-extent mismatch | F `labelExtentMismatch` | R | **F storage** (precedes `labelExtentMismatch`; `f32PadAssign`) | **R**, kernel `orderedReference32` (`f32PadAssign`); Python exact (`f32Pad`, P5) |
| zero-step plan | R | R `orderedReference64` | **F storage**, plan-level only (fixture 25) | **R `orderedReference32`** (fixture 23 in both files; J7) |
| positional route | R | R | F storage (`lowerPlan`, asserted per fixture) | **R**, Python exact (`f32ProductChain`, `f32ReductionGraph`; P6) |
| standalone-assign route | R | R | F storage (`lowerAssign`, asserted per fixture) | **R**, kernel `orderedReference32`; Python exact on 7 of 8, `f32Identity` = the §3.6 pinned divergence |

**No SI cell, and no gap left.** Every f32 cell names a dedicated fixture and a mutation that kills
it. The `f32Identity` cell is the one place the runtime is not bit-exact. It is pinned as an exact
divergence, not ignored.

**Table B: binary64 literals the f32 path now reaches**

| Site | Reached by f32? | Class | Pin |
|---|---|---|---|
| `.f64` / `admittedAlgebra` @ `jaxAssignSupported` (×3) | yes | **fixed** → `jaxRealCarrier kind` | J2–J5, J13 |
| `.orderedReference64` @ `candidateEvidenceLabel` | yes | **fixed** → `orderedReferenceFor` | J6 |
| `.orderedReference64` @ `aggregateEvidenceList` | yes (zero-step) | **fixed** → keyed by `kind` | J7, J12 |
| `storageKind == .float64` @ `validateAndConstructExecutable` | yes | **deleted** (§3.3) | fixtures 23/24, J7 |
| `requireFloat64Plan` ×7 | yes | **fixed** → `requireModeStorage mode` | J8, J11 |
| none @ `lowerAssign` / `loweringToEinsumCandidate` | yes | **added** einsum door | J9, J10 |
| `jnp.float64` / `int64` constants @ runtime | yes | **fixed** → `dtype` / `_index_dtype()` | P1–P6 |
| `Float.toBits` @ `pyTensorEntry` / `renderInputConstants` | no | **(c)**: only binary64 drivers and the einsum-gated `renderInputConstants` reach them; f32 uses the driver-local `pyTensorEntry32` | fixture 22/25 (`renderInputConstants` refuses) |
| `runDenseAssign` @ `buildAssignFixture` | f32 fails loud ("Dense run failed") | **(c)**: a binary64-only helper | §1.4 |

**Doors to open during the audit even though no diff shows them:**

- `validateAffineTable` (via `jaxSupportOk`: carrier-keyed now, no other literal);
- `requireNoIverson` and `renderAffineTerm`;
- `einsumTermLabelExtents`;
- `buildAssignFixture`;
- `EvalPlanSmoke.lean` / `evalplan_smoke.py` (einsum, binary64);
- `EvalPlanAffineSmoke.lean` / `evalplan_affine_smoke.py` / `evalplan_affine_corpus.py` /
  `scaling_probe.py` (binary64 callers on the default `dtype`).

---

## 5. Tasks

### Task 1: storage-keyed gates and the `orderedReference32` label (Lean, one commit)

**Dispatch:** Sonnet 5, medium effort. The work is apply, verify, four line-preserving prose edits,
and the audit. The soundness judgement already sits in §3.3 and belongs to the reviewer:
**per-task review at Opus 5.5, high effort**, aimed at §3.3's three points and §4 Table A.

**Files** (under `leanncd/`): `LeanNCD/Eval/Plan/Executable.lean`, `LeanNCD/Eval/Plan/EvalPlan.lean`
(doc), `LeanNCD/Eval/Plan/AGENTS.md` (Contracts bullet), `test/Eval/Plan/ExecutableTest.lean`,
`experiments/jax_bridge/EvalPlanCodegen.lean`, `spikes/AxisABoundaryProbe.lean`; plus new
`papers/f32_jax_record.md`.

**Symbols (`rg -n`, window-read):**

- `@ Executable.lean`: `ExecutionEvidence`, `orderedReferenceFor`, `candidateEvidenceLabel`,
  `jaxRealCarrier`, `jaxAssignSupported`, `checkJaxAssignSupport`, `einsumStorageAdmitted`,
  `validateEinsum`, `aggregateEvidenceList`, `JaxExecutableCandidate`, `JaxExecutableWellFormed`,
  `JaxExecutableValidationError`, `validateAndConstructExecutable`, `stepTiedToPreparedStep`.
- `@ EvalPlanCodegen.lean`: `LoweringMode`, `modeAdmitsStorage`, `requireModeStorage`,
  `lowerAssign`, `loweringToEinsumCandidate`, `generateNamed`, `lowerCheckPlanToCandidate`,
  `retag32Raw`.
- `@ ExecutableTest.lean`: `f32DestSigs`, `f32DestAssign`, `f32BoolDestAssign`.

**Step 1: apply and build.**
```bash
git apply papers/f32_jax_files/task1.patch
cd leanncd && "$HOME/.elan/bin/lake" build && "$HOME/.elan/bin/lake" build JaxExperiment
"$HOME/.elan/bin/lake" env lean spikes/AxisABoundaryProbe.lean   # 0 errors
```
Expect 8,673 and 8,514 jobs, the same as the base. Record your own numbers.

**Step 2: the mutation manifest** (background, ~45 min):
```bash
bash leanncd/scripts/mutation-manifest.sh --task 1 --out <scratch>/t1.md leanncd papers/f32_jax_mutations_post.json
```
Expect 15/15 PASS; keep the `--out` table for the record (created in step 5). A FAIL with "expected
text not in mutated build log" is a STOP (§8), not an expect edit.

**Step 3: the prose edits the patch does NOT carry.** Each is a line-for-line replacement. Find each
with the `rg` shown and replace exactly that text. Afterwards, **`wc -l
experiments/jax_bridge/EvalPlanCodegen.lean` must still be 1991.** All four were applied, built,
and line-count-checked by this write-up dispatch (§2).

1. `EvalPlanCodegen.lean` module docstring (`rg -n "accepts the context-free \`f64\` sum-product"`):
   `` * `affineReference` — accepts the context-free `f64` sum-product, assignment-only fragment, with``
   becomes
   `` * `affineReference` — accepts the context-free `f64`/`f32` sum-product, assign-only fragment, with``.
2. `generateNamed`'s docstring (`rg -n "only for the context-free \`f64\` sum-product"`):
   `` only for the context-free `f64` sum-product,`` becomes
   `` only for the context-free `f64`/`f32` sum-product,``.
3. The fixtures 22–25 section header (`rg -n "fixtures 22-25: the plan-level JAX storage gates"`).
   This is the 13 lines from the `/-! ## …` line through `… every remaining renderer/generator. -/`.
   Replace them with exactly these 13 lines:
   ```text
   /-! ## f32 slice Task 2, fixtures 22-25: the JAX storage gates (re-pointed by F32-JAX)

   Before slice F32-JAX this backend was reference64-only and refused every `.float32` checked plan
   at every candidate/generator/renderer entry, before iterating nodes, validating prepared bindings,
   or producing any text. Since F32-JAX the gate is mode-aware (`requireModeStorage`): `einsumOnly`
   still refuses binary32 at every door; `affineReference` renders it under `orderedReference32`.

   Fixture 22 uses a NONEMPTY f32 plan (`GraphCheckTest`'s fixture-6 graph, rebuilt locally — this
   library cannot import the default-build test modules) and pins both halves, at the plan-level and
   the standalone doors. Fixture 23 uses the ZERO-STEP, all-input plan, where per-node checks are
   vacuous and the empty fold is the plan's own claim (`orderedReference32`). Fixture 24 rebuilds
   fixture 23 with an out-of-range materialized binding, now reaching `invalidBindings`. Fixture 25
   feeds fixture 23's valid plan to every remaining renderer/generator. -/
   ```
4. `Executable.lean`'s "JAX support policy (Task 4.5)" section docstring
   (`rg -n "this backend is reference64-only; slice F32-JAX owns"`). It is not line-anchored.
   Replace the first three lines of its last paragraph:
   ```text
   Binary32 is refused here too (this backend is reference64-only; slice F32-JAX owns any `jnp.float32`
   artifact), but it is refused BY THE SUPPORT POLICY as a located `destinationDType … .f32`, not by
   the re-run.
   ```
   with:
   ```text
   Binary32 is admitted here since slice F32-JAX (`jaxRealCarrier` keys the policy's real carrier off
   the evidence's storage kind); a refusal it does earn (a Boolean destination, say) comes FROM THE
   SUPPORT POLICY as a located error, not from the re-run.
   ```
   The paragraph's last sentence ("Running the binary64 checker over binary32 evidence …") stays.

Then rebuild: `lake build JaxExperiment Eval.Plan.ExecutableTest` should be green. Re-run the two
`EvalPlanCodegen`-anchored cycles below the edits:
`mutation-manifest.sh leanncd papers/f32_jax_mutations_post.json J12 J15` should give 2/2 PASS.

**Step 4: value-grep the Lean tree** (only the allowed hits should remain):
```bash
rg -n "requireFloat64Plan|JaxExecutableValidationError.unsupportedStorageKind|reference64-only" leanncd/LeanNCD leanncd/experiments leanncd/test leanncd/spikes
```
Allowed hits:

- `requireModeStorage`'s docstring ("it was `requireFloat64Plan`");
- the re-pointed section header from step 3.3 ("Before slice F32-JAX this backend was
  reference64-only");
- `ExecutableTest.lean`'s historical narration of the pre-F32-JAX policy in the Task-5 and
  fixture-23 blocks, which already says "Slice F32-JAX then ADMITTED this" / "replaced that gate".

Anything else is a stale claim the patch missed: fix it, keeping the line count if it is in
`EvalPlanCodegen.lean` or `ExecutableTest.lean`.

**Step 5: re-derive §4 Tables A and B against the tree, cell by cell.** Open each door the cell
names with `rg -n`; use no line numbers. Append the result to `papers/f32_jax_record.md` (create it
with a one-line header naming this plan and the base SHA). Every f32 cell must name its fixture and
its J-cycle. An SI cell is a STOP.

**Commit:** `feat(leanncd): binary32 affineReference evidence on the JAX backend (F32-JAX Task 1)`.

---

### Task 2: runtime, binary32 harness, full-corpus evidence, docs (two dispatches)

**Files:** `leanncd/experiments/jax_bridge/evalplan_affine_runtime.py`; new
`EvalPlanAffineSmoke32.lean`, `evalplan_affine_smoke32.py` and `run-evalplan-affine32.sh` (mode
755) in the same directory; phase 2's doc files (listed there); `papers/f32_jax_record.md`.

**Symbols:**

- `@ evalplan_affine_runtime.py`: `run_assign`, `run_plan_positional`, `run_named`, `_run_term`,
  `_run_node`, `_require_dtype`, `_index_dtype`, `require_x64`.
- `@ EvalPlanAffineSmoke32.lean`: `retag32`, `prepare32`, `buildNamedFixture32`,
  `buildAssignFixture32`, `buildPositionalFixture32`, `termSum64Prog`.
- `@ evalplan_affine_smoke32.py`: `KNOWN_DIVERGENT`, `require_bits32`.

#### Phase 1: code plus evidence (one commit)

**Dispatch:** Sonnet 5, medium. Mostly long-running commands (background them). The judgement is
in reading the outputs against the observed values below.

**Step 1: the binary64 baseline, BEFORE applying.** On the Task-1 tree, run
`leanncd/experiments/jax_bridge/run-evalplan-affine.sh` (it passes) and copy
`.cache/generated_evalplan_affine_smoke.py` to a scratch path. This is the byte-identity reference.
Run `setup-python.sh` first if `.cache/python` is absent: Python 3.13, JAX/JAXlib 0.10.0,
NumPy 2.5.2, CPU.

**Step 2: apply and build.** `git apply papers/f32_jax_files/task2.patch`, then `lake build` gives
8,673 jobs and `lake build JaxExperiment` gives 8,514, unchanged. Fix one comment the patch got
wrong: `run-evalplan-affine32.sh`'s header says "the six spike fixtures plus every STRIDE-th
PropertyOracle corpus case". Make it "the 7 named fixtures (6 spike + `termSum64`), 8
standalone-assign and 2 positional fixtures, plus every STRIDE-th PropertyOracle corpus case".
Re-wrap within the comment block; it is not line-anchored.

**Step 3: binary64 preservation.** `run-evalplan-affine.sh` passes, and `cmp` of the new
`.cache/generated_evalplan_affine_smoke.py` against step 1's copy is clean (observed: 11,509
bytes). `run-evalplan.sh` passes. `run-evalplan-affine-corpus.sh` (background, ~10 min) prints
`source_cases=3832 eager_mismatches=0 feature_masks=45 jit_cases=65` and `artifact_bytes=3424195`;
the observed timings were generation 26.8 s, eager 575.8 s, JIT 6.4 s; record yours.

**Step 4: the binary32 stride-100 run, then the Python cycles** (in this order: the cycle driver
reads the stride-100 module).

- `./run-evalplan-affine32.sh` (defaults `100 1`). Observed: 56 fixtures (46 named, 8 assign, 2
  positional), 160 output checks, `known XLA CPU divergence reproduced exactly: f32Identity
  positions [1, 2]`.
- Then: `.cache/python/bin/python ../../../papers/f32_jax_files/python_mutations.py` (from
  `leanncd/experiments/jax_bridge/`; the script resolves the runtime from its own path). It prints
  `(returncode, last line)` per mutant. It has no verdict exit code, so check each one yourself:

| Mutant | Must observe (nonzero returncode, last line) |
|---|---|
| unmutated / restored | `0`, the `56 binary32 fixtures, 160 eager/jit output checks: bit-identical …` line |
| P1 reduction via `jnp.sum(mat, axis=1)` | `reduction64 eager Y: not bit-identical at 0: 0x41f80000 vs 0x00000000` |
| P2 term sum via `jnp.sum(stacked, axis=0)` | `termSum64 eager Y: not bit-identical at 0: 0x41f80000 vs 0x00000000` |
| P3 factor product reversed | `factorProduct3 eager Y: not bit-identical at 1: 0xbf5b3ca1 vs 0xbf5b3ca5` |
| P4 `_require_dtype` input check off | `float32 dtype accepted float16 inputs` |
| P5 zero-pad mask ignored | `f32Pad eager result: not bit-identical at 2: 0x40a00000 vs 0x00000000` |
| P6 positional nodes reversed | `TypeError: reshape requires ndarray or scalar arguments, got <class 'NoneType'>` |

P2 is real, not an equivalent mutant. XLA CPU sums a stacked axis sequentially up to 32 terms and in
blocks at 64 (prototype §6 P2 probe), so only `termSum64` kills it. Do not shrink that fixture.

**Step 5: THE EVIDENCE GATE, the full corpus, stride 1, JIT on every case** (background, ~13 min):
`./run-evalplan-affine32.sh 1 1`. Observed in the prototype (the values to match, not to
re-derive):

- `kinds={'named': 3839, 'assign': 8, 'positional': 2}`, which is 3,849 fixtures: 3,832 corpus,
  7 named, 8 standalone-assign, 2 positional;
- `eager_checks=5873 jit_checks=5873`, which is **11,746 checks**;
- **0 mismatches** outside the pinned `f32Identity [1, 2]`;
- eager 524.8 s, JIT 190.7 s, about 13 min wall-clock including the three `lake build`s;
- generated module `.cache/generated_evalplan_affine_smoke32.py` is **3,657,456 bytes**
  (`wc -c`).

Every fixture is JIT-checked, unlike the binary64 runner's 45 representatives. **That is deliberate,
and recorded with its reason.** The measured cost (~3 min JIT) is acceptable, and a per-case JIT
claim is strictly stronger than a representative sample. The runner keeps `JIT_STRIDE`, so a
routine run may sample, but THIS slice's evidence claim is the stride-1/1 run. Paste the two summary
lines and the module size into the record. Counts must match exactly. Timings are recorded, not
matched.

**Step 6: Python cells of §4.** Append to the record the observed outcome for the positional,
standalone-assign and zero-pad rows. Each must name its fixture and its P-cycle.

**Commit:** `feat(jax_bridge): binary32 ordered affine runtime and full-corpus evidence (F32-JAX
Task 2)`. Hand phase 2 the SHA via `.claude/skills/slice-plan/split-handoff-template.md`, together
with phase 2's file list below.

#### Phase 2: documentation sweep, both precisions' caveat included (one commit)

**Dispatch:** Sonnet 5, low/medium. Every edit is a grep plus a replacement; the wording below is
settled. **The subnormal/signed-zero caveat (§3.6) is a named deliverable, not part of a "general
sweep".** Steps 1–3 below exist for it alone.

**Phase 2 files:** `leanncd/experiments/jax_bridge/README.md`; `leanncd/LeanNCD/Eval/Plan/Executable.lean`
(`ExecutionEvidence` docstring only); `leanncd/LeanNCD/Eval/Plan/AGENTS.md` (one Pitfalls bullet;
the injected Pitfalls section is ~860 chars, so no trim is needed); and in `papers/`:
`jax_evalplan_architecture.md`, `eval_ir.md`, `backend_missing_functionality.md`,
`wave_f_capability_manifest.md`, `f32_evalplan.md`, `f32_jax_record.md`.

**Step 1: find the unqualified exact-match claims (both precisions).**
```bash
rg -n -i "bit-exact|bit-for-bit|zero mismatches|empirical binary64 results|orderedReference64\` requires bit-exact" \
  leanncd/experiments/jax_bridge/README.md leanncd/LeanNCD/Eval/Plan/Executable.lean \
  leanncd/LeanNCD/Eval/Plan/AGENTS.md papers/jax_evalplan_architecture.md
rg -n -i "subnormal|flush|signed zero" leanncd/experiments/jax_bridge/README.md \
  leanncd/LeanNCD/Eval/Plan/Executable.lean leanncd/LeanNCD/Eval/Plan/AGENTS.md papers/jax_evalplan_architecture.md
```
At `9b27008` the second grep's only hits are `jax_evalplan_architecture.md`'s "preserving signed
zero" (transport) and its "must state testable treatment of … signed zero" (a future-contract
requirement). Neither is a caveat. After step 2, every file in that grep has a caveat hit.

**Step 2: the caveat, in each place it belongs.** Use this wording. It is the settled text; adapt
only the wrapping.

1. **README, the anchor text.** Replace the sentence `These are empirical binary64 results for the
   measured CPU platform, not a proof about every XLA platform.` (end of "What this backend
   REJECTS"'s closing paragraph) with:

   > These are empirical results for the measured CPU platform, not a proof about every XLA
   > platform, and they hold for normal-range values only, in both precisions. XLA's CPU backend
   > flushes subnormal operands and results of arithmetic to zero (eager and under `jax.jit`;
   > `--xla_cpu_enable_fast_math=false` does not change it), and under `jax.jit` it simplifies the
   > reduction seed `+0 + x` to `x`, so a `-0` survives where the ordered left fold returns `+0`.
   > Neither corpus contains a subnormal or a `-0` input, which is why neither run sees it; the
   > binary32 standalone fixture `f32Identity` (`[+0, -0, least subnormal]`) does, and
   > `evalplan_affine_smoke32.py` pins that divergence exactly (`KNOWN_DIVERGENT`) instead of
   > excluding it. `orderedReference64` and `orderedReference32` carry the same limit. It is not
   > fixed: that would mean defeating XLA's flush-to-zero and its algebraic simplifier, and no XLA
   > flag that does either was found.

2. **README, the binary64 corpus bullet.** `3,832 source/eager cases, zero mismatches (both runs);`
   becomes `3,832 source/eager cases, zero mismatches (both runs; normal-range inputs only — see
   the subnormal/signed-zero limit below);`.
3. **`Executable.lean`, the `ExecutionEvidence` docstring.** Append before its closing `-/`, then
   `lake build JaxExperiment Eval.Plan.ExecutableTest` (green) and `mutation-manifest.sh --check
   leanncd papers/f32_jax_mutations_post.json` (every old-string still unique):
   ```text
       Both reference claims are MEASURED on XLA CPU, not proved, and for normal-range values only:
       XLA flushes subnormals to zero, and under `jax.jit` drops a `+0` reduction seed (a `-0` then
       survives where the left fold gives `+0`). See `experiments/jax_bridge/README.md`.
   ```
4. **`Plan/AGENTS.md`, one new Pitfalls bullet:**
   ```text
   - **JAX ordered-reference labels are measured, not proved, and exclude subnormals and jit signed zero.** XLA CPU flushes subnormals to zero and, under `jax.jit`, drops a `+0` fold seed; a fixture holding such a value diverges in BOTH precisions (pinned: `KNOWN_DIVERGENT`, `evalplan_affine_smoke32.py`).
   ```
5. **`jax_evalplan_architecture.md`, two places.** In §5.4, append to the paragraph right after the
   bounded-claim blockquote (`rg -n "This does not establish cross-platform equivalence"`):
   ```text
   Nor does it establish agreement on subnormal or signed-zero values. Measured since (slice
   F32-JAX): XLA's CPU backend flushes subnormal operands and results to zero, and under `jax.jit`
   simplifies a `+0` reduction seed away, so the agreement holds for normal-range values whose folds
   never rely on `+0 + -0 = +0`, in binary64 and binary32 alike (`leanncd/experiments/jax_bridge/README.md`).
   ```
   In the executive summary (`rg -n "agrees bit-for-bit with the Lean Dense evaluator in eager"`),
   change `on the measured CPU platform.` to `on the measured CPU platform, for normal-range values
   (subnormals and jit signed zero are a measured XLA CPU limit, Section 5.4).`

**Step 3: verify the caveat landed.** Re-run step 1's second grep. It must now hit README,
`Executable.lean`, `AGENTS.md`, and `jax_evalplan_architecture.md` (twice). Record the hit list.

**Step 4: the binary32 section, and the boundary docs that moved.**

- **README:** add a `### Binary32 (`orderedReference32`, slice F32-JAX)` subsection after the
  binary64 corpus measurements. It states what runs (`affineReference`, assign-only, context-free;
  `einsumOnly` refused, with the spike's 122-ULP reason), the parametrized runtime (`dtype`, x64
  disabled for float32), the four routes, the stride-1/1 measurements (the RECORD's values from
  Task 2 phase 1 step 5), §1.4's "structural, not fold-order, coverage" caveat, the
  JIT-every-case decision and its reason, and `./run-evalplan-affine32.sh [STRIDE [JIT_STRIDE]]`.

  Below the REJECTS table add one sentence: every row holds unchanged under a `.float32` plan for
  `affineReference` (same located errors), and under `einsumOnly` every binary32 plan is refused
  first with `unsupportedStorageKind .float32`. A sentence instead of extra columns: the table
  stays readable, and the f32 cells live in this plan's §4. In the paragraph before the table,
  `never silently stamped `orderedReference64`` becomes `never silently stamped with a reference
  label (`orderedReference64`/`orderedReference32`)`. Line 104's "`f64`/`reference64` mode"
  describes the einsum smoke and stays.
- **`eval_ir.md`** (`rg -n "It is also \*\*binary64-only\*\*"`). Replace from `It is also
  **binary64-only**:` through `…slice F32-JAX.` with the block below, and keep the following "What
  is still missing…" sentence:
  ```text
  Since slice F32-JAX its `affineReference` mode also runs binary32 under its own label,
  `orderedReference32` (evidence keyed by the plan's storage kind through `orderedReferenceFor`, so
  a zero-step f32 plan folds to `orderedReference32`, never `orderedReference64`); `einsumOnly`
  stays binary64-only, refused at every plan-level and standalone einsum door
  (`JaxCodegenError.unsupportedStorageKind`) and in `validateEinsum`.
  ```
- **`backend_missing_functionality.md`** has two edits:
  - after the paragraph ending "…the empty evidence fold is `orderedReference64`." (`rg -n "rejects
    a \`.float32\` plan at all eight"`), add an update line in the file's own convention;
  - replace `The JAX backend stays reference64-only (F32-JAX).` (`rg -n "reference64-only
    \(F32-JAX\)"`, wrapped across lines) with the second line below:
  ```text
  **Update (F32-JAX shipped, `f32_jax_evalplan.md`):** the `affineReference` mode now runs binary32 (`orderedReference32`); `einsumOnly` stays refused at every door.
  The JAX backend's `affineReference` mode runs binary32 since F32-JAX (`orderedReference32`); `einsumOnly` stays binary64-only.
  ```
- **`wave_f_capability_manifest.md`** has two replacements:
  ```text
  the experimental JAX backend rejects an f32 plan at every entry (F32-JAX).
  →  the experimental JAX backend runs f32 through `affineReference` (`orderedReference32`) since F32-JAX; `einsumOnly` stays refused.
  Only mixed `f32`/`f64` (F32-E) and JAX (F32-JAX) remain rejected.
  →  Only mixed `f32`/`f64` (F32-E) remains rejected; JAX `affineReference` runs binary32 since F32-JAX.
  ```
- **`f32_evalplan.md`:** append `**Landed by `f32_jax_evalplan.md`.**` to §1.3 item 5 and §1.4 item
  4 (the master-plan completion convention). §2.3 ("explicitly reference64-only") is a dated
  boundary snapshot, so do not rewrite it; append
  `> **Superseded by F32-JAX (2026-10):** `affineReference` runs binary32 under `orderedReference32`.`

**Step 5: value-grep, the whole repo, for the stale values** (not the vocabulary):
```bash
rg -n "reference64-only|rejects an f32 plan|rejects a \`\.float32\` plan|requireFloat64Plan|JaxExecutableValidationError\.unsupportedStorageKind|no binary32 evidence label|binary32 evidence label are slice" \
  leanncd papers --glob '!papers/f32_jax_*' --glob '!papers/f32b_*' --glob '!papers/f32c_*' --glob '!papers/f32d_*' --glob '!leanncd/docs/**'
```
Allowed hits:

- Task 1 step 4's allowed hits;
- `f32_evalplan.md`'s §1.3 item 5 (now carrying "Landed by") and its historical §2.3 and slice-time
  body (now under the superseded note);
- `backend_missing_functionality.md`'s historical "rejects a `.float32` plan at all eight …"
  paragraph (now followed by its update line).

An unexpected hit is real, not noise. Also run `rg -n "3,832" leanncd/experiments/jax_bridge/README.md
papers/jax_evalplan_architecture.md`. Each binary64 3,832 claim must sit inside or next to the
caveat's scope (README step 2.2), and the binary32 3,832 claim must sit in the new subsection.

**Step 6: completion.** Append to `papers/f32_jax_record.md`:

- step 3's caveat hit list;
- step 5's grep output (allowed hits only);
- Task 1 and Task 2's run summaries;
- the final build job counts.

Commit: `docs(leanncd): close out F32-JAX; scope both ordered-reference claims to normal-range
values`.

---

## 6. Risks and decisions

Rationale only; each item is argued where it is cited.

1. **Gate 3 removed** (user ruling): argued in §3.3, pinned by J7, J12 and fixtures 23/24. Keeping
   it would refuse the very plans this slice admits.
2. **`einsumOnly` binary32 refused, no tolerance label, a closed decision** (§1.2): pinned at the
   plan doors (J8), the standalone doors (J9/J10) and the validator (J1).
3. **Full corpus with every case JIT-checked** (user ruling; Task 2 phase 1 step 5): its weakness,
   inputs of 1–4, is owned in §1.4 and covered by P1–P3.
4. **`jaxRealCarrier` not shared with `nonlinDtypeFor`** (§3.1): a mild conflict with the repo's
   maximize-reuse preference, flagged for cleanup if a third caller appears.
5. **Subnormal/signed-zero: option (a), both precisions documented** (user ruling; §3.6): safe
   because the claim then says exactly what was measured.
6. **Line-anchored expects** (§2): the plan's one fragile coupling. Every prose edit to an anchored
   file is line-for-line, and was verified so.

## 7. Definition of done

1. `lake build` gives 8,673 jobs and `lake build JaxExperiment` gives 8,514 (record the actual
   numbers). No `sorry`. `lake env lean spikes/AxisABoundaryProbe.lean` gives 0 errors.
2. `mutation-manifest.sh leanncd papers/f32_jax_mutations_post.json` (no `--task`, `--out`), run
   once more after phase 2's `Executable.lean` docstring edit: 15/15 PASS, table in the record.
3. Python cycles P1–P6 all killed with the step-4 observations, unmutated and restored both pass.
4. Binary64 preservation: the curated module `cmp`-identical, `run-evalplan.sh` passes, and the
   3,832-case binary64 corpus has 0 mismatches at 3,424,195 bytes.
5. **The evidence gate:** the stride-1/1 binary32 run reproduces exactly 3,849 fixtures and
   5,873 + 5,873 = 11,746 checks, with 0 mismatches outside `f32Identity [1, 2]`. The module is
   3,657,456 bytes.
6. §4 Tables A/B re-derived in the record (Task 1 step 5 plus the Task 2 Python cells), with no SI
   cell.
7. The caveat is landed in all four places (phase 2 step 3), and the step-5 greps return only
   allowed hits.
8. The final whole-branch review, with **two lenses at Opus 5.5 high**, is clean or adjudicated:
   - (a) soundness of the storage-keyed evidence boundary (§3.3's three points, the gate-3 removal,
     every einsum door);
   - (b) truthfulness of every evidence and doc claim against the tree and the record, including
     whether the caveat is placed and worded so that NEITHER label over-claims.

   Per-task review: Task 1 at Opus 5.5 high, Task 2 at Sonnet 5 medium.
9. Merge to local `main` (CLAUDE.md Rule 13); do not push.

## 8. Stop conditions

- Any observed value differs from this plan's: bits, counts, payloads, a module size, or an
  `expect` string. Report both values; do not edit the expectation.
- A `git apply` of either patch does not apply cleanly onto the expected tree.
- `wc -l EvalPlanCodegen.lean` changes after a prose edit, or any J-cycle FAILs.
- A Table A cell turns out SI, or a (c) cell in Table B turns out reachable.
- `KNOWN_DIVERGENT` stops reproducing (XLA changed). That needs a decision, not a silent update.
- A binary64 run differs in any way: a byte, a mismatch, a count.
- A dispatch passes ~60 turns before its commit. Split it per `slice-plan` §5; this slice's
  authoring already overran (§9).

## 9. Authoring cost (CLAUDE.md Rule 6, stated, not hidden)

The authoring overran its budget. These counts are the dispatches' own reports, not measured with
`token-report.py`:

- **Spike:** ~260k context.
- **Explore+prototype:** two resumptions, ~626k combined subagent-reported tokens, and **95 + 45 =
  140 turns against the 60-turn cap**. Most of that was waiting: ~45 min for the manifest, ~10 min
  for the binary64 corpus, ~13 min for the binary32 stride-1 run, plus a retry turn for each
  command-guard rejection (prototype notes §10).
- **This write-up dispatch:** ~75 turns, also **over the 60-turn cap**. Its re-runs were limited to
  verifying its own prose edits (the build, J12/J15, `git apply --check`, the manifest `--check`),
  with no re-exploration. The overrun came from command-guard rejections (blocked `git checkout`,
  compound shell commands) and from assembling and trimming the plan itself.

The execution budget (Rule 6: ≤ ~175M for the slice) is measured at close-out and recorded in
`f32_jax_record.md`.

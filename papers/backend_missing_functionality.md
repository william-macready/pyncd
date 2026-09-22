# Backend missing functionality

Living inventory of what the **checked `EvalPlan` backend** (`LeanNCD/Eval/Plan/`) does not yet
support. Scope is the static compiler backend only — the reference dense interpreter (`LeanNCD/Eval/`)
already evaluates most of the constructs listed here, so nearly every row is a *backend-parity* gap
(the checked plan compiler has not caught up to the reference semantics), not a missing semantic.

> **The "Hard" Scatter row below has been audited in depth. Start at
> `papers/scatter_affine_lhs_writes.md`** — it is the current authority and supersedes
> `post_audit_roadmap.md` Section B, which is now a stub. `pre_scatter_backend_audit.md` remains the
> findings record (224-cell predicate table, 21 findings, twelve reproducible spikes); read its
> superseding banner before quoting it.
>
> **Two corrections to an earlier version of this banner, both measured 2026-09-09:**
>
> 1. It said *"one scope question gates the whole thing (are affine LHS writes wanted in `base`
>    blocks or step-only?)"*. That is **not** the gating question. A scatter-shaped LHS combined
>    with an iteration slot is rejected at DSL phase 7 by `checkScatterNoScan` in base and step
>    alike, so both options are unreachable from surface syntax and the decision governs a deferred
>    slice. The real question is whether checked-backend parity is the goal now.
> 2. The row is **two nearly-disjoint slices**, not one: top-level scatter (`Out[2*i] := X[i]`),
>    which compiles through the whole DSL and dies at a single checked-plan barrier over a *missing
>    IR node*; and strided writes into scan state, which are blocked at the DSL and have no
>    reference semantics anywhere. Top-level scatter is sequenced first — it has a reference
>    implementation to differential-test against.
>
> The hardening slice this banner recommended **has landed** (Slice 1, `post_audit_roadmap.md`
> Section A), so a new write-row kind now fails to compile at nine sites rather than being silently
> exempted. That tripwire serves the *deferred* slice.
>
> **Update (S-A shipped):** top-level scatter — the first of the two slices above — has since landed
> end to end (`scatter_affine_lhs_writes.md`, Tasks 1-6: IR node, checker, dense worker, source
> reachability, and a curated parity corpus). It is now recorded under "Already closed" below, and
> the Hard row has been narrowed to the still-open second slice (strided writes into scan state, S-B).
> The two 2026-09-09 corrections above are left as written — they accurately describe what was true
> before S-A landed.
>
> **Supersession (S-B shipped, 2026-09-13):** the second slice has now landed too. The two corrections
> above remain historical measurements; the Hard row they described has moved to “Already closed.”

## Contents

- [Authoritative source — re-derive, don't trust this copy](#authoritative-source--re-derive-dont-trust-this-copy)
- [Missing capabilities](#missing-capabilities)
  - [Difficulty ranking rationale (hardest → easiest)](#difficulty-ranking-rationale-hardest--easiest)
  - [Scan-geometry limits (not `CapabilityError` rejections)](#scan-geometry-limits-not-capabilityerror-rejections)
- [Already closed (do not re-list as missing)](#already-closed-do-not-re-list-as-missing)
- [Related documents](#related-documents)

## Authoritative source — re-derive, don't trust this copy

Every syntactically visible rejection the backend can make is one constructor of the closed enum
[`CapabilityError`](../leanncd/LeanNCD/Eval/Plan/Error.lean). There is no `unsupported : String`
escape hatch, so the enum is the whole boundary. It is thrown from **three** sites in
[`Compile.lean`](../leanncd/LeanNCD/Eval/Plan/Compile.lean), all inside `prepareEvalPlan` and all
dtype-ordered ahead of plan construction:

1. `capabilityPreflight` — the dtype-blind pass (decls in order, then statements in order, first
   failure wins). This was the only site until the f32 slice.
2. `prepareEvalPlan`'s Step 0b storage derivation — `scheduleStorageKind` disagreement, i.e. a
   schedule mixing `f32` and `f64` real tensors. Not part of `capabilityPreflight` because that
   function is dtype-blind by construction; only Step 0b knows the schedule's derived storage kind.
3. `f32CapabilityCheck` (Step 0c) — the binary32 source fragment, run for a `.float32` schedule only
   and placed before `capabilityPreflight` so an f32 program outside the admitted fragment reports
   its own f32 reason rather than a generic capability one.

This document is a prose reproduction of that enum and will decay exactly as any carried-forward
claim does. **Before trusting a row, re-derive it against those three sites on the current branch**
— read the `throw` sites, do not assume this table is current. Two rows of the sibling
`wave_f_capability_manifest.md` table went stale this way when the nonlinearity thread closed
nonlinear scans and updated the proposal but not the manifest's copy.

Last re-derived against the tree: **2026-09-21** (f32 binary32 assignment execution).

Static throw-site inspection at that date finds **10 live producer families** —
`scatterOrAffineLhs`, `unsupportedLhsSlot`, `unsupportedNonlin`, `multiAxisScatterLhs`,
`scatterOptsNotAdmitted`, `recurrenceOrCallback`, `noAdvancingAxis`, `predicateScatterDest`,
`unloweredScatterAssign`, and `unsupportedDtype` — out of the enum's **16 constructors**; the other
**6** (`scanNode`, `maskOrPredicate`, `unaryFactor`, `unsupportedAgg`, `booleanOutput`,
`dynamicShape`) are retained producer-less or are structurally unreachable. Removing a producer never
removes a constructor.

`unsupportedDtype` is the newest live family: it was producer-less until the f32 slice, which made it
the producer of every binary32 rejection — the mixed-storage schedule (site 2) and each deferred f32
construct (site 3). The pre-slice boundary was 9 live / 7 producer-less over the same 16
constructors.

## Missing capabilities

Each row names the `CapabilityError` constructor that rejects it, the site that throws, and
whether the reference dense interpreter already evaluates it (a `✓` means the gap is purely
backend-side). **Rows are ordered hardest → easiest to implement.** The difficulty column is a
grounded *estimate* (judgment from the plan-IR structure, using the nonlinearity thread as the
yardstick), not a measured figure — see the rationale below the table.

| Difficulty | Missing capability | `CapabilityError` | Throw site | Ref. interp. does it? |
|---|---|---|---|---|
| Foundational / modeling-contradiction | **`.scanPre` + recurrence / callback morphisms** — the pre-built step-morphism escape hatch | `recurrenceOrCallback` | `checkScanStmt` / `checkStmt` | partial (`Stmt.recurMorphism`) |
| Foundational | **Dynamic / value-dependent shapes** — extents that are not statically known | `dynamicShape` (producer-less/unreachable) | no throw site exists; the whole compiler resolves extents at compile time, so there is nothing yet to reject *at* | n/a (no surface syntax) |
| Foundational (scalar-domain decision first) | **`complex64` / `complex128`** — complex-valued tensors | none yet; a complex declaration has no source spelling to reject | n/a | ✗ |
| Bounded per construct | **Binary32 beyond the assignment fragment** — f32 nonlinearities, inline unary factors, top-level scatter, and every scan form | `unsupportedDtype` | `f32CapabilityCheck` / `checkF32Stmt` (Step 0c), one payload per deferred slice | ✗, permanently — the reference dense interpreter is binary64-only and refuses **any** f32 graph (`EvalError.unsupportedDtype`), so these rows have no reference oracle to differential-test against |
| Bounded, contingent | **Mixed `f32`/`f64` in one schedule** — an explicit precision conversion | `unsupportedDtype` | `prepareEvalPlan` Step 0b, on `scheduleStorageKind` disagreement | n/a (no conversion semantics anywhere) |

### Difficulty ranking rationale (hardest → easiest)

The recurring cost pattern: to land a construct you generally need a raw plan type → a new
`PlanStep`/`BlockStep` case or a `ContractionAlgebra` extension → a checker producing `Checked*`
evidence → a Dense worker → source residualization in `Compile.lean` (plus preflight admission) →
wiring into the step graph and the differential corpus. How much of that chain a construct forces is
what the ranking tracks.

1. **`.scanPre` + recurrence / callback morphisms** — hardest, and arguably *not a bounded feature*.
   These carry an opaque pre-built step morphism. Giving an arbitrary externally-supplied function a
   *checked* meaning contradicts the reason the checked plan exists (no opaque steps); the proposal
   keeps it explicitly as the escape hatch. Landing it means designing a whole new structured surface
   for what the callback expresses, not writing a lowering — you cannot validate an opaque function.
2. **Dynamic / value-dependent shapes** — foundational and wholly open. The whole checked plan
   assumes statically-known extents (shape inference, geometry, write maps, corpus gates all resolve
   sizes at compile time), so value-dependent shapes mean symbolic extents pervasively. This is the
   deepest single change on the list, and it is dtype-independent: it was bundled with `f32` in an
   earlier version of this table, and the two turned out to share nothing. The f32 slice closed its
   half without touching shapes at all.
3. **`complex64` / `complex128`** — foundational for a different reason: an unresolved *semantic*
   decision, not an unbuilt lowering. Five things are open and none is plumbing. (a) **Scalar
   domain**: the categorical route erases a real precision annotation because `f32` and `f64` are
   representations of the same real scalars; complex values are a different scalar domain, so
   erasure is unavailable and the categorical semantics must either be extended or complex
   declarations rejected before categorical lowering. (b) **Machine carrier**: the installed
   Mathlib `Complex` is a pair of mathematical `Real`s and is noncomputable in the ways that matter
   here — it is not a native machine-complex runtime, so executable `ComplexF32`/`ComplexF64`
   component carriers have to be defined outright. (c) **Operation admission**: sum-product extends
   directly, but `min`/`max` and the tropical algebras have no ordering on ℂ and must stay rejected
   until someone supplies explicit semantics; the Boolean tag's identities in a complex graph
   (real Boolean storage, or the carrier's exact `0+0i`/`1+0i`?) is a separate open decision the
   f32 slice's precision-neutral Boolean rule deliberately does not cover. (d) **Conversions**:
   real↔complex and complex precision conversions do not exist and are not implied by the dtype.
   (e) **JAX parity**: `jnp.complex64`/`complex128` exist, and `complex128` additionally requires
   JAX x64 — but **JAX's ability to store a complex array is not Tensor Logic support for complex
   tensors** and must never be reported as such. Bit-level parity would also require measuring
   XLA's own operation order before any claim of agreement.
4. **Binary32 beyond the assignment fragment** — bounded, one deferred slice per construct (F32-B
   nonlinearity and inline unary, F32-C scans including scan-local scatter, F32-D top-level
   scatter, F32-JAX). Each is genuinely bounded because the carrier, the checked evidence, the
   algebras, the storage-kind gates at every worker/adapter/JAX door, and the named public boundary
   already exist; what each slice adds is that construct's own binary32 numerics plus its fixtures.
   The cost is not plumbing but *numerical truthfulness*: routing an f32 value through the existing
   binary64 helper would be false f32, so each slice needs its own bit-level fixtures.
5. **Mixed `f32`/`f64` in one schedule** — contingent, not merely deferred. The project invariant is
   that a graph selects one real precision, so mixed precision is *rejected rather than converted*
   and no conversion plan step is planned. If that invariant is ever changed, explicit conversions
   are a slice of their own (F32-E). Boolean tensors already follow the graph's real carrier and
   need no conversion to coexist with either precision.

Scatter + affine LHS writes formerly occupied a rank here and is now closed for S-A plus S-B's
bounded scan-state subset; see “Already closed.” General data-dependent gather/scatter and the
rejected scan geometries below remain separate capabilities.

### Scan-geometry limits (not `CapabilityError` rejections)

These are rejected deeper in `compileScan`/`checkScanPlan` (via `ScanCompileError`), once inferred
sizes and lowered affine maps exist, rather than at preflight — but they are real backend limits
(proposal §5.1):

- **Multi-face full-boundary writes** — the standard n-D tabulation-DP pattern (e.g.
  row-0-plus-column-0), which always overlaps at the origin.
- **Genuinely overlapping writes with no declared precedence.**

Both need an offset/restricted-range or conflict-resolving base-write geometry beyond the current
pin-plus-full-free fragment. The first checked scan remains the rectangular uniform all-axis `+1`
fragment.

## Already closed (do not re-list as missing)

- **Unary factor functions** — admitted end-to-end (top level and inside scan `base`/`recur` blocks).
  `checkFactor` admits `.unaryFn`; `residualizeAssignment` lowers it to the same `ReadPlan` a `.read`
  produces with a new `unary : Option UnaryOp` field, and Dense's `gatherFactor` applies the function
  *after* the `zeroPad` out-of-bounds pad — so an out-of-bounds read contributes `f(0)`, matching the
  reference `gather`. The math and domain partiality live once in `UnaryOp.applyChecked`, which the
  reference `applyUnaryFn` also wraps (`log`/`sqrt`/`recip` fail loud — the checked path as
  `PositionalInputError.unaryDomain`, the reference as `EvalError.unaryDomain`). No new `PlanStep`,
  geometry, or dtype. The `unaryFactor` constructor is retained producer-less, like `scanNode`. Closed
  by `unary_factor_functions.md`.
- **max / min aggregation** — admitted end-to-end (top level and inside scan `base`/`recur` blocks).
  `checkAggOp` admits `.max`/`.min`; `algebraForAgg` selects the tropical algebra
  (`admittedAlgebraMax`/`admittedAlgebraMin`) in the *existing* `ContractionAlgebra` reduction slot —
  no new `PlanStep`, geometry, or dtype — and Dense reduces with `max`/`min` seeded at `−∞`/`+∞`. The
  `zeroPad` pad stays `0.0` (a factor value, not the reduction identity), matching the reference
  `Combine.max`/`Combine.min` oracle. `unsupportedAgg == 0` in the `DifferentialTest.lean` scan
  corpus; the constructor is retained producer-less, like `scanNode`. Closed by
  `max_min_aggregation.md`.
- **Pointwise + axiswise nonlinearities** — admitted at top level (`checkNonlinTopLevel`) and inside
  scan `base`/`recur` blocks (`checkNonlinScanBlock`), residualized into an `assign → pointwise` /
  `assign → axiswise` chain. `unsupportedNonlin == 0` in the `DifferentialTest.lean` scan corpus.
  Closed by the nonlinearity plan (`nonlinearity_split_pair_direct_lowering.md` §3.6–§3.7).
- **Masks / predicates / Iverson factors** — admitted end-to-end (top level and inside scan
  `base`/`recur` blocks). A *positional* (UID-free) predicate IR (`PosBoolExpr`/`PosPredArith`/
  `PosAffine`) plus an ordered `FactorPlan` (`read | iverson`) replace `TermPlan`'s read array;
  `checkAssign` width-checks each predicate leaf against `iterationShape` (reusing
  `affineWidthMismatch`), and Dense evaluates the predicate per contraction coordinate (`true` ⇒
  `1.0`, `false` annihilates the term). Source `BoolExpr` lowers to the positional form through one
  private recursive core reached only via `lowerFactorPredicate` (basis `context ++ output ++
  reduction`, real pins) and `lowerMaskPredicate` (local non-seeded output basis, empty pins).
  Axiswise `where=` masks add `RawAxiswisePlan.mask : Option PosBoolExpr`, with the `Eval/Nonlin.lean`
  row worker refactored around a shared `included?` callback so one `softmax`/`normalize`/`l2`
  serves both the source wrapper and the checked adapter. Every filtered read traversal keeps the
  original all-factor index; `maskOrPredicate` and `NonlinCompileError.maskedAxiswiseNotSupported`
  are retained producer-less, like `scanNode`. Boolean/predicate *declared outputs* are now closed
  too (see the row above). **Caveat:** a scan `where=` mask's basis (`lowerMaskPredicate`,
  `Compile.lean`) is deliberately the statement's non-seeded output axes only — it cannot reference
  the scan's own `.iterAt`/`.iterNext` iteration axis, which densifies to a constant 0 instead. A
  scan recurrence expressing causal masking via `where= j <= l` (the pattern this repo's CLAUDE.md
  points at as the replacement for the reverted `causal_softmax` operator) therefore does NOT see
  the live step `l` here — it compiles and runs, silently wrong, not rejected. Closed by
  `predicate_boolean_backend_parity.md`.
- **Boolean / predicate declared outputs** — admitted end-to-end (top level, scan state, scan
  scratch, published histories, and downstream reads). `ScalarDType.bool` is a **semantic
  algebra/signature tag over unchanged Float-backed storage**, not a native carrier: no `Array Bool`,
  no bit-packing, no truth-value validation, no coercion step. A predicate destination selects
  `admittedAlgebraBool` (factor `min` with identity `true`, contracted-coordinate and term `max` with
  identity `false`), mirroring the reference `Combine.bool`; `Dense.constFloat` decodes `.bool
  true`/`.bool false` to `1.0`/`0.0` and the ordinary Float `min`/`max` run, so a non-binary value
  keeps literal min/max behavior rather than being coerced or rejected. Algebra admission is
  destination-specific (`admittedAlgebrasFor`): real sum-product plus the two tropical semirings for
  `f64`, Boolean min/max only for `bool`, nothing for `f32` — a binary32 graph uses the separate
  `admittedAlgebrasForF32` table instead, added by the f32 slice; the two are deliberately not merged
  (see the binary32 row under "Already closed"). Source/destination dtype EQUALITY was
  deliberately removed as an assignment obligation — the destination selects the algebra and
  gathering is dtype-blind — so a `bool` source may feed an `f64` destination and vice versa;
  `PlanError.dtypeMismatch` was retained producer-less by that slice (nonlinearity checking keeps its
  own separate `NonlinPlanError.dtypeMismatch`) and has since acquired exactly one producer: the f32
  slice's `checkAssignCore` reports an `f64` read inside a binary32 graph as
  `dtypeMismatch .f32 .f64`, a precision *disagreement* between two known sides rather than an
  unimplementable tag. The Boolean rule above is unaffected — it is about `bool` versus a real dtype,
  not about two real carriers. Declarations are authoritative: `buildDeclEnv` rejects a repeated
  tensor-bearing name (`CompileError.duplicateTensorDecl`), `InputSignature.ofDenseInputsForDecls`
  labels declared predicates `bool`, and an explicit input signature contradicting the declaration is
  rejected (`InputSignatureError.dtypeMismatch`), never silently rewritten. Scans carry full
  `TensorSignature`s (`CompiledScan.stateSigs`) through state destinations, captures, base/step
  results, scratch, and published histories, and `checkWrites` enforces write-dtype equality
  (`ScanPlanError.writeDtypeMismatch`) BEFORE rank/geometry. `booleanOutput` is retained
  producer-less, like `scanNode`. `f32` was rejected everywhere when this row closed; it is no longer
  (see the binary32 row below), and the precision-neutral Boolean rule that slice added means a
  `bool` tensor now follows whichever real carrier its graph selected. **Not** included: JAX Boolean
  execution —
  the experimental `jax_bridge` backend now REJECTS a Boolean destination, a Boolean source, tropical
  algebra, a unary read, and a CONTEXTFUL assignment (non-empty `AssignPlan.contextShape`) with
  located typed errors before emitting Python or stamping evidence, plus — in `einsumOnly` mode only
  — a zero-padded read whose source extent disagrees with its own iteration extent
  (`labelExtentMismatch`) (see `jax_evalplan_architecture.md`). Closed by `boolean_predicate_output_evalplan.md`.
- **Top-level scatter statements + affine/diagonal LHS writes** — admitted end-to-end at top level
  (`Out[2*i] := X[i]`, `Y[i, i] := V[i]`, and their 2-D/offset/RHS-only-axis variants). `Compile.lean`'s
  `lowerArith` reclassifies an affine or diagonal LHS into a `Stmt.scatter`; `checkScatter`
  (`Check.lean`) validates its placement map, `destShape`, `fill`, and collision policy plus the
  nested compute half's own `checkAssign` obligations, producing `CheckedScatterPlan` evidence; the
  outer graph carries a `PlanStep.scatter` (whose `CheckedPlanStepEvidence.scatter` arm holds that
  evidence), and `runDenseScatter` (`Dense.lean`) executes it source-driven, placing each computed
  value through `outCoeffs`/`outBias` into a `fill`-initialized destination and rejecting coincident
  writes. **Closure is scoped to a REAL-sum-product destination** (`agg = .sum` on an `f64` or
  undeclared destination): the reference `evalScatter` (`Eval/Scatter.lean`) selects its algebra
  from `rhs.agg` alone and never consults `decls`, so a Boolean/predicate-declared scatter
  destination silently diverged from the reference (checked backend selected `admittedAlgebraBool`;
  reference computed real sum) and is now REJECTED at capability tier as `predicateScatterDest`,
  same way a tropical fill is refused — the honest report that no reference match exists, deferred
  to a future slice where the reference is taught to be dtype-aware. The parity gate is the curated
  `scatterPrograms` corpus (`DifferentialTest.lean`, 9 accepted programs), checked bit-for-bit
  against the reference `Eval/Scatter.lean` evaluator over the real sum-product algebra. Still
  rejected, deliberately: a constant-affine slot (`Out[3]`, `scatterOrAffineLhs`), a multi-axis slot
  (`Out[i+j]`, `multiAxisScatterLhs`), a collision policy other than reject-on-collision
  (`scatterOptsNotAdmitted`), a non-identity nonlinearity on a scatter (`unsupportedScatterNonlin`),
  and a Boolean/predicate destination (`predicateScatterDest`); a tropical-algebra scatter's
  unwritten cells provably diverge from the reference by design and is not a parity-corpus entry.
  The experimental `jax_bridge` backend rejects a `.scatter` step categorically (`unsupportedStep`)
  — there is no JAX scatter execution.
  **Not** included: Boolean/predicate scatter destinations — deferred, rejected at capability tier
  as `predicateScatterDest` rather than admitted; closing them requires teaching the reference
  `evalScatter` to be dtype-aware.
  Closed by `scatter_affine_lhs_writes.md`.
- **Affine scatter writes into scan state (S-B)** — positive one-axis affine placement with
  nonnegative bias is admitted in non-advancing state dimensions in both base and recurrence phases.
  The block computes a dense `AssignPlan` (including contraction) and `StateWriteMap` performs
  placement; no `BlockStep.scatter` exists. Multiple base contributions must be proven disjoint
  (equal-scale/different-residue is the new proof), recurrence still permits exactly one write per
  state, fill is zero, and collision policy is reject. Context-affine, multi-axis, scratch-scatter,
  predicate/nonlinear, non-default reduction, sign, extent, and overlap forms remain typed
  rejections. `DifferentialTest.scanScatterPrograms` pins seven source-generated cases across checked
  plan, legacy evaluator, and independent scan-free oracle. Closed by
  `2026-09-12-lhs-scatter-in-scans.md`.
- **Genuine binary32 (`f32`) execution of the scan-free assignment fragment** — admitted end to end,
  from source syntax to native materialized outputs. `tensor f32 X(i, j)` elaborates to the single
  extensible AST constructor `Decl.typedTensor TensorElementType String (List AxisSpec)`, which is
  tensor-bearing everywhere `Decl.tensor` is. A schedule selects ONE real precision
  (`scheduleStorageKind` over used names; `bool` contributes no constraint and an undeclared external
  is real `f64`), so an `f32` graph may contain Boolean tensors but never `f64` ones. `checkAssignF32`
  and `checkAssign` are two thin applications of one private `checkAssignCore`, differing at exactly
  four clauses — destination dtype admission, algebra table (`admittedAlgebrasForF32`), source dtype
  rule, and inline-unary admission — and the storage kind they record on `CheckedAssignPlan` /
  `CheckedEvalPlan` is what every worker and adapter door then refuses to cross.
  **`f32` means independently rounded binary32 at every primitive operation, never a binary64 run
  with a narrowed result**: values are `Float32`, constants decode from `ScalarConst.f32` via
  `Float32.ofBits`, and factor/reduction/term folds run through a carrier-specific `ScalarKernelOps`
  (`float32Ops` beside the existing `floatOps`) in the shared traversal. `runDenseAssignAt32` /
  `runDenseAssign32` / `runDensePlan32` execute it; `pack32` / `unpack32` / `runPreparedDense32` are
  the public named boundary over `DenseTensor32`, returning an `EvalReport32`. The container
  generalizations (`DenseTensorOf`, `NamedDenseEnvOf`, `EvalReportOf`) keep every existing Float alias
  and field name, so no Float API changed. Boolean tensors are an algebra tag over the *selected*
  carrier: the same non-binary min/max behavior, with `true`/`false` decoded to that carrier's exact
  one/zero rather than coerced.
  **Every other door is closed, fail-loud, and fixture-pinned**: the Float-backed workers, `pack` /
  `unpack` / `runPreparedDense`, and the block checker reject `.float32` evidence; the f32 workers
  and adapter reject Float-backed evidence (`storageKindMismatch`), each guard placed before its
  function's own pre-existing shape/arity/binding checks; the reference dense interpreter refuses any
  f32 graph permanently (`EvalError.unsupportedDtype` at `evalScheduled`, `evalAssignDtypedSeeded`,
  `evalPlain`, `evalStmtSliceSeeded`, `evalScan`); and the experimental `jax_bridge` backend rejects
  a `.float32` plan at all eight candidate/generator/renderer entries *before* node iteration,
  binding validation, evidence aggregation, or any Python emission — the zero-step, all-input f32
  plan is the case that makes a plan-level gate necessary, since every per-node check is vacuous
  there and the empty evidence fold is `orderedReference64`.
  **Deliberately still rejected, each with its own located `CapabilityError.unsupportedDtype`**:
  f32 pointwise/axiswise nonlinearities and inline unary factors (slice F32-B), every scan form
  including scan-local scatter (F32-C), top-level scatter (F32-D), and a schedule mixing `f32` with
  `f64` (F32-E, contingent — see the rationale above). The JAX backend stays reference64-only
  (F32-JAX). Closed by `f32_evalplan.md`.
- **Scan nodes** with at least one advancing axis — `scanNode` has no producer left in the compiler.
  Only `noAdvancingAxis` (an empty advancing-axis list) is still an error, and that is a genuine
  input error, not a capability gap.
- **Top-level and scan `.freeNorm`** LHS slots (a `·`-marked reduction axis).

## Related documents

- [`wave_f_capability_manifest.md`](wave_f_capability_manifest.md) — the Wave-F scan boundary in full
  (accepted / rejected scan constructs, corpus coverage).
- [`wave_c_capability_manifest.md`](wave_c_capability_manifest.md) — the scan-free `EvalPlan`
  boundary.
- [`wave_f_scanplan_proposal.md`](wave_f_scanplan_proposal.md) §1 — the "functionality still missing"
  table this inventory expands, kept current by the thread that changes the boundary.
- [`eval_ir.md`](eval_ir.md) — the eval-IR pipeline and backend-execution reference.
- [`predicate_boolean_backend_parity.md`](predicate_boolean_backend_parity.md) — detailed design and
  task division that closed the predicate-factor and axiswise-mask rows (Slice 5). Its own Task 4
  sketch for Boolean declared outputs is superseded by
  [`boolean_predicate_output_evalplan.md`](boolean_predicate_output_evalplan.md), the plan that
  actually closed that row.
- [`unary_factor_functions.md`](unary_factor_functions.md) — the plan that closed the unary-factor row.
- [`max_min_aggregation.md`](max_min_aggregation.md) — the plan that closed the max/min-aggregation row.
- [`f32_evalplan.md`](f32_evalplan.md) — the plan that closed the binary32 assignment row, split the
  old combined “`f32`; dynamic shapes” entry in two, and made `unsupportedDtype` a live family. It is
  also the authority on what binary32 does *not* yet cover (slices F32-B/C/D/E/JAX) and on why
  complex support is a scalar-domain decision rather than another dtype.
- [`boolean_predicate_output_evalplan.md`](boolean_predicate_output_evalplan.md) — the plan that
  closed the Boolean/predicate declared-output row and made the experimental JAX backend reject
  Boolean, tropical, unary, and contextful semantics rather than stamping them with reference
  evidence.

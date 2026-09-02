# Backend missing functionality

Living inventory of what the **checked `EvalPlan` backend** (`LeanNCD/Eval/Plan/`) does not yet
support. Scope is the static compiler backend only — the reference dense interpreter (`LeanNCD/Eval/`)
already evaluates most of the constructs listed here, so nearly every row is a *backend-parity* gap
(the checked plan compiler has not caught up to the reference semantics), not a missing semantic.

## Contents

- [Authoritative source — re-derive, don't trust this copy](#authoritative-source--re-derive-dont-trust-this-copy)
- [Missing capabilities](#missing-capabilities)
  - [Difficulty ranking rationale (hardest → easiest)](#difficulty-ranking-rationale-hardest--easiest)
  - [Scan-geometry limits (not `CapabilityError` rejections)](#scan-geometry-limits-not-capabilityerror-rejections)
- [Already closed (do not re-list as missing)](#already-closed-do-not-re-list-as-missing)
- [Related documents](#related-documents)

## Authoritative source — re-derive, don't trust this copy

Every syntactically visible rejection the backend can make is one constructor of the closed enum
[`CapabilityError`](../leanncd/LeanNCD/Eval/Plan/Error.lean), and every one is thrown from a single
function, [`capabilityPreflight`](../leanncd/LeanNCD/Eval/Plan/Compile.lean) (decls in order, then
statements in order, first failure wins). There is no `unsupported : String` escape hatch, so the
enum is the whole boundary.

This document is a prose reproduction of that enum and will decay exactly as any carried-forward
claim does. **Before trusting a row, re-derive it against `capabilityPreflight` on the current
branch** — read the `throw` sites, do not assume this table is current. Two rows of the sibling
`wave_f_capability_manifest.md` table went stale this way when the nonlinearity thread closed
nonlinear scans and updated the proposal but not the manifest's copy.

Last re-derived against the tree: **2026-08-30**.

## Missing capabilities

Each row names the `CapabilityError` constructor that rejects it, the preflight site that throws, and
whether the reference dense interpreter already evaluates it (a `✓` means the gap is purely
backend-side). **Rows are ordered hardest → easiest to implement.** The difficulty column is a
grounded *estimate* (judgment from the plan-IR structure, using the nonlinearity thread as the
yardstick), not a measured figure — see the rationale below the table.

| Difficulty | Missing capability | `CapabilityError` | Preflight site | Ref. interp. does it? |
|---|---|---|---|---|
| Foundational / modeling-contradiction | **`.scanPre` + recurrence / callback morphisms** — the pre-built step-morphism escape hatch | `recurrenceOrCallback` | `checkScanStmt` / `checkStmt` | partial (`Stmt.recurMorphism`) |
| Foundational (dynamic-shape half) | **Non-`f64` dtypes; dynamic / value-dependent shapes** | `unsupportedDtype`, `dynamicShape` | not reachable from preflight (f64-only by construction); `checkAssign` rejects non-`f64` sources downstream | n/a (mode boundary) |
| Hard | **Scatter statements + affine (strided/offset) LHS writes** — e.g. `Out[2*i] = …` | `scatterOrAffineLhs` | `checkStmt` / `checkLHSSlot` | ✓ (`Eval/Scatter.lean`) |
| Moderate–hard | **Boolean / predicate *outputs*** — a `.predicate` decl | `booleanOutput` | `checkDecl` | ✓ (bool semiring `Combine`) |

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
2. **Non-`f64` dtypes; dynamic / value-dependent shapes** — two very different things bundled. `f32`
   is mostly storage plumbing and `bool` overlaps #4, but **dynamic shapes is foundational**: the
   whole checked plan assumes statically-known extents (shape inference, geometry, write maps, corpus
   gates all resolve sizes at compile time), so value-dependent shapes mean symbolic extents
   pervasively. That half is the deepest single change on the list.
3. **Scatter + affine LHS writes** — "Wave D source semantics." Changes the *write side*: affine /
   scatter write maps, output-extent via the shared `scatterOutShape` contract (which exists), and a
   scatter-aware Dense worker. Partly scaffolded — `RawScanPlan` already carries `StateWriteMap`
   machinery scatter could model on — but write geometry is this repo's recurring defect family (the
   `stepWriteRowsOk` Critical), so the validation surface is where the cost lives.
4. **Boolean / predicate outputs** — admit `bool` end-to-end: `ScalarDType.bool` is a reserved tag
   with no producer, and `ScalarBinOp` has no `logicalAnd`/`logicalOr` (deliberately, per its doc
   comment). So this threads a new dtype *and* a new algebra family through checker, Dense worker,
   and result reporting. Bounded, but wider than the now-closed masks/predicates/Iverson-factors
   work, and naturally coupled to it (predicates consume / produce bool).

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
  are retained producer-less, like `scanNode`. Boolean/predicate *declared outputs* (`booleanOutput`)
  remain the separate open row. **Caveat:** a scan `where=` mask's basis (`lowerMaskPredicate`,
  `Compile.lean`) is deliberately the statement's non-seeded output axes only — it cannot reference
  the scan's own `.iterAt`/`.iterNext` iteration axis, which densifies to a constant 0 instead. A
  scan recurrence expressing causal masking via `where= j <= l` (the pattern this repo's CLAUDE.md
  points at as the replacement for the reverted `causal_softmax` operator) therefore does NOT see
  the live step `l` here — it compiles and runs, silently wrong, not rejected. Closed by
  `predicate_boolean_backend_parity.md`.
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
  task division that closed the predicate-factor and axiswise-mask rows (Slice 5); the Boolean
  declared-output row (`booleanOutput`) remains open.
- [`unary_factor_functions.md`](unary_factor_functions.md) — the plan that closed the unary-factor row.
- [`max_min_aggregation.md`](max_min_aggregation.md) — the plan that closed the max/min-aggregation row.

# Backend missing functionality

Living inventory of what the **checked `EvalPlan` backend** (`LeanNCD/Eval/Plan/`) does not yet
support. Scope is the static compiler backend only — the reference dense interpreter (`LeanNCD/Eval/`)
already evaluates most of the constructs listed here, so nearly every row is a *backend-parity* gap
(the checked plan compiler has not caught up to the reference semantics), not a missing semantic.

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
| Moderate | **Masks / predicates / Iverson (Boolean) factors** — `where=`/Iverson terms | `maskOrPredicate` | `checkFactor` | ✓ (`Eval/Gather.lean` mask eval) |
| Low–moderate | **Unary factor functions** — `log`/`exp`/`sqrt`/`recip` applied to a read inside a term | `unaryFactor` | `checkFactor` | ✓ (`Eval/Gather.lean` `applyUnaryFn`) |
| Low | **max / min aggregation** — only `sum` is admitted | `unsupportedAgg` | `checkAggOp` | ✓ (tropical semiring `Combine`) |

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
   and result reporting. Bounded, but wider than #5–#7, and naturally coupled to #5 (predicates
   consume / produce bool).
5. **Masks / predicates / Iverson factors** — first genuine step up from a pure assign extension:
   needs a *positional* (UID-free) predicate / coordinate-arithmetic IR at the plan layer, evaluated
   per contraction coordinate, plus its checker. No output-geometry or dtype change, and the
   reference `PredArith` / mask eval is the oracle — but the coordinate-predicate IR is new
   vocabulary the plan layer does not have yet.
6. **Unary factor functions** — cheap *because the nonlinearity thread already shipped pointwise*.
   `f(read)` residualizes into a `.pointwise` temp the term then reads (reusing `RawPointwisePlan` /
   `runDensePointwise`), or a per-factor unary op on the contraction path. The reference
   `applyUnaryFn` is the oracle; the main new work is domain-error plumbing (`log`/`sqrt`/`recip`
   fail loud via `EvalError.unaryDomain`). Localized to the assign / contraction path.
7. **max / min aggregation** — smallest surface. Fits the *existing* `ContractionAlgebra` reduction
   slot: add `min`/`max` to `ScalarBinOp`, widen `admittedAlgebra`'s acceptance in `Check.lean`, add
   the reduce cases to the Dense worker. No new `PlanStep`, no new geometry, no dtype change; the
   reference tropical semiring is the ready-made oracle. **One real subtlety:** the `zeroPad`
   out-of-bounds policy feeds identity `0` into a sum, but a max-reduce needs identity `−∞` — the
   pad / identity interaction is the only place this bites.

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

- **Pointwise + axiswise nonlinearities** — admitted at top level (`checkNonlinTopLevel`) and inside
  scan `base`/`recur` blocks (`checkNonlinScanBlock`), residualized into an `assign → pointwise` /
  `assign → axiswise` chain. `unsupportedNonlin == 0` in the `DifferentialTest.lean` scan corpus.
  Closed by the nonlinearity plan (`nonlinearity_split_pair_direct_lowering.md` §3.6–§3.7).
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

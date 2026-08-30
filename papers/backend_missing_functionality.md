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
backend-side).

| Missing capability | `CapabilityError` | Preflight site | Ref. interp. does it? |
|---|---|---|---|
| **Masks / predicates / Iverson (Boolean) factors** — `where=`/Iverson terms | `maskOrPredicate` | `checkFactor` | ✓ (`Eval/Gather.lean` mask eval) |
| **Boolean / predicate *outputs*** — a `.predicate` decl | `booleanOutput` | `checkDecl` | ✓ (bool semiring `Combine`) |
| **Unary factor functions** — `log`/`exp`/`sqrt`/`recip` applied to a read inside a term | `unaryFactor` | `checkFactor` | ✓ (`Eval/Gather.lean` `applyUnaryFn`) |
| **Scatter statements + affine (strided/offset) LHS writes** — e.g. `Out[2*i] = …` | `scatterOrAffineLhs` | `checkStmt` / `checkLHSSlot` | ✓ (`Eval/Scatter.lean`) |
| **max / min aggregation** — only `sum` is admitted | `unsupportedAgg` | `checkAggOp` | ✓ (tropical semiring `Combine`) |
| **`.scanPre` + recurrence / callback morphisms** — the pre-built step-morphism escape hatch | `recurrenceOrCallback` | `checkScanStmt` / `checkStmt` | partial (`Stmt.recurMorphism`) |
| **Non-`f64` dtypes; dynamic / value-dependent shapes** | `unsupportedDtype`, `dynamicShape` | not reachable from preflight (f64-only by construction); `checkAssign` rejects non-`f64` sources downstream | n/a (mode boundary) |

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

# JAX scan fixture survey

Status: classification recorded by prototype dispatch A3 and NOT re-run since ("from A3 run"). Scope: which of
the existing Lean scan test schedules (`Eval.Plan.ScanCompileTest`) the JAX `affineReference` scan lowering
(`checkJaxScanSupport` gate + `renderScanNode` emitter + `_run_scan_node` runtime) accepts, and what the
refusals say about the next increments.

## Classification

The 14 donor schedules of `ScanCompileTest` in the table below were pushed through the nonlinearity
differential's pipeline (prepare, JAX gate, Lean dense run, JAX eager and jit, compare). About a dozen other
schedules in that file (for example `scratchUnusedF32Sched`, `scratchThenPlainReadSched`, `lateNopeSched`,
`scratchMaxSched`, `contractBaseSched`, `neutralScratchSched`, `allNeutralStateSched`, `rejSched`) were NOT
classified: they are mostly negative guards or tropical/f32 variants, but that is not checked here. No MISMATCH
was found among the classified donors: every one the gate accepts agrees with Lean within the differential's
tolerance.

| Class | Donor | What the donor is | Outcome |
|---|---|---|---|
| A (accepted, registered, f64) | `selfRecurSched` | self-recurrence, history 3 | fixture `scan_selfrecur` |
| A | `scratchSched` | scan-local scratch, history 3 | `scan_scratch` |
| A | `contractSched` | contraction in the step, history 4 | `scan_contract` |
| A | `deepHistorySched` | history 4, reads at `l` and `l-2` | `scan_deephistory` |
| A | `extentOneSched` | history 1, ZERO steps (result = base state) | `scan_extentone` |
| A | `axisPosSched` | axis-position read, history 3 | `scan_axispos` |
| A | `twoScanSched` | two scans, 3 outer steps | `scan_twoscan` |
| A | `statePlainReadSched` | two scans, plain statement reads the state | `scan_stateplainread` |
| B (refused by the JAX gate) | `coupledSched` | two context axes, history `#[3,3]`, 2 states | `unsupportedScanAxes 0` |
| B | `multiBaseSched` | two context axes | `unsupportedScanAxes 0` |
| B | `scratchPredicateSched` | Boolean scratch inside a scan | `unsupportedDestDType 0 2 bool` |
| refused at prepare (the donor is itself a negative Lean guard, not a scan to lower) | `zeroExtentSched` | zero-extent scan axis | `scanAxisZeroExtent` |
| refused at prepare | `partialSetSched` | partially set advancing result | `partialAdvancingResult` |
| refused at prepare | `scratchF32Sched` | mixed f32/f64 scratch | `unsupportedDtype` |

The three class-B refusals are the JAX gate's own limits (the Lean side runs them), so they are the work list;
the three refused-at-prepare donors are negative guards in Lean and have no JAX counterpart to write.

## Registry design

- The donors are IMPORTED, not copied: `EvalPlanNonlinSmoke.lean` imports `Eval.Plan.ScanCompileTest` (the
  runner builds that module first), so a survey fixture cannot drift from the Lean test it came from.
- `scanSurvey64` in `EvalPlanNonlinSmoke.lean` is the registry: a list of
  (fixture name, donor schedule, donor inputs, number of scan steps). Adding a fixture is one line. Each
  donor runs through its own `explicitF64Sched` (undeclared names are binary64), so the registry is binary64
  only; there is no binary32 survey.
- Survey fixtures are LINEAR (no pointwise, axiswise or unary step), so the generated header carries
  `"linear_ok": true` and the Python driver skips its "exercises a nonlinearity" requirement for them.
- The scan count is pinned per fixture in `checkAndRender` (the `scans` argument), so a donor that stopped
  lowering to a scan record fails loudly.
- Value-independent pins registered in the driver (binary64): `scan_extentone` equals its base state with
  `step_count` 0; `scan_deephistory` equals the plain recurrence `[1, 1, 1, 2]`; `scan_twoscan` is checked
  against a plain recomputation. Each is checked on Lean's result and on the eager and jit JAX results.

## Follow-ups this implies

1. Multi-axis context: `coupledSched` and `multiBaseSched` are refused with `unsupportedScanAxes 0`. Lowering
   them needs a scan over more than one context axis (nested or flattened `lax.scan`) in the emitter and the
   runtime, plus a gate that admits it.
2. Boolean scratch inside a scan: `scratchPredicateSched` is refused with `unsupportedDestDType 0 2 bool`.
   The runtime's scan carry and scratch slots are floating-point; a Boolean scratch needs a dtype-aware slot.
3. Not a follow-up: the three refused-at-prepare donors stay negative guards.

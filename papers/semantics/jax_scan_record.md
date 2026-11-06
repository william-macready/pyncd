# JAX scan slice record

Status: implemented on branch `worktree-jax-scan-proto` (tip `d58eb8fa` before the documentation commits),
not merged at the time of writing. Date: 2026-11-05. Design note:
`leanncd/docs/superpowers/specs/2026-11-05-jax-scan-lax-design.md`. Fixture classification:
`jax_scan_fixture_survey.md` (not duplicated here). User-facing how-to: the "Scan (affineReference)" section
of `leanncd/experiments/jax_bridge/README.md`.

## 1. Summary and finish line

The finish line was: a two-layer transformer written as a scan over the layer axis runs on the JAX
`affineReference` backend and matches the Lean checked-plan Dense result in binary64 and binary32, and equals
an unrolled oracle (the same model as two hand-copied layers, test code only).

It is met. `affineReference` now lowers a `.scan` step with ONE scan axis and real (zero-initialised) states
through `jax.lax.scan`. Evidence, all observed on the branch tip:

| Check | Result |
| --- | --- |
| Build: `Tests` + `JaxExperiment` | green, 8844 jobs |
| Nonlinearity differential (`run-evalplan-nonlin.sh`) | 32 binary64 and 24 binary32 fixtures pass (was 22 + 22); rtol/atol `1e-12`/`1e-14` (f64), `1e-5`/`1e-6` (f32) |
| Unrolled oracle | JAX scan H layers 1,2 equal JAX unrolled H1,H2 bit for bit on CPU, f64 and f32, eager and jit; `ORACLE_TOL` is exactly 0 |
| Python mutation manifest `jax_scan_mutations_python.json` | 6/6 killed (JS-P-01..06) |
| Lean mutation manifest `jax_scan_mutations_post.json` | 11 entries, all killed (g1..g5 gate, e1..e5 emitter, c1) |
| Re-pinned `jax_nonlin_mutations_post.json` | 8/8; five line pins moved +148 and entry JN-T1-06 was rewritten for the new `.scan` arm |

New fixtures: `transformer_scan` / `transformer_scan32` (two-layer real-RMSNorm transformer as a scan over the
layer axis, untied per-layer weights, weight layer-extent 3 = the history extent, the unused layer-2 slice
NaN and never read), `transformer_unrolled` / `transformer_unrolled32` (the oracle), and eight binary64 donor
scans imported from `Eval.Plan.ScanCompileTest` (`scanSurvey64`, flag `linear_ok`).

## 2. Design as built versus the design note

What matched: carry = the complete state tensors (the pre-step snapshot, since JAX is functional); the base
block runs once outside the scan with the ordinary tables; one scan axis; states start at zero; the existing
node runtime is reused so ordered-fold numerics are preserved; `einsumOnly`, both candidate conversions and
the evidence path still refuse scans with `unsupportedStep`.

Deviations, both found by building it:

- **`allowContext` opt-in (the design assumption was wrong).** The note said each scan block step goes
  through `jaxAssignSupported` with `allowUnary`. In fact the outer gate refused every step-block assignment
  (`contextualAssignment`), because step blocks are contextful by construction. The shared policy
  `checkJaxScanSupport` / `jaxScanSingleAxis` (in `LeanNCD/Eval/Plan/Executable.lean`) therefore passes the
  assign gate a private `allowContext` opt-in. The outer gate still refuses contextful assigns everywhere
  else. New `JaxSupportError` cases: `scanNonRealState`, `scanMultiAxis`.
- **Table placement.** The note had the per-step tables passed to the scan as `xs`. As built, the tables are
  stacked step-major, reshaped once to `(T, local)`, CLOSED OVER (constants of the trace), and row `r` is
  taken inside the body by `jax.lax.dynamic_index_in_dim` on the traced step counter. The emitter
  (`renderScanNode`, with `renderScanBlockNodes` and `buildScanWriteIndex`) emits one scan record per node;
  its contract is the `renderScanNode` doc comment. Runtime: `_run_scan_node` with `_run_block`,
  `_bind_captures`, `_place`, `_check_index`, `_store_result` (multiple destinations per node);
  `_run_term` / `_run_node` gained `slicer` / `shift`. New `JaxCodegenError` cases: `unsupportedScanState`,
  `unsupportedScanAxes`, `scanWriteOutOfRange`, `scanContextPos`, `scanWriteCollision`.

Scope as shipped: one scan axis (`historyExtents.size == 1`), real states only. Refused with located errors:
multi-axis scans (`scanMultiAxis` / `unsupportedScanAxes`; ScanCompileTest `coupledSched`, `multiBaseSched`),
tropical or other non-real states (`scanNonRealState`), Boolean scratch inside a scan (`unsupportedDestDType`;
`scratchPredicateSched`).

## 3. Fixture survey

See `jax_scan_fixture_survey.md`. Summary: of the donor schedules the gate accepts, all agree with Lean; the
refused ones are the multi-axis pair and the Boolean-scratch donor. Honest caveat: that survey was classified
before the Lean-side gate existed and has not been re-run since; its refusal column names the emitter error
(`unsupportedScanAxes`) where the gate now answers first (`scanMultiAxis`).

## 4. Findings

1. **A design assumption was wrong.** The outer gate refused every step-block assign, so the `allowContext`
   opt-in (section 2) was needed.
2. **A1's claim that no checked two-axis scan exists was wrong.** `ScanCompileTest` compiles `coupledSched`
   to a checked two-axis scan. The gate mutant g2 (drop the multi-axis refusal) therefore survived until
   `leanncd/test/Eval/Plan/ScanJaxGateTest.lean` (registered in the lakefile `Tests` globs) pinned the
   refusal on the compiled `coupledSched`; g2 is now killed.
3. **The Python pins are redundant with the Lean-vs-JAX comparison.** The unit-mean-square pin on H layers
   1,2, the NaN layer-2 slice and finiteness check, and the exact `ORACLE_TOL` survive alone for every
   runtime mutant tried, and the runtime mutants stay killed with them weakened. They only matter if Lean and
   JAX share a bug. JS-P-05 (one step too few) is killed only by a runtime consistency `ValueError`.
4. **An equivalent mutant exists.** Re-running the step block on the already-updated state is unobservable
   for single-axis causal scans: reads touch rows `<= l` and writes land on row `l+1`. A fixture that
   separates snapshot from updated state is NOT possible for this scope.
5. **Scatter duplicates.** The runtime uses `.at[idx].set`, whose duplicate-index result is unspecified (Lean's
   `commitWrite` is last-wins). The emitter throws `scanWriteCollision` on duplicate offsets within one
   write's per-step slice.
6. **Tables are not smaller.** Stacked tables are as large as an unrolled version's. The gain is one traced
   body, so trace and compile size do not grow with the layer count. Realistic sizes remain out of scope.
7. **A pre-existing broken manifest.** `jax_scatter_mutations_post.json` has been broken since before this
   slice: entry JS-T1-04's `old` string is gone from `EvalPlanCodegen.lean` and its line pins match no guard,
   so it exits 125 at validation. Not fixed (parked, below).
8. **Generated `.cache` modules go stale.** Run `run-evalplan-nonlin.sh` and `run-evalplan-scatter.sh`
   before any Python manifest, or the manifest mutates against old generated code.
9. **Rule 6 budget breaches** by the implementers (section 6).
10. **Main moved mid-slice.** The categorical-semantics prototype landed on main from another session; main
    was merged into the branch cleanly (a merge commit on the branch, no conflicts).

## 5. Parked items

Costs are the controller's rough estimates in dispatches (one dispatch is the Rule 6 unit), not measurements.

| Item | Cost / note |
| --- | --- |
| Multi-axis scans | Gated on the Lean-side F3-b stage 2 work (multi-axis scan slots in the checked path); JAX then needs per-axis step counters. Not estimated until stage 2 lands |
| Tropical / non-real scan states | Needs JAX tropical support first; the gate refuses with `scanNonRealState`. About 3 dispatches, with S2b-style carriers |
| Boolean scratch inside a scan | Refused with `unsupportedDestDType`; needs a Boolean carry. About 1 to 2 dispatches |
| Evidence path / `einsumOnly` scan | `unsupportedStep` today; needs `ExecutionEvidence` for scan (touches core `Executable.lean`). About 3 dispatches, together with the pointwise/axiswise/scatter evidence work parked earlier |
| Scalable tables (dynamic context arithmetic instead of stacked tables) | Table memory is unrolled-size today. About 3 to 5 dispatches; changes the emitter contract and the oracle story |
| Fix `jax_scatter_mutations_post.json` | About 1 dispatch (re-derive JS-T1-04 and the line pins; then re-run the 16/16 cycle) |
| Fixture separating snapshot from updated state | NOT possible for single-axis causal scans (finding 4); revisit only with multi-axis scans |
| GPU tolerance | Tolerances were measured on CPU only. About 1 dispatch on a GPU host |
| f32 siblings of the eight donor scans | The donors are binary64 only. About 1 dispatch |
| Re-run the fixture survey against the gate | Update its refusal column (`scanMultiAxis`) and classify the dozen schedules it leaves out. About 0.5 dispatch |
| Harden the runtime against malformed records (review R1, Minor) | Step writes check only that the index length is a multiple of the step count, not `steps * output size` (a base write checks it); a step assign without `context_pos` dies on an accidental `TypeError`; `zip(dests, result)` would drop states if `dests` were short. All unreachable from `renderScanNode`. About 0.5 dispatch, then re-run the Python manifest and the differential |
| `scanContextPos` backstop has no test (review R2, Major) | The check is unreachable from a checked plan (`Block.lean` forces the step assign's context shape) and not constructible from checked input (private constructors); manifest entry JS-L-e3 (`#[0]` to `#[1]`) is killed by the happy path only. Decide: delete the check, or build a `CheckedPlanBlock` test hook. About 0.5 dispatch; deleting shifts the `EvalPlanCodegen.lean` pins |
| Mutation coverage beyond `transformer_scan` (review R2, Minor) | The Python manifest mutates only that fixture; the T = 0 early return, multi-scan, `_check_index`, `_store_result` and step-write collisions have fixtures but are never mutated on purpose. About 1 dispatch |
| Independent pins for five of the eight donor scans (review R2, Minor) | Only `scan_extentone`, `scan_deephistory` and `scan_twoscan` have a plain-Python recomputation; the other five are Lean-versus-JAX only, so a bug shared by both would pass. About 1 dispatch |
| Scan block assignment with an Iverson factor (review R2, Minor) | The gate admits it, the emitter refuses with `iversonFactor`; unpinned. About 0.3 dispatch |
| `allowContext` scope (review R2, Minor) | It is applied to the base block too (unreachable: a base block's context shape is empty) and its `false` default is observationally unpinned. Tie it to `isStep`. About 0.3 dispatch |

## 6. Budget (Rule 6)

Harness-counted tool calls per dispatch, against the Rule 6 cap for that dispatch:

| Dispatch | Harness calls | Cap |
| --- | --- | --- |
| Prototype | 63 | 60 |
| A1 | 112 | 60 |
| A2 | 68 | 60 |
| A3 | 54 | 55 |
| A4 | 50 | 50 |
| A5 | 74 | 50 |
| Docs sweep and record | 67 | 45 |
| Review R1 (correctness) | 34 | 45 |
| Review R2 (gate, tests, docs) | 37 | 45 |

A1, A2, A5, the docs dispatch and the prototype breached the cap; A3, A4 and both reviewers were within it. Slice total input tokens were NOT
measured (no `token-report.py` run), so the 175M execution and 50M authoring figures cannot be checked here.
Earlier dispatches under-reported their own call counts by roughly 2x, so these are the harness counts.

## 7. Reproduce

From `leanncd/`:

```
lake build Tests JaxExperiment
experiments/jax_bridge/run-evalplan-nonlin.sh
experiments/jax_bridge/run-evalplan-scatter.sh
```

Then the Python manifest (after the two runners above, so `.cache` is fresh), from the repository root:

```
leanncd/experiments/jax_bridge/mutation_python_manifest.py papers/semantics/jax_scan_mutations_python.json
```

The Lean manifests (validate with `--check` first; it builds nothing):

```
leanncd/scripts/mutation-manifest.sh --check leanncd papers/semantics/jax_scan_mutations_post.json
leanncd/scripts/mutation-manifest.sh leanncd papers/semantics/jax_scan_mutations_post.json
leanncd/scripts/mutation-manifest.sh leanncd papers/semantics/jax_nonlin_mutations_post.json
```

`jax_scatter_mutations_post.json` fails `--check` today (finding 7).

**Re-pin after edits.** Every entry of `jax_scan_mutations_post.json` pins a `file:line:0` failure location:
`ExecutableTest.lean` (g1, g3, g4, g5), `ScanJaxGateTest.lean` (g2), `ScanAffineEmitTest.lean` (e1, e2) and
`EvalPlanCodegen.lean` (e3, e4, e5, c1), and `jax_nonlin_mutations_post.json` pins five `EvalPlanCodegen.lean`
lines. Any edit that adds or removes lines above a pinned line breaks the pin (this slice moved the nonlin pins by
+148). After such an edit: run the manifest, read each mismatching `expect`, and re-pin to the observed line. The
Python manifest keys on message text, not lines, so it does not need this.

## 8. Whole-branch review

Two read-only reviewers with different lenses ran on the branch tip before the merge.

- **R1, correctness against `runDenseScanWith`:** no Critical or Major findings. Hand-built scan records (deep
  history at `l-1` and `l-2` over a state with a NaN at a masked lane's placeholder index; two coupled states;
  overlapping writes, last write wins as in Lean; T = 0; f32 with x64 on and off; two chained scans) all matched a
  numpy re-implementation of Lean's semantics bit for bit, eager and jit. Three Minor findings about malformed
  records the emitter never produces are parked above. One correction to the review brief: Lean's `writesCollide` is
  applied to BASE writes only, so two step writes of one step may overlap; Lean and the runtime both apply step
  writes in `stepWrites` order, last write wins, so they agree and the emitter does not rely on that check.
- **R2, gate, tests, documentation:** no Critical findings. Fixed before the merge: the unbuilt scratch prototype
  `ScanTransformerProto.lean` is removed (the program text lives in `EvalPlanNonlinSmoke.lean` and
  `ScanAffineEmitTest.lean`; the prototype findings file says how to restore it from `a4dbfbda`); the survey no
  longer claims it classified every donor; the README names the CPU scope of "bit for bit" and the unpinned
  Iverson-in-scan refusal; the gate's doc comments no longer claim a fixture pins the full check order or that a
  checked multi-axis scan cannot be constructed; the re-pin instruction above was added. Parked above: the
  `scanContextPos` backstop, mutation coverage beyond `transformer_scan`, independent pins for five donors, and the
  `allowContext` scope.
- **Not reviewed by anyone:** the f32 behaviour of the eight donor scans (binary64 only), GPU behaviour, and scan
  nodes inside the evidence path (refused).

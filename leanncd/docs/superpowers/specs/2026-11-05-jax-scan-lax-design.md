# Scan on JAX via `lax.scan` — design

Status: approved in conversation 2026-11-05 (finish line, scope, deferrals). Process weight: **Full**
(new capability; `slice-plan` §0). Not yet planned or prototyped.

## Intent

The overarching goal is to run progressively more complex ML models, with the full structure at small
scale, through both the Lean (Dense) and JAX backends. The one-layer transformer with a real RMSNorm
already runs on both (`transformer_rms`, `transformer_rms32`). Scan is the largest JAX capability gap
and the form the paper uses for L layers with untied weights (`papers/transformer_example.md`).

## Finish line (user, 2026-11-05)

A two-layer transformer written as **a scan over the layer axis** runs on the JAX `affineReference`
backend and matches the Lean checked-plan Dense result, f64 and f32, plus an **unrolled oracle**: the same
model written as two hand-copied layers, kept in test code only (not a shipped backend), which the scan
result must equal.

After this slice, further slices add more complex models that exercise other tensor-logic features.

## Non-goals (this slice)

- Multi-axis scans (user: deferred; the Lean surface for them, F3-b stage 2, is also still open).
- Tropical / Boolean scan states (`initValue` other than `zero`); JAX has no tropical support yet.
- Scalable table memory (dynamic ctx arithmetic instead of stacked tables); realistic sizes remain out of scope.
- Evidence path, `einsumOnly`, scatter compute half; they keep their scan refusal.
- Lean-side gaps (embedding gather, ALiBi, data masks, RoPE): embeddings and positions stay input tensors.

## Design (author's call, to be confirmed by a prototype)

How Lean's checked scan works (`LeanNCD/Eval/Plan/Scan.lean`, `runDenseScanWith`): states are complete-history
tensors of fixed shape; a base block runs once and writes initial slices; then for each context coordinate
in mixed-radix order the whole state is snapshotted, the step block runs with that context, and every
state write commits at once (advancing row `ctx[i]+1`). Reads of the state are causal by check.

JAX lowering:
- **Carry** = the complete state tensors (constant shape). JAX being functional makes the pre-step carry the snapshot.
- **Per-step inputs** = the step block's affine lookup tables (`safe_index`, `mask`) and write-index tables,
  **stacked with a leading step axis** and passed as `xs`. The context only changes which entries a step uses, so the traced body is uniform.
- **Body** = the existing `_run_node`, pointwise and axiswise runtime, unchanged, so ordered-fold numerics are preserved.
- **Base block** runs outside the scan with the ordinary static tables; its writes build the initial carry.
- **Single scan axis**, so the step count is `historyExtents[0] - 1`.
- **Gate**: each scan block step goes through `jaxAssignSupported` (with `allowUnary := true`); scan stays refused everywhere else.
- **What this does not buy**: stacked tables are as large as an unrolled version's. The win is trace size and compile time not growing with L.

## Open questions for the first (prototype) dispatch — facts not yet measured

1. **Does a transformer layer already compile and run as a checked scan on the Lean side?** Masked axiswise
   (slice 5.3), unary factors and pointwise nonlinearities are admitted in scans, but no checked-plan scan
   fixture has a full attention + FFN + norm layer. Lean example 13 is the *legacy* `TLProgram.eval` scan
   evaluator (tied identity weights, sum-`normalize`), not the checked-plan path, so it is not evidence.
2. **Untied weights**: each layer's weights are read with a layer-axis coordinate (`W[l, ...]`). Confirm the
   checker admits a step-block read of an external tensor with a context coordinate, and that the stacked tables express it.
3. **Per-step scratch** (`Q`, `K`, `V`, `S`, ...): Lean's `KG-scanprojection` gap concerns read-outs *inside* the scan
   block; confirm the layer scratch needs none.
4. **Fixture sizes**: pick L=2 (finish line) and keep SEQ/m/h/k/d as in `transformer_rms`.

## Phases (rough, one dispatch each unless noted)

1. Prototype, Lean only: the two-layer scan as a surface program through the checked-plan path; observe values and any rejection (answers 1–3). If question 1 fails, stop and report: this is a Lean-side blocker, not a JAX task.
2. Codegen: emit per-step stacked tables for scan nodes (`EvalPlanCodegen.lean`), gate wiring.
3. Python runtime: `_run_scan_node` with `lax.scan`, f64/f32.
4. Fixtures + unrolled oracle + value-independent pins (Rule 9) + mutation manifest entries.
5. Docs sweep and record.

## Process notes

- Plan authoring is two dispatches (prototype, then write-up from artifacts), patch-driven for GPT execution (`slice-plan` §6, memory `feedback_plans_executed_by_gpt`).
- Budgets per CLAUDE.md Rule 6; count turns with the harness number, not self-reports.

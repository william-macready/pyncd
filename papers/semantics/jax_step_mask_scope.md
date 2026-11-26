# Scope note: step-aware `where` masks (and what the natural `Kh[k, s]` spelling needs on top)

Status: PREPARATION ONLY, written 2026-11-25 at local `main` `897b5ca6` while the window-read slice (`jax_kv_window_session_brief.md`) is with an executor. Nothing here was run except greps and file reads; no code was changed. Tags: [read] = read in the source today, [judgment] = my estimate. Per CLAUDE.md Rule 13 no plan is written until the window slice has landed.

## 1. The two obstacles are independent, and (A) is the valuable one

The natural spelling `Pa[s.] := softmax(where s ≤ t)(Kh[k, s] · Qr[t, k])` is blocked twice:

- **(A) the mask cannot see the scan step.** A `where` mask is evaluated over the statement's own `.free`/`.freeNorm` output axes; any other axis, the scan axis included, reads coordinate 0. Since 2026-11-22 that is refused at the source (`maskAxisNotOutput`, `finalizeScans` in `Structural.lean`) instead of silently misread.
- **(B) the checker cannot prove `Kh[k, s]` causal** (free-axis read of the scan's own history). The window slice proves the bounded forms (`t + u - 4`, `t - u`) and leaves this one refused.

**(A) alone already gives natural attention for the slot-cache model.** `kv_cache` stores the cache as a state indexed by SLOT (`Kc(s, k, t)`) and reads it at the current step (`Kw[s, k]`), so its read is causal today; it only needs `Mk[s, t]` because the mask `s ≤ t` is unavailable. With (A): `Pa[s.] := softmax(where s ≤ t)(Kw[s, k] · Qr[t, k])`, no `Mk`. The same holds for the existing refusal pins `maskInterScanAxis` (`Pa[j.] := softmax(where j ≤ l)(S[j, l])`) and `maskStepScanAxis`. (B) matters only for the time-indexed-history spelling, and the window/lag forms already cover that model. Recommendation [judgment]: do (A) as its own slice; treat (B) as optional and decide after.

## 2. Sites a step-aware mask touches (identifier @ file)

| Layer | Site | Today [read] | Change |
|---|---|---|---|
| Source guard | `finalizeScans`, rule `maskAxisNotOutput` @ `LeanNCD/DSL/Pipeline/Structural.lean` | refuses any mask axis that is not an own output axis | allow ONLY the enclosing scan's own iteration axes in a step statement or per-step intermediate; contracted and unbound axes stay refused (`maskContractedAxis`, `maskUnboundAxis`) |
| Reference evaluator | `evalStmtSliceSeeded` @ `LeanNCD/Eval/Scan.lean` (`sliceUids` filters the `seed` axes out, then `applyNonlin rn sliceUids slice`), `coordMap` and `perRowCoreWith` @ `LeanNCD/Eval/Nonlin.lean` | coordinate map over the slice axes only | the `seed : HashMap UID Int` already holds the current scan coordinates, so the mask environment only needs `seed` added (small); top-level `Eval.lean` unchanged |
| Plan compile | three `lowerMaskPredicate` sites @ `LeanNCD/Eval/Plan/Compile.lean`: base block (~1211), scan step (~1312), top-level (~1788) | local non-seeded output basis, empty pins; comments call this "Mask policy" | only the scan-step site needs the step coordinate; the base block needs its literal pin (see 3); top level unchanged |
| Plan IR | `RawAxiswisePlan.mask : Option PosBoolExpr` (width = `shape.size`), `checkAxiswise`/`checkAxiswiseF32`, `axiswiseIncluded` @ `LeanNCD/Eval/Plan/Nonlin.lean`; `RawStep`/`Block`/`Check` | mask over the tensor's own coordinates; the width check asserts `a.shape.size` | the real design decision: a context-width convention (`shape.size + block context`) or an explicit context field; the dense worker must pass the step coordinate; the f32 siblings follow |
| JAX codegen | `buildAxiswiseInclude` @ `experiments/jax_bridge/EvalPlanCodegen.lean` | one static row-major 0/1 table per axiswise node | a step-major stacked table (steps x shape) for an axiswise node inside a step block |
| JAX runtime | `_run_axiswise_node`, `_run_scan_node` `stacked` dict, `slicer` @ `evalplan_affine_runtime.py` | axiswise ignores `slicer`; stacked step-major tables exist only for assign factors and Iverson tables | stack and slice the axiswise include table the same way (the machinery exists) |
| Lean semantic model | `LeanNCD/Semantics/` | no mention of axiswise or masks [read: grep] | none |

## 3. Policy conflicts to decide (CLAUDE.md Rule 7), found by reading the pins

1. **Slice 5.3 documented the coordinate-0 reading as the policy.** `seededAxisZero` @ `test/Eval/Plan/ScanCompileTest.lean` pins "a mask over the seeded scan axis reads coordinate 0 at every step" and its docstring names live-step substitution as a mutation that must fail. A step-aware mask reverses this: that fixture and its mutation (4) must be re-stated, not deleted.
2. **The unrolled differential encodes the same policy.** `scanParityCheck` @ `test/Eval/Plan/DifferentialTest.lean` (T5.4) unrolls scans and its structural check asserts NO unrolled mask carries the seeded scan-axis UID: the unroller substitutes `0` (not the step) into masks (its comment: "an unsubstituted `[l = 0]` and the substituted `[0 = 0]` evaluate identically"). I first read this as an existing true-semantics oracle; it is not. Flipping that one substitution to the step literal turns the existing scan-vs-unrolled parity harness into a free INDEPENDENT oracle for the new semantics (reference, checked plan and unrolled would all have to agree); that is the cheapest strong test the slice can have [judgment].
3. **Structural pins that flip or must be re-decided** (`test/DSL/Pipeline/StructuralTest.lean`): `maskInterScanAxis`, `maskStepScanAxis` flip to accepted; `maskOwnAxisAfterScan` (a scan axis of a LATER scan masked in its own step) flips the same way; `maskBaseAtZero` and `maskBaseAtOne` need a decision: the base block pins the scan axis to a literal, so a step-aware rule should read that literal (`lowerFactorPredicate` already injects base pins for Iverson factors) or keep refusing; `maskContractedAxis`, `maskUnboundAxis`, `maskOtherScanAxisFree`, `maskPostScanAxis` and the other accept neighbours stay as they are.
4. The record (`jax_scan_record.md` section 26, "Making a mask see the live step ... not done") and the `StructuralTest` header comment state the current rule and must be corrected in the same slice.

## 4. Causality of the free-axis read after (A), if (B) is wanted

After (A), a source statement `Pa[s.] := softmax(where s ≤ t)(Kh[k, s] · Qr[t, k])` compiles to an internal assign (the contraction, which holds the read) plus a masked axiswise step on its OWN destination slot [read: `Compile.lean` pushes `.assign plan` then `.axiswise` on `preSlot`; `nonlinearSourceNotLocalAssignment` forces a nonlinearity's source to be a preceding assign of the same block]. That makes a dataflow proof small: the slot has exactly one consumer (the masked step), so cells the mask excludes cannot influence any output (masked entries leave the row max and sum: pinned by the "masked extreme" fixture in `NonlinCompileTest`). The obligation is `mask(cell, step) ⇒ slot(cell) ≤ t` for every cell whose read is non-causal. Two ways to discharge it [judgment]: (i) a SYNTACTIC match, one conjunct of the mask (normalised to `affine >= 0`) equals `t - slot >= 0` plus a non-negative constant (sound, incomplete: refuses `s ≤ t ∨ s = 0`, the sink mask, where the window spelling remains); (ii) enumeration over the output box at compile time (complete, cost O(box) per scan, too slow at production sizes). I would take (i). Only the fused single-statement form is covered (a named intermediate may have other consumers and stays refused). A row whose non-causal position is a REDUCTION axis is refused (the mask ranges over output cells only).

## 5. Size [judgment, unmeasured]

(A): two Full slices, Lean first (guard, reference, plan IR, dense worker, f32, unrolled-oracle flip, structural and differential pins, mutants), then JAX (codegen stacked table, runtime slicing, fixtures: `kv_cache` rewritten without `Mk` as the natural fixture, plus a `maskInterScanAxis` program), about 6 to 9 dispatches in all; the risk is the checked-plan IR change (many constructors and tests of `RawAxiswisePlan`). (B) on top: 2 to 3 dispatches. Prerequisite from the window slice: none for (A); (B)(i) reuses its predicate only as the fallback for bounded reads.

## 5a. After the window slice landed (2026-11-26, merge `919d7350`; record section 29)

What the landed slice gives this one [read]:
- **No file overlap except two places.** The window slice changed `Scan.lean` (new definitions beside `stateReadCausal`), one line of `Compile.lean` Phase 5 (plus two comments), tests and fixtures. The mask slice touches `Compile.lean` at the scan-step `lowerMaskPredicate` site (~1312), far from that line, and `LeanNCD/Eval/Plan/AGENTS.md`'s code-map row for `Nonlin.lean`.
- **The oracle pattern transfers.** `ecBruteSafe`/`ecCases` in `ScanTest.lean` walk the box literally and compare with the predicate; the route (B)(i) implication ("mask conjunct implies `slot <= t`") can be pinned the same way, using `evalPosBool` on the mask over (output cell, step) pairs, plus mutants. It is the cheapest way to make the syntactic-conjunct rule trustworthy.
- **Reference fixtures exist.** `kv_window`/`kv_lag` and `np_kv_history` (independent numpy model, six exports, gradient references) are the natural comparison for a natural-spelling fixture: same model, masked cells exactly 0 instead of `-1e9` scores, so agreement should be at rounding level [judgment, not observed]. `kv_cache` (slot cache with the `Mk` table) is the candidate to restate with `where s <= t` for (A).
- **Gaps the review left that (A) can close.** The window fixtures never slide (width 5, 5 steps, so no JAX fixture has a written slot outside the window). A step-aware mask makes a SLIDING window expressible as `where s <= t && s > t - W`; a fixture with `W` below the step count would pin the edge on JAX, which no current fixture does.
- **The window predicate is not mask-aware.** `stateReadCausalIn shape advancingDims contextPos f` sees only the read row, so (B) needs a second predicate (or an extra argument) at the same two call sites (`checkScanCore` in `Scan.lean`, Phase 5 of `compileScan`), and the raw-plan walk in `checkScanCore` currently visits `.assign` steps only: a mask-aware rule must also see the following `.axiswise` step. This is the real additional cost of (B) over what the window slice built.
- **Consumers of the strict pair** (found by the executor and confirmed by the review): the two production call sites, `IndexedAffineScanProfile`, and `IndexedAffineScanCompilerExamples` (guards and exact refusal strings). None is affected by a mask change.

## 6. Decisions needed from the owner before a plan is written

1. (A) alone first, (B) later or never? (recommended)
2. Reverse the Slice 5.3 coordinate-0 policy outright (recommended; it was a deliberate rule, now superseded by `maskAxisNotOutput` which already treats it as a bug)?
3. Base-block masks over the pinned scan axis: read the literal, or keep refusing?
4. IR: context-width convention for `RawAxiswisePlan.mask` or an explicit context field?

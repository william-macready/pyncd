# Scope: "true nested or two-axis scans" (2026-11-24, main b7f0a9ba)

Written for the owner, to decide what, if anything, to build next. Scoping only: no production change, nothing here is planned or scheduled. Evidence is marked **[ran]** (I ran it on b7f0a9ba), **[read]** (an exploration agent read the code; I did not re-run it) or **[judgment]** (an estimate or an inference).

## 1. Answer in one paragraph

The motivating model, a stacked RNN whose layer axis is a tensor axis (stacked weights `W[l, ...]`) with layer `l` at time `t` reading layer `l-1`'s NEW state, **runs today as one ordinary scan** once it is skewed onto the diagonal `k = t + l`: exact to about 2e-16 against the true stacked model on Lean, JAX eager and JAX jit, finite gradients matching finite differences **[ran]**. The same trick handles a 2-D grid DP with a diagonal dependency (through a delay-line state). So a native grid/nested-scan capability is **not needed for this model family**; it would be a convenience (the program is written as the grid, not as its skew) plus reach into recurrences the skew cannot express. My earlier statement that the layers x time ideal "needs a capability change" (record sections 26 and 27, the layers-time brief section 6) was too strong for the stacked RNN and is corrected here.

## 2. What exists today (terminology matters)

| Term | Meaning today | Evidence |
|---|---|---|
| "Multi-axis scan" | NOT a lockstep diagonal. The reference evaluator and the checked plan run one step per TUPLE of the grid `prod(extent_a - 1)`, axis 0 fastest; each step writes the cell at `+1` on every advancing axis and reads the pre-step state | [read] `Eval/Scan.lean` `evalScan`; `Eval/Plan/Scan.lean` `runDenseScanWith`, `mixedRadixUnrank`; fixtures `coupledSched`, `coupledSched4` |
| Reads allowed in a step | per advancing axis: offset <= 0 relative to the tuple (`stateReadCausal`, `causalAdvancingRow`); `l - 1`, `t - 1`, `l - 1, t - 1` all prepare and agree with the reference | [ran] variants v0, v3, v5 |
| Reads refused | offset +1 on an axis (a west or north neighbour of the written cell): `stateReadNotCausal` in the checked plan | [ran] v1 (`l + 1, t`), v2 (`l, t + 1`), v4 (own cell) |
| Frontend check | `readsIterAhead` does not fire for these: spaced `l + 1`/`t + 1` parse, and a read inside a per-step intermediate is not examined; `compileToScheduled` accepts all six variants | [ran] |
| Reference evaluator | accepts all six, and for the west and north reads computes the TRUE grid values (max difference to a numpy grid 4.6e-7, which is the 6-decimal print rounding); so the reference already has the semantics, only the checked plan and JAX refuse | [ran] |
| JAX | refuses every multi-axis scan: gate `jaxScanSingleAxis` -> `scanMultiAxis`, rendered as `unsupportedScanAxes 0` | [ran] all variants; [read] `Executable.lean:409-437`, `EvalPlanCodegen.lean:185` |
| Boundary faces | two base statements that may write the same cell (the corner of two faces) are refused by BOTH the reference and the checked plan (`baseWritesOverlap`); one face works | [ran] |
| Nested scan (a scan inside a step body) | not representable: `BlockStep` has no scan case; base blocks have no context, and a step write that pins an advancing dimension fails `stepWriteRowsOk` | [read] `RawStep.lean:79-80`, `Plan/Scan.lean` |
| F3-b "stage 2" | multi-axis SCATTER rows inside a scan (colliding affine writes): a different item; a grid scan does not need it (its writes are `.iterNext` slots) | [read] `Compile.lean:152-153` |
| Part V certification | single time axis only (`historyShape d N = [space, time]`); a grid scan creates no obligation there, certifying one would be a new slice | [read] `Semantics/Plan/ScanHistory/*` |

## 3. The skew (no capability change) [ran]

Stacked RNN, `L = 3`, `T = 5`: layer `l` handles time `t = k - l` at scan step `k`; the state history position of `h[l, t]` is `t + l + 1`; layer `l` is active iff `l <= k <= T-1+l`, held otherwise; layer 0 consumes `x_k`, layer `l >= 1` consumes the layer below from the previous scan step. `iter k = T + L - 1 + 1 = 8` (7 scan steps).
```
iter k = 8
tensor f64 X(k, i), Wx(d, i), E0(l), Sh(l, m), H0(l, d), Wp(l, d, e), Up(l, d, e), Act(k, l), Hold(k, l)
tensor f64 G(l, d, k), Ix(k, l, e), Hi(l, e), Aa(l, d), Nn(l, d)
G[l, d, 0]     := H0[l, d]
Ix[k, l, e]    := E0[l] · Wx[e, i] · X[k, i]
Hi[l, e]       := Sh[l, m] · G[m, e, k] + Ix[k, l, e]        -- A2: Hi[l, e] := G[l - 1, e, k] + Ix[k, l, e]
Aa[l, d]       := Wp[l, d, e] · Hi[l, e] + Up[l, d, e] · G[l, e, k]
Nn[l, d]       := tanh(Aa[l, d])
G[l, d, k +1]  := Act[k, l] · Nn[l, d] + Hold[k, l] · G[l, d, k]
```
Data: `E0 = [1,0,0]`, `Sh` = lower shift, `Act[k, l] = 1` iff `l <= k <= T-1+l`, `Hold = 1 - Act`, `X` finite padding rows 5..7. In-program unskew also works: `axis t : ℕ = 5` and `Out[l, d, t] := G[l, d, t + l + 1]`.

| Check | Result |
|---|---|
| Stages (elaborate, schedule, prepare, Dense, JAX render, eager, jit) | all pass for A (shift matrix), A2 (native `l - 1` read), A + unskew; kinds (6,1,0), 7 scan steps, one scan record |
| Exactness vs the TRUE stacked model (numpy, explicit loops) | per layer 1.1e-16 / 1.5e-16 / 1.7e-16 (Lean); 2.2e-16 / 1.2e-16 / 2.2e-16 (eager and jit); held slots equal `H0[l]` exactly |
| Gradient of `sum(G[2, :, 7])` | finite in eager and jit, equal bitwise, 8 central-difference directions agree to 1e-11 |
| Probe B: 4x4 grid DP `G[i,j] = tanh(a G[i-1,j] + b G[i,j-1] + c G[i-1,j-1] + w[i,j])` skewed by `k = i + j`, the `(i-1,j-1)` dependency through a delay line `D[r, k +1] := G[r, k]` | exact to 1.1e-16 (Lean), 1.7e-16 (JAX); program below |
| Out-of-range read `Z[l - 1, e]` at `l = 0` | zero pad (Lean and JAX), not an error |

```
iter k = 8
tensor f64 Wk(k, r), Act(k, r), Hold(k, r), Ma(r, m), Mb(r, m), Mc(r, m), Gz(r)
tensor f64 G(r, k), D(r, k), Aa(r), Nn(r)
G[r, 0]     := Gz[r]
D[r, 0]     := Gz[r]
Aa[r]       := Ma[r, m] · G[m, k] + Mb[r, m] · G[m, k] + Mc[r, m] · D[m, k] + Wk[k, r]
Nn[r]       := tanh(Aa[r])
G[r, k +1]  := Act[k, r] · Nn[r] + Hold[k, r] · G[r, k]
D[r, k +1]  := G[r, k]
```
(coefficients folded into the matrices `Ma`, `Mb`, `Mc`; the state starts at zero because "not started" is read as the zero boundary.)

**Traps [ran]:** (1) the padding rows of `X` (and any input that feeds `Nn` while `Act = 0`) must be FINITE: `Act * Nn` with a NaN row gives `0 * NaN = NaN`, measured as 24 of 96 NaNs in `G` and every gradient non-finite, so the NaN spare-row convention of the other fixtures does NOT apply; (2) `Hold = 1 - Act` must be data (no subtraction in a term, no `where` over a scan axis); (3) iteration extent is steps + 1; (4) a dependency more than one skewed step back needs one delay-line state per extra step.
**Limits [judgment, not probed]:** data-dependent or non-affine dependency structure, a skew factor above 1, anything needing an inner loop whose trip count depends on the outer state; variable lengths are different `Act`/`Hold` data and a different `iter` extent, not a different program. Cost: `T + L - 1` scan steps instead of `T`; every layer is evaluated at every step and masked by `Act`. Compile and trace time were not measured.

## 4. Options

Dispatch = one agent session of at most about 60 tool calls and 250k context (Rule 6). All estimates are **[judgment]** from the agents' readings; reference points: the original JAX scan slice took 9 dispatches (5 over the cap), the four-model layers-time fixture session took about 136 harness calls (over two dispatches).

| Option | What it gives | Cost | Main risk |
|---|---|---|---|
| **A. Skewed fixtures, no capability change** | The stacked RNN with a layer axis and true new-state dependence, and a grid DP, as pinned fixtures in both precisions (programs above, in the layers-time style: independent numpy models, causality and held-slot pins, gradient pins, hand mutants) | 2 to 3 dispatches plus a short brief (the programs and traps are already probed) | the skew's limits above; the finite-padding trap needs its own pin; binary32 not probed |
| **B. Frontend desugaring (the user writes the grid, the compiler skews)** | the grid surface form with no plan, JAX or Part V change | 2 to 4 dispatches (an agent's estimate) plus a semantic spec for the generated `Act`/`Hold`/delay lines | exactness for general shapes, error messages in skewed coordinates; not probed |
| **C. Native grid scan** (relax the causality predicate; JAX flattened multi-axis) | reads at +1 on one axis, i.e. the grid as written, on Lean and JAX | Lean 2.5 to 6.5 (frontend `readsIterAhead` plus the plan's `stateReadCausal`/`causalityFailure` as ONE joint rule: each offset <= +1 and not all +1; oracle templates `ScanGen`, `ScanUnroll` scope, `DifferentialTest` three-way cases, 4 to 6 mutants) plus JAX 1.5 to 3 (gate, emitter, runtime) plus fixtures and gradient pins 1 to 2: about 5 to 11 dispatches over two Full slices, plus authoring and review (the Boolean-reach authoring cost 218M tokens against a 50M target) | silent wrong answers if the JAX stacked-table row order (last axis fastest) is not reordered to Lean's rank order (axis 0 fastest) [read]; fixtures must use UNEQUAL extents and a mutant must swap the orders; the all-ones offset or a +2 offset admitted by mistake splits the three evaluation orders; corner overlap policy; reference/plan alignment |
| **D. True nested scan** (`BlockStep.scan`, or step face writes) | an inner loop inside a step body | 4 to 8 dispatches on Lean alone, then JAX | no use case here that A or C does not cover; not recommended |

## 5. Recommendation

Option A executed on `jax-skew-exec`: all three models in both precisions, value/structural/gradient pins and eight accepted mutant kills; see [record section 28](jax_scan_record.md#28-skewed-single-scan-execution-true-stacked-layers-and-grid-dp-2026-11-24). Awaiting the owner's whole-branch review; not merged or pushed.

Do **A** if the goal is the models (stacked RNN with a layer axis, grid DPs): it is the cheapest, it is already probed, and it matches the repo's progression style. Treat **B** as optional, only if the grid surface syntax itself is a goal. Park **C** and **D** until a program needs something the skew cannot express (data-dependent structure, a skew factor above 1) or until the ergonomics justify two Full slices; if C is ever started, split it Lean first (one shared causality predicate for the frontend, the reference and the plan), JAX second.

## 6. Decisions for you

1. Is the goal the MODELS (then A) or the grid as a source construct (then B or C)?
2. If C: the exact causality rule (joint: every offset <= +1, not all +1) versus narrower (exactly one axis at +1); and whether the evaluation order is a semantic guarantee ("any linear extension of the componentwise order", which the three evaluators satisfy) or an implementation detail.
3. If C: make the reference evaluator refuse what the checked plan refuses (today it accepts the own-cell read v4 and the renamed-axis read of record section 26, P2): one shared predicate, or leave the divergence.
4. Overlapping boundary faces (the corner): keep refusing, define "later face wins", or sum (additive collection). The stacked RNN does not need two faces (the layer-0 input can enter as a step term, `Ix`), so this matters only for DPs such as edit distance.
5. Part V certification of a two-dimensional history: out of scope (current single-axis certification stays).
6. Process weight: A is Direct path (fixtures only); C is Full, two slices.

## 7. Not determined

JAX compile/trace time and gradient memory of the skewed scan; binary32 behaviour of the skew; whether `ScanUnroll` refuses a positive bias; whether a skew factor above 1 or strided/dilated dependencies work; whether B can be made exact for general shapes; the JAX stacked-table row-order trap and the cost figures are readings, not runs.

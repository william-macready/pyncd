# Two-layer transformer as a checked-plan scan: prototype findings (Lean only)

Date 2026-11-05. Serves `leanncd/docs/superpowers/specs/2026-11-05-jax-scan-lax-design.md`, open questions 1-3.
Prototype: `leanncd/experiments/jax_bridge/ScanTransformerProto.lean` (scratch; not in the lakefile; no production
Lean and no JAX code touched). Every number below is from a real run of that file.

## Verdict: ACCEPTED (no change needed)

The two-layer transformer written as `iter l = 3` with untied per-layer weights `W[l, ...]` compiles
(`compileToScheduled` -> `prepareEvalPlan`) and runs (`runPreparedDense` f64, `runPreparedDense32` f32) on the
CHECKED-plan path on the first attempt, and equals the hand-unrolled two-layer program **bitwise** in both
precisions. Open questions 1, 2 and 3 of the design note are answered yes; the work is not Lean-blocked.

## Reproduce

```
bash /abs/path/to/worktree/leanncd/scripts/lean-file.sh /abs/path/to/worktree/leanncd experiments/jax_bridge/ScanTransformerProto.lean
```

Output is the `#eval` messages; any pin failing is an error. The file imports `EvalPlanCodegen` only for
`renderCompileCause`; that olean must be built (`lake-build.sh <worktree>/leanncd JaxExperiment`, already built here).

## Program shape (what was needed)

`iter l = 3`, `axis s : ℕ = 3`, base `H[q, m, 0] := X[q, m]`, step `H[q, m, l +1] := Z2[q, m] / Sd2[q]`, 18 per-step
scratch statements recomputed from `H[·,·,l]` (Q, K, V, S, AttnOut, Attn, Z1, Ss1, Ve1, Sd1, A, F, Y, Z2, Ss2, Ve2,
Sd2), masked softmax `S[h, q, s.] := softmax(where s ≤ q)(...)`, relu FFN, residuals, real RMSNorm (`Z·Z·Inv[m]`,
`+Eps[q]`, `sqrt`, `/`), 2 heads. Weights `W_Q/W_K/W_V[l,h,k,m]`, `W_O[l,m,h,k]`, `W_in[l,d,m]`, `W_out[l,m,d]`;
inputs `X[3,4]`, `Inv[4]`, `Eps[3]`. Layer-1 weights = layer-0 weights rotated by 5 and scaled by 0.8 (genuinely
different); the layer-2 weight slice (never read by a 2-step scan) is **NaN** as a sentinel.

### Item 1: compiles and runs?
- f64: prepare OK, run OK. f32: prepare OK (`storageKind = float32`), run OK. Outer plan is exactly 1 step (a scan).
- Declared extent: `iter l = 3` is the HISTORY extent (layers 0,1,2 = 2 steps). Weight tensors sharing the axis
  `l` must have l-extent **3**, not 2. Probe with weights stacked to extent 2:
  `prepareEvalPlan: shape: axis size conflict for uid 1: 3 vs 2` (a typed shape error at prepare). The unused last
  slice (index 2) is simply never read; the NaN sentinel proves it (all outputs finite).

### Item 2: state H, both layers (f64, `H[q, m, l]`, shape [3,4,3]; row-major q, m, then layer)
```
H[:,:,0] (= X): 0.5 -1.0 0.75 0.25 | 1.25 0.5 -0.5 1.0 | -0.75 1.5 0.25 -1.25      (bitwise == X)
H[:,:,1]: 0.727577 -1.083589 1.086248 1.056657 | 1.176615 -0.527165 0.627290 1.394334 | -0.516346 1.464720 0.233705 -1.238285
H[:,:,2]: 1.308041 -0.897803 0.420359 1.142913 | 1.372335 -0.546950 0.282308 1.318265 | 0.345999 1.351628 0.914731 -1.103012
max|H1-H2| = 0.862346
```
- Layers differ. Value-independent pin (RMSNorm unit mean square per row, tolerance 1e-3): f64 layer1
  [0.999998, 0.999997, 0.999996], layer2 [0.999993, 0.999994, 0.999996]; f32 identical to 6 places. Contrast
  (the pin can fail): H[:,:,0] = X has mean squares [0.46875, 0.765625, 1.109375].
- f32 layer 1/2 values equal the f64 ones to 6 places; f32-vs-f64 scan max abs diff 1.6e-7 (layer 1), 2.1e-7 (layer 2).

### Item 3: unrolled reference (two hand-copied flat layers, same checked-plan path, 40 outer steps)
- f64: scan vs unrolled layer 1 **bitwise equal**, layer 2 **bitwise equal** (max abs diff exactly 0).
- f32: scan vs unrolled layer 1 and layer 2 **bitwise equal** (max abs diff exactly 0).
- So the scan result is not merely close to the unrolled oracle: a JAX lowering that preserves the Lean per-step
  order of operations has a bitwise target (modulo the usual libm-vs-XLA tolerance for sqrt/exp already accepted
  in the nonlinearity smoke).

### Item 4: structure of the checked scan plan (identical in f64 and f32; pinned by `checkStructure`)
- Outer: slots `[0]X[3,4] [1]W_Q [2]W_K [3]W_V [4]W_O[3,4,2,2] [5]Inv[4] [6]Eps[3] [7]W_in[3,4,4] [8]W_out[3,4,4]
  [9]H[3,4,3]` (W_Q/W_K/W_V `[3,2,2,4]`); 1 outer step = the scan; materialized `H:9`.
- **States: 1**, `destSlot=9`, shape `[3,4,3]`, `advancingDims=#[2]`, `initValue=zero`, `historyExtents=#[3]`,
  policies `axisZeroFastest` / `zeroThenBaseOverlay` / `immutablePreStep`.
- Base block: contextShape `#[]`, 1 assign (`dst=1`, out `[3,4]`, reads slot 0 = X). Base capture:
  `in0 <- external(0)`. Base write: `out1 -> state0`, coeffs `[[1,0],[0,1],[0,0]]`, bias `[0,0,0]` (row 2 constant 0 =
  layer index 0).
- **Step block: contextShape `#[2]`** (2 steps), 29 block-local slots, **20 steps in order**:
  `a a a a w a a a a a a a a p a a a a a a` = 18 assign, 1 axiswise (step 4, softmax, `axisPos=2`, shape
  `[2,3,3]`, `mask=true`), 1 pointwise (step 13, relu). Order: Q, K, V, scores(assign, step 3), softmax(axiswise),
  AttnOut, Attn, Z1, Ss1, Ve1, Sd1(unary sqrt read), A(unary recip read), FFN pre-activation, relu(pointwise), Y, Z2,
  Ss2, Ve2, Sd2(unary), H-next (unary recip read). 4 unary reads total (2 per RMSNorm); every non-input step
  tensor of the layer is block-local (scratch is NOT a state).
- **Step captures: 9**: `in1 <- state(0)` (H snapshot, `[3,4,3]`) and `in0,in2..in8 <- external(1,2,3,4,5,6,7,8)`
  (the weights, Inv, Eps; X is only a base capture).
- **Step write: 1**, `out28 -> state0`, domain = `context(1) ++ outputSlice(2)`, coeffs `[[0,1,0],[0,0,1],[1,0,0]]`,
  bias `[0,0,1]`: row 2 (the layer dim) = ctx + 1.
- **ReadPlan affine rows with the context coordinate**: exactly 10 reads carry the ctx column (term basis column 0,
  `contextPos=#[0]`): the 6 per-layer weight reads and 4 reads of the state H (Q, K, V and Z1).
  - Weight read `W_Q[l,h,k,m]` (step 0, src slot 0, source shape `[3,2,2,4]`, iteration basis `[ctx, q, h, k, m]`):
    coeffs `[[1,0,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]]`, bias 0. **The context coordinate is a
    coefficient column on source row 0** (the layer row), identity-like, no bias. Same for `W_O` (row 0 = ctx),
    `W_in`, `W_out` (source `[3,4,4]`, basis `[ctx,q,m,d]`).
  - State read `H[q,m,l]` (src slot 1): coeffs `[[0,1,0,0,0],[0,0,0,0,1],[1,0,0,0,0]]` for Q/K/V (source rows q,m,l):
    **ctx column on source row 2** (the layer row) with bias 0 (reading layer `l`); the K/V reads use `H[s,m,l]`
    in the same shape. The state snapshot is what step captures bind to slot 1.
  - All other step reads (the scratch, Inv, Eps) have no ctx coefficient: they are ordinary context-free affine maps
    over the block-local slots (the existing JAX pointwise/axiswise runtime consumes them unchanged).
- Consequence for the JAX lowering: the only context dependence is (a) a ctx column on the leading row of 6 weight
  reads, (b) a ctx column on the layer row of 4 state reads, (c) the `+1` write row. Step-stacked tables are
  needed for exactly those reads and the write; everything else is the same table at every step.

### Item 5: workarounds needed
- **No scan-specific workaround for compile/run.** Scratch tensors need no up-front declaration and no `.`-marker
  beyond the softmax marker `s.` that the one-layer fixture already uses.
- Declarations that ARE required (probed one at a time against the f32 program):
  - `axis s : ℕ = 3`: REQUIRED. Without it prepare fails:
    `shape: evalAssign K: output axis (uid 5) has no inferable size (it appears in no read position)`. Reason: in
    the step block `K[s,h,k] := W_K[l,..]·H[s,m,l]` reads `s` only through the scan state `H`, which carries no
    size for it. (In the flat one-layer fixture `s` is inferred from `X[s,m]`.) Plan for the fixture: declare `s`.
  - the softmax marker `s.`: REQUIRED (same as flat): without it `NonlinCompileError.noMarkedReductionAxis "S"`.
  - `tensor S(h, q, s)` and `tensor H(q, m, l)` declarations: NOT required here (accepted, H bitwise equal to the
    baseline either way). They are kept in the shipped form to pin axis order; do not read this as general.
  - f64: every tensor must be declared `f64` (inputs, state, scratch); declaring only `H` and `S` fails with
    `capability: unsupportedDtype "H: mixed f32/f64 storage in one schedule"`. This is the same hand-declaration
    discipline as `transformerRmsProg`; the f32 program needs none.
- The layer-2 weight slice cannot be dropped (extent must equal the declared history extent, see item 1), but it
  is never read; NaN-filling it is a free "unread slice" pin (all outputs finite).

## Answers to the design note's open questions
1. Does a transformer layer already compile and run as a checked scan on the Lean side? **Yes**, f64 and f32,
   with masked axiswise, unary reads and a pointwise relu all inside the step block; bitwise equal to the unrolled
   program.
2. Untied weights: the checker admits step-block reads of an external tensor with a context coordinate; the plan
   expresses it as a ctx coefficient column on source row 0. Weight l-extent must equal the declared
   history extent (3), shape-checked at prepare.
3. Per-step scratch: needs no read-out inside the scan block; it is block-local scratch (block sig slots 9..28),
   not a state, and no `KG-scanprojection` gap is hit. Only `H` is a state and the only materialized output.

## Surprising / worth carrying into the plan
- First-try acceptance, bitwise-equal results in both precisions (so the tolerance story in the JAX phase is only
  libm-vs-XLA, not scan-vs-unrolled).
- `axis s` must be declared (state-only reads give no size). The fixture must include it.
- History extent semantics: 3 for two layers, and the weights carry the same 3, so layer-2 weight data is a dead
  slice; the JAX fixture's weight inputs must be built with that dead slice (any finite or NaN values).
- `Float` prints at six digits, so a max-abs difference prints `0.000000` for exact and for merely tiny
  differences alike; the file reports the bitwise flag separately, and scales the f32-vs-f64 difference by 1e9.

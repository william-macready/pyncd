# Session brief: 1-D convolution (stride, dilation, causal padding) and a patch embedding feeding the layer scan (JAX bridge)

Status: not started. Written 2026-11-10 at local `main` `2c461f82` (ahead of `origin/main`; nothing here depends on the unpushed commits). Process weight: Direct path (`.claude/skills/slice-plan/` section 0): tests and fixtures only, plus ONE
small additive edit to the fixture driver's shared `checkAndRender` (section 3, step 0), no production change. Scratch probes on 2026-11-10 answer the "is it expressible" question for every form this brief uses (section 2) and found
the traps listed there. If any NEW pre-flight answer needs an emitter, runtime, grammar or checker change, STOP and report (do not edit `EvalPlanCodegen.lean`, `evalplan_affine_runtime.py`, `LeanNCD/DSL/*` or `LeanNCD/Eval/Plan/*`; that is a
different process weight and the user's call). CLAUDE.md applies, in particular Rule 13 (worktree, merge to LOCAL main, do not push unless asked), Rule 14 (scope gate) and Rule 6 (budgets). Siblings: `jax_cross_attention_session_brief.md`
(landed; record section 18 and 18.1 of `papers/semantics/jax_scan_record.md`), `jax_gqa_session_brief.md` (sections 15 to 17), `jax_multiquery_session_brief.md` (13), `jax_predicate_masks_session_brief.md` (12): same harness, same pin style, same hand-mutant discipline.

## 1. Goal

Every fixture so far reads its tensors through plain axes; the only affine reads are the GQA head map (`Q[q, 2 * g + r, k]`) and the unary-read domain pins. A convolution is the first model whose COMPUTATION is an affine read: an output position
`o` reads the input at `stride * o + dilation * i + bias` for each kernel tap `i`, with channels, a bias and zero padding at the edges. Three models, each adding one structural idea on top of the previous machinery:

1. `conv1d_cnn`: a small 1-D CNN classifier. Valid stride-1 convolution with bias, relu, a stride-2 dilation-2 convolution that READS AN INTERMEDIATE through an affine slot, relu, global mean pool, linear head, softmax. New: strided, dilated and
   biased affine reads of inputs and of intermediates, kernel and channel reductions together, a reduction over the pooled axis.
2. `conv1d_causal`: a TCN residual block. Two dilated CAUSAL convolutions (left zero padding by a negative bias, output extent = input extent), relu between, a 1x1 convolution on the skip path, residual add. New: negative-bias reads whose
   out-of-range taps are zero in every backend, and a value-independent CAUSALITY pin (like the mask fixtures' receptive field).
3. `vit_patch`: a patch embedding (non-overlapping windows, stride = window) plus a positional embedding feeding the EXISTING standard pre-norm scan transformer. New: a convolution-shaped statement computed before the scan whose result is the scan's
   base state; the end of the progression's first step (a ViT-style encoder).

Not in scope (park with a one-line cost if you find more): max pooling (a max reduction; max-plus is Lean-only today, not on JAX), transposed convolution and upsampling (top-level scatter writes, a different feature), 2-D convolutions beyond
the optional stretch in section 3, batch axes, normalisation layers other than the existing RMSNorm, a convolution INSIDE a scan step (affine reads of the scan state), explicit zero padding by a scatter write (section 2, trap 3), changing any
existing fixture, the Python runtime, the emitter, the mutation manifests.

## 2. What exists (verify each before relying on it) and the probe findings

- Harness: `leanncd/experiments/jax_bridge/EvalPlanNonlinSmoke.lean` (`fixture64` / `fixture32` ~142 / ~148, `checkAndRender` ~76, helpers `t64`, `env64`, `gqaGen seed n` = `0.6 * sin (seed + 1.7 i)`, `scanStack`, `gainStack`, `scanWeights`, the mask fixtures'
  `maskX`, `maskEps`, `maskEnv64` / `maskEnv32`, the standard `scanProg` ~597; registrations in `corpus64` / `corpus32`: `fixture64 "<name>" prog env minPw minAw (some (a, pw, aw)) true (scans := n)`). Driver `evalplan_nonlin_smoke.py`: `np_transformer` (do NOT edit it),
  `np_state`, `check_np`, `MODEL_TOL`, `TRANSFORMER_FIXTURES`, `cross_fixture_pins` / `cross_wide_pins` (the pin style to copy), `cross_grad_pins` and `fixture_grad_pins` (gradient pins), `GRAD_TOL`, `GRAD_FD_TOL`, `trim_nan_layer`.
- Baseline gates on current main: `lake-build.sh <wt>/leanncd Tests JaxExperiment` = 8846 jobs, 0 errors (re-verify); `run-evalplan-nonlin.sh` = 44 binary64 and 36 binary32 fixtures within tolerance. Expected differential if all three models are added in both
  precisions: 47 binary64 and 39 binary32 (the optional 2-D stretch adds 1 and 1). binary32 headroom has been thin (1.6x to 2.4x for the cross fixtures, sink 1.2x): REPORT the headroom of every new binary32 fixture; do not loosen any tolerance.
- **Probe findings (scratch, 2026-11-10, copies of the fixture file's head with probe `main`s, `.lean` files in the session scratchpad; nothing below is a pin yet).** Binary64 unless stated. Inputs `X[11, 2]`, `W[4, 3, 2]` by `gqaGen`-style sines.

  | Form | Source | Result |
  |---|---|---|
  | valid, stride 1 | `Y[o, d] := W[d, i, c] · X[o + i, c]`, `axis o : ℕ = 9` | prepares, Dense, JAX eager and jit == numpy loops to 2.2e-16 |
  | stride 2 | `X[2 * o + i, c]`, `axis o : ℕ = 5` | same |
  | dilation 2 | `X[o + 2 * i, c]`, `axis o : ℕ = 7` | same |
  | depthwise | `Y[o, c] := W[c, i] · X[o + i, c]` | same |
  | patch embedding, stride = window | `Pt[p, m] := Wp[m, i, c] · X[4 * p + i, c]` | same, exact |
  | 2-D patch embedding | `Pq[py, px, m] := Wq[m, iy, ix, c] · Img[2 * py + iy, 2 * px + ix, c]` | same, exact |
  | bias (broadcast add) | `Y[o, d] := W[d, i, c] · X[o + i, c] + B[d]` | same, exact |
  | conv, relu, conv on the INTERMEDIATE | `A1[o, d] := relu(Y1[o, d])`, `Y2[p, e] := W2[e, i, d] · A1[p + i, d]` | one plan, exports `Y1`, `A1`, `Y2`; all three match numpy to 2.2e-16 |
  | causal, dilated | `Y[o, d] := W[d, i, c] · X[o + 2 * i - 4, c]` (declared `axis o : ℕ = 11` AND with `o` inferred): output extent = input extent 11 | == numpy zero-pad loops to 5.6e-17; gradient == central differences (2.6e-10); `X` rows >= 5 get EXACTLY zero gradient from a loss on outputs 0 to 4 |
  | causal, stride 2 | `X[2 * o + i - 2, c]`, `axis o : ℕ = 6` | == numpy, 2.2e-16 |
  | kernel flip (true convolution) | `X[o - i + 2, c]` (NEGATIVE coefficient on the kernel axis) | prepares, == numpy, 2.2e-16 |
  | ViT-like | `Pe[q, m] := Wp[m, i, c] · Img[4 * q + i, c]`, `H[q, m, 0] := Pe[q, m]`, then the standard `scanProg` statements (q = s = 5, `Img[20, 2]`) | ONE scan record, plan counts (20 assign, 1 pointwise, 1 axiswise) over base+step+plain steps, exports exactly `Pe`, `H`; `H` == `np_transformer` run on the numpy `Pe` to 8.9e-16 (Lean, eager, jit); gradients of `H` over all 13 inputs finite, layer-2 slices exactly 0, directional derivatives == central differences (9.6e-11) |
  | binary32 | the stride-2 convolution with only `axis o : ℕ = 5` declared (and with `tensor Y(o, d)` declared) | prepares as binary32, Dense32 ok, `Y` shape `[5, 4]` |
  | gradients | stride-2 (all inputs), conv-relu-conv (all inputs), same-padding | finite, == central differences to 4e-11 / 1.2e-10 / 1.1e-10 |

  **Traps found (each is a pre-flight fact the fixtures must respect):**
  1. **The shared `checkAndRender` rejects every convolution.** It requires `generateNamed .einsumOnly` to refuse with `unsupportedStep`, `unsupportedStorageKind` or `unaryFactor`. A strided or dilated read is refused with `nonProjectionRow nodeIndex termIndex factorIndex rowIndex row`,
     and a biased one (any negative bias, `o + 2 * i - 4`) with `nonzeroAffineBias ... bias`; both are refusals, but of two kinds the match does not list, so every probe failed with "einsumOnly did not refuse". Fix: add those two arms (`.error (.nonProjectionRow ..)`, `.error (.nonzeroAffineBias ..)`) to the einsumOnly match, nothing else. The evidence door
     (`lowerCheckPlanToCandidate`) ACCEPTS a purely linear convolution (so the unchanged `| _ => throw "the evidence door did not refuse"` arm fails for it) and refuses with `unsupportedStep` as soon as the plan holds a pointwise or axiswise step. DECISION taken in this brief: every fixture ends in (or contains) a
     relu or softmax, so the evidence door still refuses and ONLY the einsumOnly arms change. The linear convolutions are still pinned individually because each fixture exports its linear intermediates (`Y1`, `Y2`, ...).
  2. **Reads past the HIGH end are refused, reads past the LOW end are zero.** With a declared output extent, a window that runs past the end of an input (`axis o : ℕ = 11` with `X[o + i, c]`, X extent 11) is refused at prepare: `shape: affine size system inconsistent (reduced witness: 0 = -2)`; with an INFERRED extent the
     output shrinks to fit (`Y[u, d] := W[d, i, c] · X[u + i - 1, c]` has extent 10, not 11). A negative index (`o + i - 1` at `o = 0`) is read as ZERO in Lean, eager and jit (no wrap-around: a wrapping model would differ by 0.32 in the probe). So zero padding exists only on the low side; the causal form
     (`X[o + 2 * i - 4, c]`, extent preserved) is the natural use of it and "same" (two-sided) padding is not expressible by a read.
  3. **Explicit padding by an affine write is a hazard, do not use it.** `Xp[u + 1, c] := X[u, c]` parses as a scan lookback (`scanAxisNotIter "u"`); `Xp[1 * u + 1, c] := X[u, c]` is a top-level scatter and works, but the materialised `Xp` has the WRITTEN extent (12 rows), not the declared `axis w : ℕ = 13`; the
     following convolution is still correct (Lean, eager, jit, gradient) only because the missing row is an out-of-range read of an intermediate (zero). A declared-versus-materialised extent mismatch is a separate defect candidate; record it in section 18-style notes if you meet it again, do not build on it.
  4. **Every output extent that is not the extent of an input axis needs `axis o : ℕ = n`** (the solver does not infer it from the stride); the binary32 siblings need those declarations too (like `axis s` in the earlier siblings). A shared axis name between an input and the output (`u` in `X(u, c)` and `Y(u, d)`) names two different extents.
  5. The hoisting rule of record section 18 applies to `Pe`: it reads no scan state, so it is a plain statement BEFORE the scan with no layer axis, which is what a patch embedding wants. No NaN-sentinel gradient problem here (no external input reaches the scan through a stacked table), but the vit weights are the standard NaN-layer-2 stacks, so gradient pins keep the exact-zero layer-2 check.
- **NOT probed:** the global mean pool as a sum times a scalar input (`Gp[e] := Ip[] · A2[p, e]`, a reduction over the pooled axis), the linear head with bias and the softmax over classes in the same plan, the TCN residual block with a 1x1 convolution and a residual add, the positional-embedding add (`... + Pos[q, m]`) in the patch statement, a patch
  embedding whose window differs from `m` (the probe used 4 = m), binary32 values and headroom (only the shape and run were probed), overlapping patches. If any of these needs an emitter, runtime, grammar or checker change, STOP and report.

## 3. What to build

Step 0 (own commit): the two einsumOnly arms of `checkAndRender` (trap 1); verify by running the existing differential (44 / 36 unchanged) before adding anything. Then THREE models, each registered in both precisions (6 fixtures; expected differential 47 binary64 and 39 binary32). Choose extents so that EVERY axis a program names has
a distinct extent where the model allows it, so no axis-order bug can hide behind equal extents; confirm by typecheck and run, change them if a pair collides or conditioning forces it. Weights by `gqaGen` with distinct seeds, biases and gains by small hand-typed or generated arrays. ONE definition per weight, shared by the 64 and 32 environments.

1. `conv1d_cnn` / `conv1d_cnn32`. Candidate extents: L = 23 positions, C = 3 channels, K1 = 2, D = 5, `o` = 22 (valid), K2 = 4, E = 6, `p` = 8 (stride 2, dilation 2: the last window starts at `2 * 7 = 14` and reads 14, 16, 18, 20 < 22), N = 7 classes.
   ```
   Y1[o, d]  := W1[d, i, c] · X[o + i, c] + B1[d]        A1[o, d]  := relu(Y1[o, d])
   Y2[p, e]  := W2[e, j, d] · A1[2 * p + 2 * j, d] + B2[e]   A2[p, e]  := relu(Y2[p, e])
   Gp[e]     := Ip[] · A2[p, e]                           Zc[n]     := Wc[n, e] · Gp[e] + Bc[n]
   Pr[n.]    := softmax(Zc[n])
   ```
   (`axis o : ℕ = 22`, `axis p : ℕ = 8`; `Ip` = 1 / 8 as a rank-0 input, derived from the shapes in the pin.) Exports every top-level tensor (`Y1`, `A1`, `Y2`, `A2`, `Gp`, `Zc`, `Pr`).
2. `conv1d_causal` / `conv1d_causal32`. A TCN residual block: `Y1[o, d] := W1[d, i, c] · X[o + 2 * i - 4, c] + B1[d]` (dilation 2, K = 3, causal), `A1 := relu(Y1)`, `Y2[o, e] := W2[e, j, d] · A1[o + 4 * j - 8, d] + B2[e]` (dilation 4), `A2 := relu(Y2)`,
   skip `Rs[o, e] := Wr[e, c] · X[o, c]`, output `Out[o, e] := A2[o, e] + Rs[o, e]`. Candidate extents: L = 17, C = 3, K = 3, D = 5, E = 6 (output extent L; every `axis o` declaration equals L). Pin the receptive field of output `o`: `X[o - 12 .. o]`.
3. `vit_patch` / `vit_patch32`. `Pe[q, m] := Wp[m, i, c] · Img[6 * q + i, c] + Pos[q, m]` (patch width 6, stride 6, C = 3 channels, q = 5 patches so `Img[30, 3]`, m = 4), `H[q, m, 0] := Pe[q, m]`, then the standard `scanProg` statements and mask `s <= q`; every other input is the mask fixtures'
   (`maskEnv`), `Img`, `Wp`, `Pos` generated. Plan: ONE scan record with 2 steps; exports exactly `Pe`, `H`. `Pos` must be non-trivial (gap pin below).
4. (Optional stretch, only if budget allows; otherwise park with a one-line cost) `conv2d_patch` / `conv2d_patch32`: the probed 2-D patch embedding `Pq[py, px, m] := Wq[m, iy, ix, c] · Img[2 * py + iy, 2 * px + ix, c]` followed by a relu, as a pure convolution fixture.

## 4. Pins (all independent of Lean's values) and mutants

Python, in the driver, ONE helper per model called once per precision (`conv_cnn_pins`, `conv_causal_pins`, `vit_patch_pins`), plus a shared numpy `np_conv(X, W, n_out, stride=1, dilation=1, bias=0)` written from the ENGLISH definition with explicit loops over output position, kernel tap and channel and a zero for an index outside `[0, L)` (do NOT use `np.convolve`,
`sliding_window_view` or `lax.conv`: the reference must not share an implementation with the plan). New numpy models `np_cnn`, `np_tcn`, `np_vit` built on it; `np_vit` feeds the numpy patch embedding to the existing `np_transformer` unchanged (do not edit `np_transformer`).
1. Value pins: every exported tensor of each fixture (the linear intermediates `Y1`, `Y2` included) equals the numpy model on the Lean, eager and jit views at `MODEL_TOL`; report observed maxima per precision.
2. Non-vacuity (numpy gaps, each > 1e-2 unless stated): CNN: dilation 1 instead of 2 on the second layer, the kernel flipped, no bias, no relu (and relu must clamp some entries and pass others: `A1` has both zero and positive entries), a stride-1 second layer (compare on the common prefix); TCN: circular (wrap-around) padding instead of zero padding, a
   non-causal (centred) window, the skip path dropped; ViT: no positional embedding, overlapping patches (stride 3 instead of 6), the patch embedding of a permuted window. The 1x1 skip and the bias must not be ignorable: perturbing each of them moves the output by more than 1e-3.
3. Structural, value-independent: CNN: `Y1`, `Y2` shapes `[22, 5]`, `[8, 6]` from the inputs, class probabilities positive and each row summing to 1; TCN: CAUSALITY on the eager runtime (perturb `X[t]`: outputs `o < t` bitwise unchanged for every `t`, outputs `t <= o <= t + 12` move, outputs beyond `t + 12` bitwise unchanged), the first output row equals the numpy zero-padded value
   (a wrapping runtime fails it); ViT: patch locality (perturb `Img[u]`: only patch `u // 6` of `Pe` changes, every other row of `Pe` bitwise unchanged), exactly `Pe` and `H` exported, ONE scan record with 2 steps and the plan's pre-scan statement before it.
4. Inputs: every input other than the new weights is bitwise the mask fixtures' (ViT) or generated by the stated formula; scalars (`Ip`, `Sc`) derived from the input shapes; the ViT weight stacks keep NaN layer-2 slices and `H` is finite.
5. Distinct extents: assert from the input shapes the extents you chose are pairwise distinct (list them in the pin's print).
6. Keep the existing pins untouched and green.

Gradients (Part B, after Part A is green; cut it first if the budget forces a cut): `jax.grad` of `L = sum(C * out)` over every float input for the CNN (`Pr`'s logits `Zc`, not the softmax, to keep the loss non-degenerate), the TCN (`Out`) and the ViT (`H[:, :, 2]`), eager and jit, against (a) a pure-JAX model written from the definition WITHOUT the plan (an explicit
gather by index arrays, or `jax.lax.conv_general_dilated` for the strided and dilated layers: any implementation that is not the plan) and (b) central differences of the numpy model; layer-2 ViT weight slices exactly zero; TCN: a loss on outputs `0 .. t` has EXACTLY zero gradient on `X` rows `> t` (the probe confirmed it) and a real one inside; ViT: `Img` and `Wp` gradients finite
and non-trivial. A separate `*_grad_pins` function is fine (the cross fixtures did the same). Report headroom.

Hand mutants (edit the f64 program text, run `run-evalplan-nonlin.sh`, name the first failing assertion, restore by the INVERSE `sed` edit AFTER committing the work: the lean4 guardrail hook blocks `git checkout --`; `git diff --stat` must be empty; BSD `sed -i '' -e ...` needs the empty suffix; no `$VAR` and no compound commands). Each must keep EVERY input used AND be accepted by the
shape solver (a refused mutant is not a kill, report it as a refusal). Suggested: A. CNN second layer loses its dilation (`A1[2 * p + j, d]`); B. CNN first layer reads the flipped kernel (`X[o - i + 1, c]`, same extents); C. CNN bias applied twice (`+ B1[d] + B1[d]`); D. CNN pool divides by the wrong constant (data: `Ip` = 1 / 7); E. TCN bias `- 4` becomes `- 2` (a shifted receptive field);
F. TCN dilation 2 becomes 1 in the first layer (`X[o + i - 2, c]`); G. TCN skip path dropped from the residual (`Out := A2[o, e] + A2[o, e]`; `Rs` stays used only if exported); H. ViT patch stride 6 becomes 5 (`Img[5 * q + i, c]`: overlapping patches, extent 25 <= 30); I. data: `Pos` all zeros (value pins pass, the non-vacuity gap pin must be the one that fires); J. one mutant on a binary32 sibling
(the f64 leg runs green first). If a mutant SURVIVES, stop and report it with the exact edit. Compute the non-vacuity gaps BEFORE the view loop so a data mutant fails on item 2 and not on the value pin. Record the table in the body of an empty commit.

## 5. Process, harness facts, budgets

- Worktree (Rule 13): `EnterWorktree`, then `bash .claude/skills/new-slice/prepare-worktree.sh` (it fast-forwards the branch to local main). The primary checkout has NO `leanncd/experiments/jax_bridge/.cache`; in the worktree run `mkdir -p <wt>/leanncd/experiments/jax_bridge/.cache` and
  `ln -s /Users/williammacready/code/python/pyncd.worktrees/task4-boolean-output/leanncd/experiments/jax_bridge/.cache/python <wt>/leanncd/experiments/jax_bridge/.cache/python` (verify it exists; never commit the link; probe scripts outside the worktree run with that venv's `bin/python`). STALE-OLEAN TRAP: run
  `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd JaxExperiment` once before any scratch probe.
- Plain, separate shell commands only (no `cd x && y`, no `$VAR`, no `;`/`$?` chains); absolute paths; `/usr/bin/git -C <wt>` (a worktree-isolated session refuses `git -C` into the primary checkout). Stage by explicit path; never `git add -A`. `ExitWorktree` (keep) before merging from the primary.
- To run a scratch Lean file: `head -n 181` of `EvalPlanNonlinSmoke.lean` gives the harness helpers (everything up to `env32`); splice in the defs you need from further down (`scanStack`, `scanWeights`, `maskX`, `maskEnv64`, ...), add your programs and a `main` outside the namespace (`open JaxBridge.NonlinSmoke in def main ...`), then
  `/Users/williammacready/.elan/bin/lake +leanprover/lean4:v4.30.0 -d <wt>/leanncd env lean --run <file> <out>`; WITHOUT the toolchain pin elan fails with "incompatible header". A probe wrapper that calls `fixture64` inherits trap 1; to see the refusal reasons call `generateNamed .einsumOnly`, `lowerCheckPlanToCandidate`, `renderAffinePlanNamed` and `runPreparedDense` yourself and print `repr` of the errors.
  `lean-file.sh <wt>/leanncd experiments/jax_bridge/EvalPlanNonlinSmoke.lean` typechecks the fixture file (`JaxExperiment` does NOT compile it).
- Measure the binary32 error against numpy BEFORE fixing the generator seeds (a scratch script on the generated 32 fixtures with Python-side regenerated weights; no Lean rebuild per candidate), report every candidate tried, never loosen a tolerance. The cross slice's untuned seeds gave 1.6x to 2.4x headroom; convolution sums are short, so expect better, but do not assume it.
- Harness traps: `Array.extract start stop` takes the END index; a tensor name `C` collides with a `C(` token (use two letters); `Vec` is avoided; the einsumOnly arms (trap 1); every program mutant needs the whole `run-evalplan-nonlin.sh` (it regenerates the Lean fixtures first), every gradient-pin tweak is a python-only run on the cached generated fixtures
  (`python evalplan_nonlin_smoke.py float64 <gen64>`); `rg` output through the rtk hook is truncated, read with `Read`.
- NEVER write wait loops, `pgrep` monitors, `time.sleep` polling or driver scripts: run builds and the differential with `run_in_background` and wait for the notification. The differential aborts at the FIRST failed assertion and takes a few minutes; batch edits and run it as few times as possible. Never run two Lean builds or runs at once.
- Do not edit `EvalPlanCodegen.lean`, `ScanAffineEmitTest.lean`, `ExecutableTest.lean`, `ScanJaxGateTest.lean`, the mutation manifest JSON files, `evalplan_affine_runtime.py` (except as a scratch gradient mutant, restored) or `LeanNCD/*`; do not touch the existing fixtures, programs, environments, `np_transformer` or assertion texts (the einsumOnly arms of step 0 ADD cases, they change no text).
- Budgets (Rule 6): a dispatch is at most about 60 harness-counted tool calls and about 250k context; report the HARNESS count if you delegate. The cross slice was inline, about 150 calls with seven mutation runs; this one has three models, three numpy models and nine mutants, so split if you delegate: A = step 0, Lean programs, envs, registrations, typecheck and one runner run; B = Python pins for the three models;
  C = mutants, docs, verification; D = Part B gradients. If the budget forces a cut, ship `conv1d_cnn` and `vit_patch` with pins 1 to 5 and park the TCN, Part B and the stretch, saying so.

## 6. Verification before merging (you run it, not a subagent)

`bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd Tests JaxExperiment` (expect 8846 jobs, 0 errors; no new Lean module) and `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh` ONCE on the final tree (expect 47 binary64 and 39 binary32 fixtures if all three models are added in both precisions, plus the stretch's 1 and 1; 44 and 36 plus the number you added otherwise). One
read-only whole-branch review by code reading of the diff: look for pins that a trivial or perturbed entry satisfies by itself (a numpy model that shares an indexing bug with the program, a non-vacuity test that is invariant under the change it claims to detect, a gradient pin whose reference reuses the plan's own gather, a causality pin that holds for a non-causal model of the same extent). Re-check `main` before merging (merge main into the
branch if it moved; check incoming Lean files with `rg -l "CompileError|finalizeScans|prepareEvalPlan|evalScheduled"`). Merge to LOCAL main, delete the branch, remove the worktree. Do NOT push unless asked (the lean4 guardrail hook blocks `git push`; after an explicit request use the one-time prefix `LEAN4_GUARDRAILS_BYPASS=1`).

## 7. Records

Add section 19 to `papers/semantics/jax_scan_record.md` (the programs, the probe findings and which became pins, the traps and their pinned or avoided form, the extents and why, the weight-generator candidates with their binary32 errors, observed numpy-pin differences and binary32 headroom, the harness change, the mutation table, anything parked) and one paragraph in the bridge README next to the cross-attention paragraph;
fix the README fixture count ("44 binary64 and 36 binary32" -> the new counts) and value-grep the README and the record for stale statements ("every fixture ... plain axes", "the only affine reads", "einsumOnly refuses with"). Update the memory index entry if you keep one.

## 8. Done when

The three models pinned on Lean, eager and jit with observed values, including the causality and patch-locality pins; every mutant killed by a NAMED assertion (or a refusal or survivor reported); `Tests` + `JaxExperiment` green; differential green with the stated counts; record and README updated; review clean or adjudicated; merged to local main; worktree and branch removed. Report faithfully: observed
values, the mutation table, tool-call counts, anything unverified or skipped.

## 9. After this slice

The progression agreed 2026-11-09 continues (each step adds one structural idea; every one needs its own pre-flight probe): a GRU or LSTM over a time axis (scan over time, several states, gates); linear attention or a diagonal state-space model (matrix state; note a causal convolution is a one-state-free SSM kernel); a GNN (dense, then scatter-add over edges at the top level, which is admitted); dense mixture of experts; the logic side
(Viterbi max-plus, Boolean reachability; Lean-side only today); layers x time (nested scans, a KV cache; the scan-local multi-axis write refusal of record section 17, `multiAxisScatterLhs`, is the first thing to revisit there). Parked from this thread: a convolution inside a scan step (affine reads of the state), max pooling (needs a max reduction on JAX), two-sided padding (the declared-versus-materialised extent mismatch of trap 3 first),
depth (item 6a, mostly a float32 measurement), `/` in index expressions as an elaboration-time desugaring, per-layer mask alternation (probably a runtime change: ask first), gradients through `transformer_head`, scatter nodes and `scatter_mode="fast"`, promoting the runtime gradient mutants to the Python manifest.

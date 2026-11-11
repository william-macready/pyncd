# Session brief: recurrent networks over a time axis (GRU, LSTM, bidirectional) on the JAX bridge

Status: not started. Written 2026-11-11 at local `main` `f3d758fe` (= `origin/main`; the conv slice and the other session's semantics work are pushed). Process weight: Direct path (`.claude/skills/slice-plan/` section 0): tests and fixtures only, NO harness
change expected (the shared `checkAndRender` already accepts a scan fixture; see section 2), no production change. A scratch probe on 2026-11-11 answers the "is it expressible" question for every form this brief uses (section 2) and found
the traps listed there. If any NEW pre-flight answer needs an emitter, runtime, grammar or checker change, STOP and report (do not edit `EvalPlanCodegen.lean`, `evalplan_affine_runtime.py`, `LeanNCD/DSL/*` or `LeanNCD/Eval/Plan/*`; that is a
different process weight and the user's call). CLAUDE.md applies, in particular Rule 13 (worktree, merge to LOCAL main, do not push unless asked), Rule 14 (scope gate) and Rule 6 (budgets: the conv slice was done inline and overran, see section 5). Siblings:
`jax_conv_session_brief.md` (landed; record section 19 of `papers/semantics/jax_scan_record.md`), `jax_cross_attention_session_brief.md` (section 18), `jax_gqa_session_brief.md`, `jax_multiquery_session_brief.md`,
`jax_predicate_masks_session_brief.md`: same harness, same pin style, same hand-mutant discipline.

## 1. Goal

Every scan fixture so far scans over the LAYER axis of a transformer: one state `H(q, m, l)`, weights stacked over the scan axis and read as `W[l, ...]`. A recurrent network scans over TIME: the scan axis indexes the INPUT SEQUENCE (`X[t, i]`), the weights are shared
across steps, the state is a vector, and the recurrence is a gated nonlinear cell. Three models, each adding one structural idea:

1. `rnn_gru`: a GRU over six steps with a sequence-to-one head. New: a per-step INPUT read at the scan axis (`X[t, i]`), the state read through a RENAMED axis (`U[d, e] · H[e, t]`, contraction against a matrix), sigmoid and tanh gates inside a scan, elementwise
   products of per-step intermediates, a PINNED read of the final state after the scan (`H[d, 6]`) feeding a softmax, gradients through time (BPTT).
2. `rnn_lstm`: an LSTM with TWO states (`H`, `Cc`) and a readout at EVERY time step after the scan (`Yt[t, v]`). New: several states in one scan, the new cell state routed through a per-step intermediate read by both updates, a post-scan consumer that
   keeps the time axis.
3. `rnn_bi`: a bidirectional tanh-RNN: a forward layer reading `X[t, i]` and a backward layer reading `X[5 - t, i]` (a REVERSED read of the scan axis) in ONE scan, their final states combined in a softmax head. New: a decreasing affine read of the scan axis.

Optional stretch (cheap, both probed; park with a one-line cost if the budget forces a cut): `rnn_stack`, a two-layer Elman RNN in one scan (layer 2 reads layer 1's NEW state through an intermediate), and `rnn_gru_long`, the GRU at 16 steps (data and `iter` extent
only: binary32 error accumulates with the step count, so it is a headroom measurement).

Not in scope (park with a one-line cost if you find more): variable-length sequences and padding masks, batch axes, teacher forcing, peephole LSTM variants, attention inside an RNN, truncated BPTT, a convolution inside a scan step (still parked from the conv slice), nested
scans (time x layers; record section 17's `multiAxisScatterLhs` refusal is the first thing to revisit there), changing any existing fixture, the Python runtime, the emitter, the grammar (see traps 1 and 2: do NOT add `-` to the term grammar or a `t +1` read; that is a
different process weight), the mutation manifests.

## 2. What exists (verify each before relying on it) and the probe findings

- Harness: `leanncd/experiments/jax_bridge/EvalPlanNonlinSmoke.lean` (`fixture64` / `fixture32`, `checkAndRender`, helpers `t64`, `t32`, `env64`, `env32`, `gqaGen seed n` = `0.6 * sin (seed + 1.7 i)`, `convBias seed n`, `scanNanSlice`; scan fixtures register as
  `fixture64 "<name>" prog env minPw minAw (some (a, pw, aw)) true (scans := 1)`, the `32` sibling as `fixture32 ...` with the same trailing arguments). Driver `evalplan_nonlin_smoke.py`: `np_gelu`, `np_softmax_last`, `check_np`, `print_np_stats`, `MODEL_TOL`, `GRAD_TOL`,
  `GRAD_FD_TOL`, `TRANSFORMER_FIXTURES` (a name set: tolerance gate and per-output records, no "relu is bit-exact"), `EAGER` (stores the eager and jit outputs of scan fixtures and `conv1d_*` names: extend the prefix test for yours), `conv_views`, `print_conv_stats`,
  `dict_gap`, `np_conv` (pin style to copy: `conv_cnn_pins`, `conv_causal_pins`, `vit_patch_pins`, `conv_grad_pins`). Do NOT edit `np_transformer`.
- Baseline gates on current main: `lake-build.sh <wt>/leanncd Tests JaxExperiment` = 8846 jobs, 0 errors (re-verify); `run-evalplan-nonlin.sh` = 47 binary64 and 39 binary32 fixtures within tolerance. Expected differential if the three models are added in both precisions: 50 and 42
  (the stretch adds 2 and 2). binary32 headroom has been 2.4x to 13.6x; REPORT the headroom of every new binary32 fixture; do not loosen any tolerance.
- **Probe findings (scratch, 2026-11-11, `head -n 182` of the fixture file plus probe programs; the programs are in Appendix A).** Binary64 unless stated; extents `t` = 7 (history of six steps), `i` = 3, `d` = 4, `v` = 5; every `X` has a NaN seventh row.

  | Form | Result |
  |---|---|
  | linear RNN `A[d] := W[d, i] · X[t, i] + U[d, e] · H[e, t]`, `H[d, t +1] := A[d]` | prepares, ONE scan record (step_count 6), plan = just the scan (3 assign); Lean, eager, jit == numpy loops to 1.7e-16 |
  | GRU (reset and update gate, tanh candidate, `Neg[]` for the minus) | 11 assign + 3 pointwise; == numpy to 2.2e-16 on Lean, eager and jit; export `H` only (per-step intermediates are not exported) |
  | GRU + a readout at every step `Yt[t, v] := Wy[v, d] · H[d, t]` | plan `[scan, assign]`, exports `H`, `Yt`; `Yt` has shape `[7, 5]` and INCLUDES t = 0; == numpy to 1.7e-16 |
  | GRU + sequence-to-one head `Lg[v] := Wy[v, d] · H[d, 6]`, `Pr[v.] := softmax(Lg[v])` | plan `[scan, assign, assign, axiswise]` (13 assign, 3 pointwise, 1 axiswise); exports `H`, `Lg`, `Pr`; == numpy to 2.2e-16 |
  | LSTM, two states, new cell state through the intermediate `Cn` | 16 assign + 5 pointwise; exports `H`, `Cc`; == numpy to 1.1e-16 on all views |
  | stacked two-layer Elman RNN in one scan (`N1` read by layer 2) | 8 assign + 2 pointwise; exports `H1`, `H2`; == numpy to 2.8e-16 |
  | reversed read `W[d, i] · X[5 - t, i]` | prepares, == numpy to 5.6e-17; X slot 6 (never read) has EXACTLY zero gradient |
  | 16-step GRU (`iter t = 17`) | step_count 16, == numpy to 2.2e-16 |
  | gradients (BPTT) of `sum(C * H[:, 6])` over every float input: linear RNN, GRU, LSTM, stacked, reversed | finite, eager == jit bitwise, X slot 6 exactly zero, directional derivatives == central differences of the numpy loops (1.5e-10, 8.1e-11, 4.8e-11, 1.1e-10, 1.6e-10) |
  | binary32: GRU and LSTM, with `iter t = 7` and the state declarations `tensor H(d, t)` / `Cc(d, t)`, AND with NO declaration at all | all four prepare as binary32, Dense32 ok; max abs vs float64 numpy 1.2e-7 (GRU), 7.0e-8 (LSTM); the axis order comes from the left-hand side |

  **Traps found (each is a pre-flight fact the fixtures must respect):**
  1. **There is NO subtraction in a term** (`Nn[d] - Zn[d]` is a parse error: `unexpected token '-'; expected '}'`). `1 - z` is written through a scalar input `Neg[] = -1`: `Zn[d] := Neg[] · Z[d] · Nn[d]`, `H[d, t +1] := Nn[d] + Zn[d] + Z[d] · H[d, t]`. The numpy
     reference hard-codes the minus, so (a) pin `Neg == -1` from the exported inputs (like `Ip = 1 / p` in the conv slice) and (b) FREEZE `Neg` in the finite-difference directions (its gradient is pinned against the pure-JAX model only); without it a 0.42 scaled error appeared in the probe.
  2. **There is NO state read at `t +1` on the RIGHT-hand side** (`Tc[d] := tanh(Cc[d, t +1])` is a parse error: `unexpected token '+1'; expected ']'`). A cell that needs the NEW state computes it as an intermediate (`Cn[d] := Fc[d] + Ic[d]`) and both `Cc[d, t +1] := Cn[d]` and
     `Tc[d] := tanh(Cn[d])` read the intermediate. Writes at `t +1` on the left are fine.
  3. **A stacked input must have the extent of the iteration axis.** `X(t, i)` with six rows under `iter t = 7` is refused: `shape: axis size conflict for uid 1: 7 vs 6`. Keep the NaN-sentinel spare slot of the weight stacks: seven rows, row 6 NaN, never read; a step that read it would make every state NaN.
  4. **Pointwise functions take ONE product, not a sum.** Gates are two statements: a pre-activation `Az[d] := W · X[t, i] + U · H[e, t] + Bz[d]` (sums of terms are fine, each with its own reduced axis) and `Z[d] := sigmoid(Az[d])`.
  5. **The conv slice's solver finding applies to affine reads** (record section 19, finding 2): an affine window may be an EXACT size equation, so a mutant that changes an index can be REFUSED at prepare instead of killed (report it as a refusal and replace it; the reversed read `X[5 - t, i]` and the pinned final read `H[d, 6]`
     use 5 = steps - 1 and 6 = history extent - 1, so a mutant that moves either constant may be refused; whether they are exact equations was NOT probed).
  6. The einsum door refuses every probed program with `unsupportedStep`, like the other scan fixtures; no `checkAndRender` arm is needed (the register call passes `unaryOk := true` and `scans := 1`, as the transformer scan fixtures do).
- **NOT probed:** the LSTM together with the per-step readout `Yt` in ONE program (the readout was probed on the GRU only); the bidirectional program with the two-term head `Lg[v] := Wo[v, d] · Hf[d, 6] + Wp[v, d] · Hb[d, 6]` (two pinned reads in one statement) and the two states in one scan
  (probed separately: two states in the LSTM, the reversed read alone); gradients through the readout `Yt` or the head; binary32 headroom of any recurrent model; values of the binary32 stacked and long variants. If a combination is refused, use the fallback of section 3 and say so; if a
  fallback is also refused, STOP and report.

## 3. What to build

Step 0 (no commit): in the worktree run the two combinations of the "NOT probed" list (the LSTM with `Yt`, the bidirectional program with its two-term head) once through a scratch probe BEFORE writing any pin, and fix the exact kind counts `(assign, pointwise, axiswise)` of all three programs from the Lean `exact` message
(the probe counts above are over the programs without the new post-scan statements; put a wrong guess in `exact` and read the real counts from the error). Then THREE models, each registered in both precisions (6 fixtures; expected differential 50 binary64 and 42 binary32). Extents: `t` = 7 (six steps), `i` = 3, `d` = 4, `v` = 5 pairwise distinct (the contraction aliases `e`, `f` of `d` are not
new extents); confirm by typecheck and run. Weights by `gqaGen` with distinct seeds, biases by `convBias`, ONE definition per weight shared by the 64 and 32 environments; `X` = `gqaGen s 18 ++ scanNanSlice 3` as a `[7, 3]` tensor; initial states `gqaGen`; `Neg` = `[-1.0]` as a rank-0 input.

1. `rnn_gru` / `rnn_gru32`: the GRU of Appendix A with the head `Lg[v] := Wy[v, d] · H[d, 6]`, `Pr[v.] := softmax(Lg[v])`; exports `H`, `Lg`, `Pr`. Reference (English): `z = sigmoid(Wz x + Uz h + bz)`, `r = sigmoid(Wr x + Ur h + br)`, `n = tanh(Wn x + r * (Un h) + bn)`, `h' = (1 - z) * n + z * h`.
2. `rnn_lstm` / `rnn_lstm32`: the LSTM of Appendix A plus `Yt[t, v] := Wy[v, d] · H[d, t]`; exports `H`, `Cc`, `Yt`. Reference: `i, f, o = sigmoid(...)`, `g = tanh(...)`, `c' = f * c + i * g`, `h' = o * tanh(c')`. Fallback if `Yt` is refused next to two states: drop `Yt` from this fixture and keep it on the GRU (the probe-verified pairing), saying so.
3. `rnn_bi` / `rnn_bi32`: the bidirectional program of Appendix A; exports `Hf`, `Hb`, `Lg`, `Pr`. Reference: forward `hf' = tanh(Wf x_t + Uf hf)` over `x_0 .. x_5`, backward `hb' = tanh(Wb x_{5 - t} + Ub hb)`, `Lg = Wo hf_6 + Wp hb_6`. Fallback if the two-term head is refused: two statements `Lf[v]`, `Lb[v]` and `Lg[v] := Lf[v] + Lb[v]`.
4. (Optional stretch) `rnn_stack` / `rnn_stack32` and `rnn_gru_long` / `rnn_gru_long32` (Appendix A, probed).

## 4. Pins (all independent of Lean's values) and mutants

Python, in the driver, ONE helper per model called once per precision (`rnn_gru_pins`, `rnn_lstm_pins`, `rnn_bi_pins`), written like `conv_cnn_pins`; numpy models `np_gru`, `np_lstm`, `np_birnn` written from the ENGLISH definitions above with explicit loops over time steps (do NOT use `lax.scan`, `np.einsum` over time or any
shared implementation: the pure-JAX model of the gradient pins is the only place a scan appears, and it is not the plan). Every model reads the exported INPUTS only.
1. Value pins: every export on the Lean, eager and jit views at `MODEL_TOL`: states over all seven history slots (slot 0 = the initial state), `Lg`, `Pr`, `Yt`; report observed maxima per precision.
2. Non-vacuity (numpy gaps, each > 1e-2 unless stated): GRU: update gate removed (`h' = n`), reset gate removed, `1 - z` and `z` swapped, no recurrence (`U = 0`), head reads step 5 instead of 6; LSTM: forget gate ignored, output gate ignored, `h' = o * tanh(c)` with the OLD cell, no cell state (`c' = i * g`), readout reads the wrong step;
   bidirectional: forward only, backward only, the backward layer NOT reversed (`X[t]`), the layers' final states swapped, no backward recurrence (`Ub = 0`). Every gate must be non-trivial: gate values are neither all near 0 nor all near 1 (assert the min and max of `z`, `f`, `i`, `o` over the steps are inside `(0.05, 0.95)` for the chosen data; re-pick a seed otherwise, report every candidate).
3. Structural, value-independent: shapes from the inputs (`H` `[4, 7]`, `Yt` `[7, 5]`, `Pr` `[5]` summing to 1, positive); `Neg == -1` and the one-hot structure of the spare slot (`X[6]` NaN, rows 0..5 finite); plan shape (ONE scan record with step_count 6, the post-scan nodes after it, exactly the stated exports);
   TIME CAUSALITY on the eager runtime (perturb `X[t]`, `t` in 0..5): for the forward state `H[:, s]` is bitwise unchanged for `s <= t` and moves at `s = t + 1`; for the BACKWARD state of `rnn_bi` (it has read `X[5], ..., X[6 - s]` after `s` steps) `Hb[:, s]` is bitwise unchanged for `s <= 5 - t` and moves at `s = 6 - t`;
   the NEVER-READ slot: set `X[6]` to 0.5 (instead of NaN) and EVERY export is bitwise unchanged; the first state row equals the initial state input.
4. Inputs: scalars (`Neg`) from the definition; every weight generated by the stated formula; extents pairwise distinct, listed in the pin's print.
5. Keep the existing pins untouched and green.

Gradients (Part B, after Part A is green; cut it first if the budget forces a cut): `jax.grad` of `L = sum(C * out)` over every float input, eager and jit, with `out` = `Lg` for the GRU and the bidirectional model (the logits, not the softmax) and `H[:, 6]` + `Yt` for the LSTM, against (a) a pure-JAX model written from the definition with
`jax.lax.scan` or an explicit Python loop (any implementation that is not the plan) and (b) central differences of the numpy models (freeze `Neg`); X slot 6 (never read) has EXACTLY zero gradient; the gradient wrt the initial states is nonzero (information flows back through all six steps); the gradient of `Wz` etc. is non-trivial. A separate `rnn_grad_pins` function is fine. Report headroom. The gradient
vacuity self-test must be an ABSOLUTE perturbation if the gradients are O(0.1) (conv slice lesson).

Hand mutants (edit the f64 program text, run `run-evalplan-nonlin.sh`, name the first failing assertion, restore by the INVERSE `sed` edit AFTER committing the work: the lean4 guardrail hook blocks `git checkout --`; `git diff --stat` must be empty; BSD `sed -i '' -e '<line>s/.../.../'` with an ADDRESS so the binary32 sibling is not edited; no `$VAR` and no compound
commands). Each must keep EVERY input used AND be accepted by the shape solver (a refused mutant is not a kill: report it, replace it). Suggested (every one keeps all inputs used): A. GRU reset gate composed by a sum instead of a product (`Rh[d] := R[d] · Uh[d]` becomes `Rh[d] := R[d] + Uh[d]`); B. GRU carries the wrong gate (`H[d, t +1] := Nn[d] + Zn[d] + Z[d] · H[d, t]` becomes `... + R[d] · H[d, t]`); C. data: `Neg` = +1 (the `Neg == -1` input assertion fires before the
value pins); D. GRU head reads the wrong step (`Lg[v] := Wy[v, d] · H[d, 5]`); E. LSTM forget gate reads the input gate (`Fc[d] := Ig[d] · Cc[d, t]`); F. LSTM hidden update uses the OLD cell (`Tc[d] := tanh(Cc[d, t])`, `Cn` stays used by the cell update); G. bidirectional backward layer not reversed (`X[5 - t, i]` becomes `X[t, i]`); H. LSTM readout reads a fixed step
(`Yt[t, v] := Wy[v, d] · H[d, 3]`; expect the solver to accept it, else replace); I. data: the backward recurrence matrix `Ub` all zeros (value pins pass, the "no backward recurrence" non-vacuity gap must be the one that fires); J. one mutant on a binary32 sibling (the f64 leg runs green first). If a mutant SURVIVES, stop and report it with the exact edit. Compute the non-vacuity gaps BEFORE the view loop so a data mutant fails on item 2 and not on the value pin. Record the table in the body of an empty commit.

## 5. Process, harness facts, budgets

- Worktree (Rule 13): `EnterWorktree`, then `bash .claude/skills/new-slice/prepare-worktree.sh` (it fast-forwards the branch to local main). The primary checkout has NO `leanncd/experiments/jax_bridge/.cache`; in the worktree run `mkdir -p <wt>/leanncd/experiments/jax_bridge/.cache` and
  `ln -s /Users/williammacready/code/python/pyncd.worktrees/task4-boolean-output/leanncd/experiments/jax_bridge/.cache/python <wt>/leanncd/experiments/jax_bridge/.cache/python` (verify it exists; it is git-ignored, never commit it; probe scripts outside the worktree run with that venv's `bin/python`). STALE-OLEAN TRAP: run
  `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd Tests JaxExperiment` once before any scratch probe (the scratch file imports `Eval.Plan.ScanCompileTest`, which is in the `Tests` target).
- Plain, separate shell commands only (no `cd x && y`, no `$VAR`, no `;`/`$?` chains, NO multi-line heredocs: a worktree-isolated session refuses commands it cannot verify; write files with the Write/Edit tools, edit by `Edit`); absolute paths; `/usr/bin/git -C <wt>` (a worktree-isolated session refuses `git -C` into the primary checkout, so do the merge after `ExitWorktree` keep and, from the primary,
  `git -C <primary> merge --no-ff <branch>`). A path containing `Eval` can trip the command checker (the same refusal hit `LeanNCD/Eval` once): pass such paths to git as separate literal commands. Stage by explicit path; never `git add -A`.
- To run a scratch Lean file: `head -n 182` of `EvalPlanNonlinSmoke.lean` gives the harness helpers (everything up to `env32`); append the probe programs of Appendix A and a `main` outside the namespace (`open JaxBridge.NonlinSmoke in def main ...`), then
  `/Users/williammacready/.elan/bin/lake +leanprover/lean4:v4.30.0 -d <wt>/leanncd env lean --run <file> <out>`; WITHOUT the toolchain pin elan fails with "incompatible header". A probe wrapper that calls `fixture64` or `fixture32` inherits `checkAndRender`; to see refusal reasons call `generateNamed .einsumOnly`, `lowerCheckPlanToCandidate`,
  `renderAffinePlanNamed` and `runPreparedDense` yourself and print `repr` of the errors. `lean-file.sh <wt>/leanncd experiments/jax_bridge/EvalPlanNonlinSmoke.lean` typechecks the fixture file (`JaxExperiment` does NOT compile it).
- Measure the binary32 error against numpy BEFORE fixing the generator seeds (a scratch script on the generated 32 fixtures with Python-side regenerated weights; no Lean rebuild per candidate), report every candidate tried, never loosen a tolerance. Short contractive recurrences should be well-conditioned, but the 16-step stretch is where error accumulates: measure it.
- Harness traps: `Array.extract start stop` takes the END index; a tensor name `C` collides with a `C(` token (use two letters, e.g. `Cc`, as the probe does); `Vec` is avoided; every program mutant needs the whole `run-evalplan-nonlin.sh` (it regenerates the Lean fixtures first; it aborts at the FIRST failed assertion and takes a few minutes), every gradient-pin tweak is a python-only run on the cached
  generated fixtures (`python evalplan_nonlin_smoke.py float64 <gen64>`, redirect the output to a file and read the tail); `rg` output through the rtk hook is truncated, read with `Read`; a numpy reference that does not read an input (here `Neg`) needs that input frozen in the finite-difference directions.
- NEVER write wait loops, `pgrep` monitors, `time.sleep` polling or driver scripts: run builds and the differential with `run_in_background` and wait for the notification. Never run two Lean builds or runs at once.
- Do not edit `EvalPlanCodegen.lean`, `ScanAffineEmitTest.lean`, `ExecutableTest.lean`, `ScanJaxGateTest.lean`, the mutation manifest JSON files, `evalplan_affine_runtime.py` (except as a scratch gradient mutant, restored) or `LeanNCD/*`; do not touch the existing fixtures, programs, environments, `np_transformer` or assertion texts.
- Budgets (Rule 6): a dispatch is at most about 60 harness-counted tool calls and about 250k context. The conv slice was done INLINE and overran (25.1M cumulative input tokens, context peak 303k, 115 turns; the twelve mutant runs and the pin iteration dominated), so split this one: A = Step 0 probe, Lean programs, envs, registrations, typecheck and one runner run; B = Python pins for the three
  models; C = mutants, docs, verification; D = Part B gradients; report the HARNESS count of each dispatch. If the budget forces a cut, ship `rnn_gru` with pins 1 to 5 and park the LSTM, the bidirectional model, Part B and the stretch, saying so.

## 6. Verification before merging (you run it, not a subagent)

`bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd Tests JaxExperiment` (expect 8846 jobs, 0 errors; no new Lean module) and `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh` ONCE on the final tree (expect 50 binary64 and 42 binary32 fixtures if all three models are added in both precisions, plus the stretch's 2 and 2; 47 and 39 plus the number you added otherwise). One read-only
whole-branch review by code reading of the diff: look for pins that a trivial or perturbed entry satisfies by itself (a numpy model that shares an indexing or time-order bug with the program, a non-vacuity test that is invariant under the change it claims to detect, a gradient pin whose reference reuses the plan's own scan, a time-causality pin that holds for a model that reads the whole sequence at every step, a spare-slot pin that holds because
the slot is read as zero). Re-check `main` before merging (merge main into the branch if it moved; check incoming Lean files with `git diff --stat -G"CompileError|finalizeScans|prepareEvalPlan|evalScheduled" <base> main -- '*.lean'`). Merge to LOCAL main, delete the branch, remove the worktree (`git worktree remove --force` only after looking at `git status --ignored`: the `.lake` cache, `.cache` and `__pycache__` are the expected ignored files). Do NOT push unless asked (the lean4
guardrail hook blocks `git push`; after an explicit request use the one-time prefix `LEAN4_GUARDRAILS_BYPASS=1`).

## 7. Records

Add section 20 to `papers/semantics/jax_scan_record.md` (the programs, the probe findings and which became pins, the traps and their pinned or avoided form, the extents and why, the weight-generator candidates with their binary32 errors, observed numpy-pin differences and binary32 headroom, the mutation table, deviations from this brief, tool-call and token counts, anything parked) and one paragraph in the bridge README next to the
convolution paragraph; fix the README fixture count ("47 binary64 and 39 binary32" -> the new counts) and value-grep the README and the record for stale statements ("one state", "scan axis is the layer axis", "weights stacked over the scan axis", "only the layer"). Update the memory index entry (`rnn-probe-findings`, `conv-brief`) if you keep one.

## 8. Done when

The three models pinned on Lean, eager and jit with observed values, including the time-causality and spare-slot pins; every mutant killed by a NAMED assertion (or a refusal or survivor reported); `Tests` + `JaxExperiment` green; differential green with the stated counts; record and README updated; review clean or adjudicated; merged to local main; worktree and branch removed. Report faithfully: observed values, the mutation table, tool-call and token counts,
anything unverified or skipped.

## 9. After this slice

The progression agreed 2026-11-09 continues (each step adds one structural idea; every one needs its own pre-flight probe): linear attention or a diagonal state-space model (matrix or elementwise state: a diagonal SSM is `H[d, t +1] := A[d] · H[d, t] + B[d, i] · X[t, i]`, the linear RNN of this probe with an elementwise recurrence, so its probe should be short; note a causal convolution is its
state-free kernel form); a GNN (dense, then scatter-add over edges at the top level, which is admitted); dense mixture of experts; the logic side (Viterbi max-plus, Boolean reachability; Lean-side only today); layers x time (nested scans, a KV cache; `multiAxisScatterLhs` of record section 17). Parked from this thread: variable-length sequences with masks, a convolution inside a scan step, max pooling, two-sided padding, the solver-equality probe of record
section 19 (which declared-axis forms are exact size equations), depth, `/` in index expressions as an elaboration-time desugaring, gradients through `transformer_head`, scatter nodes and `scatter_mode="fast"`, promoting the runtime gradient mutants to the Python manifest.

## Appendix A. The probed programs (scratch, 2026-11-11; copy into the fixture file with `tensor f64` declarations as shown, drop the dtype tag for the binary32 siblings)

The scratch files lived in the session scratchpad and are not in the repo, so the programs are recorded here. Inputs: `X[7, 3]`, `H0[4]`, `C0[4]`, matrices `W*[4, 3]`, `U*[4, 4]`, biases `B*[4]`, `Wy[5, 4]`, `Neg[]` = -1.

GRU with head:
```
iter t = 7
tensor f64 X(t, i), H0(d), Wz(d, i), Uz(d, e), Bz(d), Wr(d, i), Ur(d, e), Br(d), Wn(d, i), Un(d, e), Bn(d), Neg(), Wy(v, d)
tensor f64 H(d, t), Lg(v), Pr(v)
tensor f64 Az(d), Z(d), Ar(d), R(d), Uh(d), Rh(d), An(d), Nn(d), Zn(d)
H[d, 0]    := H0[d]
Az[d]      := Wz[d, i] · X[t, i] + Uz[d, e] · H[e, t] + Bz[d]
Z[d]       := sigmoid(Az[d])
Ar[d]      := Wr[d, i] · X[t, i] + Ur[d, e] · H[e, t] + Br[d]
R[d]       := sigmoid(Ar[d])
Uh[d]      := Un[d, e] · H[e, t]
Rh[d]      := R[d] · Uh[d]
An[d]      := Wn[d, i] · X[t, i] + Rh[d] + Bn[d]
Nn[d]      := tanh(An[d])
Zn[d]      := Neg[] · Z[d] · Nn[d]
H[d, t +1] := Nn[d] + Zn[d] + Z[d] · H[d, t]
Lg[v]      := Wy[v, d] · H[d, 6]
Pr[v.]     := softmax(Lg[v])
```
(without the last two statements and without `Wy`, `Lg`, `Pr`: the plain GRU; with `Yt[t, v] := Wy[v, d] · H[d, t]` and `tensor f64 Yt(t, v)` instead of the head: the per-step readout; with `iter t = 17` and `X[17, 3]`: the long GRU.)

LSTM (two states):
```
iter t = 7
tensor f64 X(t, i), H0(d), C0(d)
tensor f64 Wi(d, i), Ui(d, e), Bi(d), Wf(d, i), Uf(d, e), Bf(d), Wo(d, i), Uo(d, e), Bo(d), Wg(d, i), Ug(d, e), Bg(d)
tensor f64 H(d, t), Cc(d, t)
tensor f64 Ai(d), Ig(d), Af(d), Fg(d), Ao(d), Og(d), Ag(d), Gg(d), Fc(d), Ic(d), Cn(d), Tc(d)
H[d, 0]     := H0[d]
Cc[d, 0]    := C0[d]
Ai[d]       := Wi[d, i] · X[t, i] + Ui[d, e] · H[e, t] + Bi[d]
Ig[d]       := sigmoid(Ai[d])
Af[d]       := Wf[d, i] · X[t, i] + Uf[d, e] · H[e, t] + Bf[d]
Fg[d]       := sigmoid(Af[d])
Ao[d]       := Wo[d, i] · X[t, i] + Uo[d, e] · H[e, t] + Bo[d]
Og[d]       := sigmoid(Ao[d])
Ag[d]       := Wg[d, i] · X[t, i] + Ug[d, e] · H[e, t] + Bg[d]
Gg[d]       := tanh(Ag[d])
Fc[d]       := Fg[d] · Cc[d, t]
Ic[d]       := Ig[d] · Gg[d]
Cn[d]       := Fc[d] + Ic[d]
Tc[d]       := tanh(Cn[d])
Cc[d, t +1] := Cn[d]
H[d, t +1]  := Og[d] · Tc[d]
```
Bidirectional (NOT probed as one program; the forward layer, the stacked form and the reversed read were probed separately):
```
iter t = 7
tensor f64 X(t, i), Hf0(d), Hb0(d), Wf(d, i), Uf(d, e), Wb(d, i), Ub(d, e), Wo(v, d), Wp(v, d)
tensor f64 Hf(d, t), Hb(d, t), Af(d), Nf(d), Ab(d), Nb(d), Lg(v), Pr(v)
Hf[d, 0]     := Hf0[d]
Hb[d, 0]     := Hb0[d]
Af[d]        := Wf[d, i] · X[t, i] + Uf[d, e] · Hf[e, t]
Nf[d]        := tanh(Af[d])
Ab[d]        := Wb[d, i] · X[5 - t, i] + Ub[d, e] · Hb[e, t]
Nb[d]        := tanh(Ab[d])
Hf[d, t +1]  := Nf[d]
Hb[d, t +1]  := Nb[d]
Lg[v]        := Wo[v, d] · Hf[d, 6] + Wp[v, d] · Hb[d, 6]
Pr[v.]       := softmax(Lg[v])
```
Stacked two-layer Elman RNN (probed): `tensor f64 X(t, i), H10(d), H20(d), W1(d, i), U1(d, e), W2(d, e), U2(d, f)`, states `H1(d, t)`, `H2(d, t)`, intermediates `A1(d)`, `N1(d)`, `A2(d)`, `N2(d)`; `H1[d, 0] := H10[d]`, `H2[d, 0] := H20[d]`, `A1[d] := W1[d, i] · X[t, i] + U1[d, e] · H1[e, t]`, `N1[d] := tanh(A1[d])`,
`A2[d] := W2[d, e] · N1[e] + U2[d, f] · H2[f, t]`, `N2[d] := tanh(A2[d])`, `H1[d, t +1] := N1[d]`, `H2[d, t +1] := N2[d]`.

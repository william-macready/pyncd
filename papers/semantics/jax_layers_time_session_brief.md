# Session brief: layers x time on the JAX bridge (KV cache, time-then-layer scans, skewed layers)

Status: not started. Written 2026-11-23 at local `main` `5fb4a627` (= `origin/main`, pushed). Process weight: Direct path (`.claude/skills/slice-plan/` section 0, but you do not need that skill): tests and fixtures only. NO production change is expected: the programs below were probed on 2026-11-22 through every stage (record section 26 of `papers/semantics/jax_scan_record.md`) and all are accepted. If any step needs a change to `LeanNCD/*`, `EvalPlanCodegen.lean`, `evalplan_affine_runtime.py` or the grammar: STOP and report, do not edit them.

You are the EXECUTOR (a GPT-class agent with shell and repo access). Read the repo `CLAUDE.md` first: Rules 6, 12 and 14 govern you. Rule 13's standing permission to merge is the OWNER's, not yours: do NOT merge and do NOT push (see "Stop" below). Siblings that use the same harness and the same pin style, landed: `jax_rnn_session_brief.md` (record section 20), `jax_conv_session_brief.md` (19), `jax_cross_attention_session_brief.md` (18). Read `jax_rnn_session_brief.md` sections 2 and 5 and Appendix A before you start: they say how a scratch Lean probe is built, how fixtures are registered, how pins and hand mutants are written. This brief restates only what differs.

## 1. Goal

The last step of the agreed progression is "layers x time". True nested scans are NOT expressible (see section 6). Four forms ARE, each adding one structural idea; build all four as fixtures in BOTH precisions (binary64 and a `32` sibling), pinned against independent plain-Python models:

1. `kv_cache`: autoregressive decoding with a KV cache. One scan over time `t`; the cache is a STATE with a cache-position axis `s`; each step writes its key and value into slot `t` through a one-hot input `Oh[s, t]` and attends over the cache with a DATA mask `Mk[s, t]` (`0` where `s <= t`, `-1e9` otherwise) added to the scores. THE KEY PIN: the incremental cached output at step `t` equals full causal attention over `x_0 .. x_t` recomputed from scratch with the same weights (two independent numpy references).
2. `time_layer`: a time scan (a tanh RNN, `Hs[d, t]`), THEN a layer scan whose state carries the time axis as an ordinary axis (`Zz[t, d, l]`, `Zz[t, d, 0] = Hs[d, t]`, `Zz[t, d, l+1] = tanh(Wl[l] Zz[t, :, l])`). Two scan records.
3. `rnn_skew`: two stacked RNN layers over the SAME time axis where layer 2 reads layer 1's OLD state (a one-step skew), not the new state of the existing `rnn_stack`. One merged scan.
4. (stretch, park with a one-line cost if the budget forces a cut) `layer_skew`: layers as an ordinary tensor axis `l` inside ONE time scan, layer `l` reading layer `l-1`'s OLD state through a shift matrix `Sh[l, m]`. It is NOT a true stacked RNN; say so in the record.

Not in scope (park with a one-line cost if you find more, Rule 14): a nested or two-axis scan, a state read at a renamed axis, `where` masks that mention a scan axis (see trap 1), per-step intermediates in the layer scan of `time_layer`, sparse or top-k attention, variable lengths, any production change, the mutation manifests, changing an existing fixture, an existing tolerance, `np_transformer`.

## 2. Baseline and facts to verify before relying on them

- Local `main` `5fb4a627`. Baseline gates (re-verify, do not trust): `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd Tests JaxExperiment` = 8846 jobs, 0 errors; `run-evalplan-nonlin.sh` = 56 binary64 and 47 binary32 fixtures within tolerance (the bridge README still says 55; that is a stale count, note it, do not fix it outside your own README paragraph). Adding the four models in both precisions gives 60 and 51 (three models: 59 and 50).
- Harness: `leanncd/experiments/jax_bridge/EvalPlanNonlinSmoke.lean` (`fixture64`, `fixture32`, `checkAndRender`, helpers `t64`, `t32`, `env64`, `env32`, `gqaGen seed n`, `convBias`, `scanNanSlice`), driver `evalplan_nonlin_smoke.py` (`np_softmax_last`, `check_np`, `MODEL_TOL`, `GRAD_TOL`, `GRAD_FD_TOL`, `TRANSFORMER_FIXTURES`, `EAGER`, `dict_gap`, and the pin helpers to copy: `rnn_gru_pins`, `rnn_lstm_pins`, `rnn_bi_pins`, `rnn_grad_pins`, `conv_cnn_pins`). A scan fixture registers as `fixture64 "<name>" prog env minPw minAw (some (a, pw, aw)) true (scans := N)` (N = number of scan records), the sibling as `fixture32 ...`; read the existing `rnn_gru` registration and copy its shape. Do NOT edit `np_transformer`.
- Probe results (a scratch probe, 2026-11-22, binary64, extents below; the programs are in Appendix A). Observed there: `kv_cache` prepares with kind counts `(assign, pointwise, axiswise) = (14, 0, 1)`, ONE scan record with step_count 5; Lean, eager and jit agree with a plain-Python incremental loop to 5.6e-17 and with full causal recompute to 2.8e-17; cache state matches slot for slot. `time_layer`: `(6, 2, 0)`, TWO scan records (step_counts 5 and 2); agrees to 1.4e-16 (`Zz`) and 1.1e-16 (`Hs`). `rnn_skew`: `(8, 2, 0)`, ONE merged scan record (step_count 5); 1.4e-16. `layer_skew`: `(6, 1, 0)`, one scan record, two plan steps; 2.2e-16. JAX eager/jit agree with Lean to 2.2e-16 or better on all four. NOT observed: binary32 for any of them; gradients for `kv_cache` and `layer_skew` (NaN, trap 3); mutants. Confirm each observed figure yourself in Step 0 and report what you see; counts that differ are a STOP, not a silent fix.
- The einsum door refuses all four with `unsupportedStep` (like every scan fixture); pass `unaryOk := true` and `scans := N` as the existing scan fixtures do.

## 3. Traps (each is a pre-flight fact; the fixtures must respect it)

1. **A `where` mask that mentions a scan axis is REFUSED** (`CompileError.maskAxisNotOutput`, merged 2026-11-22, `5fb4a627`): a `softmax(where s <= t)` inside the time scan used to read `t` as 0 at every step, silently. So the causal mask here is a DATA mask `Mk[s, t]` added to the scores. Do not try `where`. (An Iverson factor `[s <= t]` is correct in a scan step and value-pinned in `NonlinCompileTest`, but it multiplies, so it cannot be a `-1e9` additive mask; the data mask is the form to use.)
2. **A state-independent intermediate that reads a scan-axis input is HOISTED out of the scan and summed over the scan axis** unless it carries an explicit time axis. Write `Kn[t, k] := Wk[k, i] · X[t, i]`, `Vn[t, v]`, `Qr[t, k]` (and `Ix[t, l, e]` in `layer_skew`) with `t` on the LEFT-hand side, as in Appendix A. Without it the cache gets NaN from the sentinel row (loud only because of the sentinel).
3. **Gradients through a hoisted table built from a NaN-sentinel row are NaN** (0 x NaN): the weight gradients of `kv_cache` (`Wq`, `Wk`, `Wv`) and `layer_skew` (`Wx`) are NaN while `X`'s spare row is NaN. For the gradient pins (Part B) use an environment whose spare row of `X` is a FINITE value (for example `0.0`); keep the NaN sentinel in the value environments. Measure which inputs still give NaN and report; never loosen a tolerance. `rnn_skew` and `time_layer` read `X[t, i]` directly inside the step and have finite gradients with the sentinel.
4. **Stacked inputs need the iteration extent.** `X(t, i)` has six rows under `iter t = 6` (five steps); row 5 is the spare slot, NaN in value environments, never read. A stacked weight over `l` (`Wl[l, d, e]`, three slices under `iter l = 3`, two steps) has a NaN spare slice 2. `Oh` and `Mk` are `[5, 6]` with the spare time column 5 NaN.
5. **No subtraction in a term, no state read at `t +1` on a right-hand side, pointwise functions take ONE product** (see the RNN brief traps 1, 2, 4). Programs below respect them.
6. **A per-step intermediate may not depend on two scan axes** (`shapeMismatch ... spans multiple scan components`): in `time_layer` the layer-scan step is ONE pointwise statement, with no `Al`/`Nl` intermediate.
7. **A free non-iter axis on a left-hand side cannot be sized from a read of a scan state**: in `time_layer` the time axis of the layer scan must be the SAME `iter t` (not a fresh name `u`).
8. **The solver may treat affine windows as exact size equations** (conv slice finding): a mutant that changes an index can be REFUSED at prepare instead of killed. Report it as a refusal and replace the mutant.

## 4. What to build

Step 0 (scratch, no commit): in the worktree run Appendix A through a scratch probe (the RNN brief section 5 recipe: `head -n 182` of the fixture file plus the programs plus a `main`, `lake env lean --run` with the `+leanprover/lean4:v4.30.0` pin; NOTE `scanNanSlice` is defined near line 598 and `gqaGen` near line 1362 of the fixture file, i.e. after line 182, so copy those two definitions (read them with `rg -n`) into the scratch file above your programs) and confirm the kind counts, scan-record counts and step counts of section 2. Then four fixtures x two precisions (8 registrations). A registration (`fixture64` / `fixture32`) is what builds BOTH executors' sides of the check, so each fixture is verified on three views: (1) LEAN DENSE: the registration runs the prepared plan with `runPreparedDense` (binary64) or `runPreparedDense32` (the `32` sibling) and writes the results into the generated fixture file as the `expected` values; (2) JAX EAGER and (3) JAX JIT: the registration renders the JAX plan (`checkAndRender`, which also checks the kind counts and scan-record count you pass), and the Python driver `evalplan_nonlin_smoke.py` runs that plan eagerly and under `jax.jit` and compares both to the Lean `expected` values at the stated tolerance, then pins them against your numpy models. Nothing else is needed to get all three; do not add another executor. The reference evaluator, the evidence path and the einsum door are not part of this harness (the einsum door refuses every scan fixture with `unsupportedStep`, as noted in section 2). Extents pairwise distinct per program: `kv_cache`: t=6, s=5, k=4, i=3, v=2; `time_layer`: t=6, l=3, d=4, i=3; `rnn_skew`: t=6, d=4, i=3; `layer_skew`: t=6, l=3, d=4, i=5 (`e` aliases `d`, `m` aliases `l`). Weights by `gqaGen` with distinct seeds (the probe seeds are in Appendix A), ONE definition per weight shared by the 64 and 32 environments. Exports are the state histories (per-step intermediates are not exported): `kv_cache`: `Kc`, `Vc`, `Yh`; `time_layer`: `Hs`, `Zz`; `rnn_skew`: `H1`, `H2`; `layer_skew`: `Hl`.

English references for the numpy models (write them with explicit loops over time and layers; no `np.einsum` over time, no `lax.scan`, no shared implementation with the plan; every model reads the exported INPUTS only):
- `kv_cache`: for `t = 0..4`: `q = Wq x_t`, `k = Wk x_t`, `v = Wv x_t`; write `k`, `v` into cache slot `t` (slots start at zero); scores `sc[s] = cache_k[s] . q + Mk[s, t]`; `p = softmax(sc)`; `y_t = sum_s p[s] cache_v[s]`; `Yh[:, t+1] = y_t`, `Yh[:, 0] = Y0`. Second reference (the key pin), no cache: `y_t = sum_{s<=t} softmax_{s<=t}(q_t . k_s) v_s` with `k_s = Wk x_s`, `v_s = Wv x_s`.
- `time_layer`: `h_{t+1} = tanh(Wx x_t + U h_t)` from `H0`; then independently for each `t = 0..5`: `z_0 = Hs[:, t]`, `z_{l+1} = tanh(Wl[l] z_l)` for `l = 0, 1`.
- `rnn_skew`: `h1' = tanh(W1 x_t + U1 h1)`; `h2' = tanh(W2 h1_OLD + U2 h2)` where `h1_OLD` is layer 1's state BEFORE this step's update (at step `t`, `H1[:, t]`).
- `layer_skew`: input of layer `l` at step `t` is `layer 0: Wx x_t`, `layer l>=1: H[l-1, :, t]` (the OLD state of the layer below); `H[l, :, t+1] = tanh(Wp[l] input + Up[l] H[l, :, t])`.

## 5. Pins (all independent of Lean's values) and mutants

Python, in the driver, ONE helper per model called once per precision (`kv_cache_pins`, `time_layer_pins`, `rnn_skew_pins`, `layer_skew_pins`), written like `rnn_gru_pins`. Each carries the extents in its print.
1. Value pins: every export on the Lean, eager and jit views at `MODEL_TOL` (all history slots, slot 0 = the initial state); report the observed maximum per precision. `kv_cache`: BOTH references (incremental loop and full causal recompute) on every step `t = 0..4`.
2. Non-vacuity (numpy gaps, each > 1e-2 unless stated): `kv_cache`: unmasked (`Mk = 0`) vs causal (probe: 0.46), mask off by one (`s < t`), cache never written (`Oh = 0`), cache slot written one step late, values read before the write (the current token's own `v` excluded); `rnn_skew`: layer 2 reading the NEW layer 1 state (the existing `rnn_stack` form; probe: 0.62), no recurrence in layer 2 (`U2 = 0`), layers swapped; `time_layer`: layer scan with shared weights (`Wl[0]` at every layer), time and layer order swapped; `layer_skew`: no shift (`Sh = 0`), shift upward, layer 2 vs the new-state stack (probe: 0.43).
3. Structural, value-independent: shapes from the inputs; plan shape (the scan-record count and step counts of section 2; the exact kind counts you observed); exports exactly as stated; the spare slots (NaN rows) never read: set the spare row of `X` (and of `Wl` for `time_layer`) to a finite value and EVERY export is bitwise unchanged; first history slot equals the initial state. TIME CAUSALITY on the eager runtime: perturb `X[t]`: `kv_cache` `Yh[:, s]` bitwise unchanged for `s <= t` and moves at `s = t + 1`; `rnn_skew` `H1[:, s]` unchanged for `s <= t` and `H2[:, s]` unchanged for `s <= t + 1`, moving at `s = t + 2` (the skew); `time_layer` `Hs[:, s]` unchanged for `s <= t` and `Zz[t', ...]` unchanged for `t' <= t`. FUTURE SLOTS ARE MASKED (`kv_cache`): set the initial cache rows `Kz[4]`, `Vz[4]` to a large finite value (for example `1e3`): `Yh[:, 1..4]` bitwise unchanged (the `-1e9` score underflows to exactly 0 in binary64; confirm, and in binary32 check the same or report) and the LAST step moves (the slot is written then), which proves the perturbation is live. Cache content: `Kc[s, :, tau]` is zero for `tau <= s` and equals `Wk x_s` for `tau > s`.
4. Inputs: `Oh`, `Mk`, `Sh` and every initial state from their definitions (Appendix A); the numpy side reads them from the exported inputs.
5. Keep every existing pin untouched and green.

Gradients (Part B, after Part A is green; cut it first if the budget forces a cut): `jax.grad` of `sum(C * out)` over every float input, eager and jit, with `out` = `Yh` for `kv_cache`, `Zz` for `time_layer`, `H2` for `rnn_skew`, `Hl` for `layer_skew`, against (a) a pure-JAX model written from the definition with a Python loop (not the plan) and (b) central differences of the numpy models. Use the finite-spare environment of trap 3 for `kv_cache` and `layer_skew`. The spare time row of `X` has EXACTLY zero gradient. Report headroom; do not loosen `GRAD_TOL`/`GRAD_FD_TOL`. Gradient vacuity self-test: absolute perturbation if gradients are O(0.1).

Hand mutants (edit the f64 program text, run `run-evalplan-nonlin.sh`, name the first failing assertion, restore by the INVERSE edit AFTER committing the work; `git diff --stat` must be empty; use an addressed `sed -i ''` (BSD) so the 32 sibling is not edited, or the Edit tool). Each must keep EVERY input used AND be accepted by the shape solver; a refused mutant is not a kill, report it and replace it. Suggested: A. `kv_cache` scores read the OLD key cache (`Sc[s] := Kc[s, k, t] · Qr[t, k] + Mk[s, t]`; `Kw` stays used by the cache update, so every input is used; the current token's own key is excluded); B. `kv_cache` the cache never updates (`Kc[s, k, t +1] := Kc[s, k, t]`); C. `kv_cache` output reads the OLD value cache (`Yo[v] := Pa[s] · Vc[s, v, t]`); D. `kv_cache` data: `Mk` off by one (`s < t`), the first failing assertion should be a non-vacuity gap or the causal-recompute pin; E. `rnn_skew` layer 2 reads the NEW state (`A2[d] := W2[d, e] · N1[e] + ...`); F. `time_layer` shared layer weights (`Wl[0, d, e]`); G. `layer_skew` shift through the wrong direction (`Sh` transposed, data); H. a mutant on a binary32 sibling (the f64 leg runs green first). If one SURVIVES, stop and report the exact edit. Record the table in the body of an empty commit.

## 6. What is NOT possible (do not try; these are findings, record them)

True nested or two-axis scans: the only two-axis form that elaborates is the diagonal `G[d, l +1, t +1] := f(G[d, l, t])`; the Lean checked plan accepts it and the JAX render refuses it (`unsupportedScanAxes 0`); a wavefront needs a `t +1` read on the right-hand side, which does not parse. A scan state read at a renamed axis (`Kh[k, s]` inside the step) is refused by the checked plan (`stateReadNotCausal`) although the reference evaluator accepts it. Both need a Lean checked-plan change and JAX per-axis step counters: separate slices, not yours.

## 7. Process, shell rules, budgets

- Pre-flight: `/usr/bin/git -C /Users/williammacready/code/python/pyncd merge-base --is-ancestor 5fb4a627 main` exits 0; the primary checkout is on `main` with an empty `git status --short`.
- Worktree: `/usr/bin/git -C /Users/williammacready/code/python/pyncd worktree add -b jax-layers-time-exec /Users/williammacready/code/python/pyncd/.claude/worktrees/layers-time-exec main`, then `bash <wt>/.claude/skills/new-slice/prepare-worktree.sh` with the worktree as the working directory (it must report Mathlib at or above 95%; if any build starts compiling Mathlib, STOP: hours). If the branch or directory already exists, STOP and report. Python and JAX: `bash <wt>/leanncd/experiments/jax_bridge/setup-python.sh` (needs network); if the directory `/Users/williammacready/code/python/pyncd.worktrees/task4-boolean-output/leanncd/experiments/jax_bridge/.cache/python` exists you may instead `ln -s` it to `<wt>/leanncd/experiments/jax_bridge/.cache/python` (git-ignored, never commit it). WITHOUT that directory the runner exits with "Experiment Python not found": that is NOT a pass; verify the runner printed its "fixtures within" lines. Prefix every runner command with `env -u PYTHON`.
- STALE-OLEAN TRAP: run `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd Tests JaxExperiment` once before any scratch probe, and again after any hand mutant (a mutation build leaves mutated oleans behind).
- Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command, no heredocs, no `;` chains, absolute paths, `/usr/bin/git -C <wt>`. Write files with your edit tool. Build Lean only with `lake-build.sh`; `lake` is at `~/.elan/bin/lake`, not on `PATH`. Read file windows of 40-60 lines and use `rg -n`; never read a whole file over about 20k characters. Run builds, runners and mutants in the background with output redirected to a file and wait; never run two Lean builds or runs at the same time. Stage by explicit path, never `git add -A`; never commit `.claude/settings.json`.
- Do not edit `EvalPlanCodegen.lean`, `ScanAffineEmitTest.lean`, `ExecutableTest.lean`, `ScanJaxGateTest.lean`, the mutation manifest JSON files, `evalplan_affine_runtime.py` (except as a scratch gradient mutant, restored), `LeanNCD/*`, existing fixtures, programs, environments, `np_transformer` or assertion texts.
- Budgets (Rule 6): at most about 60 tool calls and 250k context per session. Split: (A) pre-flight, worktree, setup, Step 0, the Lean programs, envs, registrations, typecheck (`bash <wt>/leanncd/scripts/lean-file.sh <wt>/leanncd experiments/jax_bridge/EvalPlanNonlinSmoke.lean`), one runner run; (B) the Python pins for the four models; (C) mutants, README, record; (D) Part B gradients. Report the call count per session from your own telemetry and name the method. If the budget forces a cut, ship `kv_cache` and `time_layer` with pins 1 to 5 and park the rest, saying so.
- Measure the binary32 error against numpy BEFORE fixing generator seeds (a scratch script on the generated 32 fixtures; no Lean rebuild per candidate); report every candidate seed tried and the headroom of each new binary32 fixture; never loosen a tolerance. Short contractive recurrences are expected to be well conditioned; the `-1e9` mask in binary32 is the thing to check.

## 8. Verification, records, stop

Before you stop: `lake-build.sh <wt>/leanncd Tests JaxExperiment` (expect 8846 jobs, 0 errors; no new Lean module), `bash <wt>/leanncd/experiments/jax_bridge/check-lean-drivers.sh` (expect `all eight drivers ran clean`), and `run-evalplan-nonlin.sh` ONCE on the final tree (expect 60 binary64 and 51 binary32 within tolerance if all four models are added, else 56 + your number). One read-only review of your own diff by reading: look for pins that a trivial or perturbed entry satisfies by itself (a numpy model sharing an indexing or time-order bug with the program, a non-vacuity test that is invariant under the change it claims to detect, a gradient reference that reuses the plan's own scan, a causality pin that holds for a model reading the whole sequence at every step, a spare-slot pin that holds because the slot is read as zero).

Records: add section 27 to `papers/semantics/jax_scan_record.md` (the programs, observed kind counts and scan records, the traps and their pinned or avoided form, the seeds and binary32 candidates with errors, observed numpy gaps and headroom, the mutation table, deviations, call counts, parked items), one paragraph in the bridge README next to the RNN paragraph, and fix the README fixture count to the number the runner prints (note that it said 55 before you started). Update the "next step" sentence of section 26 only if your result changes it.

Stop: commit the work (one commit per work item, plus the mutation table as an empty commit and the record), leave `git status --short` empty, and STOP at "READY FOR WHOLE-BRANCH REVIEW" on the branch `jax-layers-time-exec`. Do NOT merge, do NOT push, do not delete the worktree or branch. Side issues you find: write them in the record as parked with a one-line cost; do not start them (Rule 14). BLOCKED rule: if pre-flight fails, a build is red, a count differs from section 2, a runner does not print its "fixtures within" lines, a mutant survives or is not restored, or an existing pin goes red, STOP and report the exact command and output; do not repair around it.

Final message to the owner: base commit and branch tip; commit hashes with subjects; the Step 0 observations against section 2 (kind counts, scan records, step counts, max differences); the pin results with observed maxima per precision and the binary32 headroom of each new fixture; the mutation table; the three verification results with counts; parked items with cost; call counts per session and the method; every skipped step or STOP; and confirmation that nothing was merged or pushed.

## Appendix A. The probed programs (scratch, 2026-11-22; copy into the fixture file as shown, drop the `f64` tag for the binary32 siblings)

Helpers (define next to the existing ones, names free of clashes): `gT seed shape := t64 shape (gqaGen seed (product shape))`; `zT shape` = zeros; `nanRowT seed rows rest shape := t64 shape (gqaGen seed ((rows - 1) * rest) ++ scanNanSlice (gqaGen 0.0 rest))` (the last leading slice of `rest` elements is NaN); `ohT := t64 [5, 6]` with entry `(s, t)` = NaN if `t == 5`, else `1.0` if `s == t`, else `0.0`; `mkT := t64 [5, 6]` with entry `(s, t)` = NaN if `t == 5`, else `0.0` if `s <= t`, else `-1.0e9`; `shT := t64 [3, 3] #[0,0,0, 1,0,0, 0,1,0]`.

`kv_cache` (inputs: `X = nanRowT 1.0 6 3 [6, 3]`, `Wq = gT 2.0 [4, 3]`, `Wk = gT 3.0 [4, 3]`, `Wv = gT 4.0 [2, 3]`, `Kz = zT [5, 4]`, `Vz = zT [5, 2]`, `Y0 = zT [2]`, `Oh = ohT`, `Mk = mkT`):
```
iter t = 6
tensor f64 X(t, i), Wq(k, i), Wk(k, i), Wv(v, i), Kz(s, k), Vz(s, v), Y0(v), Oh(s, t), Mk(s, t)
tensor f64 Kc(s, k, t), Vc(s, v, t), Yh(v, t), Kn(t, k), Vn(t, v), Qr(t, k), Kw(s, k), Vw(s, v), Sc(s), Pa(s), Yo(v)
Kc[s, k, 0]    := Kz[s, k]
Vc[s, v, 0]    := Vz[s, v]
Yh[v, 0]       := Y0[v]
Kn[t, k]       := Wk[k, i] · X[t, i]
Vn[t, v]       := Wv[v, i] · X[t, i]
Qr[t, k]       := Wq[k, i] · X[t, i]
Kw[s, k]       := Kc[s, k, t] + Oh[s, t] · Kn[t, k]
Vw[s, v]       := Vc[s, v, t] + Oh[s, t] · Vn[t, v]
Sc[s]          := Kw[s, k] · Qr[t, k] + Mk[s, t]
Pa[s.]         := softmax(Sc[s])
Yo[v]          := Pa[s] · Vw[s, v]
Kc[s, k, t +1] := Kw[s, k]
Vc[s, v, t +1] := Vw[s, v]
Yh[v, t +1]    := Yo[v]
```

`time_layer` (inputs: `X = nanRowT 1.0 6 3 [6, 3]`, `H0 = gT 13.0 [4]`, `Wx = gT 14.0 [4, 3]`, `U = gT 15.0 [4, 4]`, `Wl = nanRowT 16.0 3 16 [3, 4, 4]`):
```
iter t = 6, l = 3
tensor f64 X(t, i), H0(d), Wx(d, i), U(d, e), Wl(l, d, e)
tensor f64 Hs(d, t), Zz(t, d, l), Ah(d), Nh(d)
Hs[d, 0]       := H0[d]
Ah[d]          := Wx[d, i] · X[t, i] + U[d, e] · Hs[e, t]
Nh[d]          := tanh(Ah[d])
Hs[d, t +1]    := Nh[d]
Zz[t, d, 0]    := Hs[d, t]
Zz[t, d, l +1] := tanh(Wl[l, d, e] · Zz[t, e, l])
```

`rnn_skew` (inputs: `X = nanRowT 1.0 6 3 [6, 3]`, `H10 = gT 7.0 [4]`, `H20 = gT 8.0 [4]`, `W1 = gT 9.0 [4, 3]`, `U1 = gT 10.0 [4, 4]`, `W2 = gT 11.0 [4, 4]`, `U2 = gT 12.0 [4, 4]`):
```
iter t = 6
tensor f64 X(t, i), H10(d), H20(d), W1(d, i), U1(d, e), W2(d, e), U2(d, f)
tensor f64 H1(d, t), H2(d, t), A1(d), N1(d), A2(d), N2(d)
H1[d, 0]       := H10[d]
H2[d, 0]       := H20[d]
A1[d]          := W1[d, i] · X[t, i] + U1[d, e] · H1[e, t]
N1[d]          := tanh(A1[d])
H1[d, t +1]    := N1[d]
A2[d]          := W2[d, e] · H1[e, t] + U2[d, f] · H2[f, t]
N2[d]          := tanh(A2[d])
H2[d, t +1]    := N2[d]
```

`layer_skew` (inputs: `X = nanRowT 21.0 6 5 [6, 5]`, `Wx = gT 22.0 [4, 5]`, `E0 = t64 [3] #[1.0, 0.0, 0.0]`, `Sh = shT`, `H0 = gT 23.0 [3, 4]`, `Wp = gT 24.0 [3, 4, 4]`, `Up = gT 25.0 [3, 4, 4]`):
```
iter t = 6
tensor f64 X(t, i), Wx(d, i), E0(l), Sh(l, m), H0(l, d), Wp(l, d, e), Up(l, d, e)
tensor f64 Hl(l, d, t), Ix(t, l, e), Hi(l, e), Aa(l, d), Nn(l, d)
Hl[l, d, 0]    := H0[l, d]
Ix[t, l, e]    := E0[l] · Wx[e, i] · X[t, i]
Hi[l, e]       := Sh[l, m] · Hl[m, e, t] + Ix[t, l, e]
Aa[l, d]       := Wp[l, d, e] · Hi[l, e] + Up[l, d, e] · Hl[l, e, t]
Nn[l, d]       := tanh(Aa[l, d])
Hl[l, d, t +1] := Nn[l, d]
```
(`layer_skew` is the weakest of the four: gradients are NaN with the sentinel row (trap 3), and it is a skewed network, not a stacked RNN. In the probe the `kv_cache` seeds above were not tuned for binary32.)

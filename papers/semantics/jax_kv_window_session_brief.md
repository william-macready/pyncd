# Session brief: extent-aware causality of state-history reads (window and lag reads) and the `kv_window` / `kv_lag` fixtures

Status: not started. Written 2026-11-25 at local `main` `a1799d71` (equal to `origin/main`). Process weight: DIRECT path with one production change that WIDENS a soundness check, therefore two review lenses (wrongly accepts, wrongly rejects) and an exhaustive brute-force oracle as the central test. The production change is exactly the patch of Appendix A (two files, three new definitions, two call sites). You may apply it as given. Any other change under `leanncd/LeanNCD/`, any change to `EvalPlanCodegen.lean`, `evalplan_affine_runtime.py`, the grammar, an existing fixture, pin or tolerance: STOP and report, do not edit.

You are the EXECUTOR (a GPT-class agent with shell and repo access). Read the repo `CLAUDE.md` first: Rules 6, 12 and 14 govern you. Rule 13's standing permission to merge is the OWNER's, not yours: do NOT merge and do NOT push (section 8). Read `papers/semantics/jax_layers_time_session_brief.md` sections 3 and 7 (traps and shell rules; they all still apply) and `papers/semantics/jax_skew_fixtures_session_brief.md` sections 5 to 8 (the pin, mutant and stop conventions you follow; its fixtures are your pattern for registration and pins). Your fixture pattern in code: in `leanncd/experiments/jax_bridge/EvalPlanNonlinSmoke.lean` the block "Layers × time" (`kvCacheInputs`, `kvCacheEnv64`, `kvCacheEnv32`, `kvCacheProg`, `kvCacheProg32` and the `kv_cache` registrations), and in `evalplan_nonlin_smoke.py` `np_kv_cache`, `kv_cache_pins`, `layers_time_grad_pins`, `require_close`, `check_np` and `TRANSFORMER_FIXTURES`. Record sections 27 and 28 of `papers/semantics/jax_scan_record.md` say which pins the earlier reviews found weak: do not repeat those weaknesses.

## 1. Goal

A scan whose state history is `Kh(k, t)` can read its OWN history at an offset that depends on a second axis, for example the last `W` slots (a sliding-window or full-history KV cache). Today that is refused by the checked plan (`stateReadNotCausal`) because the checker only knows the single row shape "scan coordinate plus a non-positive constant". The refusal is correct for a read it cannot bound, but a window read IS bounded, and can be PROVEN causal from its affine row and the axis extents alone, with no mask involved:

> A read of the state's advancing dimension has row `slot(x) = c_t * t + sum_p c_p * x_p + b` over the term's iteration box (every position `p` ranges over `[0, extent_p)`). It is causal iff `c_t == 1`, no OTHER context position appears in the row, and the largest slot it can address is `<= t`: `b + sum over p with c_p > 0 of c_p * (extent_p - 1) <= 0`. Every slot `<= t` has already been written at the step that reads it (slot `j + 1` is written at step `j`), and a slot below `0` zero-pads, as today. The existing strict rule is the special case of no other axis.

Deliver, on the branch `jax-kv-window-exec`:
1. The predicate (Appendix A.1), wired into the two places that check a scan's state reads, plus an EXHAUSTIVE brute-force oracle test (Appendix A.2), raw-plan pins, source-level pins and two hand-computable value pins.
2. Two fixtures, each in BOTH precisions, pinned against an independent numpy model: `kv_window` (read `Kh[k, t + u - 4]`, a window of `W = 5` slots ending at `t`) and `kv_lag` (read `Kh[k, t - u]`, lag `u`; a NEGATIVE coefficient on the extra axis).
3. Mutants (checker and fixtures), docs and record section 29.

(Annotation 2026-11-26: the step-aware `where` mask named in the next paragraph now exists on the Lean side (guard, reference, checked plan, unrolled differential); JAX support is the next slice, and the bare `Kh[k, s]` read is still refused by causality; see `jax_step_mask_scope.md`.)

Not in scope (park each with a one-line cost, Rule 14): the natural spelling `Kh[k, s]` with `softmax(where s <= t)` (needs a step-aware `where` mask in the reference evaluator, the checked plan and the JAX emitter plus a dataflow proof; it is refused today by `maskAxisNotOutput` AND by the causality check, and stays so); Iverson guard factors on real or max-plus terms for JAX (refused: `iversonFactor`); attention that also includes the CURRENT token's key (see trap 4); a window shorter than the history (needs another extent set); window reads in a MULTI-axis scan (the predicate handles them, no fixture); making the reference evaluator refuse non-causal reads; changing `IndexedAffineScanProfile` or any file under `experiments/indexed_execution/`.

## 2. Baseline, and what was observed versus not

- Local `main` `a1799d71` or a descendant that only adds files under `papers/semantics/`. Baseline gates (re-verify, do not trust): `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd Tests JaxExperiment` = 8846 jobs, 0 errors; `check-lean-drivers.sh` = `all eight drivers ran clean`; `run-evalplan-nonlin.sh` = 63 binary64 and 54 binary32 fixtures within tolerance. Two models in both precisions give 65 and 56.
- OBSERVED on 2026-11-25 on a scratch worktree that carried exactly the patch of Appendix A (binary64 only):
  1. The patch compiles; `lake-build.sh ... Tests JaxExperiment` on it = 8846 jobs, 0 errors: NO existing pin flips.
  2. The oracle of Appendix A.2 (24300 rows, 7 `#guard`s) passes in about 14 s; three mutated copies of the predicate (bound `<= 1`; extents ignored; extent off by one) each FAIL it.
  3. Raw-plan verdicts (a windowed sum over a reduction position, clone of `deepHistoryScan`, `checkScanPlan`), Appendix A.3: ACCEPT for `G[l + j - 1]`, `G[l - j]`, `G[l + 2j - 2]`; REJECT `causalityFailure 0 0 0 0` for `G[l + j]`, `G[l + 2j - 1]`, `G[2l + j - 3]`, `G[j]`; the unchanged deep-history scan still ACCEPT.
  4. Source-level verdicts (`rej` playground of `ScanCompileTest`), Appendix A.4: same pattern, REJECT is `.scan (.stateReadNotCausal "sc" "S" 0 0 0)`.
  5. Value pins (Appendix A.5): both `diffEqB` guards pass (source, checked plan and reference evaluator agree with the hand-computed Fibonacci table).
  6. Fixture programs of Appendix B, through every stage: `compileToScheduled` ok; `prepareEvalPlan` ok with kinds (assign, pointwise, axiswise) = (12, 0, 1), top-level plan nodes assign, assign, assign, scan (4 steps), ONE scan record with `step_count` 5; Lean dense equals the reference evaluator on every export (max diff 0); `einsumOnly` refuses with `unsupportedStep 3`; the JAX gate and render accept. Exports (`expected` keys): `Kn`, `Vn`, `Qr`, `Kh`, `Vh`, `Yh`. The neighbour `Kh[k, t + u - 3]` (reads slot `t + 1`) is REFUSED at prepare with `stateReadNotCausal "Sc" "Kh" 0 0 0`; `t + u - 5` is accepted.
  7. Exactness against the numpy model of Section 4: `Yh` 5.6e-17 (Lean, eager, jit; `kv_lag`: 5.6e-17 Lean, 8.3e-17 eager and jit), `Kh` and `Vh` exactly 0, eager == jit bitwise. `jax.grad` of `sum(Yh[:, 5])`: finite for EVERY input, eager and jit, and equal to central differences of the numpy model to 5e-12 (`Wq`), 3e-11 (`Wk`), 1.2e-11 (`Wv`), 1.8e-12 (`K0`), 4.7e-12 (`V0`), 5.1e-12 (`X`).
  8. Padding: setting `X` row 5 (never consumed by a step) to 0.5 leaves `Yh`, `Kh`, `Vh` BITWISE unchanged on the eager runtime and moves `Kn`, `Vn`, `Qr`.
  9. Causality on the eager runtime, perturbing `X[t]` by +0.37: `Yh` columns `p <= max(t, 1)` are bitwise unchanged for every `t = 0..4`; the first column that moves is `[2, 2, 3, 4, 5]` for `t = 0..4` with max move `[0.0974, 0.0008, 0.0141, 0.0412, 0.0562]`. Perturbing `K0` leaves columns 0 and 1 unchanged; perturbing `V0` moves column 1 by exactly the perturbation. Max `|softmax score|` on live cells 0.624 (nothing saturates). Both fixtures gave identical numbers.
  10. Mask removed (`Mk = 0`): JAX equals a numpy model that reads unwritten or padded cells as zero vectors (2.8e-17) and is 0.463 from the causal model (the non-vacuity gap).
  11. Positions: the dense engine enumerates every position over `List.range extent` (`allCoords` in `Coordinates.lean`), so "each position runs from 0" holds there; the JAX side consumes Lean's gather tables.
  12. The non-default target `IndexedExecutionExperiment` (it contains `IndexedAffineScanProfile`, which calls the strict `stateReadCausal` and is NOT edited) builds green ON THE PATCH: `lake-build.sh ... IndexedExecutionExperiment` = 8729 jobs, 0 errors, and its axiom audit line reads "882 constants under IndexedExecutionExperiment.AffineScan use only standard axioms". It took over ten minutes in the scratch worktree (run it in the background with output to a file). Its result at the BASE commit was not measured: build it at the base first, report both; a failure that also occurs at the base is not yours.
- NOT observed (report what you see; a difference is a finding): binary32 for either fixture; the registrations; every Python pin and mutant below; the multi-axis (grid) behaviour of the predicate beyond the oracle's single extra context position; the hand mutants.
- Audit of consumers (grep, 2026-11-25): the only production callers of `stateReadCausal` are `checkScanCore` in `Scan.lean` and Phase 5 of `Compile.lean`; no module under `LeanNCD/Semantics/` mentions causality or look-back (scan history retention reasons about allocation, not read rows). Re-run the grep for `stateReadCausal`, `causalAdvancingRow`, `stateReadNotCausal`, `causalityFailure` over `leanncd/` and `papers/` and list any consumer I missed.

## 3. Traps (pre-flight facts; each is respected by Appendix B)

1. A `where` mask over the scan axis is refused (`maskAxisNotOutput`): the window mask is DATA (`Mk[u, t]`, additive `-1.0e9`), as in `kv_cache`. The mask now only says which cells EXIST (slot `>= 0`); it carries no safety. Without it a cell with slot `< 0` zero-pads and attends with score 0 (non-vacuity gap 0.463).
2. Extents pairwise distinct: `t = 6`, `u = 5`, `k = 4`, `i = 3`, `v = 2`. The extra axis needs its declaration `axis u : ℕ = 5`.
3. The spare time row is FINITE here: `X` row 5 is `0.0` and `Mk` column 5 follows the same formula (all `0.0`). Do NOT use the NaN spare row of `kv_cache`: it makes the `Wq`, `Wk`, `Wv` gradients NaN (0 * NaN through the hoisted tables). Row 5 of every `t`-indexed table is never consumed by a step (`step_count` is 5), which is why a finite filler is safe and why the padding perturbation pin of section 5 holds.
4. History extent is 6 (`iter t = 6`): slots 0..5; slot 0 holds `K0`, slot `j + 1` holds the key of step `j`. At step `t` the visible slots are `0..t`, so the model attends over `[K0, k_0, .., k_{t-1}]`: the current token's key is NOT visible at its own step (it lands in slot `t + 1`). This is a different model from `kv_cache` (which merges the current key); at `t = 0` there is a single cell, so `Yh[:, 1] == V0` independently of the query. Do not "fix" this; parked.
5. `Mk[u, t]` for `kv_window` is `0.0` iff `t + u >= 4` (slot `t + u - 4 >= 0`), else `-1.0e9`; for `kv_lag` it is `0.0` iff `t >= u`, else `-1.0e9`; entry index `6 u + t`.
6. The strict predicate `stateReadCausal` and `causalAdvancingRow` stay, unchanged, for `experiments/indexed_execution/IndexedAffineScanProfile.lean` and the existing tests. The production call sites use the new `stateReadCausalIn`.
7. All the traps of the layers-time brief section 3 still hold (no subtraction in a TERM; the index grammar does admit `t - u` and `t + u - 4`, verified; no state read at `t +1` on a right-hand side; pointwise functions take ONE product; extents distinct; a hand mutant can be REFUSED at prepare: report it and replace it).

## 4. What to build

Work item 1 (Lean only, session A). `Scan.lean` and `Compile.lean` as in Appendix A.1 (apply with the Edit tool; the old strings are given exactly). Then, test-first order does not matter, add: (a) the oracle (Appendix A.2) as a new Part at the end of `leanncd/test/Eval/Plan/ScanTest.lean`, names prefixed `ec` (check for clashes with `rg -n`); (b) the raw-plan pins of Appendix A.3 in `ScanTest.lean` next to the Part 4 causality fixtures; (c) the source-level pins of Appendix A.4 in `ScanCompileTest.lean` section 2.7, after the "slice-dependent" fixture; (d) the two value pins of Appendix A.5 at the end of `NonlinCompileTest.lean`. Gate: `lake-build.sh <wt>/leanncd Tests JaxExperiment` = 8846 jobs. Then the checker mutants of section 6 (Lean-only, one rebuild each).

Work item 2 (session B). Four registrations after the skew block in `EvalPlanNonlinSmoke.lean`: `kv_window`, `kv_lag`, `kv_window32`, `kv_lag32`. Follow `kvCacheInputs`: ONE definition of every input shared by the 64 and 32 environments, the `32` programs omit the `f64` tag, the two fixtures share all inputs except `Mk`. Registration (confirm with the typecheck): `fixture64 "kv_window" kvWindowProg kvWindowEnv64 0 1 (some (12, 0, 1)) true (scans := 1)` and the same for `kv_lag`; `fixture32` for the siblings. Driver wiring (verify in the driver): add the four names to `TRANSFORMER_FIXTURES` at the top of `evalplan_nonlin_smoke.py` the way the layers-time names are; `EAGER` is filled automatically for plans with a scan record; do NOT add the names to `NAN_TIME_OUTPUTS` or `NAN_LAYER_OUTPUTS` (no NaN anywhere); call your pin helpers in the main pin sequence next to `kv_cache_pins(by, sfx)`. Do not change behaviour for existing fixtures.

Work item 3 (session C): fixture mutants, gradients, docs, record.

English reference for the numpy model (explicit loops, no `lax.scan`, no shared code with the plan, reads only the exported INPUTS and NEVER `Mk`): `np_kv_history`: `keys = [K0]`, `vals = [V0]`; for `t = 0..4`: `q = Wq x_t`, `kn = Wk x_t`, `vn = Wv x_t`; `p = softmax([dot(key, q) for key in keys])`; `Yh[:, t + 1] = sum_j p[j] * vals[j]`; then append `kn` to `keys`, `vn` to `vals`; `Kh[:, 0] = K0`, `Kh[:, t + 1] = kn`, `Vh[:, 0] = V0`, `Vh[:, t + 1] = vn`; `Yh[:, 0] = Y0 = 0`. Tables: `Kn[t] = Wk x_t`, `Vn[t] = Wv x_t`, `Qr[t] = Wq x_t` for all 6 rows (row 5 from the finite `X` row 5). Both fixtures use THIS model (softmax is permutation-invariant over the window axis).

## 5. Pins (all independent of Lean's values) and mutants

Python, ONE helper per fixture family called once per precision (`kv_history_pins(by, sfx)` covering both fixture names), written like `kv_cache_pins`, printing its extents. `check_np` (finiteness assert) applies to every export in full: there is no NaN row.
1. Value pins: every export on the Lean, eager and jit views at `MODEL_TOL`; the tables for all 6 rows; `Yh[:, 1] == V0`. Report the observed maximum per precision.
2. Non-vacuity (numpy gaps, each > 1e-2, asserted, computed ONLY over `Yh` columns 2..5 because column 1 is `V0` for every variant; print the domain): mask removed (cells with slot `< 0` read as zero vectors; observed 0.463 over all columns, recompute on 2..5); window one slot shorter (drops `K0` at `t = 4`: differs only in column 5, compute there); the current key included (the `kv_cache` semantics); values misaligned by one slot (`vals` shifted); `K0` replaced by zeros.
3. Structural, value-independent: shapes from the inputs; plan shape (4 top-level nodes assign, assign, assign, scan; ONE scan record, `step_count` 5; kinds exactly (12, 0, 1)); exports exactly `Kn, Vn, Qr, Kh, Vh, Yh`; every input finite; `Mk` equals its definition exactly; `X` row 5 equals `[0, 0, 0]`; weights equal their `gqaGen` formulas (as `kv_cache_pins` does). PADDING PERTURBATION: `X` row 5 to 0.5: `Yh`, `Kh`, `Vh` bitwise unchanged, `Kn`/`Vn`/`Qr` row 5 move. TIME CAUSALITY on the eager runtime, perturbing `X[t]` by +0.37 for `t = 0..4`: `Yh` columns `p <= max(t, 1)` bitwise unchanged, the first moved column is `[2, 2, 3, 4, 5]` and its max move exceeds 1e-4 (observed `[0.0974, 0.0008, 0.0141, 0.0412, 0.0562]`; the second is the smallest: report the margin); a model that read the whole sequence fails the unchanged-columns pin. HISTORY INFLUENCE: perturbing `K0` leaves columns 0 and 1 bitwise unchanged and moves columns 2..5; perturbing `V0` moves column 1 by the perturbation (within `MODEL_TOL`) and columns 2..5.
4. Keep every existing pin untouched and green.

Gradients (cut first if the budget forces a cut): `jax.grad` of `sum(C * Yh[:, 5])` (a fixed non-uniform `C`) over every float input, eager and jit, against (a) a pure-JAX model of the true attention written with Python loops and lists (NOT the plan and not `lax.scan`) and (b) central differences of the numpy model for `Wq`, `Wk`, `Wv`, `K0`, `V0` and the live rows of `X`; `X` row 5 and `Y0` have EXACTLY zero gradient (predicted, not observed); `Mk` only finite and eager == jit bitwise (freeze it in the finite-difference directions and say so). Report headroom against `GRAD_TOL` and `GRAD_FD_TOL`; do not loosen them.

Hand mutants of the fixtures (edit the f64 program or data text, run `run-evalplan-nonlin.sh`, name the first failing assertion, restore by the INVERSE edit after committing; `git diff --stat` must be empty; use the Edit tool or an addressed BSD `sed -i ''` so the `32` sibling is not edited; rebuild with `lake-build.sh` after each mutant): A (data) `kv_window` `Mk` all zeros; B (data) `kv_window` `Mk` threshold `t + u >= 3`; C (program) `kv_window` value read `Vh[v, t + u - 5]` (accepted, misaligned); D (program) `kv_window` key read `Kh[k, t + u - 3]`: this one is REFUSED at prepare (`stateReadNotCausal`), report the exact refusal text as the live demonstration and replace it by D' key read `t + u - 5`; E (program) `kv_lag` key read `Kh[k, t - u - 1]`; F (data) `kv_lag` `Mk` threshold `t >= u + 1`; G a mutant on a `32` sibling (the f64 leg green first). Each must keep EVERY input used and be accepted by the shape solver; a refused mutant is not a kill. If one SURVIVES, stop and report the exact edit. Record the table in an empty commit.

## 6. Checker mutants (Lean, work item 1)

Edit `Scan.lean`, run `lake-build.sh <wt>/leanncd Tests`, name the first failing guard, restore by the inverse edit (commit first; `git diff --stat` empty after): M1 bound `<= 0` to `<= 1` in `causalAdvancingRowIn` (killed by the oracle's soundness guard); M2 drop the sum in `maxSlotOffset` (use `bias` only) (oracle); M3 `shape_p - 1` to `shape_p` (oracle exactness guard); M4 `row.getD ctxPos 0 == 1` to `!= 0` (oracle: the conservative-outside-class guard); M5 drop the "no other context position" conjunct (oracle multi-context guard); M6 revert the `Compile.lean` call site to the strict `stateReadCausal` (killed by the source accept pins, A.4); M7 revert the `checkScanCore` call site in `Scan.lean` to the strict `stateReadCausal` (killed by the raw accept pins, A.3; note that M6 may also surface there). A survivor means a missing pin: add it, do not weaken the mutant. The three predicate mutants of observation 2 are already known killed; yours are the production ones.

## 7. What is NOT possible or not claimed (record as findings, do not try)

The oracle proves the predicate against the box model; it does not prove the box model: that every position runs over `[0, extent)` is observed for the dense engine only (observation 11); say so in the record. A window read can only address a slot below 0 (zero pad) or a written slot, never an unwritten one (excluded by the rule); the reference evaluator accepts more (non-causal reads, `S[j,l+1] := S[j,2*l]`): it is not changed. Compile and trace time of the window gather were not measured: do not quote one. `kv_window` with `W = 5` and 5 steps covers the whole history, so the window edge never drops a slot: a truncated window is parked.

## 8. Process, shell rules, budgets, stop

As in `jax_layers_time_session_brief.md` section 7 (read it), with: branch `jax-kv-window-exec`, worktree `/Users/williammacready/code/python/pyncd/.claude/worktrees/kv-window-exec`, pre-flight `/usr/bin/git -C /Users/williammacready/code/python/pyncd merge-base --is-ancestor a1799d71 main` exits 0; the Python env: `setup-python.sh` or, if `/Users/williammacready/code/python/pyncd.worktrees/task4-boolean-output/leanncd/experiments/jax_bridge/.cache/python` exists, a symlink to it at `<wt>/leanncd/experiments/jax_bridge/.cache/python` (git-ignored, never commit it); WITHOUT it the runner prints "Experiment Python not found" and that is NOT a pass: verify the "fixtures within" lines. Prefix every runner command with `env -u PYTHON`. Plain separate shell commands, no heredocs, no `cd x && y`, absolute paths, `/usr/bin/git -C <wt>`, stage by explicit path, build only with `lake-build.sh`, background long runs with output to a file, never two Lean builds or runs at once, windows of 40-60 lines.
Do not edit: `EvalPlanCodegen.lean`, `ScanAffineEmitTest.lean`, `ExecutableTest.lean`, `ScanJaxGateTest.lean`, the mutation manifest JSON files, `evalplan_affine_runtime.py` (except as a restored scratch mutant), anything under `experiments/indexed_execution/`, anything under `LeanNCD/` except the two files of Appendix A.1, existing fixtures, programs, environments, `np_transformer`, assertion texts.
Budgets (Rule 6): at most about 60 tool calls and 250k context per session. Split: (A) pre-flight, worktree, setup, base-commit build of `IndexedExecutionExperiment`, work item 1 incl. checker mutants; (B) work item 2 (Lean registrations, one typecheck with `bash <wt>/leanncd/scripts/lean-file.sh <wt>/leanncd experiments/jax_bridge/EvalPlanNonlinSmoke.lean`, one runner run, the Python pins); (C) fixture mutants, gradients, docs, record. Report the call count per session and name the method. If the budget forces a cut, ship work item 1 complete and the `kv_window` fixture with pins 1 to 4 and park the rest, saying so.
Measure the binary32 error against numpy BEFORE fixing seeds (a scratch script on the generated 32 fixtures); report every candidate seed tried and the headroom of each binary32 fixture; never loosen a tolerance.
DEVIATION AUTHORITY: you may change fixture DATA and SIZES only to satisfy a rule this brief states (an extent, a seed, a name that clashes), keeping program structure; record each deviation with the numbers you observed and continue. Anything that changes a program's structure, an export, a pin's meaning, a tolerance, the patch of Appendix A.1, or needs another production change is NOT yours: STOP and report. BLOCKED rule: if pre-flight fails, the patch does not apply, a build is red, a verdict of Appendix A differs from what you observe, an existing pin goes red, a count differs from section 2, a runner does not print its "fixtures within" lines, a mutant survives or is not restored: STOP and report the exact command and output; do not repair around it.
Before you stop: `lake-build.sh <wt>/leanncd Tests JaxExperiment` (expect 8846 jobs, 0 errors; no new Lean module), `lake-build.sh <wt>/leanncd IndexedExecutionExperiment` (expect 8729 jobs, 0 errors, as observed on the patch; background, over ten minutes), `check-lean-drivers.sh` (expect `all eight drivers ran clean`), and `run-evalplan-nonlin.sh` ONCE on the final tree (expect 65 binary64 and 56 binary32 within tolerance). One read-only review of your own diff, two lenses: WRONGLY ACCEPTS (can any row the predicate admits address an unwritten slot? multi-axis scans; a row wider than `iterationShape`; a zero-extent position; a positive coefficient on a position that is also a context position) and WRONGLY REJECTS (a read the strict rule admitted that the new rule refuses: the oracle's "strict is a special case" guard says none within its grid; look beyond it).
Records: section 29 of `papers/semantics/jax_scan_record.md` (the rule and its soundness argument, the oracle grid, the verdict tables, programs, observed counts, traps, seeds and binary32 candidates with errors, gaps, headroom, both mutation tables, deviations, call counts, parked items) and, as correction pointers, in section 26 (the P2 row and the "Next" paragraph) and in the "Parked capability work" paragraph of section 27; the bridge README (one paragraph next to the layers-time one; fix the fixture counts to what the runner prints); `papers/semantics/jax_grid_scan_scope.md` (the "Reads allowed" row of the terminology table: window reads; one line in the options list); `leanncd/LeanNCD/Eval/Plan/AGENTS.md` (the `Scan.lean` row and the hand-extended site list: add `causalAdvancingRowIn`/`maxSlotOffset`/`stateReadCausalIn` and say the strict pair is kept for the profile door); the docstring of `Scan.lean` that is the authority for the causality rule; `papers/ref_align_prototype_notes.md` (one line: the reference also accepts free-axis reads); `papers/semantics/categorical_affine_scan_alignment_handoff.md` line "Temporal state reads" and its plan (the profile door keeps the strict rule). Value-grep the repo for `stateReadCausal` and `causalAdvancingRow` and fix or list every prose claim that says the rule is only "coefficient one, non-positive bias".
Stop: commit the work (one commit per work item, both mutation tables as empty commits, the record), leave `git status --short` empty, and STOP at "READY FOR WHOLE-BRANCH REVIEW" on the branch `jax-kv-window-exec`. Do NOT merge, do NOT push, do not delete the worktree or branch. Side issues: write them in the record as parked with a one-line cost; do not start them.
Final message to the owner: base commit and branch tip; commit hashes with subjects; section 2's observations against what you see; the oracle and verdict results; the pin results with observed maxima per precision and the binary32 headroom; both mutation tables; the verification results with counts (including `IndexedExecutionExperiment` base vs tip); deviations; parked items with cost; call counts per session and the method; every skipped step or STOP; confirmation that nothing was merged or pushed.

## Appendix A. The patch, the oracle, the verdicts

### A.1 Production patch (apply exactly)

`leanncd/LeanNCD/Eval/Plan/Scan.lean`: insert this block IMMEDIATELY BEFORE the docstring line `/-- A raw `RawScanPlan` violates a scan-level invariant.` (that is right after `stateReadCausal`, which is NOT edited):
```lean
/-- The LARGEST slot-offset a read row can address above the scan position over the term's iteration
    box: `bias + sum over positions p /= ctxPos with c_p > 0 of c_p * (shape_p - 1)`. Every position
    ranges over `[0, shape_p)`, so a non-positive coefficient only lowers the slot and a positive one
    contributes at most `c_p * (shape_p - 1)`. -/
def maxSlotOffset (shape : Array Nat) (row : Array Int) (bias : Int) (ctxPos : Nat) : Int :=
  (List.range row.size).foldl (fun acc p =>
    if p != ctxPos && row.getD p 0 > 0
    then acc + row.getD p 0 * (Int.ofNat (shape.getD p 1) - 1) else acc) bias

/-- Extent-aware causality of one read row (the strict `causalAdvancingRow` is the special case of no
    other nonzero coefficient): the coefficient at the row's own context position is exactly `1`, no
    OTHER context position is referenced, and `maxSlotOffset <= 0`, so every slot the read can address
    is `<= t` (already written, or below `0` and zero-padded). -/
def causalAdvancingRowIn (shape : Array Nat) (ctxAll : Array Nat) (row : Array Int) (bias : Int)
    (ctxPos : Nat) : Bool :=
  row.getD ctxPos 0 == 1 &&
  (List.range row.size).all (fun p => p == ctxPos || row.getD p 0 == 0 || !ctxAll.contains p) &&
  decide (maxSlotOffset shape row bias ctxPos ≤ 0)

/-- `stateReadCausal` with the term's iteration extents: the rule the two production call sites use. -/
def stateReadCausalIn (shape : Array Nat) (advancingDims : Array Nat) (contextPos : Array Nat)
    (f : ReadPlan) : Bool :=
  advancingDims.size == contextPos.size &&
  (Array.range advancingDims.size).all (fun i =>
    causalAdvancingRowIn shape contextPos (f.map.coeffs.getD (advancingDims.getD i 0) #[])
      (f.map.bias.getD (advancingDims.getD i 0) 0) (contextPos.getD i 0))

```
Call site 1, `Scan.lean` (in `checkScanCore`): replace `unless stateReadCausal st.advancingDims t.contextPos f do` by `unless stateReadCausalIn t.iterationShape st.advancingDims t.contextPos f do`.
Call site 2, `leanncd/LeanNCD/Eval/Plan/Compile.lean` (Phase 5): replace `unless stateReadCausal (stateAdvDims.getD si #[]) t.contextPos f do` by `unless stateReadCausalIn t.iterationShape (stateAdvDims.getD si #[]) t.contextPos f do`.
Each old string occurs exactly once (check with `rg -c`). The error constructors `causalityFailure` and `stateReadNotCausal` are unchanged.

### A.2 The oracle (new Part at the end of `ScanTest.lean`, inside its namespace; prefix `ec`)
```lean
/-- Every point of the box `[0, shape_0) x [0, shape_1) x ...`, position 0 first. -/
def ecBoxPoints : List Nat → List (List Nat)
  | [] => [[]]
  | e :: rest => (List.range e).flatMap fun v => (ecBoxPoints rest).map (v :: ·)

/-- The slot a row addresses at box point `x`. -/
def ecSlotAt (row : Array Int) (bias : Int) (x : List Nat) : Int :=
  x.zipIdx.foldl (fun a (v, p) => a + row.getD p 0 * (v : Int)) bias

/-- SAFE by definition: every box point addresses a slot `<=` its own scan coordinate. -/
def ecBruteSafe (shape : Array Nat) (row : Array Int) (bias : Int) (ctxPos : Nat) : Bool :=
  (ecBoxPoints shape.toList).all fun x => decide (ecSlotAt row bias x ≤ (x.getD ctxPos 0 : Int))

/-- 3 positions (0 = scan axis, 1 and 2 free), scan coefficient in {-1,0,1,2}, free coefficients and
    bias as below, every extent in 1..3. -/
def ecCases : List (Array Nat × Array Int × Int) := Id.run do
  let mut out := []
  for e0 in [1, 2, 3] do
    for e1 in [1, 2, 3] do
      for e2 in [1, 2, 3] do
        for c0 in [(-1 : Int), 0, 1, 2] do
          for c1 in [(-2 : Int), -1, 0, 1, 2] do
            for c2 in [(-2 : Int), -1, 0, 1, 2] do
              for b in [(-4 : Int), -3, -2, -1, 0, 1, 2, 3, 4] do
                out := (#[e0, e1, e2], #[c0, c1, c2], b) :: out
  return out

#guard ecCases.length == 24300
-- SOUNDNESS: whatever the predicate accepts is safe.
#guard ecCases.all fun (shape, row, b) =>
  !causalAdvancingRowIn shape #[0] row b 0 || ecBruteSafe shape row b 0
-- EXACTNESS inside the class it decides (scan coefficient 1): the bound is tight, not merely sufficient.
#guard ecCases.all fun (shape, row, b) =>
  row.getD 0 0 != 1 || (causalAdvancingRowIn shape #[0] row b 0 == ecBruteSafe shape row b 0)
-- NON-VACUITY: the grid has many accepted and many refused rows of that class.
#guard (ecCases.filter fun (shape, row, b) => row.getD 0 0 == 1 && causalAdvancingRowIn shape #[0] row b 0).length > 1000
#guard (ecCases.filter fun (shape, row, b) => row.getD 0 0 == 1 && !causalAdvancingRowIn shape #[0] row b 0).length > 1000
-- CONSERVATIVE outside the class: a scan coefficient other than 1 is always refused (constant, scaled reads).
#guard ecCases.all fun (shape, row, b) =>
  row.getD 0 0 == 1 || !causalAdvancingRowIn shape #[0] row b 0
-- THE STRICT RULE IS A SPECIAL CASE.
#guard ecCases.all fun (shape, row, b) =>
  !causalAdvancingRow row b 0 || causalAdvancingRowIn shape #[0] row b 0
-- ANOTHER context position (multi-axis scans) is never referenced.
#guard ecCases.all fun (shape, row, b) =>
  row.getD 1 0 == 0 || !causalAdvancingRowIn shape #[0, 1] row b 0
```
All guards passed on the patched tree (14 s; the probe file imported only `LeanNCD.Eval.Plan.Scan` and used the unprefixed names). A guard that the grid cannot fail is vacuous: the two non-vacuity guards and the mutant results of observation 2 are what show it is not.

### A.3 Raw-plan pins (`ScanTest.lean`, after the Part 4 deep-history fixtures; donors `deepHistoryScan`, `stepReadG`, `stepAssignG`, `stepBlockG`, `outerSigsDeepHistory`)
```lean
def winScan (coeffs : Array Int) (bias : Int) (w : Nat) : RawScanPlan :=
  let read : ReadPlan := { stepReadG with map := { coeffs := #[coeffs], bias := #[bias] } }
  let term : TermPlan := { iterationShape := #[4, w], contextPos := #[0], outputPos := #[], reductionPos := #[1], factors := #[.read read] }
  { deepHistoryScan with stepBlock := { stepBlockG with steps := #[.assign { stepAssignG with terms := #[term] }] } }
```
`checkScanPlan outerSigsDeepHistory (winScan coeffs bias w)`, observed on the patched tree: `winScan #[1, 1] (-1) 2` ACCEPT (`G[l + j - 1]`); `winScan #[1, 1] 0 2` REJECT `causalityFailure 0 0 0 0` (`G[l + j]`, reads slot `l + 1`); `winScan #[1, -1] 0 2` ACCEPT (lag, negative coefficient); `winScan #[1, 2] (-2) 2` ACCEPT (max offset 0); `winScan #[1, 2] (-1) 2` REJECT (max offset 1); `winScan #[2, 1] (-3) 2` REJECT (scaled scan axis); `winScan #[0, 1] 0 2` REJECT (no scan axis); the unchanged `deepHistoryScan` ACCEPT. Pin each with `#guard (match ... with | .ok _ => true | .error _ => false)` or `... | .error e => e == .causalityFailure 0 0 0 0`.

### A.4 Source-level pins (`ScanCompileTest.lean` section 2.7; the `rej` playground already declares `axJ` with extent 2 and `iter l = 3`)
```lean
def winStmt (e : IdxExpr) : Stmt := .assign "S" [.iterNext axL]
  { body := { terms := [{ factors := [.read "S" [e]] }] }, nonlin := .identity }
```
`rej [okBase] [winStmt e]`, observed: `.affine (-1) [(1, axL), (1, axJ)]` (`S[l + j - 1]`) `none`; `.affine 0 [(1, axL), (-1, axJ)]` (`S[l - j]`) `none`; `.affine 0 [(1, axL), (1, axJ)]` (`S[l + j]`) `some (.scan (.stateReadNotCausal "sc" "S" 0 0 0))`; `.axis axJ` (`S[j]`) the same; `.affine (-3) [(2, axL), (1, axJ)]` the same; `.shift axL (-1)` `none`; `.shift axL 1` the same refusal.

### A.5 Value pins (end of `NonlinCompileTest.lean`; `diffEqB` checks the source-compiled checked plan AND the reference evaluator)
```lean
#guard diffEqB (tlprog!{ iter t = 5
      axis j : ℕ = 2
      tensor f64 H0(d), F(d, t)
      F[d, 0]     := H0[d]
      F[d, t +1]  := F[d, t + j - 1] })
    (HashMap.ofList [("H0", tl [3] [1, 2, 3])])
    "F" (tl [3, 5] [1,1,2,3,5, 2,2,4,6,10, 3,3,6,9,15])
```
(`F[t+1] = F[t-1] + F[t]`: Fibonacci per row; the scratch probe needed `open Std` for `HashMap`.) The second guard is the same with `F[d, t - j]` and the same expected table. Both passed.

## Appendix B. The fixtures (probed 2026-11-25, binary64; drop the `f64` tag for the binary32 siblings)

### B.1 Data (one definition shared by 64 and 32; `gqaGen` and `gT` as in the earlier fixtures)
`X = [6, 3]` of `gqaGen 1.0 15 ++ #[0.0, 0.0, 0.0]` (row 5 is exactly 0.0); `Wq = gT 2.0 [4, 3]`; `Wk = gT 3.0 [4, 3]`; `Wv = gT 4.0 [2, 3]`; `K0 = gT 5.0 [4]`; `V0 = gT 6.0 [2]`; `Y0 = zeros [2]`; `Mk = [5, 6]`: `kv_window` entry `n` (= `6 u + t`) is `0.0` if `n % 6 + n / 6 >= 4` else `-1.0e9`; `kv_lag` entry is `0.0` if `n % 6 >= n / 6` else `-1.0e9`.

### B.2 Programs
```
-- kv_window  (kv_lag: replace  t + u - 4  by  t - u  in BOTH reads)
iter t = 6
axis u : ℕ = 5
tensor f64 X(t, i), Wq(k, i), Wk(k, i), Wv(v, i), K0(k), V0(v), Y0(v), Mk(u, t)
tensor f64 Kh(k, t), Vh(v, t), Yh(v, t), Kn(t, k), Vn(t, v), Qr(t, k), Sc(u), Pa(u), Yo(v)
Kh[k, 0]      := K0[k]
Vh[v, 0]      := V0[v]
Yh[v, 0]      := Y0[v]
Kn[t, k]      := Wk[k, i] · X[t, i]
Vn[t, v]      := Wv[v, i] · X[t, i]
Qr[t, k]      := Wq[k, i] · X[t, i]
Sc[u]         := Kh[k, t + u - 4] · Qr[t, k] + Mk[u, t]
Pa[u.]        := softmax(Sc[u])
Yo[v]         := Pa[u] · Vh[v, t + u - 4]
Kh[k, t +1]   := Kn[t, k]
Vh[v, t +1]   := Vn[t, v]
Yh[v, t +1]   := Yo[v]
```
### B.3 Where the numbers come from
Scratch files of the probe (may be cleared): `/private/tmp/claude-501/-Users-williammacready-code-python-pyncd/a5212c88-e42b-4a66-9915-873d83efe496/scratchpad/` `kvw_probe.lean` (the two programs through every stage), `kv_check.py`, `kv_pert.py` (the numpy model, gradients, perturbations), `oracle_test.lean`, `oracle_mut.lean`, `raw_probe.lean`, `src_probe.lean`, `fib_probe.lean`. Do not rely on them; reproduce what you need from this brief.

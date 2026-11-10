# Session brief: cross-attention (external memory, unequal extents) inside the layer scan (JAX bridge)

Status: not started. Written 2026-11-10 at main `b93602d3` (local; `origin/main` is 3 commits behind it, nothing here depends on those). Process weight: Direct path
(`.claude/skills/slice-plan/` section 0): tests and fixtures only, no production change. A scratch probe on 2026-11-10 answers the "is it expressible" question for the
forms this brief uses and found one trap (section 2). If any NEW pre-flight answer needs an emitter, runtime, grammar or checker change, STOP and report (do not edit
`EvalPlanCodegen.lean`, `evalplan_affine_runtime.py`, `LeanNCD/DSL/*` or `LeanNCD/Eval/Plan/*`; that is a different process weight and the user's call). CLAUDE.md applies, in
particular Rule 13 (worktree, merge to LOCAL main, do not push unless asked), Rule 14 (scope gate) and Rule 6 (budgets). Siblings: `jax_gqa_session_brief.md` (landed; record sections
15 to 17 of `papers/semantics/jax_scan_record.md`), `jax_multiquery_session_brief.md` (section 13) and `jax_predicate_masks_session_brief.md` (section 12): same harness, same pin style,
same hand-mutant discipline.

## 1. Goal

Every attention fixture so far attends within ONE sequence: queries, keys and values all come from the layer state, so the query and key extents are equal (q = s). Cross-attention
(the decoder half of an encoder-decoder transformer) lets the layer state attend to an EXTERNAL memory `Mem[t, m]` that is not the scan state, with its own extent `t ≠ q`, and with
no causal mask. Three structural ideas are new: (i) unequal query and memory extents, (ii) a read of an external tensor that carries no layer axis from inside the scan, (iii) an
unmasked softmax over the memory axis inside the scan. The model is one decoder layer = self-attention (the standard one), then a cross-attention sub-block, then the MLP, scanned over
layers with untied per-layer weights.

Not in scope (park with a one-line cost if you find more): a causal or padding mask on the cross-attention (keep it unmasked), grouped or multi-query cross-attention, positional
information on the memory, an encoder (the memory is an input), depth beyond two steps, cross-attention in the head fixture, scatter or affine writes inside the scan (section 17 of the
record: refused), changing any existing fixture, the Python runtime, the emitter, the mutation manifests.

## 2. What exists (verify each before relying on it) and the probe findings

- Standard program `scanProg` / `scanProg32` @ `leanncd/experiments/jax_bridge/EvalPlanNonlinSmoke.lean` (~597, ~627), `scanStack` ~595, `gainStack` ~668, `scanWeights` ~670,
  `scanEnv64` / `scanEnv32` ~680 / ~683; the mask fixtures' inputs `maskX` (q = 5), `maskEps`, `maskEnv64` / `maskEnv32` ~1091-1097; the GQA block ~1170-1390 (`gqaGen seed n` =
  `0.6 * sin (seed + 1.7 i)` ~1358, `gqaRep`, `gqaEnv64`, `gqaProg`). Registrations are in `corpus64` / `corpus32` (~1434 / ~1495):
  `fixture64 "<name>" prog env minPw minAw (some (19, 1, 1)) true (scans := 1)`; `exact := none` is allowed. Driver `evalplan_nonlin_smoke.py`: `np_transformer` ~143 (do NOT edit it), `np_state`,
  `check_np`, `MODEL_TOL`, `TRANSFORMER_FIXTURES` ~48, `gqa_fixture_pins` ~492 (the pin style to copy), `fixture_grad_pins` ~736 with `canon_heads`, `GRAD_FIXTURES`, `GRAD_TOL`, `GRAD_FD_TOL`.
- Baseline gates on current main: `lake-build.sh <wt>/leanncd Tests JaxExperiment` = 8846 jobs, 0 errors (re-verify); `run-evalplan-nonlin.sh` = 41 binary64 and 33 binary32 fixtures
  within tolerance, including the gradient pins of section 16. binary32 headroom is thin for some fixtures (standard scan under 10%, sink 1.2x, GQA 1.7x): REPORT the headroom of every new
  binary32 fixture; do not loosen any tolerance.
- **Probe findings (scratch, 2026-11-10, a copy of the fixture file with a probe `main`, both precisions; nothing below is a pin yet).** Decoder layer on the standard self-attention
  inputs (q = s = 3, h = k = 2), memory `Mem[t = 5, m = 4]`, cross head width `j = 6`, `W_Qc`, `W_Kc`, `W_Vc` of shape `[3, 2, 6, 4]` and `W_Oc` `[3, 4, 2, 6]` (each stacked by `scanStack`,
  so layer 2 is NaN), `Gc[3, 4]` by `gainStack`, `Scx` = 1 / sqrt 6, weights by `gqaGen`. The program text that ran (f64; the `32` sibling re-declares only `axis s`, `H`, `S` and `Sx`):
  ```
  tensor f64 W_Qc(l, h, j, m), W_Kc(l, h, j, m), W_Vc(l, h, j, m), W_Oc(l, m, h, j), Mem(t, m), Gc(l, m), Scx()
  tensor f64 Qc(q, h, j), Kc(t, h, j, l), Vc(t, h, j, l), Sx(h, q, t), Ac(q, h, j), Ax(q, m)
  ...                                    (self-attention exactly as scanProg, ending R1 := H + Attn)
  Ssc[q]           := R1[q, m] · R1[q, m] · Inv[m]
  Vq[q]            := Ssc[q] + Eps[q]
  Sdc[q]           := sqrt(Vq[q])
  Nc[q, m]         := R1[q, m] / Sdc[q] · Gc[l, m]
  Qc[q, h, j]      := W_Qc[l, h, j, m] · Nc[q, m]
  Kc[t, h, j, l]   := W_Kc[l, h, j, m] · Mem[t, m]
  Vc[t, h, j, l]   := W_Vc[l, h, j, m] · Mem[t, m]
  Sx[h, q, t.]     := softmax(Qc[q, h, j] · Kc[t, h, j, l] · Scx[])
  Ac[q, h, j]      := Sx[h, q, t] · Vc[t, h, j, l]
  Ax[q, m]         := W_Oc[l, m, h, j] · Ac[q, h, j]
  R2[q, m]         := R1[q, m] + Ax[q, m]
  ...                                    (MLP as scanProg with R2 in place of R1: Ss2, N2 and the residual H[l+1] := R2 + Y)
  ```
  (`Vec` is avoided as a tensor name; `t` and `j` are fine axis names; an UNMASKED softmax is `Sx[h, q, t.] := softmax(...)` with no `where`.) Findings: it parses, typechecks, prepares
  (ONE scan record, 2 steps, flat steps 33 = 30 assign + 1 pointwise + 2 axiswise), runs in Dense and renders for JAX, in both precisions. `H` equals an independent float64 numpy model written from the
  English definition to 6.3e-16 (binary64, Lean, eager and jit) and 2.0e-7 (binary32, Lean, eager and jit; headroom 5x against `MODEL_TOL` 1e-6, with the generator seeds (1, 2, 3, 4) NOT tuned).
  The numpy `H` differs by 1.02 from the same model without the cross block, and by 0.056 under `Mem[4] += 0.5`; REVERSING the memory rows changes it by exactly 0.000 (attention over memory
  is permutation-invariant in `t`: reversal is NOT a usable non-vacuity test).
- **The trap (probe, binary64, same inputs).** Written the obvious way, with `Kc(t, h, j)` and `Kc[t, h, j] := W_Kc[l, h, j, m] · Mem[t, m]` (and the same for `Vc`), the plan is
  `['assign', 'assign', 'scan']` and the materialized outputs are `[Kc, Vc, H]`: a statement that reads NO scan state is not a per-step intermediate, so it runs once BEFORE the scan with `l` an
  ORDINARY axis, summed over all three stacked layers, and the step reads that single table. Lean, eager and jit all agree, and `H` is entirely NaN, because the sum reaches the NaN
  layer-2 slice. With a finite layer 2 it would be silently wrong, not NaN. This is the ordinary-axis semantics that section 10 of the record documents for POST-scan statements; whether this PRE-scan
  placement of a state-independent statement is documented anywhere was not checked (verify it, and note in the record if it is not). It is consistent semantics, not a crash, and needs no code change. The working form gives the table an explicit layer
  axis (`Kc[t, h, j, l]`, read as `Kc[t, h, j, l]` in the step), which is a pre-scan statement producing a stacked table, like the weight stacks. Consequence: `Kc` and `Vc` are then EXPORTED
  (materialized) with a NaN layer-2 slice, so the "exactly `H` is exported" pin of the earlier fixtures becomes "exactly `H`, `Kc`, `Vc`".
- **NOT probed:** gradients (in particular the gradient with respect to `Mem`, an external input read through a stacked table); a memory extent equal to another extent; a memory with a different model width;
  the exported `Kc`, `Vc` against numpy (the probe compared only `H`); mutants.

## 3. What to build

TWO new scan-only programs, each registered in both precisions (4 fixtures; expected differential: 43 binary64 and 35 binary32 if both are added).

Extents: choose them so that q (= s), t, h, k and j are pairwise distinct, so no axis-order bug can hide behind equal extents on `S`, `Sx`, `K`, `Kc`, `AttnOut`, `Ac`, `W_O` or `W_Oc`.
The probe's h = k = 2 came from reusing the standard weights; do NOT reuse them. Candidate: q = s = 5 (`maskX`, `maskEps`, `axis s : ℕ = 5`), t = 7, h = 3, k = 2 (so `Sc` = `trSc` = 1 / sqrt 2 still
holds), j = 6 (`Scx` = 1 / sqrt 6), m = d = 4, all head-specific weights generated by `gqaGen` with distinct seeds and stacked by `scanStack` (self-attention `W_Q`, `W_K`, `W_V` `[3, 3, 2, 4]`,
`W_O` `[3, 4, 3, 2]`; cross `W_Qc`, `W_Kc`, `W_Vc` `[3, 3, 6, 4]`, `W_Oc` `[3, 4, 3, 6]`), `Mem` by `gqaGen` (not stacked, `[7, 4]`), `Gc` by `gainStack`, the MLP weights, gains, `Inv`, `Eps`, `X`
from the mask fixtures' environment. Confirm by typecheck and run; change them if a pair collides or conditioning forces it. ONE definition of each weight stack shared by both programs.

1. `transformer_cross` / `transformer_cross32`: the working program of section 2 (explicit layer axis on `Kc`, `Vc`).
2. `transformer_cross_hoisted` / `transformer_cross_hoisted32`: the NAIVE form (`Kc(t, h, j)`, no layer axis), documenting the trap as a pinned semantics. It must use `W_Kc`, `W_Vc` stacks whose
   layer 2 is FINITE (a separate stack for this fixture only: a NaN layer 2 makes `H` NaN, which every fixture's finiteness gate rejects), so that the result is finite and silently different from
   per-layer cross-attention. Pins: the plan is two plain assigns then ONE scan; `Kc`, `Vc` have no layer axis; `H` equals a numpy model whose cross K/V are `einsum("lhjm,tm->thj", W_Kc, Mem)` (summed
   over ALL THREE layers, layer 2 included); and it differs from the per-layer model by more than 1e-2. If the budget forces a cut, ship (1) and park (2), saying so.

## 4. Pins (all independent of Lean's values) and mutants

Python, in the driver, one helper `cross_fixture_pins` called once per precision. Write a NEW numpy model `np_cross_transformer` (self-attention, the cross block, the MLP, from the English
definition, float64, from the exported inputs only); do not edit `np_transformer`.
1. Value pin: `H` (layers 0 to 2) of `transformer_cross` equals the numpy model on the Lean, eager and jit views at `MODEL_TOL`; the exported `Kc`, `Vc` equal the numpy tables in layers 0 and 1 and are
   NaN in layer 2; report observed maxima per precision.
2. Non-vacuity: numpy `H` differs by more than 1e-2 from (a) the model without the cross block, (b) the model with EVERY memory row perturbed (not reversed: reversal is invariant), and each single memory row's
   perturbation moves `H` by more than 1e-3 (so no memory position is ignored; scale `Mem` if the probe's 0.056 is too small at the new extents), (c) the model whose cross K and V are taken from the layer state instead of the memory.
3. Exports: exactly `H`, `Kc`, `Vc` are exported on every view; `H` finite on every view.
4. Inputs: every input other than the head weights, `Mem`, `Gc`, `Scx` and `Sc` is bitwise the mask fixtures'; `Sc` = 1 / sqrt(k of `W_Q`) and `Scx` = 1 / sqrt(j of `W_Qc`) from the input shapes; layer-2 slices NaN
   and layers 0, 1 finite and distinct in EVERY weight stack (`W_Qc`, `W_Kc`, `W_Vc`, `W_Oc`, `Gc` included).
5. Distinct extents: assert that q, t, h, k, j are pairwise distinct from the input shapes.
6. Hoisted program (if built): the pins of item 3 of section 3.
7. Keep the existing pins untouched and green.

Gradients (Part B, after Part A is green; cut it first if the budget forces a cut): add `cross` to the gradient family of `fixture_grad_pins` (section 16): `jax.grad` of `L = sum(C * H[:, :, 2])` over every float input
INCLUDING `Mem`, against a pure-JAX model (extend the model in that function with the cross block; no plan, no scan) and finite differences of `np_cross_transformer`; layer-2 weight slices exactly zero; `Mem` gradient finite and
non-trivial (`max |g| > 1e-3`), and nonzero in every memory row. Report headroom.

Hand mutants (edit the f64 `crossProg`-style program text of `transformer_cross`, run `run-evalplan-nonlin.sh`, name the first failing assertion, restore with `git checkout -- <file>` AFTER committing the work,
`git diff --stat` empty; BSD `sed -i '' -e ...` needs the empty suffix argument first). Each must keep EVERY input used AND be accepted by the shape solver (a refused mutant is not a kill). Suggested:
A. `Kc` reads `W_Vc` and `Vc` reads `W_Kc`; B. the cross softmax gains a mask, `softmax(where t ≤ q)(...)`; C. the cross score applies the scale twice, `· Scx[] · Scx[]` (dropping `Scx` or swapping in `Sc[]` would leave an input unused); D. `R2 := H[q, m, l] + Ax[q, m]`
(skip the self-attention residual; `R1` stays used through `Nc`); E. drop the layer axis from `Kc` (the naive form: `H` goes NaN on the NaN-stack fixture, killed by the finiteness / value pin, and it exercises the trap);
F. data: `Mem` replaced by zeros (the value pin passes because numpy follows the same inputs; the non-vacuity pin of item 2 must be the one that fires); G. one mutant on the binary32 sibling (B on `crossProg32`; the f64 leg
runs green first). A mutant that reads the layer state for the memory (`Kc[t, h, j, l] := ... N1[t, m]`) should be refused by the extent mismatch (t ≠ q; not run, check it), and a refusal is not a kill. Compute the non-vacuity gaps BEFORE the
view loop, as `gqa_fixture_pins` does, so that the data mutant F fails on item 2 and not on the value pin. If a mutant SURVIVES, stop and report it with the exact edit.
Record the table in the body of an empty commit.

## 5. Process, harness facts, budgets

- Worktree (Rule 13): `EnterWorktree`, then `bash .claude/skills/new-slice/prepare-worktree.sh` (it fast-forwards the branch to local main). Then `mkdir -p <wt>/leanncd/experiments/jax_bridge/.cache` and
  `ln -s /Users/williammacready/code/python/pyncd.worktrees/task4-boolean-output/leanncd/experiments/jax_bridge/.cache/python <wt>/leanncd/experiments/jax_bridge/.cache/python` (verify it exists; never commit the
  link). STALE-OLEAN TRAP: run `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd JaxExperiment` once before any scratch probe.
- Plain, separate shell commands only (no `cd x && y`, no `$VAR`, no `;`/`$?` chains); absolute paths; `/usr/bin/git -C <wt>`. A worktree-isolated session refuses `git -C` into the primary checkout and compound commands. Stage
  by explicit path; never `git add -A` (the primary checkout may hold another session's uncommitted files). `ExitWorktree` (keep) before merging from the primary.
- To run a scratch Lean file: copy `EvalPlanNonlinSmoke.lean` to the scratchpad, add the programs before `end JaxBridge.NonlinSmoke`, rename the old `main` (`mainOld`) and add a `main` outside the namespace
  (`open JaxBridge.NonlinSmoke in def main ...`), then `/Users/williammacready/.elan/bin/lake +leanprover/lean4:v4.30.0 -d <wt>/leanncd env lean --run <file> <out64> <out32>`; WITHOUT the toolchain pin elan fails with
  "incompatible header". `lean-file.sh <wt>/leanncd experiments/jax_bridge/EvalPlanNonlinSmoke.lean` typechecks the fixture file (`JaxExperiment` does NOT compile it). Reuse `fixture64` / `fixture32` in the scratch `main`
  to write generated modules, then run the driver's helpers on them (the probe did this with a scratch numpy checker).
- Measure the binary32 error against numpy BEFORE fixing the generator seeds (JAX eager on the generated 32 fixture with Python-side regenerated weights, as in the GQA slice: a scratch script, no Lean rebuild per candidate), report
  every candidate tried, and never loosen a tolerance. The GQA slice's baseline seeds failed at 3.6e-6 and 12 of 42 candidates exceeded `MODEL_TOL`; the probe's untuned seeds gave 2.0e-7 at smaller extents, so do not assume either.
- Harness traps: `Array.extract start stop` takes the END index; a tensor name `C` collides with a `C(` token (use two letters); `Vec` is avoided; every runtime mutant of the gradient pins is a python-only run on the cached generated
  fixtures (`python evalplan_nonlin_smoke.py float64 <gen64>`), while every program mutant needs the whole `run-evalplan-nonlin.sh` (it regenerates the Lean fixtures first).
- NEVER write wait loops, `pgrep` monitors, `time.sleep` polling or driver scripts: run builds and the differential with `run_in_background` and wait for the notification. The differential aborts at the FIRST failed assertion
  and takes a few minutes; batch edits and run it as few times as possible. Never run two Lean builds or runs at once.
- Do not edit `EvalPlanCodegen.lean`, `ScanAffineEmitTest.lean`, `ExecutableTest.lean`, `ScanJaxGateTest.lean`, the mutation manifest JSON files, `evalplan_affine_runtime.py` (except as a scratch gradient mutant, restored) or `LeanNCD/*`;
  do not touch the existing fixtures, programs, environments, `np_transformer` or assertion texts.
- Budgets (Rule 6): a dispatch is at most about 60 harness-counted tool calls and about 250k context; report the HARNESS count if you delegate. The GQA slice was inline, about 85 calls with 5 mutation runs; this one has a new numpy model,
  two programs and seven mutants, so plan for more. Split if you delegate: A = Lean programs, envs, registrations, typecheck and one runner run; B = Python pins; C = mutants, docs, verification; D = Part B gradients. If the budget
  forces a cut, ship `transformer_cross` with pins 1 to 5 and park the hoisted fixture and Part B, saying so.

## 6. Verification before merging (you run it, not a subagent)

`bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd Tests JaxExperiment` (expect 8846 jobs, 0 errors; no new Lean module) and `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh` ONCE on the final tree (expect 43 binary64 and 35
binary32 fixtures if both programs are added, 41 and 33 plus 2 and 2 otherwise). One read-only whole-branch review by code reading of the diff: look for pins that a trivial or perturbed entry satisfies by itself (a numpy model that
shares a bug with the program, a non-vacuity test that is permutation-invariant, a gradient pin whose reference reuses the plan's own table). Re-check `main` before merging (merge main into the branch if it moved; check incoming Lean
files with `rg -l "CompileError|finalizeScans|prepareEvalPlan|evalScheduled"`). Merge to LOCAL main, delete the branch, remove the worktree. Do NOT push unless asked (the lean4 guardrail hook blocks `git push`; after an explicit request
use the one-time prefix `LEAN4_GUARDRAILS_BYPASS=1`).

## 7. Records

Add section 18 to `papers/semantics/jax_scan_record.md` (the programs, the probe findings and which became pins, the extents and why, the weight-generator candidates with their binary32 errors, observed numpy-pin differences and
binary32 headroom, the trap and its pinned form, the mutation table, anything parked) and one paragraph in the bridge README next to the GQA paragraph; value-grep the README and the record for stale statements ("exactly `H` is exported",
"every scan fixture has q = s", "every fixture's scan statements read the state"). Add a pointer from the section 10 text on the role-based rule to the hoisting finding (and see the note on documentation in section 2). Update the memory index entry if you keep one.

## 8. Done when

Cross-attention pinned on Lean, eager and jit with observed values; the hoisting trap pinned (or parked with a reason); every mutant killed by a NAMED assertion (or a survivor reported); `Tests` + `JaxExperiment` green; differential green with the
stated counts; record and README updated; review clean or adjudicated; merged to local main; worktree and branch removed. Report faithfully: observed values, the mutation table, tool-call counts, anything unverified or skipped.

## 9. After this slice

The progression agreed 2026-11-09 continues (each step adds one structural idea; every one needs its own pre-flight probe): 1-D convolution and a patch embedding (affine reads and strides); a GRU or LSTM over a time axis (scan over time,
several states, gates); linear attention or a diagonal state-space model (matrix state); a GNN (dense, then scatter-add over edges at the top level, which is admitted); dense mixture of experts; the logic side (Viterbi max-plus, Boolean
reachability; Lean-side only today); layers x time (nested scans, a KV cache; the scan-local multi-axis write refusal of section 17, `multiAxisScatterLhs`, is the first thing to revisit there). Parked from this thread: depth (item 6a, mostly a
float32 measurement); `/` in index expressions as an elaboration-time desugaring; per-layer mask alternation (probably a runtime change: ask first); the binary32 plan noise relative to a float32 numpy emulation (cause unconfirmed); gradients through
`transformer_head`, scatter nodes and `scatter_mode="fast"`; promoting the runtime gradient mutants to the Python manifest.

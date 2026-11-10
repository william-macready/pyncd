# Session brief: grouped-query attention fixtures in the standard transformer scan (JAX bridge)

Status: not started. Written 2026-11-09 at main `ca75138c` (pushed). Process weight: Direct path
(`.claude/skills/slice-plan/` section 0): tests and fixtures only, no production change. The pre-flight below was run as a
scratch probe on 2026-11-09 and answers the "is it expressible" question for the forms this brief uses. If any new
pre-flight answer needs an emitter, runtime or grammar change, STOP and report (do not edit `EvalPlanCodegen.lean`,
`evalplan_affine_runtime.py` or `LeanNCD/DSL/*`; that is a different process weight and the user's call). CLAUDE.md applies, in particular Rule 13
(worktree, merge to LOCAL main, do not push unless asked), Rule 14 (scope gate) and Rule 6 (budgets). Siblings:
`jax_multiquery_session_brief.md` (landed; record section 13 of `papers/semantics/jax_scan_record.md`) and
`jax_predicate_masks_session_brief.md` (section 12): same harness, same pin style, same hand-mutant discipline.

## 1. Goal

Multi-query attention (section 13) shares ONE key/value head across all query heads. Grouped-query attention shares one
key/value head across each GROUP of query heads: G KV groups, R query heads per group, `G * R` query heads in all, and query head
`h = R * g + r` reads KV group `g`. The question for tensor logic is how the language expresses that head-to-group map. The
grammar has NO division in index expressions (see 2), so the map is written either by SPLITTING the query-head axis into `(g, r)`
or by an AFFINE read `Q[q, R * g + r, k]` of a flat head axis. Both were probed and agree bitwise; this slice pins both inside the
layer scan, plus the standard multi-head plan on replicated weights as a Lean-independent equivalence.

Not in scope (park with a one-line cost if you find more): adding `/` to the grammar (decided 2026-11-09: NOT now; if wanted later
it is an elaboration-time desugaring that splits the axis, because extending `IdxExpr` has a ~130-site blast radius and a
verification cost; ~1 design pass plus a probe), the flat-OUTPUT form (see 2, last bullet), a different mask (keep `softmax(where s ≤ q)`),
depth, gradient pins for the new fixtures, changing any existing fixture, the Python runtime, the emitter, the mutation manifests.

## 2. What exists (verify each before relying on it) and the probe findings

- Standard program `scanProg` / `scanProg32` @ `leanncd/experiments/jax_bridge/EvalPlanNonlinSmoke.lean` (~597, ~627), `scanStack` ~595,
  `scanWeights` ~670, `scanEnv64` ~680, `scanEnv32` ~683; MQA programs `mqaProg` / `mqaProg32` ~1105 with `mqaEnv64` / `mqaEnv32`; the mask
  fixtures use q = s = 5 inputs `maskX`, `maskEps`, `maskEnv64` / `maskEnv32` (~1090-1097). Registrations are in `corpus64` / `corpus32`:
  `fixture64 "<name>" prog env minPw minAw (some (19, 1, 1)) true (scans := 1)`. Driver: `mqa_fixture_pins`, `mask_fixture_pins`,
  `np_transformer`, `check_np`, `MODEL_TOL`, `TRANSFORMER_FIXTURES`, `grad_fixture_pins` @ `evalplan_nonlin_smoke.py`.
- Baseline gates on current main: `lake-build.sh <wt>/leanncd Tests JaxExperiment` = 8846 jobs, 0 errors; `run-evalplan-nonlin.sh` = 38 binary64
  and 30 binary32 fixtures within tolerance. binary32 headroom on `H` against `MODEL_TOL` (1e-6) is thin: standard scan under 10%,
  sink 1.2x, MQA 6.0x. REPORT the headroom of every new binary32 fixture; do not loosen any tolerance.
- **Probe findings (scratch, 2026-11-09, binary64 only, NOT committed; nothing below is a pin yet).** Two full layer-scan programs, 4 query
  heads, 2 KV groups, k = 2, q = s = 3:
  - **P1 (split heads):** `Q[q, g, r, k]`, `K[s, g, k]`, `V[s, g, k]`, `S[g, r, q, s.] := softmax(where s ≤ q)(Q[q, g, r, k] · K[s, g, k] · Sc[])`,
    `AttnOut[q, g, r, k] := S[g, r, q, s] · V[s, g, k]`, `Attn[q, m] := W_O[l, m, g, r, k] · AttnOut[q, g, r, k]`; `W_Q(l, g, r, k, m)`,
    `W_K(l, g, k, m)`, `W_V(l, g, k, m)`, `W_O(l, m, g, r, k)`.
  - **P2 (flat head axis, affine read), the program text that ran:**
    ```
    iter l = 3
    axis s : ℕ = 3
    axis r : ℕ = 2
    tensor f64 X(q, m), W_Q(l, h, k, m), W_K(l, g, k, m), W_V(l, g, k, m), W_O(l, m, h, k)
    ...                                   (everything else exactly as scanProg)
    Q[q, h, k]          := W_Q[l, h, k, m] · N1[q, m]
    K[s, g, k]          := W_K[l, g, k, m] · N1[s, m]
    V[s, g, k]          := W_V[l, g, k, m] · N1[s, m]
    S[g, r, q, s.]      := softmax(where s ≤ q)(Q[q, 2 * g + r, k] · K[s, g, k] · Sc[])
    AttnOut[q, g, r, k] := S[g, r, q, s] · V[s, g, k]
    Attn[q, m]          := W_O[l, m, 2 * g + r, k] · AttnOut[q, g, r, k]
    ```
    (`axis r` MUST be declared: no tensor has an `r` axis, so its extent cannot be inferred.)
  - Both parse, typecheck, prepare, run in Dense, and render; both are ONE scan record, 2 steps, 21 flat nodes = `some (19, 1, 1)`, export `H` only; `H` equals
    an independent numpy model (K/V weights repeated per query head, `h // R` written in Python) to ~6e-16 on Lean, eager and jit; P1 and P2 are BITWISE equal on all three.
    The numpy model differs by 7.96 from a wrong group map (heads swapped across groups) and by 1.11 from one shared group (MQA).
  - **Division does not parse:** `Bb[h / 2, k]` gives `unexpected token '/'; expected ']'` (`tl_idx_expr` allows only numerals, identifiers, `n * ident`, `+`, `-`, parentheses).
  - **Affine WRITES over free axes work OUTSIDE a scan** (Lean, eager and jit equal numpy, each a `scatter` node): `Yy[2 * g + r] := Xx[g]`, `Zz[2 * a + b] := Mm[a, b]`,
    `Yy[2 * h + a, 2 * w + b] := Xx[h, w]`, `Oo[q, 2 * g + r, k] := Ss[g, r, q, s] · Vv[s, g, k]`.
  - **Solver facts you will hit:** a multi-axis affine read is solved as an EXACT span, so `Q[q, R * g + r, k]` is accepted only with stride `R` (span `G * R` = the head extent);
    `g + r` or `R * r + g`-style variants that change the span are REFUSED at prepare ("affine size system inconsistent"), which is not a mutant kill (the span-preserving transposed map `G * r + g` is the usable mutant, section 4).
    Separate partial writers of one tensor are refused ("multi-writer ... expected extent 7, actual 2"); a bare read `Xx[t]` pins `t` to the tensor's extent.
  - **NOT probed:** binary32; the `32` sibling needs `axis r : ℕ = R` re-declared (the MQA sibling re-declares only `axis s` and the `H`, `S` declarations); the flat-OUTPUT form
    `AttnOut[q, 2 * g + r, k] := S[g, r, q, s] · V[s, g, k]` INSIDE a scan (it lowers to a scatter node, and scatter inside a scan was a known gap; probably refused: if you try it, record the
    exact error and park, do not work around); gradients through these plans.

## 3. What to build

THREE new scan-only programs, each registered in both precisions (6 fixtures; expected differential: 41 binary64 and 33 binary32). Extents: choose them so that g, r, k and q (= s)
are pairwise distinct (no axis-order bug may hide behind equal extents on S, K, Q, AttnOut or W_O). Candidate: q = s = 5 (reuse `maskX` and `maskEps`, `axis s : ℕ = 5`), m = 4, d = 4
(as the standard fixture), G = 3, R = 2, k = 7 (so h = 6; `Sc[]` = 1 / sqrt 7 as an input, pinned against `W_Q`'s own k extent in Python like the standard fixture's `Sc` pin). Confirm by typecheck
and run; change them if a pair collides or conditioning forces it.

1. `transformer_gqa` / `transformer_gqa32`: P2 (flat head axis, `Q[q, R * g + r, k]` and `W_O[l, m, R * g + r, k]`, stride `R` = 2 here).
2. `transformer_gqa_split` / `transformer_gqa_split32`: P1 (heads split into `(g, r)`, no index arithmetic).
3. `transformer_gqa_mha` / `transformer_gqa_mha32`: the STANDARD multi-head statements (`scanProg`'s K and V lines, `S[h, q, s.]`, h = G * R) with `W_K`, `W_V` replicated per head,
   `W_K_mh[l, h] = W_K[l, h / R]` (Lean `Nat` division in the env builder, where division exists).

Weights: generate by formula (probe: `0.6 * sin (seed + 1.7 i)`, stacked with `scanStack` for layer 0, derived layer 1, NaN layer 2) so there are no new magic numbers; ONE definition of each stack shared by all
three programs (P1 and P2 take the same bytes: head `h = R * g + r` makes `[g, r, k, m]` and `[h, k, m]` the same storage order; the MHA env is built from the SAME arrays). The binary32 state
is sensitive to the data (MQA: head-0 weights 3.6e-6 against `MODEL_TOL` 1e-6, head 1 gave 1.6e-7): measure the binary32 error against numpy BEFORE fixing the generator parameters, report every candidate you tried,
and never loosen a tolerance.

## 4. Pins (all independent of Lean's values) and mutants

Python, in the driver, one helper `gqa_fixture_pins` called once per precision. `np_transformer` needs NO change: build the multi-head inputs with `W_K = W_K[:, [h // R for h in range(G * R)]]` (the
division is the English definition of the map; it is exactly what the language lacks).
1. Value pin: `H` (layers 0 to 2) of ALL THREE fixtures equals that numpy model on the Lean, eager and jit views at `MODEL_TOL`; report observed maxima per precision.
2. Non-vacuity: numpy GQA `H` differs from (a) multi-head with distinct K/V per head, (b) one shared group (MQA), (c) the wrong group map `h % G` (this is the transposed map of mutant A), each by more than 1e-2; the
   `R` heads of one group attend differently from each other, and the groups differ.
3. P1 vs P2: eager and jit `H` BITWISE equal (and Lean's, if it is; state which); this is the claim that the affine read and the axis split are the same thing.
4. Equivalence: `transformer_gqa` eager `H` equals `transformer_gqa_mha` eager `H` (same weights replicated): bitwise if it is bitwise, with the observed count, otherwise the observed tolerance with the reason.
5. NaN layer-2 slices in every weight stack (including `W_K`, `W_V` of shape `[3, G, k, 4]`), all outputs finite, exactly `H` exported, every input other than the head-specific weights bitwise the mask fixtures'.
6. Distinct extents: assert that g, r, k and q are pairwise distinct from the input shapes. 7. Keep the existing pins untouched and green.

Hand mutants (edit the f64 `mqaProg`-style program text of `transformer_gqa`, run `run-evalplan-nonlin.sh`, name the first failing assertion, restore with `git checkout -- <file>`, `git diff --stat` empty). Each
must keep EVERY input used AND be accepted by the shape solver (a refused mutant is not a kill). Suggested:
A. the S-line read `Q[q, 2 * g + r, k]` to `Q[q, 3 * r + g, k]` (transposed head map, span preserved); B. the `W_O[l, m, 2 * g + r, k]` read to `3 * r + g` only; C. mask `s ≤ q` to `s < q`;
D. `K` reads `W_V` and `V` reads `W_K`; E. (if the solver accepts it) `K[s, g, k] := ... N1[q, m]`. `AttnOut` reading `K` instead of `V` leaves `V` dead and is refused at compile
(`readsPerStepIntermediate`), so it is NOT a kill. If a mutant SURVIVES, stop and report it with the exact edit. Record the table in the body of an empty commit.

## 5. Process, harness facts, budgets

- Worktree (Rule 13): `EnterWorktree`, then `bash .claude/skills/new-slice/prepare-worktree.sh`. Then `mkdir -p <wt>/leanncd/experiments/jax_bridge/.cache` and
  `ln -s /Users/williammacready/code/python/pyncd.worktrees/task4-boolean-output/leanncd/experiments/jax_bridge/.cache/python <wt>/leanncd/experiments/jax_bridge/.cache/python`
  (verified to exist 2026-11-09; never commit the link). STALE-OLEAN TRAP: run `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd JaxExperiment` once before any scratch probe.
- Plain, separate shell commands only (no `cd x && y`, no `$VAR`, no `;`/`$?` chains); absolute paths; `/usr/bin/git -C <wt>`. A worktree-isolated session refuses `git -C` into the primary checkout and refuses
  compound commands: use the Write tool for generated text, then a separate `sed -i '' 'NNr file'` to splice. `ExitWorktree` (keep) before merging from the primary. Stage by explicit path; never `git add -A`
  (the primary checkout may hold another session's uncommitted files: at the time of writing `papers/semantics/README.md` and `papers/semantics/categorical_tensor_logic_semantics.md`).
- `lean-file.sh <wt>/leanncd experiments/jax_bridge/EvalPlanNonlinSmoke.lean` typechecks the fixture file; `JaxExperiment` does NOT compile it, only the runner's `lean --run` does.
  To run a scratch Lean file (as the probe did): `/Users/williammacready/.elan/bin/lake +leanprover/lean4:v4.30.0 -d <wt>/leanncd env lean --run <file> <out>`; WITHOUT the `+leanprover/lean4:v4.30.0` toolchain pin elan picks another
  toolchain from outside `leanncd/` and fails with "incompatible header". A scratch `main` must sit OUTSIDE the `JaxBridge.NonlinSmoke` namespace (close it with `end`, then `open JaxBridge.NonlinSmoke in def main ...`).
- Harness traps: `Array.extract start stop` takes the END index (an `extract 8 8` was empty in the MQA slice); a tensor name `C` collides with a `C(` token (use two letters); `checkAndRender` requires the einsum-only emitter to refuse every
  fixture in a specific way and misreports affine-bias programs (`nonzeroAffineBias`): not an issue for P1, P2 or the MHA program (the probe passed through `fixture64`), but it blocks wraparound-style fixtures.
- NEVER write wait loops, `pgrep` monitors, `time.sleep` polling or driver scripts: run builds and the differential with `run_in_background` and wait for the notification. The differential aborts at the FIRST failed assertion
  and takes a few minutes; batch edits and run it as few times as possible. Never run two Lean builds or runs at once.
- Do not edit `EvalPlanCodegen.lean`, `ScanAffineEmitTest.lean`, `ExecutableTest.lean`, `ScanJaxGateTest.lean`, the mutation manifest JSON files, `evalplan_affine_runtime.py` or `LeanNCD/DSL/*`; do not touch
  `transformer_scan*`, `transformer_head*`, the mask or MQA fixtures or their programs, envs and assertion texts.
- Budgets (Rule 6): a dispatch is at most about 60 harness-counted tool calls and about 250k context; report the HARNESS count if you delegate. The MQA slice was inline, about 85 calls with 5 mutation runs; this one has three
  programs, so plan for more. Split if you delegate: A = Lean programs, envs, registrations, typecheck and one runner run; B = Python pins; C = mutants, docs, verification. If the budget forces a cut, ship `transformer_gqa` and
  `transformer_gqa_mha` and park `transformer_gqa_split`, saying so.

## 6. Verification before merging (you run it, not a subagent)

`bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd Tests JaxExperiment` (expect 8846 jobs, 0 errors; no new Lean module) and `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh` ONCE on the final tree (expect 41 binary64 and
33 binary32 fixtures if all three are added). One read-only whole-branch review by code reading of the diff: look for pins that a trivial or perturbed entry satisfies by itself (the P1 = P2 pin is vacuous if both programs read the same
head map by construction; check that P2 really reads through `R * g + r`). Re-check `main` before merging (merge main into the branch if it moved; check incoming Lean files with
`rg -l "CompileError|finalizeScans|prepareEvalPlan|evalScheduled"`). Merge to LOCAL main, delete the branch, remove the worktree. Do NOT push unless asked (the lean4 guardrail hook blocks `git push`; after an explicit request
use the one-time prefix `LEAN4_GUARDRAILS_BYPASS=1`).

## 7. Records

Add section 15 to `papers/semantics/jax_scan_record.md` (the changed statements, the probe findings and which of them became pins, the extents and why, the weight-generator candidates tried with their binary32 errors, observed
numpy-pin differences and binary32 headroom, the P1 = P2 and MHA-equivalence results, the mutation table, anything parked) and one paragraph in the bridge README next to the MQA paragraph; value-grep the README and record for stale
statements ("every fixture has h on K and V", "no division", "head-0 weights"). The existing test `AT11 gqa` in `test/Eval/Portfolio/AttentionTest.lean` is actually the head-free (MQA) case: note it in the record, do not edit it.
Update the memory index entry if you keep one.

## 8. Done when

GQA pinned on Lean, eager and jit with observed values for all three programs; P1 = P2 shown; equivalence to the multi-head plan shown; every mutant killed by a NAMED assertion (or a survivor reported); `Tests` + `JaxExperiment` green;
differential green with the stated counts; record and README updated; review clean or adjudicated; merged to local main; worktree and branch removed. Report faithfully: observed values, the mutation table, tool-call counts, anything
unverified or skipped.

## 9. After this slice

The progression agreed 2026-11-09 (each step adds one structural idea; every one needs its own pre-flight probe): cross-attention with unequal extents and an external memory read inside the scan; 1-D convolution and a patch embedding
(affine reads and strides); a GRU or LSTM over a time axis (scan over time, several states, gates); linear attention or a diagonal state-space model (matrix state); a GNN (dense, then scatter-add over edges); dense mixture of experts; the
logic side (Viterbi max-plus, Boolean reachability; Lean-side only today); layers x time (nested scans, a KV cache; needs the most new machinery). Parked from this thread: `/` in index expressions as an elaboration-time desugaring (the axis-split
rewrite covers literal divisors of a single axis with divisible extents; it does not cover `%` or `/` of a sum, non-divisible extents, non-literal ratios or data-dependent indices, and the wraparound cases are expressible only with
unrolled single-axis shifts); gradient pins for the MQA, mask and GQA fixtures (~1 each); depth (item 6a, mostly a float32 measurement); per-layer mask alternation (probably a runtime change: ask first); the binary32 eager
scan-versus-unrolled oracle tolerance (`ORACLE_EAGER_TOL32`, cause unconfirmed) and the plan's binary32 noise relative to a float32 numpy emulation (unconfirmed).

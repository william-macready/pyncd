# Session brief: multi-query attention fixtures in the standard transformer scan (JAX bridge)

Status: not started. Written 2026-11-09 at main `a8568ddb` (pushed). Process weight: Direct path
(`.claude/skills/slice-plan/` section 0) IF the pre-flight answers below are all "works as is": tests and fixtures
only, no production change. If any pre-flight answer needs an emitter or runtime change, STOP and report (do not
edit `EvalPlanCodegen.lean` or `evalplan_affine_runtime.py`; that is a different process weight and the user's call).
CLAUDE.md applies, in particular Rule 13 (worktree, merge to LOCAL main, do not push unless asked), Rule 14 (scope
gate) and Rule 6 (budgets). This is the sibling of `jax_predicate_masks_session_brief.md` (landed; record section 12
of `papers/semantics/jax_scan_record.md`): same harness, same pin style, same hand-mutant discipline.

## 1. Goal

Every attention fixture so far has the head axis `h` on all of Q, K and V. Multi-query attention drops `h` from the
key and value projections: `K[s, k]` and `V[s, k]` read `W_K[l, k, m]` and `W_V[l, k, m]`, only `Q[q, h, k]` keeps
`h`. The scores `Q[q, h, k] · K[s, k]` then broadcast a head-free tensor into the masked softmax, and the attention
output `S[h, q, s] · V[s, k]` broadcasts it back, INSIDE the layer scan. This tests that broadcast on the JAX bridge
against an independent numpy model and against the existing multi-head program.

Not in scope (park with a one-line cost if you find more): grouped-query attention (several query heads per KV head
needs index arithmetic on the head axis), a different mask (keep the standard causal mask, `softmax(where s ≤ q)`),
depth and gradient work, changing any existing fixture, the Python runtime, the emitter, the mutation manifests.

## 2. What exists (verify each before relying on it)

- Standard program `scanProg` / `scanProg32` @ `leanncd/experiments/jax_bridge/EvalPlanNonlinSmoke.lean` (`scanProg`
  ~line 597, `scanProg32` ~627; `scanStack` ~595, `scanWeights` ~670, `scanEnv64` ~680, `scanEnv32` ~683). Extents
  q = s = 3, m = 4, h = 2, k = 2, d = 4, `iter l = 3` (two layers). The K and V statements today are
  `K[s, h, k] := W_K[l, h, k, m] · N1[s, m]` and `V[s, h, k] := W_V[l, h, k, m] · N1[s, m]`; the attention lines are
  `S[h, q, s.] := softmax(where s ≤ q)(Q[q, h, k] · K[s, h, k] · Sc[])` and `AttnOut[q, h, k] := S[h, q, s] · V[s, h, k]`.
  Weight stacks hold layer 0, a derived layer 1 and a NaN layer 2 that a correct two-step scan never reads.
- The predicate-mask fixtures (landed) are the template for a registration, an env built by `insert` on `scanEnv64`
  (`maskEnv64` ~1094) and a pin helper: `mask_fixture_pins`, `np_transformer(..., allow=...)`, `np_masked_softmax`,
  `reachable_rows` @ `leanncd/experiments/jax_bridge/evalplan_nonlin_smoke.py` (~105-330; call site ~692;
  `TRANSFORMER_FIXTURES` ~48 must list every new fixture name; `MODEL_TOL` ~90 = 1e-12 / 1e-6; `check_np` ~195).
  Registrations are in `corpus64` / `corpus32` (~1187 and ~1244): `fixture64 "<name>" prog env minPw minAw
  (some (19, 1, 1)) true (scans := 1)`.
- `np_transformer`'s K, V and score einsums hard-code the head axis (`"hkm,sm->shk"`, `"qhk,shk->hqs"`,
  `"hqs,shk->qhk"`). Give it a flag (default unchanged, so every existing pin is untouched) rather than a second model.
- The Python driver prints per-fixture observed maxima against numpy; the f64 and f32 programs repeat the same statement
  text (the f32 program only re-declares what pins axis order and the history shape).
- Baseline gates on current main (observed after the mask slice): `lake-build.sh <wt>/leanncd Tests JaxExperiment` =
  8846 jobs, 0 errors; `run-evalplan-nonlin.sh` = 37 binary64 and 29 binary32 fixtures within tolerance. binary32
  headroom on `H` against `MODEL_TOL` is thin (window 3.9x, strict 2.2x, sink 1.2x last slice; the standard scan under
  10%): REPORT the headroom of every new binary32 fixture and do not loosen any tolerance.

## 3. What to build

TWO NEW scan-only fixtures, `transformer_mqa` and `transformer_mqa32`: the standard `scanProg` / `scanProg32` with only
these statements changed (declarations too: `K(s, k)`, `V(s, k)`, `W_K(l, k, m)`, `W_V(l, k, m)`):

```
K[s, k]          := W_K[l, k, m] · N1[s, m]
V[s, k]          := W_V[l, k, m] · N1[s, m]
S[h, q, s.]      := softmax(where s ≤ q)(Q[q, h, k] · K[s, k] · Sc[])
AttnOut[q, h, k] := S[h, q, s] · V[s, k]
```

Everything else (RMSNorms, `W_Q`, `W_O`, MLP, gains, `Sc`, `X`, `Eps`, `Inv`, q = s = 3) is the standard fixture's, so the
numpy comparison and the equivalence pin below are direct. Env: `scanEnv64.insert "W_K" ...` and `.insert "W_V" ...` with
the head-free stacks of shape `[3, 2, 4]` (layer, k, m). Build each stack from the existing multi-head layer-0 data so the
inputs are not new magic numbers, but keep layer 0, layer 1 and the NaN layer-2 structure (`scanStack`, `scanLayer1`,
`scanNanSlice`), and make the two heads' effective weights genuinely shared (that is the point). Registration
`(some (19, 1, 1))` if the statement counts hold, otherwise pin what you observe and say why.

## 4. Pins (all independent of Lean's values) and mutants

Python, in the driver, one helper (`mqa_fixture_pins`, called once per precision like `mask_fixture_pins`):
1. Value pin: `H` (layers 0 to 2) equals the numpy MQA model (head-free K and V written from the English definition, not
   copied from Lean) on the Lean, eager and jit views at `MODEL_TOL`; report observed max differences per precision.
2. Non-vacuity: the numpy MQA `H` differs from the numpy multi-head `H` run on the standard head-carrying weights by more
   than 1e-2, so the pin can tell the two models apart. Also pin that the two query heads DO attend differently in the
   numpy model (a model where both heads gave the same attention would pass a "broadcast" test vacuously).
3. Equivalence to the existing program (the strong, Lean-independent pin): build the multi-head inputs
   `W_K_mh[l, h, k, m] = W_K_mqa[l, k, m]` for both h (same for `W_V`), run the STANDARD plan
   (`by["transformer_scan" + sfx]["plan"]`) on those inputs on the eager runtime with `rt.run_named`, and assert `H` equals
   the MQA fixture's eager `H` (state the tolerance you observe; bitwise if it is bitwise, with the observed count). A
   head that read the wrong K or V slice, or a broadcast over the wrong axis, breaks this.
4. Layer-2 weight slices are NaN in the inputs and every output is finite (a step reading past layer 1 turns `H` NaN).
5. Keep the existing pins untouched and green.

Hand mutants (edit the f64 program text of the MQA fixture, run `run-evalplan-nonlin.sh`, name the first failing
assertion, restore with `git checkout -- <file>`, `git diff --stat` empty). Each must keep EVERY input used: a mutant
that drops the only reader of an input dies on the input-set `KeyError`, which is not a kill (last slice's first
candidate did exactly that; see record section 12). Suggested (each must still parse; if one does not, pick another and say so):
`AttnOut` reads `K[s, k]` instead of `V[s, k]` (`V` becomes dead: say whether the plan counts change); the score line
without `· Sc[]`; the mask `s ≤ q` changed to `s < q` (attention row 0 becomes empty); `K[s, k]` reading `N1[q, m]`
instead of `N1[s, m]` only if `q` can be a free axis there (it changes K's shape, so it may be refused: that is not a
kill unless a numpy or equivalence assertion fires). The f64 and f32 programs repeat statement text: edit by line number
(`rg -n` first, `sed -i '' 'NNs/old/new/'`, confirm with `git diff -U0` that exactly one line changed). If a mutant
SURVIVES, stop and report it with the exact edit. Record the table in the body of an empty commit.

## 5. Process, harness facts, budgets

- Worktree (Rule 13): `EnterWorktree`, then `bash .claude/skills/new-slice/prepare-worktree.sh`. Then
  `mkdir -p <wt>/leanncd/experiments/jax_bridge/.cache` and
  `ln -s /Users/williammacready/code/python/pyncd.worktrees/task4-boolean-output/leanncd/experiments/jax_bridge/.cache/python <wt>/leanncd/experiments/jax_bridge/.cache/python`
  (target verified to exist 2026-11-09; never commit the link).
- STALE-OLEAN TRAP: run `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd JaxExperiment` once after the worktree is
  prepared, before any scratch probe.
- Plain, separate shell commands only (no `cd x && y`, no `$VAR`, no `;`/`$?` chains, no pipelines into git); absolute
  paths; `/usr/bin/git -C <wt>`. A worktree-isolated session refuses `git -C` into the primary checkout and refuses
  compound commands (a heredoc plus `sed` in one command was refused): use the Write tool for generated text, then a
  separate `sed -i '' 'NNr file'` to splice. `ExitWorktree` (keep) before merging from the primary. Stage by explicit
  path; never `git add -A` (the primary checkout may hold another session's uncommitted files: at the time of writing,
  `papers/semantics/README.md` and `papers/semantics/categorical_tensor_logic_semantics.md`; check
  `git diff --stat main <branch>` against `git status --short` before merging).
- `lean-file.sh <wt>/leanncd experiments/jax_bridge/EvalPlanNonlinSmoke.lean` typechecks the fixture file (parse and
  typecheck of the new programs, about a minute); `JaxExperiment` does NOT compile that file, only the runner's
  `lake env lean --run` does.
- NEVER write wait loops, `pgrep` monitors, `time.sleep` polling or driver scripts: run builds and the differential with
  `run_in_background` and wait for the completion notification. The differential aborts at the FIRST failed assertion and
  takes a few minutes; batch edits and run it as few times as possible. Never run two Lean builds or runs at once.
- Do not edit `EvalPlanCodegen.lean`, `ScanAffineEmitTest.lean`, `ExecutableTest.lean`, `ScanJaxGateTest.lean`, the
  mutation manifest JSON files, or `evalplan_affine_runtime.py`; do not touch `transformer_scan*`, `transformer_head*`,
  `transformer_window/strict/sink*` or their programs, envs or assertion texts.
- Budgets (Rule 6): a dispatch is at most about 60 harness-counted tool calls and about 250k context; report the
  HARNESS count if you delegate (self-reported counts ran 1.3x low). The mask slice was done inline in one session
  without delegation (about 90 tool calls total including 5 mutation runs); a split if you delegate: A = Lean programs,
  envs, registrations, typecheck and one runner run; B = Python pins; C = mutants, docs, verification.
- First, before writing the fixtures, answer these by a small typecheck or a read, and put the answers in your first
  report: (i) do `K[s, k] := W_K[l, k, m] · N1[s, m]` and the head-free score line parse and typecheck; (ii) does the
  bridge emit and run `Q[q, h, k] · K[s, k]` (a head-free operand in a masked axiswise softmax) and
  `S[h, q, s] · V[s, k]` inside a scan, i.e. is the plan still one scan with counts (19, 1, 1), or does the emitter
  refuse (a typed `JaxCodegenError` or `unsupportedStep`: STOP and report the exact error, do not work around it);
  (iii) which outputs does the fixture export (`H` only, or more: every exported output needs a pin).

## 6. Verification before merging (you run it, not a subagent)

`bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd Tests JaxExperiment` (expect 8846 jobs, 0 errors; no new Lean
module) and `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh` ONCE on the final tree (expect 38 binary64
and 30 binary32 fixtures if both are added). One read-only whole-branch review by code reading of the diff (last slice's
review caught a vacuous pin and a stray edit: look for pins that the perturbed or trivial entry satisfies by itself).
Re-check `main` before merging (merge main into the branch if it moved; check incoming Lean files with
`rg -l "CompileError|finalizeScans|prepareEvalPlan|evalScheduled"`). Merge to LOCAL main, delete the branch, remove the
worktree. Do NOT push unless asked (the lean4 guardrail hook blocks `git push`; after an explicit request use the
one-time prefix `LEAN4_GUARDRAILS_BYPASS=1`).

## 7. Records

Add section 13 to `papers/semantics/jax_scan_record.md` (the four changed statements, the pre-flight answers, observed
numpy-pin differences and binary32 headroom, the equivalence-pin result, the mutation table, anything parked) and one
paragraph in the bridge README next to the mask fixtures; value-grep the README and record for stale statements ("every
fixture has h on K and V", "the only mask"). Update the memory index entry if you keep one.

## 8. Done when

MQA pinned on Lean, eager and jit with observed values; equivalence to the tiled multi-head program shown; every mutant
killed by a NAMED assertion (or a survivor reported); `Tests` + `JaxExperiment` green; differential green with the stated
counts; record and README updated; review clean or adjudicated; merged to local main; worktree and branch removed.
Report faithfully: observed values, the mutation table, tool-call counts, anything unverified or skipped.

## 9. After this slice

Item 6a (depth and binary32 error growth, about 6 layers, weight stacks generated by formula; record observed growth, do
not loosen tolerances), item 6b (`jax.grad` through the emitted scan versus the unrolled version; exploratory, may need a
runtime change and so its own mutation work; stop and ask before editing the runtime), grouped-query attention (needs
head-axis index arithmetic: check first whether the surface syntax can express it), and per-layer mask alternation
(a predicate over `l` inside the scan; probably a runtime change, so ask first). Also parked from the standard-transformer
slice: the binary32 eager scan-versus-unrolled oracle tolerance (`ORACLE_EAGER_TOL32`, layer 2 only, cause unconfirmed).

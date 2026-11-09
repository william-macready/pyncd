# Session brief: predicate-mask fixtures for the standard transformer (JAX bridge)

Status: not started. Written 2026-11-08 at main `c1e91e06` (pushed). Process weight: Direct path
(`.claude/skills/slice-plan/` section 0): tests and fixtures only, no production change. CLAUDE.md applies, in
particular Rule 13 (worktree, merge to LOCAL main, do not push unless asked), Rule 14 (scope gate) and Rule 6
(budgets).

## 1. Goal

The standard pre-norm transformer fixtures (`transformer_scan`, `transformer_head`, binary64 and binary32) use ONE
predicate: the causal mask `softmax(where s ≤ q)`. This slice tests the predicate machinery on the JAX bridge beyond
that single pattern, INSIDE the layer scan: a sliding window (subtraction in a predicate term, conjunction), a strict
mask with a fully masked row, and an attention-sink mask (disjunction, equality). Each is checked against an
independent numpy model whose mask is written from the English definition, not copied from Lean.

Not in scope (park with a one-line cost if you find more): a predicate over the iteration axis `l` inside the scan
body, data-driven masks (`where edge[i,j] > 0` does not parse, KG-datamask), Iverson factors on JAX (the bridge has
no lowering, `iversonFactor`), depth and gradient work (next slices), changing any existing fixture, the Python
runtime, the emitter, the mutation manifests.

## 2. What exists (verify each before relying on it)

- Programs: `scanProg` / `scanProg32` and `headProg` / `headProg32` @ `leanncd/experiments/jax_bridge/EvalPlanNonlinSmoke.lean`
  (`scanProg` ~line 597, `headProg` ~841), inputs `trX` (~564), `scanEnv64` (~680), `headEnv64` (~911), helpers
  `fixtureOfSched64` / `fixture64` / `fixture32` (~118-160), registrations `fixture64 "transformer_scan" ...` (~1004)
  and `fixture32 "transformer_scan32" ...` (~1058). Read `scanProg`'s statements: the mask is in
  `S[h, q, s.] := softmax(where s ≤ q)(Q[q, h, k] · K[s, h, k] · Sc[])`.
- Extents today: q=3, s=3 (`axis s : ℕ = 3`), m=4, h=2, k=2, d=4, `iter l = 3` (two layers). Weight stacks are
  `W_*(l, ...)`, gains `G1(l, m)`, `G2(l, m)`, rank-0 `Sc()` = 1/sqrt(2). None of the weight shapes depends on q.
- Standalone masked fixtures (no scan) already pin `softmax`/`normalize`/`l2normalize` with `where s ≤ q` and
  `softmax(where s < q)` (~lines 205-220 f64, 295-310 f32), and the Python driver prints
  "pinned: all-masked row = zeros (not uniform)". Read them; do not duplicate them.
- Predicate grammar @ `leanncd/LeanNCD/DSL/Syntax.lean` lines ~109-146: index expressions are `+`/`-` sums
  (`q - s`, `s + 2`), comparisons `< ≤ = ≠ > ≥`, `∧` (binds tighter than `∨`), `∨`, `¬`, `ieq(a, b)`, parentheses.
  Tensor arithmetic has `+` only (no tensor subtraction); that does not matter here.
- JAX side: the mask is lowered to a static `include` table on the axiswise node (`buildAxiswiseInclude` @
  `EvalPlanCodegen.lean`, READ ONLY).
- Python driver @ `leanncd/experiments/jax_bridge/evalplan_nonlin_smoke.py`: `np_transformer` (~100, the causal mask
  is a hard-coded `np.tril` at ~108), `np_state`, `np_head`, `MODEL_TOL` (~85: 1e-12 / 1e-6), `require_close` (~211),
  `NUM_STATS`, and the causality pin (~543, `X[2, :] += 0.5`, rows 0 and 1 bitwise identical on the eager runtime).
- Record: `papers/semantics/jax_scan_record.md` section 11 describes the standard model; bridge README
  `leanncd/experiments/jax_bridge/README.md`.
- Baseline gates on current main (observed): `lake-build.sh <wt>/leanncd Tests JaxExperiment` = 8846 jobs, 0 errors;
  `run-evalplan-nonlin.sh` = 34 binary64 and 26 binary32 fixtures within tolerance. binary32 headroom on `H` is
  under 10% of the 1e-6 numpy tolerance (observed 9.4e-7): report the headroom of every new binary32 fixture.

## 3. What to build

Three NEW scan-only fixtures (no head), each the standard `scanProg` with only the mask changed and with q = s = 5
so a window or sink is non-trivial (at q = 3 a window of 2 is barely different from causal). New names; DO NOT touch
`transformer_scan*` / `transformer_head*` or their programs, envs or assertion texts (the Python mutation manifest
`papers/semantics/jax_scan_mutations_python.json` is keyed to `transformer_scan eager H`).

| Fixture | Mask (inside the scan) | What it exercises |
|---|---|---|
| `transformer_window` | `where s ≤ q ∧ q - s < 2` | subtraction in a predicate term, `∧`, a window narrower than the history |
| `transformer_strict` | `where s < q` | strict comparison; query row 0 attends nothing (fully masked row inside the scan, expected all-zero attention row, never uniform, never NaN) |
| `transformer_sink` | `where s ≤ q ∧ (s = 0 ∨ q - s < 2)` | `∨`, `=` against a constant, parentheses, the attention-sink pattern |

Binary32 siblings (`...32`) for all three if the budget allows; if you drop any, say which and why. Each fixture
reuses the existing weight, gain and `Sc` arrays; only `X` (`[5, 4]`) and `Eps` (`[5]`) are new, with distinct,
non-degenerate rows (a wrong row or position must be a different number). Declare `axis s : ℕ = 5` in the f32
programs as well as the f64 ones if the f32 program would otherwise leave `s` unsized (the unrolled oracle needed
this last slice). The registration needs the plan-count argument: observe the (assign, pointwise, axiswise) counts
from a run; the statement count should equal the standard scan's (19, 1, 1) because only the predicate changes, but
pin what you observe.

## 4. Pins (all independent of Lean's values) and mutants

Python, in the driver, one helper reused by the three fixtures:
1. Parametrize `np_transformer` by an `allow` matrix `[q, s]` (default `np.tril`, so the standard pins are
   unchanged). Build each `allow` from the predicate's English definition with plain loops
   (`allow[q][s] = (s <= q and q - s < 2)` etc.), never by reading Lean or JAX output.
2. Value pin: every exported output of each new fixture (`H`, layers 0 to 2) equals the numpy model on the Lean, eager
   and jit views, at `MODEL_TOL`; report observed max differences per precision.
3. Non-vacuity: the numpy `H` of each mask differs from the causal numpy `H` on the same inputs by more than 1e-2,
   and the three masks differ from each other, so the pin can tell them apart.
4. Receptive-field pin on the JAX eager runtime (the strong one): perturb `X` at one position p, run again, and assert
   the rows that the mask's two-step reachability (computed in Python from `allow`, two layers) says are unreachable
   from p are BITWISE identical, and that at least one reachable row changes by more than 1e-3. Choose p per mask so
   both sets are non-empty (for the window with width 2 and two layers, perturbing position 0 reaches rows 0 to 2 only;
   for the sink every row sees position 0, so perturb a later position).
5. `transformer_strict`: row 0's attention is empty: assert all outputs finite on all views, and that numpy's row 0
   of the attention-weighted value is exactly zero in the numpy model (model the zero row, as the standalone
   all-masked fixtures do).
6. Keep the existing standard pins untouched and green.

Hand mutants (edit the f64 program text of ONE fixture, run `run-evalplan-nonlin.sh`, name the first failing
assertion, restore with `git checkout -- <file>`, `git diff --stat` empty): window width `< 2` to `< 3`; the window's
`∧` to `∨`; `strict` replaced by `s ≤ q`; the sink program without its `s = 0` clause; one value-level mutant that
keeps an input used (do not accept a crash or an input-set assertion as the only kill; last slice two mutants first
died that way). If a mutant SURVIVES, stop and report it with the exact edit. The f64 and f32 programs repeat the
same statement text: use enough surrounding text to make each edit unique and confirm with `rg -n` that exactly one
place changed. Record the table in the body of an empty commit.

## 5. Process, harness facts, budgets

- Worktree (Rule 13): `EnterWorktree`, then `bash .claude/skills/new-slice/prepare-worktree.sh`. Then
  `mkdir -p <wt>/leanncd/experiments/jax_bridge/.cache` and
  `ln -s /Users/williammacready/code/python/pyncd.worktrees/task4-boolean-output/leanncd/experiments/jax_bridge/.cache/python <wt>/leanncd/experiments/jax_bridge/.cache/python`
  (verify the target exists first; never commit the link).
- STALE-OLEAN TRAP: a fresh worktree's synced bridge oleans can be stale. Run
  `bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd JaxExperiment` before any scratch probe.
- Plain, separate shell commands only (no `cd x && y`, no `$VAR`, no `;`/`$?` chains, no pipelines into git); absolute
  paths; `/usr/bin/git -C <wt>`; a worktree-isolated session refuses `git -C` into other worktrees, so
  `ExitWorktree` (keep) before merging from the primary. Use `rg`/Read windows of about 50 lines, never whole files.
  Stage by explicit path; never `git add -A` (the primary checkout holds another session's uncommitted
  `papers/semantics/README.md`; check `git diff --stat main <branch>` against `git status --short` before merging).
- NEVER write wait loops, `pgrep` monitors, `time.sleep` polling or driver scripts: run builds and the differential
  with `run_in_background` and wait for the completion notification. The differential aborts at the FIRST failed
  assertion and takes minutes, so batch edits and run it as few times as possible. Never run two Lean builds or runs
  at once.
- Do not edit `EvalPlanCodegen.lean`, `ScanAffineEmitTest.lean`, `ExecutableTest.lean`, `ScanJaxGateTest.lean`, the
  mutation manifest JSON files, or `evalplan_affine_runtime.py`.
- Surface quirks seen so far: rank-0 tensors are declared with parentheses (`Sc()`); `tensor f64 ...` on every tensor in
  f64 programs, f32 programs spell only the declarations that pin axis order and history shape; an external tensor named
  `c[...]` fails to parse; `S[j] := S[j, 2]` gives `rankMismatch`.
- Budgets (Rule 6): a dispatch is at most about 60 harness-counted tool calls and about 250k context; report the
  HARNESS count (the agent result's `tool_uses`), not the agent's own tally (they ran 1.3x low). Suggested split
  if you delegate: A = Lean programs, envs, registrations, build and one runner run; B = Python pins; C = mutants,
  docs, verification. Past overruns on this feature: 54 calls on a 45 cap, 93 on a 60 cap with polling.
- First, before writing fixtures, answer these by a small compile or a read, and put the answers in your first
  report: (i) does `q - s < 2` parse inside `where`; (ii) does `(s = 0 ∨ q - s < 2)` with `=` against a constant and
  parentheses parse; (iii) with q = s = 5 do the plan counts stay (19, 1, 1); (iv) what happens to a fully masked row
  inside a scan on Lean and JAX (expected zeros; if it is NaN or uniform STOP and report, do not work around it).

## 6. Verification before merging (you run it, not a subagent)

`bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd Tests JaxExperiment` (expect 8846 jobs, 0 errors; no new Lean
module is added) and `bash <wt>/leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh` ONCE on the final tree
(expect 37 binary64 and 29 binary32 fixtures if all six are added, otherwise the observed count, stated). One read-only
whole-branch review by code reading. Re-check `main` before merging (merge main into the branch if it moved; check
incoming Lean files with `rg -l "CompileError|finalizeScans|prepareEvalPlan|evalScheduled"`). Merge to LOCAL main,
delete the branch, remove the worktree. Do NOT push unless asked (the lean4 guardrail hook blocks `git push`; after an
explicit request use the one-time prefix `LEAN4_GUARDRAILS_BYPASS=1`).

## 7. Records

Add section 12 to `papers/semantics/jax_scan_record.md` (the three masks, the observed numpy-pin differences and
binary32 headroom per fixture, the mutation table, anything parked) and one sentence per fixture in the bridge README;
value-grep the README and record for stale statements ("the only mask", "causal" claims about the transformer
fixtures). Update the memory index entry if you keep one.

## 8. Done when

Three masks pinned on Lean, eager and jit with observed values; every mutant killed by a NAMED assertion (or a
survivor reported); `Tests` + `JaxExperiment` green; differential green with the stated counts; record and README
updated; review clean or adjudicated; merged to local main; worktree and branch removed. Report faithfully:
observed values, the mutation table, harness tool-call counts per dispatch, anything unverified or skipped.

## 9. After this slice

Item 6a (depth and binary32 error growth, about 6 layers on this q = 5 family, weight stacks generated by formula;
record observed growth, do not loosen tolerances) and item 6b (`jax.grad` through the emitted scan versus the
unrolled version; exploratory, may need a runtime change and so its own mutation work; stop and ask before editing the
runtime). Also parked from the standard-transformer slice: the binary32 eager scan-versus-unrolled oracle tolerance
(`ORACLE_EAGER_TOL32`, layer 2 only, cause unconfirmed).

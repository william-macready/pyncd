# JAX Boolean reachability: implementation plan

> **Update 2026-11-22 (main `40b7af4a`).** The five stale entries J4, J5, J13, J14, J15 of
> `papers/f32_jax_mutations_post.json` were re-anchored (`a4552839`), and every other stale `expect`
> pin in that manifest and in `jax_scatter_mutations_post.json` was refreshed (`40b7af4a`). Both
> manifests now run unfiltered with exit 0 (f32 15/15, scatter 6/6), so the "stale entries" and the
> unfiltered `--check` exit-125 exception described below were true of the baseline this document
> was written against and no longer apply. The text below is otherwise unedited.

**Status: execution-ready plan; implementation not started.** The code was prototyped and packaged
before this document was written. It ships as five ordered patches. This document holds the
rationale, decisions, audit, fixtures, commands and expected results. It contains no implementation
code: apply the patches, do not redesign or transcribe them.

- Source baseline: `b305b363942e440845ae19e57fec0629b7c1af04` (`package.json` key `source_baseline`).
- Package: [`jax_boolean_reach_files/package.json`](jax_boolean_reach_files/package.json), per-task
  snapshots `task1.json`..`task5.json`, verifier `verify_package.py`, patches
  [`jax_boolean_reach_patches/01..05.patch`](jax_boolean_reach_patches/). The two new mutation
  manifests ship INSIDE patches 01 (Lean) and 03 (Python). They are not separate assets.
- Evidence: [`jax_boolean_reach_files/authoring_evidence.md`](jax_boolean_reach_files/authoring_evidence.md)
  (observations reported by the prototype, with controller re-checks marked) and
  [`jax_boolean_reach_files/preflight/REPORT.md`](jax_boolean_reach_files/preflight/REPORT.md)
  (decisions D1-D7, plan dump, door inventory, Boolean semantics).
- Authoring provenance: [`jax_boolean_reach_plan_record.md`](jax_boolean_reach_plan_record.md).

**Goal.** The six Boolean reachability fixtures of `EvalPlanLogicSmoke.lean` (program `reachProg`: a
Boolean scan state `Reach` plus a real `Closed` reading it) render to JAX `affineReference` records
and execute named and positional, eagerly and under `jit`, in binary64 and binary32. The Python
verifier swaps in the JAX outputs for the Lean values and gives them to the unmodified independent
BFS oracle. That needs: a Boolean destination algebra (`admittedAlgebraBool`: factor min seeded 1,
reduction and term max seeded 0) over the real carrier; Boolean sources; Iverson factors lowered only
in Boolean-algebra nodes, as static include tables decided in Lean; and a new render profile
`JaxRenderProfile.booleanReach`. The default `.realOnly` behaviour does not change.

**Process weight: Full path.** The slice adds a backend capability (a render profile, a runtime
algebra and an Iverson lowering) on a soundness surface: if the gate admits a Boolean node and
the emitter does not tag it, the node silently computes `+`/`*`.

---

## 1. Scope

**Included**

- The six `reachability*` logic fixtures through `renderAffinePlanNamed` and
  `renderAffinePlanPositional`, eager and `jit`, float64 and float32. They are checked exactly against
  the Lean plan values and then by the independent BFS oracle (`evalplan_logic_smoke.py`, unmodified).
- Boolean destination algebra and Boolean sources under the new profile `.booleanReach`. That covers
  the Boolean statements and the real sum-product `Closed` node reading a Boolean source.
- Iverson lowering in Boolean-algebra nodes only, through Lean-decided static include tables
  (`iversonIncludeTable`). Step-dependent predicates in scan step blocks are included.
- Runtime algebra `"boolean"` with semantics marker `ordered_boolean_v1`, plus 17 raw Boolean
  fixtures and 18 metadata-refusal cases. Together they pin what the six fixtures cannot see (tie
  order, min vs product, max vs sum, NaN order, include tables).

**Excluded** (owner / later slice)

| Excluded | Status after this slice | Owner / note |
|---|---|---|
| Iverson lowering in real sum-product or max-plus nodes | refused, `iversonFactor` (emitter) and "iverson factors require boolean algebra" (runtime) | D1; later slice if ever requested |
| `realToBool` casts | refused: gate `sourceDType`, runtime `real_to_bool` must be exactly `False` | D5 |
| min-plus | refused (`scanNonRealState` for `.posInf` states, min algebra not admitted) | unchanged; no plan |
| Viterbi traceback / argmax | not expressed (no native TL operator) | unchanged |
| nested scans, multi-axis scans | refused as before | unchanged |
| gradients through Boolean nodes | not run, not claimed | D7 |
| evidence, einsum, candidates, scatter paths | stay `.realOnly`, Boolean doors closed | unchanged |
| 0/1 validation of Boolean inputs | none, matching Lean (values propagate) | D6, documented |
| XLA `jit` signed-zero seed (`0 + (-0)` is `-0` under `jit`) | KNOWN and already PINNED (`KNOWN_DIVERGENT` in `evalplan_affine_smoke32.py`); not a new finding | parked; no fixture is known to expose it. With `Edge` false entries set to `-0.0` (a legal input, D6), 30 `Reach` cells are `-0` (observed in preflight), and an inferred route through `Closed` exists (section 12, K5) |

## 2. Decisions (settled by the user) and where each binds

| # | Decision | Binds in |
|---|---|---|
| D1 | Iverson lowering for Boolean-algebra nodes ONLY | 02: `renderAffineTerm`/`renderAffineFactor` `boolean` flag, `iversonFactor` elsewhere; 03: `_check_factors` |
| D2 | Bool SOURCE under real sum-product admitted in the new profile only (`Closed`); the fixture is not rewritten | 01: `boolSourceOk` arm `profile.admitsBoolean && a.algebra == realAlgebra`; 02: plain-real `Closed` pin; 03: `real_dest_reads_bool_source` |
| D3 | New superset constructor `JaxRenderProfile.booleanReach`; `.maxPlus` keeps its meaning | 01: constructor, `admitsMaxPlus`, `admitsBoolean`; 02: `renderAffineNode`/`renderScanNode` pass `.booleanReach`; `MAX-L-SCAN` re-anchored |
| D4 | Step-dependent predicates admitted (stacked table), pinned, no refusal | 02: `brStep` pin in `ScanAffineEmitTest.lean`; 03: `_run_scan_node` stacking, `bool_scan_step_iverson`, `bool_scan_step_iverson_ge` |
| D5 | `realToBool` stays refused with a located error | 01: source check refuses a real source in a Boolean statement; 03: Boolean read requires `real_to_bool` exactly `False`; 05: README row |
| D6 | No 0/1 validation of Boolean inputs (mirror Lean) | 03: runtime docstring; fixtures with 0.5, 2.0, -1, NaN inputs |
| D7 | Gradients out of scope | no gradient code; T4 gradient counts unchanged |

Also agreed in preflight: a real carrier with explicit casts (NOT `jnp.bool_` arrays). The full
`PosBoolExpr` grammar is decided in Lean over context ++ output ++ reduction coordinates, and the
runtime evaluates no predicate.

## 3. Global constraints (exact values)

**Algebra and scalar semantics** (Lean `admittedAlgebraBool`, mirrored by the runtime):

- Factor fold `_ordered_min` seeded `1` in declared order. Reduction fold (row-major over the
  reduction axes) and term fold `_ordered_max` seeded `0`. Out-of-bounds pad `0`, empty reduction `0`,
  empty factor list `1`.
- Lean ties: `minNaN` keeps the FIRST argument on a tie (`min(+0,-0) = +0`, `min(-0,+0) = -0`).
  `maxNaN` keeps the SECOND (`max(+0,-0) = -0`). Both return the first NaN seen, so NaN spreads.
  `jnp.minimum`/`jnp.maximum` are NOT equivalent.
- Real carrier, cast explicitly: Boolean values are floats in the plan's carrier dtype. They are not
  normalised to {0, 1}: 0.5 propagates, 2.0 clamps through min, NaN spreads.
- No tolerances anywhere. Raw fixtures and reachability values are compared bitwise against Lean.
  The BFS oracle compares exactly.

**Record contract** (observed, emitted by `EvalPlanCodegen.lean` after T2):

- Boolean node: `"algebra": "boolean", "semantics": "ordered_boolean_v1"`.
- Boolean read factor: `{"source_slot", "safe_index", "mask", ["unary"], "tag": "read", "real_to_bool": False}`,
  with NO `bool_to_tropical` key (that key is max-plus-only).
- Iverson factor: `{"tag": "iverson", "include": [0|1, ...]}`. It has one entry per coordinate of the
  term's full `iteration_shape` (context ++ output ++ reduction), in `allCoords` order, stacked
  step-major in step blocks. Its length is `prod(iteration_shape)`. Entries are exactly int 0 or 1
  (Python `True` is refused).
- Scan records need no `state_init`/`semantics` key; Boolean state init is `.zero`.
- The `Closed` node (real destination reading a Boolean source) is a plain real record with no
  `algebra`/`semantics`/`tag` key.
- f32 and f64 renders of `reachProg` are byte-identical (dtype is not emitted).
- Observed include tables: `reachProg` base `[i = j]` = 36-entry identity diagonal (the only include
  table in its render). Toy `S[j,l+1] := S[j,l] · [j ≤ l]` (j = 3, l = 4) gives `[1,0,0,1,1,0,1,1,1]`.

**What must NOT change**

- Default `.realOnly` behaviour: every pre-existing gate pin stays green unchanged. The patches only
  add to `ExecutableTest.lean` and `ScanJaxGateTest.lean`.
- Evidence, einsum, candidates and scatter doors stay closed to Boolean.
- T4 leaves `evalplan_affine_runtime.py` and `EvalPlanCodegen.lean` untouched (patch 04 does not touch them).
- The max-plus runner counts before the slice, per precision: 28 checked views, 26 refusals,
  28 source views, 5 gradient input points, 20 point-forward views, 20 gradient views.
- `ADVERSARIAL` stays 14 entries. The logic fixture count stays 13.
- Pre-existing tests and pins change only where the T2/T4 sections below name a flip.

**Counts at each task boundary** (per precision; f64 = f32)

| Boundary | Lean manifest entries | Python manifest entries | max-plus runner: checked / refusals / source / grad points / point-forward / grad views | `check-lean-drivers.sh` |
|---|---|---|---|---|
| baseline | (file absent) | (file absent) | 28 / 26 / 28 / 5 / 20 / 20 | 8 drivers |
| after T1 | 3 (`T1`) | (absent) | not reported by the prototype | not reported |
| after T2 | 9 (3 `T1` + 6 `T2`) | (absent) | 28 / 26 (CONTROLLER-observed); the rest not reported | 8/8 PASS (CONTROLLER-observed) |
| after T3 | 9 | 30 (`T3`) | 62 / 62 / 28 / 5 / 20 / 20 | 8/8 green |
| after T4 | 9 | 33 (30 `T3` + 3 `T4`) | 62 / 58 / 52 / 5 / 20 / 20 | exit 0, 8 drivers |
| after T5 | 9 | 33 | unchanged from T4 (not rerun by the prototype) | not rerun by the prototype |

Derivations, for checking a mismatch: T3 adds 17 raw Boolean fixtures x 2 (eager, jit) = 34 checked
views, and 18 refusal cases x 2 = 36 refusal records. T4 deletes 2 old cases x 2 = 4 refusal records
and adds 6 reachability fixtures x 2 renderers x 2 modes = 24 source views.

The "after T3" row was observed after T3 Phase A (`05e0444e`); Phase B (`2c4fac2f`) added mutation
manifests only and changed no code. The T5 row is carried from T4 (T5 changes no executable behaviour:
docs, a comment, a whitespace revert and one manifest refresh; see section 10).

## 4. Case x class audit

Columns: what the slice REQUIRES, what it FORBIDS, and what is SILENTLY IGNORED (accepted with no
check). Every silently-ignored cell is either pinned or parked. "Fails if violated" names the pin,
fixture or mutant (from the evidence and the patches) that catches a violation.

| Door | Required | Forbidden | Silently ignored | Fails if violated |
|---|---|---|---|---|
| Lean gate: Boolean destination | accepted under `.booleanReach` with `admittedAlgebraBool` | under `.realOnly`/`.maxPlus`: `destinationDType 7 1 .bool` (assignment), `destinationDType 5 0 .bool` (compiled `reachProg` scan, f64 and f32) | none | `profVerdict` pins (`ExecutableTest.lean`), `reachVerdict` pins (`ScanJaxGateTest.lean`); mutant `BR-T1-MAXPLUS-ADMITS-BOOLEAN` |
| Lean gate: bool source under Boolean algebra | accepted under `.booleanReach` | under `.realOnly`: the verdict is `destinationDType` (the destination check precedes the source check and a Boolean algebra implies a Boolean destination), so the source cell cannot be violated independently of the destination cell | none | `profVerdict ... boolBoolSigs boolDestAssign` pins |
| Lean gate: bool source under real sum-product (`Closed`) | accepted under `.booleanReach` only (D2) | `sourceDType 7 0 0 .bool` under `.realOnly`/`.maxPlus` | the value is copied with no cast (D6, intended) | mutant `BR-T1-BOOL-SRC-LEAKS-REALONLY`; raw fixture `real_dest_reads_bool_source` `[.5,-3,2,.25]` (a hidden cast would give 1s) |
| Lean gate: real source in a Boolean statement | none | refused under every profile: `sourceDType 7 0 0 .f64` (assignment), `sourceDType 5 0 0 .f64` (`linearScanBool` scan under `.booleanReach`) | none | mutant `BR-T1-REAL-SRC-IN-BOOLEAN`; `scanVerdictP .booleanReach outerSigsBool linearScanBool` pin |
| Lean gate: Boolean state init | `.zero` admitted | `.negInf`/`.posInf` on a Boolean state: refused by `checkScanPlan` as `stateInitNotAdmitted 0 .negInf .bool` / `.posInf` | the gate has no Boolean-state clause (the checker refuses first) | `checkScanPlan ... linearScanBool` init pins in `ExecutableTest.lean`; verifier asserts no `state_init` key on the Boolean scan record |
| Emitter: Iverson in a Boolean node | lowered to `{"tag":"iverson","include":[...]}` by `iversonIncludeTable` | an `evalPosBool` error counted as "included": `iversonPredicateFailed` instead | none | 12 `gridPin` family pins, donor pin, backstop pin (`EvalPlanCodegen.lean`); `brDiag6`, `brStepInclude` pins (`ScanAffineEmitTest.lean`); mutants `BR-T2-INCLUDE-ORDER`, `BR-T2-NO-CONTEXT-COORDS`, `BR-T2-ERROR-AS-INCLUDED` |
| Emitter: Iverson over a zero-extent axis or with a unary/second read in the term | none | none | `include: []` for a zero-extent iteration axis; an Iverson factor combined with a unary read, with two or more reads, or listed first: silently-ignored cell, parked (K1, K4) | none; the factor fold is uniform and only signed-zero ties are order-sensitive |
| Emitter: Iverson in a real node | none | `iversonFactor` (located) | none | donor pin real leg, `gridPin` real legs; `ScanIversonRefusalTest` (unchanged); mutant `BR-T2-IVERSON-ADMITTED-EVERYWHERE` |
| Emitter: Iverson in a max-plus node | none | `iversonFactor 0 0 1` | none | donor pin max-plus leg; `gateMatrix` Iverson rows (`EvalPlanMaxPlusSmoke.lean`) |
| Emitter: Boolean node metadata | node keys `algebra`/`semantics`; read `tag: read`, `real_to_bool: False` | `bool_to_tropical` on a Boolean read; Boolean keys on the real `Closed` node | none | `brReach` count pins and plain-real `Closed` pin (`ScanAffineEmitTest.lean`); mutants `BR-T2-NO-BOOLEAN-NODE-META`, `BR-T2-NO-BOOLEAN-READ-TAG` |
| Emitter: einsum (`lowerTerm`, `requireNoIverson`) | none | Boolean destination, bool source, Iverson: refused as before | none | einsum legs of the in-file `boolSource*` guards (stay refused) |
| Emitter: candidates | none | refused as before | none | candidate legs of the in-file `boolSource*` guards (stay refused) |
| Emitter: element dtype | none | none | dtype is not in the record (the caller supplies it) | byte-identity pin `brRendered? brReach brEdgeEnv false == ... true` |
| `realToBool` | none | gate `sourceDType`; runtime `real_to_bool` must be exactly `False` | none | gate pins above; runtime `bool_real_to_bool_true`/`_missing`; mutant `BR-T3-real_to_bool_guard_dropped-*`; existing max-plus `real_to_bool` case kept |
| Unary read in a Boolean statement | renders (`"unary": "exp"`), pads with 0 THEN applies the unary | none | admitted, no refusal (decision recorded in the evidence) | `bool_unary_sqrt_oob` `[.5,-0,0,0]`, `bool_unary_exp_oob` `[1,0,1,1]` |
| Runtime: semantics family | `ordered_boolean_v1` | unknown / missing / max-plus semantics: "boolean requires ordered_boolean_v1 semantics"; `semantics_without_algebra`: "real nodes use the legacy metadata-free format" | none | cases `bool_unknown_semantics`, `bool_missing_semantics`, `bool_max_plus_semantics`, `semantics_without_algebra` |
| Runtime: Boolean read family | `tag: read`, `real_to_bool` exactly `False`, no `bool_to_tropical` | `real_to_bool` true/missing, `bool_to_tropical` key, missing tag: "boolean read requires explicit tag read, real_to_bool false, no bool_to_tropical" | none | four cases; mutants `BR-T3-real_to_bool_guard_dropped-*`, `BR-T3-bool_to_tropical_key_guard_dropped-*` |
| Runtime: tag family | `read`, `iverson` | other tags: "unknown factor tag 'future'" | none | `bool_unknown_tag` |
| Runtime: include family | int 0/1 entries, length `prod(iteration_shape)` | short / long / entry 2 / entry `True`: "iverson include must be one 0/1 entry per iteration coordinate"; `include` on a read: "include is only valid on an iverson factor" (any algebra; added by the prototype, not requested) | the length guard has a WEAK pin: its mutant dies by a jax `TypeError`, not the ValueError reason check (parked) | `bool_include_*`, `bool_read_with_include`; mutants `BR-T3-include_range_guard_dropped-*`, `BR-T3-include_on_read_guard_dropped-*`, `BR-T3-include_length_guard_dropped-*` (weak) |
| Runtime: Iverson in non-Boolean node | none | "iverson factors require boolean algebra" | none | `iverson_in_real_node`, `iverson_in_max_plus_node`; mutant `BR-T3-iverson_admitted_in_maxplus-*` |
| Runtime: empty-range scan step block | step block validated even at `step_count=0` | bad include / include entry 2 at `step_count=0` | the stacked step-table length guard is redundant (`_check_factors` already checks it): equivalent mutant, left out. The accept neighbour is a record Lean never emits (`step_count=0` keeping step extent 3 and 9 include entries) and asserts only that the run returns one result, not its value; Lean's real zero-step record is `scan_extentone` (parked, K2) | `bool_scan_empty_step_bad_include`, `bool_scan_empty_step_include_entry_2`; accept neighbour: same record, valid step block (weak) |
| Runtime: Boolean input values | carried as floats | none | no 0/1 validation (D6) | values-not-normalised fixtures (`bool_min_not_product`, `bool_iverson_base`) pin D6 at node level only. The six reachability fixtures use 0/1 `Edge` values only, so the named and positional plan entry points never see a non-0/1 input; a hidden input cast at that boundary would pass every fixture (none exists today). Silently-ignored cell, parked (K3) |
| Runtime: real fold signed zero under `jit` | none | none | `0 + (-0)` is `-0` under `jit` (KNOWN, pre-existing). An inferred route exists through `Closed` (K5): only when a caller sets `Edge` false entries to `-0.0` (observed in preflight: 30 `Reach` cells are `-0`; the shipped fixtures use +0), Lean's real fold turns them into `+0`, and a `jit` fold that drops the `+0` seed would keep `-0`. No fixture runs it (the `jit` consequence is inferred from the documented pitfall) | pinned for the affine corpus as `KNOWN_DIVERGENT`; parked; `real_dest_reads_bool_source` dropped its `-0` input for this reason |
| Verifier: reachability assertions | 13 of 13 logic fixtures carry jax fields; shapes `Reach` (6,6,7), `Closed` (6,6); exact JAX-vs-Lean check; `oracle.verify(replaced)`; `positional_ran` covers every fixture, eager and jit | Viterbi-only replacement filter (removed) | a "stale baseline that keeps the Lean values" control and the hop-5 `Closed` control are equivalent (left out) | controls `BR-T4-stale_baseline_reachability_inputs`, `BR-T4-closed_taken_from_hop_4`, `BR-T4-positional_skipped_for_reachability` |

## 5. Execution protocol (executor)

Open every brief and session with this preamble, with `<worktree>` replaced by its absolute path:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command, no pipelines into git.
> Use absolute paths and `/usr/bin/git -C <worktree>`. Build only with
> `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd <targets>`; never run `lake` from
> the repository root. Read 40-60-line file windows; search with `rg -n`. Stage files by explicit path;
> never commit `.claude/settings.json`. Stay within about 60 turns and 250k context per session and
> say so in the report if you breach it.

Documented exceptions to "build only with `lake-build.sh`": `check-lean-drivers.sh` runs
`$LAKE build LeanNCD JaxExperiment Tests` itself, the `run-evalplan-*.sh` runners call `lake`
directly, and `run-evalplan-maxplus.py` hard-codes `~/.elan/bin/lake` for `lake env lean --run` (it ignores
`LAKE`); `LAKE` defaults to `~/.elan/bin/lake` in the shell scripts. Run these scripts as written. Do not
run `lake` yourself for anything else, and do not set `LAKE` to a different binary.

Placeholders in angle brackets are literal absolute paths you substitute. They are not shell
variables. `<primary>` = the primary checkout. `<worktree>` = the execution worktree.
`<jax-python>` = `<worktree>/leanncd/experiments/jax_bridge/.cache/python/bin/python`, the Python with
JAX that Setup step 4 creates.

**Setup**

1. Local `main` must contain the plan package: this plan, the record, `jax_boolean_reach_files/` and
   `jax_boolean_reach_patches/`. Check with `ls <primary>/papers/semantics/jax_boolean_reach_patches`.
2. Create the worktree from LOCAL `main` (not `origin/main`):
   `/usr/bin/git -C <primary> worktree add -b jax-boolean-reach-exec <primary>/.claude/worktrees/boolean-reach-exec main`
3. With `<worktree>` as the current directory, run the shell script
   `bash <worktree>/.claude/skills/new-slice/prepare-worktree.sh`. It is a plain bash script that needs no
   assistant tooling (its header mentions a tool-specific "enter worktree" step: you already created the
   worktree in step 2, so ignore that). It syncs a built `.lake` so Mathlib
   does not cold-build, and it fails loudly if it cannot. STOP if Mathlib would cold-build.
4. JAX environment. Neither the primary checkout nor a fresh worktree has
   `<worktree>/leanncd/experiments/jax_bridge/.cache/python`, and `prepare-worktree.sh` does not create it.
   Run `bash <worktree>/leanncd/experiments/jax_bridge/setup-python.sh` (needs network: it runs
   `pip install -r requirements-cpu.txt`, pinning `jax==0.10.0`, `jaxlib==0.10.0`, `numpy==2.5.2`).
   Seeding, read from the script: an existing `.cache/python/bin/python` is reused; else `$PYTHON -m
   venv` if `PYTHON` is set; else `python3.13`/`3.12`/`3.11`, then `~/miniconda3/bin/python`, then
   `conda create`; exit 1 if none exists. Afterwards make sure `PYTHON` is not set to an interpreter without
   JAX (a leftover `PYTHON` breaks the shell runners, which default to it). Each command may run in a fresh
   shell, so a bare `unset PYTHON` can be lost. Do NOT probe the variable (`printenv PYTHON` exits 1 when it is
   unset, which is the good case and would look like a failure). Instead prefix every shell runner command
   (`run-evalplan-affine.sh`, `-affine32.sh`, `-nonlin.sh`, `-scatter.sh`, `-logic.sh`) with `env -u PYTHON`;
   that is harmless whether or not `PYTHON` is set.
   - `run-evalplan-affine.sh`, `-affine32.sh`, `-nonlin.sh`, `-scatter.sh` default `PYTHON` to
     `<jax-python>`. `run-evalplan-logic.sh` defaults it to `python3` (stdlib-only oracle; harmless).
     `run-evalplan-maxplus.py` takes `--python <jax-python>`. `mutation_python_manifest.py` always uses
     the `<jax-python>` of the worktree it lives in.
   - Every extra mutation worktree (section 11) needs the same directory: rerun `setup-python.sh`
     there, or `mkdir -p <extra>/leanncd/experiments/jax_bridge/.cache` and
     `ln -s <worktree>/leanncd/experiments/jax_bridge/.cache/python <extra>/leanncd/experiments/jax_bridge/.cache/python`
     (`.cache/` is gitignored; the symlink needs no network).
   - The prototype evidence does not record the environment setup; this step is read from the scripts.
5. `python3 <worktree>/papers/semantics/jax_boolean_reach_files/verify_package.py --task 0`
   → expected `Package OK: 5 ordered patches, task 0 boundary; index unchanged.` This checks the
   affected files still hash to the baseline, that the two new manifests do not exist yet, and that
   01..05 replay onto `b305b363` in a temporary index. If the sandbox blocks `/tmp`, first run
   `mkdir -p <worktree>/.cache`, then prefix the command with `env TMPDIR=<worktree>/.cache`.

**Per task N (1..5)**

1. `python3 <worktree>/papers/semantics/jax_boolean_reach_files/verify_package.py --task <N-1>`
2. `/usr/bin/git -C <worktree> apply --check <worktree>/papers/semantics/jax_boolean_reach_patches/0N.patch`
   (silent, exit 0)
3. `/usr/bin/git -C <worktree> apply <worktree>/papers/semantics/jax_boolean_reach_patches/0N.patch`
4. `python3 <worktree>/papers/semantics/jax_boolean_reach_files/verify_package.py --task <N>` → `Package OK: ... task N boundary ...`
   (It hashes only the files of snapshot N. A stray edit to a file that a LATER task touches is not
   caught until that task's step 1; keep the tree free of edits besides the patches.)
5. Run that task's verification commands (sections 6-10) and compare with the expected results.
6. Stage exactly that task's `touched_files` (listed per task below) with `/usr/bin/git -C <worktree> add <path> ...`.
   Then `/usr/bin/git -C <worktree> status --short` must show nothing else staged. Commit once with the
   stated subject.

**Stop and report (BLOCKED), do not improvise, if:** a patch fails `--check`; `verify_package.py`
fails; a count differs from this plan; a mutant SURVIVES or is killed without its `expect` strings; a
file is not sha-restored after a cycle; a pre-existing pin goes red; Mathlib would cold-build; any
command exits non-zero, with two exceptions: `mutation-manifest.sh --check` on
`papers/f32_jax_mutations_post.json` WITHOUT a label filter exits 125 because of the five stale
entries (see section 12), and `rg` exits 1 when NOTHING matched, which for the stale-claim greps of
section 11 and for read-only searches is a result to record, not a failure. Never
hand-edit a patch, a manifest, an `expect` string, a count or a fixture. Never use `git apply --3way`
or `--reject`.

**Efficiency rules**

- Run each full suite once per task boundary that changes shared code (T1 gate, T2 emitter, T3
  runtime), and once at the end. The suites are `check-lean-drivers.sh` and the five real-path runners
  `run-evalplan-affine.sh`, `run-evalplan-affine32.sh`, `run-evalplan-nonlin.sh`,
  `run-evalplan-scatter.sh`, `run-evalplan-logic.sh`. Do not rerun them after every edit; there are no
  edits besides the patches.
- Run long builds and runners in the background with output redirected to a file under
  `<worktree>/.cache/`, and wait for them to finish. Do not poll in a loop.
- Never run a mutation runner at the same time as another mutation runner, a build or a runner in the
  same worktree: they mutate and import the same files. Mutation phases may run in parallel, in
  separate prepared worktrees at the same commit, ONLY during final verification (section 11).
- `--check` validates a manifest; it is not a mutation cycle.

**Execution record.** Create `papers/semantics/jax_boolean_reach_record.md` (do not overwrite the
authoring record). It holds: base, worktree, interpreter; verifier outputs; per-task commands, exit
codes, counts, commit IDs; mutation tables (label, killed or survived, restored); final suite results;
stale-claim classifications; measured tokens/turns or "unavailable". Commit it last with
`docs(jax): record Boolean-reachability execution`.

---

## 6. T1: Boolean profile and gate (patch 01)

**Files** (`touched_files`): `leanncd/LeanNCD/Eval/Plan/Executable.lean`,
`leanncd/test/Eval/Plan/ExecutableTest.lean`, `leanncd/test/Eval/Plan/ScanJaxGateTest.lean`,
`papers/f32_jax_mutations_post.json`, `papers/semantics/jax_boolean_reach_mutations_post.json` (new),
`papers/semantics/jax_maxplus_mutations_post.json`, `papers/semantics/jax_scan_mutations_post.json`.
Snapshot count 7. Prototype commit `15b40b9b` (+306/-12).

**What lands.** `JaxRenderProfile.booleanReach` (a superset of `.maxPlus`) and private helpers
`JaxRenderProfile.admitsMaxPlus` (`.maxPlus`, `.booleanReach`) and `JaxRenderProfile.admitsBoolean`
(`.booleanReach` only), with no wildcard arms. `jaxAssignSupported` computes `maxPlus`, `boolean`,
`boolSourceOk`. `checkJaxScanSupport` uses `profile.admitsMaxPlus` for the `.negInf` state test. No
new error constructors: it reuses `destinationDType`, `sourceDType`, `unsupportedAlgebra`,
`scanNonRealState`. f32 Boolean uses the same `admittedAlgebraBool`.

**Fixtures.** The patch adds 56 `#guard` lines to `ExecutableTest.lean` (hand-built donors
`idAssign`/`idRead`, `boolDestAssign`/`boolDestSigs`, `boolSourceSigs`, `linearScanBool`,
`tropicalScan`, new `minPlusScan`; helpers `scanVerdictP`, `profVerdict`). It adds 8 to
`ScanJaxGateTest.lean` (the compiled `reachProg`, copied verbatim from `EvalPlanLogicSmoke.lean`,
f64 and f32 retag; helper `reachVerdict`). These are counted from the patch text; a `#guard` can join
several checks. Each accept pin has a refuse neighbour that changes one thing. The prototype first
built the pins against a profile stubbed to behave like `.realOnly`, and exactly the accept pins went
red.

Observed verdicts: Boolean destination / Boolean algebra / bool source accepted under
`.booleanReach`; refused `destinationDType 7 1 .bool` under `.realOnly`/`.maxPlus`. `Closed` shape
accepted under `.booleanReach`; `sourceDType 7 0 0 .bool` elsewhere. Real source in a Boolean
statement `sourceDType 7 0 0 .f64`. Compiled `reachProg` scan accepted under `.booleanReach`;
`destinationDType 5 0 .bool` under the other two (f64 and f32). `tropicalScan` accepted by `.maxPlus`
and `.booleanReach`; `minPlusScan` refused by both as `scanNonRealState 5 0`.

**Mutation cycles: 3** (`jax_boolean_reach_mutations_post.json`, `task` `T1`, target
`Eval.Plan.ExecutableTest`): `BR-T1-REAL-SRC-IN-BOOLEAN`, `BR-T1-BOOL-SRC-LEAKS-REALONLY`,
`BR-T1-MAXPLUS-ADMITS-BOOLEAN`. All killed in the prototype.

**Manifest re-anchors (one line each).** `MAX-L-DEFAULT` in `jax_maxplus_mutations_post.json` (the
`let maxPlus := ...` line), `JS-L-g1` in `jax_scan_mutations_post.json` (the `initValue` check), `J3`
in `papers/f32_jax_mutations_post.json` (the destination dtype check). Two caveats:

- Patch 01 adds two imports to `ScanJaxGateTest.lean`, shifting the `expect` of `JS-L-g2` (`:26:0`
  becomes `:28:0`); patch 02 refreshes it. So `JS-L-g2` is stale at the T1 boundary. `--check` does not
  see this (it checks `old`, not `expect`) and cycles of existing entries run only at the end.
- `J3`'s `expect` strings were stale BEFORE this slice (they named a blank line); patch 01 re-anchored
  only its `old`, and patch 05 refreshes the `expect` (section 10).

**Commands**

```text
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd Eval.Plan.ExecutableTest Eval.Plan.ScanJaxGateTest JaxExperiment
bash <worktree>/leanncd/scripts/mutation-manifest.sh --check <worktree>/leanncd <worktree>/papers/semantics/jax_boolean_reach_mutations_post.json
bash <worktree>/leanncd/scripts/mutation-manifest.sh --task T1 <worktree>/leanncd <worktree>/papers/semantics/jax_boolean_reach_mutations_post.json
bash <worktree>/leanncd/scripts/mutation-manifest.sh --check <worktree>/leanncd <worktree>/papers/semantics/jax_maxplus_mutations_post.json
bash <worktree>/leanncd/scripts/mutation-manifest.sh --check <worktree>/leanncd <worktree>/papers/semantics/jax_scan_mutations_post.json
bash <worktree>/leanncd/experiments/jax_bridge/check-lean-drivers.sh
```

Then run the five real-path runners (section 11 lists them) once, since T1 changes the shared gate.

**Expected.** Build exit 0 with no `#guard` failure. `--check` passes (3 entries). `--task T1`: 3/3
PASS (killed for the `expect` reason, sha-restored). Both re-anchored manifests pass `--check`. Driver
check: `all eight drivers ran clean`. Runners: exit 0. The prototype did not report driver or runner
results at T1; record what you observe. Optional observation: `--check` on
`papers/f32_jax_mutations_post.json` reports J4, J5, J13, J14, J15 as stale (old-string matched 0
times) and exits 125 (this is the documented exception to the non-zero-exit stop rule). That is
pre-existing at the baseline. Do NOT fix it (section 12). `J3` is not among the stale five (patch 01
re-anchored its `old`; to check it alone use the label prefix `"J3 "`).

**Pitfall: ordering hazard.** T1 opens the gate for `.booleanReach`, but no renderer passes
`.booleanReach` until T2. If a renderer passed it before the emitter tagged Boolean nodes, a Boolean
node would be emitted as a plain real record and silently compute `+`/`*`. Patch 02 therefore switches
the profile and adds the Boolean metadata in ONE commit. Do not split it.

**Commit:** `feat(jax): admit the .booleanReach render profile in the JAX gate`

## 7. T2: emitter, Boolean metadata, Iverson include tables (patch 02)

**Files:** `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`, `EvalPlanLogicSmoke.lean`,
`EvalPlanMaxPlusSmoke.lean`, `ScanAffineEmitTest.lean` (all under `leanncd/experiments/jax_bridge/`),
`papers/semantics/jax_boolean_reach_mutations_post.json`,
`papers/semantics/jax_maxplus_mutations_post.json`, `papers/semantics/jax_scan_mutations_post.json`.
Snapshot count 11. Prototype commits `69f9d5be`, `4f56270f`, `30f66a7c` (T2c); one patch, ONE commit
here.

**What lands** (all in `EvalPlanCodegen.lean`; no core library change, because `evalPosBool` and
`allCoords` are already public in `LeanNCD/Eval/Plan/Coordinates.lean`):

- `JaxCodegenError.iversonPredicateFailed (nodeIndex termIndex factorIndex)`. This is the fail-loud
  backstop: an `evalPosBool` error is never treated as "included".
- `iversonIncludeTable nodeIndex termIndex factorIndex iterationShape b : Except JaxCodegenError (Array Nat)`,
  next to `buildFactorTable`, evaluating `evalPosBool` over `allCoords iterationShape.toList`.
- `renderAffineFactor`/`renderAffineTerm` gain `(boolean : Bool := false)`. Iverson throws the existing
  `iversonFactor` unless `boolean`. `renderAffineFields` derives `boolean := a.algebra == admittedAlgebraBool`.
- `renderAffineNode` and `renderScanNode` pass `.booleanReach`. No other `profile := .maxPlus` call
  site exists. A private test helper `accepted` sits beside `rejectedWith`.

**In-file guard flips (affine render legs ONLY).** The `boolSource` standalone and plan-level
guards; the `buildAssignFixture` boolSource eval; `mixedBoolDest` (its `renderAffinePlanNamed` leg is
now `unsupportedSourceDType 1 0 0 .f64`); `testVariantBPlanAuthoritySubstitutionRejected` (its
affineReference leg is replaced by einsumOnly); `step1Bool` positional; `f32BoolSourcePrepared?` (two
legs). Einsum and candidate legs stay refused. `ScanIversonRefusalTest` is unchanged and stays green.

**Fixtures.** `EvalPlanCodegen.lean` gets 14 `#guard` lines: the donor pin (`idIversonAssign` under
Boolean / real / max-plus), 12 `gridPin` tables (one per `PosBoolExpr` family: six relations,
`mul`, `iabs`, `and`, `or`, `not`, `ieq`) and the backstop pin (`iversonPredicateFailed 4 5 6` for a
too-wide leaf, a too-narrow leaf, and a bad leaf under `and`/`not`; accept neighbour `[1,0,0,1]`). All
12 tables agreed with an independent Python enumeration; `ieq` is `i + j = 3`, so it differs from
`eq`. `ScanAffineEmitTest.lean` gets 8 `#guard` lines: `brReach` (= `reachProg`) renders in both
precisions; Boolean counts (2 Boolean nodes, 3 tagged reads, 1 include = `brDiag6`, no
`bool_to_tropical`, no `state_init`); the plain-real `Closed` node; f32 == f64 byte identity;
`brStep` stacked include `brStepInclude`.

**Pitfall: pin placement.** The `reachProg`/`Closed`/f32/step-toy pins live in
`ScanAffineEmitTest.lean`, which is in the `JaxExperiment` globs, because `EvalPlanCodegen.lean` does
not import `tlprog!`.

**`gateMatrix` row change (`EvalPlanMaxPlusSmoke.lean`).** The Boolean row now uses all-Boolean
signatures and expects acceptance; its `run_cmd` message changes to "render-only admission differs
from max-plus and Boolean only". The old row (Boolean destination over an f64 source) was still
refused after T2, so the driver would have passed unchanged. `mixedBoolDest` keeps that mixed case
pinned. The Iverson-under-max-plus rows stay refused (D1).

**T2c: `checkStructure` flip (`EvalPlanLogicSmoke.lean`).** The refusal asserts become accepts
(2 insertions, 7 deletions). Without this, `check-lean-drivers.sh` is red at the T2 boundary with
"JAX unexpectedly admitted a Boolean scan" (observed at `69f9d5be`). `jaxFields` is unchanged until T4.

**Mutation cycles: 6** (`task` `T2`, target `JaxExperiment`): `BR-T2-INCLUDE-ORDER`,
`BR-T2-NO-CONTEXT-COORDS` (only the step-toy pin kills it), `BR-T2-ERROR-AS-INCLUDED`,
`BR-T2-NO-BOOLEAN-NODE-META`, `BR-T2-NO-BOOLEAN-READ-TAG`, `BR-T2-IVERSON-ADMITTED-EVERYWHERE`.
The two metadata mutants were observed killed only by the donor pin in `EvalPlanCodegen.lean`; the
in-file failure stops `ScanAffineEmitTest` from building. Their `expect` strings reflect that.

**Manifest re-anchors.** `MAX-L-SCAN`: `(profile := .maxPlus)` becomes `(profile := .booleanReach)`,
and the mutant still reverts to `.realOnly`. `JS-L-e4` is re-anchored the same way. The line-number
`expect`s of `JS-L-e3`, `JS-L-e4`, `JS-L-e5`, `JS-L-c1` shift by 91 lines and `JS-L-g2` by 2 (the
shift of `JS-L-g2` is caused by the two imports patch 01 added to `ScanJaxGateTest.lean`; see
section 6). These `expect` strings carry line numbers and drift if code above them moves. (They are
manifest strings, so they may carry line numbers; this plan cites identifiers elsewhere.)

**Commands**

```text
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd JaxExperiment
bash <worktree>/leanncd/scripts/mutation-manifest.sh --check <worktree>/leanncd <worktree>/papers/semantics/jax_boolean_reach_mutations_post.json
bash <worktree>/leanncd/scripts/mutation-manifest.sh --task T2 <worktree>/leanncd <worktree>/papers/semantics/jax_boolean_reach_mutations_post.json
bash <worktree>/leanncd/scripts/mutation-manifest.sh --check <worktree>/leanncd <worktree>/papers/semantics/jax_maxplus_mutations_post.json
bash <worktree>/leanncd/scripts/mutation-manifest.sh --check <worktree>/leanncd <worktree>/papers/semantics/jax_scan_mutations_post.json
bash <worktree>/leanncd/experiments/jax_bridge/check-lean-drivers.sh
python3 <worktree>/leanncd/experiments/jax_bridge/run-evalplan-maxplus.py --python <jax-python>
```

Then run the five real-path runners once (the emitter is shared).

**Expected.** Build exit 0. `--check`: 9 entries valid. `--task T2`: 6/6 PASS. Re-anchored
manifests pass `--check`. Driver check: 8/8 PASS (CONTROLLER-observed at `30f66a7c`). Max-plus
runner: `28 checked views, 26 refusals` per precision (CONTROLLER-observed, unchanged from before the
slice); the other runner fields should match the baseline row of section 3 (not reported at T2).
Real-path runners: exit 0 (not reported at T2).

**Commit:** `feat(jax): emit Boolean nodes and Lean-decided Iverson include tables`

## 8. T3: runtime and raw Boolean fixtures (patch 03)

**Files:** `leanncd/experiments/jax_bridge/EvalPlanMaxPlusSmoke.lean`,
`leanncd/experiments/jax_bridge/evalplan_affine_runtime.py`,
`leanncd/experiments/jax_bridge/evalplan_maxplus_smoke.py`,
`papers/semantics/jax_boolean_reach_mutations_python.json` (new),
`papers/semantics/jax_maxplus_mutations_python.json`. Snapshot count 15. Prototype commits
`05e0444e`, `2c4fac2f`.

**Runtime contract** (`evalplan_affine_runtime.py`):

- `_ordered_min` = Lean `minNaN`, `where`-based, with no custom JVP. `_ordered_max` already existed.
- `_algebra` accepts `"boolean"` only with `semantics == "ordered_boolean_v1"` and returns
  `(_ordered_min, dtype(1), _ordered_max, dtype(0))`.
- `_check_factors(terms, algebra)` dispatches on the factor op. Boolean reads need `tag: "read"`,
  `real_to_bool` exactly `False`, and no `bool_to_tropical` key. Iverson needs `tag: "iverson"` and an
  `include` list of length `prod(iteration_shape)` whose entries are exactly int 0 or 1. Iverson is
  refused in real and max-plus nodes (D1). An `include` key on a read is refused in any algebra.
- `_run_term` has an Iverson branch BEFORE any `source_slot` access: `where(include, factor_id, reduce_id)`.
- `_run_scan_node` stacks include tables step-major as `(None, include)` beside `safe_index`/`mask`,
  and the slicer has a `safe is None` branch. It validates the step block even when `steps == 0`.
  Boolean scan records need no `state_init`.

**Raw fixtures: 17** (`booleanRaw` in `EvalPlanMaxPlusSmoke.lean`; helper `blScanFixture`; reuses
`rawFixture`; written to `checked.py` as a `BOOLEAN` list). Expected values are Lean's own
`runDenseAssign`/`runDenseScan` bits and match bitwise in f64 and f32, eager and jit. Values (the
same at both precisions):

| Fixture | Value | Why it exists (the wrong reading it kills) |
|---|---|---|
| `bool_min_tie_order` | `[+0,-0]` | min keeps the first operand on a tie (`jnp.minimum` differs) |
| `bool_max_tie_reduction` | `[-0,+0]` | max keeps the second operand, reduction fold |
| `bool_max_tie_terms` | `[-0,+0]` | same, term fold |
| `bool_min_not_product` | `[.5,1,0,.5]` | min vs `*` (0.5·0.5, 2·2) |
| `bool_max_not_sum` | `[1,.5]` | max vs `+` at the reduction and term folds |
| `bool_nan_factor_fold` | all NaN | NaN spreads through either min operand |
| `bool_nan_reduction` | `[nan,nan,1]` | NaN spreads through max |
| `bool_iverson_base` | `[[.5,1,0],[0,.25,1],[0,0,.5]]` | include table applied in a base block |
| `bool_iverson_reduction` | `[.2,.3,.7]` | include spans the reduction axis |
| `bool_scan_step_iverson` | `[[1,1,1,1],[.5,0,0,0],[1,0,0,0]]` | step-dependent `[j ≤ l]` (monotone toy) |
| `bool_scan_step_iverson_ge` | `[[1,1,0,0],[.5,.5,.5,0],[1,1,1,1]]` | shrinking dual `[l ≤ j]`: the monotone toy cannot tell a stepped table from an unstepped one |
| `bool_unary_sqrt_oob` | `[.5,-0,0,0]` | pad 0 then unary; `sqrt(-0) = -0` survives |
| `bool_unary_exp_oob` | `[1,0,1,1]` | pad 0 then unary (`exp(0) = 1`) |
| `real_dest_reads_bool_source` | `[.5,-3,2,.25]` | `Closed`-shaped real node: no hidden cast (its `-0` input was dropped, see the jit limitation) |
| `bool_bare_oob` | `[1,0,0]` | out-of-bounds pad is 0, not -inf |
| `bool_empty_factors` | `1` | empty factor product is the factor seed 1 |
| `bool_zero_reduction` | `0` | empty reduction is the reduce seed 0 |

Pitfall (f32 scan toys): `blStepProg`/`blStepGeProg` carry a real `tensor f64 Closed(j)` and the
consumer `Closed[j] := S[j, 3]`. Without them the retag leaves the plan at f64 storage, and Lean's
`runDenseScan32` raises `storageKindMismatch`.

**Metadata refusals: 18 cases.** Each clones one record (`bool_iverson_base`, or the donors named
below) and changes one field. Each is asserted for its own message, as a ValueError in eager and jit,
in both precisions:

- `bool_unknown_semantics`, `bool_missing_semantics`, `bool_max_plus_semantics` → "ordered_boolean_v1 semantics"
- `semantics_without_algebra` → "legacy metadata-free"
- `bool_real_to_bool_true`, `bool_real_to_bool_missing`, `bool_bool_to_tropical_key`, `bool_missing_tag` → "boolean read requires"
- `bool_unknown_tag` → "unknown factor tag"
- `bool_include_short`, `bool_include_long`, `bool_include_entry_2`, `bool_include_entry_true` → "include must be one 0/1 entry"
- `bool_read_with_include` → "only valid on an iverson factor"
- `iverson_in_real_node` (donor `real_dest_reads_bool_source`), `iverson_in_max_plus_node` (donor
  `bool_to_tropical_true`, correct-length include) → "require boolean algebra"
- `bool_scan_empty_step_bad_include`, `bool_scan_empty_step_include_entry_2` (scan level, `step_count=0`) → "include must be one 0/1 entry"

Accept neighbours: the unmodified record, and the empty-range scan with a valid step block.

**Mutation cycles: 15 mutants = 30 entries** (`jax_boolean_reach_mutations_python.json`, `task`
`T3`, `verifier` `evalplan_maxplus_smoke`; one entry per precision, suffix `-64`/`-32`):
`BR-T3-ordered_min_is_jnp_minimum`, `-ordered_min_tie_swapped`, `-factor_fold_min_to_product`,
`-reduction_fold_max_to_sum`, `-term_fold_max_to_sum`, `-factor_seed_one_to_zero` (all first caught by
`bool_min_tie_order`); `-iverson_ignores_include` (`bool_iverson_base`); `-include_table_not_stepped`
(only `bool_scan_step_iverson_ge` catches it); `-reduce_id_zero_to_neg_inf` (`bool_min_not_product`);
guard-dropped mutants killed by a refusal case being admitted: `-iverson_admitted_in_maxplus`
(`iverson_in_real_node`), `-real_to_bool_guard_dropped` (`bool_real_to_bool_true`),
`-include_range_guard_dropped` (`bool_include_entry_2`), `-include_on_read_guard_dropped`
(`bool_read_with_include`), `-bool_to_tropical_key_guard_dropped` (`bool_bool_to_tropical_key`),
`-include_length_guard_dropped` (WEAK: `expect` is `TypeError: cannot reshape array of shape`).
The verifier stops at the first failure; a per-fixture probe confirmed other fixtures also kill the
masked mutants. Existing `jax_maxplus_mutations_python.json`: `MAX-P-native_max_zero_tie-64/-32`
changed their `expect`, because `jnp.maximum` is now caught earlier by `bool_min_tie_order`.

**Commands**

```text
python3 <worktree>/leanncd/experiments/jax_bridge/run-evalplan-maxplus.py --python <jax-python>
python3 <worktree>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <worktree>/papers/semantics/jax_boolean_reach_mutations_python.json
python3 <worktree>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <worktree>/papers/semantics/jax_maxplus_mutations_python.json
python3 <worktree>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <worktree>/papers/semantics/jax_maxplus_grad_mutations_python.json
bash <worktree>/leanncd/experiments/jax_bridge/check-lean-drivers.sh
```

Then run the five real-path runners once (the runtime is shared). The max-plus runner must run
first: the Python mutation runner reads the generated
`<worktree>/leanncd/experiments/jax_bridge/.cache/generated_evalplan_maxplus_smoke{64,32}.py`.

**Expected.** Runner: `PASS max-plus<precision>: 62 checked views, 62 refusals, 28 source views,
5 gradient input points, 20 point-forward views, 20 gradient views` for each precision. The Lean
driver line should read `generated 14 checked edge cases, 17 Boolean raw fixtures` (derived from the
patched driver text and the counts; not quoted in the evidence). Boolean Python manifest: 30/30
killed and sha-restored. Max-plus Python 18/18. Grad 8/8. `check-lean-drivers.sh` 8/8. Affine,
affine32, nonlin, scatter, logic runners exit 0. The runner counts, drivers and real-path results were
observed by the prototype after T3 Phase A (`05e0444e`); Phase B (`2c4fac2f`) added the mutation
manifests only and changed no code. The mutation results (30/30, 18/18, 8/8) are from Phase B.

**Commit:** `feat(jax): execute ordered_boolean_v1 nodes and pin raw Boolean fixtures`

## 9. T4: the six reachability fixtures on JAX (patch 04)

**Files:** `leanncd/experiments/jax_bridge/EvalPlanLogicSmoke.lean`,
`leanncd/experiments/jax_bridge/evalplan_maxplus_smoke.py`,
`papers/semantics/jax_boolean_reach_mutations_python.json`. Snapshot count 15. Prototype commits
`7b031673`, `c785fe7d` (+64/-10, 3 files).

**What lands.**

- `EvalPlanLogicSmoke.lean`: `jaxFields` emits `jax64`/`jaxpos64`/`jax32`/`jaxpos32` for all 13
  fixtures (f32 and f64 renders byte-identical). The module docstring no longer says reachability is
  checked/reference-only.
- `evalplan_maxplus_smoke.py`:
  - The logic assertion flips from 7 to 13 of 13 fixtures carrying jax fields.
  - The Viterbi-only replacement filter is removed, so the JAX values of all 13 replace the Lean
    values and the unmodified independent oracle checks them.
  - Shape assertion: `Reach` (6,6,7), `Closed` (6,6).
  - New assertion `positional_ran`: every logic fixture executes through the positional renderer,
    eager and jit.
  - The report line becomes "6 fixtures run on JAX (named/positional x eager/jit) and verified by the
    BFS oracle". The permuted-fixture check already lives in the oracle's `reach_pins`.
- Deleted refusal cases `boolean_output` and `iverson` (max-plus template). After T3 they refuse with
  the same messages and properties as `bool_max_plus_semantics` and `iverson_in_max_plus_node`, so
  they no longer pin anything of their own.
- Patch 04 touches neither `evalplan_affine_runtime.py` nor `EvalPlanCodegen.lean`.

**Observed values.** Reachability `Closed` has 19 true pairs. The chain fixture has
`Reach[0,5,:]` = `[0,0,0,0,0,1,1]`.

**Mutation controls: 3** (verifier-side wiring controls, `task` `T4`, `control_class`
"verifier wiring control", `runs` both precisions in one entry):
`BR-T4-stale_baseline_reachability_inputs` (killed by the exact JAX-vs-checked comparison),
`BR-T4-closed_taken_from_hop_4` (killed by the BFS oracle),
`BR-T4-positional_skipped_for_reachability` (survived until `positional_ran` was added). Their `expect`
strings contain `array([[[1., 1., ...` prefixes. Run them at the T4 boundary (below) and again in
final verification (section 11), where the full 33-entry manifest runs so that all 33 are observed together
on the final tree, which the prototype never did.

**Commands** (T4 changes no shared runtime or emitter code, so the affine, affine32, nonlin and
scatter runners are not rerun here):

```text
bash <worktree>/leanncd/experiments/jax_bridge/check-lean-drivers.sh
python3 <worktree>/leanncd/experiments/jax_bridge/run-evalplan-maxplus.py --python <jax-python>
bash <worktree>/leanncd/experiments/jax_bridge/run-evalplan-logic.sh
```

**The three `BR-T4-*` controls at the T4 boundary.** `mutation_python_manifest.py` has no task filter, so
the full manifest would re-run the 30 `T3` entries too. Write a filtered copy with only the `T4` entries
(entries resolve `file` relative to the RUNNER's directory, so the copy may live anywhere), then run it.
The runner needs the `.cache/generated_evalplan_maxplus_smoke{64,32}.py` modules that the max-plus runner
command above just produced. Do not pass `--observe` (it rewrites the manifest).

```text
python3 -c "import json; p='<worktree>/papers/semantics/jax_boolean_reach_mutations_python.json'; e=[x for x in json.load(open(p)) if x.get('task')=='T4']; json.dump(e, open('<worktree>/leanncd/experiments/jax_bridge/.cache/t4_controls.json','w'), indent=1); print(len(e))"
python3 <worktree>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <worktree>/leanncd/experiments/jax_bridge/.cache/t4_controls.json
```

The first prints `3`. The second must print three `PASS ... | killed | restored` lines and exit 0; anything
else is a STOP. Do not commit the copy (`.cache/` is gitignored). The final phase still runs the full
33-entry manifest.

**Expected** (observed by the prototype at `c785fe7d`, each run once): `check-lean-drivers.sh` exit 0
(8 drivers). Max-plus runner exit 0 with `62 checked views, 58 refusals, 52 source views, 5 gradient
input points, 20 point-forward views, 20 gradient views` per precision. `run-evalplan-logic.sh` exit
0 (13 fixtures). The three controls were observed killed by the prototype (one only after
`positional_ran` was added); the filtered-copy run itself is a first observation, record it.

**Commit:** `test(jax): run the six reachability fixtures on JAX against the BFS oracle`

## 10. T5: documentation (patch 05)

**Files (7):** `leanncd/AGENTS.md`, `leanncd/LeanNCD/Eval/Plan/AGENTS.md`,
`leanncd/LeanNCD/Eval/Plan/Executable.lean` (comment-only), `leanncd/docs/test_portfolio.md`,
`leanncd/experiments/jax_bridge/EvalPlanCodegen.lean` (one-line whitespace revert, below),
`leanncd/experiments/jax_bridge/README.md`, `papers/f32_jax_mutations_post.json` (`J3` `expect`
refresh, below). Cumulative snapshot file count 19. Prototype commits `7bf46907`, `4af683c7` (T5b) and
`b46cef9d` (T5c); prototype tip `b46cef9d`. Diff size: +125/-43 over 7 files (`git apply --numstat` on `05.patch`, run from the repo root).

**What lands.**

- In `Executable.lean`, the module-header bullet and the `jaxRealCarrier` doc comment said a Boolean
  destination or source is refused under every profile. They now say so only by default, and name
  `.maxPlus`/`.booleanReach`.
- README:
  - Refusal-table rows for the Boolean destination and for a bool source into sum-product.
  - A new `realToBool` row (still forbidden).
  - The Iverson row is split: lowered only in Boolean-algebra nodes, `iversonFactor` elsewhere. The
    error names in that table are the emitter's `unsupportedDestDType`/`unsupportedSourceDType`,
    mapped from the gate's `destinationDType`/`sourceDType`.
  - The stale "no JAX Boolean execution ... none planned" and "Lean-side only" sentences are rewritten.
  - New subsection "Boolean reachability on JAX": record contract, runtime semantics, runner counts,
    the known jit limitation, mutation records.
- `leanncd/AGENTS.md`: the JAX-bridge row and the "Boolean outputs are admitted" bullet.
- `LeanNCD/Eval/Plan/AGENTS.md`: profile/gate lines and scan lines.
- `test_portfolio.md`: the stale "JAX remains explicitly refused" is fixed, and a paragraph is added
  for the pins and the two manifests.
- T5c (`b46cef9d`, folded into patch 05):
  - `papers/f32_jax_mutations_post.json`, entry `J3`: its `expect` strings (`ExecutableTest.lean:586:0:
    Expression`, `:1861:0:`) were stale BEFORE this slice (line 586 was blank). The cycle was run on the
    tip: KILLED, with errors at several `ExecutableTest.lean` lines. `expect` is now
    `ExecutableTest.lean:587:0: Expression` and `ExecutableTest.lean:1929:0: Expression` (manifest
    `expect` strings may carry line numbers; they are quoted as is). Re-run PASS, restored
    byte-identically. `JS-L-g1` (also re-anchored by patch 01) cycled PASS unchanged: killed at lines
    2000, 2041, 2047, 2048 of `ExecutableTest.lean`, including `ExecutableTest.lean:2000:0: Expression`.
    Both are EXPECTED TO PASS in final verification. J3 is no longer a pre-existing stale entry (this
    slice refreshed it); J4, J5, J13, J14, J15 stay stale and untouched.
  - README "Known limitation" names the concrete route: `Edge` false entries are `-0`, so 30 `Reach`
    cells are `-0`; Lean's `Closed` turns them into `+0`; under `jit` the dropped `+0` seed would leave
    `-0`. No fixture runs it (inferred from the documented pitfall).
  - README runtime paragraph states what the runtime catches and misses on metadata loss: total loss
    with no Iverson factor runs silently as sum-product (observed 2.0 vs 1.0 for two empty-factor
    terms); the emitter guards it (donor pin, `BR-T2-NO-BOOLEAN-*` mutants).
  - Patch 02's whitespace-only change to `preparedOf` in `EvalPlanCodegen.lean` is reverted; the net
    diff against `b305b363` has no change on that line.

The counts these docs claim come from the authoring evidence, not from a recount at the T5 tip: 62 /
58 / 52 / 5 / 20 / 20 per precision; 9 Lean and 33 Python manifest entries; 17 raw Boolean fixtures;
18 metadata-refusal cases. Final verification re-observes them.

**Commands**

```text
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd LeanNCD JaxExperiment
/usr/bin/git -C <worktree> diff --check
```

**Expected.** Build green (prototype: 8620 jobs, observed at `4af683c7`; not re-recorded at
`b46cef9d`, record yours). `diff --check` (run before staging) prints nothing. Then run the
stale-claim greps in section 11. Replay observed by the controller: patches 01..05 applied in order
give tree `64ece7de674cac511d8ea6bad616f08355e625f8`, identical to the prototype tip.

**Commit:** `docs(jax): document Boolean reachability on JAX`, with a one-line body: "Refresh the J3
mutation expect strings; revert an unrelated whitespace change to preparedOf."

---

## 11. Final verification (controller replay)

Run serially in `<worktree>` unless marked parallel. Record commands, exit codes and counts in the
execution record. Do not substitute an agent's "green" report for these runs.

```text
python3 <worktree>/papers/semantics/jax_boolean_reach_files/verify_package.py --task 5
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd LeanNCD Tests JaxExperiment
bash <worktree>/leanncd/experiments/jax_bridge/check-lean-drivers.sh
python3 <worktree>/leanncd/experiments/jax_bridge/run-evalplan-maxplus.py --python <jax-python>
bash <worktree>/leanncd/experiments/jax_bridge/run-evalplan-affine.sh
bash <worktree>/leanncd/experiments/jax_bridge/run-evalplan-affine32.sh
bash <worktree>/leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh
bash <worktree>/leanncd/experiments/jax_bridge/run-evalplan-scatter.sh
bash <worktree>/leanncd/experiments/jax_bridge/run-evalplan-logic.sh
/usr/bin/git -C <worktree> diff --check main
```

**Expected.**

- Verifier: `Package OK: 5 ordered patches, task 5 boundary; index unchanged.`
- Full build: exit 0. The prototype did not record a job count for this target set; record yours.
- Driver check: `all eight drivers ran clean ...`.
- Max-plus runner: both precisions `62 checked views, 58 refusals, 52 source views, 5 gradient input
  points, 20 point-forward views, 20 gradient views`.
- Five real-path runners: exit 0. Record their counts; this plan asserts none for them.
- `diff --check`: empty.

**Mutation phases.** Two groups; run each serially inside ONE worktree. They mutate and build different
files, so they may run in parallel only in separate prepared worktrees at the final commit. Never run two
mutation runners, or a runner and a build, in one worktree. Running both groups serially in `<worktree>`
is also fine. For parallel running, after the T5 commit create ONE extra worktree `<mut-py>`
(= `<primary>/.claude/worktrees/boolean-reach-mut-py`):

1. `/usr/bin/git -C <primary> worktree add --detach <mut-py> jax-boolean-reach-exec`
2. With `<mut-py>` as the current directory: `bash <mut-py>/.claude/skills/new-slice/prepare-worktree.sh`
   (supports detached worktrees; STOP if Mathlib would cold-build).
3. Provide `<mut-py>/leanncd/experiments/jax_bridge/.cache/python` (Setup step 4).
4. Run `python3 <mut-py>/leanncd/experiments/jax_bridge/run-evalplan-maxplus.py --python <mut-py>/leanncd/experiments/jax_bridge/.cache/python/bin/python`
   once: it generates the `.cache/generated_evalplan_maxplus_smoke{64,32}.py` modules the Python runner reads.

Group L (Lean manifests), run in `<worktree>`:

```text
bash <worktree>/leanncd/scripts/mutation-manifest.sh <worktree>/leanncd <worktree>/papers/semantics/jax_boolean_reach_mutations_post.json
bash <worktree>/leanncd/scripts/mutation-manifest.sh <worktree>/leanncd <worktree>/papers/semantics/jax_maxplus_mutations_post.json
bash <worktree>/leanncd/scripts/mutation-manifest.sh <worktree>/leanncd <worktree>/papers/semantics/jax_scan_mutations_post.json JS-L-g1 JS-L-g2 JS-L-e3 JS-L-e4 JS-L-e5 JS-L-c1
bash <worktree>/leanncd/scripts/mutation-manifest.sh <worktree>/leanncd <worktree>/papers/f32_jax_mutations_post.json "J3 "
```

Group P (Python manifests), run in `<mut-py>` (or in `<worktree>` if running everything serially; the
max-plus runner must have run there first):

```text
python3 <mut-py>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <mut-py>/papers/semantics/jax_boolean_reach_mutations_python.json
python3 <mut-py>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <mut-py>/papers/semantics/jax_maxplus_mutations_python.json
python3 <mut-py>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <mut-py>/papers/semantics/jax_maxplus_grad_mutations_python.json
```

**Expected kills.**

- Boolean Lean manifest: 9/9 PASS (3 `T1` + 6 `T2`).
- Boolean Python manifest: 33/33 killed and sha-restored (30 `T3` per-precision entries + 3 `T4`
  controls, each control running both precisions). The 30 `T3` results and the three controls were
  observed by the prototype at T3 and T4; the 33-entry total is a first observation.
- Max-plus Python 18/18; grad 8/8: carried from T3 (T4 only deletes two refusal cases and edits the
  logic section; no `expect` names a deleted case).
- `J3` and `JS-L-g1` were cycled by the prototype at T5c and PASSED (killed at the lines quoted in
  section 10, restored byte-identically). Expect PASS for both here; a missing `expect` string is a STOP.
- The other re-anchored existing entries (`MAX-L-SCAN`, `MAX-L-DEFAULT`; `JS-L-g2`, `JS-L-e3`,
  `JS-L-e4`, `JS-L-e5`, `JS-L-c1`) are expected killed. The evidence reports their re-anchoring and
  refreshed `expect`s but no observed cycle result, so these are first observations; record them.
  A survivor or a missing `expect` string (most likely a drifted line number) is a STOP and report;
  do not edit the `expect`.
- Select `J3` by the label prefix `"J3 "` (with its trailing space). `--check` on the f32 manifest
  WITHOUT a prefix still exits 125 because of the five stale entries J4/J5/J13/J14/J15, which are
  outside the selection and do not block the run.

**Stale-claim value greps** (after T5; package files excluded because they quote the tokens):

```text
rg -n -e 'Boolean reachability remains' -e 'no JAX Boolean execution' -e 'Lean-side only' -e 'Iverson lowering' -e '62 checked views' -e '28 checked' -e '26 refusals' -e 'seven drivers' <worktree>/leanncd <worktree>/papers --glob '!jax_boolean_reach_*'
```

Expected dispositions. They come from the plan author's grep of a scratch replay of patches 01..05
onto `b305b363`, and are not from the prototype evidence. Classify every hit; any live hit not listed
here is a finding.

| Token | Expected hits after T5 | Disposition |
|---|---|---|
| `Boolean reachability remains` | `papers/semantics/jax_maxplus_record.md`, `papers/semantics/jax_maxplus_patches/03.patch` | frozen history (the `EvalPlanLogicSmoke.lean` docstring is fixed by T4) |
| `no JAX Boolean execution` | `papers/wave_f_capability_manifest.md`, `papers/wave_f_scanplan_proposal.md`, `papers/jax_evalplan_architecture.md` | dated snapshots, left stale on purpose (parked) |
| `Lean-side only` | `jax_gqa/rnn/conv/cross_attention_session_brief.md`, `jax_scan_record.md`, `jax_maxplus_patches/04.patch` | frozen history (README fixed by T5) |
| `Iverson lowering` | `leanncd/AGENTS.md`, `EvalPlanCodegen.lean` comment, README out-of-scope list ("outside Boolean-algebra nodes") | live and correct (new text) |
| `Iverson lowering` | `papers/boolean_predicate_output_evalplan.md` | unrelated sense (source-side lowering in an older design note) |
| `Iverson lowering` | `jax_maxplus_plan.md`, `jax_maxplus_plan_record.md`, `jax_maxplus_files/authoring_evidence.json`, `jax_maxplus_patches/04.patch` | frozen history |
| `62 checked views` | `leanncd/experiments/jax_bridge/README.md` | live and correct |
| `28 checked`, `26 refusals` | `papers/semantics/jax_maxplus_plan.md` | frozen history |
| `seven drivers` | `papers/semantics/jax_maxplus_record.md` | frozen history (`check-lean-drivers.sh` now says eight) |

**Integration** (after green verification and a clean or adjudicated whole-branch review):

1. Commit the execution record (stage it by explicit path; `/usr/bin/git -C <worktree> status --short`
   must then print nothing).
2. In the primary checkout, `/usr/bin/git -C <primary> status --short` must print nothing and
   `/usr/bin/git -C <primary> branch --show-current` must print `main`. STOP and report otherwise; do
   not stash, reset or switch branches there.
3. `/usr/bin/git -C <primary> merge --no-ff jax-boolean-reach-exec -m "Merge Boolean-reachability on JAX"`,
   then confirm `/usr/bin/git -C <primary> diff --stat main jax-boolean-reach-exec` is empty.
4. Clean up your own work only. Make `<primary>` your current directory first (do not remove a
   worktree while it is your current directory). Then `/usr/bin/git -C <primary> worktree remove <mut-py>` (if created), then
   `/usr/bin/git -C <primary> worktree remove <worktree>`, then
   `/usr/bin/git -C <primary> branch -d jax-boolean-reach-exec`. Add `--force` to a `worktree remove`
   only if it refuses solely over untracked `.cache`/`.lake` content; STOP for anything tracked.

No push. Leave local `main` ahead of `origin/main` and say so in the report.

## 12. Risks and parked items (from the evidence; do not claim fixed)

- **Stale entries J4, J5, J13, J14, J15 in `papers/f32_jax_mutations_post.json`.** Their old-strings
  match 0 times. They are stale at the baseline and are not yours: J13 was confirmed at `b305b363`;
  the other four were not individually confirmed against it. Do NOT fix them. `--check` on that
  manifest without a label filter reports them and exits 125. `J3` is NOT among them: it was stale
  only in its `expect` strings, and this slice refreshed it (section 10, T5c); `JS-L-g1` needed no
  refresh.
- **Weak include-length pin.** `BR-T3-include_length_guard_dropped-*` is killed only by a jax
  `TypeError: cannot reshape array of shape` escaping the refusal loop, not by the intended ValueError
  reason check. Parked.
- **Two equivalent mutants, left out** (both scratch-run, both SURVIVED). Dropping the `isnan(b)` arm
  of `_ordered_min`: when `b` is NaN, `a <= b` is False and the else branch returns `b`. Dropping the
  stacked step include-table length guard: `_check_factors` already requires
  `len == prod(iteration_shape)`. T4 equivalents: the hop-5 `Closed` variant (no 6-node graph has a
  finite distance above 5), and a stale baseline that keeps the Lean values (JAX and Lean agree bitwise).
- **Drifting `expect` strings.** Lean manifest `expect`s carry line numbers and drift if code above
  them changes (the T2 refresh of `JS-L-*` is an example).
- **`jax_maxplus_mutations_python.json` format.** It is not in `mutation-manifest.sh` format; run it
  with `mutation_python_manifest.py`.
- **Dated snapshot docs left stale on purpose:** `papers/wave_f_capability_manifest.md`,
  `papers/jax_evalplan_architecture.md`, `papers/wave_f_scanplan_proposal.md`,
  `papers/backend_missing_functionality.md`, `papers/eval_ir.md`, `papers/scatter_affine_lhs_writes.md`,
  `papers/predicate_boolean_backend_parity.md`. Historical session briefs and records are frozen.
- **Known jit signed-zero limitation (NOT new).** Under `jit` the real sum-product fold `0 + (-0)`
  gives `-0`, because XLA drops the literal `+0` seed; Lean and eager JAX give `+0`. It is documented in
  `LeanNCD/Eval/Plan/AGENTS.md` (the "JAX ordered-reference labels ... exclude subnormals and jit
  signed zero" pitfall) and pinned as `KNOWN_DIVERGENT` in `evalplan_affine_smoke32.py`. No fixture
  is known to expose it, but a concrete route exists (K5 below).
- **Not run by the prototype:** gradients (D7); XLA rewrites of `0 + x` beyond the observed jit seed
  drop; large shapes.
- **Prose outside the patches** (plan-author observation, not in the evidence). The `Zc` fixture
  comment in `EvalPlanNonlinSmoke.lean` ("The bridge has no lowering for predicate factors") stays
  accurate for that real-algebra fixture, but is now too general. No patch touches it. Report it in the
  sweep; do not edit it.
- **Dated note citing the old `J3` line.** `papers/f32_jax_prototype_notes.md` (historical) still
  cites `ExecutableTest.lean:586:0` for `J3`. Left as is (frozen history).
- **Parked review findings** (do not implement here; cost in dispatches):
  - **K1.** No pin for an Iverson factor over a ZERO-extent axis (`include: []`, e.g.
    `Y[i] := max_k X[i,k]*[k<=i]` with `k` of extent 0). About 1 small dispatch (raw fixture + mutation entry).
  - **K2.** The empty-range scan accept neighbour (`step_count=0`, step extent 3, 9 include entries) is
    a record Lean never emits and asserts only that the run returns one result, not its value; Lean's
    real zero-step record is `scan_extentone`. Small.
  - **K3.** D6 is pinned at node level only: the six fixtures use 0/1 `Edge`, so the plan entry points
    never see non-0/1 values; a hidden input cast there would pass (none exists). About 1 dispatch
    (run `reachProg` with `Edge` = 0.5 through both renderers against Lean).
  - **K4.** No fixture combines an Iverson factor with a unary read, with two or more reads in one
    term, or with the Iverson factor first. Low risk (uniform fold; only signed-zero ties are
    order-sensitive). Park; unestimated.
  - **K5.** The `jit` `-0` route through `Closed` (see the signed-zero item above; 30 `Reach` cells are
    `-0`): a bitwise difference the BFS oracle cannot see; D2 and D6 make it reachable. Pinned
    limitation, not new; no fixture covers it. Unestimated.
  - **K6.** Earlier parked items stay: J4/J5/J13/J14/J15, the weak include-length pin, the two
    equivalent mutants, the dated snapshot docs, the too-general `EvalPlanNonlinSmoke.lean` prose.
- **Budget disclosure** (CLAUDE.md Rule 6). Prototype dispatch turn budgets (~60) were exceeded:
  T2 Phase B ~85 turns, T3 Phase A ~58, T3 Phase B ~71+ across resumes (one API outage), T4 139 tool
  calls in one dispatch. T1 was stopped by mistake and resumed. The authoring token total has not been
  measured yet (`token-report.py`). Execution budget: ≤ ~175M cumulative input tokens; record the
  measured total.

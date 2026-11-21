# JAX Boolean reachability: authoring evidence (observed, from the prototype dispatch reports)

Source baseline: `b305b363` (local main at authoring time). Prototype branch `proto-boolean-reach`, tip `c785fe7d`.
These are artifact-reported observations from the prototype implementers, re-verified by the controller only where marked
`CONTROLLER`. They are not fresh execution results from the plan write-up. Line numbers are deliberately omitted: cite identifiers.

## Package replay (CONTROLLER, observed)
The four task patches in `jax_boolean_reach_patches/` (`git diff` between consecutive task tips) apply with `git apply --check`
then `git apply`, in order 01..04, onto `b305b363`, and the resulting tree equals the prototype tip tree
(`8bd705dee6675cf692015c9e68204ddcc8ef4afc`). Task tips: T1 `15b40b9b`, T2 `30f66a7c` (commits `69f9d5be`, `4f56270f`, `30f66a7c`),
T3 `2c4fac2f` (commits `05e0444e`, `2c4fac2f`), T4 `c785fe7d` (commits `7b031673`, `c785fe7d`).
Manifests ship INSIDE the patches (a manifest's `old` strings exist only after its task's code), not as separate assets.

## Decisions (user-approved) and where they bind
D1 Iverson lowering for Boolean-algebra nodes only. D2 bool source under real sum-product admitted in the new profile only (`Closed`).
D3 new superset constructor `JaxRenderProfile.booleanReach`, `.maxPlus` unchanged. D4 step-dependent predicates admitted.
D5 `realToBool` stays refused. D6 no 0/1 input validation. D7 no gradients. Full text: `preflight/REPORT.md`.

## T1: Boolean profile and gate (commit `15b40b9b`, +306/-12, 7 files)
- `JaxRenderProfile.booleanReach` (superset of `.maxPlus`); private helpers `JaxRenderProfile.admitsMaxPlus` (true for `.maxPlus`, `.booleanReach`),
  `JaxRenderProfile.admitsBoolean` (true for `.booleanReach` only). `jaxAssignSupported` computes `maxPlus`, `boolean`, `boolSourceOk`:
  bool dest admitted under `admittedAlgebraBool` with a Boolean-capable profile; bool source admitted if max-plus, or Boolean algebra, or the
  graph's real sum-product algebra under `.booleanReach` (the `Closed` arm). `checkJaxScanSupport` uses `profile.admitsMaxPlus` for the `.negInf` test.
- No new error constructors (reuses `destinationDType`, `sourceDType`, `unsupportedAlgebra`, `scanNonRealState`). f32 Boolean algebra is the same `admittedAlgebraBool`.
- Pins in `leanncd/test/Eval/Plan/ExecutableTest.lean` (assignment level) and `ScanJaxGateTest.lean` (compiled `reachProg` scan); no pre-existing max-plus profile pins existed there.
  Observed verdicts: bool dest/Boolean algebra/bool source accepted under `.booleanReach`, refused `destinationDType 7 1 .bool` under `.realOnly`/`.maxPlus`;
  `Closed` shape accepted under `.booleanReach`, `sourceDType 7 0 0 .bool` elsewhere; real source in a Boolean statement `sourceDType 7 0 0 .f64`;
  compiled `reachProg` scan accepted under `.booleanReach` and `destinationDType 5 0 .bool` under the other two (f64 and f32); a Boolean state with `.negInf`/`.posInf` init is refused by `checkScanPlan` (`stateInitNotAdmitted 0 .negInf .bool`), not by the gate.
- Pins were built first with the profile stubbed to behave like `.realOnly`: exactly the accept pins went red.
- 3 mutants killed (`BR-T1-REAL-SRC-IN-BOOLEAN`, `BR-T1-BOOL-SRC-LEAKS-REALONLY`, `BR-T1-MAXPLUS-ADMITS-BOOLEAN`) in `papers/semantics/jax_boolean_reach_mutations_post.json`.
- Re-anchored one line each in existing manifests `jax_maxplus_mutations_post.json` (MAX-L-DEFAULT), `jax_scan_mutations_post.json`, `papers/f32_jax_mutations_post.json`.
- Pre-existing (stale at the base): entries J4, J5, J13, J14, J15 of `papers/f32_jax_mutations_post.json` (old-strings match 0 times; J13 confirmed at `b305b363`, the other four not individually confirmed against the base). Not fixed.

## T2: emitter and Iverson include tables (commits `69f9d5be`, `4f56270f`, `30f66a7c`)
- All in `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean` (+ smoke/manifests/tests). No core library change: `evalPosBool`/`allCoords` are public in `LeanNCD/Eval/Plan/Coordinates.lean`.
- New `JaxCodegenError.iversonPredicateFailed (nodeIndex termIndex factorIndex)` (fail-loud backstop; never treat an error as "included").
  New public `iversonIncludeTable nodeIndex termIndex factorIndex iterationShape b : Except JaxCodegenError (Array Nat)` next to `buildFactorTable`, calling `evalPosBool` over `allCoords iterationShape.toList`.
  `renderAffineFactor`/`renderAffineTerm` gained `(boolean : Bool := false)`; Iverson throws the existing `iversonFactor` unless `boolean`. `renderAffineFields` derives `boolean := a.algebra == admittedAlgebraBool`.
  `renderAffineNode` and `renderScanNode` now pass `.booleanReach` (no other `profile := .maxPlus` call sites). Private test helper `accepted` beside `rejectedWith`.
- Record contract (observed): node-level `"algebra": "boolean", "semantics": "ordered_boolean_v1"`; Boolean read factor `{"source_slot","safe_index","mask",["unary"],"tag":"read","real_to_bool":False}` (no `bool_to_tropical`);
  Iverson factor `{"tag":"iverson","include":[0|1,...]}`, one entry per coordinate of the term's full `iteration_shape` (context++output++reduction, `allCoords` order, stacked step-major in step blocks);
  scan records need no `state_init`/`semantics`; the `Closed` node (real destination reading a bool source) is a plain real record with no tag/algebra keys; f32 and f64 renders of `reachProg` are byte-identical (dtype is not emitted).
- Observed: `reachProg` base include = 36-entry identity diagonal; step-block table sizes 216 (term 0) and 1296 (term 1); toy `S[j,l+1] := S[j,l] · [j ≤ l]` (axis j = 3, iter l = 4) gives include `[1,0,0,1,1,0,1,1,1]`.
  Unary read in a Boolean statement renders (`"unary":"exp"`); no refusal added.
- Phase A flipped in-file guards on the affine render legs only: the `boolSource` standalone and plan-level guards, the `buildAssignFixture` boolSource eval, `mixedBoolDest` (its `renderAffinePlanNamed` leg is now `unsupportedSourceDType 1 0 0 .f64`),
  `testVariantBPlanAuthoritySubstitutionRejected` (affineReference leg replaced by einsumOnly), `step1Bool` positional, `f32BoolSourcePrepared?` two legs. Einsum and candidate legs stay refused. `ScanIversonRefusalTest` unchanged and green.
- Phase B pins: `reachProg`/Closed/f32/step toy pins are in `leanncd/test/Eval/Plan/ScanAffineEmitTest.lean` (in the `JaxExperiment` glob; `EvalPlanCodegen.lean` does not import `tlprog!`); per-`PosBoolExpr`-family table pins and the backstop pin are in `EvalPlanCodegen.lean`.
  All 12 table pins were cross-checked against an independent python enumeration (agreement, no differences; `ieq` chosen as `i + j = 3` so it differs from `eq`). Backstop: `iversonPredicateFailed 4 5 6` for a too-wide leaf, a too-narrow leaf, and a bad leaf under `and`/`not`; accept neighbour `[1,0,0,1]`.
  The `EvalPlanMaxPlusSmoke.lean` `gateMatrix` row that expected a Boolean destination refused was changed to Boolean signatures expecting acceptance (the old row, a Boolean destination over an f64 source, was still refused, so the driver passed unchanged; the mixed case stays pinned by `mixedBoolDest`).
- 6 mutants killed (`BR-T2-INCLUDE-ORDER`, `BR-T2-NO-CONTEXT-COORDS` (only the step toy pin kills it), `BR-T2-ERROR-AS-INCLUDED`, `BR-T2-NO-BOOLEAN-NODE-META`, `BR-T2-NO-BOOLEAN-READ-TAG`, `BR-T2-IVERSON-ADMITTED-EVERYWHERE`). The two metadata mutants are observed killed only by the donor pin (the in-file failure stops `ScanAffineEmitTest` from building).
  Re-anchored `MAX-L-SCAN` (`(profile := .maxPlus)` became `(profile := .booleanReach)`, mutant still reverts to `.realOnly`) and `JS-L-e4`; expects of `JS-L-e3/e4/e5/c1` (shifted by 91 lines) and `g2` (2 lines) refreshed. `mutation-manifest.sh` expects carry line numbers and drift.
- T2c (`30f66a7c`): `EvalPlanLogicSmoke.checkStructure` refusal asserts flipped to accepts (2 insertions, 7 deletions) because `check-lean-drivers.sh` was red at the T2 boundary ("JAX unexpectedly admitted a Boolean scan", observed at `69f9d5be`); `jaxFields` unchanged (T4).
- CONTROLLER observed at `30f66a7c`: `check-lean-drivers.sh` all eight drivers PASS; max-plus runner 28 checked views / 26 refusals per precision (unchanged from before the slice).

## T3: runtime and raw fixtures (commits `05e0444e`, `2c4fac2f`)
- `evalplan_affine_runtime.py`: `_ordered_min = where(isnan a, a, where(isnan b, b, where(a <= b, a, b)))` (no JVP); `_algebra` gains `"boolean"` requiring `semantics == "ordered_boolean_v1"` returning `(_ordered_min, dtype(1), _ordered_max, dtype(0))`;
  `_check_factors(terms, algebra)` dispatches on the factor op: Boolean reads need `tag: "read"`, `real_to_bool` exactly `False`, no `bool_to_tropical` key; Iverson needs `tag: "iverson"` and `include` of length `prod(iteration_shape)` with entries exactly int 0 or 1 (Python `True` refused);
  `tag: "iverson"` is refused in real and max-plus nodes (D1); an `include` key on a read is refused in any algebra (not requested; added by the implementer). `_run_term` has an Iverson branch before any `source_slot` access: `where(include, factor_id, reduce_id)`.
  `_run_scan_node` stacks include tables step-major as `(None, include)` beside `safe_index`/`mask` (slicer has a `safe is None` branch). Boolean scan records need no `state_init`.
- `EvalPlanMaxPlusSmoke.lean`: new `booleanRaw` (reuses `rawFixture`, written to `checked.py` as a `BOOLEAN` list; `ADVERSARIAL` stays 14) and helper `blScanFixture`; 17 raw Boolean fixtures, bits from Lean, all matching bitwise in float64 and float32, eager and jit.
  Table (value is identical in f64 and f32): `bool_min_tie_order` `[+0,-0]`; `bool_max_tie_reduction` `[-0,+0]`; `bool_max_tie_terms` `[-0,+0]`; `bool_min_not_product` `[.5,1,0,.5]`; `bool_max_not_sum` `[1,.5]`; `bool_nan_factor_fold` all NaN; `bool_nan_reduction` `[nan,nan,1]`;
  `bool_iverson_base` `[[.5,1,0],[0,.25,1],[0,0,.5]]`; `bool_iverson_reduction` `[.2,.3,.7]`; `bool_scan_step_iverson` `[[1,1,1,1],[.5,0,0,0],[1,0,0,0]]`; `bool_scan_step_iverson_ge` `[[1,1,0,0],[.5,.5,.5,0],[1,1,1,1]]` (the shrinking `[l<=j]` dual: the monotone `[j<=l]` toy cannot tell a stepped include table from an unstepped one);
  `bool_unary_sqrt_oob` `[.5,-0,0,0]`; `bool_unary_exp_oob` `[1,0,1,1]`; `real_dest_reads_bool_source` `[.5,-3,2,.25]` (-0 was dropped from this fixture: see parked jit divergence); `bool_bare_oob` `[1,0,0]`; `bool_empty_factors` `1`; `bool_zero_reduction` `0`.
  float32 scan toys need a real `tensor f64 Closed(j)` plus consumer `Closed[j] := S[j, 3]`, otherwise the retag leaves the plan at f64 storage and Lean's `runDenseScan32` raises `storageKindMismatch`.
- 18 metadata-refusal cases (one-field clones; each asserted for its own message; ValueError in eager and jit, both precisions): wrong/unknown/missing/max-plus semantics ("boolean requires ordered_boolean_v1 semantics"), `semantics_without_algebra` ("real nodes use the legacy metadata-free format"), `real_to_bool` true/missing, `bool_to_tropical` key present, missing tag (all "boolean read requires explicit tag read, real_to_bool false, no bool_to_tropical"),
  unknown tag ("unknown factor tag 'future'"), include short/long/entry 2/entry `True` ("iverson include must be one 0/1 entry per iteration coordinate"), `bool_read_with_include` ("include is only valid on an iverson factor"), `iverson_in_real_node` and `iverson_in_max_plus_node` ("iverson factors require boolean algebra"; the max-plus clone has a correct-length include), and 2 scan-level cases at `step_count=0` (bad include, include entry 2). Accept neighbours: the unmodified record, and an empty-range scan with a valid step block.
- Runner after Phase A: 62 checked views and 62 refusals per precision (was 28/26); source views 28, gradient points 5, point-forward 20, gradient views 20 unchanged. Real-path runners (affine, affine32, nonlin, scatter, logic) and `check-lean-drivers.sh` (8/8) green.
- Python mutation manifest `papers/semantics/jax_boolean_reach_mutations_python.json`: 15 mutants as 30 per-precision entries (old layout; the later efficiency rule is one entry per mutant with both precisions), all killed in both precisions and restored sha-clean, confirmation run twice. Existing `jax_maxplus_mutations_python.json` 18/18 killed (two entries `MAX-P-native_max_zero_tie-64/-32` changed their `expect`: `jnp.maximum` is now caught earlier by `bool_min_tie_order`); grad manifest untouched 8/8.
  Mutants and first-failing fixture (the verifier stops at the first failure; a per-fixture probe confirmed other fixtures also kill the masked ones): `_ordered_min`→`jnp.minimum`, tie `<=`→`<`, factor min→`*`, reduction max→`+`, term max→`+`, factor seed 1→0 (all first caught by `bool_min_tie_order`); Iverson ignores include (`bool_iverson_base`); include not stepped (`bool_scan_step_iverson_ge`, the only fixture that catches it); reduce id 0→-inf (`bool_min_not_product`);
  guard-dropped mutants killed by refusal cases admitted: iverson-in-non-Boolean (`iverson_in_real_node`), `real_to_bool` (`bool_real_to_bool_true`), include 0/1 range (`bool_include_entry_2`), include on read (`bool_read_with_include`), `bool_to_tropical` key (`bool_bool_to_tropical_key`).
  Weak pin: the include-length-guard-dropped mutant is killed only by a jax `TypeError: cannot reshape array of shape` escaping the refusal loop (not by the intended ValueError reason check); recorded as parked.
  Equivalent (left out, scratch-run, both SURVIVED): dropping the `isnan(b)` arm of `_ordered_min` (when `b` is NaN, `a <= b` is False so the else branch already returns `b`); dropping the stacked step include-table length guard (`_check_factors` already requires `len == prod(iteration_shape)`).

## T4: the six reachability fixtures on JAX (commits `7b031673`, `c785fe7d`, +64/-10, 3 files)
- `EvalPlanLogicSmoke.lean` `jaxFields`: emits `jax64/jaxpos64/jax32/jaxpos32` for all 13 fixtures; f32/f64 renders byte-identical. `evalplan_maxplus_smoke.py`: logic assertions flipped (jax fields on 13 of 13), Viterbi-only replacement filter removed so JAX values of all 13 are replaced into the logic fixtures and checked by the unmodified independent oracle; shape assertion (`Reach` (6,6,7), `Closed` (6,6));
  new assertion `positional_ran` (every logic fixture executes through the positional renderer, eager and jit). The permuted-fixture check already lives in the oracle's `reach_pins`. No tolerance anywhere. The T4 diff does not touch `evalplan_affine_runtime.py` or `EvalPlanCodegen.lean`.
- Old refusal cases `boolean_output` and `iverson` were deleted: after T3 they refuse with the same messages/properties as `bool_max_plus_semantics` and `iverson_in_max_plus_node`.
- Counts per precision (f64 = f32): checked views 62, refusals 58 (was 62), source views 52 (was 28; +24 reachability), gradient points 5, point-forward 20, gradient views 20. Observed: reachability `Closed` has 19 true pairs; chain `Reach[0,5,:]` = `[0,0,0,0,0,1,1]`.
- 3 controls (verifier-side, labelled as such): `BR-T4-stale_baseline_reachability_inputs` (killed by the exact JAX-vs-checked comparison), `BR-T4-closed_taken_from_hop_4` (killed by the BFS oracle; a hop-5 variant is equivalent because no 6-node graph has a finite distance above 5),
  `BR-T4-positional_skipped_for_reachability` (survived until the `positional_ran` assertion was added). A "stale baseline that keeps the Lean values" mutant is equivalent (JAX and Lean agree bitwise). `expect` strings contain `array([[[1., 1., ...` prefixes.
- Final suites at the T4 tip (each once): `check-lean-drivers.sh` exit 0 (8 drivers), max-plus runner exit 0, `run-evalplan-logic.sh` exit 0 (13 fixtures). Affine/affine32/nonlin/scatter runners were not rerun in T4 because the shared runtime and emitter are untouched.

## Parked / disclosed (do not claim fixed)
- Real-path jit divergence: under `jit` the real sum-product fold `0 + (-0)` gives `-0` (XLA drops the literal `+0` seed); Lean and eager JAX give `+0`. Pre-existing, outside this slice (the six fixtures never produce -0). Fix would be an ordered-add seed on the real path (~1-2 dispatches); needs a user decision.
- Stale mutation entries J4/J5/J13/J14/J15 in `papers/f32_jax_mutations_post.json`; `jax_maxplus_mutations_python.json` is not in `mutation-manifest.sh` format (uses `mutation_python_manifest.py`).
- `expect` strings with line numbers in Lean manifests drift if code above them changes.
- Not run by prototypes: gradients (out of scope, D7); XLA rewrites of `0 + x` beyond the observed jit seed drop; large shapes.
- Budget disclosure (CLAUDE.md Rule 6): dispatch turn budgets (~60) were exceeded: T2 Phase B ~85 turns, T3 Phase A ~58, T3 Phase B ~71+ across resumes (one API outage), T4 139 tool calls in one dispatch. T1 was stopped by mistake and resumed. Authoring token total: to be measured with `.claude/skills/slice-plan/token-report.py` (not yet measured).

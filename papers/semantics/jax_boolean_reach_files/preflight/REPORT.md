# Preflight report: JAX Boolean reachability (captured from the preflight audit, 2026-11-19)

Base: main b305b363. Labels: OBSERVED = ran in Lean; READ = from code; ESTIMATE.
Raw dumps next to this file: plan_dump.txt, edge_values.txt, step_iverson.txt, minmax_ties.txt
(drivers: ReachPlanDump.lean, ReachEdgeValues.lean, StepIversonProbe.lean, MinMaxTies.lean).

## Decisions taken by the user (all recommendations accepted)
- D1 Iverson lowering for Boolean-algebra nodes ONLY (real sum-product and max-plus Iverson stay refused with `iversonFactor`).
- D2 Admit a bool SOURCE under real sum-product in the NEW profile only (needed by `Closed`); do not rewrite the fixture.
- D3 New superset render profile constructor passed by renderAffineNode/renderScanNode; `.maxPlus` keeps its meaning; re-anchor manifest entry MAX-L-SCAN.
- D4 Step-dependent predicates (e.g. `[j <= l]` in a step block) are ADMITTED (stacked table handles it); pin with one raw fixture. No refusal.
- D5 `realToBool` stays refused with a located error.
- D6 No 0/1 validation of Boolean inputs (mirror Lean), documented.
- D7 Gradients out of scope.
Also agreed: real carrier with explicit casts (NOT jnp.bool_); general PosBoolExpr grammar (rel lt/le/eq/ne/ge/gt over embed/mul/abs, and/or/not, ieq) over context++output++reduction coordinates; the mask is decided IN LEAN (shared helper next to `evalPosBool`, also used by Dense's own Iverson arm), runtime evaluates no predicate; evidence/einsum/scatter/candidates stay real-only.

## Q1 checked plan of reachProg (OBSERVED, plan_dump.txt)
Slots: 0 Edge 6x6 bool input; 1 Reach 6x6x7 bool; 2 Closed 6x6 f64. Exports Reach, Closed.
Scan node 0: history extent [7], step extents [6], one state slot 1, initValue .zero.
- Base assign: dest dtype .bool, algebra admittedAlgebraBool = {factorOp .min, factorId .bool true, reduceOp .max, reduceId .bool false}; one term, iteration shape [6,6]; sole factor `.iverson (rel .eq (affine [1,0]) (affine [0,1]))` = [i = j].
- Step block: same algebra, context shape [6]. Term0 `Reach[i,j,h]` shape [6,6,6] ctx pos [0]; term1 `Reach[i,k,h] . Edge[k,j]` shape [6,6,6,6], reduction over pos 3 (k), two reads. `.` = factor op min, `+` = term fold max. No cast flags set anywhere (bool->bool reads do not coerce).
- Writes: base output at h=0; step write (r,i,j)->(i,j,r+1).
- Node 1 Closed: real sum-product (mul/1, add/0), one read of slot 1 (bool) bias [0,0,6], NO cast flag: a bool source feeding a real destination.
- f32 retag identical except Closed dtype f32 / admittedAlgebraF32; Boolean algebra keeps same .bool constants.
Current refusals: checkJaxScanSupport -> destinationDType 0 0 .bool (Executable.lean ~:292) under both profiles; renderAffinePlanNamed/Positional -> unsupportedDestDType 0 0 .bool. Behind it (READ): unsupportedAlgebra (:294), sourceDType (:307), iversonFactor 0 0 0 in renderAffineTerm (EvalPlanCodegen ~:563). Closed alone: sourceDType 1 0 0 .bool under realOnly and maxPlus (OBSERVED).
HAZARD (READ): renderAffineFields (~:576) tags a node only when max-plus; a Boolean node that passed the gate would be emitted as plain real sum-product and silently compute +/*. Profile switch and Boolean metadata MUST land in the same task.

## Q2 Lean semantics to mirror
- admittedAlgebraBool = (factorOp min, reduceOp max, factorId 1, reduceId 0) over the real carrier; floatOps/float32Ops decode .bool true/false to exact 1/0 (Dense.lean ~:76-119).
- Iverson factor (Dense.lean ~:258-262): `if evalPosBool iter b then factorId else reduceId`: 1/0 Boolean, 0/-inf max-plus, 1/0 real.
- Casts (Dense.lean ~:159 gatherFactorWith): with either cast flag, in-bounds v != 0 -> factorId else pad; NaN true, +-0 false, +-inf true; OOB pad not cast. No cast occurs in the six fixtures.
- Ties (OBSERVED minmax_ties.txt): minNaN = `if a <= b then a else b` (first arg on tie: min(+0,-0)=+0, min(-0,+0)=-0); maxNaN = `if a <= b then b else a` (second arg on tie); both return the first NaN seen. JAX needs `_ordered_min = where(isnan a, a, where(isnan b, b, where(a<=b, a, b)))`; jnp.minimum/maximum are NOT safe.
- Values are NOT normalised to {0,1} (OBSERVED edge_values.txt; reference, plan64, plan32 agree bitwise): Edge true=0.5 -> 0.5 propagates; true=2.0 or +inf -> same as 0/1 baseline (min clamps); true=-1 -> only diagonal survives; false=-0 -> 30 Reach cells -0, Closed turns them +0; one NaN anywhere (even unreachable) -> all Closed NaN.
- Per statement: factor fold min seeded 1 in declared order; row-major reduction over k with max seeded 0; term fold max seeded 0; OOB pad and empty reduction 0; Closed uses existing real path. f32 changes nothing (Boolean ops are exact selections).
- Detectability: swapping max for + is caught (1+1=2); swapping min for * or using jnp.minimum/maximum is NOT caught by the six fixtures (only +0 and 1.0 appear) -> raw fixtures with Edge=2.0 (kills *), -0 (tie order), NaN (NaN order) are REQUIRED; BFS oracle cannot validate them, so they cannot be logic fixtures.

## Q3 Door inventory / blast radius (READ unless noted)
Lean gate (Executable.lean): jaxAssignSupported refuses dest dtype (:292), algebra (:294), source dtype (:307); JaxRenderProfile (:236) has realOnly/maxPlus only. New profile: accept bool dest w/ Boolean algebra; bool sources under Boolean AND under real sum-product (Closed); stay refused under .realOnly; realToBool stays refused. checkJaxScanSupport (:399): Boolean state .zero already passes (not a door). Pinned+unaffected (default realOnly): ExecutableTest :587 :589 :624 :626 :712 :714 :768 :1269 :1933 :2014.
Emitter (EvalPlanCodegen.lean): renderAffineTerm :563 refuses Iverson -> flips for Boolean nodes only; renderAffineFields :576 / renderAffineFactor :553 max-plus-only metadata -> need Boolean metadata; renderAffineNode :691 / renderScanNode :823 pass `profile := .maxPlus` -> switch; lowerTerm :304 + requireNoIverson :188 (einsum, candidates) stay refused. In-file guards: boolSource* (:1502-1535) affine+buildAssignFixture legs flip (einsum/candidate legs stay); f32BoolSourcePrepared? (:2273) same; mixedBoolDest (:1628-1630) flips for affine render; step1Bool (:1676+) flips for affine render; Iverson guards (:1431-1452, :2286-2293) stay refused (D1 Boolean-only).
EvalPlanMaxPlusSmoke.lean gateMatrix: line 27 (Boolean refused by renderAffineAssign) flips; line 28 (checkJaxAssignSupport default profile) stays refused; lines 41-43 (Iverson under max-plus) stay refused (D1). ScanIversonRefusalTest.lean 2 emitter #guards (real-algebra scans) stay refused.
EvalPlanLogicSmoke.lean: checkStructure (:135-145) and jaxFields gate (:184) flip; driver runs in check-lean-drivers.sh.
Runtime (evalplan_affine_runtime.py): _algebra (:157), _check_factors (:170), _run_term (:214-241, reads source_slot unconditionally), step-table stacking in _run_scan_node (:526-537, reads safe_index/mask from every factor), step validation (:516-518), _run_scatter_node (:297, stays real-only). NOTE: line numbers drift; cite identifiers.
Verifier evalplan_maxplus_smoke.py: :332-335 (only 7 logic fixtures carry jax fields), :354 (viterbi-only filter), :366 (reachability "checked/reference-only") flip; refusal cases boolean_output (:241), iverson (:247) need rethinking (would be refused only by accident); real_to_bool (:250) stays refused.
Mutation manifests: none asserts a Boolean refusal but anchors break: jax_maxplus_mutations_post.json MAX-L-SCAN anchors `(profile := .maxPlus)` in renderScanNode; MAX-L-DEFAULT anchors the `let maxPlus := ...` line; python manifests anchor `if f.get("bool_to_tropical", False):` and `jnp.where(a <= b, b, a)` (must stay unique once _ordered_min is added).
Docs: README rows ~229,230,233, ~241 ("no JAX Boolean execution ... none planned"), ~26-28, ~433-435, ~548-582; leanncd/AGENTS.md ~367, ~393; LeanNCD/Eval/Plan/AGENTS.md ~52-53, 62, 70-72, contract (c) ~41; EvalPlanNonlinSmoke.lean ~1717 prose.

## Q4 Lean-decided mask table (OBSERVED + READ)
`allCoords t.iterationShape |>.map (evalPosBool . b)` gives the exact identity diagonal for [i=j] (36 entries). Order matches Dense (iter built at context, output, reduction positions; Dense.lean ~:250-255) and buildFactorTable's allCoords iterationShape order, so the table lines up one-to-one with each factor's safe_index/mask including step-major stacking in step blocks (contextPos == #[0] enforced by renderScanBlockNodes; step contexts from mixedRadixUnrank). Factor-predicate basis is context ++ output ++ reduction (lowerFactorPredicate, Compile.lean ~:691), unlike the `where=` mask basis. evalPosBool's only error is affineWidthMismatch -> predicateWidthMismatch; checkAssign (Check.lean ~:295-297) already rejects it (unreachable) but keep a located fail-loud backstop (unlike axiswiseIncluded which treats an error as "included"). Step-dependent `[j <= l]` (OBSERVED step_iverson.txt): stacked table [1,0,0, 1,1,0, 1,1,1] matches Dense.
Suggested record field on an Iverson factor: `{"tag": "iverson", "include": [0|1, ...]}`, length = product of iteration_shape, allCoords order, stacked step-major in step blocks; ONE shared public helper (e.g. `iversonIncludeTable`) next to evalPosBool, also called by Dense's Iverson arm. Precedent: renderAxiswiseNode's `"include"` from axiswiseIncludedPredicate.

## Q5 Runtime delta (READ)
- New `_ordered_min` (where-based, no custom JVP).
- `_algebra`: add "boolean" with its own semantics marker (e.g. ordered_boolean_v1) -> (_ordered_min, 1, _ordered_max, 0).
- `_check_factors`: dispatch on algebra kind; Boolean nodes accept `tag: read` with explicit real_to_bool False and no bool_to_tropical, or `tag: iverson` with `include` of the right length.
- `_run_term`: Iverson branch BEFORE any source access: where(include, factor_id, reduce_id), table through the slicer in step blocks; unary flag `max_plus = factor_op is _ordered_add` is correctly false for Boolean.
- `_run_scan_node`: stack include tables with safe_index/mask; pass algebra to step validation; init "zero" already serves Boolean (no state_init key).
- Pads/seeds: pad and reduction seed 0, factor seed 1, empty source fills 0. float32: no change.
- Input boundary: Edge arrives as float in the carrier dtype; _require_dtype checks dtype only; neither side validates 0/1.

## Q6/Q7 other risks and task proposal (ESTIMATES)
No new door for same-step state reads with k-reduction or write geometry (same mechanisms as Viterbi). Verifier: remove the Viterbi-only replacement filter (:354) so oracle.verify(replaced) checks JAX reachability against BFS (oracle reach_pins already supports it, evalplan_logic_smoke.py ~:169-202); flip :332-335 and :366; fixture count stays 13 with 13 (not 7) carrying jax fields. Landing order matters (see HAZARD).
| T1 | New render profile in Lean: Boolean dest/algebra; bool sources under Boolean and under real; .realOnly unchanged | ~8 #guards | 3 cycles | Executable.lean + a test | - |
| T2 | Emitter: Boolean metadata, shared Iverson include-table helper (also used by Dense), located backstop, switch renderers to the new profile, flip in-file guards, gateMatrix, checkStructure | 0 new (flips) | 4-5 | EvalPlanCodegen.lean, Dense.lean/Coordinates.lean, EvalPlanMaxPlusSmoke.lean, EvalPlanLogicSmoke.lean, max-plus manifests (anchors) | T1 |
| T3 | Runtime + raw Boolean fixtures: _ordered_min, algebra/factor checks, Iverson branch, scan stacking; raw fixtures: tie order, NaN order, Edge=2.0, Iverson in base and step blocks (incl. step-dependent), metadata refusals | 8-12 raw x both precisions | ~6 | evalplan_affine_runtime.py, raw driver (EvalPlanMaxPlusSmoke extension or new EvalPlanBooleanSmoke), verifier | T2 |
| T4 | Six reachability fixtures end to end: jax fields, flip verifier asserts, BFS oracle on JAX values, named/positional x eager/JIT x f64/f32 | 6 | 2-3 | EvalPlanLogicSmoke.lean, evalplan_maxplus_smoke.py, maybe run-evalplan-maxplus.py | T3 |
| T5 | Docs | - | 0 | README, both AGENTS.md, new record | T4 |
Total ~15-17 mutation cycles (max-plus was ~27).

## Not determined by the preflight
No JAX/Python was run (runtime behaviour on Boolean records is design-level). XLA rewrite of `0 + x` (-0 -> +0) in the real fold not checked (six fixtures never produce -0). README/AGENTS lines read only at matched windows. papers/ records not inventoried. run-evalplan-maxplus.py read only at invocation lines.

# JAX max-plus execution record

## Status and scope

Implementation and validation complete; both independent whole-branch reviews
are clean for load-bearing correctness, with nonblocking observations adjudicated
below. Executes the immutable four-patch package in
[the implementation plan](jax_maxplus_plan.md), Full path. Max-plus affine
rendering/execution only; Boolean reachability remains checked/reference-only.
No push is authorized.

## Preflight

- Base: local `main` at `fadf057d`, descendant of source baseline
  `c5000dd462d72ed0ffcd5806937aa37fa477e9b0`.
- Execution branch/worktree: `jax-maxplus-exec` at
  `/Users/williammacready/code/python/pyncd.worktrees/jax-maxplus-exec`.
  Created fresh rather than reusing the stale session worktree.
- `prepare-worktree.sh --plan papers/semantics/jax_maxplus_plan.md`: exit 0.
  Primary checkout donated 8,101 Mathlib oleans / 8,094 sources (100%);
  490 project oleans copied. No cold Mathlib build.
- Build wrapper target `LeanNCD`: exit 0, 8,615 jobs.
- `verify_package.py --task 0` with worktree-local `TMPDIR`: exit 0,
  four ordered patches, three provided manifests, index unchanged.
- Required bridge-local Python and primary reusable environment were absent.
  The permitted `setup-python.sh` installed the existing pinned CPU requirements
  in this execution worktree only, exit 0. No shared environment was modified.
- Interpreter entry:
  `/Users/williammacready/code/python/pyncd.worktrees/jax-maxplus-exec/leanncd/experiments/jax_bridge/.cache/python/bin/python`.
  Resolves to uv CPython 3.13.12; JAX 0.10.0, NumPy 2.5.2,
  `[CpuDevice(id=0)]`.
- Reviewed original controller's successful scan-Python follow-up and SCOPE-01
  negative-survival proof. Amendment controller records all strengthened
  checks passed and restoration. Renewed numerical/scope reviews supersede
  historical signoff. Their inherited legacy proof reuse is provenance,
  not execution-time validation; controller checks below will run afresh.

## T1: typed render-only admission and metadata

- Exact `01.patch`: apply-check and apply exit 0.
- `verify_package.py --task 1`: exit 0 before validation and after restoration.
  Boundary hashes are exactly the immutable `task1.json` map.
- Build wrapper targets `JaxExperiment Eval.Plan.ScanJaxGateTest
  Eval.Plan.ExecutableTest`: exit 0, 8,531 jobs.
- `run-evalplan-logic.sh`: exit 0, 13 fixtures across reference, checked
  binary64 and checked binary32; every export/history exact, no skipped checks.
- `mutation-manifest.sh` with `jax_maxplus_mutations_post.json`: exit 0,
  `MAX-L-SCAN` and `MAX-L-DEFAULT` both killed with expected diagnostics
  and restored green (2/2).
- Reviewed the three-file policy/metadata diff and exact staged scope;
  staged whitespace check passed. Commit: `c129c14c`
  (`feat(jax): admit render-only max-plus plans`).
- Orchestration incident: one extra post-restoration verifier ran concurrently
  with explicit-path staging and exited 1 solely at its final real-index
  preservation assertion. No source/patch/hash assertion failed. Immediately
  reran serially with staging finished: exit 0, index unchanged. Subsequent
  verification must not overlap any real-index write.

## T2: runtime and checked witnesses

- Exact `02.patch` apply-check/apply and task-2 boundary checks: exit 0.
- Checked-only max-plus runner: exit 0, 15.63 seconds; 52 checked views,
  44 metadata refusals, scalar signed-zero/NaN/JVP pins passed.
- Kernel Python manifest: exit 0, 159.07 seconds, 18/18 independently gated
  singleton-precision controls killed with expected diagnostics/restored.
  Gradient manifest deliberately not run at this boundary.
- Cancellation returned 1; reciprocal partial-OOB returned
  `[.5, -inf, -inf]`; mixed histories retained different zero/negative-infinity
  holes. No source-execution claim was made at T2.
- Per-task review, restored hashes, staged scope and whitespace passed.
  Commit `faf3329fef8605bf61f95f2c2c54d721757c8f47`
  (`feat(jax): execute ordered max-plus assignments and scans`).
- Auxiliary payload decoding initially used an interpreter without NumPy;
  decoding succeeded with the validated bridge interpreter, without edits.

## T3: original source programs and gradient oracle

- Exact `03.patch` apply-check/apply and task-3 boundary checks: exit 0.
- Full runner regenerated the standard bundles: exit 0, 74.25 seconds;
  52 checked / 44 refusals / 56 original Viterbi source views /
  40 gradient views / 40 point-forward executions at five mathematical points.
  Baseline/permutation point deployments overlap source scenarios.
- Kernel manifest: exit 0, 804.87 seconds, 18/18 killed/restored.
  T3-only gradient manifest: exit 0, 464.46 seconds, 8/8 killed/restored.
- Baseline path `(0,1,2,1,0,1)`, score -5.25, margin .25;
  changed winner `(2,1,2,1,0,1)`, score -4.75, margin .25;
  permuted path `(1,3,0,3,1,3)`, score -5.25, margin .25.
  Opposite near-tie sides retain positive margins `2^-47` (f64) and
  `2^-18` (f32), eight output ULPs. Full Init/Trans/Emit gradient
  permutation transport and never-read Emit zero gradients passed.
- Stale-parameter controls test verifier orchestration; permutation controls
  test oracle transport; approximate-max controls test backend comparison.
  Both complementary near-tie sides were discriminating in both precisions
  and eager/JIT modes.
- Per-task review and restored boundary/staged checks passed.
  Commit `5b0c164d568a31cf1d23dee934abb5840724d5fa`
  (`test(jax): verify Viterbi values and winning-path gradients`).
- One command misspelled the worktree directory and exited 2 before execution;
  corrected invocation passed without source edits.

## T4: coupled repins and discovery

- Exact `04.patch` apply-check/apply and task-4 package verification: exit 0.
  All fifteen cumulative snapshot entries match; index unchanged.
- Reviewed exact eight-file scope, documentation boundaries and coupled
  diagnostic/anchor repins; staged whitespace passed.
  `JS-P-05` retains its decrement/expected failure with a narrowed unique anchor.
- Commit `c267aa82`
  (`docs(jax): record max-plus boundary and repin coupled controls`).
- Parked, not repaired or counted as passed: preexisting scatter
  `JS-T1-04` has no baseline anchor; max-plus does not require its repair
  (roughly one separate Direct dispatch). **Resolved 2026-11-22** (main `a4552839`, `40b7af4a`): re-anchored; the
  scatter manifest cycles 6/6.

## Controller validation

Controller executed all twelve plan commands serially, stopping on nonzero
status. Every command exited 0; total measured command time 7,701.027 seconds.
Commands used this worktree's absolute paths and local Python; package
verification used this worktree's `.cache` as `TMPDIR`.

| Command (paths relative to this worktree) | Result | Seconds |
|---|---|---:|
| `python3 leanncd/experiments/jax_bridge/run-evalplan-maxplus.py --python <local Python>` | 52 checked, 44 refusals, 56 source, 40 gradients, 40 point-forwards | 76.921 |
| `bash leanncd/scripts/mutation-manifest.sh leanncd papers/semantics/jax_maxplus_mutations_post.json` | 2/2 killed, expected diagnostic, restored | 55.297 |
| `python3 leanncd/experiments/jax_bridge/mutation_python_manifest.py papers/semantics/jax_maxplus_mutations_python.json` | 18/18 independently gated precision entries killed/restored | 806.435 |
| `python3 leanncd/experiments/jax_bridge/mutation_python_manifest.py papers/semantics/jax_maxplus_grad_mutations_python.json` | 8/8 independently gated precision entries killed/restored | 464.870 |
| `bash leanncd/scripts/mutation-manifest.sh leanncd papers/semantics/jax_nonlin_mutations_post.json` | 8/8 killed, expected diagnostic, restored | 171.629 |
| `bash leanncd/scripts/mutation-manifest.sh leanncd papers/semantics/jax_scan_mutations_post.json` | 11/11 killed, expected diagnostic, restored | 298.478 |
| `bash leanncd/scripts/lake-build.sh leanncd LeanNCD Tests JaxExperiment` | Full requested build green, 8,847 jobs | 3.524 |
| `bash leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh` | 55 f64 / 47 f32 eager/JIT fixtures plus complete model/property/gradient checks, including real scan neighbors | 733.741 |
| `python3 leanncd/experiments/jax_bridge/mutation_python_manifest.py papers/semantics/jax_scan_mutations_python.json` | 6/6 inherited grouped entries killed/restored | 4,927.677 |
| `bash leanncd/experiments/jax_bridge/run-evalplan-affine.sh` | 20 binary64 fixtures (9 named / 10 assignment / 1 positional), eager/JIT exact bits plus gradient/fold-order pins | 83.142 |
| `bash leanncd/experiments/jax_bridge/run-evalplan-scatter.sh` | 10 f64 / 5 f32 ordered eager/JIT bit-identical; fast-mode controls passed | 78.105 |
| `python3 papers/semantics/jax_maxplus_files/verify_package.py --task 4` | All final hashes/restoration and immutable assets exact, index unchanged | 1.208 |

Additional precision-completeness validation: existing
`run-evalplan-affine32.sh` defaults, exit 0, real 93.35 seconds;
7 named + 8 assignment + 2 positional + 39 sampled corpus cases = 56 fixtures,
80 eager + 80 JIT output checks. Existing `f32Identity` divergences at
positions `[1, 2]` reproduced exactly (signed-zero/subnormal CPU limit);
all other bits matched the native Lean binary32 worker. These are explicit
known-divergence assertions, not silently skipped tests.

Scatter fast mode: 8 f64 / 3 f32 collision-free fixtures exact, two colliding
fixtures per precision within existing tolerance. Colliding values happened
to be bit-identical on this backend, not a portability guarantee.

The final complete mutation pass contains 40 distinct intents represented by
53 manifest entries: 2 Lean max + 18 kernel Python + 8 gradient Python +
8 nonlinear Lean + 11 scan Lean + 6 scan Python. T1/T2/T3 repeats add 46
earlier entry executions, for 99 entry executions across execution phases.
Inherited grouped entries establish their historical aggregate verdict only;
they do not independently certify both precision kills. No survivors or
failed restoration occurred. `JS-T1-04` remained explicitly excluded (repaired 2026-11-22, `a4552839`).

Kernel intent labels (each `-64` and `-32`): `MAX-P-omit_cast`,
`MAX-P-zero_init`, `MAX-P-freeze_time`, `MAX-P-zero_pad`,
`MAX-P-native_max_zero_tie`, `MAX-P-remove_custom_jvp`,
`MAX-P-factor_order_cancellation`, `MAX-P-first_state_init`,
`MAX-P-unary_final_oob_mask`. Gradient labels (each precision):
`MAX-AD-stale_baseline_parameters`, `MAX-AD-permutation_transport`,
`MAX-AD-approximate_max`, `MAX-AD-approximate_max_left`.
Lean max labels are `MAX-L-SCAN`, `MAX-L-DEFAULT`; inherited scan Python
labels `JS-P-01` through `JS-P-06` all passed.

## Documentation sweep

Ran all three plan-specified `rg` sweeps over Markdown, exit 0:
vocabulary (2,354 matching lines: 2,212 papers / 142 leanncd);
moved values (6,136 matching lines); refusal claims (93 matching lines:
88 papers / five leanncd). Counts describe sweep output, not tests.
`git diff --check` passed.

- Current bridge README, both updated AGENTS nodes, portfolio inventory and RNN
  brief distinguish render-only max-plus from default real-only evidence,
  candidates/einsum/scatter and continued Boolean/Iverson/min-plus refusals.
- Live refusal hits concern still-forbidden non-real scatter or unrelated
  source/oracle rules, not newly admitted max assignments/scans.
- Earlier F32 notes and additive/scan plans, records, audits and findings
  describe their historical boundaries; they are not rewritten as live status.
- Most value hits concern unrelated examples, section numbers and prior
  experiment measurements. The 3,832-case corpus remains an inventory/history
  claim, not a validation or performance claim for this execution.
- Precision audit found `run-evalplan-affine.sh` is binary64-only. To satisfy
  the plan's binary32 legacy-affine requirement, additionally run the existing
  `run-evalplan-affine32.sh` at its default sampling (17 fixed fixtures plus
  every 100th corpus case), serially after controller completion. This is an
  explicit validation-set extension, not a full-corpus run or source change.
  Preserve and report its existing pinned XLA CPU divergence; do not call it
  universal bit parity or silently skipped checks.

## Boundary identities

All source hashes are the exact entries in the immutable cumulative task maps.
Snapshot-file SHA256 identities verified by package replay at each boundary:

| Boundary | Snapshot SHA256 |
|---|---|
| T1 | `9a1a82e08f32c7a2f20f9703cdce3daab5e3b234f4df498ab81ad443fe22a766` |
| T2 | `a8f6f8ca68d99a527cec1cd294a6ded47f48d32da91f65c5d4dd0b54c8150fbf` |
| T3 | `ccb5a918e637e93b62d9ad165c247e9e1ebc68e1753c4e57a286df187a995c6f` |
| T4 | `1807092121729ddf2ad195b769c10d69e5217fc0f3b9f5c66e1c6570bc83be52` |

No patch, provided manifest, tolerance, fixture count or expected diagnostic was
changed outside the authoritative patches. Final package replay confirmed
restoration of every included source/docs/manifest hash.

## Final case x caller audit

Audited actual final tree, including unchanged siblings, not just new branches.
Identifiers are in `leanncd/LeanNCD/Eval/Plan/Executable.lean` (core),
`leanncd/experiments/jax_bridge/EvalPlanCodegen.lean` (emitter),
`EvalPlanMaxPlusSmoke.lean` (`gateMatrix`) and `evalplan_affine_runtime.py`.
Independent scope reviewer supplied the full caller trace; condensed matrix:

| Case / callers | Verdict | Final-tree evidence |
|---|---|---|
| Real standalone, named, positional | Required, unchanged | All affine routes converge on `renderAffineNode`; real records remain metadata-free; curated regressions pass |
| Real unary and nonlinear | Required in affine rendering | `allowUnary` only on affine assignments; unchanged pointwise/axiswise dispatch; complete nonlinear regression |
| Max standalone, named, positional | Required, render-only | Explicit `.maxPlus` at affine/scan renderer; original seven Viterbi fixtures, all materialized exports |
| Ordered native factor fold | Required | `_ordered_add` from +0, separate `_ordered_max` reductions/outer fold from -inf; cancellation/reversal witness |
| Single-axis zero/neg_inf histories | Required per tensor | `renderScanNode` emits every init tag when needed; `_run_scan_node` allocates complete histories before base overlay; mixed holes |
| Legacy real/extent-one/independent scans | Required, unchanged | Legacy zero default, base overlay, live step capture; scan survey and nonlinear regressions |
| Nonempty-source tropical unary OOB | Required | Final mask after safe unary; reciprocal `[.5,-inf,-inf]` |
| Empty-source tropical unary OOB | Required, distinct path | Empty source bypasses gather and unary; checked log witness |
| Unique finite-winner AD | Required at five points | Independent native prefix/path enumeration, exact full Init/Trans/Emit counts, full permutation transport and both near-tie sides |
| Boolean-source max reads, cast true/false | Required, exact checked flag | `renderAffineFactor` emits checked Boolean flag; identical stored values tested under both settings; no dtype inference |
| Boolean source under real sum-product | Forbidden, unchanged | `sourceDType` core policy; unchanged standalone/plan/evidence guards for both carriers |
| Boolean destinations / realToBool | Forbidden | Destination policy, `gateMatrix`, all six reachability refusals; `_check_factors` rejects real_to_bool metadata |
| Min-plus | Forbidden | Carrier-specific max-only opt-in, min-scan positive-inf refusal, `gateMatrix`, runtime algebra/init validation |
| Iverson emitter/runtime | Forbidden | `renderAffineTerm` retains original located error; `ScanIversonRefusalTest` covers both blocks; runtime factor-tag check |
| Iverson policy alone | Silently ignored, baseline | `jaxAssignSupported` ignores Iverson; emitter/candidate/runtime doors independently refuse; no new support claim |
| Einsum/candidates/kernel validation | Strict real-only | Default support in both candidate converters, `validateAffineTable`, `validateEinsum`, `validateAndConstructKernel`; exact candidate tables in `gateMatrix` |
| Executable plan evidence | Max/nonassign evidence forbidden | `lowerCheckPlanToCandidate`, `stepTiedToPreparedStep`, `JaxExecutableWellFormed` retain strict checked ties; rendering is not evidence |
| Scatter ordered AND fast | Non-real forbidden | Shared revalidated compute policy; runtime guard before both placement modes; existing real neighbors plus eight explicit controller refusals |
| Outer contextual assignment | Forbidden | Public support always passes `allowContext=false`; unchanged f64/f32 contextual guards |
| Private checked scan context | Required, narrowly scoped | Only scan gate invokes private context opt-in with each block's own table; immutable captures/live slicing/copy-then-write unchanged |
| Multi-axis / nested scan | Forbidden | One-axis gate and existing checked two-axis refusal; checked `BlockStep` has no nested scan constructor |
| Incompatible supplied signature | Revalidation required before policy | Storage-kind-specific assignment checker runs under supplied table; altered shape returns `invalidSignatureContext` |
| Malformed max/scan metadata | Forbidden, loud | Validation precedes empty-domain shortcuts/allocation; 44 malformed-metadata refusal views |

No newly silently ignored cell found. The checker still does not establish a
global tensor-sort theorem through arbitrary pointwise/pass-through state writers;
no stronger arbitrary raw-scan claim is made.

## Independent whole-branch reviews and adjudication

Two independent bounded reviewers inspected the complete 15-file implementation
range `fadf057d..c267aa82` and unchanged caller/oracle siblings. They did not
rerun tests; controller execution above is separate evidence. Reviewers wrote
incremental reports to separate session files, collated here to avoid concurrent
edits to this record.

- **Scope/caller/evidence: clean for load-bearing correctness.** Confirmed typed
  opt-in, signature authority, strict evidence/candidate/einsum/scatter siblings,
  refusal locations, scan restrictions and honest discovery/docs.
- **Numerical/gradient/oracle: clean.** Confirmed seeds/order/native precision,
  signed-zero selection and NaN output (function-level scalar pin: the
  right-hand-wins signed-zero max tie, which kills `MAX-P-native_max_zero_tie`;
  NaN cases assert only `isnan`, so NaN priority and fold operand order inside
  statements are NOT distinguished by the current pins; see the post-landing
  section below), custom JVP, cast false, both unary OOB paths,
  mixed-state holes, independent prefix/full-path oracle, changed winners,
  complete gradient transport and both positive-margin near-tie sides.
- **N1, nonblocking source-comment drift: parked.** Some preexisting source
  contract comments/docstrings describe zero-only scan initialization or real
  padding without qualifying the new profile. Current Markdown capability
  documentation is accurate. This does not affect execution or admission and
  does not justify changing immutable patch outputs during execution.
  A separately authorized Direct documentation follow-up would be less than
  one bounded dispatch; no package repair attempted.
- **N2, nonblocking direct scatter-refusal coverage: controller probe passed.**
  Existing permanent smoke fixtures did not directly exercise the new raw
  runtime non-real scatter guard. Controller called `_run_scatter_node` on a
  max-plus scatter record in ordered/fast modes, binary64/binary32 and
  eager/JIT: **8/8** raised exactly `ValueError("scatter requires real algebra")`.
  Existing legal real scatter neighbors already passed. This supplemental probe
  adds no fixture/manifest/source edit and is not included in 53 mutation entries
  or 99 repeated entry executions. A permanent fixture remains an optional
  future package-authoring improvement, not a correctness blocker.
- No review finding requires immutable-package correction; no load-bearing
  issue is blocked or silently deferred.

## Integration and cleanup handoff

At this record commit, the primary checkout is clean and still at `fadf057d`.
All four implementation commits above are complete, controller validation is
green, and both whole-branch reviews are clean/adjudicated. This record is
committed separately before the authorized local-main merge.

Next, without pushing: merge `jax-maxplus-exec` into local `main` with `--no-ff`,
verify branch/main tree equality and ancestry, then remove only this execution
worktree and its merged branch. Generated `.cache` build/JAX environments and
the `.superpowers/sdd/jax_maxplus_plan` ledger are identified execution artifacts,
not source deliverables; remove with this worktree only after verifying all
tracked work is committed. Preserve the user's original session worktree and
all other worktrees. Final integration/cleanup outcome is reported to the user
and represented by the enclosing merge commit; no remote push is performed.

## Budget

`token-report.py 6630c22b-deec-412b-bdb4-c2a94ef0e969` exited 0 but reported
"no transcript for session". Exact cumulative input-token, peak-context and
per-dispatch turn telemetry are unavailable. T2 reported fewer than 60 turns;
T3 reported no observed breach. No exact usage estimate is asserted.
Both independent reviewers report no known dispatch-cap breach and unavailable
exact telemetry. Total 175M-input-token compliance and exact peak/turn counts
cannot be certified from the available telemetry; no exact estimate or measured
compliance claim substitutes for it.

## Post-landing review fixes (2026-11-19)

A review of the landed work (after the merge, on branch `worktree-maxplus-review-fixes`)
found two important and several minor items. Fixed as Direct-path changes; nothing here
changes the immutable four-patch package or its recorded results above, which stay as run.

**Findings and fixes**

- **I1, multi-term gap (code/test).** The ordered-max fold over a statement's terms
  (`term_body`) was exercised only with 0 or 1 terms; dropping every term but the last
  survived the verifier. Fixed in `49f2a571`: fixture `max_multi_term_winners` (three
  max-plus terms, winners differing by coordinate, a `-inf` and a NaN in non-last terms).
- **I2, stale contract (docs).** The `renderScanNode` record contract still said states
  start at `0` and omitted the max-plus keys (`state_init`, node `algebra`/`semantics`,
  factor `tag`/`bool_to_tropical`/`real_to_bool`); the `unsupportedScanState`,
  `generateNamed`, `buildAssignFixture` and file-header comments and the runtime module
  docstring still described a real-only, zero-padded backend. This is the N1 item parked
  above. Fixed in the docs commits of this batch (comments and docstring only, no
  behavior change; `JaxExperiment` rebuilt green).
- **M1-M5, minor items.** Fixed in `60d1d7c0` (`_run_scan_node` validated step-block nodes
  only when `step_count > 0`; now it always does, pinned by `empty_step_unknown_algebra` (algebra half) and `empty_step_bad_factor_metadata` (factor-metadata half).
  The review's second hole, a max-plus scan with no `state_init` "silently zero-initialising",
  was NOT a hole: the Lean emitter writes `state_init` only when some state is `.negInf`, so
  a max-plus scan whose states all start at `0` legitimately has none. The first fix refused
  it; that was reverted (it would have rejected valid programs) and the check is now an
  accept-neighbour pinning that omitting `state_init` equals declaring every state `"zero"`),
  in `66da8b1e` (`EvalPlanMaxPlusSmoke` was not run
  by `check-lean-drivers.sh`; now registered, script says "seven drivers"), and in this
  docs batch: the README row count ("eight rows" became ten; the f32 coverage of the
  max-plus rows is stated), the `leanncd/AGENTS.md` wording on max-plus mask reads
  (Boolean-source reads admitted, Iverson predicate factors still refused), the
  `check-lean-drivers.sh` header count, a README note on max-plus gradients at ties and at
  NaN outputs (behavior probed, explicitly outside the winning-path gradient promise), and
  the NaN/operand-order pin wording below.
- **Per-precision runner line** moved from 26 checked views / 22 refusals to 28 / 26
  (both precisions together: 56 / 52); source, point-forward and gradient columns are
  unchanged. The 52 / 44 figures quoted in the sections above are the as-run
  counts at the original landing.
- **Parked by the whole-branch review of these fixes (Rule 14).**
  (a) `check-lean-drivers.sh` still does not run `EvalPlanLogicSmoke.lean` (same run-time-break
  class; about one line) — CLOSED 2026-11-19 (`b1c46c65`, now eight drivers). (b) The `step_count=0` pair in `evalplan_maxplus_smoke.py` starts from a
  record Lean never emits (step extent 3 with its tables kept); Lean's real zero-step record is
  `scan_extentone`. (c) `scanNonRealState` in `LeanNCD/Eval/Plan/Executable.lean` has a comment
  saying a tropical state is "zero-initialised", stale in the same way as the codegen comments
  fixed here — CLOSED 2026-11-19 (`d09dc8d7`). (d) At zero steps pointwise/axiswise `fn`, captures and step writes are still not
  validated.

**Pin wording corrected.** The plan and the "signed-zero/NaN selection" item above said the
scalar pins distinguish first/second NaN patterns and operand order. They do not. The
verifier asserts only `isnan` for NaN cases; the right-hand-wins signed-zero tie is pinned
only at function level, by the direct `_ordered_max` scalar pin (it kills
`MAX-P-native_max_zero_tie`). NaN priority and fold operand order inside statements are
NOT distinguished by the current pins: swapping NaN priority or the fold operands in
`_ordered_max`, `red_body` or `term_body` survives the verifier, and is
forward-value-equivalent inside statements (the factor `+0` seed turns `-0` into `+0`, and NaN
payloads are not compared). It is NOT gradient-equivalent: the `red_body` operand swap moves a
tie's whole gradient from the last to the first maximal element (`[2,2,1]` gives `[1,0,0]`),
which is why the README calls tie gradients behavior, not a promise.

**Surviving mutants.** The mutants the review found surviving (NaN-priority swap and
operand swaps in `_ordered_max`/`red_body`/`term_body`, above) are documented, not
killed; no pin was added for them in this batch.

# JAX max-plus: implementation plan

**Status: execution-ready plan; strengthened controller proofs and both renewed reviews complete. Implementation not started or authorized by this planning request.**
The temporary prototype is authoring evidence, not landed production support. The original
[numerical review](jax_maxplus_files/review_numerics.md) and
[scope review](jax_maxplus_files/review_scope.md) were clean after SCOPE-01, but do not certify
this coverage amendment. Their appended amendment reviews are now clean, and controller amendment proof passed.
The [package](jax_maxplus_files/package.json)
contains four ordered patches,
boundary hashes and three provided mutation manifests. This document contains no implementation
snippets: replay the compiled patches, do not redesign or transcribe them.
T4 retains eight touched files and fifteen cumulative snapshot entries, including the
verified scan-Python `JS-P-05` repin. Kernel/gradient manifests contain 18/8 singleton-precision
entries; the latter is T3-only. Package metadata/verifier, not inline manifest hashes, is authoritative.

**Process: Full path**, because this adds a backend capability and a soundness-sensitive admission
surface. One slice, max-plus only; no Boolean/Iverson implementation plan.
Source baseline: `c5000dd462d72ed0ffcd5806937aa37fa477e9b0`.
Execution may start from its local-main descendant containing the planning assets, provided affected
source hashes still match. Planning branch `agents/jax-maxplus-plan-strengthen` is not an implementation branch.
Authoring provenance: [authoring record](jax_maxplus_plan_record.md).
The executor creates the separate future `papers/semantics/jax_maxplus_record.md`.

**Goal.** `affineReference` renders max-plus standalone assignments, named/positional plans and
single-axis scans in native binary64 and binary32. The original seven Viterbi source variants run
eagerly and under JIT; five unique-finite-winner parameter points have exact Init/Trans/Emit
path-count gradients. The six Boolean reachability variants remain checked/reference-only with explicit JAX
refusal. Rendering is not executable evidence, and no new mathematical semiring laws are assumed.
This amendment addresses skeptical points 1–3 only: existing runtime behavior already passes the
new fixtures. It strengthens proof, not capability; performance/process point 4 is not addressed.

## 1. Execution contract

Open every execution/review brief with this preamble, replacing `<worktree>` with its absolute path:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

- Resolve angle-bracket command placeholders to literal absolute paths before running commands;
  they are not shell variables. Each displayed command is a separate invocation.
- Follow `.claude/skills/new-slice/` and `.claude/skills/slice-plan/`. Use an isolated execution
  worktree from **local `main`**, not stale `origin/main`. Do not reuse the authoring worktree.
- Patches are authoritative. For each task: apply-check, apply, boundary verification, targeted
  validation, review, explicit-path staging and commit. Stop on any mismatch.
- Never hand-repair/regenerate patches, change provided manifests, loosen a fixture/tolerance/count
  or `expect`, or use `git apply --3way`/`--reject`. A baseline conflict is BLOCKED, not permission
  to improvise. Planning assets must already be present before patch application.
- Never run a mutation runner concurrently with another mutation runner, a build, generation,
  verification or regression runner. They mutate/import the same source. `--check` is not a cycle.
- Use 40–60-line Read windows around the identifiers below; no whole-file reads over 20k characters.
  Search with `rg -n`; the boundary maps include unchanged neighbors and are not task file lists.
- Each dispatch: at most about 60 turns/250k peak context; hand off at a completed boundary before
  exceeding it. Prefer one bounded dispatch each for T1, T2 and T3; T4 is controller closeout.
  No nested delegation. Two final independent review lenses are mandatory, not repeated coding.
- Total execution cap: 175M cumulative input tokens. Authoring target: 50M. Record measured totals,
  peak context and turns, or explicit unavailability; never estimate exact telemetry.
- Builds may run in the background only while independent work proceeds. Wait for completion
  notification rather than polling. Stop if Mathlib cold-builds; fix worktree preparation first.
- No push. Final implementation merges to local `main` only after the controller's full build and
  a clean/adjudicated whole-branch review. This planning-only package does not authorize execution now.

## 2. Numerical and capability contract

### Scalar evaluation

- Factor fold: native addition, left-to-right from **+0**. Reduction and outer term folds: ordered
  max, each separately seeded with **-infinity**. Preserve term-local reduction domains.
  `max_factor_order_cancellation` checks `[L,-L,1]`, `L=2^54` exact and finite in both carriers:
  the ordered result is 1, factor reversal gives 0. The original acceptance survived that mutant;
  this is a demonstrated test blind spot, not a known current runtime defect.
- Enumerate reduction coordinates row-major, last reduction dimension fastest; retain source factor
  and term order. Do not remove seeds, reassociate, flatten folds, prune false factors, use parallel
  prefix/associative scan, or infer absorbing-zero laws from the name “max-plus.”
- Ordered max selects first NaN, otherwise second NaN, otherwise RHS when `a <= b`, otherwise LHS.
  In particular RHS wins signed-zero ties. Ordinary `jnp.maximum` is not a substitute.
- Compare finite values, infinities and signed zeros by raw carrier bits; compare NaN **patterns**.
  No universal NaN payload/sign/signaling theorem or transcendental bit-portability claim is made.
  Existing CPU normal-range/flush-to-zero limitations remain; this is not a subnormal parity theorem.
- Keep binary32 native, not widened binary64 followed by a cast. The checked binary32 worker is its
  precision-specific scalar oracle; the reference evaluator is not a native-f32 oracle.
- `boolToTropical` is the checked read flag, including **false** on a Boolean-tagged source.
  Do not infer it from dtype. For a flagged bare in-bounds read, both zeros map to -infinity;
  every nonzero value, including NaN and infinities, maps to +0.
- Bare OOB reads return the statement's -infinity pad without casting it. Tropical OOB unary
  reads return that pad without applying the primitive. In-bounds unary reads use raw values,
  and admitted checked unary reads have no cast flags. Existing real unary behavior is unchanged.
- False-mask plus opposing +infinity is NaN, not a removable branch. Empty factors yield +0;
  empty terms/reductions yield -infinity; empty output stays empty without an invalid gather.
- `_ordered_add` preserves IEEE zero-pair primal bits with a **custom JVP `da + db`**. Removing that
  JVP can leave all forward bits correct but erase a winning zero Init derivative (0 instead of 1).
- Unique finite winner gradients are exact path counts for Init/Trans/Emit; Allow is frozen.
  The spare never-read Emit row has gradient zero. No derivative promise at genuine max ties
  or nonfinite active paths, and no general automatic-differentiation theorem is introduced.

### Admission and record format

- `JaxRenderProfile.maxPlus` is a typed **core policy option**, explicitly selected by affine
  rendering. It is not a bypass around `checkAssign`/`checkAssignF32` signature revalidation.
- Shared defaults remain `.realOnly` for evidence, candidates, einsum and scatter. A successful
  renderer is not permission to stamp max-plus with `ExecutionEvidence`.
- Max assignment metadata is `algebra="max_plus"`, `semantics="ordered_max_plus_v1"`; reads carry
  `tag="read"`, exact Boolean `bool_to_tropical` and `real_to_bool=False`. Real records stay in
  their legacy metadata-free format. Unknown/missing/ill-typed max metadata must fail loudly.
- A scan containing negative-infinity initialization carries `state_init` entries `zero`/`neg_inf`
  and `semantics="ordered_scan_v1"`. Legacy real scans without these keys still initialize to zero.
  Reject invalid init tags, length and semantics. No positive-infinity initialization support.
- Initialize the complete state history before base overlay; holes retain their initialization.
  `scan_mixed_init_holes` checks two persistent tensors with distinct zero/neg_inf inits,
  including both full histories and base holes; reusing `inits[0]` must fail numerically.
  Keep immutable pre-step captures, live time slicing and checked copy/write placement unchanged.
  Do not add a scalar reduction against an already-computed state write.
- The checker does not prove a global sort theorem through arbitrary pointwise/pass-through state
  writers; this plan makes no stronger arbitrary-raw-scan claim than the checked renderer supports.
- Keep inline unary-domain success as the existing unchecked precondition, not a new error API.

### Case × caller audit (including unchanged siblings)

The executor records this matrix against the final tree, rather than reviewing only new branches.
“Forbidden” means no newly admitted execution/evidence path, not rejection by the Lean language.

| Case / caller family | Required / forbidden / silently ignored | Pin / unchanged sibling |
|---|---|---|
| Real standalone, named, positional, unary/nonlinear | Required, unchanged | Legacy affine/nonlinear verification |
| Max standalone, named, positional | Required in affine rendering | Checked witnesses; original Viterbi |
| Ordered max factor fold | Required, native and source-ordered | Checked cancellation triple; reversal control |
| Single-axis zero/negInf scan init | Required per persistent tensor | Mixed two-state holes; original hole scan; real scans |
| Max unary OOB, nonempty / empty source | Required, distinct paths | Reciprocal partial-OOB / empty-source log |
| Unique-finite-winner AD | Required at five parameter points | Winner change, full permutation transport, both near-tie sides |
| Boolean-source read under max, cast true AND false | Required, exact checked flag | Same checked vector with flag changed |
| Boolean source under real sum-product | Forbidden, unchanged | Existing standalone/plan/evidence guards |
| Boolean destinations / `realToBool` | Forbidden | `gateMatrix`, reachability, runtime refusals |
| Min-plus | Forbidden | `gateMatrix`, min-scan guard, invalid algebra |
| Iverson lowering | Forbidden in emitter/runtime | `gateMatrix`, `ScanIversonRefusalTest` |
| Iverson handling inside support policy alone | Silently ignored, baseline | Emitter still explicitly refuses; not support |
| Einsum, affine/einsum candidates, kernel validation | Strict real-only required | Exact candidate tables in `gateMatrix` |
| Scatter, ordered AND fast | Non-real forbidden | Shared compute gate; runtime pre-mode backstop |
| Outer contextual assignment | Forbidden | Existing contextual guards; private scan-only opt-in |
| Multi-axis / nested scan | Forbidden | Existing scan admission/layout restrictions |
| Supplied incompatible signature | Revalidation required before policy | Altered-source-shape gate witness |

Audit identifiers: `jaxAssignSupported`, `checkJaxAssignSupportCtx`, `checkJaxAssignSupport`,
`checkJaxScatterSupport`, `checkJaxScanSupport` @ `leanncd/LeanNCD/Eval/Plan/Executable.lean`;
`requireJaxSupport`, `renderAffineNode`, `renderScanNode`, `renderScatterNode`,
`loweringToAffineTableCandidate`, `loweringToEinsumCandidate` @
`leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`;
`gateMatrix` (including `validateAndConstructKernel` calls) @
`leanncd/experiments/jax_bridge/EvalPlanMaxPlusSmoke.lean`;
`_run_node`, `_run_scatter_node`, `_run_scan_node` @
`leanncd/experiments/jax_bridge/evalplan_affine_runtime.py`.
Any newly silently ignored cell is a finding, not an automatic scope expansion.

## 3. Package and dependencies

Authoritative inputs:

- [package.json](jax_maxplus_files/package.json): baseline, provided-asset SHA256, patch SHA256,
  snapshot SHA256 and exact `touched_files`.
- [authoring_evidence.json](jax_maxplus_files/authoring_evidence.json): compact observed facts,
  donor provenance, symbols, counts, scope and budget disclosures.
- [revision_numeric_evidence.json](jax_maxplus_files/revision_numeric_evidence.json) and
  [revision_gradient_evidence.json](jax_maxplus_files/revision_gradient_evidence.json):
  case-level native observations, old-survivor/new-kill discrimination and oracle independence.
- [prerequisite_contract.json](jax_maxplus_files/prerequisite_contract.json): scalar audit.
  Use its max-plus obligations, not its out-of-slice Boolean/min-plus implementation observations.
- [verify_package.py](jax_maxplus_files/verify_package.py): asset hashes, private-index replay,
  current boundary hashes and real-index preservation. Use task 0 before implementation.
- [Lean manifest](jax_maxplus_mutations_post.json) and
  [kernel Python manifest](jax_maxplus_mutations_python.json), plus the **T3-only**
  [gradient Python manifest](jax_maxplus_grad_mutations_python.json): provided inputs, not patch outputs.
- [controller_results.json](jax_maxplus_files/controller_results.json): original operator/legacy
  proof for unchanged runtime/core/renderer and old verifier/input bytes, including SCOPE-01.
- [coverage_amendment_controller.json](jax_maxplus_files/coverage_amendment_controller.json):
  amendment reruns/restoration, observed `status="passed"` with all amendment checks complete.
  Readiness requires recorded successful new checks, refreshed hashes and renewed numerical/scope
  signoff, not just the original controller's passed statuses.

The controller corrected a packaging collision: Stage B had included add-file diffs for the two
provided manifests. Those diffs and source-map entries were removed, without changing implementation
bytes. The verifier now seeds its private index from the source baseline **plus all three provided manifests**,
then replays all four patches; it never relies on a prototype branch or implementation commits.
Do not regenerate the patches or rewrite history to compensate for already-present planning inputs.

| Task | Depends on | Patch | Cumulative boundary | Touched files |
|---|---|---|---|---|
| T1 | Prepared source baseline + provided inputs | [01.patch](jax_maxplus_patches/01.patch) | [task1.json](jax_maxplus_files/task1.json) | 3 |
| T2 | T1 | [02.patch](jax_maxplus_patches/02.patch) | [task2.json](jax_maxplus_files/task2.json) | 4 |
| T3 | T2 | [03.patch](jax_maxplus_patches/03.patch) | [task3.json](jax_maxplus_files/task3.json) | 3 |
| T4 | T3 | [04.patch](jax_maxplus_patches/04.patch) | [task4.json](jax_maxplus_files/task4.json) | 8 |

The boundary maps deliberately include unchanged neighboring source; their 4/7/7/15 entry counts are
**not** task Files counts. Files below come from patch headers/`touched_files`.
Current patch/snapshot hashes come only from package.json. The amendment leaves 01.patch and
runtime/core/renderer bytes unchanged; 02/03 were mechanically regenerated from compiled fixture
and verifier modules. 04 retains coupled repins/docs and updates README coverage prose only.
All task/hash/patch mismatches are hard stops. Raw Stage A/B logs and prototypes are archived in the
author session, not execution dependencies; the shipped package is self-contained.

| Risk / task | Fixture workload | Strict mutation workload |
|---|---|---|
| T1: scope leakage | 2 new tagged mutation controls; preserved guards and original 13-case logic suite | 2 Lean killed/restored cycles |
| T2: scalar/native precision/init | 11 assignments + 2 scans, 52 checked views; 44 metadata refusals; scalar/JVP pins | 18 singleton cycles for 9 intents; 12 targeted numeric kills for 3 new intents |
| T3: real source/AD/oracle | 7 reused Viterbi cases, 56 views; 5 parameter points, 40 gradient + 40 point-forward views; 6 reachability refusals | Regenerate full bundles; repeat kernel 18 plus T3-only gradient 8 singleton cycles |
| T4: coupled repins/docs | 5 documentation updates; complete legacy 55/47 nonlinear checks plus curated affine/scatter | 8 nonlinear + 11 scan Lean + 6 scan Python inherited cycles |

The complete pool has **40 unique mutation intents**, represented by **53 manifest entries/listed
cycles per complete pool pass**: 2 Lean + 18 kernel Python + 8 gradient Python + 8 nonlinear +
11 scan Lean + 6 scan Python. T2/T3/final repetitions add physical executions; 53 is not the total
of all executions across phases. Inherited grouped manifests retain historical aggregate semantics: do not infer
per-precision kills from their grouped PASS output. Only new singleton entries independently gate
each precision. Preserve the recorded SCOPE-01 negative-survival proof. The controller observed
T2 kernel 18, T3 kernel 18 and gradient 8 strict passes, plus all 8 gradient observe passes;
both complementary left-biased entries kill `near_tie_above`. Both renewed reviews are clean;
the sole nonblocking stale evidence-summary count was corrected to thirteen.

## 4. Preflight (controller)

1. Require amendment controller checks/restoration and renewed reviews complete; then read original
   scan-Python follow-up and successful precision-gate/negative-survival proof. Original clean reviews
   are historical, not proof of the strengthened invariant. The appended amendment reviews provide
   the renewed signoff; do not substitute the historical reviews for them.
2. Verify local-main ancestry and planning assets. Create a fresh linked execution worktree using
   the new-slice skill from local `main`; if the intended branch/path exists, STOP rather than reuse.
3. Run preparation with the tool's working directory set to that worktree, or the explicit Python
   cwd form below. Require cached Mathlib ≥95%; refresh project-owned LeanNCD oleans afterward.
4. Run package task-0 verification. It checks affected source, not whether HEAD equals the old
   baseline exactly. Do not demand every post-task manifest match on the unimplemented baseline.
5. Resolve a valid CPU JAX interpreter and the Python mutation runner's local environment honestly.
   The runner hardcodes `leanncd/experiments/jax_bridge/.cache/python/bin/python`; a valid unrelated
   `--python` alone does not satisfy this. Confirm the local path resolves and imports dependencies.
   Reuse a valid existing environment without modifying it; if local setup/import validation fails
   for a missing tool/dependency, use the repository's existing pinned CPU setup tooling.
   No unpinned install, shared-environment modification or host-specific session dependency.

```text
/usr/bin/git -C <primary> rev-parse main
/usr/bin/git -C <primary> merge-base --is-ancestor c5000dd462d72ed0ffcd5806937aa37fa477e9b0 main
/usr/bin/git -C <primary> worktree add <worktree> -b jax-maxplus-exec main
python3 -I -c "import subprocess; subprocess.run(['bash','<worktree>/.claude/skills/new-slice/prepare-worktree.sh','--plan','papers/semantics/jax_maxplus_plan.md'],cwd='<worktree>',check=True)"
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd LeanNCD
mkdir -p <worktree>/.cache
env TMPDIR=<worktree>/.cache python3 <worktree>/papers/semantics/jax_maxplus_files/verify_package.py --task 0
python3 -c "from pathlib import Path; print(Path('<worktree>/leanncd/experiments/jax_bridge/.cache/python/bin/python').resolve(strict=True))"
<worktree>/leanncd/experiments/jax_bridge/.cache/python/bin/python -c "import jax,numpy; print(jax.__version__); print(jax.devices())"
```

If dependency validation fails missing dependencies, the existing setup command is:
`bash <worktree>/leanncd/experiments/jax_bridge/setup-python.sh`.
Record the resolved interpreter/version/device and use its absolute path as `<jax-python>` below.
Keep package-verifier scratch inside the worktree via `TMPDIR`; do not write to `/tmp`.
Hook sections were measured under about 3k characters (leanncd pre-edit: 2951); no unrelated
AGENTS trimming task is justified.

## 5. T1 — typed render-only admission and metadata

**Three work items:** scoped core policy; renderer metadata; original expectation/preservation guards.
**Files (existing):**
- `leanncd/LeanNCD/Eval/Plan/Executable.lean`
- `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`
- `leanncd/experiments/jax_bridge/EvalPlanLogicSmoke.lean`

**Read windows:** `JaxRenderProfile`, `jaxMaxAlgebra`, `jaxAssignSupported`,
`checkJaxAssignSupportCtx`, `checkJaxAssignSupport`, `checkJaxScanSupport` @
`leanncd/LeanNCD/Eval/Plan/Executable.lean`;
`requireJaxSupport`, `renderAffineFactor`, `renderAffineTerm`, `renderAffineFields`,
`renderAffineNode`, `renderScanNode`, `scanTropicalRaw`, `scanMinRefusalRaw` @
`leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`;
`checkStructure` @ `leanncd/experiments/jax_bridge/EvalPlanLogicSmoke.lean`.
Read 40–60 lines per window, only after applying this task.

**Donors:** clone `scanRejectRaw`/`scanPlanStep` to change state init and step algebra for
`scanTropicalRaw`/`scanMinRefusalRaw`; clone `idAssign` under `idSigs` to pin the strict default.
Reuse `EvalPlanLogicSmoke.fixtures` unchanged; update only the expected max rendering verdict.
The tagged scan/default controls distinguish a rendering opt-in from leaked shared admission.

```text
/usr/bin/git -C <worktree> apply --check <worktree>/papers/semantics/jax_maxplus_patches/01.patch
/usr/bin/git -C <worktree> apply <worktree>/papers/semantics/jax_maxplus_patches/01.patch
env TMPDIR=<worktree>/.cache python3 <worktree>/papers/semantics/jax_maxplus_files/verify_package.py --task 1
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd JaxExperiment Eval.Plan.ScanJaxGateTest Eval.Plan.ExecutableTest
bash <worktree>/leanncd/experiments/jax_bridge/run-evalplan-logic.sh
bash <worktree>/leanncd/scripts/mutation-manifest.sh <worktree>/leanncd <worktree>/papers/semantics/jax_maxplus_mutations_post.json
```

**Acceptance:** original 13-case Lean/stdlib logic suite remains green; max rendering accepts,
Boolean rendering refuses; default support remains real-only; 2/2 new Lean controls killed and
restored green. Preserve located errors and supplied-signature revalidation.
Commit subject: `feat(jax): admit render-only max-plus plans`.

## 6. T2 — runtime, checked edge witnesses and runner

**Three work items:** scalar/fold/init runtime; checked/scalar/JVP fixtures; manifest-compatible CLI.
**Files:**
- `leanncd/experiments/jax_bridge/evalplan_affine_runtime.py` (existing)
- `leanncd/experiments/jax_bridge/EvalPlanMaxPlusSmoke.lean` (**new in 02.patch**)
- `leanncd/experiments/jax_bridge/evalplan_maxplus_smoke.py` (**new in 02.patch**)
- `leanncd/experiments/jax_bridge/run-evalplan-maxplus.py` (**new in 02.patch**)

**Read windows:** `_ordered_max`, `_ordered_add`, `_ordered_add_jvp`, `_algebra`, `_check_factors`,
`_run_term`, `_run_node`, `_run_scatter_node`, `_run_scan_node` @
`leanncd/experiments/jax_bridge/evalplan_affine_runtime.py`;
`rawFixture`, `vectorRaw`, `adversarial`, `contextProg`, `contextFixture`,
`mixedContextProg`, `mixedContextFixture`, `main` @
`leanncd/experiments/jax_bridge/EvalPlanMaxPlusSmoke.lean`;
`verify`, `__main__` @ `leanncd/experiments/jax_bridge/evalplan_maxplus_smoke.py`;
`run` @ `leanncd/experiments/jax_bridge/run-evalplan-maxplus.py`.

**Donors/provenance:** the scalar fixtures were reduced from the audited `PrototypeExtra`
`rawFixture`/`adversarial` shapes; Boolean destinations/realToBool were removed, and false Iverson
became an explicit Boolean-source read followed by a +infinity read. The checked hole witness
derives from its `contextFixture`: ordinary time-varying `Y[t,i]`, scalar base write leaving a hole.
These prototypes are not files the executor needs: all exact code is in 02.patch.
The custom JVP was integrated into the runtime, not hidden in a verifier wrapper.
New donors: clone `max_empty_factors` via `rawFixture`, replacing factors with three scalar reads
for cancellation; clone `contextProg`/`contextFixture` with coupled real/max S/R states and scalar
base writes for mixed holes; clone `max_bare_oob`, adding `.recip` to its nonempty source read.
Both assignment checkers and `checkScanPlan`/`checkScanPlanF32` accept these exact witnesses.

| Checked witness | Distinguishing obligation / observed result |
|---|---|
| `bool_to_tropical_true` | ±0 become -inf; nonzero/NaN/infinities become +0 |
| `bool_to_tropical_false` | Same Boolean-tagged values; no inferred cast, NaN retained |
| `max_empty_terms` | -inf, not zero |
| `max_empty_factors` | +0 |
| `max_zero_reduction` | -inf, no size-zero gather |
| `max_bare_oob` | `[2,-inf,-inf]` |
| `max_log_oob_bypass` | Empty source, all -inf without evaluating log on the pad |
| `false_source_opposing_infinity` | NaN, not false-factor pruning |
| `max_empty_output` | Empty checked output |
| `scan_context_holes` | `[[3,7,13,19],[-inf,11,17,23]]`; time/initialization differ observably |
| `max_factor_order_cancellation` | Three scalar reads `[2^54,-2^54,1]`: 1; reversed factors: 0 |
| `scan_mixed_init_holes` | Both histories `[[3,7,13,19],[h,11,17,23]]`, with respective `h=+0` and `h=-inf` |
| `max_reciprocal_partial_oob` | Nonempty `[2]` over 3 positions gives `[.5,-inf,-inf]` |

Eleven checked assignments + two checked scans × both precisions × eager/JIT = 52 checked views.
The 11 invalid-metadata variants × both precisions
× eager/JIT = 44 refusals. Scalar pins additionally distinguish RHS signed-zero max ties,
first/second NaN patterns, zero-pair sum signs and the zero-Init derivative.
False cast is not inferred even when the source tag could tempt such an inference; the factor
+0 seed normalizes stored -0 to +0 before max.
The empty-source log pin bypasses evaluation before gathering; it cannot certify the nonempty
reciprocal's final max-unary OOB mask. Removing that mask is killed by the reciprocal witness.
All three new controls return shaped numeric results, not syntax/import exceptions: 3 intents ×
2 precisions × 2 modes = 12 targeted numerical kills. The original ten checked fixtures survived
the same mutants, so their unchanged presence alone did not establish these obligations.

```text
/usr/bin/git -C <worktree> apply --check <worktree>/papers/semantics/jax_maxplus_patches/02.patch
/usr/bin/git -C <worktree> apply <worktree>/papers/semantics/jax_maxplus_patches/02.patch
env TMPDIR=<worktree>/.cache python3 <worktree>/papers/semantics/jax_maxplus_files/verify_package.py --task 2
python3 <worktree>/leanncd/experiments/jax_bridge/run-evalplan-maxplus.py --python <jax-python> --checked-only
python3 <worktree>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <worktree>/papers/semantics/jax_maxplus_mutations_python.json
```

The runner generates actual Lean payloads and standard bridge-local
`.cache/generated_evalplan_maxplus_smoke64.py` / `.cache/generated_evalplan_maxplus_smoke32.py`
bundles. Its optional `--out-dir` moves result payloads, not those standard bundle entry points.
The existing mutation runner accepts `evalplan_maxplus_smoke.py float64|float32 MODULE`.
The verifier also retains `--precision`, `--checked`, `--logic`; these are CLI compatibility,
not an extra production mode. Normal verification performs **zero nested self-mutations**.

**Acceptance:** 52 checked views, 44 refusals, scalar/JVP pins and **18/18 independently gated kernel
cycles for nine intents**, each killed with its expected diagnostic and restored green.
The gradient manifest is invalid here: the runner has no task selector; never combine its T3-only
anchors into this T2 manifest or invoke it on checked-only bundles. Do not claim source execution yet.
Commit subject: `feat(jax): execute ordered max-plus assignments and scans`.

## 7. T3 — original source programs and independent gradient oracle

**Three work items:** source export integration; gate matrix; exact source and gradient validation.
**Files (existing after T2):**
- `leanncd/experiments/jax_bridge/EvalPlanLogicSmoke.lean`
- `leanncd/experiments/jax_bridge/EvalPlanMaxPlusSmoke.lean`
- `leanncd/experiments/jax_bridge/evalplan_maxplus_smoke.py`

**Read windows:** `fixtures`, `checkStructure`, `emit` @
`leanncd/experiments/jax_bridge/EvalPlanLogicSmoke.lean`;
`gateMatrix` @ `leanncd/experiments/jax_bridge/EvalPlanMaxPlusSmoke.lean`;
`verify`, `native_path_oracle`, `verify_gradient_points` @
`leanncd/experiments/jax_bridge/evalplan_maxplus_smoke.py`;
`verify` @ `leanncd/experiments/jax_bridge/evalplan_logic_smoke.py` (unchanged independent oracle).
Use successive 40–60-line windows for the longer verifier, not a whole-file read.

**Donors:** reuse the original seven Viterbi and six reachability entries in
`EvalPlanLogicSmoke.fixtures`; do not duplicate source programs. Clone `idAssign`, `idSigs`,
`idIversonAssign` for checked max/min/Boolean cases and exact affine/einsum candidate tables.
For AD, clone original `viterbi` inputs, changing only `Init[2]` for winner/near-tie points;
reuse `viterbi_permuted` inputs for transport. The actual compiled baseline named/positional source
plan and its eager/JIT functions are reused across all points, not recompiled per parameter point.
`native_path_oracle` exhaustively enumerates every prefix and full path directly from inputs in
`np.float32` or `np.float64`, preserving source zero seeds and factor order. No runtime operations,
runtime results or narrowed binary64 oracle supply expected values.

- Named/positional × eager/JIT × both precisions × seven Viterbi = 56 source views.
- Compare every materialized export with the precision-specific checked worker. Feed those JAX
  exports through the original exhaustive-path/metamorphic oracle, not merely a new score check.
- Preserve original state/node permutation, input sensitivity, time-causality, spare emission,
  additive-shift, impossible/tied-sequence and reachability oracle pins.
- Enumerate Init one-hot, Trans occurrence counts and Emit time/state counts independently for each
  winner; compare full `D` histories and `Score` by bits, and every parameter gradient exactly.
- Require finite binary frozen Allow, Init finite or -inf, finite Trans/active Emit and a unique
  finite active final winner; keep the never-read NaN Emit row and require its gradient zero.
- Five mathematical points × named/positional × eager/JIT × both precisions = **40 gradient views
  and 40 point-forward executions**. Baseline/permutation overlap the existing 56 source views;
  do not sum these deployment counts into independent mathematical scenarios.
- `gateMatrix` rejects max/min/Boolean under the default policy, both candidate conversions and
  `validateAndConstructKernel`; affine rendering alone accepts max. An incompatible supplied shape
  must return `invalidSignatureContext`; an Iverson must remain `iversonFactor`.
- Six reachability fixtures have no JAX fields and still produce explicit named/positional refusals.

| AD parameter point | Independent observed winner / score / positive margin |
|---|---|
| `baseline` | `(0,1,2,1,0,1)` / -5.25 / .25 |
| `changed_winner`: `Init[2]+=4` | `(2,1,2,1,0,1)` / -4.75 / .25; Init/Trans counts differ |
| `state_permuted`: permutation `[2,0,3,1]` | `(1,3,0,3,1,3)` / -5.25 / .25 |
| `near_tie_below`: `Init[2]=1-delta` | Baseline winner / -5.25 / delta |
| `near_tie_above`: `Init[2]=1+delta` | Changed winner / `-5.25+delta` / delta |

Use native `delta=2^-47` in f64 and `2^-18` in f32: margins respectively
`7.105427357601002e-15` and `3.814697265625e-6`, exactly **8 output ULPs** on both sides.
These are opposite unique winners, not true ties. Exact full gradient transport indexes Init by
the permutation, both Trans axes by it, and Emit's state axis; also transform frozen Allow.
Compare transported baseline counts with fresh independent enumeration and actual permuted gradients.

```text
/usr/bin/git -C <worktree> apply --check <worktree>/papers/semantics/jax_maxplus_patches/03.patch
/usr/bin/git -C <worktree> apply <worktree>/papers/semantics/jax_maxplus_patches/03.patch
env TMPDIR=<worktree>/.cache python3 <worktree>/papers/semantics/jax_maxplus_files/verify_package.py --task 3
python3 <worktree>/leanncd/experiments/jax_bridge/run-evalplan-maxplus.py --python <jax-python>
python3 <worktree>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <worktree>/papers/semantics/jax_maxplus_mutations_python.json
python3 <worktree>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <worktree>/papers/semantics/jax_maxplus_grad_mutations_python.json
```

The full runner **must regenerate** standard bundles before both manifests, replacing T2's
checked-only bundles so source/gradient checks actually participate. Expected totals remain
52 checked / 44 refusals / 56 Viterbi / 40 gradients / 40 point-forwards at five points.
Repeat kernel 18, then require gradient 8 independently killed/restored cycles for four intents.
Stale-baseline parameters are a **verifier orchestration** control, not a backend mutant; wrong
permutation transport is an **oracle transport** control. Right-biased approximate max targets
`near_tie_below`; the complementary **tie-preserving left-biased** control targets `near_tie_above`.
Require each side numerically killed in both carriers/modes; non-discriminating target views do not
count as kills. Author artifacts cover six gradient entries plus targeted both-sided probes;
the controller subsequently observed/strict-verified all eight entries, including the persistent
tie-preserving left-biased pair's required `near_tie_above` failures in both precisions.
Commit subject:
`test(jax): verify Viterbi values and winning-path gradients`.

## 8. T4 — coupled repins, discovery and controller closeout

**Two work items; no heavyweight documentation dispatch.** Apply the packaged coupled
anchor/line repins and the five documentation/discovery updates.
**Files (existing; all eight included in final 04.patch):**
- `papers/semantics/jax_nonlin_mutations_post.json`
- `papers/semantics/jax_scan_mutations_post.json`
- `papers/semantics/jax_scan_mutations_python.json`
- `leanncd/AGENTS.md`
- `leanncd/LeanNCD/Eval/Plan/AGENTS.md`
- `leanncd/docs/test_portfolio.md`
- `leanncd/experiments/jax_bridge/README.md`
- `papers/semantics/jax_rnn_session_brief.md`

**Read windows:** changed entries @ the three mutation JSON files; JAX contract @
`leanncd/LeanNCD/Eval/Plan/AGENTS.md`; feasibility/discovery and Boolean-output pitfall @
`leanncd/AGENTS.md`; current rendering/evidence, scan and logic sections @
`leanncd/experiments/jax_bridge/README.md`; Viterbi/reachability inventory @
`leanncd/docs/test_portfolio.md`; remaining-JAX-boundary paragraph @
`papers/semantics/jax_rnn_session_brief.md`. Donors are those existing rows/entries, not new examples.
The existing scan-Python `JS-P-05` anchor is directly coupled: initialization metadata now lies
between `steps` and `states`. The verified packaged repin narrows only that anchor to the unique
step-count assignment, preserving the original decrement/expect and one-step-too-few intent.
The executor applies the final patch, not a handwritten replacement.
The controller's immutable sibling audit found every other existing Python-manifest anchor retained
its baseline count of one. This is not a new provided manifest or a runtime semantic change.
No import-tree expansion is required: the core change remains reachable through existing LeanNCD
exports; experimental runner discovery is updated in the existing AGENTS and bridge README.

```text
/usr/bin/git -C <worktree> apply --check <worktree>/papers/semantics/jax_maxplus_patches/04.patch
/usr/bin/git -C <worktree> apply <worktree>/papers/semantics/jax_maxplus_patches/04.patch
env TMPDIR=<worktree>/.cache python3 <worktree>/papers/semantics/jax_maxplus_files/verify_package.py --task 4
```

Commit subject: `docs(jax): record max-plus boundary and repin coupled controls`.
Stage exactly each task's Files by explicit path, review the staged diff, and commit using its
subject plus `Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>`.
Never stage `.claude/settings.json` or generated `.cache` payloads. Keep final execution-record
updates separately identifiable; do not silently add unlisted source edits.

### Manifest validity and required controller cycles

| Manifest | First valid boundary | Required actual cycles |
|---|---|---|
| `jax_maxplus_mutations_post.json` | T1 | 2 |
| `jax_maxplus_mutations_python.json` | T2 + generated checked standard bundles; repeat after full T3 regeneration | 18 singleton-precision cycles for 9 intents |
| `jax_maxplus_grad_mutations_python.json` | T3 ONLY + regenerated full standard bundles; no runner task selector | 8 singleton-precision cycles for 4 intents |
| `jax_nonlin_mutations_post.json` repins | T4 | 8 |
| `jax_scan_mutations_post.json` repins | T4 | 11 |
| `jax_scan_mutations_python.json` repin | T4 + freshly generated scan bundles | 6 inherited grouped cycles |

New Lean controls: `MAX-L-SCAN` revokes the render opt-in and kills the tagged scan acceptance;
`MAX-L-DEFAULT` leaks max into the strict default and kills its tagged refusal.
Python controls: `MAX-P-omit_cast`, `MAX-P-zero_init`, `MAX-P-freeze_time`, `MAX-P-zero_pad`,
`MAX-P-native_max_zero_tie`, `MAX-P-remove_custom_jvp`, `MAX-P-factor_order_cancellation`,
`MAX-P-first_state_init`, `MAX-P-unary_final_oob_mask`. Gradient controls are `MAX-AD-stale_baseline_parameters`,
`MAX-AD-permutation_transport`, `MAX-AD-approximate_max`, `MAX-AD-approximate_max_left`.
Each has separate `-64`/`-32` entries. Require observed diagnostic strings in the frozen manifests;
an unfinished controller supplement is not an execution-ready asset.

**SCOPE-01 correction.** The unchanged Python runner ORs grouped precision failure statuses and
concatenates diagnostics: one failing precision can conceal a survivor. The provided new max-plus
manifests therefore represent every new Python intent as two singleton `runs` entries, one f64 and
one f32, without runner changes or execution-time manifest edits. Require all 18 kernel and 8 gradient
cycles independently killed/restored green, with per-leg evidence. Do not strengthen inherited
grouped-manifest claims retroactively.

The controller's recorded negative control made **only float64 fail**: a `PASS` for float64 plus
`SURVIVED`/`FAIL` for float32 yielded overall **exit 1**, not a false pass. Both twelve-cycle
observe/strict runs and this negative proof are recorded in `precision_gate_review_fix`, with
clean restoration. The scope reviewer confirmed the correction. This is authoring evidence,
not an instruction to edit or regenerate the executor's immutable manifest.
That original SCOPE-01 correction changed provided-input metadata only. The coverage amendment
subsequently regenerated fixture/verifier patches; it preserves the independent precision gate.

**Parked side issue:** preexisting scatter manifest `JS-T1-04` has zero matching baseline anchors.
It is not required for max-plus, is not repaired here and is not counted as a pass; a separate
Direct repair would cost roughly one bounded dispatch. Do not broaden T4 to fix it.

## 9. Final verification, review and integration

The **controller** runs these serially, records commands/results and checks restored hashes.
Do not substitute agent “green” reports for its own full build and mutation runs.

```text
python3 <worktree>/leanncd/experiments/jax_bridge/run-evalplan-maxplus.py --python <jax-python>
bash <worktree>/leanncd/scripts/mutation-manifest.sh <worktree>/leanncd <worktree>/papers/semantics/jax_maxplus_mutations_post.json
python3 <worktree>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <worktree>/papers/semantics/jax_maxplus_mutations_python.json
python3 <worktree>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <worktree>/papers/semantics/jax_maxplus_grad_mutations_python.json
bash <worktree>/leanncd/scripts/mutation-manifest.sh <worktree>/leanncd <worktree>/papers/semantics/jax_nonlin_mutations_post.json
bash <worktree>/leanncd/scripts/mutation-manifest.sh <worktree>/leanncd <worktree>/papers/semantics/jax_scan_mutations_post.json
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd LeanNCD Tests JaxExperiment
bash <worktree>/leanncd/experiments/jax_bridge/run-evalplan-nonlin.sh
python3 <worktree>/leanncd/experiments/jax_bridge/mutation_python_manifest.py <worktree>/papers/semantics/jax_scan_mutations_python.json
bash <worktree>/leanncd/experiments/jax_bridge/run-evalplan-affine.sh
bash <worktree>/leanncd/experiments/jax_bridge/run-evalplan-scatter.sh
env TMPDIR=<worktree>/.cache python3 <worktree>/papers/semantics/jax_maxplus_files/verify_package.py --task 4
```

Require complete legacy nonlinear 55/47 model/property/gradient checks, real scan neighbors,
curated affine, and real scatter in f64/f32. Confirm the invoked runners actually report the required
precision legs; a missing leg is incomplete, not implicitly covered. Record actual curated/scatter
counts and timings, without inventing them. Full 3,832-case corpus/performance claims are not a
completion condition; any expansion beyond this validation set must be explicit, not quietly added.
If environment selection differs across legacy shell runners, resolve their existing local JAX
environment before launch rather than assuming max-plus `--python` controls them.
Original controller authoring checks passed: full LeanNCD/Tests/JaxExperiment (8847 jobs), nonlinear
55 f64 / 47 f32 eager/JIT fixtures, 20 curated affine fixtures, scatter 10 f64 / 5 f32 bit-identical
eager/JIT, and all 6 inherited scan-Python cycles killed/restored. Record actual execution results;
do not assume authoring counts cannot change on a valid new base. For amendment authoring only,
the original controller artifact remains operator/legacy proof where affected bytes are unchanged.
The amendment controller reruns actual new manifests and the full prototype build, then restores
baseline. Do not claim all 25 inherited controls reran if their existing proof was reused by hash.
Its portable report now records all new checks passed: T2/T3 runners and kernel 18 at each boundary,
gradient observe/strict 8, Lean 2, full prototype build (8847 jobs), task-4 package proof and restored
baseline/task-0 proof. Main is unchanged; runtime/core/renderer bytes are preserved. The controller
also reports the baseline rebuild complete. No archived raw-log path is an execution dependency.

Documentation sweep (record and classify hits; historical records are not live-status claims):

```text
rg -n -i -g '*.md' 'max.plus|tropical|Boolean|Iverson|unsupportedScanState|real.only|ordered_max_plus_v1' <worktree>/leanncd <worktree>/papers
rg -n -g '*.md' '13|seven|six|56|52|40|44|53|18|55|47|3,832|3832' <worktree>
rg -n -g '*.md' 'non.real.*refus|tropical.*refus|ONLY real|both non.real' <worktree>
/usr/bin/git -C <worktree> diff --check
```

The first sweep checks vocabulary; the second checks moved values even in documents not already
opened. No stale live max refusal claim or Boolean-execution claim is acceptable. Classify unrelated
or historical matches rather than rewriting the repository. No `File.lean:NNN` citations in shipped
docs/records; use identifiers and paths.

Two independent **whole-branch** review lenses, each bounded at about 60 turns/250k context:

1. Scope/caller/evidence: typed opt-in, signature authority, unchanged sibling doors, both scatter
   modes, refusal locations, default gates, discovery and honest documentation.
2. Numerical/gradient/oracle: seeds/order/native precision, cast false, OOB/unary/empty domains,
   NaN patterns and signed zeros, cancellation/factor reversal, two-state mixed holes, both unary OOB
   paths, independent native prefix/path oracle, full permutation gradient transport and both
   positive-margin near-tie sides, custom JVP and changed-winner derivatives.

Reviewers read 40–60-line windows and append findings incrementally to the execution record.
Check budget headroom before launching them; a fix is one bounded dispatch per finding group,
with only its relevant symbols/sections. If a finding requires changing the immutable package,
STOP for plan correction, not an ad hoc execution repair. No unreviewed patch regeneration.

After green controller validation and clean/adjudicated reviews, commit the completed execution
record, exit the worktree keeping it, merge the implementation branch to local `main` with
`/usr/bin/git -C <primary> merge --no-ff jax-maxplus-exec`, and confirm
`/usr/bin/git -C <primary> diff --stat main jax-maxplus-exec` is empty. Inspect worktree status and
identify generated files before removal; remove only this execution worktree and delete only its
merged branch. No push, no unrelated cleanup or history rewrite.

## 10. Execution-record schema and stop conditions

Create future `papers/semantics/jax_maxplus_record.md`; do not overwrite the authoring record.
Include:

- Actual base/worktree/interpreter/device, preparation/cache result and package-verifier outputs.
- Per-task commands, exit codes, exact counts, commit IDs and boundary hashes.
- Scalar/native precision observations; 13 fixtures (11 assignments/2 scans), 52 checked / 44 refusals /
  56 source / 40 gradient / 40 point-forward views across five AD points, or actual discrepancies.
  Preserve point-vs-deployment/overlap distinctions; record Boolean refusal and scoped exclusions.
- New checked witness acceptance, complete mixed histories, native margins/winners/transport and
  numeric-return kills; distinguish stale-parameter/oracle controls from backend mutants.
- Mutation labels, independently gated precision legs, kills/refusals/survivors and restoration;
  distinguish 40 unique intents / 53 entries per complete pool pass from repeated physical
  executions. Do not infer per-precision kills from inherited grouped cycles; keep `JS-T1-04` visible.
- Complete regression commands/counts/timings and full-build output, without claiming skipped checks.
- Amendment authoring provenance: old proof reused by unchanged hashes versus new controller
  reruns/restoration; original reviews versus renewed signoff. Never promote pending proof to passed.
- Case × caller audit, documentation sweep classifications, both reviews and adjudicated findings.
- Measured cumulative tokens/peak context/turns per dispatch and total, or explicit unavailable
  telemetry; disclose any cap breach rather than describing it as merely unmeasured.
- Commit/merge/no-push/cleanup status and anything genuinely blocked or excluded.

STOP on missing assets/dependencies not resolved by the permitted setup, unexpected admission,
patch/hash mismatch, surviving control, wrong diagnostic, failed restoration, regression, scope
expansion or budget-threatening task shape. Preserve evidence and report BLOCKED. Completion means
verified persistent implementation, not just patches applied or `--check` green.

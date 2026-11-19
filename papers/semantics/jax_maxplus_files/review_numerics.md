# Independent numerical / gradient / oracle plan review

Scope: immutable `02.patch` / `03.patch`, task 2/3 maps and approved Git
blobs, numerical prerequisite/evidence records, and the provided Python mutation
manifest. No feature working files, tests, builds, mutations, or commits are used.

## Review checkpoints

- Read the numerical contract and T2/T3 acceptance criteria against the patched
  scalar helpers, algebra-specific seeds/padding, checked edge fixtures, scalar
  pins, and independent winning-path gradient construction.
- No high-confidence finding at this checkpoint. Continuing with the unchanged
  oracle, complete approved runtime context, precision runner, and control evidence.

- Approved runtime blob `a1642c67c8f7041c8061d0f99b25bbe4e4b0e881` preserves
  separate seeded factor/reduction/term loops and last-reduction-dimension-fastest
  reshaping. Empty/OOB paths use the selected algebra's reduction identity; unary
  tropical pads bypass the primitive and checked cast flags remain authoritative.
  Scan initialization precedes base placement, with immutable pre-step captures,
  live time slicing, and copy placement retained.
- The unchanged baseline `evalplan_logic_smoke.py` supplies exhaustive complete
  paths, input checks, seven Viterbi variants and six reachability variants. T3
  substitutes actual JAX exports into that oracle. The separate gradient oracle
  derives counts from original input paths, checks uniqueness and the exact gap,
  differentiates only Init/Trans/Emit, and checks every count plus the spare row.
  Nothing here establishes a derivative contract at genuine ties/nonfinite paths.
- Both precision subprocesses set x64 before constructing arrays; f32 expected
  bits originate in the checked native-f32 worker. Comparisons retain signed-zero
  bits and exempt only NaN payloads, not NaN locations.
- The six new Python controls target distinct cast, init-hole, time-slicing,
  tropical-padding, max-tie and zero-seed-JVP errors. Controller results record all
  six killed/restored and byte-identical runtime restoration. The normal verifier
  has no self-mutation path. These are reviewed controller observations, not tests
  executed by this reviewer.

- Numerical claims remain bounded: checked native precision, NaN-pattern rather
  than payload comparison, explicit first-NaN/RHS-tie selection, unchecked native
  unary-domain success, and no transcendental bit-portability theorem. The
  inherited README normal-range/CPU flush-to-zero limitation is not removed by
  the package. The custom addition JVP is integrated in the runtime and tested
  both directly and through the unique finite Viterbi winner, not advertised as a
  universal theorem for arbitrary programs or gradients at genuine ties.

## Final package / close-out

The final `package.json` lists eight T4 touched files, including the existing
`jax_scan_mutations_python.json`; `task4.json` includes its approved blob
`553f57913f7663dd59118e6434de9fedfd45f2e5`. There remain exactly two provided
manifest inputs. Controller results now record `scan_python_followup_status`
`passed`, all six inherited scan-Python controls killed/restored, unchanged
runtime bytes, restored source baseline, and 33 distinct strict controls.

The plan header, T4 table/file-list annotations and authoring-record historical
pending-follow-up statements still need the coordinated readiness/metadata
refresh announced by the parent. These are disclosed close-out items, not an
implementation finding. Preserve the observed 40 checked views, 44 refusals,
56 Viterbi views and eight gradient views; do not convert the six reachability
cases into JAX executions or multiply repeated controls into distinct controls.

## Verdict

**CLEAN — no high-confidence numerical, gradient, or oracle change request.**
The numerical implementation package supports the stated bounded validation
claims. This is a read-only plan review, not production landing approval or a
claim that this reviewer reran validation. Other-lens adjudication and the
coordinated final prose refresh remain the parent's close-out responsibilities.

Only this review file was written. No tests/builds/mutations/package replay,
source/plan/patch/JSON edits, commits, or additional agents were performed.
Completed within the 18-turn cap; exact token/context telemetry is unavailable,
with no known breach of the 90k-context target.

## Final bounded follow-up — SCOPE-01 protocol correction

**CLEAN reaffirmed; no numerical blocker.** Read-only SHA256 comparison confirms
all four patches are byte-identical to this review's original inputs. Task-map
hashes still match the unchanged package snapshots, including the reviewed
runtime and numerical verifier blobs. Thus no numerical implementation changed.

The provided Python manifest now has twelve entries, each declaring exactly one
precision; its actual SHA256 matches the updated package pin. Refreshed prose
distinguishes six mutation intents / twelve independent new cycles and 33 unique
intents / 39 entries per complete pool pass. This strengthens the protocol without
changing the numerical/oracle contract or the original clean verdict.

Read `precision_gate_review_fix` evidence: observe and strict runs each record
twelve labeled killed/restored legs, while the deliberate f64-only cast mutation
records f64 killed, f32 survived/restored, and expected runner exit 1. These are
controller observations, not reviewer-executed mutations. The earlier review's
pending metadata-refresh note is superseded; final header signoff remains with
the parent and scope reviewer.

Only this report was appended. No build, test, mutation, source edit, package
replay, or delegation occurred. One read-only hash command initially failed to
parse and was corrected successfully. Follow-up used three tool-call rounds;
exact token/context telemetry remains unavailable, with no known context breach.

## Independent coverage-amendment numerical review — 2026-11-18

Scope: revised `02.patch`/`03.patch`, the numerical and gradient mutation
manifests, live coverage/contract prose, and the three amendment evidence records.
Historical review above is preserved. Production prototypes are restored;
this is acceptance-plan review, not production implementation or landing approval.
Only this report is edited; no patches, sources, manifests, builds, installations,
expensive pools, or nested agents are used.

Checkpoint: read the actual three added fixture constructions and their scalar/
complete-history assertions, plus the native exhaustive prefix/path oracle.
The cancellation pin uses exactly representable `2^54`, mixed scans require both
zero and negative-infinity initializers, and partial-OOB reciprocal checks the
valid value and both padded positions. Continuing with independent bounded
arithmetic/oracle checks, AD transport/tolerances, manifests, and evidence.

### Independent bounded-check checkpoint

Executed only in-memory NumPy/Python checks using the existing cached interpreter
(`-B`, no installation or generated output). Extracted the actual
`native_path_oracle` from `03.patch` without applying it. Decoded retained
checked/source bundles as literals and verified baseline inputs against the
restored `EvalPlanLogicSmoke.lean` declarations, not against runtime outputs.

For all ten precision-specific points, independently enumerated exact-rational
prefix/full-path scores and occurrence counts. Every full `D` history bit matched
the native oracle; final scores, winners, margins and all Init/Trans/Emit counts
matched, including 96 finite allowed final paths per point. Counts/scores/winners
also matched the retained gradient evidence. Both near cases have exactly eight
output ULPs of positive margin: `2^-47` (f64), `2^-18` (f32), on opposite winners.
Full input/gradient permutation transport passed, including both Trans axes,
Emit's state axis and frozen Allow. The unused NaN Emit row had zero counts.

Independently confirmed native cancellation ordered=1/reversed=0 in both carriers
and checked both cached mixed histories and reciprocal output by bits.
Interpreting the actual manifest comparator expressions with NumPy produced
numerical prefix disagreements on right-biased `near_tie_below` and complementary
left-biased `near_tie_above`; both preserved the tested RHS signed-zero tie.
These are not JAX eager/JIT executions or independently rerun backend mutants.

One initial probe stopped on a reviewer-script `KeyError`: the historical
gradient evidence does not contain `expected_forward_bits`. After inspecting its
actual schema, the corrected complete probe passed, comparing histories directly
to independent rational enumeration instead. This was not a candidate failure.

### Findings and verdict

**CLEAN — no load-bearing numerical/coverage finding or required fix.**
The revised acceptance closes skeptical points 1–3 within its stated finite,
unique-winner/native-carrier scope:

1. **Previously surviving reversed max factors:** `02.patch:151–155` constructs
   the checked three-scalar `[2^54,-2^54,1]` fixture; `02.patch:526–527`
   independently pins one. Both carriers represent the inputs exactly, but the
   reversed fold returns zero. The first paired entries of
   `jax_maxplus_mutations_python.json:3–30` reverse only max-plus factors, with
   numerical mismatch diagnostics. Native arithmetic was independently checked;
   the evidence's targeted eager/JIT kills were read, not rerun.

2. **Mixed-state holes and partial-OOB unary:** `02.patch:58–115` constructs
   two states with distinct initializers, restricts both base writes to leave
   holes, and rechecks the resulting scan separately in both carriers. Dense32
   execution is native, not narrowed Dense64 output. `02.patch:531–541` checks
   both complete histories, including positive-zero versus negative-infinity
   holes. `02.patch:156–157,528–530` adds the nonempty reciprocal case
   `[2] -> [.5,-inf,-inf]`. Full fixture expectations and raw bits were checked
   independently; the new controls genuinely discriminate first-state init
   reuse and omission of the final OOB mask.

3. **AD deployment versus mathematical coverage:** `03.patch:106–145`
   independently enumerates every prefix/full path from native inputs, deriving
   Init one-hot, repeated Trans counts and time/state Emit counts. It neither
   calls runtime arithmetic nor consumes runtime results. Skipping blocked paths
   is valid under its finite Trans/active Emit and binary Allow preconditions;
   no active positive infinities can turn a blocked product into NaN.
   `03.patch:164–203` constructs five parameter points and verifies full
   permutation transport; `03.patch:209–256` actually passes each point and its
   transformed Allow to named/positional eager/JIT calls, checking full `D`/
   `Score` bits and every gradient count. Only Init/Trans/Emit are differentiated
   (`argnums=0`); Allow remains frozen, and the never-read NaN Emit row must have
   zero gradient. Baseline/changed winners and both near-side margins were
   independently reproduced, not inferred from deployment counts.

The five points do not imply five unrelated gradient supports: near-below
shares baseline counts, near-above shares changed-winner counts, and permutation
is a coordinate transport. Those deliberate relationships test numerical
discrimination and transport rather than inflate mathematical independence.

**Counts and control interpretation.** Actual cached fixtures contain eleven
assignments and two scans: **13 fixtures / 52 checked views / 44 metadata
refusals**. The unchanged seven source cases retain **56 source views**.
Five parameter points give **40 gradient deployments and 40 point-forward
executions**; baseline/permutation account for 16 point-forward deployments
overlapping the original source scenarios, not 16 new mathematical cases.
The manifests independently check as **18 T2 singleton entries / nine intents**
and **eight T3-only singleton entries / four intents**, with each intent paired
across separate precision gates.

The stale-baseline pair is an orchestration control; wrong permutation transport
is an oracle control, not a backend defect. Only the two tolerance-comparator
intents in the T3-only manifest mutate backend numerical comparison.
`jax_maxplus_grad_mutations_python.json:67–137` requires right-biased
`near_tie_below` and complementary, tie-preserving left-biased `near_tie_above`
numerical assertion failures in both carriers. The actual comparator expressions
were independently discriminating in-memory; controller eager/JIT observations
remain controller evidence, not reviewer-reexecuted results.

**Evidence precedence and limits.** `revision_numeric_evidence.json:23` records
the strengthened numerical counts; its later targeted observations distinguish
numeric returned-value failures from setup exceptions. The original gradient
snapshot's six-entry counts (`revision_gradient_evidence.json:5–56`) describe an
earlier stage, explicitly superseded by `controller_supplement` at line 990 and
the eight-entry observe/strict results in
`coverage_amendment_controller.json:100`. This is not six being counted as eight.
The controller also records renewed T2/T3 kernel cycles, full prototype build,
and restoration. I read these records but did not rerun those cycles/builds.
Its `legacy_proof_reuse` at line 225 explicitly retains, rather than reruns, the
old legacy proof. Read-only Git comparison independently found no `leanncd`
production differences from `c5000dd462d72ed0ffcd5806937aa37fa477e9b0`
(planning base `d7ac2640`).

No universal correctness, derivative-at-real-ties, nonfinite-active-path,
process/performance point 4, or production-landing claim follows. Unchanged
runtime/core/renderer and admission/legacy proofs were intentionally not
re-reviewed; package/protocol review belongs to the other reviewer.
Only this report was edited. Completed within the 18-turn cap; exact
token/peak-context telemetry is unavailable, with no known breach of 100k peak
context. No source/manifest edit, patch application, pool/build rerun, commit,
installation, or delegation was performed.

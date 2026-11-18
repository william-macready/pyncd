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

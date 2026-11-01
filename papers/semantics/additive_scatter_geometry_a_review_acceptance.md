# Slice A whole-branch acceptance/correctness review

Scope: `d48691daa8d08d45bf8645b21b3b6bc85def18f3` to
`ba1c783d7d1c971c05e5651f73a14b3284a09538`, all 20 changed paths,
with the acceptance lens in plan sections 3, 6, and 7. Sources are committed
snapshots, not the working tree under the controller's mutations. No builds,
hash validation, source edits, or commits are performed by this review.

Findings and adjudications are appended incrementally below.

## Controller verification and disposition

After stopping mutations and verifying all 20 source blobs restored exactly,
the controller refreshed `Eval.Plan.ScatterGeometryTest` (successful, 8526
jobs) and ran an isolated diagnostic module through `lean-file.sh`. The
first diagnostic compile omitted the mandatory `nonlin` field; this was
corrected to `.identity` without changing any production code or fixture.
The corrected diagnostic compiled successfully and observed:

| Counterexample | Reference f64 shape | Checked f64 shape | Checked f32 shape |
| --- | --- | --- | --- |
| A1, `S[a+b] := A[a]*B[b]*C[c]`, sizes 4, 3, 0 | `[6]` | `[7]` | `[7]` |
| A2, ordinary `#constUser` axis size 2, declared output box size 8 | `[2]` | `[2]` | `[2]` |
| A2, same ordinary writer duplicated into a group | no successful result | no successful result | no successful result |

The extent helpers independently returned `some 6` for the original A1
slot and `some 7` for `scatterDestExtent #[4,3,0] #[1,1,0] 0`.
`boundedScatter` returned `false` for A2's ordinary size-two axis.
The previous boxed shape `[8]` in A2 is a committed-code baseline trace
from this review, not a separately executed baseline measurement.
The temporary diagnostic source was removed after observing these results.

**Disposition: BLOCKED, do not merge.** A1 and A2 are load-bearing plan
defects, not failures to replay the supplied patches. Correcting them needs
an explicit consistent empty-domain policy and a provenance-safe marker
(or an explicitly authorized programmatic-name restriction), beyond this
plan's exact blob/representation contract. Preserve the six implementation
commits and both review reports for a revised plan; do not hand-repair
patches or loosen fixtures. D1 documentation corrections are parked with
the repair, approximately 0.1 dispatch.

## A1 — P1 correctness blocker: an unrelated empty source axis changes M1's extent

**Identifiers:** `LHSSlot.outExtent`, `scatterPlacementSlot`,
`scatterDestExtent`, `scatterSourceAxes`, `scatterPlacementOrFail`,
`scatterOutShape`, `scatterOutputShapes`.

**Evidence:** `outExtent`'s new multi-axis arm checks emptiness over *all*
syntactically mentioned axes, including zero coefficients. The reference calls
it on the original slot; checked compilation calls it on a dense reconstruction
containing every source axis. `scatterSourceAxes` includes RHS-only axes too.
Consequently an axis absent from the original placement can incorrectly select
the legacy fallback in the checked backend.

Concrete newly admitted program: pin `a = 4`, `b = 3`, `c = 0`, declare f64
inputs `A(a)`, `B(b)`, `C(c)` and an unboxed output `S(k)`, then use a hand-built
single scatter `S[a+b] := A[a]*B[b]*C[c]`. The reference's original slot has
terms `[(1,a),(1,b)]`: both axes are nonempty, so extent is `3+2+1 = 6`.
Checked compilation reconstructs row `[1,1,0]` over source shape `[4,3,0]`:
the zero-sized `c` triggers the legacy fallback, yielding `4+3 = 7`.
Both source domains are empty, so the range check succeeds vacuously and the
workers publish all-zero tensors of different shapes, `[6]` versus `[7]`.
The same discrepancy affects a separate empty free LHS dimension.

This is introduced by M1 plus top-level admission, not a parked scan/group
behavior. It violates reference/checked shape agreement and can propagate
inconsistent shapes through downstream inference. Evidence is an exact
committed-code trace; runtime reproduction was deliberately not attempted
while the controller is mutating sources.

**Suggested verdict: fix now.** Make empty-domain extent policy consistent
between sparse source slots and dense checked rows without changing legacy
single-axis behavior. Preserve any deliberately retained explicitly-zero-term
policy, or explicitly adjudicate that policy if changing it is necessary.
Add end-to-end f64/f32/reference tests for a multi-axis slot with an unrelated
empty RHS axis and with an unrelated empty free LHS axis. Pin shapes, not only
empty data, and pin the extent helper as well.

## D1 — P3 documentation follow-up: live extent and refusal descriptions need surgical updates

Separate from A1; these are not logic blockers.

- **Fix now:** the `capabilityPreflight` documentation in
  `leanncd/LeanNCD/Eval/Plan/Compile.lean` still says
  `predicate Out(i)` with `Out[i+j]` produces `multiAxisScatterLhs`
  before `predicateScatterDest`. The top-level slot now passes, so that example
  produces the destination error. Use a raw constant bypass example to
  illustrate the retained form-before-destination precedence, or explicitly
  identify a scan-local example.
- **Fix now:** `scatterOutShape`'s docstring in
  `leanncd/LeanNCD/Eval/Eval.lean` still describes every affine extent as
  `c0 + Σ cᵢ·size(aᵢ)`. M1 makes that false for nonempty multi-axis placements.
  Describe delegation to `LHSSlot.outExtent`, distinguishing aligned
  single-axis and exact-reach multi-axis cases. Its separate claim about
  defaulting unseen UIDs to zero was already stale before this branch; do not
  count that as a new blocker.
- **Clarify as part of the doc pass:** the changed live entry in
  `Eval/Plan/AGENTS.md` and changed update in
  `papers/backend_missing_functionality.md` say boxed single constant/multi-axis
  writers are “not yet admitted.” They actually run with the derived shape;
  it is *collection into the declared box* that remains excluded. Say that
  explicitly, matching `convBoxed` and `S3`'s pinned-box guards.

Suggested cost: one small documentation edit pass (approximately 0.1 dispatch).

### Controller's other stale-text candidates: reject as findings

- `ScatterCheckTest`'s MIN-corner comment is correct: its immediately following
  fixture is row `[3,-1]`, bias `0`, source shape `[3,2]`, whose image is
  `[-1,6]` and derived extent is `7`. The later direct MIN guard uses
  `[2,-1]`, whose image is `[-1,4]` and supplied extent is `6`; it is a
  different fixture.
- `papers/scatter_affine_lhs_writes.md`'s `multiAxisScatterLhs` mention is in
  the explicitly dated S-B **scan-local** implemented design. That refusal
  remains live and correct. Its historical extent paragraph has an explicit
  slice-A update immediately afterward. No blocker or extra historical rewrite
  is warranted.
- The obsolete `LHSSlot.collapses` comment in `ScatterCompileTest` is expressly
  parked by the plan and excluded from this review's findings.

## A2 — P2 acceptance regression: the name marker misclassifies ordinary programmatic axes

**Identifiers:** `IdxExpr.isConstUnit`, `LHSSlot.boundedScatter`,
`assignUIDs`, `boxedSingleGroups`, `checkWriterGroup`.

**Evidence:** `isConstUnit` recognizes any `.affine _ [(1,a)]` whose
`a.name` starts with `#const`; it does not establish that lowering generated
the axis, or even that its extent is one. The surface grammar excludes `#`,
but `TLProgram` and `ScheduledProgram` are public programmatic inputs,
explicitly used for this slice's supported geometries. `assignUIDs`
remints UIDs without validating axis-name spelling. No source-axis prefix
reservation is enforced; `reservedNameCollision` checks generated tensor
names, not this axis prefix.

Concrete previously accepted **single-axis**, nonconstant program: create
`i = ⟨"#constUser", 90, .nat⟩`, `k = ⟨"k", 91, .nat⟩`; pin `i = 2`,
`k = 8`; declare f64 `A(i)` and `S(k)`; use one hand-built scatter with
slot `.affine (.affine 0 [(1,i)])` and RHS `A[i]`. Before the branch,
`boundedScatter` is true, `boxedSingleGroups` collects it, and all native
legs publish `[8]` with values `[1,2,0,0,0,0,0,0]` for input `[1,2]`.
At FINAL, `isConstUnit` is true despite there being no constant slot and
no generated unit declaration. Collection is silently bypassed: native
legs now publish `[2]` with `[1,2]`. Putting this ordinary writer in a
multi-writer group instead changes acceptance to `multiWriterScatter`.

This is not the deliberately excluded boxed **constant** behavior: the
slot is an ordinary extent-two identity placement. It changes previously
accepted single-axis programs solely because of a String name.
Evidence is the committed collector/marker/pipeline trace, not an executed
reproduction.

**Suggested verdict: fix now.** Identify generated constants by provenance
(for example, the generated UID set or an explicit internal marker), not
an unreserved source name alone. If reserving this prefix is preferred,
explicitly adjudicate the previously accepted programmatic-name regression;
the surface grammar alone is insufficient. Add a boxed-single and a
multi-writer accept-neighbor test using an ordinary `#const`-prefixed axis
of extent greater than one, alongside the genuine lowered-constant
refusal tests.

## Acceptance audit close-out

The complete branch diff was inspected, including all seven production
implementation paths, the four changed instruction/documentation nodes,
the test manifest, all six changed/new test modules, and both papers.
Immediate callers and relevant unchanged guards were inspected from FINAL.

- **Extent policy:** normalized repeated coefficients, mixed signs with
  nonnegative minima, three-axis reach, and single-axis stride alignment
  follow the intended code path. `a-b+2`'s widened acceptance is explicitly
  authorized and its cross-correlation values are pinned; a negative minimum
  remains a source-facing range error. A1 is the additional empty-domain
  sparse/dense mismatch the current fixtures miss.
- **Constants:** both assignment and explicit-scatter arms lower each raw
  constant to its own fresh pinned unit axis; two constants receive different
  UIDs. `assignUIDs` and lowering share the monotonically advancing `FreshM`
  counter in both real compile chains. Axis declarations deliberately stay
  out of `DeclEnv`; appended unit declarations feed `declaredAxisSizes`, so
  keeping the tensor environment unchanged is correct.
- **Groups/boxes:** genuine lowered constants retain their marker in their
  original slot shape. Both `boxedSingleGroups` and `checkWriterGroup`
  consult `boundedScatter`; multi-axis and true constant exclusions therefore
  remain intact. Derived shapes under boxed declarations are the explicitly
  parked slice-B behavior. A2 is a separate false-positive marker regression
  affecting ordinary programmatic names.
- **Scans:** raw constants next to `iterAt` or `iterNext` are not lowered;
  the assignment arm retains `overlappingScatter`. Hand-built scatters retain
  their raw constants and checked scan preflight refuses them, while its
  multi-axis sibling still produces `multiAxisScatterLhs`. A scan-dependent
  intermediate without an iteration LHS slot can be rewritten, but unchanged
  `compileScan` rejects *every* scatter scratch with
  `scatterScratchNotAdmitted`; this does not open a wrongly running checked
  scan. Reference-only scan overwrite/skip behavior stays parked under F3.
- **Other guards:** scatter nonlinearity validation still precedes lowering
  on both source constructors; checked predicate-destination and unlowered
  scatter-assignment refusals remain. Route's identity-scatter copy and JAX's
  categorical scatter exclusion were not broadened by compiler admission.
- **Fixtures:** inspected single-axis controls, mixed-sign accept/refuse
  neighbors, constant/free and two-constant placements, group/box exclusions,
  raw-constant bypass, scan-slot pins, native-f32 discriminators, and tropical
  four-leg rows. The max-plus versus max-times discriminator and tropical
  identity-filled holes encode actual semantic differences. No independent
  oracle-review verdict is claimed here.

### Verdict

**FINDINGS — not PASS.** Fix-now correctness findings: **A1 (P1)** and
**A2 (P2)**. **D1 (P3)** is a separate surgical documentation follow-up.
The three explicitly adjudicated stale-text/parked candidates are not blockers.

No builds, tests, hash checks, mutations, production edits, or commits were
performed; controller verification was not repeated. Both counterexamples
are exact committed-code traces, not runtime claims. Review stayed within the
requested turn/context budgets. Process note: the initial plan `git show`
returned oversized truncated output; the required sections were subsequently
read in bounded windows, as were committed-source snapshots.

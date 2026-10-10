# Source correspondence: authoring and execution record

## Status and authority

**Implemented and controller-verified, 2026-10-09.** All 79 named fixtures,
exactly 18 generated programs, 39/39 implementation mutation cycles, and the
controller full build (8,763 jobs) pass. T1-T5 per-task reviews and both final
whole-branch lenses are clean. Six fresh task patches replay exactly; historical
seed contrasts independently pass 6/6 and are not implementation kills.
See the final close-out below and the
[controller receipts](source_correspondence_artifacts/controller_closeout.txt).
Only the bounded source fragment described by the plan is completed; production
DSL/Eval is unchanged. Local integration is authorized by these gates; no remote
push is performed. The historical phases below retain their original scope.

The original 2026-10-08 Authoring Phase B was written from retained Phase A
evidence only, with no new implementation/prototype dispatch in that authoring
phase. The [live plan](source_correspondence_plan.md) subsequently entered
authorized implementation rehearsal; the checkpoints below record the actual
code, proofs and verification rather than treating the partial seed as complete.
Its six tasks specify the first complete slice, not several future slices.

Production is unchanged. Phase B also adds the plan's discoverability link to
the roadmap without changing its status markers. No agents, staging, commits,
integration, or remote operations occurred in Phase B. Plan-only documents may later be committed/
integrated by the controller; this authoring turn stops at document delivery.
Existing untracked evidence/patch artifacts were retained without rewriting.

## Baseline and compiled partial seed

Source: [evidence.json](source_correspondence_artifacts/evidence.json).

| Artifact | Identity |
|---|---|
| Base | `1e7be327c26bd102ffaebe38917976369bc19c59` |
| Detached prototype head | `284c7df2d169377d6029ae2a277c8a119929bbf1` |
| Context/Lowering commit | `76265762e18951399d64b6b087173cd8d03a3708` |
| Admission/Statement commit | `bd934a8eeaeda27503c25a328eaafe5a32af8e84` |
| Fixtures/imports/lake commit | `284c7df2d169377d6029ae2a277c8a119929bbf1` |
| Retained replay tree | `13b3b5f268a96bb57d8dd405602162041e81d0bd` |

Compiled patch identities retained from Phase A:

| Patch | SHA-256 |
|---|---|
| [1: Context/Lowering](source_correspondence_patches/0001-feat-semantics-prototype-UID-contexts-and-core-contr.patch) | `b492b2647813b63a399ec3d7fa42382e250b89cab079179ae254481fe3da31b6` |
| [2: Admission/Statement](source_correspondence_patches/0002-feat-semantics-prototype-pure-einsum-Program-corresp.patch) | `5810526e3721761b20642199c3429aaac6505e49dc9921fdcdec61d2dc3e4a09` |
| [3: Tests/integration](source_correspondence_patches/0003-test-semantics-verify-rational-source-correspondence.patch) | `a0a4305dd9f903e9dad7544156ccbe2826dc6509f6e488f42f2f040a132e92e0` |

Phase A reports ordered patch replay reconstructing that tree, fixture-target
build success, and full default build success with **8710 jobs**. Existing
imported Semantics warnings remain; no new prototype warnings were reported in
the successful fixture build. These are retained receipts, not full builds
rerun by Phase B.

## What the prototype actually establishes

- UID resolution and full-domain slot checking; unique binders with repeated
  slots referencing the same binder.
- **Positional** valuation/typed-coordinate equivalence only.
  `NamedVal` @ `leanncd/LeanNCD/Semantics/Source/Context.lean` is indexed by
  list position despite its name; no true UID-valuation theorem is established.
- Actual typed `Expr` products and nested reductions connect to interpretation,
  through `Program.collect`, and to independently specified `canonicalFiber`
  via `pure_correspondence` @
  `leanncd/LeanNCD/Semantics/Source/Statement.lean`.
- One defined target and one generated statement; every other tensor is input.
  Explicit supplied output/contracted partitions, read-only factors.
- Full destination coordinates, including unwritten off-diagonal empty fibers.
  This does not establish the proposed multi-target source-generated schedule.
- Reported proof dependencies are standard `propext`, `Classical.choice`,
  `Quot.sound`; evidence reports no new axioms, sorry, unsafe, noncomputable
  executable definitions, or supplied model witnesses.

These source modules/tests are patch-only future files in the planning tree.
Phase B inspected bounded patch windows, not an installed implementation.

## Observed semantic fixtures and controls

Retained exact rational runtime observations:

| Named fixture | Actual complete published values |
|---|---|
| distinct-UID-same-name-extent | `[26]` |
| shared-variable-diagonal | `[13]` |
| scalar-rank-zero | `[21]` |
| empty-contraction-nonempty-output | `[0, 0]` |
| repeated-output-full-shape | `[5, 0, 0, 9]` |
| two-term-local-bias | `[9, 9]` |

Eight admission observations: UID-lookup-distinct and UID-lookup-repeated accept;
duplicate-context rejects with duplicateContext; full-slot-domain rejects with
domain UID 10, expected 3, actual 2; output-only-pure rejects with outputOnly
UID 10; broadcast-general accepts; ordered-output-domains rejects with domain
UID 13, expected 2, actual 3; ordered-output-accept accepts.
These values/errors are from evidence, not newly derived numerical fixtures.

## Mutation class and verification strength

The six cycles in [mutations.json](source_correspondence_artifacts/mutations.json)
change fixture inputs: independent vs shared UID, shared vs independent UID,
removed scalar operand, zero vs singleton extent, incorrectly contracted bias,
and repeated vs independent output.
They are **fixture-input semantic contrast cycles, not implementation kills**.
All intended failures were observed, originals restored byte-identically, and
restored builds passed. The parent's independent replay checked the manifest's
`expect` strings and restoration gates:
[controller receipt](source_correspondence_artifacts/controller_mutations.md).

No whole-prototype external review has been performed.
The planned 79 named fixture entrypoints (F16 expands 18 candidate programs)
and 39 implementation cycles are unobserved. They have no completed receipt
and no invented `expect`. A separate future post manifest must be observed and
verified before readiness; the six retained contrast cycles are not relabeled.

## Production observations and Phase B rerun

Sources: [production_evidence.json](source_correspondence_artifacts/production_evidence.json),
[probe source](source_correspondence_artifacts/production_probe.lean), and
[retained log](source_correspondence_artifacts/production_probe.log).
Explicit f64 declarations, finite pinned domains, integer-valued input probes:

| Probe | Legacy and checked observation |
|---|---|
| matmul | shape `[2, 2]`, values `[4, 5, 10, 11]` |
| term-local-bias | shape `[2]`, values `[13, 24]` |
| diagonal-read | shape `[]`, values `[13]` |
| diagonal-write | shape `[2, 2]`, values `[5, 0, 0, 9]` |
| empty-contraction | shape `[2]`, values `[0, 0]` |
| scalar | shape `[]`, values `[21]` |
| within-statement-duplicates | shape `[2]`, values `[10, 18]` |
| cross-statement-known-contract | shape `[2]`, values `[2, 4]`; last same-lhs statement overwrites |
| default-dtype-outside-f64-profile | Legacy unsupportedDtype A f32; checked inputSignature dtypeMismatch A f32 f64 |

Seven output agreements are observations on separate probe inputs, not a
reference-production automated harness or refinement theorem. The bias inputs
differ from the retained semantic bias fixture; do not equate their values.
The overwrite observation is a known contract difference, not shared-fragment
parity. The default declaration is f32; do not silently rewrite it to f64.
Successful production probes reported empty warning lists.

Phase B copied the retained source to the uniquely named scratch file
`PhaseBSourceProductionProbe.lean` under `leanncd/spikes/`, ran:

```sh
bash /Users/williammacready/code/python/pyncd.worktrees/executable-semantics-plan-differential-debugging/leanncd/scripts/lean-file.sh /Users/williammacready/code/python/pyncd.worktrees/executable-semantics-plan-differential-debugging/leanncd /Users/williammacready/code/python/pyncd.worktrees/executable-semantics-plan-differential-debugging/leanncd/spikes/PhaseBSourceProductionProbe.lean
```

The command exited 0 and reproduced all nine retained observations above.
Phase B then removed only its named scratch copy. The artifact source remains.
A pre-existing `SourceProductionProbe.lean` scratch file was not altered.
This was a retained-probe rerun, not a new implementation or production mutation.

## Authoring checks, budgets, and pending gate

Phase B loaded the slice-plan skill, used bounded evidence/patch/style windows,
checked existing donor/integration paths without broad code exploration, and
kept source-file references as identifiers @ file rather than unstable lines.
Proposed output files are explicitly future, not asserted to exist.
No Lean blocks were written; snippet compilation is therefore not applicable.
The document validation receipt is appended below after checks.

Target: at most 30 Phase B turns; general dispatch cap approximately 60 turns/
250k peak, authoring approximately 50M cumulative input target. Token-report
telemetry is unavailable for this SDK authoring session; cumulative input and
peak are **unmeasured**, not zero. No measured token-budget compliance or breach
is claimed. A controller must record measured usage when available.

The design chooses the scope and contracts; remaining gates are validation
work, not permission to widen the slice. In particular: validate the accessible
resolved-AST seam, UID binding/capture avoidance, general tagged Program/schedule,
actual generalized proof, typed diagnostics/four-leg numerical profile, all new
fixture families/implementation cycles, public imports, and two final reviews.
If a rehearsal shows an obligation impossible without production changes or a
scope expansion, stop and report the design blocker rather than improvise.

Parked unrelated issue: stale f64 comments in production AST/DSL AGENTS.
Code and latest tests take precedence. Not needed for this goal; approximately
one Direct documentation dispatch if separately authorized.

### Document validation receipt

Automated checks passed for the plan's 79 fixture rows by task (8/18/12/8/15/18),
39 planned cycle counts (4/8/6/4/8/9), existing relative link targets, absence of
Lean blocks and unstable Lean line locators, and document whitespace.
Roadmap LANDED/REMAINING lines were compared with HEAD and are unchanged.
The Phase B scratch copy is absent. Tracked changes are only the additive
roadmap edit; the two new documents and retained evidence/patches are untracked.
`git diff --check` passed. No full prototype build or new mutation cycle was
performed in Phase B; those receipts above are explicitly retained Phase A work.

Phase B stayed within the 30-turn authoring target. Token/peak telemetry remains
unavailable, so no cumulative-input or peak-budget measurement is reported.

## Controller close-out

The controller reviewed the complete planning changes for source/semantic scope
and diagnostic/oracle fidelity. Corrections: the `collect_relabel` locator now
names `Program.lean`; failed occurrences are ready and cannot themselves have
missing reads; the independent acyclic oracle requires its own checked fixture
order; and the generated corpus has 18 distinct candidates rather than repeating
scalar programs for irrelevant extent choices. No remaining blocker to publishing
this **design plan** was found. This is not the two independent implementation
reviews required by its readiness gate, nor a whole-prototype external review.

Independently rerun controller gates:

- Six fixture-contrast cycles: intended failures, byte-identical restoration,
  and restored builds all passed; see the
  [mutation receipt](source_correspondence_artifacts/controller_mutations.md).
- [Planning-tree full build](source_correspondence_artifacts/controller_planning_build.log):
  passed, 8,704 jobs.
- [Restored prototype full build](source_correspondence_artifacts/controller_prototype_build.log):
  passed, 8,710 jobs.
- Document constraints, relative links, three patch hashes, both JSON records,
  79 fixture entries, 39 proposed cycles, and 18 distinct corpus candidates:
  passed.
- The controller's named scratch probe copy was removed. The retained probe
  source and historical logs remain.

Builds are green, not warning-free: imported existing warnings and unrelated
pre-existing `sorry` declarations remain. No new production proof or runtime
code is integrated by this planning branch.

Local main advanced concurrently to `d879b8a` with only a roadmap table of
contents. Its diff was checked: no semantic contract or implementation changed.
That addition must be preserved during local integration. The prototype and
its patches retain their measured historical base `1e7be32`.

The detached prototype is disposable; retained patches and receipts are the
persistent handoff. `emit_evidence.py` is historical provenance code referring
to the original authoring locations, not a portable execution/readiness runner.
No remote push is authorized or performed.

## Readiness rehearsal in progress

The user authorized readiness rehearsal before implementation on 2026-10-08.
The isolated execution worktree was fast-forwarded from `e13fd6f` to local
`main` at `d0f8462`; the preparation script verified its warm Mathlib cache.
Controller library refresh passed, followed by the full unchanged baseline
build: **8,704 jobs**. Existing warnings remain; this is not a warning-free
receipt or a completed source-slice build.

The public resolution seam was exercised without production changes. Direct
`resolveDecls` retained axis UID `40`; `assignUIDs` followed by `resolveDecls`
produced UID `1`. Both retained two original same-target statements in order.
Both classified the read input as external but omitted an unused declared
input from `extNames`, confirming that explicit semantic input roles cannot
be derived from that field. Two controller `#guard` checks passed through
`lean-file.sh`; the named scratch source was removed afterward.

T1 production now has UID-keyed dependent valuations, coordinate equivalences,
domain-preserving transports/pullbacks, and automatic generated-only freshness
proofs. Production module and smoke builds passed. These are partial rehearsal
results, not T1 fixture/mutation completion or an execution-ready declaration.

The V5 fixture rehearsal exposed a real API mismatch: automatic freshening
accepted no requested replacement identity, so its requested-collision witness
was unrepresentable. The user explicitly chose to preserve V5 by adding a
requested-identity freshening entry rather than weakening the fixture.
That correction is now compiled and verified by the V4-V6 fixtures. Individual fixture Lake
targets are registered as well as their aggregate; initial target-registration
failures are not counted as fixture checks or mutation kills.

Root hook guidance initially measured 3,014 characters for Patterns/Pitfalls;
its reference-summary prose was shortened below 3,000 without dropping rules.
The semantic guidance node has no matching hook sections.
The token reporter found no Claude transcript for this Copilot SDK session;
cumulative input and peak usage remain **unmeasured**, not zero.
No rehearsal code has been committed, integrated, or pushed.

### T1 readiness checkpoint

All **eight** T1 fixture entrypoints are observed and verified. The controller
built `+Semantics.SourceBindingTest`: **2,953 jobs**, including the three
registered fixture bundles. Representative observed witnesses:

| Fixture | Actual observation |
|---|---|
| V1 | UID/reference values `(1, 0)`; distinct/reversed matrix reads `11` and `2` |
| V2 | Shared-UID diagonal matrix reads `12` and `1` |
| V3 | Forward/inverse reordered coordinates `(2, 1)` and `(1, 2)` |
| V4 | Original/transported values `[2, 1, 0, 1, 1]` and read `21011`; stale metadata rejects `unbound 3` |
| V5 | Output/free collisions freshen generated UIDs to `106, 108`; valid requests give `203, 205`; original read remains `21011` |
| V6 | Rejections `domain 19 4 2`, `domain 19 4 5`, `domain 19 2 4`; legal neighbors return `[1]`, `[3]`, `[1]` |
| V7 | Pullback `[1, 0]` to `[0, 1]`; matrix `11` to `2`; repeated lookups `[0, 0]` |
| V8 | Empty/zero context enumeration `(1, 0, [[]], [])`; inverse/uniqueness/nonexistence proofs elaborate |

At the T1 checkpoint the [post manifest](source_correspondence_mutations_post.json)
contained **four of the planned 39** implementation cycles. The controller ran all four
with `expect` strings copied from retained complete mutated-build diagnostics.
Every expected payload was seen, each source was restored byte-identically, and
every restored build passed. The named protected obligations are
`Ref.get_uidCoordEquiv` / `Ref.sameUID_lookup`,
`Context.reenumerateTransport`'s inverse law,
`BinderScope.requested_fresh` / `BinderScope.requested_injective`, and
`resolveUID`'s exact domain witness. These are **proof-protected implementation
kills**, not runtime differential-fixture kills or the historical six input
contrasts. No unrelated syntax/import/target failure was counted.

The T1 read-only readiness review found no significant issues and confirmed the
aggregate build and kill classifications. This is a per-task checkpoint, not
either final whole-slice review. T2 production rehearsal has started; T2-T6
fixtures, the remaining 35 cycles, and the complete readiness gate are pending.

### T2 validation and acceptance correction

The T2 adapter, admission module, and generic read/contract donor compiled.
The original **18** admission entrypoints passed the controller's aggregate
build: **8,516 jobs**. No production DSL/Eval module changed.
Representative discriminating observations:

| Fixture | Actual observation |
|---|---|
| A1/A2 | Prefix-sharing domain rejects `domain 3 2 3` at original statement 2/term 1/factor 1/slot 0; exact-domain neighbor admits |
| A3 | Simultaneous output-domain/rank violation reports `domain 7 3 2` at original statement 2/slot 1 before rank |
| A4 | Destination `[3, 7, 3]` projects to `[2, 1, 2]`; operand `[7, 3]` projects to `[1, 2]` |
| A5/A6 | Classification is per term; missing-output term stays broadcast, and bias contraction remains empty |
| A7/A8 | Direct empty product/sum retain exact rational one/zero identities |
| A9/A10 | Duplicate axis/tensor rejects at original declaration 8; distinct resolved UID and declaration neighbors admit |
| A11/A12 | Valid input binding does not mask original statement 1 write-role refusal; unpinned domain is not inferred |
| A13/A14 | Missing unused nonempty input 8 and empty input 6 both reject; restored bindings expose complete typed buffers |
| A15/A16 | Exact length rejects `6/5`; simultaneous shape/length violation reports `[2, 3]/[3, 2]` before length |
| A17/A18 | Iverson/unary refusals retain original statement 3/term 1/factor 2, without fabricated declaration/slot |

All **eight** T2 implementation cycles were observed and rerun by the controller
through the post manifest with exact expected diagnostics, byte-identical
restoration, and green restored builds. Three are proof-protected: full-domain
`Ref` construction, `SupportPartition`'s exact bound witness, and the writable
target witness. Five fail executable admission fixtures: reordered slots,
duplicate-axis shadowing, unpinned-size inference, fabricated missing input
bindings, and shape/length bypass. The post manifest now has **12 of 39**
observed cycles. An initial invalid inequality-as-equality transport proposal
was corrected before execution; no syntax failure was counted as a kill.

The T2 review found two HIGH, goal-required acceptance defects: nat-only guards
rejected finite pinned real axes and actual parser use-site placeholders, and
blanket linear-declaration refusal rejected ordinary finite read sum-products.
Both were fixed on the **Direct correction path**, not by narrowing the plan.
Three supplemental regression families went from semantic RED to GREEN:
`FinitePinnedRealCopy`, `ParsedRawNatCopy`, and `RealLinearSumProduct` in
`SourceAdmissionAcceptanceTest`. The parsed fixture uses actual `tlprog!`
syntax; it is not a hand-built or normalized substitute. Real tensor/linear
variants retain f32/f64 metadata and original declaration identity, with both
bias flags and nearest forbidden controls. The corrected aggregate passed
**8,519 jobs**. These three supplemental families are additional to the
original 79 planned entrypoints, not retroactively relabeled matrix receipts.

The [admission audit](source_correspondence_artifacts/admission_audit.txt)
was corrected for finite nat/real declarations, UID-based
bare use sites, and compatible real linear declarations. Three supplemental
hand mutation checks observed the named acceptance guards fail when each bug
was restored, then restored aggregate builds passed. They do not add entries
to the 39-cycle post manifest. The targeted re-review confirms both HIGH
findings fixed with no new significant tightly coupled issue or narrowing.
T2's gate is cleared and T3 production lowering has started. The final whole
post-manifest rerun on the integrated corrected tree is still required.

### T3 readiness checkpoint

General normalized multi-target Programs, computational complete schedules,
validated exact execution, automatically certified original identities, and
tag-preserving statement permutations are implemented. Actual body and ordered
read-footprint proofs preserve term-local binders and multiplicity. Permutation
collection uses `Program.collect_relabel`; whole-store model invariance does
not assert event-order invariance. No production DSL/Eval changes were needed.

All **12** P entrypoints passed the controller aggregate: **8,521 jobs**.
P1/P5/P9 compare actual complete reference runs with the independent exact
oracle, including shapes and every tensor cell. P2/P3 check nonzero original
ordinals, both provenance inverses, permutation-stable UID assignments, and
different event presentations. P4 retains identical additive occurrences;
P5/P6 publish nonoutputs and full unwritten domains. P7-P9 check unequal
layouts, complete key coverage, unused/empty input presence, and exact nested
ordered read footprints. P10-P12 retain actual blocked/exhausted snapshots
and scalar/empty/repeated-slot full publication domains.

Six T3 post cycles passed observed expectations, byte-identical restoration,
and restored builds. All are **proof-protected implementation kills**:
role-derived definedness, original-ID preservation, tagged occurrence coverage,
nonoutput publication coverage, unwritten coordinate coverage, and exact
nested footprint correspondence. The first proposed P9 mutation changed
scalar interpretation as well as reads; it was not counted for the footprint
requirement. The counted mutation changes `reductionReads` and is rejected
by `footprint_contract`'s equality with the actual expression footprint.
The post manifest now has **18 of 39** planned cycles; **38 of 79** planned
fixture entrypoints have verified receipts, plus the supplemental acceptance
and independent-oracle families.

The T3 per-task review is clean. General global-fiber correspondence remains
T4 work, and source-linked diagnostics/four-leg comparison remains T5 work.
Oracle full-cell fiber rows are not actual occurrence tags: repeated-slot
offdiagonal cells have no occurrence, while valid zero-contraction output
assignments do. T5 must normalize that distinction independently.

Budget limitation: the provenance worker reported approximately 59 rounds
after its helper follow-up, followed by additional coordination replies.
This may exceed the approximate 60-turn cap; exact telemetry is unavailable.
It was retired without further work. Later draft bundles use controller-only
build coordination to avoid acknowledgement churn.

Execution interruption: work stopped after the 2026-10-08 evening status
reply; no background work continued overnight. The earlier statement that
work was continuing was inaccurate. On 2026-10-09 the controller resumed,
ran T3's actual mutation gates, and completed the synchronous per-task review.
No commit, local integration, or remote operation has occurred.

### T4 readiness checkpoint

`Fiber`, `Correspondence`, and `ProgramCorrespondence` now prove the genuine
generic-semiring bridge. The independent global domain is each term's original
read UID support union output UID support, selected in resolved order; an
unrelated zero-extent declaration does not erase a nonempty term.
True UID-dependent valuation bijections connect that domain to output and
term-local contracted valuations. Products preserve original factor order;
destinations retain repeated original slots.

Actual normalized expression interpretation and actual `Program.collect` are
the left sides of the bridge, not aliases for the global formula. The program
proof uses `collect_grouped` and genuine tag/valuation reindexing.
`collect_relabel` connects certified original IDs and statement permutations,
preserving multiplicity. Execution-backed whole-store global equations,
uniqueness, and output denotation use the existing reached result theorems.
No Float algebra, supplied model/rank witness, arbitrary successful snapshot,
or production change was introduced.

All **eight** B fixtures passed the controller aggregate: **8,524 jobs**.
They cover rank zero, nonempty outputs with zero contraction, repeated-output
offdiagonal fibers, unequal term-local bounds and bias, asymmetric original
UID order and slots, original duplicate contribution IDs, domain-preserving
rename/re-enumeration, and nested body/collection specialization to Nat and Rat.
The Rat nested observation is `173710/9`; the Nat observation is `19310`.
Initial test elaboration issues were corrected with explicit dependent binder
types and a typed `calc` endpoint, without changing production proofs.

All **four** T4 post cycles passed expected diagnostics, byte-identical restore,
and restored builds. These are proof-protected kills at zero-reduction
interpretation, full destination projection, term-local body/footprint, and
`Program.collect_relabel`'s multiplicity equation. The last mutation also
produced a class-inference diagnostic; that incidental diagnostic is not the
counted receipt. The per-task review found no significant issue.

Verified planned totals are now **46/79 fixtures** and **22/39 cycles**, plus
the supplemental acceptance and oracle families. T5 diagnostic/comparison
fixture gates and T6 corpus/final integration remain outstanding.

### T5 implementation and fixture checkpoint

`Observation` / `Diagnostics` retain actual validated execution, certified
source identities, typed admission causes, complete/blocked/exhausted snapshots,
actual event payloads, and canonical occurrence comparisons. Term evaluations
without a hook and native internals remain explicitly unobserved. Independent
oracle-row normalization distinguishes repeated-slot offdiagonal cells without
an occurrence from valid zero-contraction occurrences contributing zero.

`NumericalProfile` enforces the bounded-integer profile, including mandatory
subset-product and absolute-sum envelopes that cannot hide an oversized
intermediate behind a later zero or cancellation. Expected binary64 bits are
computed by an independent integer algorithm; comparison normalizes signed
zero but retains original observed encodings. Its smoke verified 24 guards,
including 2,097,154 bounded signed-integer encoding comparisons.

`NativeLegs` invokes actual legacy evaluation and checked compilation,
preparation, and execution without changing source declarations. Original
causes, warnings, source mappings, raw environments, shapes and bits remain
available. `Differential.compareSource` composes all four legs and retains
every refusal. Its smoke achieved **7/7** strict four-leg donor agreements and
passed all **26** guards. Arbitrary rational reference runs, f32 native failures,
known cross-statement overwrite differences, missing oracle order, identity
nonrepresentability, blocking, and exhaustion do not receive parity labels.

All **15** D entrypoints passed the controller aggregate: **8,562 jobs**.
D3 and D13 remain explicitly injected renderer protocols, not actual reached
source/backend failures. D14 never guesses native internal causes; D15 checks
stored and rendered injected warnings. D7/D8 pin exact later coordinates and
whole-structure-before-cell ordering; D9 retains interleaved original IDs.
The observed cyclic oracle error includes original declaration 1, which the
draft had omitted; the fixture was corrected to assert the actual full locator,
not to discard provenance. Reserved test identifiers and multiline record
layout errors were also corrected, without production changes.

Planned fixture receipts are **61/79**. All eight T5 post cycles subsequently
passed their intended executable guard failures, byte-identical restoration,
and restored builds. The complete post total is now **30/39**.
The mutations pin conservative intermediate envelopes, canonical occurrence
ordering, actual differing coordinates, exact shapes, original source ordinals,
compile/preparation/runtime cause distinctions, stored warnings, and unobserved
native internal localization. The per-task review found no significant issue.
The final corpus and whole-branch gates still remain.

Telemetry update: the resumed session's shutdown checkpoint reports cumulative
input `66,646,841`, output `577,764`, cache-read `64,657,712`, and cache-write
`1,986,894` tokens through the previous session segment. The input counter
includes cached input (the cache totals are approximately the input total), so
they are not added a second time. This is partial historical telemetry, not a
current end-to-end total or a peak-context measurement. Current segment and
dispatch peaks remain unmeasured until equivalent final telemetry is available.

Subsequent decoding of the SDK's serialized cache checkpoints exposed a
controller prompt checkpoint of **348,992 tokens**, above the approximately
250k context cap. This is a confirmed controller-context breach, not a claimed
compliant peak. Cumulative end-to-end input still cannot be reconstructed from
the available segment counters without double-counting cache tokens. The
remaining close-out is handed to a fresh, bounded controller context; no further
implementation work is assigned to the oversized context.

### T6 fixture and observed-mutation checkpoint

All **79 planned fixture entrypoints** are now verified, including the final
18 F families. F16 additionally evaluates exactly **18 structurally distinct**
deterministic programs: two scalar factor-count cases and sixteen rank/extent/
factor-count cases. Refusals and reference-only cases are never counted as
four-leg parity. The final aggregate passed **8,564 jobs**.

The corpus pins asymmetric matrix/packing behavior, per-term bias, repeated
reads and diagonal writes, zero contractions, scalar/AST identities, duplicate
terms, UID alpha transport, negative/zero comparison policy, inclusive integer
envelopes and unsafe intermediate refusals, unchanged f32 source failures,
known overwrite-versus-collection differences, tagged permutations, acyclic
multi-target publication, and resolved same-name/distinct-UID limitations.

Initial draft syntax/inference problems were repaired without production
changes. The geometry helper had incorrectly equated the native traversal's
complete axis-occurrence list with the semantic context's distinct UID list;
its checks now distinguish both while retaining all value/bit/publication
assertions. A final mutation run exposed parser keywords entering the
independent oracle fixture through the shared umbrella import. The shared
admission donor now imports `Source.Admission` only, and its scalar declaration
fixture imports `RationalReference` explicitly. Oracle, admission, and final
differential targets were rerun together and passed. The failed setup/restored
build was not counted as a mutation kill.

All nine T6 intended mutants were then observed and restored successfully:
eight executable fixture kills (diagonal refusal, zero-domain singleton,
transposed independent packing, term deduplication, removed zero normalization,
silent f32 rewriting, falsely shared multiple definitions, and UID lookup
merging), and one proof-protected full-publication coverage kill.
The post manifest contains all **39 observed planned cycles**, with expected
strings copied from actual failures. Final whole-manifest expected/restoration
verification, full build, patch replay, and the two independent whole-branch
review lenses are still pending at this checkpoint.

## Final controller close-out (2026-10-09)

A fresh final controller observed the already-running complete post manifest,
without launching a duplicate run. Its terminal table reports **39/39 PASS**:
every intended expected-text diagnostic was seen, every file was restored
byte-identically, and every restored build was green. These comprise **18
proof-protected kills and 21 executable-fixture kills**, not 39 runtime
differential samples. The six historical input contrasts were independently
replayed on pinned seed `284c7df2d169377d6029ae2a277c8a119929bbf1`: **6/6 PASS**,
with expected diagnostics, byte restoration and restored builds.
The tables are retained as
[implementation mutations](source_correspondence_artifacts/controller_post_mutations.md)
and [seed contrasts](source_correspondence_artifacts/controller_seed_contrasts.md).

Both independent whole-branch reviews are **CLEAN**, with no finding requiring
adjudication, against base `d0f8462` and immutable reviewed tree
`3d057e1f9a0894dd7318ba28fae50b7d89dc8015`. Lens 1 covers binding, elaboration,
soundness, provenance and schedules; lens 2 covers oracle independence, numerical
profiles, differential classifications and diagnostics. Their retained reports
are [lens 1](source_correspondence_artifacts/controller_soundness_review.txt) and
[lens 2](source_correspondence_artifacts/controller_differential_review.txt).
These are static reviews, not substitutes for controller execution.

After the manifest finished, this controller ran:

```sh
bash /Users/williammacready/code/python/pyncd.worktrees/source-correspondence-debug-plan/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/source-correspondence-debug-plan/leanncd
```

The actual-worktree full build exited 0: **8,763 jobs**. Existing unrelated
warnings and `sorry` declarations remain; there were no new Source warnings or
errors. A source-tree comparison after restoration and after the full build
confirmed all of `leanncd/` identical to the immutable reviewed tree. Subsequent
edits are documentation and mechanically generated receipt/patch sidecars only.

The fresh six-patch series is replayed in task order from `d0f8462` with an
alternate Git index. Its final tree equals the staged implementation and
documentation tree excluding the patch sidecars, which are staged separately to
avoid self-reference. Patch 6 is regenerated from the T5 checkpoint
`4c251da391667c5e2cd44d055322c0bd6b8fb360`. Exact replay identities and patch
SHA-256 values are retained in the session's final replay receipt; the committed
patch series is the persistent reproduction artifact.

Local `main` advanced during execution to
`6e1c2ea0eb9539e23acc69ede59f3e3db5ac1133`. Its changes since `d0f8462` are confined
to `tensor_logic_semantics.md`, which this branch does not modify. Integration
preserves that concurrent work; it does not rewrite or force-update history.
No remote push is performed. Final commit/merge identities and worktree/branch
cleanup are recorded in the controller's session close-out after integration.

**Limits and honest classifications.** This is finite read-only scalar
sum-product correspondence, not general backend refinement. The core supports
arbitrary rationals; strict four-leg comparison requires the checked bounded
integer profile and explicit original f64 declarations. Missing oracle order,
unsupported profiles/forms, blocking, debug exhaustion, f32 failures and known
cross-statement overwrite/collection differences remain explicit, not parity.
D3/D13 and warning/signed-zero injections are protocol checks, not actual
backend faults. Native internals without hooks remain unobserved. The parked
pre-existing f64 AST/DSL comment cleanup is outside this goal.

**Budget breach surfaced, not certified away.** The earlier controller reached
a measured **348,992-token** prompt, above the approximately 250k cap; this
close-out used the prescribed fresh-context split. Available historical input
is **66,646,841 cache-inclusive tokens**, only a partial segment, not the total.
Do not add cache counters again. End-to-end input, full dispatch peaks and
compliance with the 175M execution/50M authoring targets remain unmeasured.
No new implementation/review dispatch or duplicate mutation run was launched
for close-out.

## 2026-10-09 — bounded raw-source/admission follow-up

The original source-slice receipts above, including its 39 implementation controls,
remain historical and unchanged. The separately executed
[raw-source/admission recipe](raw_source_admission_plan.md) adds actual-success
`admitRawSource_fields` and `admitRawSource_certified`: name-keyed resolver coverage,
ordered pinned declarations and original declaration indices, exact raw indexed
statement/term/factor/slot transport, and certified raw-coordinate witnesses for
the existing body/footprint/fiber/Program results. Both new modules are reachable
through `LeanNCD`; `Semantics.SourceRawCorrespondenceTest` is in default `Tests`.

`admitRawSource_reached` requires an actual validated rational result and its
complete-outcome equality. All-defined equations, input agreement and uniqueness
are relative to `result.input`; denotation applicability is output-restricted.
Canonical parsed/asymmetric donors use `sourceInput` but do not remove the
completion premise. No independent raw denotation, parser correctness, global
mint injectivity, input-buffer certification, unconditional completion, oracle
equality or numerical/backend refinement is claimed. Existing production
cross-statement additive divergence is unchanged.

The follow-up has ten fixture families and 17 controls: 15 proof-protected
rejections, two fixture contrasts and zero runtime kills. Its stage/final
validation, review verdicts and integration disposition are recorded separately
in the [raw-source/admission record](raw_source_admission_record.md), not counted
as new differential samples or folded into the original 39.

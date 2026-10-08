# Source correspondence: authoring record

## Status and authority

2026-10-08, Authoring Phase B. Written from retained Phase A evidence only;
no new implementation/prototype dispatch. The
[live plan](source_correspondence_plan.md) is a **design plan with verified
partial prototype, NOT execution-ready**. Its six tasks specify the first
complete slice, not several future slices.

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

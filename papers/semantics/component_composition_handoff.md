# Next-session brief: static sealed component composition

## Launch instruction

Read this brief, prepare and verify one implementation plan for the static
sealed-composition slice, then execute its tasks and release gates. Preserve
existing changes. Do not rerun the completed transport plan.

**Process weight: Full.** This is a new semantic construction and proof surface.
This file is a handoff, **not a verified execution plan**: it contains no Lean
implementation blocks, executable task patches or new mutation manifests.
The next session must author those before claiming execution readiness.

## 1. Starting state and authority

Typed declaration/read/expression transport has landed on local `main`.
Its merge is `f113012d`; integration was recorded in `818e9f83`. These are
provenance, not required future implementation HEADs. Start from latest local
`main` and recheck API compatibility.

Read, in this order:

1. [Component-interface design](categorical_tensor_logic_component_interfaces.md),
   Sections 1-5, the concrete example, and remaining-work summary.
2. [Transport execution record](component_transport_execution_record.md)
   for what is actually implemented and its validation limits.
3. [Conditional correspondence proof record](categorical_tensor_logic_proof_record.md)
   and [theorem-design brief](categorical_tensor_logic_theorem_brief.md).
4. The targeted declarations in Section 5 below.

The [transport plan](component_transport_plan.md) describes the completed
prerequisite. It is not a plan for this new slice. A verified static-composition
plan does not yet exist at this handoff's authoring.

The main checkout is `/Users/williammacready/code/python/pyncd`.
Existing primary-checkout edits to the synthesis and semantics contents,
and the original authoring worktree's files, are outside this task.
Do not overwrite, stage or discard them.

Use GPT Sol with high reasoning effort for difficult design decisions.
Keep each delegated objective bounded; do not dispatch the entire new
construction/proof as one unbounded job.

## 2. Exact goal

A **matched component** packages its own finite declarations, reference
program, complete ordered schedule, contract, writer fragment, canonical
closed graph and supplied source-contract match. A **whole-tensor port**
records tensor identity, scalar sort and complete coordinate domain,
including an empty domain.

Given two matched components and compatible whole-tensor interfaces,
construct their composite data and a genuine `SourceContractMatch` for it.
The proposed theorem name `compose_match` is a design label, not an existing
Lean declaration.

The construction must use the component matches and generic preservation
lemmas. It must not independently author the entire composite match, assume
that match, or take execution agreement as a premise.

Remain in the finite, one-sort exact-rational profile:
`Declarations Unit`, `RationalReference.Carrier`, `registry` and `ops`.
Reuse supplied axis-certified transport adapters. A rank certificate is not
needed for this static theorem; ranked execution claims remain a later slice.

## 3. Construction requirements

Let `A` mean the upstream component and `B` the downstream component.
Each component declares only its own tensors. Its input/output port lists
must agree exactly with the program's roles; outputs are defined tensors,
not input aliases.

### Scope and boundary

- Match every input of `B` bijectively to an output of `A`, using every
  upstream output. Supply explicit typed domain adapters.
- Never infer identity from display names, equal extents, cardinalities or
  coincident old numeric UIDs.
- Use a composite tensor universe containing all tensors of `A` plus a
  disjoint summand of only `B`'s defined tensors.
- Embed a downstream input at its explicitly matched upstream output.
  Do not create another external input or a copy computation.
- Retain every private defined tensor and its internal work. Freshen or
  explicitly separate retained tensor, occurrence, tag and capability
  identities; apply numeric renaming consistently to all references.
- Supply checked identity embeddings rather than introducing an unrelated
  general-purpose namespace-allocation service.
- Preserve whole-tensor metadata. `Contract.outputs` is address-only and
  cannot recover the identity of an empty output tensor.

### Source, writers and contracts

- Composite inputs are exactly `A`'s inputs; exterior outputs are exactly
  `B`'s outputs. Upstream outputs remain defined internal tensors.
- Preserve statement identities, valuation counts, guards and every actual
  guard-admitted occurrence, including distinct equal-valued contributions.
- Transport destinations, bodies and their dependent valuation contexts
  through the existing embeddings. Preserve ordered full read lists,
  including repeats and strict whole-array footprints.
- Keep all noninput collectors and zero-writer fibers. A standalone `B`
  input has no collector: its boundary collector is already owned by `A`.
- Downstream destinations must lie only in its own defined summand.
  Downstream code cannot extend upstream collector capability families or
  modify a sealed upstream result. Upstream reads cannot depend on downstream
  private values.
- Keep tensor validation order explicit and complete. Append upstream
  collectors/keys before downstream collectors/keys, preserving internal
  collector and capability order.

**Structurally sealed** means the complete writer family is fixed and checked.
It does not mean runtime completion. Upstream-first priority is not, by itself,
a general runtime phase barrier: the runner skips disabled actions.
Do not introduce a staged runner or silently claim a phase theorem.

### Construct every match field

| Existing field | Required derivation |
| --- | --- |
| `close_ok` | Prove composite closure acceptance from component closure and interface/transport facts; do not retain it as an extra composite premise. |
| `input_roles` | Derive the composite input predicate from upstream roles and boundary identification. |
| `tensor_order` | Use the same complete, duplicate-free ordered enumeration for contract and schedule. |
| `outputs_exact` | Derive exact downstream output-address coverage; retain empty-output metadata separately. |
| `sourceToWriter` | Combine the actual occurrence bijections with disjoint-union/concatenated-position equivalences. |
| `writer_destination` | Transport each component's destination equality. |
| `writer_reads` | Apply ordered footprint transport, without deduplication. |
| `eval_agrees` | Restrict any composite partial store to its component, apply local agreement, and transport both evaluations. |
| `priority` | Prove the appended mapped key list equals the canonical closed graph's entire step list. |

Capability injectivity and exact collector fibers follow from the constructed
match and existing closure/fiber results. Matching selected actions, sums,
events and intermediate states are consequences of correspondence,
not interface assumptions.

## 4. Required acceptance example

Split the existing three-scalar validation into genuinely local components:

- **Producer:** no inputs; defined output `Pre`; two distinct contributions
  `1` and `-1`.
- **Consumer:** input `Pre`; defined output `Out = square(Pre)`; private
  defined `Audit`.

The audit body is `Pre + at(V, 0)`, where `V` is the strictly constructed
reciprocal array with arguments `[2, other]`. It is not reciprocal of `Pre`.
Selection still demands the whole array.

Compose their local matches and apply the existing correspondence theorem:

- With `other = 0`, preserve the six-event failure at `Audit` after `Out`
  was published; do not return the published output as successful completion.
- With `other = 4`, preserve seven-event completion, including `Audit = 1/2`.
- Retain the exact three-scalar program: four writer occurrences and three
  coordinate publications. No forwarding-copy events or duplicate boundary
  collector may appear.

These are required behaviours inherited from the existing validation.
Reobserve them through the newly constructed composite. The existing
whole-fixture `suppliedMatch` is a donor/comparison, not the construction's
premise or replacement.

Also require discriminating fixtures for private identity collisions, explicit
unequal-axis boundary adapters, empty tensor ports/input presence, zero-writer
collectors, multiplicity and ordered priorities. Use type-level impossibility
or explicit rejection tests as appropriate to the chosen interface; do not
invent a broad runtime checker just to manufacture diagnostics.

## 5. Targeted source map

Use `rg -n` to locate these identifiers, then read roughly 40-60-line windows.
Do not reread entire large files or survey unrelated backends.

| Identifiers | File |
| --- | --- |
| `Declarations`, `Address`, `PartialStore`, `AdmittedRead` | [Types.lean](../../leanncd/LeanNCD/Semantics/Types.lean) |
| `Program`, `Defined`, `Occurrence`, `output_defined` | [Program.lean](../../leanncd/LeanNCD/Semantics/Program.lean) |
| `Key`, `Schedule`, `validate` | [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean) |
| `Domain`, `Domain.policy_id`, `Domain.policy_comp`, `Embedding`, `address_injective`, `pull`, `pullComplete` | [IndexedComponentTransport.lean](../../leanncd/experiments/indexed_execution/IndexedComponentTransport.lean) |
| `transport`, `footprint_transport` | [IndexedComponentTransportExpr.lean](../../leanncd/experiments/indexed_execution/IndexedComponentTransportExpr.lean) |
| `evalWith_transport`, `evalReady_transport`, `interpret_transport`, `footprint_comp` | [IndexedComponentTransportEval.lean](../../leanncd/experiments/indexed_execution/IndexedComponentTransportEval.lean) |
| `SourceOccurrence`, `SourceContractMatch`, `keyStep` | [IndexedCompositionMatch.lean](../../leanncd/experiments/indexed_execution/IndexedCompositionMatch.lean) |
| `Contract`, `Writer`, `Fragment`, `definedAddresses`, `close`, `combine`, `runChecked` | [IndexedOpenComposition.lean](../../leanncd/experiments/indexed_execution/IndexedOpenComposition.lean) |
| `canonicalSteps`, `close_success_canonical`, `close_success_defined_covered`, `close_success_writer_destination_iff` | [IndexedCompositionClosure.lean](../../leanncd/experiments/indexed_execution/IndexedCompositionClosure.lean) |
| `SourceContractMatch.capability_injective`, `collectorFiber` | [IndexedCompositionFibers.lean](../../leanncd/experiments/indexed_execution/IndexedCompositionFibers.lean) |
| `default_run_correspondence` | [IndexedCompositionValidated.lean](../../leanncd/experiments/indexed_execution/IndexedCompositionValidated.lean) |
| `reference`, `refSchedule`, `contract`, `fragment`, `strictArray`, `auditBody` | [IndexedCompositionParityTest.lean](../../leanncd/experiments/indexed_execution/IndexedCompositionParityTest.lean) |
| `suppliedMatch`, `strict_execution`, `total_execution` | [IndexedCompositionFixtureProof.lean](../../leanncd/experiments/indexed_execution/IndexedCompositionFixtureProof.lean) |

Existing closure lemmas are evidence to reuse, not proof that concatenating
arbitrary contracts works. Audit their exact premises before designing
the closure-preservation task.

## 6. Next-session plan and execution discipline

1. Read repository instructions and invoke `slice-plan` and `new-slice`.
   Create an isolated linked worktree from latest local main. Set the session
   working directory correctly: preparation discovers its caller's checkout.
2. Run `prepare-worktree.sh`; check its cache verification. Refresh project
   oleans with `lake-build.sh <checkout>/leanncd LeanNCD` before single-file
   checks. Use the wrappers, never a root-level or hand-rolled Lake invocation.
   Omit `--plan` until its primary-checkout copy source actually exists.
3. Audit the supplied match/closure APIs and choose independently rejectable
   task boundaries: component scope/embeddings, source/occurrence/key
   assembly, closure/priority preservation, match construction, and fixtures.
   This is a dependency outline, not a pre-verified task list.
4. Prototype and verify in real module splits. A fresh authoring dispatch
   writes the plan from those artifacts. Ship mechanically generated
   per-task patches, observed fixture values, and observed mutation failures.
   Do not transcribe plausible Lean or invent expected diagnostics.
5. Put the live plan and separate authoring/execution records under
   `papers/semantics/`, with a `component_composition` prefix. Names and
   module splits are proposed deliverables, not files already present.
6. Include exact files/identifiers, donors plus changed fields, fixture/cycle
   counts, and a required/forbidden/silently-ignored audit. Order requirements
   need fixtures that distinguish the competing readings. Every Lean block
   must compile through `check-snippet.sh`.
7. Execute every validated task without permission pauses. Use task reviews
   as checkpoints. Stop for genuine blocked tasks or load-bearing plan defects.
8. Keep new modules discoverable through the nondefault
   `IndexedExecutionExperiment`; do not add production `LeanNCD` imports.
   Update its instruction/discovery entry and the design's status accurately.
9. The controller runs both unfiltered manifest validation and actual cycles,
   exact probe/patch checks, and the full
   `lake-build.sh <checkout>/leanncd LeanNCD Tests IndexedExecutionExperiment`.
   Preserve existing correspondence and transport regressions.
10. Complete two final whole-branch review lenses, soundness and integration/
    observations. Once the build is green and findings are fixed or adjudicated,
    merge to local main and remove only the task's own branch/worktree.
    Do not push without an explicit request.

Use the shell-harness preamble from `new-slice` in every agent brief.
Cap dispatches at approximately 60 turns and 250k retained context; target
roughly 40 turns and at most three work items. Split anticipated overruns
before dispatch. Authoring targets approximately 50M cumulative input tokens;
execution caps at 175M. Measure with `token-report.py` where available;
the previous SDK session had no supported transcript, so do not assert
measured compliance when accounting is unavailable.

## 7. Exclusions and close-out

Do not add rank stitching, a generic ranked phase/spliced-trace theorem,
complete-model restriction/gluing, categorical associativity/identities,
general adapter synthesis, residual inputs, fan-out, open contribution ports,
or a general category library. Do not change runners, language partiality,
the primitive registry or strict-array selection.

Do not widen this slice to repair the previous slice's parked per-fixture
mutation coverage or token-accounting tooling. The new construction needs
its own meaningful controls; label copied-computation, observer/donor and
live-source mutation evidence honestly.

Close-out must state the new constructor and its exact premises, account for
all nine match fields, record the split-fixture outcomes and internal work,
include actual controller gates/review adjudication, and leave later
rank/model/categorical obligations explicitly unproved.

# Next-session brief: complete-model restriction and gluing

## Launch instruction

Prepare and verify one implementation plan for complete-model restriction
and gluing over the existing static component composition, then execute it
through the repository's release gates. Preserve existing changes.
Do not rerun the completed transport or static-composition plans.

**Process weight: Full.** This adds a semantic theorem and soundness surface.
This handoff is not an execution-ready plan: no new Lean implementation,
compiled task patches or mutation manifests are supplied here.

The core result must be rank-independent. Derive the partial-function
corollary only under explicit uniqueness restrictions. Do not smuggle
execution completion, a phase theorem or model existence into the premises.

## 1. Starting state

Static composition has landed on local main: merge `67f49129`, with integration
recorded by `80fa754a`. These are provenance, not required implementation HEADs.
Start from latest local main and verify the actual APIs.

Read:

1. [Interface design](categorical_tensor_logic_component_interfaces.md),
   especially Section 6, "Complete models before output functions".
2. [Synthesis](categorical_tensor_logic_semantics.md), Sections 9.2-9.3.
3. [Static-composition record](component_composition_record.md) and its
   exact public premises.
4. The targeted source map below.

The main checkout is `/Users/williammacready/code/python/pyncd`.
Its existing contents/synthesis edits, including the updated synthesis
working copy, are protected. Do not replace them with an older checkout's
text or commit unrelated edits. Other worktrees are outside this task.

Use GPT Sol with high reasoning effort for difficult design decisions.
Keep delegated objectives bounded, with targeted source windows; do not
assign the entire model theorem and fixture suite to one unbounded dispatch.

## 2. Semantic target and notation

Let `A` and `B` be existing `MatchedComponent` values and `wire` their
explicit `Boundary`. Write $P$ for `A.program`, $Q$ for `B.program`, and
$C$ for the already constructed `program A B wire`.
Stay with finite decidable `Declarations Unit` and the constructor's fixed
`RationalReference.Carrier`, registry and operations. Do not generalize this
slice to arbitrary sorts or primitive registries.

A **complete-model witness** is a whole store satisfying `Program.Models`:
input agreement, definedness of every actual occurrence body, and every
defined coordinate's collected equation. It includes private tensors.
It is not an output assignment, a reached runtime state, or the identity
of an admissibility proof term.

Write $\mathcal M_P(\eta)$ for the set/subtype of whole stores that model
program $P$ on validated input $\eta$; use analogous notation for $Q,C$.
Treat different proofs of the same model store as the same witness.

Let $\eta_A$ be a validated upstream input. Construct its lifted composite
input $\eta_C$: retain upstream input bindings and leave every composite
noninput absent. Conversely restrict a validated composite input to the
upstream input. Prove validity and the corresponding round-trip laws.
Do not infer tensor presence from an address store: empty inputs still
require `some` of their empty value.

For an upstream whole store $\rho_A$, define $\eta_B(\rho_A)$, the downstream
input environment, by explicit boundary transport. For each downstream input
tensor $i$, let $b(i)$ be its matched upstream output and $e_i$ the certified
coordinate adapter supplied by `wire`. Its present input value is

```math
\eta_B(\rho_A)(i)[p]=\rho_A(b(i))[e_i(p)].
```

Every downstream input is present, even with an empty domain; noninput
bindings are absent. Never infer boundary identity from names or extents.

**Core theorem:** construct the bijection

```math
\mathcal M_C(\eta_C)
\cong
\left\{(\rho_A,\rho_B)\ \middle|\
 \rho_A\in\mathcal M_P(\eta_A),\
 \rho_B\in\mathcal M_Q(\eta_B(\rho_A))
\right\}.
```

Here $\cong$ means an explicit bijection of complete witnesses.
The downstream model family depends on the upstream witness; this is not
a product of two fixed, independently chosen model sets.

## 3. Required construction and proof obligations

### Whole stores and compatible pairs

Use the existing upstream/downstream address embeddings and
`Embedding.pullComplete` to restrict a composite store.

Define gluing over the existing disjoint-union declarations: use $\rho_A$
on the upstream summand and $\rho_B$ on downstream defined tensors.
Their common boundary is not duplicated. Downstream input agreement
establishes consistency there.

Prove:

- Restriction of a composite model gives an upstream model and a downstream
  model on exactly the transported upstream boundary.
- Gluing any such pair gives a complete composite model.
- Restriction and gluing are inverse on complete witnesses.
- The composite's output projection is the appropriately transported
  downstream output projection, retaining empty-output identity.

These are proofs about all complete candidate stores, including models of
blocked cyclic programs. Do not restrict to successful or reachable executions.

### Definedness and collected equations

Preserve and reflect `AdmEnv` for every actual guard-admitted occurrence,
not only writers reaching an exterior output.
Use `interpret_transport`, the existing body/destination equations, and
the defined/occurrence equivalences.

Preserve all collected equations through finite-sum reindexing:

- Distinct equal-valued contributions remain separate.
- Guard-excluded valuations do not become actual occurrences.
- Zero-writer fibers still constrain their coordinate to additive zero.
- All private defined tensors remain in the complete model.

Do not hide upstream internal witnesses existentially before checking
uniqueness. Store restriction alone is not a model-preservation proof.
Do not use final-output agreement as a substitute for the witness bijection.

### Partial-function corollary

An **at-most-one-model** hypothesis states that, on each validated input,
any two complete model stores are equal. It does not assert existence.

Under explicit at-most-one-model component hypotheses, derive the
admissibility-domain correspondence and successive input/output denotation
law using the existing `AdmInput`, `outputProjection` and `denotation`.
Both domain equality and values matter; a conditional equality only on
already successful runs is insufficient.

Existing ranked uniqueness results may discharge the component hypotheses
in a corollary. Do not add a composite rank certificate or phase proof to
establish the rank-independent witness theorem.

No unrestricted unique-model partial-function composition law is allowed:
downstream definedness can select one of several upstream models.

## 4. Discriminating acceptance cases

These are required proof/fixture goals, not newly observed results.
Name exact donors and deltas in the verified plan; observe executable values
where applicable and use explicit witnesses/contradictions for model predicates.

1. **Strict internal audit.** Reuse the local producer and consumer at
   `other = 0`. The producer has its complete `Pre = 0` model, but the
   consumer's private strict reciprocal array is undefined. Prove no
   compatible model pair and no composite model, despite the satisfiable
   `Out = 0` equation. Do not bypass nonselected reciprocal work.
2. **Total neighbour.** Change only `other` to `4`. Retain the whole
   `Pre = 0`, `Out = 0`, `Audit = 1/2` store, its component witnesses and
   gluing/restriction round trips. These values are not permission to omit
   the internal definedness proof.
3. **Zero-writer fiber.** Reuse `zeroProducerComponent`: the producer's
   unwritten scalar is constrained to zero, not an arbitrary boundary value.
4. **Empty tensors.** Reuse the empty producer/consumer interfaces. Lifted
   and transported empty inputs must be present; empty outputs keep their
   role/identity. Do not prove presence by vacuous coordinate agreement.
5. **Nontrivial coordinates.** Reuse the unequal-axis producer/consumer and
   `axisBoundary` with nonconstant values. A wrong coordinate transport must
   differ from the intended downstream input/model.
6. **Downstream model selection.** Build a logical model fixture with upstream
   $t=t^2$ and downstream reciprocal of input $t$. Preserve both upstream
   witnesses $t=0,1$; only $t=1$ extends. The composite may be uniquely
   modeled while the upstream unique-model partial function is undefined.
   This is not a claim that the executor solves the cycle or that ranks exist.
7. **Hidden internal multiplicity.** Build a producer with two internal models
   agreeing on its output boundary, and a total consumer on that boundary.
   The two composite stores must remain distinct internally even when their
   final outputs agree. This distinguishes whole-witness gluing from an
   output-only relation.

Do not replace the generic theorem by Boolean parity checks or fixture
certificates. Label proof-elaboration failures, concrete model-counterexample
checks and runtime observation kills accurately in mutation evidence.

## 5. Targeted source map

Locate identifiers with `rg -n`, then read roughly 40-60-line windows.
Avoid whole files over 20k characters and unrelated backend surveys.

| Identifiers | File |
| --- | --- |
| `InputBinding`, `ValidInput`, `Input`, `InputAgreement`, `Models`, `AdmInput`, `Output`, `outputProjection`, `denotation`, `denotation_of_model` | [Models.lean](../../leanncd/LeanNCD/Semantics/Models.lean) |
| `Defined`, `Occurrence`, `outcome`, `AdmEnv`, `contribution`, `collect`, `collect_relabel`, `admEnv_relabel` | [Program.lean](../../leanncd/LeanNCD/Semantics/Program.lean) |
| `pushforward`, `pushforward_relabel`, `pushforward_grouped` | [Collection.lean](../../leanncd/LeanNCD/Semantics/Collection.lean) |
| `MatchedComponent`, `Boundary`, `declarations`, `upstream`, `downstream` | [IndexedComponentCompositionScope.lean](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionScope.lean) |
| `program`, `upstreamDefined`, `downstreamDefined`, `definedEquiv`, `occurrenceEquiv`, `upstream_body`, `downstream_body`, `upstream_destination`, `downstream_destination` | [IndexedComponentCompositionProgram.lean](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionProgram.lean) |
| `downstream_defined_address` | [IndexedComponentCompositionMatch.lean](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionMatch.lean) |
| `compose_match`, `compose` | [IndexedComponentComposition.lean](../../leanncd/experiments/indexed_execution/IndexedComponentComposition.lean) |
| `Embedding.pullComplete`, address injection/composition, `Domain` | [IndexedComponentTransport.lean](../../leanncd/experiments/indexed_execution/IndexedComponentTransport.lean) |
| `interpret_transport`, `evalWith_transport` | [IndexedComponentTransportEval.lean](../../leanncd/experiments/indexed_execution/IndexedComponentTransportEval.lean) |
| `producerComponent`, `consumerComponent`, `scalarBoundary`, `zeroProducerComponent`, `emptyProducerComponent`, `emptyConsumerComponent` | [IndexedComponentCompositionPortFixtures.lean](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionPortFixtures.lean) |
| `axisProducer`, `axisConsumer`, `axisBoundary` | [IndexedComponentCompositionAxisFixtures.lean](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionAxisFixtures.lean) |
| `model_maximal_success`, `initialization_iff_singleton` (optional uniqueness corollary, not core theorem) | [Progress.lean](../../leanncd/LeanNCD/Semantics/Progress.lean) |

Existing relabeling lemmas do not automatically establish cross-program model
gluing; check their exact programs, stores, valuations and premises.
No new model-gluing API name in this brief denotes an existing declaration.

## 6. Plan authoring, execution and exclusions

Use `slice-plan` and `new-slice`. Prepare an isolated latest-local-main
worktree, verify its warm Mathlib cache, and refresh project-owned oleans.
Use `lake-build.sh`/`lean-file.sh`; never invoke Lake from the repository root.
The preparation helper discovers its caller's checkout; set session cwd
correctly and omit `--plan` until its primary-copy source actually exists.

Choose independently rejectable proof tasks from input/store transport,
admissibility/collection preservation, witness inverses, the restricted
denotation corollary, and discriminating fixtures. This is a dependency
outline, not a verified task list.

Prototype in real module splits, then use a fresh artifact-only authoring
dispatch for the plan. Ship mechanically generated compiled patches,
observed fixtures/controls, exact identifier/file lists and a
required/forbidden/silently-ignored audit. Compile every Lean block with
`check-snippet.sh`; do not invent expected mutation diagnostics.
Use a proposed `component_model_gluing` prefix under `papers/semantics/`
for the plan, separate records and artifacts.

Keep the new proof surface in the nondefault `IndexedExecutionExperiment`,
with explicit import/discovery documentation. Preserve the existing source
constructor, registry, runners, strict partiality and numerical operations.
Do not add a general span/category library or alternate model semantics.

Execute every verified task with checkpoints and task reviews. The controller
must run actual unfiltered manifests, patch/probe checks, namespace audits
and `lake-build.sh <checkout>/leanncd LeanNCD Tests IndexedExecutionExperiment`.
Use two final whole-branch review lenses: model-theorem soundness and
integration/fixtures/claim fidelity. After green gates and adjudicated
findings, merge to local main and remove only the task's branch/worktree.
Do not push without an explicit request.

Use the `new-slice` shell-harness preamble in every agent brief.
Target approximately 40 turns and at most three work items per dispatch;
split anticipated work before exceeding approximately 60 turns/250k context.
Authoring targets approximately 50M cumulative input tokens; execution caps
at 175M. Measure when the session transcript is supported and report missing
accounting rather than asserting unmeasured compliance.

**Excluded:** rank stitching, runtime phase/projection or spliced-trace
theorems, categorical associativity/identities, wider interfaces, automatic
leaf matching, general source parsing, previous-slice coverage repairs and
token-accounting tooling. Blocked cycles may have models; neither blocking
nor structural sealing proves model absence or operational completion.

Close-out must distinguish the rank-independent witness bijection from the
restricted denotation corollary, report exact premises and preserved private
work, and keep operational/categorical obligations explicitly open.

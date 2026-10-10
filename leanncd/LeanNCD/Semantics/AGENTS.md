# LeanNCD/Semantics

## Purpose

Expression/readiness and finite collection/model semantic validation,
separate from the production DSL evaluator and execution backends.

## Current artifact

`ExecutableState`, `ExecutableSelection`, and `ReferenceExecutor` realize the
same reference `Step` edges computationally, with function-valued typed stores.
Provide computational tensor equality and a complete, duplicate-free ordered
`Executor.Schedule` (tensors and tagged occurrence/publication keys).
`Schedule.reverse` is a debug presentation; selection restarts at the beginning
after each edge. `runValidated` checks tensor-level input presence before
initialization, including empty inputs, and returns the first offending tensor.
`runFuel` is an arbitrary-state debug API: exhausted is not success or failure.
`run` uses a proved initial bound; supplied address ranks rule out reachable
blocking, but not ready undefinedness. Outcomes retain endpoints, legal typed
event traces, and unavailable-read diagnostics. Model/uniqueness/denotation
theorems concern the whole store, not only outputs. `RationalReference` offers
exact rational scalar operations and the closed reciprocal/square registry.
The source layer below adds bounded read-only elaboration; rank synthesis and
native floats in the semantic core are not provided.

The semantic validation layer `LeanNCD.Semantics` is reachable from `LeanNCD`.
`Types`, `Expr`, `Interpret`, `Readiness`, and `Completeness` separate typed
values/declarations/registries, structurally admitted expressions, strict
interpretation/footprints, structural stability/readiness, and whole-array
completeness. Default `Tests` includes `Semantics.ExpressionTest`,
`Semantics.NativeTest`, `Semantics.ContractTest`, `Semantics.CollectionModelTest`,
`Semantics.ReferenceMachineTest`, `Semantics.RankedMachineTest`, and
`Semantics.ExecutableReferenceTest`.

`Source.Context` supplies UID-keyed dependent valuations, coordinate
equivalences, full-domain index pullbacks, and generated-only alpha transport.
Requested generated identities are honored when fresh and injective; a collision
or duplicate target freshens the whole generated group, leaving protected
identities fixed. `Semantics.SourceBindingTest` checks the binding contract in
the default build.
`Source.Adapter` / `Source.Admission` admit resolved snapshots and raw parsed
programs through the existing resolver, preserving original declaration and
statement identities. The finite bare-slot fragment accepts pinned nat/real
axes and real tensor/linear declarations, with explicit roles, all input
bindings (including unused/empty tensors), exact domains and shape/lengths,
and term-local contraction support. `Semantics.SourceAdmissionTest` includes
the original admission fixtures and the parsed/real/linear acceptance
regressions. `Source.Statement` / `Source.Program` lower admitted statements into
term-local typed expressions and role-based multi-target Programs.
`Source.Schedule` enumerates every occurrence and full defined publication
domain, and runs the existing validated rational executor with optional debug
fuel. `Source.Provenance` certifies original-ID inverses from successful
admission; `Source.Permutation` preserves tagged collection and whole-store
models, not event order. `StatementPermutation.successful_results` also equates
whole stores of completed rational executions under a statement permutation
when their inputs agree; it does not assert completion or equal traces.
`Source.Oracle` provides an independent exact
global-fiber evaluator with explicitly checked fixture dependency order.
`Semantics.SourceProgramTest` checks actual executor/oracle parity and endpoint
contracts. `Source.Fiber`, `Source.Correspondence`, and
`Source.ProgramCorrespondence` prove actual normalized-body and Program
collection agreement with independently specified original-read global fibers.
Their relevant UID domains exclude unused axes, preserve term-local contractions
and repeated destinations, and connect reached rational execution to whole-store
global equations. `interpret_contract_reindex` in `Source.Lowering` preserves actual
nested reduction interpretations under coordinate reindexing with transported
read environments, without changing factor order or claiming float parity.
`Semantics.SourceCorrespondenceTest` specializes the generic proofs to Nat and
Rat, including reversed reduction bounds and empty/zero domains.
`Source.RawCorrespondence` proves actual successful raw admission preserves
original declarations and indexed statements/terms/factors/slots through the
name-keyed resolver memo, including metadata, order and multiplicity.
`Source.RawSemanticConnection` supplies certified raw-coordinate read/output
witnesses and existing body/footprint/fiber/Program applicability.
`admitRawSource_fields` / `admitRawSource_certified` require actual admission success;
`admitRawSource_reached` requires an actual complete validated rational outcome.
Equations and uniqueness are relative to `result.input`; denotation is output-restricted.
No independent raw denotation, parser correctness, global mint injectivity,
input-buffer certification or unconditional completion is claimed.
`Semantics.SourceRawCorrespondenceTest` covers ten structural/semantic families,
including parsed and asymmetric sourceInput donors, in default `Tests`.
`Source.Observation` / `Source.Diagnostics` expose actual
source-linked endpoints and canonical contribution data. `Source.NumericalProfile`
checks the exact bounded-integer binary64 comparison profile;
`Source.NativeLegs` preserves actual legacy/checked phase causes and warnings.
`Source.compareSource` / `Source.renderSourceComparison` compose and render the
four differential legs with explicit refusals and evidence-limited localization.
`Semantics.SourceDiagnosticTest` pins payloads, ordering, and protocol cases.
The differential fixtures (including the generated corpus), implementation
mutation controls, and both final whole-branch reviews have landed. Nothing in
`Oracle`, `Observation`, `Diagnostics`, `NativeLegs`, `NumericalProfile`, or
`Differential` is a theorem: the oracle is tested against, not proved equal to,
`globalFiber`, and bit parity holds only on the bounded-integer, f64-declared,
single-definition profile. Same-LHS multi-statement programs are a known
production contract difference and are never compared natively. See the
[source correspondence record](../../../papers/semantics/source_correspondence_record.md)
for scope and limits.

`Collection` represents Naperian coordinate families as functions. Pullback
is contravariant lookup; finite additive pushforward is covariant collection.
Identity, composition, zero/add preservation, occurrence relabeling, and
sigma-family grouping are generic theorems, not full Cat/Functor/Kan machinery.
`Program` uses that pushforward for finite typed statement/valuation tags,
guard-admitted domains, and already bounded destinations on defined tensors.
`Models` tracks complete input tensor presence (including empty tensors), all
defined equations, partial equation-operator fixed points, and nonconstructive
unique-model output projection. Only defined carriers need `AddCommMonoid`;
nonlinear body primitives do not acquire sum-preservation laws.

`Semantics.AxiomAudit` (a test) fails the build if anything under `LeanNCD.Semantics` reaches an
axiom outside `propext`, `Classical.choice`, `Quot.sound`: no `sorry`, `native_decide`, or new
`axiom` here. New modules must be imported by `LeanNCD/Semantics.lean` to be audited.

This is semantic validation, not an execution-backend replacement. Scalar sorts and
carriers are open; operations are data, not assumed machine-float semiring laws.
Contexts are typed valuation spaces with product extension, not named affine
syntax. Read admission and the bounded raw-AST correspondence are explicit;
general source checking beyond the finite read-only fragment, syntactic
substitution (only reduction-binder reindexing is proved), raw writes,
and full categorical/backend interpretation remain deferred.
See the [implementation plan](../../../papers/semantics/expression_readiness_plan.md)
and [authoring verification](../../../papers/semantics/expression_readiness_authoring_record.md)
for clause coverage, observed fixtures, and validation.

`interpret` evaluates complete environments; `evalReady` distinguishes
unavailable reads from ready undefinedness. `evalWith` is a low-level partial
computation whose `none` result alone does not distinguish those cases.
Use the readiness entry, not that helper, to classify execution eligibility.

`Machine` gives a relation-only reference machine with immutable published values,
retained accumulators, and finite tagged pending occurrences. `Invariants` uses
existential proof-only consumed-value history for conservation. `Soundness` proves
that reached success is a complete model, unique among all models, and projects to
the existing denotation; a reachable ready failure excludes every model. No rank
or supplied model witness is needed for successful soundness. Dependency blocking
is not failure: cyclic solving is not supplied.

`Ranks` derives coordinate dependencies directly from each guard-admitted occurrence's
existing strict footprint; input addresses have empty dependencies. Certificates
rank addresses, not tensor identifiers. `Measure` counts pending tags and unpublished
defined addresses (including nonoutputs), proves exact one-step running decreases,
finite trace bounds, and well-founded termination independently of ranks. An undefined
step is terminal and may add one transition beyond the initial running measure.
`Progress` uses ranks and reachable invariants, with no model premise, to exclude
blocking. Maximal finite runs reach terminal endpoints, not arbitrary stopped prefixes.
Every reachable prefix has a terminal extension; ranked maximal runs succeed or
explicitly fail, and initialization reaches a complete store exactly when Models is
its singleton. Existing soundness supplies model uniqueness and denotation.
These modules remain relations and proofs; the executor above refines their
edges computationally. No runtime rank checker is provided.

[`TensorLogicSemanticCoreSpike.lean`](TensorLogicSemanticCoreSpike.lean) proves
read stability and partial-store consistency for a carrier-parametric scalar
fragment, with a restricted bridge to an existing formal `StMat`.
Its existing namespace `LeanNCD.TensorLogicSemanticCoreSpike` is preserved.
The module path is `LeanNCD.Semantics.TensorLogicSemanticCoreSpike`.

The prior spike is not imported by `LeanNCD`, but `Semantics.ContractTest`
imports it for the existing formal-index witness, so the default `Tests`
target now checks it indirectly. The explicit `SemanticCoreSpike` target
remains available for standalone checks.

## Scope

Read the [plan](../../../papers/semantics/tensor_logic_semantic_core_spike_plan.md)
and [results](../../../papers/semantics/tensor_logic_semantic_core_spike_record.md)
before extending that spike. The validation layer covers the admitted
array/heterogeneous expression fragment, finite additive program models,
reference-machine soundness, and bounded read-only pure-einsum correspondence.
General source-expression elaboration, cyclic solving, general unique-model
existence, and complete categorical/backend interpretations remain outside it.

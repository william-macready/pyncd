# LeanNCD/Semantics

## Purpose

Expression/readiness and finite collection/model semantic validation,
separate from the production DSL evaluator and execution backends.

## Current artifact

The semantic validation layer `LeanNCD.Semantics` is reachable from `LeanNCD`.
`Types`, `Expr`, `Interpret`, `Readiness`, and `Completeness` separate typed
values/declarations/registries, structurally admitted expressions, strict
interpretation/footprints, structural stability/readiness, and whole-array
completeness. Default `Tests` includes `Semantics.ExpressionTest`,
`Semantics.NativeTest`, `Semantics.ContractTest`, `Semantics.CollectionModelTest`,
`Semantics.ReferenceMachineTest`, and `Semantics.RankedMachineTest`.

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

This is semantic validation, not an execution-backend replacement. Scalar sorts and
carriers are open; operations are data, not assumed machine-float semiring laws.
Contexts are typed valuation spaces with product extension, not named affine
syntax. Read admission is explicit; runtime boundary rejection ordering,
source checking, syntactic substitution, expression reindexing laws, raw writes, scheduling,
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
These are noncomputable relations and proofs, not an executable scheduler or rank checker.

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
array/heterogeneous expression fragment, finite additive program models, and
reference-machine soundness, but not pure-einsum elaboration correctness, cyclic
solving, general unique-model existence, or complete categorical/backend interpretations.

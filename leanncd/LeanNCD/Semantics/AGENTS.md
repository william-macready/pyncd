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
`Semantics.NativeTest`, `Semantics.ContractTest`, and `Semantics.CollectionModelTest`.

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
publication, and full categorical/backend interpretation remain deferred.
See the [implementation plan](../../../papers/semantics/expression_readiness_plan.md)
and [authoring verification](../../../papers/semantics/expression_readiness_authoring_record.md)
for clause coverage, observed fixtures, and validation.

`interpret` evaluates complete environments; `evalReady` distinguishes
unavailable reads from ready undefinedness. `evalWith` is a low-level partial
computation whose `none` result alone does not distinguish those cases.
Use the readiness entry, not that helper, to classify execution eligibility.

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
array/heterogeneous expression fragment and finite additive program models,
but not pure-einsum elaboration correctness, publication, cyclic solving,
general unique-model existence, or complete categorical/backend interpretations.

# LeanNCD/Semantics

## Purpose

Expression/readiness semantic validation, separate from the production
DSL evaluator, execution backends, and categorical interpretation.

## Current artifact

The semantic validation layer `LeanNCD.Semantics` is reachable from `LeanNCD`.
`Types`, `Expr`, `Interpret`, `Readiness`, and `Completeness` separate typed
values/declarations/registries, structurally admitted expressions, strict
interpretation/footprints, structural stability/readiness, and whole-array
completeness. Default `Tests` includes `Semantics.ExpressionTest`,
`Semantics.NativeTest`, and `Semantics.ContractTest`.

This is semantic validation, not an execution-backend replacement. Scalar sorts and
carriers are open; operations are data, not assumed machine-float semiring laws.
Contexts are typed valuation spaces with product extension, not named affine
syntax. Read admission is explicit; runtime boundary rejection ordering,
source checking, syntactic substitution, reindexing laws, writes, scheduling,
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
array/heterogeneous expression fragment, but not additive program models,
publication, or complete categorical/backend interpretations.

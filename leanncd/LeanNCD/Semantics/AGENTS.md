# LeanNCD/Semantics

## Purpose

Exploratory semantic definitions and proofs, separate from production
evaluation and categorical interpretation.

## Current artifact

[`TensorLogicSemanticCoreSpike.lean`](TensorLogicSemanticCoreSpike.lean) proves
read stability and partial-store consistency for a carrier-parametric scalar
fragment, with a restricted bridge to an existing formal `StMat`.
Its existing namespace `LeanNCD.TensorLogicSemanticCoreSpike` is preserved.
The module path is `LeanNCD.Semantics.TensorLogicSemanticCoreSpike`.

The prototype is not imported by `LeanNCD`. Check it explicitly with the
repository build wrapper and target `SemanticCoreSpike`; a default build
does not cover it.

## Scope

Read the [plan](../../../papers/semantics/tensor_logic_semantic_core_spike_plan.md)
and [results](../../../papers/semantics/tensor_logic_semantic_core_spike_record.md)
before extending it. The full array grammar, heterogeneous dtypes, additive
program models, publication machine, and complete categorical/backend
interpretations remain unimplemented here.

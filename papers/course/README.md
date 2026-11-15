# Categorical semantics for agentic coding: Tensor Logic from meaning to Lean

Course notes. One running example, Tensor Logic, is given a denotational
semantics (what equations a program defines), an operational semantics (how
a reference machine computes them), and a Lean realization of both. Each
chapter introduces a categorical structure only where the example needs it.

## Who this is for

Students who know categories, functors and natural transformations, and who
want to see adjunctions, Kan extensions, monads, coalgebras and spans do
real work in a semantics that is then handed to a coding agent and to a
proof assistant.

## Thesis

A semantics expressed categorically tells a coding agent which structures
are distinct, which laws must hold, and where a tempting shortcut is a
semantic error. For Tensor Logic the slogan is:

> coordinate maps route (a functor out of $\mathbf{FinSet}$), partial maps
> interpret (the Kleisli category of Option), additive pushforward collects
> (the covariant functor), an equalizer selects models, a well-founded
> coalgebra computes them, and a span composes them.

## Reading order

| Chapter | File | Categorical tool | Semantic question answered |
| --- | --- | --- | --- |
| 0 | [The categorical toolkit](00-prerequisites.md) | adjunctions, Kan extensions, Kleisli, (co)algebras, spans, equalizers | none; vocabulary |
| 1 | [Tensor Logic and the running example](01-tensor-logic.md) | none | what the language says |
| 2 | [Categories of indices and values](02-index-categories.md) | $\mathbf{FinSet}$, $\Sigma_f\dashv f^\ast\dashv\Pi_f$, pullback/pushforward, Naperian adjunction, $\mathbf{Span}(\mathbf{FinSet})$ | where values live; what index expressions do; einsum |
| 3 | [Partial computations](03-partiality.md) | $\mathbf{Pfn}=\mathrm{Kl}(\mathrm{Option})$, strict pairing, `sequence`, lax naturality | what a body means when a primitive is undefined |
| 4 | [Denotational semantics](04-denotational.md) | equalizer, span | how contributions combine; what a program means |
| 5 | [Operational semantics](05-operational.md) | coalgebra, subcoalgebra invariants, well-foundedness, lax morphism | how it is computed; when computation agrees with meaning |
| 6 | [From categories to Lean](06-lean.md) | the dictionary | how the structures become code |
| 7 | [Refinement and open problems](07-outlook.md) | simulation | when a compiled program is correct |

The companion Lean file is [`lean/MiniTensorLogic.lean`](lean/MiniTensorLogic.lean).
Compile it from the `leanncd` directory with
`lake env lean ../papers/course/lean/MiniTensorLogic.lean`.

Assessment material (question sets, answer keys, and the recorded results of
agent "students" who saw only these notes) is under [`assessment/`](assessment/).

## Sources

The semantic authority is the Tensor Logic specification in
[`../semantics/`](../semantics/README.md). The categorical presentation
adapts the [categorical proposal](../semantics/categorical_tensor_logic_semantics.md);
the adjustments are listed in Chapter 7. The production Lean modules are
under [`../../leanncd/LeanNCD/Semantics/`](../../leanncd/LeanNCD/Semantics/).
Instructor material: [DESIGN.md](DESIGN.md), [CONVENTIONS.md](CONVENTIONS.md).

## Rendering

Math uses `$...$` and `$$` blocks; preview in VS Code with
`markdown.math.enabled` or any KaTeX-capable renderer.

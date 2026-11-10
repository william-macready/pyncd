# Tensor Logic semantics and the Lean executable reference

These documents describe Tensor Logic's mathematical meaning and its Lean
formalization. They are split into independently readable parts to keep
GitHub's browser-based mathematical rendering manageable.

## Reading order

Start with the [specification introduction](tensor_logic_semantics.md), then
read Parts I and II for notation and syntax. Part III defines program meaning;
Parts IV and V explain reference execution and compilation. The notation
reference and bibliography are collected in a separate final file.

Read the [Lean guide introduction](lean_executable_semantics_path.md) alongside
the specification to see which definitions and proofs have landed and what
work remains. Its six parts retain the original top-level section numbering.

The specification remains the semantic authority; the Lean guide records
implementation correspondence and status. The split preserves their prose,
mathematical notation, examples, and numbered results. Each part has previous,
contents, and next links at both the top and bottom.

## GitHub math rendering

The specification and Lean-guide series use fenced `math` blocks so Markdown
does not interpret standalone equality signs as heading underlines.
The [categorical synthesis](categorical_tensor_logic_semantics.md) instead
uses `$$` display blocks consistently for VS Code preview compatibility.
Interpretation brackets use
standard TeX square brackets with tight spacing instead of package-specific
bracket commands. Both opening and closing interpretation brackets are teal;
enclosed expressions and subscripts keep their own role-specific colors.
These choices change only the typesetting, not the mathematical meaning.

## Table of contents

## Tensor Logic semantics

[Series introduction and detailed contents](tensor_logic_semantics.md).

| Part |
| --- |
| [Part I: Background notation](tensor_logic_semantics_part_i.md) |
| [Part II: Core language and surface elaboration](tensor_logic_semantics_part_ii.md) |
| [Part III: Denotational semantics](tensor_logic_semantics_part_iii.md) |
| [Part IV: Operational semantics](tensor_logic_semantics_part_iv.md) |
| [Part V: Compilation and refinement](tensor_logic_semantics_part_v.md) |
| [Notation reference and bibliography](tensor_logic_semantics_reference.md) |

## Lean executable reference

[Series introduction and detailed contents](lean_executable_semantics_path.md).

| Part |
| --- |
| [1. Purpose, authority, and current position](lean_executable_semantics_path_part_1.md) |
| [2. One notation, two presentations](lean_executable_semantics_path_part_2.md) |
| [3. The category-theoretic organization](lean_executable_semantics_path_part_3.md) |
| [4. What is implemented and proved](lean_executable_semantics_path_part_4.md) |
| [5. Remaining work, in dependency order](lean_executable_semantics_path_part_5.md) |
| [6. The landed admitted-core milestone](lean_executable_semantics_path_part_6.md) |

## Worked examples

For complete programs and numerical execution traces, see
[Tensor Logic semantics: worked examples](tensor_logic_semantics_examples.md).

## Background reading

[Categorical operational semantics: syntax and behaviour](categorical_operational_semantics.md)
is a separate introductory document for readers familiar with categories,
functors, and natural transformations. It begins with the motivation and
benefits of the categorical approach, followed by an appendix on algebras
and coalgebras, with examples and notation defined as it is introduced.

[Tensor Logic through the categorical lens: a refined assessment](categorical_tensor_logic_assessment.md)
relates the existing specification and reference machine to that framework.
It distinguishes the categorical structure already documented from proposed
work on constructor compatibility, shared-writer interfaces, and refinement.

[Effect-sensitive indexed Tensor Logic: prototype and results](categorical_tensor_logic_lean_prototype.md)
describes the executable Lean experiment, its graph/reference comparisons
and mutation controls, what the results establish, and the remaining limits.
Execution modules are proof-free; a separate experimental proof layer now
establishes conditional correspondence with the reference executor, with
actual matches for both independently authored validation cases.

[Categorical Tensor Logic semantics: a prototype-grounded proposal](categorical_tensor_logic_semantics.md)
brings together St/Br and Naperian arrays, partial maps, additive collection,
open diagrams, model witnesses, causal iteration, and Turi-Plotkin-style
compatibility. It separates mathematical laws from prototype evidence
and the proved conditional execution theorem, while retaining general
composition as a further target. A mathematical appendix explains the
proof without assuming one formalism is the best foundation.

[Ranked operational interpretation and units: new-session brief](categorical_ranked_operational_interpretation_handoff.md)
sets the next goal: interpret the existing administrative identity/wire syntax
in full histories, retain private frames and metadata, and justify the ranked
source equations before categorical packaging. It requires a verified plan
and prototype before implementation; it is not itself an execution plan.

[Source-contract execution correspondence: theorem-design brief](categorical_tensor_logic_theorem_brief.md)
fixes the first semantic theorem's scope, supplied match, state relation,
proof dependencies, and output-metadata boundary. It distinguishes existing
reference results from the original proof obligations. The
[proof record](categorical_tensor_logic_proof_record.md) documents the implemented
conditional theorem, retained assumptions, actual instances and validation.

[New-session proof execution brief](categorical_tensor_logic_proof_handoff.md)
is the handoff for implementing that scoped correspondence theorem,
including code entry points, proof obligations, validation and exclusions.

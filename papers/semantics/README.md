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

Display equations use fenced `math` blocks so Markdown does not interpret
standalone equality signs as heading underlines. Interpretation brackets use
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

# Bool Semiring Extension — To-Do

Picking up from the bool semiring implementation session. All changes are
in commit `c6d11f7` ("bool semiring theory + implmentation"). 257 existing
tests pass; 24 new tests in `tests/test_torch_compile.py` also pass.

The full design record is in `docs/bool_semiring_extension.md`.

---

## What is done

- `data_structure/TensorExpr.py` — new file: `TensorRef`, Iverson expression
  tree (`IversonConst`, `IversonBinOp`, `IversonUnaryOp`), `_factor_axes`,
  `_serialize_iverson`, helpers `ieq`/`imul`/`iabs`, `RawAxis` operator patches
- `data_structure/BroadcastedCategory.py` — `Bool(Datatype)` added
- `data_structure/AxisAnnotations.py` — `PredAxis` deleted
- `data_structure/TensorLogic.py` — `rhs` typed as `Prod[RHSFactor]`;
  `bc_signature` and `to_morphism` accept `array_datatypes`
- `data_structure/TensorDSL.py` — `__setitem__` produces `TensorRef`;
  `_array_datatypes()` maps predicate names to `Bool()`; Iverson factors
  accepted in `RHSExpression`
- `acset/instances.py` — `DataTag.BOOL`; `ArrayRow.iverson_expr: str | None`
- `acset/convert.py` — `_dt_fields` handles `Bool`; `_add_equation` dispatches
  `TensorRef` vs Iverson
- `acset/csv_io.py` — `iverson_expr` column added to arrays CSV read/write
- `torch_compile/torch_compile.py` — `generate_tensor_equation_signature`;
  `ConstructedTensorEquation` (registered for `TensorEquation` operator,
  applies `H(x) = (x > 0)` when `output_weave.datatype == Bool()`)
- `tests/test_torch_compile.py` — 24 tests: signature generation, dispatch,
  Reals forward, Bool/Heaviside forward, pre-materialised Iverson interface
- `construction_helpers/composition.py` — `align_axes` now raises `TypeError`
  on datatype mismatch (`Bool→Reals`, `Natural→Reals`, etc.)
- `tests/test_composition.py` — 8 tests covering matching and mismatching cases
- `data_structure/BroadcastedCategory.py` — `iverson_expr: str | None` added to
  `Weave` and `Array`; forwarded in `target()` and `imprint_to_degree()`
- `data_structure/TensorLogic.py` — `bc_signature()` populates `iverson_expr`
  on Iverson input weaves via `_serialize_iverson`
- `tsncd/src/data_structure/BroadcastedCategory.ts` — `Bool` class added;
  `iverson_expr` added to `Weave` and `Array`; forwarded in `imprint_to_degree()`
  and `target()`
- `tsncd/src/data_structure/Category.ts` — `Bool` added to re-export list
- `tsncd/src/display/Framework/CategoryRenderer.ts` — `curve_attributes` made
  `public`
- `tsncd/src/display/Framework/BroadcastedCategoryRenderer.ts` — `DatatypeAnchor`
  gains `extra_curve_attributes` param; `ArrayMeridian` applies amber dotted
  styling to Bool axis wires, renders `𝔹` anchor with amber stroke, and uses
  `iverson_expr` as wire annotation in place of axis names
- `docs/bool_semiring_extension.md` — design section fully updated; all four
  challenges marked resolved or accounted for
- `tsncd/src/data_structure/TensorLogic.ts` — new file: `TensorRef`,
  `IversonConst`, `IversonBinOp`, `IversonUnaryOp` stubs (for deserialization),
  `TensorEquation` (mirrors Python, field order matches for positional `to_term`)
- `tsncd/src/display/Framework/Operations/additionalOperationBoxes.ts` —
  `TensorEquationBox` registered for `TensorEquation`; renders `∃` for
  Bool-output, `Σ` for Reals-output
- `torch_compile/materialise.py` — **new file**: `materialise_iverson` evaluates
  an `IversonExpr` tree to a float `{0,1}` tensor; `_eval` traverses the AST in
  left-before-right DFS order (matching `_iverson_axes`), consuming one
  positional grid tensor per `RawAxis` leaf via an iterator
- `torch_compile/torch_compile.py` — `ConstructedTensorEquation` updated:
  `__init__` populates `_factor_slots` and `_caller_positions`; Iverson factors
  with all-sized axes are auto-materialised via `materialise_iverson` and stored
  as named buffers (`_mask_{i}`); unsized axes emit `UserWarning` and fall
  through to caller-provided path; `forward` uses a counter over `_factor_slots`
  instead of `iter(xs)` for `torch.compile` transparency
- `tests/test_torch_compile.py` — 9 new tests: `test_materialise_upper_triangular`,
  `test_materialise_diagonal`, `test_materialise_banded`,
  `test_materialise_compound`, `test_materialise_free_axis_raises`,
  `test_auto_materialise_shape`, `test_auto_materialise_values`,
  `test_auto_materialise_buffer_registered`, `test_auto_materialise_bool_output`;
  298 total tests pass
- `papers/pytorch_compilation.md` — Section 4.1 updated with `_factor_slots`
  machinery and sized/unsized examples; Section 8 corrected (AST not discarded;
  new Iverson materialisation subsection added); Section 9 worked example updated
  to use inline `(i <= j)` predicate with sized axes and buffer-based FX graph

---

## Remaining tasks

### 1. Embedding DSL

`ops.Embedding.template()` is unchanged. The Iverson-based embedding derivation
(embedding as a masked contraction over a `Natural`-typed axis) is theoretically
grounded but not yet exposed in the DSL.

---

## Key files for context

| File | Role |
|---|---|
| `data_structure/TensorExpr.py` | Iverson tree types, `TensorRef`, `_serialize_iverson` |
| `data_structure/TensorDSL.py` | DSL entry point; `TL`, `TensorProxy`, `_array_datatypes` |
| `data_structure/TensorLogic.py` | `TensorEquation.bc_signature`, `TensorProgram.to_morphism` |
| `torch_compile/materialise.py` | `materialise_iverson`, `_eval` |
| `torch_compile/torch_compile.py` | `ConstructedTensorEquation`, `generate_tensor_equation_signature` |
| `tests/test_torch_compile.py` | Compilation, Heaviside, and materialisation tests (all pass) |
| `tsncd/src/data_structure/TensorLogic.ts` | TypeScript stubs + `TensorEquation` operator |
| `tsncd/src/display/Framework/Operations/additionalOperationBoxes.ts` | `TensorEquationBox` |
| `docs/bool_semiring_extension.md` | Full design record |

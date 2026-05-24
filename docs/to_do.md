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

---

## Remaining tasks

### 1. Iverson materialisation in `torch_compile` (highest priority)

`ConstructedTensorEquation.forward(*xs)` already accepts one tensor per RHS
factor. The missing step is generating the Bool input tensor automatically from
an `IversonExpr` tree, so callers don't have to pre-build it.

#### Design

The same axis can appear at multiple leaves of the expression tree (e.g.
`(q < x) & (x < k)` has `x` at two leaves). `_factor_axes` returns axes in
DFS order including duplicates: `(q, x, x, k)`. The weave built by
`bc_signature` preserves these slots, so `generate_tensor_equation_signature`
emits `x0 x0` for the two `x` slots. `einops.einsum` interprets `x0 x0` in
one tensor as a diagonal trace, contracting only `T[..., x, x, ...]` over `x`.

For the trace to give the correct predicate value, each occurrence of `x` must
be an **independent positional dimension**. That is, the materialised tensor
for `axes = (q, x, x, k)` has shape `(size_q, size_x, size_x, size_k)`, and
`T[q, x1, x2, k] = [(q < x1) & (x2 < k)]`. The diagonal `x1 = x2 = x` is
then `[(q < x) & (x < k)]`, and the einops trace contracts it correctly.

No changes to `_factor_axes` or `_iverson_axes` are needed.

#### `materialise_iverson(factor, axes) -> torch.Tensor`

File: `torch_compile/torch_compile.py`

`axes` is `_factor_axes(factor)` — DFS-ordered axis slots, possibly with
duplicate UIDs. The function:

1. Validates every `ax._size` is `nm.Integer`; raises `ValueError` for free
   axes (caller must pre-materialise).
2. Builds `n = len(axes)` positional coord tensors: `grids[i]` has shape
   `(1, ..., size_i, ..., 1)` with `size_i` at dimension `i` only.
3. Creates `grid_iter = iter(grids)`.
4. Evaluates the expression tree with a nested `_eval(expr)` that dispatches
   on node type:

   | Node | Result |
   | --- | --- |
   | `RawAxis` | `next(grid_iter)` — consumes next positional coord |
   | `IversonConst(Integer(v))` | `torch.tensor(float(v))` (0-D scalar) |
   | `IversonBinOp('<'/'<='/'>'/>='/'==')` | `(eval(l) op eval(r)).float()` |
   | `IversonBinOp('+'/'-'/'*')` | `eval(l) op eval(r)` |
   | `IversonBinOp` (logical `&` / `or`) | `(eval(l).bool() op eval(r).bool()).float()` |
   | `IversonUnaryOp('abs')` | `eval(operand).abs()` |
   | `IversonUnaryOp('-')` | `-eval(operand)` |
   | `IversonUnaryOp('not')` | `(~eval(operand).bool()).float()` |

   `_eval` traverses left-before-right (same DFS order as `_factor_axes`), so
   the i-th `RawAxis` leaf consumes `grids[i]`. PyTorch broadcasting expands
   the positional tensors to the full shape automatically when they are
   combined.

**Worked example — `(q < x) & (x < k)`, `axes = (q, x, x, k)`, sizes 3, 4, 4, 5:**

- `grids = [(3,1,1,1), (1,4,1,1), (1,1,4,1), (1,1,1,5)]`
- `q < x` → `grids[0] < grids[1]` → shape `(3,4,1,1)`
- `x < k` → `grids[2] < grids[3]` → shape `(1,1,4,5)`
- `&` → broadcasts to shape `(3,4,4,5)`; `T[q,x1,x2,k] = [(q<x1) & (x2<k)]`
- einops `y0 x0 x0 y1` traces over diagonal → `∑_x [(q<x) & (x<k)]` ✓

#### Changes to `ConstructedTensorEquation`

`__init__`: iterate `target.operator.rhs`. For each factor at position `i`:

- `TensorRef` → append `None` to `self._factor_slots`
- Iverson with all `nm.Integer` axes → call `materialise_iverson`, call
  `self.register_buffer(f'_mask_{i}', tensor)`, append `f'_mask_{i}'`
- Iverson with any free axis → append `None` (caller must pre-provide)

`forward`:

```python
xs_iter = iter(xs)
full_tensors = [
    getattr(self, slot) if slot is not None else next(xs_iter)
    for slot in self._factor_slots
]
result = einops.einsum(*full_tensors, self.signature)
if self.demote:
    return (result > 0).to(result.dtype)
return result
```

Backward-compatible: free-axis equations (all existing tests) have all
`_factor_slots = None`, so `forward` consumes every tensor from `*xs` as
before.

#### Tests (`tests/test_torch_compile.py`)

`materialise_iverson` unit tests (5):

- `test_materialise_lower_triangular` — `q <= x`, 4×4 → equals `torch.tril`
- `test_materialise_diagonal` — `ieq(q, x)`, 4×4 → equals `torch.eye`
- `test_materialise_banded` — `iabs(q - x) < IversonConst(Integer(2))`, 5×5
- `test_materialise_compound` — `(q < x) & (x < k)`, axes `(q, x, x, k)`,
  sizes 3,4,4,5 → verify shape `(3,4,4,5)` and diagonal values
- `test_materialise_free_axis_raises` — unsized axis → `ValueError`

`ConstructedTensorEquation` integration tests (4):

- `test_auto_materialise_shape` — sized axes, `Score * (q<=x)` → `module(Score)`
  gives correct shape
- `test_auto_materialise_values` — values match `Score * tril_mask`
- `test_auto_materialise_buffer_registered` — `_mask_1` in
  `dict(module.named_buffers())`
- `test_auto_materialise_bool_output` — Bool-output + Iverson factor →
  correct `∃` semantics

Regression (1):

- `test_pre_materialised_still_works` — existing free-axis `module(Score, Mask)`
  call unchanged

### 2. Embedding DSL

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
| `torch_compile/torch_compile.py` | `ConstructedTensorEquation`, `generate_tensor_equation_signature` |
| `tests/test_torch_compile.py` | Compilation and Heaviside tests (all pass) |
| `tsncd/src/data_structure/TensorLogic.ts` | TypeScript stubs + `TensorEquation` operator |
| `tsncd/src/display/Framework/Operations/additionalOperationBoxes.ts` | `TensorEquationBox` |
| `docs/bool_semiring_extension.md` | Full design record |

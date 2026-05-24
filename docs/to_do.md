# Bool Semiring Extension — To-Do

Picking up from the bool semiring implementation session. All changes are
uncommitted (see `git diff --stat HEAD` for the full list). 257 existing
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
- `docs/bool_semiring_extension.md` — design section fully updated

---

## Remaining tasks

### 1. Iverson materialisation in `torch_compile` (highest priority)

`ConstructedTensorEquation.forward(*xs)` already accepts one tensor per RHS
factor. The missing step is generating the Bool input tensor automatically from
an `IversonExpr` tree, so callers don't have to pre-build it.

Work needed:
- Write `materialise_iverson(expr: IversonExpr, sizes: dict[UID, int]) -> torch.Tensor`
  in `torch_compile/` — evaluates the expression tree over a meshgrid of axis
  sizes to produce an `(s0, s1, ...) -> bool` tensor.
- Wire it into `ConstructedTensorEquation.__init__`: detect which input weaves
  have an `IversonBinOp | IversonUnaryOp` operator (readable from
  `target.operator.rhs`) and pre-compute the mask tensors as registered buffers.
- The axis sizes come from the concrete `RawAxis._size` fields (set when using
  `real_axis('x', 512)` etc.) or from declared shapes. Decide how to handle
  free (unsized) axes.

### 2. tsncd rendering (three sub-tasks, all independent)

All signals are already in the pyncd layer. Only TypeScript display code remains.
See `docs/bool_semiring_extension.md § Rendering` for full details.

- **a. `Bool` TypeScript class** — add `export class Bool extends Datatype {}`
  to `tsncd/src/data_structure/BroadcastedCategory.ts`
- **b. `𝔹` datatype anchor** — add `instanceof cat.Bool` branch in
  `tsncd/src/display/Framework/BroadcastedCategoryRenderer.ts` alongside the
  existing `Natural` check; `DatatypeAnchor` shows `𝔹` instead of a number
- **c. Wire styling** — apply `'2,6'` dotted stroke + distinct color to
  `Bool`-typed input weaves; Iverson factor wires (anonymous, no tensor name)
  label themselves with the `iverson_expr` string rather than a name

### 3. Equation string notation in tsncd

Switch `∃`/`∧` display for Bool-output equations. Signal is
`output_weave.datatype == Bool()` — same flag as `ConstructedTensorEquation.demote`,
already set correctly. Only the display string generation in tsncd needs updating.

### 4. Embedding DSL

`ops.Embedding.template()` is unchanged. The Iverson-based embedding derivation
(embedding as a masked contraction over a `Natural`-typed axis) is theoretically
grounded but not yet exposed in the DSL.

### 5. Commit

None of the above changes have been committed. Once a natural stopping point is
reached, commit with a message summarising the bool semiring work.

---

## Key files for context

| File | Role |
|---|---|
| `data_structure/TensorExpr.py` | Iverson tree types, `TensorRef`, `_serialize_iverson` |
| `data_structure/TensorDSL.py` | DSL entry point; `TL`, `TensorProxy`, `_array_datatypes` |
| `data_structure/TensorLogic.py` | `TensorEquation.bc_signature`, `TensorProgram.to_morphism` |
| `torch_compile/torch_compile.py` | `ConstructedTensorEquation`, `generate_tensor_equation_signature` |
| `tests/test_torch_compile.py` | Compilation and Heaviside tests (all pass) |
| `docs/bool_semiring_extension.md` | Full design record |

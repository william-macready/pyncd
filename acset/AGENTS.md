# acset

## Purpose
Owns: converting pyncd's category-theoretic morphism types (`StrideMorphism`, `TensorEquation`, `TensorProgram` from `data_structure/`) into a flat, table-based "acset" (algebraic C-set) representation, and serializing those tables to/from CSV — for interchange with tools outside the recursive `Term`/`UID` object graph.
Does not own: model definition or compilation (`data_structure/`, `torch_compile/`). As of writing, nothing under `tsncd/` yet consumes these CSVs — the boundary is prepared but not wired to a live consumer.

## Code Map

### Find It Fast
| Looking for... | Go to |
|---|---|
| Row/schema dataclasses (the acset schema itself) | `instances.py` |
| `StrideMorphism` → acset conversion | `convert.py::from_stride_morphism` |
| `TensorEquation`/`TensorProgram` → acset conversion | `convert.py::from_tensor_equation`, `from_tensor_program`, `_add_equation` |
| Operator → `OpTag` mapping | `convert.py::_operator_fields`, `_OpFields`, `_TAG_FROM_TYPE` |
| CSV write/read entry points | `csv_io.py::write_sst/read_sst`, `write_sbr/read_sbr` |
| UID string encoding (`Type:id`) and axis-type registry | `csv_io.py::_uid_str/_parse_uid`, `_UID_TYPE_BY_NAME` |

### Key Relationships
Clean layering, one-way: `instances.py` (schema, no deps within this dir) ← `convert.py` (semantic bridge from `data_structure`) and `csv_io.py` (UID/Numeric/name serialization only). Nothing in `data_structure/` imports `acset` — a comment in `data_structure/TensorLogic.py` references `acset.convert` only in prose, to avoid a real import cycle.

## Public API

### Key Exports
| Export | Used By | Change Impact |
|---|---|---|
| `from_tensor_program(prog) -> SBrInstance` | main conversion entry point for real models | relies on `topological_sort` for stable `equation_idx` — reordering breaks CSV determinism |
| `write_sst`/`read_sst`, `write_sbr`/`read_sbr` | persistence layer, `tests/test_acset_csv.py` | fieldname changes must be mirrored in both write and read — hand-paired, not schema-driven |
| `OpTag`, `DataTag` (enums) | `ArrayRow.operator_tag`/`datatype_tag` | new operator → new `OpTag` member + case in `_operator_fields`/`_TAG_FROM_TYPE`, possibly a new CSV column |

### Core Types
- `SStInstance` — one `StrideMorphism`: `axis_sizes`, `entries: list[EntryRow]`.
- `SBrInstance` — one `TensorProgram`: `axis_sizes`, `equations`, `arrays`, `array_axes`, `samples`.
- `ArrayRow` — one tensor (output at `slot=0`, inputs at `slot=1..N`), keyed by `(equation_idx, slot)`; carries `operator_tag`, `op_predicate` (masked-softmax/normalize mask, output-side), `wire_label` (serialized Iverson factor, input-side phantom array).
- `SampleRow` — one reindexing component: `src_uid`, `tgt_uid`, `coeff`, `offset` (affine `b + c*a`).

## Entry Points
| Task | Start Here |
|------|------------|
| Convert a `TensorProgram` to acset tables | `convert.py::from_tensor_program` |
| Write/read acset tables to/from CSV | `csv_io.py::write_sbr`/`read_sbr` (and `write_sst`/`read_sst` for `StrideMorphism`) |
| Add a new operator's serialization support | `convert.py::_operator_fields`/`_OpFields`/`_TAG_FROM_TYPE` |
| Add a new `Axis` subclass's serialization support | `csv_io.py::_UID_TYPE_BY_NAME`/`_UID_NAME_BY_TYPE` |

## Contracts
- **UID identity, not display name, is preserved** across round-trip — `_uid_str`/`_parse_uid` encode only `(_type, _id)`, dropping `_name`.
- **`FreeNumeric` round-trips correctly despite dropping `_name`**, because its equality is by `uid._id` only (see `data_structure/AGENTS.md`, fix `d146fb6`) — `_numeric_str` serializes only `?<uid._id>`.
- **Every `RawAxis` subclass must be registered** in `csv_io.py`'s `_UID_TYPE_BY_NAME`/`_UID_NAME_BY_TYPE` (`test_uid_registry_covers_all_axis_subclasses` enforces this) — an unregistered subclass breaks `_uid_str` with a `KeyError` at write time, with no runtime guard in `csv_io.py` itself.
- **`equation_idx` is assigned from topological order and used as a foreign key everywhere** — reordering equations changes every downstream row reference.
- **Retained axes always sample as identity** (`src_uid == tgt_uid`, `coeff=1`, `offset=0`) because `TensorEquation` retained axes are literally the same object on lhs and rhs.
- **CSV writer/reader fieldname lists are hand-paired, not shared** — a column added to one side without the other silently drops data or raises `KeyError`. `SampleRow.offset` was added later; `read_sbr` defensively does `_parse_numeric(row['offset']) if 'offset' in row else nm.Integer(0)` to stay backwards-compatible with pre-offset CSVs — replicate this pattern for future additive schema changes.

## Patterns
- **Adding a new operator variant**: extend `_operator_fields`/`_OpFields` (one function, with an explicit ordering comment — `Identity` before `Elementwise` since it subclasses it; masked variants checked before generic dispatch) — don't scatter new `isinstance` checks elsewhere.
- **Adding a masked operator with a predicate**: decide whether it's output-side (`op_predicate`) or input-side phantom (`wire_label`) — see Pitfalls, these were split from one field and are easy to conflate.

## Pitfalls
- **`op_predicate` vs `wire_label` confusion** (split via refactor `f8bc09b` from a single `iverson_expr` field): `op_predicate` is the output-side mask (`MASKED_SOFTMAX`/`MASKED_NORMALIZE`); `wire_label` is the input-side serialized Iverson factor on a phantom (`name=None`) array. Writing to the wrong field silently produces an empty column, not an error.
- **`MASKED_NORMALIZE` was previously mis-positioned in `OpTag`** (fix `bc1fc6e`, alongside a missing `ops` import in tests) — signals `OpTag` additions were done ad hoc; watch for tests asserting exact enum ordering when adding new tags.
- **Adding a new `RawAxis` subclass without registering it in `csv_io.py`** breaks `write_sst`/`write_sbr` with a `KeyError`, caught only by `test_uid_registry_covers_all_axis_subclasses` — no runtime guard exists in `csv_io.py` itself.
- **This package is disproportionately tested relative to its size** (~617 lines vs. ~44KB combined in `tests/test_acset_convert.py` + `tests/test_acset_csv.py`) — the conversion/round-trip logic has many subtle edge cases; read those tests before assuming a change is safe.

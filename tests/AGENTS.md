# tests

## Purpose
Owns: test conventions for pyncd — tests are organized by compilation-pipeline layer (DSL surface → categorical/threading semantics → acset conversion/serialization → torch codegen), mirroring the source tree rather than grouping by feature.
Does not own: application code documentation — see each subsystem's own `AGENTS.md` (`data_structure`, `torch_compile`, `acset`, `construction_helpers`, `display`).

## Code Map

### Find It Fast
| Looking for... | Go to |
|---|---|
| TL DSL surface (declarations, indexing, `axes()`, `relu`/`softmax`, `Reindex`) | `test_tensor_dsl.py` |
| Categorical composition, `ThreadedComposed` vs `Composed`, topo sort | `test_tensor_logic.py` |
| Axis alignment (`align_axes`) for composing morphisms | `test_composition.py` |
| Converting `TensorProgram`/`StrideMorphism` → acset | `test_acset_convert.py` |
| CSV (de)serialization primitives | `test_acset_csv.py` |
| `SStInstance`/`EntryRow` construction | `test_acset_instances.py` |
| End-to-end golden-file round-trip of full TL programs | `test_cset_roundtrip.py` (+ generator `generate_cset_serialization.py`) |
| PyTorch codegen (signatures, forward pass, coupled/uncoupled recurrences, Iverson materialisation) | `test_torch_compile.py` (68.6K, largest file — organized in `# ---` banner sections) |
| ASCII rendering of `Reindex` nodes | `test_reindex_display.py` |
| Import-cycle regression (`TensorLogic`/`Operators`/`Category`) | `test_import_hygiene.py` |

## Entry Points
| Task | Start Here |
|------|------------|
| Run the full suite | `uv run pytest` from repo root |
| Regenerate golden CSV fixtures after a schema change | `python tests/generate_cset_serialization.py` |
| Add a new TL example that needs round-trip coverage | add matching builder functions to both `generate_cset_serialization.py` and `test_cset_roundtrip.py` |

## Contracts
- **Golden fixtures under `tests/cset_serialization/` are gitignored, generated artifacts** — `test_cset_roundtrip.py` requires them to exist on disk but they are never committed; there is no CI workflow or fixture that regenerates them automatically.
- **`test_import_hygiene.py` pins the `TensorLogic → Operators → Category → TensorLogic` import order as importable from any entry point** — breaking this (e.g. by adding a new eager cross-import) fails a subprocess-based test, not just an in-process one.

## Patterns
- **Running tests**: `uv run pytest` (or `pytest` inside `.venv`) from repo root. No Makefile test target; `pythonpath = ["."]` in `pyproject.toml` is what makes `data_structure.*`/`acset.*`/`torch_compile.*` resolve without an editable install. No `conftest.py`, no custom markers, no CI workflow.
- **Golden-file fixtures** (`tests/cset_serialization/{matmul,attention_qk,attention_core_qk,attention_core_sv,ffn,attention_chain}/`, 5 CSVs each) are produced **exclusively** by `python tests/generate_cset_serialization.py` — never hand-write them. Regenerate whenever `acset.csv_io.write_sbr` or the CSV schema changes.
- **These fixtures are NOT committed to git** (`.gitignore` lists all 30 CSV paths individually) — a fresh clone/CI run of `test_cset_roundtrip.py` fails with file-not-found until someone manually runs the generator; nothing automates this (no `.github/workflows`).
- **The generator and `test_cset_roundtrip.py` intentionally duplicate the same builder functions** (`_matmul()`/`_attention_qk()` etc. in `generate_cset_serialization.py`, mirrored as `_fresh_matmul()`/`_fresh_attention_qk()` etc. in `test_cset_roundtrip.py`, commented as "matching generate_cset_serialization.py" in both files) — adding a new TL example to one without the matching builder in the other means its round-trip test silently never runs.
- **`test_import_hygiene.py`** enforces that each member of the `TensorLogic → Operators → Category → TensorLogic` cycle, plus `data_structure.TensorDSL` (4 modules total — `TensorDSL` isn't actually part of the import cycle, but is checked the same way), is independently importable as the *first* module loaded in a clean interpreter (spawns a subprocess per case, since `sys.modules` caching hides the bug in-process), and that `Category`'s lazy re-export of `TensorEquation`/`TensorProgram` is `is`-identical to the real objects.

## Pitfalls
- **Hand-editing a fixture CSV instead of regenerating** desyncs it from the generator's builder functions silently — comparison in `test_cset_roundtrip.py` is structural/`_id`-based against a freshly built instance, not an exact CSV diff, so a hand-edit could pass some checks while corrupting others.
- **Fixtures aren't in version control** — a clean checkout fails `test_cset_roundtrip.py` outright unless `tests/generate_cset_serialization.py` is run first; easy to forget since nothing automates it.
- **Stale expected-type assertions**: `test_tensor_logic.py` and `test_ffn_to_morphism` (in `test_tensor_dsl.py:227`, not `test_torch_compile.py`) previously asserted `Composed` where the compiler now returns `ThreadedComposed` for uncoupled recurrences (fixes `0aa2bed`, `be35ed3`). Check current behavior before trusting an `isinstance(morph, Composed)` assertion on a recurrence/Scan-derived morphism — `ThreadedComposed` is the general case.
- **Generator and roundtrip test hardcode identical axis-shape helpers in two files** (`_seq`, `_d`, `_h`, `_k`, `_q`, `_x`) — a mismatch between the two (e.g. changing an axis size in one but not the other) makes the round-trip comparison meaningless rather than failing loudly.
- **`generate_cset_serialization.py` explicitly excludes transformer-level examples** (embedding/projections/aggregator — these live at the `BroadcastedCategory` composition level with no `TensorProgram` representation) — don't expect fixture coverage there.

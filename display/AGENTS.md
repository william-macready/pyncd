# display

## Purpose
Owns: pure, stateless textual rendering of the `data_structure` algebraic AST — a generic box-layout engine (`Box.py`, `Color.py`, no deep-learning knowledge) plus a domain-specific renderer (`node_category.py`) that pattern-matches `Category` variants into `Box` trees, and a debug-table renderer (`display_config.py`) for `term_utilities.ConfigLog`.
Does not own: any mutation of `data_structure` objects — display only reads via dataclass field access / structural pattern matching.

## Code Map

### Find It Fast
| Looking for... | Go to |
|---|---|
| Top-level "print this morphism" entry point | `display/__init__.py` → `print_category` |
| Real recursive renderer / dispatch on Category variant | `node_category.py` → `display_category` |
| Add support for a new Category variant | `node_category.display_category`'s `match` block |
| Generic box layout (rows/cols, padding, fill, justification) | `Box.py` |
| ANSI 24-bit terminal color model | `Color.py` |
| Debug table of `ConfigLog` term→bucket/name assignments | `display_config.py` |
| Rendering a `Reindex` affine gather as text | `node_category.py` → `reindex`, `_row_label` |
| Truncated name/id label for a `UTerm` | `node_category.py` → `display_uterm` |

### Key Relationships
`node_category.py` imports `data_structure.Category` (most variants) and, separately, `data_structure.TensorDSL.Reindex` directly (not part of the `Category` re-export union, so matched via `isinstance` rather than a dataclass pattern). Both renderer files also depend on `term_utilities.term_utilities` (to pick reindexed-weave rendering branch) and `utilities.justification`/`utilities.utilities` for layout.

## Public API

### Key Exports
| Export | Used By | Change Impact |
|---|---|---|
| `print_category` | any script/notebook doing `display.print_category(x)` | thin wrapper; signature changes break callers directly |
| `display_category` | `print_category`, recursively itself | adding a new `Category` subtype requires a new `case` arm — see Pitfalls |
| `Box`/`Horizontal`/`Vertical`/`TextBox`/`Padded`/`Fill` | all of `node_category.py`, `display_config.py` | core layout primitives; a layout bug affects every renderer |

### Core Types
- `Box.Box` (ABC) — template method: override `raw_rows()` (leaf, e.g. `TextBox`) or `rows()` directly (e.g. `Horizontal`/`Vertical`); neither → hits `NotImplementedError`.
- `Box.TextBox(text, fg, bg)` — leaf node; the only place color is actually applied.
- `Box.Padded` — draws a unicode box (`╔═╗║╚╝`) around a body.
- `Color.Color`/`HexadecimalColor` — 24-bit color model (`'#rrggbb'`).

## Entry Points
| Task | Start Here |
|------|------------|
| Print a morphism to the terminal | `display/__init__.py::print_category` |
| Add rendering support for a new `Category` variant | `node_category.py::display_category`'s `match` block |
| Adjust box layout (padding, fill, justification) | `Box.py` |

## Contracts
- `Box.width()`/`height()` are computed **independently** of `rows()`/`raw_rows()` — a custom `Box` must keep both views consistent or layout silently misaligns (no cross-check exists).
- `TextBox.width()` measures ANSI-stripped text (`Color.original`) — color must be applied via `fg`/`bg` constructor params, not embedded in `text`, or width math breaks.
- Importing `display_config.py` has a **module-level side effect**: it monkeypatches `term_utilities.generate_config.ConfigLog.__str__` globally, process-wide, on first import.

## Patterns
- Render a term: `print_category(target)` builds a `Box` tree, then `.render()` produces the multi-line string.
- A `Broadcasted` renders as three columns: input weaves | degree+operator | output weaves, each built with `separated_product` (Vertical, `-`-fill separators).
- Weave/axis rendering shares iterators zipped against `weave._shape` — strictly order-dependent; a real `Axis` entry renders via `display_axis`, other slots pull the next item from the same shared iterator.
- `UTerm` labels are hard-truncated to exactly 2 characters (first 2 chars of the name, or last 2 hex digits of `uid._id`).

## Pitfalls
- **`display_category`'s `match` has no unconditional default arm** — the last case is `case _ if isinstance(target, Reindex)`. Any `Category` value matching none of the explicit patterns and not a `Reindex` (e.g. a bare `Scatter`, or a new variant added upstream without updating this file) falls through with **no error** — the function implicitly returns `None`, and the failure surfaces later as a confusing `AttributeError` deep inside `Box.Horizontal.rows()`'s `zip(*box_rows)`.
- **2-character name/id truncation is intentional, not a bug** — distinct terms whose first-2-chars or last-2-hex-digits coincide render identically.
- **`Color.original()` assumes well-formed ANSI escapes** — a malformed/truncated escape (no trailing `m`) makes `s.find('m', start)` return `-1`, silently corrupting the string (mis-slices from position 0) rather than raising.
- **`reindexed_weave` branches purely on `tutil.is_mappable(reindexing)`** (`# type: ignore` at the call site) — the two branches expect structurally different reindexing shapes not enforced by the type system; a `StrideCategory` value misclassified by `is_mappable` picks the wrong renderer.
- **Importing `display_config.py` mutates global state** merely by being imported (monkeypatches `ConfigLog.__str__`), independent of whether anything in the module is called.

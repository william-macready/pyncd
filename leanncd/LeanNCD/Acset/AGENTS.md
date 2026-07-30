# LeanNCD/Acset

## Purpose
Owns: the acset **schema** (`SBrInstance`, five typed row-tables mirroring Python `pyncd/acset/instances.py`) and **CSV text mechanics** (byte-faithful field encode/decode, mirroring Python `csv_io.py`).
Does not own: the interesting round-trip proofs — `../Bridge/AcsetCodec.lean` imports only `Acset.SBrInstance` (the schema types) and builds `SBrInstance` values directly from `ThreadedComposed` in memory; it never touches this dir's `Csv`/`Io`. **The CSV-text round-trip (`readSBr ∘ writeSBr = id`) and the semantic round-trip (`ThreadedComposed ↔ SBrInstance`, proved in Bridge/) are two independent, un-composed claims** — nothing in this repo proves decoding a `ThreadedComposed` from CSV text and back recovers it end-to-end.

## Code Map

### Find It Fast
| Looking for... | Go to |
|---|---|
| Row/schema structures (mirrors Python `instances.py`) | `SBrInstance.lean` |
| Field string-codecs (UID, size, bool, enum tags) | `Csv.lean` |
| Table framing (`\r\n`, header+rows, comma-split) | `Csv.lean` — `renderRow`/`renderTable`/`parseTable` |
| Five-table serialize/deserialize entry points | `Io.lean` — `writeSBr`/`readSBr` |

### Key Relationships
`../Bridge/AcsetCodec.lean` and `../Bridge/SBr.lean` import only `Acset.SBrInstance` (schema types), not `Csv`/`Io`. This dir imports `Base.SizeExpr` (`ArrayRow.maxValue`, `axisSizes : List (AxisUID × SizeExpr)`).

## Public API

### Key Exports
| Export | Used By | Change Impact |
|---|---|---|
| `SBrInstance`, `ArrayRow`, `ArrayAxisRow`, `SampleRow`, `EquationRow`, `OpTag`, `DataTag` | `Bridge/AcsetCodec.lean`, `Bridge/SBr.lean`, `test/Acset/*`, `test/Bridge/AcsetCodecTest.lean` | field-order changes must be mirrored in `Io.lean`'s row builders (hand-paired, not schema-driven — same caveat as Python's `csv_io.py`) |
| `writeSBr : SBrInstance → List (String × String)` | `test/Acset/IoTest.lean` | five `(filename, csv-text)` pairs, Python-identical column headers |
| `readSBr : List (String × String) → Except CsvError SBrInstance` | `test/Acset/IoTest.lean` | inverse of `writeSBr`; errors on missing file / malformed field |

### Core Types
`SBrInstance { axisSizes, equations, arrays, arrayAxes, samples }` — the same schema as Python's `SBrInstance`/`ArrayRow`/`SampleRow`, as typed Lean structures (`DecidableEq`, `Repr`, `Inhabited`) rather than Python dataclasses — notably more constrained (`maxValue : Option SizeExpr`, `coeff`/`offset : Int` are computable values, not opaque strings).

## Entry Points
| Task | Start Here |
|------|------------|
| Add a new schema field | `SBrInstance.lean` — then `Csv.lean` (codec) and `Io.lean` (both directions) in lockstep |
| Serialize/deserialize an `SBrInstance` | `Io.lean::writeSBr`/`readSBr` |

## Contracts
- **No embedded commas/quotes assumed** — acset CSV data is comma-split with no quoting, assumed a faithful inverse of Python `csv.writer`/`DictReader`; this is a documented, **unchecked** assumption, not proved.
- Every row (including the last) is `\r\n`-terminated to byte-match Python's `csv` module.
- `decodeUID` treats untagged UIDs (no `:`) as `RawAxis`, matching Python's `_UID_TYPE_BY_NAME.get` fallback.
- CSV field order in `writeSBr`/row builders must stay in sync with Python's exact column order — hand-written pairing, not derived from `SBrInstance`'s field list.

## Pitfalls
- **The Io.lean "sorry" is a false alarm — do not go looking for a live proof obligation there.** A precise grep matches exactly one line, inside a doc comment: *"Fully executable, zero `sorry`."* `writeSBr`/`readSBr` are fully computable with no `sorry`/`admit`/axiom anywhere.
- **The CSV-text round trip `readSBr (writeSBr inst) = .ok inst` is NOT a proven theorem anywhere in the repo** — despite a commit titled "Lean round-trip readSBr∘writeSBr = id," it is only checked via `#guard` on three concrete fixture instances in `test/Acset/IoTest.lean` (decidable-equality spot-checks), not a universally-quantified theorem. It would break silently for e.g. a name/field containing a literal comma (see the no-quoting assumption above).
- **`encodeSize` is partial over `SizeExpr`** — errors on compound expressions (`.add`/`.sub`/`.mul`/`.div`); only `.lit`/`.var` round-trip through CSV. An `SBrInstance` with compound symbolic sizes fails to serialize (`Except.error`, not a crash) unless the caller handles it. ⚠️ **This became true only in Wave A (2026-07-30); it described intent, not behaviour, when first written.** `writeSBr` used to **swallow** the error — probed: `encodeSize` errored on a compound `SizeExpr` yet `writeSBr` emitted a truncated `"axis_uid,size\r\nRawAxis:1,\r\n"` and returned *normally* (audit finding **#17**). What enforces it now is the signature: `encSizeOpt`/`axisSizesRows`/`arrayRows`/`writeSBr` all return `Except CsvError`, so the error has nowhere to go but the caller. The former docstring claim "sizes here are `.lit`/`.var` so total" was an assumption stated as fact — and was the reason nobody checked.
- **Field encode/decode pairs are hand-paired per column** — same maintenance hazard as Python's `acset/AGENTS.md` Contracts section. Adding a new `ArrayRow` field requires touching `SBrInstance.lean`, `Csv.lean` (new codec), and `Io.lean` (both directions) in lockstep.

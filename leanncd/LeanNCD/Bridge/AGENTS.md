# LeanNCD/Bridge

## Purpose
Owns: the seam between the noncomputable math tower (`../Base/Br`, `../Base/St`) and the computable pipeline (`../DSL/Target`'s `ThreadedComposed`, `../Acset/SBrInstance`'s CSV twin). Answers three questions: what `Br` morphism does a compiled DAG *mean* (`Realize.lean`), what does it look like as flat relational tables and can we get it back losslessly (`AcsetCodec.lean`), and do the DSL-compiled path and the CSV-round-trip path agree (`Agreement.lean`). `SBr.lean` composes decode+realize into one entry point.
Does not own: the routing/compile proofs themselves (`../DSL/Pipeline/RouteSpec.lean`) — Bridge only *consumes* them. Nothing else in the tree depends on Bridge/ (it's a terminal consumer, verified via `grep -rl "LeanNCD\.Bridge"` — only `LeanNCD.lean` matches).

## Code Map

### Find It Fast
| Looking for... | Go to |
|---|---|
| Interpret a compiled DAG as a categorical morphism | `Realize.lean` → `realize`, `ThreadedComposed.WellFormed` |
| Does every compiled program satisfy realize's precondition? | `Agreement.lean` → `compile_wellFormed` |
| Encode/decode `ThreadedComposed` ↔ acset tables | `AcsetCodec.lean` → `fromThreadedComposed` (encode), `toThreadedComposed` (decode) |
| Round-trip theorem (decode∘encode = id) | `AcsetCodec.lean` → `toThreadedComposed_fromThreadedComposed` |
| Realize an acset instance directly (CSV path) | `SBr.lean` → `realizeSBr` |
| DSL-path and CSV-path agree | `Agreement.lean` → `realize_fromThreadedComposed_agree` (Prop 8) |
| Extra shape invariant the round-trip needs beyond `WellFormed` | `AcsetCodec.lean` → `ThreadedComposed.WellShaped` |
| Two-slot axis name/id encoding | `AcsetCodec.lean` → `nameUidFor3`/`encodeAxisSizes` |

### Key Relationships
Bridge imports `Base.Br`/`Base.BrWiring`/`Base.SizeExpr` (math tower), `DSL.Target`/`DSL.Compile`/`DSL.Pipeline.RouteSpec` (pipeline), `Acset.SBrInstance` (schema). Only `LeanNCD.lean` imports Bridge — safe to change internals as long as the four exported theorems/defs below keep their signatures.

## Public API

### Key Exports
| Export | Used By | Change Impact |
|---|---|---|
| `realize (tc) (h : tc.WellFormed)` | `SBr.lean`, `Agreement.lean` | signature change breaks both downstream files |
| `compile_wellFormed` | `realizeCompiled` | core compiler-soundness contract — "any real compiled program can be realized" |
| `fromThreadedComposed`/`toThreadedComposed` | `SBr.realizeSBr`, `Agreement`'s agreement proof | codec changes must re-prove `toThreadedComposed_fromThreadedComposed` |
| `realizeSBr` | external CSV/Python-interop consumers | `noncomputable`; total via classical `Decidable` + empty-identity fallback on malformed input |
| `realize_fromThreadedComposed_agree` / `agree_dom`/`agree_cod` | top-level correctness claim of the whole bridge (Prop 8/8′) | — |

### Core Types
`ThreadedComposed`/`Acset.SBrInstance` are defined elsewhere (`../DSL/Target`, `../Acset/SBrInstance`) — Bridge adds `.WellFormed` (`Realize.lean`) and `.WellShaped` (`AcsetCodec.lean`) predicates on top.

## Entry Points
| Task | Start Here |
|------|------------|
| Interpret a compiled DAG categorically | `Realize.lean::realize` |
| Add a new acset table field | `AcsetCodec.lean`'s `from_field_filter` (reuse, don't re-derive) |
| Check whether a compiled program is realizable | `Agreement.lean::compile_wellFormed` |
| Realize straight from a CSV-backed acset instance | `SBr.lean::realizeSBr` |

## Contracts
- **`realize` is total and sorry-free under `WellFormed`** — `Realize.lean`'s only grep hit for `sorry` is a prose "no `sorry`" comment.
- **Every compiled program is `WellFormed`**: `compile_wellFormed` (`Agreement.lean`) assembles `wf_typeMatch` (routed reads match step inputs — depends on `RouteSpec.buildStep_output_fixedAxes`, see `../DSL/AGENTS.md`), `wf_singleOutput` (weakened to `≥1` output for multi-output scans), `wf_topo` (reads ⊆ live pool), plus `wellFormedDom` (carried by construction from `route`'s fail-loud guard). A change to `slotWeave`'s ordering in `../DSL/Pipeline/` ripples into `wf_typeMatch`/`compile_wellFormed`.
- **`wf_topo`/`topo_bound` is a soundness tripwire.** As first stated it was false (`897d515`): true cycles, and coupled-scan self-recurrence (a scan step reading its own just-produced output). A plain "fail loud on cycle" guard also rejected valid coupled scans and was reverted. It holds now via a `routableInOrder` guard plus excluding self-reads from `inputReadFactors` (`../DSL/Pipeline/RouteSpec.lean`); a change to scan/scheduling logic can silently make it false again.
- **The acset round-trip needs `WellFormed ∧ WellShaped`**, not `WellFormed` alone (`toThreadedComposed_fromThreadedComposed`, `AcsetCodec.lean`). `WellShaped` (routing/step-count agreement, reindexing-matrix dimensions) exists because the presentation types in `../DSL/Target.lean` dropped the dependent `StMat` typing that would otherwise enforce it.
- **`Realize.lean`, `AcsetCodec.lean`, `SBr.lean`, `Agreement.lean` are all sorry-free** (by reading, confirmed independently by `SORRY_INVENTORY.md`). `LeanNCD.lean`'s top-of-file comment still lists "the `Bridge` realize/agreement bodies" among staged sorries — it is stale.
- **Proof structure.** `AcsetCodec.lean`'s round trip is built bottom-up: `fromThreadedComposed` (pure bookkeeping) → `toThreadedComposed` (total, degrades gracefully on garbage) → isolation infrastructure → per-field round trips → per-slot inversion → per-step assembly → the final theorem; then `realizeSBr` and Prop 8. **A new acset table field reuses `from_field_filter`**, the generic per-field isolation lemma, rather than a bespoke proof.
- **Two-slot axis encoding**: `nameUidFor3` beside `axisUidFor3` — axis identity and axis name are independent entries keyed by one `Nat.pair`-derived id, so name recovery is unconditional (the one-slot design conflated them; fix `a94e725`).
- **Nat strings are unary, deliberately** (`natToUnary`/`unaryToNat`): decimal string round-trip lemmas don't exist ready-made in Mathlib/Batteries, while unary length + `Nat.pair`/`unpair` round-trip trivially. Don't switch to decimal without re-deriving those lemmas.
- **`AcsetCodec.lean` is NOT byte-faithful to Python's `pyncd/acset/instances.py`** — `brOpIdx`/`brOpOfIdx` are an internal 0–14 tag unrelated to Python's `OpTag`. Round-trip fidelity here does not imply Python-CSV fidelity (`../Acset/`'s separate, weaker guarantee).
- **`brOpOfIdx?` is the single total table and `brOpOfIdx` derives from it**, so the two cannot drift. A `| _ => .contract` default used to be reachable from CSV (a missing `EquationRow` gives `"" ⇒ 0 ⇒ .contract`, silently turning a garbled relu/softmax/scatter/scan tag into a plain contraction). Guarded by three `#guard`s (mutual inverse over `0..14`, two out-of-range). Keep `brOpOfIdx?_brOpIdx` proved by `cases op <;> rfl`, not `simp [brOpOfIdx]`, which widens the axiom set to `[propext]`.
- **The boundary decoders are still unaudited** (semantic-payload finding #6): `realizeStMat` zero-fill, `realizeBrBaseP`, `AcsetCodec` decode defaults, `realizeSBr` → empty identity are the same class of meaning-changing default the `brOpOfIdx` fix closed, and have not been probed. Do not assume that fix generalised to them.
- **`brCancelPoint` (`../Base/Br.lean`) is upstream context, not a Bridge blocker** — `realize`/`Agreement`/`AcsetCodec` do not depend on it.

## Pitfalls
- **`topo_bound` can silently become false again** after any scan/scheduling change — see Contracts before touching `routableInOrder` or `inputReadFactors`.
- **Round-trip fidelity ≠ Python-CSV fidelity** — `brOpIdx` tags are internal.
- **Don't trust file-level doc summaries** (e.g. `LeanNCD.lean`'s sorry list) — read the file.
- **Decoders may still hide meaning-changing defaults** (finding #6, unaudited).

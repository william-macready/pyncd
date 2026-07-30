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
| Round-trip theorem (decode∘encode = id) | `AcsetCodec.lean:1569` → `toThreadedComposed_fromThreadedComposed` |
| Realize an acset instance directly (CSV path) | `SBr.lean` → `realizeSBr` |
| DSL-path and CSV-path agree | `Agreement.lean:407` → `realize_fromThreadedComposed_agree` (Prop 8) |
| Extra shape invariant the round-trip needs beyond `WellFormed` | `AcsetCodec.lean:524` → `ThreadedComposed.WellShaped` |
| Two-slot axis name/id encoding | `AcsetCodec.lean:124-139` → `nameUidFor3`/`encodeAxisSizes` |

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
`ThreadedComposed`/`Acset.SBrInstance` are defined elsewhere (`../DSL/Target`, `../Acset/SBrInstance`) — Bridge adds `.WellFormed` (`Realize.lean:139`) and `.WellShaped` (`AcsetCodec.lean:524`) predicates on top.

## Entry Points
| Task | Start Here |
|------|------------|
| Interpret a compiled DAG categorically | `Realize.lean::realize` |
| Add a new acset table field | `AcsetCodec.lean`'s `from_field_filter` (reuse, don't re-derive) |
| Check whether a compiled program is realizable | `Agreement.lean::compile_wellFormed` |
| Realize straight from a CSV-backed acset instance | `SBr.lean::realizeSBr` |

## Contracts
- **`realize` is total and sorry-free under `WellFormed`** — no bare `sorry` in `Realize.lean` (the one grep hit at line 24 is a prose "no `sorry`" comment).
- **Every compiled program is `WellFormed`**: `compile_wellFormed` (`Agreement.lean:379`) assembles `wf_typeMatch` (routed reads match step inputs — depends on `RouteSpec.buildStep_output_fixedAxes`, see `../DSL/AGENTS.md`), `wf_singleOutput` (weakened to `≥1` output for multi-output scans), `wf_topo` (reads ⊆ live pool — see Pitfalls), plus `wellFormedDom` (carried by construction from `route`'s fail-loud guard).
- **The acset round-trip needs `WellFormed ∧ WellShaped`**, not `WellFormed` alone (`AcsetCodec.lean:1569`) — `WellShaped` (routing/step-count agreement, reindexing-matrix dimensions) exists because the presentation types dropped the dependent `StMat` typing that would otherwise enforce it (`../DSL/Target.lean:63`).
- **`Realize.lean`, `AcsetCodec.lean`, `SBr.lean`, `Agreement.lean` are all sorry-free** (verified by reading, not just grep — `SORRY_INVENTORY.md` lines 310-322 confirms this independently).

## Patterns
- **`AcsetCodec.lean`'s round-trip proof is staged across lettered Tasks** (visible in commits): Task A (`fromThreadedComposed`, pure bookkeeping, no proof obligations) → Task B (`toThreadedComposed`, total, degrades gracefully on garbage input) → Task C (the round-trip theorem, built bottom-up: isolation infra → per-field round trips → per-slot inversion → per-step assembly → final theorem) → Task D (`realizeSBr`) → Task E (Prop 8, trivial once C+D exist).
- **Generic per-field isolation lemma**: `from_field_filter` (`AcsetCodec.lean:444`) is the reusable higher-order lemma every per-field round-trip theorem instantiates. **Anyone adding a new acset table field should reuse this, not re-derive a bespoke proof.**
- **Two-slot axis encoding** (`nameUidFor3` alongside `axisUidFor3`): axis identity and axis name are independent entries keyed by the same `Nat.pair`-derived id, so name recovery is unconditional (fix `a94e725` — the original one-slot design conflated the two).
- **Unary `Nat`-string encoding chosen deliberately over decimal** (`AcsetCodec.lean:27`) — decimal string round-trip lemmas don't exist ready-made in Mathlib/Batteries; unary-length + `Nat.pair`/`unpair` round-trip trivially. Don't "simplify" to decimal without re-deriving those lemmas.

## Pitfalls
- **`wf_topo`/`topo_bound` was FALSE as originally stated** (`897d515`): two real counterexamples — true cycles (no acyclicity check originally) and coupled-scan self-recurrence (a scan step reading its own just-produced output, which the monotonic-pool model doesn't yet contain at that point). A naive "fail loud on cycle" guard was tried and reverted because it also rejected valid coupled scans. Now resolved via a `routableInOrder` guard + excluding self-reads from `inputReadFactors` (in `../DSL/Pipeline/RouteSpec.lean`). **A future change to scan/scheduling logic can silently make `topo_bound` false again — this is a real soundness tripwire.**
- **`RouteSpec.buildStep_output_fixedAxes` (outside Bridge/) is load-bearing for `wf_typeMatch`** — a change to `slotWeave`'s ordering convention in `../DSL/Pipeline/RouteSpec.lean` would ripple into `wf_typeMatch`/`compile_wellFormed` here.
- **`AcsetCodec.lean` is intentionally NOT byte-faithful to Python's `pyncd/acset/instances.py`** — `brOpIdx`/`brOpOfIdx` are an internal 0-14 tag unrelated to Python's `OpTag` cardinality. Round-trip-fidelity here does not imply Python-CSV-fidelity (that's `../Acset/`'s separate, weaker guarantee).
- **`brOpOfIdx?` is the single total table; `brOpOfIdx` DERIVES from it** — so the two cannot drift. Until 2026-07-30 `brOpOfIdx`'s final arm was `| _ => .contract`, and that default was **reachable from CSV**: `decodeStep` takes the tag via `unaryToNat` of a raw string, and a **missing `EquationRow` yields `"" ⇒ 0 ⇒ .contract`**, so a garbled relu/softmax/scatter/scan tag silently became a plain contraction with no error (audit finding **D**). Guarded by three `#guard`s (mutual-inverse over `0..14`, plus two out-of-range). Keep `brOpOfIdx?_brOpIdx` proved by `cases op <;> rfl`, **not** `simp [brOpOfIdx]` — the `simp` form widens the axiom set from axiom-free to `[propext]`.
- **⚠️ The boundary DECODERS are still unaudited** — finding **#6** (`realizeStMat` zero-fill, `realizeBrBaseP`, `AcsetCodec` decode defaults, `realizeSBr` → empty identity) is the same *class* of meaning-changing default that D turned out to be, but has **not been probed**. Assigned to Stage-5 bridge hardening. Do not assume the D fix generalised to them.
- **`LeanNCD.lean`'s top-of-file doc comment is stale** — it still lists "the `Bridge` realize/agreement bodies" among deliberate staged sorries, but both are now fully sorry-free (Tasks C/D/E landed after that comment was written). `SORRY_INVENTORY.md` itself flags this class of staleness. Don't trust file-level doc summaries at face value — read the actual file.
- **`brCancelPoint` (`../Base/Br.lean`, see that dir's AGENTS.md) is upstream context, not a Bridge/ blocker** — `realize`/`Agreement`/`AcsetCodec` do NOT depend on it.

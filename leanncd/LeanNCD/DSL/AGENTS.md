# LeanNCD/DSL

## Purpose
Owns: the Lean-side twin of pyncd's TensorLogic DSL — parses `tl!{...}` surface syntax, elaborates to a typed AST, and proves properties of the compile→route pipeline that produces a routed DAG (`ThreadedComposed`). Two layers, strict one-way dependency: top-level files (`Syntax`→`Elab`→`Ast`/`Target`, plus `Traverse*`) own parsing/AST/UID-remapping; `Pipeline/` (`Types`→`Structural`→`Lowering`→`RouteSpec`) owns the 8-phase compile pipeline and its correctness proofs.
Does not own: evaluation semantics (`../Eval/`) or the acset bridge (`../Bridge/`) — both consume `DSL.Target`'s presentation types.

**House principle: fail loud, never silently drop semantics.** Cyclic dataflow, non-injective scatters, nonlinear scatters, inconsistent coupled-scan axis orders are all explicit `CompileError` variants, not silent miscompiles.

## Code Map

### Find It Fast — top-level `DSL/`
| Looking for... | Go to |
|---|---|
| Surface grammar (23 syntax categories) | `Syntax.lean` |
| `Syntax → AST` elaborators | `Elab.lean` |
| AST types (`Stmt`, `LHSSlot`, `RHSExpr`, `Nonlin`, `IdxExpr`, `Decl`) | `Ast.lean` |
| Routed-DAG target format (`ThreadedComposed`/`BrBaseP`/`Wire`/`StMatP`) | `Target.lean` |
| 8-phase pipeline chain + `tl!{...}` macro | `Compile.lean` |
| Generic per-node axis traversal (canonical UID-remap primitive) | `TraverseAxes.lean` |
| `mapUID` per-node instantiations (thin wrappers over TraverseAxes) | `Traverse.lean` |

### Find It Fast — `DSL/Pipeline/`
| Looking for... | Go to |
|---|---|
| Pipeline intermediate types (`ResolvedProgram`, `ScanStmt`, `ScheduledProgram`) | `Types.lean` |
| Phases 1-5 (assignUIDs/resolveDecls/checkReadRanks/checkDtypes/checkScatterNonlin/lowerArith/finalizeScans) | `Structural.lean` |
| Phase 6-8 (splitNonlins/schedule/route/buildStep/routeCore) | `Lowering.lean` |
| Proofs about routeCore/buildStep (Track A, lemmas B.1-B.7) | `RouteSpec.lean` |

### Key Relationships
Strictly layered: `Syntax`→`Elab`→`Ast`/`Target`→`Traverse`/`TraverseAxes`→`Pipeline/Types`→`Pipeline/Structural`→`Pipeline/Lowering`→`Pipeline/RouteSpec`→`Compile`. **One deliberate cross-layer exception**: `Structural.lean:15` imports `../Eval/Contract` — flagged in its own header comment as "the ONLY cross-layer import on this branch," solely so `Stmt.uids_eq` and six `specsX_map_uid_eq` lemmas can state their RHS against `Eval.Contract`'s real UID collectors. Downstream: `Bridge/AcsetCodec.lean`/`Realize.lean` import only `DSL.Target`; `Bridge/Agreement.lean` imports `DSL.Compile` and `Pipeline.RouteSpec` directly. `Eval/*` imports `DSL.Ast`/`DSL.Compile`/`Pipeline.Types`/`TraverseAxes` but never `Pipeline.Structural`/`Lowering` directly.

## Public API

### Key Exports
| Export | Used By | Change Impact |
|---|---|---|
| `tl!{ ... }` macro | any file embedding a TL program | any pipeline-phase change ripples here |
| `TLProgram.compile`/`.compileToScheduled` | `tl!` macro; `Eval/Eval.lean` | central pipeline-order contract |
| `ThreadedComposed`, `BrBaseP`, `Wire`, `StMatP` (`Target.lean`) | `Bridge/*`, `Eval/*` | the stable wire format to downstream layers — treat as an ABI |
| `route`/`routeCore`/`buildStep` (`Lowering.lean`) | `Bridge/Agreement.lean`, `RouteSpec.lean`'s proofs | any signature change invalidates all B.1-B.7 lemmas |

### Core Types
- `TLProgram { decls, stmts }`; `Stmt = assign | scatter | recurMorphism`; `LHSSlot = free | freeNorm | iterAt | iterNext | affine` (the scatter/plain/scan classifier); `Nonlin = identity | pointwise PointwiseFn | axiswise AxiswiseFn (Option BoolExpr)` (mask-typed-in by construction).
- `ScanStmt = plain Stmt | scan (base recur : List Stmt) (isAffine) | scanPre` — post-`finalizeScans` unit grouping coupled recurrences.
- `ThreadedComposed { steps : List BrBaseP; routing : List (List Wire); nExternal }`; `Wire = external Nat | internal Nat Nat`; `StMatP { domLen codLen : Nat; coeffs; bias }` with `.wellFormed`/`.validate`.

## Entry Points
| Task | Start Here |
|------|------------|
| Add new surface syntax | `Syntax.lean` — then `Elab.lean` for elaboration, `Ast.lean` for the target type |
| Add a new compile phase / validation | `Pipeline/Structural.lean` (validation-only) or `Pipeline/Lowering.lean` (transforming) |
| Debug a routing/`buildStep` proof | `Pipeline/RouteSpec.lean` — check which B.\* lemma covers your change |
| Change the routed-DAG wire format | `Target.lean` — ripples into `../Bridge/AGENTS.md` and `../Eval/AGENTS.md` |

## Contracts
Proved (verified by reading, not sorry'd): `dedupByUid_uid_nodup`; `reindexing_wellFormed`; **B.1** `buildNameToStep_lt`/`_slot_lt`; **B.3** `routeCore_routable`; **B.5** `buildStep_wires_mapM`; **B.6** `buildStep_inputWeaves`; **B.7** `buildStep_output_fixedAxes` (`RouteSpec.lean:381-395` — real proof body, closes via `outputAxesConsistent` + `fixedAxesP_mapWeave_pos`, the Phase-B capstone); downstream **M3** `buildStep_output_reducesOnlyContracted`; `buildExtIndex_injective`/`_lt_card`.

**Conditional/documented gap**: `ScanStmt.readArityOk` (`Lowering.lean:427-430`) — a hypothesis that every internal read's index-position count matches its producer's published rank. Its doc comment states this is an **upstream** property (owned by `checkReadRanks`/`env`), not derivable at the routing layer. `buildStep_reindexings_codLen_eq_inputRank` (`RouteSpec.lean:645-662`) takes it as a hypothesis — this closes Track A "#1" *modulo* the stated gap, not unconditionally. Not a bug; don't try to "finish" it without a separate upstream effort.

## Patterns
`tl!{...}` flow (`Compile.lean:19-29`): Parse → **assignUIDs** (mint fresh UIDs per axis name) → **resolveDecls** (classify external vs. produced names) → **checkReadRanks**/**checkDtypes**/**checkScatterNonlin** (validation, fail loud) → **lowerArith** (Phase 4: reclassify affine/diagonal LHS to `.scatter`; reject non-injective scatters without `reduce sum`) → **finalizeScans** (Phase 5: group `iterAt`/`iterNext` into `ScanStmt.scan` via union-find on shared iteration-axis UID) → **splitNonlins** (Phase 6: isolate each nonlinearity into its own step) → **schedule** (Phase 7: topological sort, fail loud on cycles) → **route** (Phase 8: two-pass — build `nameToStep`/`extIndex`, then fold `buildStep` into `BrBaseP` steps + `Wire` routing).

## Pitfalls
- **`traverseAxes` is canonical** — `mapUID`/`specs*` are thin instantiations of `TraverseAxes.lean`'s generic traversal, not independent implementations. `unifyAxes`/`Exec/Context.lean` and all `*_eq_old` scaffolding are confirmed fully deleted (zero grep hits) — don't look for them.
- **`schedule` fails loud on cycles** (`Lowering.lean:157-164`) — the underlying Kahn's-algorithm `topoSort` silently falls back to source order on a cycle; `schedule` re-checks with `isTopoOrdered` and throws `CompileError.cyclicDataflow` explicitly, rather than letting a bad order surface later as an obscure eval-time error.
- **`buildStep_output_fixedAxes` (B.7) depends on `outputAxesConsistent`**, a fail-loud guard inside `buildStep` (`Lowering.lean:447-450,509-512`): a coupled scan whose outputs disagree on shared-axis order (e.g. base `G[i,j]` vs. recur `G[j,i]`) is a compile error (`CompileError.inconsistentScanAxes`), not a silently-wrong output weave. This guard is what makes the canonical `ScanStmt.slotWeave` ordering sound — a change to that ordering ripples into `Bridge/Agreement.lean`'s `wf_typeMatch`.
- **`relu(where=...)` is unrepresentable by design, not omission**: `Syntax.lean` splits nonlinearity keywords into two *closed* categories (`tl_pointwise_kw` vs `tl_axiswise_kw`) — only the axiswise grammar production has an optional mask clause. This trades worse parse diagnostics for compile-time impossibility of a masked pointwise nonlinearity.
- **Scatter + nonlinearity is a currently-enforced restriction tracing to a real fixed bug**: `checkScatterNonlin` (`Structural.lean:713-741`) rejects any scatter/affine-LHS write with non-identity nonlin, because `Eval/Scatter.lean`'s `evalScatter` never applied `rhs.nonlin` — `Out[2*i] := relu(X[i])` used to compile and silently drop the `relu`. Documented as a "Spike-3 Stage-0 SHORT-TERM policy," not permanent — real nonlinear-scatter support needs a semantic decision (activate before/after collision-reduction) that's explicitly deferred.
- **The `Eval.Contract` import in `Structural.lean` is a documented SPIKE EXCEPTION** — don't treat it as precedent for other cross-layer imports between `Pipeline/` and `Eval/`; reverting it means deleting the import together with `Stmt.uids_eq` and its six dependent lemmas.
- **Track A is complete except `readArityOk`** — everything else (uid-distinctness, M2/M3, #1's unconditional half) is fully proved; only the internal-read codomain-length tie needs the stated hypothesis.

# LeanNCD/DSL

## Purpose
Owns: the Lean-side twin of pyncd's TensorLogic DSL — parses `tl!{...}` surface syntax, elaborates to a typed AST, and proves properties of the compile→route pipeline that produces a routed DAG (`ThreadedComposed`). Two layers, strict one-way dependency: top-level files (`Syntax`→`Elab`→`Ast`/`Target`, plus `Traverse*`) own parsing/AST/UID-remapping; `Pipeline/` owns the 8-phase compile pipeline and its correctness proofs.
Does not own: evaluation semantics (`../Eval/`) or the acset bridge (`../Bridge/`) — both consume `DSL.Target`'s presentation types.

**House principle: fail loud, never silently drop semantics.** Cyclic dataflow, non-injective scatters, nonlinear scatters, inconsistent coupled-scan axis orders are all explicit `CompileError` variants, not silent miscompiles.

## Code Map

### Top-level `DSL/`
| Looking for... | Go to |
|---|---|
| Surface grammar | `Syntax.lean` |
| `Syntax → AST` elaborators | `Elab.lean` |
| AST types (`Stmt`, `LHSSlot`, `RHSExpr`, `Nonlin`, `IdxExpr`, `Decl`), `TensorElementType`, declaration→storage-kind rules (`storageConstraintOfDecl`, `storageConstraintOfName?`, `buildDeclEnv`), shared slot helpers (`LHSSlot.toReadIdx`, `producerSlots`, `slotsBecomeScatter`, `LHSSlot.outExtent`) | `Ast.lean` |
| Routed-DAG target format (`ThreadedComposed`/`BrBaseP`/`Wire`/`StMatP`) | `Target.lean` |
| Pipeline chain + `tl!{...}` macro | `Compile.lean` |
| Generic per-node axis traversal (canonical UID-remap primitive) | `TraverseAxes.lean`; `Traverse.lean` holds thin `mapUID` instantiations |

### `DSL/Pipeline/`
| Looking for... | Go to |
|---|---|
| Intermediate types (`ResolvedProgram`, `ScanStmt`, `ScheduledProgram`) | `Types.lean` |
| Phases 1–5 (`assignUIDs`, `resolveDecls`, `reclassifyIterSlots`, `checkReadRanks`, `checkDtypes`, `checkScatterNonlin`, `lowerArith`, `finalizeScans`) and the shared statement-level rules (`declaredAxisSizes`, `externalReadNames`, rank, LHS axis-kind, predicate-output checks) | `Structural.lean` |
| Whole-schedule validation (`validateScheduled`, the execution/preparation boundary), topology helpers, external-name order, storage-kind derivation (`scheduleStorageKind`, `scheduleStorageNames`, `scheduleFloat32Name?`) | `ScheduledValidation.lean` |
| Phases 6–8 (`schedule`, `route`, `buildStep`, `routeCore`); `splitNonlins`/`splitStmt` survive only as a regression comparator | `Lowering.lean` |
| Logical schedule → physical `routeCore` input (`physicalizeForRoute`, `physicalizeOne`, `fragmentClass`) | `RouteFragments.lean` |
| Proofs about `routeCore`/`buildStep` (Track A, B.1–B.7) | `RouteSpec.lean` |

### Import structure
`Syntax`→`Elab`→`Ast`/`Target`→`Traverse`/`TraverseAxes`→`Pipeline/Types`→`Structural`→`ScheduledValidation`→`Lowering`→`RouteSpec`; `Compile` imports `Structural`, `Lowering`, `Elab`. `RouteFragments` imports `Pipeline/Types` **only** — `Lowering` imports it, so the reverse edge would cycle. That is why `LHSSlot.toReadIdx` and `producerSlots` live in `Ast.lean`: both `splitStmt` and `physicalizeOne` need them, and only `Ast` is below both.

Cross-layer imports, each deliberate:
- `Structural.lean` → `Eval.Contract` — a spike exception, solely so `Stmt.uids_eq` and six `specsX_map_uid_eq` lemmas can state their RHS against `Eval.Contract`'s real UID collectors. Not a precedent; reverting it means deleting the import with those lemmas.
- `Eval/*` normally imports only `DSL.Ast`/`DSL.Compile`/`DSL.TraverseAxes`/`Pipeline.Types`/`Pipeline.ScheduledValidation`. Exceptions: `Eval/Plan/Compile.lean` imports `Pipeline.Lowering` (reusing `idxToRow`), and `Eval/Plan/Signature.lean` imports `Pipeline.Structural`.
- `Bridge/AcsetCodec.lean`/`Realize.lean` import only `DSL.Target`; `Bridge/Agreement.lean` imports `DSL.Compile` and `Pipeline.RouteSpec`.

## Public API

| Export | Used By | Change Impact |
|---|---|---|
| `tl!{ ... }` macro | any file embedding a TL program | any pipeline-phase change ripples here |
| `TLProgram.compile`/`.compileToScheduled` | `tl!` macro; `Eval/` | central pipeline-order contract |
| `ThreadedComposed`, `BrBaseP`, `Wire`, `StMatP` (`Target.lean`) | `Bridge/*`, `Eval/*` | stable wire format to downstream layers — treat as an ABI |
| `route`/`routeCore`/`buildStep` (`Lowering.lean`) | `Bridge/Agreement.lean`, `RouteSpec.lean` | a signature change invalidates the B.1–B.7 lemmas |

### Core Types
- `TLProgram { decls, stmts }`; `Stmt = assign | scatter | recurMorphism`; `LHSSlot = free | freeNorm | iterAt | iterNext | affine`; `Nonlin = identity | pointwise PointwiseFn | axiswise AxiswiseFn (Option BoolExpr)`; `AxisKind = real | nat` (no size payload).
- `Decl = tensor | typedTensor TensorElementType .. | predicate | linear | axis | iter`; `TensorElementType = f32`. **`typedTensor` is the one extensible typed-declaration constructor** — a future `complex64` extends `TensorElementType`, not `Decl`. It is tensor-bearing everywhere `Decl.tensor` is, so every traversal must handle it; a wildcard arm silently loses the declaration.
- `ScanStmt = plain Stmt | scan name axes base recur isAffine | scanPre` — `finalizeScans`' grouping of coupled recurrences.
- `ThreadedComposed { steps; routing; nExternal }`; `Wire = external Nat | internal Nat Nat`; `StMatP { domLen codLen; coeffs; bias }` with `.wellFormed`/`.validate`.

### ScheduledProgram consumers
- `prepareEvalPlan` and `evalScheduled` are the two public preparation/execution boundaries. Both require `validateScheduled` and consume its declarations, explicit sizes, external-name order, and original statements. Its topology advances by `ScanStmt.outputs`, not `writes`: recurrence scratch stays block-local, plain statements cannot read their own destination, and scan-internal dependencies remain legal.
- `schedule` establishes the invariant for source programs. `capabilityPreflight` and `orderedExtNames` run only after the checked boundary.
- `elaborateAffineReindexings`, `routeCore`, `routeNameInventory`, `physicalizeRaw`, `physicalizeForRoute`, `route` are routing-local; they never invoke evaluation validation.
- `PropertyOracle.independentRun` is an independent oracle with a valid-source precondition; its scan-free calls reach the shared boundary through `evalScheduled`.

## Pipeline Order
`tl!{...}` (`Compile.lean`): parse → `assignUIDs` (one fresh UID per distinct axis name) → `resolveDecls` (external vs. produced names) → `reclassifyIterSlots` (promote `.affine (.shift a 1)` to `.iterNext` iff `a` is declared `iter`, else `scanAxisNotIter`) → `checkReadRanks`/`checkDtypes`/`checkScatterNonlin` → `lowerArith` (Phase 4: affine/diagonal LHS → `.scatter`; reject non-injective scatters without `reduce sum`) → `finalizeScans` (Phase 5: group `iterAt`/`iterNext` into `ScanStmt.scan` by shared iteration-axis UID) → `schedule` (Phase 6: topological sort; the LOGICAL `ScheduledProgram` that `compileToScheduled` returns) → `route` (Phases 7–8: `physicalizeForRoute` expands each nonlinear plain statement into a private producer/consumer pair, then `nameToStep`/`extIndex` and the `buildStep` fold produce `BrBaseP` steps + `Wire` routing).

## Entry Points
| Task | Start Here |
|------|------------|
| Add surface syntax | `Syntax.lean`, then `Elab.lean`, then `Ast.lean` for the target type |
| Add a compile phase / validation | `Pipeline/Structural.lean` (validation) or `Pipeline/Lowering.lean` (transforming) |
| Debug a routing/`buildStep` proof | `Pipeline/RouteSpec.lean` — find the B.\* lemma covering the change |
| Change the routed-DAG wire format | `Target.lean` — ripples into `../Bridge/AGENTS.md` and `../Eval/AGENTS.md` |
| Add a tensor element type (`complex64`, …) | `Ast.lean`'s `TensorElementType` + `storageConstraintOfDecl`, then `Syntax.lean`/`Elab.lean`. **Read `papers/f32_evalplan.md` §1.1–§1.3 first**: `f32` changes representation, not scalar domain, which is why the categorical branch may erase it; complex is a different domain, so do not generalize that erasure |
| Find where a declared `f32` executes | not here — see `../Eval/Plan/AGENTS.md` (`scheduleStorageKind` derives the kind here; `checkAssignF32`, `Dense32.lean`, `Adapter32.lean` run it) |
| Why was a nonlinear or scatter statement rejected at route time? | `RouteFragments.lean`'s ten-class table, below |

### Physicalization classes (`RouteFragments.lean`; `papers/nonlinearity_split_pair_direct_lowering.md` §2.4)
Every input class is classified explicitly by `fragmentClass`; no catch-all arm exists.

| # | Input class | From surface `compile`? | Handling |
|---:|---|---|---|
| 1 | `.plain (.assign …)`, `.identity` | yes | copy, width 1 |
| 2–4 | `.plain (.assign …)`, `.pointwise` / `.axiswise _ none` / `.axiswise _ (some mask)`, not `slotsBecomeScatter` | yes | split, width 2 (a mask rides the consumer) |
| 5 | `.plain (.scatter …)`, `.identity` | yes | copy, width 1 |
| 6 | nonlinear `.scatter`, or nonlinear `.assign` with `slotsBecomeScatter` | no — `checkScatterNonlin` rejects first | **rejected**, `unsupportedNonlinScatter`; never copied |
| — | nonlinear `.plain (.assign …)` carrying `.iterAt`/`.iterNext` (hand-built only) | no | **rejected**, `unsupportedNonlinIterSlot` (`slotsCarryIterSlot`) |
| 7 | `.plain (.recurMorphism …)` | no — `unsupportedRecurMorphism` | copy, width 1 |
| 8–9 | `.scan …` (either `isAffine`) | yes | copy verbatim, width 1 |
| 10 | `.scanPre …` | hand-built only | copy verbatim, width 1 |

## Contracts
- **Proved** (real proof bodies): `dedupByUid_uid_nodup`; `reindexing_wellFormed`; B.1 `buildNameToStep_lt`/`_slot_lt`; B.3 `routeCore_routable`; B.5 `buildStep_wires_mapM`; B.6 `buildStep_inputWeaves`; B.7 `buildStep_output_fixedAxes` (via `outputAxesConsistent` + `fixedAxesP_mapWeave_pos`); M3 `buildStep_output_reducesOnlyContracted`; `buildExtIndex_injective`/`_lt_card`.
- **Conditional gap — `ScanStmt.readArityOk`** (`Lowering.lean`): every internal read's index count matches its producer's rank. It is an UPSTREAM property (`checkReadRanks`/`env`), not derivable at the routing layer; `buildStep_reindexings_codLen_eq_inputRank` takes it as a hypothesis. Track A is complete modulo this; don't try to "finish" it without a separate upstream effort.
- **Physicalization width is tied by proof only in one direction.** `physicalizeOne_length_eq_fragmentWidth` holds on every class `physicalizeOne` accepts, so emitting the wrong number of statements fails to compile. It is conditional on `.ok`, so it is vacuous on reject classes: relaxing class 6 to `.copy` in `fragmentClass` while `physicalizeOne` still throws typechecks. The guard for that direction is `test/DSL/Pipeline/RouteWeaveTest.lean` fixtures 13 (`.scatter` door), 14 (`.assign` door), 15 (the `[.free a, .freeNorm a]` diagonal), 16 (iteration slot).
- **Class 6 is rejected even though `checkScatterNonlin` already runs first**, because `physicalizeForRoute` accepts a logical schedule from any caller, including hand-built ones; copying such a node would route it with the nonlinearity silently absent. `LHSSlot.toReadIdx` maps `.affine _ => none` and collapses `.iterAt`/`.iterNext` to a plain axis, which is why those doors must reject rather than split.
- **`slotsBecomeScatter` treats `.free` and `.freeNorm` alike** — `LHSSlot.freeUID?` returns the UID for both, so `Y[i, i]` and `Y[i, i.]` are the same diagonal LHS. The one reader of the marker's VALUE is `LHSSlot.normUID?`, read only by `normAxisUidOf` in `Eval/Slots.lean`.
- **A nonlinear statement's producer half must not carry `.freeNorm`.** `physicalizeOne` (and the regression-only `splitStmt`) build the producer's slots through the shared `producerSlots` (`Ast.lean`), which degrades `.freeNorm → .free`; the consumer keeps the marker, which is what `Eval/Plan/Compile.lean`'s `resolveNonlinAxis` needs. This is safe because no `normUID?` reader sees a physicalized schedule: `normAxisUidOf` is used only in `Eval/`, and nothing in `Eval/` calls `physicalizeForRoute`. A new marker-value reader that runs after `route` breaks that; re-check before adding one. Fixtures: `test/Eval/Plan/NonlinCompileTest.lean`'s end-to-end `normalize`/`softmax`/`l2normalize`.
- **Scans are copied verbatim by physicalization** (classes 8–9), unlike the old `splitScan`, which split nonlinearities inside scan bodies. It is still route-equal because scan routing is opaque. Assert both physical conservation and categorical projection equality (`RouteWeaveTest.lean` F7/F8/F9).
- **`outputAxesConsistent`** (inside `buildStep`) makes a coupled scan whose OUTPUTS disagree on shared-axis order (`G[j,l]` vs `H[l,j]`) a compile error (`inconsistentScanAxes`). It is what makes `ScanStmt.slotWeave`'s canonical order sound, and changing that order ripples into `Bridge/Agreement.lean`'s `wf_typeMatch`. It compares outputs of an already-grouped scan; nothing in `finalizeScans` checks that a base case and its recurrence agree on slot order.
- **A declaration selects PRECISION, and `predicate` selects nothing.** `storageConstraintOfDecl` maps `typedTensor .f32` to `.float32`, `tensor`/`linear` to `.float64`, `predicate` to `none` (Boolean is an algebra tag over the graph's real carrier). `storageConstraintOfName?` makes an undeclared external real `f64`, so every real external in an f32 graph must be declared `tensor f32`. `scheduleStorageKind` scans in USED-NAME order (`orderedExternalNames`, reads then writes, scan scratch included) and names the FIRST conflict. A scan contributes `ScanStmt.writes` (not `outputs`), so block-local scratch constrains precision. Unused declarations select nothing: a stray `tensor f32 Unused(i)` must not reject an f64 program.
- **Scan iteration axes must be declared `iter l = N`** — the only way; `axis l : ℕ = N` does not suffice. `ident "+1"` and `+ 1` elaborate identically to `.affine (.shift a 1)`; `reclassifyIterSlots` then promotes to `.iterNext` iff the axis is declared `iter`, else `scanAxisNotIter`. Coverage: `test/DSL/IterDeclTest.lean`.
- **Axis extents come only from declarations, never from the kind.** `AxisKind` carries no size (`axis l : ℕ[3]` does not parse). `declaredAxisSizes` (`Structural.lean`) folds `.axis ax (some n)` and `.iter ax n`; a "is this axis sized?" check must test the `Decl` payload.
- **A scan base case does not name its iteration axis**: `G[j, 0]` elaborates to `.iterAt` on an axis named `""`, which `adoptBaseIterAxes` recovers from the matching step by slot position. Surface programs cannot make this silent — `assignUIDs` gives `""` its own distinct UID, so an un-adopted base fails loud as `missingBaseCase` or `inconsistentScanAxes`. A hand-built AST bypassing `assignUIDs` could; don't detect the placeholder by `uid == 0`.
- **Scatter + nonlinearity is rejected** by `checkScatterNonlin` (and defensively by `Eval/Scatter.lean`'s `evalScatter`): `Out[2*i] := relu(X[i])` once compiled and silently dropped the `relu`. This is a short-term policy; real support needs a decision on activating before vs. after collision reduction. Scatter-shaped scan-state writes are admitted only through the narrow checked-scan geometry — see `../Eval/Plan/AGENTS.md`.

## Pitfalls
- **`traverseAxes` is canonical** — `mapUID`/`specs*` are thin instantiations of it; `unifyAxes`, `Exec/Context.lean`, and the `*_eq_old` scaffolding are deleted.
- **`schedule` fails loud on cycles** — the underlying `topoSort` silently falls back to source order; `schedule` re-checks with `isTopoOrdered` and throws `cyclicDataflow`.
- **`f32` is a GLOBAL parser token** — a Lean identifier named `f32` no longer parses anywhere downstream of `DSL/Syntax.lean`; write `«f32»`. A future element-type keyword will do the same to its spelling.
- **`relu(where=...)` is unrepresentable by design** — only `tl_axiswise_kw` has a mask clause; `tl_pointwise_kw` does not.
- **The producer/consumer split's `.freeNorm` degradation is safe only by phase order** — read the Contracts entry before adding any reader of a slot's norm marker.

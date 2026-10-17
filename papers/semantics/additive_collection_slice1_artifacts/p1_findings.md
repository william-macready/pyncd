# P1 findings (additive collection, slice 1 prototype)

Branch `proto-additive-slice1-p1`, three prototype commits on main `b0d37f2f`, exported as
`p1_patches/0001..0003` by `git format-patch main..HEAD` (generated from real commits, so they apply in
order onto `b0d37f2f`). Final tree: `lake-build.sh … LeanNCD Eval.CollectEvalTest DSL.Pipeline.CollectTest
Eval.Plan.ContractTest DSL.Pipeline.RouteFragmentCorpusTest` green. Full `Tests` after T3: the only
failures are the P2-owned ones listed in (b).

Shape of the change:
- `DSL/Pipeline/Collect.lean` (new; imports `RouteFragments` only): `collectorName`, `Decl.cloneAs`,
  `WriterGroup`, `writerGroups`, `checkWriterGroup`, `collectorStmt`, `desugarMultiWriters`.
- `Exec/Uid.lean`: `CompileError.multiWriterScatter | multiWriterAlgebra | writerShapeMismatch T k pos |
  reservedNameCollision`.
- `ScheduledValidation.lean`: `ScanStmt.publications`, all-writers `eligible`; `collectDefinitions`
  (= `desugarMultiWriters` + `isTopoOrdered` assertion); `CheckedScheduledProgram.privateNames`;
  `validateScheduled` returns the COLLECTED program.
- `Eval/Error.lean` `EvalError.inputIsDefined`; `Eval/Eval.lean` `evalScheduled` B3 check + erasure.

## (a) §2 sibling audit — "writers of a name" / "what a statement writes"

Classes: **R** required-to-change in slice 1, **F** forbidden-to-change (must stay as is), **S**
silently-ignored-today (multi-writer input handled by last-wins/first-wins without diagnosis: candidate
bug). "Post-P1" says what happens now that P1 is in.

| Function @ file | What it computes | Single writer | Multi plain-assign writers | Multi incl. scatter | Plain + scan writer | Post-P1 |
|---|---|---|---|---|---|---|
| `ScanStmt.writes/outputs/reads` @ ScheduledValidation | per-node names | F | F | F | F | unchanged; `publications` added beside |
| `routeWrites/routeOutputs/routeReads` @ RouteFragments | route copies (pinned by `routeWrites_eq` etc.) | F | F | F | F | unchanged, reused by the collector |
| `eligible`/`topoSortFuel`/`isTopoOrdered` @ ScheduledValidation | readiness | F (same verdict) | **R** (was any-writer: S) | **R** | **R** (reader waits for both; was any-writer) | changed |
| `schedule` @ Lowering | topoSort + assert | F | **R** (reorders via topoSort) | R | R | changes through `topoSort` only |
| `orderedExternalNames` @ ScheduledValidation | reads minus writes | F | F | F | F | unchanged (T#k are written) |
| `scheduleStorageNames/Constraints/Kind`, `scheduleFloat32Name?` @ ScheduledValidation | storage over used names | F | F (clones carry storage) | F | F | sees `T#k` with cloned decls |
| `externalReadNames` @ Structural | reads minus writes | F | F | F | F | — |
| `checkReadRanksIn` `producedRank` @ Structural | rank of a produced undeclared name, `HashMap.insert` fold | F | **S** (last writer's rank; a reader is checked against it only) | S | S | still S, but run on the ORIGINAL program before collection; `writerShapeMismatch` now covers rank disagreement for plain-assign sets (a reader may report `rankMismatch` first) |
| `checkReadRanksIn` declared-destination LHS arity | per statement | F | F | F | F | — |
| `checkPredicateOutput(s)` @ Structural | per statement | F | F (collector is identity/sum, passes) | F | F | — |
| `stmtLhsRank` @ Structural | published rank of one stmt | F | F | F | F | — |
| `finalizeScans` / scratch absorption @ Structural | groups scans; absorbs plain readers of scan state | F | F | F | F (fail-loud `duplicateScratchProducer`, per brief) | not touched (note §C.9) |
| `buildNameToStep` @ Lowering | name → (step, slot), `HashMap.insert` fold | F | **S** (last writer wins: reader wired to last writer, earlier writers dead steps) | S | S | **still S on `route` until P2 inserts `collectDefinitions` before `physicalizeForRoute`**; also duplicate `outputs` of one scan (`[G,G]`) map to the last slot (pre-existing) |
| `routableInOrder` @ Lowering | backward wires | F | S (inherits buildNameToStep) | S | S | P2 |
| `routeNameInventory`/`routeName` @ RouteFragments | freshness inventory | F | F | F | F | collector reuses inventory; route names computed after desugar must stay so (P2) |
| `physicalizeRaw`/`physicalizeForRoute` @ RouteFragments | per-statement fragments | F | R (must see collected program) | R | — | P2 |
| `scatterOutputShapes` @ Eval/SizeInfer | scatter extents, `HashMap.insert` fold | F | F | **S** (last scatter's extent) | F | multi-writer scatter now rejected before it runs |
| `inferAxisSizes` @ Eval/SizeInfer | sizes from inputs/scatter outputs | F | F (T#k reads are bare, no new size source) | — | — | — |
| `evalScheduled` env fold @ Eval/Eval | `env.insert` per statement | F | **R** (was last-wins: S) | R (now rejected) | S in P1 (collector skipped scan-written names) -> **R in P2a-T0**: `desugarMultiWriters` rejects it outright as `CompileError.multiWriterScan` (plain + scan, and scan + scan), before any fold runs | changed: collected program + erasure + B3 |
| `combineFor`/`isPredicateDest` @ Eval/Contract | algebra from destination decl | F | F (clones keep predicate) | F | F | — |
| `evalScan` duplicate checks @ Eval/Scan | in-scan writers | F | F | F | F | — |
| `slotOf` rebinding @ Eval/Plan/Compile | fresh slot per statement | F | S (last wins) → R in P2 | S | S | prepareEvalPlan already consumes the collected program (one writer per public name); hiding is P2 |
| `materializedNames` push sites @ Eval/Plan/Compile | persistent outputs | F | **R** (must omit `T#k`) | — | — | **P2**: currently lists `Y#1, Y#2, Y` |
| `unpack`/`unpack32` @ Eval/Plan/Adapter(32) | last-wins fold | F | moot once one binding per name | — | — | P2 |
| `orderedExtNames` @ Eval/Plan/Compile | ext names | F | F | F | F | — |
| `capabilityPreflight` @ Eval/Plan/Compile | per-statement | F | F | F | F | — |
| `duplicateDestination` @ Eval/Plan/Block | raw plans only | F | F | F | F | — |
| `checkStructure` @ Semantics/Source/NumericalProfile | `crossStatementOverwrite` refusal | F | **R** (remove refusal) | stays refused (Admission refuses scatter) | — | **P2** |

Candidate bugs (S cells that survive P1): `buildNameToStep` last-wins on `route` (closed by P2's route
integration); `producedRank` last-wins (masked by `writerShapeMismatch`, but a reader can still be
rank-checked against only the last writer); plain + scan writer of one name in `evalScheduled` (collector
skipped it in P1; CLOSED in P2a-T0 by `multiWriterScan`, controller answer to Question 6).

## (b) P2 must handle

1. `route` (`DSL/Pipeline/Lowering.lean`): call `collectDefinitions` before `physicalizeForRoute`. Between P1
   and P2, `T:=A; U:=T; T:=B` is reordered by `schedule` to `[T,T,U]` and `route` wires `U` to the LAST
   writer through `buildNameToStep` (silent last-wins; previously `cyclicDataflow`). Not probed through
   `route`; inferred from `buildNameToStep`'s `HashMap.insert` fold.
2. `prepareEvalPlan` (`Eval/Plan/Compile.lean`): it already compiles `checked.program` (collected); it must
   omit `checked.privateNames` from `materializedAcc` (push sites in the materialization loop; assembled into
   `PlanBindings.materializedNames`). Observed failures caused by P1 (all P2-owned):
   - `test/Eval/Plan/CompileTest.lean` repeat-assignment block (`repeatPrepared`, `repeatPredPrepared`,
     `repeatPredBadSlot`, `repeatPredTrailingBadSlot`): `materializedNames == ["Y","Y","Z"]`, signature list,
     `tensorSigs.size == 5`, and `slotOutOfRange … 5` expectations fail (5 guards).
   - `test/Eval/Plan/DifferentialTest.lean` repeated-assignment case: `DISAGREEMENT (env) between
     runPreparedDense and evalScheduled` (the plan exposes `Y#k`; the reference hides them).
   - `Adapter32Test.lean` (~L118-150) not observed failing in the Tests run (check whether it asserts two `Y`
     entries by a path the run did not exercise).
3. B3 on the checked side: `runPreparedDense`/`runPreparedDense32`/`unpack` still accept a supplied input
   naming a defined tensor. `CompileTest` ordered twin now passes `topologyInputs.erase "Z"` to
   `evalScheduled` only; its `runPreparedDense prepared topologyInputs` still supplies `Z` and must change
   when P2 adds the checked rejection. Name the checked error and make both backends reject the same
   programs (the reference uses `EvalError.inputIsDefined`, first defined name in schedule write order).
4. `Semantics/Source/NumericalProfile.lean` `checkStructure`: remove the `crossStatementOverwrite` refusal.
   Observed failing after P1: `SourceDifferentialPolicyTest` `F14`, `F15` (`did not evaluate to true`),
   `SourceDiagnosticAdmissionTest` `D10` (L178). Expected new values: F14 [7,13], F15 [12,22] (both also
   observed through the reference as V1/V2).
5. Bridge/Agreement and `BrOp` labels: the collector is an `.assign` with `agg := .sum` and identity
   nonlinearity, so `toBrBaseP` labels it `.contract`; verify Agreement lemmas over routes with collectors.
6. The JAX runtime (`experiments/jax_bridge/evalplan_affine_runtime.py`) last-wins fold: moot only after (2).
7. f32 checked path (user constraint): test on `runPreparedDense32`/`Adapter32`/`Dense32`/`checkAssignF32`
   with `tensor f32 Y(i)` and with undeclared (default-f32) multi-writer `Y`: (i) the V5 non-integral
   3-writer order fixture in f32 (expect source-order fold; derive the f32 bit pattern from a run, it differs
   from binary64); (ii) V4 predicate OR on an f32 schedule (predicate is storage-neutral, clones are
   `.predicate`); (iii) private names absent from `unpack32` output; (iv) no `mixedStorageKinds` from
   `T#k` (clones carry T's storage; undeclared T and undeclared T#k both default to f32).

## (c) Questions for the controller

1. **Placement of the topological assertion.** Note §C.3 puts "assert `isTopoOrdered`" inside the collector,
   but `isTopoOrdered` lives in `ScheduledValidation.lean`, which must import the collector (it calls it from
   `validateScheduled`, whose structure has a private constructor). I split it: the desugar is
   `desugarMultiWriters` in `Collect.lean`; `collectDefinitions` (the note's name and signature) is a thin
   wrapper in `ScheduledValidation.lean` that adds the assertion. `route` (P2) should call
   `collectDefinitions`. Accept, or move the topology helpers into `Collect.lean`?
2. **`.plain (.recurMorphism …)` writers.** The note does not cover them. `writerGroups` skips a name that
   any `.recurMorphism` writes (like a scan writer), because every entry already rejects the escape hatch.
   Alternatively reject as a new error. Decide.
3. **`.plain (.assign …)` with an `iterAt`/`iterNext` slot in a multi-writer set** (hand-built only): I
   report `writerShapeMismatch T k pos` at the first non-bare slot. An `.assign` with an `.affine` slot or a
   repeated free UID (diagonal) is reported as `multiWriterScatter` (`slotsBecomeScatter`). Confirm.
4. **Rejection order.** Per group, all writers are checked for scatter first, then algebra, then shape; groups
   in first-writer order; freshness after all groups. A reader whose arity differs from the last writer can
   still report `rankMismatch` (from `checkReadRanks`, which runs first on the original program) before
   `writerShapeMismatch`. Acceptable?
5. **Where B3 lives.** I made it `EvalError.inputIsDefined` (an input-binding error), checked after the f32
   check and before size inference, not a `CompileError`. The note gives only the name. Confirm the family.
6. **Plain + scan writers of one name** on a hand-built schedule whose plain writer is not absorbed as
   scratch: the collector skips the name (note §C.9) and readiness makes a reader wait for both, but
   `evalScheduled`'s env fold would then still be last-wins. The brief's verification (`duplicateScratchProducer`)
   covers the surface case only. Not probed (budget). Should `collectDefinitions` reject it outright
   (`multiWriterScan`), rather than "do nothing"?
7. **Clone placement.** Clones are appended to `decls` (after all source declarations), not next to `T`'s
   declaration. Nothing reads declaration order for tensors except `combineFor`'s first-match scan, which is
   unaffected because names are distinct.

## (d) Budget

Roughly 75 tool turns against the ~60-turn budget: a breach of about 25%. The main causes were two full
`Tests` runs (~25 min each, waited on in 10-minute blocks) and the harness refusing compound shell commands
(several were retried). I did not measure peak context; it stayed well under 250k by estimate (no large file
dumps). I did not run `token-report.py`, because I have no session id.

## (e) Deviations from the decision note

- `collectDefinitions` is split as described in Question 1. Its signature and name match the note; the pass
  itself is `desugarMultiWriters`.
- `CheckedScheduledProgram.privateNames : List String` was added as specified. The note's `algebras` field
  (A3) is S3 and was not added.
- Readiness counts **nodes**, not output occurrences: `ScanStmt.publications = outputs.eraseDups`. The note
  says "number of emitted publications equals number of nodes that write r". Without the dedup, a 2-D scan
  with two base faces (`outputs = [G, G]`) would never be ready (fixture R4; mutation observed).
- `validateScheduled` runs the source checks (`buildDeclEnv`, `checkScheduledReadRanks`,
  `checkScheduledDtypes`, `isTopoOrdered`) on the ORIGINAL program. It then collects and rebuilds
  `declEnv`/`explicitSizes`/`extNames` from the COLLECTED program. `program` is the collected schedule, so
  `prepareEvalPlan` compiles it too (P1 does not touch the checked plan's code, but its behaviour changes).
- f32 (user constraint 2026-10-14): a declared `T` gets one clone per writer with the same constructor and
  element type (C4b pins `tensor f64`; `tensor f32`/`.tensor`/`.linear` clone the same way through
  `Decl.cloneAs`). An undeclared `T` gets no clone (note §C.4). That is safe because undeclared `T` and
  undeclared `T#k` both default to f32, so no `mixedStorageKinds` can arise. A predicate `T` gets predicate
  clones, which are storage-neutral like `T`. The default-f32 rule does not change which names count as
  declared: cloning keys only on an explicit tensor-bearing declaration of `T` (`declaredTensorName?`).
  Under `explicitF64`, every undeclared name, `T` included, becomes declared `tensor f64` before scheduling,
  so evaluator fixtures always exercise the clone path. In the reference evaluator the collector behaves
  identically for f32- and f64-declared `T` up to the f32 refusal: both f32 variants are refused as
  `unsupportedDtype` naming the first used f32 name (the external `A`), never a `T#k`. f32 numerics are P2
  (item b7).
- B3 uses `ScanStmt.writes` of the collected program, so a supplied input named `T#k` is also rejected.

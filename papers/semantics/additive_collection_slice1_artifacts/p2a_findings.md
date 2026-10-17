# P2a findings (additive collection, slice 1 prototype)

Branch `proto-additive-slice1-p2a`, on `proto-additive-slice1-p1` (tip `5861a282`), commits
`proto: P2a-T0 …`, `proto: P2a-T1+T2 …`, `proto: P2a artifacts`; patches in `p2a_patches/`
(`git format-patch proto-additive-slice1-p1..HEAD`; they apply on top of the P1 branch). Values, mutation
strings and donors are in `p2a_observed.md`.

## What was built

- **T0.** `CompileError.multiWriterScan : String → …` (`Exec/Uid.lean`); `scanWriterConflict?`
  (`DSL/Pipeline/Collect.lean`), called first in `desugarMultiWriters`: a name written by two or more
  nodes of which one is a scan node (`.scan`/`.scanPre`; plain + scan AND scan + scan) is rejected. A
  single scan writing a name in both halves stays one writer (`routeWrites` dedups). `writerGroups`
  keeps skipping `.recurMorphism` writers (controller answer 2). Fixtures C9, C9b, accept-neighbour C9c.
- **T1.** `prepareEvalPlan` (`Eval/Plan/Compile.lean`) splits the collector's private names off at Step F:
  `PlanBindings.materializedNames` holds public names only, new `PlanBindings.privateSlots :
  Array TensorSlot := #[]` records the hidden publication slots, and `checkPreparedBindings`
  (`Eval/Plan/Prepared.lean`) now requires the visible slots to equal the raw publication sequence
  (`rawPublicationSlots`) minus `privateSlots`; a hidden slot the raw plan never publishes is the new
  `PreparedBindingsError.privateSlotUnpublished`. `materializedSignatures` and `unpack`/`unpack32` consume
  only the visible bindings, so they list only public names with no further change.
- **T2.** `PlanBindings.definedNames : Array String := #[]` (every name the schedule writes, private and
  scan scratch included, first-write order) and `InputBindingError.inputIsDefined (name : String)`
  (`Eval/Plan/Error.lean`), raised by `packBodyOf` (all of `pack`/`pack32`/`runPreparedDense*`) and, for a
  direct call, by `unpackBodyOf` as `PlanRunCause.binding (.inputIsDefined nm)`; helper
  `firstDefinedInput?` (`Eval/Plan/Adapter.lean`). Family chosen by reading how `pack` reports a missing
  input (`InputBindingError.missingEnvBinding`) and how the other input-binding failures are wrapped
  (`PlanRunFailure.cause = .binding …`).
- New test module `test/Eval/Plan/CollectPlanTest.lean` (in `lakefile.toml` globs); migrated
  `CompileTest`, `DifferentialTest`, `Adapter32Test`; AGENTS.md updated (`Eval/Plan/AGENTS.md`,
  `DSL/AGENTS.md`).

Targeted build/tests green (final tree): `Eval.Plan.CollectPlanTest Eval.Plan.CompileTest
Eval.Plan.Adapter32Test Eval.Plan.DifferentialTest` (including the 3,832-case differential sweep),
`DSL.Pipeline.CollectTest`, and for T0 `DSL.Pipeline.RouteFragmentCorpusTest`, `RouteWeaveTest`,
`ScanAffineTest`, `Eval.ScanTest`, `Eval.CollectEvalTest`, `Eval.Portfolio.RecurrenceTest`.

Full `Tests` run (one, background, on the final source tree; `lake-build.sh … Tests`, 8,799 jobs):
exactly two modules fail, both P2b-owned, nothing else:
- `Semantics.SourceDiagnosticAdmissionTest`: `SourceDiagnosticAdmissionTest.lean:178:0 Expression D10 did
  not evaluate to true`.
- `Semantics.SourceDifferentialPolicyTest`: `:301:0 Expression F14 did not evaluate to true` and
  `:302:0 Expression F15 did not evaluate to true` (the `crossStatementOverwrite` refusal, P1 list (b)4).
`JaxExperiment` (`EvalPlanCodegen`, which builds `PlanBindings` literals) also builds green.

## (a) §2 sibling audit, checked-plan side

Classes: **R** required-to-change in P2a, **F** forbidden-to-change (must stay as is), **S**
silently-ignored-today. "Done" says what P2a did.

| Function (identifier) | What it computes / consumes | Single writer | Multi plain writers | Scatter / scan multi | Supplied input names a defined tensor | Done |
|---|---|---|---|---|---|---|
| `materializedAcc` push sites (plain `.identity`/`.pointwise`/`.axiswise`, `.scatter`, scan states) in `prepareEvalPlan` | persistent outputs | F | **R** (private `T#k` must not be a public output) | F (unreachable: rejected before compile by `multiWriterScatter`/`multiWriterScan`, so no private name can be a scatter or scan-state output) | — | one partition at Step F over all push sites, so no site can forget it (deviation from "omit at the push sites") |
| `PlanBindings.materializedNames` / `privateSlots` | public outputs / hidden slots | F | **R** | F | — | public-only + hidden slots |
| `checkPreparedBindings` (`rawPublicationSlots`, `expected`/`actual`) | binds names to the raw publication sequence | F | **R** (exact-sequence check would reject every collected plan) | F | — | expected = published minus `privateSlots`; junk hidden slot rejected (`privateSlotUnpublished`) |
| `rawMaterializedWith` / `PreparedPlan.materializedSignatures` | name-to-signature table of persistent outputs | F | F (consumes the public list) | F | — | pinned `[("Y",f64)]`, `[("Y",f32)]`, `[("R",bool)]` |
| `unpack` / `unpack32` / `unpackBodyOf` | reported environment (starts from the supplied env) | F | F (last-wins fold moot: one binding per public name) | F | **R** (a supplied defined name is silently overwritten) | B3 check after the storage guard, before the arity check |
| `pack` / `pack32` / `packBodyOf` | resolves required inputs by name | F | F | F | **R** (a supplied defined name is ignored when not required) | B3 check after the storage guard |
| `runPreparedDenseOf` / `runPreparedDense` / `runPreparedDense32` | pack, worker, unpack | F | F | F | R (through the two bodies) | unchanged; the pack door is invisible through it (see mutation), so direct `pack`/`pack32` observers pin it |
| `requiredInputsAcc`, `checked.extNames`, `orderedExternalNames` | external names | F (collector reads are bare, `T#k` are written so never external) | F | F | F | verified by H1/H2/H3 (signatures needed = inputs only) |
| `orderedExtNames` (Compile.lean) | reads minus writes | F | F | F | F | not on the prepare path (`checked.extNames` is used); untouched |
| `InputSignature.ofDenseInputs*`, `prepareEvalPlan` Step B | builds/validates the signature table | F | F | F | **S**: a signature entry naming a defined tensor (a supplied-env name) is silently ignored at prepare; only the run-time check refuses it | NOT fixed (scope; see Questions 3) |
| `PlanBindings` literals in `experiments/jax_bridge/EvalPlanCodegen.lean`, `spikes/` | hand-built bindings | F | F | F | F | unaffected (new fields default to `#[]`); `renderOutputLines` over `materializedBindings` now emits public outputs only |
| `experiments/jax_bridge/evalplan_affine_runtime.py` last-wins fold | JAX output fold | F | moot after this (one binding per public name) | F | — | not touched |
| `evalScheduled` (reference) | env + B3 | F | R (P1) | R (P1; plain+scan rejected P2a-T0) | R (P1) | the reference and the plan now name the same tensor |

## (b) P2b must handle (additions to P1's list)

1. P1's list (b)1 (route), (b)4 (`crossStatementOverwrite`, F14/F15/D10), (b)5 (Bridge/Agreement, `BrOp`)
   stands unchanged.
2. **`route` has no `privateNames` equivalent.** `collectDefinitions` returns the private names; `route`
   (P2) must decide whether routed diagrams expose `T#k` (P1 inferred that diagnostics may). P2a hid them
   only on the evaluator and checked-plan surfaces.
3. **Source-oracle correspondence** (`Semantics/Source` adapters) compares plan/reference environments:
   with hiding both now equal, which is what F14/F15 expect (`[7,13]`, `[12,22]`).
4. **JAX evidence on collected plans** was not probed (the collector is a `.contract`-labelled sum of bare
   reads; `affineReference` runs it as an ordinary assign). `EvalPlanCodegen` emits only visible
   `materializedBindings`, so the JAX output dict has no `Y#k`; whether JAX agreement tests should compare
   the private tensors is a P2b/bridge decision.
5. `multiWriterScan` is a new `CompileError` constructor: any P2b renderer/dispatcher that enumerates
   `CompileError` exhaustively must add it (none exists today; the build is green).

## (c) Questions for the controller

1. **`PlanBindings` grew two fields and `PreparedBindingsError` one constructor.** Hiding by omitting
   private names from `materializedNames` breaks `checkPreparedBindings`' exact publication-sequence
   equality, which is the integrity check that pins which slots are outputs (fixture
   `repeatPredMissingPublication`). I kept it strict and added `privateSlots` (hidden publication slots)
   plus `privateSlotUnpublished`, rather than weakening the check to a subsequence test. `privateSlots`
   is as unauthenticated as the names (a hand-built plan can hide any published slot). Accept?
2. **`definedNames` includes scan scratch and private names**, mirroring the reference's
   `ScanStmt.writes` check so both backends refuse exactly the same environments. A supplied name equal to
   a block-local scratch is therefore refused although scratch is not a persistent output. Accept
   (matches P1's reference behaviour), or narrow both to publications?
3. **B3 is run-time only on the checked side.** `prepareEvalPlan` does not refuse a signature entry naming
   a defined tensor (audit row S). Adding it is one small dispatch (a new `InputSignatureError` arm plus
   f64/f32 fixtures). Park or schedule?
4. **Partition at Step F instead of at each push site** (deviation from the brief's wording; same
   effect, one place). Accept?
5. **T1 and T2 are one commit**: both edit `PlanBindings`/`Adapter`/`Compile`/`CompileTest` and the new
   test module interleaves hiding and B3 fixtures. Split in the plan if per-task review is wanted.
6. The brief's `mixedStorageKinds` is not an identifier; the observed rejection is
   `CapabilityError.unsupportedDtype "<name>: mixed f32/f64 storage in one schedule"`.
7. `multiWriterScan` also rejects two scan nodes writing one name and a plain statement sharing a name
   with scan scratch; no existing test relied on either (see the full-run result above).

## (d) Budget

About 140 tool turns against the ~60-turn budget (a breach of more than 2x). Causes: each source change
below `Exec/Uid.lean`/`Prepared.lean` rebuilds a multi-minute chain, there were 12 single-mutation
builds (each restored), one full-`Tests` run, and the harness refusing foreground sleeps (builds were
polled through monitors). Context peak not measured (no session id for `token-report.py`); estimated
below 250k because no large file dumps were made, but this is an estimate.

## (e) Deviations from the brief

- Hiding is one partition at Step F, not an omission at each push site (above, Q4).
- `privateSlots`/`definedNames`/`privateSlotUnpublished` are additions the brief did not list (Q1/Q2).
- T1 and T2 share a commit (Q5).
- Adapter32Test "does it assert the old two-`Y` behaviour": yes (fixture 4 asserted `["Y","Y","Z"]` and the
  last-write value); migrated. P1 did not observe it failing; I did not investigate why.
- f32 fixtures were derived from runs; the only independent cross-check is that `numpy.float32` left-fold
  arithmetic on the H2 inputs gives the same two bit patterns (1061997773 / 1061997774) as `Dense32`.

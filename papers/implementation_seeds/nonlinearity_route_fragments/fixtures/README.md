# Nonlinearity route-fragment fixture seeds

These files are executable implementation seeds for
`papers/nonlinearity_split_pair_direct_lowering.md`. They import production code but are not imported
by `LeanNCD`, `Tests`, or any production module.

## Artifacts

| Seed | Durable content | Planned destination / lakefile entry |
|---|---|---|
| `FixtureSupportSeed.lean` | Local logical scheduler, collision-free `#` physicalizer, fragment evidence, old/new smoke comparison | `LeanNCD/DSL/Pipeline/RouteFragments.lean`; helpers cloned into `DSL.Pipeline.RouteWeaveTest` |
| `RouteFragmentDiagnosticSeed.lean` | Exactly 19 compile observations, two route-domain observations, and cases 1/2/16 at starts 0/7/41 | `test/DSL/Pipeline/RouteFragmentDiagnosticTest.lean`; add `DSL.Pipeline.RouteFragmentDiagnosticTest` |
| `PayloadConservationSeed.lean` | 19 named payload fixtures; separate physical-conservation and categorical-opacity checks | `test/DSL/Pipeline/RouteFragmentCorpusTest.lean`, `Bridge.AcsetCodecTest`, `Bridge.RealizeTest` |
| `RouteFragmentCorpusSeed.lean` | Deterministic 145 cases/13 families; 137 exact common-domain route+ACSet checks; eight `%nl0` transitions | `test/DSL/Pipeline/RouteFragmentCorpusTest.lean`; add `DSL.Pipeline.RouteFragmentCorpusTest` |

## Donor map

| Seed fixture/family | Donor named by the plan |
|---|---|
| Diagnostic 1–4, 6–9, 11 | `StructuralTest` rank/dtype/predicate/scatter fixtures; `MaxReduceTest` predicate aggregation |
| Diagnostic 10 | `ScatterNonlinRejectTest.RSN1` |
| Diagnostic 12 | `IterDeclTest` undeclared iteration axis |
| Diagnostic 13–14 | `RejectTest.SS4` and `RejectTest.UF5` |
| Diagnostic 15–16 | `LoweringTest` identity cycle plus its two-ReLU mutation |
| Diagnostic 17 | `AcsetCodecTest` causal-attention statement, with no tensor declaration |
| Diagnostic 18–19 | Plan-specified long-`#` and escaped `%nl2` constructions |
| Pointwise payloads | `NonlinCompileTest.reluProg`, with sigmoid/tanh/GELU/leaky-ReLU tags |
| Axiswise payloads | `NonlinCompileTest.softmaxProg`, with normalize/L2-normalize tags |
| Aggregation payloads | `LoweringTest` AGG1, programmatic ReLU-over-max/min |
| Mask payloads | `AcsetCodecTest` causal mask and its negation |
| Iverson payloads | `ParsePredicatesTest.band` and its negation |
| Metadata payloads | `CompileTest.acceptedSched`, varied to tensor/predicate metadata |
| Affine payloads | `LoweringTest` scale/shift reads and `AcsetCodecTest` general affine convolution |
| `scanPre` payloads | `RecurMorphismTest.stepTC`, varied operation/output weave |
| Generated scan families | Public `ScanAffineTest`/`ScanCompileTest` shapes, reconstructed locally; no private `ScanGen.template2` import |

## Exact diagnostic observations

Every row is an executable `#guard`; `@n` is the final `FreshM` state.

| Cases | Old → proposed observation |
|---|---|
| 1 | success `@2` → exact same value `@2` |
| 2–4 | exact `rankMismatch` payloads `@3/@3/@4` → identical errors and states |
| 5 | success `@3` → exact same value `@2` |
| 6–15 | exact named errors and payloads at `@2,@2,@2,@2,@2,@3,@4,@4,@5,@2` → identical |
| 16 | `cyclicDataflow "schedule: cyclic dataflow" @4` → same error `@2` |
| 17–18 | success `@5/@3` → exact same values `@4/@2` |
| 19 | `cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)" @3` → success `@2` |

The two direct-route cases start at 7 and preserve that state: undeclared `Ghost`, and the exact
`wellFormedDom` `shapeMismatch`. Cases 1, 2, and 16 additionally compare the separately spelled
proposed public entry point with its `compileToScheduled >>= route` factorization at starts 0, 7,
and 41.

## Production callers and proof dependencies inspected

- `DSL/Compile.lean` currently runs `splitNonlins` before `schedule`; both `compile` and
  `compileToScheduled` must flip atomically, while retaining exact public composition.
- `Eval/Entry.lean`, PropertyOracle generators/unrollers, and Plan tests consume
  `compileToScheduled`. They need logical-schedule expectation updates; `evalScheduled` itself
  consumes complete `ScheduledProgram` payloads and must not receive a route-only projection.
- `Pipeline/RouteSpec.lean` proves `routeCore`/`buildStep` facts (lengths, routability, weaves,
  reindexings). The transplant must keep `routeCore` physical and its theorem statements unchanged.
- `Bridge/Agreement.lean::compile_eq_route` unfolds `route` and extracts a direct `routeCore`
  witness; it must instead consume the checked physicalizer witness before restoring the unchanged
  `compile_wellFormed` signature.
- `Bridge/AcsetCodec.lean` depends only on `DSL.Target`. Its theorem-level round trip requires
  `WellFormed ∧ WellShaped`; these seeds deliberately perform computational full-value round trips
  and leave theorem plumbing to the Bridge transplant.

## Commands

From the repository root:

```bash
cd leanncd
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/FixtureSupportSeed.lean
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/RouteFragmentDiagnosticSeed.lean
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/PayloadConservationSeed.lean
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/RouteFragmentCorpusSeed.lean
"$HOME/.elan/bin/lake" build DSL.Pipeline.LoweringTest DSL.Pipeline.RouteWeaveTest DSL.Pipeline.ScanAffineTest
"$HOME/.elan/bin/lake" build Bridge.AgreementTest Bridge.AcsetCodecTest Bridge.RealizeTest
"$HOME/.elan/bin/lake" build Tests LeanNCD
```

If `lake` is already on `PATH`, the `$HOME/.elan/bin/` prefix is optional.

## Mutation cycles

The disabled constants are executable production-mutation stand-ins, not comments or assertion
mutations. On 2026-08-25 each listed constant was changed to `true`, the file's direct command was
observed to fail, then it was restored to `false` and observed to pass:

| Seed | Toggle | Guarded defect |
|---|---|---|
| Diagnostic | `enableCheckOrderMutation` | `checkReadRanks`/`checkDtypes` precedence in combined case 4 |
| Diagnostic | `enableExternalArityMutation` | successful routed `nExternal` and public composition |
| Payload | `enableDropMaskMutation` | axiswise mask physical conservation |
| Payload | `enableDropAggregationMutation` | max/min aggregation physical conservation |
| Payload | `enableDropMetadataMutation` | declarations, environment, and explicit-size conservation |
| Payload | `enableReplaceScanPreMutation` | byte-for-byte nested `scanPre` body conservation |
| Corpus | `enableReusePrivateNameMutation` | internal-name injectivity and exact routes |
| Corpus | `enableKeepFreeNormMutation` | producer `.freeNorm → .free` degradation |
| Corpus | `enableRouteFromEntryMutation` | fragment-exit routing and complete route equality |

The remaining planned production cycles map as follows:

1. Restore `splitNonlins` in logical scheduling → logical count/name smoke fails.
2. Generate `maxLen`, not `maxLen + ordinal + 1` → freshness/adversarial-name guards fail.
3. Reuse a private name → branch/corpus exact-route guards fail.
4. Route from fragment entry → chain/corpus exact-route guards fail.
5. Split scan bodies → opaque scan identity/corpus guards fail.
6. Add a second scheduler → composition and collision observations fail.
7. Drop freshness/coverage/exit/topology checking → support evidence or exact route checks fail.
8. Change the rank-error constructor/payload → exact diagnostic case 2 fails.
9. Drop a nontrivial affine read → exact reindexing/route checks fail.
10. Reorder physical fragment steps or recompute externals from private reads → corpus route checks
    fail; these require production mutations because the local adapter intentionally exposes no
    unchecked constructor for either invariant.

## Limitations

- This is a local proposed physicalizer, not proof-carrying production code; Bool checks seed the
  future private constructor and theorems. It records intervals but does not prove them in `Prop`.
- Current production `route` accepts an already-physical schedule. Each seed therefore calls the
  current `route` only after local physicalization; this is deliberately not the final public API.
- The generated scan corpus uses hand-built scheduled nodes to isolate routing. Runtime scan
  admission/publication belongs to later Plan/oracle tests.
- Masks, Iverson predicates, dtype metadata, and nested `scanPre` bodies are preserved physically but
  omitted by today’s categorical projection. Equal routes/ACSets for those pairs are projection
  equality, not semantic equivalence.
- ACSet checks use the current synthetic codec and round trip in memory; CSV I/O and realization
  assertions belong in the planned Bridge tests.
- The corpus checks complete `ThreadedComposed`, routing/domain/weaves/reindexings transitively
  through structure equality, but does not execute `Bridge.realize`; that requires theorem evidence
  and shaped runtime inputs unavailable in this standalone donor.
- Seeds duplicate small local physicalizer functions so each file compiles directly from its final
  path without adding the papers directory to Lake’s module search path.

## Exact transplant order

1. If needed, move `LHSSlot.toReadIdx` from `Lowering` to `DSL/Ast`; do not create a reverse import.
2. Create `DSL/Pipeline/RouteFragments.lean` importing only `Types`; transplant the support
   physicalizer, make `PhysicalRouteProgram` private/checked, and prove preservation, coverage,
   contiguity, freshness/injectivity, unique exits, and physical topology.
3. Make `schedule` consume logical post-`finalizeScans` statements, retain the compatibility alias,
   and keep `routeCore` plus every `RouteSpec` theorem statement physical and unchanged.
4. Change public `route` to checked-physicalize then call `routeCore`; flip `compileToScheduled` and
   `compile` together and prove exact result/error/final-state factorization.
5. Adapt `Bridge/Agreement.compile_eq_route` to extract the physical witness and restore the exact
   public `compile_wellFormed` type before changing downstream consumers.
6. Clone diagnostic cases into `test/DSL/Pipeline/RouteFragmentDiagnosticTest.lean`, replace local
   proposed functions with production APIs, preserve every constructor/payload/state, and register
   `DSL.Pipeline.RouteFragmentDiagnosticTest`.
7. Clone corpus and payload fixtures into
   `test/DSL/Pipeline/RouteFragmentCorpusTest.lean`; reuse production physicalization and retain
   family counts, 137/8 outcomes, 40 opaque scans, 32 split-body observations, and all 19 payloads.
8. Place theorem-level ACSet assertions in `test/Bridge/AcsetCodecTest.lean` and shaped realization
   assertions in `test/Bridge/RealizeTest.lean`; never relabel projection equality as semantics.
9. Update `Eval/Entry`, Plan, PropertyOracle, and scan expectations only after the logical boundary
   is live. Run every mutation as mutate/fail/restore/pass, targeted entries, then
   `lake build Tests LeanNCD`.

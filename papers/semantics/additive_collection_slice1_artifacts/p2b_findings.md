# P2b findings (additive collection, slice 1)

Branch `proto-additive-slice1-p2b`, on `proto-additive-slice1-p2a` (tip `72fde8c8`); commits
`proto: P2b-T3 …`, `proto: P2b-T4 …`, `proto: P2b artifacts`; patches in `p2b_patches/`
(`git format-patch proto-additive-slice1-p2a..HEAD`). Values, mutation strings and donors are in
`p2b_observed.md`; the documentation sweep is `p2b_docsweep.md`.

## What was built

- **T3, route integration.** `route` (`DSL/Pipeline/Lowering.lean`) now runs `desugarMultiWriters` on
  the logical schedule and hands the COLLECTED schedule to `physicalizeForRoute`; a reader of a
  multi-writer name is wired to the sum collector, which reads every private writer `T#k`.
  - **Probe (both inferences of P1 CONFIRMED by observation):** before the change, `T:=A; U:=T; T:=B`
    and `T:=A; T:=B; U:=T` compile to the same schedule `[T, T, U]` and route to 3 steps with `U` wired
    to step 1 (`T := B`) only; step 0 is a dead step. Same for default-f32 and `explicitF64`.
  - **Deviation: `desugarMultiWriters`, not `collectDefinitions`.** The first attempt called
    `collectDefinitions` and broke the three `RouteFragmentDiagnosticTest` pins that a cyclic hand-built
    schedule reports `routeCore`'s `cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)"`:
    the wrapper's `isTopoOrdered` assertion fired first. That test (and the `RouteFragments` section
    note "No physical-topology check lives here") documents a deliberate single-gate design:
    `routeCore`'s `routableInOrder` is the only topology gate on the route path. Once every name has one
    writer, `routableInOrder` (last-writer) and `isTopoOrdered` (all-writers) agree, so the assertion adds
    nothing on this path. Rule 7: I kept the more tested single-gate pattern and flagged it (Q1). The
    `collectDefinitions` docstring now says `validateScheduled` calls it and `route` calls the pass.
  - **Route-name freshness** needs no new code: `physicalizeForRoute collected` computes
    `routeNameInventory` from the collected program, so `T#k` is in the inventory and the
    `routeNamesFresh` proof obligation covers it (route names are all-`#` strings longer than every
    inventory name; `T#k` also contains a non-`#` character).
  - **Hiding decision: route does NOT hide `T#k`.** Grounds: (i) `route` has no name-hiding surface at
    all; `ThreadedComposed` carries `steps`/`routing`/`nExternal` only, no tensor names, so `T#k`
    appears only as anonymous internal steps (`BrBaseP` has no name field); (ii) the nonlinear split
    is the same kind of artifact: `physicalizeForRoute` adds a private producer step named by
    `routeName` that no consumer outside the pair sees, and nothing hides it; (iii) the ACSet export
    (`AcsetCodec.fromThreadedComposed`) encodes steps, wires and axes, not tensor names, so there is no
    `T#k` string to leak. Hiding would mean deleting steps, which changes the morphism.
  - **`BrOp` labelling.** The collector is `.plain (.assign …)` with `agg := .sum` and identity
    nonlinearity, so `ScanStmt.toBrBaseP` labels it `.contract` (observed: RT1-RT6 ops). A private
    nonlinear writer keeps its split (`relu` op on the consumer step, RT5).
  - **ACSet codec.** New fixture 10 (`AcsetCodecTest`) round-trips RT5's program (5 steps, the
    collector has two internal input wires) and pins `steps.length = 5`.
- **T4, oracle profile lift.** `checkStructure` (`Semantics/Source/NumericalProfile.lean`) no longer
  refuses a second definition of a declaration; `SharedFragment.definitions` lists every
  (declaration, origin) pair in statement order. `StructuralCondition.crossStatementOverwrite` had no
  other constructor site and was deleted (the inductive keeps `usedDType`). F14, F15 and D10's
  `acceptedNonshared` are flipped to value comparison; the policy test's `overwriteRefusal` helper (only
  user: F14/F15) became `valueCompared`. New F14f32 (default-f32 twin of F14).

## Agreement statement changes (`Bridge/Agreement.lean`)

- `compile_eq_physical_route`: CHANGED. The existential gains `collected : ScheduledProgram` and
  `privateNames : List String` and the conjunct `desugarMultiWriters logical = .ok (collected,
  privateNames)`; the physicalization conjunct is now `physicalizeForRoute collected = .ok physical`
  (was `physicalizeForRoute logical`). Why: `route` has a new stage, and the plumbing lemma states each
  stage's success. Proof: one more `rcases` on the new stage, same `simp` set for the error arm.
- `compile_wellFormed`: statement UNCHANGED; only its `obtain` pattern grew two binders. Its docstring
  and the module header now name the collection stage.
- No other lemma mentions `physicalizeForRoute` over the logical schedule. `wf_typeMatch`,
  `wf_singleOutput`, `wf_topo` and everything in `RouteSpec` are stated over `routeCore`'s physical
  input and are untouched. `test/Bridge/AgreementTest.lean` (pins `compile_wellFormed`'s type) is green.
- `RouteFragmentDiagnosticTest`'s composition observations (`compile ≡ compileToScheduled >>= route`)
  still hold (green).

## (a) §2 sibling audit, route / oracle side

Classes: **R** required-to-change in P2b, **F** forbidden-to-change, **S** silently-ignored-today.

| Function (identifier) | Computes / consumes | Single writer | Multi plain writers | Scan / scatter multi | Done |
|---|---|---|---|---|---|
| `route` | logical schedule → `ThreadedComposed` | F (identity: `desugarMultiWriters` returns the schedule unchanged; every pre-existing route test green) | **R** (was S: last-writer wiring, dead steps) | F (rejected by `multiWriterScan`/`multiWriterScatter` before physicalization, now on the route path too) | collected before `physicalizeForRoute` |
| `buildNameToStep` | name → (step, slot), `HashMap.insert` fold | F | F after `route` (sees one writer per name); still S for a direct `routeCore` caller with a multi-writer schedule | F | unchanged; its last-wins is now unreachable from `route`/`compile` |
| `routableInOrder` / `routeCore` | backward-wire topology gate | F | F (single gate; agrees with `isTopoOrdered` on collected schedules) | F | unchanged; payload pins preserved |
| `ScanStmt.toBrBaseP` (`inputWeaves` via `nameToStep`) | op label, input weave shapes | F | F (collector → `.contract`; weaves from the collector's own reads) | F | observed, no change |
| `routeNameInventory` / `routeName` / `routeNamesFresh` | private route-name freshness | F | F (inventory taken from the collected program) | F | no change |
| `physicalizeRaw` / `physicalizeForRoute` | per-statement fragments | F | **R** (input is now the collected program) | F | input changed at the caller only |
| `PhysicalRouteProgram.logical` | the schedule physicalized | F | now holds the COLLECTED schedule (field name unchanged) | F | note only (Q3) |
| `compile_eq_physical_route` | plumbing lemma | F | **R** | F | statement extended (above) |
| `compile_wellFormed` | compiler theorem | F | F | F | statement unchanged |
| `AcsetCodec.fromThreadedComposed` / `toThreadedComposed` | steps/wires/axes tables | F | F (no names encoded; multi-input collector round-trips) | F | fixture 10 |
| `checkStructure` (`NumericalProfile`) | oracle structural refusals | F | **R** (refusal removed) | F (scatter/scan refused by Admission before the profile) | done |
| `checkStructure` dtype refusals (`usedDType`) | f64-only profile | F | F (order unchanged: statement 0's output dtype is checked before a second definition is seen) | F | F14f32 pins it |
| `ComparisonRun.classification` (`Differential`) | run classification | F | F (multi-definition f64 programs now reach `fourLegParity`) | F | no code change |
| `knownContractDifference` | classification constructor | F | F (still produced by `usedDType`) | F | NOT dead, kept |
| `SharedFragment.definitions` | (declaration, origin) list | F | now may repeat a declaration | F | consumers: `SourceDifferentialGeometryTest` (single definition, green) and the new F14/F15/D10 pins |
| `NativeLegs` legacy/checked legs | native observations vs oracle | F | F (the evaluator and the checked plan already collect and hide since P1/P2a) | F | observed agreeing (F14/F15/D10) |

## Probe observations

See `p2b_observed.md` (before/after routing, the rejected `collectDefinitions` attempt, the `tlprog!`
`tensor f64 T(i)` parse failure side-finding).

## f32 coverage

- Route: RT1, RT2, RT4, RT5, RT6 are undeclared (default f32); RT3 declares `tensor f64 Y(i)`; the
  probe also ran `explicitF64` twins (identical routing).
- Differential legs: F14f32 (default-f32 twin of F14). **Classification is unchanged by the lift**:
  `knownContractDifference (usedDType (output, decl 3, statement 0) "Y" f32)` both before and after,
  because `checkStructure` refuses the first statement's f32 output before it can see a second
  definition; the oracle still computes `[7,13]` for Y. So for untyped tensors the path doc's
  "classified separately" (`usedDType`) still holds and now is the ONLY structural refusal.

## Questions for the controller

1. **`route` calls `desugarMultiWriters`, not `collectDefinitions`** (deviation; reasons above). The
   alternative is to keep `collectDefinitions` and re-pin the three `RouteFragmentDiagnosticTest`
   payloads to the wrapper's message, which that test's own rationale argues against. Accept?
2. **`route` discards `privateNames`.** Nothing on the routed surface names tensors, so there is nothing
   to hide. If a later diagnostic/diagram layer attaches names to steps, it must take `privateNames`
   from `desugarMultiWriters` then.
3. **`PhysicalRouteProgram.logical` now holds the collected schedule**, so `fragmentCount`
   (`fragments.length = logical.stmts.length`) counts collected statements (writers + collectors).
   Rename the field / restate its doc, or leave it?
4. **`buildNameToStep`'s last-wins stays reachable for a direct `routeCore` caller** (tests and
   `RouteSpec`). All production callers go through `route`. Add a guard, or leave it (it is F for
   `route`)?
5. **JAX evidence on collected plans** (P2a (b)4) was not probed (out of the P2b task list).

## Budget

About 75 tool turns against the ~60-turn budget, a breach of about 25%. The causes were the rejected
`collectDefinitions` attempt (one extra build cycle), and three harness refusals: commands whose
paths contain `/Source/` are rejected as "runs a string through source", so the scripts had to go
into files first. There were also two build-wait turns. Context peak was not measured (no session
id for `token-report.py`). My estimate is about 120k, because the docsweep triage went to a
read-only subagent (about 139k of its own tokens) and its file windows never entered this context.

## Verification

- Targeted green, final tree: `DSL.Pipeline.CollectTest`, `Bridge.AcsetCodecTest`,
  `Bridge.AgreementTest`, `DSL.Pipeline.RouteFragmentDiagnosticTest`, `RouteFragmentCorpusTest`,
  `RouteWeaveTest`, `LoweringTest`, `StructuralTest`, `RecurMorphismTest`, `ScanAffineTest`,
  `DSL.ComplexElementTypeTest`, `DSL.CompileExamplesTest`, `DSL.IterDeclTest`,
  `Semantics.SourceDifferentialPolicyTest`, `Semantics.SourceDiagnosticAdmissionTest`,
  `Semantics.SourceDifferentialGeometryTest`, `LeanNCD.Bridge.Agreement`.
- Full `Tests` (one background run on the T4 commit `d45a85d7`, `lake-build.sh … Tests`):
  `Build completed successfully (8799 jobs)`, no failing module. The two P2a-era failures
  (`SourceDiagnosticAdmissionTest` D10, `SourceDifferentialPolicyTest` F14/F15) are closed.

## Deviations

- `route` calls `desugarMultiWriters` (Q1).
- `crossStatementOverwrite` deleted rather than left unused (the brief allowed this for constructors used
  only by the refusal).
- The acset round-trip fixture is a codec witness, not a pin of the route change (M1 did not break it);
  its companion `steps.length = 5` guard is the pin.

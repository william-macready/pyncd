# Task 1 adapter/proof donor

These files are durable implementation seeds for Task 1 of
`papers/nonlinearity_split_pair_direct_lowering.md`. They are production-shaped donors, not a
production dependency.

## Durable artifact

- `RouteFragmentsSeed.lean`
  - executable route-name inventory and strictly-longer `#` name generation;
  - proofs `routeName_length`, `routeName_not_mem`, and `routeName_injective`;
  - `RouteFragment` plus checked, proof-carrying `PhysicalRouteProgram`;
  - one-pass `physicalizeForRoute`, including producer `.freeNorm → .free`, payload preservation,
    contiguous fragment layout, logical-exit checks, freshness, and physical topology checks;
  - logical `compileToScheduled`, public-logical-route-shaped `route`, and source `compile`;
  - exact FreshM composition/result/state guards (including old-pipeline split-mint deltas);
  - ReLU, softmax, downstream chain, opaque nonlinear scan, long-`#` collision, and old/new routed
    presentation checks;
  - negative freshness, duplicate-name, noncontiguous-layout, and cyclic-physical-route checks;
  - `compile_eq_physical_route` and the repaired, unchanged-shape `compile_wellFormed`.

Agreement remains in this single file because a directly checked file outside `leanncd/` cannot
import a sibling as a Lake module without changing `lakefile.toml`, which this preservation task
forbids. Split the marked Agreement declarations during production transplantation.

## Transplant map and safe order

1. **`LeanNCD/DSL/Ast.lean`**: move the existing `LHSSlot.toReadIdx` declaration here from
   `Pipeline/Lowering.lean`; the donor calls that shared declaration.
2. **`LeanNCD/DSL/Pipeline/Types.lean`**: make `LinearProgram` a deprecated alias of the logical
   schedulable scan-program shape. Change `schedule` to accept that logical shape.
3. **new `LeanNCD/DSL/Pipeline/RouteFragments.lean`** (imports `Types` only): transplant
   `declaredTensorName?`, the `routeWrites`/`routeOutputs`/`routeReads`/`routeInputReads` accessors,
   `routeNameInventory`, `maxSourceNameLength`, `routeName`, the three route-name theorems,
   `RouteFragment`, `PhysicalizeAcc`, `producerSlots`, `physicalizeOne`, `physicalizeStep`,
   `physicalizeRaw`, `physicalizeRaw_fragmentCount`, `generatedRouteNames`, `routeNamesFresh`,
   `fragmentWidth`, `checkFragmentAt`, `fragmentLayoutOk`, `fragmentExitsOk`,
   `physicalRouteInOrder`, `PhysicalRouteProgram`, and `physicalizeForRoute`. Keep the fold-count
   helper private and make the real package constructor/private representation inaccessible outside
   the route boundary. The local accessors/topology check intentionally avoid depending on
   `Lowering`'s `ScanStmt.writes`/`outputs`/`reads`, `buildNameToStep`, or `routableInOrder`.
4. **`LeanNCD/DSL/Pipeline/Lowering.lean`**: import `RouteFragments`; keep `routeCore` unchanged;
   replace public `route` with the donor wrapper body. Keep `splitStmt`, `splitScan`, and
   `splitNonlins` only for regression callers.
5. **`LeanNCD/DSL/Compile.lean`**: transplant the donor `compileToScheduled` and `compile`, removing
   `splitNonlins` from the production chain. After step 2, delete the donor-only `scheduleLogical`
   record adapter and call `schedule` directly.
6. **`LeanNCD/DSL/Pipeline/RouteSpec.lean`**: retain existing `routeCore` theorem statements. Add
   adapter-specific lemmas only where tests need named proof projections.
7. **`LeanNCD/Bridge/Agreement.lean`**: replace `compile_eq_route` with
   `compile_eq_physical_route`; transplant the donor `compile_wellFormed` proof body. Do not thread
   fragment evidence into `wf_typeMatch`, `wf_singleOutput`, or `wf_topo`.
8. **Tests only, not production**: move the private source fixtures, exact-state/result guards,
   malformed-fragment checks, and `run_cmd` payload checks into the Task 1 test modules named by the
   canonical plan. Only then add their Lake globs.

## Assumptions and intentional seed differences

- The seed imports `LeanNCD.Bridge.Agreement` so one durable file can directly compile against the
  current tree. Production must use the plan's acyclic `Types ← RouteFragments ← Lowering` graph.
- Current `LinearProgram` is still a distinct structure, so `scheduleLogical` performs a record-only
  compatibility conversion. Production deletes this helper after introducing the alias/API change.
- The seed package constructor is namespace-visible. Production makes it private; successful seed
  construction nevertheless carries exact-build, preservation, count, layout, exit, freshness, and
  topology evidence.
- Adapter-check failures reuse existing `shapeMismatch`/`cyclicDataflow` constructors. Production may
  introduce the plan's final diagnostics, but must preserve common-domain error precedence.
- Route-name ordinal is the logical fragment index. Gaps are harmless: strict length growth still
  proves source freshness and injectivity.
- Scans and `scanPre` are deliberately opaque and copied as top-level nodes. This does not claim
  categorical representation of masks, Iverson predicates, dtype metadata, or nested `scanPre`
  payloads.
- This donor proves the Agreement repair and checks representative old/new route equality. It is not
  the full 145-case Task 2 corpus or the Task 1 diagnostic differential suite.
- Exact nonzero-start states pinned by the seed are: ReLU `9 → 10` (old split pipeline `→ 11`),
  softmax `23 → 25` (old `→ 26`), chain `31 → 32` (old `→ 33`), opaque scan `47 → 50` (old
  `→ 51`), and escaped `%nl8` acceptance `7 → 8`. At a zero start, `assignUIDs` intentionally spends
  an extra mint to avoid UID zero; the composition guard compares that case without hard-coding a
  misleading nonzero-start delta.
- The negative guards exercise the public Boolean checks and a cyclic `ScheduledProgram`; malformed
  packages cannot be passed to `route` through `physicalizeForRoute` because successful construction
  fixes statements/fragments to `physicalizeRaw`.

## Required verification

Run from repository root:

```bash
cd leanncd
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/adapter_proof/RouteFragmentsSeed.lean
"$HOME/.elan/bin/lake" build LeanNCD.DSL.Pipeline.Lowering LeanNCD.Bridge.Agreement
"$HOME/.elan/bin/lake" build Tests LeanNCD
```

The first command must always target the final durable path. On 2026-08-25 all three commands above
completed successfully. The direct check executed 15 `#guard`s and five `run_cmd` blocks, including
exact result/state, old/new presentation, malformed evidence, payload, scan-opacity, collision, and
escaped-prefix checks. The builds retained existing dependency warnings, including the repository's
known `St`/`Br` `sorry` declarations and unrelated linter warnings; this donor itself contains no
`sorry`, `admit`, or `axiom`.

Four donor-local implementation mutation cycles were also run as mutate/fail/restore/pass:
reinserting `splitNonlins`, removing strict route-name growth, mapping a nonlinear fragment exit to
its entry, and corrupting routed `nExternal`. The restored file passed the direct check after every
cycle. This is not the plan's complete 14-cycle Task 1 production mutation gate, the 145-case Task 2
corpus, or a production transplant; those remain required when the donor is moved into production.

## Prohibition

Production Lean files and tests must **not import this seed**. Copy reviewed declarations into their
mapped production modules, restore the exact planned import graph, and then delete all seed-qualified
references from the production diff. Keep this subtree as historical proof/adapter donor material.

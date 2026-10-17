# P2b-T5 documentation sweep (read-only; nothing edited)

Scope: `leanncd/`, `papers/`, `.claude/` (excluding `.lake/`, this artifacts directory and the decision
note). Searched phrases: "last write wins" / "last-write-wins" / "last-wins", "later insertion wins",
"known contract difference" / `knownContractDifference`, `crossStatementOverwrite`, "cross-statement
overwrite", "one definition per left-hand side", "multi-definition", "repeated assignment",
`materializedNames` examples with duplicates, F14/F15 values `[2,4]`/`[5,9]`, AGENTS.md rows. The
window triage was done by a read-only search agent and spot-checked; every FALSE row names an
identifier or heading, not a line number.

Excluded as unrelated (stay true): last-write-wins INSIDE one scatter statement
(`ScatterReduce.overwrite`), overlapping writes inside one scan, and last-wins insertion over duplicate
DECLARATIONS (`buildDeclEnv`, `duplicateTensorDecl`, `resolveDecls`). `[2,4]`/`[5,9]` hits in other
Semantics tests are input data, not F14/F15 results.

## FALSE after slice 1 (propose a rewrite)

| File | Identifier / heading | Falsified phrase | Proposed new text |
|---|---|---|---|
| papers/semantics/lean_executable_semantics_path.md | "Differential debugging", **Numerical profile** bullet | "one definition per left-hand side" | Requires explicit `f64` declarations; several statements may define one left-hand side and are collected and value-compared. |
| papers/semantics/lean_executable_semantics_path.md | same section, **Known contract differences** bullet | "Production overwrites when several statements define one left-hand side … F14 and F15 observe `[2,4]` against `[7,13]`, and `[5,9]` against `[12,22]`" | Every backend sums multiple definitions; F14/F15 are value-compared on all four legs at `[7,13]`/`[12,22]`. The remaining known contract difference is an untyped (default-f32) tensor (`usedDType`). |
| papers/semantics/lean_executable_semantics_path.md | same bullet, "Planned alignment" paragraph | "decided 2026-10-14, not landed … rewritten when the first slice lands" | Additive collection landed in slice 1 (`collectDefinitions`/`desugarMultiWriters`); scatter, max/min and scan multi-writers are rejected. |
| papers/semantics/lean_executable_semantics_path.md | §5.1 "Beyond the bounded source fragment" | "value comparison of multi-definition programs once production collects additively" | Delete the clause (already compared by value). |
| papers/semantics/lean_executable_semantics_path.md | §5.1 decision-note paragraph | "It is planned and not yet implemented, so the divergence described next still holds today." | Slice 1 implemented collection for sum-algebra bare-slot writers; the note's other slices remain planned. |
| papers/semantics/lean_executable_semantics_path.md | §5.1 gap-audit paragraph | "production does not yet implement … classifies such programs as a known contract difference and never compares their native output values" | Production sums definitions and the differential compares them by value; gap-audit G04 records the pre-slice state. |
| papers/semantics/tensor_logic_semantics.md | **Remark (current production pipeline)** | "the pipeline currently replaces the supplied value silently, and enforcing the rejection is part of the planned alignment" | Both backends reject such an input (`EvalError.inputIsDefined` / `InputBindingError.inputIsDefined`). |
| papers/semantics/tensor_logic_semantics.md | **Remark (production readiness)** | "The scheduler currently releases a reader after the first of several writers" | A reader of a tensor with several writers waits for every writer (all-writers readiness). |
| papers/semantics/tensor_logic_semantic_gap_audit.md | "Established baseline: multiple LHS definitions are not additive", status update | "The change is planned and not implemented" | Slice 1 implemented the change; the findings below describe the code as audited before it. |
| leanncd/LeanNCD/Semantics/AGENTS.md | source differential paragraph | "single-definition profile. Same-LHS multi-statement programs are a known production contract difference and are never compared natively." | Bit parity holds on the bounded-integer, f64-declared profile; same-LHS multi-statement programs are summed by every backend and compared by value on all four legs. |
| leanncd/LeanNCD/Semantics/Source/NativeLegs.lean | `runNative` doc | "backend failures or known overwrite behavior" | "… is metadata, not a gate on observing actual backend failures." |
| leanncd/LeanNCD/Eval/Plan/Prepared.lean | `PlanBindings` doc, first paragraph | "A name reassigned twice appears twice; `unpack` (Task 3) relies on this" | Only hand-built bindings can repeat a name (then `unpack` keeps the later entry); `prepareEvalPlan` never repeats one. |
| leanncd/LeanNCD/Eval/Plan/Prepared.lean | materialized-signatures doc (`materializedWith`) | "a name reassigned twice appears twice here too" | A name repeated in hand-built bindings appears twice here too, each with its own slot's signature. |
| leanncd/LeanNCD/Eval/Plan/Adapter.lean | `unpack` doc | "a name written twice by the schedule appears twice here too … (the plan's own last write) naturally wins" | A name repeated in hand-built `materializedNames` is inserted twice and the later entry wins; `prepareEvalPlan` publishes each collected name once. |
| leanncd/test/Eval/Plan/ExecutableTest.lean | "VALID sibling: a name REASSIGNED" comment | "which is exactly what a repeated source assignment produces (`materializedNames` is not deduplicated)" | A hand-built shape; a repeated source assignment now publishes one collected name. |
| leanncd/test/Eval/Plan/CompileTest.lean | Task 4.3 fixture 8 comment (`repeatPredSched`) | "VALID repeated-name ordering sibling … repeats included" | The valid ordering sibling: slots in range and aligned with `materializedNames` (`Y` once, then `Z`). |
| papers/jax_evalplan_architecture.md | §2.1 "Semantic domain and ownership" | "retain existing last-write-wins behavior, including repeated names" | Materialized bindings are rebuilt left to right; prepared plans never repeat a public name, only hand-built bindings may (later entry wins). |
| papers/jax_evalplan_architecture.md | Appendix A (RequiredBindings discussion) | "may repeat names, and are reconstructed left-to-right with last-write-wins … incorrectly ban an existing materialization behavior" | Materialized bindings may repeat names only when hand-built; prepared plans publish each collected name once. |
| papers/f32_evalplan.md | Task 4 (named f32 boundary), fixture item 4 | "require repeated materialized names in schedule order and last-write-wins native bits" | Fixture 4 requires `#["Y","Z"]` and the `A + B` bits. |

## Proposed ADDITIONS (statements now missing, found while doing T3/T4)

| File | Identifier / heading | Proposed new text |
|---|---|---|
| leanncd/LeanNCD/DSL/AGENTS.md | Pipeline contracts (route) | `route` runs `desugarMultiWriters` before `physicalizeForRoute` (not `collectDefinitions`: `routeCore`'s `routableInOrder` stays the single topology gate); private `T#k` steps stay in the routed diagram. |
| leanncd/LeanNCD/DSL/Pipeline/RouteFragments.lean | "The checked package (§2.2)" section note | Add: on the `route` path the schedule is collected first, so the "same last-writer-wins check" sees one writer per name; `PhysicalRouteProgram.logical` holds the COLLECTED schedule. |
| leanncd/LeanNCD/Semantics/AGENTS.md | source differential paragraph | `StructuralCondition` now has only `usedDType`; `knownContractDifference` is produced only by it. |

## STILL TRUE (checked; optional qualification only)

- leanncd/LeanNCD/Eval/Plan/Prepared.lean `rawMaterializedWith` doc ("later insertion wins"), and the
  `PlanBindings` additive-collection paragraph (already updated by P2a).
- leanncd/LeanNCD/Eval/Plan/Adapter32.lean `unpack32` doc ("repeated-name last-write-wins"):
  hand-built bindings only; optionally qualify.
- papers/f32_evalplan.md §3.4 ("preserving the existing last-write-wins behavior for repeated names"):
  same mechanism; optionally qualify "hand-built".
- leanncd/LeanNCD/DSL/Pipeline/RouteFragments.lean section note "the same last-writer-wins check":
  `routableInOrder` is unchanged.
- Declaration last-wins texts: `InputSignatureBuildError` doc (Eval/Plan/Error.lean),
  `duplicateTensorDecl` comment (Exec/Uid.lean), `buildDeclEnv` doc (DSL/Ast.lean), SignatureTest
  fixture 14, StructuralTest Task 4.1 fixture 1, papers/leanncd.md `resolveDecls`,
  predicate_boolean_backend_parity.md / boolean_predicate_output_evalplan.md declaration rows.
- Scatter/scan texts: papers/leanncd.md §14.3 `ScatterOpts`, Eval/ScanTest collision comments,
  DifferentialTest Wave F F4 scope note, jax_evalplan_architecture.md scan snapshot subsection,
  ref_align_prototype_notes.md shape 5, tensor_logic_boundary_policies.md "Remapped collisions".
- Already rewritten for collection: DifferentialTest repeated-assignment coverage, Adapter32Test
  fixture 4, AdapterTest (c) (hand-built bindings).
- papers/semantics/source_correspondence_plan.md §4 "Known contract difference" row and §2 "Multiple
  definitions contribute separately": still true (`usedDType` still uses the class).
- papers/semantics/lean_executable_semantics_path.md "an untyped tensor is classified separately":
  still true; F14f32 confirms the classification is unchanged by the lift.

## HISTORICAL records (dated; leave, optionally add a "superseded by slice 1" banner)

papers/semantics/source_correspondence_record.md (production observations `[2, 4]`, Phase B rerun,
T5/T6 checkpoints, 2026-10-09 close-out); source_correspondence_plan.md §4.1 four legs, §6 F14/F15
rows, T6 mutation list (plan marked IMPLEMENTED); source_correspondence_artifacts/ (close-out,
`production_evidence.json` `"legacy": [2, 4]`, `production_probe.lean`);
source_correspondence_readiness_patches/*.patch and source_correspondence_mutations_post.json
(`crossStatementOverwrite`); tensor_logic_semantic_gap_audit.md G04 / F01;
predicate_boolean_backend_parity.md "repeated names" mapping row; leanncd/docs/superpowers/plans/
2026-08-10-jax-evalplan-smoke.md requirement 6 and 2026-06-26-scan-lowering-fix.md open questions;
papers/wave_c_evalplan_proposal.md tests list and review quote.

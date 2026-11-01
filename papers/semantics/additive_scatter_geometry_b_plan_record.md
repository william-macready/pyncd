# Scatter geometry slice B: plan record (authoring)

Live plan: [additive_scatter_geometry_b_plan.md](additive_scatter_geometry_b_plan.md). Binding design:
[additive_scatter_geometry_b_design.md](additive_scatter_geometry_b_design.md). Prototype ledger:
[additive_scatter_geometry_b_files/proto_notes.md](additive_scatter_geometry_b_files/proto_notes.md).
This record holds what execution does not need.

## Authoring dispatches and Rule 6

| Dispatch | Tool calls | Cap | Breach |
| --- | --- | --- | --- |
| Prototype 1 (engine) | the controller's count is about 152; the ledger's own budget section says "about 125" (the ledger text was written before the last rounds; the larger figure is the controller's harness count and is the one to trust) | 60 | YES, about 2.5x. Cause: the re-pin ripple (15 guards in 7 modules, one of them, `OracleMixedRefusalTest`, needing a redesign), Lake skipping dependents of a failing module so a second round of failures appeared only after the first fixes, and the Intent-Layer hook re-attaching a long `AGENTS.md` excerpt on every `Edit` of a DSL file |
| Prototype 2 (surface) | the controller's count is about 103; the ledger says "about 66" | 60 | YES. Cause (ledger): three scratch-observation rounds, one unusable rebuild because `bias` is a reserved token, four manifest waits |
| Plan write (this dispatch, T5 patch plus package) | about 130 tool calls | about 60 | YES, about 2x. Cause: the docs sweep found 8 more stale statements than the ledger's value-grep list (portfolio rows, `Error.lean`, `Collect.lean` header, `Uid.lean` comment, Semantics counts), a T5 build plus a replay of five patches in single commands, and a line-number-stability fix after the manifest check |

Context peaks were not measured by the harness here (the plan-write dispatch read one whole 40k-character
test file by mistake while looking for a line number; no other whole large file). Authoring token total is
not known to this dispatch: it must be taken with `python3 .claude/skills/slice-plan/token-report.py` per
session by the controller, against the Rule 6 authoring target of about 50M (a target) and the design note's
guess of about 35M. Not measured here, so no overrun is claimed or excluded.

Consequence recorded for Rule 6: the plan splits what was one engine dispatch into T1 (production plus the
15 re-pins, shipped as ONE patch) and T2 (new fixtures), because the first dispatch showed a hand-made T1
is unbounded; the executor never hand-edits the re-pins.

## Deviations from the design note

1. Task structure. The design note listed T1 engine, T2 surface, T3 docs. The plan has five tasks: engine
   (T1) and its fixtures (T2) are split, and the surface into syntax (T3) and fixtures (T4), so that each task
   has one fixture/mutation count and a reviewer can reject one while approving its neighbour. Docs are T5.
2. Predicate name. The design left "whether the predicate keeps the name `boundedScatter`" to plan time. It was
   renamed `LHSSlot.collectable`: the old name was false for the cases it now admits. Cost: 3 call sites, 1
   doc, the `AGENTS.md` row (all in T1/T5).
3. B-D5 evidence. The design said a scan-local `[=n]` slot "fails loudly". Observed: the SURFACE-built
   constant slot in a scan fails with `overlappingScatter` at compile (the surface route lowers the constant
   first), not with the programmatic `checkScanScatterLHSSlot` constant refusal, which stays pinned on a
   hand-built schedule (`CompileTest`). A surface multi-axis slot in a scan fails `multiAxisScatterLhs` at
   preflight. Both pinned in `ScatterSurfaceTest`.
4. B-D6. "Shared predicate taken only if it falls out cheaply": it did not (the oracle works from
   `AdmittedStatement` forms, the predictor from `LHSSlot`s, the collector from `LHSSlot`s with the
   environment). Parked, about 0.5 dispatch.
5. B-D1 probe. `checkCollectorShapes` needs no new arithmetic (it calls `LHSSlot.outExtent` per slot):
   confirmed by F1-F4 passing and re-grepped at plan time.
6. B-D4 probe. `S[=3]` tokenizes and parses without a space; `S[= 3]` also parses; no fallback spelling
   needed; no existing parse changed (the full build is green; `axis a : N = 3` uses `=` in other
   categories). One surprise the design did not predict: `S[a + b +1]` is a parse error (`+1` is one token);
   documented in T5, no code change.
7. A fact the design note did not state: T1 forced 15 re-pinned guards in 7 test modules. Their intent is
   listed in plan section 3; none was loosened to pass.
8. The design note's anti-goal "no second extent formula" is met: the multi-axis arm of `outExtent` and the
   checked plan's range rule share `affineImageBounds` (slice A); `derivedShape` calls `outExtent`.
   `OracleSortRules.predictedExtent` (TEST code) is an older, independent sum-rule restatement for multi-axis
   slots that this slice does not touch (parked).
9. Doc truth found during T5 that the prototype ledger did not list: `docs/test_portfolio.md` (KG-reshape
   twice, EC9), `EdgeCaseTest.lean` and `KnownGapTest.lean` comments ("does not parse"),
   `CapabilityError.multiAxisScatterLhs` docstring (said unreachable from the surface; now reachable for a
   scan statement), the `Syntax.lean` comment (rules "above" are below), `Exec/Uid.lean` comment on
   `multiWriterScatter`, `Semantics/AGENTS.md` C1 counts (`222/195/88` and `81` are `281/186/38` and `99`),
   and the wrong `x +1 -> .iterNext` docstring line (the code gives `.affine (.shift x 1)`; scan lowering
   reclassifies to `.iterNext`).

## Probe results (prototype)

- P1 re-pins: plan section 3. P2 shape changes (B-D3): plan section 2. P3 users of the deleted names:
  only `ScatterGeometryTest`, `StructuralTest` (re-pinned) and `DSL/AGENTS.md` (T5); nothing in
  `leanncd/spikes`; `papers/` mentions are history and were not edited.
- Raw `.affine (.const _)`: not reachable through `compile`/`compileToScheduled`; pinned by F8 on a
  hand-built schedule.
- Surface: no ambiguity; parse results and fixture values in plan section 3.
- Mutant `SGB-T1-04` survived the `tag` guards (the native legs publish the declared shape and never
  `confirm` a predicted condition); `conditionCount fI2 == 0` was added. The mutated build FAILED for 8 of 9
  engine mutants at first run; after the added guard 9/9. Surface mutants 8/8.
- Observation not made: rank-0 destination under `declaredShapeWins` (vacuously true); zero-coefficient
  writer in a group or boxed destination.

## Decisions log

- Constant marker spelling `S[=3]` (owner, 2026-10-31). The constant is rewritten to `n + 1*u` over a synthetic
  size-1 axis by `lowerArith` (slice A); that axis keeps the readable name `#const<uid>` for display only.
- Refuse a raw `.affine (.const _)` in `collectable` by CONSTRUCTOR (slice A refused it by name).
- Do not validate degenerate slots (`a + a`, `0*a + b`): not needed by the goal (Rule 14); behaviour pinned as
  observed, documented in `DSL/AGENTS.md`.
- Keep the T3 manifest `expect` strings as file prefixes (as observed); do not hand-pin line numbers that the
  plan's own edits would move. The T1 entries DO pin lines; the T5 patch is therefore line-count-neutral for
  `SourceDifferentialScatterTest.lean` (guards `fFbig` and `fI2` sit at the lines the manifest names).
- T5 stays comment/doc only. It changes `.lean` files, so it ends with the full build (8844 jobs).
- Historical narrative notes in `papers/semantics` that say "multi-writer scatter sets are rejected"
  (`lean_executable_semantics_path_part_4.md`, `tensor_logic_semantic_gap_audit.md`,
  `additive_production_decision_note.md`) were NOT edited (dated records); wording-only follow-up, about 0.2.

## Parked list (Rule 14), with estimated costs in dispatches

| Item | Cost |
| --- | --- |
| scan-local multi-axis/constant slots (F3) | about 1 |
| validation of degenerate slots `a + a`, `0*a + b` | about 1 (Direct path) |
| shared predicate between `boxedSingleGroups` and the oracle | about 0.5 |
| `OracleSortRules.predictedExtent` multi-axis exact reach | about 0.3 |
| rank-0 destination in `declaredShapeWins` (`!declaredAxes.isEmpty`) | about 0.3 (Direct path) |
| independent kill power of F1-F6 (per-file `lean-file.sh` against each engine mutant) | about 1 |
| tighten T3 manifest `expect` strings to line pins | about 0.3 |
| zero-coefficient writer in a group or boxed destination: no pin | about 0.3 |
| diagonal scatter in a scan: no pin (inherited from slice A) | about 0.3 |
| wording of the three historical narrative notes | about 0.2 |
| predicate destination groups; negative surface coefficients; route/JAX | not estimated |
| other slice A parked nits | see slice A record, not re-derived |

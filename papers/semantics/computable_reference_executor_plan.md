# Computable reference executor: implementation plan

## 1. Status, authority, and fixed scope

**Full path: a new executable capability with a soundness surface.**
Authoring Phase B, 2026-10-08. **Verified and execution-ready:** exact replay,
full builds, all controls, and both final review lenses passed. This document
plans later implementation, not integration
performed during authoring. Production remains unchanged and the roadmap's
LANDED/NEXT markers must not move during this phase.

Authority, in order:

1. [Tensor Logic semantics](tensor_logic_semantics.md), especially Sections 21
   and 27 for worked denotational/operational examples.
2. [Executable-semantics roadmap](lean_executable_semantics_path.md), Sections
   3, 5.1, 5.2, and 6 for organization, computation, validation, and endpoint.
3. [Verified evidence](computable_reference_executor_artifacts/evidence.json)
   for the four prototype commits, patch digests, symbols, observations, and
   28-cell scope audit.
4. The exact [per-task patches](computable_reference_executor_patches/), not
   code transcribed into this plan.

The [authoring record](computable_reference_executor_record.md) holds receipts,
artifact identities, limitations, and pending gates separately from this plan.
The prototype is disposable, **not integrated**. All new modules below are
future outputs represented by patches; they do not exist in the planning tree.

### 1.1 Accepted endpoint

A directly constructed admitted core program, valid tensor input binding,
computational tensor equality, supplied complete ordered schedule, and supplied
coordinate-rank certificate have an exact rational executable reference:

- Computation selects only existing reference-machine edges and retains a
  typed selected-event path with an exact endpoint.
- Success implies the complete whole-store model, uniqueness among all models,
  and agreement of output projection with the existing denotation.
- Reached ready-undefined failure excludes all models. This implication is
  restricted to runs reached from validated initialization.
- The default finite bound prevents exhaustion. Supplied address ranks and
  existing reached-state progress exclude blocking; no model witness is supplied.
- Invalid tensor input returns an offending tensor before initialization.
  Arbitrary-state debug execution still distinguishes complete, failed, blocked,
  and exhausted; blocking and exhaustion are not no-model claims.

### 1.2 Constraints and deliberately deferred work

The generic typed executor requires computational `DecidableEq` on tensors,
`Program.tensors`, canonical finite coordinate layouts/equality, supplied
scalar operations/registry, and `AddCommMonoid` **only on defined carriers**.
The validated fixtures use the closed `Unit` sort and exact rational carrier:
zero, one, addition, multiplication, reciprocal with domain `x != 0`, and square.
Unsupported operations are not translated through a native-registry fallback.
There is no claim of exact-real transcendental execution or floating-point laws.

Keep function-valued `Running` storage and existing dependent coordinate domains.
A rank-zero shape `[]` has one coordinate; a zero extent has none.
Preserve every admitted statement/valuation tag, guard, bounded destination,
strict footprint, and existing boundary policy.

Out of scope: source/production correspondence; named syntax or rank checking;
source elaboration; rank or schedule synthesis; dense storage/backend refinement;
general cyclic equation solving; native floats; exact-real transcendentals;
custom boundary-policy changes; and a full categorical interpreter.
**Parked:** a heterogeneous non-additive-input runtime fixture is not required by
the agreed rational profile; estimated future cost is one small fixture dispatch.
The generic input type remains heterogeneous; do not weaken it to fit the tests.

## 2. Finite Naperian families and ordered presentations

This is the representation layer, not a new semantic coordinate system.
Finite tensor values remain functions on their dependent coordinate domains.
Canonical layout enumeration is a presentation isomorphism; supplied ordered
tensor/key lists present the same finite domains with deterministic priorities.
Contravariant reads remain lookup/precomposition through admitted reads.

Task 1 adds [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean):
computable finite instances, equality, input validation, state updates, and budget.
It uses existing `canonicalLayout` @ [Types.lean](../../leanncd/LeanNCD/Semantics/Types.lean)
and `coordDecidableEq` @ [Program.lean](../../leanncd/LeanNCD/Semantics/Program.lean).
Enumeration is admissible presentation data, **not classical selection**.
No generic automatic schedule builder or noncomputable `Finset.toList` order
is introduced.

`Schedule` supplies two lists with kernel-checked nodup and coverage proofs:
all tensors, and all occurrence/publication keys. Coverage includes **all tagged
occurrences and all defined publication coordinates**, including nonoutputs and
unwritten/empty fibers. Tensor input presence is checked even when a tensor has
no coordinates. Reversing a schedule reverses both validation and transition
priorities. Selection restarts from its first key after every transition.

Proof obligations: computable updates equal the existing noncomputable updates;
input success preserves the supplied binding; an error identifies a role/presence
mismatch; finite counts agree with the initial state measure.
Task 4 Group 2 protects singleton/empty domains, full-store counting, simultaneous
input violations, and exact budget boundaries.

## 3. Tagged coproducts and covariant additive collection

Occurrence identity is the coproduct of statement identities and their admitted
valuations, not a set of distinct bodies or values. Separate statements and
valuations must never be deduplicated, even when bodies, values, or destinations
coincide. Contributions implement covariant additive pushforward to destinations.

Existing [Collection.lean](../../leanncd/LeanNCD/Semantics/Collection.lean) and
[Program.lean](../../leanncd/LeanNCD/Semantics/Program.lean) remain the equation
authority. Task 1's computable `consume` removes exactly the chosen pending tag
and adds its value only at its destination. `publish` copies the retained
accumulator without changing it. Task 2 proves that selected contribution and
publication events are the existing edges, not an alternative collection relation.

Task 4 Group 1 distinguishes two statements times two valuations at a colliding
destination, observes contribution/publication order and payloads, checks a
literal complete candidate at every coordinate, and compares reversed schedules'
whole stores. The existing `successful_schedules_agree` @
[Progress.lean](../../leanncd/LeanNCD/Semantics/Progress.lean) supplies semantic
successful-result independence; the runtime contrast does **not** establish
independence of failure selection, diagnostics, or traces.

The literal candidate equation check is not an equation solver. Likewise, the
independent reciprocal prior is used only for read-free interpretation/collection.
Neither candidate is supplied to the executor to justify success or progress.

## 4. Option partial maps and the strict readiness boundary

Primitive meanings are partial set maps organized by the `Option` Kleisli view.
They are **not** arbitrary additive homomorphisms. Strict interpretation precedes
additive collection; undefinedness is not a zero contribution.
This protects nonlinear placement: reciprocal before collection differs from
reciprocal after addition. No linearity assumption may move square or reciprocal.

Task 2 adds [ExecutableSelection.lean](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean).
Its occurrence attempt checks pending membership first, then existing
`evalReady` @ [Readiness.lean](../../leanncd/LeanNCD/Semantics/Readiness.lean):

| Ready classification | Selector behavior |
| --- | --- |
| `notReady` | Skip this key; do not substitute zero or report undefinedness |
| `evaluated none` | Select undefined event retaining exactly this `Running` snapshot |
| `evaluated (some v)` | Select contribution carrying the evaluated value |

Publication requires an absent published cell and the exact `FiberEmpty`
barrier. Its legal event payload equals the retained accumulator.
The scan chooses the **first eligible key**, with no separate global
contribute-before-publish policy. A publication-first key can be skipped until
its fiber empties, then selected before later contributions elsewhere.

Task 3 adds the closed [RationalReference.lean](../../leanncd/LeanNCD/Semantics/RationalReference.lean)
registry. Task 4 protects guard exclusion versus strict zero multiplication,
ready undefinedness versus unavailable reads, both primitive meanings, internal
nonoutput failure, and exact missing-address diagnostics.

## 5. Store extension, transition paths, and operational refinement

Published stores retain the extension-preorder/thin-category interpretation:
contribution leaves the published store unchanged; publication extends it without
overwrite. Existing ready evaluation is stable on its footprint under extension.
The transition graph's selected finite paths refine existing `Step` and `Reaches`.
Forgetting the trace via `Execution.reaches` yields the existing reachability
relation; this is not new Mathlib `Cat`, `Functor`, or Kan machinery.

Task 2's `Event.Legal` and `Event.legal_step` certify edges. Task 3's
[ReferenceExecutor.lean](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean)
packages outcomes, event lists, and `Result.execution`.
Events retain typed tensor, statement/valuation, destination, contribution,
and publication payloads. `Event.effect` replays selected snapshots.
**The trace is not a log of every selection scan or readiness check.**
Blocked outcomes retain unavailable-read observations with actual typed missing
addresses; the observations API can separately inspect ready `Option` values.
Fixture scalar/string rows are test projections, not a public renderer or CLI.

`runFuel` first classifies already-failed states, then running completeness,
then no legal move/blocking, and only then checks fuel for a remaining move.
Exhausted means an eligible move remains but the debug budget is zero.
`run` initializes with occurrence count + **all** defined coordinate counts + 1.
`initialBudget_agrees` connects this computation to existing `stateMeasure` @
[Measure.lean](../../leanncd/LeanNCD/Semantics/Measure.lean);
`step_decreases` proves enough fuel without evaluating that noncomputable measure.

`result_model`, `result_unique`, and `result_denotation` reuse existing whole-store
soundness. `result_failure` uses reached failure, not arbitrary debug snapshots.
`result_not_blocked` uses `ranked_progress` @
[Progress.lean](../../leanncd/LeanNCD/Semantics/Progress.lean) and reached-state
invariants; `run_ranked_dichotomy` concerns the actual default run.
Certificates rank coordinate addresses and are supplied proof data, not synthesized
or checked by a new runtime validator. An unranked cycle can block with or without
a model; do not identify that outcome with undefinedness or inconsistency.

## 6. Execution protocol and artifact preflight

### 6.1 Common brief preamble: include in all four dispatches

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Read 40-60-line windows around the supplied symbols; do not reread entire semantic
modules or rediscover implementation. Apply exact patch bytes in task order.
Each task has an independent reviewer and its own target validation.
Expected execution is a short exact replay, not four redesign exercises.
Each dispatch stays within approximately 60 turns and 250k peak context.
If redesign or a missing obligation makes that implausible, **STOP and reauthor**;
do not silently alter patches, weaken proofs, or improvise another semantics.
Report cumulative usage where measurable; slice execution budget is about 175M.

### 6.2 Controller setup and refusal gates

Later execution starts in an isolated prepared worktree from **current local
main**, not the prototype HEAD and not an unconditional reset to the artifact base.
Use the repository's [new-slice skill](../../.claude/skills/new-slice/SKILL.md)
to prepare compatible Mathlib/project artifacts; stop if a cold build begins.
All paths in commands below are literal parameters: replace `/path/to/worktree`,
`/path/to/main`, and `/path/to/session-files` with controller-resolved absolute
paths before running. No shell variables or computed command paths are required.

```bash
/usr/bin/git -C /path/to/main rev-parse main
/usr/bin/git -C /path/to/worktree status --short
/usr/bin/git -C /path/to/worktree rev-parse HEAD
bash /path/to/worktree/leanncd/scripts/lake-build.sh /path/to/worktree/leanncd LeanNCD
```

Controller checks base compatibility and protected files before dispatch:

- Verify the four patch SHA256 values against the record/evidence; cross-check
  parent/commit/tree links. The [patch manifest](computable_reference_executor_patches/manifest.json)
  and evidence both contain all four tasks and the same final candidate tree.
  The controller regenerated the formerly three-task manifest from the measured
  evidence ledger; no implementation patch bytes changed.
- Confirm all five new modules/test paths are absent; inspect explicit protected
  existing paths for unrelated staged/unstaged changes. Refuse conflicts rather
  than overwriting. Current planning status is not future execution preflight.
- Patch 3 alone changes existing public import, AGENTS discoverability, and
  default test discovery. Existing semantic definitions and production evaluators
  are protected. Verify the exact allowed path set against each patch header.
- At a newer compatible baseline, sequential patch checks and target builds are
  required; original prototype tree hashes are provenance, not promised new HEADs.
- Hook-read budget: the measured planning node's Patterns + Global Pitfalls
  bodies total 2,981 characters, near the approximately 3k limit. Recheck actual
  injected sections before execution; if oversized, stop for a scoped preparation
  decision rather than inserting unrelated AGENTS trimming into these patches.

```bash
test ! -e /path/to/worktree/leanncd/LeanNCD/Semantics/ExecutableState.lean
test ! -e /path/to/worktree/leanncd/LeanNCD/Semantics/ExecutableSelection.lean
test ! -e /path/to/worktree/leanncd/LeanNCD/Semantics/ReferenceExecutor.lean
test ! -e /path/to/worktree/leanncd/LeanNCD/Semantics/RationalReference.lean
test ! -e /path/to/worktree/leanncd/test/Semantics/ExecutableReferenceTest.lean
/usr/bin/git -C /path/to/worktree diff -- leanncd/AGENTS.md leanncd/LeanNCD/Semantics.lean leanncd/LeanNCD/Semantics/AGENTS.md leanncd/lakefile.toml
/usr/bin/git -C /path/to/worktree diff --cached -- leanncd/AGENTS.md leanncd/LeanNCD/Semantics.lean leanncd/LeanNCD/Semantics/AGENTS.md leanncd/lakefile.toml
```

## 7. Four bounded task briefs

### Task 1: computational state, inputs, and finite presentation

Open with Section 6.1. Apply [01.patch](computable_reference_executor_patches/01.patch).
Only output: [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean).

Window-read locators; each is in that future file:

- `finiteDefined` @ [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean)
- `finiteCoords` @ [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean)
- `addressEq` @ [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean)
- `Key` @ [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean)
- `Schedule`, `Schedule.reverse` @ [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean)
- `validate`, `validate_error` @ [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean)
- `consume`, `consume_agrees` @ [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean)
- `publish`, `publish_agrees` @ [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean)
- `initialBudget`, `initialBudget_agrees` @ [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean)
- `completeDecidable`, `fiberDecidable` @ [ExecutableState.lean](../../leanncd/LeanNCD/Semantics/ExecutableState.lean)

Three review units: finite presentation/equality; presence validation; update and
budget refinement. Reviewer checks Sections 2-3, defined-only additive assumptions,
tensor-level empty-input presence, and all-coordinate/nonoutput enumeration.
No new runtime fixtures or mutation cycles execute at this stage.

```bash
/usr/bin/git -C /path/to/worktree apply --check /path/to/worktree/papers/semantics/computable_reference_executor_patches/01.patch
/usr/bin/git -C /path/to/worktree apply /path/to/worktree/papers/semantics/computable_reference_executor_patches/01.patch
bash /path/to/worktree/leanncd/scripts/lake-build.sh /path/to/worktree/leanncd LeanNCD.Semantics.ExecutableState
```

Accept only with target green and independent review adjudicated. Stage only the
single output path explicitly if making an execution commit. Do not use `--index`
to mix patch application with staging unrelated files.

### Task 2: exact selector and legal typed events

Open with Section 6.1. Depends on Task 1. Apply
[02.patch](computable_reference_executor_patches/02.patch).
Only output: [ExecutableSelection.lean](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean).

- `Event`, `Event.destination` @ [ExecutableSelection.lean](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean)
- `Event.effect`, `Event.Legal` @ [ExecutableSelection.lean](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean)
- `Event.legal_step`, `Move` @ [ExecutableSelection.lean](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean)
- `attempt` @ [ExecutableSelection.lean](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean)
- `scan`, `scan_none` @ [ExecutableSelection.lean](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean)
- `select`, `select_none_iff` @ [ExecutableSelection.lean](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean)
- `Observation`, `observations` @ [ExecutableSelection.lean](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean)

Three review units: pending/readiness classification; publication barrier/payload;
complete scan coverage and observation addresses. `select_none_iff` must prove
none exactly when no existing legal `Step` exists. It must not merely prove
selected steps sound while leaving completeness assumed.
Reviewer checks Sections 4-5 and the sibling scope matrix in Section 9.
Four proof/type controls belong here, but the combined mutation gate is deferred
until all patches are applied. No runtime mutation gate exists at Task 2.

```bash
/usr/bin/git -C /path/to/worktree apply --check /path/to/worktree/papers/semantics/computable_reference_executor_patches/02.patch
/usr/bin/git -C /path/to/worktree apply /path/to/worktree/papers/semantics/computable_reference_executor_patches/02.patch
bash /path/to/worktree/leanncd/scripts/lake-build.sh /path/to/worktree/leanncd LeanNCD.Semantics.ExecutableSelection
```

Accept target green plus independent review; stage only its output path explicitly.

### Task 3: bounded driver, rational profile, and discovery

Open with Section 6.1. Depends on Task 2. Apply
[03.patch](computable_reference_executor_patches/03.patch).
Outputs/allowed edits: [ReferenceExecutor.lean](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean),
[RationalReference.lean](../../leanncd/LeanNCD/Semantics/RationalReference.lean),
[ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean),
[Semantics.lean](../../leanncd/LeanNCD/Semantics.lean),
[lakefile.toml](../../leanncd/lakefile.toml), [leanncd AGENTS](../../leanncd/AGENTS.md),
and [semantic AGENTS](../../leanncd/LeanNCD/Semantics/AGENTS.md).

- `validate_accepts`, `validate_preserves` @ [ReferenceExecutor.lean](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean)
- `Execution`, `Execution.reaches` @ [ReferenceExecutor.lean](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean)
- `Outcome`, `Outcome.state`, `Outcome.isExhausted`, `Outcome.kind` @ [ReferenceExecutor.lean](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean)
- `Result`, `runFuel`, `runFuel_not_exhausted` @ [ReferenceExecutor.lean](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean)
- `run`, `run_not_exhausted` @ [ReferenceExecutor.lean](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean)
- `result_success`, `result_model`, `result_unique`, `result_denotation` @ [ReferenceExecutor.lean](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean)
- `result_failure`, `result_not_blocked`, `run_ranked_dichotomy` @ [ReferenceExecutor.lean](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean)
- `ValidatedResult`, `runValidated`, `runValidated_error` @ [ReferenceExecutor.lean](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean)
- `Carrier`, `ops`, `Primitive`, `registry` @ [RationalReference.lean](../../leanncd/LeanNCD/Semantics/RationalReference.lean)
- `shape`, `declarations`, `point`, `program`, `tag`, `schedule` @ [ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean)
- `duplicateBody`, `failureBody`, `strictPolicy`, `selfRead`, `blockedBody` @ [ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean)
- `summarize`, `checkSmoke` @ [ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean)

Three review units: driver/theorem refinement; closed rational profile;
integration/discovery plus three smoke rows. This deliberately bundles wiring
with semantic verification: the reviewer must check both, not waive the wiring.
The public [LeanNCD.lean](../../leanncd/LeanNCD.lean) already imports the semantic
entry; patch 3 makes the new modules transitively reachable there and adds the
test module to the actual default `Tests` glob. No new separate test library.

Smoke rows and donors are in Section 8. R1/R2 production controls are owned by the
profile but require Task 4 fixtures; do **not** run those gates at Task 3.

```bash
/usr/bin/git -C /path/to/worktree apply --check /path/to/worktree/papers/semantics/computable_reference_executor_patches/03.patch
/usr/bin/git -C /path/to/worktree apply /path/to/worktree/papers/semantics/computable_reference_executor_patches/03.patch
bash /path/to/worktree/leanncd/scripts/lake-build.sh /path/to/worktree/leanncd LeanNCD +Semantics.ExecutableReferenceTest
```

Accept target/import green, three observed smoke rows, and independent review.
Stage only the seven listed paths explicitly; never stage a directory wholesale.

### Task 4: broadened equation/operational fixtures and all control cycles

Open with Section 6.1. Depends on Task 3. Apply
[04.patch](computable_reference_executor_patches/04.patch).
Only output edit: [ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean).
No production edits are needed. Three validation groups add **19 rows**, retaining
three smoke rows: totals are 10 + 6 + 6 = **22 observed rows**.

- `check`, `eventRow`, `vectorStore`, `snapshot`, `noInput` @ [ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean)
- `taggedSchedule`, `taggedResult`, `taggedReverse`, `taggedCandidate`, `taggedAdmitted` @ [ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean)
- `zeroBody`, `excludedSchedule`, `excludedResult`, `reciprocalBody`, `squareBody`, `reciprocalCandidate`, `reciprocalAdmitted` @ [ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean)
- `scalarRole`, `scalarSchedule`, `scalarBinding`, `scalarInput`, `scalarResult`, `scalarSummary`, `validationRow`, `extraDefined`, `simultaneous` @ [ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean)
- `emptyRole`, `emptySchedule`, `presentEmpty`, `emptyRow`, `taggedFuel` @ [ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean)
- `readAt`, `chainBody`, `routedSchedule`, `chainInput`, `chainResult`, `chainCertificate` @ [ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean)
- `cycleBody`, `cycleResult`, `observationRow`, `cycleObservations` @ [ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean)
- `failureAfterBody`, `failureAfterSchedule`, `failureAfterResult`, `replay`, `replayRow` @ [ExecutableReferenceTest.lean](../../leanncd/test/Semantics/ExecutableReferenceTest.lean)

Reviewer checks each group against observed evidence, donor/contrast mappings,
and Section 9's scope matrix; this is exact replay, not new fixture design.
Complete the Section 10 gates after patch application, not during earlier tasks.
If the 19 new rows demand redesign, stop for reauthoring rather than growing a
single fixture dispatch past its budget.

```bash
/usr/bin/git -C /path/to/worktree apply --check /path/to/worktree/papers/semantics/computable_reference_executor_patches/04.patch
/usr/bin/git -C /path/to/worktree apply /path/to/worktree/papers/semantics/computable_reference_executor_patches/04.patch
bash /path/to/worktree/leanncd/scripts/lake-build.sh /path/to/worktree/leanncd +Semantics.ExecutableReferenceTest
bash /path/to/worktree/leanncd/scripts/lake-build.sh /path/to/worktree/leanncd
```

Accept all 22 observations, all 19 restored cycles with expected failure evidence,
full default build, and independent task review. Stage only the listed test file.

### 7.1 Risk and dispatch sizing

| Task | Three bounded review units | New fixture rows | Owned controls | Cycles executed here |
| --- | --- | ---: | --- | ---: |
| 1 | enumeration; input roles; update/budget equality | 0 | 0 | 0 |
| 2 | readiness; publication; selector completeness | 0 | 4 proof/type | 0 |
| 3 | driver; rational profile; imports/discovery | 3 smoke | 2 production runtime | 0 |
| 4 | collection; presence/fuel; ranks/failure diagnostics | 19 | 13 fixture contrasts | 19 combined |

Task 4 is the highest validation-cost task despite changing only one test file.
No phase split beyond the 60-turn cap is expected for applying verified bytes.
Per-task review is the checkpoint; final branch review is not replaced by it.

## 8. Fixture intent, donors, and discriminating observations

Donors below are existing symbols in
[CollectionModelTest.lean](../../leanncd/test/Semantics/CollectionModelTest.lean) (`CM`)
and [ReferenceMachineTest.lean](../../leanncd/test/Semantics/ReferenceMachineTest.lean) (`RM`),
or earlier future executor fixtures (`EF`) in the same patched test module.
These are provenance locators, not instructions to clone/rewrite the verified patch.
The evidence contains the full exact outputs and observed failure substrings.

### Group 1: additive collection and nonlinear boundary (10 total, 9 new)

| Row | Donor; changed field/construction | Observed discriminator | Control |
| --- | --- | --- | --- |
| duplicate (smoke) | CM.duplicate; closed rational profile | complete, 5 events, store `[4,0,0]`, pending 0 | S1 |
| tagged-trace | RM.valuationP + CM.collision; 2 statements x 2 valuations, destination 1, publication-first | four tagged contributions `2,2,5,5`, then publish `14,0,0` | F1, F2 |
| tagged-whole-store | EF.schedule; reverse supplied complete order | both complete; both stores `[0,14,0]` | F1 |
| tagged-equations | CM.collision; literal complete candidate | collected and literal vectors both `[0,14,0]` | F1 |
| zero-contribution | EF.duplicateBody; one literal-zero occurrence | complete, 4 events, three published zeros | F3 |
| empty-fiber | CM.noStatements; zero statements | complete, 3 publication events, three zeros | F3 |
| guard-excluded-undefined | EF.failureBody; false guard | complete, 3 publications; excluded undefined body not demanded | F3 |
| nonlinear-boundary | CM.reciprocalProgram; closed registry and independent prior | before sum `3/4`; after sum `some 1/6` | R1 |
| primitive-square | EF.duplicateBody + rational registry; square literal 3 | complete, 4 events, store `[9,0,0]` | R2 |
| trace-effect-replay | EF.taggedResult; fold selected effects | running, published `[0,14,0]`, pending 0 | F1 |

### Group 2: input presence, full-store roles, and fuel (6 new)

| Row | Donor; changed field/construction | Observed discriminator | Control |
| --- | --- | --- | --- |
| scalar-input-nonoutput | RM.scalarRole/scalarInput; singleton coordinates and internal tensor | complete, 4 events, `[7,2,3]` | F4 |
| internal-nonoutput-failure | CM.roleProgram; internal reciprocal zero | failed, 3 events, `[some 7,some 2,none]` | F4 |
| input-validation-order | CM.omittedEmpty/extraDefined; simultaneous errors at tensors 0,1,2 | errors `0,1,0,2`; reverse simultaneous first error is 2 | F5 |
| empty-input-and-defined | CM.roleProgram/presentEmpty/omittedEmpty; zero-extent tensor | present input complete 0; omitted error 0; empty defined complete 0 | F6 |
| fuel-boundaries | EF.taggedResult; budgets 6,7,8,9,0 | initial budget 8; exhausted, complete, complete, complete, exhausted | F7 |
| zero-fuel-terminal | EF.taggedResult/scalarResult; already terminal endpoints | complete and failed, not exhausted | F7 |

### Group 3: ranks, strict blocking, and retained failure (6 total, 4 new)

| Row | Donor; changed field/construction | Observed discriminator | Control |
| --- | --- | --- | --- |
| ready-failure (smoke) | CM.partialProgram; closed reciprocal zero | failed, 1 event, all three cells absent, pending 1 | S2 |
| blocked (smoke) | RM.cycleP; closed strict self-read | blocked, 2 events, `[none,some 0,some 0]`, pending 1 | S3 |
| coordinate-ranked-chain | RM.dependentP; same tensor, coordinate 2 reads coordinate 1, supplied address rank | complete `[0,3,4]`; contribution/publication interleaving | F2, F10 |
| strict-zero-cycle-locators | RM.cycleP/waitingBad; zero times reciprocal unavailable read | blocked `[some 0,none,none]`; destination 2 misses address 1 and destination 1 misses address 2 | F8 |
| failure-retained-snapshot | EF.failureBody + RM.badP; publish 2, contribute 2 at 0, fail statement 1 | exact `[none,none,some 0]`, accumulator 2, pending 1 | F2, F9 |
| ready-observations | RM.readinessLabel; pending literal versus reciprocal zero | ready `some 2` and ready `none`, both with no missing addresses | F9 |

A supplied `chainCertificate` proves coordinate ranks; runtime values alone do
not validate rank synthesis. The kernel proves initial measure 8 through budget
agreement; no `#eval stateMeasure` is claimed.
Locator and order fixtures intentionally separate candidate readings:
missing addresses differ from destinations; simultaneous input violations distinguish
first-error order; tagged publication priority distinguishes barrier skipping/rescan
from a global contribution-first policy. Publication tags in fixture rows use
projection placeholders; public events retain their actual typed constructors.

## 9. Required/forbidden/silently-ignored sibling audit

Carry forward this 7 x 4 matrix, derived from the evidence, during review.
R = required; F = forbidden case rejected; I = intentionally silently ignored by
this API because a named sibling owns it. An I cell is not permission to ignore
the contract at the public initialized-run boundary.

| Case | validate | attempt | observations | runFuel |
| --- | --- | --- | --- | --- |
| input presence | R: ordered tensor roles | I: takes Running | I: diagnostic Running | I: runValidated validates; run takes Input |
| occurrence membership | I: tensor roles only | R: pending guard | R: pending filter | R: delegates to select/attempt |
| readiness | I: no body evaluation | R: evalReady | R: evalReady + footprint | R: selector, blocked if no edge |
| undefinedness | I: no body demand | R: ready none -> failure | R: retain ready Option | R: exact failed endpoint |
| destination fiber | I: no collection | R: FiberEmpty and destination update | I: body diagnostics only | R: legal selected effects |
| publication eligibility | I: no publication | F: inputs/overwrite/nonempty fiber | I: publication keys omitted | R: Event.Legal |
| full-store completion | I: not solved-store check | I: local eligibility only | I: pending bodies only | R: Complete before selection/fuel |

Review `validate`, `attempt`, `observations`, and `runFuel` as siblings, including
their call-site preconditions. In particular, debug `runFuel` cannot validate
the presence of an empty input from addresses alone. Typed defined keys prohibit
input publication; `Event.Legal` additionally protects payload equality.
There was no identified production correctness defect in the prototype scope audit.

## 10. Controller validation, documentation sweep, and close-out

### 10.1 All controls after all patches

The [16-control manifest](computable_reference_executor_mutations_post.json)
contains P1-P4 proof/type rejections, R1-R2 production runtime oracle kills, and
F1-F10 fixture contrasts. The [3-smoke manifest](computable_reference_executor_smoke_mutations_post.json)
adds S1-S3 fixture contrasts. Total **19 = 4 proof/type + 2 production runtime
+ 13 fixture contrasts**, not 19 production runtime kills.
The A2 fixture ledger leaves three smoke mappings empty; use the smoke manifest
for those rows, not an invented edit to the evidence.

Use the repository's existing
[mutate-and-build.sh](../../leanncd/scripts/mutate-and-build.sh) and
[mutation-cycle.sh](../../leanncd/scripts/mutation-cycle.sh) through
`mutation-manifest.sh`, exactly as documented by the repository.
Their internal pinned-toolchain Lake invocations need no temporary routing edit.
The controller independently ran all 19 controls against unmodified scripts and
verified their base bytes afterward. A2's temporary routing was an authoring
detail, not an execution prerequisite or a fifth implementation patch.

```bash
bash /path/to/worktree/leanncd/scripts/mutation-manifest.sh --check /path/to/worktree/leanncd /path/to/worktree/papers/semantics/computable_reference_executor_mutations_post.json
bash /path/to/worktree/leanncd/scripts/mutation-manifest.sh --check /path/to/worktree/leanncd /path/to/worktree/papers/semantics/computable_reference_executor_smoke_mutations_post.json
bash /path/to/worktree/leanncd/scripts/mutation-manifest.sh --out /path/to/session-files/executor-16.md /path/to/worktree/leanncd /path/to/worktree/papers/semantics/computable_reference_executor_mutations_post.json
bash /path/to/worktree/leanncd/scripts/mutation-manifest.sh --out /path/to/session-files/executor-smoke-3.md /path/to/worktree/leanncd /path/to/worktree/papers/semantics/computable_reference_executor_smoke_mutations_post.json
```

Require every expected failure substring, exact source restoration, and restored
green target. `--check` alone is not a mutation gate. The discarded A2 scalar body
mutation failed in coverage proofs and does not count as a runtime kill.
Do not hand-write fresh mutation cycles or relabel fixture contrasts as production
mutations. Append execution receipts to the separate record.

### 10.2 Proof audit and two final branch lenses

Audit the added definitions and test certificates for no `sorry`, `native_decide`,
or new axioms. Interpret printed axioms for `select_none_iff`, `run_not_exhausted`,
`run_ranked_dichotomy`, `result_model`, `result_failure`, and `chainCertificate`.
Existing `propext`, `Classical.choice`, and `Quot.sound` proof dependencies are
erased content, not a runtime enumeration or rational operation.
Do not claim axiom-free or warning-free: prototype unusedSectionVars and
unnecessarySeqFocus warnings are present, including new warnings.

Two distinct final whole-branch reviewers, each with 40-60-line read windows:

1. **Semantic soundness:** initialized reachability, failure quantifiers, default
   bound, coordinate-rank progress, nonlinear placement, whole-store equations.
2. **Executable fidelity/integration:** computability, supplied schedule coverage,
   trace/effect payloads, validation priority, all 22 observations/19 controls,
   public import/default discovery, harness restoration, and docs boundary claims.

Both review the whole branch, not only their nominal files. Persist findings
incrementally in controller session artifacts; fix each finding group with a
bounded brief. Do not spend another implementation dispatch rediscovering the plan.
Controller runs the actual 19 cycles and full default build itself, then adjudicates
both lenses. Only these completed gates can justify an execution-ready/landed claim.

### 10.3 Later authoritative documentation sweep

Run these only during actual execution after the capability has been verified:

```bash
rg -n --glob '*.md' 'relation-only|no executable scheduler|not an executable scheduler|computable state/step selection|NEXT|REMAINING' /path/to/worktree/papers/semantics /path/to/worktree/leanncd
rg -n --glob '*.md' '22|19|16/16|3/3|8561|8704' /path/to/worktree/papers/semantics /path/to/worktree/leanncd
rg -n 'RationalReference|ReferenceExecutor|ExecutableReferenceTest' /path/to/worktree/leanncd/LeanNCD/Semantics.lean /path/to/worktree/leanncd/lakefile.toml /path/to/worktree/leanncd/AGENTS.md /path/to/worktree/leanncd/LeanNCD/Semantics/AGENTS.md
rg -n 'sorry|native_decide|axiom' /path/to/worktree/leanncd/LeanNCD/Semantics/ExecutableState.lean /path/to/worktree/leanncd/LeanNCD/Semantics/ExecutableSelection.lean /path/to/worktree/leanncd/LeanNCD/Semantics/ReferenceExecutor.lean /path/to/worktree/leanncd/LeanNCD/Semantics/RationalReference.lean /path/to/worktree/leanncd/test/Semantics/ExecutableReferenceTest.lean
bash /path/to/worktree/leanncd/scripts/lake-build.sh /path/to/worktree/leanncd
```

Review grep hits, not just counts; historical receipts remain historical.
Update the authoritative roadmap's current position and computational/validation
sections only after final gates, retaining categorical separation and explicit
source/backend gaps. Section 6's endpoint must describe this admitted rational
profile, not general source or exact-real execution. Patch 3 already carries
AGENTS/import/discovery hunks; do not defer discoverability.
Documentation is a bounded sweep, not another heavyweight dispatch.

Close-out records exact builds, observations, all control classes/restorations,
review adjudications, allowed changes, warnings, parked work, and measured usage
or telemetry unavailability. The controller may publish/integrate this reviewed plan package under repository
policy; that is not integration of the prototype. Production modules and
capability markers remain unchanged until the later implementation gates pass.
No remote push is part of authoring or execution without an explicit request.

# Collection/model execution verification

The [verified plan](collection_model_plan.md) was implemented by exact replay,
without redesign, in the isolated `collection-model-exec` worktree. All required
controller checks and both final implementation review lenses passed.

## Delivered semantics

- Finite coordinate families, contravariant pullback, and additive fiberwise
  pushforward with identity, composition, zero/add preservation, occurrence
  relabeling, and statement grouping laws.
- Typed finite programs with guard-admitted statement/valuation tags and bounded
  defined destinations. Duplicate and colliding contributions retain multiplicity;
  undefined bodies are never zero summands and prior candidate values are not seeds.
- Complete input tensor presence, including empty inputs; simultaneous equations
  for every defined tensor, including nonoutputs; model/fixed-point equivalence
  and nonconstructive output projection under unique-complete-model assumptions.

Collection genuinely uses the generic pushforward. Only participating defined
carriers need `AddCommMonoid`; expression operations remain explicit data.
This is not a full categorical interpretation, source checker, runtime boundary
resolver, solver, operational publication machine, or backend/numerical refinement.
The plan's excluded Boolean OR collection and equation-operator escape fixtures
remain explicitly uncovered, rather than silently reported as verified.

## Preparation and exact replay

Execution began at published local main `3acce41`. Repository preparation used
the primary checkout's warm cache: 8,101 Mathlib oleans / 8,094 sources and 199
project oleans. Clean status, baseline ancestry from `26fcfe6`, and every listed
protected-source/specification diff guard passed before the project refresh.
No protected source differences, patch conflicts, ports, or rebases occurred.

All three ordered actual-source `apply --check` operations passed. All nine
delivered file blobs matched the verified full-index patches exactly; unchanged
expression/readiness, historical spike, and production evaluator siblings remained
unchanged. Task 3 was committed only after actual controller gates completed.

| Task | Commit | Controller acceptance and targeted check |
| --- | --- | --- |
| T1 | `edce152` | Finite-family variance and additive laws accepted; Collection target passed, 2,944 jobs. |
| T2 | `1a22e4e` | Tagged admission, exact presence, all equations and model distinctions accepted; Models target passed, 2,948 jobs. |
| T3 | `ae46219` | Discriminating fixtures, sibling boundaries and discovery accepted; CollectionModelTest passed, 2,953 jobs. |

## Actual controller verification

- **13 production theorems** and **18 assertions: 9 guards + 9 theorems**.
  Five proof helpers and one evaluation command are not extra assertions.
- Observed fixture values: `[4, 9, 0, 0, 9, 5, 14, 3 / 4]`.
- Manifest schema and all 12 unique anchors passed. The actual complete suite
  passed **12/12**, each with the expected failure, byte-identical source
  restoration, and a green restored build. See the
  [execution mutation results](collection_model_execution_mutation_results.md).
  Five entries mutate source/invariants; seven are fixture contrasts. Generic
  proofs can kill M01/M04 before guards; M02 is a static admission-invariant
  rejection, not an observed runtime checker regression.
- All 13 production theorem axiom audits compiled with only `propext`,
  `Quot.sound`, and where needed `Classical.choice`; no `sorryAx`.
- Post-mutation working-source diff against the staged snapshot was empty.
- Full default build passed: **8,690 jobs**, including the new collection/model
  fixtures and all prior semantic modules. Existing dependency warnings,
  including pre-existing categorical `sorry` warnings, remained visible.
- All four required documentation/value sweeps ran. Current bounded-layer claims,
  historical plans/records/counts, generated patch context, and unchanged
  production contracts were distinguished; no further prose correction was needed.
- Modified root named injected sections measured **2,882 characters**. Local
  semantic guidance has **zero named hook sections**, while its whole-file
  length is **3,541 characters**; no claim that the whole file is below 3k is made.

Both final reviewers inspected immutable staged tree
`d689936972662c6fd39a96f90302f3b52edbb6b1`, which exactly matches the committed
implementation tree, rather than transient mutation sources.
Categorical/semantic/model fidelity was clean (8 reported tool rounds);
type/admission/artifact/execution fidelity was clean (10 reported rounds).
No findings required fixes or adjudication.

## Budget and integration

Execution used direct controller replay and bounded per-task reads, with only
the two required independent final reviews delegated. Mutation testing and
immutable-snapshot reviews ran concurrently; no polling or skipped gates.
The token-report tool found no matching SDK transcript, so measured aggregate
usage is unavailable. Reviewer round counts are estimates, not measured token
compliance; neither reviewer reported a budget breach.

No protected f32 branch/worktree was modified, rebased, built in, or removed.
Only this validated execution branch is eligible for local main integration.
The controller records the actual merge and own-worktree/branch cleanup in
session state. No remote push is authorized or performed.

# Actual nested graph/reference run prototype

## Status and ownership

Authoring phase (a), not execution or integration close-out. Only new module
`leanncd/experiments/indexed_execution/IndexedOperationalRuns.lean` is owned here.
It imports the controller's compiled `IndexedOperationalReassociation`.
Controller must register `IndexedOperationalRuns` in the Lake module list before
named downstream imports. No existing module, runner, lakefile or history module
was changed. No commits, merges or pushes.

## Exact proved boundary

- `StepRelated` relates actual writer/collector actions, including writer tags,
  capabilities, destination, ordered reads and `evalReady` in every related
  state. It does not assert syntactic equality of transported expressions.
- `step_enabled`, `steps_complete`, `steps_missing`, `steps_selected` derive
  actual runner decision alignment from ordered `List.Forall₂ StepRelated`.
- `stepFuel_transport` proves `RunRelated` for arbitrary equal fuels and related
  starting states. Events are exactly mapped in order, and the complete state
  lists are related by `Forall₂`, with no reorder, dropped state or stutter.
  Complete, failed, blocked, exhausted and both mismatch terminal branches
  retain their states and diagnostic payloads.
- `StateRelated` is `Projection f rename []`: the entire produced ledger is
  mapped in order with no prefix. `stateRelated_full` uses an address
  equivalence to recover every target available cell, not merely public cells.
- `StepImage`, `stepImage_map`, `images_related` derive semantic correspondence
  of multiply transported actions using `evalReady_transport`. This avoids the
  unavailable expression-syntax composition equality.
- `nested_steps` instantiates these lemmas on all actual A/B/C graph steps of
  both nested constructors. It uses the controller's `embedding_address`,
  `address_A/B/C`, `identity_A/B/C`; selected-action agreement is not a premise.
- `nested_default_runs` proves `RunRelated` of the actual default
  `IndexedOpenComposition.runChecked` calls of `leftBracket` and `rightBracket`
  on the same validated A input lifted along each constructor. It rewrites with
  `checked_eq_stepFuel` and `default_budgets` (both nA+nB+nC+1).
  There is no rank, completion, model-existence, execution-agreement or
  selected-action-agreement premise.
- `ranked_nested_default_runs` additionally derives `SuccessfulOrFailed` for
  both actual runs using constructed `leftRank/rightRank` and the existing
  `ranked_default_terminal`.
- `nested_reference_runs` concerns the actual two `Program.Executor.run`
  results. Normalized ordered events agree. Their actual `referenceSnapshots`
  are related by `Forall₂ ReferenceStateProjection`, retaining both complete
  `LedgerInvariant` and `Relation` values (published, pending, accumulators).
  Both actual reference outcomes retain their complete graph correspondence.
- `ReferenceOutcomeRelated`, `reference_terminal_transport`, and
  `ranked_nested_reference_outcomes` additionally prove that the two actual
  reference terminal outcomes are both complete or both failed. Failures
  preserve the renamed occurrence tag; both branches retain full endpoint
  `ReferenceStateProjection`. These require only validated A input and the
  three leaf rank certificates.

## Verification

Final command (exit 0, no warnings), saved in `compile.log`:

```text
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-handoff/leanncd/scripts/lean-file.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-handoff/leanncd experiments/indexed_execution/IndexedOperationalRuns.lean
```

Four `#print axioms` controls (`stepFuel_transport`, `nested_default_runs`,
`nested_reference_runs`, `ranked_nested_reference_outcomes`) report only
`propext`, `Classical.choice`, `Quot.sound`; no sorry/admit/new axiom.

Destructive controls copied the complete real module to separately named owned
Lean modules and ran the same single-file checker. All three returned exit 1:

| Mutation | Observed rejection |
|---|---|
| Reverse mapped events in `RunRelated.events` | `Type mismatch: After simplification, term` at the recursive produced/sealed event proof; `mutation-events.log` |
| Reverse target snapshots in `RunRelated.states` | `Type mismatch: After simplification, term` at the recursive state proof; `mutation-states.log` |
| Replace the B `identity_B` proof by `identity_A` | `Type mismatch` at actual nested B identity coherence; `mutation-identity.log` |

The mutation copies are removed. Mutation logs may contain recovery `sorryAx`
from intentionally rejected declarations; the restored final module does not.
These controls verify proof/observation sensitivity, not new runtime fixture
values. The controller separately reported success events/states 12/13 and
failure A 3/3, B 7/7, C 11/11; those measurements were not independently rerun
by this dispatch and are not claimed as this dispatch's fixture evidence.

## Remaining authoring/integration obligations

- Register the module and run its named Lake target and eventual whole build.
- Connect these actual-run theorems to the other agent's compatible-history
  splice/transport algebra. This dispatch deliberately does not claim that
  actual histories equal a particular three-way splice.
- Controller-owned metadata coherence and runtime fixtures remain outside this
  module's ownership. No source-category or process-category laws are claimed.
- Production and normalized reference theorem objectives above are proved;
  no missing reference proof obligation is being hidden as a theorem blocker.

## Budget and telemetry

Budget assessed after production/reference proof checkpoints: stop after
controls/evidence, do not widen into history-splice integration. Manual count is
approximately 55 turns; exact per-agent count/peak telemetry is unavailable, so
a small turn-budget overrun cannot be ruled out. Context remained substantially
below the requested 250k peak by local estimate.

```text
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-handoff/.claude/skills/slice-plan/token-report.py e513127c-9c86-44d6-9ad8-bf82d0bb54c1
no transcript for session e513127c-9c86-44d6-9ad8-bf82d0bb54c1
```

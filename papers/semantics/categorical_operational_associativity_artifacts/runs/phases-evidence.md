# Four actual leaf outcomes and reached phase cuts

## Status

Authoring/prototype follow-up, not integration completion.
Only production-source addition owned here:
`leanncd/experiments/indexed_execution/IndexedOperationalRunsPhases.lean`.
It imports the already registered `IndexedOperationalRuns`. Controller must
register the new module before named Lake/import consumers. No existing source,
runner, lakefile or another agent's module was edited. No commits/merge/push.

## Exact proved statements

- `FailedPhase` and `ReachedPhase` retain the complete binary alternatives of
  `compose_default_phases`: actual default checked runs, exact ordered event
  equations, every state projection, ordered produced ledgers, terminal state,
  complete source store, residual budget and downstream default-run projection.
  `binary_phases` constructs one alternative from validated input and ranks.
- `TriplePhases` has four explicit constructors:
  - `failA`: actual A failure and nested failure tag `upstreamId (upstreamId tag)`;
    no boundary is claimed reached.
  - `failB`: actual A success, actual B failure on `boundaryInput A B ab`,
    nested failure tag `upstreamId (downstreamId tag)`, and the first reached cut.
  - `failC`: actual A/B success, actual C failure on the original BC boundary
    input, nested failure tag `downstreamId tag`, and both reached cuts.
  - `allSuccess`: actual A/B/C success and both reached cuts.
- `triple_phases` constructs this certificate for the actual left nested default
  run using `compose_default_phases` twice and the constructed composite rank.
  Its only supplied evidence is validated A input and the three leaf rank
  certificates. There are no completion, model, execution-agreement or
  selected-action-agreement premises.
- The two-success prefix is retained as `TwoReached`. Its `inner`/`outer`
  binary certificates keep all private states and exact ordered ledgers.
  `b_complete`, `b_projection`, `b_full` prove that the restricted actual AB
  complete store is the actual completed B store.
- `ab_boundary` and `bc_boundary` retain the original
  `boundaryInput = boundaryFromOutput (outputProjection store)` equations.
  `original_bc_input`/`c_input` prove that the actual outer C input equals the
  input from the original BC boundary, not a substituted public execution.
- A `Cut states` contains before/current/after and the exact equation
  `states = before ++ current :: after`. The shared current is inserted once.
  `TwoReached` records both actual cuts, their ordered indices, the full
  upstream-state relation at the first cut and actual outer state at the second.
  The representation allows coincident cuts without concatenating or duplicating
  a shared snapshot. `cut_coincide` proves same-index cuts have the same state;
  `two_reached_empty_B` proves coincidence when B has no graph steps.
- `TwoReached.default_budget` exposes the actual triple budget
  `nA+nB+nC+1` after the second cut plus its preceding snapshots.
- `right_cut` transports any actual left-run cut to the actual right run,
  including all before/current/after state relations, exact cut index, every
  available cell through the full address equivalence and exact produced ledger.
  `two_reached_right` transports both reached cuts and preserves their order and
  possible coincidence. `right_failed`/`right_complete` transport terminal
  endpoints and failure identities through the actual run proof.
- `reference_cuts` transports these same cuts to both actual
  `Program.Executor.run` `referenceSnapshots`. The entire before/current/after
  lists retain both `LedgerInvariant` and the existing full `Relation`
  (published, pending, accumulators). Both normalized cut indices are retained;
  the two cut states satisfy `ReferenceStateProjection`. This uses the already
  proved actual graph transport and accepted execution correspondence, not a
  new runner proof or weakened output-only relation.
- `triple_phases_with_transport` packages the actual four-case certificate with
  the proved actual nested run relation.

## Validation and controls

Final single-file command, exit 0 without warnings; `phases-compile.log`:

```text
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-handoff/leanncd/scripts/lean-file.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-handoff/leanncd experiments/indexed_execution/IndexedOperationalRunsPhases.lean
```

`#print axioms` for `triple_phases`, `two_reached_right`,
`two_reached_empty_B`, `reference_cuts` reports only
`propext`, `Classical.choice`, `Quot.sound`.

Four full-source copied destructive controls were checked with the same
single-file command, each exit 1. Exact replacements are in
`phases-controls.json`; diagnostic logs are `phases-mutation-*.log`.

| Mutation | Observed rejection |
|---|---|
| Duplicate current in the cut equation | `Application type mismatch` in `cut_transport`, then unsolved `cut_exists` |
| Require strictly ordered cuts | `Type mismatch: After simplification, term` constructing `TwoReached` |
| Give B the upstream/upstream failure tag | `Type mismatch: After simplification, term` in actual failB construction |
| Add one to the original BC boundary values | `Type mismatch` in `original_bc_input` |

Intentionally rejected recovery declarations may mention `sorryAx` in mutation
logs; restored final source has none. Mutation source copies are removed.

The controller-owned donor file `IndexedOperationalAssociativityFixtures.lean`
was independently rerun read-only with `lean-file.sh`, exit 0, output in
`phases-donor-fixtures.log`. Observations:

- Actual nested success events/states 12/13; fail A 3/3, B 7/7, C 11/11.
- All four full event/state/terminal comparisons agree.
- Empty fixture: complete, zero events, one state; input-presence metadata retained.
- Actual reference shared-cut observations retain the private A/B values,
  ordered capabilities, pending flags and accumulators; all reference parity
  checks pass. No new donor numerical value was hand-derived.

## Remaining work / boundaries

Register and named-build this module, then perform controller whole-build gates.
These results do not prove the separate history algebra's actual LEFT/RIGHT
leaf-common flattening theorem; the other agent explicitly retains that
obligation. This module neither changes nor reproves runner transport.
No load-bearing theorem blocker was encountered for the requested four-case,
boundary, right-cut or normalized reference-cut objectives.

## Budget / telemetry

Follow-up ended below 50 manually counted response/tool rounds (approximately
40); no known turn-budget breach. Context estimate remained well below 250k.
Exact Copilot turn/peak/cumulative token telemetry was unavailable:

```text
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-operational-handoff/.claude/skills/slice-plan/token-report.py e513127c-9c86-44d6-9ad8-bf82d0bb54c1
no transcript for session e513127c-9c86-44d6-9ad8-bf82d0bb54c1
```

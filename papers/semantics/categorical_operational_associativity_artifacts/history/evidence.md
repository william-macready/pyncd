# History prototype: authoring phase (a)

Base: `8268da1f`. Full process; this is compiled prototype evidence, not an
implementation plan or a claim that actual nested executions have been connected.
Owned implementation: `leanncd/experiments/indexed_execution/IndexedOperationalHistory.lean`.
No existing module, runner or lakefile was edited by this dispatch.

## Representation and observation

`History S E F A` has `done state value`, `step state event tail`, and
`failed state event failure`. Ordinary events retain their pre-state and their
tail's next state. Failure retains its event, occurrence identity and terminal
state, with no second failed-state snapshot. There is no permutation, stuttering,
output-only or private-state quotient.

`History.start`, `states`, `events`, `finish` expose the observations.
`GraphHistory` specializes to the actual `IndexedOpenComposition.State` and
`Event`, failing tag and `Unit` success value. The complete successful state,
not the unit value, indexes downstream continuation. Thus all availability
functions and ordered capability/value rows, including private work, remain
data. `GraphHistory.toRun` preserves the actual success/failure outcome,
events and states exactly, and `GraphHistory.toRun_injective` proves no
information was lost by this encoding.

`GraphHistory.Admissible` permits production/publication ordinary events and
only `undefined tag` at a `failed ... tag` terminal. `CompleteObservation`
requires this certificate. `GraphMetadata` retains the metadata-bearing ordered
input/output `Port` lists, input role function, full Option-valued external input
and validity proof, port uniqueness/completeness, and explicitly supplied adapter
data. `GraphMetadata.ofComponent` obtains these from an actual matched component
and validated input. An empty tensor's presence is not recovered from addresses.

`MetadataTransport` includes tensor and address equivalences, every actual
`Domain` (including raw-coordinate data), and their coherence equation.
`MetadataTransport.Agrees` checks exact port lists after transport, role
functions, the entire Option input binding (including presence), and explicit
adapter transport. `CompleteObservation.Agrees` additionally requires exact
transported history equality. Adapter data must contain the actual intermediate
boundary/domain witnesses; the algebra does not manufacture these.

`GraphTransport` accepts the controller's actual address and Nat identity
bijections. It does NOT certify leaf ownership merely by being a bijection;
integration must supply the controller's leaf equations, not search for an
arbitrary permutation that makes runs agree. Tags and capabilities use the same
explicit bijection, matching the existing execution transport.

## Reusable algebra

`History.Continuation.run : S → A → History S E F B` is success-indexed;
`shared` requires its initial snapshot to equal the completed predecessor state.
`History.splice` invokes it only on success. Its failure case does not evaluate
or require a boundary output or continuation result.

`History.success_cut` proves prefix snapshots end in the exact completed state
and the composite is `prefix ++ continuation.states`, retaining one shared
snapshot; events are concatenated without synthetic boundary events.
`History.failure_absorbs` preserves failure events, states and terminal identity.
`History.Continuation.then`, `splice_assoc`, `splice_congr`,
`GraphHistory.splice_admissible` give reusable composition, not a relation
defined to mean agreement between two selected runs.

`History.map_id`, `map_comp`, `Transport.apply_refl`, `apply_symm`,
`apply_trans`, `apply_splice` prove identity, inverse, composition and
composition compatibility under explicit lawful transports. `Observed` retains
metadata too; `observed_refl`, `observed_symm`, `observed_trans` establish its
transport laws. These generic laws do not replace the remaining task of
instantiating coherent metadata/domain transport for the actual bracketings.

Concrete APIs: `GraphTransport.mapState`, `mapEvent`, `stateEquiv`, `eventEquiv`,
`history`, `mapOutcome`, `mapRun`, `run_inverse`;
`GraphHistory.transport_admissible`, `toRun_transport`.
`mapOutcome` preserves even blocked diagnostics, exhausted/invalid/mismatch
outcomes rather than silently dropping them; admissible ranked histories use
the success/failure subprofile.

## Actual runner and full reference relation

`GraphHistory.stepFuel_exists` proves that every existing `stepFuel` run known
to end complete/failed has an admissible history with EXACT `toRun` equality and
the supplied initial state. The proof follows the existing runner, including
strict undefinedness; it neither changes the runner nor assumes agreement.
`GraphHistory.ranked_default_exists` specializes via existing
`ranked_default_terminal` and `checked_eq_stepFuel` to actual `runChecked` and
its own default budget. No model/execution-completion premise is added.

`ReferenceSnapshot` stores BOTH the graph state and actual `P.Running`, with
`LedgerInvariant` and the FULL `Relation`. `ReferenceObservation` stores an
actual `Executor.Result` and `ExecutionCorrespondence`.
`ReferenceObservation.full_relations` exposes all normalized snapshots via
the existing `referenceSnapshots`. Hence published stores, every pending
occurrence and every accumulator remain explicit; they are not replaced by
graph availability or final outputs. Pending is an actual per-tensor Finset;
the ordered produced ledger is independently retained on the graph side.
Comparing reference observations requires a coherent transport of actual
Running/event/occurrence data, not just graph-history equality.

## Verification and discriminating controls

Commands executed with absolute worktree paths:

1. `bash .../leanncd/scripts/lake-build.sh .../leanncd IndexedExecutionExperiment`
   exited 0, refreshing existing named dependencies.
2. `bash .../leanncd/scripts/lake-build.sh .../leanncd +IndexedOperationalHistory`
   initially reported unknown module: the baseline lakefile uses EXPLICIT
   module globs, not a wildcard. This dispatch did not edit registration.
3. `bash .../leanncd/scripts/lean-file.sh .../leanncd experiments/indexed_execution/IndexedOperationalHistory.lean`
   exited 0 on the final source; full output is `compile.log`.
   The prototype imports the REAL named modules and namespace, not a renamed
   concatenation. Controller integration must register/build the new module.
4. `python3 .../history/verify_mutations.py` rejected all six destructive
   controls; `mutations.json` records actual diagnostics and each log is retained.
5. `python3 .../history/package_patch.py` generates `prototype.patch` from the
   compiled bytes and `source.json` records their SHA-256.
6. Both `git apply --check --reverse prototype.patch` against the compiled
   source and forward `git apply --check --directory=.../history/patch-check`
   into an absent source tree exited 0. No check tree was created.

Kernel-checked fixtures (`Fixtures`):

- Three success phases: ordered events `[10,20,30]`, states `[0,1,2,3]`;
  actual reassociation equality uses the reusable theorem.
- Empty first phase: states `[1,2]`, no invented event or duplicated boundary.
- Private failure after visible work: events `[10,11,99]`, states `[0,1,2]`,
  terminal error `(2,7)`; continuation work never appears.
- Explicit swap transport: events `[99,11,10]`, states `[2,1,0]`, failure
  `(0,8)`; inverse/composite/transported-splice laws checked.
- Negative controls distinguish duplicate cut `[0,1,1,2]`, dropped private
  event `[10,99]`, reversed event order `[20,10]`, and incompatible starts.
- Concrete graph controls distinguish reversed ordered ledgers and private
  availability despite otherwise identical data. Identity transport preserves
  both exactly.
- Cloned existing empty-port fixtures show equal address observations for
  present/missing inputs while their Option bindings differ; metadata retains
  one input port and explicit presence.

Mutation controls change only generated owned copies and clean them afterward:
drop failure event, duplicate snapshot, drop private prefix, reverse ledger,
erase private availability, erase empty input port. All are rejected by actual
Lean checking; some fail a general proof before reaching their regression
fixture. This is not a claim that every individual example was isolated in a
separate mutation run.
The prototype uses the persisted in-tree-copy verifier, not the repository's
`mutation-manifest.sh`: the new module initially had no registered Lake target,
and this dispatch was prohibited from changing registration. The later
execution plan must package these controls for the registered target and run
the standard manifest gate. That gate is not claimed complete here.

`#print axioms` confirms the listed general theorems use only the repository's
ordinary Lean axioms (`propext`, `Classical.choice`, `Quot.sound` as applicable).
No sorry, admit, new axiom or unchecked proof is present.

## Remaining integration obligations and budget

No mathematical blocker was found. The controller/sibling owns actual nested
constructor transport and run integration; this dispatch did not duplicate it.
Still required for the slice: use actual leaf/domain/ownership bijections,
construct whole-boundary continuations from completed states via
`boundaryInput`/`boundaryFromOutput`, establish their shared-snapshot property
including retained upstream private state/ledger, connect BOTH nested default
runs through the binary phase theorem, and instantiate full reference-state,
event, occurrence and metadata transport. Generic history algebra does not
by itself prove any of these actual nested-execution equations.

This dispatch used fewer than 55 assistant/tool rounds (manual count about 50).
No context warning occurred; exact cumulative input/context-peak telemetry is
unavailable. The prescribed `token-report.py` invocation returned
`no transcript for session e513127c-9c86-44d6-9ad8-bf82d0bb54c1`.
No measured token total or precise peak is claimed. No commit/merge/push.

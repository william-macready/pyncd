# Actual binary history composition — bounded follow-up

## Deliverable and registration

New module: `IndexedOperationalHistoryComposition`.
Source: `leanncd/experiments/indexed_execution/IndexedOperationalHistoryComposition.lean`.
Register this ONE module in the experiment's explicit Lake globs.
No existing source or lakefile was edited by this dispatch.
The finalized `IndexedOperationalHistory.lean` and its original patch are untouched;
`composition_source.json` verifies the original source hash.

Separate mechanically generated patch: `composition.patch`.
Generation, owned-copy mutation controls and hash check: `composition_verify.py`.
This is authoring phase (a) evidence, not an execution plan.

## Load-bearing actual-run theorem — complete and compiled

`compose_history A B wire η rankA rankB source source_run` accepts ANY supplied
upstream graph history whose exact `toRun` is the actual upstream default
`runChecked`. It proves existence of a `BinaryHistory` whose exact `toRun` is
the actual composite default `runChecked`.

The proof invokes the EXISTING `compose_default_phases` directly. Its failure
branch reconstructs the whole composite prefix and has no downstream history,
complete upstream store or completed-boundary premise. Its success branch:

1. Retains the completed upstream state and its full store witness.
2. Uses `GraphHistory.ranked_default_exists` on the actual downstream runner,
   with exactly `boundaryInput A B wire store`.
3. Reconstructs every composite suffix snapshot, including ALL upstream
   private availability and the ordered upstream ledger as the fixed prefix.
4. Proves equality of the full shared boundary snapshot.
5. Constructs the result by structural history append and derives exact
   composite events, states and outcome from the actual binary decomposition.

`boundaryInput_from_whole_output` proves this input equals
`boundaryFromOutput` applied to the completed WHOLE upstream output restriction.
There is no invented wire event, fallback `.done`, total continuation on an
impossible state, new interpreter, assumed model/execution agreement or
composite run equality among the relation's premises.

## Full-state reconstruction and reusable soundness

`upstreamState`: all upstream addresses retain their source availability;
every downstream-defined address is absent; produced ledger is the full
upstream ordered ledger under the existing identity map.

`downstreamState completed`: all upstream addresses retain
`completed.available`, including private values; all downstream-defined
addresses retain local suffix availability; produced ledger is EXACTLY
`mapLedger upstreamId completed.produced ++ mapLedger downstreamId local.produced`.

`upstream_reconstruction` and `downstream_reconstruction` prove existing
`UpstreamState`/`DownstreamState` uniquely determine these reconstructed states
over ALL addresses, not just public outputs. `forall₂_reconstruct` and
`projected_history` turn the existing relational run projections into exact
lifted histories. `liftUpstream`/`liftDownstream` reuse actual existing
`mapEvent`/identity maps without discarding any event or snapshot.

`BinaryHistory` is an inductive STRUCTURAL relation:

- Failure stores only the source failing endpoint/tag and the lifted prefix.
- Success stores completed state, full store, actual boundary-derived local
  suffix run, suffix admissibility, and a shared full-state cut.

It does NOT define composition as equality with the composite runner.
`BinaryHistory.unique` proves structural uniqueness using full-store
extensionality and `GraphHistory.toRun_injective`.
`BinaryHistory.sound` therefore proves correctness for EVERY witness of this
structural relation, not only the witness selected by `compose_history`.
`BinaryHistory.admissible` preserves the history admission invariant.

`BinaryHistory.phase_cut` exposes either strict prefix failure or the actual
boundary-derived suffix with ordered
`upstream.states = pre ++ [cut]`,
`result.states = pre ++ suffix.states`,
and exact event concatenation and terminal outcome.
There is NO strict-positivity/distinct-cut requirement; empty phases can share
a cut. The suffix owns the single boundary snapshot.

## Reusable algebra and transport

`SharedSplice.Splice` is a shared-cut splicing relation, not a total
`Continuation S → Unit` with behavior on impossible completed states.
`none` is permitted for an absorbing failure without constructing any
downstream result. `append` is ordinary structural history binding to an
already supplied suffix; `Splice.done` certifies its shared initial state.

`SharedSplice.success`, `failure`, `canonical`, `unique`, `cut`, `start`,
`associative` and `associative_eq` prove reusable composition and full history
associativity, including strict failure absorption when suffixes are supplied.
`SharedSplice.transport` preserves splicing under explicit maps.
`BinaryHistory.splices` connects EVERY structural binary history to this
algebra. `BinaryHistory.transport_splices` specializes transport to the actual
bijective `GraphTransport` API, retaining exact common-space history data.

`left_nested_history` applies the actual binary theorem TWICE, with a
constructed `compositeRankCertificate`, to the actual named `leftBracket`
and nested lifted input. It returns both structural binary-history witnesses
and exact default runner equality. These witnesses expose each reached join
through `BinaryHistory.phase_cut`.

## Verification

Executed successfully, with the worktree's absolute paths:

- `bash .../scripts/lake-build.sh .../leanncd IndexedOperationalHistory`
  refreshed registered dependencies before authoring.
- `bash .../scripts/lean-file.sh .../leanncd experiments/indexed_execution/IndexedOperationalHistoryComposition.lean`
  exited 0 on the final source; `composition-compile.log` has no warnings.
- `python3 .../history/composition_verify.py` rejected all FOUR destructive
  controls: drop prefix; erase retained private upstream ledger; erase retained
  private upstream store; admit an incompatible boundary snapshot.
  Logs are `composition-<label>.log`.
- Standard `mutation-manifest.sh --check` exited 0:
  `manifest OK: 4 entries, 4 selected, every old-string unique`.
  Full registered-target mutation execution remains a controller gate.
- Forward additive and reverse exact-source `git apply --check` both exited 0.
  No check tree was created.

Fixtures clone the existing generic history `first`, `second`, and
`privateFailure`: actual successful shared cut; failure with NO suffix;
event-free coincident cut; states `[0,1,2]` without duplicate boundary; and
rejection of unequal initial/terminal cut states. The general theorems are also
kernel checked. All printed axioms are only `propext`, `Classical.choice`,
`Quot.sound` as applicable; `SharedSplice.associative_eq` uses no axioms.

## Precisely remaining triple/observation obligations

No mathematical blocker was found. This follow-up completes the missing actual
BINARY phase-to-splice bridge and one actual nested binary-history tree.
It does NOT claim all triple integration is complete.

1. Sibling `IndexedOperationalRunsPhases` owns the explicit four actual
   A/B/C-failure/success branches, reached ordered cuts, and right-cut transport.
   This module does not duplicate that investigation.
2. To identify the TWO actual bracketings specifically BY reusable history
   associativity, transport/flatten their nested binary-history witnesses into
   the SAME leaf-owned state/event space, prove the suffix/input squares and
   transported shared-cut premises there, and apply
   `SharedSplice.associative_eq`. The present left tree and existing exact
   parent nested-run observation theorem do not silently substitute for this
   flattening/premise theorem.
3. There remains a separate concrete observation-law gap: generic
   `Observed`/`Transport` has identity/inverse/composition laws, but the chosen
   concrete `CompleteObservation.Agrees` uses `MetadataTransport.Agrees`.
   No bridge or concrete metadata reflexive/symmetric/transitive constructors
   have been proved in the history modules. Whole ports, Option input presence,
   and adapter metadata must be retained while closing this gap.

This follow-up used fewer than 50 assistant/tool rounds (manual count about 45).
Exact context-peak/cumulative-token telemetry remains unavailable; the earlier
prescribed token-report invocation found no Copilot transcript. No context
warning occurred and no precise measured token total is claimed.
No commits, merge, push, production runner changes or original history edits.

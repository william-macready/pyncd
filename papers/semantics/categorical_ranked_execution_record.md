# Ranked operational execution and phase projections

## Result and scope

The proof implementation, release reviews, verified-plan replay and local
integration are complete. Their separate receipts are recorded below.

The nondefault entry point is `import IndexedRankedExecutionSemantics`.
It exports the rank construction, actual graph execution phase theorem and
normalized reference phase theorem for the existing finite decidable,
exact-rational, explicitly wired sealed matched-component profile.
No core language, registry, scheduler, runner, denotational category or
certified source functor was changed.

## Constructed certificate

`IndexedComponentComposition.compositeRankCertificate A B wire rankA rankB`
is a certificate for the actual `(compose A B wire).program`, not an
additional premise. `rankOffset A rankA` sums ranks over every upstream
address and adds one. This includes input addresses and equals one when
there are no addresses; it requires no inhabited maximum.

Upstream ranks remain unchanged. Downstream defined addresses have rank
`rankOffset A rankA + rankB.rank address`. `compositeRank_decreases`
destructs actual guard-admitted occurrence dependencies and transports their
full footprints. Upstream dependencies, downstream internal dependencies and
boundary reads are separate cases. Certified coordinate adapters remain
explicit; neither names nor equal cardinality identify axes.

Ranks establish progress, not totality of registered primitives. A ready
undefined private body still fails.

## Actual graph phase theorem

`IndexedComponentExecution.compose_default_phases` takes exactly the two
matched components, their supplied `Boundary`, validated upstream input and
both component certificates. The composite input is `liftInput`.
The executions are actual default `IndexedOpenComposition.runChecked` runs,
not the older `IndexedExecution.run` or public graph `run` wrapper.

`graph_steps_standalone` derives the constructed transported step append.
`selected_projection` and the run induction transport actual first-enabled
selection. Standalone ranked terminality rules out skipping incomplete
upstream work; list order alone is never treated as a phase barrier.

If upstream fails, the composite fails at `upstreamId tag`. Its events are
exactly the transported upstream events, and every snapshot satisfies
`UpstreamState`: no downstream defined values or produced capabilities.
This includes failures after visible outputs but before private completion.

If upstream succeeds, the theorem derives a complete upstream store and
constructs the downstream input with `boundaryInput`. The theorem supplies
an actual cut state, a prefix snapshot list and residual fuel. All upstream
snapshots project to the prefix plus the cut. `RunProjection` relates the
entire downstream default run to the actual composite suffix, including
success or transported undefined failure, ordered events and every snapshot.
`DownstreamState` retains the entire upstream availability function and
ordered completed ledger, including private values, while projecting
downstream availability and its fresh ordered ledger.

The cut state already is the downstream initial state under the relation.
No wire/copy/boundary action is inserted. Composite snapshots are the prefix
without its last cut copy followed by the suffix snapshots; the cut occurs
once, not twice.

## Reference snapshots and boundary metadata

`reference_default_phases` derives the same explicit cut for
`Program.Executor.run` through existing accepted graph/reference
correspondence. Its composite normalized snapshots have shape
`pre ++ cutRef :: suffix`. Standalone upstream snapshots project to
`pre ++ [cutRef]`, and downstream snapshots project to `cutRef :: suffix`.

`ReferenceStateProjection` witnesses both graph states, the phase relation,
both `LedgerInvariant`s and both full graph/reference `Relation`s.
Consequently published/available values, produced ledgers, pending
occurrences and accumulators are related, not just final outputs.
Events compare through the existing matched event maps and explicit
upstream/downstream renamings; raw dependent event types are not identified.
Undefinedness records its event but no additional failed-state snapshot,
using the existing `referenceSnapshots`.

The input is the whole completed upstream boundary, not a partial
contribution or merely the visible coordinates currently available.
`boundaryInput_outputProjection` exposes its equality with
`boundaryFromOutput` applied to the completed output interface.
`boundary_input_presence` retains empty input tensors using metadata even
when their address type is empty.

## Budgets and validation

The composite default budget is `nA + nB + 1`, not `(nA + 1) + (nB + 1)`.
The phase theorem proves
`remaining + prefix.length = composite.graph.steps.length + 1`,
`prefix.length ≤ nA` and `nB + 1 ≤ remaining`.
The decreasing remaining-action measure bounds the prefix.
Fuel-stability helpers preserve entire actual runs, including snapshots.
No equivalence for arbitrary unequal explicit debug fuel is claimed.

The theorem starts on validated upstream input and does not assume models,
uniqueness, execution completion or execution agreement. The existing
`default_run_correspondence` remains the raw-input/`runValidated` theorem.
Composite full-tensor validation order is unchanged; it is not two
standalone validations, and internal boundary bindings are not new external
input requirements.

## Acceptance evidence

`IndexedComponentRankedExecutionFixtures` adds nine executable checks:

- Private upstream success, private upstream failure after visible `Out`,
  and downstream strict failure, pinning every available vector and ordered
  produced ledger. External input 3 yields upstream `Out = 9`,
  private `Audit = 7/2`, downstream `Out = 81`, private `Audit = 19/2`.
  The successful cut is at zero-based snapshot index 4.
- Reference snapshot normalization and default budgets: success 8 events /
  9 snapshots; upstream failure 3 / 3; downstream failure 7 / 7.
  Composite budget 9 versus leaf budgets 5 and 5.
- A graph-only private-priority control that still closes but permits
  downstream work before upstream private failure; it has no composite match.
- Complete contribution collection (+1 and -1) before boundary publication,
  zero-writer publication, and empty metadata/validation with a valid
  neighbour. The two-invalid-binding case distinguishes validation order
  from UID order.
- A cyclic private-upstream counterexample: downstream produces/publishes 1
  before the composite blocks. `hidden_no_rank` proves its self-dependency
  excludes a certificate; blocking does not imply absence of models.

`IndexedComponentRankedExecutionRankTest` supplies coordinate-sensitive axis
and guarded/colliding-name certificates and actual composite instances.
The nonpalindromic repeated footprint has ranks `[2,3,2,3]`; an unread input
rank 100 is included in the offset bound. Private downstream dependencies
are tested separately from designated outputs.

`IndexedComponentRankedExecutionTest` instantiates both actual graph and
normalized reference phase theorems for private, collection, zero, empty,
axis and guarded-collision donor families. These proof-valued definitions
retain the general theorem's full proposition without transcribing it.
`IndexedComponentRankedExecutionAudit` audits all new proof/test namespaces.

## Authoring controls and verification

- Latest local main base: `a8568ddb`. Existing isolated task worktree was
  prepared with `prepare-worktree.sh`: 8,101 / 8,094 Mathlib oleans, 443
  project oleans; project refresh passed.
- All new Lean modules passed real named-module builds and final-content
  `check-snippet.sh` checks.
- Controller full `LeanNCD Tests IndexedExecutionExperiment` prototype build
  passed. Namespace and main theorem/instance audits use only standard Lean
  axioms.
- The seven-entry post-code manifest passed unfiltered intended-diagnostic,
  restored-build and byte-identical-source checks:
  [fixture results](categorical_ranked_execution_fixture_mutation_results.md).
  These are fixture-source/binding and graph-only counterexample controls,
  not seven live production runner mutations.
- Initial failure-bypass substitutions were type-inconsistent and are not
  credited as runtime kills. Coherent component/boundary/input substitutions
  were then observed at the intended strict-failure assertions and rerun in
  the complete certified manifest.
- Both snapshot controls passed the final unfiltered intended-diagnostic,
  restored-build and byte-identical checks:
  [snapshot results](categorical_ranked_execution_snapshot_mutation_results.md).
  They break live proof consumers; the graph duplicate also breaks independent
  strict/total parity checks.
- All 16 inherited composition controls were rerun unfiltered:
  [inherited results](categorical_ranked_execution_inherited_mutation_results.md).
  Namespace separation, ordered reads, guards, empty metadata, nonconstant
  transport, typed legal neighbours and graph-only counterexamples all passed
  intended-diagnostic/restoration checks. These retain their original control
  classifications, not 16 new live runner mutations.
- The controller reran the full three-target build after all 25 final
  failure/restoration cycles; it passed.

## Process accounting

The helper-layer dispatch reached its 55-turn checkpoint; a validation-only
registration follow-up conservatively exceeded it. This was reported rather
than counted as compliant. The rank, actual run induction and normalized
reference dispatches reported no known turn/context breach.

`token-report.py a285d1df-05fb-4a49-9f7e-23b13dcfa082` reported no transcript.
Cumulative input totals and peak context therefore remain unmeasured with
that tool; neither the 50M authoring target nor 175M slice cap is declared
verified from unavailable accounting.

## Remaining boundary

General trace algebra, process identities/associativity, event-exact
source-category interpretation, broader interfaces, automatic matches and
frontend/backend or numerical refinement remain separate work.
Administrative semantic/source identities are still not event-free core
programs. This slice proves ranked binary operational sequencing and its
state/event projections, not a process category.

## Controller release and actual plan execution

The [verified plan](categorical_ranked_execution_plan.md) was authored in a
fresh context from compiled receipts and mechanically generated patches.
Its six task patches cover 21 exact files. `package.py --check` verified
their SHA256 values and ordered application to a temporary index.

Both whole-branch review lenses completed:

- [Rank/progress/phase soundness](categorical_ranked_execution_artifacts/review_soundness.md):
  clean, no required findings.
- [Runner/state/validation/budget integration](categorical_ranked_execution_artifacts/review_integration.md):
  two P2 findings were fixed and confirmed resolved. The interface's remaining-work
  section still described ranking/phases as open, and replay mutation commands
  needed inherited project-local `TMPDIR`. Only the documentation patch changed;
  all five proof/acceptance patches remained byte-identical.

The controller prepared a new detached replay worktree at the exact
`a8568ddb` base, verified warm Mathlib and refreshed `LeanNCD`.
Only after review adjudication, every task patch was actually applied in
order. Each checkpoint checked patch SHA256 and all cumulative source bytes,
then ran its named build. Task05 reran all three mutation manifests without
filters, sequentially, with local scratch storage: all 25 intended failures,
restored builds and source hashes passed. Namespace/source probes and the full
`LeanNCD Tests IndexedExecutionExperiment` replay build passed.
Task06's exact documentation snapshot and the final 21-file inventory matched.

[Execution checkpoints](categorical_ranked_execution_artifacts/execution_replay.json)
record six passed tasks and 25 successful controller commands;
[actual replay mutation results](categorical_ranked_execution_artifacts/execution_replay_mutations.md)
record 7/7, 2/2 and 16/16 cycles. These are actual replay results, not a
second label on the prototype run. The controller retained the original
implementation history rather than fabricating duplicate replay commits.

Concurrent local main `c48293db` contained five unrelated JAX MQA changes.
It was merged into the candidate without overlap. Every one of the 21 frozen
source hashes remained unchanged afterward, and the controller reran the full
three-target candidate build successfully.

This close-out addendum is intentionally outside task06's frozen record
snapshot; it changes no proof, configuration or acceptance bytes.
The plan author additionally disclosed 37 invocations including batched
calls/wrappers against its 35-invocation aim (13 tool-call rounds).
The final token-report attempt still found no transcript; cumulative accounting
remains unavailable, not silently declared compliant.

## Local integration and cleanup

The candidate was merged into local main as `40cd7ffb`.
The controller's full `LeanNCD Tests IndexedExecutionExperiment` build on
merged main passed (8,930 jobs). All 12 reviewed Lean/configuration file
hashes matched the frozen package; its six ordered patches remained valid.
Before cleanup, the implementation branch and main had identical committed
trees and the branch was confirmed merged.

With explicit user permission, only the primary checkout's two pre-existing
document edits were temporarily stashed and restored. Restoration conflicted
only in the synthesis progress ledger. Resolution preserved the user's
step-column mapping and explanatory prose while retaining the newly proved
rank/phase status. The README was restored byte-for-byte; the synthesis's
original edit payload was independently compared and preserved apart from
that explicit status reconciliation. Both edits remain unstaged. The pinned
temporary stash was dropped only after restoration verification.

The owned replay worktree was removed after verifying that all 21 dirty
paths were exactly the byte-checked replay package. The clean implementation
worktree and its merged branch were removed. All unrelated worktrees and
branches were left untouched.

The user's workspace transition created a separate current chat worktree.
It was fast-forwarded to merged main without creating another worktree and
is retained as requested. This final documentation close-out changes no
proofs or acceptance evidence. Nothing was pushed; local main remains ahead
of `origin/main`.

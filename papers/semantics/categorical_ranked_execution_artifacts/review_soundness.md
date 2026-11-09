# Whole-branch ranked execution soundness review

Scope: `a8568ddb..370b53a4`, including the handoff, live-plan/frozen-record boundary,
actual proof sources, immediate donor contracts and acceptance evidence. Source
is read-only; replay and mutation execution belong to the controller.

## Incremental status

- Handoff and plan/record boundary read. Required claims include full-footprint
  ranks, actual upstream-first default execution, strict/private/empty behavior,
  shared-cut graph and normalized reference state projections, and the composite
  default budget. No execution-agreement or completion premise is permitted.
- Initial substantive proof review began without a finding; the final verdict
  below supersedes that intermediate checkpoint.
- Reviewed `compositeRankCertificate`, both phase-state relations, transition
  and selection transport, the complete graph-run induction and normalized
  reference theorem. The rank bound sums all upstream addresses (including
  inputs), with empty-address offset one. Dependency cases retain actual
  transported footprints and certified boundary coordinates.
- `compose_default_phases` derives terminality from matched ranked execution,
  rather than assuming it. The upstream relation excludes all downstream
  defined availability and ledger entries; the downstream relation preserves
  the entire completed upstream availability and ordered ledger. The induction
  handles undefined writers and empty collector lists without a boundary action.
- The residual-fuel argument uses the actual composite step count plus one.
  Graph snapshots and normalized reference snapshots share a single cut;
  reference projections include both complete `Relation`s (published values,
  pending occurrences and accumulators) and both ledger invariants.
- Completed immediate donor-contract, acceptance and whole-branch scope checks.

## Final verdict

**Clean. No load-bearing soundness or goal-completeness findings.**
Required changes: none. No optional cleanup is requested.

### Checked obligations

- **Ranks:** `compositeRank_decreases` in
  `leanncd/experiments/indexed_execution/IndexedComponentCompositionRanks.lean`
  destructs actual guard-admitted occurrences from `Program.dependencies`, not
  an output-restricted surrogate. Upstream, internal downstream and boundary
  reads use the actual footprint transports. The boundary adapter is the
  supplied certified axis/coordinate equivalence. The nonconstant swapped-axis
  fixture, repeated ordered footprint, private dependency and unread input rank
  100 substantiate the distinctions. The empty-address offset is one.
- **Progress and strictness:** `ranked_default_terminal` derives its dichotomy
  from actual accepted-run correspondence, ranked nonblocking and default
  nonexhaustion. The donor `ranked_progress` uses reachable invariants and
  minimum unpublished rank, admitting undefined evaluation as a failing step.
  Completion covers every writer and collector, including private work and
  zero-writer publication; it is not boundary-output readiness.
- **Operational phases:** `selected_projection` transports first-enabled
  selection, and `stepFuel_prefix` inducts over actual runner transitions.
  `compose_default_phases` takes only matched components, their boundary,
  validated upstream input and the two local ranks. Incomplete upstream work
  cannot fall through to downstream actions. Upstream failure has exactly the
  renamed upstream events/states. After success, `RunProjection` covers both
  downstream completion and strict failure while retaining every upstream
  value and the ordered private ledger.
- **Cut, inputs and budget:** `downstream_at_cut` initializes downstream from
  the derived complete upstream store, not partial contributions. Metadata
  preserves empty tensor presence; `boundaryInput_outputProjection` exposes
  equality with the completed whole output interface. Prefix snapshots omit
  their last cut copy and the suffix begins at that same cut, without a
  transition or synthetic event. The remaining-action bound leaves at least
  the downstream default budget within the composite's own `nA+nB+1`.
- **Reference states:** `reference_default_phases` bridges actual default
  reference runs through existing correspondence. Its normalized composite
  list is `pre ++ cutRef :: suffix`, with the same `cutRef` in both phase
  projections. `ReferenceStateProjection` retains both graph witnesses, their
  phase relation, ordered ledger constraints and both full `Relation`s,
  including pending occurrences and accumulators. Strict terminal outcomes
  transfer through existing `OutcomeRelated`; failed normalization adds an
  undefined event but no additional state.
- **Assumptions and boundaries:** Complete stores and terminality are derived,
  not supplied execution agreement, completion, model-existence or uniqueness
  hypotheses. Ranks are not primitive totality. Raw validation remains the
  existing full-tensor composite validation, not two leaf validations.
  The root imports only proof-library modules in the nondefault experiment.
  No production runner, scheduler, language, registry or category changed;
  no runtime gate or general trace/process laws were added.

### Evidence and execution limits

Read all new Lean implementation/acceptance modules, immediate relevant donor
definitions/proofs, handoff, plan/record boundary, changed status claims,
package verifier and mutation inventories/receipts. Did not reread generated
patch copies. The source probe found no `sorry`, `admit`, `axiom`, `unsafe` or
`native_decide` shortcuts in the new modules. The controller's supplied green
builds, standard-axiom audits and 25 restored diagnostic cycles were supporting
evidence, not substitutes for statement/invariant review.

No build, package replay, mutation or commit was performed by this reviewer.
Clean replay remains independently controller-owned. Only this report was
edited; the concurrently appearing `review_integration.md` was left untouched.

## Budget

Review limit: 45 assistant/tool rounds and approximately 250k context.
Completed in 20 tool-call rounds with batched window reads, plus final response.
No known turn/context breach; exact peak token telemetry was not available.
No subagents, proof edits, builds, mutations or commits performed.

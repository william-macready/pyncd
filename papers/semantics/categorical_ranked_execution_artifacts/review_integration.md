# Whole-branch runner/state/validation/budget integration review

Scope: `a8568ddb..370b53a4`, actual source plus the ranked execution handoff,
plan and record. Read-only review except this report; no mutations, commits,
integration or changes to other worktrees.

## Status

Review complete: both original P2 findings resolved and confirmed below;
no remaining required findings or Lean theorem, runner or state
projection correctness blocker found in the checked scope. Controller clean
replay, replay validation and local integration remain pending gates, not
completed accomplishments.

## Original findings (both resolved)

### P2 — Current interface status still says ranking and phases are unproved

Path: `papers/semantics/categorical_tensor_logic_component_interfaces.md`,
section **10. Assumptions, obligations and remaining work**, paragraphs
**Caller-supplied assumptions** and **Proved static construction facts**.

The current-status text calls rank certificates “additional future premises”
and explicitly says “Composite ranking, phase behavior and process
associativity remain unproved.” This contradicts section 5, the new actual
`compose_default_phases` / `reference_default_phases` APIs and the document's
own concluding paragraph. Readers consulting the remaining-work inventory
are told to redo the slice's completed proof goals.

Minimal fix: remove “future” for the ranked premises, mark constructed
composite ranking and ranked phase/state projections proved, and retain only
the genuinely open process laws in that sentence. This is a current status
section, not a historical record; no historical record needs changing.
The controller must reconcile the reviewed correction with the task06 frozen
documentation package, not change only the working copy and replay stale prose.

### P2 — Replay mutation commands do not constrain scratch storage

Path: `papers/semantics/categorical_ranked_execution_plan.md`, task05
**Mutation classification and exact replay**, three executing
`mutation-manifest.sh` command lines.

Unlike the package-check commands, these commands do not set `TMPDIR`.
`leanncd/scripts/mutation-manifest.sh` allocates its log with
`tempfile.mkstemp`; `mutation-cycle.sh` and `mutate-and-build.sh` allocate
logs and source backups with `mktemp`. The `--cd <W>` option changes cwd,
not the temporary-file directory. In a normal environment the advertised
replay therefore writes source backups/logs to the system temporary
directory, violating the task's project-local scratch restriction.
The earlier `env TMPDIR=<S> ...package.py` is process-local and does not
protect subsequent commands.

Minimal fix: prefix each executing manifest command with
`env TMPDIR=<W>` (a literal absolute path after substitution), inherited by
its Python and shell children. No mutation runner changes or new proof
implementation are needed. Treat this as a replay-instruction safety fix,
not a theorem blocker or a demand to rerun already pending gates now.

## Checked scope

- Handoff requires actual `IndexedOpenComposition.runChecked`, validated
  `Program.Executor.run`, full private state, one normalized cut, strict
  failure, metadata-preserving inputs and composite default fuel.
- Plan distinguishes frozen prototype evidence from pending clean replay;
  task01 deliberately registers later modules and restricts early builds
  to named targets.
- `compose_default_phases` / `upstream_default_prefix` /
  `downstream_default_run` in
  `leanncd/experiments/indexed_execution/IndexedComponentExecutionRuns.lean`
  use matched constructor graphs and actual first-enabled selection.
  Ranked standalone terminality excludes skipping incomplete private work;
  no runtime gate or assumed execution agreement was found.
- `UpstreamState` / `DownstreamState` in `IndexedComponentExecutionPhase.lean`
  retain complete ordered ledgers and upstream availability, exclude
  downstream defined values before the cut and establish the fresh
  downstream initial state. `graph_steps_standalone` derives the actual
  transported append from matched closure.
- `reference_default_phases` / `ReferenceStateProjection` in
  `IndexedComponentExecutionReference.lean` bridge the same graph cut to
  validated `Program.Executor.run` snapshots through both full `Relation`s
  and `LedgerInvariant`s. The normalized cut is shared once; undefinedness
  supplies its event but no duplicate failed-state snapshot.
- Composite residual fuel is derived from decreasing remaining actions:
  `remaining + snapshots.length = nA + nB + 1`,
  `snapshots.length ≤ nA`, `remaining ≥ nB + 1`. Fuel stability helpers
  preserve whole runs; the phase induction does not pretend to invoke them.
- Read all nine executable checks, all twelve graph/reference proof
  definitions and axis/collision rank checks in the three
  `IndexedComponentRankedExecution*` acceptance modules. Private snapshots
  enumerate every scalar address and exact ordered ledger. The graph-only
  reorder and unranked cycle deliberately omit matched/ranked premises.
- Existing `IndexedOpenComposition.execute` validates full tensors in
  contract order; `IndexedCompositionValidated.default_run_correspondence`
  retains `runValidated`. `IndexedComponentModelInputs.boundaryInput` and
  `boundaryFromOutput` use tensor-role metadata, including empty coordinates.
  The simultaneous-invalid fixture distinguishes missing external UID 20
  from unexpected retained/internal UID 0 without requiring any new
  external binding for the wired downstream input.
- `Domain` / `Embedding` in `IndexedComponentTransport.lean` and `Boundary` /
  `downstream` in `IndexedComponentCompositionScope.lean` retain explicit
  certified axis/raw/coordinate transport and tensor roles. No name/equal-
  extent heuristic replaces these adapters.
- `IndexedComponentCompositionRanks.lean` includes every upstream address
  (including unread inputs) in its strict finite offset and separately
  proves the empty-address case. Dependencies use actual full guarded
  occurrence footprints. Axis checks distinguish the supplied swap and
  repeated ordered reads; collision checks include private nonoutputs.
- `IndexedComponentRankedExecutionAudit.lean` audits all new proof/test
  namespaces. The audit implementation rejects reachable nonstandard
  axioms, rather than merely printing selected theorem names; its own
  negative self-test is guarded. Executable `check` throws on mismatches.
- Reviewed all seven post-code fixture/graph controls, two live snapshot
  proof controls and sixteen inherited mixed controls, their classifications
  and prototype result tables. The manifest runner requires intended
  diagnostics from the mutated build, restored green and source-byte
  restoration, and rejects setup refusal. The plan runs all 25 sequentially
  without filters, not only manifest schema checks.
- `IndexedRankedExecutionSemantics.lean` is the new import entry, registered
  only in nondefault `IndexedExecutionExperiment`. No new imports appear in
  production `LeanNCD` or default test sources. Source-category and
  denotational implementations and historical records were not redone.
- Verified `a8568ddb..c48293db` changes exactly the five JAX paths described
  by the plan, without overlap with this branch. The explicit two-file
  primary-checkout stash permission/restoration is recorded; no primary or
  other-worktree operation was attempted.

## Validation performed in this review

- `package.py --check` with project-local `TMPDIR`: PASS, six patches /
  21 files, hashes and ordered index application. The emitter obtains
  patches mechanically from Git diffs; proofs are not transcribed.
- Independent hashes of the actual 21 current packaged files: PASS.
- Read-only inspection of all 25 manifest anchors: every old string occurs
  once, with nonempty targets and intended diagnostic requirements.
- Wrapped named build `IndexedComponentRankedExecutionAudit`: PASS
  (exit 0), covering imported acceptance instances and namespace audits.
- Forbidden-proof-shortcut scan over all new Lean modules: no matches.
- Whole-branch `git diff --check` reports blank context-line whitespace in
  the checked-in `06-documentation.patch` artifact; this is patch-text
  context, not a substantive source defect, and is not a required finding.
- No mutations or clean replay were performed here. The checked-in
  7/7, 2/2 and 16/16 prototype receipts and controller full-three-target
  build are recorded evidence, not newly executed replay gates.
- Only this report was edited by this reviewer. A peer's
  `review_soundness.md` also appeared during review and was not inspected
  or changed.

## Budget

Completed in 26 tool-call rounds plus the final response, below the
45-turn bound. Parallel window reads were batched; no subagents were launched.
Peak context was below the 250k bound by available session context, but no
exact cumulative-token/peak telemetry was available. No known budget breach.

## Narrow fix confirmation

Both P2 findings are **resolved**; integration-review verdict is **clean**.

- The corrected section **10. Assumptions, obligations and remaining work**
  in `categorical_tensor_logic_component_interfaces.md` removes “future”
  from the rank premises, explicitly marks composite ranking and ranked
  graph/reference phase/state projections proved, and retains general
  trace algebra/process associativity as open.
- All six patch hashes match their metadata. Tasks01–05 retain their
  original hashes, and all 21 actual packaged files match their current
  source hashes. Only task06 changed, to
  `bc2e8455df486d4bc79e12ea80b42cbe92f8ff89bcc3ed367ad6dba8dc8115a3`;
  the plan's task06 hash row agrees. The corrected prose is therefore
  reconciled with the frozen replay package.
- The plan defines `<T> = <W>/.cache/categorical-ranked-execution-tmp`,
  creates it before the cycles, and supplies `env TMPDIR=<T>` on each of
  the three actual manifest executions. Its separate command discipline
  and approved two-file stash/restoration guidance remain intact.
- The session-only `files/replay.py` sets `SCRATCH` under the literal
  replay worktree's `.cache`, creates it before executing tasks, and
  passes the corresponding `TMPDIR` through the subprocess environment.
- Reran `package.py --check` with project-local `.cache` scratch: PASS,
  six patches / 21 files, hashes and ordered application. No proofs were
  rereviewed, no builds rerun, and no mutations executed in this follow-up.

This adjudicates only the two corrections. Clean replay, final replay
validation and integration remain controller gates; this review does not
claim they have completed. Lifetime review accounting remains below
36 assistant/tool-call rounds including both final responses, within the
45-round limit; no known context-budget breach.

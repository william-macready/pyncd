# New-session brief: prove source-contract execution correspondence

[Theorem-design brief](categorical_tensor_logic_theorem_brief.md) |
[Categorical synthesis](categorical_tensor_logic_semantics.md) |
[Prototype results](categorical_tensor_logic_lean_prototype.md)

## Task

Implement the conditional Lean correspondence theorem described in the
theorem-design brief. Prove that a correctly matched, closed contract-based
graph and reference program execute correspondingly under matched priorities.
Instantiate the theorem for the independently constructed `Pre`/`Out`/`Audit`
fixture in its strict-failure and successful cases.

This session is authorised to develop **semantic Lean proofs**, not merely
fixture certificates. The earlier proof-free restriction applied to the
executable prototype. Do not add `sorry`, new axioms, unsafe escape hatches,
or computational assertions in place of the general theorem.

Use GPT Sol for complex proof work, with high reasoning effort for difficult
design decisions. Keep delegated tasks bounded rather than dispatching the
entire proof as one unbounded job.

## Start here

1. Read the [theorem-design brief](categorical_tensor_logic_theorem_brief.md)
   first. Its proposed lemma names are not existing declarations.
2. Read [`leanncd/AGENTS.md`](../../leanncd/AGENTS.md) and the applicable
   semantic-node instructions before touching Lean files.
3. Use the repository `slice-plan` and `new-slice` skills. This is a new
   semantic proof capability: choose the Full path, but keep the scope to
   one correspondence slice.
4. Work in an isolated linked worktree based on **latest local `main`**.
   Preserve existing edits and other chats' workspaces. Run
   `prepare-worktree.sh` there; do not cold-build Mathlib.
5. Refresh project-owned oleans through the build wrapper before using
   single-file checks.
6. Audit the existing proof APIs and private graph helpers, then prepare a
   small execution plan. This handoff is not a verified paste-in Lean plan.
   Do not reopen broad categorical brainstorming.

The main checkout is `/Users/williammacready/code/python/pyncd`.
Use the chosen worktree's own paths for implementation and builds.

## The two implementations

**Candidate:** `IndexedOpenComposition.runChecked` in
[`IndexedOpenComposition.lean`](../../leanncd/experiments/indexed_execution/IndexedOpenComposition.lean).
Its state contains available values and produced capability/value pairs.
It derives reference accumulators and pending occurrences only for comparison.

**Reference:** `Program.Executor.runValidated` in
[`ReferenceExecutor.lean`](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean).
It executes the already formalised reference machine, recording legal
contribution, publication, and undefined-operation events.
It is not the production backend or PyTorch.

Do **not** substitute the older `IndexedExecution.run` for the candidate.
Agreement between that runner and the reference is not this task.

## Scope and non-negotiable assumptions

Use common typed tensor declarations, one rational scalar sort,
`RationalReference.registry`/`ops`, finite coordinates and guard-admitted
occurrences, and the runners' default sufficient budgets.

Formalise a supplied source-contract match covering:

- Equal input roles and ordered tensor enumeration, including empty inputs.
- Output-address agreement with all coordinates of reference output tensors.
- A bijection between actual source occurrences and writer entries, with
  unique tags/capabilities and matching destinations.
- Full read-list and local `evalReady` agreement at the source valuation
  and writer unit context, including definedness.
- Canonical collector/fiber correspondence, derived using closure checks
  and the occurrence matching.
- Equality of the entire mapped reference priority list and canonical
  graph step list.

Local body agreement is an explicit hypothesis, not a proof of a generic
translator. Do not replace these obligations with assumed equality of runs,
selected actions, or final results.

Accepted contract closure does not establish source correspondence.
The source program must not supply the graph's writer contract.
The proof must remain conditional rather than claiming automatic contract
inference.

## State and outcome obligations

Define the relation and invariants from the design brief:

- Graph available values equal reference published values at every address.
- Reference pending occurrences are exactly those with no produced
  mapped capability.
- Reference accumulators equal the sums of produced mapped contributions.
- Produced capabilities are valid and duplicate-free.
- Production is append-only; established available values are immutable.

Prove initial agreement and preservation through contribution and
publication steps. A ready undefined body must map to the corresponding
terminal failure. Full completion includes internal nonoutputs; empty
fibers publish zero, while missing inputs do not.

Derive first-eligible agreement from ordered key/step correspondence and
eligibility equivalence. Do not assume it.

Handle these boundaries explicitly:

1. **Validation:** successful closure is a premise. Invalid graph and
   invalid input are different. Matching tensor order is needed to report
   the same first invalid tensor.
2. **Failure snapshots:** the graph returns a failed outcome without
   appending a separate failed state. Reference replay adds that wrapper.
   Compare projected data with the stated normalisation, not literal
   raw-state lists.
3. **Budgets:** prove the default runs do not exhaust. Arbitrary explicit
   debug fuel is outside the initial theorem.
4. **Blocking:** correspondence needs no rank certificate. Add ranking
   only for the separate no-blocking corollary; blocked does not mean
   the equations have no model.
5. **Public closed data:** `Closed` is forgeable. Target the canonical
   successful closure used by `runChecked`. Public `run` revalidates and
   regenerates collectors; its equivalence is a separate lemma if needed.
6. **Empty output tensors:** address lists do not retain their output
   identity. Recover denotation through the reference program's tensor
   roles and shared signatures, not a fictitious standalone graph decoder.

## Proof work and reading map

Read approximately 40-80-line windows around relevant identifiers.
Do not repeatedly load entire large modules.

| Work | Entry points |
| --- | --- |
| Match, closure enumeration, ledger relation, initial agreement | `Writer`, `Contract`, `close`, `State`, `initial`, `producedValue` @ [graph runner](../../leanncd/experiments/indexed_execution/IndexedOpenComposition.lean) |
| Readiness and one-step preservation | `enabled`, private `stepFuel` @ graph runner; `checkReads_iff`, `notReady_iff`, `ready_consistent` @ [Readiness](../../leanncd/LeanNCD/Semantics/Readiness.lean); `consume`, `publish` @ [ExecutableState](../../leanncd/LeanNCD/Semantics/ExecutableState.lean) |
| Priority, terminal classification, bounded execution | `Event.Legal`, `Event.legal_step`, `attempt`, `scan`, `select`, `select_none_iff` @ [ExecutableSelection](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean); `step_decreases` @ [Measure](../../leanncd/LeanNCD/Semantics/Measure.lean) |
| Semantic corollaries | `Execution.reaches`, `run_not_exhausted`, `result_model`, `result_unique`, `result_denotation`, `result_failure`, `run_ranked_dichotomy` @ reference executor |
| Nonvacuous theorem instances | `reference`, `refSchedule`, `contract`, `fragment`, `sourceToWriter`, `parity` @ [independent fixture](../../leanncd/experiments/indexed_execution/IndexedCompositionParityTest.lean) |

Audit these names against the actual tree before relying on signatures.
The private `stepFuel`/`execute` boundary needs a minimal proof interface.
Behaviour-preserving helper extraction is allowed when justified; do not
change the interpreter, publication semantics, or failure policy to ease
the proof.

Prefer a separately split proof layer beside the experimental runner.
Register its actual entry modules with the non-default
`IndexedExecutionExperiment` target. Do not import experimental fixtures
or proofs into production `LeanNCD` merely for discoverability.

Reuse reference model/uniqueness/denotation and failure soundness theorems.
Those are corollaries to obtain, not hypotheses that runs already succeed
or that a model exists.

## Evidence to preserve and extend

The previously observed baseline is 93 executable check rows, including
16 independent parity checks. Reverify before reporting current counts.

The fixture has three distinct scalar tensors, no inputs, and only `Out`
as output:

- `Pre` receives contributions 1 and -1.
- `Out` squares completed `Pre`.
- Internal `Audit` reads `Pre` and selects from a strictly constructed
  reciprocal array.

Observed outcomes:

| Case | Both executions |
| --- | --- |
| Reciprocal arguments 2 and 0 | Six events then `Audit` failure; `Pre = Out = 0`, `Audit` unavailable |
| Reciprocal arguments 2 and 4 | Seven events then completion; `Pre = Out = 0`, `Audit = 1/2` |

Keep the independently authored program and contract independent. Shared
typed expression helpers are deliberate; do not claim independent
verification of expression interpretation.

Preserve the checks that unmapped observations fail explicitly and that
matching errors do not count as parity. The new theorem must be instantiated
for both real cases, not merely proved under an uninhabited or conclusion-shaped
match assumption.

## Validation and finish

From the implementation checkout root, use the wrappers:

```bash
bash leanncd/scripts/lake-build.sh leanncd LeanNCD Tests IndexedExecutionExperiment
bash leanncd/scripts/lean-file.sh leanncd experiments/indexed_execution/IndexedCompositionParityTest.lean
```

Add targeted build checks for the actual new proof modules. Compile every
Lean snippet shipped in an implementation plan. Audit the new main
theorem and fixture instances for axiom dependencies; do not use admitted
proofs or computational trust shortcuts to establish correspondence.

When executable definitions change, rerun the existing baseline and
extension mutation manifests through `mutation-manifest.sh`, and the
reference-only strict-Audit bypass control through `mutation-cycle.sh`.
Do not weaken tests, the match, or the theorem simply to retain a green build.

Completion requires the general conditional theorem, reference-correctness
corollaries, strict and total fixture instances, unchanged executable
behaviour, and a clean whole-branch review. Run the full build yourself.
Update the design/results documents to distinguish proved statements from
remaining targets.

Follow repository integration policy after the proof and review gates:
commit, merge locally into `main`, and remove only this task's branch and
worktree. Do not push. Report exactly what was proved, assumptions retained,
axiom audit, executed checks, and any blocked or deferred item.

Excluded: general component composition, automatic contract generation,
parser correctness, new scalar sorts, floating-point, physical storage,
arbitrary cyclic solvers, and a global St/Br or Turi-Plotkin theorem.
If the scoped theorem itself is blocked, report the precise obstruction
rather than silently broadening or weakening the task.

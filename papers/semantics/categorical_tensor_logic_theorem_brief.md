# Source-contract execution correspondence: theorem-design brief

[Semantics contents](README.md) |
[Categorical synthesis](categorical_tensor_logic_semantics.md) |
[Prototype results](categorical_tensor_logic_lean_prototype.md)

## Purpose and status

The implemented theorem establishes a conditional correspondence between
the **contract-based graph runner** and the existing reference executor.
It should not attempt a general categorical compositionality theorem first.

This brief fixes the scope, assumptions, state relation, and proof
dependencies. **The conditional semantic proof is implemented** in the
separate experimental proof layer. See the
[proof record](categorical_tensor_logic_proof_record.md) for actual declarations,
validation and limits. Historical proposed names below remain design labels;
they are not aliases for the implemented Lean APIs.

The motivating evidence is the independent three-scalar validation:
both executions fail at internal `Audit` after six events in the strict
case, and complete after seven events in its total neighbour.
Mapped terminal observations, events, and intermediate states agree.
Those executable results remain finite evidence. The new general proof uses
a supplied local source-contract match, not those parity checks as hypotheses.

## Contents

- [1. Scope and the theorem to prove](#1-scope-and-the-theorem-to-prove)
- [2. The supplied source-contract match](#2-the-supplied-source-contract-match)
- [3. The state relation and invariants](#3-the-state-relation-and-invariants)
- [4. Step, terminal, and trace correspondence](#4-step-terminal-and-trace-correspondence)
- [5. Proof dependencies and existing results](#5-proof-dependencies-and-existing-results)
- [6. Corollaries and output metadata](#6-corollaries-and-output-metadata)
- [7. Decisions fixed by this brief](#7-decisions-fixed-by-this-brief)
- [8. Completion criteria and exclusions](#8-completion-criteria-and-exclusions)

## 1. Scope and the theorem to prove

Fix common tensor declarations, named $\Delta$, which determine tensor
identities, coordinate domains, and value types. Work with one scalar
sort whose values are exact rationals, written $\mathbb{Q}$.
Tensor identities and coordinate families are finite and decidable.
Named tensors may be arrays; each contribution body returns one scalar.

Use the fixed `RationalReference.registry` and `RationalReference.ops`.
Array construction, selection, finite reductions, and partial reciprocal
remain within the existing typed expression interpretation.

Let:

- $P$ be a well-formed finite reference program.
- $S$ be its complete, duplicate-free ordered priority schedule.
- $G$ be the canonical graph returned by successful closure of an
  independently supplied contract and fragment.
- $\beta$ be a raw tensor-level input binding, which may omit required
  inputs or supply values for tensors not declared as inputs.
- $\eta$ be the validated complete input environment, when validation
  of $\beta$ succeeds.

The exact implementation targets are:

- `IndexedOpenComposition.runChecked` in
  [`IndexedOpenComposition.lean`](../../leanncd/experiments/indexed_execution/IndexedOpenComposition.lean).
- `Program.Executor.runValidated` in
  [`ReferenceExecutor.lean`](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean).

Use their default sufficient budgets. Do not initially quantify over
arbitrary user-supplied debugging fuel.

**Proposed theorem.** Given a supplied source-contract match:

1. Both executions reject the same first invalid input tensor, or both
   accept the same input binding.
2. On accepted inputs, they produce matching complete, failed, or blocked
   outcomes, mapped ordered events, and corresponding state observations.
3. Neither default execution exhausts its budget, and the graph reports
   no internal readiness or collector mismatch.
4. Complete endpoints agree on every coordinate, including internal
   nonoutputs; failed endpoints identify the corresponding occurrence.

No dependency rank is needed for this correspondence. A rank certificate
is an additional premise only for a no-blocking corollary.

Successful graph closure is a premise. A malformed graph is not classified
as an invalid reference input, and closure acceptance does not establish
the source-contract match.

## 2. The supplied source-contract match

Define a proposed `SourceContractMatch` carrying the following data and
obligations. The caller must establish them for a source program and
contract; the theorem does not infer a correct contract from arbitrary source.

### Roles, coordinates, and input enumeration

The common declarations $\Delta$ establish shared typed coordinates.
The contract's input roles must equal $P$'s input roles.
Its ordered tensor enumeration must equal $S$'s enumeration: set equality
alone would not ensure that both validators identify the same first
invalid input when several bindings are wrong.

Contract output addresses must be exactly the addresses of $P$'s
designated output tensors, not an arbitrary selection of their entries.
Every noninput coordinate needs its collector, including unwritten
coordinates and internal nonoutputs.

Output-address equality is only an address-level requirement. It does
not recover the identity of an output tensor with no coordinates.
Section 6 states the resulting output-metadata boundary.

### Occurrence-to-writer identity

Let $O$ be the finite set of actual source occurrences. An occurrence
consists of a defined target, statement identity, and guard-admitted
valuation. Let $W$ be the fragment's finite writer family, indexed by
positions in its writer list. This does not require decidable equality
of entire expression-valued writer records.

Supply a bijection $\chi:O\longrightarrow W$: every source occurrence
has exactly one writer, and every writer represents one occurrence.
The symbol $\chi$ names this matching function.

Each matched writer retains unique tag and capability identifiers.
Write $\operatorname{cap}(o)$ for the capability identifier of $\chi(o)$.
These identifiers are natural numbers, written $\mathbb{N}$, meaning
nonnegative integers. Their uniqueness is checked/proved; they are
not unforgeable tokens.

The matched destination must be the source occurrence's destination.
Together with closure's capability and destination checks, the
bijection should establish that each collector's capabilities match
exactly that destination's occurrence fiber. Proving this enumeration
fact is part of the first lemma, not an assumption that the collected
numerical results already agree. Equal-valued contributions, repeated
statements, and colliding writes remain distinct occurrences.

### Full reads and local body agreement

The matched writer's read list must equal the source occurrence's
full footprint list. This first theorem chooses exact list equality,
not merely equal address sets, so ordered blocked-read observations
can be compared without introducing another normalisation.

For every typed partial store, require equal `evalReady` results for:

- The writer's closed body at its unit context.
- The source statement body at the occurrence's admitted valuation.

This equality includes not-ready, ready-and-defined, and
ready-but-undefined results. The graph's closure independently checks
its own declared footprint against its body.

This is a **local expression obligation**, not an assumed equality
of the two executions. It prevents agreement only at a successful
final environment from hiding a difference in readiness or failure.

Literal syntax equality is not required: the source and writer bodies
can have different context types. A general syntactic valuation-
specialisation operation is not presupposed. A future translator would
need its own proof that it supplies this body agreement.

### Ordered priority correspondence

Map each reference occurrence key to its matched writer step and each
publication key to its collector step.
Require that mapping the entire ordered key list of $S$ produces
the canonical step list of $G$.

The graph generates its steps from contract collector/capability order.
Both runners restart their priority search after each action.

This list equation is the premise from which first-eligible agreement
must be proved. Assuming that already-selected actions agree would
hide the central scheduling obligation.

The theorem is consequently conditional on matched priorities.
Different priorities are not required to produce identical traces or
the same first failing occurrence.

## 3. The state relation and invariants

Let $A$ denote all typed coordinate addresses.
An address is a pair of tensor identity and valid coordinate tuple.
Let $g$ be a graph state and $c$ a reference running state.

Write:

- $\operatorname{Avail}_g$ for the graph's partial available-value store.
- $\operatorname{Pub}_c$ for the reference published-value store.
- $\operatorname{Pending}_c\subseteq O$ for pending source occurrences.
- $\operatorname{Acc}_c(a)$ for the reference accumulator at defined
  address $a\in A$.
- $\mathsf{Done}_g\subseteq O$ for occurrences whose mapped capabilities
  have produced a value.
- $v_o$ for the recorded rational value of a produced occurrence
  $o\in\mathsf{Done}_g$.
- $\operatorname{dst}(o)$ for that occurrence's destination.

Define the proposed relation $\mathcal{R}(g,c)$ using three equalities:

$$
\operatorname{Avail}_g=\operatorname{Pub}_c,
$$

$$
\operatorname{Pending}_c=O\setminus\mathsf{Done}_g,
$$

$$
\operatorname{Acc}_c(a)=
\sum_{\substack{o\in\mathsf{Done}_g\\\operatorname{dst}(o)=a}}v_o.
$$

Equality of partial stores includes both availability and values;
missing is not an available zero. The set difference $\setminus$
removes produced occurrences. The sum is ordinary finite rational
addition, with empty result zero.

Carry a separate graph-state invariant:

- Every produced capability belongs to the closed contract.
- No capability occurs twice in the produced ledger.

Without these conditions, looking up one value per capability could hide
duplicate or extraneous ledger entries.

Also prove transition properties:

- Produced values are appended and never changed or removed.
- Established available values remain available and unchanged.

These are preservation properties across steps, not claims that one
arbitrary state records its whole past. The proof starts at validated
initial states and maintains the relation and invariants through execution.
It does not quantify indiscriminately over public, invented states.

## 4. Step, terminal, and trace correspondence

### Initialisation

Validated input presence must agree at tensor level, including empty
inputs. Initial available/published stores contain only the supplied
input values. Graph production is empty; every source occurrence is
pending; all reference accumulators are zero.

These facts establish $\mathcal{R}$ and the ledger invariant initially.

### Contribution and undefinedness

Pending correspondence and full-footprint agreement establish equal
writer readiness. Local body agreement gives the same successful value
or ready undefinedness.

A successful graph write adds one fresh mapped capability. Its reference
step removes the corresponding occurrence and adds the same value to
the destination accumulator. Published stores remain unchanged.
Finite rational addition establishes the accumulator equality.

On undefinedness, the produced ledger and available values do not change.
The two terminal outcomes carry corresponding source occurrence and
graph tag identities. No further execution follows that terminal outcome.

### Collection and publication

All collector capabilities are produced exactly when its source
occurrence fiber has no pending members. Available-store equality also
matches the unpublished-coordinate premise.

The collector sum therefore equals the reference accumulator, and both
publish the same value. A zero-writer collector publishes zero by the
same argument; it does not make missing inputs readable.

### Completion, blocking, and budget

Full occurrence and collector coverage makes graph completion equivalent
to empty reference pending families and publication of every coordinate.
Output availability alone is insufficient.

Using the ordered key/step equation, prove first-eligible agreement.
If neither is complete and no graph step is eligible, no reference step
is selected either. Blocked diagnostics are compared after mapping their
different constructor formats, not by raw datatype equality.

The complete mapped step lists also identify the finite work bound:
one successful action finishes a previously unfinished writer or collector.
Undefinedness is terminal. Transfer the existing reference no-exhaustion
result, or prove the equivalent remaining-work bound on the graph.
No fairness assumption or rank inference is required.

### Failure snapshots need an explicit observation policy

The graph's undefined event leaves its state unchanged and returns a
failed outcome. Reference `Event.effect` wraps the same underlying running
data in a failed machine state.
Reference replay consequently contains a separate final failed snapshot
that the graph's recorded state list does not append.

The theorem must compare projected data and terminal failure identities,
with this explicit normalisation. It must not claim literal equality
of raw machine-state lists.

## 5. Proof dependencies and existing results

All targets in the first column are proposed new lemmas. They are not
existing declarations.

| Proposed target | Main dependency and obligation |
| --- | --- |
| `match_close_enumeration` | Successful closure and the supplied match give complete canonical writer/collector correspondence and ordered step lists |
| `input_validation_agrees` | Equal tensor order and input roles give equal acceptance or the same first invalid tensor |
| `initial_related` | Accepted inputs establish the state relation and empty valid ledger |
| `enabled_key_agrees` | State relation, occurrence/fiber matching and local body agreement equate readiness and publication eligibility |
| `step_preserves_relation` | Contribution/publication updates preserve the relation and ledger invariant; undefinedness maps to terminal failure |
| `first_eligible_agrees` | Induction over the ordered mapped lists, using enabled-key agreement |
| `complete_blocked_agree` | Full coverage and first-eligible agreement identify terminal classification and blocked observations |
| `default_run_correspondence` | Induction over bounded runs gives mapped traces/endpoints, preserves invariants, and excludes default exhaustion and graph mismatches |

Relevant existing results, verified against the source, are:

- `checkReads_iff`, `notReady_iff`, and `ready_consistent` in
  [`Readiness.lean`](../../leanncd/LeanNCD/Semantics/Readiness.lean).
  They describe readiness and interpretation stability, not the new
  cross-body agreement.
- `consume` and `publish` in
  [`ExecutableState.lean`](../../leanncd/LeanNCD/Semantics/ExecutableState.lean).
  These give the computational reference updates and its budget data.
- `Event.Legal`, `Event.legal_step`, `attempt`, `scan`, `select`,
  and `select_none_iff` in
  [`ExecutableSelection.lean`](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean).
  No-step selection is already related to legal reference steps;
  cross-runner priority agreement is new work.
- `failed_terminal` in
  [`Machine.lean`](../../leanncd/LeanNCD/Semantics/Machine.lean).
- `step_decreases` in
  [`Measure.lean`](../../leanncd/LeanNCD/Semantics/Measure.lean).
- `Execution.reaches`, `run_not_exhausted`, `result_model`,
  `result_unique`, `result_denotation`, `result_failure`, and
  `run_ranked_dichotomy` in
  [`ReferenceExecutor.lean`](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean).

The graph's `stepFuel` and `execute` are private implementation helpers.
Proof implementation must choose a minimal theorem interface for those
definitions or expose a suitable internal one-step helper.
This brief does not assume such a proof interface already exists.
Any refactoring must preserve the observed runner behaviour.

## 6. Corollaries and output metadata

From corresponding completed reference results, reuse `result_model`,
`result_unique`, and `result_denotation`: the common whole store yields
the unique complete model of $P$ and its designated output meaning.
From corresponding failed results, reuse `result_failure` to establish
that $P$ has no model on those inputs.

These are consequences of correspondence and the existing legal
reference execution, not additional model-existence premises.
No model conclusion follows merely from blocking.

Reconstruct outputs using $P$'s authoritative tensor output roles and
the shared declarations. `Program.finalStore` supplies complete values,
and `P.outputProjection` selects whole output tensors.
An empty output has its unique empty value; its identity as an output
comes from $P$, not from an empty list of coordinate addresses.

The current `Contract.outputs` cannot encode that empty-output identity
by itself. Adding output tensor metadata to the contract is deferred.
The first theorem therefore does not promise a standalone graph
output-interface decoder.

With an additional supplied `P.RankCertificate`, transfer
`run_ranked_dichotomy` to exclude blocking and obtain complete-or-failed
classification. Ranking is not needed for state correspondence,
finite execution, or failure soundness.

## 7. Decisions fixed by this brief

- Target the canonical graph used by `runChecked`, not the original
  fixed-program `IndexedExecution.run`.
- Supply source-contract correspondence; do not treat closure acceptance
  as source alignment.
- Use common declarations, one rational scalar sort, the existing
  registry, and local `evalReady` agreement rather than a new interpreter.
- Initially require ordered footprint and priority agreement.
- Prove correspondence from validated initial states with ledger invariants.
- Compare projected failure data, not literal state-list representations.
- Obtain output semantics through the reference program's complete model
  and tensor metadata.

Public `run` revalidates writer claims and regenerates collector steps
from publicly constructible `Closed` data. Extending the theorem to
that entry point requires a separate canonicalisation/entry-point
equivalence lemma. No theorem about arbitrary unvalidated fields is proposed.

## 8. Completion criteria and exclusions

The proof stage would be complete when:

1. The supplied match and state relation are formal definitions.
2. Initial, step, selection, terminal and default-budget correspondence
   are proved without `sorry` or new axioms.
3. The resulting model/failure corollaries reuse existing reference proofs.
4. The independent fixture in
   [`IndexedCompositionParityTest.lean`](../../leanncd/experiments/indexed_execution/IndexedCompositionParityTest.lean)
   instantiates the theorem in both its strict and total cases.
5. The existing executable checks still pass after any proof-interface
   refactoring.

These obligations are now implemented by the separate experimental proof
layer, including both actual fixture instances. This is a conditional semantic
theorem, not merely more finite structural certificates or automatic contract
inference. See the proof record for the exact theorem and retained hypotheses.

Excluded from that stage are general open-program composition,
automatic contract inference, parser correctness, other scalar sorts,
floating-point execution, physical storage refinement, a cyclic solver,
and a general St/Br or Turi-Plotkin compatibility law.
Those can build on the correspondence later without being prerequisites
for this first result.

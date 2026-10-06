# Tensor Logic: Targeted Semantic Gap Audit

## Status and audit brief

**Status: targeted audit completed 2026-10-06.** The original brief and
procedure are retained below; the [results](#audit-results) record the
evidence, qualifications, and recommended next task.

The purpose of this audit is to determine how the existing Lean code relates
to [Tensor Logic: Operational and Denotational Semantics](tensor_logic_semantics.md),
and identify the smallest coherent next formalization task. It is not a
repository-wide correctness certification or a proof of the specification.
The audit must distinguish implementation behavior, reusable infrastructure,
tests, and kernel-checked correspondence claims.

Plan authored against repository revision
`3bdd7f9c9baa98e541b6951223d0bc89c610a23b`, on branch
`agents/tensor-logic-boundary-policy-review`. The boundary-policy document has
uncommitted session edits. The execution baseline and local changes are recorded in the results; the
planning revision was confirmed unchanged.

The authoritative comparison contract is the core semantics specification.
[The boundary-policy note](tensor_logic_boundary_policies.md) and
[Naperian Typing](../NaperianTyping.md) are contextual design documents, not
adopted extensions of that contract. Existing evaluator behavior must not
silently redefine the specification, and differences from a newly proposed
contract must not automatically be labelled implementation bugs.

### Established baseline: multiple LHS definitions are not additive

The existing code is already known not to satisfy the specification's
additive collection of contributions from multiple statements defining the
same LHS. This is a user-confirmed semantic divergence, not an open audit
question. It is not necessary to rediscover or repeatedly demonstrate it.

G04 must still record the concrete representations and implementation
boundaries affected, and distinguish cross-statement collection from
within-statement contraction and scatter-collision behavior. The audit should
identify what would need to connect to an additive collector, without
implementing it. Do not infer that all other obligations fail simply because
cross-statement collection is missing.

In particular, assess the reusable expression, binding, domain, dependency,
and execution machinery independently, including its behavior on the
single-definition fragment. Any correspondence claim restricted to that
fragment must say so explicitly. The known divergence is a formalization
gap relative to the new contract; it is not automatically a bug relative
to the existing code's intended contract.

## Scope and exclusions

Audit the following layers:

1. Core syntax, binding, structural validity, and expression interpretation.
2. Tagged occurrences, additive collection, environments, and models.
3. Read footprints, readiness, dependencies, and the ranked fragment.
4. Accumulation, publication, failures, and logical execution.
5. Existing proof/test evidence connecting those layers.

Read compiler and backend code only as needed to trace those semantics and
determine whether candidate infrastructure is actually used. The initial
audit does not attempt to verify all of Part V's kernel, scheduling, or
storage-refinement contracts.

Explicit exclusions:

- No Lean implementation changes, fixes, refactoring, or new semantic APIs.
- No full implementation plan or several-slice roadmap.
- No configurable-boundary implementation or Naperian integration.
- No general audit of categorical coherence, serialization, performance,
  JAX, or floating-point accuracy.
- No new cyclic solver or executable model checker.

Exact mathematical semantics and floating-point execution must be separated.
A numerical worker may provide useful infrastructure without satisfying an
exact-semiring theorem. A symbolic routing theorem may establish useful
structural facts without proving value interpretation or execution.

## Obligation checklist

Use [Section 28's foundational proof targets](tensor_logic_semantics.md#28-reference-machine-boundaries-and-proof-targets)
to organize the comparison. Split a row when different constructors or
execution paths have materially different dispositions.

| ID | Obligation | Specification sections | Principal discriminators |
| --- | --- | --- | --- |
| G01 | Scoped and typed expressions, signatures, structural access validity | 4, 6, 13-16 | UID/slot identity, rank versus bounds, binder scope, lifted domains, undeclared reads, tensor roles |
| G02 | Strict expression interpretation and primitive definedness | 8, 18 | Zero is not a guard; empty binders have no body instances; array selection requires a complete array; primitive domains remain explicit |
| G03 | Binding and elaboration correspondence | 13-17, 28 | Renaming and capture-avoiding substitution, per-term contraction, diagonal fibers, occurrence/domain preservation |
| G04 | Tagged occurrences and additive collection | 9, 19 | Duplicate statements and colliding valuations remain distinct; cross-statement collection is not overwrite; empty fibers give the additive identity |
| G05 | Complete environments, model relation, and functional denotation | 5, 20-22 | All inputs supplied; all defined tensors constrained; uniqueness of the complete model, not just outputs; cyclic meaning is not implicit iteration |
| G06 | Read footprints and stable ready evaluation | 23.1-23.3 | Whole-array and strict-operand footprints; unavailable is not zero; footprint agreement preserves values and definedness |
| G07 | Coordinate dependencies and ranked execution | 23.4, 26.4 | Coordinate-level rather than tensor-name acyclicity; scan time/version identity; rank certifies readiness, not primitive definedness |
| G08 | Accumulation, completion barriers, and terminal outcomes | 24-25 | Exactly-once contributions, immutable published values, no early publication; success, undefinedness, and blocking remain distinct |
| G09 | Conservation and operational/denotational correspondence | 26, 28 | Model preservation, successful-run uniqueness, undefined-run exclusion of models, decreasing measure, ranked progress, successful schedule independence |

This is the original obligation checklist. G04's cross-statement additivity
gap was an established starting point, not a discovery of this audit.
The assessed dispositions and evidence are in the results below.

## Evidence standards and classifications

The final matrix must separate **semantic disposition** from **evidence
strength**.

Semantic dispositions:

- **Aligned:** an identified representation/path meets the obligation in a
  stated scope, without an unaccounted semantic difference.
- **Partial:** some constructors, cases, or required properties are covered;
  list exactly which are not.
- **Divergent:** identifiable behavior or definitions differ from the
  specification; state both contracts and whether the difference is intentional.
- **Absent:** no corresponding formalization was located in the inspected
  scope; record the search coverage. This is a scoped repository observation,
  not a claim that the construction is impossible.
- **Unresolved:** evidence is insufficient or conflicting; name the concrete
  unanswered question and what would settle it.

Evidence strength must state whether the conclusion comes from definition
inspection, an inspected test, an executed witness, a kernel-checked theorem,
or an assumption. These are not interchangeable.

For each matrix row, record:

1. The precise obligation and linked specification section.
2. Linked definitions and relevant callers/entry paths.
3. Representation differences and supported fragment.
4. Linked tests, with inspected versus executed status.
5. Relevant theorem statements, hypotheses, and proof dependencies.
6. Disposition, confidence/limitations, and formalization consequence.

Inspect theorem statements rather than relying on names or documentation
claims. Distinguish generic algebraic results from concrete `Float` workers;
structural well-formedness from semantic interpretation; and standalone
helpers/spikes from production-reachable code. Where a proof is material,
identify `sorry`, explicit assumptions, and relevant transitive dependencies.
Use `#print axioms` when available and needed; report if a required check
could not be run. Ordinary foundational Lean axioms are not automatically
semantic gaps, but an assumed version of the target theorem is.

Classify findings independently as:

- A bug relative to an existing implementation contract.
- An intentional semantic difference from the proposed specification.
- Missing definitions, coverage, or correspondence proofs.
- An ambiguity, inconsistency, or unsupported argument in the specification.

An unproved but apparently aligned worker is a proof gap, not automatically
a behavioral bug. A proved theorem about a different contract is not
correspondence evidence.

## Execution sequence

### A. Fix the evidence baseline

Record checkout revision, relevant local changes, and the inspected scope.
Confirm the specification's exclusions and exact-value assumptions. Load
the applicable Lean subsystem guidance before following its implementation.
Preserve existing session edits and other work.

### B. Trace semantic representations and reachable paths

Start with [DSL syntax](../../leanncd/LeanNCD/DSL/Ast.lean),
[source compilation](../../leanncd/LeanNCD/DSL/Compile.lean),
[reference entry](../../leanncd/LeanNCD/Eval/Entry.lean),
[scheduled evaluation](../../leanncd/LeanNCD/Eval/Eval.lean), and the
[checked-plan layer](../../leanncd/LeanNCD/Eval/Plan/).
Follow relevant definitions to their callers, validators, and tests.
Consult routed/categorical code only where it supplies a candidate semantic
representation or proof.

Map the specification's expressions, occurrences, environments, stores,
and transitions to existing representations, or record the lack of a
located counterpart. Inventory the G01-G09 obligations without forcing a
one-to-one mapping where the existing architecture differs.
For the established multiple-LHS gap, locate the relevant boundaries rather
than spend the audit re-establishing non-additivity.

### C. Assess behavior and proof coverage

Complete the obligation matrix using the evidence standards above.
For material contradictions between documents, comments, tests, and code,
state the conflict rather than averaging them into an apparent match.
Verify the implementation's existing contract before classifying a mismatch
as a bug. Treat earlier session observations as leads, not sufficient audit
evidence by themselves.

### D. Resolve consequential uncertainty with bounded witnesses

Use existing fixtures first. Where needed, derive a minimal exact-value
example or run a focused existing Lean check to distinguish interpretations.
Prioritize duplicate/colliding contributions, early publication, strict
undefinedness, and internal-tensor completeness. Add empty-domain, binding,
or cyclic examples where they discriminate a disputed obligation.
Use multiple-definition witnesses only if they clarify an unresolved
mechanism or boundary of the known gap, not merely to confirm it again.

For each witness record its inputs, relevant collected equation or rule,
expected behavior under each contract, observed/derived result, and
execution status. A floating-point example can expose overwrite or ordering
structure, but cannot certify an exact-semiring law. Do not create a new
test framework or implement missing semantics to make a witness runnable.

Use the repository's constrained Lean wrappers and smallest relevant
targets. Do not cold-build Mathlib for this audit. Missing executable
evidence must be reported as unavailable, not as a pass or as evidence of
absence. A non-executable specification example can still be a useful
mathematical discriminator if clearly labelled.

### E. Produce the findings and next-task recommendation

Append the completed matrix, classified findings, and necessary witnesses
to this report. Identify reusable aligned infrastructure and the first
load-bearing semantic/proof gaps. Recommend the smallest coherent next
formalization task, with prerequisites and unresolved decisions; do not
expand it into an implementation plan in this audit.

Include scope limitations, checks actually run, checks not run, and explicit
unresolved questions. Do not fix findings during the audit.

## Completion criteria

The audit is complete when:

- Every G01-G09 obligation has an evidence-backed disposition or a specific
  unresolved explanation with a proposed way to settle it.
- Behavioral alignment and proof coverage are recorded separately.
- Consequential divergence claims have concrete definitions, execution paths,
  or discriminating witnesses behind them.
- Statements of absence identify their inspected scope.
- Candidate reuse and the recommended first task follow from the findings.
- The report names its evidence baseline and faithfully lists exclusions,
  checks not run, and remaining uncertainties.

Completion does not require every gap to be solved, every proof to be checked
afresh, or all questions to be settled. It does require that no unresolved
question be silently presented as alignment or correctness.

The expected outcome is an evidence-based choice of the next formalization
task, not a certificate that the prose semantics or existing Lean code is
bug-free.

## Audit results

### Executive conclusion

The repository contains an executable, tested **scheduled tensor evaluator**
and a **checked positional backend**, together with substantial structural
compiler/bridge proofs. It does not yet contain a located formalization of
the specification's complete-model relation or its
contribution/accumulator/publication reference machine.

The established multiple-LHS additivity gap is therefore one part of a
larger semantic separation, not the only missing correspondence obligation.
Even on a single-definition fragment, the current representations do not
cover the general expression language, explicit input/defined/output roles,
or coordinate publication model.

The recommended next task is a small, exact, typed expression-and-readiness
foundation, culminating in read stability. Reuse the current UID/index and
traversal infrastructure where its contract matches; do not retrofit the
Float workers or categorical action before that foundation exists.

No newly adjudicated implementation bug was established by this bounded
audit. The findings below are semantic differences and missing definitions
or proofs. In particular, the legacy/checked scan-causality difference needs
explicit treatment in any future correspondence claim; passing their
respective tests does not make their accepted fragments identical.

### Baseline, coverage, and evidence limits

- Audited revision: `3bdd7f9c9baa98e541b6951223d0bc89c610a23b`.
- Audit checkout: `pyncd.worktrees/tensor-logic-boundary-policy-review`,
  branch `agents/tensor-logic-boundary-policy-review`.
- Local source changes: none under `leanncd/`. The boundary-policy document
  had the session's uncommitted edits; this report was initially untracked.
- Inspected production paths: `DSL/Ast`, `Compile`, `TraverseAxes`,
  `Pipeline/Structural`, `ScheduledValidation`, `Lowering`, `RouteSpec`,
  `RouteFragments`, and `Target`; reference `Eval/Entry`, `Eval`, `Gather`,
  `Contract`, `Scatter`, `Scan`, and `Tensor`; checked-plan `Types`, `Kernel`,
  `Check`, `Coordinates`, `Dense`, `Scan`, `Compile`, `EvalPlan`, `Signature`,
  `Prepared`, and `Adapter`; selected `Bridge/Agreement`/`Realize`,
  `Algebra`, `Mixins/Temporal`, and `Props/Generic`.
- Inspected tests include the executed targets below and the restricted
  property-oracle generator/driver. Additional portfolio documentation was
  used only as a lead, not as live test evidence.
- Absence findings concern the production representations, execution paths,
  and declaration inventory in this revision's `leanncd/LeanNCD/`, with
  focused examination of DSL/Eval, algebra signatures, and bridge/temporal
  proof statements. They do not claim exhaustive inspection of every
  categorical proof, historical branch, or ignored scratch file.
- This audit did not independently prove the prose arguments in Sections
  18-26. It found no settled contradiction in those arguments during the
  targeted comparison, but that is not a proof that they are correct.

### Obligation-to-code matrix

Here **partial** means useful coverage in a stated fragment, not a
correspondence theorem for the complete obligation.

| ID | Semantic disposition | Implementation evidence and supported fragment | Proof/test coverage and limitation |
| --- | --- | --- | --- |
| G01 | **Partial; ordinary-access contract divergent** | [AST](../../leanncd/LeanNCD/DSL/Ast.lean), `buildDeclEnv`, [rank/dtype checks](../../leanncd/LeanNCD/DSL/Pipeline/Structural.lean), and [schedule validation](../../leanncd/LeanNCD/DSL/Pipeline/ScheduledValidation.lean) provide UID axes, declarations, ranks, and entry checks. [Checked assignment](../../leanncd/LeanNCD/Eval/Plan/Check.lean) additionally validates positional geometry; [packing](../../leanncd/LeanNCD/Eval/Plan/Adapter.lean) validates buffer shape/length. Reads nevertheless zero-pad instead of implementing the specification's ordinary in-bounds admission. There is no located general scoped expression judgment over lifted binder domains. | Entry/kernel/scan-compile checks passed. Structural theorems about routed ranks and affine matrices exist, but do not establish bounds, complete signatures/roles, or the full Section 14 judgment. |
| G02 | **Partial; general expression interpretation absent** | [Gather](../../leanncd/LeanNCD/Eval/Gather.lean) and [contraction](../../leanncd/LeanNCD/Eval/Contract.lean) eagerly evaluate product factors and propagate unary-domain errors. [Dense assignment](../../leanncd/LeanNCD/Eval/Plan/Dense.lean) has explicit factor/reduction/term folds. The source AST is sums of products of read/Iverson/unary-read factors, with post-contraction nonlinearities; it has no general nested reduction, tabulation, array selection, or arbitrary primitive-application constructors. | Domain, empty-reduction, scalar, and empty-output fixtures passed. These cover particular computational cases, not a typed interpretation theorem for all Section 13 constructors or an arbitrary primitive registry. |
| G03 | **Partial infrastructure; semantic elaboration/substitution proofs absent** | [Axis traversal](../../leanncd/LeanNCD/DSL/TraverseAxes.lean), UID canonicalization, per-term axis collection, and [affine routing](../../leanncd/LeanNCD/DSL/Pipeline/Lowering.lean) are reusable. Implicit contraction is term-local; diagonal writes lower to scatter. This is not capture-avoiding substitution for the specification's bound-variable language, which is not represented by the current AST. | [RouteSpec](../../leanncd/LeanNCD/DSL/Pipeline/RouteSpec.lean) proves shape/degree/reindexing properties. Route-weave fixtures and the restricted statement-permutation/materialization oracle passed. No located proof connects elaboration to the exact contribution-core denotation. |
| G04 | **Known divergence; some local collection reusable** | [Reference execution](../../leanncd/LeanNCD/Eval/Eval.lean) inserts each completed tensor into a name-keyed environment. [Checked execution](../../leanncd/LeanNCD/Eval/Plan/EvalPlan.lean) stores complete results in slots. There is no located tagged cross-statement occurrence collector. [Local contraction](../../leanncd/LeanNCD/Eval/Contract.lean) preserves term/factor iteration; [scatter](../../leanncd/LeanNCD/Eval/Scatter.lean) has a separate collision policy, while [checked scatter](../../leanncd/LeanNCD/Eval/Plan/Check.lean) admits only collision rejection. | Contract/kernel tests passed for local folds. They do not test or prove additive collection across multiple definitions. This gap was accepted at the outset, not rediscovered by a repeated-LHS experiment. |
| G05 | **Model formalization absent; role contract divergent** | No located counterparts of `AdmEnv`, `Models`, or unique-complete-model functional denotation. [External-name derivation](../../leanncd/LeanNCD/DSL/Pipeline/Structural.lean) classifies inputs as reads not produced; [scheduling](../../leanncd/LeanNCD/DSL/Pipeline/Lowering.lean) retains all top-level statements but drops never-read external names. [Entry](../../leanncd/LeanNCD/Eval/Entry.lean) returns an evaluated environment, not a solution of collected equations over explicit `In`/`Def`/`Out` sets. | Required live-source failures are tested; explicit role/signature completeness and model uniqueness are not established. The evaluator does execute independent top-level statements: it must not be described as dropping all unused internal computations. |
| G06 | **Partial dependency machinery; footprint/read-stability formalization absent** | [Name collectors](../../leanncd/LeanNCD/DSL/Pipeline/ScheduledValidation.lean) and [factor reads](../../leanncd/LeanNCD/Eval/Plan/Kernel.lean) track whole-tensor dependencies. `evalIdx` uses a coordinate map; no located general `Read(E,nu)` over the specified expression language, partial published-coordinate store, or ready-evaluation definition. Scan buffers make in-bounds zero initialization readable, which is not the specification's unavailable-value rule. | Structural collectors/traversal equalities are not read stability, especially its definedness component. No located theorem that footprint agreement preserves the general expression interpretation. |
| G07 | **Partial supported scheduling; no general coordinate-rank certificate** | [Topology](../../leanncd/LeanNCD/DSL/Pipeline/ScheduledValidation.lean) orders whole statements by producer names, with scan-internal exceptions. [Checked scans](../../leanncd/LeanNCD/Eval/Plan/Scan.lean) check explicit advancing read/write geometry and immutable snapshots. This supports a particular scan fragment, not arbitrary coordinate-ranked dependencies. Legacy `readsIterAhead` in [Structural](../../leanncd/LeanNCD/DSL/Pipeline/Structural.lean) checks positive `.shift` offsets, whereas checked scans also reject scaled/cross-axis state reads. | Scan and scan-compile fixtures passed, including scaled-read rejection on the checked path. No located proof relates these recognizers to the specification's rank condition or proves general ranked progress. Their admission rules are not identical. |
| G08 | **Reference-machine representation absent; procedural execution divergent** | [Reference worker](../../leanncd/LeanNCD/Eval/Eval.lean) and [checked worker](../../leanncd/LeanNCD/Eval/Plan/EvalPlan.lean) execute finite schedules of complete tensor operations. Neither is the located implementation of `(sigma, alpha, U)` or the `CONTRIBUTE`/`PUBLISH` rules. [Scan execution](../../leanncd/LeanNCD/Eval/Scan.lean) allocates zero-filled histories; checked scans use zero/base overlays and successor commits. Typed errors exist, but there is no machine-level completion/blocking outcome corresponding to Part IV. | Runtime failures and geometry are tested. Whole-operation ordering can be useful for a later restricted refinement, but a checked constructor does not prove occurrence conservation or the resolved completion barrier. |
| G09 | **Operational/denotational correspondence absent; structural proofs present** | [Compiler/bridge agreement](../../leanncd/LeanNCD/Bridge/Agreement.lean) proves successful compilation yields a well-formed routed graph and that two representation paths realize the same `Br` morphism. [Algebra](../../leanncd/LeanNCD/Algebra/Algebra.lean) supplies abstract interpretation-law signatures, not a located concrete evaluator/model connection. [Temporal properties](../../leanncd/LeanNCD/Props/Generic.lean) are conditional abstract laws, not proofs about `evalScan`. | Bridge type/axiom checks passed; the printed representation-agreement theorem has only standard foundational axioms. No located conservation, model-preservation, successful-run uniqueness, or ranked correspondence theorem for Sections 24-26. |

### Classified findings

#### F01. Additive collection needs a new semantic representation

**Kind:** established divergence and missing formalization.
**Confidence:** high.

The implementation boundary is not merely a different scalar `combine`
function. `evalScheduled` materializes one statement result, then
`env.insert` replaces that name's binding. A checked `AssignPlan` similarly
computes a complete local result and commits it to its destination slot.
Local term contraction and a scatter's collision reducer are different
layers from collecting tagged occurrences across all source statements.

A future additive core needs explicit occurrence identity, destination
fibers, and a collection definition. Existing local folds and coordinate
helpers can be reused only after their coverage is related to those fibers.
Adding another collision policy alone does not close this gap.

#### F02. The full typed expression language is not the current DSL AST

**Kind:** missing definitions/semantic proofs; deliberate narrower language.
**Confidence:** high.

`Factor` is `read | iverson | unaryFn`; `RHSExpr` is a sum-of-products body
plus aggregation/nonlinearity. This is useful for the current einsum-like
fragment, but Sections 13 and 18 also need nested binding, complete array
values, `tab`, `at`, and general scalar/array primitive applications.

The current strict factor evaluation is useful behavioral evidence. It
does not formalize capture-avoiding substitution or complete-array
definedness. An adapter from this DSL to a typed core will need a stated
supported fragment and a value/domain/multiplicity correspondence theorem.
The core should not be forced into the restricted factor representation.

#### F03. Ordinary reads and input roles do not have the core contract

**Kind:** contract divergence, not a newly established implementation bug.
**Confidence:** high.

`gatherRead` and checked dense gather explicitly zero-pad invalid
coordinates. The core specification instead structurally admits ordinary
reads only in bounds; boundary policies remain a proposed extension.
Rank/width validation must not be presented as a proof of strict access
validity.

External inputs are derived from actual reads-minus-produced names.
Consequently, the existing pipeline does not encode the specification's
explicit input set requiring even unused/empty designated inputs. The
checked adapter strongly validates required live buffers, which is reusable,
but it does not establish the complete input-role contract.

Do not attribute internal dead-code elimination to the present scheduler:
it retains `ordered := topoSort lp.stmts`. Its liveness restriction here is
on external names, not wholesale elimination of unused top-level results.

#### F04. Readiness and general operational correspondence are not supplied by scans

**Kind:** missing definitions/proofs plus legacy/checked fragment divergence.
**Confidence:** high for inspected code; source-derived witness qualified below.

The operational specification separates unreadable partial accumulators
from immutable published values. The current evaluators expose complete
tensor buffers, and scan allocation makes zeros readable before later
recurrence writes. Checked causality guards constrain access to these
buffers in an admitted scan fragment; they do not implement the general
publication machine.

The legacy positive-shift check and the checked affine-row causality check
are not interchangeable. In particular, the checked compiler's existing
`S[2*l]` fixture fails as `stateReadNotCausal`, whereas the legacy structural
predicate does not flag `.scale 2`. Any oracle/correspondence claim must
restrict to their common supported fragment or adjudicate the difference.

`TemporalGraded` and `scan_catamorphism` do not close this gap:
the former supplies abstract operations/laws as class fields, and the
latter proves reflexive restriction is identity using `restrict_id`.
Neither states that the numerical scan worker obeys collected equations,
ready evaluation, or the Part IV transition rules.

#### F05. Existing proofs are real, but prove structural/representation claims

**Kind:** missing correspondence proofs; important proof-scope distinction.
**Confidence:** high.

`compile_wellFormed` has the checked type

```text
successful TLProgram.compile p -> tc.WellFormed
```

`buildStep_output_reducesOnlyContracted` establishes an output-weave rank
equality; reindexing theorems establish matrix dimensions and equality to the
constructed affine artifact. None says that concrete evaluation agrees
with the strict expression interpreter or additive collected equations.

`realize_fromThreadedComposed_agree` proves equality of the DSL and extracted
ACSet realization paths as a dependent pair of objects and a `Br` morphism.
Its executed `#print axioms` output was:

```text
[propext, Classical.choice, Quot.sound]
```

There was no `sorryAx` in that theorem's dependency list. The existing test
comment saying it "uses sorryAx" is stale; it was not changed during this
audit. Build output did warn about pre-existing `sorry` declarations in
imported Base modules, so the green check is not a claim that the entire
categorical foundation is sorry-free. This audit did not separately print
the full axiom dependencies of every other structural theorem.

The `Algebra`/`TargetActegory` layer contains abstract signatures. Its
concrete instance/correspondence was not located in the production inventory.
`semiring_choice_split` proves a numerical non-idempotency fact and explicit
Boolean-OR idempotency, not an interpreter-correctness theorem. A future
Boolean formalization must avoid accidentally using Mathlib's XOR Boolean
ring addition when the intended combination is OR.

#### F06. Exact-value proofs cannot be inherited from Float fixtures

**Kind:** refinement boundary and missing proof, not a floating-point audit.
**Confidence:** high.

The generic dense shell stores a shape and `Array alpha`, without a
dependent proof of storage length. Reference arithmetic is `Float`;
the checked workers specialize a shared traversal to `Float`/`Float32`.
Their explicit fold order is meaningful and tested, but exact commutative
semiring laws are not consequences of that execution.

Retain this machinery as a prospective numerical backend. Build the semantic
foundation over an explicit exact carrier/algebra first, then separately
state which numerical refinement guarantee is desired. No general
floating-point equivalence was attempted here.

### Discriminating witnesses

The following separate evidence already executed in existing fixtures from
new mathematical/source-derived examples. None is a rerun intended merely
to reconfirm the established multiple-LHS gap.

| Witness | Discriminator | Evidence status |
| --- | --- | --- |
| W01 | Empty term arrays and zero-extent reductions produce the reduction identity; empty outputs produce empty storage. | Existing [KernelDenseTest](../../leanncd/test/Eval/Plan/KernelDenseTest.lean) fixtures executed and passed. They validate local folds, not a complete model/publication theorem. |
| W02 | Unary-domain failure propagates rather than becoming zero; warnings inferred earlier survive the failure. | Existing [EntryTest](../../leanncd/test/Eval/EntryTest.lean) and unary fixtures in KernelDenseTest executed and passed. |
| W03 | A producer/consumer statement permutation is repaired by scheduling, while dropping a term changes the result. | Existing [PropertyOracleTest](../../leanncd/test/Eval/PropertyOracleTest.lean) executed and passed, including its deliberately wrong materialization control. The oracle uses the current evaluator, not an independent complete-model checker. |
| W04 | Positive-bias, scaled, cross-axis, and slice-dependent captured-state reads are rejected by the checked scan compiler. | Existing [ScanCompileTest](../../leanncd/test/Eval/Plan/ScanCompileTest.lean) causality fixtures executed and passed. |
| W05 | Multiplying an undefined unary read by a false Iverson value does not suppress its failure. | Derived from the eager factor loops and `gather` error propagation; this exact combined example was not executed as a new fixture. Statement guards, in contrast, are not represented by an occurrence-domain field in this AST. |
| W06 | In-bounds self-dependent history can have several models even though a zero-initialized procedural scan chooses one value. | Mathematical/source-derived example below; no new execution fixture was created. |
| W07 | An explicitly designated but unread input must still be supplied under the specification; derived external-name lists do not impose that obligation. | Contract/source-derived example below, not a new executed fixture. |

For W06, use a three-cell exact-real history, base $S[0]=7$, and occurrences

$$
S[l+1]\mathrel{+}=S[2l],\qquad l\in[2].
$$

Every read and write is in bounds. The collected equations are

$$
S[0]=7,\qquad S[1]=S[0],\qquad S[2]=S[2].
$$

Every $(7,7,c)$ is a model, so there is no unique-model functional denotation
and no coordinate-rank certificate. This example has exactly one
contribution per destination coordinate: the issue is not duplicate
contribution collection. Reading the current legacy scan loop predicts
$(7,7,0)$ from its zero allocation, because the last step reads its own
still-zero cell. That predicted legacy result was not separately executed
in this audit. The checked compiler's scaled-read rejection was executed
as W04, preventing the corresponding accepted checked plan.

For W07, let a core signature designate `X` and `Unused` as inputs, with
`Y[i] += X[i]` as its only computation. Supplying only `X` is not a well-typed
input environment, even if `Unused` is empty. The current external-name
functions derive only `X` from reads; adding an unproduced, unread tensor
declaration does not create a required live binding. Relating those two
representations therefore requires explicit role metadata or a restricted
input contract, not simply a buffer-packing proof.

### Checks actually run

The audit worktree has no `.lake` build cache. To avoid a Mathlib cold build,
existing targets were checked in the registered primary checkout
`/Users/williammacready/code/python/pyncd`.

Before checking, SHA-256 comparison found no differences in the 206 tracked
Lean/configuration/toolchain files. The primary Mathlib cache had 8,094
compiled modules for 8,094 source modules. After the first check batch,
comparison of all 189 production/test Lean sources again found no
differences. This establishes source equivalence for the checked paths,
not a claim that arbitrary ignored scratch files or documents match.

Both commands used the repository build wrapper:

```bash
bash leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd/leanncd \
  Eval.ContractTest Eval.EntryTest Eval.Plan.KernelDenseTest \
  Eval.ScanTest Eval.Plan.ScanTest Bridge.AgreementTest

bash leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd/leanncd \
  Eval.Plan.ScanCompileTest Eval.PropertyOracleTest DSL.Pipeline.RouteWeaveTest
```

**Result: all nine requested targets passed.** Their required dependencies
were built/replayed normally; no requested target was skipped. The property
generator reported its documented two-statement enumeration cap of 40 RHS
choices per statement. This is bounded fragment testing, not exhaustive
program/model validation.

Not run: the full project suite, an independent model enumerator, new
undefined-Iverson/input-role/legacy-scan witnesses, mutation cycles,
floating-point refinement checks, or an axiom audit of every theorem.
No proof of the general denotational/operational correspondence was attempted.
No Lean source files or fixtures were changed; running the targets updated
ordinary build artifacts in the warm checkout.

### Recommended first formalization task

Build an **exact, typed expression-and-readiness core**, separate from the
current scheduled Float workers, with one small connected proof target:

> If two complete environments agree on an expression's read footprint,
> its interpretations have the same value or the same undefined result.

The subsequent
[semantic-core feasibility spike](tensor_logic_semantic_core_spike_record.md)
tests this seam in a carrier-parametric scalar fragment, including actual
native-carrier examples and a restricted formal-index connection. Its
prototype choices are not adopted production interfaces.

#### Architectural constraint: preserve scalar and backend flexibility

The user requires at least the flexibility of the existing architecture:
the new formalization must not hard-code one scalar type, storage precision,
primitive implementation, or execution backend. Binary32, binary64, complex
carriers, Lean dense execution, and JAX are architectural use cases, not a
commitment to implement all combinations in this first task.

Separate the following choices:

- **Scalar values and operations:** parameterize expression values and
  interpretation by a carrier and operation/primitive interface. Exact
  reals, rationals, complex values, and Boolean OR/AND algebras must not be
  conflated with one fixed `Float` or one default Lean typeclass instance.
- **Algebraic proof assumptions:** state the laws needed by each theorem
  explicitly. Read stability primarily needs deterministic, footprint-local
  interpretation; exact order-independent collection needs additional
  algebraic laws. Do not require machine floating-point operations to
  satisfy an exact commutative-semiring interface merely to be representable
  or executable.
- **Storage and numerical contract:** keep dtype/precision and their
  representations explicit. `f32`, `f64`, and `complex64` are storage/type
  choices, not interchangeable exact-semiring instances. A backend's
  rounding, fold-order, or approximation contract requires its own stated
  correspondence; do not promise bitwise equality across precisions or
  backends from the exact-value proofs.
- **Execution realization:** define denotation and logical readiness without
  Lean dense arrays, positional backend buffers, JAX APIs, or a compulsory
  scheduling strategy in their interfaces. Existing checked plans and
  backend-specific validators/workers should connect through explicit
  representation and execution contracts.

The first proof can use a simple exact instance for fixtures, but the
definitions and theorem must expose their actual parameters and hypotheses.
Selecting that fixture instance must not select the only future carrier.
Likewise, no backend should be required to support every dtype/primitive:
capability rejection remains explicit and backend-specific.

Reuse the established carrier-shared traversals, storage-kind checks,
closed errors, and checked-private-constructor pattern rather than building
unrelated per-dtype or per-backend semantic stacks. This does not prescribe
a universal backend API or implement a new dtype registry in the first task.

Current-support qualification: the audited Lean AST admits the spelling
`complex64`/`complex128`, but `rejectComplexDecls` rejects both; the current
JAX experiment also supports a narrower fragment than the dense workers.
Preserving room for complex/JAX support must not be reported as preserving
already-working execution of every combination.

Its essential scope is:

1. Explicit finite signatures and input/defined roles; scalar and array value
   types; scoped index valuations and binder-domain lifting.
2. Typed expression constructors with strict interpretation, empty-domain
   behavior, and parameterized scalar operations and primitive
   interpretation/domain contracts.
3. Coordinate read footprints and the read-stability theorem, including
   complete-array selection and primitive definedness.
4. Ready evaluation from a partial published store, justified by that theorem.
5. A small exact fixture set covering renamed/nested binders, empty domains,
   zero times undefined, and selection from an undefined tabulation.

Reuse canonical `UID` identity, affine normalization, and traversal patterns
after stating their correspondence. Do not treat current implicit
contraction as an already proved elaboration into explicit binders.
The existing test style and checked-private-constructor pattern are useful
engineering precedents, not substitutes for the semantic statements.

This first task does not need full Naperian integration, categorical
coherence, backend conversion, configurable boundaries, or a cyclic solver.
Concrete representation and process weight should be chosen when that task
is scoped; this report does not preselect an implementation slice pipeline.

After read stability, the next dependency is tagged collection/models,
followed by accumulator/publication invariants and ranked correspondence.
Only then should an adapter/refinement connect the current supported DSL and
checked workers. This is dependency guidance, not several implementation
plans.

### Unresolved questions and stopping boundary

- Which scoped-expression representation and exact carrier should the first
  implementation use? This is a design choice, not answered by the current
  AST or by passing Float fixtures.
- How should a source adapter declare `In`/`Def`/`Out`, binder domains, and
  ordinary strict access while preserving the current DSL as an explicitly
  narrower/legacy profile?
- Should the legacy scaled-state-read acceptance be aligned with the checked
  backend, or remain an explicit oracle exclusion? The source-derived W06
  would merit a live fixture if that behavior is to be changed. No such fix
  is authorized or attempted by this audit.
- The conservation, model-preservation, uniqueness, and progress arguments
  remain mathematical proof targets. Their mechanization, not another
  backend test pass, is what can substantiate their correctness.

All nine obligations have a scoped disposition and evidence limitation.
The audit stops here: it has located the formalization boundary and selected
a defensible first task, without claiming general correctness or widening
into implementation.

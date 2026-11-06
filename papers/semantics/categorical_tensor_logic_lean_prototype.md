# An effect-sensitive indexed model of Tensor Logic: prototype and results

[Semantics contents](README.md) |
[Tensor Logic specification](tensor_logic_semantics.md)

## Summary

The executable Lean prototype represents computation using two node kinds:
an occurrence evaluates its contribution when all its reads are available,
and a collector publishes a coordinate when all its writers have succeeded.
The runner records available values and produced contributions. Reference
accumulators and pending occurrences are reconstructed for comparison,
not maintained as additional runtime state.

**All 93 executable check rows pass**: 36 baseline checks, 12 strict-effect
checks, 29 open-composition checks, and 16 independent parity checks.
The new parity fixture directly compares the composition runner with an
independently authored three-scalar reference program in a failing case
and its successful neighbour. The executable checks alone do not establish
general program parity; a separate conditional proof is described below.

The result supports a narrower claim than a new categorical foundation:
this representation reproduces the tested reference executions without
storing separate mutable accumulators and pending sets. It does not yet
establish a general compositionality theorem, an independently implemented
expression semantics, or a more efficient implementation.

The prototype is isolated from production imports and uses exact rational
values. The execution modules remain proof-free; a separate experimental
proof layer now establishes conditional source-contract execution
correspondence. Its actual match includes read admission, output roles,
occurrence identities, local body agreement and ordered priorities.
No new axiom or `sorry` is used.

## 1. The question and the semantic contract

The experiment asks:

> Can explicit contribution and completed-value interfaces make execution
> easier to describe, compose, and implement while preserving Tensor Logic?

The specification remains authoritative. The relevant requirements are:

- Statements generate tagged occurrences. Duplicate statements and
  colliding destinations retain multiplicity.
- Guards and finite domains determine which occurrences exist before
  their bodies are evaluated.
- Empty contribution fibers yield the additive identity. Missing inputs
  do not become implicit zeros.
- Incomplete subtotals are not readable tensor values.
- Primitives retain their domains and placement. Nonlinear operations
  cannot be moved across collection without justification.
- Array construction and selection preserve strict definedness, including
  failures in demanded coordinates not subsequently selected.
- All actual contributions and all defined coordinates participate in
  completion, including internal nonoutputs.
- Blocking, undefinedness, and successful completion are different.
  Blocking does not establish that the equations have no model.
- Logical coordinates remain distinct from physical storage locations.

These requirements come from
[core statements](tensor_logic_semantics_part_ii.md#135-core-contribution-statements),
[strict interpretation](tensor_logic_semantics_part_iii.md#18-expression-interpretation-and-definedness),
[models](tensor_logic_semantics_part_iii.md#20-program-models-and-functional-denotation),
and [reference execution](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics).

The [St/Br framework](../graded_prop.md) remains a possible source of
structure, not an assumed optimal foundation. The prototype tests explicit
indexed interfaces without constructing a general graded PROP or imposing
its strongest equations on partial computations.

## 2. The mathematical organisation

### 2.1. Indexed values and strict computations are different

Let $I$ be a finite index set and $A$ a set of values. Write $A^I$ for
functions from $I$ to $A$, representing indexed value families.
For another finite index set $J$, a coordinate map
$r:I\longrightarrow J$ induces a pullback
$r^*:A^J\longrightarrow A^I$:

$$
r^*(v)=v\circ r.
$$

Here $v:J\longrightarrow A$ is a value family, $\circ$ denotes function
composition, and the superscript $*$ names precomposition along $r$.
Affine expressions and guarded domains provide particular coordinate maps;
not every guarded domain needs to be treated as a rectangular shape.

Let $B$ be a set of result values. Define
$\operatorname{Result}(B)=B+\{\bot\}$, where $+$ is a tagged disjoint union
and $\bot$ denotes undefinedness. A partial computation is represented
by a total function

$$
f:A\longrightarrow\operatorname{Result}(B).
$$

Pointwise application, named $f^I$, produces individual results:

$$
f^I:A^I\longrightarrow\operatorname{Result}(B)^I.
$$

Strict array assembly is a separate function,
$\operatorname{sequence}_I$:

$$
\operatorname{sequence}_I:
\operatorname{Result}(B)^I
\longrightarrow
\operatorname{Result}(B^I).
$$

It succeeds exactly when every member succeeds. An empty family succeeds
with its unique empty value. Strict batching is the composite

$$
\operatorname{batch}_I(f)=\operatorname{sequence}_I\circ f^I.
$$

Restricting coordinates before strict assembly can omit a failure that
assembly of the complete family would encounter. Consequently, ordinary
total-function reindexing equations do not hold unconditionally for
strict partial computations.

The prototype preserves this distinction through the existing interpreter.
The strict-effect extension also exercises it inside graph execution and
reference comparison. It does not implement a new effect calculus or a
generic array-assembly node.

### 2.2. Contributions and collectors

For a fixed finite core program, let $O$ be its set of actual tagged
contribution occurrences and $C$ its set of defined coordinate addresses.
An address identifies a tensor and its coordinate. Let
$d:O\longrightarrow C$ assign each occurrence its destination.

Let $K$ be the scalar carrier, with associative, commutative combination
$\oplus$ and identity $0_K$. These data form a commutative monoid.
The implementation fixes $K$ to exact rational values and uses ordinary
addition for $\oplus$.

For each occurrence $o\in O$, let $R_o$ be its complete read footprint:
the addresses that must be available before its body is evaluated.
The body determines a partial function

$$
g_o:K^{R_o}\rightharpoonup K.
$$

Here $K^{R_o}$ is the set of value assignments on the footprint and
$\rightharpoonup$ denotes a partial function.
[Read stability](tensor_logic_semantics_part_iv.md#233-stable-evaluation-from-a-partial-store)
justifies dependence on those coordinates rather than the whole environment.

For a destination $a\in C$, its writer family is
$O_a=\{o\in O\mid d(o)=a\}$. A collector
$\mu_a:K^{O_a}\longrightarrow K$ combines that family:

$$
\mu_a(v)=\bigoplus_{o\in O_a}v(o).
$$

Here $v:O_a\longrightarrow K$ supplies one value per occurrence, and
$\bigoplus$ is finite combination using $\oplus$, with empty result $0_K$.
Equal-valued occurrences remain distinct inputs.

A collector's writer family must be fixed before execution. Runtime
publication requires every member to have produced a successful value.
Structural writer closure and runtime completion are different conditions.

## 3. The implemented graph and runner

### 3.1. Scope and representation

The implementation is parameterised by an existing
`LeanNCD.Semantics.Program` over `RationalReference.registry`, a complete
reference `Schedule`, and a raw input binding.
The registry provides reciprocal and square; ReLU is not a supported
primitive in this prototype.

The program and schedule supply finite, dependent tensor, coordinate,
and occurrence identities. The prototype reuses their existing evidence
rather than adding proofs to construct new fixtures.

The implementation is
[`IndexedExecutionPrototype.lean`](../../leanncd/experiments/indexed_execution/IndexedExecutionPrototype.lean).

### 3.2. Explicit ports and structural validation

`Node.evaluate` contains an occurrence identity, its full read-port list,
and its destination. Its body is obtained from the fixed program.
`Node.collect` contains a defined coordinate and its complete writer-port list.

`fragment` constructs the canonical graph from the program and schedule.
`Fragment.append` concatenates node fragments. `close` validates:

1. The required number of nodes.
2. Unique occurrence and collector identities.
3. Presence of every required node.
4. Exact read, destination, and writer ports.

The validation compares against canonical lists, including their order.
It is not a general account of port isomorphisms.

Fragment recomposition is exercised within one fixed program. The
implementation does not provide phase-typed open contribution ports,
incremental sealing, or arbitrary composition of independently authored
programs. The collection interface makes writer completeness explicit,
but its correctness still depends on validation against the whole program.

### 3.3. Runtime state and eligibility

`State` contains:

- `available`: inputs and completed collector values.
- `produced`: successful occurrence identities paired with their values.
- `failure`: the failed occurrence, if any.

It retains produced values after collection. No separately mutated
pending set or accumulator map is stored.

`enabled` checks eligibility directly from ports:

- An evaluation node is enabled when it has not produced a value and all
  its read ports are available.
- A collector is enabled when its coordinate is unavailable and all
  its writer ports have produced values.

Evaluation is atomic at occurrence level. The runner uses the existing
`evalReady` to interpret the whole body only after the graph's readiness
gate succeeds. An undefined body terminates execution; a successful body
records its contribution exactly once.

If graph eligibility and the interpreter's readiness disagree, the runner
reports `contractMismatch`, not a fallback scheduling decision.
A collector likewise reports `collectorMismatch` if its supposedly
available writer values cannot be assembled.

Atomic evaluation preserves an important boundary: an undefined
subexpression must not be reported early when another required read
prevents the whole occurrence from ever becoming ready.

### 3.4. Inputs, scheduling, and terminal outcomes

Input presence is checked independently from the reference validator:
each supplied tensor must match the program's input role. A missing
zero-coordinate input is still invalid. Typed input values already
carry their coordinate domains; malformed untyped external shapes are
outside this interface.

The runner uses the supplied schedule as priority data, finds the first
eligible graph node, and restarts from the beginning after each action.
It does not call reference `attempt` or `select`.

The executable outcomes distinguish:

| Outcome | Meaning |
| --- | --- |
| `complete` | Every occurrence has succeeded and every defined coordinate is available |
| `failed` | A ready occurrence is undefined; its identity and failure state are retained |
| `blocked` | Work remains and no graph node is enabled |
| `invalidInput` | Tensor-level bindings do not match input roles |
| `invalidGraph` | Structural validation failed |
| `exhausted` | A requested debugging budget ended before an enabled step |
| `contractMismatch` / `collectorMismatch` | An internal graph contract was violated |

An `unsupported` outcome constructor exists, but the runner does not
implement general feature admission through it.

The default budget is the number of graph nodes plus one. Successful
actions finish previously unfinished nodes, and undefinedness is terminal.
No new termination theorem is claimed. Running the blocked-cycle fixture
requires no rank certificate and does not solve its equations.

## 4. What the reference comparison checks

### 4.1. Shared and independent components

The reference entry point is `runValidated` in
[`ReferenceExecutor.lean`](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean).
It validates inputs and returns the existing exact-reference execution.

The graph shares the program, schedule data, scalar operations, body
interpreter, and footprint construction. Therefore agreement does not
independently validate expression interpretation.

The graph independently computes node eligibility, input presence,
collector completion, its execution loop, and its state changes.
`graphSnapshot` derives a reference-shaped observation:

- Published values are the graph's available values.
- An accumulator is the sum of contributions already produced for its
  destination.
- Pending occurrences are those without produced values.

This derivation is used for observation only. It does not drive execution.

### 4.2. Intermediate states, not just final outputs

`compare` checks four components:

- Matching terminal outcome, including the located failure occurrence.
- Equal snapshots at every recorded step.
- Matching event identities and exact values.
- Matching unavailable-read observations for blocked states.

Snapshots enumerate all declared coordinates, including internal
nonoutputs. They retain unavailable versus available-zero distinctions,
derived accumulators, pending identities, and tensor-level input presence.
They compare ordinary data rather than dependent proof fields.

Reference snapshots are reconstructed from its initial state and
recorded event effects. This is a comparison of the witnessed execution,
not an independent reference interpreter.

The comparison is deliberately stronger than result equality under a
matched priority. Across different priorities, the tested successful
stores agree; identical traces or first failure locations are not asserted.

## 5. Observed results

### 5.1. Executable coverage

[`IndexedExecutionPrototypeTest.lean`](../../leanncd/experiments/indexed_execution/IndexedExecutionPrototypeTest.lean)
contains **36 passing executable check rows** and **18 unchanged
graph/reference comparison invocations**. These counts are assertions
and invocations, not distinct programs or exhaustive schedules.

| Evidence | Passing checks and observations |
| --- | --- |
| Duplicate contributions | Exact complete-store entries are 4, 0, 0; five execution events |
| Colliding tagged valuations | The shared destination is 14 under both tested priorities; seven events in the original priority |
| Writer completion | After one of four writers succeeds, the destination remains unavailable and its collector is disabled |
| Missing versus zero | A produced zero exists as a contribution while its destination remains unpublished |
| Failure | Ready undefinedness matches; failure snapshots retain earlier produced contributions and published values |
| Guards and empty fibers | Excluded bodies are not evaluated; zero-writer coordinates complete |
| Empty input declarations | Present empty input is accepted; absent empty input is rejected; empty defined tensors complete |
| Whole-program completion | An available output does not hide an unfinished, failing internal nonoutput |
| Coordinate dependencies | Original and reversed chain priorities match; the checked dependent coordinate values are 3 and 4 |
| Unranked cycle | The graph and reference both block, retaining missing-read observations |
| Nonlinear placement | Per-occurrence reciprocals collect to $3/4$, not $1/6$; square is also exercised |
| Debug budgets | Unfinished work at zero budget is exhausted, while an already complete empty computation remains complete |
| Graph construction | Recomposition is accepted; missing node, duplicate tag, missing writer and dropped read ports are rejected |
| Expression-only strictness | Existing pins cover strict selection/tabulation, undefined nonselected work, zero strictness, empty reduction, and demanded empty-array undefinedness |
| Total finite families | Concrete pushforward grouping/composition and reindex composition checks pass |

The strict-array row is expression-level evidence from the existing
interpreter, not a graph/reference adapter for array selection.
The finite-family row tests concrete laws; it is not a batched graph
kernel or a general proof of those laws.

### 5.2. Implementation mutation controls

Both entries of the
[mutation manifest](categorical_tensor_logic_prototype_mutations.json)
were executed against the prototype:

| Control | Deliberate defect | Observed failure | Restoration |
| --- | --- | --- | --- |
| P1 | Seed every collector with one instead of zero | `duplicate-exact-store` and `tagged-final`, among other assertions, fail | Source restored byte-identically; build passes |
| P2 | Remove the full-footprint readiness condition | `coordinate-chain` and `full-footprint-waiting`, among other assertions, fail | Source restored byte-identically; build passes |

These controls alter implementation behaviour, not expected assertion
values. The manifest also checks that the intended failure diagnostics
appear. Separate malformed-graph checks exercise validation rejection;
they are not additional source-mutation cycles.

### 5.3. Build and review

The full `LeanNCD` and default `Tests` build, the non-default experiment
target, and fresh test-file elaboration all passed in the integrated
checkout. The whole-branch code review found no significant issues.
The new modules introduced no source warnings; pre-existing repository
proof warnings remain outside the prototype.

### 5.4. Separate effect and composition extensions

The extensions are deliberately separated:

| Module | Executable checks | Evidence |
| --- | --- | --- |
| [`IndexedEffectSequencingTest.lean`](../../leanncd/experiments/indexed_execution/IndexedEffectSequencingTest.lean) | 12 | Strict two-entry tabulation followed by selection fails on an undefined nonselected reciprocal; the all-defined neighbour returns $1/2$. Both and the deliberately non-equivalent select-first shortcut match their respective reference executions. |
| [`IndexedOpenCompositionTest.lean`](../../leanncd/experiments/indexed_execution/IndexedOpenCompositionTest.lean) | 29 | Independently built writer fragments, closure, consumer readiness, join order, identity checks, failure, empty declarations, and composition with strict effects. Two checks rerun original-runner reference controls; they are not comparisons of the new composition runner. |

[`IndexedOpenComposition.lean`](../../leanncd/experiments/indexed_execution/IndexedOpenComposition.lean)
does not take a `Program` or reference `Schedule`. A separately supplied
`Contract` lists tensor roles, all defined-coordinate collectors, readable
and output ports, and the complete permitted writer capability IDs.
A capability ID is a checked numeric identity, not an unforgeable token.

`combine` rejects overlapping tags or capability claims. `close` requires
exact capability coverage, matching destinations and body footprints,
readable ports, and complete collector coverage, including nonoutputs and
empty fibers. It generates collectors from this contract, rather than a
canonical reference program graph.

The contract remains the declared completeness assumption: the experiment
does not discover all possible future writers. `sealAssembly` and `extend`
distinguish an open assembly from a sealed one and reject later extension.
`Closed` is publicly constructible data, not a proof of validation:
public `run` revalidates the writers and regenerates collectors, while
`runChecked` validates a contract and fragment directly.
Forged empty graphs and forged collector ports cannot bypass these entry
points.

The central composition fixture supplies contributions 1 and -1 to an
intermediate, then squares its completed value. The intermediate and result
are both zero; the intermediate stays unavailable after only one writer.
Reversed and parenthesised joins preserve results. Distinct equal-valued
writers retain their multiplicity.

The combined effect case has an additional internal nonoutput writer that
reads the completed intermediate and evaluates strict array selection.
Its undefined nonselected reciprocal causes failure even though the
designated output is already available. The total neighbour completes
with internal value $1/2$. The invalid select-first rewrite instead
succeeds, and is explicitly distinguished from the strict computation.

Four extension implementation controls in the
[extension mutation manifest](categorical_tensor_logic_extensions_mutations.json)
exercise bypassed strict assembly, weakened all-writer completion, omitted
capability coverage, and execution of forged rather than validated
collector ports. Each mutation produced its named assertion failure and
restored byte-identically with a passing rebuild.

### 5.5. Independently authored reference validation

[`IndexedCompositionParityTest.lean`](../../leanncd/experiments/indexed_execution/IndexedCompositionParityTest.lean)
adds 16 passing checks. It declares three distinct scalar tensors:
`Pre` and `Audit` are internal, only `Out` is an output, and none is an
input. The reference program and fragment contract are authored separately.
Neither supplies the other's writer family or execution structure.
Both deliberately reuse the same typed expression helpers and interpreter.

The computation has four contributions:

```text
Pre += 1
Pre += -1
Out += square(Pre)
Audit += Pre + first(strict_array(reciprocal(2), reciprocal(other)))
```

This is explanatory notation: `+=` introduces a contribution, `strict_array`
requires both entries to be defined, and `first` selects the first entry
only after the array is constructed. The parameter `other` distinguishes
the two executed cases.

| Case | Observed reference and composition outcome |
| --- | --- |
| `other = 0` | Six events, then failure at `Audit`; `Pre = 0` and `Out = 0` are published, `Audit` remains unavailable, and its occurrence remains pending |
| `other = 4` | Seven events, then completion; `Pre = 0`, `Out = 0`, `Audit = 1/2`, with no pending occurrences |

The checks explicitly verify no-input and output roles, the mapping between
source occurrence identities and graph tags/capabilities, ordered events,
and every recorded available/accumulator/pending snapshot.
The terminal, event and intermediate-state comparison components are all
true in both cases. Failure trace observations account explicitly for the
two runners' different representations of the terminal failure snapshot.

Unknown source occurrences, unknown graph tags, and incorrect capability
observations return explicit errors; matching observation errors cannot
count as parity. A graph-only shortcut is also checked to disagree with
the strict reference execution.

The reference-only mutation V1 replaced `Audit`'s strict array evaluation
with its selected valid reciprocal, leaving the graph unchanged. The
failure/parity assertions broke as intended; the source was restored
byte-identically and rebuilt successfully. This is a hand-run mutation
cycle, separate from the earlier manifests.

Constructing this exact fixture required new structural evidence:
scalar read bounds/admission, `Program.output_defined`, and the reference
schedule's tensor/key duplicate-freedom and coverage. These certificates
allow the existing executor to accept the concrete fixture; they do not
prove equivalence of the two execution models.

## 6. What the experiment establishes

The tested executions support a modest structural improvement:

- Explicit read ports suffice for the candidate's readiness gate.
- Explicit writer ports express the collection barrier.
- Produced values and available values suffice to reconstruct reference
  accumulators and pending sets for comparison.
- A separate execution loop reproduces the tested intermediate states,
  failures, blocking diagnostics, and complete stores.

This is more than checking final tensor numbers. It tests the state
relationship throughout execution and catches meaningful defects in
collection and readiness.

The baseline `close` still validates against a fixed whole program.
The composition extension removes that dependency, checking independent
fragments against a declared writer contract instead. The parity fixture
now connects one such independently assembled contract to a separately
declared reference program. This is stronger evidence for interface-based
composition, but not a proof that every composition obligation is local
or that contracts can be inferred from arbitrary source programs.

### Conditional semantic correspondence

The [proof record](categorical_tensor_logic_proof_record.md) identifies
`default_run_correspondence`: accepted canonical closure and a supplied
`SourceContractMatch` imply agreement of the actual `runChecked` and
`runValidated` default executions. The proof covers input rejection,
ordered events, related intermediate data, complete/failed/blocked endpoints,
and sufficient budgets. Failure snapshots omit the reference-only final
failed wrapper. Complete endpoints transfer whole-store model, uniqueness
and output denotation; failure transfers absence of a model. Ranking is only
needed for the additional no-blocking corollary.

The independently authored fixture supplies real matches for every rational
`other`, with explicit strict (`0`) and total (`4`) theorem instances.
The numerical endpoint observations above remain executable evidence,
not substitute hypotheses for the general proof. Contract inference,
general component composition and independent expression interpretation
remain outside the result.

Nor is storing all produced values necessarily cheaper than incremental
accumulation. The experiment measures semantic fidelity, not execution
speed, memory reduction, or optimality of the abstraction.

## 7. Remaining limitations and useful next experiments

The implemented scope does not include:

- Exhaustive graph-state or reference-schedule exploration.
- Full bounded-history execution or a compact symbolic scan adapter.
- Arbitrary source admission, general independent source-program
  composition, or a generic reference adapter beyond the concrete
  three-scalar validation fixture.
- A general effect-sensitive indexed category or Turi-Plotkin
  compositionality theorem.
- Primitive-level execution, physical memory reuse, floating-point
  arithmetic, or general cyclic solvers.

Existing programs and schedules carry proofs for roles, typed reads, and
complete enumeration. The exact parity fixture now supplies those
structural certificates directly. Constructing and relating arbitrary
new fixtures remains separate from proving semantic correspondence.

The most informative follow-ups are:

1. Extend independent reference comparison beyond the tested three-scalar
   cases, preserving explicit source/contract identity mappings and supplying
   the hypotheses of the now-proved conditional correspondence theorem.
2. Exercise a bounded history while retaining coordinate-level causality
   and the whole-history output contract.
3. Explore small graph schedules with explicit limits, distinguishing
   graph-only exploration from independently compared reference priorities.

These experiments should precede claims that the candidate is a simpler
general foundation. No change to the fundamental Tensor Logic semantics
is justified merely to make the abstraction easier to express.

## 8. Reproducing the checks

From the checkout root:

```bash
bash leanncd/scripts/lake-build.sh leanncd IndexedExecutionExperiment
bash leanncd/scripts/lean-file.sh leanncd experiments/indexed_execution/IndexedExecutionPrototypeTest.lean
bash leanncd/scripts/lean-file.sh leanncd experiments/indexed_execution/IndexedEffectSequencingTest.lean
bash leanncd/scripts/lean-file.sh leanncd experiments/indexed_execution/IndexedOpenCompositionTest.lean
bash leanncd/scripts/lean-file.sh leanncd experiments/indexed_execution/IndexedCompositionParityTest.lean
```

The first command builds dependencies and the experiment. The second
elaborates the test file afresh, executing its checks even when Lake has
cached the module.

To repeat the baseline and extension mutation controls:

```bash
bash leanncd/scripts/mutation-manifest.sh leanncd papers/semantics/categorical_tensor_logic_prototype_mutations.json
bash leanncd/scripts/mutation-manifest.sh leanncd papers/semantics/categorical_tensor_logic_extensions_mutations.json
```

The experiment is non-default and not imported by production `LeanNCD`.
Running the full default build alone does not substitute for explicitly
building `IndexedExecutionExperiment`.

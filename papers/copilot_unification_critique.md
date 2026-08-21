# Critique: nonlinearity inside scan blocks

## Scope

This document reviews
[`docs/superpowers/specs/2026-08-21-nonlinearity-in-scans-design.md`](../docs/superpowers/specs/2026-08-21-nonlinearity-in-scans-design.md)
against the Backend Eval IR implementation at `549adb6`.

The proposed high-level direction is sound:

- introduce a scan-local closed step sum that excludes nested scans;
- reuse the existing checked nonlinearity payloads and workers;
- preserve Backend IR's positional, UID-free representation;
- treat persistent state, scratch, and base outputs uniformly as values produced by block steps.

However, the draft currently misses one pipeline-level blocker and several important
indexing/publication details. As written, an implementation following it literally would likely fail
before reaching `compileScan`, or produce invalid slot and axis positions.

## Critical weaknesses

### 1. The design assumes scan nonlinearities reach `compileScan` unsplit

The proposed shared chaining helper assumes `compileScan` receives an original statement whose RHS
contains the contraction and nonlinearity together. But `TLProgram.compileToScheduled` runs
`splitNonlins` before producing the `ScheduledProgram` consumed by `prepareEvalPlan`.
`splitScan` applies `splitStmt` independently to every base and recurrence statement.

A nonlinear scan statement is therefore already transformed into:

1. a `%nl...` linear statement carrying the original scan placement slots; and
2. the named nonlinear statement carrying the same scan placement slots.

This conflicts with the current scan classifier:

- In a recurrence, the `%nl...` intermediate has advancing `.iterNext` slots but is not a persistent
  state name, so it is rejected as `orphanAdvancingResult`.
- In a base block, `%nl...` becomes a base destination and is therefore incorrectly classified as
  another persistent state candidate.
- A direct nonlinear state is no longer represented as one source statement by the time
  `compileScan` sees it.

This also makes the claim that "essentially zero new nonlinearity-specific code gets written for the
scan case" inaccurate.

**Suggested improvement:** add an explicit architectural decision for the split boundary. The
cleanest option appears to be:

- keep top-level splitting unchanged;
- stop splitting statements inside `ScanStmt.scan`;
- let the plan compiler lower each unsplit scan statement into its block-local
  assign/nonlinearity chain;
- verify that the legacy evaluator remains equivalent on unsplit scan statements;
- document the effect on the routed path, which already collapses scan bodies.

If changing the common pipeline is unacceptable, the alternative must define a scan-aware split
transformation that produces a genuine block-local scratch value without scan placement slots. The
current generic `splitStmt` output cannot simply be consumed as-is.

This issue should be promoted to the first architecture section, not left to the implementation
plan.

### 2. `resolveNonlinAxis` does not already return a block-local axis position

The draft says the local-axis restriction needs "zero changes" because `resolveNonlinAxis` ignores
`.iterAt` and `.iterNext` when finding `.freeNorm`. That establishes which axis is marked, but it
does not produce the right positional index.

`resolveNonlinAxis` currently returns the marked slot's position in the complete LHS slot list. This
works at top level because all admitted slots become output dimensions.

Inside a scan, iteration slots are removed from the local slice shape. For example:

```text
G[l + 1, j.] := softmax(...)
```

has LHS positions:

```text
0 = iterNext l
1 = freeNorm j
```

but the block-local output has shape `[|j|]`, so its axiswise position is `0`, not `1`. Returning `1`
causes `axisPositionOutOfRange`. Interleaved multi-axis placements make this easier to get wrong.

**Suggested improvement:** redefine or generalize the resolver so it returns the position among
retained local output slots:

- count only `.free` and `.freeNorm`;
- exclude `.iterAt` and `.iterNext`;
- still reject missing, multiple, or inappropriate markers;
- preserve the existing top-level result as a special case.

The design should state this mapping explicitly and include an interleaved-slot example.

### 3. The slot-allocation and publication contract is underspecified

Current scan compilation relies heavily on "one source statement equals one assignment equals one
new slot":

- base destination: `baseInputCount + bi`;
- step destination: `stepInputCount + ri`;
- base writes point to that destination;
- scratch/state name maps point to that destination;
- causality diagnostics use assignment index as source statement index.

A nonlinear statement instead produces:

- an internal preactivation slot;
- a final nonlinear value slot;
- two block steps.

The design mentions an allocation callback but does not define which slot:

- is published under the source name;
- is used by `StateWriteMap.outputSlot`;
- appears in `RawPlanBlock.outputs`;
- is inserted into `scratchSlotOf` or `resultSlotOf`;
- is inspected by later statements;
- is associated with the original source statement for diagnostics.

**Suggested improvement:** define a concrete helper result, such as:

```lean
structure CompiledLocalChain (Step : Type) where
  steps       : Array Step
  signatures  : Array TensorSignature
  valueSlot   : TensorSlot
  assignPlan  : AssignPlan
```

Its contract should state:

- identity: one slot, one assign step, `valueSlot` is the assign destination;
- non-identity: two slots, assign then nonlinearity, `valueSlot` is the nonlinearity destination;
- only `valueSlot` is published under the source name;
- write maps always consume `valueSlot`;
- internal slots are produced but never named or listed as block outputs;
- allocation and publication occur only after successful axis resolution;
- `assignPlan` remains associated with the original source statement for causality checking and
  error locators.

Without this contract, the implementation risks writing the preactivation rather than the nonlinear
result into persistent state.

### 4. `.freeNorm` requires changes throughout scan compilation, not just preflight

The draft identifies relaxing `checkScanLHSSlot`, but current code assumes `.free` exclusively at
several later points:

- base `outputUids`;
- step `outputUids`;
- base write-map construction;
- step state-write construction;
- scratch context-axis validation;
- "unreachable" branches in both write-map builders.

**Suggested improvement:** add a complete affected-site inventory to the design:

- `.freeNorm` contributes the same local UID and extent as `.free`;
- `.freeNorm` contributes the same identity placement row as `.free`;
- it differs only by marking the axiswise reduction position;
- context-axis-as-local-output checks must treat `.freeNorm` like `.free`;
- state geometry must accept `.freeNorm` in non-advancing dimensions;
- all "unreachable" comments and totality guards must be updated.

This is important enough to be an explicit invariant, not an implementation-plan discovery.

## Significant design weaknesses

### 5. The generic wiring-loop abstraction is not yet specified tightly enough

The draft describes a record containing `sourceSlots`, `destinationSlots`, and checker/runner
dispatch. A flat `sourceSlots` interface is insufficient for assignment errors.

The current outer checker deliberately does not use `PlanStep.sourceSlots` for assignments because
flattening loses the term and factor indices required by `invalidForwardRead`.

The generic loop must also preserve:

- exact validation order;
- exact error precedence;
- block context checks versus top-level empty-context checks;
- multi-destination atomicity for scans;
- block output range and uniqueness checks;
- assignment-specific term/factor locators.

**Suggested improvement:** parameterize over a richer callback such as:

```lean
checkSources :
  nodeIndex -> available -> node -> Except Error Unit
```

rather than merely exposing flat source slots. Destination bookkeeping can remain generic, while
each node family retains its source diagnostics.

Also split the proposed first task. Combining:

- new raw types;
- checked evidence types;
- checker refactoring;
- runner refactoring;
- regression baselining

is too large for the highest-risk task. Make behavior-preserving loop extraction its own reviewed
task or commit before changing the block node vocabulary.

### 6. The proposed `ScanCompileError.nonlin` wrapper is redundant or too weak

The draft proposes:

```lean
| nonlin (stmtName : String) (cause : NonlinCompileError)
```

But:

- `PlanCompileCause` already has a `.nonlin` arm;
- `liftNonlin` already turns `NonlinCompileError` into that arm;
- every `NonlinCompileError` constructor already carries the statement name.

Therefore this wrapper duplicates both the error layer and the statement locator.

If scan-specific context is genuinely required, the proposed payload is not sufficient: it does not
include scan name, base-versus-step, or statement index.

**Suggested improvement:** choose one of two coherent policies:

1. Reuse `PlanCompileCause.nonlin` for top-level and scan-local source nonlinearities.
2. If scan context matters, add a genuinely informative wrapper carrying:
   - scan name;
   - base/step discriminator;
   - source statement index;
   - existing `NonlinCompileError`.

Do not add a wrapper that only repeats `stmtName`.

The proposed `BlockError.nonlin nodeIndex cause` is more justified because it identifies a malformed
directly constructed block node.

### 7. The semantics of nonlinear state publication need to be normative

The draft says persistent state may directly be the result of a nonlinearity, but it does not fully
state the execution order.

The design should explicitly specify:

- contraction produces the preactivation slice;
- nonlinearity executes over that local slice;
- only the nonlinear result is committed through `StateWriteMap`;
- a nonlinear scratch name resolves to the post-nonlinearity slot;
- later recurrence statements reading a persistent state name still observe the immutable pre-step
  capture, not an earlier state result from the same block;
- base overlay applies the nonlinearity before writing the slice into history;
- axiswise reduction operates independently at each scan context coordinate.

These rules should be added as semantic laws. They are more important than the code-sharing
accounting.

### 8. `RawPlanBlock.assignments` should probably be renamed

Once its element type becomes `BlockStep`, this declaration is misleading:

```lean
assignments : Array BlockStep
```

The field will contain pointwise and axiswise operations that are specifically not assignments.

**Suggested improvement:** rename it to `steps`. There is no canonical wire format yet, so this is
the least expensive time to make the vocabulary accurate. If the field must remain for
compatibility, state that reason explicitly.

## Testing weaknesses

### 9. Six positive fixtures are not enough

The proposed six-fixture matrix is a good smoke test, but it does not cover the failure modes
introduced by the design.

Add at least the following.

#### Positional correctness

- axiswise state with an iteration slot before the marked local axis;
- iteration slots interleaved between multiple local axes;
- marked local axis first, middle, and last;
- multi-axis scan with non-trailing advancing dimensions.

These catch the `resolveNonlinAxis` bug.

#### Publication correctness

- nonlinear scratch consumed by a later scratch;
- nonlinear scratch consumed by a state result;
- direct nonlinear state consumed downstream outside the scan;
- coupled scan where one state is nonlinear and another remains linear;
- verification that the committed state is the nonlinear result, not the preactivation.

#### Base-block correctness

- nonlinear base state;
- multiple base writes to one state;
- point override plus free-face base write;
- verification that every `StateWriteMap.outputSlot` names the final nonlinear slot.

#### Negative source tests

- masked axiswise in base and step;
- missing reduction marker;
- multiple markers;
- marker on pointwise or identity;
- `.freeNorm` naming a context axis;
- malformed local axis position.

#### Direct block-checker tests

For hand-built `BlockStep`s:

- forward read;
- duplicate destination;
- input overwrite;
- slot out of range;
- source/destination shape mismatch;
- non-`f64` signature;
- axis position out of range;
- missing production;
- exact error constructor and node index.

#### Semantic differential tests

Compare:

- compiled checked plan;
- legacy scheduled evaluator;
- independent scan unrolling where supported.

Include a fixture whose result would differ if softmax were accidentally applied across history
rather than over each local slice.

### 10. "Byte-identical" needs a precise observable definition

The checked evidence types do not all derive equality, so "every fixture must come out
byte-identical" is not a directly actionable test criterion.

**Suggested improvement:** define preservation in terms of observable artifacts:

- raw plan exact equality;
- materialized bindings exact equality;
- warning list exact equality;
- exact error constructor and error priority;
- Dense output shapes and `Float.toBits` data;
- existing corpus counts unchanged.

For the wiring refactor, capture a pre-refactor mutation/error matrix so validation order cannot
silently change.

## Overclaims in the forward-compatibility section

### 11. Scatter is not necessarily a one-source-slot node

The draft says a future scatter node's wiring only needs "one source slot and one destination slot."
A scatter RHS may contain multiple terms and multiple tensor factors, so it can read many source
slots. `StateWriteMap` supplies only placement; it does not cover:

- RHS contraction;
- fill initialization;
- collision detection;
- overwrite/sum/max/min collision reduction.

The analogy is useful, but incomplete.

**Suggested improvement:** say that the shared graph loop helps any future node that exposes a
derived set of source and destination slots. Avoid claiming a particular scatter payload shape
before it is designed.

### 12. A compiled predicate IR would not automatically unblock both masks and Iverson factors

A shared UID-free Boolean expression representation could serve both features, but their integration
points differ:

- an axiswise mask is evaluated over output/reduction coordinates;
- an Iverson factor participates inside a term and can introduce contracted axes and multiplicity.

**Suggested improvement:** change "would also unblock" to "could provide a shared prerequisite for."
Each feature would still need separate lowering, checking, and worker integration.

## Recommended revision structure

Revise the design in this order:

1. **Pipeline boundary decision**
   - explain `splitNonlins`;
   - decide whether scan bodies remain unsplit.
2. **Normative semantics**
   - local-axis reduction;
   - preactivation to nonlinearity to publication/write;
   - immutable state capture behavior.
3. **Block IR**
   - `BlockStep`;
   - rename `assignments` to `steps`;
   - checked evidence and errors.
4. **Compilation algorithm**
   - retained-local-axis mapping;
   - chain helper result and slot contract;
   - base/state/scratch publication;
   - source-statement locator preservation.
5. **Checker/runner sharing**
   - exact generic callback boundaries;
   - validation-order preservation.
6. **Complete `.freeNorm` impact inventory**
7. **Positive, negative, structural, and differential test matrix**
8. **Forward compatibility**
   - soften the scatter and predicate claims.

The first two critical issues--pre-splitting and local axis-position remapping--should be resolved
before this becomes an implementation plan.

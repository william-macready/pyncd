# Tensor Logic: Boundary Policy Design Questions

## Introduction

A tensor has a finite, declared coordinate domain, but an index expression
can produce an integer tuple outside that domain. A stencil can ask for
$X[i-1]$ at $i=0$; a shifted contribution can target $Y[i+1]$ beyond its last
coordinate. **Boundary value policies specify how such accesses are
interpreted.** They are part of the mathematical contract of an access,
not an accidental consequence of a storage library's indexing rules.

This note uses a paired read/write policy. A read policy can reject the
access, return a fixed scalar, or remap the raw coordinate to a valid one.
A write policy can reject the access, drop the contribution, or remap its
destination. Examples include strict access, zero or constant extension,
clamping, periodic wrapping, and two reflection conventions. Valid
coordinates retain their ordinary meaning. Read and write rules need not
be identical: reading a virtual padding constant does not create a mutable
padding cell to which contributions can be written.

These choices affect more than edge values. Remapping can make several
distinct contributions target one coordinate, or make a recurrence depend
on a future coordinate. Dropping before body evaluation can avoid a
primitive-domain failure that evaluate-and-discard must still report.
Reading an outside zero and applying `exp` yields one; applying `log` to
that zero is undefined. A policy must therefore specify access resolution,
evaluation demands, and its interaction with dependencies, rather than
merely prescribe an integer-to-array-index conversion.

### Relationship to the core semantic specification

[Tensor Logic: Operational and Denotational Semantics](tensor_logic_semantics.md)
separates the equations a program defines from their execution and from a
compiled storage realization. It gives source statements **additive
contribution semantics**: each tagged statement/valuation occurrence
produces a contribution, and the final value of a defined coordinate is
the combination of all occurrences targeting it. It does not interpret
each statement as an immediate overwrite or a separate final-value equation.
Padding and out-of-range access are explicitly outside its current fragment;
this note develops a candidate extension, not a reinterpretation of rules
already adopted there.

Boundary formalization fits into that separation as follows:

- **Syntax, typing, and elaboration (Part II).** Add explicit policy
  configuration and boundary-aware accesses, preserving declared signatures,
  tensor roles, scoped indices, and guard-admitted domains. Check raw tuple
  rank, configuration validity, and resolved-coordinate validity. Decide
  which rejection obligations are structural and which are runtime checks;
  rejection must not silently become padding or dropping.
- **Denotational meaning (Part III).** Extend expression interpretation so
  reads select a resolved coordinate or a constant. Replace raw write fibers
  by resolved destination fibers, retaining the identity and multiplicity
  of every contributing occurrence. Extend admissible-environment conditions
  to match the selected drop timing. A model still assigns complete values
  to every declared tensor, agrees with all supplied inputs, and satisfies
  the collected equations for every defined coordinate. Empty fibers still
  give the additive identity, not the outside read constant.
- **Operational meaning (Part IV).** Compute read footprints from resolved
  addresses. An outside constant requires no source-coordinate publication,
  but a resolved in-bounds read must wait for its complete value. Accumulate
  each retained contribution exactly once and publish a coordinate only
  after its entire resolved fiber is complete. Drop-before-evaluation can
  remove body demands; evaluate-and-discard requires additional evaluation
  obligations for occurrences with no destination. Recheck dependency ranks
  after remapping rather than assuming an existing scan order is still valid.
- **Compilation and refinement (Part V).** Require gather/scatter kernels,
  batching, materialized padding, and buffer reuse to preserve the extended
  expression meaning, contribution fibers, demanded definedness, publication
  barriers, and logical versions. Matching a few numerical edge values is
  not enough to establish this correspondence.

The core denotation is a **model relation**, including for cyclic equations;
its functional interpretation applies on inputs with a unique complete
model. The direct executor's progress guarantees apply to the
coordinate-ranked fragment. Boundary remapping can change both the equations
and their dependency graph, so coordinate validity alone guarantees neither
model uniqueness nor a supported execution strategy.

The intended integration is conservative: boundary-aware accesses should
agree with ordinary accesses in bounds, without turning omitted inputs,
unpublished values, or undefined primitives into successful zeros. The
[Naperian construction in Section 8.4](#84-realizing-policies-with-naperian-tensor-definitions)
keeps tensors as total families over valid coordinates and places policy
resolution before lookup and contribution collection. The
[Lean implementation summary](#current-lean-implementation) records today's
executable baseline; the remaining sections separate proposed policy
definitions from the decisions and proof obligations still needed to extend
the formal specification.

## Purpose and status

This is a working design note for formalizing boundary policies and integrating
them into [Tensor Logic: Operational and Denotational Semantics](tensor_logic_semantics.md).
It collects candidate definitions, unresolved decisions, proof obligations,
and examples that distinguish competing interpretations.

It does not extend the semantics yet, select every policy convention, or
claim that a compiler implements these policies. Formulas labelled
**candidate** are proposals to examine, not adopted language rules.
The existing specification is authoritative where the two documents differ.
The [current Lean implementation summary](#current-lean-implementation)
below records the executable baseline, not an adoption of the candidate rules.

The main goal is to make boundary behavior explicit without weakening the
distinctions between contributions and equations, unavailable and zero values,
structural errors and undefined primitives, or logical and physical addresses.
A boundary policy should adjudicate **both reads and writes**. This note treats
it as a pair of access rules: a read selects a value or rejects the access,
while a write selects a contribution destination, drops the contribution, or
rejects the access. These rules belong to one policy contract but need not
have identical outcomes.

## Contents

- [Introduction](#introduction)
- [Current Lean implementation](#current-lean-implementation)
- [1. Existing commitments and notation](#1-existing-commitments-and-notation)
- [2. A candidate read/write resolution interface](#2-a-candidate-readwrite-resolution-interface)
  - [2.5 Required contract for an admitted profile](#25-required-contract-for-an-admitted-profile)
- [3. Policy meanings and one-dimensional edge cases](#3-policy-meanings-and-one-dimensional-edge-cases)
- [4. Shapes, configuration, and multidimensional composition](#4-shapes-configuration-and-multidimensional-composition)
- [5. Write resolution, occurrence domains, and equations](#5-write-resolution-occurrence-domains-and-equations)
  - [5.6 Candidate demanded-task contract](#56-candidate-demanded-task-contract)
- [6. Binding, guards, and strict expression interpretation](#6-binding-guards-and-strict-expression-interpretation)
- [7. Dependencies, scans, and logical versions](#7-dependencies-scans-and-logical-versions)
- [8. Compilation, transformations, and differentiation](#8-compilation-transformations-and-differentiation)
  - [8.4 Realizing policies with Naperian tensor definitions](#84-realizing-policies-with-naperian-tensor-definitions)
- [9. Integration map and proof obligations](#9-integration-map-and-proof-obligations)
- [10. Open decisions and discriminating examples](#10-open-decisions-and-discriminating-examples)

## Current Lean implementation

**Reviewed 2026-10-06, against repository revision `3bdd7f9`.** This section
describes the existing DSL reference evaluator and checked dense `EvalPlan`
backend. It is a source-and-test review, not a new correctness proof or a claim
that the additive semantics document has been implemented.

The short version is **implicit zero extension on reads, evaluate-and-discard
on out-of-range top-level scatter writes, and zero-initialized scan histories
with explicit base overlays**. These are separate implementation rules, not
one configurable read/write policy.

**The existing read/top-level-scatter access behavior is captured by the
candidate Zero/drop profile in Section 3.1, with evaluate-and-discard timing
from Section 5.2.** Selecting that profile would preserve these boundary
decisions; the implementation currently fixes them implicitly rather than
offering a configuration choice. For real sum-product and Boolean logic,
the numeric-zero pad is $0_K$. For tropical max/min, whose reduction
identities are $-\infty$/$+\infty$, the exact match is instead the
**Constant $c$/drop profile with $c=0$**, again with evaluate-and-discard.
This correspondence covers access resolution and drop timing, not scatter
collision handling, additive publication, or scan-history initialization.

| Surface | Implemented boundary behavior |
|---|---|
| Plain and unary tensor reads | Read the original coordinate if every component is in range; otherwise return scalar zero. |
| Ordinary assignment | Enumerate the finite output domain and compute every output cell; there is no out-of-range write to resolve. |
| Top-level affine scatter | Evaluate the RHS first; retain an in-range placement, silently skip an out-of-range placement. |
| Persistent scan state | Allocate a complete zero-filled history, overlay base slices, then write successor slices in the recurrence interior. |
| Checked scan writes | Require statically admitted, in-range placement geometry; invalid placement is rejected rather than delegated to a runtime drop policy. |

### Reads: a fixed zero-extension rule

The reference implementation is
[`gatherRead` and `gather`](../../leanncd/LeanNCD/Eval/Gather.lean).
Indices are evaluated as signed integers. For a correctly ranked read of a
present tensor, any component $z_d<0$ or $z_d\ge n_d$ makes the **whole scalar
read** return `0.0`; otherwise the original coordinate is read. Bounds are
tested before conversion to natural-number storage indices.
There is no clamping, wrapping, reflection, or shape-changing padding.

The checked IR makes this explicit:
[`OutOfBoundsPolicy`](../../leanncd/LeanNCD/Eval/Plan/Types.lean) has exactly
one constructor, `zeroPad`;
[`ReadPlan`](../../leanncd/LeanNCD/Eval/Plan/Kernel.lean) carries it;
[`residualizeAssignment`](../../leanncd/LeanNCD/Eval/Plan/Compile.lean) emits it;
and [`checkAssignCore`](../../leanncd/LeanNCD/Eval/Plan/Check.lean) admits it.
The shared binary64/binary32 worker,
[`gatherFactorWith`](../../leanncd/LeanNCD/Eval/Plan/Dense.lean), uses
[`inBoundsPerDim`](../../leanncd/LeanNCD/Eval/Plan/Coordinates.lean) before
flattening. A flat-offset-only test would incorrectly alias some invalid
multidimensional coordinates onto valid cells.

The pad is the carrier's exact zero, **not the selected reduction identity**.
Boolean reads therefore pad with false (`0`), but max/min reductions also read
an out-of-range factor as `0`, not as $-\infty$/$+\infty$. A padded zero can
consequently win a max reduction over negative values.

Unary read functions run **after** padding: an out-of-range `exp(X[...])`
evaluates to `exp(0) = 1`, while `log(X[...])` or `recip(X[...])` fails its
domain check at zero. All product factors are evaluated; an Iverson factor
whose value is zero does not short-circuit another factor's domain error.
This is not the guard-restricted occurrence domain proposed in Section 6.

Zero-sized source dimensions make every actual read out of range; a rank-zero
tensor instead has the one coordinate `[]`. Empty output/reduction domains
can avoid body evaluation entirely. Padding does **not** excuse a missing
source tensor: the reference assignment/scatter workers validate source names,
and the checked worker's `validateStore` rejects missing slots, wrong shapes,
and wrong storage lengths before gathering. These claims concern validated
programs/checked plans, not arbitrary malformed calls to low-level helpers.

### Writes: finite assignments and evaluate-and-discard scatters

[`evalAssignSeeded`](../../leanncd/LeanNCD/Eval/Contract.lean) and
[`denseValueAtWith`](../../leanncd/LeanNCD/Eval/Plan/Dense.lean) compute values
over a finite output domain, with term-local contraction. They do not enumerate
raw out-of-range destinations for ordinary assignments.

For top-level scatter,
[`evalScatter`](../../leanncd/LeanNCD/Eval/Scatter.lean) and
[`runDenseScatterWith`](../../leanncd/LeanNCD/Eval/Plan/Dense.lean) enumerate
source coordinates, evaluate the RHS, then compute and bounds-check the affine
destination. An invalid destination selects no write and produces no boundary
diagnostic. Crucially, RHS evaluation has already happened: a domain error
still fails the operation even when that source occurrence would be discarded.
In Section 5.2's terminology, this is **evaluate-and-discard**, not
drop-before-evaluation.

Unwritten cells retain the scatter fill. The low-level reference worker uses
[`ScatterOpts`](../../leanncd/LeanNCD/DSL/Ast.lean)' integer fill (default `0`)
and supports `rejectCollisions`, `overwrite`, `sum`, `max`, and `min`.
The checked scatter checker admits **only `rejectCollisions`** and requires
`fill == compute.algebra.reduceId`. Thus checked real/Boolean scatter holes
contain zero, while checked tropical max/min scatter holes contain
$-\infty$/$+\infty$. This differs from direct reference-worker calls with a
finite tropical fill; the reference source-facing
[`evalPlain`](../../leanncd/LeanNCD/Eval/Eval.lean) rejects an incompatible fill
rather than silently claiming parity.

Placement extents are also an implementation convention, not policy
resolution. [`LHSSlot.outExtent`](../../leanncd/LeanNCD/DSL/Ast.lean) is the shared
extent rule. For positive one-axis placement $c i+b$, with $b\ge0$ and source
extent $n>0$, it returns $cn+\lfloor b/c\rfloor c$. For example, stride-two
placement over three source cells has extent six, including an unwritten
trailing cell. Other affine forms use the legacy integer expression converted
with `Int.toNat`. Programmatic zero/negative-coefficient plans can consequently
have an empty destination and discard every evaluated source value; negative
LHS coefficients/biases are not expressible in the current surface grammar.

### Scans: initialized boundaries, not unavailable-value padding

The checked scan IR's
[`ScanBoundaryPolicy`](../../leanncd/LeanNCD/Eval/Plan/RawStep.lean) has exactly
one constructor, `zeroThenBaseOverlay`. Both
[`evalScan`](../../leanncd/LeanNCD/Eval/Scan.lean) and
[`runDenseScanWith`](../../leanncd/LeanNCD/Eval/Plan/Scan.lean) allocate complete
histories with carrier zero, then apply explicit base writes.
For advancing extents $L_a$, recurrence coordinates range over
$\prod_a[0,L_a-1)$ and successor writes advance every such coordinate by one.
Lower boundary faces (any advancing coordinate equal to zero) remain at their
initialized value unless a base write supplies them.

These are **in-bounds initialized zeros**, distinct from constants returned by
an out-of-bounds read. The following causality and snapshot guarantees belong
to the **checked backend**, not to both evaluators. Its scan checker requires
every advancing row of
a captured-state read to be `context[q] + b` with $b\le0$
(`causalAdvancingRow`); non-advancing dimensions retain ordinary zero-padded
read behavior. Base blocks cannot capture state. Checked recurrence blocks
observe an immutable pre-step snapshot and commit next-state slices together.

The legacy reference evaluator's `readsIterAhead` check rejects positive
`.shift` offsets but does not enforce that complete affine-row condition.
A subsequent review verified a three-cell history with base $S[0]=7$ and
step $S[l+1]=S[2l]$ for $l\in[2]$: the reference returns $(7,7,0)$, reading
the last cell's initialized zero before computing it, while the checked
backend rejects the scaled state read. All accesses in this example are
in bounds. Its collected equations permit $(7,7,c)$ for arbitrary $c$;
the reference's procedural choice of zero is not a unique-model result.
Neither initialization nor boundary policy authorizes reading unpublished
in-bounds values as zero in the proposed additive reference machine.

Checked base writes must touch a lower boundary, be pairwise disjoint per
state, and have in-range pinned literals and consistent extents. Admitted
positive strided placement is confined to non-advancing dimensions. The
checked commit therefore needs no out-of-range drop rule. The reference
`writeScanStmtSlice` retains a defensive bounds-and-rank check that skips
invalid placements after computing the slice; this is not a configurable
scan boundary policy.

### Evidence and implications for the additive design

Existing fixtures pin negative-index padding in
[`GatherTest`](../../leanncd/test/Eval/GatherTest.lean); carrier-zero tropical
reads, pad-then-unary evaluation, and empty-source reads in
[`KernelDenseTest`](../../leanncd/test/Eval/Plan/KernelDenseTest.lean); native
binary32 pad-then-unary behavior in
[`KernelDense32Test`](../../leanncd/test/Eval/Plan/KernelDense32Test.lean);
out-of-range scatter drops, empty-destination degeneracies, collisions, and
tropical fills in
[`ScatterDenseTest`](../../leanncd/test/Eval/Plan/ScatterDenseTest.lean); and
deep-history look-back padding and extent-one/zero cases in
[`ScanTest`](../../leanncd/test/Eval/ScanTest.lean). These fixtures were inspected,
not rerun for this documentation-only review.

In the candidate resolver notation, an admitted read behaves like
`At(original coordinate)` or `Const(0)`, and top-level scatter placement like
`To(original coordinate)` or `Drop`, with evaluate-and-discard. That analogy
does **not** make the implementation an additive contribution collector:
ordinary assignments materialize results, scan writes replace designated
slices, and checked scatter collisions fail instead of combining occurrence
multiplicities by $\oplus$.

There is no paired access resolver, user-selectable strict/constant/remapping
policy, or coordinate-publication store in these evaluators. In particular,
the existing implicit zero reads differ from this note's conservative proposal
that ordinary accesses remain strict. Adopting that proposal, additive collision
collection, or drop-before-evaluation would be an intentional behavior change,
not merely a name for the current implementation. The current code is a
compatibility baseline for deciding those changes, not authority over the
new specification.

## 1. Existing commitments and notation

Boundary policies should preserve the following existing commitments:

- A tensor signature fixes each tensor's rank, ordered coordinate domains,
  and scalar carrier. A policy does not infer a missing shape.
- Inputs must be supplied, including empty inputs. Padding does not excuse
  an omitted input or an undeclared tensor.
- Contributions combine by the selected semiring operation $\oplus$.
  Remapped collisions do not become last-write-wins assignments.
- A write specifies a contribution to a declared defined tensor, not an
  immediate mutation. A policy cannot authorize writes to an input or an
  undeclared tensor.
- Guards restrict occurrence domains. Multiplication by zero does not
  short-circuit an undefined expression.
- A coordinate is readable only after publication. A policy cannot treat an
  unavailable in-bounds coordinate as zero.
- Complete program models include all defined tensors, not just outputs.
- Axis identities and ordered slots must be respected; labels or equal
  extents are not sufficient to identify axes.

Use the main document's notation:

- $\Sigma(T)$ is the signature of tensor $T$.
- $\operatorname{Coord}_{\Sigma}(T)$ is its finite coordinate domain.
- $K$ is the scalar carrier, with additive identity $0_K$.
- $\rho$ is a complete candidate environment; $\sigma$ is a partial store
  of published values.
- $\Gamma,\nu,D$ are an index context, valuation, and admissible valuation domain.
- $(s,\nu)$ is a tagged contribution occurrence, with body $E_s$.

For a rank-$k$ tensor, let $z\in\mathbb{Z}^k$ denote a **raw coordinate tuple**:
the result of evaluating well-scoped integer index expressions before
boundary resolution. Negative coordinates must remain negative at this stage.
For a vector, write its domain as $[n]$ and use a scalar integer $z$ as
shorthand for the one-component tuple $(z)$.

**Conservative-extension requirement:** explicit boundary-aware reads and
writes should agree with ordinary accesses at every valid coordinate.
For a write, agreement means retaining the occurrence and its original
destination, not replacing additive collection with mutation.
Ordinary accesses should retain their existing in-bounds requirement unless
a separate language decision deliberately changes it.

## 2. A candidate read/write resolution interface

### 2.1 One policy, two tagged outcomes

**Candidate:** a policy $b=(b^{\mathrm{read}},b^{\mathrm{write}})$ supplies two
resolvers using signature metadata and integer indices:

$$
\operatorname{resolve}^{\mathrm{read}}_b(T,z)
\in
\{\mathsf{At}(p)\mid p\in\operatorname{Coord}_{\Sigma}(T)\}
\sqcup
\{\mathsf{Const}(c)\mid c\in K\}
\sqcup
\{\mathsf{Reject}\}.
$$

$$
\operatorname{resolve}^{\mathrm{write}}_b(T,z)
\in
\{\mathsf{To}(p)\mid p\in\operatorname{Coord}_{\Sigma}(T)\}
\sqcup
\{\mathsf{Drop}\}
\sqcup
\{\mathsf{Reject}\}.
$$

These are tagged alternatives. A constant zero and coordinate $(0)$ must
not be confused simply because both contain the numeral zero.

- $\mathsf{At}(p)$ reads the existing valid coordinate $p$ of $T$.
- $\mathsf{Const}(c)$ supplies a specified scalar value without reading a
  coordinate of $T$.
- $\mathsf{Reject}$ indicates that this access cannot be resolved under
  the policy's contract.
- $\mathsf{To}(p)$ retains a write occurrence with destination $(T,p)$.
- $\mathsf{Drop}$ selects no tensor destination; its consequences for body
  evaluation must be specified, as discussed in Section 5.

A read's $\mathsf{Const}(c)$ is not a write destination. Fixed virtual padding
constants are not mutable cells. For example, a candidate zero-extension
policy can pair constant-zero reads with dropped writes; another explicit
pair can use the same read rule but reject out-of-bounds writes.
Neither write rule follows automatically from the read rule.

The signature is an implicit parameter. In this candidate profile, resolution
does not inspect tensor values or physical memory. This keeps dependency
analysis independent of input values.

For valid $p$, require
$\operatorname{resolve}^{\mathrm{read}}_b(T,p)=\mathsf{At}(p)$ and
$\operatorname{resolve}^{\mathrm{write}}_b(T,p)=\mathsf{To}(p)$.
Decide whether paired policies are attached to individual accesses, tensor
declarations, or ordered slots, and how explicit read or write overrides
compose with those defaults. Per-access policies would permit the same tensor
to be read strictly in one expression and with padding in another.

### 2.2 Read denotation and readiness

Write $\operatorname{read}_b(T,e_1,\ldots,e_k)$ as provisional notation,
not settled surface syntax. At valuation $\nu$, evaluate the indices to $z$.
For an admitted access, the candidate interpretation is

$$
\llbracket\operatorname{read}_b(T,e_1,\ldots,e_k)\rrbracket_{\rho,\nu}
=
\begin{cases}
\rho(T)[p],&\operatorname{resolve}^{\mathrm{read}}_b(T,z)=\mathsf{At}(p),\\
c,&\operatorname{resolve}^{\mathrm{read}}_b(T,z)=\mathsf{Const}(c).
\end{cases}
$$

The corresponding candidate read footprint is

$$
\operatorname{Read}(\operatorname{read}_b(T,e_1,\ldots,e_k),\nu)
=
\begin{cases}
\{(T,p)\},&\operatorname{resolve}^{\mathrm{read}}_b(T,z)=\mathsf{At}(p),\\
\varnothing,&\operatorname{resolve}^{\mathrm{read}}_b(T,z)=\mathsf{Const}(c).
\end{cases}
$$

Thus a padded constant is immediately available, but a remapped read waits
for its resolved coordinate to be published. No rule fills missing store
entries with zeros.

### 2.3 Rejection and resolution order

**Open decision:** for both access modes, classify $\mathsf{Reject}$ as a
structural access failure, a runtime boundary error, or both in different
checking profiles. It must not be treated as a constant read or a dropped write.
The conservative starting point is a structural obligation that rejection
never occurs at actual demanded accesses. Under drop-before-evaluation, these
include writes at guard-admitted raw valuations but exclude body reads of
dropped occurrences. Under evaluate-and-discard, those body reads remain
demanded. Section 5 makes this distinction precise.
This preserves the current separation between invalid access and primitive
undefinedness $\bot$.

### 2.4 Constant parameters

The formulas above assume a fixed typed constant $c\in K$.
Allowing a scalar expression or learnable tensor as the padding value would
require additional rules for its evaluation, definedness, and footprint.
In particular, decide whether that expression is evaluated at in-bounds
accesses where its value is unused. It must not become a hidden store read.

### 2.5 Required contract for an admitted profile

**Candidate admission contract:** a configurable profile is ready to use only
when it supplies the following data and satisfies the stated laws. This is
a checklist for complete profiles, not a choice of one global default.
The current construction concerns fixed typed constants and value-independent
geometry; expression-valued parameters require the separate extension in
Section 2.4.

| Component | Required contract |
| --- | --- |
| Configuration | Identify both access rules, typed parameters, ordered slots/axis identities, supported extents, and multidimensional resolution. |
| Successful resolution | Every `At`/`To` contains a valid coordinate; every `Const` belongs to the declared carrier. All in-bounds accesses agree with the original coordinate. |
| Rejection mode | Specify structural admission, runtime checking, or which obligations belong to each. Boundary rejection is distinct from dropping, primitive undefinedness, and unavailable values. |
| Dropped-body demands | Specify drop-before-evaluation or evaluate-and-discard; derive the demanded domain and pending tasks as in Section 5.6. |
| Error ordering | State any observable priority between configuration/access rejection, readiness, and primitive errors. Do not inherit it accidentally from a backend traversal. |
| Backend admission | Explicitly report unsupported profiles or geometries; a backend cannot substitute its own boundary rule. |

Two checking contracts can coexist:

- **Structurally admitted:** no write at a guard-admitted raw valuation
  resolves to `Reject`, and no body read on the selected demanded domain
  resolves to `Reject`. These are access-admission obligations, not proofs
  that value-dependent primitives are defined.
- **Runtime checked:** demanded accesses may resolve to `Reject`, which
  produces an explicit access-rejection outcome with the tensor, raw
  coordinate, access mode, and cause. A model requires every guard-admitted
  raw write to avoid rejection and every read of a demanded body to be
  admitted, as well as all demanded bodies to be defined; a rejected
  access is not a successful summand or a primitive result of $\bot$.
  The profile must define its rejection rule and ordering before use.
  The core machine's existing failure/progress results do not automatically
  cover this extra outcome.

Declaration, scope, tuple-rank, constant-type, and writable-role obligations
remain unconditional. They cannot be suppressed by guards or dropping.
Extent support must be classified explicitly: an unsupported extent can
invalidate the configuration, or an admitted configuration can reject actual
outside accesses. Those are different contracts. An absent body instance
causes no access resolution, but it does not waive an unconditional
configuration error.

Likewise, unavailability is an operational readiness condition for `At(p)`,
not an alternative resolver outcome for an in-bounds coordinate. Nothing
here turns a missing required input into a constant.

## 3. Policy meanings and one-dimensional edge cases

### 3.1 Candidate policy families

The table gives illustrative **paired profiles**, not compulsory pairings.
All agree with ordinary reads and contributions in bounds. Other combinations,
such as constant reads with strict writes, need equally explicit contracts.

| Paired profile | Out-of-bounds read | Out-of-bounds write | Decision or restriction |
| --- | --- | --- | --- |
| Strict | $\mathsf{Reject}$ | $\mathsf{Reject}$ | Matches ordinary access admission. |
| Zero/drop | $\mathsf{Const}(0_K)$ | $\mathsf{Drop}$ | Specify drop timing; never use zero for an unpublished coordinate. |
| Constant $c$/drop | $\mathsf{Const}(c)$ | $\mathsf{Drop}$ | Validate $c$; writes do not modify it. |
| Clamp | $\mathsf{At}(\operatorname{clamp}_n(z))$ | $\mathsf{To}(\operatorname{clamp}_n(z))$ | Cannot remap into an empty domain. |
| Wrap | $\mathsf{At}(\operatorname{wrap}_n(z))$ | $\mathsf{To}(\operatorname{wrap}_n(z))$ | Specify integer modulo, especially for negative indices. |
| Reflect | $\mathsf{At}(\operatorname{reflect}_n(z))$ | $\mathsf{To}(\operatorname{reflect}_n(z))$ | Specify singleton behavior and permitted distances. |
| Symmetric | $\mathsf{At}(\operatorname{symm}_n(z))$ | $\mathsf{To}(\operatorname{symm}_n(z))$ | Names and restrictions must not be inferred from a backend. |

The last two names are descriptive conventions for this note. Compatibility
with a library requires comparing its definition, not matching a name.

The current Lean read/top-level-scatter boundary behavior instantiates
**Zero/drop with evaluate-and-discard** for real sum-product and Boolean
logic. Its tropical numeric-zero padding instantiates **Constant $c$/drop,
$c=0$, with evaluate-and-discard**, since numeric zero is not the tropical
additive identity. See the [implementation summary](#current-lean-implementation)
for the separate collision and scan-initialization rules.

### 3.2 Clamp and wrap candidates

For $n>0$:

$$
\operatorname{clamp}_n(z)=\min(\max(z,0),n-1),
\qquad
\operatorname{wrap}_n(z)=z\bmod n.
$$

Here $z\bmod n$ is the unique remainder in $[n]$, including for negative $z$.
Both results must be proved to lie in $[n]$.
The same normalization can select a read coordinate or a write destination;
repeated write destinations collect all retained contributions.
For $n=4$, wrapping $-1$ gives $3$, while clamping it gives $0$.

Python-style indexing from the end is not a synonym for periodic wrapping:
it does not generally admit arbitrarily distant negative or positive indices.

### 3.3 Two reflection candidates

For reflection without repeated endpoints, one candidate for $n\ge2$ uses
$h=2(n-1)$ and $t=z\bmod h$:

$$
\operatorname{reflect}_n(z)=
\begin{cases}
t,&t<n,\\
h-t,&t\ge n.
\end{cases}
$$

For symmetric reflection with repeated endpoints, a candidate for $n\ge1$
uses $t=z\bmod(2n)$:

$$
\operatorname{symm}_n(z)=
\begin{cases}
t,&t<n,\\
2n-1-t,&t\ge n.
\end{cases}
$$

For $T=(2,5,7,11)$, these disagree:

| Query | Reflect candidate | Symmetric candidate |
| --- | --- | --- |
| $T[-1]$ under the stated policy | $T[1]=5$ | $T[0]=2$ |
| $T[4]$ under the stated policy | $T[2]=7$ | $T[3]=11$ |

The table uses policy-annotated reads conceptually; ordinary strict `T[-1]`
remains invalid.
For the paired remapping profiles, writes at the same raw indices target
the displayed coordinates, without assigning the displayed read values.
For the first candidate, $n=1$ would give a zero period. Decide whether to
reject such demanded accesses or define an explicit singleton extension.
The symmetric candidate maps every integer to $0$ when $n=1$.

If a singleton configuration is admitted, conservative agreement still
requires read/write resolution at raw coordinate $0$ to be `At(0)`/`To(0)`.
Its outside queries may be rejected or remapped to zero according to the
declared convention. Rejecting the entire singleton configuration instead
is a configuration-admission decision; it must not be described as rejecting
a valid in-bounds access under an admitted profile.

Also distinguish an arbitrarily extended virtual read from a finite padding
operator whose backend permits only certain padding widths.

### 3.4 Empty domains and rank-zero tensors

If an axis has extent zero, the tensor's coordinate product is empty.
No remapping policy can return a valid $\mathsf{At}(p)$ or $\mathsf{To}(p)$
for an actual access.
A constant-extension candidate can instead return its constant at every
raw coordinate of the correct rank.
A paired drop rule can discard every raw write to an empty defined tensor;
a strict write rule rejects every such demanded write. Neither creates a
coordinate or changes the tensor's declared shape.

Do not implement empty wrapping as modulo zero, or invent coordinate zero
for empty clamping. Any constant fallback would need to be an explicit
policy decision, not a successful-looking repair.

A rank-zero tensor is different: its coordinate domain is $\{()\}$.
The only correctly ranked raw tuple is $()$, so ordinary scalar access is
valid and all conservative read/write policies should agree with it.

## 4. Shapes, configuration, and multidimensional composition

### 4.1 Virtual extension versus shape-changing padding

Boundary-aware reads and writes need not change $\Sigma(T)$.
Read resolution can describe a virtual extension on integer coordinates;
write resolution still selects only declared destinations or drops or rejects
the occurrence. Actual queries and raw write occurrences remain drawn from
finite binder domains. This does not require an infinite stored tensor.

Materialized padding is a different operation: it creates a new finite
tensor or array with a declared shape and an offset correspondence.
For example, an input of length $n$ can be copied into a fresh tensor of
length $n+2p$, with $p\in\mathbb{N}$, by writes at positions $i+p$; the uncovered coordinates can
receive the existing empty-sum zero.
This is related to the gather/scatter discussion in
[Integer constants and affine index arithmetic](../index_arithmetic.md#4-gather-and-scatter).
Its offset construction does not itself define arbitrary out-of-range reads
or writes, or make virtual padding constants writable.

Decide how explicit padding widths, cropping, output shapes, and axis
identities relate to the paired access interface. A padding constant alone
does not determine an output extent.

### 4.2 Per-axis composition and corners

For a uniform constant read rule, an obvious candidate is: return the constant
if any component is outside its slot domain, otherwise read the coordinate.
For a uniform drop write rule, drop if any component is outside, otherwise
retain the original destination. For uniform remapping rules on nonempty axes,
normalize each component for either access mode.

Mixed policies require a combination rule. For example, on shape $(2,3)$,
consider a query at $(-1,4)$ with constant extension on the first axis and
strict access on the second. One axis proposes a constant; the other rejects.
Decide whether rejection dominates, constant extension dominates, or this
configuration requires another explicit rule.

The write counterpart is a raw destination $(-1,4)$ with drop on the first
axis and rejection on the second. Decide whether rejection dominates dropping
or dropping suppresses the rejected component. Specify read and write
combination rules separately within the paired policy; constant precedence
does not automatically determine drop precedence.

Axis-processing order must not accidentally choose the answer.
The same issue appears with an empty axis and a remapping policy on another
axis. Separate configuration validity from demanded-access resolution.

An admitted mixed profile must supply a total, deterministic tuple-level
combination rule, including corners where several axes propose different
constants. Requiring a uniform constant, rejecting the configuration, or
declaring an explicit corner rule are distinct options; none follows from
Naperian product structure. Any logical priority must be part of the profile,
not the order in which an implementation happens to inspect axes. The
combination rule cannot produce a coordinate in an empty coordinate domain.

Policies must attach to resolved ordered slots or explicitly identified axes,
not to coincidentally equal names or extents.

## 5. Write resolution, occurrence domains, and equations

### 5.1 Adjudicate a contribution, not a mutation

The write resolver in Section 2 adjudicates the raw destination of each
tagged occurrence. A retained occurrence contributes its body value to a
resolved coordinate. It does not update a readable tensor immediately,
overwrite another contribution, or write to a virtual constant.
Rejection is an error, not an alternative spelling of dropping.

Keep read and write contracts explicit even when they share a normalization
helper. A mapped read selects one collected value; a mapped write adds one
contribution to a fiber. They are not automatically inverse operations.
Whether a pairing must satisfy an additional duality property is a separate
decision, particularly for differentiation (Section 8.3).

### 5.2 Dropping before or after evaluation

For ignore-write behavior, distinguish:

- **Drop before evaluating the body:** exclude the raw valuation from the
  actual occurrence domain, similarly to an index guard.
- **Evaluate and discard:** demand a defined body, then produce no tensor
  contribution.

These differ when the discarded body is undefined.
For a length-one output, a raw write at $-1$ with body $\log(-1)$ is harmless
under the first interpretation and fails under the second.

Before-body dropping could elaborate a raw boundary statement into a core
statement with a restricted $D_s$ and a valid write map.
Evaluate-and-discard would need machinery for demanded occurrences with
no tensor destination; the current reference machine gives every occurrence
a destination. It is not just a storage optimization.

### 5.3 Candidate retained domains and collected equations

For the **drop-before-evaluation, structurally checked** profile, let
$D_s^{\mathrm{raw}}\subseteq\operatorname{Val}(\Gamma_s)$ contain the
guard-admitted raw valuations of statement $s$, and let
$z_s:D_s^{\mathrm{raw}}\to\mathbb{Z}^k$ give its raw write coordinates.
The destination tensor $T_s$ must already be a declared defined tensor.
Require that write resolution never returns $\mathsf{Reject}$ on this raw
domain; do not silently remove rejected valuations.

If statement $s$ uses paired policy $b_s$, define the retained domain by

$$
D_s^b=
\{\nu\in D_s^{\mathrm{raw}}\mid
  \operatorname{resolve}^{\mathrm{write}}_{b_s}(T_s,z_s(\nu))
  =\mathsf{To}(p)\text{ for some }p\}.
$$

For $\nu\in D_s^b$, define $\phi_s^b(\nu)=p$ using the unique resolved
destination, and set

$$
\operatorname{dst}_b(s,\nu)=(T_s,\phi_s^b(\nu)).
$$

Only these retained occurrences demand body interpretation, including all
boundary-aware reads in their actual reduction and tabulation instances.
Unconditional declaration, scope, and type checks still apply to the source.
The candidate collected equations are

$$
\rho(T)[p]=
\bigoplus_{s:\,T_s=T}
\ \bigoplus_{\substack{\nu\in D_s^b\\\phi_s^b(\nu)=p}}
\llbracket E_s\rrbracket_{\rho,\nu},
\qquad p\in\operatorname{Coord}_{\Sigma}(T),
$$

for every defined tensor $T$, together with the existing input agreement and
definedness requirements. Expression interpretation here includes the read
rules of Section 2. Empty resolved fibers still give $0_K$, not a padding
constant. Thus a constant-read/drop-write policy does not initialize unwritten
coordinates to its read constant.

These formulas specify semantic domains and maps, not an assertion that every
non-affine resolver already elaborates into the current affine surface syntax.
Evaluate-and-discard would additionally demand the bodies of dropped raw
occurrences without including their values in these sums. Its model
admissibility and operational tasks need explicit definitions before adoption.

### 5.4 Remapping preserves occurrence multiplicity

Suppose three tagged occurrences have raw destinations $-1,0,1$ and values
$2,3,5$. Clamping their destinations into $[2]$ gives collected values

$$
Y[0]=2+3=5,\qquad Y[1]=5.
$$

All three occurrences remain distinct. Normalization must not merge their
identities, simplify away contribution binders, or replace accumulation
with overwrite. Fibers must be computed from the resolved write map.

### 5.5 Dropped writes and unwritten coordinates

For a length-two defined tensor $Y$, suppose raw destinations $-1,0,2$
carry values $2,3,5$. Under drop-before-evaluation outside $[2]$, only the
middle occurrence survives:

$$
Y[0]=3,\qquad Y[1]=0_K.
$$

If the same policy returns a read constant $c$ outside $[2]$, an out-of-bounds
read of $Y$ returns $c$; an in-bounds read of $Y[1]$ returns its collected zero
after publication. Neither dropped value is retained in a hidden padding cell.

### 5.6 Candidate demanded-task contract

**Candidate schema for admitted geometry:** assume all guard-admitted raw
writes resolve to `To` or `Drop`, and all reads of demanded bodies are
admitted. Structural profiles prove these obligations; runtime profiles
add their explicit rejection rules separately. The schema below specifies
demand and completion, not a proved extension of the core machine.

Let $\mathcal{O}^{\mathrm{raw}}$ be the finite tagged raw occurrence set.
Partition it into retained occurrences $\mathcal{R}$, whose writes resolve
to `To`, and dropped occurrences $\mathcal{D}$, whose writes resolve to
`Drop`. Each occurrence keeps its statement identity and valuation.
Let $\mathcal{D}_{\mathrm{eval}}\subseteq\mathcal{D}$ contain exactly those
dropped occurrences whose profile selects evaluate-and-discard. Define

$$
\mathcal{Q}=\mathcal{R}\cup\mathcal{D}_{\mathrm{eval}}.
$$

$\mathcal{Q}$ is the demanded-task set; the union is disjoint because
$\mathcal{R}$ and $\mathcal{D}$ partition the raw occurrences. Dropped occurrences using
drop-before-evaluation are absent from it. For $o\in\mathcal{R}$, let
$\operatorname{dst}_b(o)$ be its resolved address. There is deliberately no
tensor destination for $o\in\mathcal{D}_{\mathrm{eval}}$.

A candidate complete environment is admissible only when every body
demanded by $\mathcal{Q}$ has a successful interpretation. Collected
equations nevertheless use only retained occurrences:

$$
\rho(T)[p]=
\bigoplus_{\substack{o\in\mathcal{R}\\
  \operatorname{dst}_b(o)=(T,p)}}
\llbracket E_o\rrbracket_{\rho},
\qquad T\in\mathrm{Def}.
$$

Here $E_o$ includes its occurrence's valuation. Input agreement and all
defined tensors remain part of the model. The dropped evaluated values
do not become extra summands, fills, or writable virtual cells.

For operational realization, extend the pending set to $U\subseteq\mathcal{Q}$
and use the resolved read footprint of each demanded body:

| Task/rule | Premise | Effect |
| --- | --- | --- |
| Retained contribution | A pending retained task is ready and its body succeeds with $v$ | Add $v$ to its destination accumulator and remove that task from $U$. |
| Evaluate-only task | A pending task in $\mathcal{D}_{\mathrm{eval}}$ is ready and its body succeeds | Remove it from $U$ without changing any accumulator. |
| Undefined demanded body | Either kind of pending task is ready and its body yields $\bot$ | Explicit terminal primitive failure; do not consume it as zero. |
| Publication | A defined address is unpublished and no pending retained task targets it | Publish its complete accumulator value, including the empty-sum zero. |
| Successful completion | $U$ is empty and every address is published | Return the complete environment, then project designated outputs. |

Initialization still validates complete inputs and unconditional structural
requirements, publishes only input addresses, initializes defined
accumulators to $0_K$, and sets $U=\mathcal{Q}$.
An evaluate-only task need not delay a coordinate's publication, because
it contributes nothing to that fiber. It **must** delay successful program
completion: even after every coordinate is published, its body can still
fail. Publishing values is not permission to return a successful result early.

For example, a raw write to an empty defined tensor whose body is
$\log(0)$ creates no task under drop-before-evaluation, but creates an
evaluate-only task under evaluate-and-discard. The empty result's lack of
coordinates does not erase the latter failure.

The finite measure remains a candidate

$$
|U|+
|\operatorname{Addr}_{\mathrm{Def}}\setminus\operatorname{dom}(\sigma)|.
$$

Retained and evaluate-only successful tasks each decrease $|U|$ by one;
publication decreases the second term. Progress needs an extra case:
once every address is published, all remaining admitted evaluate-only
bodies are ready. Their evaluation can succeed or fail, but is not silently
skipped. Before that point, the coordinate-rank condition applies to the
resolved reads of retained destination fibers.
Conservation, model preservation, failure exclusion, and correspondence
must be proved for this extended task set; they are not obtained merely
by changing the core machine's occurrence-domain name. Runtime rejection
needs its additional failure rules and proof obligations as well.

## 6. Binding, guards, and strict expression interpretation

### 6.1 Actual domains matter

Structural obligations must account for $D_s$ and for lifted body domains
inside reductions and tabulations, not just inspect surface indices.
Guard-excluded valuations and empty binders have no body instances.
Write resolution applies only at guard-admitted raw valuations. Under
drop-before-evaluation, it further restricts the domains at which body reads
and primitive-definedness obligations are considered; evaluate-and-discard
does not remove those demands.

Decide which policy-configuration errors remain unconditional and which
resolution obligations quantify over actual instances. For example, an
ill-typed padding constant is a configuration error, while an empty
remapping domain need not be consulted inside a nonexistent body instance.
Avoid accidentally rejecting previously valid empty-domain programs.

Policy annotations must not introduce hidden index binders or change
term-local contraction. Resolved coordinates must not be used to infer
undeclared output domains or relax the standard full-axis einsum profile.

### 6.2 Padding is not a guard

Replacing a guard with a padded read does not itself remove occurrences.
For writes that are retained, or dropped only after evaluation, their entire
bodies must still be interpreted. Dropping a write before evaluation is a
different rule that can remove these demands.
A padded zero can become nonzero through another operation:

$$
f(\operatorname{read}_{\mathrm{zero}}(T,-1))=1
\quad\text{when }f(x)=x+1.
$$

Likewise, $\log(\operatorname{read}_{\mathrm{zero}}(T,-1))$ is undefined
over the reals. Zero padding fixes access definedness, not the logarithm's
domain or the definedness of other body operands.

Applying $f$ before extending a tensor and applying $f$ after extending
it are different constructions. Moving padding across an operator requires
a value-and-definedness argument, including its action on the padding constant.

### 6.3 Complete arrays and unused coordinates

Boundary-aware reads inside a tabulation resolve each actual body coordinate.
An enclosing primitive still receives a complete array on the tabulation's
declared domain. Selection cannot skip undefined nonselected entries.

Constant reads need no coordinate of $T$, but this does not authorize omitting
required inputs or actual statements defining other tensors. The whole-program
complete-model criterion remains in force.

## 7. Dependencies, scans, and logical versions

Read footprints must contain resolved coordinates, not raw coordinates.
Constants introduce no coordinate edge; several remapped queries can share
one availability requirement while still contributing their values separately.

Recompute dependencies after resolving reads and writes. In particular,
wrapping an input's spatial coordinates is different from wrapping the
time coordinate of a defined recurrence.
For a retained occurrence targeting $a=\operatorname{dst}_b(s,\nu)$, every
resolved body read $q$ contributes an edge $q\to a$. Under drop-before-evaluation,
dropped occurrences create neither a destination nor body-read edges.
Evaluate-and-discard instead retains body availability obligations even
though there is no destination to which the current dependency rule can
attach them.

For $N\ge1$, let $H$ be a defined tensor with time domain $[N+1]$.
Consider the candidate history statements

$$
H[t]\mathrel{+}=\operatorname{read}_{\mathrm{wrap}}(H,t-1),
\qquad t\in[N+1].
$$

The time-zero read resolves to $H[N]$, creating a dependency cycle through
the history. Existing forward-scan ranks no longer apply.
At $N=0$, the same construction has a self-dependency.
The equations can still have a model relation, but the direct executor
must not silently select a cyclic solution.

Write remapping alone can create the same cycle. With strict reads $H[t]$
and raw writes at $t+1$, wrapping the writes gives resolved contributions

$$
H[\operatorname{wrap}_{N+1}(t+1)]\mathrel{+}=H[t],
\qquad t\in[N+1].
$$

The final occurrence targets $H[0]$ and reads $H[N]$.
Publication must therefore wait for all occurrences in each **resolved**
destination fiber, not merely those whose raw coordinates match it.
Neither remapping nor source order authorizes adding to an already published
coordinate. Extra contributions remapped into a scan's base region combine
additively with its initialization rather than overwrite it.

Boundary policies also do not justify enlarging a scan's recurrence domain
into its base region: extra occurrences can change initialization or invoke
a primitive at an invalid padded value.

Resolved accesses determine storage liveness. A boundary remapping can keep
an earlier slice live beyond the point where a two-buffer plan would normally
retire it. Logical version identity and full-history output retention remain
unchanged.

## 8. Compilation, transformations, and differentiation

### 8.1 Backend and layout obligations

A kernel must implement the selected mathematical policy rather than inherit
its indexing library's defaults. Relevant issues include:

- Negative indexing and the sign convention for integer remainder.
- Empty dimensions and backend restrictions on reflection or padding widths.
- Preserving signed raw coordinates before normalization.
- Overflow in affine index arithmetic before modulo or clamping.
- Initializing materialized padding and protecting live values from aliasing.
- Gathering all required resolved inputs before conflicting writes.
- Preserving remapped scatter sums and completed-coordinate barriers.
- Resolving write rejection and dropping at the selected semantic stage,
  rather than evaluating every body and masking stores afterward.
- Reporting structural, policy, and primitive-domain failures distinctly.

Resource exhaustion and hardware faults are separate implementation errors,
not evidence that the tensor equations lack a model.

Modulo, clamping, and reflection are not generally affine maps.
Decide whether compilation uses a policy resolver, partitions finite query
domains into guarded affine cases, or materializes an extended array.
None of these options should redefine the policy to match a convenient kernel.

### 8.2 Transformations need more than numerical spot checks

Materialization, fusion, reindexing, and common-expression sharing must
preserve values, domains, demanded definedness, and contribution multiplicity.
Auxiliary tensors must have explicit signatures and a correspondence to the
original program's models; temporary buffers need a representation proof.

An all-zero outside region does not license dropping a body containing an
undefined operator. Replacing a guarded computation by a padded one, or
vice versa, requires a proof of the whole expression's behavior.

### 8.3 Compatibility with differentiation

No differentiation semantics is adopted here, but boundary choices affect it.
Over exact reals with fixed geometry, an $\mathsf{At}(p)$ read selects a tensor
coordinate; a fixed $\mathsf{Const}(c)$ has zero derivative with respect to
the source tensor. Multiple queries resolving to the same coordinate require
reverse-mode contributions to accumulate there.

Resolved writes have the complementary multiplicity issue: if several body
values contribute to one coordinate, its cotangent is passed to each retained
contribution, not just one representative. Under drop-before-evaluation, a
dropped occurrence has no body computation to differentiate; representing
it as a computed body multiplied by zero can change definedness.

If read/write duality is desired, it needs an explicit obligation. Over the
reals with fixed geometry, the transpose of a mapped read's linear part
scatters additively to the same resolved coordinates. Fixed constant reads
have no source-tensor derivative and correspond to no source contribution.
Nonzero constant extension is affine rather than linear, and arbitrary
read/write pairings need not implement this transpose.

Learnable padding values would have their own derivatives and dependencies.
These observations concern tensor values, not derivatives of discrete
indices, extents, or policy choices.

### 8.4 Realizing policies with Naperian tensor definitions

**Candidate semantic construction, not a shipped implementation.** The
representability approach in [Naperian Typing](../NaperianTyping.md) can express
every policy family in Section 3. It does not select their conventions or
make them consequences of representability. Keep three layers separate:

1. A tensor is a total family over its **valid coordinate type**.
2. A configured boundary resolver converts raw integer tuples into tagged
   access outcomes.
3. Gather, contribution collection, and execution interpret those outcomes,
   preserving definedness, multiplicity, and publication requirements.

#### 8.4.1 Valid-coordinate families remain Naperian

For a concrete rank-$k$ shape $P=(n_1,\ldots,n_k)$, define

$$
I_P=\prod_{d=1}^{k}\operatorname{Fin}(n_d),
\qquad
\mathcal{N}_P(A)=(I_P\to A).
$$

Here each factor is an ordered axis slot with its resolved axis identity,
not merely an extent. A concrete representation is Naperian when it has
inverse operations

$$
\operatorname{lookup}:\mathcal{N}_P(A)\to I_P\to A,
\qquad
\operatorname{tabulate}:(I_P\to A)\to\mathcal{N}_P(A).
$$

For the function representation, these operations are direct evaluation and
construction. For dense storage, the lookup/tabulate equivalence needs a
representation proof, including storage length and coordinate ordering.
Total lookup accepts only $I_P$; it does not accept arbitrary integers and
then decide what to do with them.

Let $Z_P=\mathbb{Z}^k$ be the correctly ranked raw tuples and
$\iota_P:I_P\to Z_P$ the embedding that forgets bounds evidence. Boundary
policies live between $Z_P$ and $I_P$, not inside ordinary lookup.
Consequently, two accesses to the same tensor can use different policies
without changing its stored values or its Naperian laws.

If a dimension is empty, $I_P$ is empty and there is exactly one empty
family $I_P\to A$. No policy can fabricate an element of $I_P$.
For rank zero, $I_P$ is the singleton empty tuple, so the tensor is a scalar.
Symbolic shape/axis checks can precede size solving; concrete `Fin` types and
enumeration evidence require the resolved extents, following the symbolic
versus concrete split in [Naperian Typing, Section 5.3.1](../NaperianTyping.md#531-pass-ordering-symbolic-naperian-typing-vs-affine-size-inference).

#### 8.4.2 Typed resolvers package the configuration

For a scalar carrier $K$, use the tagged types

$$
\mathsf{ReadOutcome}_P(K)
=\mathsf{At}(I_P)\sqcup\mathsf{Const}(K)\sqcup\mathsf{Reject},
$$

$$
\mathsf{WriteOutcome}_P
=\mathsf{To}(I_P)\sqcup\mathsf{Drop}\sqcup\mathsf{Reject}.
$$

A valid policy configuration supplies functions

$$
r_b:Z_P\to\mathsf{ReadOutcome}_P(K),
\qquad
w_b:Z_P\to\mathsf{WriteOutcome}_P,
$$

and conservative-agreement laws

$$
r_b(\iota_P(i))=\mathsf{At}(i),
\qquad
w_b(\iota_P(i))=\mathsf{To}(i).
$$

Using $I_P$ in the constructors ensures that a successful remapping carries
valid-coordinate evidence. It does not prove that a resolver's implementation
matches its selected formula; that still requires a proof or a checked
construction. Invalid configuration and demanded-access rejection remain
distinct from primitive-domain failure.

The profile is additional metadata: chosen read/write rules, constant
parameters, reflection and singleton conventions, and drop timing. It can
be attached to accesses, tensors, or ordered slots once B01 is settled.
For per-slot configuration, a tuple-level resolver must implement B06's
explicit corner precedence. A product coordinate type does not decide
whether rejection dominates a constant read or a dropped write.

#### 8.4.3 Boundary-aware gather constructs another Naperian family

Let $J$ be a finite query domain and $a:J\to Z_P$ its raw index map.
For a complete tensor $T\in\mathcal{N}_P(K)$, define

$$
\operatorname{gather}_b(T,a)(j)=
\begin{cases}
T(i),&r_b(a(j))=\mathsf{At}(i),\\
c,&r_b(a(j))=\mathsf{Const}(c),\\
\mathsf{Reject},&r_b(a(j))=\mathsf{Reject}.
\end{cases}
$$

The rejection row denotes an access failure, not a member of $K$.
In the structural profile, require it to be absent on all demanded queries;
tabulation then constructs an element of $\mathcal{N}_J(K)=(J\to K)$.
A runtime-checking profile can first represent per-query outcomes as
$J\to\operatorname{Except}(\mathsf{AccessError},K)$ and traverse the finite
domain to obtain either an error or a complete $J$-family. Do not confuse
a family of fallible values with a successfully constructed tensor.
If diagnostic precedence is observable, traversal order must be specified.

| Read policy | Resolver and Naperian construction |
| --- | --- |
| Strict | Convert to $I_P$ only with bounds evidence; reject demanded invalid tuples. |
| Clamp, wrap, reflect, symmetric | Apply the chosen normalization with a proof that its result lies in $I_P$, then use `At` and lookup. |
| Zero/drop's read half | Use `At` in bounds and `Const` of the selected additive identity outside. |
| Constant/drop's read half | Use `At` in bounds and `Const(c)` outside, with $c\in K$. |

When every query resolves to `At`, the resolver gives a total map
$\eta:J\to I_P$ and gather is ordinary contravariant reindexing:

$$
\eta^*(T)=T\circ\eta.
$$

For constant extension, gather is a case split followed by lookup or a
constant, not merely precomposition with a map into $I_P$. One can factor
it through the coproduct $I_P\sqcup K$, extending the lookup function by
$c\mapsto c$. These extra points describe read outcomes; they are not
writable tensor coordinates.

For example, with shape $[3]$, $T=(2,5,7)$, and query tuples $(-1,0,3)$,
clamp gives $(2,2,7)$, wrap gives $(7,2,2)$, zero extension gives $(0,2,0)$,
and constant-nine extension gives $(9,2,9)$. Strict access rejects the
first and last queries. Each successful complete result is an ordinary
three-element Naperian family.

These constructions are compatible with Naperian tensors even for an empty
source: constant reads can still construct a nonempty query family, whereas
remapping to an empty $I_P$ is impossible. If $J$ itself is empty, there are
no demanded reads; unconditional configuration checks remain separate.
Virtual extension does not require storing an infinite integer-indexed
tensor. Only the actual finite query domain is tabulated.

#### 8.4.4 Additive writes are fiberwise pushforwards

Fix one defined destination tensor with coordinate type $I_P$.
Let $O$ be the finite **tagged occurrence domain**, including statement
identity and binder valuation, and let $a:O\to Z_P$ give raw destinations.
After resolving $w_b(a(o))$, reject any demanded `Reject` according to the
selected checking profile. On an admitted occurrence set, define

$$
R=\{o\in O\mid w_b(a(o))=\mathsf{To}(i)\text{ for some }i\},
\qquad
d:R\to I_P.
$$

For defined retained body values $v:R\to K$, additive collection is

$$
(d_!v)(i)=
\bigoplus_{\substack{o\in R\\d(o)=i}}v(o).
$$

This **pushforward** constructs the destination family
$d_!v\in\mathcal{N}_P(K)$. It requires finite enumeration and the chosen
additive aggregation, not just lookup/tabulate. It is a direct fiberwise
fold; no categorical Kan-extension machinery is required to define it.
Exact commutative-semiring semantics makes finite collection independent of
enumeration order. A floating-point refinement must separately specify its
fold order and numerical contract rather than infer associativity from
Naperian structure.

| Write policy | Retention and destination map |
| --- | --- |
| Strict | Retain original in-bounds destinations; reject demanded invalid ones. |
| Zero/drop or constant/drop | Retain original in-bounds destinations; exclude `Drop` occurrences from $R$. The read constant does not become a write fill. |
| Clamp, wrap, reflect, symmetric | Retain every admitted occurrence and map it to the normalized coordinate. Sum all members of each resulting fiber. |

For instance, clamping raw writes $(-1,0,1)$ with contributions $(2,3,5)$
into shape $[2]$ constructs $(5,5)$, not $(3,5)$: the first two occurrences
remain distinct even though their destinations coincide.
Empty fibers give $0_K$; an empty destination has no coordinates to fill.
Naperian representation does not authorize overwrite or collision rejection
in place of this additive fold. Such behavior is a different write contract.

#### 8.4.5 Drop timing belongs to body evaluation

The retained set $R$ determines collection, but not all definedness demands.
Let $O$ already include only guard-admitted raw occurrences.
For drop-before-evaluation, bodies are demanded only on $R$.
For evaluate-and-discard, bodies are demanded on all of $O$, including
occurrences resolving to `Drop`; only values belonging to $R$ are collected.

Thus the two profiles can produce the same destination family when every
body is defined, yet disagree about whether the program is admissible.
A dropped raw write with body $\log(-1)$ distinguishes them.
Do not implement drop-before-evaluation by first tabulating every body value
and then multiplying dropped lanes by zero: strict tabulation has already
demanded those values. Resolve the retained domain first.
Conversely, evaluate-and-discard needs explicit destinationless evaluation
tasks or an equivalent demand rule, not simply a retained-domain fold.
Section 5.6 gives the candidate task/admissibility contract, including the
requirement that those tasks complete before reporting program success.

Naperian families describe complete values. They do not by themselves
encode evaluation order, errors, guards, or the occurrence demands of
Section 5. Those remain part of expression and machine semantics.

#### 8.4.6 Pointwise lifting and boundary rewrites

For a total scalar function $f:K\to L$ and a genuine coordinate map
$\eta:J\to I_P$, pointwise lifting commutes with reindexing:

$$
\operatorname{map}(f)(\eta^*T)=\eta^*(\operatorname{map}(f)(T)).
$$

For constant extension, the corresponding law changes the constant:

$$
\operatorname{map}(f)(G_c(T))=G_{f(c)}(\operatorname{map}(f)(T)).
$$

Here $G_c$ uses a fixed query geometry and constant $c$ at its outside
queries. Moving $f$ across padding while keeping the same constant requires
$f(c)=c$ when the carriers coincide. A fixed padding choice across carriers
is not automatically natural in arbitrary scalar functions.
For a partial primitive, the rewrite must additionally preserve demanded
definedness. Zero padding followed by `exp` yields one outside, whereas
applying `exp` first and then zero padding yields zero outside; zero padding
followed by `log` fails. Representability does not erase these differences.

#### 8.4.7 Publication and temporal access need additional evidence

A complete history can be represented as a Naperian family over
$\operatorname{Fin}(L+1)$, but that type permits lookup at **every** history
coordinate. It does not prove causality. In particular, the illustrative
`ScanState.history` type in
[Naperian Typing, Section 5.2](../NaperianTyping.md#52-mixin-specific-implementation-strategies-with-dependent-type-optimization)
does not on its own prevent future reads or enforce the recurrence equations.

During execution, expose only published coordinates, or require readiness
evidence for a resolved `At(i)`. Constant outcomes need no source-coordinate
readiness. A missing published value must never become a padding constant
merely because its coordinate is in bounds.
Prefix-indexed state access can enforce forward-scan availability; general
dependency evidence can handle more expressive admitted access patterns.

Resolve policies before validating those dependencies. A time-wrap read can
map a negative raw index to the final history cell, yielding a well-typed
coordinate but a dependency cycle. Write remapping also changes destination
fibers: publication must wait for every retained contribution in the resolved
fiber, including any remapped into the base region. Naperian typing establishes
coordinate validity, not acyclic execution or unique cyclic solutions.
The current zero-then-base-overlay initialization is a separate implemented
scan rule, not something forced by representability.

#### 8.4.8 Integration with the proposed Naperian layer

The construction can preserve the intended separation in
[Naperian Typing](../NaperianTyping.md):

- `NaperianAxis`/concrete point data identify ordered valid coordinate types;
  `NaperianFamily` supplies total lookup/tabulate.
- `ReindexAction` handles actual total coordinate maps. The existing
  affine `StMatP` vocabulary does not automatically contain clamp, modulo,
  or reflection; add a checked boundary resolver alongside it, or deliberately
  enrich the index category and prove its point action.
- Boundary gather combines typed resolution with lookup/constant/error
  handling. Configuration includes carrier-appropriate constants and
  explicit multidimensional precedence.
- Finite reduction machinery collects writes over resolved fibers, preserving
  occurrence identity and the selected algebra.
- Expression-definedness and temporal/publication evidence enforce demand
  and readiness separately from complete tensor representation.

In particular, the current Lean numeric-zero-read/drop-write behavior can be
realized by this gather and an evaluate-and-discard demand rule. Reproducing
its collision rejection would require that separate write contract;
realizing the proposed additive semantics instead requires the fiberwise
sum above. No Naperian law makes those contracts equivalent.

The useful proof targets are resolver validity and in-bounds agreement,
gather/lookup correspondence, fiberwise collection with multiplicity
preservation, exact drop-demand correspondence, and readiness-preserving
execution. Only after those are established should optimizations reuse the
reindexing and pointwise laws; constants, errors, and temporal dependencies
must remain visible in their hypotheses.

## 9. Integration map and proof obligations

The extension should be integrated across the existing semantic layers,
not appended only as a kernel convention:

| Existing layer | Required addition or check |
| --- | --- |
| Background notation, Sections 3-6 | Paired policies, raw coordinates, distinct read/write outcomes, and configuration requirements. |
| Core syntax and typing, Sections 13-14 | Explicit read and destination annotations, writable tensor roles, and structural admission rules, including lifted domains. |
| Elaboration, Sections 15-17 | Paired defaults and overrides, guarded raw domains, retained occurrences, and the distinction from ordinary full-axis einsum. |
| Expression interpretation, Section 18 | Resolved reads, constants, rejection classification, and strict primitive composition. |
| Collection and models, Sections 19-20 | Resolved write maps and fibers, empty-sum zeros, and the definedness demands of the selected drop timing. |
| Dependencies and execution, Sections 23-27 | Resolved sources and destinations, completed-fiber publication, rank checks, and any destinationless evaluation tasks. |
| Compilation and refinement, Sections 29-33 | Kernel correspondence, materialization, collision accounting, and revised liveness. |

Proof obligations include:

1. Determinism and type correctness of both resolvers: every $\mathsf{At}(p)$
   and $\mathsf{To}(p)$ is valid, and every $\mathsf{Const}(c)$ belongs to $K$.
2. Conservative agreement with existing in-bounds reads and contributions.
3. Well-defined negative-index normalization and the selected empty/singleton rules.
4. Read stability and ready evaluation for the extended expression constructor.
5. Explicit error classification without zero or NaN fallbacks, and without
   conflating rejected writes with dropped ones.
6. Occurrence and fiber preservation under remapping or a precise account
   of the chosen dropping semantics.
7. Dependency-rank progress only where the resolved graph supports it.
   Evaluate-only tasks and runtime access rejection require their additional
   progress/failure cases; coordinate publication alone is not global completion.
8. Primitive-definedness preservation, including complete-array interpretation.
9. Simulation, output decoding, and storage-reuse correctness for selected kernels.

**Candidate starting scope:** settle paired read/write policies together,
retaining strict ordinary accesses and literal padding constants. Include
strict rejection, constant-read/drop-write, and shared-normalization remapping
profiles, with explicit drop timing and multidimensional precedence.
Specify empty-domain and reflection conventions before admitting those cases.
Expression-valued parameters and evaluate-and-discard machinery can remain
separate extensions, but every admitted policy must specify both access modes.
This is a recommendation, not a completed policy selection or implementation plan.

## 10. Open decisions and discriminating examples

### 10.1 Decision register

| ID | Decision to settle | Why it matters |
| --- | --- | --- |
| B01 | Placement of paired policies and read/write overrides | Controls scope, defaults, and conservative elaboration. |
| B02 | Structural versus runtime rejection for both access modes | Determines typing and error semantics; rejection is not dropping. |
| B03 | Literal versus expression-valued padding constants | Changes demand, footprints, and differentiation. |
| B04 | Empty-domain and singleton conventions | Prevents fabricated coordinates and division by zero. |
| B05 | Reflection variant and distance restrictions | Distinguishes actual values and backend compatibility. |
| B06 | Per-axis composition: constant/reject, conflicting constants, and drop/reject precedence | Makes read and write corners independent of processing order. |
| B07 | Virtual extension versus finite padding operations | Separates query semantics from shape and storage changes. |
| B08 | Permitted read/write pairings, drop timing, and any duality requirement | Changes occurrence domains, definedness, and differentiation obligations. |
| B09 | Supported non-affine normalization in compilation | Determines proof and rejection obligations, not meaning. |
| B10 | Scan acceptance and retention after resolution | Detects cycles and additional live logical versions. |

### 10.2 Examples to retain as decisions are made

| Case | Distinction the example must expose |
| --- | --- |
| Length four, raw indices $-1$ and $5$ | The pair distinguishes zero, clamp, wrap, reflect, and symmetric reads. |
| Raw indices $-n-1$ and $2n+1$ | Periodic normalization differs from bounded negative-index conventions. |
| Extents $0$ and $1$ | Empty domains differ from scalar tensors; reflection conventions need explicit treatment. |
| Empty reduction or tabulation containing a remapped read | No nonexistent body instance should resolve a boundary access. |
| A constant extension combined with strict rejection at a multidimensional corner | Exposes policy-precedence choices. |
| Dropping combined with strict write rejection at a multidimensional corner | Exposes write precedence independently of read precedence. |
| An in-bounds source coordinate that is not published | Must wait rather than return the padding constant. |
| A declared empty input omitted from the environment | Must be rejected even if all demands would return constants. |
| An ignored write with an undefined body | Distinguishes drop-before-evaluation from evaluate-and-discard. |
| An evaluated dropped write still pending after every coordinate is published | Prevents reporting success before all demanded bodies are defined. |
| An empty destination with a dropped $\log(0)$ body | Distinguishes an empty successful tensor from failure of an evaluate-only task. |
| An admitted singleton reflection profile at raw coordinate zero | Must retain `At(0)`/`To(0)`, regardless of its convention for outside accesses. |
| Several outside axes with different constant parameters | Requires a declared tuple-level rule rather than accidental traversal priority. |
| A dropped write whose body contains a rejected read | Tests which read-access obligations survive dropping. |
| Raw writes to an empty defined tensor | Distinguishes dropping from rejection or invalid remapping without fabricating storage. |
| Constant reads paired with dropped writes and an unwritten valid coordinate | Distinguishes virtual constants from collected empty-sum zeros. |
| A write to an input or undeclared tensor with an otherwise dropping policy | Must fail the unconditional role or declaration check. |
| Several writes clamped or wrapped to one coordinate | Must preserve every retained tagged contribution. |
| Padding before versus after $f(x)=x+1$ or $\log(x)$ | Exposes value and domain changes through operator placement. |
| A nonselected undefined entry of a tabulated array | Prevents an unsafe lazy-selection interpretation. |
| Spatial wrapping of an input versus temporal wrapping of a recurrence | Separates valid boundary access from unsupported dependency cycles. |
| Strict history reads with the final write wrapped into the base coordinate | Exposes a cycle introduced by destination resolution alone. |
| A remapped contribution to a coordinate with other pending contributions | Publication must await the entire resolved fiber. |
| Two-buffer reuse with a remapped read of an old slice | Detects missing liveness or version-retention obligations. |

Each settled decision should add its precise definition, the nearest
contrasting interpretation, and the relevant proof obligations here.
Once a coherent profile is established, integrate its definitions into
the corresponding sections of the main specification rather than leaving
boundary behavior as an independent implicit convention.

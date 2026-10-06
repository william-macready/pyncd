# Tensor Logic: Boundary Policy Design Questions

## Purpose and status

This is a working design note for formalizing boundary policies and integrating
them into [Tensor Logic: Operational and Denotational Semantics](tensor_logic_semantics.md).
It collects candidate definitions, unresolved decisions, proof obligations,
and examples that distinguish competing interpretations.

It does not extend the semantics yet, select every policy convention, or
claim that a compiler implements these policies. Formulas labelled
**candidate** are proposals to examine, not adopted language rules.
The existing specification is authoritative where the two documents differ.

The main goal is to make boundary behavior explicit without weakening the
distinctions between contributions and equations, unavailable and zero values,
structural errors and undefined primitives, or logical and physical addresses.
A boundary policy should adjudicate **both reads and writes**. This note treats
it as a pair of access rules: a read selects a value or rejects the access,
while a write selects a contribution destination, drops the contribution, or
rejects the access. These rules belong to one policy contract but need not
have identical outcomes.

## Contents

- [1. Existing commitments and notation](#1-existing-commitments-and-notation)
- [2. A candidate read/write resolution interface](#2-a-candidate-readwrite-resolution-interface)
- [3. Policy meanings and one-dimensional edge cases](#3-policy-meanings-and-one-dimensional-edge-cases)
- [4. Shapes, configuration, and multidimensional composition](#4-shapes-configuration-and-multidimensional-composition)
- [5. Write resolution, occurrence domains, and equations](#5-write-resolution-occurrence-domains-and-equations)
- [6. Binding, guards, and strict expression interpretation](#6-binding-guards-and-strict-expression-interpretation)
- [7. Dependencies, scans, and logical versions](#7-dependencies-scans-and-logical-versions)
- [8. Compilation, transformations, and differentiation](#8-compilation-transformations-and-differentiation)
- [9. Integration map and proof obligations](#9-integration-map-and-proof-obligations)
- [10. Open decisions and discriminating examples](#10-open-decisions-and-discriminating-examples)

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
[Integer constants and affine index arithmetic](index_arithmetic.md#4-gather-and-scatter).
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
| B06 | Per-axis composition: constant/reject and drop/reject precedence | Makes read and write corners independent of processing order. |
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

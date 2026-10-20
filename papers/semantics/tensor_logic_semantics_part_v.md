# Tensor Logic semantics - Part V: Compilation and refinement

[Previous: Part IV: Operational semantics](tensor_logic_semantics_part_iv.md) | [Contents](README.md) | [Next: Notation reference and bibliography](tensor_logic_semantics_reference.md)

## In this part

- [Part V: Compilation and refinement](#part-v-compilation-and-refinement)
- [29. Execution plans and logical action contracts](#29-execution-plans-and-logical-action-contracts)
  - [29.1 Plans, commands, and annotations](#291-plans-commands-and-annotations)
  - [29.2 Accumulation and publication contracts](#292-accumulation-and-publication-contracts)
  - [29.3 Coverage and schedule certificates](#293-coverage-and-schedule-certificates)
- [30. Concrete states and logical representation](#30-concrete-states-and-logical-representation)
  - [30.1 Concrete command execution](#301-concrete-command-execution)
  - [30.2 Resource views and live representations](#302-resource-views-and-live-representations)
  - [30.3 Storage changes and retirement](#303-storage-changes-and-retirement)
  - [30.4 The refinement relation and output decoder](#304-the-refinement-relation-and-output-decoder)
- [31. Simulation and compiler correctness](#31-simulation-and-compiler-correctness)
  - [31.1 Acceptance and explicit rejection](#311-acceptance-and-explicit-rejection)
  - [31.2 Initial states and successful-step simulation](#312-initial-states-and-successful-step-simulation)
  - [31.3 Failure matching, progress, and finishing](#313-failure-matching-progress-and-finishing)
  - [31.4 The compiled-correctness theorem](#314-the-compiled-correctness-theorem)
- [32. Batched collection and array kernels](#32-batched-collection-and-array-kernels)
  - [32.1 Why exact batched accumulation refines individual steps](#321-why-exact-batched-accumulation-refines-individual-steps)
  - [32.2 Complete arrays, empty groups, and shared computations](#322-complete-arrays-empty-groups-and-shared-computations)
  - [32.3 Publication fusion and interference](#323-publication-fusion-and-interference)
- [33. Scan compilation and buffer reuse](#33-scan-compilation-and-buffer-reuse)
  - [33.1 A separate-buffer history plan](#331-a-separate-buffer-history-plan)
  - [33.2 Reusing two state buffers](#332-reusing-two-state-buffers)
  - [33.3 Full-history outputs change the retention obligation](#333-full-history-outputs-change-the-retention-obligation)
  - [33.4 Scan edge cases and snapshots](#334-scan-edge-cases-and-snapshots)
- [34. Refinement boundaries and formalization targets](#34-refinement-boundaries-and-formalization-targets)

## Part V: Compilation and refinement

The reference machine specifies which values may be computed and when
they become readable. A compiled plan adds a schedule, kernels, and a
storage discipline. Correct compilation must preserve the reference
meaning while allowing many reference steps to be performed by one
kernel and allowing dead physical storage to be reused.

The plan contracts define an exact-value, sequential execution profile.
"Sequential" refers to command boundaries: a kernel may internally batch
or parallelize independent work if its contract is proved.
No particular existing plan representation or compiler is assumed to
satisfy these contracts. Lowering $K$ to machine arithmetic is a separate
refinement problem.

## 29. Execution plans and logical action contracts

### 29.1 Plans, commands, and annotations

Fix a structurally well-formed program $\textcolor{#9D75C4}{P}$ in the coordinate-ranked fragment
(the rank certificate of [Section 23.4](tensor_logic_semantics_part_iv.md#234-coordinate-dependencies-and-the-ranked-fragment), which a schedule certificate already
implies; see the end of [Section 29.3](#293-coverage-and-schedule-certificates)).
An execution plan $\textcolor{#C16C86}{\Pi}$ records the source signature and tensor roles
$(\textcolor{#5688C7}{\mathrm{In}},\textcolor{#5688C7}{\mathrm{Def}},\textcolor{#5688C7}{\mathrm{Out}})$,
a finite buffer collection $\textcolor{#C16C86}{\mathcal{B}}$ with capacities, and a finite
command sequence

```math
(\textcolor{#C16C86}{\kappa}_0,\ldots,\textcolor{#C16C86}{\kappa}_{m-1}).
```

Each command has a kernel implementation and an annotation specifying
its logical action. The basic action contracts are:

- $\textcolor{#C16C86}{\mathsf{Accumulate}}(G)$, for a finite set
  $G\subseteq\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}$ of tagged contribution occurrences.
- $\textcolor{#C16C86}{\mathsf{Publish}}(B)$, for a finite block
  $B\subseteq\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}$ of coordinates.
- $\textcolor{#C16C86}{\mathsf{Storage}}(\textcolor{#C16C86}{\theta})$, for a declared storage operation $\textcolor{#C16C86}{\theta}$
  such as initialization, copying, relocation, or retirement, with no
  change to the reference configuration.

Here $B$ is a set of logical addresses, not the buffer collection
$\textcolor{#C16C86}{\mathcal{B}}$. A block may describe a tensor, a slice, or a smaller region.
The set $G$ contains occurrence identities, not distinct numerical values;
equal-valued contributions are not deduplicated.

A fused command may have a finite sequence of these annotations.
Its contract is their sequential composition, even if intermediate
states exist only in its proof. Bounded loops may describe commands and
occurrence groups compactly; their mathematical expansion must be finite.
The specification does not require a compiler to enumerate every occurrence.

### 29.2 Accumulation and publication contracts

For $\textcolor{#C16C86}{\mathsf{Accumulate}}(G)$ at $(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$, require

```math
G\subseteq \textcolor{#A87C28}{U},
\qquad
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})\subseteq\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})
\quad\text{for every }\textcolor{#9D75C4}{o}\in G.
```

If every body succeeds with value $v_{\textcolor{#9D75C4}{o}}$, the logical post-state is
$(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha}',\textcolor{#A87C28}{U}\setminus G)$, where

```math
\textcolor{#A87C28}{\alpha}'(a)
=\textcolor{#A87C28}{\alpha}(a)\oplus
 \bigoplus_{\textcolor{#9D75C4}{o}\in G\cap\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)}v_{\textcolor{#9D75C4}{o}}
\quad(a\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}).
```

The contract leaves $\textcolor{#A87C28}{\sigma}$ unchanged. If a body is undefined, the kernel
must explicitly fail in a way matching a reference execution ending in
$\textcolor{#A87C28}{\mathsf{Failed}}$, not produce a successful aggregate.
[Section 32](#32-batched-collection-and-array-kernels) specifies the correspondence for both cases.

For $\textcolor{#C16C86}{\mathsf{Publish}}(B)$, require

```math
B\cap\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})=\varnothing,
\qquad
\textcolor{#A87C28}{U}\cap\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)=\varnothing
\quad\text{for every }a\in B.
```

Its logical post-state extends $\textcolor{#A87C28}{\sigma}$ by $a\mapsto\textcolor{#A87C28}{\alpha}(a)$ for all
$a\in B$, leaving $\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U}$ unchanged.
Publishing a block does not replace completion of its constituent fibers.
An empty $G$ or $B$ has no logical effect; it does not evaluate nonexistent
bodies or supply missing shapes.

### 29.3 Coverage and schedule certificates

Expand fused annotations in their stated order. A plan's logical schedule
must satisfy:

1. Its accumulation groups are pairwise disjoint and their union is
   $\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}$.
2. Its publication blocks are pairwise disjoint and their union is
   $\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}$.
3. Every defined address in $\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})$ is published before
   the group containing $\textcolor{#9D75C4}{o}$. Input addresses are supplied initially.
4. Every occurrence in $\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)$ is in an accumulation group
   before the block publishing $a$.

"Before" in conditions 3 and 4 is the expanded order, including between annotations of one command:
a later annotation of a command may read an address published earlier in the same command, and an
annotation that reads or publishes too early inside a command violates the condition exactly as it would
across two commands. A command may be empty (a no-op that changes no state or set).

These conditions preserve all actual contributions and every declared
defined coordinate, including empty fibers. They also ensure the readiness
and completion premises of [Section 29.2](#292-accumulation-and-publication-contracts) at each successful prefix.
They do not establish body-definedness on every input.

**As formalized (slice-1 to slice-4 profile: fused commands by expansion, retirement and typed static same-sort buffer reuse).**
The conditions play different roles. Conditions 1 and 2 (covering) are *terminal*: only terminal
adequacy uses them. Condition 4 is a *safety* condition of each publication. Condition 3 is a
*progress* premise, not a simulation premise: readiness is enforced dynamically by the read view, so
an unready read makes a step report `stuck` rather than compute a wrong value, and condition 3 is what
rules that out (`step_not_stuck`). Publication also requires materialisation: every member of a
published block must have a slot, including addresses whose fiber is empty
([Section 31.1](#311-acceptance-and-explicit-rejection) gives the per-command form and the role of each
clause). Slice 2: a command is a finite, possibly empty, list of annotations executed in order;
the per-annotation conditions (3, 4 and the freshness/materialisation clauses; 1 and 2 are whole-plan) are
evaluated at expanded positions (`offset pc + j`) on the static sets $\mathrm{Pub}(n)$,
$\mathrm{Cons}(n)$, $\mathrm{Mat}(n)$, $\mathrm{Ret}(n)$ (condition 3 and the retire clause read
$\mathrm{Live}(n)=\mathrm{Pub}(n)\setminus\mathrm{Ret}(n)$), so "before" inside a command is the expanded order. The plan is valid when its
expansion is valid (`FValid`, `checkPlanF`).

Storage annotations have additional representation obligations in
[Section 30](#30-concrete-states-and-logical-representation). Schedule validity alone does not prove a correct kernel,
layout, or aliasing discipline.

A schedule satisfying conditions 1-4 itself yields a coordinate rank. Let
$r(a)=0$ for input addresses and, for defined $a$, let $r(a)$ be one plus the
position in the expanded annotation sequence of the block publishing $a$.
If $b\in\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)$ is defined, then $b\in\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})$ for some
$\textcolor{#9D75C4}{o}\in\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)$. So $b$ is published before the group containing
$\textcolor{#9D75C4}{o}$ (condition 3), and that group precedes the publication of $a$
(condition 4), giving $r(b)<r(a)$. If $b$ is an input,
$r(b)=0<r(a)$. The ranked-fragment hypothesis is therefore implied by a
valid schedule.

For example, grouping both copies of `T[i] = X[i]` into one kernel is
permitted, but the group still contains both occurrence identities.
Publishing `T` after only one group is not permitted if another group
still contributes to it.

## 30. Concrete states and logical representation

### 30.1 Concrete command execution

A running concrete state has the form

```math
\textcolor{#C16C86}{\mathsf{C}}=(\textcolor{#C16C86}{\mathsf{pc}},\textcolor{#C16C86}{M},\textcolor{#C16C86}{\chi}),
\qquad \textcolor{#C16C86}{\mathsf{pc}}\in[m+1],
```

where $\textcolor{#C16C86}{M}$ is the memory from [Section 5.3](tensor_logic_semantics_part_i.md#53-logical-addresses-physical-slots-and-proof-only-history) and $\textcolor{#C16C86}{\chi}$ is the plan's specified
control and layout metadata. It is not a second source-language environment.
Metadata may be determined statically by the command position rather than
stored as runtime fields.

For $\textcolor{#C16C86}{\mathsf{pc}}<m$, executing $\textcolor{#C16C86}{\kappa}_{\textcolor{#C16C86}{\mathsf{pc}}}$ defines a transition

```math
\textcolor{#C16C86}{\mathsf{C}}\textcolor{#C16C86}{\longrightarrow}_{\textcolor{#C16C86}{\Pi}}\textcolor{#C16C86}{\mathsf{C}}'.
```

A successful command advances $\textcolor{#C16C86}{\mathsf{pc}}$ by one.
An undefined source contribution produces a terminal
$\textcolor{#C16C86}{\mathsf{PlanFailed}}(\textcolor{#9D75C4}{o})$ with an identified source occurrence $\textcolor{#9D75C4}{o}$.
Command execution must be defined by the chosen kernels; the action
annotations specify obligations on that execution, not a substitute for
implementing the kernels.

Write $\textcolor{#C16C86}{\mathop{\mathrm{Start}}\nolimits}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#398B83}{\eta})$ for concrete initialization from
the same well-typed input environment as the reference machine.
It validates input identifiers and shapes and installs the required
input values and initial metadata. An omitted empty input is still an error.

### 30.2 Resource views and live representations

Distinguish two kinds of logical resource:

- $\textcolor{#A87C28}{\mathsf{pub}}(a)$, for $a\in\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$: the immutable
  published value $\textcolor{#A87C28}{\sigma}(a)$.
- $\textcolor{#A87C28}{\mathsf{acc}}(a)$, for
  $a\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}\setminus\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$:
  an unpublished accumulator value $\textcolor{#A87C28}{\alpha}(a)$.

For a related concrete and reference state, a layout view
$\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}$ partially maps these resources to
$\textcolor{#C16C86}{\mathop{\mathrm{Slot}}\nolimits}_{\textcolor{#C16C86}{\mathcal{B}}}$.
The layout is justified by plan metadata and proof annotations; it may
be known from the command position.
Whenever a resource is mapped:

```math
\textcolor{#C16C86}{M}[\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}(\textcolor{#A87C28}{\mathsf{pub}}(a))]=\textcolor{#A87C28}{\sigma}(a),
\qquad
\textcolor{#C16C86}{M}[\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}(\textcolor{#A87C28}{\mathsf{acc}}(a))]=\textcolor{#A87C28}{\alpha}(a),
```

with the respective side conditions
$a\in\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$ and
$a\notin\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$.
Every mapped slot is initialized. The simple profile here requires
$\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}$ to be injective on its domain: distinct simultaneously
represented resources occupy distinct slots.
More permissive aliasing needs a separate justification.

Define the output address set

```math
\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Out}}}
=\{(T,p)\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\mid T\in\textcolor{#5688C7}{\mathrm{Out}}\}.
```

At $(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$, every published address in

```math
\textcolor{#A87C28}{\mathop{\mathrm{Need}}\nolimits}_{\mathrm{pub}}(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{U})
=\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})\cap
 \left(
 \textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Out}}}
 \cup\bigcup_{\textcolor{#9D75C4}{o}\in \textcolor{#A87C28}{U}}\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})
 \right)
```

must have a mapped $\textcolor{#A87C28}{\mathsf{pub}}$ resource.
All outputs remain concretely represented once published, and every
remaining contribution's already-published sources remain represented.
A plan may retain extra resources for its own storage operations.
Any such operation's actual reads must also have valid representations.

For $a\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}$, an unpublished address
that has already received a contribution must
retain a mapped accumulator:

```math
a\notin\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma}),
\quad
\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)\setminus \textcolor{#A87C28}{U}\ne\varnothing
\quad\Longrightarrow\quad
\textcolor{#A87C28}{\mathsf{acc}}(a)\in\mathop{\mathrm{dom}}\nolimits(\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}).
```

An untouched accumulator has the known value $0_K$ by Lemma 26.1 and
need not yet occupy a slot. Before a kernel updates or reads its physical
accumulator, it must materialize that zero or prove an equivalent
initial-write operation. Uninitialized memory is never used as a zero.

**As formalized (slice-1 to slice-4 profile: fused commands by expansion, retirement and typed static same-sort buffer reuse).**
`Allocation` records independent finite buffer identities, sorts, capacities and
bounded sort-certified placement (`locate`). `Slot = InputSlot P ⊕ BufferSlot A`
keeps inputs separate from reusable defined storage. `SlotView` represents
published resources on `Live` and accumulators on `Mat` but not `Pub`;
`LayoutOK` requires injectivity on this domain, not on all addresses.
Canonical allocation retains globally injective placement: `layoutOK_of_canonical`
(`Plan.Memory`) proves layout safety at every boundary, and
`checkPlan_of_canonical` (`Plan.Validity`) discharges the layout checker clause
when the other checks pass. These compatibility bridges are library theorems,
not test-only helpers.
Materializing a zero does not by itself make the zero correct: an `initZero` of an accumulator that
already holds contributions would silently erase them. The slice-1 plan therefore also requires
*initZero freshness* (`InitOK`): each initialised address is still unpublished at that command, and no
occurrence consumed by an earlier command targets it, so its logical accumulator is still $0_K$
(`acc_zero_of_unconsumed`). Publication likewise requires *materialisation* (`PubOK`): every member of a
published block is materialised at that point, including addresses whose fiber is empty.

These requirements permit a compiled execution to forget dead published
values and completed accumulators physically. Their values remain in the
reference state as ghost history, not as available runtime storage. Slice 2: fusion adds no new storage
rule; a later annotation of a command reads the running memory through `readPub` at its expanded position,
and the published-only view is $\mathrm{Pub}(n)$. Slice 3: the readable view is
$\mathrm{Live}(n)=\mathrm{Pub}(n)\setminus\mathrm{Ret}(n)$; a retired address stays in $\mathrm{Pub}(n)$ and in
$\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$, only its slot is cleared (`readPub` and `SlotView .pub` range over `Live`).

### 30.3 Storage changes and retirement

A $\textcolor{#C16C86}{\mathsf{Storage}}(\textcolor{#C16C86}{\theta})$ command must preserve its related reference
configuration. Typical valid effects include:

- Initialize an untouched accumulator's physical slot to $0_K$.
- Copy or relocate a represented resource, updating its layout view while
  preserving its value.
- Retire a published resource that is not needed by any remaining
  contribution, output decoding, or remaining concrete storage operation.
- Reuse a retired slot for a different logical resource.

A live unpublished accumulator cannot be discarded before its coordinate
is published. At publication its slot may change role from
$\textcolor{#A87C28}{\mathsf{acc}}(a)$ to $\textcolor{#A87C28}{\mathsf{pub}}(a)$ without changing its contents.
The reference accumulator remains in the proof state.

Retirement removes a physical representation, not the address from
$\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$. Reuse does not identify the old and new logical
addresses. Buffer ownership and ordered coordinates must follow $\textcolor{#5688C7}{\Sigma}$;
matching printed axis names or equal extents is not a layout proof.

**As formalized (slice-3 to slice-4 profile: retirement and typed static same-sort buffer reuse).**
The annotation `retire B` retires published addresses of $B$ (defined addresses only; inputs are never retired,
`live_input`). `execRet` sets each member's slot to `none` and the reference state is unchanged, so a retired
address stays in $\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$ as ghost history. Its slot is immediately
cleared, then may represent another resource under boundary-local `LayoutOK`. The logical published set $\mathrm{Pub}$ is unchanged; the readable set is
$\mathrm{Live}=\mathrm{Pub}\setminus\mathrm{Ret}$ (`Live`, `Ret`, `retList`). "Not needed by any remaining
contribution" is enforced at the reader: a later `acc` whose footprint contains a retired address fails `ReadyOK`,
which ranges over $\mathrm{Live}$. "Not needed by output decoding" is the `RetOK` clause that no member is an
output (`live_output_of_valid`: every output is live at the end of a valid plan). "Remaining concrete storage
operation" is vacuous: copy and relocate are not formalized. Slice 4 permits
static same-sort reuse after retirement: `place` need not be globally injective.
`R.dead` requires emptiness only outside the current layout image, including
unused capacity; it does not require an old address's reused slot to stay empty.
A later read of the retired logical address still returns `none` even when its
former slot holds a new value; such a demanded read is a plan defect (rejected
by the checker, `stuck` at run time). Decoding a retired output yields `none`.
Re-retirement is also a safety violation under reuse: the second clear could
erase a new occupant. The fixture `reuse-retire-again-after-reuse` pins this
hazard, whereas its canonical-allocation twin has separate storage and finishes
despite static rejection. `storage-live-output-claim` pins the opposite retention
direction: a later internal tensor cannot claim a live output's slot. Its old
step checks pass, the layout check rejects it, and its canonical twin is valid.
Custom zero-capacity storage and both resource kinds are independently tested.

Liveness between commands is not sufficient for safety inside a kernel:
all required reads of old contents must occur before an overlapping write,
or an independent snapshot must preserve them. Temporary array storage
must also be initialized, typed, and protected from conflicting writes.

### 30.4 The refinement relation and output decoder

Write

```math
\textcolor{#C16C86}{\mathcal{R}}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#C16C86}{\mathsf{C}},\textcolor{#A87C28}{\mathsf{Conf}})
```

for the plan's representation relation. It includes:

1. The memory/layout equalities and live-resource requirements above.
2. Agreement between the command prefix and the reference bookkeeping:
   consumed occurrences, published coordinates, and remaining occurrences.
3. Correct types, capacities, coordinate layouts, and control metadata.

It relates memory to a reference configuration, not directly to an arbitrary
solution of the equations. Starting from the same input and simulating
steps will establish the related reference state's reachability.
Ghost information may witness this relation but may not supply kernel
reads or returned values.

At $\textcolor{#C16C86}{\mathsf{pc}}=m$, a successful output decoder
$\textcolor{#C16C86}{\mathop{\mathrm{Decode}}\nolimits}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#C16C86}{\mathsf{C}})$ must reconstruct the whole declared
output environment from concrete representations and signature metadata.
For every output coordinate:

```math
\textcolor{#C16C86}{\mathop{\mathrm{Decode}}\nolimits}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#C16C86}{\mathsf{C}})(T)[p]
=\textcolor{#C16C86}{M}[\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}(\textcolor{#A87C28}{\mathsf{pub}}((T,p)))].
```

An output with empty coordinate domain is reconstructed as its unique
empty function with the declared signature; it requires no slots.
A scalar output requires its one rank-zero coordinate.
The decoder cannot recover overwritten output entries from ghost history
or silently supply zeros at missing nonempty output coordinates.

**As formalized (slice-1 to slice-4 profile: fused commands by expansion, retirement and typed static same-sort buffer reuse).**
The general relation above stays the contract; the allocation-indexed instance is the structure `R` (`Plan.Memory`),
with the input $\eta$ explicit and the pc-local sets $\mathrm{Pub}(\textcolor{#C16C86}{\mathsf{pc}})$, $\mathrm{Cons}(\textcolor{#C16C86}{\mathsf{pc}})$,
$\mathrm{Mat}(\textcolor{#C16C86}{\mathsf{pc}})$ computed from the first $\textcolor{#C16C86}{\mathsf{pc}}$ commands (`prefixAnn`). The layout view `SlotView` maps exactly the addresses of
$\mathrm{Live}(\textcolor{#C16C86}{\mathsf{pc}})$ (the published, not yet retired addresses) to their published slots,
and `Mat`-but-not-`Pub` accumulator resources to their accumulator slots;
$\mathrm{Pub}(\textcolor{#C16C86}{\mathsf{pc}})$ is the logical set.

- R1 (reach): $\textcolor{#A87C28}{\mathsf{Conf}}$ is reachable from the initial state on $\eta$. R1 is kept because R2-R4 do
  not pin untouched accumulators; only conservation from the initial state does
  (`acc_zero_of_unconsumed`).
- R2 (agreement, as equations): $o\in U(t)\iff(t,o)\notin\mathrm{Cons}(\textcolor{#C16C86}{\mathsf{pc}})$, and $\sigma(a)$ is
  defined $\iff a\in\mathrm{Pub}(\textcolor{#C16C86}{\mathsf{pc}})$.
- R3 (memory): for $a\in\mathrm{Live}(\textcolor{#C16C86}{\mathsf{pc}})$, $M[\mathrm{place}\ a]=\sigma(a)$; for
  $x\in\mathrm{Mat}(\textcolor{#C16C86}{\mathsf{pc}})\setminus\mathrm{Pub}(\textcolor{#C16C86}{\mathsf{pc}})$, $M[\mathrm{place}\ x]=\mathsf{acc}(x)$. The layout
  view `SlotView` depends on $\textcolor{#C16C86}{\mathsf{pc}}$ only, not on the memory.
- R4 (retention): if $x$ is unpublished and some consumed occurrence targets $x$, then
  $x\in\mathrm{Mat}(\textcolor{#C16C86}{\mathsf{pc}})$.
- R5 (dead): every physical slot outside the image of `SlotView pc` contains
  `none`, including unused capacity; `dead`. A retired address's former slot
  may hold a different mapped resource.
- R6 (Lean only): a retired address is published (`retPub`); it is needed because $R$ does not remember earlier
  steps' conditions.
- `Decode` at $\textcolor{#C16C86}{\mathsf{pc}}$ is partial. It succeeds iff every output coordinate is in $\mathrm{Live}(\textcolor{#C16C86}{\mathsf{pc}})$ with an
  initialised slot (`decode_of_R` under R), and it never fills a missing coordinate.
- Slice 3: `readPub_eq` is pointwise on $\mathrm{Live}$ (`readPub pc M a = c.published a` for live $a$). The
  function equality of slice 1 is false once a retired address keeps its ghost value.
- Inputs and outputs are disjoint: $\mathrm{Out}\subseteq\mathrm{Def}$ and $\mathrm{In}\cap\mathrm{Def}=\emptyset$ ([Section 13.6](tensor_logic_semantics_part_ii.md#136-core-programs); `Program.output_defined`). So an output coordinate is never an input slot, `Start` leaves every non-input slot uninitialised (`start_noninput`), and an output is decoded only after a `pub` command publishes it.

Slice 2: `R` and `refState` are indexed by command count and computed from the expanded annotations of the
first `pc` commands (`prefixAnn`); `R` is claimed at command boundaries
only (`step_R_command`), and the intermediate states of a fused command exist only inside the fold.
Slice 4: expansion preserves allocation; prefix transport (`R_transport`,
`execAnn_prefix`, `decode_prefix_congr`) requires allocation equality as well as
prefix equality and casts memory along that equality. Layout safety is required
at all expanded annotation boundaries, not only the outer command boundaries.

## 31. Simulation and compiler correctness

### 31.1 Acceptance and explicit rejection

**Definition 31.1 (valid plan).** Write
$\textcolor{#9D75C4}{P}\vdash\textcolor{#C16C86}{\Pi}\ \textcolor{#C16C86}{\mathsf{valid}}$ when the plan
satisfies all of the following.

1. **Schedule.** The coverage and order conditions 1-4 of [Section 29.3](#293-coverage-and-schedule-certificates).
2. **Initialization.** The initialization obligation of [Section 31.2](#312-initial-states-and-successful-step-simulation).
3. **Step simulation.** The successful-step simulation obligation of
   [Section 31.2](#312-initial-states-and-successful-step-simulation), including the representation requirements and the output
   decoder of Sections [30.2](#302-resource-views-and-live-representations)-[30.4](#304-the-refinement-relation-and-output-decoder).
4. **Failure matching.** Every $\textcolor{#C16C86}{\mathsf{PlanFailed}}(\textcolor{#9D75C4}{o})$ has a matching
   reference segment ([Section 31.3](#313-failure-matching-progress-and-finishing)).
5. **Progress.** The concrete progress and kernel-termination obligation of
   [Section 31.3](#313-failure-matching-progress-and-finishing).

Condition 1 is a static check on the plan. Conditions 2-5 quantify over all
well-typed inputs and reachable related states, and conditions 3-5 are
discharged kernel by kernel. Terminal adequacy is not a sixth condition; it
follows from the others (Lemma 31.2). The rank certificate of [Section 23.4](tensor_logic_semantics_part_iv.md#234-coordinate-dependencies-and-the-ranked-fragment),
assumed in [Section 29.1](#291-plans-commands-and-annotations), is implied by condition 1 (end of [Section 29.3](#293-coverage-and-schedule-certificates)).

A proposed compiler may return an accepted plan satisfying
Definition 31.1,
or explicitly reject an invalid source, unsupported dependency form,
unsupported primitive, or unjustified storage strategy.

Rejection does not assert that the program has no model.
Compiler completeness for every ranked program is not required by this
specification. Compiler **soundness** requires that every accepted plan
satisfy Definition 31.1 for all well-typed inputs, with semantic failures
handled as below.

**As formalized (slice-1 to slice-4 profile: fused commands by expansion, retirement and typed static same-sort buffer reuse).**
The five-condition definition above stays the general contract. Lean's `Valid` (`Plan.Validity`) is a
purely static condition, stated per command $\textcolor{#C16C86}{\mathsf{pc}}$ with `commands[pc] = [a]` against the prefix sets
$\mathrm{Pub}(\textcolor{#C16C86}{\mathsf{pc}})$, $\mathrm{Cons}(\textcolor{#C16C86}{\mathsf{pc}})$, $\mathrm{Mat}(\textcolor{#C16C86}{\mathsf{pc}})$, $\mathrm{Ret}(\textcolor{#C16C86}{\mathsf{pc}})$ (condition 3 and the retire clause read
$\mathrm{Live}(\textcolor{#C16C86}{\mathsf{pc}})=\mathrm{Pub}(\textcolor{#C16C86}{\mathsf{pc}})\setminus\mathrm{Ret}(\textcolor{#C16C86}{\mathsf{pc}})$; the rows below). Definition 31.1's semantic
conditions 2-5 are not fields of it: for the profile's singleton kernels they are theorems, `R_start` (2),
`step_R` (3, for the reference state `refState pc = some c`; see
[Section 31.2](#312-initial-states-and-successful-step-simulation)), `step_failed` (4) and
`step_not_stuck` (5). Each clause has a role: *safety* (needed for a correct
step), *progress* (needed so that a step is not stuck), *terminal* (needed only at $\textcolor{#C16C86}{\mathsf{pc}}=m$), or
*diagnostic* (checked but consumed by no theorem).

| clause | role | consumed by |
| --- | --- | --- |
| profile: every command is a singleton | progress | `step_not_stuck`, `run_R` |
| every boundary: `LayoutOK pc`, including pc = command count (`Valid.layout`) | safety | `step_init` (post), `step_acc`/`step_retire` (pre), `step_R`, run preservation |
| initZero $S$: each $x\notin\mathrm{Pub}(\textcolor{#C16C86}{\mathsf{pc}})$, and no occurrence in $\mathrm{Cons}(\textcolor{#C16C86}{\mathsf{pc}})$ targets $x$ (initZero freshness) | safety | `step_R` |
| acc $G$: $G$ duplicate-free, $G\cap\mathrm{Cons}(\textcolor{#C16C86}{\mathsf{pc}})=\varnothing$, every target $\in\mathrm{Mat}(\textcolor{#C16C86}{\mathsf{pc}})$ | safety + progress | `step_R`, `step_failed`, `step_not_stuck` |
| acc $G$: every footprint address $\in\mathrm{Live}(\textcolor{#C16C86}{\mathsf{pc}})$ (`ReadyOK`; [Section 29.3](#293-coverage-and-schedule-certificates) condition 3, and where [Section 30.3](#303-storage-changes-and-retirement)'s "no remaining reader" is enforced) | progress | `step_not_stuck` |
| pub $B$: $B$ duplicate-free, $B\cap\mathrm{Pub}(\textcolor{#C16C86}{\mathsf{pc}})=\varnothing$, $B\subseteq\mathrm{Mat}(\textcolor{#C16C86}{\mathsf{pc}})$, every occurrence targeting $B$ is in $\mathrm{Cons}(\textcolor{#C16C86}{\mathsf{pc}})$ (Section 29.3 condition 4) | safety + progress | `step_R`, `step_not_stuck` |
| retire $B$: every $x\in B$ is published at pc (the $\mathrm{Pub}$ half of $\mathrm{Live}$) | safety (a retire of an unpublished address would clear a live accumulator) | `step_retire` |
| retire $B$: no $x\in B$ is already retired (the $\neg\mathrm{Ret}$ half of $\mathrm{Live}$) | safety with reuse (a second retire could clear a new occupant); the canonical `retire-twice` fixture remains rejected | `step_retire` uses the retiring resource's pre-boundary `SlotView` |
| retire $B$: no $x\in B$ is an output (`RetOK`) | terminal | `live_output_of_valid`, `terminal_adequacy` |
| whole plan: groups duplicate-free (Section 29.3 condition 1, Nodup half) | diagnostic (derivable from the `acc` step conditions: `accFlat_nodup_of_accOK`) | none |
| whole plan: blocks duplicate-free (Section 29.3 condition 2, Nodup half, `checkCov2Nodup`) | diagnostic (derivable from the `pub` step conditions: `pubFlat_nodup_of_pubOK`) | none |
| whole plan: blocks cover $\mathrm{Addr}_{\mathrm{Def}}$ (Section 29.3 condition 2 covering) | terminal | `complete_of_refState` (Lemma 31.2) |
| whole plan: groups cover $\mathcal{O}_P$ (Section 29.3 condition 1 covering) | terminal (redundant: derivable from Section 29.3 condition 2 covering and condition 4) | `complete_of_refState` |

Section 29.3 condition 1 covering is redundant in the singleton profile: it follows from Section 29.3
condition 2 covering plus Section 29.3 condition 4 (`accFlat_complete`, packaged as
`cov1_of_cov2_pubOrder`). It is nevertheless kept in `Valid` and is not diagnostic:
`complete_of_refState` consumes it directly. That the Nodup halves of Section 29.3 conditions 1 and 2
follow from the per-step `AccOK` and `PubOK` conditions is proved on a singleton plan
(`accFlat_nodup_of_accOK`, `pubFlat_nodup_of_pubOK`, and for a `Valid` plan
`Valid.coverage_nodup_of_steps`; the checker-level form is `checkPlan_nodup_redundant`). Runtime execution (`runPlan`)
does not detect an invalid plan: soundness rests on the computable checker `checkPlan`, whose
acceptance implies `Valid` (`checkPlan_sound`) and every `Valid` plan is accepted (`checkPlan_complete`), so
`checkPlan` decides `Valid` exactly (`checkPlan_iff`).

Slice 4: `checkLayoutAt` enumerates pub/pub, pub/acc and acc/acc pairs using
`resourceList`; `checkLayouts` checks `range (commands.length + 1)`.
`checkLayouts_iff` is exactly the `Valid.layout` condition. Sort compatibility
and capacity bounds are enforced by allocation types, not runtime metadata
checks. An unchecked live alias can still finish `done` with corrupted values
(`reuseBad`); the checker is the safety gate, not the runner.

Slice 2: Definition 31.1 for a fused plan is Definition 31.1 of its expansion (`FValid`). The slice-1
`checkSteps` ignores a fused command, so the checker for fused plans is `checkPlanF` (sound and complete:
`checkPlanF_sound`, `checkPlanF_complete`). The empty command is accepted. Runtime execution still does not detect an invalid
fusion (`misfused-run-undetected`).

Slice 3: `Valid` gains the field `retOK` and `checkPlan` the clause `checkRet`; `checkPlan_iff` is unchanged in
statement. There is no duplicate check inside a retire block (clearing is idempotent). A retire inside a fused
command is covered by expansion (`FValid`); the fixtures `retire-fused-before-read` and `retire-fused-after-read`
pin the order. Runtime execution does not detect a retire of an output (the run ends `done` and `Decode` is
`none`, fixture `retire-output`): only the checker does.

### 31.2 Initial states and successful-step simulation

The initialization obligation is

```math
\textcolor{#C16C86}{\mathcal{R}}_{\textcolor{#C16C86}{\Pi}}(
 \textcolor{#C16C86}{\mathop{\mathrm{Start}}\nolimits}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#398B83}{\eta}),\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})).
```

For each successful concrete step, require

```math
\textcolor{#C16C86}{\mathcal{R}}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#C16C86}{\mathsf{C}},\textcolor{#A87C28}{\mathsf{Conf}})
\ \land\
\textcolor{#C16C86}{\mathsf{C}}\textcolor{#C16C86}{\longrightarrow}_{\textcolor{#C16C86}{\Pi}}\textcolor{#C16C86}{\mathsf{C}}'
\quad\Longrightarrow\quad
\exists\textcolor{#A87C28}{\mathsf{Conf}}'\;.\;
\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\longrightarrow}^{*}\textcolor{#A87C28}{\mathsf{Conf}}'
\ \land\
\textcolor{#C16C86}{\mathcal{R}}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#C16C86}{\mathsf{C}}',\textcolor{#A87C28}{\mathsf{Conf}}').
```

The matching reference segment must implement the command's declared
annotations. A batch may match many contribution steps; a block publication
may match many publication steps; a pure storage change matches zero steps.
$\mathcal{R}_{\Pi}$ is claimed only at command boundaries ([Section 30.4](#304-the-refinement-relation-and-output-decoder)).
The reference segment matched by a fused command is the concatenation of the segments of its annotations
in the expanded order of [Section 29.3](#293-coverage-and-schedule-certificates); the intermediate states
inside the command are not concrete states of $\Pi$ and carry no $\mathcal{R}_{\Pi}$ obligation.

This is a **forward simulation with stuttering**: a concrete step may
leave the reference state unchanged. It is not enough, by itself, to prove
concrete termination or prevent an incorrectly stuck compiled execution.

**As formalized (slice-1 to slice-4 profile: fused commands by expansion, retirement and typed static same-sort buffer reuse).**
The one-step theorem `step_R` assumes a singleton command `[a]` with `AnnOK pc a`,
pre/post `LayoutOK`, and, besides R, that
$\textcolor{#A87C28}{\mathsf{Conf}}$ is the deterministic logical post-state of the prefix, `refState pc`. So the simulation
invariant is $R\land\textcolor{#A87C28}{\mathsf{Conf}}=\mathtt{refState}\ \textcolor{#C16C86}{\mathsf{pc}}$, not R alone: R2-R4 do not pin untouched
accumulators, so R does not determine $\textcolor{#A87C28}{\mathsf{Conf}}$. Simulation is proved for that reference state
only, not for every R-related state. `R_start` is the initialization obligation, and `run_R` chains the
steps over the whole plan. Slice 2: simulation for a command is the fold of the per-annotation steps. From
$R\land\textcolor{#A87C28}{\mathsf{Conf}}=\mathtt{refState}\ \textcolor{#C16C86}{\mathsf{pc}}$ and `AnnOK` at each expanded position
`offset pc + j` of the command, `stepCommand = ok` gives `R` and the reference state at `pc + 1`
(`step_R_command`); progress holds under `FValid` (`stepCommand_not_stuck`). The concatenation requirement
above is `step_R_command`'s fold over the expanded order, and the per-position side conditions are `FValid`,
the validity of the expansion.
Slice 4: initialization uses successor-layout safety; accumulation and
retirement use current-layout safety; publication and failure add no layout
premise. `Valid.layout_boundary` supplies the pair for singleton steps, and
fused folds receive every expanded-boundary layout.

### 31.3 Failure matching, progress, and finishing

If a related concrete state steps to $\textcolor{#C16C86}{\mathsf{PlanFailed}}(\textcolor{#9D75C4}{o})$, require
a matching reference segment ending in

```math
\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\longrightarrow}^{*}
\textcolor{#A87C28}{\mathsf{Failed}}(\textcolor{#9D75C4}{o},\textcolor{#A87C28}{\sigma}',\textcolor{#A87C28}{\alpha}',\textcolor{#A87C28}{U}').
```

For a fused command that fails at its $j$-th annotation, the matching reference segment is the segment of
the $j-1$ preceding annotations of that command followed by the failing step. Whether the concrete memory
reported with $\mathsf{PlanFailed}(o)$ keeps the effects of those preceding annotations (partial commit) or
is the memory from before the command (rollback) is not constrained by the specification; a kernel
chooses, and must justify the reference snapshot it matches.

Thus the reported semantic failure is caused by an actual ready,
undefined source occurrence. A generic kernel exception is not automatically
such a proof. Resource exhaustion or hardware faults are separate explicit
**implementation errors**: a third terminal outcome, distinct from success and
from matched semantic failure, that does not establish absence of a model.
The **error-free profile** consists of the runs in which no implementation
error occurs. Concrete progress below, and the converse direction of
Theorem 31.3, are stated for that profile.

**As formalized (slice-1 to slice-4 profile: fused commands by expansion, retirement and typed static same-sort buffer reuse).**
Failure matching is proved with the same occurrence $o$ the plan reports. For one command,
`step_failed` gives, from any R-related $\textcolor{#A87C28}{\mathsf{Conf}}$, the single `undefined` event
$\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\longrightarrow}\textcolor{#A87C28}{\mathsf{Failed}}(o,\ldots)$, with no preceding contributions, so its
matched snapshot is that related $\textcolor{#A87C28}{\mathsf{Conf}}$. This holds because `runFrom` reports
the memory from before the failing command (`PlanFailed` carries it), so a partial commit is never
observed. For the whole run, `runPlan_R` gives only some reference execution from the initial state to
$\textcolor{#A87C28}{\mathsf{Failed}}(o,\ldots)$ on the same $o$; its snapshot is left existential. The snapshot may differ
from the state the reference executor `Executor.run` reaches under its own schedule (fixture
`failureAfter`: executor accumulator 2, plan 0). Theorem 31.3 (b) claims only that no model exists, so
this difference is harmless. Committing raw values versus view values, and transactional versus
sequential commit, are not told apart by any fixture on `checkPlan`-valid plans. This is an
observation, not a theorem: neither variant is defined in Lean, the
[mutation record](plan_layer_mutation_results.md) lists both as equivalent mutants, and the argument
that no run outcome distinguishes them (from `dest_not_pub` and `acc_slot_isSome`) is informal.
Slice 2: a failing annotation of a fused command rolls back the whole command, so `failed o pc M_pre`
carries the memory from before the command (the choice of rollback left open above). The reference runs the
earlier annotations of the command and then fails with the same occurrence $o$ (`step_failed_command` per
command, `runFrom_R_F` and `runPlan_R_F` for the run: each states that some reference run reaches `Failed` on
the same occurrence); unlike `step_failed`, the reference run needed is not the single `undefined`
event from the related state, because earlier annotations of the command have already executed.
Transactional versus sequential commit, which no slice-1 fixture told apart, is told apart by fused plans
(`fused-failure-after`, `fused-scalar-bad`).

Concrete progress requires that, in the error-free profile, every reachable
running state with $\textcolor{#C16C86}{\mathsf{pc}}<m$ can execute its next command successfully or report a
matched semantic failure. It cannot merely wait forever for an unmet
completion premise that the schedule certificate should have supplied.
Kernel and domain-test implementations must terminate on their stated
preconditions. Since every successful command advances the bounded program
counter, maximal plan runs are then finite, including storage-only steps.

**Lemma 31.2 (terminal adequacy).** Let
$\textcolor{#9D75C4}{P}\vdash\textcolor{#C16C86}{\Pi}\ \textcolor{#C16C86}{\mathsf{valid}}$, and let a concrete run from
$\textcolor{#C16C86}{\mathop{\mathrm{Start}}\nolimits}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#398B83}{\eta})$ reach
$\textcolor{#C16C86}{\mathsf{pc}}=m$ in $\textcolor{#C16C86}{\mathsf{C}}$. Then the related reference state
$\textcolor{#A87C28}{\mathsf{Conf}}=(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$ is complete and

```math
\textcolor{#C16C86}{\mathop{\mathrm{Decode}}\nolimits}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#C16C86}{\mathsf{C}})=\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}|_{\textcolor{#5688C7}{\mathrm{Out}}}.
```

*Argument.* The run executed every command. By the agreement clause of the
representation relation ([Section 30.4](#304-the-refinement-relation-and-output-decoder), item 2), $\textcolor{#A87C28}{\mathsf{Conf}}$ has consumed and
published exactly what the annotations of the whole command sequence account
for. By coverage conditions 1 and 2 of [Section 29.3](#293-coverage-and-schedule-certificates) these exhaust
$\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}$ and $\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}$. So $\textcolor{#A87C28}{U}=\varnothing$,
every defined address is published, and the input addresses were published
initially; hence $\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})=\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}$. Every output
address lies in $\textcolor{#A87C28}{\mathop{\mathrm{Need}}\nolimits}_{\mathrm{pub}}$ ([Section 30.2](#302-resource-views-and-live-representations)), so its $\textcolor{#A87C28}{\mathsf{pub}}$ resource
is mapped, and the decoder requirement of [Section 30.4](#304-the-refinement-relation-and-output-decoder) together with the memory
equation of [Section 30.2](#302-resource-views-and-live-representations) gives
$\textcolor{#C16C86}{\mathop{\mathrm{Decode}}\nolimits}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#C16C86}{\mathsf{C}})(T)[p]=\textcolor{#C16C86}{M}[\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}(\textcolor{#A87C28}{\mathsf{pub}}((T,p)))]=\textcolor{#A87C28}{\sigma}(T,p)$.

**As formalized (slice-1 to slice-4 profile: fused commands by expansion, retirement and typed static same-sort buffer reuse).**
`terminal_adequacy` is one theorem about the plan run from $\mathrm{Start}(\eta)$: for a valid plan, if
`runPlan` ends `done m M'`, then $m$ is the number of commands, the deterministic reference state $c$ at
$m$ (`refState m`) exists and is R-related to `M'`, $c$ is complete (`complete_of_refState`: $U=\varnothing$
by coverage of $\mathcal{O}_P$, and $\mathrm{dom}(\sigma)=\mathrm{Addr}_\Sigma$ by coverage of
$\mathrm{Addr}_{\mathrm{Def}}$ plus inputs), and $\mathrm{Decode}_m(M')=\rho_c|_{\mathrm{Out}}$, where
$\rho_c$ is the final store of $c$. The general argument above stays: its step through
$\mathrm{Need}_{\mathrm{pub}}$ is the one that matters once retirement
([Section 33](#33-scan-compilation-and-buffer-reuse)) separates "published" from "mapped". In slices 1-2
that step is trivial (nothing is retired). In slice 3 it is the theorem `live_output_of_valid`: at $\textcolor{#C16C86}{\mathsf{pc}}=m$
every output coordinate is in $\mathrm{Live}(m)$, because it is published and `RetOK` forbids retiring an output;
`decode_of_R` takes that as its hypothesis `outs`. Slice 2: `terminal_adequacy_F` is the same
statement for a fused plan under `FValid`; at `done m M'` the count $m$ is the number of commands (not of
expanded annotations), and the $\mathrm{Need}_{\mathrm{pub}}$ argument is the slice-1 argument on the expansion.
Slice 4: output slots follow the chosen physical allocation. A nonempty scalar
output can take a retired internal tensor's slot (`PlanReuseStorage.reuse`,
decoded value 2, matching canonical donors). Once represented, the output
cannot be retired or collide with another represented resource. Ghost history
cannot repair missing or overwritten output storage.

Write
$\textcolor{#C16C86}{\mathop{\mathrm{Start}}\nolimits}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#398B83}{\eta})\textcolor{#C16C86}{\Downarrow}_{\textcolor{#C16C86}{\Pi}}\textcolor{#398B83}{\zeta}$
for a finite concrete run ending at $\textcolor{#C16C86}{\mathsf{pc}}=m$ with
decoded output environment $\textcolor{#398B83}{\zeta}$.
No decoded success is permitted after a failed command.

### 31.4 The compiled-correctness theorem

**Theorem 31.3 (compiled correctness).** Let
$\textcolor{#9D75C4}{P}\vdash\textcolor{#C16C86}{\Pi}\ \textcolor{#C16C86}{\mathsf{valid}}$ and let $\textcolor{#398B83}{\eta}$ be
well-typed.

- (a) If a run reaches decoded success $\textcolor{#398B83}{\zeta}$, then
  $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ is a singleton $\{\textcolor{#398B83}{\rho}\}$
  and $\textcolor{#398B83}{\zeta}=\textcolor{#398B83}{\rho}|_{\textcolor{#5688C7}{\mathrm{Out}}}$.
- (b) If a run ends in $\textcolor{#C16C86}{\mathsf{PlanFailed}}(\textcolor{#9D75C4}{o})$, then
  $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\varnothing$.
- (c) In the error-free profile, an error-free maximal run exists, every
  such run ends in decoded success or $\textcolor{#C16C86}{\mathsf{PlanFailed}}$, and the converse
  of (a) holds:

```math
\textcolor{#C16C86}{\mathop{\mathrm{Start}}\nolimits}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#398B83}{\eta})\textcolor{#C16C86}{\Downarrow}_{\textcolor{#C16C86}{\Pi}}\textcolor{#398B83}{\zeta}
\quad\Longleftrightarrow\quad
\exists\textcolor{#398B83}{\rho}\;.\;
\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\{\textcolor{#398B83}{\rho}\}
\ \land\ \textcolor{#398B83}{\zeta}=\textcolor{#398B83}{\rho}|_{\textcolor{#5688C7}{\mathrm{Out}}}.
```

Equivalently, in the error-free profile, successful plan inputs are precisely
$\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P})$, and on that domain the decoded output equals
$\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\mathclose{]\!]}}(\textcolor{#398B83}{\eta})$. The model-set formulation avoids applying
the partial denotation outside its domain.

*Argument.* For (a), initialization and successful-step simulation
produce a reachable reference state; Lemma 31.2 makes it complete and
identifies the decoded output with $\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}|_{\textcolor{#5688C7}{\mathrm{Out}}}$.
Theorem 26.3 then gives the unique model and the stated decoded output.
For (b), a matched concrete failure gives a reference run ending in
$\textcolor{#A87C28}{\mathsf{Failed}}$, so $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\varnothing$ by
Theorem 26.3.

For (c), concrete progress, terminating kernels, and the finite command
counter give an error-free maximal run, and every error-free maximal run
ends in decoded success or matched failure. If a model exists, Lemma 26.2(c)
excludes matched failure, so the run ends in decoded success with output
$\textcolor{#398B83}{\rho}|_{\textcolor{#5688C7}{\mathrm{Out}}}$ by (a). If no model exists, success is
impossible by (a), so every error-free maximal run reports a matched semantic
failure.

Outside the error-free profile a valid plan can end in an implementation error
even when a model exists; (a) and (b) are unaffected.

**As formalized (implementation errors, D7; slice-1 to slice-4 `Valid` and fused `FValid` plans).** The third outcome is a wrapper, not a
new constructor of the Section 30.1 state: `FOutcome` is `run o` (an ordinary `PlanOutcome`) or `error e pc M`, with
`e : ImplErr` (`allocFail`, `kernelFault`; no information about models). A fault schedule `Faults : Nat → Option ImplErr`
is indexed by expanded annotation position and is consulted for a command's positions before the command runs
(`runFromE`), so a fault pre-empts a semantic failure at the same step and reports the memory from before the command.
`stuck` stays a plan defect, separate from `error`. Proved: with no faults `runPlanE` is `run (runPlan …)`
(`runPlanE_noFault`); a non-error outcome is the fault-free outcome (`runFromE_run`); an error at command `pc'` carries
exactly the fault-free memory there and a fault at one of that command's positions (`runFromE_error`); hence (a) and
(b) hold under every schedule (`done_correct_E`, `failed_correct_E`) and the run is never `stuck`
(`runPlanE_not_stuck`). The fused counterparts hold for `FValid` plans (`done_correct_FE`, `failed_correct_FE`,
`runPlanE_not_stuck_FE`); the wrapper runs fused commands unchanged, and a fault at any annotation of a fused command
reports the pre-command memory.

*Error-free profile.* The profile is the set of runs that end `run _` (`ErrorFreeRun`); a schedule with no fault at any
expanded position of the plan (`NoFaultsInPlan`, faults beyond the plan are never reached) gives such a run
(`errorFreeRun_of_noFaultsInPlan`). Under an error-free run, (c) holds for fused plans: the run ends `done` or `failed`
(`done_or_failed_FE`), a model forces `done` with the model's decoded output (`done_of_model_FE`), and `done` iff a
model exists (`done_iff_model_FE`). Outside the profile the converse fails, as the specification says: with a fault at
an executed position of the first command, the fault-free run is `done` while the faulty run is an `error` at pc 0
(`error_despite_model`). *`R` at the error state:* the memory an `error` reports is related by `R` to the reference
state at that command (`runFromE_error_R`, `runPlanE_error_R`), so it is a fault-free reachable state. Not modelled:
concrete error sources (allocation failure and kernel faults are abstract oracle outputs), and matching of an error to
a reference segment (an error establishes no absence of a model, so none is required).
Slice 4: `FOutcome` carries the plan's allocation-indexed memory. A fault after
the reused-slot write reports command pc 5, physical value 4 and error-state R
(`reuseFused_fault_after_write`, `reuseFused_error_R`), while the retired read
is `none` and the reference ghost is 0. No-fault parity remains
`runPlanE_noFault`; concrete error sources are still not modeled.

**As formalized (slice-1 to slice-4 profile: fused commands by expansion, retirement and typed static same-sort buffer reuse;
error-free).** For a `Valid` plan and a well-typed $\eta$, with the run `runPlan` from $\mathrm{Start}(\eta)$:

- (a) `done_correct`: if the run ends `done m M'`, then
  $\mathrm{Models}(P,\eta)=\{\rho_c\}$, $\mathrm{Decode}_m(M')=\rho_c|_{\mathrm{Out}}$, and that equals
  $\textcolor{#398B83}{\mathopen{[\![}} P\textcolor{#398B83}{\mathclose{]\!]}}(\eta)$.
- (b) `failed_correct`: if the run ends `failed o pc M'`, then $\mathrm{Models}(P,\eta)=\varnothing$, as
  stated above. Separately, failure matching holds with the same occurrence $o$
  ([Section 31.3](#313-failure-matching-progress-and-finishing)); `M'` is the memory before the failing
  command.
- (c) The run is never stuck (`runPlan_not_stuck`), so it ends `done` or `failed` (`done_or_failed`). If
  $\mathrm{Models}(P,\eta)$ is nonempty, the run is `done` with $\mathrm{Decode}=\rho|_{\mathrm{Out}}$
  (`done_of_model`). Hence the run is `done` iff a model exists (`done_iff_model`).

The theorem is conditional on Definition 31.1. Its hypotheses are exactly
those conditions; the generic steps (Lemma 31.2 above and, for batched
kernels, Lemma 32.1 in [Section 32.1](#321-why-exact-batched-accumulation-refines-individual-steps)) carry a mathematical argument in general, while conditions
3-5 remain an obligation on each kernel. For the slice-1 to slice-4 kernels (singleton/fused commands,
retirement and typed static same-sort reuse with boundary-local layout safety)
the generic steps and conditions 2-5 are kernel-checked in Lean (`R_start`,
`step_R` for the reference state `refState pc = some c`, `step_failed`, `step_not_stuck`,
`batch_execution`, `terminal_adequacy`); every other kernel
keeps the obligation. Beyond that profile it is a compiler proof specification with a mathematical
argument, not a claim that a particular compiler or kernel has already been
verified.

Slice 2: Theorem 31.3 holds for fused plans under `FValid` (`Plan.FusionCorrectness`): `done_correct_F`,
`failed_correct_F`, `done_or_failed_F`, `done_of_model_F`, `done_iff_model_F`, with `runPlan_not_stuck_F`.
Part (b) compares failure and absence of a model only; the failure memory is the memory before the failing
command.

## 32. Batched collection and array kernels

### 32.1 Why exact batched accumulation refines individual steps

**Lemma 32.1 (batched accumulation refines individual steps).**
For a ready group $G$ with all successful values $v_{\textcolor{#9D75C4}{o}}$, define

```math
\textcolor{#398B83}{\Delta}_G(a)=\bigoplus_{\textcolor{#9D75C4}{o}\in G\cap\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)}v_{\textcolor{#9D75C4}{o}}.
```

Enumerate $G$ in any order and apply $\textcolor{#A87C28}{\mathrm{CONTRIBUTE}}$ once per member.
Every member stays ready because these steps leave $\textcolor{#A87C28}{\sigma}$ unchanged.
The resulting accumulator is
$\textcolor{#A87C28}{\alpha}(a)\oplus\textcolor{#398B83}{\Delta}_G(a)$, and the remaining set is $\textcolor{#A87C28}{U}\setminus G$.
Finite associativity and commutativity justify the aggregate update.
This proves the logical success contract without requiring identical
physical reduction order.

A grouped scatter kernel must compute these complete fibers, including
colliding valuations. An overwrite kernel does not satisfy the contract
when a fiber contains multiple contributions.
Likewise, counting only distinct numerical body values is not a substitute
for retaining all occurrence identities.

If a member is undefined, $\textcolor{#398B83}{\Delta}_G$ is not defined by inserting zero or
NaN for it. A transactional kernel may report an undefined member before
committing any group contributions: the reference machine can choose that
member first. A kernel that commits a successful prefix before failing must
justify the corresponding reference prefix. In either case failure is
terminal and yields no successful output.

**As formalized (slice-1 to slice-4 profile: fused commands by expansion, retirement and typed static same-sort buffer reuse).**
`batch_execution` (`Plan.Batch`) proves the success half at the logical level, with premises: `G.Nodup`
(the list form of "$G$ is a set"), every member of $G$ is pending, every member is ready, and every
member evaluates successfully to $v_o$. The contribution events then form a reference execution
ending in the state `accumulateBatch c G v`, whose accumulator is $\alpha\oplus\Delta_G$
(`accumulateBatch_accumulators`), whose remaining set is $U\setminus G$ (`accumulateBatch_pending`),
and whose published store is unchanged (`accumulateBatch_published`); any enumeration order gives the
same state (`batch_execution_perm`). The failure paragraph is proved only for the transactional
singleton kernel (`step_failed`): the plan reports the first undefined member, matched by one
`undefined` event from the related reference state with no preceding contributions, because the
reported memory is the one from before the failing command; that snapshot may
differ from the reference executor's own schedule ([Section 31.3](#313-failure-matching-progress-and-finishing)).
A kernel that commits a successful prefix before failing is not formalized.
Slice 2: the lemma is unchanged. A fused command may contain `acc G` followed by `pub B` (the example of
[Section 32.3](#323-publication-fusion-and-interference)); the fused failure relation is
`step_failed_command` (`Plan.Fusion`), while the failure half of this lemma stays as proved (`step_failed`,
singleton).

### 32.2 Complete arrays, empty groups, and shared computations

An array kernel must implement [Section 18](tensor_logic_semantics_part_iii.md#18-expression-interpretation-and-definedness)'s interpretation, including
complete arguments, primitive domains, and complete-array selection.
In particular, computing only the selected coordinate of

```math
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[2]}(\log(X[j])),(0)
\right)
```

is not valid if the other tabulated coordinate has an invalid logarithm,
as in [Section 18.5](tensor_logic_semantics_part_iii.md#185-definedness-examples-and-transformation-limits).

For a whole-slice primitive, the logical footprint contains every required
input coordinate. Those published values must have concrete representations
when the kernel reads them. Sharing one evaluation of a deterministic
array primitive among several occurrence bodies is permitted if it preserves
their individual values and definedness and their contribution accounting.

An empty occurrence group evaluates no bodies. A compiler must not invoke
a partial primitive merely because the syntax contains it in a statement
whose occurrence domain is empty.
An actually demanded primitive on an empty array is different: its
$\textcolor{#398B83}{\mathcal{D}}_f$ condition still applies, as in [Section 25.3](tensor_logic_semantics_part_iv.md#253-surface-undefined-operations).

### 32.3 Publication fusion and interference

An accumulation-and-publication kernel may fuse
$\textcolor{#C16C86}{\mathsf{Accumulate}}(G)$ and $\textcolor{#C16C86}{\mathsf{Publish}}(B)$ only when publication's
premises hold after removing $G$ from $\textcolor{#A87C28}{U}$. It must not expose a partial
accumulator while another contribution to the same address remains: this is the
publication premise
$\textcolor{#A87C28}{U}\cap\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)=\varnothing$
for every $a\in B$ of [Section 29.2](#292-accumulation-and-publication-contracts), checked after removing $G$.

For `Pre[] = A[]; Pre[] = B[]; T[] = relu(Pre[])`, collecting the two
`Pre` occurrences, publishing `Pre`, and then evaluating ReLU can be fused
if those logical barriers are respected internally. Applying ReLU after
just the first contribution changes the program.

Concurrent updates within a kernel need an implementation argument that
they realize the exact aggregate without lost or duplicated contributions.
If a destination aliases a source location, the old source values must
be preserved until every required read finishes. Exact semiring
commutativity alone does not prove either property.

## 33. Scan compilation and buffer reuse

### 33.1 A separate-buffer history plan

Use the finite history of [Section 11.4](tensor_logic_semantics_part_i.md#114-a-finite-history-with-persistent-input) with total
$F:\mathbb{R}^{[d]}\to\mathbb{R}^{[d]}$.
For each $l\in[N+1]$, let
$B_l=\{(H,(i,l))\mid i\in[d]\}$.
Let $G_l^X$ be the persistent-input occurrences targeting $B_l$,
$G_0^Z$ the base occurrences, and $G_l^F$ for $1\le l\le N$ the
recurrence occurrences reading $H_{l-1}$ and targeting $B_l$.
These are subsets of the already defined $\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}$.

A simple plan uses a distinct state buffer $\textcolor{#C16C86}{\beta}_l$ of capacity $d$ for
each time slice, alongside the supplied-input storage:

1. Initialize the physical accumulators for $B_0$ to zero.
2. Accumulate $G_0^X\cup G_0^Z$ and publish $B_0$.
3. For each $l=1,\ldots,N$, initialize $B_l$'s physical accumulators,
   accumulate $G_l^X\cup G_l^F$, and publish $B_l$.

The union in each group is a disjoint union of occurrence subsets.
Each recurrence group reads a complete, earlier published slice.
The certificate $r(H,(i,l))=l+1$ from [Section 27.4](tensor_logic_semantics_part_iv.md#274-bounded-scans-and-complete-logical-slices) applies.
If an explicit `Last` output is included, finish by accumulating its reads
of $H_N$ and publishing `Last`.

Unlike the schedule in [Section 27.4](tensor_logic_semantics_part_iv.md#274-bounded-scans-and-complete-logical-slices), this plan consumes a slice's persistent
input only when constructing that slice. It still accounts for every
occurrence exactly once. It never adds $X$ twice merely because a previous
slice remains stored.

**As formalized (slice 5, full-history output).** `Plan.ScanHistory` certifies
this plan with $H$ as the sole output, over any additive commutative monoid and
any registered total unary same-sort array operator $F$. For arbitrary natural
$d,N$, it uses $N+1$ buffers of capacity $d$ and exactly $3(N+1)$ singleton
commands, including empty groups. The independent recurrence is connected to
the Program's collected equations and unique model. `plan_valid` and
`plan_checkPlan` establish schedule acceptance; `prefix_done_R` and
`history_retained_later` preserve each published slice's actual physical value
at every later command boundary. `scan_decode_history` completes for every
validated input and returns the full typed history, including successful empty
output decoding; `scan_denotation_history` identifies the independent output.
This is a constructed bounded scan certificate, not automatic source/scan recognition.

### 33.2 Reusing two state buffers

If $H$ is internal and the designated output is defined by

```math
\mathop{\mathrm{Last}}\nolimits[i]\textcolor{#9D75C4}{\mathrel{+}=}H[i,N],
\qquad i\in[d],
```

the plan can use two state buffers of capacity $d$:
one for the published current slice, the other for the next accumulator.
This counts state buffers only; supplied-input storage and any workspace
required by $F$ or its kernels are accounted for separately.

At each step, read the complete current slice, construct the next slice's
contributions in the other buffer, and publish the next slice.
After all recurrence occurrences reading the old slice have been consumed,
that slice has no remaining readers in this program.
It can be retired, and its buffer can be zero-initialized for a later
accumulator. Retirement occurs only after any other declared uses of that
slice have also finished.

The logical $\textcolor{#A87C28}{\sigma}$ still contains every earlier slice. Only its physical
representation is retired. Future untouched accumulators remain logical
zeros until materialized; this schedule does not pre-accumulate their
persistent-input contributions and then discard them.

For $d=1$, $N=2$, $X[0]=2$, $Z[0]=3$, and $F(h)[0]=2h[0]$, the storage
history can be:

| Completed action | State buffer $\textcolor{#C16C86}{\beta}_A$ | State buffer $\textcolor{#C16C86}{\beta}_B$ |
| --- | --- | --- |
| Construct and publish $H_0$ | $H_0=5$, live | Free |
| Construct and publish $H_1$ | Old $H_0$, now retireable | $H_1=12$, live |
| Retire $H_0$; construct and publish $H_2$ | $H_2=26$, live | Old $H_1$, now retireable |
| Retire $H_1$; construct and publish `Last` | $H_2$ can retire after the copy | $\mathop{\mathrm{Last}}\nolimits=26$, retained output |

Each construction zero-initializes its destination accumulator before
adding the prescribed contributions. Input storage is separate from the
two state buffers in this table.
The final free buffer can hold `Last` while its source slice remains
readable during copying.

Although the slot formerly holding $H_0=5$ later holds $H_2=26$, the proof
history still has distinct logical addresses with values $5$ and $26$.
No remaining kernel is permitted to read the overwritten $H_0$ slot as
though it still represented $H_0$.

**As formalized (slice-3 to slice-4 profile).** Retirement and static same-sort
reuse are formalized: `execRet` clears storage without changing the reference
history; subsequent `initZero` and accumulation may occupy that slot for a
different resource, under `LayoutOK`. `readPub` still excludes the retired
address even when its former slot has a new value (`reuseGood`).
The parked retirement/reuse component mutation-probe gaps are closed; this is
validation of the existing storage model, not a scan-liveness theorem or a
claim of independent whole-executor mutation coverage for every fixture.
This is not the Section 33.2 scan program or its liveness proof: that two-buffer
schedule, its values 5 and 26, full-history copy/relocation and in-place
snapshots remain unformalized.

### 33.3 Full-history outputs change the retention obligation

If instead $H\in\textcolor{#5688C7}{\mathrm{Out}}$, every published slice belongs to
$\textcolor{#A87C28}{\mathop{\mathrm{Need}}\nolimits}_{\mathrm{pub}}$. The two-buffer plan cannot simply
discard earlier slices and return only $H_N$.

It may still reuse working buffers if each completed slice is first copied
to retained output storage and its published layout view is relocated
there. The copy preserves the reference configuration; the working slot
becomes reusable while the output remains concretely represented.
Under this dense representation profile, retaining the full history uses
$d(N+1)$ scalar output slots, separate from any reusable working buffers.

Thus "two reusable state buffers" is not a claim that an entire requested
history can be returned using only $2d$ stored scalar values.
Output selection is a semantic contract, not an inference from the
compiler's preferred memory layout.

### 33.4 Scan edge cases and snapshots

For $N=0$, construct and publish only the base slice; the recurrence groups
are absent. A `Last` output reads that base slice.
For $d=0$, all slice and `Last` coordinate sets and contribution groups
are empty. Empty outputs keep their declared signatures but require no
slots, and no nonexistent recurrence body invokes $F$.

A partial $F$ uses the same schedule, but its demanded applications may
explicitly fail; totality was assumed above to guarantee success.
Reusing the current-slice buffer in place is not justified merely by a
time rank. A kernel must snapshot all required old values before overwriting
them or prove another read-before-write discipline for that particular $F$.
The two-buffer construction avoids that conflict between current-slice
reads and next-slice writes.

## 34. Refinement boundaries and formalization targets

Parts [III](tensor_logic_semantics_part_iii.md#part-iii-denotational-semantics)-[V](#part-v-compilation-and-refinement) separate three obligations:

1. **Meaning:** collected equations define models and functional denotation.
2. **Logical execution:** the reference machine collects occurrences and
   publishes completed coordinates.
3. **Compiled realization:** kernels, schedules, and storage represent and
   simulate that reference execution with explicit failure and progress.

This separation prevents a storage convention or an existing mutation
policy from silently defining the language.
Testing final outputs is useful evidence, but does not replace proofs of
occurrence coverage, barriers, domain behavior, and safe reuse.

The compilation-layer proof targets are:

- Typed plan annotations and sound validation of their coverage and order.
  *Proved for the slice-1 to slice-4 profile* (`Valid`, `checkPlan_sound`, `checkPlan_complete`, `checkLayouts_iff`; fused plans: `FValid`, `checkPlanF_sound`, `checkPlanF_complete`).
- Resource views, concrete states, and the representation relation,
  including empty shapes and untouched zero accumulators.
  *Proved for the slice-1 to slice-4 profile* (typed static allocation and boundary-local layout injectivity: `Allocation`, `SlotView`, `LayoutOK`, `R`, `R_start`, `step_retire`).
- Refinement lemmas for individual kernels, block publication, and storage
  operations; composite lemmas for fused commands.
  *Proved for the slice-1 to slice-4 profile's singleton kernels* (`step_R`, `step_failed`), for the retirement storage
  operation (slice 3: `step_retire`) and, for fused commands
  by expansion, the composite lemmas `step_R_command`, `step_failed_command`.
- Preservation of explicit undefinedness when batching or sharing expressions.
  *Batching proved for the transactional singleton accumulate kernel* (`batch_execution`,
  `step_failed`); sharing remains a target.
- Concrete progress and termination, not just forward simulation.
  *Proved for the slice-1 to slice-4 profile* (`step_not_stuck`, `runPlan_not_stuck`; fused plans:
  `stepCommand_not_stuck`, `runPlan_not_stuck_F`).
- Terminal decoding and the compiled-correctness theorem.
  *Proved for the slice-1 to slice-4 profile* (`terminal_adequacy`, `done_correct`, `failed_correct`,
  `done_iff_model`; fused plans: `terminal_adequacy_F`, `done_correct_F`, `failed_correct_F`, `done_iff_model_F`).
- Separate-buffer and two-buffer scan proofs, with full-history and
  terminal-only output contracts tested separately.
  *Separate-buffer full history proved in slice 5* (`plan_valid`,
  `history_retained_later`, `scan_decode_history`). Terminal-only two-buffer
  schedules and their last-reader condition remain unformalized.

**Full-history milestone completed:** the bounded separate-buffer plan of
[Section 33.1](#331-a-separate-buffer-history-plan) retains every published
slice as required by [Section 33.3](#333-full-history-outputs-change-the-retention-obligation).
Schedule validity, actual numerical preservation at all command boundaries and
complete typed decoding are proved, without retirement, reuse or copy/relocation.
Two-buffer terminal-only scans and reusable working buffers with retained-history
copy/relocation remain later targets with different output contracts.

Beyond the slice-1 to slice-4 profile (singleton/fused commands, retirement of
defined published addresses, typed static same-sort reuse with boundary-local layout safety)
and the slice-5 bounded full-history instance, these are
proposed contracts and proof targets, not kernel-checked results
or claims about current compiler acceptance. The slice-1 results fix one concrete plan representation
and kernel fragment (`LeanNCD.Semantics.Plan`); extending them requires
choosing further plan representations and kernel fragments and proving that
they satisfy the contracts, including additive contribution semantics.
Machine-number refinement, more permissive aliasing, asynchronous command
execution, and general cyclic solvers require their own explicit extensions.
Further buffer work includes copy/relocation for retained values, ownership-aware
input retirement, dynamic allocation, cross-sort reuse, and in-place
read-before-write or snapshot contracts. Concrete allocation/kernel error
sources and a refinement connection to the production `Eval/Plan` backend also
remain outside the proved profile; the existing fault wrapper is an abstract oracle.

---

[Previous: Part IV: Operational semantics](tensor_logic_semantics_part_iv.md) | [Contents](README.md) | [Next: Notation reference and bibliography](tensor_logic_semantics_reference.md)

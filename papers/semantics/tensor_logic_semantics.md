# Tensor Logic: Operational and Denotational Semantics

## Status and purpose

This specification defines tensor-logic syntax, denotational meaning,
reference execution, and compilation contracts. Its purpose is to provide
a coherent mathematical foundation for a Lean formalization and verified
implementation.

The intended language uses **additive contribution semantics**: separate source
statements can contribute to the same tensor coordinate. A source statement's
`=` is not, by itself, an assertion that the final tensor entry equals that
statement's contribution.

The specification separates three questions: what equations a program
defines, how those equations can be evaluated, and when a compiled execution
faithfully realizes that evaluation. A mutation order or storage convention
does not determine the source language's meaning.

### Roadmap and reading guide

The document has five parts, followed by a notation reference and bibliography:

| Part | Central question | Contents and result |
| --- | --- | --- |
| [I: Background notation](#part-i-background-notation), Sections [1](#1-numbers-finite-sets-and-functions)-[12](#12-notation-for-operational-and-proof-rules) | What mathematical objects and notation are used? | Finite domains, scalar algebras, tensor signatures, environments, stores, indices, operators, and contribution occurrences, illustrated by running examples. |
| [II: Core language and surface elaboration](#part-ii-core-language-and-surface-elaboration), Sections [13](#13-core-syntax-and-binding)-[17](#17-pure-einsum-semantics-and-transformation-foundations) | What does a well-formed statement say explicitly? | Scoped core syntax, structural checks, surface-to-core translation, and the canonical pure-einsum meaning and rewrite conditions. |
| [III: Denotational semantics](#part-iii-denotational-semantics), Sections [18](#18-expression-interpretation-and-definedness)-[22](#22-denotational-scope-and-execution-requirements) | What equations and values does a program define? | Strict expression interpretation, additive collection, complete program models, and a partial input-output function on inputs with a unique model. |
| [IV: Operational semantics](#part-iv-operational-semantics), Sections [23](#23-read-footprints-and-executable-dependencies)-[28](#28-reference-machine-boundaries-and-proof-targets) | How can the contributions be computed safely? | Read footprints, dependency ranks, accumulation and publication rules, explicit failures, and correspondence with unique models for the ranked fragment. |
| [V: Compilation and refinement](#part-v-compilation-and-refinement), Sections [29](#29-execution-plans-and-logical-action-contracts)-[34](#34-refinement-boundaries-and-formalization-targets) | When does a compiled plan implement that meaning? | Plan contracts, buffer representations, simulation and progress obligations, batching, scan-buffer reuse, and a conditional compiler-correctness theorem. |

Read Parts [I](#part-i-background-notation) and [II](#part-ii-core-language-and-surface-elaboration) before the formal semantics: they establish the notation
and binding conventions used throughout. [Part III](#part-iii-denotational-semantics) applies even to cyclic
equation systems; the progress guarantees in Parts [IV](#part-iv-operational-semantics) and [V](#part-v-compilation-and-refinement) concern the
coordinate-ranked fragment, not every structurally valid program.
The distinction between having a unique model and having a supported
execution strategy is therefore essential.

The boundary, colliding-write, activation, and finite-history examples are
revisited across the parts to connect notation, elaboration, equations,
execution, and storage. [Section 35](#35-compact-notation-reference) collects the notation; the references
identify the mathematical sources and related design documents.

For the implementation path, see
[From Tensor Logic semantics to a Lean executable reference](lean_executable_semantics_path.md).
It maps this document's notation and mathematical clauses to the landed Lean
definitions and proofs, explains their category-theoretic organization, and
separates the verified admitted exact-rational reference executor and the
bounded source-correspondence layer from the remaining general-source and
backend-refinement work.

### Semantics at a glance

The development rests on five ideas. [Part I](#part-i-background-notation) fixes the notation, and each
item names the section that makes it precise. The colors are explained in the
next subsection.

1. **Occurrences ([§9](#9-programs-and-contribution-occurrences), [§13](#13-core-syntax-and-binding)).** A statement $\textcolor{#9D75C4}{s}$ generates one
   occurrence $(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$ for each
   admissible valuation $\textcolor{#5688C7}{\nu}\in\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$.
   It is addressed to $\textcolor{#9D75C4}{\mathop{\mathrm{dst}}\nolimits}(\textcolor{#9D75C4}{o})=(T_{\textcolor{#9D75C4}{s}},\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu}))$
   and carries a body value $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}$,
   which can be undefined ($\textcolor{#398B83}{\bot}$).
2. **Collection ([§19](#19-contribution-collection)).** All occurrences addressed to a coordinate are
   combined, none deduplicated, and an empty fiber gives $0_K$:
   $$
   \textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[p]
   =\bigoplus_{(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\in\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T,p)}
   \textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}.
   $$
3. **Meaning ([§20](#20-program-models-and-functional-denotation)).** A model on inputs $\textcolor{#398B83}{\eta}$ is a complete
   environment that extends $\textcolor{#398B83}{\eta}$, has every actual body defined, and satisfies
   $\textcolor{#398B83}{\rho}(T)=\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)$ for every defined tensor $T$.
   The denotation $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\rrbracket}(\textcolor{#398B83}{\eta})$ is the output part of the model when
   $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ has exactly one element.
4. **Execution ([§24](#24-machine-configurations-and-initialization)–[§25](#25-execution-rules-and-terminal-outcomes)).** A configuration $(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$ holds published values,
   accumulators, and pending occurrences. Three rules fire in any order their
   premises allow:
   $\textcolor{#A87C28}{\mathrm{CONTRIBUTE}}$ adds a pending occurrence's value to its destination's
   accumulator once every address in its read footprint is published;
   $\textcolor{#A87C28}{\mathrm{PUBLISH}}$ makes a coordinate readable once no pending occurrence
   targets it; $\textcolor{#A87C28}{\mathrm{UNDEFINED}}$ ends the run in an explicit failure when a
   ready body is undefined.
5. **Correspondence ([§26](#26-conservation-termination-and-correspondence), [§31](#31-simulation-and-compiler-correctness)).** For programs with a coordinate rank
   certificate, every maximal run succeeds exactly when $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ is a
   singleton and then returns that model; otherwise it fails explicitly.
   A valid compiled plan refines this machine.

In the boundary example of [Section 11.1](#111-boundary-contributions), `T[0,c] = C[c]` and `T[r,0] = R[r]`
give the corner two occurrences, so $T[0,0]=C[0]+R[0]$. Interior coordinates
have empty fibers and receive $0$, and the corner is not readable until both
occurrences have been consumed.

### Notation color key

Color is a visual guide to a symbol's semantic role, not an additional
mathematical assumption. The same roles are used throughout the document:

| Color | Role | Representative notation | Reading cue |
| --- | --- | --- | --- |
| $\textcolor{#5688C7}{\text{Blue}}$ | Domains, signatures, and index binding | $\textcolor{#5688C7}{\Gamma},\textcolor{#5688C7}{\nu},\textcolor{#5688C7}{\Sigma},\textcolor{#5688C7}{I},\textcolor{#5688C7}{\phi}$ | Which coordinates and index assignment? |
| $\textcolor{#9D75C4}{\text{Purple}}$ | Program syntax and source identities | $\textcolor{#9D75C4}{P},\textcolor{#9D75C4}{s},\textcolor{#9D75C4}{E},\textcolor{#9D75C4}{\mathcal{O}},\textcolor{#9D75C4}{\mathrel{+}=}$ | What does the source program say? |
| $\textcolor{#398B83}{\text{Teal}}$ | Denotational values and equations | $\textcolor{#398B83}{\rho},\textcolor{#398B83}{\eta},\textcolor{#398B83}{V},\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits},\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}$ | What values and equations does it mean? |
| $\textcolor{#A87C28}{\text{Amber}}$ | Reference execution and readiness | $\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U},\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits},\textcolor{#A87C28}{\longrightarrow}$ | What is available or executable now? |
| $\textcolor{#C16C86}{\text{Rose}}$ | Compiled execution and physical representation | $\textcolor{#C16C86}{\Pi},\textcolor{#C16C86}{\mathsf{C}},\textcolor{#C16C86}{M},\textcolor{#C16C86}{\xi},\textcolor{#C16C86}{\lambda}$ | How is it scheduled and stored? |

In particular, an index valuation $\textcolor{#5688C7}{\nu}$, a complete
tensor environment $\textcolor{#398B83}{\rho}$, a published-value store
$\textcolor{#A87C28}{\sigma}$, and physical memory $\textcolor{#C16C86}{M}$
are different kinds of object. Color reinforces that distinction.
Published stores and incomplete accumulators share the execution color;
their names and definitions still distinguish them.

Mixed formulas keep each component's role rather than taking one color
as a whole. Tensor names, individual coordinates, ordinary arithmetic,
scalar algebra, and generic mathematical punctuation generally remain
neutral. Locally reused letters are colored by their stated meaning:
for example, a matrix identifier $\textcolor{#9D75C4}{M}$ is source notation, whereas physical
memory $\textcolor{#C16C86}{M}$ is a storage object. Source contribution
notation is purple even when it resembles an update; mathematical equality
remains neutral. Neither color nor source-list position specifies an
execution order.

Read this document in
VS Code's Markdown preview with the built-in `markdown.math.enabled`
setting enabled (the default), or in a browser Markdown preview supporting
KaTeX or MathJax. Plain Markdown without a math renderer displays the
source notation rather than typesetting it. GitHub also imposes a per-page
math-rendering complexity limit; this long document can exceed it even with
supported macros. Use the local preview to render the complete specification.

### Semantic scope

The specification assumes:

- Finite, explicitly determined index domains, including finite scan histories.
- A fixed scalar algebra, or a fixed family of scalar sorts ([Section 2.4](#24-scalar-sorts)), for a
  given development.
- Exact mathematical values, distinguished from machine floating-point values.
- Explicitly specified domains for primitive operators.
- Tensor names whose roles as inputs or defined tensors are distinguished.

Several distinctions apply throughout:

- A statement generates contributions; their collected totals define equations.
- A supplied input is not an implicit contribution, and an unwritten defined
  coordinate receives the empty sum on its declared domain.
- An unavailable value is not an available zero; a ready but undefined
  expression is a different case again.
- Primitive applications and constructed arrays use the strict interpretation
  in [Part III](#part-iii-denotational-semantics). A zero multiplier is not a guard.
- Logical coordinates and published versions remain distinct even when
  physical storage is reused.

Cyclic dependencies remain permitted in the denotational language, but the
direct executor does not select solutions for cyclic equations. Padding,
out-of-range access, implicit conversion between scalar types, floating-point
reduction order, and
machine-number representations are outside the specified fragment. [Part V](#part-v-compilation-and-refinement) treats
physical storage reuse within an exact-value memory model; it does not
silently replace the scalar carrier by floating-point values.

Every lemma and theorem here carries a mathematical argument. Which of them
are also kernel-checked in Lean is recorded in
[Proof status and numbered results](#proof-status-and-numbered-results). The
[Part V](#part-v-compilation-and-refinement) compilation results have no Lean proof. Compiler correctness is
conditional on the stated certificates and kernel contracts; it is not a claim
that an existing compiler satisfies them.
Structural well-formedness alone establishes neither existence of a model
nor an executable dependency order.

The pure-einsum material draws on
[*The Syntax and Semantics of einsum*](https://arxiv.org/html/2509.20020).
[Section 17](#17-pure-einsum-semantics-and-transformation-foundations) adapts it to zero-based finite domains, explicit signatures, and
tagged contributions. The paper uses one-based intervals with positive
extents; this specification permits zero extents. Correspondence arguments
must preserve that difference rather than exclude empty domains implicitly.

### Proof status and numbered results

The lemmas, propositions, theorems, and corollaries below are labeled where
they are stated. Other sections cite them by label. Labels are numbered
sequentially within each top-level section and are not subsection numbers:
"Theorem 26.5" is in [Section 26.4](#264-finite-execution-and-progress-for-ranked-programs), and "[Section 26.3](#263-successful-execution-gives-the-unique-model)" names a section.

| Result | Statement | Lean status (`LeanNCD.Semantics`) |
| --- | --- | --- |
| Proposition 19.1 | Pure-einsum elaboration correspondence | Proved for the bounded source fragment (read-only sums of products over bare slots, over any semiring): `Term.collectedBody_correspondence`, `AdmittedSource.collect_correspondence`, `AdmittedSource.models_iff_global` (`Source`). Open beyond it: the link from admitted reads back to raw source text holds by construction only, and affine slots, guards, marked slices, and nonlinear bodies are outside the fragment. |
| Proposition 19.2 | Source-order invariance | Partial. The occurrence-relabeling form is proved generically (`models_relabel`) and for source programs under any statement permutation: `StatementPermutation.models`, `.collect`, `.admEnv`, `.identities` (`Source.Permutation`). Not stated: the form about successful execution results (Section 28, target 5). |
| Lemma 23.1 | Read stability | Proved: `evalWith_stable`, `interpret_stable` (`Readiness`). |
| Lemma 26.1 | Conservation invariants | Proved: `reachable_invariant` (`Invariants`) yields `Invariant.published` (item 4), `Invariant.consumed` (item 5), `Invariant.conservation` (accumulator formula), and `Invariant.inputs` (inputs unchanged, part of item 3), with `initial_invariant`, `consume_invariant`, `publish_invariant`. Items 1 and 2 follow from the step premises and typing (item 1 via the pending premise and `Finset.erase`). Monotone publication has only the one-step lemma `publish_extends`; the invariant does not need more. |
| Lemma 26.2 | Preservation of every candidate model | Partial. Parts (b) and (c) are `candidate_preserved` (`Soundness`), which also makes failed states incompatible with a model. For part (a), the finished-fiber case is `finished_accumulator`; the partial-fiber sum follows from `Invariant.conservation` and `Invariant.consumed` and is not stated separately in Lean. |
| Theorem 26.3 | A successful run gives the unique model; a failed run excludes every model | Proved: `successful_model`, `successful_unique`, `successful_admInput`, `successful_denotation`, `failed_no_model` (`Soundness`). Executor level: `result_model`, `result_unique`, `result_denotation`, `result_failure` (`ReferenceExecutor`). |
| Lemma 26.4 | Finite execution | Proved: `step_wellFounded`, `no_infinite_chain`, `running_trace_bound`, `failed_trace_bound` (`Measure`). Executor level: `initialBudget_agrees`, `run_not_exhausted` (`ExecutableState`, `ReferenceExecutor`). |
| Theorem 26.5 | Ranked progress | Proved: `ranked_progress`, `ranked_not_blocked` (`Progress`). Executor level: `result_not_blocked`. |
| Theorem 26.6 | Ranked correspondence | Proved: `maximal_dichotomy`, `model_maximal_success`, `no_model_maximal_failure`, `initialization_iff_singleton`, `successful_schedules_agree` (`Progress`). Executor level: `run_ranked_dichotomy`. |
| Corollary 26.7 | Ranked uniqueness | Follows from `model_maximal_success`, `maximal_extension` and `successful_unique`; no separately named theorem. |
| Lemma 31.2 | Terminal adequacy of a valid plan | Not formalized. |
| Theorem 31.3 | Compiled correctness | Not formalized. |
| Lemma 32.1 | Batched accumulation refines individual steps | Not formalized. |

The Lean results above concern the reference machine as a transition relation
over abstract finite carriers and primitives. Its computable refinement now
selects those same legal transitions, validates tensor-level input presence,
and retains typed event paths and exact endpoints. The verified runtime profile
uses exact rationals with reciprocal and square; successful initialized runs
give the unique whole-store model, and reached ready failures exclude models.
For the generic executor the rank certificate and complete ordered schedule
are supplied as data. The bounded source layer builds its schedule
automatically but synthesizes and checks no rank, and its admission accepts only
a bounded fragment rather than general source. No production/backend
refinement is claimed. Arbitrary debug blocking or exhaustion is not a
no-model result.

The bounded source layer admits finite read-only sums of products over bare
slots with identity-keyed valuations, and proves Proposition 19.1 and the
model and collection forms of Proposition 19.2 for that fragment. Its
differential comparison of four evaluation legs (an independent exact oracle,
the rational executor, legacy evaluation, and the checked dense backend) is
executed evidence, not theorems: 79 named fixtures and 39 mutation controls.
Its numerical profile claims exact bit agreement only for programs with
f64-declared integral values of magnitude at most $2^{20}$ and one definition
per left-hand side; it is not a floating-point semantics. Proof target 2 is
covered only at the level of identity-keyed valuations and binder freshening;
there is no substitution on expressions. See
[the Lean path document](lean_executable_semantics_path.md#47-bounded-source-correspondence-and-differential-debugging).
Items 1 and 2 of the proof targets in [Section 28](#28-reference-machine-boundaries-and-proof-targets) (well-definedness of typed
interpretation, and renaming and substitution) are not numbered statements;
the companion document records what covers them. The table reflects
[the Lean path document](lean_executable_semantics_path.md) as of its
2026-10-09 snapshot, which is authoritative for what has landed. Update both
together.

## Table of contents

- [Status and purpose](#status-and-purpose)
  - [Roadmap and reading guide](#roadmap-and-reading-guide)
  - [Semantics at a glance](#semantics-at-a-glance)
  - [Notation color key](#notation-color-key)
  - [Semantic scope](#semantic-scope)
  - [Proof status and numbered results](#proof-status-and-numbered-results)
- [Part I: Background notation](#part-i-background-notation)
  - [1. Numbers, finite sets, and functions](#1-numbers-finite-sets-and-functions)
  - [2. Scalar algebras and finite combination](#2-scalar-algebras-and-finite-combination)
  - [3. Axes, index variables, and valuations](#3-axes-index-variables-and-valuations)
  - [4. Tensor signatures, coordinates, and values](#4-tensor-signatures-coordinates-and-values)
  - [5. Environments and stores](#5-environments-and-stores)
  - [6. Index expressions and coordinate maps](#6-index-expressions-and-coordinate-maps)
  - [7. Free indices, contraction, and broadcasting](#7-free-indices-contraction-and-broadcasting)
  - [8. Operators, predicates, and definedness](#8-operators-predicates-and-definedness)
  - [9. Programs and contribution occurrences](#9-programs-and-contribution-occurrences)
  - [10. Equality, source notation, and interpretation brackets](#10-equality-source-notation-and-interpretation-brackets)
  - [11. Running examples fixing the notation](#11-running-examples-fixing-the-notation)
  - [12. Notation for operational and proof rules](#12-notation-for-operational-and-proof-rules)
- [Part II: Core language and surface elaboration](#part-ii-core-language-and-surface-elaboration)
  - [13. Core syntax and binding](#13-core-syntax-and-binding)
  - [14. Structural well-formedness](#14-structural-well-formedness)
  - [15. Surface-to-core elaboration](#15-surface-to-core-elaboration)
  - [16. Worked core elaborations](#16-worked-core-elaborations)
  - [17. Pure einsum semantics and transformation foundations](#17-pure-einsum-semantics-and-transformation-foundations)
    - [17.1 Index strings and global valuations](#171-index-strings-and-global-valuations)
    - [17.2 Canonical fiber semantics](#172-canonical-fiber-semantics)
    - [17.3 Connection to the contribution core](#173-connection-to-the-contribution-core)
    - [17.4 Delta tensors and diagonal identities](#174-delta-tensors-and-diagonal-identities)
    - [17.5 Conditions for semantic transformations](#175-conditions-for-semantic-transformations)
    - [17.6 Neutral operands and domain preservation](#176-neutral-operands-and-domain-preservation)
- [Part III: Denotational semantics](#part-iii-denotational-semantics)
  - [18. Expression interpretation and definedness](#18-expression-interpretation-and-definedness)
  - [19. Contribution collection](#19-contribution-collection)
  - [20. Program models and functional denotation](#20-program-models-and-functional-denotation)
  - [21. Worked denotational examples](#21-worked-denotational-examples)
  - [22. Denotational scope and execution requirements](#22-denotational-scope-and-execution-requirements)
- [Part IV: Operational semantics](#part-iv-operational-semantics)
  - [23. Read footprints and executable dependencies](#23-read-footprints-and-executable-dependencies)
  - [24. Machine configurations and initialization](#24-machine-configurations-and-initialization)
  - [25. Execution rules and terminal outcomes](#25-execution-rules-and-terminal-outcomes)
  - [26. Conservation, termination, and correspondence](#26-conservation-termination-and-correspondence)
  - [27. Worked operational examples](#27-worked-operational-examples)
  - [28. Reference-machine boundaries and proof targets](#28-reference-machine-boundaries-and-proof-targets)
- [Part V: Compilation and refinement](#part-v-compilation-and-refinement)
  - [29. Execution plans and logical action contracts](#29-execution-plans-and-logical-action-contracts)
  - [30. Concrete states and logical representation](#30-concrete-states-and-logical-representation)
  - [31. Simulation and compiler correctness](#31-simulation-and-compiler-correctness)
  - [32. Batched collection and array kernels](#32-batched-collection-and-array-kernels)
  - [33. Scan compilation and buffer reuse](#33-scan-compilation-and-buffer-reuse)
  - [34. Refinement boundaries and formalization targets](#34-refinement-boundaries-and-formalization-targets)
- [35. Compact notation reference](#35-compact-notation-reference)
- [References and related documents](#references-and-related-documents)

## Part I: Background notation

This part fixes the mathematical objects shared by the core language,
both semantics, and the compilation contracts. Its source examples illustrate
contributions; their explicit syntax and interpretation are defined in
Parts [II](#part-ii-core-language-and-surface-elaboration) and [III](#part-iii-denotational-semantics).

## 1. Numbers, finite sets, and functions

### 1.1 Number systems and finite intervals

We use:

- $\mathbb{N}=\{0,1,2,\ldots\}$ for natural numbers, including zero.
- $\mathbb{Z}$ for integers.
- $\mathbb{R}$ for exact real numbers.
- $\mathbb{B}=\{\mathrm{false},\mathrm{true}\}$ for Booleans.

For $n\in\mathbb{N}$, define the finite ordinal

$$
[n]=\{k\in\mathbb{N}\mid k<n\}.
$$

Thus $[0]=\varnothing$, $[1]=\{0\}$, and $[4]=\{0,1,2,3\}$.
The notation $[n]$ is a set, not a one-element list containing $n$.

A statement ranging over $l\in[N]$ visits $0,\ldots,N-1$. A history with a
base state and $N$ recurrence steps has time domain $[N+1]$, containing
$0,\ldots,N$.

For a finite set $A$, $|A|$ denotes its cardinality. For example,
$|[4]|=4$.

### 1.2 Tuples, products, and rank-zero cases

An ordered tuple is written $(a_1,\ldots,a_k)$. Its positions matter:
$(0,1)$ and $(1,0)$ need not denote the same coordinate.
In coordinate and shape notation, $(a)$ denotes a one-component tuple,
whereas $()$ denotes the empty tuple.

The Cartesian product

$$
A_1\times\cdots\times A_k
$$

contains the tuples whose $j$th component belongs to $A_j$.

The product of no sets is the singleton $\{()\}$ containing the empty tuple.
This convention lets a scalar be treated as a rank-zero tensor with one
coordinate. By contrast, a product with any empty factor is empty.

**Examples.**

- $[2]\times[3]$ has six coordinates.
- A shape with one zero extent, such as $(2,0,3)$, has no coordinates.
- Shape $()$ has one coordinate, namely $()$.

### 1.3 Functions and inverse images

The notation $f:A\to B$ denotes a total function with domain $A$ and codomain
$B$. We write either $f(a)$ or, for tensors, $f[a]$ for application.
For a function on tuple arguments, $f(a,b)$ abbreviates $f((a,b))$.

Composition is $(g\circ f)(a)=g(f(a))$.

For $b\in B$, the inverse image or **fiber** of $b$ is

$$
f^{-1}(\{b\})=\{a\in A\mid f(a)=b\}.
$$

This does not assume that $f$ is invertible.

A function is injective if

$$
f(a)=f(a')\Longrightarrow a=a'.
$$

**Example: a write map with collisions.** Let

$$
\textcolor{#5688C7}{\phi}:[2]\times[2]\to[3],
\qquad
\textcolor{#5688C7}{\phi}(i,j)=i+j.
$$

Then

$$
\textcolor{#5688C7}{\phi}^{-1}(\{1\})=\{(0,1),(1,0)\}.
$$

Two different source coordinates address output coordinate $1$. Such a
collision is legitimate for additive contributions.

We use $\forall$ for universal quantification, $\exists$ for existential
quantification, $\land$ for conjunction, $\lor$ for disjunction, and
$\Longrightarrow$ for implication. The notation
$\{a\in A\mid \textcolor{#9D75C4}{Q}(a)\}$ selects the elements satisfying predicate $\textcolor{#9D75C4}{Q}$.

## 2. Scalar algebras and finite combination

### 2.1 The scalar carrier

$K$ denotes a set of scalar values. The numerical interpretation uses
$K=\mathbb{R}$. Exact reals are mathematical objects; this does not assert that
a Lean runtime stores exact real numbers.

Tensor contraction and contribution collection use a commutative semiring
([Section 2.3](#23-which-algebraic-laws-each-part-uses) records which results use which of its laws)

$$
\mathcal{K}=(K,\oplus,\otimes,0_K,1_K).
$$

Specifically:

- $\oplus$ is associative and commutative, with identity $0_K$.
- $\otimes$ is associative and commutative, with identity $1_K$.
- Multiplication distributes over addition.
- $0_K$ is absorbing for multiplication.

The two principal interpretations are:

| Interpretation | $K$ | $\oplus$ | $\otimes$ | $0_K$ | $1_K$ |
| --- | --- | --- | --- | --- | --- |
| Numerical | $\mathbb{R}$ | $+$ | $\cdot$ | $0$ | $1$ |
| Boolean | $\mathbb{B}$ | $\lor$ | $\land$ | false | true |

The word "additive" means combination by $\oplus$. For Boolean tensors this is
OR, not arithmetic addition of truth values.

Subtraction, division, ordering, and nonlinear functions are **not** supplied
by the semiring structure alone. They need an appropriate carrier and their own
specified operations.

### 2.2 Finite sums and products

For a finite indexing set $A$ and a function $v:A\to K$, write

$$
\bigoplus_{a\in A}v(a)
\qquad\text{and}\qquad
\bigotimes_{a\in A}v(a)
$$

for finite combination and multiplication. Their empty cases are

$$
\bigoplus_{a\in\varnothing}v(a)=0_K,
\qquad
\bigotimes_{a\in\varnothing}v(a)=1_K.
$$

In the numerical interpretation, we also use $\sum$ and $\prod$.

These expressions are indexed by **occurrences**, not by the set of distinct
values. Equal-valued contributions are not deduplicated:

$$
\sum_{a\in[2]}3=6.
$$

In the Boolean interpretation, combining two true contributions gives true
because OR is idempotent. Real addition is not idempotent.

Associativity and commutativity make finite combination independent of
enumeration order in this mathematical setting. Floating-point addition does
not satisfy those laws exactly; an implementation correspondence must address
that distinction explicitly.

### 2.3 Which algebraic laws each part uses

The standing assumption is a commutative semiring, but the results use
different fragments of it:

| Used by | Needs |
| --- | --- |
| Contribution collection ([Section 19](#19-contribution-collection)), conservation, soundness, finite execution, and progress (Sections [24](#24-machine-configurations-and-initialization)-[26](#26-conservation-termination-and-correspondence)), and batched accumulation ([Section 32.1](#321-why-exact-batched-accumulation-refines-individual-steps)) | A commutative monoid $(K,\oplus,0_K)$ on the carrier of each defined tensor |
| Expression interpretation ([Section 18](#18-expression-interpretation-and-definedness)), read footprints, read stability ([Section 23](#23-read-footprints-and-executable-dependencies)) | No laws: $\oplus$, $\otimes$, $0_K$, $1_K$ are interpreted operations, and a reduction is the ascending fold of [Section 18.3](#183-reduction-and-tabulation) |
| Enumeration independence of nested reductions ([Section 15.2](#152-statement-variables-and-term-local-contraction)), the pure-einsum correspondence (Proposition 19.1), Sections [17.1](#171-index-strings-and-global-valuations)-[17.3](#173-connection-to-the-contribution-core) | The commutative-monoid laws of $\oplus$ (associativity, commutativity, identity), the coherence condition, and the bracketing convention below |
| Delta tensors, operand permutation, distribution, neutral operands (Sections [17.4](#174-delta-tensors-and-diagonal-identities)-[17.6](#176-neutral-operands-and-domain-preservation)) | The full semiring laws: $\otimes$ associative and commutative with identity $1_K$, distributivity, and $0_K$ absorbing |

No result of Parts [III](#part-iii-denotational-semantics) and [IV](#part-iv-operational-semantics) uses a law of $\otimes$, distributivity, or
absorption; $1_K$ appears only as the value of a true Iverson predicate.

**Coherence.** An expression combines values with $\oplus$ and uses $0_K$ for an
empty reduction, while collection combines contribution values with $\oplus$
starting from $0_K$. Several results treat these as the same operation and the
same identity, for example the equality of a reduction with its finite
combination ([Section 15.2](#152-statement-variables-and-term-local-contraction)), Proposition 19.1, and [Section 27.3](#273-guards-empty-binders-and-failure), where an
empty reduction contributes the collection identity. This is an assumption on
the development: the expression-level $\oplus$ and $0_K$ agree with the
collection monoid. The Lean formalization keeps them as separate data and
links them by hypothesis; it evaluates a reduction as an ascending fold, which
equals the finite combination of [Section 2.2](#22-finite-sums-and-products) when the monoid laws and
coherence hold.

**Bracketing.** A finite product of an ordered list of factors is the
left-nested product. The $\bigotimes$ over operands in [Section 17.2](#172-canonical-fiber-semantics) and the
product that [Section 15.2](#152-statement-variables-and-term-local-contraction) builds from the same factors in the same order use
this nesting, so relating them uses no law of $\otimes$.

A formalization may give each defined tensor its own commutative monoid when it
proves only the results of the first row, which assume no coherence. Wherever
coherence is used, every defined tensor of a sort uses that sort's $\oplus$ and
$0$. No result compares the monoids of different tensors. This document does
not use that freedom.

### 2.4 Scalar sorts

The text is written for one carrier $K$, but nothing in Parts [III](#part-iii-denotational-semantics)-[IV](#part-iv-operational-semantics) depends
on there being only one. A development may instead fix a family of **sorts**,
each with a carrier $K_s$ and operations $(\oplus_s,\otimes_s,0_s,1_s)$, and a
tensor signature ([Section 4.1](#41-signatures-and-coordinate-domains)) names the sort of its entries. Then:

- A scalar expression has a sort. Literals, tensor reads, Iverson values,
  $\oplus$, $\otimes$, reductions, tabulations, and selection stay within one
  sort, and a tensor read has the sort of the tensor.
- A contribution body has the sort of its destination tensor.
- A registered primitive ([Section 13.2](#132-value-types-and-primitive-signatures)) may have input and output types in
  different sorts. This is the only way a value changes sort.
- Collection on a defined tensor uses the monoid of its sort. A sort that is
  the sort of no defined tensor needs no $\oplus$ laws for Sections [19](#19-contribution-collection)-[26](#26-conservation-termination-and-correspondence);
  enumeration independence of reductions in such a sort needs
  $(K_s,\oplus_s,0_s)$ to be a commutative monoid.
- Every carrier is nonempty, since it contains $0_s$.

The single-carrier text is the case of one sort. Still excluded are implicit
conversion between sorts and machine-number carriers; a Boolean mask feeding a
real computation goes through a registered primitive with declared sorts.

## 3. Axes, index variables, and valuations

### 3.1 Axes and identities

An axis $a$ has an identity and a finite extent $n_a\in\mathbb{N}$. Its
coordinate range is

$$
\textcolor{#5688C7}{I}_a=[n_a].
$$

A printed name is only a label. Distinct axis identities can have the same
label or the same extent. Neither equal spelling nor equal cardinality
establishes identity.
Their coordinate ranges can nevertheless be equal as sets of integers.
Equality of those ranges does not, by itself, identify the axes.

The abstract distinction is relevant to the repository's UID-based axis
representation. The exact correspondence between these mathematical objects
and Lean structures will be specified separately.

### 3.2 Index variables and contexts

An index variable such as $i$ is a bound symbol ranging over a finite domain
$\textcolor{#5688C7}{I}_i$. An **index context** records a finite collection of distinct variable
identities and their domains:

$$
\textcolor{#5688C7}{\Gamma}=(i_1:\textcolor{#5688C7}{I}_{i_1},\ldots,i_k:\textcolor{#5688C7}{I}_{i_k}).
$$

Write $\textcolor{#5688C7}{\mathop{\mathrm{vars}}\nolimits}(\textcolor{#5688C7}{\Gamma})=\{i_1,\ldots,i_k\}$ for the set of
variable identities declared in the context.
The affine core uses scalar integer indices. Tuple coordinates are formed
from several such indices; they are not single integer index variables.

Using the same variable twice imposes the same coordinate value twice. Using
different variables allows different values, even when their ranges coincide.

**Example.** In $\textcolor{#9D75C4}{M}[i,i]$, the two slots use one variable and select a
diagonal. In $\textcolor{#9D75C4}{M}[i,j]$, the two slots vary independently.

Variables are scoped by their binders. A consistently renamed bound variable
does not change meaning. Reusing the spelling `i` in separate statements does
not itself relate their valuations.

### 3.3 Valuations

A valuation $\textcolor{#5688C7}{\nu}$ for $\textcolor{#5688C7}{\Gamma}$ assigns each variable a coordinate in its
declared domain. The set of all such valuations is

$$
\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma})
=
\prod_{i\in\textcolor{#5688C7}{\mathop{\mathrm{vars}}\nolimits}(\textcolor{#5688C7}{\Gamma})}\textcolor{#5688C7}{I}_i.
$$

Here the product is a dependent family of assignments keyed by variable
identity, not an assertion that variable order matters semantically.

We write $\textcolor{#5688C7}{\nu}(i)$ for the assigned coordinate. We write
$\textcolor{#5688C7}{\nu}[i\mapsto k]$ for extension with a fresh variable or replacement of an
existing variable's binding, with $k\in \textcolor{#5688C7}{I}_i$.

**Example.** For $\textcolor{#5688C7}{\Gamma}=(i:[2],j:[3])$, the valuation
$\textcolor{#5688C7}{\nu}=\{i\mapsto1,j\mapsto2\}$ evaluates $i+j$ to $3$.

An admissible iteration domain can be a subset

$$
\textcolor{#5688C7}{D}\subseteq\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma}),
$$

such as the valuations satisfying an explicit guard. A guard restricts
which contributions exist; an Iverson factor changes the value of a
contribution. [Section 13.1](#131-index-expressions-and-predicates) makes that distinction explicit in the syntax.

## 4. Tensor signatures, coordinates, and values

### 4.1 Signatures and coordinate domains

$T,\textcolor{#9D75C4}{U},W,\ldots$ denote tensor identifiers. A finite tensor signature $\textcolor{#5688C7}{\Sigma}$ records
the ordered coordinate domains and scalar carrier of each tensor.

For a rank-$k$ tensor $T$, write

$$
\textcolor{#5688C7}{\Sigma}(T)=(\textcolor{#5688C7}{I}_{T,1},\ldots,\textcolor{#5688C7}{I}_{T,k};K),
\qquad
\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)
=\textcolor{#5688C7}{I}_{T,1}\times\cdots\times \textcolor{#5688C7}{I}_{T,k}.
$$

Its numerical shape is

$$
\textcolor{#5688C7}{\mathop{\mathrm{shape}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)
=(|\textcolor{#5688C7}{I}_{T,1}|,\ldots,|\textcolor{#5688C7}{I}_{T,k}|).
$$

Coordinate-slot position is significant even when domains have equal sizes.
Shape equality alone does not establish a semantic correspondence between
axes.

**Example.** If $T$ has row domain $[5]$ and column domain $[4]$, then
$\textcolor{#5688C7}{\mathop{\mathrm{shape}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)=(5,4)$ and $(3,2)$ is a valid coordinate.
$(5,2)$ is not.

### 4.2 Tensor values

A tensor value for $T$ is a total function

$$
\textcolor{#398B83}{V}_T:\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)\to K.
$$

Write $\textcolor{#398B83}{V}_T[p]$ for its value at coordinate tuple $p$.
The set of such functions can also be written
$K^{\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)}$.

The zero tensor is the function $\textcolor{#398B83}{\mathbf{0}}_T$ given by

$$
\textcolor{#398B83}{\mathbf{0}}_T[p]=0_K
$$

at every coordinate. Zero defaults require a known coordinate domain; they
do not determine a tensor's shape.

A rank-zero tensor is a function $\{()\}\to K$ and is identified with its
single scalar value.

The notation $H_l$ abbreviates the slice $H[:,l]$ when time is the last
coordinate. For example, if $H:[d]\times[N+1]\to K$, then

$$
H_l[i]=H[i,l].
$$

This shorthand refers to logical values, not to a storage layout.

## 5. Environments and stores

### 5.1 Complete tensor environments

A complete tensor environment $\textcolor{#398B83}{\rho}$ assigns each tensor identifier in scope
a value with the signature prescribed by $\textcolor{#5688C7}{\Sigma}$:

$$
\textcolor{#398B83}{\rho}(T):\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)\to K.
$$

The notation $\textcolor{#398B83}{\rho}(T)[p]$ means "coordinate $p$ of the value assigned to $T$."

Write $\textcolor{#5688C7}{\mathrm{In}}$ for input identifiers and $\textcolor{#5688C7}{\mathrm{Def}}$ for defined
identifiers. These disjoint sets partition the signature's identifiers;
$\textcolor{#5688C7}{\mathrm{Out}}\subseteq\textcolor{#5688C7}{\mathrm{Def}}$ designates the outputs.
[Section 13.6](#136-core-programs) includes these roles in a core program's declaration.

An input environment $\textcolor{#398B83}{\eta}$ assigns values only to identifiers in
$\textcolor{#5688C7}{\mathrm{In}}$. A supplied input value is not automatically a contribution
to a defined tensor.

Write $\textcolor{#398B83}{\rho}|_{\textcolor{#5688C7}{\mathrm{In}}}=\textcolor{#398B83}{\eta}$ when $\textcolor{#398B83}{\rho}$ agrees with $\textcolor{#398B83}{\eta}$ on all
designated inputs.

### 5.2 Partial stores and available values

For operational reasoning, a tensor address is a pair

$$
a=(T,p),\qquad p\in\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T).
$$

Let $\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}$ be the set of all such addresses, tagged
by tensor identifier. Coordinates of different tensors are different
addresses even if their tuples coincide.

A partial store is written

$$
\textcolor{#A87C28}{\sigma}:\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\rightharpoonup K.
$$

The hooked arrow denotes a partial function.
$\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$ is the set of addresses at which a value is
available.

An absent value is **not** the same as an available zero. For example,
$(T,p)\notin\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$ does not imply
$\textcolor{#A87C28}{\sigma}(T,p)=0_K$.

Write $\textcolor{#A87C28}{\sigma}[(T,p)\mapsto v]$ for the store updated at that address.
This is a mathematical description of a machine-state update, not an
additive source-language statement.

[Part IV](#part-iv-operational-semantics) distinguishes finalized values from accumulators containing only some
contributions.

### 5.3 Logical addresses, physical slots, and proof-only history

An address $(T,p)$ identifies a **logical tensor coordinate**, not a memory
location. For example, $(H,(i,0))$ and $(H,(i,2))$ remain distinct addresses even if
an implementation stores them in the same buffer at different times.

For physical storage notation, let $\textcolor{#C16C86}{\mathcal{B}}$ be a finite set of buffer
identifiers, with capacity $m_{\textcolor{#C16C86}{\beta}}\in\mathbb{N}$ for each
$\textcolor{#C16C86}{\beta}\in\textcolor{#C16C86}{\mathcal{B}}$. Define

$$
\textcolor{#C16C86}{\mathop{\mathrm{Slot}}\nolimits}_{\textcolor{#C16C86}{\mathcal{B}}}
=\{(\textcolor{#C16C86}{\beta},k)\mid\textcolor{#C16C86}{\beta}\in\textcolor{#C16C86}{\mathcal{B}},\ k\in[m_{\textcolor{#C16C86}{\beta}}]\}.
$$

A physical slot $\textcolor{#C16C86}{\xi}=(\textcolor{#C16C86}{\beta},k)$ is tagged by its buffer identifier, just
as a logical address is tagged by its tensor identifier.
An exact-value memory is a partial map
$\textcolor{#C16C86}{M}:\textcolor{#C16C86}{\mathop{\mathrm{Slot}}\nolimits}_{\textcolor{#C16C86}{\mathcal{B}}}\rightharpoonup K$.
An uninitialized slot is not a stored zero. A capacity-zero buffer has
no slots.

The logical store $\textcolor{#A87C28}{\sigma}$ records published values immutably. A physical
memory $\textcolor{#C16C86}{M}$ may change and reuse slots after their old contents are no
longer needed. A correctness proof may retain an old logical value as
**ghost history**: mathematical information carried by the proof but not
necessarily stored by the executing program.
Ghost history is not a runtime source of tensor values. Every actual read
and every returned output must still have a justified concrete representation.
[Part V](#part-v-compilation-and-refinement) makes this distinction precise.

Here "physical" distinguishes storage from tensor semantics; the contents
are still elements of the exact carrier $K$, not unspecified machine bits.

## 6. Index expressions and coordinate maps

### 6.1 Evaluating index expressions

An index expression $\textcolor{#9D75C4}{e}$ denotes an integer-valued expression under an
appropriate valuation. Write

$$
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{e}\rrbracket_{\textcolor{#5688C7}{\nu}}\in\mathbb{Z}
$$

for its evaluated value.

Examples include constants, variables, and affine expressions:

$$
\textcolor{#9D75C4}{e}=b+\sum_{j=1}^{k}c_j i_j,
\qquad b,c_j\in\mathbb{Z}.
$$

Under $\textcolor{#5688C7}{\nu}(i)=2$, the expression $2i+1$ evaluates to $5$.
Evaluation into $\mathbb{Z}$ preserves negative values; it does not silently
convert them to valid natural-number coordinates.

For an access $T[\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_k]$, write

$$
\textcolor{#5688C7}{\phi}(\textcolor{#5688C7}{\nu})=
(\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{e}_1\rrbracket_{\textcolor{#5688C7}{\nu}},\ldots,
 \textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{e}_k\rrbracket_{\textcolor{#5688C7}{\nu}}).
$$

Calling this a map into $\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)$ asserts that the
tuple is in range throughout the stated domain. Otherwise, it is merely an
integer-tuple-valued expression requiring a boundary policy.

### 6.2 Read maps and write maps

A **read map** selects a source tensor coordinate.
A **write map** associates a contribution occurrence with its destination.
The arithmetic notation is the same, but their roles differ.

**Gather example.** With $i\in[3]$,

$$
Y[i]\textcolor{#9D75C4}{\mathrel{+}=}X[2i]
$$

reads source coordinates $0,2,4$. The source must contain those coordinates
unless an extension policy is explicitly provided.

**Scatter example.** With $i\in[3]$ and $Y$ of shape $(6)$,

$$
Y[2i]\textcolor{#9D75C4}{\mathrel{+}=}X[i]
$$

addresses output coordinates $0,2,4$. Coordinates $1,3,5$ receive no
contributions in this example.

## 7. Free indices, contraction, and broadcasting

A variable is **free** in an expression if it is not bound by a reduction
or another expression binder. A reduction binds its index locally.

In the normalized notation, free variables are the parameters of a
contribution, and contracted variables are explicitly bound:

$$
\textcolor{#9D75C4}{E}(i,j)=\bigoplus_{k\in \textcolor{#5688C7}{I}_k}W[i,k]\otimes X[k,j].
$$

Here $i,j$ are free and $k$ is contracted.

Surface einsum notation may omit this binder:

```text
Y[i,j] = W[i,k] X[k,j]
```

The elaboration of surface notation is defined in [Part II](#part-ii-core-language-and-surface-elaboration). We do not use
"all RHS-only variables are summed" as a substitute for specifying binder
scope.

**Term-local contraction example.**

$$
\textcolor{#9D75C4}{E}(i)=\left(\sum_{k\in \textcolor{#5688C7}{I}_k}W[i,k]X[k]\right)+B[i].
$$

The bias is added once, not once per value of $k$.

**Broadcasting example.** A contribution parameterized by $i,l$ may have
value $X[i]$, independent of $l$. Varying $l$ generates separate contributions
with the same value at different history positions. Independence from a
variable is not contraction over that variable.

**Affine-write example.** In $Y[i+j]\textcolor{#9D75C4}{\mathrel{+}=}A[i]B[j]$, both $i$ and $j$
parameterize contributions because both occur in the output map. Their
colliding images are handled by contribution collection, not by contracting
either variable in the body.

## 8. Operators, predicates, and definedness

A primitive operator $f$ is specified by its input and output value spaces
and its domain of definition. Write

$$
f:\textcolor{#398B83}{\mathcal{D}}_f\to B,
\qquad
\textcolor{#398B83}{\mathcal{D}}_f\subseteq A,
$$

when it accepts values in $\textcolor{#398B83}{\mathcal{D}}_f$ rather than all of $A$.

For exact real arithmetic:

- $\mathop{\mathrm{ReLU}}\nolimits(x)=\max(0,x)$ is defined for every real $x$.
- Real $\log(x)$ requires $x>0$.
- Real $\sqrt{x}$ requires $x\ge0$.
- Division by $z$ requires $z\ne0$.

An operator can consume a whole slice. For example, softmax over nonempty
$[m]$ is a function from $\mathbb{R}^{[m]}$ to
$\mathbb{R}^{[m]}$:

$$
\mathop{\mathrm{softmax}}\nolimits(x)[j]
=
\frac{\exp(x[j])}{\sum_{k\in[m]}\exp(x[k])}.
$$

This is not an independent scalar operation at each coordinate. [Part IV](#part-iv-operational-semantics)
represents its slice dependencies through the full argument footprint.

An Iverson value embeds a predicate $\textcolor{#9D75C4}{Q}$ into the scalar algebra:

$$
\mathbf{1}_{\textcolor{#9D75C4}{Q}}
=
\begin{cases}
1_K,&\textcolor{#9D75C4}{Q}\text{ is true},\\
0_K,&\textcolor{#9D75C4}{Q}\text{ is false}.
\end{cases}
$$

Multiplication by $\mathbf{1}_{\textcolor{#9D75C4}{Q}}$ is a value-level operation, not
short-circuit evaluation of the other factor. In the core, $\textcolor{#9D75C4}{Q}$ depends
only on index values, as specified in [Section 13.1](#131-index-expressions-and-predicates).
For example, $\mathbf{1}_{i<1}\log(X[i])$ is still undefined at $i=1$
if $X[1]=-1$: the zero factor does not make the logarithm defined.

Likewise, a zero-valued contribution is different from removing an occurrence
using a guard, even when their final collected values coincide.

## 9. Programs and contribution occurrences

### 9.1 Statement identities

A program $\textcolor{#9D75C4}{P}$ has a finite sequence of source statements, each assigned a
distinct occurrence identifier $\textcolor{#9D75C4}{s}$.

The sequence records source occurrences; it does not prescribe an
execution order. Identical text appearing twice creates two statement
occurrences. They must not be deduplicated under numerical additive semantics.

In formulas, $\textcolor{#9D75C4}{s}\in \textcolor{#9D75C4}{P}$ means that $\textcolor{#9D75C4}{s}$ ranges over the program's distinct
statement identifiers, not over distinct statement texts.
For each core statement, use the data:

- $T_{\textcolor{#9D75C4}{s}}$: destination tensor identifier.
- $\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$: context of free contribution variables.
- $\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}\subseteq\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}})$: admissible valuations.
- $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}:\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}\to\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T_{\textcolor{#9D75C4}{s}})$: write map.
- $\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}$: body expression, with free variables in $\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$.

[Part II](#part-ii-core-language-and-surface-elaboration) gives the syntax that supplies these data. The write map is derived
from the statement's output index expressions.

### 9.2 Tagged contribution occurrences

A contribution occurrence is a pair $\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$ with $\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$.
The collection of all occurrences is the tagged union

$$
\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}
=
\coprod_{\textcolor{#9D75C4}{s}\in \textcolor{#9D75C4}{P}}\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}
=
\{(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\mid \textcolor{#9D75C4}{s}\in \textcolor{#9D75C4}{P},\ \textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}\}.
$$

The symbol $\coprod$ denotes a disjoint union: the statement identifier
distinguishes otherwise identical valuations.

Its destination is

$$
\textcolor{#9D75C4}{\mathop{\mathrm{dst}}\nolimits}(\textcolor{#9D75C4}{o})=(T_{\textcolor{#9D75C4}{s}},\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu})).
$$

**Example: different occurrences, different destinations.** Let $X$ have
shape $(2)$ and $Y$ shape $(3)$:

```text
s_1: Y[i+1] = X[i]    # i in [2]
```

| Contribution occurrence $\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$ | Destination $\textcolor{#9D75C4}{\mathop{\mathrm{dst}}\nolimits}(\textcolor{#9D75C4}{o})$ |
| --- | --- |
| $(\textcolor{#9D75C4}{s}_1,\{i\mapsto0\})$ | $(Y,(1))$, the entry `Y[1]` |
| $(\textcolor{#9D75C4}{s}_1,\{i\mapsto1\})$ | $(Y,(2))$, the entry `Y[2]` |

An occurrence identifies a statement and its index assignment.
A destination identifies a tensor and its coordinate tuple.

For a tensor coordinate $(T,p)$, define its candidate contribution occurrences:

$$
\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T,p)
=
\{(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\in\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}
  \mid T_{\textcolor{#9D75C4}{s}}=T,\ \textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu})=p\}.
$$

The word "candidate" does not indicate optional contributions. It emphasizes
that this definition locates occurrences without evaluating their bodies.

**Duplicate-statement example.** Independently, let $T$ and $X$ both
have shape $(2)$:

```text
s_1: T[i] = X[i]    # i in [2]
s_2: T[i] = X[i]    # i in [2]
```

At coordinate $(0)$, the two distinct occurrences are

$$
\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T,(0))
=\{(\textcolor{#9D75C4}{s}_1,\{i\mapsto0\}),(\textcolor{#9D75C4}{s}_2,\{i\mapsto0\})\}.
$$

Both have destination $(T,(0))$. With real-valued addition their
collected value is $2X[0]$, not $X[0]$.

**Example: one statement, a shared destination.** For
`s_1: Y[i+j] = A[i] B[j]`, with $A,B$ of shape $(2)$,
$i,j\in[2]$, and $Y$ of shape $(3)$,
the occurrences $(\textcolor{#9D75C4}{s}_1,\{i\mapsto0,j\mapsto1\})$ and
$(\textcolor{#9D75C4}{s}_1,\{i\mapsto1,j\mapsto0\})$ are different but both have destination
$(Y,(1))$. Their contributions are respectively $A[0]B[1]$ and
$A[1]B[0]$.

## 10. Equality, source notation, and interpretation brackets

We distinguish three kinds of notation:

| Notation | Role |
| --- | --- |
| Mathematical $a=b$ | Equality of mathematical objects |
| Surface `T[...] = E` | A source contribution statement |
| Core and expository $T[\textcolor{#5688C7}{\phi}(\textcolor{#5688C7}{\nu})]\textcolor{#9D75C4}{\mathrel{+}=}\textcolor{#9D75C4}{E}(\textcolor{#5688C7}{\nu})$ | Makes the contribution reading explicit |

The symbol $\textcolor{#9D75C4}{\mathrel{+}=}$ does not mean "read the current mutable value of
$T$ and update it immediately." It describes a contribution to be collected.
For a non-numerical scalar algebra, its combination operation is $\oplus$.

Use the following interpretation notation, made precise in [Part III](#part-iii-denotational-semantics):

- $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{e}\rrbracket_{\textcolor{#5688C7}{\nu}}$: the value of an index expression.
- $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}$: the result of interpreting a tensor
  expression under a complete tensor environment and an index valuation;
  it may be undefined.
- $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\rrbracket}(\textcolor{#398B83}{\eta})$: the partial input-output denotation,
  defined when $\textcolor{#398B83}{\eta}$ has a unique complete model, as specified in [Section 20.3](#203-functional-admissibility).
- $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$: environments satisfying a program's
  collected equations on the supplied inputs.

Expression interpretation and program-model satisfaction are different
notions: a complete environment can give every expression a value without
satisfying the equations defining its tensors. A cyclic program must not
be assumed to have a unique model merely because this notation is available.

## 11. Running examples fixing the notation

These examples illustrate the intended contribution reading. They do not
replace the formal semantic definitions in Parts [III](#part-iii-denotational-semantics) and [IV](#part-iv-operational-semantics).

### 11.1 Boundary contributions

Let $C$ and $R$ be inputs of shapes $(4)$ and $(5)$, and let the defined
tensor $T$ have shape $(5,4)$:

```text
T[0,c] = C[c]    # c in [4]
T[r,0] = R[r]    # r in [5]
```

The first write map is $\textcolor{#5688C7}{\phi}_1(c)=(0,c)$ and the second is
$\textcolor{#5688C7}{\phi}_2(r)=(r,0)$. The corner has two contribution occurrences:
$(\textcolor{#9D75C4}{s}_1,c=0)$ and $(\textcolor{#9D75C4}{s}_2,r=0)$.

Under real-valued additive collection, the intended values are

$$
T[r,c]
=
\mathbf{1}_{r=0}C[c]
+
\mathbf{1}_{c=0}R[r].
$$

In particular, $T[0,0]=C[0]+R[0]$. There is no requirement that the
two corner contributions agree. Interior coordinates receive an empty sum,
namely zero.

### 11.2 Colliding affine writes

Let $A,B$ be inputs of shape $(2)$ and $Y$ a defined tensor of shape $(3)$:

```text
Y[i+j] = A[i] B[j]    # i,j in [2]
```

The write fiber at $1$ has two occurrences, giving

$$
\begin{aligned}
Y[0]&=A[0]B[0],\\
Y[1]&=A[0]B[1]+A[1]B[0],\\
Y[2]&=A[1]B[1].
\end{aligned}
$$

The body has no contracted variables. The addition arises from collecting
different free-variable valuations with the same write image.

### 11.3 Activation before versus after collection

Let $A,B$ be inputs on the same declared vector domain, with $T$ and,
where used, `Pre` defined on that domain. These two programs have different
collected values:

| Activation within contributions | Activation after collection |
| --- | --- |
| `T[i] = relu(A[i])` | `Pre[i] = A[i]` |
| `T[i] = relu(B[i])` | `Pre[i] = B[i]` |
| | `T[i] = relu(Pre[i])` |

They respectively give

$$
T[i]=\mathop{\mathrm{ReLU}}\nolimits(A[i])+\mathop{\mathrm{ReLU}}\nolimits(B[i])
$$

and

$$
T[i]=\mathop{\mathrm{ReLU}}\nolimits(A[i]+B[i]).
$$

For $A[i]=1$ and $B[i]=-1$, the first is $1$ and the second is $0$.
Expression structure, not statement enumeration order, determines the
activation boundary.

### 11.4 A finite history with persistent input

Let $X,Z$ be inputs of shape $(d)$ and $H$ a defined tensor of shape
$(d,N+1)$. Let
$F:\mathbb{R}^{[d]}\to\mathbb{R}^{[d]}$ be a total function:

```text
H[i,l]   = X[i]             # i in [d], l in [N+1]
H[i,0]   = Z[i]             # i in [d]
H[i,l+1] = F(H[:,l])[i]     # i in [d], l in [N]
```

The occurrences addressed to time zero come from the first two statements.
Occurrences addressed to later times come from the first and third.
The intended collected equations are

$$
H_0=X+Z,
\qquad
H_{l+1}=X+F(H_l)\quad(l\in[N]).
$$

$H_l$ means the completed logical slice, not an accumulator containing only
some contributions. The domains $[N+1]$ and $[N]$ are deliberately different.
Reusing the printed variable `l` does not make their binders identical.

## 12. Notation for operational and proof rules

Use:

- $\textcolor{#A87C28}{\mathsf{Conf}}$ for a machine configuration.
- $\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\longrightarrow}\textcolor{#A87C28}{\mathsf{Conf}}'$ for one execution step.
- $\textcolor{#A87C28}{\longrightarrow}^{*}$ for zero or more execution steps.
- $\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\Downarrow}\textcolor{#398B83}{\rho}$ for termination with result environment $\textcolor{#398B83}{\rho}$.
- $\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)$ for the tensor addresses required to evaluate the
  contributions at address $a$, as defined in [Section 23](#23-read-footprints-and-executable-dependencies).
- $r:\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\to\mathbb{N}$ for a dependency rank when
  a finite acyclic ordering exists.

The rank condition used in [Part IV](#part-iv-operational-semantics) is

$$
b\in\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)\Longrightarrow r(b)<r(a).
$$

This is notation for a sufficient well-founded ordering, not a claim that all
tensor logic programs possess one. Dependencies at tensor-name level and
coordinate level are different: a recurrence can read its own tensor name
while still depending only on earlier coordinates.

For proof judgments, $\textcolor{#5688C7}{\Gamma}\vdash J$ reads "judgment $J$ holds in context
$\textcolor{#5688C7}{\Gamma}$." Here $\textcolor{#5688C7}{\Gamma}$ will be an index context unless explicitly qualified.
[Part II](#part-ii-core-language-and-surface-elaboration) introduces structural typing judgments, and [Part III](#part-iii-denotational-semantics) defines expression
interpretation and program models. [Part IV](#part-iv-operational-semantics) defines the execution judgments
and their rules.

## Part II: Core language and surface elaboration

The core removes implicit contraction and implicit slice construction.
It retains additive statements: their contributions are not converted into
ordered mutation commands.

The core specifies the **in-bounds fragment**. A read or write must
address a valid coordinate throughout its applicable index domain. Boundary
extensions such as zero padding are not silently inserted; they require
separate syntax or an explicit extension of this fragment.

## 13. Core syntax and binding

### 13.1 Index expressions and predicates

The core index expressions are affine:

$$
\textcolor{#9D75C4}{e} ::= b \mid i \mid \textcolor{#9D75C4}{e}+\textcolor{#9D75C4}{e} \mid c\,\textcolor{#9D75C4}{e},
\qquad b,c\in\mathbb{Z}.
$$

Here $i$ is an index variable from a context $\textcolor{#5688C7}{\Gamma}$, not a tensor value.
Subtraction is expressed using coefficient $-1$.
Scalar arithmetic in an expression is distinct from integer index arithmetic.

The index predicates used for guards and Iverson values are:

$$
\textcolor{#9D75C4}{Q} ::= \mathrm{true}\mid\mathrm{false}
\mid \textcolor{#9D75C4}{e}=\textcolor{#9D75C4}{e}\mid \textcolor{#9D75C4}{e}<\textcolor{#9D75C4}{e}
\mid \neg \textcolor{#9D75C4}{Q}\mid \textcolor{#9D75C4}{Q}\land \textcolor{#9D75C4}{Q}\mid \textcolor{#9D75C4}{Q}\lor \textcolor{#9D75C4}{Q}.
$$

The usual comparisons such as $\textcolor{#9D75C4}{e}\le \textcolor{#9D75C4}{e}'$ are abbreviations. Predicates depend
only on index valuations, not on tensor values. This makes a statement's
contribution domain determinable without executing its body.

Write $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{Q}\rrbracket_{\textcolor{#5688C7}{\nu}}\in\mathbb{B}$ for predicate evaluation
using integer comparisons and Boolean connectives.
This Boolean result is distinct from its scalar embedding
$\mathbf{1}_{\textcolor{#9D75C4}{Q}}\in K$.

**Example.** The guard $i+1<4$ selects the valuations $i=0,1,2$ from
$i\in[4]$. It creates no occurrence for $i=3$.
Multiplication by $\mathbf{1}_{i+1<4}$ instead retains that occurrence
and changes its body value; it does not automatically suppress invalid reads.

### 13.2 Value types and primitive signatures

An expression has a value type $\textcolor{#5688C7}{\tau}$, which is either:

- The scalar type $K$.
- An array type $K^{\textcolor{#5688C7}{I}_1\times\cdots\times \textcolor{#5688C7}{I}_m}$, with $m\ge1$.

Each array slot has a specified finite coordinate domain, just as for a
tensor signature in [Section 4](#4-tensor-signatures-coordinates-and-values). Rank-zero values use the scalar type $K$.
Arrays here are expression values, not necessarily named tensors.

A fixed primitive registry $\textcolor{#9D75C4}{\mathcal{F}}$ supplies, for every operator $f$,
an arity $q$, input types $\textcolor{#5688C7}{\tau}_1,\ldots,\textcolor{#5688C7}{\tau}_q$, an output type $\textcolor{#5688C7}{\tau}$,
and a domain

$$
\textcolor{#398B83}{\mathcal{D}}_f\subseteq\textcolor{#5688C7}{\tau}_1\times\cdots\times\textcolor{#5688C7}{\tau}_q.
$$

The types in this formula denote their value spaces. This specializes the
operator-domain notation from [Section 8](#8-operators-predicates-and-definedness).
Primitive interpretations are deterministic mathematical functions of
their arguments on $\textcolor{#398B83}{\mathcal{D}}_f$. They have no hidden store reads or side
effects. Computable implementations and domain tests are separate requirements.

For example, real ReLU has one scalar argument and result. Softmax is
registered for every $m\ge0$, with one argument and result of type
$\mathbb{R}^{[m]}$. Its domain of definition is all of $\mathbb{R}^{[m]}$
when $m>0$ and is empty when $m=0$, matching the nonempty requirement of
[Section 8](#8-operators-predicates-and-definedness). Because softmax is registered at $m=0$, a statement whose slice
domain is empty type checks; having no occurrences, it never demands the
application. A demanded application to an empty array is undefined.
A user-supplied $F:\mathbb{R}^{[d]}\to\mathbb{R}^{[d]}$ can be a registered
array operator, with its domain specified in the same way.

There is no implicit application of an array operator coordinate by
coordinate, and no implicit distribution of any operator over $\oplus$.

### 13.3 Expression constructors

The core expression constructors are:

| Constructor | Meaning and binding |
| --- | --- |
| $c_K$ | A scalar literal belonging to $K$ |
| $T[\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_k]$ | A scalar read from a named tensor |
| $\mathbf{1}_{\textcolor{#9D75C4}{Q}}$ | Scalar embedding of an index predicate |
| $\textcolor{#9D75C4}{E}_1\oplus \textcolor{#9D75C4}{E}_2$ | Combination of two scalar expressions |
| $\textcolor{#9D75C4}{E}_1\otimes \textcolor{#9D75C4}{E}_2$ | Multiplication of two scalar expressions |
| $\bigoplus_{j\in \textcolor{#5688C7}{I}_j}\textcolor{#9D75C4}{E}$ | Scalar reduction; binds $j$ in $\textcolor{#9D75C4}{E}$ |
| $\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j_1\in \textcolor{#5688C7}{I}_1,\ldots,j_m\in \textcolor{#5688C7}{I}_m}(\textcolor{#9D75C4}{E})$ | Array construction; binds all $j_1,\ldots,j_m$ in a scalar body |
| $\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}(\textcolor{#9D75C4}{E},(\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_m))$ | Selects a scalar coordinate from an array expression |
| $f(\textcolor{#9D75C4}{E}_1,\ldots,\textcolor{#9D75C4}{E}_q)$ | Applies a primitive with its declared input and output types |

The number of indices in a named read must match its tensor rank. A scalar
tensor is read as $T[]$.
Tabulation uses $m\ge1$ distinct bound variables and constructs the full
Cartesian product of their domains, including an empty array if a domain
is empty.

The combining operations displayed here are scalar operations.
Pointwise array addition, if desired, is expressed by tabulating scalar
addition or by a registered primitive with an explicit array signature.

**Example: construct a vector, then select an entry.** Work over
$K=\mathbb{R}$ and let $X$ have shape $(3)$, with entries
$X[0]=2$, $X[1]=5$, and $X[2]=7$.
The array expression

$$
\textcolor{#398B83}{V}=\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[3]}(X[j]+1)
$$

constructs all three entries: $\textcolor{#398B83}{V}[0]=3$, $\textcolor{#398B83}{V}[1]=6$, and $\textcolor{#398B83}{V}[2]=8$.
The bound variable $j$ visits each coordinate; it is not summed out.
Selection then gives

$$
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}(\textcolor{#398B83}{V},(1))=6.
$$

Here $(1)$ is the one-coordinate tuple for a vector, and $\textcolor{#398B83}{V}$ is an expository
name for the resulting value, not an additional core binding construct.
Thus `tab` constructs an array from a scalar body, whereas `at` reads
one scalar from that array.

**Example: a history slice.**

$$
\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[d]}(H[j,l])
$$

is an array expression of type $K^{[d]}$, with $l$ free and $j$ bound.
It makes the shorthand $H[:,l]$ from [Part I](#part-i-background-notation) explicit.

**Example: a scalar selected from an array computation.**

$$
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
F\left(\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[d]}(H[j,l])\right),(i)
\right)
$$

is the core form of $F(H[:,l])[i]$.

### 13.4 Scope, freshness, and substitution

All bound variables have identities distinct from the variables already
in scope. Printed names can be changed consistently to satisfy this
freshness convention.

For an expression $\textcolor{#9D75C4}{E}$, $\textcolor{#9D75C4}{\mathop{\mathrm{FV}}\nolimits}(\textcolor{#9D75C4}{E})$ denotes its free variables.
For example,

$$
\textcolor{#9D75C4}{\mathop{\mathrm{FV}}\nolimits}\left(\bigoplus_{k\in \textcolor{#5688C7}{I}_k}W[i,k]\otimes X[k,j]\right)
=\{i,j\}.
$$

The corresponding notation applies to index expressions and predicates.
For multiple expressions, take the union of their free-variable sets.

$\textcolor{#9D75C4}{E}[i:=\textcolor{#9D75C4}{e}]$ denotes capture-avoiding substitution of index expression $\textcolor{#9D75C4}{e}$
for the free occurrences of $i$. Bound variables are renamed when needed
to prevent capture. This syntactic substitution is distinct from the
valuation update $\textcolor{#5688C7}{\nu}[i\mapsto k]$.

**Example.** In

$$
\textcolor{#9D75C4}{E}(i)=\bigoplus_{k\in[k_0]}W[i,k]\otimes X[k],
$$

the substitution $\textcolor{#9D75C4}{E}[i:=k]$ first renames the bound reduction variable,
giving, for a fresh $h$,

$$
\bigoplus_{h\in[k_0]}W[k,h]\otimes X[h].
$$

The replacement's $k$ stays free.

### 13.5 Core contribution statements

A core statement with occurrence identifier $\textcolor{#9D75C4}{s}$ has the form

$$
\text{for }\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}\text{ where }\textcolor{#9D75C4}{Q}_{\textcolor{#9D75C4}{s}}:
\qquad
T_{\textcolor{#9D75C4}{s}}[\textcolor{#9D75C4}{e}_{\textcolor{#9D75C4}{s},1},\ldots,\textcolor{#9D75C4}{e}_{\textcolor{#9D75C4}{s},k_{\textcolor{#9D75C4}{s}}}]\textcolor{#9D75C4}{\mathrel{+}=}\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}.
$$

$\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$ binds the statement's contribution variables in its guard,
output indices, and body. The body must have the scalar type of its
destination tensor ($K$ when there is one sort).
The guard is optional, with omitted guard meaning $\mathrm{true}$.

The guard and output indices determine the data introduced in [Section 9](#9-programs-and-contribution-occurrences):

$$
\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}=\{\textcolor{#5688C7}{\nu}\in\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}})
       \mid\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{Q}_{\textcolor{#9D75C4}{s}}\rrbracket_{\textcolor{#5688C7}{\nu}}=\mathrm{true}\},
$$

$$
\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu})=
(\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{e}_{\textcolor{#9D75C4}{s},1}\rrbracket_{\textcolor{#5688C7}{\nu}},\ldots,
 \textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{e}_{\textcolor{#9D75C4}{s},k_{\textcolor{#9D75C4}{s}}}\rrbracket_{\textcolor{#5688C7}{\nu}}).
$$

The binders are part of the statement's identity as a contribution
generator. They are not discarded when an output index simplifies.
For instance, with $i\in[3]$, the statement

$$
T[0i]\textcolor{#9D75C4}{\mathrel{+}=}1_K
$$

has three occurrences addressed to coordinate $0$, not one.

### 13.6 Core programs

A core program consists of:

1. A finite signature $\textcolor{#5688C7}{\Sigma}$, over the scalar carrier $K$ (or the
   sort family of [Section 2.4](#24-scalar-sorts)).
2. A partition of its tensor identifiers into designated inputs
   $\textcolor{#5688C7}{\mathrm{In}}$ and defined tensors $\textcolor{#5688C7}{\mathrm{Def}}$.
3. Designated output identifiers $\textcolor{#5688C7}{\mathrm{Out}}\subseteq\textcolor{#5688C7}{\mathrm{Def}}$.
4. A finite sequence of core statements with distinct occurrence identifiers.

These named identifier sets are finite; $\textcolor{#5688C7}{\mathrm{In}}$ and $\textcolor{#5688C7}{\mathrm{Def}}$
are disjoint and their union is exactly the identifier domain of $\textcolor{#5688C7}{\Sigma}$.
Every statement targets an identifier in $\textcolor{#5688C7}{\mathrm{Def}}$.
Reads may refer to either set.

A defined tensor need not have any statements targeting it. Its values
are governed by the empty-collection rule in [Section 19](#19-contribution-collection).
Conversely, declaring a tensor to be an input does not
provide its values: an input environment $\textcolor{#398B83}{\eta}$ must supply them.

Designated outputs specify whole tensor values with their declared coordinate
domains. If $H$ is a history tensor and $H\in\textcolor{#5688C7}{\mathrm{Out}}$, the output includes
every time slice, not just its last slice. Returning only the final state
requires a separately declared output, for example a tensor `Last` defined
by `Last[i] = H[i,N]`. This distinction also determines which values a
compiled execution must retain for output decoding.

## 14. Structural well-formedness

### 14.1 Judgments and admissible valuations

Use the judgments

$$
\textcolor{#5688C7}{\Gamma}\vdash \textcolor{#9D75C4}{e}:\mathbb{Z},
\qquad
\textcolor{#5688C7}{\Gamma}\vdash \textcolor{#9D75C4}{Q}:\mathrm{pred},
\qquad
\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma};\textcolor{#5688C7}{D}\vdash \textcolor{#9D75C4}{E}:\textcolor{#5688C7}{\tau},
$$

where $\textcolor{#5688C7}{D}\subseteq\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma})$.
The marker $\mathrm{pred}$ classifies index predicates; it is not a scalar
type. The primitive registry and scalar algebra are fixed parameters.

The expression judgment establishes binding, value types, and
in-bounds index use for valuations in $\textcolor{#5688C7}{D}$.
It does **not** assert that value-dependent primitive domains are met.
In particular, $\log(T[i])$ can have scalar type while still requiring
positive tensor values for its interpretation to be defined.

For a fresh $j:\textcolor{#5688C7}{I}_j$, define the lifted valuation domain

$$
\textcolor{#5688C7}{D}^{+j}
=
\{\textcolor{#5688C7}{\nu}[j\mapsto k]\mid\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D},\ k\in \textcolor{#5688C7}{I}_j\}
\subseteq\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma},j:\textcolor{#5688C7}{I}_j).
$$

For several fresh variables, lift successively. This accounts for every
coordinate evaluated inside a reduction or tabulation.

**Example: a guarded row sum.** Work over $K=\mathbb{R}$, with
$\textcolor{#5688C7}{\Sigma}(X)=([4],[2];\mathbb{R})$ and $\textcolor{#5688C7}{\Gamma}=(i:[4])$.
Choose the index expression $\textcolor{#9D75C4}{e}=i+1$ and predicate $\textcolor{#9D75C4}{Q}=(i+1<4)$.
The first two judgments are

$$
\textcolor{#5688C7}{\Gamma}\vdash i+1:\mathbb{Z},
\qquad
\textcolor{#5688C7}{\Gamma}\vdash i+1<4:\mathrm{pred}.
$$

The admissible valuations are

$$
\textcolor{#5688C7}{D}=\{\{i\mapsto0\},\{i\mapsto1\},\{i\mapsto2\}\}.
$$

Introduce a fresh reduction variable $j\in[2]$. Lifting gives

$$
\textcolor{#5688C7}{D}^{+j}
=
\{\{i\mapsto a,j\mapsto b\}\mid a\in[3],\ b\in[2]\}.
$$

This domain contains six valuations. Every one makes the read
$X[i+1,j]$ valid: its row is $1$, $2$, or $3$, and its column is
$0$ or $1$. For instance, $\{i\mapsto2,j\mapsto1\}$ reads $X[3,1]$.
Consequently, the body and reduction judgments are

$$
\textcolor{#5688C7}{\Sigma};(\textcolor{#5688C7}{\Gamma},j:[2]);\textcolor{#5688C7}{D}^{+j}\vdash X[i+1,j]:\mathbb{R},
$$

$$
\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma};\textcolor{#5688C7}{D}\vdash
\bigoplus_{j\in[2]}X[i+1,j]:\mathbb{R}.
$$

The result is a scalar row sum for each admissible $i$, not an array.
If $\textcolor{#5688C7}{D}$ instead included $\{i\mapsto3\}$, the body would try to read
row $4$, so the in-bounds expression judgment would fail even though
$i+1$ remains a well-scoped integer expression.

### 14.2 Index and expression rules

Index literals are integers, variables must belong to $\textcolor{#5688C7}{\Gamma}$, and
affine constructors preserve the integer index type.
Predicates are built from well-scoped index expressions using the
constructors in [Section 13.1](#131-index-expressions-and-predicates).

The expression rules are:

| Constructor | Required premises and result |
| --- | --- |
| $c_K$ | $c_K\in K$; result $K$ |
| $T[\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_k]$ | $T$ is declared, rank is $k$, indices are well-scoped, and their tuple belongs to $\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)$ for every $\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}$; result $K$ |
| $\mathbf{1}_{\textcolor{#9D75C4}{Q}}$ | $\textcolor{#5688C7}{\Gamma}\vdash \textcolor{#9D75C4}{Q}:\mathrm{pred}$; result $K$ |
| $\textcolor{#9D75C4}{E}_1\oplus \textcolor{#9D75C4}{E}_2$, $\textcolor{#9D75C4}{E}_1\otimes \textcolor{#9D75C4}{E}_2$ | Both operands have type $K$ under the same $\textcolor{#5688C7}{\Sigma},\textcolor{#5688C7}{\Gamma},\textcolor{#5688C7}{D}$; result $K$ |
| $\bigoplus_{j\in \textcolor{#5688C7}{I}_j}\textcolor{#9D75C4}{E}$ | The body has type $K$ under $\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma},j:\textcolor{#5688C7}{I}_j;\textcolor{#5688C7}{D}^{+j}$; result $K$ |
| $\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j_1\in \textcolor{#5688C7}{I}_1,\ldots,j_m\in \textcolor{#5688C7}{I}_m}(\textcolor{#9D75C4}{E})$ | The body has type $K$ under the extended context and lifted domain; result $K^{\textcolor{#5688C7}{I}_1\times\cdots\times \textcolor{#5688C7}{I}_m}$ |
| $\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}(\textcolor{#9D75C4}{E},(\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_m))$ | $\textcolor{#9D75C4}{E}$ has the matching array type, the indices are well-scoped, and the selected tuple is in its coordinate domain for every $\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}$; result $K$ |
| $f(\textcolor{#9D75C4}{E}_1,\ldots,\textcolor{#9D75C4}{E}_q)$ | Each operand has the corresponding type from $\textcolor{#9D75C4}{\mathcal{F}}$ under the same $\textcolor{#5688C7}{\Sigma},\textcolor{#5688C7}{\Gamma},\textcolor{#5688C7}{D}$; result is the declared output type |

Tabulation and reduction lift $\textcolor{#5688C7}{D}$ over the whole declared binder domain,
not just over coordinates occurring in some other statement.
Arrays are complete on their own declared domains, not sparse collections
of available entries. An explicitly restricted tabulation can still
construct a complete array on a prefix of a named tensor's domain.

These rules use compatible declared coordinate domains, not name-based
axis matching or an implicit transpose. An implementation mapping must
retain any axis identities and explicitly justified identifications.
Because $\textcolor{#5688C7}{I}_a=[n_a]$ is a set of integers ([Section 3.1](#31-axes-and-identities)), these
judgments see only coordinate ranges: two axes of equal extent are
indistinguishable to them. Distinguishing such axes is the job of domain
resolution (assumed before elaboration in [Section 15.1](#151-explicit-inputs-to-elaboration)) and the
implementation mapping, not of the core rules.

The core permits an explicitly restricted index domain. For example,
with $A$ of shape $(3)$, $B$ of shape $(5)$, and $i\in[3]$, the reads
$A[i]$ and $B[i]$ are both in bounds. The pointwise product
$A[i]\otimes B[i]$ uses all three entries of $A$ but only the first
three entries of $B$; $B[3]$ and $B[4]$ are unused.
This is not a full-axis einsum, which requires matching domains for
the shared index.
The standard pure-einsum profile below imposes the additional full-domain
compatibility rule. It does not replace the more general core read rule.

### 14.3 Statement and program rules

A statement is structurally well-formed when:

1. Its destination belongs to $\textcolor{#5688C7}{\mathrm{Def}}$.
2. Its guard and output indices are well-scoped under $\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$.
3. Its output arity matches the destination rank.
4. $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu})\in\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T_{\textcolor{#9D75C4}{s}})$ for every $\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$.
5. $\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}};\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}\vdash \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}:K$.

A program is structurally well-formed when its declarations, role
partition, output identifiers, occurrence identifiers, and every
statement satisfy their respective conditions.

Neither injectivity of $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}$ nor disjointness of different statements'
write images is required. Additive overlap is allowed.
No condition here requires an acyclic dependency graph.

### 14.4 Mathematical conditions versus compiler decisions

The quantified in-bounds premises specify a mathematical property.
They do not require a particular compiler to decide every such property
automatically. A compiler may prove admitted affine cases, accept explicit
evidence, or reject a case it cannot establish.

Operator definedness is a different condition. The interpretation in
[Section 18](#18-expression-interpretation-and-definedness) accounts for $\textcolor{#398B83}{\mathcal{D}}_f$ (where $f$ is the primitive
operator and $\textcolor{#398B83}{\mathcal{D}}_f$ is its domain of definition), distinguishing
defined values from undefined results. [Section 20](#20-program-models-and-functional-denotation) then specifies
admissible inputs for a functional program denotation.
A runtime check is not a proof that every input meets that condition.

**Guard example.** Let $X$ have shape $(4)$ and $i\in[4]$:

$$
\text{for }i\in[4]\text{ where }i+1<4:
\qquad Y[i]\textcolor{#9D75C4}{\mathrel{+}=}X[i+1].
$$

The guard makes the read in bounds throughout $\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$.
Replacing it by the body
$\mathbf{1}_{i+1<4}X[i+1]$ without a guard does not satisfy the read
rule at $i=3$.

## 15. Surface-to-core elaboration

**Surface notation** is the compact, user-facing syntax in which tensor
logic programs are written, such as `Y[i,j] = W[i,k] X[k,j]`.
It leaves some information implicit, including the contraction over $k$.
The **core notation** from [Section 13](#13-core-syntax-and-binding) makes binders, reductions, and
operator applications explicit. **Elaboration** translates the surface
form into that core form; it is not execution of the program.

### 15.1 Explicit inputs to elaboration

The surface notation abbreviates the core; it is not a second semantics.
Elaboration takes:

- A tensor signature and the input/defined/output roles.
- Resolved index-variable identities and their finite domains.
- The statement's output indices, optional guard, and expression structure.
- The fixed primitive registry.

Domains may originate from declarations or an unambiguous inference
procedure. This section assumes each index variable's domain is already
known. It specifies translation into core syntax, not the preceding
domain-inference procedure. Equal printed names or equal extents alone do
not resolve semantic axis identities. Ambiguous or inconsistent domains are errors,
not silent choices.

**Standard pure-einsum profile.** When a statement is presented as an
ordinary full-axis einsum, its operand indices are bare variables,
its body is a product of at least one tensor read, and it has no guard or enclosing
primitive. Every occurrence of an index variable must range over the
entire coordinate domain of its corresponding slot. Thus all slots
sharing that variable must have equal resolved domains, not merely a
common in-bounds subset. Each output variable must occur in an operand.
The declared destination has one slot per output index, in that order,
with exactly that index's resolved domain. Repeated output variables are
permitted; they label separate destination slots.

Consequently, $A[i]B[i]$ with operand lengths $3$ and $5$ is rejected as
a standard full-axis einsum. An explicitly restricted core binder can
still specify the prefix computation described in [Section 14.2](#142-index-and-expression-rules).
Broadcasting an output-only variable from a declared domain is also a
core/general surface capability, not a standard pure-einsum inference.
[Section 17](#17-pure-einsum-semantics-and-transformation-foundations) gives the reference semantics for the standard profile.

Surface syntax supported here consists of an additive body of products
of scalar factors, optionally enclosed by one unary scalar operator or
one marked slice operator. Factors are scalar literals, named scalar
reads, Iverson values, or registered scalar unary operators on a named
scalar read. Such a factor introduces no hidden reduction of its own.

More general nesting must use explicit core reductions, tabulations, and
primitive applications. This restriction prevents inventing a contraction
scope for arbitrary nested surface expressions.

Explicit core scalar expressions can also be written as a statement body,
with their binders and primitive signatures checked directly rather than
adding implicit contractions. The slice shorthand $T[:,l]$ expands to
$\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in \textcolor{#5688C7}{I}_{T,1}}(T[j,l])$ for a fresh $j$;
the corresponding rule for several colon slots tabulates their declared
domains in slot order. Selection from an array expression, such as
$F(T[:,l])[i]$, expands to $\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}$ as in [Section 13.3](#133-expression-constructors).
The fixed indices must remain well-scoped and in bounds.

### 15.2 Statement variables and term-local contraction

The contribution-variable context $\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$ contains the variables
occurring in the output index expressions. Domains are resolved as above.
They are collected before algebraically simplifying those expressions,
so cancellation of coefficients does not remove contribution binders.

For this surface fragment, guard variables must also belong to
$\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$. A more general core statement can explicitly bind additional
contribution variables.

Write the surface additive body as a finite list of product terms
$t_1,\ldots,t_h$. For term $t_b$, define its contracted-variable set

$$
C_b=\textcolor{#9D75C4}{\mathop{\mathrm{FV}}\nolimits}(t_b)\setminus\textcolor{#5688C7}{\mathop{\mathrm{vars}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}),
$$

where $\textcolor{#5688C7}{\mathop{\mathrm{vars}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}})$ is the context's variable-identity set
from [Section 3.2](#32-index-variables-and-contexts). Each contracted variable has its own resolved
domain.

Elaborate the factors to scalar core expressions, multiply them with
$\otimes$, and bind the variables in $C_b$ using nested $\bigoplus$
reductions. A repeated variable in several factors is bound once and
has the same value in each occurrence.

Use a fixed enumeration of $C_b$ to produce a concrete syntax tree.
The commutative-monoid laws of $\oplus$, with the coherence condition of
[Section 2.3](#23-which-algebraic-laws-each-part-uses), justify independence from that enumeration; floating-point
execution must separately specify its order.
Each reduction binder is scoped only over its own term.

Let $B_{\textcolor{#9D75C4}{s}}$ denote the core body obtained by combining the elaborated terms
with $\oplus$. An empty product uses $1_K$, and an empty list of terms
uses $0_K$.

This rule gives

$$
W[i,k]X[k]+B[i]
\quad\mapsto\quad
\left(\bigoplus_{k\in \textcolor{#5688C7}{I}_k}W[i,k]\otimes X[k]\right)\oplus B[i].
$$

It does not give
$\bigoplus_{k\in \textcolor{#5688C7}{I}_k}(W[i,k]\otimes X[k]\oplus B[i])$.

### 15.3 Scalar operator placement

Without an enclosing operator, the contribution body is $\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}=B_{\textcolor{#9D75C4}{s}}$.
With a registered unary scalar operator $f$, it is

$$
\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}=f(B_{\textcolor{#9D75C4}{s}}).
$$

In particular, contractions inside each term and explicit combination
of those terms occur inside $f$'s argument.

Separate statements with enclosing operators still create separate
contributions. Elaboration does not move $f$ outside their collection
or assume $f(x\oplus y)=f(x)\oplus f(y)$.

### 15.4 Marked slice operators

In the marked slice abbreviation, a trailing dot on a surface output index
(for example, `A[q,s.]`) marks a slice axis; it is not part of the variable's
identity or an index arithmetic operation. The output marks distinct bare
variables $j_1,\ldots,j_m$ as the operator's slice axes. Each occurs in
exactly one output slot and nowhere else in the output indices.
Their resolved domains are $\textcolor{#5688C7}{I}_1,\ldots,\textcolor{#5688C7}{I}_m$.
The statement guard must be independent of these marked variables.
This defines a rectangular slice over the full product of the marked
variables' domains for each valuation of the other contribution variables.

The enclosing operator $f$ must have the array signature

$$
f:K^{\textcolor{#5688C7}{I}_1\times\cdots\times \textcolor{#5688C7}{I}_m}\to
  K^{\textcolor{#5688C7}{I}_1\times\cdots\times \textcolor{#5688C7}{I}_m}
$$

with its own specified domain $\textcolor{#398B83}{\mathcal{D}}_f$.

Choose fresh variables $h_1,\ldots,h_m$ with those domains. The scalar
contribution body at the original output coordinates is

$$
\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}=
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
f\left(
\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{h_1\in \textcolor{#5688C7}{I}_1,\ldots,h_m\in \textcolor{#5688C7}{I}_m}
\left(B_{\textcolor{#9D75C4}{s}}[j_1:=h_1,\ldots,j_m:=h_m]\right)
\right),
(j_1,\ldots,j_m)
\right).
$$

The simultaneous substitution affects free occurrences only.
Marked variables remain contribution variables, not contracted variables.
The fresh tabulation binders supply the entire slice to the operator.

This applies an operator to one statement's body slice.
It does not first collect slices from other statements defining the
same destination. To apply softmax or another operator to a collected
tensor, use a separate named intermediate, as in [Section 11.3](#113-activation-before-versus-after-collection).

Nonrectangular slices, guards depending on marked slice variables, and other
operator shapes require explicit core expressions or an explicit surface-language
extension. They are not assigned an implicit meaning by this abbreviation.
A causal mask is such a guard; [Section 16.7](#167-a-causal-mask-is-not-a-marked-slice) gives its core forms.

### 15.5 Structural checks after elaboration

Derive $\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$ and $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}$ from the resulting statement and check the
rules in [Section 14](#14-structural-well-formedness). Elaboration preserves every source statement
occurrence. It neither merges identical statements by textual equality
nor orders them as destructive assignments.

Recognition of bounded scans, scheduling, and kernel fusion belong to
compilation rather than surface elaboration; they do not change contribution
syntax.

## 16. Worked core elaborations

### 16.1 Matrix multiplication and a bias

Take inputs $W$ of shape $(i_0,k_0)$ and $X$ of shape $(k_0,j_0)$,
and a defined tensor $Y$ of shape $(i_0,j_0)$:

```text
Y[i,j] = W[i,k] X[k,j]
```

Its core statement is

$$
\text{for }i\in[i_0],j\in[j_0]:
\quad
Y[i,j]\textcolor{#9D75C4}{\mathrel{+}=}
\bigoplus_{k\in[k_0]}W[i,k]\otimes X[k,j].
$$

For a separate vector-input bias example, retain $W$'s shape, take input
$X$ of shape $(k_0)$ and input $B$ of shape $(i_0)$, and define $Y$ on
shape $(i_0)$:

```text
Y[i] = W[i,k] X[k] + B[i]
```

the core is

$$
\text{for }i\in[i_0]:
\quad
Y[i]\textcolor{#9D75C4}{\mathrel{+}=}
\left(\bigoplus_{k\in[k_0]}W[i,k]\otimes X[k]\right)\oplus B[i].
$$

If $k_0=0$, the reduction is $0_K$ and the contribution is $B[i]$.
That distinguishes the intended rule from incorrectly placing the bias
inside the empty reduction.

### 16.2 Diagonal reads and writes

For input $\textcolor{#9D75C4}{M}$ of shape $(n,n)$ and a defined rank-zero `Trace`:

```text
Trace[] = M[i,i]
```

elaborates to the rank-zero contribution

$$
\text{for }():
\quad
\mathop{\mathrm{Trace}}\nolimits[]\textcolor{#9D75C4}{\mathrel{+}=}
\bigoplus_{i\in[n]}\textcolor{#9D75C4}{M}[i,i].
$$

The empty statement context has one valuation, the empty assignment,
identified with $()$ under the rank-zero convention of [Section 1.2](#12-tuples-products-and-rank-zero-cases).
The repeated RHS variable binds once and selects diagonal coordinates.

By contrast, with input $X$ of shape $(n)$ and a defined `Diagonal`
of shape $(n,n)$,

```text
Diagonal[i,i] = X[i]
```

has statement context $i\in[n]$ and write map
$\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(i)=(i,i)$. It contributes only to diagonal coordinates of a
declared shape $(n,n)$ tensor. Off-diagonal coordinates have empty
contribution collections.

### 16.3 Colliding writes and lost-binder prevention

The affine-write example from [Section 11.2](#112-colliding-affine-writes) elaborates to

$$
\text{for }i\in[2],j\in[2]:
\quad
Y[i+j]\textcolor{#9D75C4}{\mathrel{+}=}A[i]\otimes B[j].
$$

There is no body reduction. The two occurrences at output coordinate $1$
remain distinct members of $\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(Y,1)$, with scalar-coordinate
notation $1$ abbreviating tuple $(1)$.

In a separate numerical example, let $X$ be an input of shape $(3)$
and $Y$ a defined tensor of shape $(1)$. Then

```text
Y[i-i] = relu(X[i])    # i in [3]
```

retains three contribution occurrences at coordinate $0$.
Its intended collected value is

$$
Y[0]=\sum_{i\in[3]}\mathop{\mathrm{ReLU}}\nolimits(X[i]),
$$

not $\mathop{\mathrm{ReLU}}\nolimits(\sum_i X[i])$.
Simplifying $i-i$ must not change the statement's binding structure or
move its activation boundary.

### 16.4 A strided convolution and an in-bounds guard

Let inputs $X,W$ have shapes $(h,w)$ and $(a,b)$, and let $Y$ be a defined
tensor whose declared output domain is such that every $(i,j)$ in it satisfies

$$
i+a\le h,\qquad 2j+b\le w.
$$

For nonempty filter extents $a,b$, these conditions ensure the largest
read coordinates are in bounds. All indices range over finite ordinals,
so their lower bounds are nonnegative.

The surface statement

```text
Y[i,j] = W[p,r] X[i+p,2*j+r]
```

elaborates to

$$
\text{for }i,j:
\quad
Y[i,j]\textcolor{#9D75C4}{\mathrel{+}=}
\bigoplus_{p\in[a]}
\bigoplus_{r\in[b]}
W[p,r]\otimes X[i+p,2j+r],
$$

where the displayed $i,j$ binders abbreviate their declared domains.
Alternatively, with a larger declared output domain, those inequalities can
be the statement guard, leaving other output coordinates without contributions. That specifies a
guarded computation, not zero-padded convolution.

### 16.5 Softmax over an attention slice

Work over exact reals. Let inputs $\textcolor{#9D75C4}{Q},K_{\mathrm{key}}$ have shapes
$(q_0,d)$ and $(\textcolor{#5688C7}{s}_0,d)$, and let the defined tensor $A$ have shape
$(q_0,\textcolor{#5688C7}{s}_0)$. If $\textcolor{#5688C7}{s}_0=0$, the statement below has no
occurrences and nothing is evaluated:

```text
A[q,s.] = softmax(Q[q,k] Key[s,k])
```

`Key` denotes $K_{\mathrm{key}}$. The marked variable $\textcolor{#5688C7}{s}$ selects the
slice domain $[\textcolor{#5688C7}{s}_0]$. The core body for $q\in[q_0],\textcolor{#5688C7}{s}\in[\textcolor{#5688C7}{s}_0]$ is

$$
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
\mathop{\mathrm{softmax}}\nolimits\left(
\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{t\in[\textcolor{#5688C7}{s}_0]}
\left(\sum_{k\in[d]}\textcolor{#9D75C4}{Q}[q,k]K_{\mathrm{key}}[t,k]\right)
\right),(\textcolor{#5688C7}{s})
\right).
$$

The feature index $k$ is contracted; the key-position index is tabulated
for softmax and then selected at $\textcolor{#5688C7}{s}$. It is not contracted into a scalar.
The full statement contributes that body to $A[q,\textcolor{#5688C7}{s}]$.

### 16.6 A scan history with explicit slice input

Use the shapes and bounds of [Section 11.4](#114-a-finite-history-with-persistent-input). The recurrence statement
elaborates to

$$
\text{for }i\in[d],l\in[N]:
\quad
H[i,l+1]\textcolor{#9D75C4}{\mathrel{+}=}
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
F\left(\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[d]}(H[j,l])\right),(i)
\right).
$$

The read time $l$ and write time $l+1$ are both within $[N+1]$.
$l$ is a free contribution variable, not a contracted index.
The tabulated $j$ is fresh and represents all coordinates required by $F$.

For $N=0$, this statement has no occurrences, while the base statements
still apply at time zero. For $N>0$, its apparent self-reference by tensor
name does not prevent the coordinate-level dependency analysis in [Section 23](#23-read-footprints-and-executable-dependencies) from
recognizing a forward scan.

### 16.7 A causal mask is not a marked slice

Keep the inputs and shapes of [Section 16.5](#165-softmax-over-an-attention-slice), but normalize over only the keys
$t\le q$ for each query $q$. The marked-slice abbreviation of [Section 15.4](#154-marked-slice-operators) does
not apply: the mask $\textcolor{#5688C7}{s}\le q$ is a guard that depends on the marked variable
$\textcolor{#5688C7}{s}$. A mask inside the argument of $\mathop{\mathrm{softmax}}\nolimits$ does not work either.
That argument is a complete array on $[\textcolor{#5688C7}{s}_0]$, and multiplying an
entry by $\mathbf{1}_{t\le q}$ turns it into $0$. Then $\exp(0)=1$, so the key
is still normalized over, and exact reals have no $-\infty$ to use instead.

The core expresses the mask with scalar primitives. Register $\exp$, which is
total on $\mathbb{R}$, and division, defined where the divisor is nonzero
([Section 8](#8-operators-predicates-and-definedness)). Abbreviate the explicit reduction
$S(q,t)=\bigoplus_{k\in[d]}\textcolor{#9D75C4}{Q}[q,k]\otimes K_{\mathrm{key}}[t,k]$. For
$q\in[q_0]$ and $\textcolor{#5688C7}{s}\in[\textcolor{#5688C7}{s}_0]$, one statement suffices:

$$
A[q,\textcolor{#5688C7}{s}]\textcolor{#9D75C4}{\mathrel{+}=}
\mathop{\mathrm{div}}\nolimits\left(
\mathbf{1}_{\textcolor{#5688C7}{s}\le q}\otimes\exp(S(q,\textcolor{#5688C7}{s})),\;
\bigoplus_{t\in[\textcolor{#5688C7}{s}_0]}\mathbf{1}_{t\le q}\otimes\exp(S(q,t))
\right).
$$

Every read is in bounds for every lifted valuation. Because $\exp$ is total,
multiplying by the Iverson value is safe here, unlike the logarithm of
[Section 21.3](#213-a-guard-differs-from-a-zero-multiplier): the masked bodies are defined and contribute $0$. For
$\textcolor{#5688C7}{s}_0>0$ the denominator is at least $\exp(S(q,0))>0$, because $0\le q$ always holds,
so every division is defined and $A[q,\textcolor{#5688C7}{s}]=0$ for $\textcolor{#5688C7}{s}>q$. For
$\textcolor{#5688C7}{s}_0=0$ there are no occurrences.

An equivalent form uses guards, so masked bodies are never evaluated. Let $\mathit{Den}$ be
a defined tensor of shape $(q_0)$:

$$
\begin{aligned}
&\text{for }q\in[q_0],t\in[\textcolor{#5688C7}{s}_0]\text{ where }t\le q:
&&\mathit{Den}[q]\textcolor{#9D75C4}{\mathrel{+}=}\exp(S(q,t)),\\
&\text{for }q\in[q_0],\textcolor{#5688C7}{s}\in[\textcolor{#5688C7}{s}_0]\text{ where }\textcolor{#5688C7}{s}\le q:
&&A[q,\textcolor{#5688C7}{s}]\textcolor{#9D75C4}{\mathrel{+}=}\mathop{\mathrm{div}}\nolimits(\exp(S(q,\textcolor{#5688C7}{s})),\mathit{Den}[q]).
\end{aligned}
$$

Entries with $\textcolor{#5688C7}{s}>q$ have empty fibers and are $0$. $\mathit{Den}[q]$ is read as a
named tensor, so its whole fiber is collected before any division is ready
([Section 25.2](#252-publish-a-completed-coordinate)).

The two forms differ on fully masked rows. Replace $t\le q$ by the strict mask
$t<q$, and assume $q_0>0$ and $\textcolor{#5688C7}{s}_0>0$. Row $q=0$ then has no unmasked key.
In the first form the denominator at $q=0$ is a sum of $\textcolor{#5688C7}{s}_0$ masked zeros,
equal to $0_K$, so the division is undefined at an actual occurrence and the
program has no model (the machine ends in
$\textcolor{#A87C28}{\mathsf{Failed}}$). In the guarded form row $0$ has no
occurrence of $A$, so $A[0,\textcolor{#5688C7}{s}]=0$ is defined. This is the guard-versus-multiplier
distinction of [Section 21.3](#213-a-guard-differs-from-a-zero-multiplier) again.

## 17. Pure einsum semantics and transformation foundations

This section fixes the mathematical reference meaning of the standard
pure-einsum profile from [Section 15.1](#151-explicit-inputs-to-elaboration). It does not extend the core with
a new primitive and does not define whole-program semantics.

The reference operands are complete tensor values from an environment
$\textcolor{#398B83}{\rho}$. There are no nonlinear operators, guards, or affine access
maps in this profile. The general core retains those capabilities.

Sections [17.1](#171-index-strings-and-global-valuations)-[17.3](#173-connection-to-the-contribution-core) need only the commutative-monoid laws of $\oplus$, the
coherence condition, and the bracketing convention of [Section 2.3](#23-which-algebraic-laws-each-part-uses). Sections [17.4](#174-delta-tensors-and-diagonal-identities)-[17.6](#176-neutral-operands-and-domain-preservation) use the full
semiring laws.

### 17.1 Index strings and global valuations

An **index string** $\textcolor{#5688C7}{L}=(j_1,\ldots,j_k)$ is an ordered tuple of index
variable identities. Unlike a context, an index string can repeat an
identity. It specifies which variable supplies each coordinate slot.

For operands $T_1,\ldots,T_m$, with $m\ge1$, let $\textcolor{#5688C7}{L}_r$ be the string
for operand $T_r$ and let $\textcolor{#5688C7}{L}$ be the output string.
Empty strings represent scalar operands or a scalar result.
The standard profile requires:

1. $\textcolor{#5688C7}{L}_r$ has the same length as the rank of $T_r$.
2. Each index variable's domain equals the domain of every slot it labels.
3. Every variable in $\textcolor{#5688C7}{L}$ occurs in at least one operand string.
4. If the result is assigned to a declared destination $T_{\textcolor{#9D75C4}{s}}$, its rank
   and ordered slot domains match $\textcolor{#5688C7}{L}$ exactly.

Let $\textcolor{#5688C7}{\Gamma}_{\mathrm{all}}$ contain every distinct variable in the
operand strings, once, with its resolved domain. This is a context
in the sense of [Section 3](#3-axes-index-variables-and-valuations), not a concatenation retaining duplicates.
Its valuations are the paper's global index assignments, expressed
using our existing $\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}$ notation.

For a string $\textcolor{#5688C7}{L}=(j_1,\ldots,j_k)$, define

$$
\textcolor{#5688C7}{J}_{\textcolor{#5688C7}{L}}=\textcolor{#5688C7}{I}_{j_1}\times\cdots\times \textcolor{#5688C7}{I}_{j_k},
\qquad
\textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}}(\textcolor{#5688C7}{\nu})=(\textcolor{#5688C7}{\nu}(j_1),\ldots,\textcolor{#5688C7}{\nu}(j_k)).
$$

Thus $\textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}}:\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\mathrm{all}})\to \textcolor{#5688C7}{J}_{\textcolor{#5688C7}{L}}$ is a
coordinate projection. Equal-domain compatibility ensures that
$\textcolor{#5688C7}{J}_{\textcolor{#5688C7}{L}_r}=\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T_r)$ for each operand.
The destination condition similarly gives
$\textcolor{#5688C7}{J}_{\textcolor{#5688C7}{L}}=\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T_{\textcolor{#9D75C4}{s}})$. A larger declared destination
would instead describe a core computation with additional empty fibers,
not this standard pure-einsum profile.

For the empty string, $\textcolor{#5688C7}{J}_{()}=\{()\}$ and $\textcolor{#5688C7}{\pi}_{()}(\textcolor{#5688C7}{\nu})=()$.
For $\textcolor{#5688C7}{L}=(i,i)$, $\textcolor{#5688C7}{J}_{\textcolor{#5688C7}{L}}=\textcolor{#5688C7}{I}_i\times \textcolor{#5688C7}{I}_i$ but the projection reaches only
the diagonal. A coordinate projection need not be surjective.

**Example.** For matrix multiplication, the strings are
$\textcolor{#5688C7}{L}_1=(i,k)$, $\textcolor{#5688C7}{L}_2=(k,j)$, and $\textcolor{#5688C7}{L}=(i,j)$.
A global valuation of $i,k,j$ simultaneously identifies the entries
of both operands and the result coordinate.

### 17.2 Canonical fiber semantics

The result of this pure einsum is the tensor value $\textcolor{#398B83}{V}_{\textcolor{#5688C7}{L}}:\textcolor{#5688C7}{J}_{\textcolor{#5688C7}{L}}\to K$
defined by

$$
\textcolor{#398B83}{V}_{\textcolor{#5688C7}{L}}[p]
=
\bigoplus_{\substack{
 \textcolor{#5688C7}{\nu}\in\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\mathrm{all}})\\
 \textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}}(\textcolor{#5688C7}{\nu})=p
}}
\;\bigotimes_{r=1}^{m}
\textcolor{#398B83}{\rho}(T_r)[\textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}_r}(\textcolor{#5688C7}{\nu})].
$$

For each output coordinate, this combines all global assignments in
its projection fiber. Each assignment multiplies the corresponding
operand values. Equal-valued products remain distinct occurrences.

This definition directly handles:

- Contraction: assignments vary over variables not retained in $\textcolor{#5688C7}{L}$.
- Repeated input variables: the same value supplies several operand slots.
- Repeated output variables: off-diagonal projection fibers can be empty.
- Scalars: the empty string selects the sole rank-zero coordinate.
- Empty contracted domains: there are no global assignments, so a
  nonempty output domain receives $0_K$.

**Example: ordinary contraction.**

$$
\textcolor{#398B83}{V}_{(i,j)}[i,j]
=\bigoplus_{k\in \textcolor{#5688C7}{I}_k}
\textcolor{#398B83}{\rho}(W)[i,k]\otimes\textcolor{#398B83}{\rho}(X)[k,j].
$$

**Example: diagonal construction.** For the single operand $v$ with
input string $(i)$ and output string $(i,i)$,

$$
\textcolor{#398B83}{V}_{(i,i)}[p,q]
=
\begin{cases}
\textcolor{#398B83}{\rho}(v)[p],&p=q,\\
0_K,&p\ne q.
\end{cases}
$$

The full output domain remains $\textcolor{#5688C7}{I}_i\times \textcolor{#5688C7}{I}_i$, not a diagonal-only
coordinate set.

**Example: scalar-only operands.** If every string is empty, then
$\textcolor{#5688C7}{\Gamma}_{\mathrm{all}}$ is empty and has one valuation.
The result is the product of the scalar operands, not an empty sum.

### 17.3 Connection to the contribution core

Partition the global variables into:

- The distinct output variables, forming the statement context
  $\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}}$.
- The remaining variables, contracted in the body.

Use guard $\mathrm{true}$, an output map $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}$ given by the same
tuple projection on $\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma}_{\textcolor{#9D75C4}{s}})$, and body

$$
\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}=
\bigoplus_{\text{remaining variables}}
\;\bigotimes_{r=1}^{m}T_r[\textcolor{#5688C7}{L}_r].
$$

$T_r[\textcolor{#5688C7}{L}_r]$ abbreviates a read with the variables in $\textcolor{#5688C7}{L}_r$ in slot order.
The displayed reduction abbreviates nested core reductions, one binder
per remaining variable. When none remain, the body is just the product.

For this single statement, collecting body values over
$\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T_{\textcolor{#9D75C4}{s}},p)$ is intended to reproduce the canonical formula.
The required correspondence proof separates each global valuation into
its output-variable valuation and its contracted-variable valuation,
then combines the finite sums. Empty domains and repeated output
indices must be included in the proof.

[Section 19.3](#193-correspondence-with-pure-einsum) states this correspondence using the core interpretation.
It is proved in Lean for the bounded source fragment (Proposition 19.1);
beyond that fragment it remains a proof obligation.

The formula cannot be extended to nonlinear bodies by moving an
operator inside the products or sums. For example,

$$
\mathop{\mathrm{ReLU}}\nolimits\left(\sum_k W[i,k]X[k]\right)
$$

is not generally the sum of $\mathop{\mathrm{ReLU}}\nolimits(W[i,k]X[k])$.
The operator boundary fixed in Sections [13](#13-core-syntax-and-binding) and [15](#15-surface-to-core-elaboration) remains authoritative.

### 17.4 Delta tensors and diagonal identities

For a finite coordinate domain $\textcolor{#5688C7}{J}$, define the **delta tensor**

$$
\textcolor{#398B83}{\delta}_{\textcolor{#5688C7}{J}}:\textcolor{#5688C7}{J}\times \textcolor{#5688C7}{J}\to K,
\qquad
\textcolor{#398B83}{\delta}_{\textcolor{#5688C7}{J}}[p,q]=
\begin{cases}
1_K,&p=q,\\
0_K,&p\ne q.
\end{cases}
$$

If $\textcolor{#5688C7}{J}$ is a product of $k$ slot domains, this can be represented as
a rank-$2k$ named tensor with the two copies of those slots in order.
For the scalar coordinate domain $\textcolor{#5688C7}{J}=\{()\}$, it is the scalar $1_K$.

Delta is an equality indicator, already expressible by the core
Iverson constructor. For product coordinates, $p=q$ abbreviates conjunction
of the corresponding slot equalities. It needs no additional primitive operation.
For $p\in \textcolor{#5688C7}{J}$ and a complete value $\textcolor{#398B83}{V}:\textcolor{#5688C7}{J}\to K$, finite combination gives

$$
\bigoplus_{q\in \textcolor{#5688C7}{J}}\textcolor{#398B83}{\delta}_{\textcolor{#5688C7}{J}}[p,q]\otimes \textcolor{#398B83}{V}[q]=\textcolor{#398B83}{V}[p].
$$

Exactly one summand selects $p$ and the rest are $0_K$.
For empty $\textcolor{#5688C7}{J}$, this pointwise statement has no $p$ to quantify over.

For a vector $v:\textcolor{#5688C7}{I}\to K$, diagonal construction is

$$
\textcolor{#398B83}{D}[p,q]=\textcolor{#398B83}{\delta}_{\textcolor{#5688C7}{I}}[p,q]\otimes v[p].
$$

For matrices with compatible domains,

$$
\bigoplus_{k\in \textcolor{#5688C7}{I}}A[i,k]\otimes \textcolor{#398B83}{D}[k,j]
=A[i,j]\otimes v[j].
$$

This explains how a nested contraction with a diagonal intermediate
can be replaced by a direct pointwise scaling. It uses an equality
constraint, not merely renaming a bound variable.

**Identity caveat.** With repeated input and output string $(i,i)$,
a single-operand einsum keeps diagonal entries and zeros the rest:

$$
\textcolor{#398B83}{V}_{(i,i)}[p,q]
=
\begin{cases}
\textcolor{#398B83}{\rho}(\textcolor{#9D75C4}{M})[p,p],&p=q,\\
0_K,&p\ne q.
\end{cases}
$$

It is not the identity on arbitrary matrices. The ordinary
single-operand identity law uses a string of distinct indices, so
every coordinate is reached exactly once.

### 17.5 Conditions for semantic transformations

The following transformations are useful foundations for
compiler proofs. Their validity is about the canonical pure-einsum
values, not about arbitrary primitive operators or floating-point
executions.

**Operand permutation.** Permuting operands preserves a contraction
only when their index strings are permuted with them.
This follows from commutativity of $\otimes$.
It does not assert that matrix multiplication satisfies $AB=BA$:
changing which tensor occupies a given index string changes its reads.

**Distribution over pointwise combination.** For complete tensor values
$\textcolor{#398B83}{U},\textcolor{#398B83}{V}$ with the same coordinate domain, define

$$
(\textcolor{#398B83}{U}\oplus \textcolor{#398B83}{V})[p]=\textcolor{#398B83}{U}[p]\oplus \textcolor{#398B83}{V}[p].
$$

A pure einsum distributes over replacement of one operand by this
pointwise combination, retaining that operand's index string.
The scalar distributive law and finite combination justify the result.
The core can express pointwise combination using tabulation, as
specified in [Section 13.3](#133-expression-constructors).

**Nesting and denesting.** An intermediate contraction may aggregate
only indices that are no longer needed by the outer contraction.
Its output interface must retain the necessary shared and final-output
indices. Inner and outer index variables must be renamed apart except
where an interface explicitly identifies them.

For example,

$$
\textcolor{#9D75C4}{s}=\sum_i a[i]b[i]c[i]
$$

can use $u[i]=a[i]b[i]$ followed by $\textcolor{#9D75C4}{s}=\sum_i u[i]c[i]$.
Replacing $u$ by the scalar $\sum_i a[i]b[i]$ loses the correlation
with $c[i]$ and is generally incorrect.

Likewise,

$$
\left(\sum_i a[i]\right)\left(\sum_i b[i]\right)
=\sum_i\sum_j a[i]b[j],
$$

not $\sum_i a[i]b[i]$. Equal printed binder names in separate reductions
do not identify their variables.

For the restricted rule described in the reference paper, the inner
output string and its outer operand string agree, and inner and outer
variable sets intersect only in variables carried by that interface.
That condition permits matching valuations to be combined into one
global valuation.

**Renaming versus identification.** A capture-avoiding renaming changes
variable identifiers bijectively and preserves their declared domains.
Identifying two different variables constrains their values to agree;
it is not generally semantics-preserving without justification.
Delta factors and repeated interface indices can supply that justification.

The reference paper's general denesting construction uses an index-symbol
graph to derive the identifications forced by an interface. An
implementation may use such a graph or an equivalent representation,
but must preserve those constraints and compatible domains.
This specification does not prescribe that algorithm.

### 17.6 Neutral operands and domain preservation

Define an all-ones tensor $\mathbf{1}_{\textcolor{#5688C7}{J}}:\textcolor{#5688C7}{J}\to K$ by
$\mathbf{1}_{\textcolor{#5688C7}{J}}[p]=1_K$.
Multiplying a summand by an all-ones operand does not change its value.
Removing that operand is a different claim: it must not remove a
variable domain, introduce or remove reductions, or change output shape.

**Counterexample.** Over the reals,

$$
\sum_{j\in[m]}X[i]\cdot\mathbf{1}_{[m]}[j]=m\,X[i].
$$

Removing both the operand and the $j$ binder gives $X[i]$, which is
generally different, including when $m=0$.
If a domain-carrying operand is eliminated, its binder and domain must
remain explicit unless a separate valid rule removes them.

Similarly, all-ones values can be introduced to represent a constant
array or retain index information, but this does not create that domain
from nothing. Domains remain supplied by signatures and binders.

This is particularly important for differentiation. Over exact reals,
with $W$ of shape $(d,e)$ and $x$ of shape $(e)$,

$$
F[i]=\sum_{j\in[e]}W[i,j]x[j]
$$

has the coordinate derivative

$$
\frac{\partial F[i]}{\partial W[a,b]}
=\textcolor{#398B83}{\delta}_{[d]}[i,a]x[b].
$$

The derivative has coordinate domain $[d]\times[d]\times[e]$ for
$(i,a,b)$, even though $W$ no longer appears as an operand in its value
expression. Those domains must survive any transformation.

Our explicit signatures and binders can preserve this information
without the reference paper's all-ones-operand workaround.
Rewrite and differentiation judgments must specify both their
result values and their result coordinate domains.
No differentiability claim is made here for arbitrary primitives such
as ReLU or for arbitrary semirings.

## Part III: Denotational semantics

Denotational semantics describes values and equations without prescribing
how a machine computes them. In this part, $\textcolor{#398B83}{\rho}$ is always a complete,
signature-respecting environment as defined in [Section 5](#5-environments-and-stores). It supplies
candidate values even for tensors that the program defines.

Reading $\textcolor{#398B83}{\rho}(T)$ does not recursively execute statements defining $T$.
Instead, expression interpretation uses those candidate values, and
the program equations determine whether the environment is a model.
This distinction allows the same definitions to describe both acyclic
programs and cyclic equation systems.

## 18. Expression interpretation and definedness

### 18.1 Successful and undefined results

For an expression value type $\textcolor{#5688C7}{\tau}$ from [Section 13.2](#132-value-types-and-primitive-signatures), define the result
space

$$
\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau})=\textcolor{#5688C7}{\tau}\sqcup\{\textcolor{#398B83}{\bot}\}.
$$

This is a tagged disjoint union. A member of $\textcolor{#5688C7}{\tau}$ is a successful
value; $\textcolor{#398B83}{\bot}$ denotes an undefined result. We write $v$ for the
successful tag carrying value $v$.

The symbol $\textcolor{#398B83}{\bot}$ is not a scalar zero, a missing-store entry, a
floating-point NaN, or a selected solution of an equation. No order
or least-fixed-point interpretation is attached to it.

For a structurally well-formed expression
$\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma};\textcolor{#5688C7}{D}\vdash \textcolor{#9D75C4}{E}:\textcolor{#5688C7}{\tau}$, a complete environment $\textcolor{#398B83}{\rho}$, and
$\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}$, define

$$
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}\in\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau}).
$$

Index expressions and predicates have the total interpretations already
introduced: integer arithmetic for $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{e}\rrbracket_{\textcolor{#5688C7}{\nu}}$ and
Boolean operations for $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{Q}\rrbracket_{\textcolor{#5688C7}{\nu}}$.
The result space is needed for value-dependent primitive applications,
not to excuse malformed tensor accesses.

Use the notation

$$
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}\downarrow v
$$

to mean that the result is the successful value $v$, and

$$
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}=\textcolor{#398B83}{\bot}
$$

to mean that it is undefined. The downward arrow on an expression
means definedness, not operational termination.
The separate $\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\Downarrow}\textcolor{#398B83}{\rho}$ notation denotes successful
machine execution in [Part IV](#part-iv-operational-semantics).

### 18.2 Scalar constructors

Scalar literals, named tensor reads, and Iverson values are interpreted by

$$
\textcolor{#398B83}{\llbracket} c_K\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}=c_K,
$$

$$
\textcolor{#398B83}{\llbracket} T[\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_k]\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\textcolor{#398B83}{\rho}(T)[
 \textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{e}_1\rrbracket_{\textcolor{#5688C7}{\nu}},\ldots,
 \textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{e}_k\rrbracket_{\textcolor{#5688C7}{\nu}}],
$$

$$
\textcolor{#398B83}{\llbracket}\mathbf{1}_{\textcolor{#9D75C4}{Q}}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\begin{cases}
1_K,&\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{Q}\rrbracket_{\textcolor{#5688C7}{\nu}}=\mathrm{true},\\
0_K,&\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{Q}\rrbracket_{\textcolor{#5688C7}{\nu}}=\mathrm{false}.
\end{cases}
$$

The read is valid by the structural premises and $\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}$.
For a scalar tensor, its index tuple is empty.

For $\star\in\{\oplus,\otimes\}$, define the strict lifting

$$
\textcolor{#398B83}{\mathop{\mathrm{lift}}\nolimits}_2(\star,u,v)
=
\begin{cases}
u\star v,&u,v\text{ are successful scalar values},\\
\textcolor{#398B83}{\bot},&\text{otherwise}.
\end{cases}
$$

Then

$$
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_1\star \textcolor{#9D75C4}{E}_2\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\textcolor{#398B83}{\mathop{\mathrm{lift}}\nolimits}_2\left(
 \star,\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_1\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}},
 \textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_2\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
\right).
$$

Both operands must be defined, even when one is $0_K$.
This lifting is not an assertion that
$\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(K)$ itself forms the scalar semiring.
For instance, multiplying a successful zero by $\textcolor{#398B83}{\bot}$ gives $\textcolor{#398B83}{\bot}$,
not a successful zero.

### 18.3 Reduction and tabulation

For a reduction, let
$v_k=\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}[j\mapsto k]}$ for each
$k\in \textcolor{#5688C7}{I}_j$. Define

$$
\textcolor{#398B83}{\llbracket}\bigoplus_{j\in \textcolor{#5688C7}{I}_j}\textcolor{#9D75C4}{E}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\begin{cases}
\displaystyle\bigoplus_{k\in \textcolor{#5688C7}{I}_j}v_k,
 &\text{every }v_k\text{ is successful},\\
\textcolor{#398B83}{\bot},&\text{otherwise}.
\end{cases}
$$

Here $\bigoplus_{k\in\textcolor{#5688C7}{I}_j}v_k$ is the fold of $\oplus$ over the ascending enumeration of
$\textcolor{#5688C7}{I}_j$, which needs no law; it equals the finite combination of
[Section 2.2](#22-finite-sums-and-products) under the monoid laws ([Section 2.3](#23-which-algebraic-laws-each-part-uses)).
An empty reduction succeeds with $0_K$. Its body is not interpreted
at any valuation, so an unreachable primitive application does not
cause undefinedness.

For tabulation, let $\textcolor{#5688C7}{J}=\textcolor{#5688C7}{I}_1\times\cdots\times \textcolor{#5688C7}{I}_m$ and define the extended
valuation for $p=(p_1,\ldots,p_m)\in \textcolor{#5688C7}{J}$ by

$$
\textcolor{#5688C7}{\nu}_p=\textcolor{#5688C7}{\nu}[j_1\mapsto p_1,\ldots,j_m\mapsto p_m].
$$

The tabulation result is

$$
\textcolor{#398B83}{\llbracket}
\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j_1\in \textcolor{#5688C7}{I}_1,\ldots,j_m\in \textcolor{#5688C7}{I}_m}(\textcolor{#9D75C4}{E})
\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\begin{cases}
\textcolor{#398B83}{V},&
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}_p}\downarrow \textcolor{#398B83}{V}[p]
\text{ for every }p\in \textcolor{#5688C7}{J},\\
\textcolor{#398B83}{\bot},&\text{some body result is undefined}.
\end{cases}
$$

Here $\textcolor{#398B83}{V}:\textcolor{#5688C7}{J}\to K$ is a complete array value.
An empty $\textcolor{#5688C7}{J}$ produces the unique empty array successfully.
These binders use exactly the lifted domains from [Section 14.1](#141-judgments-and-admissible-valuations).

### 18.4 Array selection and primitive application

For array selection, let
$p=(\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{e}_1\rrbracket_{\textcolor{#5688C7}{\nu}},\ldots,\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{e}_m\rrbracket_{\textcolor{#5688C7}{\nu}})$.
Then

$$
\textcolor{#398B83}{\llbracket}\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}(\textcolor{#9D75C4}{E},(\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_m))\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\begin{cases}
\textcolor{#398B83}{V}[p],&\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}\downarrow \textcolor{#398B83}{V},\\
\textcolor{#398B83}{\bot},&\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}=\textcolor{#398B83}{\bot}.
\end{cases}
$$

The structural rule guarantees that $p$ belongs to the array domain.
Selection requires the array expression to denote a complete value.
It does not bypass an undefined element of a tabulation by selecting
a different coordinate.

For a primitive $f$ with arity $q$, interpret its operands and let
$u_r=\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_r\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}$. Define

$$
\textcolor{#398B83}{\llbracket} f(\textcolor{#9D75C4}{E}_1,\ldots,\textcolor{#9D75C4}{E}_q)\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\begin{cases}
f(u_1,\ldots,u_q),
 &\text{all }u_r\text{ are successful and }
 (u_1,\ldots,u_q)\in\textcolor{#398B83}{\mathcal{D}}_f,\\
\textcolor{#398B83}{\bot},&\text{otherwise}.
\end{cases}
$$

The primitive's signature guarantees the successful result has its
declared type. Its domain $\textcolor{#398B83}{\mathcal{D}}_f$ determines definedness;
typing alone does not.
For a nullary primitive, its argument tuple is $()$ and the same
domain-membership rule applies.

### 18.5 Definedness examples and transformation limits

Work over exact reals. The following results illustrate strictness:

$$
\textcolor{#398B83}{\llbracket}\log(-1)\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}=\textcolor{#398B83}{\bot},
\qquad
\textcolor{#398B83}{\llbracket} 0\cdot\log(-1)\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}=\textcolor{#398B83}{\bot},
$$

$$
\textcolor{#398B83}{\llbracket}\bigoplus_{j\in[0]}\log(-1)\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}=0.
$$

The empty reduction has no body instances. Multiplication by zero,
by contrast, still has an undefined operand.

If $X$ has shape $(2)$ with $\textcolor{#398B83}{\rho}(X)[0]=4$ and $\textcolor{#398B83}{\rho}(X)[1]=-1$, then

$$
\textcolor{#398B83}{\llbracket}
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
 \textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[2]}(\log(X[j])),(0)
\right)
\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=\textcolor{#398B83}{\bot}.
$$

The selected coordinate would be positive before taking its logarithm,
but the array construction includes the invalid logarithm at coordinate
$1$. This is a deliberate complete-array interpretation, not lazy
coordinate selection.

Therefore, transformations involving partial primitives must preserve
both values and definedness. Replacing $0\cdot \textcolor{#9D75C4}{E}$ by $0$ is unsound when
$\textcolor{#9D75C4}{E}$ can be undefined. The pure semiring transformations of [Section 17](#17-pure-einsum-semantics-and-transformation-foundations)
do not have this problem: their structurally valid reads and semiring
operations are total on complete environments.

## 19. Contribution collection

The Lean status of Sections [19](#19-contribution-collection)–[20](#20-program-models-and-functional-denotation) is recorded in
[Proof status and numbered results](#proof-status-and-numbered-results).
[Section 19.3](#193-correspondence-with-pure-einsum)'s pure-einsum elaboration correspondence (Proposition 19.1)
is proved in Lean for the bounded source fragment only (see the status table).

### 19.1 Environments with defined contributions

For a structurally well-formed program $\textcolor{#9D75C4}{P}$, define

$$
\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})
=
\left\{
\textcolor{#398B83}{\rho}\ \middle|\
\begin{array}{l}
\textcolor{#398B83}{\rho}\text{ is a complete, signature-respecting environment, and}\\
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}\ne\textcolor{#398B83}{\bot}
\text{ for every }(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\in\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}
\end{array}
\right\}.
$$

Membership says all actual contribution bodies are defined. It does
not yet say the environment satisfies the program's equations.

Guards affect $\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}$ through $\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$, before interpreting bodies.
A valuation excluded by a guard imposes no body-definedness obligation.
Likewise, a statement with an empty occurrence domain imposes none.
In contrast, a present zero-valued contribution must still be defined.

### 19.2 Statement contributions and collected tensors

For $\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$, define the contribution tensor
of one statement:

$$
\textcolor{#398B83}{V}_{\textcolor{#9D75C4}{s}}^{\textcolor{#398B83}{\rho}}[p]
=
\bigoplus_{\substack{\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}\\\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu})=p}}
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}},
\qquad p\in\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T_{\textcolor{#9D75C4}{s}}).
$$

Each term here is a successful scalar value; $\textcolor{#398B83}{\bot}$ is never treated
as a summand.
An empty fiber gives $0_K$.

For every defined tensor $T$, define its collected value:

$$
\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[p]
=
\bigoplus_{(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\in\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T,p)}
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}.
$$

Equivalently, partitioning the occurrences by statement gives

$$
\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[p]
=
\bigoplus_{\substack{\textcolor{#9D75C4}{s}\in \textcolor{#9D75C4}{P}\\T_{\textcolor{#9D75C4}{s}}=T}}\textcolor{#398B83}{V}_{\textcolor{#9D75C4}{s}}^{\textcolor{#398B83}{\rho}}[p].
$$

The collection is indexed by statement occurrences, so duplicate
statements remain duplicate summands. In the Boolean interpretation,
the same definitions combine contributions by OR.

The prior candidate value $\textcolor{#398B83}{\rho}(T)[p]$ is not an additional summand.
It influences a contribution only if that contribution explicitly
reads it. This is equation construction, not a cumulative update of
an existing mutable tensor.

A defined tensor with no targeting statements has the zero tensor as
its collected value. No analogous default supplies an omitted input:
the input environment must provide every designated input value.

### 19.3 Correspondence with pure einsum

**Proposition 19.1 (pure-einsum correspondence).**
For the normalized pure-einsum statement of [Section 17.3](#173-connection-to-the-contribution-core),
the intended local correspondence is

$$
\textcolor{#398B83}{V}_{\textcolor{#9D75C4}{s}}^{\textcolor{#398B83}{\rho}}[p]=\textcolor{#398B83}{V}_{\textcolor{#5688C7}{L}}[p]
$$

for every output coordinate, with $\textcolor{#398B83}{V}_{\textcolor{#5688C7}{L}}$ computed from the same operand
values in $\textcolor{#398B83}{\rho}$ by [Section 17.2](#172-canonical-fiber-semantics).
This statement applies whenever the contribution tensor is defined;
the pure statement itself has no partial primitive applications.

The mathematical proof decomposes a global valuation into the values
of distinct output variables and the remaining contracted variables.
The core body combines over the latter, while the write fiber combines
over the former. This uses only the commutative-monoid laws of
$\oplus$, coherence, and the bracketing convention ([Section 2.3](#23-which-algebraic-laws-each-part-uses)), not
distributivity. The resulting finite
combinations enumerate exactly the assignments in $\textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}}^{-1}(\{p\})$.

Repeated output indices can leave an empty fiber, and an empty
contracted domain can leave an empty reduction. Both sides then use
the same $0_K$ convention. With no variables, the single empty
valuation yields the scalar operand product.

The proof description here is a paper argument. A Lean proof exists for the
bounded source fragment (see the status table); it covers repeated slots, empty
contractions, zero extents, factor order, and multiplicity.

### 19.4 Source order and nonlinear boundaries

**Proposition 19.2 (source-order invariance).**
Permuting source statements while preserving their bodies, binders,
guards, and distinct occurrence identities leaves
$\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$ and collected values unchanged, up to the
corresponding relabeling of occurrences.
Finite commutative combination justifies this property.
Deleting a duplicate statement does not generally preserve it.

Collection does not move primitive operators across sums.
Two contributions $f(A[i])$ and $f(B[i])$ give

$$
f(\textcolor{#398B83}{\rho}(A)[i])\oplus f(\textcolor{#398B83}{\rho}(B)[i]),
$$

provided both applications are defined.
An intermediate defined by contributions $A[i]$ and $B[i]$, followed
by a read through $f$, is related by the program equations to

$$
f(\textcolor{#398B83}{\rho}(A)[i]\oplus\textcolor{#398B83}{\rho}(B)[i]).
$$

These are equal only under an appropriate property of $f$ on the
relevant values. The semantics assumes no such property.

## 20. Program models and functional denotation

### 20.1 Models on supplied inputs

An input environment $\textcolor{#398B83}{\eta}$ is well-typed when it supplies a value
with the prescribed coordinate domain and carrier for every identifier
in $\textcolor{#5688C7}{\mathrm{In}}$, and its identifier domain is exactly $\textcolor{#5688C7}{\mathrm{In}}$.

For such an $\textcolor{#398B83}{\eta}$, define

$$
\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})
=
\left\{
\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})\ \middle|\
\begin{array}{l}
\textcolor{#398B83}{\rho}|_{\textcolor{#5688C7}{\mathrm{In}}}=\textcolor{#398B83}{\eta},\ \text{and}\\
\textcolor{#398B83}{\rho}(T)[p]=\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[p]\\
\text{for every }T\in\textcolor{#5688C7}{\mathrm{Def}}
\text{ and }p\in\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)
\end{array}
\right\}.
$$

All defined tensors participate in these equations, not just
designated outputs. Zero defaults follow from empty contribution
collections, rather than from an extra initialization equation.

Thus the unconditional denotational meaning of a structurally
well-formed program is its model relation: it associates each
well-typed input environment with its set of models.
That set can be empty, a singleton, or contain several environments.

### 20.2 A partial equation operator

The same definition can be expressed using the partial map

$$
\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}:\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})\to
\{\text{complete, signature-respecting environments}\},
$$

given by

$$
\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)=
\begin{cases}
\textcolor{#398B83}{\rho}(T),&T\in\textcolor{#5688C7}{\mathrm{In}},\\
\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T),&T\in\textcolor{#5688C7}{\mathrm{Def}}.
\end{cases}
$$

It is partial relative to the space of all complete environments,
because its domain is $\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$.
Its result need not itself belong to $\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$.
For example, for the scalar statement `T[] = log(T[])`, a candidate
value $T=1$ makes the contribution defined, but $\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}$ produces
$T=0$, at which the same contribution is undefined.

A model is exactly an environment $\textcolor{#398B83}{\rho}$ extending $\textcolor{#398B83}{\eta}$ for which
$\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}$ is defined and

$$
\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})=\textcolor{#398B83}{\rho}.
$$

This is a fixed-point characterization of simultaneous equations,
not an instruction to iterate $\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}$ from zero.
No least-fixed-point selection, convergence claim, or solver is
introduced by this characterization.

### 20.3 Functional admissibility

Let $\textcolor{#398B83}{\mathop{\mathrm{Input}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}$ denote the well-typed input
environments for the program's designated inputs, and let
$\textcolor{#398B83}{\mathop{\mathrm{Output}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}$ denote the corresponding value
environments on $\textcolor{#5688C7}{\mathrm{Out}}$.
The fixed program's role sets are implicit in this notation; $\textcolor{#5688C7}{\Sigma}$
alone does not determine which identifiers are inputs or outputs.

Define the set of **functionally admissible inputs** by

$$
\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P})
=
\{\textcolor{#398B83}{\eta}\in\textcolor{#398B83}{\mathop{\mathrm{Input}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}
\mid\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})
\text{ contains exactly one environment}\}.
$$

For $\textcolor{#398B83}{\eta}\in\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P})$ with unique model $\textcolor{#398B83}{\rho}_{\textcolor{#398B83}{\eta}}$,
define

$$
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\rrbracket}(\textcolor{#398B83}{\eta})=\textcolor{#398B83}{\rho}_{\textcolor{#398B83}{\eta}}|_{\textcolor{#5688C7}{\mathrm{Out}}}.
$$

This gives a partial function

$$
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\rrbracket}:
\textcolor{#398B83}{\mathop{\mathrm{Input}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}
\rightharpoonup\textcolor{#398B83}{\mathop{\mathrm{Output}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}.
$$

Here the function domain is precisely $\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P})$.
If an application specifies an input class
$\textcolor{#398B83}{\mathcal{A}}\subseteq\textcolor{#398B83}{\mathop{\mathrm{Input}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}$, total functional
meaning on that class requires

$$
\textcolor{#398B83}{\mathcal{A}}\subseteq\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P}).
$$

The unique-model criterion is deliberately stronger than uniqueness
of outputs alone. Several models might agree on all designated outputs
while differing in internal tensors. Such output-only determinacy
could be studied separately; it is not silently substituted for the
criterion above.

Functionally admissible inputs and admissible candidate environments
are different notions. An environment can make every contribution
defined without satisfying any defining equation.
Conversely, a program can have no model even if all expressions are
defined on every complete environment.

### 20.4 Denotation does not imply executability

The model relation does not require acyclic dependencies.
A cyclic equation system can have a unique model and hence a
functional denotation while being outside a compiler's supported
execution fragment.

Conversely, a structurally valid program with partial operators may
fail to have a model on some well-typed inputs.
An operational implementation must distinguish successful execution
from undefined operations or unsupported dependency forms; it must
not return a success-shaped default for these cases.

Least-model semantics for monotone Boolean recursion, algebraic
solvers, and fixed-point iterations would each impose additional
requirements or select a particular interpretation. They are not
part of the semantics defined here.

## 21. Worked denotational examples

### 21.1 Duplicate contributions and zero defaults

Let $X$ be a numerical input of shape $(2)$ with values $2,5$, and
$T$ a defined output of the same shape:

```text
s_1: T[i] = X[i]    # i in [2]
s_2: T[i] = X[i]    # i in [2]
```

Every body is defined. For every candidate environment extending
the inputs, the collected values are

$$
\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[0]=4,
\qquad
\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[1]=10.
$$

The model equations therefore force the unique output $T=(4,10)$.
There is no previous value of $T$ added to those entries.

For the boundary example in [Section 11.1](#111-boundary-contributions), the same definition gives
the sum at the corner and zero throughout the uncovered interior.
For an untargeted defined tensor it gives zero at every coordinate
of its declared domain.

### 21.2 An intermediate fixes the activation boundary

At a fixed coordinate with numerical inputs $A[i]=1$, $B[i]=-1$,
two statements targeting $T$ with bodies
$\mathop{\mathrm{ReLU}}\nolimits(A[i])$ and $\mathop{\mathrm{ReLU}}\nolimits(B[i])$
force $T[i]=1$.

If those inputs instead contribute to `Pre`, and the only contribution
to $T[i]$ is $\mathop{\mathrm{ReLU}}\nolimits(\mathop{\mathrm{Pre}}\nolimits[i])$, the model
equations force

$$
\mathop{\mathrm{Pre}}\nolimits[i]=0,\qquad T[i]=0.
$$

The distinction follows from collected equations, not from the order
in which the statements are listed.

### 21.3 A guard differs from a zero multiplier

Let $X$ be a real input of shape $(2)$ with values $4,-1$, and let
$Y$ be a defined output of shape $(2)$.
The guarded core statement

$$
\text{for }i\in[2]\text{ where }i<1:
\quad Y[i]\textcolor{#9D75C4}{\mathrel{+}=}\log(X[i])
$$

has only the occurrence $i=0$. Its unique model gives

$$
Y[0]=\log(4),\qquad Y[1]=0.
$$

Replacing the guard by an Iverson multiplier gives

$$
\text{for }i\in[2]:
\quad Y[i]\textcolor{#9D75C4}{\mathrel{+}=}\mathbf{1}_{i<1}\log(X[i]).
$$

Now $i=1$ is an actual occurrence. Its body is undefined, so no
environment extending these inputs belongs to
$\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$ and the program has no model on this input.
The zero multiplier does not repair the logarithm's domain failure.

### 21.4 Three different cyclic equation systems

Work over $\mathbb{R}$ with scalar tensors. The following programs
are structurally well-formed:

| Source statements | Collected equation | Models |
| --- | --- | --- |
| `T[] = X[]`; `T[] = 2 T[]` | $T=X+2T$ | Unique: $T=-X$ for every supplied scalar $X$ |
| `T[] = T[]` | $T=T$ | Every real scalar value is a model |
| `T[] = T[] + 1` | $T=T+1$ | No model |

In the first row, $X$ is an input and $T$ is defined.
In the other rows, only $T$ is present and the input environment is
empty.
Every contribution expression in all three rows is defined on every
complete environment.

Thus the first program has a functional denotation despite its cycle.
The second and third do not satisfy the unique-model criterion.
A bounded-scan compiler may reject all three as unsupported cycles,
without contradicting their denotational descriptions.

### 21.5 Bounded histories have simultaneous equations too

For the finite-history program in [Section 11.4](#114-a-finite-history-with-persistent-input), assume
$F:\mathbb{R}^{[d]}\to\mathbb{R}^{[d]}$ is total.
The collected equations are

$$
H_0=X+Z,
\qquad
H_{l+1}=X+F(H_l)\quad(l\in[N]).
$$

They determine a unique history for every well-typed $X,Z$:
construct $H_0$, then the successive slices. Induction on time shows
that any other model must agree at time zero and at each following
slice. Totality and the stated array signature of $F$ ensure that
each constructed slice is defined and has the required domain.

For $d=1$, $N=2$, $X[0]=2$, $Z[0]=3$, and $F(h)[0]=2h[0]$, the
history entries are

$$
H[0,0]=5,\qquad H[0,1]=12,\qquad H[0,2]=26.
$$

When $N=0$, only the base slice is present. The recurrence statement
has no occurrences and does not create an additional equation.
This establishes the mathematical history meaning. [Part IV](#part-iv-operational-semantics) explains how
completion barriers and a time-based rank yield this same history.

## 22. Denotational scope and execution requirements

The denotational definitions apply to every structurally well-formed core
program, including cyclic equations. They determine a model relation and,
on inputs with a unique complete model, a partial input-output function.
They do not choose an execution order or guarantee that every input has
a model. In particular:

- Structural well-formedness does not discharge primitive definedness.
- Repeated destinations are contributions, not mutation versions.
- Array operators depend on complete slices, not partially collected
  coordinate values.
- A cyclic but structurally well-formed program can have zero, one,
  or many models. Executing such a program requires an execution
  restriction or a separately justified solver.

An execution strategy must respect these conditions rather than replace
them with mutation-order rules. [Part IV](#part-iv-operational-semantics) supplies a direct executor for the
coordinate-ranked fragment.
It uses complete logical values, not guesses obtained by iterating $\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}$.
Its correspondence is with the unique-model meaning of [Section 20](#20-program-models-and-functional-denotation), not
with a newly selected least model or mutation-order interpretation.

## Part IV: Operational semantics

The reference machine evaluates and collects individual contribution
occurrences. It permits arbitrary interleaving where dependencies allow,
but publishes a defined coordinate only after all occurrences targeting it
have been consumed.

This is an abstract, exact-value machine using the primitive interpretations
fixed in [Section 13.2](#132-value-types-and-primitive-signatures). Expression evaluation
is atomic at this level. Computable implementations of the primitives and
their domain tests are separate requirements, especially over exact reals.

## 23. Read footprints and executable dependencies

### 23.1 Address partitions

Fix a structurally well-formed core program $\textcolor{#9D75C4}{P}$. Its roles partition the
address set:

$$
\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{In}}}
=\{(T,p)\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\mid T\in\textcolor{#5688C7}{\mathrm{In}}\},
\qquad
\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}
=\{(T,p)\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\mid T\in\textcolor{#5688C7}{\mathrm{Def}}\}.
$$

Recall the destination function from [Section 9.2](#92-tagged-contribution-occurrences): for
$\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\in\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}$,

$$
\textcolor{#9D75C4}{\mathop{\mathrm{dst}}\nolimits}(\textcolor{#9D75C4}{o})=(T_{\textcolor{#9D75C4}{s}},\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu})).
$$

For $a=(T,p)\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}$, abbreviate
$\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)=\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T,p)$.
These are the existing tagged occurrences and fibers, not new contributions.

### 23.2 Read footprints of expressions

For a structurally valid expression at an admissible valuation $\textcolor{#5688C7}{\nu}$,
define its **read footprint**
$\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})\subseteq\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}$ recursively.
This set records which named coordinates must be available before the
expression is interpreted by the direct executor:

$$
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(c_K,\textcolor{#5688C7}{\nu})
=\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\mathbf{1}_{\textcolor{#9D75C4}{Q}},\textcolor{#5688C7}{\nu})=\varnothing,
$$

$$
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(T[\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_k],\textcolor{#5688C7}{\nu})
=\{(T,(\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{e}_1\rrbracket_{\textcolor{#5688C7}{\nu}},\ldots,
        \textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{e}_k\rrbracket_{\textcolor{#5688C7}{\nu}}))\},
$$

$$
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E}_1\star \textcolor{#9D75C4}{E}_2,\textcolor{#5688C7}{\nu})
=\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E}_1,\textcolor{#5688C7}{\nu})\cup\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E}_2,\textcolor{#5688C7}{\nu}),
\qquad\star\in\{\oplus,\otimes\},
$$

$$
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}\left(\bigoplus_{j\in \textcolor{#5688C7}{I}_j}\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu}\right)
=\bigcup_{k\in \textcolor{#5688C7}{I}_j}\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu}[j\mapsto k]),
$$

$$
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}\left(
 \textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j_1\in \textcolor{#5688C7}{I}_1,\ldots,j_m\in \textcolor{#5688C7}{I}_m}(\textcolor{#9D75C4}{E}),\textcolor{#5688C7}{\nu}
\right)
=\bigcup_{p\in \textcolor{#5688C7}{I}_1\times\cdots\times \textcolor{#5688C7}{I}_m}
  \textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu}_p),
$$

$$
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}(\textcolor{#9D75C4}{E},(\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_m)),\textcolor{#5688C7}{\nu})
=\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu}),
$$

$$
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(f(\textcolor{#9D75C4}{E}_1,\ldots,\textcolor{#9D75C4}{E}_q),\textcolor{#5688C7}{\nu})
=\bigcup_{r=1}^{q}\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E}_r,\textcolor{#5688C7}{\nu}).
$$

Here $\textcolor{#5688C7}{\nu}_p$ is the simultaneous valuation extension from [Section 18.3](#183-reduction-and-tabulation).
An empty union is empty, including for empty reductions, empty tabulations,
and nullary primitives.

The footprint of `at` includes the whole array expression, not just the
selected entry. Both operands of a scalar operation remain in the footprint,
even for multiplication by zero. These choices implement [Part III](#part-iii-denotational-semantics)'s strict
interpretation. A statement guard instead removes excluded occurrences
before footprints are taken.

A footprint is a set: reading the same address twice does not create two
availability requirements. It does **not** erase the two reads from the
expression or erase contribution multiplicity.
The footprint is a sufficient readiness requirement, not a claim of minimal
mathematical dependence. Pruning a semantically irrelevant read requires
an additional value-and-definedness preservation argument.

### 23.3 Stable evaluation from a partial store

Write $\textcolor{#A87C28}{\sigma}\textcolor{#A87C28}{\sqsubseteq}\textcolor{#398B83}{\rho}$ when the complete environment $\textcolor{#398B83}{\rho}$ extends
the store's available values:

$$
\textcolor{#A87C28}{\sigma}(a)=\textcolor{#398B83}{\rho}(T)[p]
\quad\text{for every }a=(T,p)\in\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma}).
$$

For typed stores, complete extensions exist: assign, for example, $0_K$ to
unspecified coordinates. This is a mathematical extension for defining an
interpretation, not operational permission to read missing values as zero.

**Lemma 23.1 (read stability).** If two complete environments agree on
$\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})$, their interpretations of $\textcolor{#9D75C4}{E}$ at $\textcolor{#5688C7}{\nu}$ are
equal, including the possibility that both results are $\textcolor{#398B83}{\bot}$.

The proof is structural induction on $\textcolor{#9D75C4}{E}$. Reads use the stipulated
agreement; scalar operations use the induction hypotheses for both
operands. Reductions and tabulations use them at every actual body
valuation. Selection uses equality of the complete array result.
A primitive uses equal argument results and the same domain
$\textcolor{#398B83}{\mathcal{D}}_f$, hence has equal definedness and value.

When
$\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})\subseteq\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$,
define the ready evaluation

$$
\textcolor{#A87C28}{\mathop{\mathrm{Eval}}\nolimits}_{\textcolor{#A87C28}{\sigma}}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})
=\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
\quad\text{for any complete }\textcolor{#398B83}{\rho}\text{ with }\textcolor{#A87C28}{\sigma}\textcolor{#A87C28}{\sqsubseteq}\textcolor{#398B83}{\rho}.
$$

Read stability makes the choice irrelevant. This result belongs to
$\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau})$ for an expression of type $\textcolor{#5688C7}{\tau}$.
Write $\textcolor{#A87C28}{\mathop{\mathrm{Eval}}\nolimits}_{\textcolor{#A87C28}{\sigma}}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})\downarrow v$ for a successful
result. If the footprint is not available, ready evaluation is not invoked:
the occurrence waits. Waiting is distinct from a ready result of $\textcolor{#398B83}{\bot}$.

### 23.4 Coordinate dependencies and the ranked fragment

For $\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$, abbreviate
$\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})=\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}},\textcolor{#5688C7}{\nu})$.
Define

$$
\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)
=\bigcup_{\textcolor{#9D75C4}{o}\in\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)}\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})
\quad(a\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}),
$$

and set $\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)=\varnothing$ for input addresses.

The **coordinate-ranked fragment** consists of programs with a certificate
$r:\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\to\mathbb{N}$ satisfying

$$
b\in\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)\Longrightarrow r(b)<r(a).
$$

Equivalently, the finite directed graph with edges $b\to a$ for
$b\in\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)$ is acyclic.
This graph and its certificate are independent of input values: indices,
guards, and binder domains do not depend on tensor values.
The certificate ensures dependency progress, not primitive definedness.

A compiler for this fragment must justify such a certificate or explicitly
reject the dependency form. It may use symbolic ranks without enumerating
every coordinate. The abstract graph is a specification, not a prescribed
compilation data structure.

Dependencies must be taken at coordinate level. A finite history may read
the same tensor identifier that it defines while its time coordinates
still admit a strictly increasing rank.

## 24. Machine configurations and initialization

### 24.1 Published values, accumulators, and pending occurrences

A running configuration is a triple

$$
\textcolor{#A87C28}{\mathsf{Conf}}=(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U}),
$$

where:

- $\textcolor{#A87C28}{\sigma}:\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\rightharpoonup K$ is the store of
  **published, complete** coordinate values.
- $\textcolor{#A87C28}{\alpha}:\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}\to K$ is the accumulator map.
  An accumulator may contain only some of a coordinate's contributions.
- $\textcolor{#A87C28}{U}\subseteq\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}$ is the set of pending occurrences, not yet
  successfully consumed.

Accumulators are not expression-readable. Only $\textcolor{#A87C28}{\sigma}$ supplies named
reads. A published value is immutable; source contributions are never
applied as later mutations to that value.
The reference machine retains accumulators after publication to simplify
the conservation argument. Its immutable published history and completed
accumulators may become proof-only information in a compiled implementation,
as introduced in [Section 5.3](#53-logical-addresses-physical-slots-and-proof-only-history). This does not relax logical readiness.

It also has terminal failed configurations
$\textcolor{#A87C28}{\mathsf{Failed}}(\textcolor{#9D75C4}{o},\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$, recording an occurrence whose ready
body was undefined and the machine state at failure.
This outcome is an explicit error, not a scalar result or an empty sum.
More detailed primitive-path diagnostics can refine this record without
changing the rules below.

### 24.2 Initial configuration

For $\textcolor{#398B83}{\eta}\in\textcolor{#398B83}{\mathop{\mathrm{Input}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}$, initialize

$$
\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})
=(\textcolor{#A87C28}{\sigma}_{\textcolor{#398B83}{\eta}},\textcolor{#A87C28}{\alpha}_0,\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}),
$$

where

$$
\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma}_{\textcolor{#398B83}{\eta}})=\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{In}}},
\qquad
\textcolor{#A87C28}{\sigma}_{\textcolor{#398B83}{\eta}}(T,p)=\textcolor{#398B83}{\eta}(T)[p],
\qquad
\textcolor{#A87C28}{\alpha}_0(a)=0_K
\quad(a\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}).
$$

No defined address is initially published.
Accumulator initialization is a machine operation, not an additional
source contribution. In particular, zero-filled accumulators do not make
a recurrence's future states readable.

The program's structural judgments and the complete input signature must
be validated before initialization. Missing inputs, malformed shapes, or
invalid structural accesses require explicit rejection; they are not
repaired with zeros. This applies even to an empty input tensor: its value
must be supplied although it contributes no coordinate entries to
$\textcolor{#A87C28}{\sigma}_{\textcolor{#398B83}{\eta}}$.

## 25. Execution rules and terminal outcomes

The step relation fixes $\textcolor{#9D75C4}{P}$ and its primitive registry. Rules select any
occurrence or address satisfying their premises; source-list order is not
an execution priority.

### 25.1 Consume a defined contribution

For $\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$ and $a=\textcolor{#9D75C4}{\mathop{\mathrm{dst}}\nolimits}(\textcolor{#9D75C4}{o})$:

$$
\frac{
\textcolor{#9D75C4}{o}\in \textcolor{#A87C28}{U}
\qquad
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})\subseteq\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})
\qquad
\textcolor{#A87C28}{\mathop{\mathrm{Eval}}\nolimits}_{\textcolor{#A87C28}{\sigma}}(\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}},\textcolor{#5688C7}{\nu})\downarrow v
}{
(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})
\textcolor{#A87C28}{\longrightarrow}
(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha}[a\mapsto\textcolor{#A87C28}{\alpha}(a)\oplus v],\textcolor{#A87C28}{U}\setminus\{\textcolor{#9D75C4}{o}\})
}
\quad\textcolor{#A87C28}{\mathrm{CONTRIBUTE}}.
$$

This rule removes exactly one tagged occurrence and combines its value
exactly once. The destination remains unpublished until the completion
rule applies. A successful zero-valued body still consumes its occurrence.

### 25.2 Publish a completed coordinate

$$
\frac{
a\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}\setminus
      \mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})
\qquad
\textcolor{#A87C28}{U}\cap\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)=\varnothing
}{
(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})
\textcolor{#A87C28}{\longrightarrow}
(\textcolor{#A87C28}{\sigma}[a\mapsto\textcolor{#A87C28}{\alpha}(a)],\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})
}
\quad\textcolor{#A87C28}{\mathrm{PUBLISH}}.
$$

This is the **completion barrier**: no pending contribution to $a$ remains.
Publication may be delayed by scheduling but cannot occur early.

When $\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)=\varnothing$, publication is enabled immediately
and publishes $0_K$. An unwritten coordinate thus becomes an available
zero by an explicit completion step, not by treating absence as zero.
When a coordinate has contributions, even a currently zero accumulator
cannot be published until all those occurrences are consumed.

### 25.3 Surface undefined operations

For $\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$:

$$
\frac{
\textcolor{#9D75C4}{o}\in \textcolor{#A87C28}{U}
\qquad
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})\subseteq\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})
\qquad
\textcolor{#A87C28}{\mathop{\mathrm{Eval}}\nolimits}_{\textcolor{#A87C28}{\sigma}}(\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}},\textcolor{#5688C7}{\nu})=\textcolor{#398B83}{\bot}
}{
(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})
\textcolor{#A87C28}{\longrightarrow}
\textcolor{#A87C28}{\mathsf{Failed}}(\textcolor{#9D75C4}{o},\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})
}
\quad\textcolor{#A87C28}{\mathrm{UNDEFINED}}.
$$

The failed configuration has no outgoing steps. The invalid occurrence
is not consumed as zero, and partially published outputs are not returned
as a successful program result.
The occurrence identifier and valuation locate the failed contribution.

Undefinedness is checked only for actual, ready occurrences. A guard-excluded
valuation has no occurrence; an empty binder has no body instances.
No failure is raised for those absent body instances. A primitive applied
outside an empty binder still has its own domain requirement.

### 25.4 Completion and dependency blocking

A running configuration is **complete** when

$$
\textcolor{#A87C28}{U}=\varnothing,
\qquad
\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})=\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}.
$$

It then determines a complete environment $\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}$ by
$\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}(T)[p]=\textcolor{#A87C28}{\sigma}(T,p)$.
Tensors with empty coordinate domains have their unique empty function
values in this environment.

Define successful execution by

$$
\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\Downarrow}\textcolor{#398B83}{\rho}
\quad\Longleftrightarrow\quad
\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\longrightarrow}^{*}(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\varnothing)
\text{ with }\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})=\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}
\text{ and }\textcolor{#398B83}{\rho}=\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}.
$$

All defined tensors must complete, including internal tensors not in
$\textcolor{#5688C7}{\mathrm{Out}}$. This matches the complete-model criterion in [Section 20.3](#203-functional-admissibility).
The externally returned output is $\textcolor{#398B83}{\rho}|_{\textcolor{#5688C7}{\mathrm{Out}}}$.

A running configuration is **blocked** when it is not complete and has
no enabled transition. It is neither a successful result nor an
undefined-operation failure. Blocking reports an unresolved dependency
structure; it does not prove that the equations lack a model.
[Section 26](#26-conservation-termination-and-correspondence) shows that a ranked program cannot reach such a state.

## 26. Conservation, termination, and correspondence

The claims below concern configurations reachable from
$\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ for well-typed $\textcolor{#398B83}{\eta}$.
They are stated with proof arguments. Their Lean counterparts for the
reference machine as a transition relation are listed in
[Proof status and numbered results](#proof-status-and-numbered-results).

### 26.1 Basic conservation invariants

**Lemma 26.1 (conservation).** Induction on transitions establishes:

1. $\textcolor{#A87C28}{U}\subseteq\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}$ and every successful contribution step removes
   one previously pending occurrence. No occurrence is consumed twice.
2. Accumulators and published values belong to $K$.
3. Published addresses only increase, input values remain unchanged, and
   no published value is overwritten.
4. If a defined address is published, no occurrence targeting it remains
   pending, and its published value equals its accumulator.
5. Every consumed occurrence $\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\in\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}\setminus\textcolor{#A87C28}{U}$
   has a recorded value $v_{\textcolor{#9D75C4}{o}}$, the value returned at the step consuming it, and
   for every complete environment $\textcolor{#398B83}{\rho}$ with
   $\textcolor{#A87C28}{\sigma}\textcolor{#A87C28}{\sqsubseteq}\textcolor{#398B83}{\rho}$,
   $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}$
   is defined and equals $v_{\textcolor{#9D75C4}{o}}$. The footprint of $\textcolor{#9D75C4}{o}$ was
   published when it was consumed and published values only increase (item 3),
   so this is read stability (Lemma 23.1). It needs no model and no admissibility
   hypothesis on $\textcolor{#398B83}{\rho}$.

More explicitly, with the recorded values $v_{\textcolor{#9D75C4}{o}}$ of item 5,
at each running configuration

$$
\textcolor{#A87C28}{\alpha}(a)=
\bigoplus_{\textcolor{#9D75C4}{o}\in\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)\setminus \textcolor{#A87C28}{U}}v_{\textcolor{#9D75C4}{o}}.
$$

The values $v_{\textcolor{#9D75C4}{o}}$ are associated with the execution history for this
argument; they need not be extra stored machine fields.
The formula follows from zero initialization and finite commutative
combination. Duplicate statements and colliding write valuations remain
distinct terms because they have distinct tagged occurrences.

### 26.2 Preservation of every candidate model

**Lemma 26.2 (preservation of every candidate model).**
At every reachable running configuration:

(a) For every defined address $a=(T,p)$ and every complete environment
$\textcolor{#398B83}{\rho}$ with $\textcolor{#A87C28}{\sigma}\textcolor{#A87C28}{\sqsubseteq}\textcolor{#398B83}{\rho}$,

$$
\textcolor{#A87C28}{\alpha}(a)=
\bigoplus_{(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\in\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)\setminus \textcolor{#A87C28}{U}}
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}},
$$

with every term defined. If the fiber of $a$ has no pending occurrence and
$\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$, then
$\textcolor{#A87C28}{\alpha}(a)=\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[p]$.

(b) For every
$\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$,

$$
\textcolor{#A87C28}{\sigma}\textcolor{#A87C28}{\sqsubseteq}\textcolor{#398B83}{\rho}.
$$

(c) If $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})\ne\varnothing$, no reachable configuration
is $\textcolor{#A87C28}{\mathsf{Failed}}$.

*Argument.* Part (a) follows from Lemma 26.1: each term equals the recorded value
$v_{\textcolor{#9D75C4}{o}}$ by item 5, so the sum is the accumulator formula, and a finished fiber is
the whole of $\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)$. It needs no model.
Part (b) is by induction on reachability. Initially the store agrees on
inputs. A contribution step leaves $\textcolor{#A87C28}{\sigma}$ unchanged. At publication, the induction
hypothesis lets part (a) apply to the model $\textcolor{#398B83}{\rho}$, which is admissible, and the model equation
gives $\textcolor{#A87C28}{\alpha}(a)=\textcolor{#398B83}{\rho}(T)[p]$; so agreement is preserved.
For (c), an undefined-operation step from a reachable configuration, where
$\textcolor{#A87C28}{\sigma}\textcolor{#A87C28}{\sqsubseteq}\textcolor{#398B83}{\rho}$ by (b) for any model $\textcolor{#398B83}{\rho}$, is impossible: the ready body would be defined in the
admissible $\textcolor{#398B83}{\rho}$ and, by read stability, equal to its ready evaluation,
which is $\textcolor{#398B83}{\bot}$.

### 26.3 Successful execution gives the unique model

**Theorem 26.3 (successful runs give the unique model).** Suppose
$\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})\textcolor{#A87C28}{\Downarrow}\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}$.
Every occurrence was consumed successfully. Its footprint was available
when it was consumed, and published values never changed.
Lemma 26.1 (item 5) therefore identifies its recorded value with its
interpretation in the final $\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}$.
All contribution bodies are defined there, and each published accumulator
is their complete fiber sum. Hence

$$
\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}\in\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta}).
$$

For any other model $\textcolor{#398B83}{\rho}$, Lemma 26.2(b) gives
$\textcolor{#A87C28}{\sigma}\textcolor{#A87C28}{\sqsubseteq}\textcolor{#398B83}{\rho}$ at the complete final store. Since the store has
every address, $\textcolor{#398B83}{\rho}=\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}$. Thus

$$
\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\{\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}\},
\qquad
\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\rrbracket}(\textcolor{#398B83}{\eta})=\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}|_{\textcolor{#5688C7}{\mathrm{Out}}}.
$$

No rank certificate is needed for this implication: any successful run
has this meaning.
Similarly, if a run reaches $\textcolor{#A87C28}{\mathsf{Failed}}(\textcolor{#9D75C4}{o},\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$,
then $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\varnothing$.
Otherwise Lemma 26.2(c) and read stability would force the failed ready
body to be defined in a model, a contradiction.
This failure claim does not apply to dependency blocking.

### 26.4 Finite execution and progress for ranked programs

**Lemma 26.4 (finite execution).** For a running configuration define the
natural-number measure

$$
\textcolor{#A87C28}{\mu}(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})
=|\textcolor{#A87C28}{U}|+
\left|\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}\setminus
             \mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})\right|.
$$

A contribution step decreases its first term by one. A publication step
decreases its second term by one. An undefined-operation step is terminal.
Thus every run has at most
$|\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}|+|\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}|$
non-failure steps and cannot have infinitely many transitions.
A **maximal run** continues until no transition is enabled; a finite
prefix stopped by a scheduler is not automatically maximal.
No fairness assumption is needed: each contribution or publication step
strictly decreases $\textcolor{#A87C28}{\mu}$ and an undefined-operation step is terminal, so every
run has at most $\textcolor{#A87C28}{\mu}$ such steps from its start, plus at most one failing step,
and every maximal run ends at a terminal configuration.

**Theorem 26.5 (ranked progress).** Assume a rank certificate exists.
In any reachable, noncomplete
running configuration there is an unpublished defined address:
if all were published, the invariants would also force $\textcolor{#A87C28}{U}=\varnothing$.
Choose one of minimum rank. All its dependencies are already published,
since inputs were supplied initially and defined dependencies have lower
rank. If its fiber has pending occurrences, each is ready and enables
either $\textcolor{#A87C28}{\mathrm{CONTRIBUTE}}$ or $\textcolor{#A87C28}{\mathrm{UNDEFINED}}$.
If it has none, $\textcolor{#A87C28}{\mathrm{PUBLISH}}$ is enabled.
This proves progress and excludes blocking.

**Theorem 26.6 (ranked correspondence).** Combining Theorem 26.5,
Lemma 26.4, and Theorem 26.3 gives the
operational/denotational correspondence for the ranked fragment:

$$
\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})\textcolor{#A87C28}{\Downarrow}\textcolor{#398B83}{\rho}
\quad\Longleftrightarrow\quad
\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\{\textcolor{#398B83}{\rho}\}.
$$

In more detail, every maximal run either succeeds or explicitly fails.
If a model exists, model preservation excludes failure, so every maximal
run succeeds and returns that unique model. If no model exists,
successful completion is impossible, so every maximal run fails.

**Corollary 26.7 (ranked uniqueness).** A ranked program has at most one
model on any well-typed input: a model forces every maximal run to succeed,
and a successful run has a unique model by Theorem 26.3.

Therefore every maximal run of the reference machine, under any schedule,
realizes exactly the partial function of
[Section 20.3](#203-functional-admissibility) for ranked programs. The machine is a transition relation;
choosing a schedule is a separate, computable artifact. The Lean executor is
one such artifact, for an exact-rational profile with a supplied schedule
(see [the Lean path document](lean_executable_semantics_path.md#46-the-computable-reference-executor)).
Successful schedules produce the same
environment, even if they consume contributions and publish unrelated
addresses in different orders. On a failing input, schedules may report
different undefined occurrences; the first diagnostic is not claimed to
be schedule-independent.

## 27. Worked operational examples

### 27.1 An accumulator is not a readable intermediate

Use scalar numerical inputs $A[]=1$ and $B[]=-1$:

```text
Pre[] = A[]
Pre[] = B[]
T[]   = relu(Pre[])
```

After consuming only the first contribution,
$\textcolor{#A87C28}{\alpha}(\mathop{\mathrm{Pre}}\nolimits,())=1$, but
$(\mathop{\mathrm{Pre}}\nolimits,())\notin\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$.
The contribution to $T$ is not ready. Consuming the second gives
$\textcolor{#A87C28}{\alpha}(\mathop{\mathrm{Pre}}\nolimits,())=0$; publication now makes the completed
zero readable. ReLU then contributes zero to $T$, which can be published.
Reversing the first two consumption steps gives the same result.

Applying ReLU to the partially accumulated value $1$ would violate the
readiness rule and change the program's meaning.
Separate contributions `relu(A[])` and `relu(B[])` instead produce $1$,
as in [Section 21.2](#212-an-intermediate-fixes-the-activation-boundary); that is a different program.

### 27.2 Boundary overlap and unwritten coordinates

For [Section 11.1](#111-boundary-contributions), the corner's fiber contains both its row and column
occurrences. If $C[0]=2$ and $R[0]=7$, its accumulator may first be $2$
or $7$, depending on scheduling. It becomes readable only after both
occurrences are consumed and $T[0,0]=9$ is published.
There is no overlap-agreement test.

An interior coordinate such as $(T,(1,1))$ has an empty fiber.
It can be published as zero immediately. A consumer may read that zero
after publication, but never merely because the address is absent.
Duplicate statements and affine write collisions use the same completion
rule, with all their occurrences retained.

### 27.3 Guards, empty binders, and failure

For the guarded logarithm of [Section 21.3](#213-a-guard-differs-from-a-zero-multiplier), only $i=0$ belongs to the
occurrence set. Its body is ready from the supplied $X$ and contributes
$\log(4)$; the empty fiber at $Y[1]$ publishes zero.

For the Iverson-multiplied version, both occurrences are present.
The body at $i=1$ is ready but undefined, so a maximal run reaches
$\textcolor{#A87C28}{\mathsf{Failed}}((\textcolor{#9D75C4}{s},i=1),\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$.
It cannot return the partially computed $Y$ as a successful output.

Empty binders also affect dependencies. The scalar statement

$$
T[]\textcolor{#9D75C4}{\mathrel{+}=}\bigoplus_{j\in[0]}T[]
$$

has one contribution occurrence, but that body's read footprint is empty.
It contributes zero and $T$ then publishes zero.
The tensor name appears on both sides, yet there is no coordinate
dependency cycle: the bound body has no instances.

### 27.4 Bounded scans and complete logical slices

For [Section 11.4](#114-a-finite-history-with-persistent-input), the recurrence body at $(i,l)$ has the core form

$$
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
F\left(\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[d]}(H[j,l])\right),(i)
\right).
$$

Its footprint is $\{(H,(j,l))\mid j\in[d]\}$.
Thus every coordinate of $H_l$ must be published before this recurrence
contribution is ready. No update reads a partially accumulated slice.

A certificate is

$$
r(X,i)=r(Z,i)=0,
\qquad
r(H,(i,l))=l+1,
$$

where $r(X,i)$ abbreviates $r((X,(i)))$, and similarly for $Z$.
The persistent-input and base contributions depend only on supplied
inputs. Every recurrence destination at time $l+1$ depends only on the
lower-ranked slice at time $l$.

For the scalar example $X[0]=2$, $Z[0]=3$, $F(h)[0]=2h[0]$, and $N=2$,
one legal schedule is:

| Step group | Accumulator change or publication |
| --- | --- |
| Consume the three persistent-input occurrences | Accumulators at times $0,1,2$ are each $2$ |
| Consume the base occurrence | Time-zero accumulator becomes $5$ |
| Publish time zero | $H[0,0]=5$ becomes readable |
| Consume the recurrence occurrence for $l=0$ | Time-one accumulator becomes $2+10=12$ |
| Publish time one | $H[0,1]=12$ becomes readable |
| Consume the recurrence occurrence for $l=1$ | Time-two accumulator becomes $2+24=26$ |
| Publish time two | $H[0,2]=26$ becomes readable |

The first row represents three separate machine steps.
There are six contribution steps and three publication steps in total.
Other legal schedules give the same history.
In particular, a future slice may accumulate its persistent input early,
but it cannot publish until its recurrence contributions also arrive.

When $N=0$ there are no recurrence occurrences. When $d=0$ there are no
history coordinates or contributions, and the history is the unique
empty tensor. No nonexistent recurrence body is evaluated.

### 27.5 A cycle can block with or without a model

For `T[] = X[]; T[] = 2 T[]`, the supplied-input occurrence can contribute
$X$ to the accumulator. The self-reading occurrence then waits for $T$,
while publication waits for that same occurrence. The machine is blocked,
although the unique model is $T=-X$.

For `T[] = T[]`, the initial machine is already blocked and the equations
have many models. For `T[] = T[] + 1`, it is also blocked and there is no
model. These three outcomes are denotationally different despite the
same kind of unresolved operational cycle.

None admits the rank certificate of [Section 23.4](#234-coordinate-dependencies-and-the-ranked-fragment).
A ranked-fragment compiler should report an unsupported dependency form,
not assert inconsistency or pick the zero accumulator as a solution.

## 28. Reference-machine boundaries and proof targets

[Part IV](#part-iv-operational-semantics) specifies logical execution, not a storage layout or a claim about
the current compiler. A compiled implementation may collect whole tensors,
batch occurrences, fuse reductions, or run independent work in parallel,
provided it preserves:

- Every actual contribution occurrence, exactly once, including duplicate
  statements and colliding valuations.
- The exact-semiring fiber combination.
- Ready, complete values for every expression read and primitive argument.
- Immutable logical versions, particularly distinct scan time coordinates.
- Explicit undefined-operation failure and rejection of unsupported
  dependencies, rather than success-shaped defaults.

Fusing contribution and publication steps is valid only if the same
completion barrier is maintained. Pruning reads or occurrences requires
definedness preservation as well as value preservation.
Physical buffer reuse requires a separate liveness and representation
argument: a time-based logical rank does not itself justify overwriting a
value that a remaining operation still needs.
Exact commutative sums are not automatically bitwise floating-point
guarantees; a machine-arithmetic interpretation must specify its reduction
order or numerical correctness criterion.

The foundational proof targets are:

1. Typed expression interpretation and read footprints are well-defined;
   interpretation returns a declared value or $\textcolor{#398B83}{\bot}$.
2. Interpretation and footprints respect bound-variable renaming and
   well-scoped, domain-respecting capture-avoiding substitution.
3. Read stability justifies ready evaluation independently of a chosen
   complete extension (Lemma 23.1).
4. Core elaboration preserves pure-einsum values, domains, and multiplicity,
   including empty domains and repeated output indices (Proposition 19.1;
   proved in Lean for the bounded source fragment).
5. Source-statement permutation preserves the model relation and successful
   execution results under corresponding occurrence relabeling
   (Proposition 19.2).
6. The transition invariants and model-preservation claims hold
   (Lemmas 26.1 and 26.2, Theorem 26.3).
7. The finite measure and rank certificate establish termination and
   progress; every maximal run of the reference machine computes exactly the
   unique model or explicitly fails on a ranked program
   (Lemma 26.4, Theorems 26.5 and 26.6, Corollary 26.7).

The arguments in [Part IV](#part-iv-operational-semantics) establish the reference-machine properties.
[Proof status and numbered results](#proof-status-and-numbered-results)
records which are also proved in Lean.
[Part V](#part-v-compilation-and-refinement) supplies the compilation/refinement layer: it defines plan contracts
and the relation between logical states and reusable storage.
General cyclic solvers remain a separately justified extension, not an
implicit fallback.

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
(the rank certificate of [Section 23.4](#234-coordinate-dependencies-and-the-ranked-fragment), which a schedule certificate already
implies; see the end of [Section 29.3](#293-coverage-and-schedule-certificates)).
An execution plan $\textcolor{#C16C86}{\Pi}$ records the source signature and tensor roles
$(\textcolor{#5688C7}{\mathrm{In}},\textcolor{#5688C7}{\mathrm{Def}},\textcolor{#5688C7}{\mathrm{Out}})$,
a finite buffer collection $\textcolor{#C16C86}{\mathcal{B}}$ with capacities, and a finite
command sequence

$$
(\textcolor{#C16C86}{\kappa}_0,\ldots,\textcolor{#C16C86}{\kappa}_{m-1}).
$$

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

$$
G\subseteq \textcolor{#A87C28}{U},
\qquad
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})\subseteq\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})
\quad\text{for every }\textcolor{#9D75C4}{o}\in G.
$$

If every body succeeds with value $v_{\textcolor{#9D75C4}{o}}$, the logical post-state is
$(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha}',\textcolor{#A87C28}{U}\setminus G)$, where

$$
\textcolor{#A87C28}{\alpha}'(a)
=\textcolor{#A87C28}{\alpha}(a)\oplus
 \bigoplus_{\textcolor{#9D75C4}{o}\in G\cap\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)}v_{\textcolor{#9D75C4}{o}}
\quad(a\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}).
$$

The contract leaves $\textcolor{#A87C28}{\sigma}$ unchanged. If a body is undefined, the kernel
must explicitly fail in a way matching a reference execution ending in
$\textcolor{#A87C28}{\mathsf{Failed}}$, not produce a successful aggregate.
[Section 32](#32-batched-collection-and-array-kernels) specifies the correspondence for both cases.

For $\textcolor{#C16C86}{\mathsf{Publish}}(B)$, require

$$
B\cap\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})=\varnothing,
\qquad
\textcolor{#A87C28}{U}\cap\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)=\varnothing
\quad\text{for every }a\in B.
$$

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

These conditions preserve all actual contributions and every declared
defined coordinate, including empty fibers. They also ensure the readiness
and completion premises of [Section 29.2](#292-accumulation-and-publication-contracts) at each successful prefix.
They do not establish body-definedness on every input.

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

$$
\textcolor{#C16C86}{\mathsf{C}}=(\textcolor{#C16C86}{\mathsf{pc}},\textcolor{#C16C86}{M},\textcolor{#C16C86}{\chi}),
\qquad \textcolor{#C16C86}{\mathsf{pc}}\in[m+1],
$$

where $\textcolor{#C16C86}{M}$ is the memory from [Section 5.3](#53-logical-addresses-physical-slots-and-proof-only-history) and $\textcolor{#C16C86}{\chi}$ is the plan's specified
control and layout metadata. It is not a second source-language environment.
Metadata may be determined statically by the command position rather than
stored as runtime fields.

For $\textcolor{#C16C86}{\mathsf{pc}}<m$, executing $\textcolor{#C16C86}{\kappa}_{\textcolor{#C16C86}{\mathsf{pc}}}$ defines a transition

$$
\textcolor{#C16C86}{\mathsf{C}}\textcolor{#C16C86}{\longrightarrow}_{\textcolor{#C16C86}{\Pi}}\textcolor{#C16C86}{\mathsf{C}}'.
$$

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

$$
\textcolor{#C16C86}{M}[\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}(\textcolor{#A87C28}{\mathsf{pub}}(a))]=\textcolor{#A87C28}{\sigma}(a),
\qquad
\textcolor{#C16C86}{M}[\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}(\textcolor{#A87C28}{\mathsf{acc}}(a))]=\textcolor{#A87C28}{\alpha}(a),
$$

with the respective side conditions
$a\in\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$ and
$a\notin\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})$.
Every mapped slot is initialized. The simple profile here requires
$\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}$ to be injective on its domain: distinct simultaneously
represented resources occupy distinct slots.
More permissive aliasing needs a separate justification.

Define the output address set

$$
\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Out}}}
=\{(T,p)\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\mid T\in\textcolor{#5688C7}{\mathrm{Out}}\}.
$$

At $(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$, every published address in

$$
\textcolor{#A87C28}{\mathop{\mathrm{Need}}\nolimits}_{\mathrm{pub}}(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{U})
=\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})\cap
 \left(
 \textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Out}}}
 \cup\bigcup_{\textcolor{#9D75C4}{o}\in \textcolor{#A87C28}{U}}\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})
 \right)
$$

must have a mapped $\textcolor{#A87C28}{\mathsf{pub}}$ resource.
All outputs remain concretely represented once published, and every
remaining contribution's already-published sources remain represented.
A plan may retain extra resources for its own storage operations.
Any such operation's actual reads must also have valid representations.

For $a\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}$, an unpublished address
that has already received a contribution must
retain a mapped accumulator:

$$
a\notin\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma}),
\quad
\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)\setminus \textcolor{#A87C28}{U}\ne\varnothing
\quad\Longrightarrow\quad
\textcolor{#A87C28}{\mathsf{acc}}(a)\in\mathop{\mathrm{dom}}\nolimits(\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}).
$$

An untouched accumulator has the known value $0_K$ by Lemma 26.1 and
need not yet occupy a slot. Before a kernel updates or reads its physical
accumulator, it must materialize that zero or prove an equivalent
initial-write operation. Uninitialized memory is never used as a zero.

These requirements permit a compiled execution to forget dead published
values and completed accumulators physically. Their values remain in the
reference state as ghost history, not as available runtime storage.

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

Liveness between commands is not sufficient for safety inside a kernel:
all required reads of old contents must occur before an overlapping write,
or an independent snapshot must preserve them. Temporary array storage
must also be initialized, typed, and protected from conflicting writes.

### 30.4 The refinement relation and output decoder

Write

$$
\textcolor{#C16C86}{\mathcal{R}}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#C16C86}{\mathsf{C}},\textcolor{#A87C28}{\mathsf{Conf}})
$$

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

$$
\textcolor{#C16C86}{\mathop{\mathrm{Decode}}\nolimits}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#C16C86}{\mathsf{C}})(T)[p]
=\textcolor{#C16C86}{M}[\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}(\textcolor{#A87C28}{\mathsf{pub}}((T,p)))].
$$

An output with empty coordinate domain is reconstructed as its unique
empty function with the declared signature; it requires no slots.
A scalar output requires its one rank-zero coordinate.
The decoder cannot recover overwritten output entries from ghost history
or silently supply zeros at missing nonempty output coordinates.

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
follows from the others (Lemma 31.2). The rank certificate of [Section 23.4](#234-coordinate-dependencies-and-the-ranked-fragment),
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

### 31.2 Initial states and successful-step simulation

The initialization obligation is

$$
\textcolor{#C16C86}{\mathcal{R}}_{\textcolor{#C16C86}{\Pi}}(
 \textcolor{#C16C86}{\mathop{\mathrm{Start}}\nolimits}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#398B83}{\eta}),\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})).
$$

For each successful concrete step, require

$$
\textcolor{#C16C86}{\mathcal{R}}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#C16C86}{\mathsf{C}},\textcolor{#A87C28}{\mathsf{Conf}})
\ \land\
\textcolor{#C16C86}{\mathsf{C}}\textcolor{#C16C86}{\longrightarrow}_{\textcolor{#C16C86}{\Pi}}\textcolor{#C16C86}{\mathsf{C}}'
\quad\Longrightarrow\quad
\exists\textcolor{#A87C28}{\mathsf{Conf}}'\;.\;
\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\longrightarrow}^{*}\textcolor{#A87C28}{\mathsf{Conf}}'
\ \land\
\textcolor{#C16C86}{\mathcal{R}}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#C16C86}{\mathsf{C}}',\textcolor{#A87C28}{\mathsf{Conf}}').
$$

The matching reference segment must implement the command's declared
annotations. A batch may match many contribution steps; a block publication
may match many publication steps; a pure storage change matches zero steps.
A fused command must justify the same intermediate logical barriers as
its annotation sequence.

This is a **forward simulation with stuttering**: a concrete step may
leave the reference state unchanged. It is not enough, by itself, to prove
concrete termination or prevent an incorrectly stuck compiled execution.

### 31.3 Failure matching, progress, and finishing

If a related concrete state steps to $\textcolor{#C16C86}{\mathsf{PlanFailed}}(\textcolor{#9D75C4}{o})$, require
a matching reference segment ending in

$$
\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\longrightarrow}^{*}
\textcolor{#A87C28}{\mathsf{Failed}}(\textcolor{#9D75C4}{o},\textcolor{#A87C28}{\sigma}',\textcolor{#A87C28}{\alpha}',\textcolor{#A87C28}{U}').
$$

Thus the reported semantic failure is caused by an actual ready,
undefined source occurrence. A generic kernel exception is not automatically
such a proof. Resource exhaustion or hardware faults are separate explicit
**implementation errors**: a third terminal outcome, distinct from success and
from matched semantic failure, that does not establish absence of a model.
The **error-free profile** consists of the runs in which no implementation
error occurs. Concrete progress below, and the converse direction of
Theorem 31.3, are stated for that profile.

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

$$
\textcolor{#C16C86}{\mathop{\mathrm{Decode}}\nolimits}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#C16C86}{\mathsf{C}})=\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}|_{\textcolor{#5688C7}{\mathrm{Out}}}.
$$

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

$$
\textcolor{#C16C86}{\mathop{\mathrm{Start}}\nolimits}_{\textcolor{#C16C86}{\Pi}}(\textcolor{#398B83}{\eta})\textcolor{#C16C86}{\Downarrow}_{\textcolor{#C16C86}{\Pi}}\textcolor{#398B83}{\zeta}
\quad\Longleftrightarrow\quad
\exists\textcolor{#398B83}{\rho}\;.\;
\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\{\textcolor{#398B83}{\rho}\}
\ \land\ \textcolor{#398B83}{\zeta}=\textcolor{#398B83}{\rho}|_{\textcolor{#5688C7}{\mathrm{Out}}}.
$$

Equivalently, in the error-free profile, successful plan inputs are precisely
$\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P})$, and on that domain the decoded output equals
$\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\rrbracket}(\textcolor{#398B83}{\eta})$. The model-set formulation avoids applying
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

The theorem is conditional on Definition 31.1. Its hypotheses are exactly
those conditions; the generic steps (Lemma 31.2 above and, for batched
kernels, Lemma 32.1 in [Section 32.1](#321-why-exact-batched-accumulation-refines-individual-steps)) are argued on paper, while conditions
3-5 remain an obligation on each kernel. It is a compiler proof specification with a mathematical
argument, not a claim that a particular compiler or kernel has already been
verified.

## 32. Batched collection and array kernels

### 32.1 Why exact batched accumulation refines individual steps

**Lemma 32.1 (batched accumulation refines individual steps).**
For a ready group $G$ with all successful values $v_{\textcolor{#9D75C4}{o}}$, define

$$
\textcolor{#398B83}{\Delta}_G(a)=\bigoplus_{\textcolor{#9D75C4}{o}\in G\cap\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)}v_{\textcolor{#9D75C4}{o}}.
$$

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

### 32.2 Complete arrays, empty groups, and shared computations

An array kernel must implement [Section 18](#18-expression-interpretation-and-definedness)'s interpretation, including
complete arguments, primitive domains, and complete-array selection.
In particular, computing only the selected coordinate of

$$
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[2]}(\log(X[j])),(0)
\right)
$$

is not valid if the other tabulated coordinate has an invalid logarithm,
as in [Section 18.5](#185-definedness-examples-and-transformation-limits).

For a whole-slice primitive, the logical footprint contains every required
input coordinate. Those published values must have concrete representations
when the kernel reads them. Sharing one evaluation of a deterministic
array primitive among several occurrence bodies is permitted if it preserves
their individual values and definedness and their contribution accounting.

An empty occurrence group evaluates no bodies. A compiler must not invoke
a partial primitive merely because the syntax contains it in a statement
whose occurrence domain is empty.
An actually demanded primitive on an empty array is different: its
$\textcolor{#398B83}{\mathcal{D}}_f$ condition still applies, as in [Section 25.3](#253-surface-undefined-operations).

### 32.3 Publication fusion and interference

An accumulation-and-publication kernel may fuse
$\textcolor{#C16C86}{\mathsf{Accumulate}}(G)$ and $\textcolor{#C16C86}{\mathsf{Publish}}(B)$ only when publication's
premises hold after removing $G$ from $\textcolor{#A87C28}{U}$. It must not expose partial
accumulators through an output view while another contribution remains.

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

Use the finite history of [Section 11.4](#114-a-finite-history-with-persistent-input) with total
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
The certificate $r(H,(i,l))=l+1$ from [Section 27.4](#274-bounded-scans-and-complete-logical-slices) applies.
If an explicit `Last` output is included, finish by accumulating its reads
of $H_N$ and publishing `Last`.

Unlike the schedule in [Section 27.4](#274-bounded-scans-and-complete-logical-slices), this plan consumes a slice's persistent
input only when constructing that slice. It still accounts for every
occurrence exactly once. It never adds $X$ twice merely because a previous
slice remains stored.

### 33.2 Reusing two state buffers

If $H$ is internal and the designated output is defined by

$$
\mathop{\mathrm{Last}}\nolimits[i]\textcolor{#9D75C4}{\mathrel{+}=}H[i,N],
\qquad i\in[d],
$$

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

Parts [III](#part-iii-denotational-semantics)-[V](#part-v-compilation-and-refinement) separate three obligations:

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
- Resource views, concrete states, and the representation relation,
  including empty shapes and untouched zero accumulators.
- Refinement lemmas for individual kernels, block publication, and storage
  operations; composite lemmas for fused commands.
- Preservation of explicit undefinedness when batching or sharing expressions.
- Concrete progress and termination, not just forward simulation.
- Terminal decoding and the compiled-correctness theorem.
- Separate-buffer and two-buffer scan proofs, with full-history and
  terminal-only output contracts tested separately.

These are proposed contracts and proof targets, not kernel-checked results
or claims about current compiler acceptance. Connecting them to Lean requires
choosing a concrete plan representation and kernel fragment and proving that
they satisfy the contracts, including additive contribution semantics.
Machine-number refinement, more permissive aliasing, asynchronous command
execution, and general cyclic solvers require their own explicit extensions.

## 35. Compact notation reference

The groups follow the reading-guide color key. Scalar algebra and generic
mathematical notation remain neutral; mixed expressions retain the colors
of their individual components.

### Domains, signatures, and index binding

| Symbol | Meaning |
| --- | --- |
| $[n]$ | Finite ordinal $\{0,\ldots,n-1\}$ |
| $()$ | Empty tuple; the sole rank-zero coordinate |
| $a,\textcolor{#5688C7}{I}_a,n_a$ | Axis, its coordinate range, and extent |
| $\textcolor{#5688C7}{\Gamma},\textcolor{#5688C7}{\nu}$ | Index context and valuation |
| $\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma})$ | All valuations for that context |
| $\textcolor{#5688C7}{\Gamma}_{\mathrm{all}}$ | All distinct variables of a pure einsum with resolved domains |
| $\textcolor{#5688C7}{L},\textcolor{#5688C7}{L}_r$ | Output and operand index strings |
| $J_{\textcolor{#5688C7}{L}},\textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}}$ | A string's coordinate domain and projection from a global valuation |
| $\textcolor{#5688C7}{\mathop{\mathrm{vars}}\nolimits}(\textcolor{#5688C7}{\Gamma})$ | Variable-identity set of an index context |
| $\textcolor{#5688C7}{D}^{+j}$ | A valuation domain lifted over a fresh binder |
| $\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$ | Admissible free-variable valuations for statement $\textcolor{#9D75C4}{s}$ |
| $\textcolor{#5688C7}{\Sigma}$ | Tensor signature |
| $\textcolor{#5688C7}{\mathrm{In}},\textcolor{#5688C7}{\mathrm{Def}},\textcolor{#5688C7}{\mathrm{Out}}$ | Input, defined, and designated output identifiers |
| $\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)$ | Coordinate domain of tensor $T$ |
| $(T,p)$ | Tensor address |
| $\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{In}}},\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}$ | Input and defined address partitions |
| $\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Out}}}$ | All declared output coordinates |
| $\textcolor{#5688C7}{\tau},\textcolor{#9D75C4}{\mathcal{F}}$ | Expression value type and primitive registry |
| $\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma};\textcolor{#5688C7}{D}\vdash \textcolor{#9D75C4}{E}:\textcolor{#5688C7}{\tau}$ | Structural expression judgment under a signature, index context, and admissible valuation domain |

### Program syntax and source identities

| Symbol | Meaning |
| --- | --- |
| $\textcolor{#9D75C4}{\mathop{\mathrm{FV}}\nolimits}(\textcolor{#9D75C4}{E})$ | Free variables of an expression |
| $\textcolor{#9D75C4}{E}[i:=\textcolor{#9D75C4}{e}]$ | Capture-avoiding index substitution |
| $\textcolor{#9D75C4}{\mathop{\mathrm{dst}}\nolimits}(\textcolor{#9D75C4}{o})$ | Destination address of contribution occurrence $\textcolor{#9D75C4}{o}$ |
| $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}$ | Statement's write map |
| $\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}$ | Statement's contribution expression |
| $(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$ | Tagged contribution occurrence |
| $\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}$ | All contribution occurrences of program $\textcolor{#9D75C4}{P}$ |
| $\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T,p)$ | Occurrences addressing coordinate $p$ of $T$ |
| $\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits},\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}$ | Array construction and scalar coordinate selection |
| $C_b,B_{\textcolor{#9D75C4}{s}}$ | Contracted variables of a surface term and elaborated additive body |

### Scalar foundations, denotational values, and equations

| Symbol | Meaning |
| --- | --- |
| $K$ | Scalar carrier |
| $\mathcal{K}$ | Scalar semiring structure |
| $\oplus,\otimes$ | Contribution/reduction combination and multiplication |
| $0_K,1_K$ | Additive and multiplicative identities |
| $\textcolor{#398B83}{V}_{\textcolor{#5688C7}{L}}$ | Canonical pure-einsum result tensor |
| $\textcolor{#398B83}{\rho},\textcolor{#398B83}{\eta}$ | Complete tensor environment and input environment |
| $\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau}),\textcolor{#398B83}{\bot}$ | Successful typed values or an undefined result |
| $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}\downarrow v$ | Expression interpretation is defined with value $v$ |
| $\textcolor{#398B83}{\mathop{\mathrm{lift}}\nolimits}_2$ | Strict lifting of a scalar binary operation to results |
| $\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}$ | Complete environment reconstructed from a complete store |
| $\textcolor{#398B83}{\zeta}$ | Decoded output environment |
| $\textcolor{#398B83}{\Delta}_G$ | Exact fiber aggregate for a successful ready occurrence group |
| $\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$ | Complete environments on which all actual contributions are defined |
| $\textcolor{#398B83}{V}_{\textcolor{#9D75C4}{s}}^{\textcolor{#398B83}{\rho}}$ | Contribution tensor of statement $\textcolor{#9D75C4}{s}$ in environment $\textcolor{#398B83}{\rho}$ |
| $\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})$ | Values collected for all defined tensors |
| $\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}$ | Partial equation operator preserving inputs and collecting defined tensors |
| $\textcolor{#398B83}{\mathop{\mathrm{Input}}\nolimits}_{\textcolor{#5688C7}{\Sigma}},\textcolor{#398B83}{\mathop{\mathrm{Output}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}$ | Value environments on the program's designated input and output identifiers |
| $\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P})$ | Well-typed inputs admitting exactly one complete model |
| $\mathbf{1}_{\textcolor{#9D75C4}{Q}}$ | Iverson value of predicate $\textcolor{#9D75C4}{Q}$ |
| $\textcolor{#398B83}{\delta}_J$ | Equality-indicator tensor on $J\times J$ |
| $\mathbf{1}_J$ | All-ones tensor on coordinate domain $J$ |
| $\textcolor{#398B83}{\mathcal{D}}_f$ | Domain of definition of primitive $f$ |
| $H_l$ | Logical history slice $H[:,l]$ |
| $\textcolor{#398B83}{\llbracket}\cdot\textcolor{#398B83}{\rrbracket}$ | Interpretation brackets, with parameters as specified |
| $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ | Complete environments satisfying the collected equations on inputs $\textcolor{#398B83}{\eta}$ |

### Reference execution and readiness

| Symbol | Meaning |
| --- | --- |
| $\textcolor{#A87C28}{\sigma}$ | Partial store of available coordinate values |
| $\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu}),\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})$ | Read footprints of an expression instance and an occurrence |
| $\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a),r$ | Coordinate dependency set and strictly increasing dependency rank |
| $\textcolor{#A87C28}{\sigma}\textcolor{#A87C28}{\sqsubseteq}\textcolor{#398B83}{\rho}$ | The complete environment agrees with every published store value |
| $\textcolor{#A87C28}{\mathop{\mathrm{Eval}}\nolimits}_{\textcolor{#A87C28}{\sigma}}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})$ | Expression result from an available footprint, independent of complete extension |
| $\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U}$ | Defined-coordinate accumulators and pending occurrence set |
| $\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ | Initial store, zero accumulators, and all pending occurrences |
| $\textcolor{#A87C28}{\mathsf{Failed}}(\textcolor{#9D75C4}{o},\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$ | Terminal undefined-contribution error with its occurrence and state |
| $\textcolor{#A87C28}{\mu}$ | Number of pending occurrences plus unpublished defined coordinates |
| $\textcolor{#A87C28}{\mathsf{pub}}(a),\textcolor{#A87C28}{\mathsf{acc}}(a)$ | Published-value and unpublished-accumulator resource identities |
| $\textcolor{#A87C28}{\mathop{\mathrm{Need}}\nolimits}_{\mathrm{pub}}(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{U})$ | Published coordinates required by remaining contributions or outputs |
| $\textcolor{#A87C28}{\mathsf{Conf}},\textcolor{#A87C28}{\longrightarrow},\textcolor{#A87C28}{\Downarrow}$ | Machine configuration, execution-step relation, and successful termination |

### Compiled execution and physical representation

| Symbol | Meaning |
| --- | --- |
| $\textcolor{#C16C86}{\mathcal{B}},m_{\textcolor{#C16C86}{\beta}}$ | Physical buffer identifiers and their capacities |
| $\textcolor{#C16C86}{\mathop{\mathrm{Slot}}\nolimits}_{\textcolor{#C16C86}{\mathcal{B}}},\textcolor{#C16C86}{\xi}$ | Physical slot set and a slot $(\textcolor{#C16C86}{\beta},k)$ |
| $\textcolor{#C16C86}{M}$ | Partial exact-value memory on physical slots |
| $\textcolor{#C16C86}{\Pi},\textcolor{#C16C86}{\kappa}_t$ | Execution plan and a kernel command with logical annotations |
| $\textcolor{#C16C86}{\mathsf{Accumulate}}(G),\textcolor{#C16C86}{\mathsf{Publish}}(B),\textcolor{#C16C86}{\mathsf{Storage}}(\textcolor{#C16C86}{\theta})$ | Batched contribution, block publication, and representation-only action contracts |
| $\textcolor{#C16C86}{\mathsf{C}},\textcolor{#C16C86}{\mathsf{pc}},\textcolor{#C16C86}{\chi}$ | Concrete state, command position, and plan control/layout metadata |
| $\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}$ | Partial resource-to-slot layout view |
| $\textcolor{#C16C86}{\mathcal{R}}_{\textcolor{#C16C86}{\Pi}}$ | Concrete/reference representation relation |
| $\textcolor{#C16C86}{\mathop{\mathrm{Start}}\nolimits}_{\textcolor{#C16C86}{\Pi}},\textcolor{#C16C86}{\mathop{\mathrm{Decode}}\nolimits}_{\textcolor{#C16C86}{\Pi}}$ | Concrete initialization and whole-output decoding |
| $\textcolor{#9D75C4}{P}\vdash\textcolor{#C16C86}{\Pi}\ \textcolor{#C16C86}{\mathsf{valid}}$ | Valid plan: certified schedule, representation, and kernel behavior (Definition 31.1) |
| $\textcolor{#C16C86}{\longrightarrow}_{\textcolor{#C16C86}{\Pi}},\textcolor{#C16C86}{\Downarrow}_{\textcolor{#C16C86}{\Pi}}$ | Concrete plan-step and decoded successful-execution relations |
| $\textcolor{#C16C86}{\mathsf{PlanFailed}}(\textcolor{#9D75C4}{o})$ | Terminal concrete failure matched to an undefined source occurrence |

## References and related documents

- Pedro Domingos, [*Tensor Logic: The Language of AI*](https://arxiv.org/html/2510.12269v3).
  Its additive convention motivates this specification; the definitions and
  implementation correspondence here must be stated independently.
- [*The Syntax and Semantics of einsum*](https://arxiv.org/html/2509.20020).
  Sections [3](#3-axes-index-variables-and-valuations)-[4](#4-tensor-signatures-coordinates-and-values) provide the pure-einsum syntax and global-position semantics;
  Sections [5](#5-environments-and-stores)-[7](#7-free-indices-contraction-and-broadcasting) supply algebraic, nesting, delta, and neutral-operand results.
  [Section 17](#17-pure-einsum-semantics-and-transformation-foundations) adapts the relevant foundations to this document's conventions.
- [Tensor logic and einsum](../einsum_tensor_logic.md).
- [Integer constants and affine index arithmetic](../index_arithmetic.md).
- [Iteration in tensor logic](../iteration.md).

Related repository documents describe existing designs or implementations.
They are context, not substitutes for the definitions in this specification.

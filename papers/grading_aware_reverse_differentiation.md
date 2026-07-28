# Grading-Aware Reverse Differentiation for Tensor Logic

**From a formal language of forward tensor programs to certified differentiable programming**

This note develops a proposed next step for the tensor-logic and `D`-graded colored-PROP framework: a **grading-aware reverse derivative**. The aim is not merely to implement automatic differentiation inside Lean, nor to reproduce PyTorch autograd. The aim is to make differentiation a structure-preserving transformation of tensor-logic programs and to prove that the generated backward program computes the mathematical vector-Jacobian product of the forward program.

The central claim is:

> The framework will be substantially more valuable to machine-learning researchers when it can certify that compilation, lifting, reindexing, parameter sharing, program rewrites, and reverse differentiation agree both on forward values and on parameter gradients.

The word **grading-aware** is essential. An axis in tensor logic can mean an independent batch dimension, an index transformed by an affine map, a contraction dimension, a shared-parameter use, or a causal iteration dimension. Reverse differentiation must treat these structures differently. A backend AD system can often recover the right numerical answer from lowered code, but it does not expose or prove the structural reason that the answer is right.

This document first explains the gap in the current framework, then defines the proposed structure, develops its laws through representative examples, and ends with a staged formalization and implementation program.

---

## Contents

1. [Part I. Motivation and scope](#part-i-motivation-and-scope)  
   What is missing, what PyTorch already provides, and why a source-level theory may still matter.
   - [I.1 The opportunity](#i1-the-opportunity)
   - [I.2 Why not rely entirely on PyTorch autograd?](#i2-why-not-rely-entirely-on-pytorch-autograd)
2. [Part II. Mathematical core](#part-ii-mathematical-core)  
   Reverse differentiation, the four grading-aware distinctions, and the central lift law.
   - [II.1 Ordinary reverse differentiation](#ii1-ordinary-reverse-differentiation)
   - [II.2 What makes reverse differentiation grading-aware](#ii2-what-makes-reverse-differentiation-grading-aware)
   - [II.3 The central lift law](#ii3-the-central-lift-law)
3. [Part III. Applications and research agenda](#part-iii-applications-and-research-agenda)  
   Worked models, routing boundaries, and research questions enabled by the framework.
   - [III.1 Integrated model examples](#iii1-integrated-model-examples)
   - [III.2 Data-dependent routing](#iii2-data-dependent-routing)
   - [III.3 Machine-learning research questions](#iii3-machine-learning-research-questions-enabled-by-the-framework)
4. [Part IV. Formalization target](#part-iv-formalization-target)  
   The proposed interface, correctness theorem, and differentiability boundaries.
   - [IV.1 First-class cotangents and backward programs](#iv1-first-class-cotangents-and-backward-programs)
   - [IV.2 A proposed categorical interface](#iv2-a-proposed-categorical-interface)
   - [IV.3 Semantic adequacy and the target theorem](#iv3-semantic-adequacy-and-the-target-theorem)
   - [IV.4 Differentiability boundaries](#iv4-differentiability-boundaries)
5. [Part V. Implementation roadmap and payoff](#part-v-implementation-roadmap-and-payoff)  
   A staged implementation program, the broader non-AD research agenda, and the intended payoff.
   - [V.1 Research and implementation program](#v1-research-and-implementation-program)
   - [V.2 Broader opportunities beyond differentiation](#v2-broader-opportunities-beyond-differentiation)
   - [V.3 How the broader agenda reinforces grading-aware AD](#v3-how-the-broader-agenda-reinforces-grading-aware-ad)
   - [V.4 Prioritization](#v4-prioritization)
   - [V.5 Research payoff](#v5-research-payoff)

---

## Part I. Motivation and scope

This part separates the practical motivation from the mathematical proposal. It first identifies the
current semantic gaps, then asks whether PyTorch autograd already solves enough of the problem.

### I.1 The opportunity

The existing framework already has much of the forward-language substrate required for a serious differentiable-programming system:

- tensor programs are represented compositionally as morphisms;
- tensor products represent parallel composition;
- `D`-graded lifting distinguishes an operation's active axes from axes over which it is broadcast;
- affine index maps describe gather, scatter, convolution, slicing, diagonalization, and permutation;
- the tensor-logic DSL compiles and executes contractions, predicates, nonlinearities, normalization, scatter, and finite scans;
- `Algebra` describes structure-preserving interpretation into a target category;
- `ParaAlgebra` describes parameterized morphisms and weight tying;
- the Lean bridge proves important structural results, including well-formedness of compiled programs.

These are unusually strong foundations. However, three pieces remain disconnected.

#### I.1.1 The abstract graded structure is not yet a proved concrete model

The flagship instance

```lean
DGradedColoredPROP StObj BrObj
```

has a concrete shape map, but its lift action, distributivity maps, coherence laws, and broadcast-generation property remain deferred in `LeanNCD/Instances/StBr.lean`. The generic theorems therefore describe the intended model without yet proving that the concrete `St`/`Br` implementation satisfies it.

#### I.1.2 The categorical algebra and executable evaluator are separate

`Algebra` and `ParaAlgebra` state strong and meaningful laws, but the executable `DenseTensor` evaluator is not currently an instance of those abstractions. Conversely, the evaluator computes many useful ML programs but there is no end-to-end theorem identifying its result with the interpretation of the realized categorical morphism.

To state that missing theorem precisely, fix the following quantities:

- $p : \mathrm{TLProgram}$ is a tensor-logic abstract-syntax tree whose declarations and statements pass the compiler's rank, dtype, scheduling, routing, and well-formedness checks.
- $x : \mathrm{InputEnv}(p)$ is a concrete input environment: in the current evaluator, a `HashMap String DenseTensor` assigning a correctly shaped tensor to every external input name of $p$.
- $\operatorname{eval}(p,x)$ is `TLProgram.eval`: the executable reference semantics. It compiles $p$ to a `ScheduledProgram`, infers concrete axis sizes from $x$, executes the statements and scans, and returns an environment containing both the inputs and all computed tensors. In the equation below, it is understood to be projected to the declared outputs of $p$.
- $\operatorname{compile}(p)$ is the successful full compiler pipeline from `TLProgram` to the routed presentation `ThreadedComposed`: UID assignment, declaration resolution, rank and dtype checking, arithmetic lowering, scan finalization, nonlinear splitting, scheduling, and routing.
- $\operatorname{realize}$ maps a well-formed `ThreadedComposed` presentation to a typed categorical morphism

  $$
  \operatorname{realize}(\operatorname{compile}(p))
  :
  \operatorname{Dom}(p)
  \longrightarrow
  \operatorname{Cod}(p)
  $$

  in `Br`. It replaces presentation-level axes, weaves, reindexings, generators, and routing wires with their formal `St`/`Br` counterparts and composes them into one `BrMorph`.
- $\llbracket f \rrbracket$ denotes the concrete denotation of a categorical morphism $f$ under a tensor algebra

  $$
  F : \mathrm{Br} \longrightarrow \mathrm{Tensor},
  $$

  so $\llbracket f \rrbracket = F(f)$ is the executable tensor function represented by $f$. Here $\mathrm{Tensor}$ names the prospective semantic target category of concrete tensor spaces and functions; it is not an existing Lean definition. For example, a `DenseTensor` algebra maps an array object of shape $[m,n]$ to the concrete tensor space $\mathbb R^{m\times n}$ and maps a `Br` matrix-multiplication morphism to the function $(A,B)\mapsto AB$. It maps categorical composition to function composition, tensor product to parallel execution, and a lift over a batch grade to batched execution. Consequently, $\llbracket f \rrbracket(x)$ means applying that concrete tensor function to the input environment $x$. The current evaluator approximates this interpretation using `Float`, but is not yet a proved `Algebra` instance.

The missing forward theorem has the schematic form

$$
\operatorname{eval}(p, x)
=
\llbracket \operatorname{realize}(\operatorname{compile}(p)) \rrbracket(x).
$$

This equation suppresses the compiler's `Except`/state plumbing, the proof that successful compilation produces a well-formed presentation, and the projection of the evaluator's full environment to the program outputs. Its content is **semantic adequacy**: direct DSL evaluation and categorical realization followed by algebraic interpretation denote the same function on every valid input.

#### I.1.3 Training semantics is delegated to the backend

The PyTorch path ultimately relies on AOTAutograd to trace a backward computation. That is useful engineering, but it leaves the framework's strongest mathematical structure unused during training. In particular, the framework itself does not currently state or prove:

- how a gather becomes scatter-add in reverse;
- when a batch axis is retained and when it is reduced;
- how gradients from tied parameters are accumulated;
- how reverse differentiation interacts with a `D`-lift;
- how a scan becomes a reverse scan;
- when a rewrite preserves gradients rather than only shapes or forward values.

The proposed capability closes this gap.

### I.2 Why not rely entirely on PyTorch autograd?

If the only objective is to train tensor-logic models efficiently, lowering them to PyTorch and
using PyTorch autograd may be sufficient. PyTorch already supplies mature reverse rules for
contractions, broadcasting, reductions, gathers, scatter-adds, shared parameters, and recurrent
computations. Reimplementing those rules in Lean merely to reproduce the same numerical gradients
would offer little practical benefit.

The case for grading-aware reverse differentiation is therefore not that it should replace PyTorch
as an execution engine. Its value is that it supplies a **source-level specification and
verification layer** for differentiation.

#### I.2.1 What PyTorch differentiates

Let $p$ be a tensor-logic program and let

$$
L(p)
$$

denote the PyTorch computation graph produced by lowering $p$. PyTorch autograd computes the VJP
of the function represented by that graph:

$$
D\llbracket L(p)\rrbracket_{\mathrm{Torch}}(x)^{\mathsf T}\bar y.
$$

This can be numerically correct even when $L$ contains a compiler error. Autograd differentiates
the graph it receives; it does not establish that the graph denotes the original tensor-logic
program. The missing forward obligation is

$$
\llbracket L(p)\rrbracket_{\mathrm{Torch}}
=
\llbracket p\rrbracket,
$$

and the corresponding reverse obligation is

$$
D\llbracket L(p)\rrbracket_{\mathrm{Torch}}(x)^{\mathsf T}\bar y
=
D\llbracket p\rrbracket(x)^{\mathsf T}\bar y.
$$

For example, lowering might introduce an incorrect permutation, reduce the wrong axis, use the
wrong affine gather map, or accidentally duplicate an intended shared parameter. PyTorch can
correctly differentiate each resulting operation while still computing the derivative of the wrong
function.

PyTorch also sees tensor operations after the source structure has been encoded into a graph. It
does not know, as tensor-logic facts, that:

- an axis came from an independent $D$-grade rather than from a contraction or recurrence;
- a gather arose from a particular affine index morphism;
- two parameter uses represent intentional weight tying;
- a transformation is justified by a colored-PROP equation;
- a scan has a distinguished causal dependency;
- a hard route has been assigned a particular gradient estimator.

Autograd often reconstructs the correct numerical accumulation from the lowered operators, but it
does not expose or prove the source-level reason for that accumulation.

#### I.2.2 What grading-aware differentiation adds

**End-to-end correctness.** A proved source-level reverse transformation can connect the original
program directly to its mathematical VJP:

$$
\llbracket R[p]\rrbracket(x,\bar y)
=
D\llbracket p\rrbracket(x)^{\mathsf T}\bar y.
$$

Combined with a lowering theorem, this distinguishes two questions that backend AD alone conflates:
whether the backend correctly differentiates its graph, and whether that graph correctly implements
the source program.

**Structural reverse laws.** The backward behavior of a program can be derived from its formal
construction:

| Forward structure | Required reverse structure |
| --- | --- |
| independent lift | independently lifted VJP |
| gather | additive pushforward, usually scatter-add |
| copying or shared use | cotangent addition |
| deletion | zero cotangent |
| scan | residual-aware reverse scan |
| permutation | inverse permutation |

These are reusable laws of the language rather than facts left implicit in one generated backend
graph. In particular, they make clear why a broadcast is reversed by a reduction, why an
overlapping gather requires collision sums, and why tied parameter uses contribute to one
cotangent.

**Certified rewrites.** If a tensor-logic optimization proves

$$
p\equiv q,
$$

then a compatible reverse theory can establish

$$
R[p]\equiv R[q].
$$

This supports gradient-preserving contraction reordering, fusion, layout changes, batching, and
routing transformations. Differentiating both lowered graphs with PyTorch gives two backward
computations, but does not by itself prove that the source rewrite or either lowering is valid.

**Source-level diagnostics.** The framework can report errors in the concepts used to write and
transform the program: a cotangent dropped an independent grade, a broadcast was not reversed by a
reduction, a shared parameter failed to accumulate contributions, or a discrete route has no
declared derivative policy. Such explanations are more informative than discovering the problem
only through a generated graph, a shape error, or a numerical gradient test.

**Backend independence.** One reverse semantics can be implemented by PyTorch, JAX, XLA, custom
kernels, or a Lean evaluator. Agreement with the source specification can then be established
separately for each backend, instead of allowing each backend to define the meaning of
differentiation for the language.

**Nonstandard gradings.** The benefit grows for graph indices, sparse or ragged layouts,
distributed sharding, causal streams, and other future choices of $D$. In such settings the
framework must specify which forward reindexings admit cotangent pushforwards and what those
pushforwards are. A general-purpose backend can execute a chosen implementation, but it cannot
infer the intended mathematics of a newly introduced grading.

#### I.2.3 What it does not add

Grading-aware differentiation does not inherently produce more accurate gradients, faster kernels,
or better optimization than PyTorch. For ordinary dense differentiable programs with a trusted
lowering, it may compute exactly the same VJP at substantially greater formalization cost. It is
most valuable when the project intends to provide one or more of:

- formal guarantees connecting source programs, compiler transformations, and gradients;
- proof-producing source-level optimization;
- precise semantics for sharing, reindexing, scans, and routing;
- portability across several execution backends;
- new graded models whose reverse transport is not already standardized.

If none of these is a project goal, delegating differentiation to PyTorch is the simpler engineering
choice.

#### I.2.4 Recommended division of responsibility

The strongest architecture is hybrid:

1. tensor logic defines the source-level forward and grading-aware reverse semantics;
2. the compiler proves, or is validated against, preservation of forward and reverse meaning;
3. PyTorch continues to generate and execute optimized backward graphs;
4. PyTorch autograd serves as both an execution mechanism and an independent numerical oracle.

In this architecture, grading-aware differentiation is the **specification and correctness layer**,
while PyTorch remains the **execution engine**. The purpose is not to compete with autograd, but to
state and verify what autograd is supposed to compute after a structured tensor program has passed
through the compiler.

---

## Part II. Mathematical core

This part defines ordinary reverse differentiation first, then isolates the extra obligations imposed
by graded tensor structure. It culminates in the lift law that characterizes independent grades.

### II.1 Ordinary reverse differentiation

Let $C$ be the category of tensor-program objects and morphisms. Its objects form the collection $\operatorname{Ob}(C)$, and $\operatorname{Hom}_C(X,Y)$ denotes the morphisms from an object $X$ to an object $Y$. In the present framework, commonly $C=\mathrm{Br}$: objects describe typed tensor interfaces and morphisms describe tensor programs. The monoidal product $\otimes$ places objects or programs in parallel.

Let

$$
F:C\longrightarrow\mathrm{Tensor}
$$

be a tensor algebra that interprets categorical tensor programs as concrete tensor spaces and functions. As in [§I.1.2](#i12-the-categorical-algebra-and-executable-evaluator-are-separate), write

$$
\llbracket X\rrbracket=F(X)
\quad\text{and}\quad
\llbracket f\rrbracket=F(f)
$$

for the denotations of an object and a morphism.

Now fix objects $X,Y\in\operatorname{Ob}(C)$ and a morphism

$$
f\in\operatorname{Hom}_C(X,Y),
\qquad
f:X\longrightarrow Y.
$$

Assume that $\llbracket X\rrbracket$ and $\llbracket Y\rrbracket$ are finite-dimensional real tensor spaces and that

$$
\llbracket f\rrbracket:
\llbracket X\rrbracket
\longrightarrow
\llbracket Y\rrbracket
$$

is differentiable. A **primal input** is a concrete tensor value $x\in\llbracket X\rrbracket$, and its forward output is

$$
y=\llbracket f\rrbracket(x)\in\llbracket Y\rrbracket.
$$

Write $T_x\llbracket X\rrbracket$ for the tangent space of the interpreted input space at $x$ and $T_y\llbracket Y\rrbracket$ for the tangent space of the interpreted output space at $y$. A tangent vector represents an infinitesimal perturbation of the corresponding primal value. For a finite-dimensional vector space, every tangent space is canonically isomorphic to the vector space itself; the base-point notation is retained because the derivative depends on $x$.

The derivative, or Jacobian as a linear map, is

$$
D\llbracket f\rrbracket(x)
:
T_x\llbracket X\rrbracket
\longrightarrow
T_y\llbracket Y\rrbracket.
$$

Write

$$
T_x^*\llbracket X\rrbracket
=
\operatorname{Hom}_{\mathbb R}
\bigl(T_x\llbracket X\rrbracket,\mathbb R\bigr)
$$

and

$$
T_y^*\llbracket Y\rrbracket
=
\operatorname{Hom}_{\mathbb R}
\bigl(T_y\llbracket Y\rrbracket,\mathbb R\bigr)
$$

for the **dual cotangent spaces**. A cotangent is therefore a linear functional: an element $\bar x\in T_x^*\llbracket X\rrbracket$ consumes an infinitesimal input perturbation $v\in T_x\llbracket X\rrbracket$ and returns the scalar first-order sensitivity $\bar x(v)\in\mathbb R$. Tangent vectors describe directions in which a value can change; cotangents describe how a scalar objective responds to those directions.

For finite-dimensional Euclidean tensor spaces, the inner product identifies each space with its dual. Under this identification, a cotangent can be stored as an array with the same shape as its primal tensor, which is why ML implementations often call both tangent vectors and cotangents “gradients.” They remain conceptually different: a tangent propagates a perturbation forward through $D\llbracket f\rrbracket(x)$, whereas a cotangent propagates a sensitivity backward through its adjoint.

Reverse-mode AD uses that adjoint:

$$
D\llbracket f\rrbracket(x)^{\mathsf T}
:
T_y^*\llbracket Y\rrbracket
\longrightarrow
T_x^*\llbracket X\rrbracket.
$$

Here ${}^{\mathsf T}$ denotes the adjoint under the chosen Euclidean inner products. Given an output cotangent $\bar y\in T_y^*\llbracket Y\rrbracket$, the vector-Jacobian product is the input cotangent $\bar x\in T_x^*\llbracket X\rrbracket$ defined by

$$
\bar x
=
D\llbracket f\rrbracket(x)^{\mathsf T}\bar y.
$$

To represent this construction inside $C$, introduce a cotangent-object assignment

$$
\mathrm{Cot} : \operatorname{Ob}(C) \longrightarrow \operatorname{Ob}(C).
$$

The object $\mathrm{Cot}(X)$ represents cotangents to values of $X$. For ordinary real tensors, its interpretation has the same shape as $\llbracket X\rrbracket$, although it is useful to keep primal and cotangent roles distinct in the formal interface. The symbol $R$ denotes the proposed reverse differential combinator; for each $f:X\to Y$, it produces a morphism

$$
R[f] :
X \otimes \mathrm{Cot}(Y)
\longrightarrow
\mathrm{Cot}(X),
$$

with semantics

$$
\llbracket R[f] \rrbracket(x,\bar y)
=
D\llbracket f\rrbracket(x)^{\mathsf T}\bar y.
$$

For a linear map $L:X\to Y$, the derivative is the same at every input, so reverse differentiation can assign the context-free reversed linear map

$$
L^{\mathsf T}:\mathrm{Cot}(Y)\longrightarrow\mathrm{Cot}(X).
$$

This assignment is genuinely contravariant:

$$
(L;M)^{\mathsf T}=M^{\mathsf T};L^{\mathsf T}.
$$

For a nonlinear $f$, however, the Jacobian changes with the primal input. There is no single map $\mathrm{Cot}(Y)\to\mathrm{Cot}(X)$ determined by the types $X$ and $Y$ that computes every backward pass; the required map is the family

$$
\bar y
\longmapsto
D\llbracket f\rrbracket(x)^{\mathsf T}\bar y,
$$

indexed by the particular primal point $x$. For example, if $f(x)=x^2$, then the reverse map is

$$
\bar y\longmapsto 2x\,\bar y,
$$

which cannot be evaluated without knowing $x$. Under composition, the reverse chain rule also needs the intermediate primal value:

$$
D\bigl(\llbracket g\rrbracket\circ\llbracket f\rrbracket\bigr)(x)^{\mathsf T}\bar z
=
D\llbracket f\rrbracket(x)^{\mathsf T}
\left(
D\llbracket g\rrbracket\bigl(\llbracket f\rrbracket(x)\bigr)^{\mathsf T}\bar z
\right).
$$

Suppose one tried to define a context-free reverse-arrow operator, written ${}^{\dagger}$, that assigned to every morphism $f:X\to Y$ a reversed morphism

$$
f^\dagger:\mathrm{Cot}(Y)\longrightarrow\mathrm{Cot}(X)
$$

using only $f$, with no primal input or saved residual. For linear maps this notation can mean the adjoint, so $f^\dagger=f^{\mathsf T}$. Arbitrary nonlinear maps do not admit such an operator: their backward computation changes with the primal point. The notation $f^\dagger$ here is therefore a hypothetical construction used to state what fails, not the proposed reverse combinator $R[f]$, whose input includes the primal value. The backward computation must retain that primal input or equivalent residual values from the forward pass. Reverse differentiation is therefore better modeled as a **reverse differential combinator**, or operationally as a residualizing transformation:

$$
f : X \longrightarrow Y
\quad\leadsto\quad
\widetilde f :
X \longrightarrow Y \otimes S_f,
$$

$$
b_f :
S_f \otimes \mathrm{Cot}(Y)
\longrightarrow
\mathrm{Cot}(X),
$$

where $\widetilde f$ is the residual-producing forward morphism, $S_f$ is the type of saved residuals needed by the backward pass, and $b_f$ is the backward morphism that consumes those residuals and an output cotangent. For example, sigmoid can save its output, while matrix multiplication may save one or both operands.

The simpler notation $R[f](x,\bar y)$ will be used below when the residual policy is not the point at issue.
Likewise, equations involving concrete values suppress denotation brackets when the types make the
interpretation unambiguous: $f(x)$ abbreviates $\llbracket f\rrbracket(x)$, and
$R[f](x,\bar y)$ abbreviates $\llbracket R[f]\rrbracket(x,\bar y)$. Objects and morphisms
remain categorical; $x$, $y$, and barred variables denote values in their concrete interpretations.

### II.2 What makes reverse differentiation grading-aware

Let $D$ be the index PROP, whose objects are grades such as axis collections and whose morphisms are reindexings. Let $C$ be the colored PROP of tensor-program objects and operations, equipped with a $D$-grading and lift action

$$
\mathbin{\circledast} :
C \times D^{\mathrm{op}} \longrightarrow C.
$$

For a grade $P \in \operatorname{Ob}(D)$, an object $X\in\operatorname{Ob}(C)$, and a morphism $f:X\to Y$ in $C$, write

$$
X \mathbin{\circledast} P
$$

for the object $X$ independently replicated or broadcast over $P$, and

$$
[f,P] :
X \mathbin{\circledast} P
\longrightarrow
Y \mathbin{\circledast} P
$$

for the corresponding pointwise lift of $f$.

> **Implementation note: axis order.** This convention is important when translating the abstract
> laws into Lean, but is not needed for their logical development. At the executable DSL level, the
> axes represented abstractly by the grade $P$ do not receive a privileged position in a
> `DenseTensor`: its `shape : List Nat` follows the axis order written in the tensor-logic program.
> When $P$ is a batch grade, this means that its batch axis need not appear first. For example,
>
> ```text
> Y[b, i, j] := A[b, i, k] · X[b, k, j]
> ```
>
> has shape order $[b,i,j]$ because that is the left-hand-side order; another order may be written
> explicitly. By contrast, the planned concrete `St`/`Br` action defines a literal categorical lift
> by appending the grade axes:
> $\operatorname{shape}(X\mathbin{\circledast}P)=\operatorname{shape}(X)\mathbin{+\!\!+}P$,
> where $+\!\!+$ is list concatenation. A symmetry or
> braid may move those axes, but the permutation is not definitional equality. Regardless of
> presentation, a cotangent preserves its primal's axis order: if $Y$ has shape
> $[a_1,\ldots,a_r]$, then $\bar Y$ has the same shape. Thus a leading $b$ in later coordinate
> formulas is a readable DSL presentation, not a claim that Lean always places batch first.

A reverse derivative is **grading-aware** when it respects the semantics carried by this action rather than treating every tensor dimension as an undifferentiated list coordinate. Four distinctions matter.

#### II.2.1 Shape and degree

The reverse transformation must produce a well-typed morphism and preserve the expected shape and grade of cotangents.

**Example (a lifted linear map).** Let $f:\mathbb R^d\to\mathbb R^m$ be the linear map $f(x)=Wx$ for a fixed matrix $W\in\mathbb R^{m\times d}$, and lift it over a batch grade $B$ of size $n$. The lifted program has

$$
X\in\mathbb R^{d\times n},
\qquad
Y\in\mathbb R^{m\times n},
\qquad
Y_b=WX_b.
$$

Here $b\in\{1,\ldots,n\}$ indexes the appended batch grade, $X_b=X[:,b]\in\mathbb R^d$ is the input-feature slice at batch position $b$, and $Y_b=Y[:,b]\in\mathbb R^m$ is the corresponding output-feature slice.

Given an output cotangent $\bar Y\in\mathbb R^{m\times n}$, with the same axis order as $Y$, the input cotangent is

$$
\bar X_b=W^{\mathsf T}\bar Y_b,
\qquad
\bar X\in\mathbb R^{d\times n}.
$$

The feature dimension changes from $m$ back to $d$, while the appended batch grade $B$ is retained. A reverse transformation that dropped $B$, moved it without an explicit symmetry, merged it with a feature axis, or returned shape $m\times n$ for $\bar X$ would be ill-typed.

**Required law (cotangents preserve tensor structure and grade).** The cotangent assignment must
come with coherent isomorphisms

$$
\chi_{X,Y}:
\mathrm{Cot}(X\otimes Y)
\overset{\sim}{\longrightarrow}
\mathrm{Cot}(X)\otimes\mathrm{Cot}(Y)
$$

The notation

$$
A\overset{\sim}{\longrightarrow}B
$$

means an **isomorphism** from $A$ to $B$: a morphism $u:A\to B$ for which there is an
inverse morphism $u^{-1}:B\to A$ satisfying

$$
u;u^{-1}=\mathrm{id}_A
\qquad\text{and}\qquad
u^{-1};u=\mathrm{id}_B.
$$

The tilde above the arrow does not mean “approximately.” It says that the two objects may not be
definitionally or literally equal, but they are reversibly identifiable within the category. Thus
$\chi_{X,Y}$ converts a cotangent of the parallel object $X\otimes Y$ into a pair consisting of
an $X$-cotangent and a $Y$-cotangent, and $\chi_{X,Y}^{-1}$ combines such a pair back into the
cotangent of $X\otimes Y$. Calling these isomorphisms **coherent** additionally requires these
conversions to agree with associativity, units, symmetries, and the other structural maps, rather
than being arbitrary reversible encodings.

and

$$
\kappa_{X,P}:
\mathrm{Cot}(X\mathbin{\circledast}P)
\overset{\sim}{\longrightarrow}
\mathrm{Cot}(X)\mathbin{\circledast}P.
$$

The first law says that cotangents split across parallel wires. The second says that taking
cotangents preserves an independent grade. Within the finite-dimensional real tensor fragment,
where a cotangent is represented by an array with the same axes as its primal, they require at the
shape level

$$
\operatorname{sh}^*(\mathrm{Cot}(X))
\cong
\operatorname{sh}^*(X)
$$

and, compatibly,

$$
\operatorname{sh}^*
\bigl(\mathrm{Cot}(X\mathbin{\circledast}P)\bigr)
\cong
\operatorname{sh}^*(\mathrm{Cot}(X))\otimes P.
$$

Here $\operatorname{sh}^*$ is the object-level shape map from `C` to `D`, extended over tensor
products. The isomorphisms $\chi$ and $\kappa$ must satisfy the usual associativity, unit, and
symmetry coherences, so splitting or reordering a composite object cannot change the resulting
cotangent type. Finally, for every $f:X\to Y$, the reverse morphism must have the well-typed form

$$
R[f]:
X\otimes\mathrm{Cot}(Y)
\longrightarrow
\mathrm{Cot}(X).
$$

Section II.3 adds the corresponding morphism-level condition that $R$ commute with the lift via
$\kappa$.

#### II.2.2 Reindexing

An index transformation used for a forward read must be transposed in the backward program. The reverse of gather is generally scatter-add, not gather.

**Example (a repeated gather).** Let $A=\{0,1,2\}$ be one source axis of length three, and let
$x:A\to\mathbb R$ be a rank-one tensor on that axis. The notation
$x=(x_0,x_1,x_2)$ lists its three scalar entries, where $x_a=x[a]$ is the value at position
$a\in A$; $x_0,x_1,x_2$ are entries, not separate axes. Let $Q=\{0,1,2\}$ be an output axis and
let the index map $\eta:Q\to A$ be given by $\eta(0)=0$, $\eta(1)=0$, and $\eta(2)=2$. Thus the
gather selects source positions $(0,0,2)$ and produces

$$
y=(x_0,x_0,x_2).
$$

For a supplied output cotangent $\bar y=(\bar y_0,\bar y_1,\bar y_2)$, the correct input cotangent is

$$
\bar x
=
(\bar y_0+\bar y_1,\ 0,\ \bar y_2).
$$

This cotangent is unique under the standard Euclidean inner products. For an arbitrary input
perturbation $\delta x=(\delta x_0,\delta x_1,\delta x_2)$, the gather produces

$$
\delta y=(\delta x_0,\delta x_0,\delta x_2).
$$

The defining adjoint condition requires

$$
\langle\bar x,\delta x\rangle
=
\langle\bar y,\delta y\rangle
=
(\bar y_0+\bar y_1)\delta x_0
+0\,\delta x_1
+\bar y_2\delta x_2
$$

for every choice of $\delta x$. The Euclidean inner product is nondegenerate, so equality for all
perturbations determines each coefficient uniquely: the coefficients of $\delta x_0$,
$\delta x_1$, and $\delta x_2$ must be $\bar y_0+\bar y_1$, $0$, and $\bar y_2$, respectively.
Another result would be possible only after changing the inner product or using a degenerate
pairing.

The two reads of $x_0$ contribute additively to the same source position, while unread $x_1$
receives zero. Reusing the forward gather rule on the output cotangent would instead select
positions $(0,0,2)$ from $\bar y$ and produce

$$
G_\eta\bar y=(\bar y_0,\bar y_0,\bar y_2),
$$

not the required source cotangent
$S_\eta\bar y=(\bar y_0+\bar y_1,0,\bar y_2)$. It duplicates $\bar y_0$, discards
$\bar y_1$, and does not sum the two output positions that originated from $x_0$. More generally,
the forward gather has type $G_\eta:\mathbb R^A\to\mathbb R^Q$, whereas the reverse map must have
the opposite type $S_\eta:\mathbb R^Q\to\mathbb R^A$; the fact that $A$ and $Q$ both contain three
positions in this example only hides that type mismatch at the level of array length.

**Required law (reindexing reverses by the adjoint pushforward).** For every finite index map
$\eta:Q\to A$, let

$$
G_\eta:\mathbb R^A\longrightarrow\mathbb R^Q,
\qquad
(G_\eta x)[q]=x[\eta(q)]
$$

be its forward pullback, and define the additive pushforward

$$
S_\eta:\mathbb R^Q\longrightarrow\mathbb R^A,
\qquad
(S_\eta\bar y)[a]
=
\sum_{\substack{q\in Q\\\eta(q)=a}}\bar y[q].
$$

Reverse differentiation must satisfy

$$
R[G_\eta](x,\bar y)=S_\eta\bar y,
$$

or equivalently the adjoint law

$$
\langle G_\eta x,\bar y\rangle_Q
=
\langle x,S_\eta\bar y\rangle_A
$$

for every $x\in\mathbb R^A$ and $\bar y\in\mathbb R^Q$. Under nondegenerate Euclidean inner
products, this equation uniquely determines $S_\eta$.

The pushforwards must also respect identity and composition. If
$\theta:R\to Q$ is another index map, then

$$
S_{\mathrm{id}_A}=\mathrm{id}_{\mathbb R^A},
\qquad
S_{\eta\circ\theta}=S_\eta\circ S_\theta.
$$

Thus reversing a sequence of gathers reverses their order and composes their accumulating
pushforwards.

#### II.2.3 Sharing

Repeated use of one parameter is not the same as a family of independent parameters indexed by the same grade. The former requires gradient accumulation; the latter retains the grade.

**Example (shared versus per-example weights).** Let $b\in\{1,\ldots,n\}$ index a batch. If one matrix $W$ is shared across all examples,

$$
Y_b=WX_b,
$$

then its cotangent sums contributions from the whole batch:

$$
\bar W
=
\sum_{b=1}^{n}\bar Y_bX_b^{\mathsf T}.
$$

If instead each example has an independent matrix $W_b$,

$$
Y_b=W_bX_b,
\qquad
\bar W_b=\bar Y_bX_b^{\mathsf T}.
$$

The shared parameter has no batch axis and therefore receives a reduction over $b$; the independent parameter family retains that axis. Equal forward values at one choice of the $W_b$ do not make these parameterizations equivalent for training.

**Required law (duplication reverses to accumulation).** Let $\Theta$ be a parameter object and let

$$
\Delta_n:\Theta\longrightarrow\Theta^{\otimes n}
$$

be the $n$-fold diagonal that shares one parameter value across $n$ uses:

$$
\Delta_n(\theta)=(\theta,\ldots,\theta).
$$

Using

$$
\mathrm{Cot}(\Theta^{\otimes n})
\cong
\mathrm{Cot}(\Theta)^{\otimes n},
$$

the reverse derivative must satisfy

$$
R[\Delta_n]
\bigl(
\theta,
(\bar\theta_1,\ldots,\bar\theta_n)
\bigr)
=
\sum_{i=1}^{n}\bar\theta_i.
$$

Equivalently, the cotangent map induced by $\Delta_n$ is the $n$-ary addition morphism

$$
\Delta_n^\dagger
=
+_\Theta^{(n)}
:
\mathrm{Cot}(\Theta)^{\otimes n}
\longrightarrow
\mathrm{Cot}(\Theta).
$$

Here $\Delta_n^\dagger$ denotes the adjoint of the linear duplication map, and
$+_\Theta^{(n)}$ adds its $n$ cotangent inputs. For an independent parameter family
$\Theta^{\otimes n}$ there is no preceding diagonal, so the reverse result remains
$(\bar\theta_1,\ldots,\bar\theta_n)$ rather than being reduced.

More generally, if a model uses a reparameterization $\psi:\Theta'\to\Theta$, reverse
differentiation must obey the reverse chain rule

$$
\bar\theta'
=
D\llbracket\psi\rrbracket(\theta')^{\mathsf T}\bar\theta.
$$

The diagonal law is the sharing-specific instance of this condition.

#### II.2.4 Causality

A scan axis does not represent independent pointwise copies. Its reverse is a causally ordered reverse scan. Treating time as an ordinary lift would erase the recurrence dependency and produce an incorrect backward program.

**Example (a scalar recurrence).** Let

$$
h_{t+1}=a h_t+x_t,
\qquad
t=0,\ldots,T-1,
$$

where $a\in\mathbb R$ is shared across time, and suppose a loss supplies a final-state cotangent $\bar h_T$. The state cotangents must be computed backward:

$$
\bar h_t=a\,\bar h_{t+1},
\qquad
\bar x_t=\bar h_{t+1}.
$$

The parameter cotangent accumulates contributions from every transition:

$$
\bar a
=
\sum_{t=0}^{T-1}h_t\,\bar h_{t+1}.
$$

An independent pointwise lift over $t$ would miss the path from $h_t$ through every later state and could not produce this backward recurrence.

**Required law (reverse of scan is a backward fold of the step VJP).** Let $H$ be the state
object, $X$ the per-step input object, $\Theta$ a parameter object shared across time, and

$$
\phi:H\otimes X\otimes\Theta\longrightarrow H
$$

the transition morphism. A length-$T$ scan computes

$$
h_{t+1}
=
\llbracket\phi\rrbracket(h_t,x_t,\theta),
\qquad
t=0,\ldots,T-1.
$$

Let $c_t\in\mathrm{Cot}(H)$ be the direct state cotangent supplied by outputs or losses attached
at time $t$. In the final-state-only case, $c_T=\bar h_T$ and $c_t=0$ for $t<T$. After identifying
the cotangent of the step input with

$$
\mathrm{Cot}(H)
\otimes
\mathrm{Cot}(X)
\otimes
\mathrm{Cot}(\Theta),
$$

write the step VJP as

$$
R[\phi](h_t,x_t,\theta,a_{t+1})
=
(u_t,\bar x_t,g_t).
$$

Here $a_{t+1}$ is the total cotangent arriving from the future, $u_t$ is the contribution to the
previous state, $\bar x_t$ is the input cotangent at time $t$, and $g_t$ is that step's contribution
to the shared-parameter cotangent. The reverse scan is the backward recurrence

$$
a_T=c_T,
$$

$$
a_t=c_t+u_t,
\qquad
(u_t,\bar x_t,g_t)
=
R[\phi](h_t,x_t,\theta,a_{t+1}),
\qquad
t=T-1,\ldots,0,
$$

with parameter accumulation

$$
\bar\theta
=
\sum_{t=0}^{T-1}g_t.
$$

If $\operatorname{Scan}_T(\phi)$ denotes the forward scan morphism and
$\operatorname{RevScan}_T(R[\phi])$ denotes this residual-aware backward fold, the required
compatibility law is

$$
R[\operatorname{Scan}_T(\phi)]
\cong
\operatorname{RevScan}_T(R[\phi]),
$$

up to the coherence isomorphisms that arrange the state, input-sequence, parameter, and cotangent
wires. The right side consumes the forward states $h_0,\ldots,h_{T-1}$ as residuals, or recomputes
them under an explicitly proved checkpointing strategy.

These distinctions are structural. They are visible before choosing concrete floating-point values and should therefore be part of the categorical and compiler-level account.

### II.3 The central lift law

The simplest and most important compatibility condition is:

> Differentiating an independently lifted operation is equivalent to independently lifting its derivative.

Fix a morphism $f:X\to Y$ in $C$ and a grade $P\in\operatorname{Ob}(D)$. Let

$$
\kappa_{X,P} :
\mathrm{Cot}(X \mathbin{\circledast} P)
\overset{\sim}{\longrightarrow}
\mathrm{Cot}(X) \mathbin{\circledast} P
$$

be the coherence isomorphism identifying the cotangent of a lifted object with the lift of its cotangent. Let

$$
\delta_{X,Y,P} :
(X \otimes Y) \mathbin{\circledast} P
\overset{\sim}{\longrightarrow}
(X \mathbin{\circledast} P)
\otimes
(Y \mathbin{\circledast} P)
$$

be the existing distributor of the `D`-action, which separates a lifted tensor product into the tensor product of the two lifted objects. The symbol $\mathrm{id}_{X\circledast P}$ below is the identity morphism on $X\circledast P$, $\delta^{-1}$ and $\kappa^{-1}$ are inverse isomorphisms, and the semicolon denotes diagrammatic composition: first the morphism on the left, then the one on the right.

Using diagrammatic composition order, the desired law is

$$
\begin{aligned}
R\bigl([f,P]\bigr)
={}&
\bigl(
\mathrm{id}_{X\circledast P}
\otimes
\kappa_{Y,P}
\bigr)
\\
&\mathbin{;}
\delta^{-1}_{X,\mathrm{Cot}(Y),P}
\\
&\mathbin{;}
[R[f],P]
\\
&\mathbin{;}
\kappa^{-1}_{X,P}.
\end{aligned}
$$

Both sides have type

$$
(X \mathbin{\circledast} P)
\otimes
\mathrm{Cot}(Y \mathbin{\circledast} P)
\longrightarrow
\mathrm{Cot}(X \mathbin{\circledast} P).
$$

This equation is stronger than saying that two generated programs happen to return equal arrays. It states that reverse differentiation is compatible with the `D`-action itself.

For `D = St`, the law certifies familiar assumptions:

- a batch of elementwise operations has a batch of elementwise VJPs;
- a head-wise attention operation has a head-wise backward operation;
- a spatially lifted pointwise map differentiates independently at each spatial location.

It also establishes the boundary of the claim: the law applies to a genuine lift. It does not automatically apply to a contraction axis, a tied-parameter use, or a temporal recurrence.

---

## Part III. Applications and research agenda

This part moves from laws to consequences. It applies the structure to representative models,
marks the boundary at discrete routing, and develops the research program enabled by a complete
implementation.

### III.1 Integrated model examples

The following examples are ordered so that each introduces one genuinely new structural issue. Together they show why ordinary operator-by-operator AD is insufficient as the specification.

#### III.1.1 Independently lifted sigmoid

Let $i$ index feature coordinates and let $\sigma(u)=1/(1+e^{-u})$ be the logistic sigmoid. Start with the pointwise map

$$
f(x)_i=\sigma(x_i).
$$

Its reverse derivative is

$$
R[f](x,\bar y)_i
=
\bar y_i\,\sigma(x_i)\bigl(1-\sigma(x_i)\bigr).
$$

Here $\bar y_i$ is the supplied cotangent of the output coordinate and the equation defines the returned input cotangent at coordinate $i$.

Lift the operation over batch and head grades:

$$
Y_{bhi}=\sigma(X_{bhi}).
$$

Then

$$
\bar X_{bhi}
=
\bar Y_{bhi}Y_{bhi}(1-Y_{bhi}).
$$

No sum over $b$ or $h$ appears. Each position is independent, so the whole backward operation is the lift of the scalar or feature-wise backward operation:

$$
R\left[
[f,B\otimes H]
\right]
\cong
[R[f],B\otimes H].
$$

This is the canonical use of the central lift law.

#### III.1.2 Overlapping convolution

Let $b$ index batch elements, $o$ output positions, $k$ kernel offsets, $c_i$ input channels, and $c_o$ output channels. Let $X_{b,t,c_i}$ be the input activation at input position $t$, let $W_{c_o,c_i,k}$ be a kernel shared across batches and output positions, and let $Y_{b,o,c_o}$ be the output. Consider the one-dimensional convolution-like contraction

$$
Y_{b,o,c_o}
=
\sum_{k,c_i}
W_{c_o,c_i,k}
X_{b,o+k,c_i}.
$$

The forward read uses the affine map

$$
(b,o,k,c_i)
\longmapsto
(b,o+k,c_i).
$$

The activation cotangent is

$$
\bar X_{b,t,c_i}
=
\sum_{\substack{o,k,c_o\\t=o+k}}
\bar Y_{b,o,c_o}W_{c_o,c_i,k}.
$$

Here $\bar Y$ is the cotangent supplied for the convolution output; $\bar X$ and $\bar W$ are the activation and parameter cotangents returned by the reverse computation. Multiple windows can contribute to the same position $t$. Therefore, the reverse of the affine gather must be an accumulating scatter. An assignment-based scatter would silently lose contributions and compute an incorrect gradient.

The parameter cotangent is

$$
\bar W_{c_o,c_i,k}
=
\sum_{b,o}
\bar Y_{b,o,c_o}
X_{b,o+k,c_i}.
$$

This example combines all of the following:

- the batch grade is retained in $\bar X$;
- the batch and output-position grades are reduced in $\bar W$;
- the affine index map is transposed;
- overlap requires additive collision handling;
- sharing of $W$ across $b$ and $o$ determines the reduction axes.

The correct backward structure can therefore be derived from the forward weave, reindexing maps, contractions, and parameter placement.

#### III.1.3 Causal self-attention

For one attention head, let $q$ index query positions, $k$ key positions, $r$ the shared query/key feature coordinate, and $v$ the value feature coordinate. Let $d$ be the query/key feature dimension; let $Q_{qr}$, $K_{kr}$, and $V_{kv}$ be the query, key, and value tensors; and let $M_{qk}$ be a fixed structural mask, equal to $0$ on allowed pairs and $-\infty$ on disallowed pairs. Define the score tensor $S$, attention weights $A$, and output $O$ by

$$
S_{qk}
=
\frac{1}{\sqrt d}
\sum_r Q_{qr}K_{kr},
$$

$$
A_{qk}
=
\operatorname{softmax}_k(S_{qk}+M_{qk}),
$$

$$
O_{qv}
=
\sum_k A_{qk}V_{kv}.
$$

For the final contraction,

$$
\bar V_{kv}
=
\sum_q A_{qk}\bar O_{qv},
$$

$$
\bar A_{qk}
=
\sum_v \bar O_{qv}V_{kv}.
$$

Here $\bar O$ is the supplied output cotangent, while $\bar V$ and $\bar A$ are the cotangents propagated to $V$ and $A$. For each query $q$, the softmax VJP is

$$
\bar S_{qk}
=
A_{qk}
\left(
\bar A_{qk}
-
\sum_j A_{qj}\bar A_{qj}
\right).
$$

The score contraction then gives

$$
\bar Q_{qr}
=
\frac{1}{\sqrt d}
\sum_k \bar S_{qk}K_{kr},
$$

$$
\bar K_{kr}
=
\frac{1}{\sqrt d}
\sum_q \bar S_{qk}Q_{qr}.
$$

Batch and head axes are genuine independent grades, so the entire derivation lifts pointwise over them. Query, key, and feature axes belong to the elemental contractions and reductions.

For this fixed exact-mask semantics:

- no cotangent is produced for the predicate itself;
- masked entries contribute zero to the softmax and its VJP (a finite negative mask would instead
  define a different, nonzero approximation);
- the causal mask changes the respected symmetry on sequence positions, but it does not destroy independent lifting over batch or head.

A grading-aware proof can therefore certify that differentiating attention commutes with batching and head-wise lifting while still respecting the nontrivial sequence-axis structure.

#### III.1.4 Graph message passing

Let $V$ be a finite set of vertices and $E$ a finite set of directed edges. Let the graph have source and destination maps

$$
\operatorname{src},\operatorname{dst}:E\longrightarrow V.
$$

Let $X_v$ be the feature at vertex $v$, let $W$ be a parameter shared across edges, let $\phi$ be a differentiable message function, and let $Y_v$ be the aggregated output at vertex $v$. Consider

$$
Y_v
=
\sum_{\substack{e\in E\\\operatorname{dst}(e)=v}}
\phi(X_{\operatorname{src}(e)},W).
$$

The forward program:

1. gathers source features along $\operatorname{src}$;
2. computes one message per edge;
3. pushes messages along $\operatorname{dst}$;
4. sums messages in each destination fiber.

The reverse program:

1. gathers the supplied output cotangent $\bar Y_v$ from each destination onto its incoming edges;
2. applies $R[\phi]$ independently on edges;
3. pushes source-feature cotangents back along $\operatorname{src}$;
4. sums all cotangents that arrive at the same source vertex;
5. sums parameter cotangents over edges when $W$ is shared.

The essential law is again pullback/pushforward adjointness. This example also shows what a future generic-`D` implementation must provide: a graph grading is differentiable only when its reindexings have suitable cotangent pushforwards.

### III.2 Data-dependent routing

The lift and scan laws apply only to differentiable structure. Data-dependent discrete choices require an explicit policy.

Let $x$ be an input, let $g(x)$ be a vector of expert scores, and let $e(x)$ be the set of expert indices selected from those scores. Suppose a router chooses

$$
e(x)=\operatorname{arg\,topk}(g(x)),
$$

and forwards $x$ only through the selected expert. The route decision is discrete and generally non-differentiable. A sound framework must not silently pretend otherwise.

Possible semantics include:

- differentiate routed values but not the route decision;
- replace hard routing with a soft relaxation;
- use a straight-through estimator;
- use a score-function estimator;
- declare the operation non-differentiable.

These alternatives are not equal and should appear as explicit generators or algebra choices. Grading awareness therefore provides not only positive compatibility laws, but also a precise boundary where no canonical reverse law exists.

### III.3 Machine-learning research questions enabled by the framework

A fully functional implementation would be most valuable when the structure of a model or training
computation is itself the subject of study. Its distinctive contribution would not be another way
to train a fixed dense network. It would provide a language in which lifting, reindexing, sharing,
causality, differentiation, and compiler transformation can be varied deliberately and related by
proof.

The research opportunities fall into five connected themes.

#### III.3.1 Structural equivalence and optimized training

The lift law makes it possible to ask exactly when differentiation commutes with an architectural
replication. For an operation $f$ and grade $P$, the relevant equation is

$$
R([f,P])\cong [R[f],P].
$$

This can distinguish axes over which backward computations are genuinely independent from axes
that participate in contraction, normalization, sharing, or recurrence. Concrete research
questions include:

- When is a batched gradient exactly a batch of per-example gradients?
- When can attention heads, ensemble members, spatial positions, or group elements be
  differentiated and scheduled independently?
- Which normalization or communication operations break this independence?
- Which independent grades can be vectorized, streamed, or sharded without synchronization?

The same framework can study whether program transformations preserve training semantics. If

$$
\llbracket p\rrbracket=\llbracket q\rrbracket,
$$

then, under the appropriate differentiability assumptions, one wants to derive

$$
\llbracket R[p]\rrbracket=\llbracket R[q]\rrbracket.
$$

This turns contraction reordering, fusion, layout conversion, convolution lowering, sparse
reformulation, and checkpointing into candidates for **proof-carrying optimization**. A compiler
could search for a faster forward-and-backward implementation while certifying preservation of the
VJP.

This creates several performance research questions. Can reductions for shared parameters be fused
into the contractions that produce their contributions? Can an injective reindexing avoid an
atomic scatter-add? Can sparse incidence structure preserve $O(|E|)$ graph-gradient complexity
instead of introducing an $O(|V|^2)$ dense representation? Can forward and backward contraction
orders be optimized jointly? Grading-aware AD does not guarantee faster gradients, but it preserves
the source information from which such optimizations can be derived and justified.

#### III.3.2 Sharing, scaling, and optimization geometry

Parameter sharing is represented by a structural copying map rather than being inferred from
repeated storage references. If a parameter $\theta$ is used $n$ times, its cotangent has the
form

$$
\bar\theta=\sum_{i=1}^{n}\bar\theta_i.
$$

This gives a controlled way to compare:

- tied and untied transformer layers;
- shared and head-specific attention parameters;
- recurrent weights shared across time;
- convolutional kernels shared across space;
- graph-network parameters shared across edges;
- partially shared, low-rank, or otherwise reparameterized models.

The resulting question is not only whether sharing reduces the parameter count. One can ask how a
specified sharing morphism changes gradient magnitude, covariance, conditioning, and effective
learning rate. Because the framework records the fibers over which contributions are summed, it may
also help derive scaling hypotheses:

- Should cotangent accumulation use a sum or an average for a particular objective?
- How should initialization or learning rates scale with the cardinality of a grade?
- When does sharing over batch, time, space, or edges amplify gradient variance?
- Which forms of sharing contribute to exploding or vanishing gradients?

The system could generate matched model families that differ by one explicit tying or
reparameterization map. This would make ablations more reliable than separately implementing model
variants and assuming that no unintended differences were introduced.

#### III.3.3 Differentiable data models, sparsity, and symmetry

For a new grading $D$, a central design question is whether each forward reindexing has a suitable
cotangent pushforward. If $G_\eta$ is forward transport along an index map $\eta$, its reverse
transport $S_\eta$ should satisfy

$$
\langle G_\eta x,\bar y\rangle
=
\langle x,S_\eta\bar y\rangle.
$$

Treating this equation as part of the data model opens research into:

- graph incidence and neighborhood aggregation;
- sparse, ragged, and nested tensors;
- point clouds and simplicial or cellular complexes;
- distributed tensor layouts and sharding maps;
- group actions and equivariant models;
- stochastic index transformations.

For sparse models, one can ask which index languages remain closed under reverse differentiation,
when both passes can retain sparse complexity, which collision patterns require synchronization,
and which edge or segment orderings improve accumulation.

For equivariant models, one can ask whether symmetry is preserved not only by the forward function
but also by its cotangent transport. For a group element $g$, a representative semantic law is

$$
R[f]\bigl(g\cdot x,g\cdot\bar y\bigr)
=
g\cdot R[f](x,\bar y).
$$

This provides a precise setting for studying whether normalization, parameterization, data
augmentation, optimizers, or compiler rewrites preserve the symmetry of training.

#### III.3.4 Causality, memory, and routing estimators

The explicit scan structure supports research in recurrent networks, state-space models, and
streaming attention. For a transition

$$
h_{t+1}=\phi(h_t,x_t,\theta),
$$

the backward program is a reverse scan that threads an adjoint state and accumulates the cotangent
of the time-shared parameter. Alternative residual policies can therefore be compared while
retaining one mathematical VJP.

This permits questions such as:

- Which values must be saved, and which can be recomputed?
- Which checkpoint schedules minimize memory subject to a runtime budget?
- When can an associative transition admit a parallel reverse scan?
- How should truncated backpropagation be represented as a deliberate approximation?
- Can batching around a scan be proved independent while time remains causal?

Routing raises a complementary class of questions because a hard decision such as

$$
e(x)=\operatorname{arg\,topk}(g(x))
$$

has no canonical derivative. By making stop-gradient, soft relaxation, straight-through, and
score-function semantics distinct constructions, the framework could investigate:

- which routing estimators are invariant under program rewrites;
- how routing interacts with sharing and load-balancing objectives;
- which optimizations remain valid for an estimator that is not a true derivative;
- when a reported gradient is a derivative, subgradient, or stochastic estimator.

The advantage here is not that the formalism chooses one universally correct policy. It prevents
different policies from being treated as though they were mathematically identical.

#### III.3.5 Controlled model generation and structural debugging

Architectures can be varied by named transformations rather than by unrelated implementations. A
research tool could:

- lift an operation over a new grade;
- tie or untie selected parameters;
- replace dense indexing with graph incidence;
- replace independent replication with a causal scan;
- change a contraction schedule or sparse layout;
- insert an equivariant action.

The corresponding forward and backward programs would be generated together, with a record of the
single structural change defining each experimental variant. This offers a foundation for
reproducible algebraic ablations and automated architecture-family generation.

It also gives a useful classification of gradient bugs. Failures can be localized to missing
accumulation after copying, an incorrect reverse reindexing, reduction over the wrong grade,
accidental parameter untying, treatment of a causal axis as independent, differentiation through a
discrete control, or permutation of cotangent axes. Such categories could guide compiler fuzzing,
custom-gradient validation, and minimal counterexample generation.

#### III.3.6 A flagship research program

A focused initial demonstration would ask:

> Can tensor-logic transformations generate faster attention implementations whose forward values
> and VJPs are certified equivalent?

Causal attention combines independent batch and head grades, query-key contractions, affine
indexing, a structural mask, shared parameters, softmax, fusion opportunities, and nontrivial
residual choices. A study could compare:

1. ordinary PyTorch autograd on a reference implementation;
2. a tensor-logic-generated backward program lowered to PyTorch;
3. optimized tensor-logic forward and backward rewrites lowered to PyTorch.

For a reference program $p_{\mathrm{ref}}$ and optimized program $p_{\mathrm{opt}}$, the formal
targets would be

$$
\llbracket p_{\mathrm{opt}}\rrbracket
=
\llbracket p_{\mathrm{ref}}\rrbracket
$$

and

$$
\llbracket R[p_{\mathrm{opt}}]\rrbracket
=
\llbracket R[p_{\mathrm{ref}}]\rrbracket.
$$

The empirical targets would be runtime, peak memory, scaling, and floating-point error relative to
the PyTorch reference. Even a negative result would be informative: it would separate the value of
formal structural guarantees from any unsupported claim of automatic performance improvement.

The broader research proposition is therefore:

> Tensor logic with grading-aware AD is a language in which architectural structure,
> differentiation, optimization, and correctness can be studied together.

It is likely to be most useful when program structure is the experimental variable. It is less
likely to transform routine training of a fixed dense architecture already represented faithfully
and efficiently in PyTorch.

---

## Part IV. Formalization target

This part converts the preceding mathematical and research requirements into a candidate Lean
interface and two correctness layers: semantic adequacy and a precisely delimited differentiable
fragment.

### IV.1 First-class cotangents and backward programs

There is a practical benefit to representing cotangents and generated backward programs as
first-class tensor-logic syntax. The benefit does not come from giving every tensor a mutable
`.grad` field. It comes from making the backward computation an ordinary `TLProgram` that can be
typed, inspected, transformed, realized, interpreted, and proved correct by the same pipeline as a
forward program.

The mathematically primary notion should be a **cotangent**, not a gradient. A gradient is the
array representation of a cotangent after choosing a Euclidean inner product. Keeping the role
explicit leaves room for non-Euclidean interpretations and prevents the implementation
representation from being mistaken for the underlying semantics.

#### IV.1.1 What the current syntax can already express

The current elaborated grammar has tensor declarations and equations, but no `cotangent`,
`linearize`, `pullback`, or `vjp` form. Nevertheless, it can already express many backward
equations as ordinary tensor programs. The examples in this section use only syntax accepted by
the current tensor-logic elaborator.

For a batched linear map, the forward program is:

```text
Y[b, i] := X[b, j] · W[j, i]
```

Its input- and parameter-cotangent equations are:

```text
dX[b, j] := dY[b, i] · W[j, i]
dW[j, i] := X[b, j] · dY[b, i]
```

The elaborator infers contraction from an axis that occurs on the right-hand side but not on the
left. Thus `i` is contracted in the equation for `dX`, while `b` is contracted in the equation for
`dW`. The second equation makes the consequence of sharing visible: because one `W` is used for
every batch position, its cotangent sums over `b`.

An untied parameter carrying the batch axis instead has:

```text
Y[b, i] := X[b, j] · WBatch[b, j, i]
dWBatch[b, j, i] := X[b, j] · dY[b, i]
```

Here `b` remains on the left-hand side, so no batch reduction occurs. The two programs distinguish
shared and independent parameters syntactically rather than relying on backend storage aliasing.

Cotangent accumulation after two uses can also be represented directly:

```text
Y[i] := X[i]
Z[i] := X[i]
dX[i] := dY[i] + dZ[i]
```

The sum is a pure tensor equation. A backend may realize it using an in-place buffer or a reduction
tree, but mutation is not part of its mathematical meaning.

Affine gather and its reverse transport can be written using the existing affine-read and Iverson
predicate syntax:

```text
axis i : ℕ = 5, q : ℕ = 2
Y[q] := X[2 * q + 1]
dX[i] := dY[q] · [i = 2 * q + 1]
```

The `q` axis is absent from the left-hand side of the `dX` equation, so the evaluator sums all
matching contributions. The predicate places those contributions at the source positions selected
by the forward affine read. This dense Iverson form states the correct reverse equation using the
current grammar.

For efficient generated code, the compiler should normally lower the same equation to an additive
scatter. The AST already has `Stmt.scatter` and a reduction option, but the present surface grammar
does not expose a collision-accumulating scatter annotation: affine left-hand sides currently lower
with no reduction policy. Therefore, first-class reverse syntax requires either:

- a surface form that elaborates to `Stmt.scatter` with additive reduction; or
- a trusted reverse elaborator that constructs that existing AST form programmatically.

The distinction matters. An overwrite scatter is not a valid implementation when several output
cotangents map to the same input position.

#### IV.1.2 First-class status should live in typing and elaboration

Names such as `dX` and `dW` are sufficient for examples, but names alone do not make cotangents
first-class. The elaborated representation should record the semantic role of each binding. A
minimal Lean-side design could introduce:

```lean
inductive TensorRole
  | primal
  | cotangent
  | residual
  | control
  | estimator

structure TensorBinding where
  name : String
  axes : List AxisSpec
  role : TensorRole
```

The existing surface declaration

```text
tensor dX(b, j)
```

could initially remain unchanged and receive its role from the generated reverse-program
interface. A later ergonomic extension might add a dedicated declaration keyword, but such a
keyword should elaborate to role metadata rather than define a second tensor equation language.

Role-aware checking can enforce that:

- a generated pullback consumes output cotangents and produces input cotangents;
- a cotangent has axes compatible with its primal;
- structural controls and integer indices do not accidentally receive Euclidean cotangents;
- residuals are produced by the forward phase and consumed by the backward phase;
- estimator outputs are distinguished from true mathematical cotangents.

The numerical evaluator may still store all real-valued roles as `DenseTensor`. The distinction is
semantic and static, not necessarily a different runtime representation.

#### IV.1.3 Residualized reverse programs

A nonlinear backward computation needs primal values or saved residuals. The first-class unit
should therefore contain both a residual-producing forward program and a backward program, rather
than pretending that a backward equation depends only on `dY`.

A Lean representation could be:

```lean
structure ReverseTLProgram where
  forward       : TLProgram
  residualNames : List String
  backward      : TLProgram
  inputCotNames : List String
```

For the linear example, the backward equations read `X` and `W`; those names are therefore part of
the residual contract:

```text
dX[b, j] := dY[b, i] · W[j, i]
dW[j, i] := X[b, j] · dY[b, i]
```

An implementation can choose whether `X` and `W` are retained, recomputed, or supplied from an
enclosing scope. That choice changes storage and execution, but not the tensor equations computed
by the backward program. Making the residual-name interface explicit allows checkpointing and
rematerialization to be treated as transformations of a single reverse specification.

#### IV.1.4 Custom reverse rules

A primitive reverse rule should likewise be represented by tensor-logic programs, not an opaque
backend callback. Conceptually, its Lean record would contain:

```lean
structure VJPRule where
  forward  : TLProgram
  backward : TLProgram
  residualNames : List String
```

For matrix multiplication, the `backward` field can contain exactly:

```text
dX[b, j] := dY[b, i] · W[j, i]
dW[j, i] := X[b, j] · dY[b, i]
```

Attaching this rule to a primitive must also create a proof obligation identifying the denotation
of these equations with the mathematical VJP. Merely registering executable code would reproduce
the trust model of backend custom-gradient hooks.

Rules for operations such as sigmoid cannot yet be stated entirely in the present surface grammar:
the grammar supports applying `sigmoid` to a tensor expression, but lacks general scalar literals
and subtraction in tensor RHS expressions needed for the usual closed-form backward equation.
This is a concrete language-design requirement, not a reason to introduce an opaque escape hatch.

#### IV.1.5 Gradient-oriented transformations

Once backward programs are ordinary `TLProgram` values, existing and future compiler passes can
operate on them. They can:

- remove equations for unused cotangents;
- fuse a shared-parameter reduction into the contraction producing it;
- choose contraction orders jointly for forward and backward programs;
- replace dense Iverson reverse transport with sparse additive scatter;
- shard equations along certified independent grades;
- alter residual storage through proved checkpointing transformations.

The representation also exposes useful research quantities. Per-example parameter cotangents are
obtained by retaining the batch axis:

```text
dWPerExample[b, j, i] := X[b, j] · dY[b, i]
```

Their ordinary shared-parameter cotangent is then:

```text
dW[j, i] := dWPerExample[b, j, i]
```

These remain ordinary tensor equations, so clipping, projection, multitask combination, or
distributed aggregation should be introduced as explicit program transformations rather than
implicit mutation of hidden gradient buffers.

#### IV.1.6 What first-class cotangents make possible

The important new capability is not merely that a program can name `dW`. It is that the axes and
data flow of a cotangent become available to tensor logic. A generated backward program can retain,
contract, reindex, lift, or combine cotangent axes just as a forward program does. This turns
quantities that normally require framework hooks or special-purpose APIs into explicit tensor
programs.

**Batched sensitivity probes.** A VJP ordinarily propagates one supplied output cotangent. Adding a
free probe axis `s` propagates several output cotangents in one tensor program:

```text
dXProbe[s, b, j] := dYProbe[s, b, i] · W[j, i]
```

Each `s` slice is a separate VJP. The compiler can recognize `s` as an independent grade and
vectorize, shard, or stream the probes. Choosing `dYProbe` to contain coordinate seeds exposes
selected Jacobian rows; choosing application-specific seeds computes sensitivities of several
objectives or observables without materializing the full Jacobian.

**Per-example gradients and gradient statistics.** Retaining the batch axis produces one parameter
cotangent per example:

```text
dWPerExample[b, j, i] := X[b, j] · dY[b, i]
```

Once this tensor is explicit, its squared norm and pairwise gradient kernel are ordinary
contractions:

```text
GradNormSq[b] := dWPerExample[b, j, i] · dWPerExample[b, j, i]
GradKernel[a, b] :=
  dWPerExample[a, j, i] · dWPerExample[b, j, i]
```

`GradKernel[a, b]` measures alignment between the parameter cotangents induced by examples `a` and
`b`. Such tensors are useful for studying gradient conflict, example similarity, influence
approximations, data selection, curriculum design, and empirical neural-tangent or Fisher-style
quantities. The explicit program also exposes their potentially high cost, allowing a compiler to
seek matrix-free, blocked, sampled, or low-rank implementations rather than silently materializing
every intermediate.

Per-example cotangents are also the necessary input to differentially private training. Tensor
logic can expose the per-example object and its reduction structure; a complete DP-SGD
implementation would additionally need a well-specified clipping primitive, random-noise
semantics, and a separate privacy proof.

**Multi-objective and multitask combination.** If `alpha[]` and `beta[]` are scalar input tensors,
two task cotangents can be combined explicitly:

```text
dWCombined[j, i] :=
  alpha[] · dWTaskA[j, i] + beta[] · dWTaskB[j, i]
```

This equation records where task weighting occurs and makes the resulting parameter update
auditable. More elaborate gradient-surgery methods first compute task-gradient inner products:

```text
TaskGram[a, b] := dWTask[a, j, i] · dWTask[b, j, i]
```

Conditional projection based on the signs of `TaskGram` is not expressible in the current grammar:
predicates currently range over index arithmetic rather than real tensor values. Supporting PCGrad,
conflict-averse updates, or norm clipping therefore requires an explicit piecewise real-valued
operator and a stated differentiability policy. First-class cotangents make that missing operation
visible instead of hiding it in optimizer-side mutation.

**Normalization and preconditioning.** Some useful transforms already fit the current equation
language. Task cotangents can be normalized by their tensor norms:

```text
TaskNormSq[t] := dWTask[t, j, i] · dWTask[t, j, i]
TaskNorm[t] := sqrt(TaskNormSq[t])
dWUnit[t, j, i] := dWTask[t, j, i] / TaskNorm[t]
```

A production rule must define the zero-norm case. With suitable primitives, the same pattern can
express clipping, diagonal preconditioning, loss scaling, gradient centralization, and optimizer
updates as named transformations from exact cotangents to update tensors. The type system should
not claim that the transformed result is still the mathematical cotangent of the original forward
program: it is an optimizer input derived from that cotangent.

**Distributed aggregation and communication.** A device or shard axis can remain explicit while
local cotangents are computed, then be contracted when the global shared-parameter cotangent is
required:

```text
dW[j, i] := dWShard[device, j, i]
```

This equation specifies summation over `device` independently of whether a backend realizes it as
an all-reduce, reduce-scatter, tree reduction, or local accumulation. Alternative communication
schedules can therefore be optimized and proved against one denotational specification. Similar
programs can express gradient sketches or compression maps:

```text
dWSketch[r] := Projection[r, j, i] · dW[j, i]
```

Compression is an explicit approximation unless reconstruction is lossless; it should carry an
approximation contract rather than masquerade as an equality-preserving rewrite.

**Structural auditing and debugging.** Because cotangent production is syntax, tools can answer
questions before running a model:

- Which loss terms can contribute to a parameter?
- Over which batch, time, edge, head, or device axes is its cotangent reduced?
- Where are two cotangent paths added after a copied value?
- Which reverse reindexings can collide?
- Which parameters receive structurally zero cotangents?
- Did a rewrite alter sharing, reduction axes, or cotangent support?

These checks can produce source-level explanations and small counterexamples rather than relying
only on numerical gradient comparison.

**Higher-order differentiation.** If a generated backward program is itself an ordinary
differentiable `TLProgram`, it can in principle be transformed again. Combined with a
forward-direction transformation or a second reverse pass, this supports Hessian-vector products,
Jacobian-transpose-Jacobian products, meta-learning, and differentiable optimizers. First-class
cotangents are necessary for this closure, but not sufficient by themselves: the system must define
the tangent and cotangent roles of residuals, prove higher-order rules for primitives, and avoid
confusing differentiation of an exact VJP with differentiation through an approximate estimator.

**Custom estimators and surrogate gradients.** Hard routing, quantization, and discrete sampling
may use straight-through or stochastic estimators. Representing the estimator as a tensor program
makes it inspectable, optimizable, and backend-independent. The added `estimator` role is important:
the framework should record that such a program supplies an optimization signal but is not the
mathematical cotangent of the discrete forward operation.

These examples show why first-class status is more than notation. It turns cotangent structure into
an object of compilation and research: users can derive new tensors from it, while the framework
retains enough provenance to distinguish exact reverse semantics, optimizer transformations, and
chosen estimators.

#### IV.1.7 Differential equations and discrete adjoints

First-class cotangents also make tensor logic a plausible language for **differentiable numerical
solvers**. The immediate object represented by the DSL would not be a continuous differential
equation in isolation. It would be a selected discretization of that equation: a finite tensor
program whose time evolution is expressed as a scan.

Consider the parameterized ordinary differential equation

$$
\frac{dx}{dt}=f_\theta(t,x),
\qquad
x(0)=x_0.
$$

Here $x(t)$ is the state, $\theta$ is a collection of shared parameters, and $f_\theta$ is an
arbitrary differentiable vector field of the appropriate type. After choosing time points $t_n$,
step size $h$, and forward Euler integration, the discrete transition is

$$
x_{n+1}
=
x_n+h\,f_\theta(t_n,x_n).
$$

More generally, a numerical method defines a step map

$$
x_{n+1}
=
\Phi_h(t_n,x_n,\theta).
$$

The Euler scan should be parameterized by a tensor-logic program representing the vector field
$f_\theta$. The current surface grammar has no syntax for quantifying over an arbitrary program or
invoking a named tensor-logic subprogram from a scan body. Consequently, the current-language
encoding places the equations that define the vector-field tensor `F[i, n]` in the same program as
the scan. Those equations are the replaceable part; the initial-condition and Euler-update equations
are independent of the choice of $f_\theta$.

For example, the following parser-valid program uses the nonlinear, non-autonomous vector field

$$
f_\theta(t_n,x_n)
=
\tanh\!\left(Wx_n+V\tau(t_n)\right),
\qquad
\theta=(W,V),
$$

where `TimeFeature[k, n]` contains a chosen feature representation $\tau(t_n)$:

```text
axis n : ℕ = 100
X[i, 0] := X0[i]
StateDrive[i, n] := W[i, j] · X[j, n]
TimeDrive[i, n] := V[i, k] · TimeFeature[k, n]
F[i, n] := tanh(StateDrive[i, n] + TimeDrive[i, n])
X[i, n +1] :=
  Identity[i, j] · X[j, n]
  + Dt[] · Identity[i, j] · F[j, n]
```

`Dt[]` is a scalar tensor containing the step size. The assignments ending in `F[i, n]` are one
possible tensor-logic implementation of $f_\theta(t_n,x_n)$; they can be replaced by any collection
of supported tensor-logic equations with the same output interface. This is how the present language
represents an arbitrary *tensor-logic-definable* vector field without inventing unsupported function
call syntax such as `F(Theta, T[n], X[:, n])`. A reusable `step` or named-generator form would make
this program parameterization explicit and remains a useful language extension.

Writing both terms of the update with the contracted index `j` is important under the current
equation-level contraction semantics. The identity in the second term transports `F[j, n]` to the
free output index `i` without causing the vector-field contribution to be repeated by the contraction.

The same pattern covers a spatially discretized partial differential equation. If `L[i, j]` is a
finite-difference, finite-volume, finite-element, or spectral spatial operator, a time-stepped field
can be represented by:

```text
axis n : ℕ = 100
U[i, 0] := U0[i]
U[i, n +1] :=
  Identity[i, j] · U[j, n]
  + Dt[] · L[i, j] · U[j, n]
```

On a regular grid, `L` can ultimately be generated from affine neighbor reads and boundary
predicates. A future graph or mesh grading could instead represent vertices, edges, cells, and
incidence maps directly, avoiding a forced dense matrix representation.

First-class cotangents expose the local reverse rule for each solver step as another tensor
program. Let $a_{n+1}$ be the cotangent arriving at $x_{n+1}$. The generic step VJP produces

$$
\bar x_n
=
D_x\Phi_h(t_n,x_n,\theta)^{\mathsf T}a_{n+1},
$$

$$
g_n
=
D_\theta\Phi_h(t_n,x_n,\theta)^{\mathsf T}a_{n+1},
$$

where $\bar x_n$ is the contribution to the preceding state and $g_n$ is the contribution to the
shared parameter cotangent. For forward Euler these become

$$
\bar x_n
=
a_{n+1}
+
h\,D_xf_\theta(t_n,x_n)^{\mathsf T}a_{n+1},
$$

$$
g_n
=
h\,D_\theta f_\theta(t_n,x_n)^{\mathsf T}a_{n+1}.
$$

For the linear specialization $F[i,n]=A[i,j]X[j,n]$, if `dXNext[n, i]` is $a_{n+1}$, the state
contribution is:

```text
dXStep[n, j] :=
  dXNext[n, i] · Identity[i, j]
  + Dt[] · dXNext[n, i] · A[i, j]
```

Because `A` is shared over all time steps, its total cotangent contracts the time axis:

```text
dA[i, j] := Dt[] · dXNext[n, i] · X[j, n]
```

In the general case, the total shared-parameter cotangent is

$$
\bar\theta
=
\sum_n g_n,
$$

with additional terms if the objective depends directly on $\theta$. The complete solver adjoint
must also combine $\bar x_n$ with any cotangent contributed by an objective at time $n$, then
propagate that total into the preceding step. It is therefore a reverse scan, not an independent
lift over `n`. The present surface grammar can describe forward recurrences but has no dedicated
reverse-time scan form; the reverse compiler should generate such a form, or generate a forward
scan over an explicit reversal of the time axis. Once generated, the adjoint-state sequence and
parameter cotangents remain ordinary, inspectable tensor-logic values.

This supports several research and engineering uses:

- neural ODEs and continuous-time state-space models;
- differentiable physics and simulation;
- system identification and parameter estimation;
- optimal control and trajectory optimization;
- inverse problems and PDE-constrained optimization;
- learned constitutive laws and closure models;
- sensitivity analysis of solver choices and discretization parameters.

For an inverse problem, an unknown coefficient can be represented as a shared parameter of the
step program. Its cotangent then accumulates information from every time step and spatial
location. Retaining those axes instead of immediately contracting them yields time-resolved or
space-resolved sensitivity fields that can be analyzed before forming the final parameter update.

Implicit methods require additional structure. If a step is specified by a residual equation and
solved iteratively, its VJP generally requires a transposed linear solve. A first-class solver
primitive should therefore include:

- the primal solve program;
- its convergence or failure contract;
- the residuals needed in reverse;
- the transposed-solve backward program;
- a theorem relating that program to implicit differentiation.

The formal system must also distinguish two routes:

1. **discretize, then differentiate:** generate the exact VJP of the finite numerical program;
2. **differentiate, then discretize:** derive a continuous adjoint equation and discretize it.

These routes need not yield identical numerical algorithms. A reverse-correctness theorem for the
DSL proves the derivative of the discrete solver. It does not by itself prove that the primal
solver converges to the continuous differential equation, that the discrete cotangent converges to
the continuous adjoint, or that either computation is numerically stable. Those require separate
numerical-analysis results.

This separation is a strength of first-class cotangent syntax: it makes the discrete adjoint
program explicit enough to compare with a discretized continuous adjoint, optimize its memory and
runtime, and state precisely which correctness claim has actually been proved.

The recommended design is therefore:

1. generated backward computations are `TLProgram` values;
2. the elaborated environment distinguishes primal, cotangent, residual, and control roles;
3. residual dependencies form an explicit interface;
4. custom VJPs are tensor-logic programs accompanied by correctness proofs;
5. mutation and gradient buffers remain backend implementation choices.

This makes the backward **program** first-class. Adding only a special name or mutable field for a
gradient array would not provide the same semantic, optimization, or verification benefits.

### IV.2 A proposed categorical interface

The following is a design sketch rather than final Lean syntax. It shows the minimum structure that
appears necessary for the differentiable subcategory identified in Section IV.4; it is not intended as
an instance for every operation and scalar domain currently supported by the DSL.

```lean
class ReverseDGradedPROP
    (D C : Type)
    [ColoredPROP D]
    [ColoredPROP C]
    extends DGradedColoredPROP D C where

  Cot : C → C

  reverse :
    {X Y : C} →
    (X ⟶ Y) →
    (X ⊗ Cot Y ⟶ Cot X)

  cotTensor :
    ∀ X Y, Cot (X ⊗ Y) ≅ Cot X ⊗ Cot Y

  cotAct :
    ∀ X P, Cot (act.obj (X, P)) ≅ act.obj (Cot X, P)

  reverseId : ...
  reverseComp : ...
  reverseTensor : ...
  reverseAct : ...
  reverseCopy : ...
  reverseDelete : ...
```

The omitted laws carry most of the mathematical content.

#### IV.2.1 Identity

For a primal value $x\in\llbracket X\rrbracket$ and cotangent
$\bar x\in\llbracket\mathrm{Cot}(X)\rrbracket$, the identity morphism passes the cotangent through
unchanged:

$$
R[\mathrm{id}_X](x,\bar x)=\bar x.
$$

#### IV.2.2 Reverse chain rule

For

$$
X \xrightarrow{f} Y \xrightarrow{g} Z,
$$

where $f:X\to Y$ and $g:Y\to Z$, let $x\in\llbracket X\rrbracket$ be the primal input and let
$\bar z\in\llbracket\mathrm{Cot}(Z)\rrbracket$ be the output cotangent. The reverse computation first
propagates $\bar z$ through $g$, then propagates the resulting cotangent through $f$:

$$
R[f;g](x,\bar z)
=
R[f]\bigl(x,R[g](f(x),\bar z)\bigr).
$$

Operationally, this law determines how residuals compose.

#### IV.2.3 Parallel composition

For independent maps $f : X \to Y$ and $g : X' \to Y'$,

$$
R[f\otimes g]
\cong
R[f]\otimes R[g],
$$

modulo symmetry and cotangent-tensor coherence.

#### IV.2.4 Lift compatibility

The `reverseAct` law is the equation from [§II.3](#ii3-the-central-lift-law). It is the defining grading-aware law.

#### IV.2.5 Additive cotangent structure

Let $I$ denote the monoidal unit of $C$, representing no input wires. Reverse differentiation needs a zero cotangent and an addition morphism for each object $X$:

$$
0_X : I \longrightarrow \mathrm{Cot}(X),
$$

$$
+_X :
\mathrm{Cot}(X)\otimes\mathrm{Cot}(X)
\longrightarrow
\mathrm{Cot}(X).
$$

These operations are required whenever:

- one value is unused, producing zero;
- one value is used more than once, requiring accumulation;
- a non-injective reindexing creates collisions;
- a shared parameter receives contributions from many examples or time steps.

The reverse laws for structural deletion and copying are therefore, at the semantic level,

$$
R[\mathrm{delete}](x,\ast)=0,
$$

$$
R[\mathrm{copy}](x,(\bar x_1,\bar x_2))
=
\bar x_1+\bar x_2.
$$

Here $\ast$ is the unique cotangent of the monoidal-unit output. Categorically, these equations also
discard the primal $x$; writing only $R[\mathrm{delete}]=0$ or $R[\mathrm{copy}]=+$ would suppress
that necessary input and would not be a literal equality of morphism types.

#### IV.2.6 Differentiable reindexing

The index category needs an additional adjoint-transport operation. Schematically:

```lean
class CotangentPushforward (D : Type) where
  CotangentFamily : D → Type
  inner :
    (A : D) →
    CotangentFamily A → CotangentFamily A → ℝ

  pull :
    {Q A : D} →
    (η : Q ⟶ A) →
    CotangentFamily A → CotangentFamily Q

  push :
    {Q A : D} →
    (η : Q ⟶ A) →
    CotangentFamily Q → CotangentFamily A

  adjoint :
    ∀ {Q A : D} (η : Q ⟶ A)
      (x : CotangentFamily A) (y : CotangentFamily Q),
      inner Q (pull η x) y = inner A x (push η y)
```

Here `Q` and `A` are objects of the index category `D`; `CotangentFamily A` is the type of cotangent-valued families indexed by `A`; `pull` is forward gather; `push` is reverse accumulation; and `inner` is the relevant pairing or inner product. The exact Lean type should be expressed through the chosen target algebra, but the adjoint law is the important part.

#### IV.2.7 Reverse Para algebra

The parameterized layer should expose the split cotangent

$$
\mathrm{Cot}(\Theta\otimes X)
\cong
\mathrm{Cot}(\Theta)\otimes\mathrm{Cot}(X)
$$

and prove naturality with respect to reparameterization. If

$$
\Delta:\Theta'\longrightarrow\Theta
$$

ties or otherwise transforms parameters, then the induced parameter gradient must be transported by the reverse derivative of $\Delta$:

$$
\bar\theta'
=
D\Delta(\theta')^{\mathsf T}\bar\theta.
$$

Here $\theta'\in\Theta'$ is the underlying parameter value, $\theta=\Delta(\theta')\in\Theta$ is the expanded or transformed value used by the model, $\bar\theta\in\mathrm{Cot}(\Theta)$ is its cotangent, and $\bar\theta'\in\mathrm{Cot}(\Theta')$ is the cotangent returned to the underlying parameter. For a tying diagonal, this transport is summation. For a linear low-rank parameterization, it is multiplication by the transpose of the parameterization map.

### IV.3 Semantic adequacy and the target theorem

Reverse differentiation should be built on top of a proved forward semantics, not alongside an unverified one.

Use the quantities defined in [§I.1.2](#i12-the-categorical-algebra-and-executable-evaluator-are-separate). For a
fixed well-typed program $p$, write

$$
E_p(x)=\operatorname{eval}(p,x)
$$

for the output-projected executable semantics. The forward adequacy theorem is

$$
E_p(x)
=
\llbracket
\operatorname{realize}(\operatorname{compile}(p))
\rrbracket(x).
$$

Now let $\operatorname{revCompile}(p)$ be the generated backward program. The final reverse-correctness theorem should state

$$
\operatorname{eval}
\bigl(
\operatorname{revCompile}(p),
(x,\bar y)
\bigr)
=
DE_p(x)^{\mathsf T}\bar y.
$$

The stronger categorical statement is

$$
\llbracket
R\bigl[
\operatorname{realize}(\operatorname{compile}(p))
\bigr]
\rrbracket
=
R_F\bigl[
\llbracket
\operatorname{realize}(\operatorname{compile}(p))
\rrbracket
\bigr],
$$

where $R_F$ is the mathematical reverse derivative in the target.

Together with the grading laws, this yields the intended theorem:

> For every program in the differentiable fragment, the generated backward morphism computes the mathematical VJP of the forward interpretation, preserves the `D`-graded structure, transposes reindexings correctly, and accumulates cotangents exactly according to structural sharing.

This theorem is substantially more useful than a proof that the backward compiler matches a previous implementation. It identifies both implementations with an independently specified mathematical derivative.

### IV.4 Differentiability boundaries

The current DSL deliberately supports more than ordinary real-valued smooth tensor calculus. A rigorous AD design must classify this surface rather than provide one misleading global instance.

#### IV.4.1 Smooth real-valued fragment

Canonical reverse rules exist for:

- addition and multiplication;
- tensor contraction;
- affine gather;
- scatter-add;
- `exp`, `log`, sigmoid, and `tanh`;
- softmax away from exceptional numerical behavior;
- smooth normalization with a stated zero-denominator policy.

This should be the first proved fragment.

#### IV.4.2 Almost-everywhere differentiable operations

Operations such as ReLU, maximum, and minimum require a subgradient convention at ties or nondifferentiable points. The convention must be explicit in the target semantics and matched by the backend.

For example, `max` reduction requires a policy for distributing cotangents when multiple inputs attain the maximum:

- choose one winner;
- divide among all winners;
- use another documented subgradient.

These are different functions.

#### IV.4.3 Discrete and logical operations

Boolean contraction, predicates, integer indices, hard masks, `argmin`, and hard routing generally have no canonical real reverse derivative. They may still participate in a differentiable program as **structural constants**. A fixed causal mask, for example, controls which real-valued paths exist without itself receiving a cotangent.

The type system should distinguish:

- a differentiable real-valued input;
- a nondifferentiable control or index input;
- a constant structural value;
- an operation equipped with an estimator rather than a true derivative.

#### IV.4.4 Alternative semirings

The Bool and tropical evaluators are valuable precisely because tensor logic is broader than real linear algebra. They should not be forced into a false Euclidean AD interface.

Possible future notions include:

- semiring sensitivity;
- perturbation analysis;
- provenance semirings;
- subdifferentials for tropical programs.

These are separate research programs. The first reverse-differentiation theorem should remain scoped to a clearly identified real-valued fragment.

#### IV.4.5 Floating-point versus real-number correctness

A theorem over real numbers does not by itself prove bitwise equivalence of floating-point execution. The project should distinguish:

1. exact mathematical VJP correctness over $\mathbb R$;
2. correspondence between the Lean `Float` evaluator and generated backend code;
3. numerical stability and rounding-error bounds.

The first is already a major result. The latter two can be layered on rather than silently conflated with it.

---

## Part V. Implementation roadmap and payoff

This final part orders the work needed to realize the formalization, places it alongside the other
major opportunities in the repository, and states the resulting research value.

### V.1 Research and implementation program

The work should proceed in an order that prevents the backward formalization from resting on an unverified forward path.

#### Phase 1: close the concrete forward model

Complete the concrete `DGradedColoredPROP StObj BrObj` instance:

- define the lift functor on `Br` objects and morphisms;
- prove the distributor, unit, and associativity isomorphisms;
- prove shape compatibility;
- prove action and distributivity coherences;
- prove the required generation/factorization property.

This turns the generic graded-PROP propositions into theorems about the actual tensor-program model.

#### Phase 2: provide a concrete-size tensor algebra

The symbolic `FGModuleCat` target has recorded dimension obstructions. The executable development should instead use concrete `Nat`-sized tensor spaces compatible with `DenseTensor`.

Required results include:

- a concrete target actegory;
- an `Algebra` instance interpreting `Br`;
- a `ParaAlgebra` or equivalent concrete parameter interpretation;
- agreement between primitive categorical generators and evaluator operations.

#### Phase 3: prove forward semantic adequacy

Prove that parse, compile, route, realize, and interpret agree with `TLProgram.eval` on successful programs. Scans may require either:

- enriching the routed representation so it retains complete scan bodies; or
- stating adequacy against the scheduled representation and proving a separate scan-aware realization theorem.

The current distinction between pre-route evaluation and routed realization must be resolved explicitly.

#### Phase 4: define the differentiable fragment

Introduce a judgment or subtype expressing that every primitive in a program has a valid reverse rule under a selected real-valued semantics.

The judgment should reject or separately classify:

- Boolean outputs;
- hard routing;
- unsupported recurrence forms;
- nondifferentiable operations without a chosen convention.

#### Phase 5: implement primitive reverse rules

Start with a small basis that already covers compelling models:

1. identity, composition, and tensor product;
2. copying, deletion, zero, and addition;
3. contraction;
4. affine gather and accumulating scatter;
5. elementary smooth nonlinearities;
6. softmax and normalization;
7. parameter reads and tying;
8. sequential scan.

The reverse compiler should generate tensor-logic or `Br` morphisms, not opaque backend callbacks.

#### Phase 6: prove reverse correctness compositionally

For each primitive $g$, prove

$$
\llbracket R[g]\rrbracket
=
R_{\mathrm{math}}[\llbracket g\rrbracket].
$$

Then prove that the property is preserved by:

- composition;
- tensor product;
- symmetry;
- `D`-lift;
- reindexing;
- parameter reparameterization;
- scan formation.

The whole-program theorem should follow by induction over the program representation.

#### Phase 7: validate against independent oracles

The formal theorem should be supplemented by executable differential testing:

- compare generated VJPs with PyTorch autograd;
- compare with central finite differences on small random programs;
- compare with hand-derived gradients for matrix multiplication, convolution, attention, tied parameters, and scans;
- test collision-heavy gather/scatter maps;
- test that a lifted parameter and a shared parameter produce different gradient shapes and reductions.

The oracles are validation tools, not the semantic specification.

#### Phase 8: certify optimization passes

Once forward and reverse semantics exist, a rewrite

$$
f \rightsquigarrow g
$$

can carry two levels of certificate:

$$
\llbracket f\rrbracket=\llbracket g\rrbracket,
$$

and, when needed,

$$
\llbracket R[f]\rrbracket=\llbracket R[g]\rrbracket.
$$

For differentiable real functions, forward extensional equality under appropriate regularity often implies derivative equality, but the assumptions and exceptional points matter. Explicit reverse preservation is especially valuable for floating-point rewrites, custom gradient rules, checkpointing, and nondifferentiable conventions.

### V.2 Broader opportunities beyond differentiation

Grading-aware reverse differentiation is one demanding application of the framework, not its only
research purpose. Once the concrete semantics and compiler are proved, the same foundations could
support a broader program organized around three questions:

1. How can an implementation change while its denotation remains fixed?
2. Which index structures support useful executable tensor languages?
3. What can be learned by interpreting one tensor program in several algebras?

#### V.2.1 Program transformation and execution

The first theme is **proof-carrying tensor compilation**. An optimization from a reference program
$p$ to a transformed program $q$ should carry a proof of

$$
\llbracket p\rrbracket=\llbracket q\rrbracket.
$$

Candidate transformations include:

- contraction reordering;
- fusion and fission;
- elimination of redundant permutations and reshapes;
- convolution lowering;
- sparse versus dense reformulation;
- scan chunking and streaming transformations;
- layout conversion and mixed-precision placement.

This would make program equivalence a compiler resource. A normalization or rewrite system could
deduplicate architecture-search results, validate model conversions, and determine when two
syntactically different tensor programs are structurally equivalent. Complete equivalence for
arbitrary nonlinear programs is not expected to be decidable, but sound rewrite systems and useful
decidable fragments are realistic.

The same semantics can support **verified backend interoperability**. If $p$ is interpreted by two
backends, the desired theorem is

$$
\llbracket p\rrbracket_{\mathrm{backend}\,1}
=
\llbracket p\rrbracket_{\mathrm{backend}\,2}.
$$

This reframes conversion among Lean evaluation, PyTorch, JAX, ONNX, MLIR, and accelerator dialects
as semantic preservation rather than serialization. It is especially relevant for broadcasting,
indexing, masking, and numerical conventions that can silently differ across systems.

Grades and reindexings could also describe **distributed execution**. Device placement,
partitioning, replication, and collectives can be treated as structured transformations of a
single-device reference program. Research questions include whether legal shardings can be derived
from axis structure, whether communication requirements can be synthesized from reindexing maps,
and whether a distributed implementation can be certified equivalent to its reference:

$$
\llbracket p_{\mathrm{distributed}}\rrbracket
=
\llbracket p_{\mathrm{reference}}\rrbracket.
$$

Finally, resource annotations could support certified or statically checked claims about peak
memory, communication, precision, and recomputation. These are not semantic equalities: two
equivalent contraction trees may have very different costs. A useful research challenge is to
combine a proof of denotational equivalence with a separate, explicit cost model rather than
conflating correctness and performance.

#### V.2.2 New index structures and model families

The second theme is to make the index category $D$ genuinely generic and executable. The concrete
system is currently centered on $D=\mathrm{St}$: dense shapes and affine reindexings. Other choices
could represent:

- graph and hypergraph incidence;
- ragged and sparse coordinate systems;
- point-cloud neighborhoods;
- geometric meshes and cellular complexes;
- group actions;
- database-style relations;
- distributed tensor partitions.

The unifying research question is:

> Which choices of $D$ admit compositional typing, useful algebraic laws, efficient execution, and
> faithful realization as tensor programs?

Explicit index maps expose properties hidden by generic gather and scatter operators, including
injectivity, surjectivity, fiber cardinalities, collisions, locality, and sparsity. A compiler could
specialize a bijection to a permutation, an injection to collision-free scatter, a regular
many-to-one map to segmented reduction, or graph incidence to an edge-linear implementation. This
could support graph networks, sparse attention, finite-element models, and geometric learning
without forcing their structure through dense tensor representations.

A group-action grading could support **equivariant architectures by construction**. For a group
element $g$, the forward requirement is

$$
f(g\cdot x)=g\cdot f(x).
$$

The framework could generate layers whose composition preserves this law, identify nonlinearities
and reductions that break it, and certify that compiler transformations retain equivariance.

Because well-typed architectures are compositional morphisms, the same machinery could support
**semantics-aware architecture generation**. Search operations might add a grade, introduce or
remove sharing, replace dense indexing with graph incidence, insert a scan, or enforce a symmetry.
Typing would reject invalid candidates, while equivalence rules could avoid repeatedly exploring
different presentations of the same computation.

#### V.2.3 Alternative interpretations and structural analysis

The third theme exploits `Algebra`: one tensor-logic program may admit several interpretations.
Besides ordinary real or floating-point arithmetic, possible targets include:

- Boolean and tropical semirings;
- counting and provenance semirings;
- symbolic expressions;
- interval or abstract domains;
- dependency and resource analyses.

The numerical interpretation computes tensor values. Another interpretation of the same program
might compute support, reachability, provenance, possible influence, or an upper bound on resource
use. This could connect tensor compilation with static analysis without introducing a separate
program representation for every analysis.

The explicit representation of copying, deletion, contraction, reindexing, and scans also enables
**structural information-flow analysis**. Independently of learned weights, one could ask:

- Which outputs can depend on a given input or parameter?
- Which outputs share a parameter or intermediate value?
- Which sequence positions or graph neighborhoods can influence a prediction?
- Where can information be duplicated, aggregated, or discarded?
- Which transformations preserve locality or causal reachability?

This is program-level interpretability, not statistical feature attribution. It characterizes the
possible dependency structure induced by the architecture.

Scans provide a particularly useful non-AD application. One could prove equivalence among unrolled,
scanned, chunked, and streaming executions, provided the state is transported correctly. Such
results would address discrepancies between full-sequence research implementations and
incremental deployment even when no gradients are involved.

### V.3 How the broader agenda reinforces grading-aware AD

These directions share infrastructure rather than competing for unrelated abstractions:

| Broader capability | Connection to grading-aware AD |
| --- | --- |
| Proof-carrying optimization | Rewrites can preserve both forward denotation and VJPs |
| Generic executable gradings | Each forward reindexing suggests a corresponding cotangent transport |
| Sparse compilation | Sparse index structure should survive forward and backward lowering |
| Distributed compilation | Independent grades identify safe opportunities for backward sharding |
| Resource semantics | Residual storage, checkpointing, and recomputation become explicit costs |
| Alternative algebras | They identify interpretations for which Euclidean AD is inapplicable |
| Streaming semantics | Forward scan equivalences motivate corresponding reverse-scan results |

AD is therefore a strong integration test for the framework. It forces the object language,
reindexing semantics, parameter sharing, compiler, concrete algebra, and backend to agree.
Conversely, the forward semantic and optimization work required for AD remains valuable even if
some users ultimately delegate differentiation to PyTorch.

### V.4 Prioritization

The breadth of this agenda should not lead to simultaneous implementation of every proposed
grading, backend, and analysis. A defensible order is:

1. complete the concrete $\mathrm{St}/\mathrm{Br}$ forward model;
2. prove agreement between compilation, realization, and executable evaluation;
3. develop a small proof-carrying forward rewrite system;
4. establish grading-aware reverse differentiation for the smooth real-valued fragment;
5. generalize the paired forward/reverse interface to selected new choices of $D$;
6. pursue sparse, distributed, equivariant, and alternative-algebra applications on that base.

The third step can begin before the full AD development and provides immediate evidence that the
categorical semantics improves compilation. New gradings should come later: otherwise each one
multiplies an already unverified semantic surface.

### V.5 Research payoff

The proposed work changes the character of the framework.

At the broadest level, a fully realized system would be a **proof-carrying compiler and research
language for structured tensor programs**. Grading-aware reverse differentiation would make it,
more specifically, a proof-carrying compiler for trainable tensor programs rather than a forward
formalism whose training semantics is inherited entirely from a backend.

The resulting system could answer questions that ordinary AD systems usually leave implicit:

- Which axes are independent batch grades?
- Which axes must be reduced in a parameter gradient?
- Which forward gather induces which reverse scatter?
- Where are collision sums required?
- Is a parameter shared, lifted, or reparameterized?
- Does differentiation commute with batching or equivariant lifting?
- Does a scan's backward pass respect causality?
- Does a fusion or routing rewrite preserve the VJP?
- Which operations are genuinely differentiable, and which use an estimator or convention?

The compelling end-to-end demonstration would be a small causal attention block with shared parameters and affine indexing for which the project can:

1. compile and evaluate the forward tensor-logic program;
2. generate a backward morphism in the same formal language;
3. prove the backward morphism computes the mathematical VJP;
4. prove batching and head lifting commute with that transformation;
5. prove tied parameter uses accumulate correctly;
6. generate executable backend code;
7. numerically agree with PyTorch autograd.

That result would connect the repository's strongest existing ideas—graded lifting, weaves,
algebras, `Para`, compilation, and Lean verification—around the central operation of machine
learning: computing correct gradients of structured, parameterized programs. The same proved
foundation could then support verified optimization, new executable index systems, distributed and
sparse compilation, alternative algebraic interpretations, and structural analysis without making
those directions prerequisites for the initial AD result.

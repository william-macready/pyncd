# Categorical operational semantics: syntax and behaviour

This document explores the categorical approach to operational semantics
introduced by Turi and Plotkin in 1997, and the developments that followed it.
It assumes familiarity with categories, functors, and natural transformations,
but not with algebras, coalgebras, or their universal properties.

The opening sections explain the motivation and benefits before introducing
the technical machinery. Appendix A gives a self-contained introduction to
algebras and coalgebras. The notation in this document is independent of the
other documents in this directory.
Mathematics uses `$...$` for inline expressions and `$$...$$` for display
equations, for viewing in VS Code's Markdown preview.

## 1. Why approach operational semantics categorically?

### 1.1. From execution rules to mathematical questions

An **operational semantics** describes how programs execute. One common
approach specifies individual execution steps: what a program can do now,
and which program remains to execute afterward. Such a step is called a
**transition**.

A language's **syntax** specifies how its programs are formed. A
**constructor** is one of its ways of forming a program from smaller
pieces, such as sequencing two programs or running them in parallel.
**Structural operational semantics** gives execution rules organised
around these constructors. A rule explains the behaviour of a compound
program using information about its components.

For example, consider **nondeterministic choice**, a constructor that
offers alternative behaviours without assigning probabilities to them.
One of its rules can say:

> If an alternative can perform an action and continue as a new program,
> then the choice program can perform that action and continue as that
> new program.

An **action** here is a label recording an execution event, such as sending
a message. This rule explains how the choice constructor turns a possible
step of a component into a possible step of the whole.

Rules of this kind are concrete and useful. But writing them down leaves
important questions:

- Do the rules determine an execution model with the intended properties?
- When should two programs count as having the same behaviour?
- Can equivalent programs replace one another inside larger programs?
- Can the rules be connected to a mathematical interpretation that
  supports reasoning about whole executions?

These are not merely questions about an individual program. They concern
the design of a language and its rules.

### 1.2. The difficulty: local rules must support global reasoning

A single rule usually examines only a small amount of information: one
constructor and some facts about its arguments. The properties we want,
however, concern complete executions and arbitrarily large programs.

For example, deciding that two programs are equivalent requires a choice
of what to observe. We might observe every labelled step and the
alternative continuations, or only the sequences of externally visible
actions. These choices need not produce the same equivalence.

A **program context** is a larger program with a designated hole into
which another program can be inserted. An equivalence is a
**congruence** when inserting equivalent programs into the same context
always produces equivalent results.

This is the replacement principle needed for reasoning about components:
establish that two components are equivalent, then use either one without
reproving the behaviour of every surrounding program. Establishing
equivalence for programs in isolation does not, by itself, establish this
replacement principle.

There is a second connection to justify. A **denotational semantics**
assigns programs mathematical meanings, called **denotations**.
A denotation might be a function, a tree of possible behaviours, or
another mathematical object appropriate to the language.

A denotational interpretation is **compositional** when the meaning of a
compound program is determined by the meanings of its components and the
constructor combining them. That interpretation must also agree with the
execution rules in an appropriate sense; a compositional interpretation
that forgets important execution behaviour would not be enough.

Proving these properties separately for each language can be difficult.
Moreover, similar arguments recur for languages with different syntax
or different kinds of behaviour.

### 1.3. The categorical idea: identify the structure behind the rules

The motivation for category theory is to isolate what those repeated
arguments actually depend on.

Turi and Plotkin separate three ingredients:

1. **The shape of syntax:** which constructors are available and what
   kinds of arguments they take.
2. **The shape of behaviour:** what a single observation reveals and how
   execution can continue.
3. **The interaction between them:** how a constructor uses information
   about its arguments to determine the behaviour of the compound program.

Functorial descriptions capture the first two ingredients. Suitable
natural transformations describe the third. The required form of the
transformation matters: an arbitrary transformation does not automatically
constitute a suitable operational specification.

The key is then to prove results about this abstract interaction, rather
than about one particular list of language constructs.

This explains the roles of the two notions developed in Appendix A.
In the syntax examples, an **algebra** supplies a morphism that constructs
or interprets compound objects. In the behaviour examples, a
**coalgebra** supplies a morphism that reveals one observation and its
continuations. A further compatibility law connects these structures.

Simply having an algebra and a coalgebra is not enough. The compatibility
law is what makes the two descriptions work together.

## 2. What benefits does the categorical approach provide?

### 2.1. Reusable theorems instead of repeated proofs

In their [1997 paper](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf),
Turi and Plotkin give general conditions under which suitably expressed
operational rules yield compatible operational and denotational models.

To apply such a theorem, a language designer must show that the chosen
syntax, behaviour, and rules meet its hypotheses. The reward is that
conclusions such as compositionality can then follow from the general
theorem, rather than from a new proof tailored to every constructor.

This does not eliminate proof obligations. It moves them to a more
reusable level: show that the specification fits the framework, then
reuse the framework's results.

### 2.2. A reason that behavioural equivalence respects constructors

In a **labelled transition system**, states represent stages of execution,
and transitions carry action labels. An important equivalence for these
systems is **strong bisimilarity**. Roughly, two programs are strongly
bisimilar when each step of either program can be matched by a step with
the same label from the other, with the continuations again related.
The matching must work in both directions.

For appropriate specifications, the categorical framework proves that
this equivalence is a congruence. Equivalent programs can therefore be
substituted inside the language's contexts.

The benefit is not merely knowing that a particular operator preserves
equivalence. It is understanding which structural conditions on the
rules ensure that all the constructors in a specification do so.

### 2.3. A bridge between execution and mathematical meaning

Under the relevant hypotheses, the framework constructs a domain of
behaviours together with operations interpreting the program constructors.
It also provides a map assigning a behaviour to each program.

Two routes then agree:

1. Construct the compound program, then determine its behaviour.
2. Determine the behaviours of its components, then combine those
   behaviours using the corresponding interpretation of the constructor.

This agreement connects the operational account of execution to a
compositional denotational account. It explains why one can reason about
component meanings without losing the connection to execution.

### 2.4. A common framework for different kinds of behaviour

The description of behaviour is an explicit ingredient, not something
permanently fixed to one kind of transition system.

Later work has used this separation to study probabilistic behaviour,
transitions carrying rates or weights, and other variations. The
categorical framework helps identify what is shared and where new
conditions are necessary. [Klin's survey](https://www.cs.ox.ac.uk/people/bartek.klin/papers/tcs11.pdf)
describes several such developments.

This is reuse of an organising principle, not a promise that changing
the behaviour functor leaves every theorem applicable without further
work.

### 2.5. Guidance for designing operational rules

A **rule format** specifies permitted patterns for operational rules.
For example, it can restrict which facts about the arguments a rule
may inspect and how its conclusion may use them.

Categorical semantics can explain why a format has desirable properties:
its rules determine transformations with the required compatibility.
It can also guide the search for formats suited to a different kind
of behaviour.

Thus category theory is not only a language for describing an existing
semantics. It can help explain and organise the design of semantics.

## 3. What the approach does not promise

The categorical approach does not automatically establish that:

- Every collection of operational rules has a suitable model.
- Every endofunctor has an initial algebra or a final coalgebra.
- Every proposed notion of behavioural equivalence is a congruence.
- Behavioural equivalence coincides with every independently chosen
  notion of what programs can observe about one another.
- A compiler or implementation faithfully executes the specified rules.

Those questions require their own hypotheses and arguments. In particular,
changing what counts as an observation can change both the equivalence
and the conditions needed for compositionality.

The central benefit is more precise:

> By expressing syntax, behaviour, and their interaction in the right
> categorical form, we can prove structural guarantees once and apply
> them across suitable languages and models.

Appendix A develops the algebra and coalgebra vocabulary needed to make
this statement precise. It starts with examples in the category of sets,
then shows how the same definitions work in a different category.

## Appendix A. Algebras and coalgebras

### A.1. The setting and some elementary notation

Let $\mathcal{C}$ denote a category. An **endofunctor** is a functor from a
category to itself. We write

$$
F:\mathcal{C}\longrightarrow\mathcal{C}
$$

for an endofunctor named $F$. It assigns an object $FX$ to each object $X$,
and a morphism $Ff:FX\longrightarrow FY$ to each morphism
$f:X\longrightarrow Y$. The expressions $FX$ and $Ff$ mean the application
of the functor to an object and to a morphism, respectively.

An algebra or coalgebra is always relative to a chosen endofunctor.
The functor specifies the shape of the structure; the algebra or coalgebra
supplies a morphism with that shape.

The definitions apply to an arbitrary category $\mathcal{C}$ equipped
with an endofunctor. The examples are divided into two classes:

- **Examples in $\mathbf{Set}$ (A.2-A.5).** In every example in these
  sections, $\mathcal{C}=\mathbf{Set}$, the category whose objects are
  sets and whose morphisms are functions.
- **Examples in an ordered category (A.7).** Here the objects are
  rational numbers and the arrows express inequalities. This is a
  different category, not $\mathbf{Set}$.

For the first class, a function $f:X\longrightarrow Y$ takes an
element of the set $X$ to an element of the set $Y$. We write $x\in X$ to
say that $x$ is an element of $X$, and $f(x)$ for its image. An equality
sign, $=$, asserts that the expressions on its two sides are equal.

We will use these ways of forming sets:

- **Cartesian product.** $X\times Y$ is the set of ordered pairs $(x,y)$,
  with $x\in X$ and $y\in Y$. An ordered pair remembers which component
  comes first.
- **Singleton.** $\mathbf{1}=\{\ast\}$ is a set with exactly one element,
  named $\ast$. Braces denote a set containing the listed elements.
  Here $\mathbf{1}$ names a set, not a number.
- **Disjoint union.** $X+Y$ is the set of elements of $X$ or $Y$, with a
  tag recording which side they came from. We write
  $\operatorname{inl}(x)$ for an element from the left side and
  $\operatorname{inr}(y)$ for an element from the right side. The tags
  keep the two sides distinct even when $X$ and $Y$ overlap.

The plus sign in $X+Y$ denotes disjoint union of sets. A plus sign between
numbers will denote ordinary arithmetic addition.

For composable morphisms $f:X\longrightarrow Y$ and
$g:Y\longrightarrow Z$, where $Z$ is another object, we write
$g\circ f:X\longrightarrow Z$ for their composition: first apply $f$,
then apply $g$. Thus $(g\circ f)(x)=g(f(x))$ in $\mathbf{Set}$.
We write $\operatorname{id}_X:X\longrightarrow X$ for the identity
morphism on $X$.

### A.2. What is an algebra?

For the chosen endofunctor $F$, an **$F$-algebra** consists of:

1. An object $A$, called its **carrier**.
2. A morphism $\alpha:FA\longrightarrow A$, called its **structure map**.

We write $(A,\alpha)$ for this pair. In $\mathbf{Set}$, the carrier is a
set and the structure map is a function.

The useful picture is:

$$
FA\xrightarrow{\alpha}A.
$$

In our $\mathbf{Set}$ examples, $F$ describes an arrangement of inputs
from $A$. Then $\alpha$ turns such an arrangement into an element of $A$.

**In these examples, an algebra tells us how to combine or interpret
structured inputs.** The general definition requires only the
structure morphism $\alpha:FA\longrightarrow A$.

#### Example 1: a binary operation

Choose the endofunctor defined on sets by

$$
FX=X\times X.
$$

To specify a functor we must also say what it does to functions. For a
function $f:X\longrightarrow Y$, its action is

$$
Ff(x_1,x_2)=(f(x_1),f(x_2)),
$$

where $x_1$ and $x_2$ are the two input elements of $X$.
The identity and composition laws hold because the function is applied
separately to each component.

An algebra for this functor is a function

$$
\alpha:A\times A\longrightarrow A.
$$

That is exactly a binary operation on $A$.

Let $\mathbb{N}=\{0,1,2,\ldots\}$ denote the natural numbers, including
zero; the ellipsis means that the sequence continues. Arithmetic addition
gives an algebra with carrier $\mathbb{N}$ and structure map

$$
\alpha(m,n)=m+n,
$$

where $m,n\in\mathbb{N}$ are its two arguments. Multiplication gives a
different algebra for the same functor, using the structure map
$\alpha(m,n)=m\cdot n$, where $\cdot$ denotes arithmetic multiplication.

The functor fixes the input shape: two elements. It does not choose
which operation to perform.

For this functor, the definition of an algebra does **not** require the
operation to be associative or commutative. Those would be additional
requirements. An algebra for an endofunctor is therefore not automatically
a group, ring, or vector-space algebra.

#### Example 2: a distinguished element and a unary operation

Now choose a different endofunctor:

$$
FX=\mathbf{1}+X.
$$

For a function $f:X\longrightarrow Y$, define its action by

$$
Ff(\operatorname{inl}(\ast))=\operatorname{inl}(\ast),
\qquad
Ff(\operatorname{inr}(x))=\operatorname{inr}(f(x)).
$$

Here $\qquad$ simply separates the two cases. The singleton branch is
left unchanged; the other branch is transformed using $f$.

An algebra $\alpha:\mathbf{1}+A\longrightarrow A$ makes two choices:

- The value $\alpha(\operatorname{inl}(\ast))$ selects an element of $A$.
- The values $\alpha(\operatorname{inr}(x))$, for $x\in A$, specify a
  unary operation: an operation taking one element of $A$ to another.

On the natural numbers, take the structure map
$\alpha_{\mathbb{N}}:\mathbf{1}+\mathbb{N}\longrightarrow\mathbb{N}$
defined by

$$
\alpha_{\mathbb{N}}(\operatorname{inl}(\ast))=0,
\qquad
\alpha_{\mathbb{N}}(\operatorname{inr}(n))=n+1.
$$

The subscript identifies this as the structure map on $\mathbb{N}$.
This algebra consists of zero and the successor operation.

It lets us construct every natural number: begin with zero, then apply
successor a finite number of times.

#### Example 3: constructing expression trees

Let $\Sigma$ name the endofunctor

$$
\Sigma X=\mathbb{N}+(X\times X).
$$

Its input shape has two alternatives:

- A natural-number label.
- An ordered pair of elements of $X$.

For a function $f:X\longrightarrow Y$, define

$$
\Sigma f(\operatorname{inl}(n))=\operatorname{inl}(n),
\qquad
\Sigma f(\operatorname{inr}(x_1,x_2))
  =\operatorname{inr}(f(x_1),f(x_2)).
$$

In the second expression, $\operatorname{inr}(x_1,x_2)$ means the
right-tagged ordered pair. Number labels remain unchanged.

Let $T$ be the set of finite ordered binary trees with natural-number
labels at their leaves. "Ordered" means that a left child and a right
child are distinguished. Define two tree constructors:

- $\operatorname{leaf}(n)$ is a tree consisting of a single leaf
  labelled by $n\in\mathbb{N}$.
- $\operatorname{node}(t,u)$ is a tree with left subtree $t\in T$ and
  right subtree $u\in T$.

The structure map $\tau:\Sigma T\longrightarrow T$ is

$$
\tau(\operatorname{inl}(n))=\operatorname{leaf}(n),
\qquad
\tau(\operatorname{inr}(t,u))=\operatorname{node}(t,u).
$$

For example,

$$
\operatorname{node}
  \bigl(\operatorname{leaf}(2),\operatorname{leaf}(3)\bigr)
$$

is a tree with two leaves, labelled 2 and 3. The larger parentheses
have the same meaning as ordinary parentheses.

This algebra **constructs syntax**. It does not yet evaluate the tree
as an arithmetic expression.

For evaluation, give $\mathbb{N}$ a different $\Sigma$-algebra, with
structure map $\varepsilon:\Sigma\mathbb{N}\longrightarrow\mathbb{N}$:

$$
\varepsilon(\operatorname{inl}(n))=n,
\qquad
\varepsilon(\operatorname{inr}(m,n))=m+n.
$$

This algebra **interprets** a number label as itself and a pair as
addition. The same functor describes both syntax construction and one
possible interpretation.

### A.3. Algebra morphisms and initial algebras

#### Maps that preserve algebraic structure

Suppose $(A,\alpha)$ and $(B,\beta)$ are algebras for the same endofunctor
$F$. Here $B$ is a second carrier and
$\beta:FB\longrightarrow B$ is its structure map.

An **algebra morphism** from $(A,\alpha)$ to $(B,\beta)$ is a morphism
$h:A\longrightarrow B$ satisfying

$$
h\circ\alpha=\beta\circ Fh.
$$

Both sides are morphisms from $FA$ to $B$. The equation compares two
routes:

1. Combine inputs using $\alpha$, then apply $h$.
2. Apply $h$ to the inputs using $Fh$, then combine them using $\beta$.

**Preserving structure means that these routes give the same result.**

For the binary-operation example, this becomes

$$
h(\alpha(x,y))=\beta(h(x),h(y)),
$$

where $x,y\in A$. It says that $h$ preserves the binary operation.

Algebras for a fixed $F$, together with their algebra morphisms, form a
category. Its identities and composition are inherited from
$\mathcal{C}$.

#### Initiality: a unique map to every interpretation

An **initial $F$-algebra** is an $F$-algebra $(I,\iota)$ such that,
for every $F$-algebra $(A,\alpha)$, there is exactly one algebra morphism

$$
h:I\longrightarrow A.
$$

Here $I$ names the initial carrier and $\iota:FI\longrightarrow I$
its structure map. Initiality concerns the category of $F$-algebras,
not the original category $\mathcal{C}$.

The existence of the map says that the initial algebra can be
interpreted in any algebra of the same shape. Its uniqueness says that
preserving the operations completely determines the interpretation.
Such an interpretation is often called a **fold**.

#### Example: folding natural numbers

For $FX=\mathbf{1}+X$, the algebra
$(\mathbb{N},\alpha_{\mathbb{N}})$ from Example 2 is initial.

To see what its unique map does, let $(A,\alpha)$ be any algebra for
this functor. Define

$$
a_0=\alpha(\operatorname{inl}(\ast)),
\qquad
s(x)=\alpha(\operatorname{inr}(x)).
$$

Thus $a_0$ names the chosen element of $A$, and
$s:A\longrightarrow A$ names its unary operation.
The unique algebra morphism $h:\mathbb{N}\longrightarrow A$ obeys

$$
h(0)=a_0,
\qquad
h(n+1)=s(h(n)).
$$

These equations determine every value of $h$: begin with $a_0$ and
apply $s$ once for each successor.

For a concrete interpretation, take $A=\mathbb{N}$, $a_0=0$, and
$s(x)=x+2$. Then $h(0)=0$, $h(1)=2$, $h(2)=4$, and in general
$h(n)=2\cdot n$.

#### Example: folding expression trees

The tree algebra $(T,\tau)$ from Example 3 is initial for $\Sigma$.
Its unique algebra morphism to $(\mathbb{N},\varepsilon)$ is the
evaluation function, which we name
$\operatorname{eval}:T\longrightarrow\mathbb{N}$.

Preserving the constructors requires

$$
\operatorname{eval}(\operatorname{leaf}(n))=n,
$$

and

$$
\operatorname{eval}(\operatorname{node}(t,u))
  =\operatorname{eval}(t)+\operatorname{eval}(u).
$$

Consequently,

$$
\operatorname{eval}
  \bigl(\operatorname{node}
    (\operatorname{leaf}(2),\operatorname{leaf}(3))\bigr)=5.
$$

More generally, a $\Sigma$-algebra can interpret leaves in any carrier
and interpret a node using any chosen binary operation. Initiality
then gives a unique interpretation of every finite tree.

In these examples, initial algebras describe objects built by finitely
many constructor applications. This is an important pattern, not a
claim that every endofunctor on every category has such an algebra.

### A.4. What is a coalgebra?

For an endofunctor $F$, an **$F$-coalgebra** consists of:

1. An object $S$, called its **carrier**.
2. A morphism $c:S\longrightarrow FS$, called its **structure map**.

We write $(S,c)$ for this pair. In our computational examples in
$\mathbf{Set}$, the elements of $S$ are called **states**.

The direction of the structure map is the reverse of the algebra
direction:

$$
S\xrightarrow{c}FS.
$$

In these $\mathbf{Set}$ examples, the functor describes the shape of
an observation and its possible continuations. The map $c$ tells us
how to obtain that information from a state.

**In these examples, a coalgebra tells us how to observe or unfold a
state.** The general definition requires only the structure morphism
$c:S\longrightarrow FS$.

This need not be the inverse of an algebra map. Usually an observation
does not reconstruct the state from which it came.

#### Example 1: a system that repeatedly produces outputs

Let $O=\{0,1\}$ be a set of output symbols, and let $H$ name the
endofunctor

$$
HX=O\times X.
$$

For a function $f:X\longrightarrow Y$, define its action by

$$
Hf(o,x)=(o,f(x)),
$$

where $o\in O$ is the output component and $x\in X$ is the continuation
component. The output is unchanged.

An $H$-coalgebra has a structure map
$c:S\longrightarrow O\times S$. Each state supplies:

- Its next output.
- The state to use after that output.

For a concrete system, take $S=\{q_0,q_1\}$, where $q_0$ and $q_1$ name
two distinct states. Define

$$
c(q_0)=(0,q_1),
\qquad
c(q_1)=(1,q_0).
$$

Starting from $q_0$, repeated observations produce
$0,1,0,1,\ldots$. Starting from $q_1$, they produce
$1,0,1,0,\ldots$.

The structure map specifies only one observation at a time. The
infinite sequence arises by repeatedly applying it to the continuation.

#### Example 2: a system that can terminate

Return to the endofunctor $FX=\mathbf{1}+X$. A coalgebra now has a map

$$
c:S\longrightarrow\mathbf{1}+S.
$$

The two tagged alternatives mean:

- $\operatorname{inl}(\ast)$: terminate.
- $\operatorname{inr}(s)$, with $s\in S$: continue in state $s$.

For example, let
$\gamma:\mathbb{N}\longrightarrow\mathbf{1}+\mathbb{N}$ be the
countdown structure map

$$
\gamma(0)=\operatorname{inl}(\ast),
\qquad
\gamma(n+1)=\operatorname{inr}(n).
$$

Starting from 3, the continuation states are 2, then 1, then 0, where
the system terminates.

This uses exactly the same functor as the zero-and-successor algebra.
The algebra builds numbers; the coalgebra runs a countdown.
Coalgebras can therefore describe finite as well as infinite behaviour.

#### Example 3: a system with several possible transitions

Let $L$ be a set of action labels. For any set $Y$, write
$\mathcal{P}_f(Y)$ for the set of all finite subsets of $Y$.
Let $B$ now name the endofunctor

$$
BX=\mathcal{P}_f(L\times X).
$$

For a function $f:X\longrightarrow Y$, the function $Bf$ transforms
each finite set of labelled successors by replacing every pair
$(\ell,x)$ with $(\ell,f(x))$, where $\ell\in L$ is a label and
$x\in X$ is a successor. Repeated resulting pairs count only once,
because the result is a set.

A $B$-coalgebra with state set $Q$ has a structure map

$$
\delta:Q\longrightarrow\mathcal{P}_f(L\times Q).
$$

For each state, it lists the finitely many possible labelled next
states. This is a **finitely branching labelled transition system**.
"Finitely branching" restricts each state's number of outgoing
transitions; it does not require $Q$ to be finite.

For example, take $Q=\{p,r\}$ and $L=\{a,b\}$, where $p,r$ are states
and $a,b$ are action labels. Define

$$
\delta(p)=\{(a,p),(b,r)\},
\qquad
\delta(r)=\varnothing.
$$

Here $\varnothing$ denotes the empty set.
State $p$ can perform action $a$ and return to itself, or perform
action $b$ and move to $r$. State $r$ has no outgoing transitions.
The coalgebra does not select which alternative will occur.
Without further information, having no outgoing transitions need not
distinguish successful termination from a stuck state.

We can write $p\xrightarrow{a}p$ and $p\xrightarrow{b}r$ for these
transitions. More generally, the notation
$q\xrightarrow{\ell}q'$ means that $(\ell,q')$ is an element of
$\delta(q)$, where $q,q'\in Q$ are states.
These labelled arrows denote transitions, not functions between sets.

### A.5. Coalgebra morphisms and final coalgebras

#### Maps that preserve observations

Suppose $(S,c)$ and $(R,d)$ are coalgebras for the same endofunctor
$F$. Here $R$ is a second carrier and $d:R\longrightarrow FR$ is
its structure map.

A **coalgebra morphism** from $(S,c)$ to $(R,d)$ is a morphism
$h:S\longrightarrow R$ satisfying

$$
d\circ h=Fh\circ c.
$$

Both sides are morphisms from $S$ to $FR$. The equation compares
two routes:

1. Map the state using $h$, then observe it using $d$.
2. Observe the original state using $c$, then map its continuations
   using $Fh$.

**Preserving observations means that these routes give the same result.**

For the output functor $HX=O\times X$, if $c(s)=(o,s')$, where
$s,s'\in S$, this requirement says

$$
d(h(s))=(o,h(s')).
$$

The output must agree, and the successor states must correspond.

Coalgebras for a fixed $F$, together with their coalgebra morphisms,
form a category, with identities and composition inherited from
$\mathcal{C}$.

#### Finality: a unique map from every state system

A **final $F$-coalgebra** is an $F$-coalgebra $(Z,\zeta)$ such that,
for every $F$-coalgebra $(S,c)$, there is exactly one coalgebra morphism

$$
b:S\longrightarrow Z.
$$

Here $Z$ names the final carrier and $\zeta:Z\longrightarrow FZ$
its structure map. Finality concerns the category of $F$-coalgebras,
not the original category $\mathcal{C}$.

Compare the directions:

- An initial algebra has a unique structure-preserving map **to**
  every algebra.
- A final coalgebra receives a unique structure-preserving map
  **from** every coalgebra.

In behavioural examples, the map $b$ assigns each state its complete
observable behaviour. This assignment is often called an **unfold**.

#### Example: streams are the final output coalgebra

For $HX=O\times X$, the final carrier is the set of infinite streams
of symbols from $O$.

We write this set as $O^{\mathbb{N}}$. The superscript means a function
set: its elements are functions from $\mathbb{N}$ to $O$.
Such a function is a stream, because it specifies an output at every
position numbered $0,1,2,\ldots$.

For a stream $u\in O^{\mathbb{N}}$, write $u[n]$ for its output at
position $n\in\mathbb{N}$. Define its **tail**, named
$\operatorname{tail}(u)$, by

$$
\operatorname{tail}(u)[n]=u[n+1].
$$

The final structure map
$\zeta:O^{\mathbb{N}}\longrightarrow O\times O^{\mathbb{N}}$ is

$$
\zeta(u)=(u[0],\operatorname{tail}(u)).
$$

It reveals the first output and the remaining stream.

Given any coalgebra $c:S\longrightarrow O\times S$, its unique map
$b:S\longrightarrow O^{\mathbb{N}}$ assigns a stream to each state.
If $c(s)=(o,s')$, preserving observations requires

$$
b(s)[0]=o,
\qquad
\operatorname{tail}(b(s))=b(s').
$$

These equations determine the first output, then the second, then
every later output. That explains both the existence and the
uniqueness of the stream assignment.

For the two-state system in A.4, the stream assigned to $q_0$ is
$0,1,0,1,\ldots$, and the stream assigned to $q_1$ is
$1,0,1,0,\ldots$.

Different internal states can nevertheless have the same stream.
For a concrete example, define another $H$-coalgebra with carrier
$\mathbb{N}$ and structure map
$e:\mathbb{N}\longrightarrow O\times\mathbb{N}$ by

$$
e(n)=(\operatorname{parity}(n),n+1),
$$

where $\operatorname{parity}(n)$ is 0 when $n$ is even and 1 when
$n$ is odd. Even numbers are multiples of 2; odd numbers are one
more than a multiple of 2.

States 0 and 2 are different natural numbers, but both generate the
stream $0,1,0,1,\ldots$.

More generally, when a final coalgebra exists, we define two states
$s,t\in S$ to be **behaviourally equivalent** when

$$
b(s)=b(t).
$$

The chosen functor determines what is observed. For our stream
functor, behavioural equivalence means equality of output streams.
For finitely branching labelled transition systems, it corresponds
to strong bisimilarity: each transition from either state can be
matched by a transition with the same label from the other, leading
to states that are again related.

Final coalgebras do not exist for every endofunctor on every
category. Their existence must be established in the setting being
used.

### A.6. What is dual, and what is not?

The algebra and coalgebra definitions have opposite arrow directions:

| Concept | Algebra | Coalgebra |
| --- | --- | --- |
| Structure map | $\alpha:FA\longrightarrow A$ | $c:S\longrightarrow FS$ |
| Typical role in the $\mathbf{Set}$ examples | Construct or interpret | Observe and continue |
| Structure-preserving map | Commutes with combination | Commutes with observation |
| Universal object, when it exists | Initial algebra | Final coalgebra |
| Universal map | From the initial algebra | Into the final coalgebra |
| Typical operation on an example | Fold a finite tree | Unfold a state into a stream |

The arrows can be reversed formally by passing to the **opposite
category**, written $\mathcal{C}^{\mathrm{op}}$: it has the same
objects as $\mathcal{C}$, but all morphisms point in the opposite
direction. The superscript $\mathrm{op}$ indicates this reversal.
An $F$-coalgebra in $\mathcal{C}$ is an algebra in the opposite
category for the induced endofunctor $F^{\mathrm{op}}$, which applies
$F$ to the corresponding objects and reversed morphisms.
In this precise sense, coalgebras are dual to algebras.

However, several tempting conclusions are false:

- An arbitrary algebra map and an arbitrary coalgebra map are not
  inverses.
- An arbitrary algebra is not initial, and an arbitrary coalgebra is
  not final.
- A coalgebra need not have infinite executions; the countdown
  example terminates.
- An initial algebra is not an initial object of the underlying
  category, and a final coalgebra is not a final object of that
  category. The universal properties concern structure-preserving
  maps.
- Having the same observable behaviour does not require having the
  same internal state representation.

### A.7. A different class of examples: an ordered category

The examples in A.2-A.5 all used $\mathcal{C}=\mathbf{Set}$. We now
change the category, while keeping the general definitions of
algebra and coalgebra unchanged.

#### Turning the rational numbers into a category

Let $\mathbb{Q}$ denote the rational numbers: numbers expressible
as fractions of integers with a nonzero denominator. In this section,
$\mathcal{C}$ denotes the following category:

- Its objects are the individual rational numbers.
- For rational numbers $p,q\in\mathbb{Q}$, there is exactly one
  morphism $p\longrightarrow q$ when $p\leq q$, and none otherwise.
  The symbol $\leq$ denotes the usual numerical ordering.
- The identity on $p$ exists because $p\leq p$.
- If $r\in\mathbb{Q}$ is another rational number, arrows
  $p\longrightarrow q$ and $q\longrightarrow r$ compose to the unique
  arrow $p\longrightarrow r$. This is possible because the ordering
  is transitive: $p\leq q$ and $q\leq r$ imply $p\leq r$.

Associativity and the identity laws hold because there is at most
one morphism between any two objects.

This construction is often called the **category associated with
an ordered set**. It is not $\mathbf{Set}$: its objects are individual
numbers, not sets used as carriers, and its arrows represent
inequalities, not functions between those numbers.

#### The endofunctor: halve each object

Define an endofunctor $F:\mathcal{C}\longrightarrow\mathcal{C}$ by

$$
F(p)=\frac{p}{2}.
$$

The fraction means ordinary arithmetic division by 2. The notation
$F(p)$ is another way of writing the functor's action on an object,
previously written $Fp$.

If $f:p\longrightarrow q$ is a morphism, define $Ff$ to be the
unique morphism

$$
Ff:\frac{p}{2}\longrightarrow\frac{q}{2}.
$$

This morphism exists because halving preserves the inequality:
$p\leq q$ implies $p/2\leq q/2$. The functor preserves identities
and composition because arrows with the required endpoints are
unique.

#### An algebra: an inequality from the halved object to the carrier

An $F$-algebra consists of a rational-number object $a$ and a
structure morphism

$$
\alpha:F(a)\longrightarrow a.
$$

Here $a$ names the carrier object, and $\alpha$ names its structure
morphism. Such a morphism exists precisely when

$$
\frac{a}{2}\leq a.
$$

For example, choose $a=2$. Since $F(2)=1$, its algebra structure is
the unique arrow

$$
\alpha:1\longrightarrow 2.
$$

This arrow exists because $1\leq 2$. The numbers 1 and 2 here are
objects of the ordered category; 1 is not the singleton set
$\mathbf{1}$ used in the earlier examples.

More generally, $a/2\leq a$ holds exactly when $a\geq 0$, where
$\geq$ denotes the reverse numerical ordering. Thus **every
nonnegative rational number has an $F$-algebra structure**, and no
negative rational number does. When the structure morphism exists,
it is unique.

#### A coalgebra: an inequality in the other direction

An $F$-coalgebra consists of a rational-number object $s$ and a
structure morphism

$$
c:s\longrightarrow F(s).
$$

Here $s$ names the carrier object, and $c$ names its structure
morphism. Such a morphism exists precisely when

$$
s\leq\frac{s}{2}.
$$

For example, choose $s=-2$. Since $F(-2)=-1$, its coalgebra structure
is the unique arrow

$$
c:-2\longrightarrow -1.
$$

This arrow exists because $-2\leq -1$.

More generally, $s\leq s/2$ holds exactly when $s\leq 0$. Thus
**every nonpositive rational number has an $F$-coalgebra structure**,
and no positive rational number does. Again, the structure morphism
is unique when it exists.

Zero carries both structures, since $F(0)=0$ and the required
structure morphism in either case is the identity
$\operatorname{id}_0:0\longrightarrow 0$.

#### What changes, and what stays the same?

Both examples use the same ordered category and the same halving
endofunctor. Their difference is the direction of the structure arrow:

- An algebra requires an arrow from the transformed object to the
  carrier.
- A coalgebra requires an arrow from the carrier to the transformed
  object.

There are no input elements to combine or output streams to reveal
in these examples. Instead, the structure arrows express oppositely
directed inequalities.

The construction and observation pictures from $\mathbf{Set}$ are
therefore useful interpretations of the definitions, not requirements
that all algebras and coalgebras must satisfy.

### A.8. Why this matters for operational semantics

In the approach we will explore, **syntax and behaviour have different
roles**:

- A syntax functor describes program constructors. Its initial
  algebra, when available, gives the program terms.
- An algebra interpreting those constructors gives a compositional
  interpretation: the interpretation of a compound term is obtained
  from the interpretations of its components.
- A behaviour functor describes observations and continuations.
  A coalgebra on program terms supplies their operational behaviour.
- A final coalgebra, when available, gives a domain of complete
  behaviours and a unique map assigning a behaviour to each program.

The syntax functor and the behaviour functor need not be the same.
The examples above showed the two kinds of structure independently.

Turi and Plotkin's central question is how to make them **compatible**:
how can the rules describing a compound program's execution ensure
that combining programs also combines their meanings consistently?

Algebras and coalgebras supply the two sides of that question. The
additional compatibility law connecting them is the next topic; it
is not implied merely by having both kinds of structure.

### Further reading

- Daniele Turi and Gordon Plotkin,
  [Towards a Mathematical Operational Semantics](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf),
  1997. The foundational application to operational semantics.
- Bartek Klin,
  [Bialgebras for Structural Operational Semantics: An Introduction](https://www.cs.ox.ac.uk/people/bartek.klin/papers/tcs11.pdf),
  2011. An introduction and survey with additional examples.

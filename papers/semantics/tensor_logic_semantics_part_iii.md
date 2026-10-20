# Tensor Logic semantics - Part III: Denotational semantics

[Previous: Part II: Core language and surface elaboration](tensor_logic_semantics_part_ii.md) | [Contents](README.md) | [Next: Part IV: Operational semantics](tensor_logic_semantics_part_iv.md)

## In this part

- [Part III: Denotational semantics](#part-iii-denotational-semantics)
- [18. Expression interpretation and definedness](#18-expression-interpretation-and-definedness)
  - [18.1 Successful and undefined results](#181-successful-and-undefined-results)
  - [18.2 Scalar constructors](#182-scalar-constructors)
  - [18.3 Reduction and tabulation](#183-reduction-and-tabulation)
  - [18.4 Array selection and primitive application](#184-array-selection-and-primitive-application)
  - [18.5 Definedness examples and transformation limits](#185-definedness-examples-and-transformation-limits)
- [19. Contribution collection](#19-contribution-collection)
  - [19.1 Environments with defined contributions](#191-environments-with-defined-contributions)
  - [19.2 Statement contributions and collected tensors](#192-statement-contributions-and-collected-tensors)
  - [19.3 Correspondence with pure einsum](#193-correspondence-with-pure-einsum)
  - [19.4 Source order and nonlinear boundaries](#194-source-order-and-nonlinear-boundaries)
- [20. Program models and functional denotation](#20-program-models-and-functional-denotation)
  - [20.1 Models on supplied inputs](#201-models-on-supplied-inputs)
  - [20.2 A partial equation operator](#202-a-partial-equation-operator)
  - [20.3 Functional admissibility](#203-functional-admissibility)
  - [20.4 Denotation does not imply executability](#204-denotation-does-not-imply-executability)
- [21. Worked denotational examples](#21-worked-denotational-examples)
  - [21.1 Duplicate contributions and zero defaults](#211-duplicate-contributions-and-zero-defaults)
  - [21.2 An intermediate fixes the activation boundary](#212-an-intermediate-fixes-the-activation-boundary)
  - [21.3 A guard differs from a zero multiplier](#213-a-guard-differs-from-a-zero-multiplier)
  - [21.4 Three different cyclic equation systems](#214-three-different-cyclic-equation-systems)
  - [21.5 Bounded histories have simultaneous equations too](#215-bounded-histories-have-simultaneous-equations-too)
- [22. Denotational scope and execution requirements](#22-denotational-scope-and-execution-requirements)

## Part III: Denotational semantics

Denotational semantics describes values and equations without prescribing
how a machine computes them. In this part, $\textcolor{#398B83}{\rho}$ is always a complete,
signature-respecting environment as defined in [Section 5](tensor_logic_semantics_part_i.md#5-environments-and-stores). It supplies
candidate values even for tensors that the program defines.

Reading $\textcolor{#398B83}{\rho}(T)$ does not recursively execute statements defining $T$.
Instead, expression interpretation uses those candidate values, and
the program equations determine whether the environment is a model.
This distinction allows the same definitions to describe both acyclic
programs and cyclic equation systems.

## 18. Expression interpretation and definedness

### 18.1 Successful and undefined results

For an expression value type $\textcolor{#5688C7}{\tau}$ from [Section 13.2](tensor_logic_semantics_part_ii.md#132-value-types-and-primitive-signatures), define the result
space

```math
\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau})=\textcolor{#5688C7}{\tau}\sqcup\{\textcolor{#398B83}{\bot}\}.
```

This is a tagged disjoint union. A member of $\textcolor{#5688C7}{\tau}$ is a successful
value; $\textcolor{#398B83}{\bot}$ denotes an undefined result. We write $v$ for the
successful tag carrying value $v$.

The symbol $\textcolor{#398B83}{\bot}$ is not a scalar zero, a missing-store entry, a
floating-point NaN, or a selected solution of an equation. No order
or least-fixed-point interpretation is attached to it.

For a structurally well-formed expression
$\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma};\textcolor{#5688C7}{D}\vdash \textcolor{#9D75C4}{E}:\textcolor{#5688C7}{\tau}$, a complete environment $\textcolor{#398B83}{\rho}$, and
$\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}$, define

```math
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}\in\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau}).
```

Index expressions and predicates have the total interpretations already
introduced: integer arithmetic for $\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{e}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#5688C7}{\nu}}$ and
Boolean operations for $\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{Q}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#5688C7}{\nu}}$.
The result space is needed for value-dependent primitive applications,
not to excuse malformed tensor accesses.

Use the notation

```math
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}\downarrow v
```

to mean that the result is the successful value $v$, and

```math
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}=\textcolor{#398B83}{\bot}
```

to mean that it is undefined. The downward arrow on an expression
means definedness, not operational termination.
The separate $\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\Downarrow}\textcolor{#398B83}{\rho}$ notation denotes successful
machine execution in [Part IV](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics).

### 18.2 Scalar constructors

Scalar literals, named tensor reads, and Iverson values are interpreted by

```math
\textcolor{#398B83}{\mathopen{[\![}} c_K\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}=c_K,
```

```math
\textcolor{#398B83}{\mathopen{[\![}} T[\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_k]\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\textcolor{#398B83}{\rho}(T)[
 \textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{e}_1\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#5688C7}{\nu}},\ldots,
 \textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{e}_k\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#5688C7}{\nu}}],
```

```math
\textcolor{#398B83}{\mathopen{[\![}}\mathbf{1}_{\textcolor{#9D75C4}{Q}}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\begin{cases}
1_K,&\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{Q}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#5688C7}{\nu}}=\mathrm{true},\\
0_K,&\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{Q}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#5688C7}{\nu}}=\mathrm{false}.
\end{cases}
```

The read is valid by the structural premises and $\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}$.
For a scalar tensor, its index tuple is empty.

For $\star\in\{\oplus,\otimes\}$, define the strict lifting

```math
\textcolor{#398B83}{\mathop{\mathrm{lift}}\nolimits}_2(\star,u,v)
=
\begin{cases}
u\star v,&u,v\text{ are successful scalar values},\\
\textcolor{#398B83}{\bot},&\text{otherwise}.
\end{cases}
```

Then

```math
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}_1\star \textcolor{#9D75C4}{E}_2\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\textcolor{#398B83}{\mathop{\mathrm{lift}}\nolimits}_2\left(
 \star,\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}_1\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}},
 \textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}_2\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
\right).
```

Both operands must be defined, even when one is $0_K$.
This lifting is not an assertion that
$\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(K)$ itself forms the scalar semiring.
For instance, multiplying a successful zero by $\textcolor{#398B83}{\bot}$ gives $\textcolor{#398B83}{\bot}$,
not a successful zero.

### 18.3 Reduction and tabulation

For a reduction, let
$v_k=\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}[j\mapsto k]}$ for each
$k\in \textcolor{#5688C7}{I}_j$. Define

```math
\textcolor{#398B83}{\mathopen{[\![}}\bigoplus_{j\in \textcolor{#5688C7}{I}_j}\textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\begin{cases}
\displaystyle\bigoplus_{k\in \textcolor{#5688C7}{I}_j}v_k,
 &\text{every }v_k\text{ is successful},\\
\textcolor{#398B83}{\bot},&\text{otherwise}.
\end{cases}
```

Here $\bigoplus_{k\in\textcolor{#5688C7}{I}_j}v_k$ is the fold of $\oplus$ over the ascending enumeration of
$\textcolor{#5688C7}{I}_j$, which needs no law; it equals the finite combination of
[Section 2.2](tensor_logic_semantics_part_i.md#22-finite-sums-and-products) under the monoid laws ([Section 2.3](tensor_logic_semantics_part_i.md#23-which-algebraic-laws-each-part-uses)).
An empty reduction succeeds with $0_K$. Its body is not interpreted
at any valuation, so an unreachable primitive application does not
cause undefinedness.

For tabulation, let $\textcolor{#5688C7}{J}=\textcolor{#5688C7}{I}_1\times\cdots\times \textcolor{#5688C7}{I}_m$ and define the extended
valuation for $p=(p_1,\ldots,p_m)\in \textcolor{#5688C7}{J}$ by

```math
\textcolor{#5688C7}{\nu}_p=\textcolor{#5688C7}{\nu}[j_1\mapsto p_1,\ldots,j_m\mapsto p_m].
```

The tabulation result is

```math
\textcolor{#398B83}{\mathopen{[\![}}
\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j_1\in \textcolor{#5688C7}{I}_1,\ldots,j_m\in \textcolor{#5688C7}{I}_m}(\textcolor{#9D75C4}{E})
\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\begin{cases}
\textcolor{#398B83}{V},&
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}_p}\downarrow \textcolor{#398B83}{V}[p]
\text{ for every }p\in \textcolor{#5688C7}{J},\\
\textcolor{#398B83}{\bot},&\text{some body result is undefined}.
\end{cases}
```

Here $\textcolor{#398B83}{V}:\textcolor{#5688C7}{J}\to K$ is a complete array value.
An empty $\textcolor{#5688C7}{J}$ produces the unique empty array successfully.
These binders use exactly the lifted domains from [Section 14.1](tensor_logic_semantics_part_ii.md#141-judgments-and-admissible-valuations).

### 18.4 Array selection and primitive application

For array selection, let
$p=(\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{e}_1\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#5688C7}{\nu}},\ldots,\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{e}_m\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#5688C7}{\nu}})$.
Then

```math
\textcolor{#398B83}{\mathopen{[\![}}\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}(\textcolor{#9D75C4}{E},(\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_m))\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\begin{cases}
\textcolor{#398B83}{V}[p],&\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}\downarrow \textcolor{#398B83}{V},\\
\textcolor{#398B83}{\bot},&\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}=\textcolor{#398B83}{\bot}.
\end{cases}
```

The structural rule guarantees that $p$ belongs to the array domain.
Selection requires the array expression to denote a complete value.
It does not bypass an undefined element of a tabulation by selecting
a different coordinate.

For a primitive $f$ with arity $q$, interpret its operands and let
$u_r=\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}_r\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}$. Define

```math
\textcolor{#398B83}{\mathopen{[\![}} f(\textcolor{#9D75C4}{E}_1,\ldots,\textcolor{#9D75C4}{E}_q)\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=
\begin{cases}
f(u_1,\ldots,u_q),
 &\text{all }u_r\text{ are successful and }
 (u_1,\ldots,u_q)\in\textcolor{#398B83}{\mathcal{D}}_f,\\
\textcolor{#398B83}{\bot},&\text{otherwise}.
\end{cases}
```

The primitive's signature guarantees the successful result has its
declared type. Its domain $\textcolor{#398B83}{\mathcal{D}}_f$ determines definedness;
typing alone does not.
For a nullary primitive, its argument tuple is $()$ and the same
domain-membership rule applies.

### 18.5 Definedness examples and transformation limits

Work over exact reals. The following results illustrate strictness:

```math
\textcolor{#398B83}{\mathopen{[\![}}\log(-1)\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}=\textcolor{#398B83}{\bot},
\qquad
\textcolor{#398B83}{\mathopen{[\![}} 0\cdot\log(-1)\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}=\textcolor{#398B83}{\bot},
```

```math
\textcolor{#398B83}{\mathopen{[\![}}\bigoplus_{j\in[0]}\log(-1)\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}=0.
```

The empty reduction has no body instances. Multiplication by zero,
by contrast, still has an undefined operand.

If $X$ has shape $(2)$ with $\textcolor{#398B83}{\rho}(X)[0]=4$ and $\textcolor{#398B83}{\rho}(X)[1]=-1$, then

```math
\textcolor{#398B83}{\mathopen{[\![}}
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
 \textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[2]}(\log(X[j])),(0)
\right)
\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=\textcolor{#398B83}{\bot}.
```

The selected coordinate would be positive before taking its logarithm,
but the array construction includes the invalid logarithm at coordinate
$1$. This is a deliberate complete-array interpretation, not lazy
coordinate selection.

Therefore, transformations involving partial primitives must preserve
both values and definedness. Replacing $0\cdot \textcolor{#9D75C4}{E}$ by $0$ is unsound when
$\textcolor{#9D75C4}{E}$ can be undefined. The pure semiring transformations of [Section 17](tensor_logic_semantics_part_ii.md#17-pure-einsum-semantics-and-transformation-foundations)
do not have this problem: their structurally valid reads and semiring
operations are total on complete environments.

## 19. Contribution collection

The Lean status of Sections [19](#19-contribution-collection)–[20](#20-program-models-and-functional-denotation) is recorded in
[Proof status and numbered results](tensor_logic_semantics.md#proof-status-and-numbered-results).
[Section 19.3](#193-correspondence-with-pure-einsum)'s pure-einsum elaboration correspondence (Proposition 19.1)
is proved in Lean for the bounded source fragment only (see the status table).

### 19.1 Environments with defined contributions

For a structurally well-formed program $\textcolor{#9D75C4}{P}$, define

```math
\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})
=
\left\{
\textcolor{#398B83}{\rho}\ \middle|\
\begin{array}{l}
\textcolor{#398B83}{\rho}\text{ is a complete, signature-respecting environment, and}\\
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}\ne\textcolor{#398B83}{\bot}
\text{ for every }(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\in\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}
\end{array}
\right\}.
```

Membership says all actual contribution bodies are defined. It does
not yet say the environment satisfies the program's equations.

Guards affect $\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}$ through $\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$, before interpreting bodies.
A valuation excluded by a guard imposes no body-definedness obligation.
Likewise, a statement with an empty occurrence domain imposes none.
In contrast, a present zero-valued contribution must still be defined.

### 19.2 Statement contributions and collected tensors

For $\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$, define the contribution tensor
of one statement:

```math
\textcolor{#398B83}{V}_{\textcolor{#9D75C4}{s}}^{\textcolor{#398B83}{\rho}}[p]
=
\bigoplus_{\substack{\textcolor{#5688C7}{\nu}\in \textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}\\\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu})=p}}
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}},
\qquad p\in\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T_{\textcolor{#9D75C4}{s}}).
```

Each term here is a successful scalar value; $\textcolor{#398B83}{\bot}$ is never treated
as a summand.
An empty fiber gives $0_K$.

For every defined tensor $T$, define its collected value:

```math
\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[p]
=
\bigoplus_{(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\in\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T,p)}
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}.
```

Equivalently, partitioning the occurrences by statement gives

```math
\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[p]
=
\bigoplus_{\substack{\textcolor{#9D75C4}{s}\in \textcolor{#9D75C4}{P}\\T_{\textcolor{#9D75C4}{s}}=T}}\textcolor{#398B83}{V}_{\textcolor{#9D75C4}{s}}^{\textcolor{#398B83}{\rho}}[p].
```

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

**Collection through per-statement tensors.** Because $\oplus$ is
associative and commutative, the occurrences addressed to $(T,p)$ may be grouped
by statement. If $T$ is targeted by statements $s_1,\ldots,s_n$ and $T_k$ is a
fresh defined tensor of the same signature and sort targeted only by $s_k$,
then $\mathop{\mathrm{Collect}}(T)[p]=\bigoplus_{k}\mathop{\mathrm{Collect}}(T_k)[p]$.
This is the statement-wise grouping of the Lean `Program.collect_grouped`. A program in which
$T$ is replaced by $T_1,\ldots,T_n$ and one collector statement
$T[\vec{i}]\mathrel{+}=T_1[\vec{i}]+\cdots+T_n[\vec{i}]$ (the sum
in the sort of $T$, in statement order) therefore defines the same value of
$T$. A compiler may collect multiple definitions this way. The result is
independent of the grouping, and the order of the summands has no semantic
meaning.

### 19.3 Correspondence with pure einsum

**Proposition 19.1 (pure-einsum correspondence).**
For the normalized pure-einsum statement of [Section 17.3](tensor_logic_semantics_part_ii.md#173-connection-to-the-contribution-core),
the intended local correspondence is

```math
\textcolor{#398B83}{V}_{\textcolor{#9D75C4}{s}}^{\textcolor{#398B83}{\rho}}[p]=\textcolor{#398B83}{V}_{\textcolor{#5688C7}{L}}[p]
```

for every output coordinate, with $\textcolor{#398B83}{V}_{\textcolor{#5688C7}{L}}$ computed from the same operand
values in $\textcolor{#398B83}{\rho}$ by [Section 17.2](tensor_logic_semantics_part_ii.md#172-canonical-fiber-semantics).
This statement applies whenever the contribution tensor is defined;
the pure statement itself has no partial primitive applications.

The mathematical proof decomposes a global valuation into the values
of distinct output variables and the remaining contracted variables.
The core body combines over the latter, while the write fiber combines
over the former. This uses only the commutative-monoid laws of
$\oplus$, coherence, and the bracketing convention ([Section 2.3](tensor_logic_semantics_part_i.md#23-which-algebraic-laws-each-part-uses)), not
distributivity. The resulting finite
combinations enumerate exactly the assignments in $\textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}}^{-1}(\{p\})$.

Repeated output indices can leave an empty fiber, and an empty
contracted domain can leave an empty reduction. Both sides then use
the same $0_K$ convention. With no variables, the single empty
valuation yields the scalar operand product.

The proof description here is a paper argument. A Lean proof exists for the
bounded source fragment (see the status table); it covers repeated slots, empty
contractions, zero extents, factor order, multiplicity, and the order of nested
reductions (`interpret_contract_reindex`).

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

```math
f(\textcolor{#398B83}{\rho}(A)[i])\oplus f(\textcolor{#398B83}{\rho}(B)[i]),
```

provided both applications are defined.
An intermediate defined by contributions $A[i]$ and $B[i]$, followed
by a read through $f$, is related by the program equations to

```math
f(\textcolor{#398B83}{\rho}(A)[i]\oplus\textcolor{#398B83}{\rho}(B)[i]).
```

These are equal only under an appropriate property of $f$ on the
relevant values. The semantics assumes no such property.

## 20. Program models and functional denotation

### 20.1 Models on supplied inputs

An input environment $\textcolor{#398B83}{\eta}$ is well-typed when it supplies a value
with the prescribed coordinate domain and carrier for every identifier
in $\textcolor{#5688C7}{\mathrm{In}}$, and its identifier domain is exactly $\textcolor{#5688C7}{\mathrm{In}}$.

For such an $\textcolor{#398B83}{\eta}$, define

```math
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
```

All defined tensors participate in these equations, not just
designated outputs. Zero defaults follow from empty contribution
collections, rather than from an extra initialization equation.

Thus the unconditional denotational meaning of a structurally
well-formed program is its model relation: it associates each
well-typed input environment with its set of models.
That set can be empty, a singleton, or contain several environments.

### 20.2 A partial equation operator

The same definition can be expressed using the partial map

```math
\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}:\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})\to
\{\text{complete, signature-respecting environments}\},
```

given by

```math
\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)=
\begin{cases}
\textcolor{#398B83}{\rho}(T),&T\in\textcolor{#5688C7}{\mathrm{In}},\\
\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T),&T\in\textcolor{#5688C7}{\mathrm{Def}}.
\end{cases}
```

It is partial relative to the space of all complete environments,
because its domain is $\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$.
Its result need not itself belong to $\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$.
For example, for the scalar statement `T[] = log(T[])`, a candidate
value $T=1$ makes the contribution defined, but $\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}$ produces
$T=0$, at which the same contribution is undefined.

A model is exactly an environment $\textcolor{#398B83}{\rho}$ extending $\textcolor{#398B83}{\eta}$ for which
$\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}$ is defined and

```math
\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})=\textcolor{#398B83}{\rho}.
```

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

```math
\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P})
=
\{\textcolor{#398B83}{\eta}\in\textcolor{#398B83}{\mathop{\mathrm{Input}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}
\mid\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})
\text{ contains exactly one environment}\}.
```

For $\textcolor{#398B83}{\eta}\in\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P})$ with unique model $\textcolor{#398B83}{\rho}_{\textcolor{#398B83}{\eta}}$,
define

```math
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\mathclose{]\!]}}(\textcolor{#398B83}{\eta})=\textcolor{#398B83}{\rho}_{\textcolor{#398B83}{\eta}}|_{\textcolor{#5688C7}{\mathrm{Out}}}.
```

This gives a partial function

```math
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\mathclose{]\!]}}:
\textcolor{#398B83}{\mathop{\mathrm{Input}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}
\rightharpoonup\textcolor{#398B83}{\mathop{\mathrm{Output}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}.
```

Here the function domain is precisely $\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P})$.
If an application specifies an input class
$\textcolor{#398B83}{\mathcal{A}}\subseteq\textcolor{#398B83}{\mathop{\mathrm{Input}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}$, total functional
meaning on that class requires

```math
\textcolor{#398B83}{\mathcal{A}}\subseteq\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P}).
```

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

```math
\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[0]=4,
\qquad
\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[1]=10.
```

The model equations therefore force the unique output $T=(4,10)$.
There is no previous value of $T$ added to those entries.

For the boundary example in [Section 11.1](tensor_logic_semantics_part_i.md#111-boundary-contributions), the same definition gives
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

```math
\mathop{\mathrm{Pre}}\nolimits[i]=0,\qquad T[i]=0.
```

The distinction follows from collected equations, not from the order
in which the statements are listed.

### 21.3 A guard differs from a zero multiplier

Let $X$ be a real input of shape $(2)$ with values $4,-1$, and let
$Y$ be a defined output of shape $(2)$.
The guarded core statement

```math
\text{for }i\in[2]\text{ where }i<1:
\quad Y[i]\textcolor{#9D75C4}{\mathrel{+}=}\log(X[i])
```

has only the occurrence $i=0$. Its unique model gives

```math
Y[0]=\log(4),\qquad Y[1]=0.
```

Replacing the guard by an Iverson multiplier gives

```math
\text{for }i\in[2]:
\quad Y[i]\textcolor{#9D75C4}{\mathrel{+}=}\mathbf{1}_{i<1}\log(X[i]).
```

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

For the finite-history program in [Section 11.4](tensor_logic_semantics_part_i.md#114-a-finite-history-with-persistent-input), assume
$F:\mathbb{R}^{[d]}\to\mathbb{R}^{[d]}$ is total.
The collected equations are

```math
H_0=X+Z,
\qquad
H_{l+1}=X+F(H_l)\quad(l\in[N]).
```

They determine a unique history for every well-typed $X,Z$:
construct $H_0$, then the successive slices. Induction on time shows
that any other model must agree at time zero and at each following
slice. Totality and the stated array signature of $F$ ensure that
each constructed slice is defined and has the required domain.

For $d=1$, $N=2$, $X[0]=2$, $Z[0]=3$, and $F(h)[0]=2h[0]$, the
history entries are

```math
H[0,0]=5,\qquad H[0,1]=12,\qquad H[0,2]=26.
```

When $N=0$, only the base slice is present. The recurrence statement
has no occurrences and does not create an additional equation.
This establishes the mathematical history meaning. [Part IV](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics) explains how
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
them with mutation-order rules. [Part IV](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics) supplies a direct executor for the
coordinate-ranked fragment.
It uses complete logical values, not guesses obtained by iterating $\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}$.
Its correspondence is with the unique-model meaning of [Section 20](#20-program-models-and-functional-denotation), not
with a newly selected least model or mutation-order interpretation.

---

[Previous: Part II: Core language and surface elaboration](tensor_logic_semantics_part_ii.md) | [Contents](README.md) | [Next: Part IV: Operational semantics](tensor_logic_semantics_part_iv.md)

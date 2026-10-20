# Tensor Logic semantics - Part IV: Operational semantics

[Previous: Part III: Denotational semantics](tensor_logic_semantics_part_iii.md) | [Contents](README.md) | [Next: Part V: Compilation and refinement](tensor_logic_semantics_part_v.md)

## In this part

- [Part IV: Operational semantics](#part-iv-operational-semantics)
- [23. Read footprints and executable dependencies](#23-read-footprints-and-executable-dependencies)
  - [23.1 Address partitions](#231-address-partitions)
  - [23.2 Read footprints of expressions](#232-read-footprints-of-expressions)
  - [23.3 Stable evaluation from a partial store](#233-stable-evaluation-from-a-partial-store)
  - [23.4 Coordinate dependencies and the ranked fragment](#234-coordinate-dependencies-and-the-ranked-fragment)
- [24. Machine configurations and initialization](#24-machine-configurations-and-initialization)
  - [24.1 Published values, accumulators, and pending occurrences](#241-published-values-accumulators-and-pending-occurrences)
  - [24.2 Initial configuration](#242-initial-configuration)
- [25. Execution rules and terminal outcomes](#25-execution-rules-and-terminal-outcomes)
  - [25.1 Consume a defined contribution](#251-consume-a-defined-contribution)
  - [25.2 Publish a completed coordinate](#252-publish-a-completed-coordinate)
  - [25.3 Surface undefined operations](#253-surface-undefined-operations)
  - [25.4 Completion and dependency blocking](#254-completion-and-dependency-blocking)
- [26. Conservation, termination, and correspondence](#26-conservation-termination-and-correspondence)
  - [26.1 Basic conservation invariants](#261-basic-conservation-invariants)
  - [26.2 Preservation of every candidate model](#262-preservation-of-every-candidate-model)
  - [26.3 Successful execution gives the unique model](#263-successful-execution-gives-the-unique-model)
  - [26.4 Finite execution and progress for ranked programs](#264-finite-execution-and-progress-for-ranked-programs)
- [27. Worked operational examples](#27-worked-operational-examples)
  - [27.1 An accumulator is not a readable intermediate](#271-an-accumulator-is-not-a-readable-intermediate)
  - [27.2 Boundary overlap and unwritten coordinates](#272-boundary-overlap-and-unwritten-coordinates)
  - [27.3 Guards, empty binders, and failure](#273-guards-empty-binders-and-failure)
  - [27.4 Bounded scans and complete logical slices](#274-bounded-scans-and-complete-logical-slices)
  - [27.5 A cycle can block with or without a model](#275-a-cycle-can-block-with-or-without-a-model)
- [28. Reference-machine boundaries and proof targets](#28-reference-machine-boundaries-and-proof-targets)

## Part IV: Operational semantics

The reference machine evaluates and collects individual contribution
occurrences. It permits arbitrary interleaving where dependencies allow,
but publishes a defined coordinate only after all occurrences targeting it
have been consumed.

This is an abstract, exact-value machine using the primitive interpretations
fixed in [Section 13.2](tensor_logic_semantics_part_ii.md#132-value-types-and-primitive-signatures). Expression evaluation
is atomic at this level. Computable implementations of the primitives and
their domain tests are separate requirements, especially over exact reals.

## 23. Read footprints and executable dependencies

### 23.1 Address partitions

Fix a structurally well-formed core program $\textcolor{#9D75C4}{P}$. Its roles partition the
address set:

```math
\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{In}}}
=\{(T,p)\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\mid T\in\textcolor{#5688C7}{\mathrm{In}}\},
\qquad
\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}
=\{(T,p)\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\mid T\in\textcolor{#5688C7}{\mathrm{Def}}\}.
```

Recall the destination function from [Section 9.2](tensor_logic_semantics_part_i.md#92-tagged-contribution-occurrences): for
$\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\in\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}$,

```math
\textcolor{#9D75C4}{\mathop{\mathrm{dst}}\nolimits}(\textcolor{#9D75C4}{o})=(T_{\textcolor{#9D75C4}{s}},\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu})).
```

For $a=(T,p)\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}$, abbreviate
$\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)=\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T,p)$.
These are the existing tagged occurrences and fibers, not new contributions.

### 23.2 Read footprints of expressions

For a structurally valid expression at an admissible valuation $\textcolor{#5688C7}{\nu}$,
define its **read footprint**
$\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})\subseteq\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}$ recursively.
This set records which named coordinates must be available before the
expression is interpreted by the direct executor:

```math
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(c_K,\textcolor{#5688C7}{\nu})
=\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\mathbf{1}_{\textcolor{#9D75C4}{Q}},\textcolor{#5688C7}{\nu})=\varnothing,
```

```math
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(T[\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_k],\textcolor{#5688C7}{\nu})
=\{(T,(\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{e}_1\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#5688C7}{\nu}},\ldots,
        \textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{e}_k\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#5688C7}{\nu}}))\},
```

```math
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E}_1\star \textcolor{#9D75C4}{E}_2,\textcolor{#5688C7}{\nu})
=\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E}_1,\textcolor{#5688C7}{\nu})\cup\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E}_2,\textcolor{#5688C7}{\nu}),
\qquad\star\in\{\oplus,\otimes\},
```

```math
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}\left(\bigoplus_{j\in \textcolor{#5688C7}{I}_j}\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu}\right)
=\bigcup_{k\in \textcolor{#5688C7}{I}_j}\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu}[j\mapsto k]),
```

```math
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}\left(
 \textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j_1\in \textcolor{#5688C7}{I}_1,\ldots,j_m\in \textcolor{#5688C7}{I}_m}(\textcolor{#9D75C4}{E}),\textcolor{#5688C7}{\nu}
\right)
=\bigcup_{p\in \textcolor{#5688C7}{I}_1\times\cdots\times \textcolor{#5688C7}{I}_m}
  \textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu}_p),
```

```math
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}(\textcolor{#9D75C4}{E},(\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_m)),\textcolor{#5688C7}{\nu})
=\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu}),
```

```math
\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(f(\textcolor{#9D75C4}{E}_1,\ldots,\textcolor{#9D75C4}{E}_q),\textcolor{#5688C7}{\nu})
=\bigcup_{r=1}^{q}\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E}_r,\textcolor{#5688C7}{\nu}).
```

Here $\textcolor{#5688C7}{\nu}_p$ is the simultaneous valuation extension from [Section 18.3](tensor_logic_semantics_part_iii.md#183-reduction-and-tabulation).
An empty union is empty, including for empty reductions, empty tabulations,
and nullary primitives.

The footprint of `at` includes the whole array expression, not just the
selected entry. Both operands of a scalar operation remain in the footprint,
even for multiplication by zero. These choices implement [Part III](tensor_logic_semantics_part_iii.md#part-iii-denotational-semantics)'s strict
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

```math
\textcolor{#A87C28}{\sigma}(a)=\textcolor{#398B83}{\rho}(T)[p]
\quad\text{for every }a=(T,p)\in\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma}).
```

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

```math
\textcolor{#A87C28}{\mathop{\mathrm{Eval}}\nolimits}_{\textcolor{#A87C28}{\sigma}}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})
=\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
\quad\text{for any complete }\textcolor{#398B83}{\rho}\text{ with }\textcolor{#A87C28}{\sigma}\textcolor{#A87C28}{\sqsubseteq}\textcolor{#398B83}{\rho}.
```

Read stability makes the choice irrelevant. This result belongs to
$\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau})$ for an expression of type $\textcolor{#5688C7}{\tau}$.
Write $\textcolor{#A87C28}{\mathop{\mathrm{Eval}}\nolimits}_{\textcolor{#A87C28}{\sigma}}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})\downarrow v$ for a successful
result. If the footprint is not available, ready evaluation is not invoked:
the occurrence waits. Waiting is distinct from a ready result of $\textcolor{#398B83}{\bot}$.

### 23.4 Coordinate dependencies and the ranked fragment

For $\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$, abbreviate
$\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})=\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}},\textcolor{#5688C7}{\nu})$.
Define

```math
\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)
=\bigcup_{\textcolor{#9D75C4}{o}\in\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)}\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})
\quad(a\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}),
```

and set $\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)=\varnothing$ for input addresses.

The **coordinate-ranked fragment** consists of programs with a certificate
$r:\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\to\mathbb{N}$ satisfying

```math
b\in\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)\Longrightarrow r(b)<r(a).
```

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

**Remark (production readiness).** The production profile orders whole
tensors: a tensor is ready only when every statement that defines it has run,
and a program whose tensor-level dependency graph has a cycle, apart from a scan
node's reads of its own state, is rejected. (A reader of a tensor with several
writers waits for every writer: all-writers readiness, recorded in the
[decision note](additive_production_decision_note.md).) The programs accepted
under this rule have a coordinate-rank certificate, but the converse fails. This is a strict subset of the coordinate-ranked fragment, and
a self-dependent history is expressed there only through the scan construct.


## 24. Machine configurations and initialization

### 24.1 Published values, accumulators, and pending occurrences

A running configuration is a triple

```math
\textcolor{#A87C28}{\mathsf{Conf}}=(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U}),
```

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
as introduced in [Section 5.3](tensor_logic_semantics_part_i.md#53-logical-addresses-physical-slots-and-proof-only-history). This does not relax logical readiness.

It also has terminal failed configurations
$\textcolor{#A87C28}{\mathsf{Failed}}(\textcolor{#9D75C4}{o},\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$, recording an occurrence whose ready
body was undefined and the machine state at failure.
This outcome is an explicit error, not a scalar result or an empty sum.
More detailed primitive-path diagnostics can refine this record without
changing the rules below.

### 24.2 Initial configuration

For $\textcolor{#398B83}{\eta}\in\textcolor{#398B83}{\mathop{\mathrm{Input}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}$, initialize

```math
\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})
=(\textcolor{#A87C28}{\sigma}_{\textcolor{#398B83}{\eta}},\textcolor{#A87C28}{\alpha}_0,\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}),
```

where

```math
\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma}_{\textcolor{#398B83}{\eta}})=\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{In}}},
\qquad
\textcolor{#A87C28}{\sigma}_{\textcolor{#398B83}{\eta}}(T,p)=\textcolor{#398B83}{\eta}(T)[p],
\qquad
\textcolor{#A87C28}{\alpha}_0(a)=0_K
\quad(a\in\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}).
```

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

```math
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
```

This rule removes exactly one tagged occurrence and combines its value
exactly once. The destination remains unpublished until the completion
rule applies. A successful zero-valued body still consumes its occurrence.

### 25.2 Publish a completed coordinate

```math
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
```

This is the **completion barrier**: no pending contribution to $a$ remains.
Publication may be delayed by scheduling but cannot occur early.

When $\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)=\varnothing$, publication is enabled immediately
and publishes $0_K$. An unwritten coordinate thus becomes an available
zero by an explicit completion step, not by treating absence as zero.
When a coordinate has contributions, even a currently zero accumulator
cannot be published until all those occurrences are consumed.

### 25.3 Surface undefined operations

For $\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$:

```math
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
```

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

```math
\textcolor{#A87C28}{U}=\varnothing,
\qquad
\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})=\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}.
```

It then determines a complete environment $\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}$ by
$\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}(T)[p]=\textcolor{#A87C28}{\sigma}(T,p)$.
Tensors with empty coordinate domains have their unique empty function
values in this environment.

Define successful execution by

```math
\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\Downarrow}\textcolor{#398B83}{\rho}
\quad\Longleftrightarrow\quad
\textcolor{#A87C28}{\mathsf{Conf}}\textcolor{#A87C28}{\longrightarrow}^{*}(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\varnothing)
\text{ with }\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})=\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}
\text{ and }\textcolor{#398B83}{\rho}=\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}.
```

All defined tensors must complete, including internal tensors not in
$\textcolor{#5688C7}{\mathrm{Out}}$. This matches the complete-model criterion in [Section 20.3](tensor_logic_semantics_part_iii.md#203-functional-admissibility).
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
[Proof status and numbered results](tensor_logic_semantics.md#proof-status-and-numbered-results).

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
   $\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}$
   is defined and equals $v_{\textcolor{#9D75C4}{o}}$. The footprint of $\textcolor{#9D75C4}{o}$ was
   published when it was consumed and published values only increase (item 3),
   so this is read stability (Lemma 23.1). It needs no model and no admissibility
   hypothesis on $\textcolor{#398B83}{\rho}$.

More explicitly, with the recorded values $v_{\textcolor{#9D75C4}{o}}$ of item 5,
at each running configuration

```math
\textcolor{#A87C28}{\alpha}(a)=
\bigoplus_{\textcolor{#9D75C4}{o}\in\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)\setminus \textcolor{#A87C28}{U}}v_{\textcolor{#9D75C4}{o}}.
```

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

```math
\textcolor{#A87C28}{\alpha}(a)=
\bigoplus_{(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\in\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(a)\setminus \textcolor{#A87C28}{U}}
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}},
```

with every term defined. If the fiber of $a$ has no pending occurrence and
$\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$, then
$\textcolor{#A87C28}{\alpha}(a)=\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[p]$.

(b) For every
$\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$,

```math
\textcolor{#A87C28}{\sigma}\textcolor{#A87C28}{\sqsubseteq}\textcolor{#398B83}{\rho}.
```

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

```math
\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}\in\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta}).
```

For any other model $\textcolor{#398B83}{\rho}$, Lemma 26.2(b) gives
$\textcolor{#A87C28}{\sigma}\textcolor{#A87C28}{\sqsubseteq}\textcolor{#398B83}{\rho}$ at the complete final store. Since the store has
every address, $\textcolor{#398B83}{\rho}=\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}$. Thus

```math
\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\{\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}\},
\qquad
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\mathclose{]\!]}}(\textcolor{#398B83}{\eta})=\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}|_{\textcolor{#5688C7}{\mathrm{Out}}}.
```

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

```math
\textcolor{#A87C28}{\mu}(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})
=|\textcolor{#A87C28}{U}|+
\left|\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}\setminus
             \mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})\right|.
```

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

```math
\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})\textcolor{#A87C28}{\Downarrow}\textcolor{#398B83}{\rho}
\quad\Longleftrightarrow\quad
\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\{\textcolor{#398B83}{\rho}\}.
```

In more detail, every maximal run either succeeds or explicitly fails.
If a model exists, model preservation excludes failure, so every maximal
run succeeds and returns that unique model. If no model exists,
successful completion is impossible, so every maximal run fails.

**Corollary 26.7 (ranked uniqueness).** A ranked program has at most one
model on any well-typed input: a model forces every maximal run to succeed,
and a successful run has a unique model by Theorem 26.3.

Therefore every maximal run of the reference machine, under any schedule,
realizes exactly the partial function of
[Section 20.3](tensor_logic_semantics_part_iii.md#203-functional-admissibility) for ranked programs. The machine is a transition relation;
choosing a schedule is a separate, computable artifact. The Lean executor is
one such artifact, for an exact-rational profile with a supplied schedule
(see [the Lean path document](lean_executable_semantics_path_part_4.md#46-the-computable-reference-executor)).
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
as in [Section 21.2](tensor_logic_semantics_part_iii.md#212-an-intermediate-fixes-the-activation-boundary); that is a different program.

### 27.2 Boundary overlap and unwritten coordinates

For [Section 11.1](tensor_logic_semantics_part_i.md#111-boundary-contributions), the corner's fiber contains both its row and column
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

For the guarded logarithm of [Section 21.3](tensor_logic_semantics_part_iii.md#213-a-guard-differs-from-a-zero-multiplier), only $i=0$ belongs to the
occurrence set. Its body is ready from the supplied $X$ and contributes
$\log(4)$; the empty fiber at $Y[1]$ publishes zero.

For the Iverson-multiplied version, both occurrences are present.
The body at $i=1$ is ready but undefined, so a maximal run reaches
$\textcolor{#A87C28}{\mathsf{Failed}}((\textcolor{#9D75C4}{s},i=1),\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$.
It cannot return the partially computed $Y$ as a successful output.

Empty binders also affect dependencies. The scalar statement

```math
T[]\textcolor{#9D75C4}{\mathrel{+}=}\bigoplus_{j\in[0]}T[]
```

has one contribution occurrence, but that body's read footprint is empty.
It contributes zero and $T$ then publishes zero.
The tensor name appears on both sides, yet there is no coordinate
dependency cycle: the bound body has no instances.

### 27.4 Bounded scans and complete logical slices

For [Section 11.4](tensor_logic_semantics_part_i.md#114-a-finite-history-with-persistent-input), the recurrence body at $(i,l)$ has the core form

```math
\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}\left(
F\left(\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{j\in[d]}(H[j,l])\right),(i)
\right).
```

Its footprint is $\{(H,(j,l))\mid j\in[d]\}$.
Thus every coordinate of $H_l$ must be published before this recurrence
contribution is ready. No update reads a partially accumulated slice.

A certificate is

```math
r(X,i)=r(Z,i)=0,
\qquad
r(H,(i,l))=l+1,
```

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
   (Proposition 19.2; the model and collection forms are proved in Lean for the
   bounded source fragment, as is whole-store agreement for two completed
   rational executions with equal inputs; completion and trace invariance
   are not claimed).
6. The transition invariants and model-preservation claims hold
   (Lemmas 26.1 and 26.2, Theorem 26.3).
7. The finite measure and rank certificate establish termination and
   progress; every maximal run of the reference machine computes exactly the
   unique model or explicitly fails on a ranked program
   (Lemma 26.4, Theorems 26.5 and 26.6, Corollary 26.7).

The arguments in [Part IV](#part-iv-operational-semantics) establish the reference-machine properties.
[Proof status and numbered results](tensor_logic_semantics.md#proof-status-and-numbered-results)
records which are also proved in Lean.
[Part V](tensor_logic_semantics_part_v.md#part-v-compilation-and-refinement) supplies the compilation/refinement layer: it defines plan contracts
and the relation between logical states and reusable storage.
General cyclic solvers remain a separately justified extension, not an
implicit fallback.

---

[Previous: Part III: Denotational semantics](tensor_logic_semantics_part_iii.md) | [Contents](README.md) | [Next: Part V: Compilation and refinement](tensor_logic_semantics_part_v.md)

# Tensor Logic semantics: worked examples

This is a companion to
[Tensor Logic: Operational and Denotational Semantics](tensor_logic_semantics.md).
It follows one multilayer perceptron from the surface DSL through core
elaboration to a complete reference-machine run, then develops three further
examples and a Lean-focused compilation walkthrough. Linked section numbers
refer to the specification; unlinked section
references refer to this companion. The notation is the same, without its
color annotations.

The architecture follows the
[deep-MLP DSL example](../../docs/dsl_examples.md#deep-mlp):
an input projection, a scan of hidden transformations, and a final projection
with softmax over ten classes. We count **L total learned layers**, so the scan
has **N = L - 2 recurrence steps**. The input projection and output projection
account for the other two layers. This is not an L-step recurrence followed
by an additional classifier.

Sections 9-11 demonstrate capabilities not exercised by that MLP: multiple
contributions to a preactivation, guarded partial operations and explicit
failure, and affine scatter with collisions and empty fibers. Each is a
separate program with its own signature and input environment, using the same
core language and reference-machine rules.
Section 12 follows the MLP into Part V, distinguishing the current Lean
source compiler from the verified semantic plan layer and an illustrative
two-buffer refinement.

## Contents

1. [The model and its domains](#1-the-model-and-its-domains)
2. [Start with the DSL](#2-start-with-the-dsl)
3. [Translate to the core language](#3-translate-to-the-core-language)
4. [Identify occurrences, destinations, and fibers](#4-identify-occurrences-destinations-and-fibers)
5. [Determine readiness and a coordinate rank](#5-determine-readiness-and-a-coordinate-rank)
6. [Execute the symbolic program](#6-execute-the-symbolic-program)
7. [A numerical instance, including all 32 transitions](#7-a-numerical-instance-including-all-32-transitions)
8. [What the example establishes](#8-what-the-example-establishes)
9. [Residual scan with collected preactivations](#9-residual-scan-with-collected-preactivations)
10. [Guarded logarithmic features and explicit failure](#10-guarded-logarithmic-features-and-explicit-failure)
11. [Affine scatter, collisions, and empty-fiber publication](#11-affine-scatter-collisions-and-empty-fiber-publication)
12. [Compilation and buffer refinement in Lean](#12-compilation-and-buffer-refinement-in-lean)

## 1. The model and its domains

Use the numerical scalar algebra

$$
K=\mathbb{R},\qquad \oplus=+,\qquad \otimes=\cdot,\qquad 0_K=0.
$$

These are exact mathematical reals, not floating-point execution semantics.
Let B be the batch size, D the input width, and M the uniform hidden width.
For the main example, assume B, D, M are positive and L is an integer with
L at least 2. Set N = L - 2. Recall that
$[n]=\{0,\ldots,n-1\}$, so N scan steps require N + 1 hidden-state slices.

| Index variable | Domain | Meaning |
| --- | --- | --- |
| q | $[B]$ | Batch member |
| d | $[D]$ | Input feature |
| i | $[M]$ | Output hidden coordinate |
| k | $[M]$ | Contracted input hidden coordinate |
| l | $[N]$ | Scan step |
| c | $[10]$ | Class label, from 0 through 9 |
| t | $[10]$ | Fresh tabulation variable used by softmax |

The variables i and k are distinct identities even though their domains have
the same size. They distinguish the input and output slots of a hidden weight
matrix. Tensor-slot names do not bind variables: reading `H[q,k,l]` uses k to
range over H's hidden slot, whereas writing `H[q,i,l+1]` uses i.

The tensor signature and roles are:

| Tensor | Coordinate domain | Role |
| --- | --- | --- |
| X | $[B]\times[D]$ | Input batch |
| $W_{\mathrm{in}}$ | $[M]\times[D]$ | Input-projection weights |
| W | $[N]\times[M]\times[M]$ | Independent weights at each scan step; slots are (step, input, output) |
| $W_{\mathrm{out}}$ | $[10]\times[M]$ | Classifier weights |
| H | $[B]\times[M]\times[N+1]$ | Defined hidden history |
| Y | $[B]\times[10]$ | Defined class probabilities |

Thus

$$
\mathrm{In}=\{X,W_{\mathrm{in}},W,W_{\mathrm{out}}\},\qquad
\mathrm{Def}=\{H,Y\},\qquad
\mathrm{Out}=\{Y\}.
$$

The input environment $\eta$ supplies both the observations and the fixed
trained weights. Treating weights as semantic inputs means their values are
given for this evaluation; it does not mean they are unlearned.
There are no biases in this example, matching the existing deep-MLP example.
Its base input projection has no activation; each scanned hidden
transformation has ReLU.

For one batch member, the intended forward computation is

$$
h_0[i]=\sum_{d\in[D]}W_{\mathrm{in}}[i,d]X[q,d],
$$

$$
h_{l+1}[i]=\operatorname{relu}
\left(\sum_{k\in[M]}W[l,k,i]h_l[k]\right)
\quad(l\in[N]),
$$

$$
z_q[c]=\sum_{k\in[M]}W_{\mathrm{out}}[c,k]h_N[k],
\qquad
Y[q,c]=\frac{\exp(z_q[c])}{\sum_{t\in[10]}\exp(z_q[t])}.
$$

Here $h_l[i]$ abbreviates H[q,i,l], and $z_q$ is an explanatory name for a
value, not a separately declared tensor.

**Probabilities versus a label.** Softmax returns ten probabilities; it does
not return an integer label. Outside this core program, the classifier decodes
them with

$$
\widehat c(q)=
\min\{c\in[10]\mid Y[q,c]=\max_{t\in[10]}Y[q,t]\}.
$$

The minimum specifies a deterministic tie policy. This argmax decoding is
post-processing, not an unstated core operator or reference-machine rule.

## 2. Start with the DSL

With the domains and roles above, write:

```text
H[q,i,0]   = W_in[i,d] X[q,d]                # base
H[q,i,l+1] = relu(W[l,k,i] H[q,k,l])          # step
Y[q,c.]    = softmax(W_out[c,k] H[q,k,N])     # out
```

The meaning of the implicit notation is:

- d is contracted in the base statement.
- k is contracted in the recurrence and classifier statements.
- l is retained as a contribution variable: it selects which layer is read
  and which next hidden-state slice is written. It is not summed out.
- The dot on c marks the complete ten-class softmax slice. It is not part of
  c's identity, and c is not a contracted index.
- The three surface assignments generate contributions. They are not
  imperative overwrites.

## 3. Translate to the core language

Apply the elaboration clauses in
[Sections 15.2-15.4](tensor_logic_semantics_part_ii.md#152-statement-variables-and-term-local-contraction).
Give the three statements distinct identifiers
$s_{\mathrm{base}},s_{\mathrm{step}},s_{\mathrm{out}}$.
Each omitted guard is true.

### 3.1 Base statement: make the contraction explicit

The output indices contain q and i, so

$$
\Gamma_{\mathrm{base}}=(q\in[B],i\in[M]).
$$

d occurs only on the right, so term-local contraction binds it in a reduction:

$$
s_{\mathrm{base}}:\quad
\text{for }q\in[B],i\in[M]:
\quad
H[q,i,0]\mathrel{+}=
\sum_{d\in[D]}W_{\mathrm{in}}[i,d]\cdot X[q,d].
$$

The scalar core body is
$E_{\mathrm{base}}=\sum_{d\in[D]}W_{\mathrm{in}}[i,d]\cdot X[q,d]$.
The sum is part of one occurrence's body, not D separate contributions to H.

### 3.2 Recurrence: contract first, then apply ReLU

The output indices contain q, i, and l, including l inside l + 1. Therefore

$$
\Gamma_{\mathrm{step}}=(q\in[B],i\in[M],l\in[N]).
$$

By term-local contraction and scalar operator placement:

$$
s_{\mathrm{step}}:\quad
\text{for }q\in[B],i\in[M],l\in[N]:
\quad
H[q,i,l+1]\mathrel{+}=
\operatorname{relu}
\left(\sum_{k\in[M]}W[l,k,i]\cdot H[q,k,l]\right).
$$

Call the scalar body $E_{\mathrm{step}}$.
ReLU is applied to the complete contraction. The body is not
$\sum_k\operatorname{relu}(W[l,k,i]\cdot H[q,k,l])$.

For every l in [N], both l and l + 1 are in [N + 1]; the weight read uses l
in [N]. The apparent self-reference to H is between distinct time coordinates.

### 3.3 Classifier: tabulate, apply softmax, then select

The contribution context is

$$
\Gamma_{\mathrm{out}}=(q\in[B],c\in[10]).
$$

First form the contracted scalar body
$B_{\mathrm{out}}=\sum_{k\in[M]}W_{\mathrm{out}}[c,k]\cdot H[q,k,N]$.
The marked-slice rule introduces the fresh variable t and substitutes t for
free occurrences of c inside that body:

$$
s_{\mathrm{out}}:\quad
\text{for }q\in[B],c\in[10]:
\quad
Y[q,c]\mathrel{+}=
\operatorname{at}\left(
\operatorname{softmax}\left(
\operatorname{tab}_{t\in[10]}
\left(\sum_{k\in[M]}W_{\mathrm{out}}[t,k]\cdot H[q,k,N]\right)
\right),(c)
\right).
$$

Call this scalar body $E_{\mathrm{out}}$. Its construction has three distinct
operations:

1. `tab` constructs the complete ten-entry logit vector.
2. `softmax` maps that vector to a complete probability vector.
3. `at(..., (c))` selects one scalar contribution to Y[q,c].

The singleton tuple (c) is a vector coordinate. Tabulation over t is not a
sum over classes. The sum over k is the hidden-feature contraction.
There is no named logit tensor in this core program and no additional
publication step for the explanatory value $z_q$.

## 4. Identify occurrences, destinations, and fibers

By
[Section 13.5](tensor_logic_semantics_part_ii.md#135-core-contribution-statements),
true guards give

$$
D_{\mathrm{base}}=[B]\times[M],\qquad
D_{\mathrm{step}}=[B]\times[M]\times[N],\qquad
D_{\mathrm{out}}=[B]\times[10].
$$

A tuple here specifies a valuation in the displayed binder order.
For example, (q,i,l) means
$\nu(q)=q,\nu(i)=i,\nu(l)=l$.
The write maps are

$$
\phi_{\mathrm{base}}(q,i)=(q,i,0),\qquad
\phi_{\mathrm{step}}(q,i,l)=(q,i,l+1),\qquad
\phi_{\mathrm{out}}(q,c)=(q,c).
$$

The tagged occurrence set is the disjoint union

$$
\mathcal O_P=
\{(s_{\mathrm{base}},(q,i))\mid q\in[B],i\in[M]\}
\sqcup
\{(s_{\mathrm{step}},(q,i,l))\mid q\in[B],i\in[M],l\in[N]\}
\sqcup
\{(s_{\mathrm{out}},(q,c))\mid q\in[B],c\in[10]\}.
$$

For an occurrence o = (s,$\nu$),
$\operatorname{dst}(o)=(T_s,\phi_s(\nu))$. In particular,

$$
\operatorname{dst}(s_{\mathrm{step}},(q,i,l))=(H,(q,i,l+1)).
$$

Every defined coordinate has exactly one occurrence in its fiber:

$$
\mathcal C_P(H,(q,i,0))=\{(s_{\mathrm{base}},(q,i))\},
$$

$$
\mathcal C_P(H,(q,i,u))=
\{(s_{\mathrm{step}},(q,i,u-1))\}
\quad(1\le u\le N),
$$

$$
\mathcal C_P(Y,(q,c))=\{(s_{\mathrm{out}},(q,c))\}.
$$

Consequently, there are

$$
|\mathcal O_P|=BM(N+1)+10B=BM(L-1)+10B
$$

occurrences and the same number of defined addresses. There are no colliding
writes or unwritten defined coordinates here. The additive semantics reduces
to the familiar forward equations because each fiber is a singleton, not
because `=` changed its meaning.

## 5. Determine readiness and a coordinate rank

### 5.1 Read footprints

Apply the recursive footprint clauses in
[Section 23.2](tensor_logic_semantics_part_iv.md#232-read-footprints-of-expressions).
Named reads give singleton address sets; multiplication takes unions;
reductions and tabulations take unions over their binders; primitive
application and array selection retain the operand's entire footprint.

For a base occurrence,

$$
\operatorname{Read}(s_{\mathrm{base}},(q,i))=
\{(W_{\mathrm{in}},(i,d))\mid d\in[D]\}
\cup
\{(X,(q,d))\mid d\in[D]\}.
$$

These are all input addresses, available at initialization.

For a recurrence occurrence,

$$
\operatorname{Read}(s_{\mathrm{step}},(q,i,l))=
\{(W,(l,k,i))\mid k\in[M]\}
\cup
\{(H,(q,k,l))\mid k\in[M]\}.
$$

Thus a next-slice contribution waits for **every hidden coordinate of the
previous slice for that batch member** to be published. It cannot read an
accumulator or an unpublished zero.

For an output occurrence,

$$
\operatorname{Read}(s_{\mathrm{out}},(q,c))=
\{(W_{\mathrm{out}},(t,k))\mid t\in[10],k\in[M]\}
\cup
\{(H,(q,k,N))\mid k\in[M]\}.
$$

This footprint is independent of c. Even the contribution to class 0
constructs the full softmax slice; it is not ready merely because the inputs
for logit 0 are available. Selecting c does not shrink the tabulation's
footprint. Zero-valued weights do not remove named reads either.

Different batch members have independent hidden dependencies. A schedule may
advance one batch member without waiting for all the others.

### 5.2 Coordinate rank certificate

Using
[Section 23.4](tensor_logic_semantics_part_iv.md#234-coordinate-dependencies-and-the-ranked-fragment),
assign

$$
r(a)=0\quad(a\in\operatorname{Addr}_{\mathrm{In}}),\qquad
r(H,(q,i,u))=u+1,\qquad
r(Y,(q,c))=N+2=L.
$$

Each base dependency has rank 0, below its destination rank 1.
Each recurrence reads H at rank l + 1 and writes H at rank l + 2.
Each classifier reads the final hidden slice at rank N + 1, below N + 2.
All weight reads have rank 0. Hence

$$
b\in\operatorname{Dep}(a)\Longrightarrow r(b)<r(a).
$$

The tensor-name graph would show H referring to H, but the coordinate graph
is acyclic. The rank certificate explains why this is an executable scan
rather than a blocked recursive equation system.

## 6. Execute the symbolic program

### 6.1 Initialize

By
[Section 24.2](tensor_logic_semantics_part_iv.md#242-initial-configuration),

$$
C_0=\operatorname{Init}(P,\eta)
=(\sigma_\eta,\alpha_0,\mathcal O_P).
$$

The published store contains exactly the supplied input coordinates:

$$
\operatorname{dom}(\sigma_\eta)=\operatorname{Addr}_{\mathrm{In}},\qquad
\sigma_\eta(T,p)=\eta(T)[p].
$$

For every defined address a, $\alpha_0(a)=0$.
Neither H nor Y has any published coordinates yet.
In particular, the all-zero initial accumulators are not a zero hidden history.

### 6.2 The two successful transition rules

The reference configuration is
$C=(\sigma,\alpha,U)$: published values, accumulators, and pending occurrences.
Specializing
[Section 25.1](tensor_logic_semantics_part_iv.md#251-consume-a-defined-contribution)
to real addition gives

$$
\frac{
o=(s,\nu)\in U
\qquad \operatorname{Read}(o)\subseteq\operatorname{dom}(\sigma)
\qquad \operatorname{Eval}_{\sigma}(E_s,\nu)\downarrow v
}{
(\sigma,\alpha,U)\longrightarrow
(\sigma,\alpha[a\mapsto\alpha(a)+v],U\setminus\{o\})
}
\quad\mathrm{CONTRIBUTE},
\qquad a=\operatorname{dst}(o).
$$

By
[Section 25.2](tensor_logic_semantics_part_iv.md#252-publish-a-completed-coordinate),

$$
\frac{
a\in\operatorname{Addr}_{\mathrm{Def}}\setminus\operatorname{dom}(\sigma)
\qquad U\cap\mathcal C_P(a)=\varnothing
}{
(\sigma,\alpha,U)\longrightarrow
(\sigma[a\mapsto\alpha(a)],\alpha,U)
}
\quad\mathrm{PUBLISH}.
$$

A `CONTRIBUTE` step changes the accumulator and U, not the published store.
A `PUBLISH` step changes the store, not the accumulator or U.
Because each fiber is a singleton here, consuming its occurrence enables
publication of that coordinate. These remain **two separate transitions**.

### 6.3 Evaluate and publish the base slice

For each q and i, let
$o=(s_{\mathrm{base}},(q,i))$ and $a=(H,(q,i,0))$.
Its footprint is available in $\sigma_\eta$. Evaluate the body by:

1. The named-read and multiplication clauses of
   [Section 18.2](tensor_logic_semantics_part_iii.md#182-scalar-constructors).
2. The reduction clause of
   [Section 18.3](tensor_logic_semantics_part_iii.md#183-reduction-and-tabulation).

These give

$$
\operatorname{Eval}_{\sigma}(E_{\mathrm{base}},(q,i))
\downarrow
v_{q,i,0}=
\sum_{d\in[D]}\eta(W_{\mathrm{in}})[i,d]\eta(X)[q,d].
$$

`CONTRIBUTE` sets $\alpha(a)=0+v_{q,i,0}$ and removes o from U.
`PUBLISH` then adds $\sigma(a)=v_{q,i,0}$.
After doing this for all q and i, the entire base slice is readable.

The individual products and reduction are expression-interpretation clauses,
not additional machine transitions. The machine consumes the whole scalar
body in one `CONTRIBUTE` step.

### 6.4 Evaluate and publish each scan slice

For l = 0 through N - 1, suppose the previous slice is published.
For each q and i, use $o=(s_{\mathrm{step}},(q,i,l))$ and
$a=(H,(q,i,l+1))$.

Named reads, multiplication, and reduction produce

$$
b_{q,i,l}=
\sum_{k\in[M]}\eta(W)[l,k,i]\sigma(H,(q,k,l)).
$$

The primitive-application clause of
[Section 18.4](tensor_logic_semantics_part_iii.md#184-array-selection-and-primitive-application)
then gives

$$
\operatorname{Eval}_{\sigma}(E_{\mathrm{step}},(q,i,l))
\downarrow v_{q,i,l+1}=\max(0,b_{q,i,l}).
$$

Real ReLU is defined on all real inputs. Apply `CONTRIBUTE` once for o,
then `PUBLISH` once for a. Only after the full previous slice is published
are next-layer contributions ready. A ReLU result of zero still requires
both transitions; the occurrence is not omitted.

### 6.5 Evaluate and publish the ten-class output

Once the final hidden slice for q is published, every output occurrence
$(s_{\mathrm{out}},(q,c))$ is ready.

For each such occurrence, the expression clauses give:

1. **Reads, multiplication, reduction:** for each t,
   $z_q[t]=\sum_k\eta(W_{\mathrm{out}})[t,k]\sigma(H,(q,k,N))$.
2. **Tabulation (Section 18.3):** construct the complete array
   $z_q:[10]\to\mathbb R$.
3. **Primitive application (Section 18.4):** obtain
   $p_q=\operatorname{softmax}(z_q)$.
4. **Array selection (Section 18.4):** return the scalar $p_q[c]$.

Softmax is defined because [10] is nonempty and
$\sum_t\exp(z_q[t])>0$.
`CONTRIBUTE` sets $\alpha(Y,(q,c))=p_q[c]$ and consumes that occurrence.
`PUBLISH` makes Y[q,c] readable.

There are ten scalar output occurrences per batch member, not one
vector-valued occurrence. The expression semantics supplies the same complete
probability vector for every c. Sharing that computation would be a compiled
optimization requiring its own correctness justification; it is not a new
reference rule.

### 6.6 Completion and the unused failure rule

After all contributions and publications,

$$
U=\varnothing,\qquad
\operatorname{dom}(\sigma)=\operatorname{Addr}_\Sigma.
$$

By
[Section 25.4](tensor_logic_semantics_part_iv.md#254-completion-and-dependency-blocking),
this is successful completion:

$$
\operatorname{Init}(P,\eta)\Downarrow\rho_\sigma,
\qquad
\rho_\sigma(T)[p]=\sigma(T,p).
$$

The returned result is $\rho_\sigma|_{\{Y\}}$.
H must also be complete, even though it is internal rather than an output.
There is no extra `SUCCESS` transition in the specified machine; completion
is a condition on the final running configuration.

The third rule,
[UNDEFINED (Section 25.3)](tensor_logic_semantics_part_iv.md#253-surface-undefined-operations),
would enter $\mathsf{Failed}(o,\sigma,\alpha,U)$ for a ready body whose evaluation
is $\bot$. It is never enabled here: structurally valid real arithmetic and
ReLU are total, and every demanded softmax slice has ten entries.
An unavailable hidden slice makes an occurrence wait; it is not an undefined
body or permission to substitute zero.

The layer-by-layer schedule just described uses
$2(BM(N+1)+10B)$ transitions. Other legal interleavings give the same result;
source-statement order is not an execution priority.

## 7. A numerical instance, including all 32 transitions

Take

$$
B=1,\quad D=M=2,\quad L=4,\quad N=2.
$$

There is one input projection, two independent hidden scan transformations,
and one output projection with softmax: four learned layers altogether.
Suppressing the sole batch index q = 0 when displaying vectors, supply

$$
X[0,:]=(1,-1),\qquad
W_{\mathrm{in}}=
\begin{pmatrix}
1&0\\
0&2
\end{pmatrix},
$$

$$
W[0,:,:]=
\begin{pmatrix}
2&1\\
-1&2
\end{pmatrix},
\qquad
W[1,:,:]=
\begin{pmatrix}
\tfrac12&\tfrac14\\
-1&2
\end{pmatrix}.
$$

Rows of each W slice are k (input hidden coordinates); columns are i
(output hidden coordinates). This orientation differs from the
output-by-input layout of $W_{\mathrm{in}}$ and $W_{\mathrm{out}}$.

The ten classifier rows are:

| c | $W_{\mathrm{out}}[c,0]$ | $W_{\mathrm{out}}[c,1]$ |
| --- | --- | --- |
| 0 | 0 | 0 |
| 1 | 0 | 1 |
| 2 | 1 | 0 |
| 3 | 0 | -1 |
| 4 | -1 | 0 |
| 5 | 1 | 1 |
| 6 | 2 | 0 |
| 7 | 2 | 1 |
| 8 | 3 | 0 |
| 9 | 3 | 1 |

### 7.1 Expand every hidden scalar body

Applying the expression clauses named in Section 6 gives:

| Destination | Core-body evaluation | Value |
| --- | --- | --- |
| H[0,0,0] | $1\cdot1+0\cdot(-1)$ | 1 |
| H[0,1,0] | $0\cdot1+2\cdot(-1)$ | -2 |
| H[0,0,1] | $\operatorname{relu}(2\cdot1+(-1)\cdot(-2))$ | 4 |
| H[0,1,1] | $\operatorname{relu}(1\cdot1+2\cdot(-2))$ | 0 |
| H[0,0,2] | $\operatorname{relu}(\tfrac12\cdot4+(-1)\cdot0)$ | 2 |
| H[0,1,2] | $\operatorname{relu}(\tfrac14\cdot4+2\cdot0)$ | 1 |

Hence the completed hidden slices are

$$
h_0=(1,-2),\qquad h_1=(4,0),\qquad h_2=(2,1).
$$

These are the values justified by the trace below, not values available
before their publication steps.

### 7.2 Expand the softmax body

Tabulating the classifier contraction over t gives:

| t | Logit contraction using $h_2=(2,1)$ | $z[t]$ |
| --- | --- | --- |
| 0 | $0\cdot2+0\cdot1$ | 0 |
| 1 | $0\cdot2+1\cdot1$ | 1 |
| 2 | $1\cdot2+0\cdot1$ | 2 |
| 3 | $0\cdot2+(-1)\cdot1$ | -1 |
| 4 | $(-1)\cdot2+0\cdot1$ | -2 |
| 5 | $1\cdot2+1\cdot1$ | 3 |
| 6 | $2\cdot2+0\cdot1$ | 4 |
| 7 | $2\cdot2+1\cdot1$ | 5 |
| 8 | $3\cdot2+0\cdot1$ | 6 |
| 9 | $3\cdot2+1\cdot1$ | 7 |

Write the positive normalizing value as

$$
S=1+e+e^2+e^{-1}+e^{-2}+e^3+e^4+e^5+e^6+e^7.
$$

Primitive application and selection yield

$$
p=\frac1S(1,e,e^2,e^{-1},e^{-2},e^3,e^4,e^5,e^6,e^7),
\qquad
\operatorname{Eval}_{\sigma}(E_{\mathrm{out}},(0,c))\downarrow p[c].
$$

The machine stores these exact expressions. Decimal values below are only
for readability.

### 7.3 Initialize the full configuration

Name the sixteen occurrences:

$$
b_i=(s_{\mathrm{base}},(0,i)),\qquad
r_{i,l}=(s_{\mathrm{step}},(0,i,l)),\qquad
y_c=(s_{\mathrm{out}},(0,c)).
$$

Also abbreviate logical addresses by

$$
a_{i,u}=(H,(0,i,u)),\qquad d_c=(Y,(0,c)).
$$

Initially,

$$
U_0=\{b_0,b_1,r_{0,0},r_{1,0},r_{0,1},r_{1,1},
       y_0,y_1,\ldots,y_9\}.
$$

The input store has 34 published addresses:
2 from X, 4 from $W_{\mathrm{in}}$, 8 from W, and 20 from
$W_{\mathrm{out}}$. All sixteen defined accumulators are zero.
No $a_{i,u}$ or $d_c$ is published.

Both base occurrences are ready. Every recurrence occurrence and every
output occurrence is waiting for hidden reads. No defined coordinate can
publish yet, since every fiber still contains its pending occurrence.

### 7.4 Every machine transition

Each row is **one** application of the named rule.
Unmentioned entries of $\sigma$ and $\alpha$ remain unchanged.
For `CONTRIBUTE`, remove the named occurrence from the preceding U.
For `PUBLISH`, U is unchanged. Accumulator entries remain present after
publication.

| Step | Rule | Selected occurrence or address | Accumulator change or new published value | Pending count after step |
| --- | --- | --- | --- | --- |
| 1 | CONTRIBUTE | $b_0$ | $\alpha(a_{0,0}):0\mapsto1$ | 15 |
| 2 | PUBLISH | $a_{0,0}$ | $\sigma(a_{0,0})=1$ | 15 |
| 3 | CONTRIBUTE | $b_1$ | $\alpha(a_{1,0}):0\mapsto-2$ | 14 |
| 4 | PUBLISH | $a_{1,0}$ | $\sigma(a_{1,0})=-2$ | 14 |
| 5 | CONTRIBUTE | $r_{0,0}$ | $\alpha(a_{0,1}):0\mapsto4$ | 13 |
| 6 | PUBLISH | $a_{0,1}$ | $\sigma(a_{0,1})=4$ | 13 |
| 7 | CONTRIBUTE | $r_{1,0}$ | $\alpha(a_{1,1}):0\mapsto0$ | 12 |
| 8 | PUBLISH | $a_{1,1}$ | $\sigma(a_{1,1})=0$ | 12 |
| 9 | CONTRIBUTE | $r_{0,1}$ | $\alpha(a_{0,2}):0\mapsto2$ | 11 |
| 10 | PUBLISH | $a_{0,2}$ | $\sigma(a_{0,2})=2$ | 11 |
| 11 | CONTRIBUTE | $r_{1,1}$ | $\alpha(a_{1,2}):0\mapsto1$ | 10 |
| 12 | PUBLISH | $a_{1,2}$ | $\sigma(a_{1,2})=1$ | 10 |
| 13 | CONTRIBUTE | $y_0$ | $\alpha(d_0):0\mapsto1/S$ | 9 |
| 14 | PUBLISH | $d_0$ | $\sigma(d_0)=1/S$ | 9 |
| 15 | CONTRIBUTE | $y_1$ | $\alpha(d_1):0\mapsto e/S$ | 8 |
| 16 | PUBLISH | $d_1$ | $\sigma(d_1)=e/S$ | 8 |
| 17 | CONTRIBUTE | $y_2$ | $\alpha(d_2):0\mapsto e^2/S$ | 7 |
| 18 | PUBLISH | $d_2$ | $\sigma(d_2)=e^2/S$ | 7 |
| 19 | CONTRIBUTE | $y_3$ | $\alpha(d_3):0\mapsto e^{-1}/S$ | 6 |
| 20 | PUBLISH | $d_3$ | $\sigma(d_3)=e^{-1}/S$ | 6 |
| 21 | CONTRIBUTE | $y_4$ | $\alpha(d_4):0\mapsto e^{-2}/S$ | 5 |
| 22 | PUBLISH | $d_4$ | $\sigma(d_4)=e^{-2}/S$ | 5 |
| 23 | CONTRIBUTE | $y_5$ | $\alpha(d_5):0\mapsto e^3/S$ | 4 |
| 24 | PUBLISH | $d_5$ | $\sigma(d_5)=e^3/S$ | 4 |
| 25 | CONTRIBUTE | $y_6$ | $\alpha(d_6):0\mapsto e^4/S$ | 3 |
| 26 | PUBLISH | $d_6$ | $\sigma(d_6)=e^4/S$ | 3 |
| 27 | CONTRIBUTE | $y_7$ | $\alpha(d_7):0\mapsto e^5/S$ | 2 |
| 28 | PUBLISH | $d_7$ | $\sigma(d_7)=e^5/S$ | 2 |
| 29 | CONTRIBUTE | $y_8$ | $\alpha(d_8):0\mapsto e^6/S$ | 1 |
| 30 | PUBLISH | $d_8$ | $\sigma(d_8)=e^6/S$ | 1 |
| 31 | CONTRIBUTE | $y_9$ | $\alpha(d_9):0\mapsto e^7/S$ | 0 |
| 32 | PUBLISH | $d_9$ | $\sigma(d_9)=e^7/S$ | 0 |

The table and unchanged-entry convention specify every intermediate
configuration $C_j=(\sigma_j,\alpha_j,U_j)$ starting from $C_0$.

### 7.5 Check the rule premises at the barriers

For every contribution row, its occurrence is still in U and its body's
defined value is listed in Sections 7.1-7.2.
The remaining readiness and publication premises can be checked explicitly:

- **Steps 1 and 3:** their footprints contain only the 34 initially
  published input addresses.
- **Step 2:** $\mathcal C_P(a_{0,0})=\{b_0\}$ and step 1 removed $b_0$.
  The address has never been published, so `PUBLISH` is enabled.
  However, $r_{0,0}$ and $r_{1,0}$ are still not ready: $a_{1,0}$ is missing.
- **Step 4:** consuming $b_1$ completed its singleton fiber. Both base
  coordinates are now published, making steps 5 and 7 ready.
- **Step 6:** publishing $a_{0,1}=4$ alone does not enable either next-layer
  occurrence. Both require $a_{1,1}$ too.
- **Steps 7 and 8:** a zero-valued body still consumes $r_{1,0}$ and
  requires explicit publication. Only after step 8 is the whole first
  scan slice readable, making steps 9 and 11 ready.
- **Step 10:** the final slice is incomplete. Every $y_c$ still waits for
  $a_{1,2}$, even though some classifier weights on that coordinate are zero.
- **Step 12:** the whole final hidden slice is published. Together with the
  supplied classifier weights, this makes all ten output occurrences ready.
- **Steps 13-32:** each contribution evaluates the same complete logit
  vector and selects its own c. Each following publication has an empty
  pending intersection with its singleton fiber.
- **Step 31:** U is empty, but $d_9$ is not yet published. The machine is
  **not** complete until step 32.

No publication row changes U, and no contribution row publishes a value.
In particular, step 7 is necessary despite leaving its accumulator
numerically unchanged.

### 7.6 Final output and predicted class

After step 32, $\operatorname{dom}(\sigma)$ has all 50 addresses:
34 input addresses and 16 defined addresses. U is empty, so

$$
C_0\longrightarrow^{32}C_{32},
\qquad C_0\Downarrow\rho_\sigma.
$$

The output is the one-row tensor

$$
\rho_\sigma(Y)[0,:]=p.
$$

For readability, its approximate values are:

| Class | Probability |
| --- | --- |
| 0 | 0.0005764455 |
| 1 | 0.0015669414 |
| 2 | 0.0042593882 |
| 3 | 0.0002120625 |
| 4 | 0.0000780134 |
| 5 | 0.0115782175 |
| 6 | 0.0314728583 |
| 7 | 0.0855520989 |
| 8 | 0.2325547159 |
| 9 | 0.6321492584 |

Exactly, all entries are positive and $\sum_{c\in[10]}p[c]=S/S=1$.
The largest logit is z[9] = 7, so the largest probability is p[9].
The decoded class is therefore $\widehat c(0)=9$, one of the ten labels.

## 8. What the example establishes

### 8.1 Correspondence with the equations

At every defined address a, the final accumulator equals its one consumed
body value and the published store equals that accumulator. Therefore

$$
\rho_\sigma(T)[p]=
\operatorname{Collect}_P(\rho_\sigma)(T)[p]
\quad(T\in\{H,Y\}).
$$

The environment extends $\eta$, every actual body is defined, and the
coordinate rank determines the values successively from base slice through
classifier. Thus it is the unique model, and

$$
\llbracket P\rrbracket(\eta)=\rho_\sigma|_{\{Y\}}.
$$

This is the concrete instance of the conservation and correspondence results
in
[Section 26](tensor_logic_semantics_part_iv.md#26-conservation-termination-and-correspondence).
It is a worked mathematical derivation, not a new kernel-checked Lean theorem.

### 8.2 The zero-step boundary

When L = 2, N = 0. The recurrence domain is empty and generates no
occurrences. H has only its base slice, and the output reads that slice.
There are BM + 10B contributions and the same number of publications.
The zero-extent input tensor W must still be supplied as a value of its
declared shape; an empty input is not an omitted input.

### 8.3 Notation lessons

| Notation | Its concrete role in this MLP |
| --- | --- |
| $\eta$ | Supplied batch and fixed weights |
| $\Gamma_s$ | Variables generating one statement's occurrences |
| $D_s$ | Finite admissible valuations of those variables |
| $\phi_s$ | Map from a valuation to the destination coordinate |
| $(s,\nu)$ | One tagged scalar contribution, not a product term |
| $\mathcal C_P(a)$ | All occurrences targeting a coordinate; singleton here |
| $\sum$ / $\bigoplus$ | Contraction inside one scalar body |
| `tab` | Construct every class logit for softmax |
| `at` | Select one scalar probability from the complete softmax result |
| $\operatorname{Read}(o)$ | Published coordinates required before consuming o |
| $\operatorname{Eval}_\sigma$ | Ready expression evaluation using only published reads |
| $\alpha$ | Accumulated contributions, never a readable hidden state |
| $\sigma$ | Immutable published coordinate values |
| U | Contributions still awaiting successful consumption |
| $\longrightarrow$ | One machine transition |
| $\Downarrow$ | Successful execution to a complete environment |
| $\llbracket P\rrbracket(\eta)$ | Output restriction of the unique model |

The reference machine keeps the complete logical H history. Nothing in this
trace overwrites an earlier slice with a later one. A compiler might use
rolling buffers, batch contributions, or share the softmax calculation, but
those are refinement questions addressed separately in
[Part V](tensor_logic_semantics_part_v.md#part-v-compilation-and-refinement) and
worked through in Section 12 below.

## 9. Residual scan with collected preactivations

**Additional capability:** several independently scheduled statements
contribute to each preactivation, and a nonlinear consumer waits for their
completed total. Unlike the MLP, these contribution fibers are not singletons.

### 9.1 Surface program and explicit core

Use two hidden coordinates and two scan steps. Inputs are X with domain [2],
W with domain $[2]\times[2]\times[2]$, and B with domain
$[2]\times[2]$. W's slots here are (step, output, input).
Defined tensors are H with domain $[2]\times[3]$ and Pre with domain
$[2]\times[2]$; choose $\mathrm{Out}=\{H\}$ to return the complete history.
The contribution variables i, k, and l range over [2].

```text
H[i,0]     = X[i]                     # base
Pre[i,l]   = W[l,i,k] H[k,l]          # matrix contribution
Pre[i,l]   = H[i,l]                   # residual contribution
Pre[i,l]   = B[l,i]                   # bias contribution
H[i,l+1]   = relu(Pre[i,l])           # activation after collection
```

Give these statements distinct identifiers
$s_b,s_m,s_r,s_\beta,s_a$. Applying term-local contraction and scalar
operator placement gives the core program:

$$
\begin{aligned}
s_b:\ &\text{for }i\in[2]:
&&H[i,0]\mathrel{+}=X[i],\\
s_m:\ &\text{for }i,l\in[2]:
&&\operatorname{Pre}[i,l]\mathrel{+}=
  \sum_{k\in[2]}W[l,i,k]H[k,l],\\
s_r:\ &\text{for }i,l\in[2]:
&&\operatorname{Pre}[i,l]\mathrel{+}=H[i,l],\\
s_\beta:\ &\text{for }i,l\in[2]:
&&\operatorname{Pre}[i,l]\mathrel{+}=B[l,i],\\
s_a:\ &\text{for }i,l\in[2]:
&&H[i,l+1]\mathrel{+}=\operatorname{relu}(\operatorname{Pre}[i,l]).
\end{aligned}
$$

All guards are true. The statement domain for $s_b$ is [2], with write
map i to (i,0). Each other domain is $[2]\times[2]$ in binder order (i,l).
For $s_m,s_r,s_\beta$, the write map is (i,l) to (i,l); for $s_a$, it is
(i,l) to (i,l+1).
In particular,

$$
\mathcal C_P(\operatorname{Pre},(i,l))
=\{(s_m,(i,l)),(s_r,(i,l)),(s_\beta,(i,l))\}.
$$

This is three contributions, not three alternative definitions or overwrites.
H's base and later coordinates each have a singleton fiber.

### 9.2 Dependencies and the collection barrier

The read footprints are:

| Occurrence | Read footprint |
| --- | --- |
| $(s_b,i)$ | $\{(X,(i))\}$ |
| $(s_m,(i,l))$ | $\{(W,(l,i,k)),(H,(k,l))\mid k\in[2]\}$ |
| $(s_r,(i,l))$ | $\{(H,(i,l))\}$ |
| $(s_\beta,(i,l))$ | $\{(B,(l,i))\}$ |
| $(s_a,(i,l))$ | $\{(\operatorname{Pre},(i,l))\}$ |

Bias contributions can be consumed even for a future layer whose H slice
does not yet exist in the published store. They cannot by themselves enable
publication of Pre: its two other occurrences remain pending.
The activation reads only its own completed preactivation, whereas a matrix
contribution needs the complete previous H slice.

A coordinate rank is

$$
r(\text{input address})=0,\qquad
r(H,(i,u))=2u+1,\qquad
r(\operatorname{Pre},(i,l))=2l+2.
$$

All reads have lower rank than their destination.
The collected equations are therefore the residual recurrence

$$
h_0=X,\qquad
h_{l+1}[i]=\operatorname{relu}
\left(\sum_k W[l,i,k]h_l[k]+h_l[i]+B[l,i]\right).
$$

### 9.3 Numerical execution with an early future-layer contribution

Supply

$$
X=(2,-1),\qquad
W[0,:,:]=\begin{pmatrix}-1&2\\1&1\end{pmatrix},\qquad
W[1,:,:]=\begin{pmatrix}2&-1\\1&1\end{pmatrix},
$$

$$
B[0,:]=(1,1),\qquad B[1,:]=(2,-3).
$$

Reading rows as output coordinates, the expression evaluations give:

| Layer l | Matrix contribution $W_lh_l$ | Residual $h_l$ | Bias $B_l$ | Collected Pre | Activated $h_{l+1}$ |
| --- | --- | --- | --- | --- | --- |
| 0 | $(-4,1)$ | $(2,-1)$ | $(1,1)$ | $(-1,1)$ | $(0,1)$ |
| 1 | $(-1,1)$ | $(0,1)$ | $(2,-3)$ | $(1,-1)$ | $(1,0)$ |

Initialize all ten defined accumulators to zero and publish only the
fourteen input addresses. U has eighteen occurrences: two base, twelve
preactivation, and four activation occurrences.

The following is a complete 28-transition run. **Each row contains two
separate transitions**, selecting i = 0 and then i = 1. Vectors describe the
two accumulator entries or published entries after the row. A contribution
removes only its selected occurrence; a publication leaves U unchanged.

| Steps | Rule | Selected statement or addresses | Result after both transitions | Pending count |
| --- | --- | --- | --- | --- |
| 1-2 | CONTRIBUTE | $s_b$ at i = 0,1 | $\alpha(H_0)=(2,-1)$ | 16 |
| 3-4 | PUBLISH | H[i,0] | $\sigma(H_0)=(2,-1)$ | 16 |
| 5-6 | CONTRIBUTE | $s_\beta$ at (i,1) | $\alpha(\operatorname{Pre}_1)=(2,-3)$ | 14 |
| 7-8 | CONTRIBUTE | $s_r$ at (i,0) | $\alpha(\operatorname{Pre}_0)=(2,-1)$ | 12 |
| 9-10 | CONTRIBUTE | $s_\beta$ at (i,0) | $\alpha(\operatorname{Pre}_0)=(3,0)$ | 10 |
| 11-12 | CONTRIBUTE | $s_m$ at (i,0) | $\alpha(\operatorname{Pre}_0)=(-1,1)$ | 8 |
| 13-14 | PUBLISH | Pre[i,0] | $\sigma(\operatorname{Pre}_0)=(-1,1)$ | 8 |
| 15-16 | CONTRIBUTE | $s_a$ at (i,0) | $\alpha(H_1)=(0,1)$ | 6 |
| 17-18 | PUBLISH | H[i,1] | $\sigma(H_1)=(0,1)$ | 6 |
| 19-20 | CONTRIBUTE | $s_r$ at (i,1) | $\alpha(\operatorname{Pre}_1)=(2,-2)$ | 4 |
| 21-22 | CONTRIBUTE | $s_m$ at (i,1) | $\alpha(\operatorname{Pre}_1)=(1,-1)$ | 2 |
| 23-24 | PUBLISH | Pre[i,1] | $\sigma(\operatorname{Pre}_1)=(1,-1)$ | 2 |
| 25-26 | CONTRIBUTE | $s_a$ at (i,1) | $\alpha(H_2)=(1,0)$ | 0 |
| 27-28 | PUBLISH | H[i,2] | $\sigma(H_2)=(1,0)$ | 0 |

H_u abbreviates the vector of logical addresses (H,(i,u)); Pre_l
abbreviates the corresponding two preactivation addresses.
No physical vector-valued transition is being introduced.

At step 9, $\alpha(\operatorname{Pre},(0,0))=3$. Applying ReLU to that
accumulator would produce 3, but the true completed value is
$\operatorname{relu}(-1)=0$. `PUBLISH` is forbidden at that point because
the matrix occurrence is still pending, and `CONTRIBUTE` for the activation
is forbidden because its named read is unpublished.
Nor may the bias pre-accumulated at steps 5-6 be discarded or added again
when layer 1 is reached.

At the end, all 24 addresses are published and U is empty. The unique model
returns the history

$$
H[:,0]=(2,-1),\qquad H[:,1]=(0,1),\qquad H[:,2]=(1,0).
$$

## 10. Guarded logarithmic features and explicit failure

**Additional capability:** a guard removes padded feature occurrences before
a partial primitive is evaluated. A subsequent array operation uses the
completed feature tensor. Replacing the guard by a zero multiplier produces
an explicit failed run rather than the same output.

### 10.1 Surface program, domains, and core translation

Inputs consist of X with domain $[2]\times[3]$: two observations, each with
two valid features and one padding slot.
F and Y are defined tensors with the same domain, and $\mathrm{Out}=\{Y\}$.
Use q in [2] and j, c in [3]. The validity condition is an **index-based
prefix declaration**, not a test of tensor values.

```text
F[q,j]  = log(X[q,j]) where j < 2    # valid feature positions only
Y[q,c.] = softmax(F[q,c])            # normalize the completed feature row
```

Register real log with domain $(0,\infty)$ and softmax on
$\mathbb R^{[3]}$. With distinct identifiers $s_f,s_y$, the core is:

$$
s_f:\quad
\text{for }q\in[2],j\in[3]\text{ where }j<2:
\quad F[q,j]\mathrel{+}=\log(X[q,j]),
$$

$$
s_y:\quad
\text{for }q\in[2],c\in[3]:
\quad Y[q,c]\mathrel{+}=
\operatorname{at}\left(
\operatorname{softmax}
\left(\operatorname{tab}_{t\in[3]}(F[q,t])\right),(c)
\right).
$$

Thus $D_f=[2]\times[2]$, a guarded subset of
$\operatorname{Val}(\Gamma_f)=[2]\times[3]$; $D_y=[2]\times[3]$.
Both write maps are the identity on their respective admissible domains.
There are four feature occurrences and six output occurrences.
The two F coordinates with j = 2 have empty fibers.

The footprints are

$$
\operatorname{Read}(s_f,(q,j))=\{(X,(q,j))\}
\quad(j<2),
$$

$$
\operatorname{Read}(s_y,(q,c))=\{(F,(q,t))\mid t\in[3]\}.
$$

There is no feature occurrence or feature footprint at j = 2.
However, each softmax occurrence reads its entire completed F row, including
the zero supplied by empty-fiber publication.
A certificate assigns input rank 0, F rank 1, and Y rank 2.

### 10.2 Successful execution

Supply

$$
X=
\begin{pmatrix}
1&e&-7\\
e^2&1&0
\end{pmatrix}.
$$

The four actual log applications are defined and evaluate to 0, 1, 2, 0.
The invalid padding values -7 and 0 are never passed to log.
The complete feature and probability tensors are

$$
F=\begin{pmatrix}0&1&0\\2&0&0\end{pmatrix},\qquad
Y[0,:]=\frac{(1,e,1)}{2+e},\qquad
Y[1,:]=\frac{(e^2,1,1)}{e^2+2}.
$$

Initialize the six input addresses as published, all twelve defined
accumulators as zero, and U with the ten actual occurrences.
One complete schedule is:

| Steps | Rule | Selected occurrences or addresses | Effect | Pending count after group |
| --- | --- | --- | --- | --- |
| 1-2 | PUBLISH | F[0,2], then F[1,2] | Publish both empty fibers as zero | 10 |
| 3-6 | CONTRIBUTE | $s_f$ at (0,0), (0,1), (1,0), (1,1) | Accumulate log values 0, 1, 2, 0 | 6 |
| 7-10 | PUBLISH | The same four F coordinates in the same order | Complete both feature rows | 6 |
| 11-16 | CONTRIBUTE | $s_y$ at (0,0), (0,1), (0,2), (1,0), (1,1), (1,2) | Tabulate, softmax, select; accumulate the six probabilities | 0 |
| 17-22 | PUBLISH | The same six Y coordinates in the same order | Publish the complete output | 0 |

Each selected item is one transition. All unmentioned state entries are
unchanged. Each publication either has an empty fiber from the start or
follows consumption of its singleton occurrence.
The first row alone enables no softmax contribution: the other F coordinates
are still unpublished. All softmax occurrences are ready after step 10.
After step 22, all eighteen addresses are published and U is empty.

**Guarding is not masked softmax.** The guard removes contributions to F's
padding coordinates; it does not remove those coordinates from Y's slice.
They receive F = 0, hence a softmax numerator of $\exp(0)=1$, not zero.
If padding classes should have zero probability, a separately specified
masked normalization is required. This example deliberately normalizes all
three completed feature coordinates.

### 10.3 The zero-multiplier variant fails

Replace only the guarded feature statement by:

```text
F[q,j] = 1_{j < 2} log(X[q,j])       # multiply; do not exclude occurrences
```

Its core statement is now

$$
s_f':\quad
\text{for }q\in[2],j\in[3]:
\quad F[q,j]\mathrel{+}=\mathbf 1_{j<2}\cdot\log(X[q,j]).
$$

The feature statement domain is the full $[2]\times[3]$, so both padding
coordinates now have pending singleton fibers. U initially has twelve
occurrences, and no F coordinate can publish immediately.
The rank certificate still applies: being ranked does not make partial
primitives total.

Consider this nine-transition run from the new initialization:

| Steps | Rule | Selection | Effect | Pending count |
| --- | --- | --- | --- | --- |
| 1-4 | CONTRIBUTE | $s_f'$ at (0,0), (0,1), (1,0), (1,1) | Accumulate the four valid log features | 8 |
| 5-8 | PUBLISH | Those four F coordinates in the same order | Publish their completed values | 8 |
| 9 | UNDEFINED | $o=(s_f',(0,2))$ | Enter $\mathsf{Failed}(o,\sigma_8,\alpha_8,U_8)$ | 8 |

For the last step, o is pending and its footprint
$\{(X,(0,2))\}$ is already published. But the strict clauses give

$$
\operatorname{Eval}_{\sigma_8}
(\mathbf 1_{j<2}\cdot\log(X[q,j]),(0,2))
=0\cdot\bot=\bot,
$$

where the displayed multiplication denotes the strict lifting, not real
arithmetic on $\bot$. The primitive log(-7) is undefined; multiplying by
zero does not suppress its evaluation.
Consequently,
[UNDEFINED](tensor_logic_semantics_part_iv.md#253-surface-undefined-operations)
preserves the failing occurrence and records an explicit terminal error.

At failure, U still contains both padding-feature occurrences and all six
softmax occurrences. Neither feature row is completely published, so no
Y contribution has been ready. No partially computed feature tensor is
returned as a successful program output. The other padding value would also
fail, since log(0) is undefined.

## 11. Affine scatter, collisions, and empty-fiber publication

**Additional capability:** distinct source valuations scatter products into
the same destination coordinate, while holes in the declared output become
readable zeros only by publication. A downstream nonlinear window operation
uses both populated and empty-fiber coordinates.

### 11.1 Surface program and core translation

Use input vectors X with domain [3] and K with domain [2].
Declare S with domain [8] and Z with domain [4] as defined tensors, with
$\mathrm{Out}=\{Z\}$. Let i range over [3], j over [2], and r over [4].

```text
S[2i+2j] = X[i] K[j]                # dilated scatter-add
Z[r]     = relu(S[2r] + S[2r+1])    # combine a two-coordinate window
```

The affine output index retains **both i and j as contribution variables**.
Neither is contracted away. Each valuation contributes one product, and
collection sums products with the same destination.
With statement identifiers $s_s,s_z$, elaboration gives:

$$
s_s:\quad
\text{for }i\in[3],j\in[2]:
\quad S[2i+2j]\mathrel{+}=X[i]\cdot K[j],
$$

$$
s_z:\quad
\text{for }r\in[4]:
\quad Z[r]\mathrel{+}=
\operatorname{relu}(S[2r]+S[2r+1]).
$$

All guards are true. The scatter domain is $D_s=[3]\times[2]$ and its write
map is $\phi_s(i,j)=(2i+2j)$. Its maximum output index is 6, within [8].
The window reads have maximum indices 6 and 7, also within [8].
$D_z=[4]$ and $\phi_z(r)=(r)$.

The footprints are

$$
\operatorname{Read}(s_s,(i,j))=\{(X,(i)),(K,(j))\},
\qquad
\operatorname{Read}(s_z,r)=\{(S,(2r)),(S,(2r+1))\}.
$$

Input rank 0, S rank 1, and Z rank 2 give a certificate.
Every Z occurrence waits for both members of its window, even when one will
be an empty-fiber zero.

### 11.2 Fibers and numerical contributions

Supply $X=(1,2,-1)$ and $K=(3,-2)$.
The six scatter occurrences have these destinations and scalar body values:

| Valuation (i,j) | Destination | Body $X[i]K[j]$ |
| --- | --- | --- |
| (0,0) | S[0] | 3 |
| (0,1) | S[2] | -2 |
| (1,0) | S[2] | 6 |
| (1,1) | S[4] | -4 |
| (2,0) | S[4] | -3 |
| (2,1) | S[6] | 2 |

For example,

$$
\mathcal C_P(S,(2))=\{(s_s,(0,1)),(s_s,(1,0))\},
\qquad
\mathcal C_P(S,(4))=\{(s_s,(1,1)),(s_s,(2,0))\}.
$$

The singleton fibers are at 0 and 6. The four odd coordinates
1, 3, 5, 7 have empty fibers. These are coordinates of the declared tensor,
not missing coordinates to be omitted from the result.
Collecting all six occurrences gives

$$
S=(3,0,4,0,-7,0,2,0),\qquad Z=(3,4,0,2).
$$

This is a dilated convolution-shaped scatter: S[2u] contains the sum of
products with i + j = u. Its zeros come from the declared geometry, not
implicit padding of out-of-bounds reads.

### 11.3 A complete interleaved run

Initially, only the five input addresses are published. All twelve defined
accumulators are zero. U contains six scatter and four window occurrences.
Name the latter $z_r=(s_z,r)$.

Each row below is one transition, except the first row, which explicitly
lists four publications in ascending coordinate order.

| Steps | Rule | Selection | Accumulator change or new published value | Pending count |
| --- | --- | --- | --- | --- |
| 1-4 | PUBLISH | S[1], S[3], S[5], S[7] | Publish each empty-fiber coordinate as 0 | 10 |
| 5 | CONTRIBUTE | $(s_s,(0,0))$ | $\alpha(S,(0)):0\mapsto3$ | 9 |
| 6 | PUBLISH | S[0] | $\sigma(S,(0))=3$ | 9 |
| 7 | CONTRIBUTE | $z_0$ | $\alpha(Z,(0)):0\mapsto3$ | 8 |
| 8 | PUBLISH | Z[0] | $\sigma(Z,(0))=3$ | 8 |
| 9 | CONTRIBUTE | $(s_s,(0,1))$ | $\alpha(S,(2)):0\mapsto-2$ | 7 |
| 10 | CONTRIBUTE | $(s_s,(1,0))$ | $\alpha(S,(2)):-2\mapsto4$ | 6 |
| 11 | PUBLISH | S[2] | $\sigma(S,(2))=4$ | 6 |
| 12 | CONTRIBUTE | $z_1$ | $\alpha(Z,(1)):0\mapsto4$ | 5 |
| 13 | PUBLISH | Z[1] | $\sigma(Z,(1))=4$ | 5 |
| 14 | CONTRIBUTE | $(s_s,(1,1))$ | $\alpha(S,(4)):0\mapsto-4$ | 4 |
| 15 | CONTRIBUTE | $(s_s,(2,0))$ | $\alpha(S,(4)):-4\mapsto-7$ | 3 |
| 16 | PUBLISH | S[4] | $\sigma(S,(4))=-7$ | 3 |
| 17 | CONTRIBUTE | $z_2$ | $\alpha(Z,(2)):0\mapsto0$ | 2 |
| 18 | PUBLISH | Z[2] | $\sigma(Z,(2))=0$ | 2 |
| 19 | CONTRIBUTE | $(s_s,(2,1))$ | $\alpha(S,(6)):0\mapsto2$ | 1 |
| 20 | PUBLISH | S[6] | $\sigma(S,(6))=2$ | 1 |
| 21 | CONTRIBUTE | $z_3$ | $\alpha(Z,(3)):0\mapsto2$ | 0 |
| 22 | PUBLISH | Z[3] | $\sigma(Z,(3))=2$ | 0 |

All scatter bodies are ready from initialization, so the interleaving is
legal. Each window body is interpreted only after both named reads have been
published. Unmentioned state entries remain unchanged, and the rules update
U exactly as in the MLP trace.

At step 9, S[2]'s accumulator is -2, but the occurrence (1,0) is still
pending. `PUBLISH` cannot expose -2, and $z_1$ cannot apply ReLU to it.
After step 10 the fiber is complete, step 11 publishes 4, and step 12
contributes $\operatorname{relu}(4+0)=4$.

Likewise, before step 1, the accumulator for S[1] is zero but S[1] is not
readable. Its empty fiber enables `PUBLISH`, not a default-zero named read.
The window at r = 0 still waits for S[0] after S[1] is published.
The zero contributed at step 17 remains an actual occurrence and must be
consumed before Z[2] can publish.

After step 22, all seventeen addresses are published and U is empty:
ten contributions and twelve publications have produced the unique model.
The returned tensor is Z = (3,4,0,2); the complete internal S is part of the
model even though it is not a designated output.

## 12. Compilation and buffer refinement in Lean

This section revisits the four-layer MLP of Section 7:
$h_0=(1,-2)$, $h_1=(4,0)$, $h_2=(2,1)$, and output p.
It illustrates
[Part V](tensor_logic_semantics_part_v.md#part-v-compilation-and-refinement):
choosing commands and storage that implement the reference computation,
rather than changing its equations.

### 12.1 Two Lean layers, with different guarantees

There are two relevant developments in the repository:

| Lean layer | What it provides | Status of this MLP |
| --- | --- | --- |
| [Checked source compiler](../../leanncd/LeanNCD/Eval/Plan/Compile.lean), namespace `LeanNCD.Eval.Plan` | `prepareEvalPlan` specializes a scheduled source program into positional operations and checks the resulting graph; dense workers execute checked evidence using binary32 or binary64 values | Scan and nonlinear lowering are implemented; the current scan retains complete history |
| [Semantic plans](../../leanncd/LeanNCD/Semantics/Plan/), namespace `LeanNCD.Semantics.Program.Plan` | A plan language with accumulation, publication, initialization and retirement, with generic simulation and correctness theorems | The exact-real MLP and its scan allocation below are mathematical instances, not newly constructed Lean terms or kernel-checked fixtures |

**There is no proved connection between those two layers yet.** In
particular, accepting a `CheckedEvalPlan` is not a proof of refinement to the
Part IV reference machine. Conversely, the semantic-plan correctness theorems
do not establish that `prepareEvalPlan` emits such plans.
See the
[Lean correspondence guide](lean_executable_semantics_path_part_4.md#49-part-v-slice-1-the-singleton-command-plan-layer).

The walkthrough therefore separates:

1. The current compiler's source and IR conventions.
2. An exact-value plan using the semantic-plan vocabulary.
3. A storage optimization of that plan, with explicit validity obligations.

The latter two illustrate the contract the compiler should ultimately meet.
They are not assertions that the source compiler currently generates a
two-buffer implementation, or that exact-real softmax is a computable Lean
kernel. The landed plan layer is sort-generic; its executable numerical
fixtures use computable carriers such as exact rationals. Rational fixtures
do not supply an exact-real exponential or softmax implementation.

### 12.2 Current Lean source lowering: history, contractions, and nonlinearities

First reconcile the scan-bound convention. This companion uses N recurrence
steps and N + 1 hidden slices. In the current Lean source compiler,
`compileScan` interprets an iteration axis's declared extent as the
**complete-history length** and derives the step extent by subtracting one.
Thus the four-layer instance requires a history extent of **3**, a step
extent of **2**, and a final hidden read at index **2**.
The source declaration `axis l : ℕ = 3` expresses that history extent; it
does not request three recurrence steps.

There is also a source-shape restriction to make explicit. With the bare-axis
weight read `W[l,k,i]`, current
[size inference](../../leanncd/LeanNCD/Eval/SizeInfer.lean) requires W's l slot
to have the same extent as the declared l axis. Section 1's semantic input W
has only N matrices. For that direct Lean source spelling, an explicit input
adapter must instead provide a stack $\widetilde W$ with N + 1 matrices:

$$
\widetilde W[l,k,i]=W[l,k,i]\quad(l<N),\qquad
\widetilde W[N,k,i]=0.
$$

For Section 7 this has shape (3,2,2); the final matrix is unused because the
step context ranges only over [2]. This is an explicit extension of an input
representation, not permission for an out-of-bounds read to become zero.
The semantic program and its two-step weight domain remain unchanged.
The comparison below is mathematical; it does not assert exact agreement
between real softmax and the floating-point backend.

Starting from the source program, `TLProgram.compileToScheduled` supplies the
logical scan and downstream classifier to `prepareEvalPlan`. The latter
revalidates source invariants, checks capabilities and input signatures,
infers shapes, emits the positional graph, checks it, and constructs name
bindings. For this MLP shape, the lowering is schematically:

```text
outer graph:
  scan H
    base block:
      assign       h0[q,i] = sum_d W_in[i,d] X[q,d]
      write        H[q,i,0] <- h0[q,i]
    step block, context l in [2]:
      assign       a[q,i] = sum_k W_tilde[l,k,i] H[q,k,l]
      pointwise    hnext[q,i] = relu(a[q,i])
      write        H[q,i,l+1] <- hnext[q,i]
  assign           logits[q,c] = sum_k W_out[c,k] H[q,k,2]
  axiswise         Y[q,c] = softmax_c(logits[q,c])
```

This is an explanatory rendering, not serialized Lean IR or a newly executed
compiler fixture. `assign`, `pointwise`, and `axiswise` are actual step kinds;
the displayed writes describe the scan's separate `StateWriteMap` records.
a, hnext, and logits name IR intermediates, not extra tensors or statements
in the semantic source program.
The outer graph has a scan followed by an assignment and an axiswise
operation; the scan's local step block has an assignment followed by a
pointwise ReLU.

The positional translation makes the source indices explicit. For example,
on the recurrence basis (l,q,i,k), the W read selects (l,k,i) and the state
read selects (q,k,l). The state write uses the basis (l,q,i) and affine map

$$
\begin{pmatrix}q\\i\\l+1\end{pmatrix}
=
\begin{pmatrix}
0&1&0\\
0&0&1\\
1&0&0
\end{pmatrix}
\begin{pmatrix}l\\q\\i\end{pmatrix}
+
\begin{pmatrix}0\\0\\1\end{pmatrix}.
$$

The classifier's H read pins its time coordinate to 2; its output shape is
(1,10), and the marked class slot selects softmax axis position 1, using
zero-based slot numbering.

The
[scan IR](../../leanncd/LeanNCD/Eval/Plan/RawStep.lean) records complete-history
materialization, zero-then-base-overlay initialization, and immutable
pre-step snapshots. The
[current scan worker](../../leanncd/LeanNCD/Eval/Plan/Scan.lean) allocates
complete state histories and commits each step's writes after evaluating
against the pre-step state. It does **not** implement the rolling-buffer
plan below. Nor is its zero-filled future storage an assertion that future
coordinates are published in the reference machine.

### 12.3 Choose logical command groups

Return to the original exact-real semantic program of Sections 1-7,
including its original W input and $\mathrm{Out}=\{Y\}$.
For the general batch and hidden widths, define hidden blocks and occurrence
groups by

$$
B_u=\{(H,(q,i,u))\mid q\in[B],i\in[M]\}
\quad(0\le u\le N),
$$

$$
G_0=\{(s_{\mathrm{base}},(q,i))\mid q\in[B],i\in[M]\},
$$

$$
G_u=\{(s_{\mathrm{step}},(q,i,u-1))\mid q\in[B],i\in[M]\}
\quad(1\le u\le N).
$$

For the output, let

$$
B_Y=\{(Y,(q,c))\mid q\in[B],c\in[10]\},\qquad
G_Y=\{(s_{\mathrm{out}},(q,c))\mid q\in[B],c\in[10]\}.
$$

These are the existing source occurrences, not newly generated contributions.
Use q-major, then i-major or c-major order when representing each finite set
as a Lean list. No occurrence or coordinate is duplicated.

The
[semantic-plan syntax](../../leanncd/LeanNCD/Semantics/Plan/Syntax.lean)
uses annotations `initZero`, `acc`, `pub`, and `retire`.
A command is an ordered list of annotations. We write those annotations
schematically with the mathematical blocks and groups:

| Annotation | Concrete effect | Matching reference behavior |
| --- | --- | --- |
| `initZero B` | Materialize untouched accumulator slots as zero | No reference step; logical accumulators were already zero |
| `acc G` | Evaluate the ready bodies, then add their values to destination slots | One `CONTRIBUTE` per occurrence in G |
| `pub B` | Change slot roles from accumulators to published values without changing their contents | One `PUBLISH` per address in B |
| `retire B` | Clear the physical representations of dead published addresses | No reference step; logical history is retained |

These effects correspond to `execInit`, `execAcc`, `execPub`, and `execRet` in
[plan execution](../../leanncd/LeanNCD/Semantics/Plan/Step.lean).
In particular, `acc` is transactional over its group: it evaluates all bodies
before committing additions. It is not permission to read partially
accumulated destinations.

### 12.4 First plan: keep each hidden slice in its own buffer

Allocate one buffer $\beta_u$ of capacity BM for each hidden slice u,
and an output buffer $\beta_Y$ of capacity 10B. Define static placement by

$$
\operatorname{place}(H,(q,i,u))=(\beta_u,qM+i),\qquad
\operatorname{place}(Y,(q,c))=(\beta_Y,10q+c).
$$

Input storage is separate. All defined slots start uninitialized; the
reference accumulators start at zero independently of physical storage.
For each u from 0 through N, run the fused command

$$
\kappa_u=[
\operatorname{initZero}(B_u),\
\operatorname{acc}(G_u),\
\operatorname{pub}(B_u)
],
$$

then run the output command

$$
\kappa_Y=[
\operatorname{initZero}(B_Y),\
\operatorname{acc}(G_Y),\
\operatorname{pub}(B_Y)
].
$$

For the numerical instance there are four commands and twelve expanded
annotations. Their reference segments contain 32 transitions:
three hidden groups each contribute two values and publish two coordinates,
then the output group contributes ten values and publishes ten coordinates.
This groups the same operations differently from Section 7: both coordinates
are accumulated before their block publishes. Their equations are unchanged.

The plan uses six hidden slots and ten output slots. After its four commands:

| Boundary | Newly completed buffer | Reference store extension |
| --- | --- | --- |
| $\kappa_0$ | $\beta_0=(1,-2)$ | Publish $H_0=(1,-2)$ |
| $\kappa_1$ | $\beta_1=(4,0)$ | Publish $H_1=(4,0)$ |
| $\kappa_2$ | $\beta_2=(2,1)$ | Publish $H_2=(2,1)$ |
| $\kappa_Y$ | $\beta_Y=p$ | Publish Y = p |

Every earlier buffer remains represented. The plan uses
BM(N + 1) hidden slots in general. This is a simple Part V representation
of full history, not a claim that the current compiler allocates a distinct
physical buffer for each slice.

### 12.5 Second plan: reuse two hidden-state buffers

Allocate $\beta_A$ and $\beta_B$, each of capacity BM, and retain
$\beta_Y$ of capacity 10B. Give all buffers the real scalar sort and place
hidden addresses by time parity:

$$
\operatorname{place}(H,(q,i,u))=
\begin{cases}
(\beta_A,qM+i),&u\text{ even},\\
(\beta_B,qM+i),&u\text{ odd}.
\end{cases}
$$

Output placement is unchanged.
This placement is intentionally **not globally injective**:
H[0,0,0] and H[0,0,2] share a slot. What must be injective is the
layout view of the resources represented **at the same boundary**.

Use the same base command $\kappa_0$. For u = 1 through N, use

$$
\kappa_u=[
\operatorname{initZero}(B_u),\
\operatorname{acc}(G_u),\
\operatorname{pub}(B_u),\
\operatorname{retire}(B_{u-1})
],
$$

and finish with

$$
\kappa_Y=[
\operatorname{initZero}(B_Y),\
\operatorname{acc}(G_Y),\
\operatorname{pub}(B_Y),\
\operatorname{retire}(B_N)
].
$$

The old slice is not retired until every occurrence in the next hidden group
has finished reading it. The final slice is retained until **all ten**
classifier occurrences per batch member have been consumed.
The final retirement is allowed because H is internal, not a designated
output.

For N = 2 this is four commands, fifteen expanded annotations, and still
32 reference transitions. Seven annotations are storage-only: four
initializations and three retirements.

### 12.6 Every expanded storage boundary of the two-buffer plan

The following table gives memory **after** each annotation for the Section 7
inputs. The start row is not an annotation. A dash denotes uninitialized
storage (`none` in the Lean memory model), not a scalar zero.
Each hidden buffer entry shows both its current logical owner and its two
values. Published inputs remain separately available throughout.

| Annotation | Action | $\beta_A$ | $\beta_B$ | $\beta_Y$ | Pending occurrences |
| --- | --- | --- | --- | --- | --- |
| Start | Install inputs only | - | - | - | 16 |
| 1 | `initZero` $B_0$ | acc $H_0:(0,0)$ | - | - | 16 |
| 2 | `acc` $G_0$ | acc $H_0:(1,-2)$ | - | - | 14 |
| 3 | `pub` $B_0$ | pub $H_0:(1,-2)$ | - | - | 14 |
| 4 | `initZero` $B_1$ | pub $H_0:(1,-2)$ | acc $H_1:(0,0)$ | - | 14 |
| 5 | `acc` $G_1$ | pub $H_0:(1,-2)$ | acc $H_1:(4,0)$ | - | 12 |
| 6 | `pub` $B_1$ | pub $H_0:(1,-2)$ | pub $H_1:(4,0)$ | - | 12 |
| 7 | `retire` $B_0$ | - | pub $H_1:(4,0)$ | - | 12 |
| 8 | `initZero` $B_2$ | acc $H_2:(0,0)$ | pub $H_1:(4,0)$ | - | 12 |
| 9 | `acc` $G_2$ | acc $H_2:(2,1)$ | pub $H_1:(4,0)$ | - | 10 |
| 10 | `pub` $B_2$ | pub $H_2:(2,1)$ | pub $H_1:(4,0)$ | - | 10 |
| 11 | `retire` $B_1$ | pub $H_2:(2,1)$ | - | - | 10 |
| 12 | `initZero` $B_Y$ | pub $H_2:(2,1)$ | - | acc $Y:0^{10}$ | 10 |
| 13 | `acc` $G_Y$ | pub $H_2:(2,1)$ | - | acc Y:p | 0 |
| 14 | `pub` $B_Y$ | pub $H_2:(2,1)$ | - | pub Y:p | 0 |
| 15 | `retire` $B_2$ | - | - | pub Y:p | 0 |

For example, annotation 9 writes into the slots that once held H_0.
At that point H_0 is retired and H_2 is an unpublished accumulator; H_1
remains published in the other buffer.
The layout is injective at each intermediate boundary, including those
**inside** a fused command.

After annotation 10, the logical store still contains all three hidden slices.
Its values at the reused addresses are distinct:

$$
\sigma(H,(0,0,0))=1,\qquad
\sigma(H,(0,0,2))=2.
$$

Only H_2's resource is mapped to $\beta_A$.
The read view `readPub` returns no value for retired H_0, even though
H_0's placement points to a slot now holding 2. Retirement therefore cannot
turn a stale read of H_0 into a read of H_2.

The two-buffer plan reserves four hidden slots instead of six, with the
same ten output slots. In general its reserved hidden capacity is 2BM,
independent of N. These counts exclude input storage and any workspace
needed by expression evaluation or a concrete matrix/softmax kernel; they
are not a total runtime-memory bound. For N = 0 a single hidden buffer
suffices, although the uniform two-buffer allocation remains valid.

### 12.7 Check the certificates, not just the final numbers

The
[validity layer](../../leanncd/LeanNCD/Semantics/Plan/Validity.lean)
checks more than whether a run happened to produce p. The requirements
for these plans specialize as follows:

| Obligation | Why it holds in the displayed plans |
| --- | --- |
| Occurrence coverage | $G_0,\ldots,G_N,G_Y$ are disjoint and cover exactly $\mathcal O_P$ |
| Publication coverage | $B_0,\ldots,B_N,B_Y$ are disjoint and cover every defined address |
| Initialization freshness | A block is initialized before any occurrence targeting it is consumed; no accumulated value is erased |
| Materialization | Every destination has an initialized accumulator slot before accumulation or publication |
| Readiness | $G_0$ reads inputs; $G_u$ reads live $B_{u-1}$; $G_Y$ reads live $B_N$ |
| Completion | Each coordinate's singleton occurrence is consumed before its publication |
| Retirement | Only live internal H slices retire, after their last required reads; no Y output retires |
| Layout safety | The current and next slices occupy different buffers; a reused slot's old resource has already retired |
| Sort and capacity | Every offset is below BM or 10B, and placement preserves the scalar sort |

The plan's
[side conditions](../../leanncd/LeanNCD/Semantics/Plan/Simulation.lean)
are named `InitOK`, `AccOK`, `PubOK`, and `RetOK`.
One important distinction: `RetOK` itself checks that the retired addresses
are live and not outputs. The prohibition on retiring a value needed by
a later contribution is enforced by that later accumulation's `ReadyOK`
condition over `Live`, not by a future-reader test inside `RetOK`.

For fused commands, the relevant validity is `FValid`: validity of the
expanded annotation sequence. `checkPlanF` checks that expansion.
Inspecting only the four outer command boundaries would miss illegal
intermediate aliasing or a read-before-publication inside a command.

Some concrete invalid variants show why these premises matter:

- Move retirement of $B_0$ before accumulation of $G_1$: the next group
  loses its live source, even though the logical store still remembers it.
- Omit retirement of $B_0$, then initialize $B_2$: both old published H_0
  and new accumulator H_2 map to the same slots, violating `LayoutOK`.
- Initialize $B_2$ again after its accumulation: this erases (2,1);
  initialization freshness fails.
- Publish $B_Y$ after consuming only nine classifier occurrences: the tenth
  coordinate's fiber is incomplete.
- Retire $B_Y$ after publication: output retention fails, even if no
  contribution reads Y.

These are validity failures, not alternative successful implementations.
The semantic-plan runner alone is not a substitute for checking validity;
some invalid plans can run to an apparently finished state.

### 12.8 Relate concrete execution to reference execution

Write the concrete state at a command boundary as $(\mathsf{pc},M)$ and its
reference state as $C=(\sigma,\alpha,U)$. The relation R from
[plan memory](../../leanncd/LeanNCD/Semantics/Plan/Memory.lean) requires:

- C is reference-reachable from the same input environment.
- U contains exactly the occurrences not in the consumed prefix, and
  $\operatorname{dom}(\sigma)$ is exactly the logical published prefix.
- Every live published resource and every materialized unpublished
  accumulator has its correct value in its placed slot.
- Any unpublished accumulator that has received a contribution remains
  materialized.
- Unmapped slots contain `none`, and retired addresses remain logically
  published.

The expanded prefix sets are `Cons`, `Pub`, `Mat`, and `Ret`;
`Live = Pub \ Ret`. Retiring an address changes Ret and the concrete
representation but does not remove it from Pub or from $\sigma$.
In particular, after the final command there are still 50 logical published
addresses in the Section 7 model, although only the 34 inputs and ten Y
addresses remain live in the two-buffer representation.

At the initial boundary, inputs agree and all defined storage is
uninitialized, matching the initialization obligation `R_start`.
An accumulation group matches a sequence of `CONTRIBUTE` transitions;
a publication block matches a sequence of `PUBLISH` transitions.
Initialization and retirement match **zero reference transitions**.
Thus each successful concrete command preserves R while taking zero or
more reference steps:

$$
R((\mathsf{pc},M),C)
\ \land\
(\mathsf{pc},M)\longrightarrow_\Pi(\mathsf{pc}+1,M')
\quad\Longrightarrow\quad
\exists C'.\
C\longrightarrow^* C'
\ \land\
R((\mathsf{pc}+1,M'),C').
$$

This is the shape of the landed simulation theorem `step_R_command`;
it additionally requires the certified prefix reference state, annotation
side conditions, and layout safety at every expanded boundary.
Here each hidden command matches four reference transitions and the output
command matches twenty, totalling the same 32 transitions as before.

At the final boundary, coverage makes the reference state complete. All Y
coordinates remain live, so `Decode` reads

$$
\operatorname{Decode}(M_{\mathrm{final}})[0,c]
=M_{\mathrm{final}}[(\beta_Y,c)]
=\sigma(Y,(0,c))
=p[c].
$$

If instantiated as a valid semantic plan with suitable scalar operations
and primitive interpretations, this is the conclusion supplied by
`terminal_adequacy_F` and `done_correct_F`: the decoded result is the
denotation of the source program. A failing primitive would instead require
the matching failure theorem; it cannot be hidden as a zero or a partial
successful output.

For this document, the buffer trace and its certificates are a worked
mathematical illustration. No new Lean MLP term, accepted `checkPlanF`
result, scan-liveness proof, or source-to-plan compiler-correctness theorem
has been added. The current Lean compiler lowering, the proved generic
semantic-plan machinery, and the remaining link between them are intentionally
kept distinct.

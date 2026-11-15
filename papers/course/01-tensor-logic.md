# Chapter 1. Tensor Logic and the running example

**Summary.** Tensor Logic (TL) is a tiny language whose statements do not assign to tensors but contribute scalar values to tensor coordinates, and the meaning of a coordinate is the sum of everything contributed to it. This chapter introduces the surface syntax, the core syntax it elaborates to, the vocabulary of occurrences, destinations and fibres, and the running example `Scorer` with all its numbers, and it ends by listing the six questions that the rest of the course answers.

This chapter needs only finite sets, functions, and commutative monoids; [Chapter 0](00-prerequisites.md) is not a prerequisite. The semantic authority is the specification in `papers/semantics/`, Parts I and II (Sections 3 to 16), Section 21 of Part III for the worked examples, and the overview. Rules are cited by specification section.

Throughout, scalars are exact reals: $K=\mathbb{R}$, $\oplus=+$, $\otimes=\cdot$, $0_K=0$. Intervals are zero-based: $[n]=\{0,\dots,n-1\}$, and $[0]=\varnothing$.

## 1. What Tensor Logic is

Most numerical languages read `Y[i] = e` as a command: evaluate $e$ and store the result in cell `Y[i]`, destroying the old content. TL reads it differently.

> A statement `T[...] = E` generates one *contribution* for each admissible choice of its index variables. A contribution is a scalar value addressed to one coordinate of $T$. The value of a coordinate is the sum of all contributions addressed to it. The sum over no contributions is $0$.

So `=` is a contribution, not an assignment. Several statements may write the same coordinate, and then their contributions add. The surface notation is einsum-style: an index variable that appears on the right of a statement but not in the output indices is summed away, term by term. A supplied input is never an implicit contribution to anything.

We look at five short programs. Each is used again later in the chapter.

**Example 1.1 (matrix multiply, then with a bias).** Let $W$ have shape $(m,n)$ and $X$ shape $(n,p)$.

```text
Y[i,j] = W[i,k] X[k,j]
```

The variable $k$ occurs only on the right, so it is summed: $Y[i,j]=\sum_k W[i,k]X[k,j]$. This is the ordinary matrix product. Now add a bias. Let $X$ have shape $(n)$ and $B$ shape $(m)$:

```text
Y[i] = W[i,k] X[k] + B[i]
```

The right side has two additive terms. The first contains $k$, so $k$ is summed inside that term. The second contains no $k$. The bias $B[i]$ is added once, not once for each $k$. Section 2 makes this rule exact.

The implemented Python DSL (`docs/tensor_logic_dsl.md`) has the same statement shape, with axis objects instead of strings carrying identity:

```text
tl.Out[q, dm] = tl.W2[dm, dh] * tl.Y[q, dh] + tl.H[q, dm]   # contraction + residual
```

Here `dh` is summed in the first term only, and `tl.H[q, dm]` is a residual added once.

**Example 1.2 (the boundary example).** Let $C$ and $R$ be inputs of shapes $(4)$ and $(5)$, and $T$ a defined tensor of shape $(5,4)$ (spec Section 11.1):

```text
T[0,c] = C[c]    # c in [4]
T[r,0] = R[r]    # r in [5]
```

The first statement addresses the top row, the second the left column. The corner $(0,0)$ is addressed by both. It receives two contributions and
$$T[0,0]=C[0]+R[0].$$
There is no requirement that the two contributions agree. The interior coordinates $(r,c)$ with $r,c\ge1$ receive no contribution and are $0$. In one formula,
$$T[r,c]=\mathbf{1}_{r=0}\,C[c]+\mathbf{1}_{c=0}\,R[r].$$

**Example 1.3 (an MLP layer with relu).** Let $W$, $X$, $B$ be as in Example 1.1:

```text
H[i] = relu(W[i,k] X[k] + B[i])
```

The primitive $\mathrm{relu}(x)=\max(0,x)$ is applied to the whole right side: the sum over $k$ and the bias are both inside its argument. Contrast two programs on a shared vector domain with inputs $U$ and $V$ (spec Section 11.3):

```text
T[i] = relu(U[i])         Pre[i] = U[i]
T[i] = relu(V[i])         Pre[i] = V[i]
                          T[i]   = relu(Pre[i])
```

The left program has two contributions to each $T[i]$ and gives $\mathrm{relu}(U[i])+\mathrm{relu}(V[i])$. The right program collects $\mathrm{Pre}[i]=U[i]+V[i]$ first and then applies relu once. For $U[i]=1$, $V[i]=-1$ the left gives $1$ and the right gives $0$. The activation boundary is set by the shape of the expressions, not by the order of lines.

**Example 1.4 (a guarded statement).** Let $X=(4,-1)$ and let $Y$ have shape $(2)$ (spec Section 21.3):

```text
Y[i] = log(X[i]) where i < 1
```

The guard `where i < 1` keeps only the valuation $i=0$. The program has one contribution, $\log 4$, so $Y=(\log 4,\,0)$. The coordinate $Y[1]$ is addressed by nothing and is $0$. The partial primitive $\log$ is never applied to $X[1]=-1$.

**Example 1.5 (a finite history, the scan example).** Let $X,Z$ be inputs of shape $(d)$, let $H$ be defined of shape $(d,N+1)$, and let $F:\mathbb{R}^{[d]}\to\mathbb{R}^{[d]}$ be a total function (spec Section 11.4):

```text
H[i,l]   = X[i]             # i in [d], l in [N+1]
H[i,0]   = Z[i]             # i in [d]
H[i,l+1] = F(H[:,l])[i]     # i in [d], l in [N]
```

The first statement contributes the persistent input $X$ at every time. The second adds the initial state $Z$ at time $0$. The third adds the next step, where $H[:,l]$ is the completed time slice $l$. Writing $H_l$ for that slice, the collected equations are
$$H_0=X+Z,\qquad H_{l+1}=X+F(H_l)\quad(l\in[N]).$$
Take $d=1$, $N=2$, $X[0]=2$, $Z[0]=3$ and $F(h)[0]=2h[0]$. Then
$$H_0=2+3=5,\qquad H_1=2+2\cdot5=12,\qquad H_2=2+2\cdot12=26,$$
so $H[0,0]=5$, $H[0,1]=12$, $H[0,2]=26$. The program names $H$ on both sides, yet at the level of coordinates $H[\cdot,l+1]$ reads only $H[\cdot,l]$. Chapter 5 turns that observation into a rank certificate. The printed variable `l` has two different ranges, $[N+1]$ and $[N]$, in different statements. Reusing a spelling does not identify binders.

**Why this matters for an agentic coder.** An agent that reads `=` as assignment will generate code that overwrites. In Example 1.2 overwriting loses the corner sum; in Example 1.5 it loses the persistent input $X$. The first thing to teach an agent about TL is: every statement is a summand, and unwritten coordinates are zero.

## 2. Surface versus core

The surface language is short to write but leaves information implicit: which variables are summed, where their sums are scoped, and where slices begin and end. The *core* language states all of it. *Elaboration* translates surface to core. It is a translation, not an execution. The specification fixes the core in Part II, Section 13, and the translation in Section 15. We give the vocabulary, then explain elaboration by example. For the full rules see Part II, Section 15.

### 2.1 Index variables, contexts and valuations

An *index variable* such as $i$ is a bound symbol ranging over a finite coordinate set $I_i=[n_i]$. Two variables with the same spelling in different statements are unrelated. Two slots use the same variable only if the statement says so by using one variable identity; equal spelling in different statements, or equal extent, does not make variables the same. Chapter 2 treats the matching of axes properly.

**Definition 1.6 (context and valuation).** An *index context* is a finite list of distinct index variables with their ranges,
$$\Gamma=(i_1:I_{i_1},\dots,i_k:I_{i_k}).$$
A *valuation* for $\Gamma$ assigns each variable a coordinate in its range. The set of valuations is
$$\mathrm{Val}(\Gamma)=\prod_{i\in\mathrm{vars}(\Gamma)}I_i.$$
The empty context has exactly one valuation, the empty assignment, written $()$.

For $\Gamma=(i:[2],j:[3])$ and $\nu=\{i\mapsto1,\,j\mapsto2\}$, the index expression $i+j$ evaluates to $3$. Core index expressions are affine: $e::=b\mid i\mid e+e\mid c\,e$ with integer $b,c$. In $M[i,i]$ the two slots share one variable and select the diagonal. In $M[i,j]$ they vary independently.

### 2.2 Guards versus Iverson factors

The core has index predicates $Q$, built from $\mathrm{true}$, $\mathrm{false}$, $e=e$, $e<e$ and the Boolean connectives. A predicate depends only on index values, never on tensor values. There are two ways to use one, and they are different.

- A *guard* $Q$ on a statement removes valuations. Only valuations with $Q$ true generate occurrences. A removed valuation imposes no obligation on the body, which is never evaluated there.
- An *Iverson factor* $\mathbf{1}_Q$ is a scalar expression equal to $1_K$ when $Q$ holds and $0_K$ when it does not. It keeps every occurrence and multiplies the body value.

Take the guarded statement of that example and replace the guard by a factor:

```text
Y[i] = 1_{i<1} log(X[i])      # i in [2], X = (4, -1); 1_{i<1} is mathematical notation for the Iverson factor
```

Now $i=1$ is an actual occurrence whose body is $0\cdot\log(-1)$. The primitive $\log$ is undefined at $-1$, and multiplying by zero does not repair it. We will see in Chapter 3 that the product is undefined too ($0\otimes\bot=\bot$). The guarded program has a value; this one has none on that input. The guard exists so that the valuations it removes carry no obligation: their bodies are not evaluated, their primitives need not be in domain, and their reads need not be in bounds. An Iverson factor removes none of these obligations. Both uses depend on indices only, so both give a set of contributions that can be counted before any body is evaluated; they differ in what the surviving and the removed valuations owe.

### 2.3 Term-local contraction

An index variable that occurs in a term of the right-hand side but not in the statement's output indices is *contracted* in that term, and its sum is scoped over that term only. Formally, the surface body is a list of product terms $t_1,\dots,t_h$ and the contracted set of term $t_b$ is
$$C_b=\mathrm{FV}(t_b)\setminus\mathrm{vars}(\Gamma_s),$$
where $\Gamma_s$ is the statement's context, built from the variables in its output indices (spec Section 15.2). Each variable in $C_b$ gets a reduction $\bigoplus_{k\in I_k}$ around its own term. Then:
$$W[i,k]X[k]+B[i]\;\mapsto\;\Big(\bigoplus_{k\in I_k}W[i,k]\otimes X[k]\Big)\oplus B[i].$$
It does not elaborate to $\bigoplus_k(W[i,k]\otimes X[k]\oplus B[i])$, which would add the bias $|I_k|$ times. The difference is visible at an empty range: if $I_k=[0]$ the first form gives $0\oplus B[i]=B[i]$ and the second gives $0$. A registered unary primitive $f$ enclosing the right side puts the whole elaborated body inside its argument, $E_s=f(B_s)$, which is why $\mathrm{relu}$ in Example 1.3 sees the sum and the bias together.

### 2.4 The core constructors

Core expressions are built from the constructors below (spec Section 13.3). All the combining operations are scalar. There is no implicit application of an array operator coordinate by coordinate and no implicit distribution of any operator over $\oplus$.

| Constructor | Meaning |
| --- | --- |
| $c_K$ | A literal scalar of $K$. |
| $T[e_1,\dots,e_k]$ | The scalar stored at one coordinate of the named tensor $T$; the number of indices equals its rank, and a scalar tensor is read as $T[]$. |
| $\mathbf{1}_Q$ | The scalar embedding of an index predicate: $1_K$ if $Q$ holds, $0_K$ if not. |
| $E_1\oplus E_2$ | The sum of two scalar expressions. |
| $E_1\otimes E_2$ | The product of two scalar expressions. |
| $\bigoplus_{j\in I_j}E$ | A reduction: the sum of $E$ over the whole range of $j$, which it binds in $E$; the empty reduction is $0_K$. |
| $\mathrm{tab}_{j_1\in I_1,\dots,j_m\in I_m}(E)$ | Tabulation: the complete array whose entry at $(j_1,\dots,j_m)$ is the scalar $E$; it binds the $j$'s and is not a sum. |
| $\mathrm{at}(E,(e_1,\dots,e_m))$ | Selection: the scalar at one coordinate of an array expression $E$. |
| $f(E_1,\dots,E_q)$ | Application of a registered primitive, such as $\mathrm{relu}$ or $\log$, which carries its own domain of definition $\mathcal{D}_f$. |

The primitive registry matters here. A primitive is a deterministic function on its domain $\mathcal{D}_f\subseteq\tau_1\times\dots\times\tau_q$, and outside it the application is undefined. A registered primitive may take and return arrays; $F$ in Example 1.5 is one. `tab` builds its argument and `at` selects from its result. For real arithmetic, $\mathrm{relu}$ is defined everywhere, $\log$ needs $x>0$, and division needs a nonzero divisor.

### 2.5 The core statement form

**Definition 1.7 (core statement).** A core statement with identifier $s$ has the form
$$\text{for }\Gamma_s\text{ where }Q_s:\qquad T_s[e_{s,1},\dots,e_{s,k_s}]\mathrel{+}=E_s.$$
Here $T_s$ is a defined tensor, $\Gamma_s$ is the statement's context of contribution variables, $Q_s$ is its guard (true if omitted), the $e_{s,r}$ are affine output indices over $\Gamma_s$, and $E_s$ is a scalar body whose free variables lie in $\Gamma_s$. The symbol $\mathrel{+}=$ is shorthand for "contribute"; it never reads the current value of $T_s$.

The binders $\Gamma_s$ are part of the statement. They are collected before output indices are simplified, so cancelling coefficients does not delete a binder. Let $T$ have extent $1$ (one coordinate, $0$). With $i\in[3]$ the statement $T[0\cdot i]\mathrel{+}=1_K$ (the index $i$ has coefficient $0$, so every valuation writes the scalar-indexed coordinate $0$) has three occurrences addressed to $(T,0)$, not one. Likewise $Y[i-i]=\mathrm{relu}(X[i])$ on $X=(2,-1,5)$ has three contributions to $Y[0]$, namely $2$, $0$, $5$, and $Y[0]=7$, not $\mathrm{relu}(6)=6$.

### 2.6 Elaboration by example

The recipe is: collect $\Gamma_s$ from the output indices, bind every other variable by a reduction around its own term, and put a primitive around the whole body.

- Bias and activation (Examples 1.1 and 1.3). The formula of Section 2.3 is the core body; for Example 1.3 it sits inside $\mathrm{relu}$.
- Guard (Example 1.4). The guard moves to the `where` clause: for $i\in[2]$ where $i<1$: $Y[i]\mathrel{+}=\log(X[i])$.
- The scan (Example 1.5). The first statement has $\Gamma=(i:[d],l:[N+1])$ and body $X[i]$, which does not mention $l$. That is a broadcast, not a contraction: varying $l$ makes separate contributions with the same value. The third statement contains the slice $H[:,l]$, which expands to a tabulation with a fresh bound variable $j$, and the selection $[i]$ expands to $\mathrm{at}$:
$$\text{for }i\in[d],\,l\in[N]:\quad H[i,l+1]\mathrel{+}=\mathrm{at}\Big(F\big(\mathrm{tab}_{j\in[d]}H[j,l]\big),(i)\Big).$$

The surface language accepts only an additive body of products of scalar factors, optionally under one unary operator or one marked slice operator. Factors are literals, named reads, Iverson values $\mathbf{1}_Q$, and registered unary operators applied to a named read; a factor adds no reduction of its own (spec Section 15.1). The slice shorthand `H[:,l]` followed by a selection `[i]`, as in Example 1.5, is not in this fragment: it is an explicit core scalar expression written in short form (spec Section 15.1), while a marked slice operator (`A[q,s.]`) is a separate abbreviation (spec Section 15.4). Anything more deeply nested must be written directly in core, with explicit reductions and tabulations. This restriction exists so that no scope for a contraction has to be guessed. Elaboration never merges two textually identical statements and never orders statements.

**Why this matters for an agentic coder.** Two classes of bug live here. An agent may put a contraction around the whole right-hand side, so that a bias gets added once per summed index. An agent may also encode a boundary as a zero factor when it should be a guard, which changes both the number of contributions, which partial primitives are ever evaluated, and which reads must be in bounds. Both are checked cheaply against the elaboration rules, never by running the program.

## 3. Statements, occurrences, destinations

After elaboration every statement $s$ carries the data below. They are the interface between syntax and semantics.

| Data | Meaning |
| --- | --- |
| $T_s$ | the destination tensor |
| $\Gamma_s$ | the context of contribution variables |
| $D_s\subseteq\mathrm{Val}(\Gamma_s)$ | admissible valuations: those where the guard $Q_s$ holds |
| $\phi_s:D_s\to\mathrm{Coord}(T_s)$ | the write map: $\phi_s(\nu)=([\![e_{s,1}]\!]_\nu,\dots,[\![e_{s,k_s}]\!]_\nu)$ |
| $E_s$ | the scalar body |

$D_s$ and $\phi_s$ depend on indices only. That is why the set of contributions is known without evaluating a single body.

**Definition 1.8 (occurrences, destinations, fibres).** The set of *occurrences* of a program $P$ is the disjoint union
$$\mathcal{O}_P=\coprod_{s\in P}D_s=\{(s,\nu)\mid s\in P,\ \nu\in D_s\}.$$
The *destination* of an occurrence $o=(s,\nu)$ is $\mathrm{dst}(o)=(T_s,\phi_s(\nu))\in\mathrm{Addr}_{\mathrm{Def}}$. The *fibre* (writer family) of a defined address $a$ is
$$\mathcal{C}_P(a)=\mathrm{dst}^{-1}(a)=\{o\in\mathcal{O}_P\mid\mathrm{dst}(o)=a\}.$$

An *address* $(T,p)$ is a tensor name together with a coordinate. Coordinates of different tensors are different addresses even if the tuples coincide. 

**Proposition 1.9.** The fibres $\mathcal{C}_P(a)$, over defined addresses $a$ in the image of $\mathrm{dst}$, partition $\mathcal{O}_P$. The addresses outside the image have empty fibres.

*Proof.* $\mathrm{dst}$ is a function on $\mathcal{O}_P$, and the fibres of a function partition its domain. The write maps land in the declared shapes because structural well-formedness requires it (spec Section 14.3, condition 4). $\square$

Neither injectivity of $\phi_s$ nor disjointness of different statements' write images is required. Overlap is the point of the language.

**Why duplicate statements are distinct occurrences.** The occurrence is the pair $(s,\nu)$, and $s$ is a statement identifier, not statement text. The statements
```text
T[i] = X[i]      # s1, i in [2]
T[i] = X[i]      # s2, i in [2]
```
have fibre $\mathcal{C}_P(T,0)=\{(s1,i{=}0),(s2,i{=}0)\}$, with two members, so $T[0]=2X[0]$ and not $X[0]$. If occurrences were identified by their text, or by their destination and body, the two summands would collapse and the language would silently become idempotent. Elaboration preserves every source statement.

**Why a statement with empty context has exactly one occurrence.** $\mathrm{Val}(())=\{()\}$ has one element. If $Q_s$ is true there (including when no guard is written), $D_s=\{()\}$, and the statement has exactly one occurrence, $(s,())$. The number of occurrences is $|D_s|$, which depends on $\Gamma_s$ and $Q_s$, not on the rank of the destination. The scalar statement `L[] = log(Y[1])` has one occurrence addressed to $(L,())$. By contrast `T[0] = 1` (with no binders) writes coordinate $0$ of a tensor $T$ of extent $1$ and also has exactly one occurrence, while $T[0\cdot i]\mathrel{+}=1_K$ has $|I_i|$. A guard with no variables could remove the sole occurrence, if it is the constant $\mathrm{false}$.

**Occurrences are not multiplications.** In `Z[j] = W[j,i] X[i]` the sum over $i$ lives inside the body of one occurrence for each $j$. It does not create an occurrence for each pair $(j,i)$. Chapter 2 presents the same statement as a pushforward over the four pairs $(j,i)$, which gives the same value. Here the count that matters is the count of contributions to a defined coordinate, and for s1 that is one per $j$.

**Why this matters for an agentic coder.** The sets $\mathcal{O}_P$ and $\mathrm{dst}$ are the first things worth computing and printing for any program: they are cheap, depend only on indices, and answer "how many writers does this coordinate have" before any value is touched. An implementation that merges, reorders or drops occurrences has changed the program.

## 4. The running example

We use one fixed program in every chapter. It is small enough to compute by hand and rich enough to show a collision, a nonlinearity, and a partial primitive.

### 4.1 Surface program

```text
inputs:   X[i]    i in [2]
          W[j,i]  j in [2], i in [2]
          B[j]    j in [2]
defined:  Z[j], Y[j]  j in [2];   L[]  (scalar)
outputs:  Y, L

s1:  Z[j] = W[j,i] X[i]      # surface einsum: i is contracted
s2:  Z[j] = B[j]             # a second writer to every Z[j]
s3:  Y[j] = relu(Z[j])
s4:  L[]  = log(Y[1])        # log is partial: needs Y[1] > 0
```

So $\mathrm{In}=\{X,W,B\}$, $\mathrm{Def}=\{Z,Y,L\}$, $\mathrm{Out}=\{Y,L\}$. Note that $Z\in\mathrm{Def}$ is not an output. A program with several outputs and a coordinate written twice is exactly the situation that distinguishes TL from assignment-based languages.

### 4.2 Core forms

Applying Section 2:

- s1: for $j\in[2]$: $\;Z[j]\mathrel{+}=\bigoplus_{i\in[2]}W[j,i]\otimes X[i]$
- s2: for $j\in[2]$: $\;Z[j]\mathrel{+}=B[j]$
- s3: for $j\in[2]$: $\;Y[j]\mathrel{+}=\mathrm{relu}(Z[j])$
- s4: (no binders) $\;L[]\mathrel{+}=\log(Y[1])$

For s1 the context is $\Gamma_{s1}=(j:[2])$, the term has free variables $\{j,i\}$, and so $C_1=\{i\}$ is contracted inside the body. For s4, $L[]$ has no output indices and no variable occurs in the body, so the context is empty. No guards are written; every $Q_s$ is true.

### 4.3 The occurrence table

The admissible domains are $D_{s1}=D_{s2}=D_{s3}=[2]$ (valuations of $j$) and $D_{s4}=\{()\}$. So
$$\mathcal{O}_P=D_{s1}\sqcup D_{s2}\sqcup D_{s3}\sqcup D_{s4},\qquad|\mathcal{O}_P|=2+2+2+1=7.$$
The write maps are $\phi_{s1}(j)=\phi_{s2}(j)=\phi_{s3}(j)=(j)$ and $\phi_{s4}(())=()$. The *read footprint* $\mathrm{Read}(E,\nu)$ of an occurrence is the set of addresses its body reads. We will use it in Chapters 3 and 5, to state read stability and to say when an occurrence is ready. For a reduction it includes every address under the binder.

| Occurrence $o$ | $\mathrm{dst}(o)$ | Body at $o$ | $\mathrm{Read}(o)$ |
| --- | --- | --- | --- |
| $(s1,j{=}0)$ | $(Z,0)$ | $\bigoplus_i W[0,i]\otimes X[i]$ | $\{(W,(0,0)),(W,(0,1)),(X,0),(X,1)\}$ |
| $(s1,j{=}1)$ | $(Z,1)$ | $\bigoplus_i W[1,i]\otimes X[i]$ | $\{(W,(1,0)),(W,(1,1)),(X,0),(X,1)\}$ |
| $(s2,j{=}0)$ | $(Z,0)$ | $B[0]$ | $\{(B,0)\}$ |
| $(s2,j{=}1)$ | $(Z,1)$ | $B[1]$ | $\{(B,1)\}$ |
| $(s3,j{=}0)$ | $(Y,0)$ | $\mathrm{relu}(Z[0])$ | $\{(Z,0)\}$ |
| $(s3,j{=}1)$ | $(Y,1)$ | $\mathrm{relu}(Z[1])$ | $\{(Z,1)\}$ |
| $(s4,())$ | $(L,())$ | $\log(Y[1])$ | $\{(Y,1)\}$ |

The fibres are:

| Address $a$ | Fibre $\mathcal{C}_P(a)$ |
| --- | --- |
| $(Z,0)$ | $\{(s1,j{=}0),(s2,j{=}0)\}$ |
| $(Z,1)$ | $\{(s1,j{=}1),(s2,j{=}1)\}$ |
| $(Y,0)$ | $\{(s3,j{=}0)\}$ |
| $(Y,1)$ | $\{(s3,j{=}1)\}$ |
| $(L,())$ | $\{(s4,())\}$ |

There are five defined addresses, and $2+2+1+1+1=7$ occurrences, as Proposition 1.9 requires. Every fibre is nonempty here. The only collisions are the two addresses of $Z$, where s1 and s2 both write.

### 4.4 Values on the primary input $\eta_1$

Let
$$X=(1,-2),\qquad W=\begin{pmatrix}1&1\\2&-1\end{pmatrix},\qquad B=(1,0),$$
that is $W[0,0]=1$, $W[0,1]=1$, $W[1,0]=2$, $W[1,1]=-1$. We compute the contribution of each occurrence, then collect. Dependencies make the order forced: $Z$ reads only inputs, $Y$ reads $Z$, $L$ reads $Y$.

1. Occurrences of s1.
$$(s1,0):\ 1\cdot1+1\cdot(-2)=-1,\qquad(s1,1):\ 2\cdot1+(-1)(-2)=2+2=4.$$
2. Occurrences of s2: $(s2,0)$ contributes $B[0]=1$ and $(s2,1)$ contributes $B[1]=0$.
3. Collect $Z$:
$$Z[0]=-1+1=0,\qquad Z[1]=4+0=4.$$
So $Z=(0,4)$. The check from the surface form is $Z[0]=1\cdot1+1\cdot(-2)+1=0$ and $Z[1]=2\cdot1+(-1)(-2)+0=4$.
4. Occurrences of s3: $\mathrm{relu}(0)=0$ and $\mathrm{relu}(4)=4$. Each fibre has one member, so $Y=(0,4)$.
5. Occurrence of s4: $\log(Y[1])=\log4$, defined because $4>0$. So $L=\log4$.

The result is $Z=(0,4)$, $Y=(0,4)$, $L=\log 4$. Note that $Y[0]=0$ is harmless: s4 does not read $Y[0]$, and $\mathrm{relu}(0)$ is defined. Also $Z[0]$ is the sum of the contribution $-1$ and the contribution $1$, not either alone.

This triple is the unique *model* of `Scorer` on $\eta_1$ in the sense of Chapter 4. Informally, a model is a complete assignment of values to $Z$, $Y$ and $L$ that extends the inputs, makes every occurrence body defined, and gives each defined coordinate the sum over its fibre. The triple above has all three properties. It is the only one, because each defined coordinate is forced by the coordinates it reads, level by level, so no other assignment can satisfy the sums.

### 4.5 The failing input $\eta_0$

Keep $W$ and $B$ and set $X=(0,0)$.

1. s1: both contributions are $0$, since every product contains $X$.
2. s2: $1$ and $0$.
3. Collect: $Z=(0+1,\,0+0)=(1,0)$.
4. s3: $\mathrm{relu}(1)=1$, $\mathrm{relu}(0)=0$. So $Y=(1,0)$.
5. s4: the body is $\log(Y[1])=\log0$. The primitive $\log$ is defined only for $x>0$, so the body is *undefined*.

`Scorer` has no model on $\eta_0$, and we say why in words. A model must extend $\eta_0$, so $X=(0,0)$. The equations for $Z$ read only inputs, so they force $Z=(1,0)$. The equations for $Y$ then force $Y=(1,0)$. In any assignment satisfying these equations, the unique occurrence of s4 has body $\log0$, which is undefined. A model requires every occurrence body to be defined. An assignment with a different $Y[1]$ would make $\log(Y[1])$ defined, but it would then violate the equation for $Y$. No assignment to $L$ can rescue this, because the failure is in the body, not in the value of $L$. In particular, "undefined" does not mean "contributes $0$": if it did, the program would have the model $L=0$ on $\eta_0$, and that is exactly the wrong answer.

The reference machine of Chapter 5 behaves accordingly: it publishes all of $Z$ and $Y$, then takes the rule UNDEFINED at $(s4,())$ and ends in an explicit failure. That failure is a defined outcome, not a crash.

**Why this matters for an agentic coder.** The example fixes a test pair. A correct implementation must return $(0,4)$ and $\log 4$ on $\eta_1$ and must *fail visibly* on $\eta_0$. An implementation that returns $L=0$, `nan` that nobody checks, or any silently produced number on $\eta_0$ has the wrong semantics, even if it is accurate on $\eta_1$. Every later chapter returns to these two inputs.

## 5. The six questions a semantics must answer

A semantics for TL answers six questions. Each has a tempting answer that is wrong in a way the running example exhibits. The table is a map of the course.

| # | Question | Naive answer and why it is wrong | Chapter |
| --- | --- | --- | --- |
| Q1 | What are values, and what do index expressions do? | "Tensors are arrays, and indices are loop counters matched by name or by extent." Wrong: axis identity is by the variable, not the spelling or the size; a read and a write use the same affine notation for different jobs (a gather picks a source coordinate, a scatter picks a destination); and an out-of-range index is not silently zero or wrapped. | [Chapter 2](02-index-categories.md) |
| Q2 | What does a body mean when a primitive is undefined? | "Undefined is zero" (or `nan`, or an exception that propagates in whatever order the machine happens to evaluate). Wrong: $\bot$ is not a scalar, not zero, and not a missing entry; interpretation is strict, so $0\otimes\bot=\bot$, and failure must not depend on evaluation order. | [Chapter 3](03-partiality.md) |
| Q3 | How are several contributions to one coordinate combined? | "The last write wins." Wrong: a coordinate's value is the sum of its whole fibre, and duplicate statements are distinct summands. | [Chapter 4](04-denotational.md) |
| Q4 | What does a whole program mean, including cyclic programs? | "Iterate the equations to a fixed point" (or "take the least one"). Wrong: there is no order on $\bot$ and no least fixed point; a model is *any* fixed point extending the inputs, and the denotation exists only when the model is unique. | [Chapter 4](04-denotational.md) |
| Q5 | How is it computed, and when does computation agree with meaning? | "Run the statements in text order." Wrong: the order of statements is not the order of execution. An occurrence may run (CONTRIBUTE) once everything it reads is published and its body is defined, in any order relative to the other writers of its destination; an address is published (PUBLISH) only after every occurrence addressed to it has contributed. A successful run always yields the unique model, but "success if and only if a unique model exists" needs a rank certificate. | [Chapter 5](05-operational.md) |
| Q6 | When is a compiled program correct? | "It matches the reference on some test inputs." Wrong: a compiled plan must refine the machine, including failing runs, and buffer reuse must not change which logical value is read. | [Chapter 7](07-outlook.md) |

We spell out how the running example refutes each naive answer.

**Q1.** In `Z[j] = W[j,i] X[i]` the symbol `i` occurs in two slots and is one variable, which is why it is contracted. Two variables with the same extent are still two variables. Chapter 2 models coordinate sets as objects of $\mathbf{FinSet}$ and reads and writes as functions between them.

**Q2.** On $\eta_0$ the body of s4 is $\log0$. If undefined were zero, `Scorer` would report $L=0$, and a downstream consumer could not distinguish "the score is zero" from "the score does not exist". Chapter 3 models bodies as partial maps, that is, as the Kleisli category of the option monad (see [Chapter 0, Section 4](00-prerequisites.md#4-monads-and-kleisli-categories)), and shows why strict pairing is the right product.

**Q3.** If the last write won, then with $\eta_1$ the program would store $Z=B=(1,0)$ and $Y=(1,0)$, and then $L=\log Y[1]=\log0$ would fail, although the intended model $L=\log4$ exists. Last-write-wins changes the answer, not merely the style. Chapter 4 defines
$$\mathrm{Collect}_P(\rho)(T)[p]=\bigoplus_{o\in\mathcal{C}_P(T,p)}[\![E_s]\!]_{\rho,\nu},$$
and an empty fibre gives $0_K$.

**Q4.** `Scorer` is acyclic, but the specification (Section 21.4) shows what happens without that luck. The program `T[] = X[]; T[] = 2 T[]` has collected equation $T=X+2T$. Its unique model is $T=-X$, yet the iteration $T_{n+1}=X+2T_n$ diverges from $T_0=0$ whenever $X\ne0$. The program `T[] = T[]` has *every* real value as a model, and `T[] = T[] + 1` has none. A semantics that picks "the" fixed point cannot tell these three apart. Chapter 4 takes the set of all fixed points, as an equalizer, and the denotation is a span ([Chapter 0](00-prerequisites.md), Sections 7 and 6).

**Q5.** In `Scorer` the textual order s1, s2, s3, s4 happens to work. Move s3 first and an executor that obeys text order reads $Z$ before it is complete. The right notion is a machine with three rules, CONTRIBUTE, PUBLISH and UNDEFINED, that fire when their premises hold in any order they allow (Chapter 5). For instance $(s1,j{=}0)$ and $(s2,j{=}0)$ may contribute to $(Z,0)$ in either order, and only PUBLISH waits for both. On $\eta_1$ a maximal run has seven CONTRIBUTE steps (one per occurrence) and five PUBLISH steps (one per defined address). The comparison with models needs a rank certificate: here $r=0$ on every input address, $r(Z,j)=1$, $r(Y,j)=2$, $r(L,())=3$.

**Q6.** A compiled `Scorer` can be right on $\eta_1$ and wrong on $\eta_0$, for instance by returning a number there. Chapter 7 describes what is and is not proved about refinement.

**Why this matters for an agentic coder.** The six questions are a checklist for review. Before trusting generated code, ask which of Q1 to Q6 it silently answered with a naive default.

## 6. Scope of the semantics

The specification is deliberately narrow. These are the assumptions (overview, "Semantic scope").

- **Finite domains.** Every index range is a finite $[n]$, including finite scan histories. Zero extents are allowed and not excluded. A tabulation over $[0]$ is the empty array, a reduction over $[0]$ is $0_K$ and evaluates no body, and a statement with an empty range has no occurrences.
- **Exact scalars.** $K$ is a fixed algebra, here $\mathbb{R}$ with exact values. Floating-point values are not the semantics; they are an implementation that has to be related to it.
- **Explicit primitive domains.** Each primitive carries its domain $\mathcal{D}_f$. Outside it the application is undefined. A primitive has no hidden reads and no side effects.
- **Declared roles.** Tensors are inputs ($\mathrm{In}$) or defined ($\mathrm{Def}$), and these are disjoint; outputs form a subset $\mathrm{Out}\subseteq\mathrm{Def}$. Declaring an input does not supply its values; an input environment $\eta$ must. A supplied input is not a contribution. A defined tensor with no writers is the empty sum, $0$ everywhere on its declared domain. Designated outputs are whole tensors: if a history $H$ is an output, every time slice is returned.

Three things are outside the fragment.

- **Floating point.** Reduction order, rounding and machine representations are not specified. The semantics does not replace the carrier by floats.
- **Out-of-range access.** A read or write of an index outside the declared shape is neither a read nor a write of an in-bounds coordinate. The structural rules reject such a statement (a write outside the shape is an ill-formed statement, not a dropped contribution). A surface profile can give such a read a meaning, such as a zero extension, as a separate and explicit extension.
- **Cyclic solvers.** Cyclic programs are well formed and have a denotation when their model is unique (Section 21.4, Q4 above). But the reference machine does not select a solution of a cyclic system. Not every structurally valid program has an execution strategy, and having a unique model is different from being executable.

**Why this matters for an agentic coder.** The scope list is a list of things an agent must not claim. "The compiled code matches the semantics" can only be said within the stated fragment, with a stated carrier, a stated primitive domain, and in-range accesses. Outside it, say so rather than hope.

## Exercises

1. **Elaborate.** Elaborate each surface statement to core, giving $\Gamma_s$ and the contracted set of each term. (a) `Y[i] = A[i,j] B[j,k] V[k] + C[i]`. (b) `U[a] = relu(M[a,b] N[b] + 2 P[a])`. State where each reduction binder sits and which free variables remain in the body.

2. **List the occurrences.** For $T$ and $X$ of shape $(2)$, $S$ of shape $(3)$, and the program
```text
s1: T[i]   = X[i]       # i in [2]
s2: T[i]   = X[i]       # i in [2]
s3: S[i+1] = X[i]       # i in [2]
s4: T[0]   = 5
```
list $\mathcal{O}_P$ with destinations, and write down every nonempty fibre. Which coordinates of $T$ and $S$ have empty fibres? Then state $\mathrm{Collect}$ at each coordinate in terms of $X$.

3. **Collected values by hand.** For `Scorer` with the same $W$ and $B$ but $X=(2,1)$, compute the contribution of each of the seven occurrences, then $Z$, $Y$ and $L$. Which occurrence bodies are evaluated?

4. **Guard versus Iverson.** Let $X=(1,\,e,\,-7)$ with $i\in[3]$. (a) Compare `F[i] = log(X[i]) where i < 2` with `F[i] = 1_{i<2} log(X[i])`. State $D_s$ for each and say which has a value on this input and why. (b) Give an input vector on which the second program does have a value.

5. **Boundary fibres.** Let $C$ have shape $(3)$, $R$ shape $(2)$, and $T$ shape $(2,3)$ with the statements of Example 1.2 restricted to these shapes. Write $\phi_1$ and $\phi_2$, list all five occurrences, and write the fibre of each of the six coordinates of $T$. Which fibres are empty, which have one member, and which two? Check Proposition 1.9.

6. **Lost binder.** Let $X=(3,-1,2)$ and $Y$ have shape $(1)$. Count the occurrences of `Y[i-i] = relu(X[i])` ($i\in[3]$) and compute $Y[0]$. Compare with `Pre[i-i] = X[i]; Y[0] = relu(Pre[0])`, which has the same $X$ and a defined `Pre` of shape $(1)$. Why do the answers differ, and which paragraph of Section 2 explains it?

7. $^*$ **Where does Scorer succeed?** With $W$ and $B$ fixed as in Section 4.4, find all $X=(x_0,x_1)\in\mathbb{R}^2$ for which every occurrence body of `Scorer`, evaluated on the collected values of $Z$ and $Y$, is defined. Show your answer is a half-plane in $x$ and say how it relates to $\eta_0$ and $\eta_1$. Does $Z[0]$ matter? Does the answer change if s2 is duplicated (a statement $s2'$ identical to s2)? What if $B=(1,1)$ and s2 is duplicated?

8. $^*$ **Scan by hand.** For Example 1.5 with $d=1$, $N=2$, $X[0]=2$, $Z[0]=3$, $F(h)[0]=2h[0]$: (a) elaborate the three statements to core, giving $\Gamma_s$ for each; (b) list all six occurrences with destinations and write the three fibres; (c) give $\mathrm{Read}$ of the occurrence $(s3,\,l{=}1)$; (d) compute the collected value of each of the three addresses and check $5,12,26$; (e) say what the statement set becomes for $N=0$ and what $H$ is then. Explain why it is wrong to decide from the printed names alone that the program has a cyclic dependency.

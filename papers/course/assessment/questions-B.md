# Assessment: question set B (transfer)

Instructions to the student. Answer using only these course notes
(`papers/course/*.md`, `papers/course/lean/MiniTensorLogic.lean`) and basic
category theory. Do not consult the specification under `papers/semantics/`
or any Lean module under `leanncd/`. Unlike set A, most of these questions
are about programs, rewrites and sorts that the notes do not discuss. Apply
the notes' constructions to them. Show your work, give numbers where asked,
and name the categorical construction or result from the notes that your
argument uses. Scalars are exact reals unless a question says otherwise.

**Q1. Colliding writes.** Consider

```text
inputs:  A[i]  i in [2];   B[j]  j in [3]
defined: Y[k]  k in [5]
Y[i+j] = A[i] B[j]
```

with $A=(1,2)$ and $B=(1,1,1)$.
(a) How many occurrences does the statement have, and what are the fibres
of the write map $\phi:[2]\times[3]\to[5]$? Is $\phi$ injective? Surjective?
(b) Compute $Y$ as a pushforward.
(c) Is any index contracted in this statement? Explain the difference
between this statement and a contraction in terms of where the sum comes
from.
(d) Use the transpose identity with the all-ones family on $[5]$ to check
your answer to (b) without recomputing any coordinate.

**Q2. A guard over two variables.** Let $M$ be a $3\times3$ real input and
compare

```text
G:  for i in [3], j in [3] where i < j:  S[] += log(M[i,j])
I:  for i in [3], j in [3]:              S[] += 1_{i<j} * log(M[i,j])
```

(a) How many occurrences does each program have?
(b) Suppose `log` is replaced by the identity, so both bodies are total.
Prove that the collected values of $S$ agree, writing the guard as a mono
$m:D\hookrightarrow[3]\times[3]$ and the Iverson factor as its indicator
$\chi_D$. Name the identity relating $m_!\,m^\ast v$ to $\chi_D$ and $v$, and
say which result in the notes it is the decategorified form of.
(c) With `log` restored, give a concrete $M$ for which $G$ has a model and
$I$ has none, and state the general relation between the two programs as
partial maps from inputs to outputs.

**Q3. Gather through a partial map.** $X$ is an input of extent 4. Compare

```text
P1:  Y[i] = recip(X[2i])            # i in [2]
P2:  R[k] = recip(X[k])             # k in [4]   (R is not an output)
     Y[i] = R[2i]                   # i in [2]
```

(a) For $X=(2,0,4,0)$ and for $X=(2,1,4,1)$, give the model set of each
program (or its output).
(b) Express both programs with the batching operation and a reindexing map
$r$, and state the relation between them in the definedness order. Which
hypothesis of the equality case fails?
(c) An agent proposes to rewrite P2 into P1 as "dead-code elimination,
since nothing reads `R[1]` or `R[3]`". Is the rewrite meaning-preserving?
What observable changes on the reference machine?

**Q4. Merging statements.** In `Scorer`, replace statements s1 and s2 by
the single statement

```text
s12: Z[j] = W[j,i] X[i] + B[j]
```

(a) Write its core form. Is the bias added once or once per $i$?
(b) Prove that the model set is unchanged for every input. Which law of
pushforward do you use, and why is the occurrence-relabeling law not
enough? Why is admissibility unchanged?
(c) Give the number of occurrences, the initial measure $\mu$ on
$\eta_1$, and the length of a successful maximal run, for the merged
program.
(d) Which observations differ between the original and merged programs
even though the models agree?
(e) Someone instead writes `Z[j] = W[j,i] (X[i] + B[j])`. Compute $Z$ on
$\eta_1$ and explain the difference.

**Q5. A cyclic equation with a partial primitive.**

```text
inputs:  X[]
defined: T[]   (output)
T[] = X[]
T[] = -1 * recip(T[])
```

(a) Write the collected equation and describe $\mathrm{Models}(P,X)$ for
every real $X$, giving the number of models.
(b) What is $\mathrm{AdmInput}(P)$ and what is $[\![P]\!]$ on it?
(c) Describe the witness span $\mathrm{Env}(\mathrm{In})\leftarrow W_P\to\mathrm{Env}(\mathrm{Out})$
concretely. Is its left leg monic? What is its image?
(d) What does the reference machine do for $X=1$, $X=2$ and $X=3$? For
$X=1$, explain why the run does not end in a failed configuration even
though there is no model.

**Q6. A private free tensor.**

```text
P:  inputs x[];  defined h[], y[];  outputs y
    h[] = h[]
    y[] = x[]
Q:  inputs y[];  defined z[];  outputs z
    z[] = recip(y[])
```

(a) Describe $\mathrm{Models}(P,x)$, the span $W_P$, and the relation
$\{(\ell(w),r(w))\}\subseteq\mathrm{Env}(\mathrm{In})\times\mathrm{Env}(\mathrm{Out})$
it determines. Is that relation a function? Is $[\![P]\!]$ defined anywhere?
(b) Compute the apex of the composite span for $P$ then $Q$, and say what
$[\![P;Q]\!]$ is.
(c) What does the reference machine do on $P$?
(d) Let $P'$ be $P$ with the tensor $h$ and its statement deleted. Compare
the spans of $P$ and $P'$ up to span isomorphism, and compare their
output relations. What does this show about the notes' choice of
equivalence for program meanings?

**Q7. A boundary program on the machine.**

```text
inputs:  C[c] c in [2];  R[r] r in [2]
defined: T[r,c] r in [2], c in [2];  S[]   (output S)
b1:  T[0,c] = C[c]
b2:  T[r,0] = R[r]
b3:  S[]    = T[r,c] T[r,c]          # r and c contracted
```

with $C=(2,3)$ and $R=(7,5)$.
(a) List the occurrences and the fibre of every defined address. Compute
$T$ and $S$.
(b) Give the initial measure $\mu$, the number of CONTRIBUTE and PUBLISH
steps in a successful maximal run, and the earliest step at which some
address can be published.
(c) After consuming only $(b1,c{=}0)$, what is $\alpha(T,(0,0))$ and is the
occurrence of $b3$ ready?
(d) Give a rank certificate.
(e) An implementation initializes the storage of $T$ to zeros and lets
$b3$ read it at any time. What can it output for $S$, and which premise of
which machine rule does it violate?

**Q8. Other sorts.**
(a) Over the max-plus semiring $(\mathbb{R}\cup\{-\infty\},\max,+,-\infty,0)$,
take $f:[3]\to[2]$ with $f(0)=0$, $f(1)=1$, $f(2)=0$, $v=(5,7,11)$ and
$w=(2,3)$. Compute $f_!v$, $f^\ast w$ and both sides of the transpose
identity.
(b) Over max-plus, does deleting one of two identical statements preserve
the model set? Over $(\mathbb{R},+,\times)$? Explain in terms of collection.
(c)$^\ast$ Let $K$ be idempotent ($a\oplus a=a$) and order it by
$a\le b\iff a\oplus b=b$. Prove that for every $f:I\to J$,
$f_!u\le w\iff u\le f^\ast w$ (pointwise order). Say what this is in
categorical terms, identify $f_!$ and $f^\ast$ concretely for the Boolean
sort, and relate the result to Theorem 2.4 of the notes. Does the same hold
over $(\mathbb{R},+,\times)$?

**Q9. A broken rule.** A colleague proposes to replace PUBLISH and
UNDEFINED by one rule:

> LENIENT-PUBLISH: if $a$ is unpublished and every pending occurrence
> targeting $a$ is ready, add to $\alpha(a)$ the values of those whose
> bodies are defined, remove all of them from $U$, and publish $a$.

(a) Run the modified machine on `Scorer` with input $\eta_0$. What does it
return?
(b) Which theorem of the notes fails for the modified machine, and which
step of its proof breaks? Does the theorem still hold on inputs that have
a model? Why?
(c) Which non-negotiable fact of the semantics does the rule violate,
stated in one sentence?

**Q10. Extending the Lean companion.** Add an Iverson constructor to the
mini development's `Expr`:

```lean
| iverson {Γ : Type} (q : Γ → Bool) : Expr d K Γ
```

(a) Write the new clauses of `evalWith` and `footprint`.
(b) Prove, as you would on paper from the definitions, that for every
`e`, store `σ` and `γ` with `q γ = false`,
`evalWith σ (.mul (.iverson q) e) γ = none ↔ evalWith σ e γ = none`.
What semantic point does this lemma formalize?
(c) How does the mini development express a guard, and why is no new
constructor needed for it?

# Assessment: question set A

Instructions to the student. Answer using only these course notes
(`papers/course/*.md`, `papers/course/lean/MiniTensorLogic.lean`) and basic
category theory (categories, functors, natural transformations). Do not
consult the specification under `papers/semantics/` or any Lean module under
`leanncd/`. Show your work. Where a question asks for a number, give the
number. Where it asks "why", give the categorical reason named in the notes.

## Part I. Index geometry (Chapter 2)

**Q1.** Let $f:[3]\to[2]$ be $f(0)=0$, $f(1)=1$, $f(2)=0$ and let
$v=(5,7,11)\in\mathbb{Z}^{[3]}$ and $w=(2,3)\in\mathbb{Z}^{[2]}$.
Compute $f_!v$, $f^\ast w$, and verify the transpose identity
$\langle f_!v,w\rangle_{[2]}=\langle v,f^\ast w\rangle_{[3]}$ numerically.

**Q2.** For a function $f:I\to J$ between finite sets regarded as discrete
categories, state what $\mathrm{Lan}_f A$ and $\mathrm{Ran}_f A$ are for a
family $A:I\to\mathbf{Set}$, and explain in one paragraph why these are
the left and right adjoints of restriction $f^\ast$. Which of the two
decategorifies to tensor contraction (summing over an index), and what
structure on $K$ does that decategorification need?

**Q3.** Write the surface statement `Y[i,k] = A[i,j] B[j,k]` with
$i\in[2],j\in[3],k\in[2]$ as a weighted span (or spans) of finite sets, name
the apex and the three projections, and state the pushforward/pullback
formula for $Y$. In which category is "composition of two contractions is
matrix multiplication" a statement about composition of morphisms?

**Q4.** The program has two statements `T[0i] = 1` for $i\in[3]$ and
`T[0] = 1` (one statement, no binders), both writing the scalar-indexed
coordinate $T[0]$ of a tensor of extent 1. How many occurrences target
$(T,0)$, what is the collected value over $\mathbb{R}$, and which
categorical construction (name it) makes the two statements' occurrences
distinct even though their bodies and destinations coincide?

## Part II. Partiality (Chapter 3)

**Q5.** Over exact reals, give the value in $\mathrm{Result}(\mathbb{R})$ of
each of: (a) $0\otimes\log(-1)$; (b) $\bigoplus_{j\in[0]}\log(-1)$;
(c) $\mathrm{at}(\mathrm{tab}_{j\in[2]}(\log X[j]),(0))$ with $X=(4,-1)$;
(d) the guarded statement body at the only occurrence of
`for i in [2] where i<1: Y[i] += log(X[i])` with $X=(4,-1)$;
(e) the body at $i=1$ of `for i in [2]: Y[i] += 1_{i<1} log(X[i])` with the
same $X$. One sentence of justification each.

**Q6.** State the lax naturality property of batching a partial map
$f:A\rightharpoonup B$ over finite index sets along $r:I\to J$ (give the
inequality, say what order it is in, and the two sufficient conditions
for equality). Give the reciprocal counterexample from the notes. Then say
which optimisation a compiler might be tempted to make that this property
forbids.

**Q7.** Why is strict pairing in $\mathbf{Pfn}$ not a categorical product?
Give the failing law and a two-line counterexample. What does this say
about discarding an unused intermediate result?

## Part III. Denotational semantics (Chapter 4)

**Q8.** For the running example `Scorer` on the primary input $\eta_1$,
compute $\mathrm{Collect}_P(\rho)$ for $Z$, $Y$, $L$ at the claimed model
$\rho$ and verify it is a fixed point of $\Phi_P$. List the fibre of
$(Z,1)$. Then explain in two sentences why on the input $\eta_0$
($X=(0,0)$) the model set is empty although every environment with
$Y[1]>0$ is admissible.

**Q9.** Describe $\mathrm{Models}(P,\eta)$ as an equalizer (say of which
two maps, between which objects, and how $\eta$ enters). Why does the
semantics take all fixed points rather than a least one? For the program
`T[] = X[]; T[] = 2 T[]` with input $X=3$, compute the model set.

**Q10.** Define the witness span of a program. Suppose $P$ has outputs
exactly the inputs of $Q$. What is the apex of the composite span, and what
does it have to do with models of the glued program? Under what hypothesis
on $P$ and $Q$ does the composite denotation become a composite of partial
functions, and why does model existence still not compose?

## Part IV. Operational semantics (Chapter 5)

**Q11.** Give the three machine rules in words, and for each say what it
requires of the configuration. Then take the program of Section 27.1 of
the notes' worked examples (`Pre[] = A[]; Pre[] = B[]; T[] = relu(Pre[])`
with $A=1$, $B=-1$): after consuming only the first contribution, what are
$\alpha(\mathrm{Pre})$ and $\mathrm{dom}\,\sigma$, is the contribution to
$T$ ready, and why does the answer not depend on which contribution was
consumed first?

**Q12.** State Theorem 26.3 of the specification as the notes present it
(success gives the unique model; failure excludes models) and say why it
needs no rank certificate. Then state the correspondence theorem for the
ranked fragment and explain, using the program `T[] = T[]`, why the ranked
hypothesis cannot be dropped.

**Q13.** What is a rank certificate, and in what precise sense is it a lax
morphism of coalgebras? Give the rank certificate for the running example
and for the finite history $H$ with $N=2$, and give the measure $\mu$ of
the running example's initial configuration on $\eta_1$.

**Q14.** Explain the difference between a blocked configuration and a
failed one, and give one program that blocks with no model, one that
blocks with a unique model, and one that blocks with many models.

## Part V. Lean (Chapter 6 and the Lean file)

**Q15.** Fill in the dictionary: for each of pullback, pushforward,
occurrences-as-coproduct, Kleisli interpretation, the equation operator,
the model relation, the step relation, and the termination measure, name
the corresponding definition in `lean/MiniTensorLogic.lean` and, where the
notes give it, in the production `LeanNCD.Semantics` modules.

**Q16.** In `MiniTensorLogic.lean`, why is the running example's last
statement written with a reciprocal instead of a logarithm, and what
property of the two primitives makes the substitution faithful to the
notes' failing input $\eta_0$?

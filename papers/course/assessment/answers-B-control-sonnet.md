# Answers to question set B (control run, no notes)

## Q1

(a) The index context is Γ = {i, j}, with i in [2] and j in [3]. Both variables occur on the left-hand side, so there are 2·3 = 6 occurrences. The write map is φ(i,j) = i+j. Its fibres are:

| coordinate k | fibre φ⁻¹(k) |
|---|---|
| 0 | {(0,0)} |
| 1 | {(0,1),(1,0)} |
| 2 | {(0,2),(1,1)} |
| 3 | {(1,2)} |
| 4 | ∅ |

φ is not injective, because fibres 1 and 2 have size 2. It is not surjective, because coordinate 4 has an empty fibre (max i+j = 3).

(b) Y = φ_!(A⊗B), where (A⊗B)(i,j) = A_i B_j, and (φ_!u)(k) = Σ_{φ(i,j)=k} u(i,j).
- Y0 = 1·1 = 1
- Y1 = A0B1 + A1B0 = 1+2 = 3
- Y2 = A0B2 + A1B1 = 1+2 = 3
- Y3 = A1B2 = 2
- Y4 = 0 (empty fibre, so the empty sum)

So Y = (1,3,3,2,0). This is the polynomial product (1+2x)(1+x+x²) = 1+3x+3x²+2x³, that is, a convolution.

(c) No index is contracted. Contraction applies to variables that occur only on the right-hand side, and both i and j occur in the target address i+j. In a contraction the sum happens inside one occurrence, as a `reduce` in the body. Here the sum happens across occurrences: several occurrences are addressed to the same coordinate and the collection step adds them. This is the contribute-style semantics, not a contraction.

(d) The transpose identity is ⟨φ_!v, w⟩ = ⟨v, φ^*w⟩. Take w = 1 (all ones on [5]). Then φ^*1 = 1 on [2]×[3], so Σ_k Y_k = Σ_{i,j} A_iB_j = (ΣA)(ΣB) = 3·3 = 9. Direct check: 1+3+3+2+0 = 9. ✓

## Q2

(a) G has 3 occurrences, the valuations with i<j: (0,1), (0,2), (1,2). I has 9 occurrences, one per valuation.

(b) Let D = {(i,j) | i<j} and m: D ↪ [3]×[3]. Let v(i,j) = M[i,j], which is total once log is the identity. G collects S = Σ_{x∈D} v(x) = π_! m^* v, where π is the map to the one-point set. I collects S = Σ_x χ_D(x)·v(x) = π_!(χ_D · v).

The identity is m_! m^* v = χ_D · v (extension by zero of the restriction equals multiplication by the indicator). It is the projection formula, also called Frobenius reciprocity: m_!(m^*v · 1) = v · m_!1, with m_!1 = χ_D. Applying π_! to both sides, and using π_!m_! = (πm)_!, gives that G and I agree. I believe this is the decategorified form of the Frobenius law / Beck–Chevalley condition for pullback of a mono. I do not know the notes' name for it. I am guessing that it is their "guard = pullback along a mono" statement.

(c) Take M with all entries 1 except M[1,0] = 0, which is below the diagonal. G never reads M[1,0] and gives S = 3·log 1 = 0, so G has a model. I has an occurrence at (1,0) with body 1_{false}·log(0). The body is strict, so 0·undefined = undefined, and I has no model.

General relation: dom(I) ⊆ dom(G), and on dom(I) the two outputs are equal. As partial maps, ⟦I⟧ ⊑ ⟦G⟧ in the definedness (extension) order. The guard is strictly more defined, because it removes occurrences while the Iverson factor keeps them.

## Q3

(a) P1 reads only X[0] and X[2].
- X=(2,0,4,0): P1 has the unique model Y=(1/2, 1/4).
- X=(2,1,4,1): Y=(1/2, 1/4).

P2 has an occurrence for every k in [4]. For X=(2,0,4,0), the occurrence at k=1 has body recip(0), which is undefined. Every occurrence body must be defined in a model, so P2 has no model and its output is undefined. For X=(2,1,4,1), the unique model has R=(1/2,1,1/4,1) and Y=(1/2,1/4).

(b) Let r:[2]→[4], r(i)=2i. P2 is r^*(batch(recip) X), and P1 is batch(recip)(r^* X). Batching lifts the partial primitive pointwise over the axis. The relation is P2 ⊑ P1 in the definedness order. Where P2 is defined, P1 is defined with the same value. P1 can be defined where P2 is not, as at X=(2,0,4,0).

The equality case needs r to be surjective (every coordinate that is batch-evaluated must also be read). Here r is not surjective, since its image is {0,2}, so the hypothesis fails. Reindexing commutes with a pointwise function as total functions, but not with its domain of definedness.

(c) The rewrite is not meaning-preserving. The code is dead as to value, but it is not dead as to definedness, because strictness makes R[1] and R[3] matter. On X=(2,0,4,0) the reference machine on P2 reaches the occurrence R[1] = recip(X[1]) with an undefined body. UNDEFINED fires and the run ends failed, with no result. After the rewrite, the run succeeds with Y=(1/2,1/4). So the observable change is failure becoming success, and the program has become strictly more defined. Such a rewrite is only valid when the removed code is total.

## Q4

(a) I read the notes' rule as contracting per term (each term closes over its own right-hand-side-only variables). Core form: Z[j] = (reduce_i W[j,i]·X[i]) + B[j]. The bias is added once, not once per i, because i is bound inside the reduce of the first term and B[j] does not mention i.

(b) The original has occurrences s1(j) and s2(j), contributing a_j = Σ_i W[j,i]X[i] and b_j = B[j] to Z[j]. The merged program has one occurrence per j with body a_j + b_j. The collected value is the same, since Z[j] = a_j + b_j in both. The law used is additivity (linearity) of pushforward over coproducts of occurrence sets, φ_!(u+v) = φ_!u + φ_!v, together with the way ⊕ in the body is strict, so the merged body is defined iff both a_j and b_j are. This matches the original, where every occurrence must be defined. Occurrence relabeling (reindexing along a bijection of the occurrence sets) is not enough: the occurrence sets have different cardinalities (4 versus 2), so there is no bijection. We are fusing two occurrences into one.

Admissibility is unchanged. The dependency graph is the same: Z[j] reads X, W and B either way, and any rank certificate for the original works for the merged program.

(c) The merged program has 2 (Z) + 2 (Y) + 1 (L) = 5 occurrences. The defined addresses are Z[0], Z[1], Y[0], Y[1] and L[], so 5 unpublished. The initial measure is μ = 5 + 5 = 10. A successful maximal run has 5 CONTRIBUTE steps and 5 PUBLISH steps, so length 10. (The original has 7 occurrences, μ = 12, and 12 steps.) On η1: Z=(0,4), Y=(0,4), L=log 4, all defined.

(d) The following differ, even though the models agree:
- the occurrence count (7 versus 5);
- the measure and the run length (12 versus 10);
- the accumulator states along a run (the original has an intermediate α(Z[j]) holding only the product term, or only B[j]; the merged one has none);
- the scheduling freedom (the original has two independent occurrences per Z[j]);
- the failure point when exactly one of the two summands would be undefined. The original consumes the defined one first, and the merged program fails with nothing consumed.

(e) For `Z[j] = W[j,i] (X[i] + B[j])`, there is a single term, and i is contracted over the whole product: Z[j] = Σ_i W[j,i](X[i]+B[j]).
- j=0: 1·(1+1) + 1·(−2+1) = 2 − 1 = 1.
- j=1: 2·(1+0) + (−1)(−2+0) = 2 + 2 = 4.

So Z = (1,4), against (0,4) for the original. Here the bias is distributed through the contraction, so Z[j] = (WX)[j] + B[j]·Σ_i W[j,i]. For j=0, WX = 1−2 = −1 and the row sum is 2, so Z[0] = −1 + 1·2 = 1 (the original gives −1 + 1 = 0). For j=1, B[1] = 0, so there is no difference. The original adds the bias once; this version adds it once per i, weighted by W.

## Q5

(a) The collected equation is T = X + (−1)·recip(T). Because bodies are strict, the second occurrence is defined only if T ≠ 0. A model is a real T ≠ 0 with T = X − 1/T, that is, T² − XT + 1 = 0 (T=0 is never a root). The discriminant is X² − 4. Number of models:
- 2 if |X| > 2: T = (X ± √(X²−4))/2;
- 1 if |X| = 2: T = X/2 = ±1;
- 0 if |X| < 2.

(b) AdmInput(P) = {X : exactly one model} = {2, −2}. ⟦P⟧(2) = 1 and ⟦P⟧(−2) = −1.

(c) The witness span is W_P = {(X,T) | T ≠ 0, T² − XT + 1 = 0} ≅ ℝ∖{0}, parametrised by T. The left leg is T ↦ X = T + 1/T and the right leg is T ↦ T. The left leg is not monic, since T and 1/T have the same X (for example T=2 and T=1/2 both give X=5/2). Its image is {X : |X| ≥ 2} = (−∞,−2] ∪ [2,∞). The program has a model exactly on that set, and a unique model exactly on the points where the leg is injective locally, namely X = ±2.

(d) The statements are o1: T = X and o2: T = −1·recip(T). For all three inputs the machine does the same thing. CONTRIBUTE o1 (α(T) = X). o2 reads T, which is unpublished, so o2 is not ready. PUBLISH T needs every pending occurrence targeting T to be consumed, and o2 is still pending. UNDEFINED needs a ready occurrence with an undefined body, and o2 is not ready. No rule applies: the machine is stuck. There is no rank certificate (r(T) > r(T) is impossible), so the program is not admissible, and the machine cannot compute anything.
- X=1: no model, and the run is stuck, not failed.
- X=2: there is a model (T=1), but the machine is stuck anyway. The machine is incomplete for cyclic programs.
- X=3: two models, also stuck.

For X=1 the run does not end in a failed configuration because failure is produced only by UNDEFINED, which needs a ready occurrence whose body is undefined. Here o2 never becomes ready, so its body is never evaluated. A "failed" run is evidence that there is no model; a stuck run says nothing about models, since the machine only decides admissible programs.

## Q6

(a) Models(P,x) = {(x, h, y=x) : h ∈ ℝ}. The statement h = h reads h = h + (empty), so any h satisfies it, and y = x. The span is W_P ≅ ℝ_x × ℝ_h with ℓ(x,h) = x and r(x,h) = y = x. The relation {(ℓ(w), r(w))} is the graph of the identity {(x,x)}, so as a relation it is a function (the identity). But ⟦P⟧ is defined nowhere, since every input has a continuum of models (not exactly one).

(b) W_Q = {(y,z) : y ≠ 0, z = 1/y}. The composite span is the pullback over Env(y): the apex is {(x,h,y,z) : y = x, z = 1/y, y ≠ 0} ≅ {(x,h) : x ≠ 0} = (ℝ∖{0}) × ℝ. The output relation is {(x, 1/x) : x ≠ 0}. ⟦P;Q⟧ is undefined everywhere: h is still free, so there is never exactly one model.

(c) The machine on P: CONTRIBUTE y = x, PUBLISH y. The occurrence for h reads h, which is unpublished, so it is not ready. No rule applies, and the run is stuck. There is no rank certificate (r(h) > r(h) is impossible), so P is not admissible.

(d) P′ has apex ℝ_x, with ℓ the identity and r the identity. The spans of P and P′ are not isomorphic: the apexes ℝ² and ℝ differ, and the left leg of P is not monic. The output relations are equal, both being the identity graph. Yet ⟦P′⟧ = id is total while ⟦P⟧ is nowhere defined. So the notes choose equivalence of program meaning as span isomorphism, which is finer than equality of relations. It keeps the witness (private, hidden, underdetermined tensors), and the relation alone would wrongly identify P and P′.

## Q7

(a) The occurrences are:
- b1(c=0), addressed to T[0,0], body C[0];
- b1(c=1), addressed to T[0,1], body C[1];
- b2(r=0), addressed to T[0,0], body R[0];
- b2(r=1), addressed to T[1,0], body R[1];
- b3, addressed to S[], one occurrence, with r and c contracted inside the body.

That is 5 occurrences. Fibres:

| address | fibre |
|---|---|
| T[0,0] | {b1(0), b2(0)} |
| T[0,1] | {b1(1)} |
| T[1,0] | {b2(1)} |
| T[1,1] | ∅ |
| S[] | {b3} |

Values: T[0,0] = 2+7 = 9, T[0,1] = 3, T[1,0] = 5, T[1,1] = 0 (empty sum). S = 81+9+25+0 = 115.

(b) μ = |U| + unpublished defined addresses = 5 + 5 = 10. A successful maximal run has 5 CONTRIBUTE and 5 PUBLISH steps (10 steps). The earliest address that can be published is T[1,1], at step 1, since its fibre is empty and there is nothing pending to consume.

(c) After consuming only b1(c=0), α(T,(0,0)) = C[0] = 2. The occurrence of b3 is not ready: it reads all of T, and none of T is published (readiness needs the footprint inside the published store). Here b2(r=0) still has to be consumed, and the address has to be published.

(d) A rank certificate: r = 0 on inputs, r(T[r,c]) = 1 for all four cells, and r(S) = 2. T reads only inputs (rank 0 < 1) and S reads T (1 < 2).

(e) With T zero-initialised and read at any time, S can be any Σ of squares of partial states: T[0,0] ∈ {0,2,7,9}, T[0,1] ∈ {0,3}, T[1,0] ∈ {0,5}, T[1,1] = 0. For example S = 0 if b3 runs first, or 115 if it runs last. The machine only guarantees S = 115. The implementation violates the readiness premise of CONTRIBUTE: the occurrence's footprint must lie in the published store σ, and the address is published only when its entire fibre has been consumed. A zero-initialised store reads unpublished, incomplete accumulators.

## Q8

(a) Over max-plus, f_!v(j) = max over {i : f(i) = j} of v_i. f_!v = (max(5,11), 7) = (11, 7). f^*w = w∘f = (w0, w1, w0) = (2, 3, 2). The pairing is ⟨a,b⟩ = max_j (a_j + b_j).
- LHS ⟨f_!v, w⟩ = max(11+2, 7+3) = 13.
- RHS ⟨v, f^*w⟩ = max(5+2, 7+3, 11+2) = 13.

They are equal. ✓

(b) Over max-plus, deleting one of two identical statements preserves the model set, because collection is ⊕ = max, which is idempotent: a ⊕ a = a. Definedness is also unchanged, because the two bodies are identical. Over (ℝ,+,×) it does not preserve it: the duplicate contributes twice, so the collected value is 2a instead of a, and the models differ except where a = 0. Collection counts multiplicity of occurrences in a non-idempotent sort and does not in an idempotent one.

(c) Proof. In the idempotent K, ⊕ is the join for the order a ≤ b ⟺ a ⊕ b = b: it is the least upper bound. So f_!u ≤ w ⟺ for every j, ⊕_{f(i)=j} u_i ≤ w_j ⟺ for every j and every i with f(i) = j, u_i ≤ w_j (a join is below w_j iff each part is) ⟺ for every i, u_i ≤ w_{f(i)} = (f^*w)_i ⟺ u ≤ f^*w. ∎

In categorical terms, this is an adjunction f_! ⊣ f^* between the posets K^I and K^J, that is, a Galois connection. For the Boolean sort (K = {0,1}, ∨, ∧), f_! is the direct image of subsets (U ↦ f(U), the existential quantifier ∃_f) and f^* is the preimage (W ↦ f⁻¹(W)), and the statement is f(U) ⊆ W ⟺ U ⊆ f⁻¹(W).

Relation to Theorem 2.4: I guessed that Theorem 2.4 is the transpose identity ⟨f_!v, w⟩ = ⟨v, f^*w⟩, which makes f_! and f^* adjoint with respect to the bilinear pairing. In the idempotent case this is the order-theoretic shadow of it, where the pairing adjunction is replaced by the poset adjunction. Over (ℝ,+,×) it does not hold: ⊕ = + is not idempotent, and the order a ⊕ b = b would force a = 0. With the usual order on ℝ it fails: I = {0,1}, J = {0}, u = (1,1), w = (1) gives f_!u = 2 > 1 = w, but u ≤ f^*w = (1,1). The transpose identity still holds there, as a bilinear identity, not as an order adjunction.

## Q9

(a) On η0: Z[0] = 0+1 = 1 and Z[1] = 0+0 = 0, so Y = (1, 0). The occurrence of s4 is ready once Y[1] is published, but its body is log(0), which is undefined. The standard machine fires UNDEFINED and fails (there is no model). The modified machine fires LENIENT-PUBLISH on L: the only pending occurrence targeting L is ready, none of the bodies is defined, so α(L) stays 0, the occurrence is removed, and L is published as 0. The run succeeds and returns Y = (1,0), L = 0. This is wrong, because there is no model.

(b) The soundness theorem fails: a successful run ends in a model (the final published store is a model of the program). The step that breaks is the invariant behind it: every consumed occurrence had a defined body, and α(a) is the sum of all contributions to a. LENIENT-PUBLISH discards occurrences with undefined bodies without recording failure. So at the end "U empty" no longer implies that every occurrence body is defined, and the final store is not a model.

On inputs that have a model, the theorem still holds. By induction on rank, the machine's published values agree with any model (every address value is the sum of the contributions in the model). In that model every occurrence body is defined, so the machine's store gives defined bodies at every ready occurrence. Hence the "whose bodies are defined" filter drops nothing, and LENIENT-PUBLISH behaves exactly like PUBLISH.

(c) An undefined body is not a skipped or zero contribution: strictness means any occurrence whose body is undefined makes the whole program have no model, and the machine must fail instead of publishing.

## Q10

(a) The new clauses assume that K has `0` and `1` (the semiring structure), as the other constructors presumably do.

```lean
-- in evalWith (σ fixed), matching on the expression:
| .iverson q, γ => some (if q γ then 1 else 0)

-- in footprint:
| .iverson _, _ => []          -- reads no address
```

(If `footprint` takes no valuation, the clause is `| .iverson _ => []`.) The Iverson factor is total and reads nothing.

(b) With `evalWith σ (.mul a b) γ = do let x ← evalWith σ a γ; let y ← evalWith σ b γ; pure (x * y)` (strict through two binds):

```lean
theorem iverson_false_none (σ) (e) (γ) (q : Γ → Bool) (hq : q γ = false) :
    evalWith σ (.mul (.iverson q) e) γ = none ↔ evalWith σ e γ = none := by
  simp only [evalWith, hq]          -- iverson evaluates to `some 0`
  cases h : evalWith σ e γ <;> simp [h]
```

On paper: since q γ = false, evalWith σ (.iverson q) γ = some 0. So the product is `do let y ← evalWith σ e γ; pure (0 * y)`. If `evalWith σ e γ = none`, the bind gives `none`. If it is `some y`, the result is `some (0*y)`, which is not `none`. So the product is `none` iff `e` is `none`.

The semantic point is that a false Iverson factor does not mask undefinedness. The product `0 * undefined` is still undefined, because bodies are strict. This is exactly the difference between the indicator and the guard in Q2.

(c) A guard is not part of the expression language. It is part of the statement, as a predicate on the index context (`Γ → Bool`), and it determines which valuations γ yield occurrences. The occurrence set is the filter of valuations with `q γ = true` (the mono D ↪ Γ), and bodies are evaluated only at those valuations. No new constructor is needed, because a guard removes occurrences instead of producing a body value, and so it never evaluates the body where the guard is false.

## What I had to guess

- Q2(b): the notes' name and number of the result that `m_! m^* v = χ_D · v` decategorifies. I said projection formula / Frobenius reciprocity / Beck–Chevalley.
- Q4(a): the notes' convention for what "term" means in the contraction rule. I assumed contraction is per additive term, so the bias is added once. Q4(e) is consistent with that reading. - Q5(d): the exact machine terminology (stuck versus failed) and whether the notes allow other terminal states. I assumed a stuck configuration is a non-failed dead end.
- Q7(d): whether ranks are assigned to inputs. I gave a certificate that works either way.
- Q8(c): what Theorem 2.4 of the notes says. I assumed it is the transpose / adjunction f_! ⊣ f^* identity.
- Q10: the exact signatures of `evalWith` and `footprint` (argument order, whether footprint depends on γ), and the exact shape of the guard in the mini development. I assumed a predicate in the statement and not in `Expr`.
- Q9(b): the name of the theorem (I assumed soundness / adequacy of the machine with respect to models) and the exact invariant in its proof.
- Q3(b): the name of the equality case (I assumed surjectivity of r), and "batching" as a pointwise lift along an axis.

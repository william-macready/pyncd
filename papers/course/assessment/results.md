# Assessment results: question set A

Date: 2026-11-15. Grader: the instructor, against `answer-key.md`.
Students: two agents that could read only `papers/course/` (minus the
answer key, the reviews, DESIGN and CONVENTIONS) and the Lean companion;
no access to the specification or the production Lean modules.

| Student | Model tier | Score (of 32) | Questions with a deduction |
| --- | --- | --- | --- |
| A | Sonnet 5.5 | 32 | none |
| B | Haiku 5.5 | 32 | none |

## Per-question notes

- Q1, Q13: both students produced the exact numbers (16, 7; 2, 3, 2; 53;
  ranks 0/1/2/3; μ = 12).
- Q2: both gave the discrete-fibre Kan extension computation and the
  hom-set bijection, named Lan = Σ as the contraction side, and stated the
  commutative-monoid requirement with the semiring needed only for products.
  Both repeated the course's honesty line (no adjunction on K-families).
- Q3: both chose Mat(K) via the linearization functor and gave the
  one-span and two-span presentations. Student A flagged that the notes did
  not say which category the slogan refers to; fixed (see below).
- Q4: both counted four occurrences and named the coproduct.
- Q5, Q6, Q7: both gave all five strictness verdicts, the lax inequality in
  the correct direction with both equality conditions and the (2,0)
  reciprocal example, and the failing projection law.
- Q8: both separated admissibility (Y[1] > 0) from the model equations
  (which force Y[1] = 0 on η0).
- Q9, Q10: both described the equalizer and its fibre over η, rejected the
  least fixed point for the right reason, and gave the gluing bijection and
  the non-compositionality example. Student A noted the ambiguous hypothesis
  statement in the composition proposition; fixed.
- Q11, Q12, Q14: both got the rules, readiness versus accumulators, the
  "no rank needed" direction, and the three blocking programs.
- Q15, Q16: both produced the dictionary from Chapter 6 and the
  reciprocal-for-log argument via Y = relu Z ≥ 0.

## What the students found unclear, and what was done

Student A (13 items) and student B (10 items) each listed places that were
ambiguous. The following were accepted as defects and fixed in the notes:

1. Chapter 2 did not say in which category "composition of contractions is
   matrix multiplication" is a statement about morphisms, nor which
   structure on K each operation needs. Fixed.
2. Chapter 4's composition proposition stated its hypotheses ambiguously
   (the domain/value formula needs at-most-one-model only for the first
   component). Fixed in the statement.
3. Chapter 4's cyclic-systems table abbreviated environments by their T
   value without saying so. Fixed.
4. Chapter 5's Remark 5.19 read as contradicting "needs no rank
   certificate". Reworded: the proof uses none; a successful run itself
   witnesses acyclicity.
5. Chapter 5's accumulator example did not say the intermediate accumulator
   differs between orders while readiness does not. Fixed.
6. Chapter 0 and Chapter 5 disagreed on the measure of a failed state.
   Aligned (0, as in Lean's `stateMeasure`).
7. Chapter 5's finite-history rank was only symbolic. Concrete instance
   added.
8. `T[0i]` in Q4 versus `T[0·i]` in the notes. Question and Chapter 1
   aligned on `T[0·i]`.
9. Chapter 5, Example 5.33: the sentence describing the alternative
   six-step failing run was garbled. Rewritten as an explicit step list.
10. Chapter 5, Example 5.35: "the first row is three machine steps" was
    ambiguous. Clarified.
11. Chapter 7 wrote the rank target as (ℕ, <) while Chapter 5 uses
    (ℕ, pred). Aligned.
12. Chapter 7 cited parts (a), (b), (c) of Theorem 31.3 without stating
    them, and left the status-table date confusing. Both clarified.
13. Chapter 6 said the Lean output "matches Example 4.8" where the values
    differ (1/4 versus log 4). Hedged properly.

Rejected or outside scope: cross-references into `papers/semantics/` are by
design (the notes cite their authority); the categorical product in Pfn
being A ⊔ B ⊔ (A × B) is an exercise, not needed for the course; Q11's
reference to "Section 27.1" was the question's fault and is fixed in the
question.

## Assessment of the assessment

Both students answered every question fully from the notes alone. The set
therefore shows the notes are self-contained for recall and routine
derivation at the level asked. It does not yet test transfer: no question
asks the student to categorify a new construct (e.g. a scan step, a guard
over two variables) or to spot an unsound rewrite not already discussed. A
question set B with such transfer items is the natural next test.

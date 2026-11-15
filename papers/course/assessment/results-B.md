# Assessment results: question set B (transfer)

Date: 2026-11-15. Grader: the instructor, against `answer-key-B.md`.
Student C: one Sonnet 5.5 agent with access to the notes and the Lean
companion only (same rules as set A). It read Chapters 0 to 5 and the Lean
file, and skipped Chapters 6 and 7. Cost: about 285,000 subagent tokens.

| Question | Topic | Score (of 2) |
| --- | --- | --- |
| Q1 | colliding writes as pushforward | 2 |
| Q2 | guard vs Iverson via the projection formula | 2 |
| Q3 | gather through a partial map, lax naturality | 2 |
| Q4 | merging statements, term-local contraction | 2 |
| Q5 | cyclic equation with a partial primitive | 2 |
| Q6 | private free tensor, span isomorphism | 2 |
| Q7 | boundary program on the machine | 2 |
| Q8 | max-plus and Boolean sorts, Galois connection | 2 |
| Q9 | a broken PUBLISH rule | 2 |
| Q10 | extending the mini Lean `Expr` | 2 |
| **Total** | | **20 / 20** |

## Notable answers

- Q2: derived $m_!m^\ast v=\chi_D\otimes v$ from the notes' projection formula
  (Lemma 2.12c) with $x=\mathbf 1$, and stated the decategorified
  Frobenius reciprocity correctly.
- Q5: parameterized the witness span by $T$, giving
  $\mathbb R\xleftarrow{T+1/T}\mathbb R^\times\xrightarrow{\mathrm{id}}\mathbb R$,
  a cleaner form than the key's.
- Q7(e): enumerated every wrong value a zero-initialized reader could
  produce, and tied the violation to both the CONTRIBUTE readiness premise
  and the PUBLISH barrier that makes "published" mean "complete".
- Q8(c): proved the idempotent Galois connection from scratch (the notes
  explicitly decline to treat it), identified image ⊣ preimage for the
  Boolean sort, and gave a counterexample over $\mathbb R$.
- Q9(b): located the broken proof step (conservation, item 5) and proved
  that the variant coincides with the original machine on inputs that
  have a model.

## Notes defects reported, and what was done

| Report | Action |
| --- | --- |
| Chapter 2 never says outright that a collision sum is collection while a contraction sum is a body reduction | Fixed: one paragraph after the index-map table |
| Chapter 5's outcome table says "a program without a certificate never succeeds", conflating "none supplied" with "none exists" | Fixed: reworded to "a program for which no certificate exists" |
| Chapter 2 declines to treat idempotent sorts; $m_!m^\ast v=\chi_D\otimes v$ is not stated | Parked deliberately: these are the transfer content of Q2 and Q8; stating them in the notes would turn set B into a recall test |
| No explicit statement about dead-code elimination of an unread defined tensor (only of subterms) | Parked: Q3 tests exactly this transfer |
| Q7(b) step numbering ambiguous | Question wording; acceptable, the student's reading (first action is step 1) is the key's |
| The Lean file's L = 1/4 contradicts the prose's log 4 if read alone | Already explained in Chapter 6, which the student skipped |

## Assessment of the assessment

Set B was meant to separate recall from transfer, and the Sonnet student
transferred every construction correctly, including one result (the
idempotent Galois connection) that the notes explicitly leave out. So the
notes support transfer at the level asked, but this test still does not
discriminate: a single perfect score cannot tell "the notes teach transfer"
from "the student already knew the mathematics". Cheap ways to sharpen the
signal, if wanted:

1. Run the same set with a Haiku student (set A did not separate the tiers;
   transfer questions might).
2. Run a control: a student with NO notes, only the questions and the
   conventions sheet. A large gap between the control and student C is
   the evidence that the notes, not prior knowledge, did the work.

Both were run afterwards; see Phase 2 below.

## Phase 2: control and second tier (2026-11-15)

Two further runs on the same questions and key.

| Run | Model | Notes? | Score | Tokens |
| --- | --- | --- | --- | --- |
| Control | Sonnet 5.5 | no (questions file only, plus a short rule summary and `Scorer` in the prompt) | 19 / 20 | 76k |
| Student C (above) | Sonnet 5.5 | yes | 20 / 20 | 285k |
| Student D | Haiku 5.5 | yes | 20 / 20 | 388k |

The control lost one point, on Q8(c). It derived the idempotent Galois
connection and the image-preimage case correctly, but guessed that
Theorem 2.4 was the transpose identity, so it could not connect the result
to the adjoint triple. Every other answer, including the projection-formula
argument (Q2), lax naturality (Q3), the witness span over a hyperbola (Q5)
and the broken proof step (Q9), came from prior knowledge plus the rule
summary. The Haiku student matched the Sonnet student; its only slip was
taking `recip` from the Lean file as $L$'s body in Q9(a).

### Interpretation

Set B does not measure the notes. With a one-paragraph rule summary, a
Sonnet-tier model answers transfer questions about this semantics almost
perfectly without the notes, and both tiers score full marks with them.
The notes' measurable contribution on this set is one point: knowing the
course's own framing (Theorem 2.4 as $\Sigma_f\dashv f^\ast$).

Two caveats keep this from meaning "the notes are useless":

- The control's prompt carried the semantics' non-obvious rules (strict
  bodies, additive contributions, models as complete environments, the
  machine vocabulary). Those rules are what the notes spend most of their
  length establishing, so the control was not starting from zero.
- For agent readers the notes' value is a shared, fixed vocabulary and a
  map from each structure to its Lean definition, not mathematical content
  a strong model lacks. A score on derivations cannot see that.

A test that could see it would ask for things only the course fixes: the
specific choice of equivalence and why, the Lean name that realizes a law,
the conventions that rule out a tempting implementation. Those are recall
questions by design, which is what set A already measured.

### Notes defects found by student D, and what was done

| Report | Action |
| --- | --- |
| Chapter 1 §2.3 says $\Gamma_s$ is built from the output variables, but §2.5 keeps explicit binders | Fixed: §2.3 now says explicit binders add to $\Gamma_s$ |
| Chapter 6 says the mini development "has no guards", but `Stmt` encodes guards by `n` | Fixed: the dictionary row now explains the encoding |
| The exact step count of a successful run is never stated | Fixed: one paragraph after Corollary 5.22 |
| The claim "a cyclic program never succeeds" rests on an unsolved exercise | Fixed: the three-sentence argument is now in the text |
| No example of a product containing a sum; nothing on dead statements; no general guard-versus-Iverson comparison | Parked: these are the transfer content of Q4(e), Q3 and Q2 |

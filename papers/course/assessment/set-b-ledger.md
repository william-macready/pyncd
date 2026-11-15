# Ledger: assessment set B (transfer questions)

Resume from the last line marked DONE. Plan (agreed with the user 2026-11-15):
the instructor writes set B and its key in-session (no authoring agents),
then ONE Sonnet student takes it with notes-only access, then the instructor
grades, records results, fixes notes defects the student reports, commits.
Budget intent: minimize tokens; no separate key reviewer.

| Step | Status | Output |
| --- | --- | --- |
| 1. Ledger created | DONE | this file |
| 2. Write `questions-B.md` (10 transfer questions, 20 points) | DONE | `questions-B.md` |
| 3. Write `answer-key-B.md` (instructor check of non-mechanical answers against the spec) | DONE | `answer-key-B.md`; Q2/Q5/Q8/Q9 derivations checked by hand |
| 4. Dispatch one Sonnet student, notes-only access, answers to `answers-B-student-C.md` | DONE | `answers-B-student-C.md` (285k subagent tokens) |
| 5. Grade against key; write `results-B.md` | DONE | `results-B.md`, 20/20 |
| 6. Fix notes defects the student reports (small edits only; larger ones parked in results-B.md) | DONE | ch02 collision/contraction paragraph; ch05 certificate wording; two items parked deliberately |
| 7. Mechanical check (scratchpad `check_course.py`), commit on local main, update memory | DONE | only known false positives remain; see commit after bb1ac664 |

## Notes for a resumer

- Set B covers: write collisions as pushforward (Q1), guard vs Iverson via
  the projection formula (Q2), gather-through-map and lax naturality (Q3),
  statement merging and term-local contraction (Q4), a cyclic program with a
  partial primitive and input-dependent model count (Q5), a private free
  tensor and span isomorphism (Q6), a boundary program machine run (Q7),
  max-plus and Boolean sorts and the idempotent Galois connection (Q8), a
  broken PUBLISH variant (Q9), extending the mini Lean `Expr` with Iverson
  (Q10).
- Student access rules are the same as set A (see the set A dispatch in
  `results.md`): notes and Lean companion only; no reviews, no keys, no
  DESIGN/CONVENTIONS, no `papers/semantics/`, no `leanncd/`.

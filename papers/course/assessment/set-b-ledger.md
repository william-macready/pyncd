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

## Phase 2: discrimination runs (requested 2026-11-15)

Goal: tell "the notes teach transfer" from "the student already knew it".
Both runs grade against `answer-key-B.md`; theorem-number citations are
graded on substance only for the control (it cannot know the numbering).

| Step | Status | Output |
| --- | --- | --- |
| 8. Ledger phase 2 | DONE | this section |
| 9a. Control: Sonnet, NO notes; may read only `questions-B.md`; `Scorer` and its inputs given in the prompt | DONE, graded 19/20 (Q8c: could not relate to Theorem 2.4); 76k tokens | `answers-B-control-sonnet.md` |
| 9b. Haiku student with notes (same access rules as student C) | DONE, graded 20/20; 388k tokens | `answers-B-student-D-haiku.md` |
| 10. Grade both; append comparison to `results-B.md` | DONE | control 19/20, Haiku 20/20; four notes fixes from student D |
| 11. Commit; update memory | DONE | see commit after aeba5f4e |

Resume: if 9a or 9b was interrupted, resume the agent (SendMessage) or
re-dispatch with the same brief; check whether its answers file exists first.

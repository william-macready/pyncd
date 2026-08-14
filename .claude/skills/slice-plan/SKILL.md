---
name: slice-plan
description: Authoring discipline for leanncd slice implementation plans (Wave C C0/C1/C2..., or any subagent-driven-development plan in this repo) — how to right-size tasks so dispatch overhead does not dominate, and how to verify plan code compiles before it ships. Use when writing or revising an implementation plan for leanncd, before executing it.
---

# Writing a leanncd slice plan

Two disciplines, both learned from measured failures in Wave C. Apply them
while authoring the plan — after it ships to an implementer, both are too late.

Setting up the worktree to *execute* a plan is a different step: see
`.claude/skills/new-slice/`.

## 1. Verify plan code compiles — before writing it into the plan

Lean's elaborator rejects far more plausible-looking code than most languages,
so "it reads correctly" is not evidence. Three real examples, each of which
looked fine on the page and each of which cost a fix round or a review cycle:

| Shipped in a plan | Why it fails |
|---|---|
| `decide (e1.error = e2.error)` | `EvalError` has no `DecidableEq` — a `Float` field blocks it |
| `structure Checked where private` | does **not** privatize; needs `private mk ::` |
| `tlprog!{ axis i : ℕ = size }` | axis sizes must be `Nat` literals, not variables |

**Rule: every Lean code block in a plan gets compiled first.** One command:

```bash
bash .claude/skills/slice-plan/check-snippet.sh <file.lean>   # or: ... - (stdin)
```

It compiles against the real leanncd environment in gitignored `spikes/`,
cleans up after itself, and exits non-zero on failure. Snippets that are
fragments (a `#guard` referencing a fixture from another block) should be
concatenated into one scratch file with their dependencies and checked
together — check what will actually be *elaborated*, not each fence alone.

**For fixtures asserting values, also verify the values.** Run the fixture
against the real evaluator and copy the observed result into the plan. This
was done for C0 and it produced zero fixture-value defects across ten
fixtures; skipping it for C1's helper is what let the first row above ship.

**For regression/parity fixtures, mutation-test them.** A fixture that passes
whether or not the code under test works is worse than no fixture — it reports
safety it does not provide. C1's parity fixtures all passed with an *empty*
signature, because every fixture pinned its axis sizes and so never exercised
the shape lookup the slice existed to build. Break the thing under test,
confirm the fixture fails, restore, confirm it passes. Record both observations
in the plan so the implementer can re-run the same check.

**Re-verify after assembly, not just during drafting.** A large plan is
usually built from several verified pieces (one per task, sometimes drafted by
different subagents) and then combined into one document. That combination
step is itself an edit — reformatting a multi-line snippet, inlining a `let`
binding for concision, re-wrapping a line — and Lean's `do`/`match` blocks are
column-sensitive enough that a purely cosmetic edit can silently break parsing.
Real example, Wave C C4: a verified draft used
`let unreachableDiag := {...}` then `throw (.shape (.solveFailure unreachableDiag))`;
the assembled plan inlined the binding directly into the `throw` as a nested
multi-line struct literal "for concision" — never re-verified — and it failed
to *parse* (not elaborate) when the implementer transcribed it, costing a real
debugging cycle for a change that carried zero semantic difference. **Any
reformatting during assembly — even one that looks purely cosmetic — needs
`check-snippet.sh` run again on the *assembled* text, not just trust carried
over from verifying the pre-assembly draft.** If a code block survives
assembly completely unedited (copy-pasted verbatim), it does not need
re-verification; the risk is specifically in edits made *after* the drafting
agent's own verification pass.

**Verify prose claims about the code too, not just code blocks.** The same elaborator-catches-it
argument for Lean snippets does not cover claims written in plain English about how two pieces of
code relate — "X reuses Y," "no second Z was added," "both are reachable from W" — and those are
just as checkable, and were just as wrong. Real example, Wave F F2: the plan's architecture section
said `checkPlanBlock` "reuses `checkPlan`'s availability/production-order loop shape," and the
completion-record template it handed to a later task went further and claimed "no second
graph-wiring loop" was added. Neither was verified against the actual functions before being
written. The real relationship — caught only by the SDD final review, not by drafting or by either
per-task review — was a ~36-of-44-line structural copy, not a shared function; the same completion
record also gave one justification for two different deferred items when it was only true for one
of them. Catching this at the final review (the most expensive tier) rather than at plan-authoring
time cost roughly a third to a half of that slice's total SDD token spend.

**Rule: before writing a sentence of the form "X reuses/shares/duplicates Y" or "both are reachable
from Z," diff or grep the actual functions/files it describes.** This applies to the plan's own
architecture prose and to any completion-record template the plan hands to a later task —
templated prose is not exempt just because it looks like documentation rather than code.

## 2. Right-size tasks — dispatch overhead is fixed, deliverables are not

Each task costs one implementer dispatch plus one reviewer dispatch regardless
of size. Measured on Wave C C1 (7 tasks, 16 dispatches, ~1M subagent tokens):

| Task | Deliverable | Cost |
|---|---|---|
| Task 1 | a 37-line file of type definitions | ~70k tokens |
| Task 4 | two `#guard` lines | ~109k tokens |
| Task 2 | the `SizeInfer` refactor touching ~12 callers | ~108k tokens |

Task 2 earned its cost — the reviewer verified it line-by-line and that
verification was worth having. Tasks 1 and 4 paid the same toll for almost
nothing. C1's seven tasks should have been about four.

**The test is the reviewer's, not the author's** (this is
`superpowers:subagent-driven-development`'s own criterion, under-applied in
C0/C1): *split only where a reviewer could meaningfully reject one task while
approving its neighbor.*

Merge a task into its neighbor when:

- its deliverable has no failure mode independent of the neighbor's;
- it is small (roughly <50 lines) and purely additive;
- it shares a test cycle with the neighbor rather than having its own.

Keep a task separate when:

- it touches existing production code with dependents (its own blast radius);
- it could plausibly be rejected while the neighbor stands;
- it is the natural rollback unit.

Pure-addition sequences — "define the types", "define the function over those
types" — are usually one task. Sequential appends to one test file are usually
two tasks, not three or four.

**A task that bundles mechanical housekeeping with a claim needing verification is worth flagging
even when it isn't worth splitting.** Wave F F2's Task 3 combined a plain import-line addition and
an AGENTS.md table update (housekeeping, no failure mode of its own) with a completion record's
accuracy claims (exactly the kind section 1 above requires verifying). The housekeeping was clean
on the first pass; the record's claims survived Task 3's own review and only broke at the final
review. The reviewer test still applies here: a reviewer could approve the import/AGENTS.md edit
while rejecting the completion record, so the record's claims need the section-1 diff-it-yourself
treatment specifically — not folded into a generic "does this look right" pass — even when the
task as a whole isn't worth splitting.

## 3. What not to trim

The final whole-branch review. Both Wave C slices' most valuable findings came
from it and from nowhere else: C0's capability matrix contradicting itself over
`RHSExpr.agg`, and C1's tautological parity fixtures. Neither was visible in any
individual task diff. Per-task reviews of *mechanical* tasks are the trimmable
part; the whole-branch pass is the one earning its keep.

## Authoring checklist

- [ ] Every Lean block compiled via `check-snippet.sh` (fragments concatenated
      with their dependencies).
- [ ] Every Lean block that was reformatted, inlined, or otherwise edited
      *after* its drafting agent's own verification — including during final
      assembly into one document — re-verified in its post-edit form, not
      assumed safe because the pre-edit version compiled.
- [ ] Every asserted fixture value observed from a real run, not hand-derived.
- [ ] Every regression/parity fixture mutation-tested, with both observations
      recorded in the plan.
- [ ] Every claim in the plan's prose or a completion-record template it produces
      — "X reuses Y," "no second Z was added," "both are reachable from W" —
      checked against the actual functions/files, not asserted from the plan's
      own design intent.
- [ ] Task boundaries pass the reviewer test above; tiny pure-addition tasks
      merged into neighbours.
- [ ] Global Constraints state exact values, and name anything the plan
      deliberately does *not* do (and which later slice owns it).
- [ ] If this slice introduces a new subsystem or file tree, the plan makes it
      *discoverable*, not just correct: reachable from a plain top-level import
      a new reader would already use, and mentioned in the AGENTS.md a reader
      would already open. Wave C's C0-C4 shipped 10 files and a working
      compiler that `import LeanNCD` couldn't reach and neither AGENTS.md
      mentioned — invisible until a later audit slice (C6) fixed it. Don't
      defer this to "someone will notice eventually."

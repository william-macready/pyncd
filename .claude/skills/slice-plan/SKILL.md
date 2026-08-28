---
name: slice-plan
description: Authoring discipline for leanncd slice implementation plans (Wave C/F slices, or any subagent-driven-development plan in this repo) — verifying plan code, paths, and prose claims before they ship; covering the recurring-defect siblings a diff review structurally cannot see; right-sizing tasks by fixture count so dispatch overhead does not dominate; and where review budget actually pays. Use when writing or revising an implementation plan for leanncd, before executing it.
---

# Writing a leanncd slice plan

Disciplines learned from measured failures in Waves C and F. Apply them while
authoring the plan — after it ships to an implementer, they are all too late.

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

**A locator, index, or ordering requirement is invisible to every value-comparing
test.** This is the sharp case of the rule above, and mutation-testing the fixtures
you *have* will not save you — the problem is the fixture's SHAPE, not its absence.
Violating such a requirement changes no accept/reject verdict and no computed value;
it changes only which position an error payload names. Every fixture that compares
results still passes.

The nonlinearity plan's Task 3 (`papers/nonlinearity_split_pair_direct_lowering.md`
§3.5) shipped requiring `causalityFailure` to "retain original block-step indices"
after a block's element type gained non-assignment cases. Nothing
could have caught a violation: every pre-existing step block held only assignments,
so a block-step index and a filtered-assignment index *coincide* in all of them. The
requirement survived plan authoring, an external agent's execution, and a review of
that execution — surfacing only when a field rename came to depend on it. The fix was
one fixture with a non-assignment step *between* two assignments, forcing the two
indexings apart (correct reports 2, filtered reports 1). The mutation that proves it
fails exactly that one fixture and leaves every other test green.

**Rule: when a plan states a requirement about an index, a locator, a check order, or
a diagnostic's payload, name the fixture that could fail if it were violated — and
check that the fixture's own construction can distinguish the two readings.** If every
candidate fixture makes the two readings coincide, you have no test, however many you
write. The same argument applies to a check-ORDER claim ("X is enforced before Y"): it
needs a fixture violating both X and Y at once, or nothing pins the order.
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

**Verify every path the plan names, with `ls`, at authoring time.** The same argument one more
level down: a plan cites files, and a wrong path costs the implementer a judgment call and a
concern round-trip. Wave F F4's plan sent Task 5 to `leanncd/docs/design/eval_ir.md`, which does
not exist — the real file is `papers/eval_ir.md` — and omitted `DifferentialTest.lean` from that
task's Files list even though the deliverable (a third differential leg) could only be wired
there. Both were caught by the implementer rather than the author. Derive a task's file list from
"where does this deliverable have to live," then `ls` each entry.

**Never put line numbers in text the plan tells a task to ship.** Completion records, AGENTS.md
rows, and design-doc edits should cite identifiers and function names, never `File.lean:NNN`. In
F4's final fix wave the docs commit landed before the code commit (correct — it kept trivial prose
off the critical path), and the code commit then inserted 22 lines above the cited region,
invalidating six line references in one stroke. Identifiers survive that; line numbers cannot.

## 2. Cover what a diff cannot show

Review packages are diffs, and a diff cannot contain unchanged code. That is a structural blind
spot, not a reviewer failure, and it lands precisely where this repo's recurring defect family
lives.

Wave F F4's Critical finding was in `stepWriteRowsOk`. Task 1 had edited `checkWrites` — the
function that *calls* it — and added guards sitting immediately adjacent in the same call sequence.
Task 1's reviewer read a diff whose hunks were inside the calling function and still could not see
the bug, because `stepWriteRowsOk` itself was unchanged and therefore absent from the package. It
survived five per-task reviews and surfaced only at the whole-branch tier, where finding and fixing
it cost roughly 560k tokens across the review, its fix wave, and the re-review.

It was also the **fourth** instance of one shape across two slices — a write-geometry predicate
validating *which rows must be a given kind* without validating *which rows may not be*
(free-extent, pinned-literal, write-map rank, then this). F4's own plan documented the third
instance in its §0 and still left the fourth to be discovered at the most expensive tier.

**Rule: when a task fixes instance _N_ of a known recurring defect family, the plan names the
sibling functions and makes auditing them a deliverable of that same task.** The artifact is an
explicit table — every case × class cell classified as (a) required, (b) forbidden, or (c) silently
ignored — because **every (c) cell is a candidate instance _N+1_**. F4 eventually produced exactly
this table over all seven of its geometry/causality predicates and it found no fifth instance;
produced in Task 1 it would have cost perhaps 20k tokens instead of 560k.

Two refinements that fell out of that sweep, worth carrying rather than re-deriving:

- All four instances were **write-path** predicates, because the write helper performs no bounds
  recovery by design while reads are backstopped by `inBoundsPerDim`. A (c) cell on a read
  predicate is usually safe; one on a write predicate usually is not.
- A predicate can be sound only by an **unenforced call-site precondition** — `baseWriteRowsOk` is
  safe purely because its single caller passes `contextWidth = 0`, making one row kind
  unclassifiable. That is a (c) cell in disguise, so audit call sites, not just predicate text.

## 3. Right-size tasks — dispatch overhead is fixed, deliverables are not

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

**Size by test artifacts, not by production lines.** Wave F F4's plan rated Task 1 low-to-moderate
risk by counting what it changed: two small, fully-specified bug fixes with known repro shapes. It
ran ~200k tokens and 82 minutes — comparable per-token to Task 3, the slice's architectural
centerpiece. The cost was never in the fixes; it was in 6 fixtures × 3 mutation cycles, each built
by trial and error. **Count fixtures and mutation cycles when estimating a task, and state that
count in the plan's own risk table** so the controller sizes the dispatch to the real work rather
than to the diff.

**Name the donor fixture for every fixture the plan requires.** Most of that trial-and-error is
avoidable: a new fixture is nearly always a one-field mutation of an existing one, and the plan
author usually knows which. F3's *completion record* described its own fixtures precisely this way
("a one-field mutation of Fixture 5: dim-0 bias `1 -> 5`") — but F4's *plan* did not carry that
forward into its fixture list, so each implementer rediscovered the donor. Write
`clone <existing fixture>, change <one field>` beside each required fixture. This is the same
lesson as F2's 97-minute fix-wave outlier, applied one stage earlier in the pipeline.

**A task that bundles mechanical housekeeping with a claim needing verification is worth flagging
even when it isn't worth splitting.** Wave F F2's Task 3 combined a plain import-line addition and
an AGENTS.md table update (housekeeping, no failure mode of its own) with a completion record's
accuracy claims (exactly the kind section 1 above requires verifying). The housekeeping was clean
on the first pass; the record's claims survived Task 3's own review and only broke at the final
review. The reviewer test still applies here: a reviewer could approve the import/AGENTS.md edit
while rejecting the completion record, so the record's claims need the section-1 diff-it-yourself
treatment specifically — not folded into a generic "does this look right" pass — even when the
task as a whole isn't worth splitting.

## 4. What not to trim

The final whole-branch review. Every slice's most valuable finding has come from it and from
nowhere else: C0's capability matrix contradicting itself over `RHSExpr.agg`, C1's tautological
parity fixtures, F3's write-extent soundness gap, F4's `stepWriteRowsOk` Critical. None was visible
in any individual task diff. Per-task reviews of *mechanical* tasks are the trimmable part; the
whole-branch pass is the one earning its keep.

F4 measured the split directly, and the ratio is worth knowing when a plan sets its own process
weight:

| Review tier | Tokens | Yield |
|---|---|---|
| 5 per-task reviews | ~647k | 1 Important (a stale doc passage) |
| 1 final whole-branch review | ~305k | **1 Critical** (a real soundness hole) |

The tempting read — cut per-task review — is the wrong one: those five reviews are why the branch
arrived clean enough for one reviewer to go deep enough to find the Critical. The right move is
**more depth at the tier that pays**: for a slice with a soundness surface, plan for two independent
final reviewers with different lenses rather than one. Mid-tier models handle per-task review of
clean, well-specified tasks adequately, which is where the budget for the second final lens comes
from.

**Sequence expensive independent verification early, not last.** F4's independent oracle — a
from-scratch second implementation forming a third differential leg — was its single most expensive
task (~386k tokens) and found no disagreement. That is the expected result for a differential and
not a reason to cut it; the guarantee is the point. But it ran as terminal work, after every other
leg already agreed, which is the position where it can teach the least. Schedule that kind of task
while the implementation it checks is still being actively built, so a disagreement arrives when
someone still has the context to act on it.

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
- [ ] For every requirement about an index, locator, check order, or diagnostic
      payload: the plan names a fixture that could FAIL if it were violated, and
      that fixture's construction actually distinguishes the two readings (the
      common trap is a fixture in which both readings coincide, so it pins
      nothing). Order claims need a fixture violating both conditions at once.
- [ ] Every claim in the plan's prose or a completion-record template it produces
      — "X reuses Y," "no second Z was added," "both are reachable from W" —
      checked against the actual functions/files, not asserted from the plan's
      own design intent.
- [ ] Every file path the plan names verified with `ls`, and each task's Files
      list derived from where its deliverable must live rather than from memory.
- [ ] No `File.lean:NNN` line numbers in any text the plan tells a task to ship
      (completion records, AGENTS.md rows, design-doc edits) — identifiers only,
      since a later code commit in the same slice invalidates line numbers.
- [ ] For any task fixing instance _N_ of a known recurring defect family: the
      plan names the sibling functions a diff review cannot see, and requires the
      case × class table (required / forbidden / **silently ignored**) as a
      deliverable of that task. Every silently-ignored cell is a candidate
      instance _N+1_.
- [ ] Every required fixture names its donor — `clone <existing fixture>, change
      <one field>` — rather than leaving the implementer to rediscover it.
- [ ] Task boundaries pass the reviewer test above; tiny pure-addition tasks
      merged into neighbours.
- [ ] Each task's risk entry states its fixture and mutation-cycle count, not
      just its production-line count — that count, not the diff size, is what
      the task will actually cost.
- [ ] Global Constraints state exact values, and name anything the plan
      deliberately does *not* do (and which later slice owns it).
- [ ] If this slice introduces a new subsystem or file tree, the plan makes it
      *discoverable*, not just correct: reachable from a plain top-level import
      a new reader would already use, and mentioned in the AGENTS.md a reader
      would already open. Wave C's C0-C4 shipped 10 files and a working
      compiler that `import LeanNCD` couldn't reach and neither AGENTS.md
      mentioned — invisible until a later audit slice (C6) fixed it. Don't
      defer this to "someone will notice eventually."

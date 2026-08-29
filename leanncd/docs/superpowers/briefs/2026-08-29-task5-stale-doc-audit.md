# Brief: audit active documentation for claims made stale by Tasks 1–4

**Audience:** an external coding agent (GPT / Copilot), working in this repository.
**Written:** 2026-08-29. **Against:** `main` at `85fa004`.

This is a **read-only audit**. You will find and classify stale claims; you will **not** rewrite any
of them. The deliverable is a report, committed.

---

## Where output goes

Commit your report. **A branch or `main` is equally fine** — what matters is that it is committed and
that you tell me the SHA. Nothing counts as delivered if it exists only in a chat reply.

One new file:

```
leanncd/docs/superpowers/briefs/2026-08-29-task5-stale-doc-audit-RESULTS.md
```

Change no other file. Before replying, run this and paste its output:

```bash
cd /Users/williammacready/code/python/pyncd
git log --oneline -3
git status --porcelain          # must be empty
```

---

## Why this audit exists

Task 5 (`papers/nonlinearity_split_pair_direct_lowering.md` §3.7) must sweep ~24 documents that
describe a pipeline four slices out of date. The sweep is the bulk of that task, and its risk is
specific: this project's history is a run of **inaccurate prose claims about unchanged code**, caught
only at the final review tier — most recently in Task 4. So the sweep is claim-verification against
the tree, not light work because it is prose.

Your job is the **finding** half. Someone else does the rewriting, because deciding what a passage
*should* say requires knowing what four slices changed, and getting that wrong ships silently.

---

## What actually changed, so you know what stale looks like

Four merged slices. Each bullet is a fact about the tree today:

- **Task 1** — `TLProgram.compileToScheduled` is now **logical**: it does not call `splitNonlins` and
  emits **no generated `%nl` names**. Public `route` accepts a logical schedule and performs checked
  private physicalization (`DSL/Pipeline/RouteFragments.lean`) before invoking the unchanged
  `routeCore`. `LinearProgram` survives only as a **deprecated compatibility alias**. `splitNonlins`
  remains as a non-production regression helper only.
- **Task 2** — a durable 145-case route corpus and 19-case payload matrix; four "class-6 door"
  physicalization soundness bugs closed.
- **Task 3** — `RawPlanBlock.assignments : Array AssignPlan` **is now** `steps : Array BlockStep`,
  where `BlockStep` is `.assign`/`.pointwise`/`.axiswise`. `checkPlanBlock` checks all three kinds;
  `runDenseBlock` dispatches all three; scan causality walks `.assign` payloads only; and
  `ScanPlanError.causalityFailure`'s second field is now **`blockStepIndex`**, not `stmtIndex`.
- **Task 4** — `compileScan` **admits and lowers nonlinear scan sources**. The 17-case differential
  corpus moved from `9 accepted / 4 unsupportedNonlin / 4 unsupportedAgg` to **13 / 0 / 4**. The
  independent unroller preserves `.freeNorm`.

**Concrete stale markers to look for** (non-exhaustive — use judgment beyond this list):

| Marker | Why it is stale |
|---|---|
| `RawPlanBlock.assignments`, "blocks hold assignments" | renamed to `steps`, holds `BlockStep` |
| `splitNonlins` described as part of the active compile/route pipeline | it is regression-only now |
| "generated `%nl` names" in the shared schedule | `compileToScheduled` emits none |
| `LinearProgram` as a distinct live type | deprecated alias |
| "nonlinear scans are unsupported / rejected" | admitted since Task 4 |
| `unsupportedNonlin = 4`, or the 9/4/4 split | now 13/0/4 |
| `causalityFailure`'s `stmtIndex` | now `blockStepIndex` |
| the three-step Eval lowering | superseded by the two-step `assign → pointwise/axiswise` |
| "Task N is not yet built / does not exist yet" for Tasks 1–4 | all merged |

---

## Part 1 — the specified scan (mechanical)

§3.7's gate already defines a stale-recommendation scan: an `rg --multiline-dotall` over 17 named
documents with a fixed regex. Find it in §3.7 (search for `stale-recommendation scan`), run it
**verbatim**, and record its exact output — including "no matches", which is a meaningful result.

Do not modify the regex or the file list. If it errors, paste the error.

---

## Part 2 — the audit the regex cannot do (the real work)

For **every document in §3.7's Files list** (~24, including the four `docs/superpowers/` specs and
plans), find each passage that makes a claim about the nonlinearity work, and classify it.

One row per passage:

| Document | Passage (quoted, ≤2 lines) | Claim it makes | Verdict | The code fact that settles it |
|---|---|---|---|---|

**Verdict** is exactly one of **STALE** / **STILL TRUE** / **UNCERTAIN**.

**The last column is the point of the exercise.** A verdict without a checkable code fact — a
`grep` you ran, an identifier that does or does not exist, a job count you observed — is not usable,
because the next person has to re-derive it. "Seems outdated" is not a code fact. Quote the command
or name the identifier.

Prefer **UNCERTAIN** over a confident wrong call. An honest "this passage's claim depends on
something I could not settle, here is what I checked" is worth more than a guess, because a wrong
STILL TRUE means a stale passage ships.

---

## The trap: archived ≠ active

**Archived documents keep their superseded content, and their rejected terminology is correct
there.** §3.7 step 5 requires archived scan documents to retain permanent superseded banners; step 7
excludes the canonical decision record from the scan for the same reason.

So:

- `papers/nonlinearity_split_pair_reconstruction_archived.md` describing neutral pairs or shared
  splitting is **not stale** — that is what an archive is for.
- `papers/nonlinearity_split_pair_direct_lowering.md` (the canonical record) discussing rejected
  designs, or quoting the lost oracle floats as history, is **not stale**.
- `docs/superpowers/specs/2026-08-21-nonlinearity-in-scans-design.md` and
  `leanncd/docs/superpowers/plans/2026-08-21-nonlinearity-in-scans.md` are **superseded** documents.
  For these, the question is **not** "is the content current" (it is not, by design) but **"does its
  banner correctly direct a reader to the canonical plan, and does its active prose avoid
  *recommending* the superseded approach as a next step?"** Flag a missing or misdirecting banner;
  do not flag the historical content itself.

For each document, **state which category you placed it in** (active / superseded-with-banner /
archived) and why. Miscategorising is the most likely way this audit goes wrong.

One document is called out in §3.7 specifically:
`leanncd/docs/superpowers/plans/2026-08-21-wiring-loop-generalization.md` has a completed historical
record (keep) but an **active next-slice pointer** aimed at the superseded plan (flag).

---

## Also report

- **Coverage:** any document in §3.7's Files list you could not assess, and why.
- **Gaps in the Files list:** any *other* active document you encountered that carries a stale
  nonlinearity claim but is **not** in §3.7's list. That is a genuine finding — the list was written
  before Tasks 3 and 4 existed.
- **§3.7 steps 2–3 gap check.** Step 1 (five differential cases) is already satisfied by Task 4's
  `nonlinearScanFixtures` in `DifferentialTest.lean` — verify that and say so. Then check what
  remains of step 2 ("compare exact source-visible keys and warning order") and step 3 ("confirm the
  3,832-case scan-free gate and the 17-case 13/0/4 split") against the tree. Report what exists and
  what does not; do not implement anything.

---

## Hard boundaries

1. **Change no document.** No rewrites, no "while I'm here" corrections, not even an obvious typo.
   The audit's value is that its findings can be checked before anything moves.
2. **Do not modify the §3.7 scan's regex or file list.**
3. **Invent no verdicts.** Every row needs a code fact you actually established.
4. Your only new file is the RESULTS document named above.

---

## Stop and report rather than improvise if

- the §3.7 scan errors or its file list references a document that does not exist;
- a document's category (active / superseded / archived) is genuinely ambiguous — record the
  ambiguity rather than picking;
- you find a stale claim that appears to indicate a **real code defect** rather than a stale
  description — that is a much more serious finding than a doc bug, and it should be reported
  loudly and separately, not filed in the table;
- the §3.7 steps 2–3 gap check suggests the differential is missing something material.

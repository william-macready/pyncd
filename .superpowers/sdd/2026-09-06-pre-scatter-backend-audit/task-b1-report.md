# Task B1 report — Axis B, part 1: write-geometry predicate table + call-site sweep

**Status: DONE_WITH_CONCERNS** (concerns are audit findings, not task failures — see §6).

Worktree: `.claude/worktrees/pre-scatter-audit`, branch `worktree-pre-scatter-audit`.
Base HEAD at start: `267976e`. Build verified green at **8660 jobs** before and after (no production
code changed, so the second build is definitionally identical; `git diff` against `leanncd/LeanNCD`,
`leanncd/lakefile.toml` and `leanncd/test` is **empty**).

## 1. Deliverables

| Deliverable | Where | State |
|---|---|---|
| The table (current row kinds only) | `axis-b-fragment.md` §B1.2 | 12 rows × 14 columns = 168 cells, every cell classified |
| Adjudication of every `c` cell | `axis-b-fragment.md` §B1.3 | 86 `c` cells across 15 groups; 9 closed, 6 open |
| The call-site sweep | `axis-b-fragment.md` §B1.4 | 19 production call sites + 8 type-signature positions |
| Construction spikes | `axis-b-spikes/` (2 files + 2 captured outputs) | 15 probes, S1–S15 |

Fragment path is exactly as briefed: `.superpowers/sdd/2026-09-06-pre-scatter-backend-audit/axis-b-fragment.md`.
`papers/pre_scatter_backend_audit.md` was **not** created or edited. `axis-a-fragment.md` and the
Task A files (`Adapter.lean`, `Prepared.lean`, `Executable.lean`, `Signature.lean`,
`EvalPlan.lean`'s input loop) were not touched.

## 2. Findings, in one line each

| ID | Finding | Verdict |
|---|---|---|
| B1-F1 | No write case-by-class audit over the geometry predicates exists. **Two** documents presuppose it (`boolean_predicate_output_evalplan.md` Task 4.4; `predicate_boolean_backend_parity.md` §9.4), two later ones declined it | Stale inherited obligation, confirmed |
| B1-F2 | **Candidate gap 1** — `baseWriteRowsOk` still carries the verbatim defect-instance-4 `filterMap` and ADMITS a hand-built `.advancing` row at both dim classes. Held up *solely* by `checkWrites`' `if isBase then 0` | `c`‡ **latent, not live** — a full-plan attempt is rejected `writeGeometryNotAdmitted true 0` |
| B1-F3 | **Candidate gap 2** — coeff-row width is genuinely unchecked, but provably irrelevant: the free-position cover bounds the single nonzero's index into the real domain, and `applyAffine`'s `zip` only ever drops zeros | **REFUTED**, with mechanism + 5 probes |
| B1-F4 | A `free` row may sit at an **advancing** dimension in a base write; `baseWriteRowsOk` clause 2 records the position and discards the dimension | **OPEN**, memory-safe, policy-consistent, unpinned |
| B1-F5 | Base writes need touch the lower boundary of only **one** advancing dimension; every other advancing dim's pinned literal need only be in range | **OPEN**, memory-safe; the docstring's "touches the lower boundary" gloss holds only for a 1-axis scan |
| B1-F6 | `Compile.lean`'s second call site: two hand-inlined duplicates confirmed, **and** the source-facing pass is a strict subset (no counterpart of `baseWriteRowsOk` clauses 1–2, none of `stepWriteRowsOk`, none of `freeExtentsAgree`) | Drift risk, confirmed and widened |
| B1-F7 | `commitWrite`'s docstring has one bullet per constructor (complete), but the `.advancing` bullet's argument is **step-scoped** and silent on the base phase where `ctx = []` | Docstring-as-predicate gap |
| B1-F8 | `writesCollide` is length-blind in **both** directions; a dimension present in only one array never separates the writes | **REFUTED as harmful** (fails conservative; lengths always equal at both call sites) |
| B1-F9 | `LHSSlot.outExtent` collapses **every** negative-valued affine form to extent `0` via `Int.toNat`, unrejected and undocumented, while an unsized axis correctly fails loud | **OPEN**, flagged for B2, deliberately not closed |
| B1-F10 | **10 of the 16 `b` cells have no located test.** Every `#guard` on either geometry predicate in the whole suite is a positive; `stepWriteRowsOk`'s clause 2 is the least-pinned clause in the file | Gate shortfall, measured |

## 3. Predicted-vs-actual counts (the controller asked for divergence, not agreement)

| Quantity | Brief's estimate | Actual | Note |
|---|---|---|---|
| Adjudicable (`c`) cells | ~40 | **86** | Large overshoot, explained: 3 of 14 columns are entirely `c` by construction (36 cells) and 2 more are dimension-class-blind (20 cells). Excluding those five leaves **30**, i.e. the estimate's order. Reported in the fragment rather than forced to match. |
| Call sites | ~21 | **19** production + 8 type positions | Close; the 8 signature positions of `WriteRowKind` are what brings it to ~27 if counted. |
| Construction spikes | ~8 | **15 probes in 2 files** | Overshoot by probe count, not by effort — several probes are one `#eval` tuple each. |

## 4. The (a)/(b)/(c) definitions I fixed, and why

The brief's vocabulary is closed but not defined operationally, and the naive reading ("does the site
demand this row's presence?") makes `freeExtentsAgree` and `pinnedLiteralsInRange` come out `c`
everywhere, which is plainly wrong — they are *value* constraints, not *presence* constraints. The
definition used throughout, stated in the fragment's legend:

- **a** — the site imposes a constraint on such a row and rejects when it fails (including demanding
  the row's presence);
- **b** — the site rejects when such a row is present at that dim class in that phase;
- **c** — the site neither constrains nor rejects it; the row passes through unexamined.

Two structural marks were needed beyond the closed letters, and both are declared: **—** for "the
site is not reached in that phase" (`baseWriteRowsOk` is base-only, `stepWriteRowsOk` step-only,
`writesCollide` base-only, so 18 cells are structurally n/a) and **▷** for "the site classifies
*read* rows, a disjoint vocabulary" (`causalAdvancingRow`, `stateReadCausal`, 24 cells). Neither
softens a `c`; both are honest n/a rather than a letter. **‡** flags the brief's "`c` in disguise" —
a mark holding only via an unenforced call-site precondition.

## 5. Appendability for Task B2 (the interface I owe it)

The row axis is `kind × dim-class × phase`; the column axis is fixed at 14 sites. A `strided` kind
appends **exactly four rows at the bottom** (R13–R16) with no change to any header, existing row, or
legend entry. §B1.2's "How Task B2 appends a fourth row kind" states this plus three measured facts
B2 needs:

1. `classifyWriteRow` is the single chokepoint — every coefficient ≠ 1 and every bias ∉ {0,1} is
   `none` today [S12].
2. A `strided` row **will be emittable at base** (unlike `advancing`, it is not gated on
   `p < contextWidth`), so `baseWriteRowsOk`'s clause-2 `filterMap` will silently drop it and neither
   value predicate will look at it — **the five-times defect, live rather than latent**. This is the
   single most important handoff in the fragment.
3. `writesCollide`'s `| _, _ => false` catch-all makes two strided base writes to one state always
   report as colliding — over-rejecting, therefore safe, but it makes strided-plus-strided base
   initialization inexpressible.

The fragment ends with `<!-- END OF TASK B1 SECTION — Task B2 appends below this line. -->` and no
closing summary that would strand B2's additions. §B1.5's summary is scoped as "Axis B part 1 state
against the gate", not as a document conclusion.

## 6. Concerns

1. **B1-F10 is the one I would escalate.** `stepWriteRowsOk`'s clause 2 — the clause B2 must extend
   to classify a strided row at an advancing dimension — has **no negative test anywhere**. Rows R3
   and R7 (`pinned`/`free` at an advancing dim in a step write) are rejected only per this audit's
   S3. Every `#guard` on either geometry predicate is an acceptance. If B2 touches clause 2, nothing
   in the suite will catch an over-permissive edit.
2. **B1-F4 and B1-F5 are open but memory-safe**, and both are consistent with the declared
   `ScanBoundaryPolicy.zeroThenBaseOverlay`. I did **not** propose fixes (findings-only), and I
   deliberately did not close them as "backstopped" — they are write-path cells. What they lack is a
   pin, since `ScanTest` exercises free base faces only at non-advancing dimensions.
3. **B1-F9 is not fully chased.** I confirmed `outExtent` returns `some 0` for four distinct negative
   affine forms and that both callers (`Eval.scatterOutShape`, `SizeInfer.scatterOutputShapes`)
   distinguish only `some` from `none`. Whether a zero-extent scatter output is rejected further down
   the scatter path I did **not** determine — that is scatter territory, which is B2's. Flagged, not
   closed. Rule 12: this is the one place the fragment stops short of a verdict, and it says so.
4. **Two Task-A failure modes were guarded against explicitly.** (a) Before calling anything a
   defect I grepped docs and tests for whether the behavior is already documented and pinned as
   intended — that is what moved `writesCollide`'s free/advancing blindness (G8) to
   "documented-and-pinned intentional", quoting its docstring and two green `#guard`s, rather than
   promoting it. (b) Every exhaustiveness claim in the fragment was verified before shipping, and
   **three were wrong on the first pass and corrected**: the "excluding those five columns leaves 20"
   arithmetic (actually 30), the closed/open group split, and — most importantly — an initial claim
   that the 16 `b` cells were "located by `ScanTest`'s Part 1 `#guard`s plus the mutation fixtures",
   which the audit's own material falsified. Re-reading `ScanTest.lean` Part 8 showed exactly two
   located fixtures covering exactly two of the twelve step-phase `b` cells; that correction became
   B1-F10.
5. **One incidental fact worth knowing repo-wide** (not a finding, no action requested): importing
   the `LeanNCD` umbrella makes `bias` a reserved syntax token, because `LeanNCD/DSL/Syntax.lean`
   declares `"bias"` in `tl_linear_item`. Any file that imports the umbrella cannot write
   `{ coeffs := …, bias := … }` — it is a parse error at `bias`. This is why both spikes import
   `LeanNCD.Eval.Plan.Scan` directly, and it is recorded in the fragment's header so the next person
   does not lose the same twenty minutes.

## 7. Constraint compliance

- No production code changed — `git diff` against `leanncd/LeanNCD`, `leanncd/lakefile.toml`,
  `leanncd/test` is empty.
- `lakefile.toml` untouched; no test module added; nothing fixed.
- Task A's files untouched; `axis-a-fragment.md` untouched; `papers/pre_scatter_backend_audit.md` not
  created.
- No subagents dispatched.
- Working spikes live in `leanncd/spikes/` (gitignored); committed copies live in
  `axis-b-spikes/` (force-added, matching Task A's precedent, since `.superpowers/sdd/.gitignore`
  is `*`).
- Prose cites identifiers only — no `file:NNN` line numbers anywhere in the fragment.
- Commit prefix `docs(leanncd):`.

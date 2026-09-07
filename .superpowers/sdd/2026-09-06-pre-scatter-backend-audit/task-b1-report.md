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
| Adjudication of every `c` cell | `axis-b-fragment.md` §B1.3 | 86 `c` cells across 17 groups; 9 groups / 71 cells closed, 8 groups / 15 cells open |
| The call-site sweep | `axis-b-fragment.md` §B1.4 | 19 production call sites + 11 type-signature positions |
| Construction spikes | `axis-b-spikes/` (2 files + 2 captured outputs) | 16 probes, S1–S16 |

Fragment path is exactly as briefed: `.superpowers/sdd/2026-09-06-pre-scatter-backend-audit/axis-b-fragment.md`.
`papers/pre_scatter_backend_audit.md` was **not** created or edited. `axis-a-fragment.md` and the
Task A files (`Adapter.lean`, `Prepared.lean`, `Executable.lean`, `Signature.lean`,
`EvalPlan.lean`'s input loop) were not touched.

## 2. Findings, in one line each

| ID | Finding | Verdict |
|---|---|---|
| B1-F1 | No write case-by-class audit over the geometry predicates exists. **Two** documents presuppose it (`boolean_predicate_output_evalplan.md` Task 4.4; `predicate_boolean_backend_parity.md` §9.4), two later ones declined it | Stale inherited obligation, confirmed |
| B1-F2 | **Candidate gap 1** — `baseWriteRowsOk` still carries the verbatim defect-instance-4 `filterMap` and ADMITS a hand-built `.advancing` row at both dim classes; so do **both value predicates**, at any extents. Held up by **two** independent barriers (fix round 1) | `c`‡ **latent, not live** — a full-plan attempt is rejected `writeGeometryNotAdmitted true 0`. **10 cells**, not 6 |
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
| Call sites | ~21 | **19** production + 11 type positions | Close; the 11 signature positions of `WriteRowKind` bring it to 30 if counted. |
| Construction spikes | ~8 | **16 probes in 2 files** | Overshoot by probe count, not by effort — several probes are one `#eval` tuple each. |

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
a mark holding only via an unenforced call-site precondition. Fix round 1 added one more, at the
reviewer's request: **§** marks a cell that is `a` for the row *class* while a sub-case inside it is
unconstrained by that site (only R1 × col 4, pointing at B1-F5), so the letter is not read as
stronger than it is.

## 5. Appendability for Task B2 (the interface I owe it)

The row axis is `kind × dim-class × phase`; the column axis is fixed at 14 sites. A `strided` kind
appends **exactly four rows at the bottom** (R13–R16) with no change to any header, existing row, or
legend entry. §B1.2's "How Task B2 appends a fourth row kind" states this plus three facts B2 needs —
**two measured, one an explicitly-labelled conditional** (corrected in fix round 1):

1. **[measured]** `classifyWriteRow` is the single chokepoint — every coefficient ≠ 1 and every bias
   ∉ {0,1} is `none` today [S12].
2. **[conditional, not measured]** *If* B2's strided branch is not gated on `contextWidth` — a design
   choice B2 owns, which nothing in the current code forces either way — then a strided row becomes
   emittable at base, `baseWriteRowsOk`'s clause-2 `filterMap` silently drops it, neither value
   predicate looks at it, and `commitWrite`'s `c·x + b` is unbounded. §B1.2 gives the smallest
   exhibiting shape and states that **B2's first obligation is to decide the gating question and build
   the construction either way** — carried forward as a test to run, not as a finding.
3. **[measured]** `writesCollide`'s `| _, _ => false` catch-all makes two strided base writes to one
   state always report as colliding — over-rejecting, therefore safe, but it makes
   strided-plus-strided base initialization inexpressible.

§B1.2 also now states that B2 must update **two things outside the row block**, one of which
(§B1.5's gate summary) sits *before* the append marker: editing it in place is expected, since the
marker exists to order new prose, not to freeze B1's counts.

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

---

# Fix round 1 — report

**Status: DONE.** All three Important items and all six accuracy items addressed. One new spike
section (S16) added; no production code changed.

## Evidence the coordinator required

| Required | Observed |
|---|---|
| Build job count from a real run | `lake build` → **`Build completed successfully (8660 jobs).`** |
| Production diff still empty | A `--stat` diff of HEAD restricted to `leanncd/LeanNCD`, `leanncd/lakefile.toml` and `leanncd/test` returns **nothing**; a short status restricted to `leanncd` likewise returns **nothing**. Only the two fragment/report files and the refreshed spike copies are modified |
| Important 1: observed evaluation of an `.advancing` row at base through both value predicates | **S16**, below |

### S16 — the construction Important 1 asked for

Appended to `AxisBBaseBoundaryProbe.lean`; captured output refreshed in `axis-b-spikes/`. Rows
`#[some (.pinned 0), some (.advancing 0), some (.free 0)]` — a rank-3 state, dim0 satisfying
`baseWriteRowsOk` clause 3, dim1 carrying the advancing row, dim2 the free cover, output rank 1.

```
baseWriteRowsOk #[0,1] 1 / #[0] 1                     → (true, true)
  (R9: advancing @ advancing dim; R10: advancing @ non-advancing dim — both admitted)

(freeExtentsAgree #[1,3,3] #[3], pinnedLiteralsInRange #[1,3,3],
 freeExtentsAgree #[1,1,3] #[3], pinnedLiteralsInRange #[1,1,3])
                                                      → (true, true, true, true)
  (both value predicates pass it at ANY extents, including dim1 extent 1)

writeRowKinds 3 0 <that map>   → #[some (.pinned 0), none, some (.free 0)]
  (the `none` at dim1 is what actually blocks it today — clause 1, not either value predicate)

applyAffine <that map> [0] / [1] / [2]                → ([0,1,0], [0,2,1], [0,3,2])
inBoundsPerDim [1,3,3] <each>                         → (true, true, false)
flatIndex [1,3,3] <each>                              → (3, 7, 11)      -- 9-element store

probe "non-empty base block contextShape"
  → checkScanPlan REJECTED: ScanPlanError.baseBlockContextNotEmpty #[2]
```

Two silent writes into cells belonging to other coordinates, then an out-of-range `Array.set!` —
the verbatim F4 failure signature. And the last line confirms there is no base-phase context shape to
appeal to.

## Important items

**Important 1 — G6/G7 misclosure, fixed.** The four cells (R9, R10 × cols 6, 7) are now `c`‡ in the
table and are adjudicated in a **new group G16**, open and folded into B1-F2. G6 shrank 8→6 cells
(now R1–R4, R11, R12) and G7 8→6 (now R5–R8, R11, R12), each stating explicitly that advancing rows
at **base** are excluded and why. I accepted the review's reasoning in full and verified each leg
myself before rewriting: `stepWriteRowsOk` is marked `—` at base in my own table, so its clauses 2
and 3 cannot fire there; `advancingSizeMismatch` relates `stateShape[advancingDims[i]]` to
`historyExtents[i]` and is silent on an advancing row's presence or placement; and
`pinnedLiteralsInRange`'s docstring appeal to "the checked output/context shapes" has no referent at
base, since `baseBlockContextNotEmpty` forces the base context shape empty (now measured, S16).
**The false justification is no longer quoted approvingly** — G7 now says which half of that docstring
sentence is accurate and which is false in this phase. B1-F2's cell scope is restated as **10 cells,
not 6**, and its own text now carries the worker-level consequence worked out rather than argued.

**Important 2 — forecast presented as measurement, fixed.** §B1.2's header no longer says "all
measured here"; it says facts 1 and 3 are measured and fact 2 is a conditional B2 must test. Fact 2 is
rewritten as `[CONDITIONAL — not measured; no strided constructor exists to measure]`, with the design
assumption named explicitly ("*if* B2's strided branch is not gated on `contextWidth` — which nothing
in the current code forces either way, and which is a design choice B2 owns"). I kept the mechanism,
since the review independently re-derived it and confirmed the substance, and added the smallest
exhibiting shape plus a sentence making **B2's first obligation** the gating decision and the
construction either way — "carried forward as the test to run", not as a finding. The report's §5
mirrors this.

**Important 3 — "solely" was wrong, fixed.** B1-F2 now names **two independent barriers**: barrier 1
is `checkWrites`' `if isBase then 0` (governs every plan); barrier 2 is `Compile.lean`'s base-write
construction loop, which can emit only an all-zero coefficient row with the literal as bias
(`.iterAt`) or a single `1` with bias `0` (`.free`/`.freeNorm`), and has **no arm** producing
coefficient `1` together with bias `1` — so a compiled base write could not carry an advancing row
even at nonzero `contextWidth`. A new subsection, **"Where barrier 2 disappears"**, makes the forward
connection the earlier draft left implicit: the same loop's `| .iterNext _ | .affine _ =>` arm is what
B2 must lower for affine LHS writes, and **the moment it gets a real lowering, barrier 2 is gone for
compiled programs and barrier 1 becomes the whole defence.** B1-F6 now points at that subsection, and
the call-site sweep's "three known instances" entry 1 no longer says "sole".

## Accuracy items

| # | Item | Fix |
|---|---|---|
| 1 | B1-F1's verification narrative did not reproduce | Re-ran both greps and restated the trail from observation. Pass 1 gives **19** files in my run; I say so, and add that the count is sensitive to directories/globs and is *not* the load-bearing part. Pass 2's intersection is now a **6-row table**, each file classified once and correctly: two presuppose (both quoted), two prose-only (`wave_f_scanplan_proposal.md`, the nonlinearity-t1 plan), one is this audit's own plan, one is `Compile.lean` (source). The self-contradiction over `predicate_boolean_backend_parity.md` is gone; `Compile.lean` is no longer omitted; "this audit's own brief" is gone. Added that the two **declining** documents are absent from the intersection because neither contains `forbidden` — they came from a separate grep. |
| 2 | G2 closed by deferral to an open group | Split into **G2a** (18 cells, closed) and **G2b** (2 cells, R5 × cols 2–3, **OPEN**, folded into B1-F4), with the reason stated: a group cannot be closed by deferral to an open group. B1-F4's cell count is now **5**. |
| 3 | S6 and S13 never cited | Both cited. **S6** now appears in the sweep row for `writeRowKinds`, as the demonstration of what the "no rank guard at `Compile.lean`'s two sites" assumption buys — `getD` *manufactures* `.pinned 0` rows (`writeRowKinds 3 0` on one supplied row → `#[free 0, pinned 0, pinned 0]`) or silently drops them (`writeRowKinds 1 0` on three → `#[free 0]`). **S13** is a new paragraph after the sweep table showing all four standalone predicates **fail closed** off-contract. |
| 4 | Quotation and count slips | B1-F6 no longer attributes one pattern to both loops: it states the base arm is `\| .iterNext _ \| .affine _ =>` and the step arm `\| .iterAt .. \| .affine _ =>`, verified by grep, and notes `.affine` is what they share. B1-F9: "Four distinct extent conventions" → **"Five"**. Sweep: `WriteRowKind`'s signature positions **8 → 11**, enumerated (adding `classifyWriteRow`'s return, `checkWrites`' return, `checkWrites`' `rowsByState`), verified by grepping every `WriteRowKind` occurrence in production. §B1.4's intro and the report's §1/§3 counts updated to match. |
| 5 | R1 × col 4 `a` on the strength of an `.any` | Added legend mark **§** ("the mark holds for the row *class* but a sub-case inside the cell is unconstrained by this site"), applied to that one cell, and B1-F5 now opens by saying it is the finding the `§` points at and how to read the `a`. |
| 6 | Appendability narrower than claimed | §B1.2's append instructions now say B2 must also update the §B1.2 cell census **and** §B1.5's gate summary, that the latter sits *before* the append marker, and that editing it in place is expected — "the marker exists so B2's new prose lands after B1's, not to freeze B1's counts." |

## Verification of this round

- **Census re-verified mechanically** after every edit: 12 rows × 14 columns = 168 cells,
  `24 a / 16 b / 86 c / 18 — / 24 ▷` — unchanged, since Important 1 moved cells between *groups*, not
  between *letters*.
- **Group arithmetic re-verified mechanically**: 17 groups summing to 86; 9 closed / 71 cells;
  8 open / 15 cells; B1-F4 = 5 cells, B1-F2 = 10 cells. A script also cross-checked every group's
  declared cell count in §B1.3 against the expected value — no mismatches.
- **Stale-count sweep**: found and fixed two leftovers ("15 adjudication groups" → 17, "8 signature
  positions" → 11) plus five in the report.
- Fragment still has **no** `file:NNN` citations, exactly **one** append marker as its last line, and
  no document-level conclusion.
- One markdown defect found and fixed in passing: an unescaped `|` inside a code span in G6 was
  breaking that table row's cell count. A script now checks for unescaped pipes in table code spans;
  there are none.

## Residual concerns after this round

1. **B1-F10 still stands and is unchanged** — 10 of 16 `b` cells have no located test, and
   `stepWriteRowsOk`'s clause 2 remains the least-pinned clause in the file. Fix round 1 did not
   touch it; the review confirmed it independently.
2. **§B1.2 fact 2 is now a labelled conditional, which is honest but weaker as a handoff.** If the
   controller wants it to be a *measurement* before the Scatter slice starts, that requires adding a
   `strided` constructor — production code, out of scope for a findings-only audit. Flagging the
   tradeoff rather than resolving it unilaterally.
3. **B1-F9 remains deliberately unclosed** (whether a zero-extent scatter output is rejected further
   down the scatter path is B2's territory). Unchanged from the initial report.

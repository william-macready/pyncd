# Axis B — write-geometry predicate surface

Findings-only audit of the checked-plan write-geometry predicates, taken at `267976e` with a green
build (`lake build`, **8660 jobs**) [built]. No production code was changed.

Evidence tags: `[built]` = whole-project build, `[read]` = identifier inspected, `[snippet]` = a
construction spike with observed output. Two spike files, each committed with its captured output
alongside this fragment in `axis-b-spikes/`, mirroring Task A's layout:

- `AxisBWriteGeometryProbe.lean` (+ `.output.txt`) — probes **S1–S13**
- `AxisBBaseBoundaryProbe.lean` (+ `.output.txt`) — probes **S14–S16** (S16 added in fix round 1)

To re-run, copy both into `leanncd/spikes/` (gitignored except `BrNF.lean`, so the working copies are
not tracked there) and run `lake env lean spikes/<file>.lean` from `leanncd/`. Neither is in
`lakefile.toml` or any default build target. Note for whoever re-runs them: they import
`LeanNCD.Eval.Plan.Scan` rather than the `LeanNCD` umbrella *deliberately* — `LeanNCD/DSL/Syntax.lean`
declares `"bias"` as a syntax token, which makes `{ coeffs := …, bias := … }` a parse error in any
file that imports the umbrella [snippet].

---

## B1.1 — The inherited "F4 seven-predicate table" does not exist

**Finding B1-F1 (process; stale inherited obligation).** There is no required/forbidden/ignored table
over the write-geometry predicates anywhere in the repo.

Verification trail, re-run and restated in fix round 2 (the previous two narratives did not
reproduce). **Pass 1** — the exact commands, both run from the repository root, differing only in
case sensitivity:

```text
grep -rl  --include='*.md' --include='*.lean' forbidden papers/ docs/ leanncd/docs/ leanncd/experiments/ leanncd/LeanNCD/   → 19 files
grep -ril --include='*.md' --include='*.lean' forbidden papers/ docs/ leanncd/docs/ leanncd/experiments/ leanncd/LeanNCD/   → 20 files
```

**Case sensitivity is the real instability in this trail**, and it is the reason two earlier drafts
failed to reproduce: exactly one file carries the word capitalised as "Forbidden" and is therefore
invisible to the case-sensitive form — `leanncd/docs/superpowers/plans/2026-08-20-thread-4-nonlinearity.md`,
the last row of the table below. (A reviewer running these same two commands observed 18 and 19
rather than 19 and 20; the one-file difference in the *baseline* is a file that does not survive
pass 2, so it does not move the intersection. The baseline count is the environment-sensitive
number; the intersection is not.)

**Pass 2** — intersecting each pass-1 result with files that also mention any of
`classifyWriteRow`, `baseWriteRowsOk`, `stepWriteRowsOk`, `freeExtentsAgree`,
`pinnedLiteralsInRange`, `writesCollide` gives **6** files from the case-sensitive list and **7**
from the case-insensitive one — the same 6 plus the capitalised file. All 7 were opened and read
[snippet]:

| File | What it is |
|---|---|
| `papers/boolean_predicate_output_evalplan.md` | **presupposes** the artifact (Task 4.4, quoted below) |
| `papers/predicate_boolean_backend_parity.md` | **presupposes** the artifact (§9.4, quoted below) |
| `papers/wave_f_scanplan_proposal.md` | prose only; its sole `forbidden` hit is a cross-reference to "its §4.8 forbidden list" |
| `leanncd/docs/superpowers/plans/2026-08-26-nonlinearity-t1-logical-schedule.md` | prose only ("same shape as `baseWriteRowsOk` in Wave F F4") |
| `docs/superpowers/plans/2026-09-06-pre-scatter-backend-audit.md` | this audit's own plan |
| `leanncd/LeanNCD/Eval/Plan/Compile.lean` | source, not a document |
| `leanncd/docs/superpowers/plans/2026-08-20-thread-4-nonlinearity.md` | **sibling case × class table, different predicate family** — reachable only case-insensitively. Does **not** falsify B1-F1: its axes are *case × {Pointwise, Axiswise} × class* over `checkPointwise`/`checkAxiswise`, so it has no row for any write-geometry predicate; it merely *cites* `baseWriteRowsOk`/`stepWriteRowsOk` as the defect family it argues it is not an instance of. See below |

So: no required/forbidden/ignored table over the **write-geometry** predicates in any of them. The
two **declining** documents quoted below appear in neither intersection, because neither contains the
word `forbidden` in any case — they were found by a separate grep for
`case-by-class|sibling audit|not required` [snippet].

What actually exists:

- A **completed** seven-row table in `papers/boolean_predicate_output_evalplan.md` whose axes are
  *assignment feature × {Dense checked plan, JAX render, JAX candidate evidence}* — mirrored in
  `leanncd/experiments/jax_bridge/README.md`. Not geometry predicates [read].
- An **instruction** in that same document (its Task 4.4 paragraph) reading: *"Task 4.4 must append a
  row to the existing write case-by-class audit. Re-read unchanged siblings `baseWriteRowsOk`,
  `stepWriteRowsOk`, `freeExtentsAgree`, `pinnedLiteralsInRange`, `writesCollide`, and their call
  sites. Record every cell as required, forbidden, or intentionally ignored."* The artifact it says to
  append to was never produced [read].
- **A second document presupposing the same artifact**, `papers/predicate_boolean_backend_parity.md`
  §9.4: *"Extend the existing write-predicate case table with block-output dtype versus state dtype.
  … If implementation touches `classifyWriteRow`, `baseWriteRowsOk`, `stepWriteRowsOk`, free extents,
  pins, or causality rows, stop and require the full write-geometry sibling audit rather than
  reviewing only the diff."* Same missing artifact, named differently [read].
- Two later documents that declined the obligation outright: `papers/max_min_aggregation.md` — *"no
  case × class sibling audit is required"* — and `papers/unary_factor_functions.md`, same wording
  [read].

So the "extend the existing table" instruction has been carried forward by at least two documents
against an artifact that does not exist, and twice explicitly declined.

**The closest existing precedent for the table in §B1.2, and why it is not that table.**
`2026-08-20-thread-4-nonlinearity.md` §4 is titled *"Case × class table —
`checkPointwise`/`checkAxiswise` geometry obligations"*, uses the Required/Forbidden vocabulary, and
introduces itself thus:

> Required per the slice-plan skill: a new geometry-checking predicate family gets this table as an
> explicit deliverable even though it is not an *instance* of the write-geometry defect family found
> four times in F3/F4 (free-extent, pinned-literal, write-map-rank, `stepWriteRowsOk`) — verified
> below, not assumed, since every `(c)` cell is a candidate instance *N+1* regardless of ancestry.

Its row 15 then discharges exactly that question — the nonlinearity family is not a fifth instance
because *"there is no second 'target' tensor addressed via an independently-boundable affine map the
way `commitWrite` (`Scan.lean`) has — this is the structural reason this family is not a 5th
instance … not merely an unexamined absence"* [read].

That is the same discipline §B1.2 applies, one predicate family over, and it is worth knowing three
things about it. First, it **confirms** B1-F1 rather than weakening it: it exists precisely because
the write-geometry table it defers to did not, and it never tabulates a write-geometry predicate.
Second, its `(c)`-cells-are-candidates-regardless-of-ancestry rule is the rule §B1.3 follows. Third,
it is the model for the appendability contract in §B1.2 — a case × class table whose classes stayed
stable while its rows grew.

The table in §B1.2 below is therefore built from scratch. It reuses only the JAX table's column
grammar and its closing gate sentence:

> Every forbidden cell needs a located test. No cell may be silently ignored.

---

## B1.2 — The write-geometry predicate table (current row kinds)

### Reading the table

A **row** is one write-map row *kind* sitting at one *dimension class* in one *phase*:

- kind ∈ {`pinned lit`, `free outputPos`, `advancing contextPos`} — the three current
  `WriteRowKind` constructors [read]
- dimension class ∈ {**adv** = the dimension is a member of `StateSlot.advancingDims`, **non-adv** =
  it is not}
- phase ∈ {**base** (`contextWidth = 0`), **step** (`contextWidth = advancingDims.size`)}

A **column** is one of the 14 audited sites. A **cell** answers: *does this site constrain such a
row?*

| Mark | Meaning |
|---|---|
| **a** | **required** — the site imposes a constraint on such a row and rejects the plan when it fails (including demanding the row's presence) |
| **b** | **forbidden** — the site rejects the plan when such a row is present at that dimension class in that phase |
| **c** | **silently ignored** — the site neither constrains nor rejects it; the row passes through unexamined. **Every `c` cell is a candidate gap** and is adjudicated in §B1.3 |
| **—** | the site is not reached in that phase (structural, not a classification) |
| **▷** | the site classifies *read* rows, a disjoint row vocabulary (see §B1.3, group G-READ) |
| **‡** | the mark holds only via an **unenforced call-site precondition** — a `c` cell in disguise; routed to the call-site sweep in §B1.4 |
| **§** | the mark holds for the row **class** but a sub-case inside the cell is unconstrained by this site. Do not read this `a` as stronger than it is — the named finding says which sub-case escapes |

Column keys: **1** `WriteRowKind` · **2** `classifyWriteRow` · **3** `writeRowKinds` ·
**4** `baseWriteRowsOk` · **5** `stepWriteRowsOk` · **6** `freeExtentsAgree` ·
**7** `pinnedLiteralsInRange` · **8** `writesCollide` · **9** `causalAdvancingRow` ·
**10** `stateReadCausal` · **11** `checkWrites` · **12** `checkScanPlan` · **13** `commitWrite` ·
**14** `runDenseScan`.

### The table

| # | row kind @ dim class @ phase | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| R1 | `pinned` @ adv @ base | c | c | c | **a**§ | — | c | **a** | **a** | ▷ | ▷ | **a** | **a** | c | c |
| R2 | `pinned` @ non-adv @ base | c | c | c | **c** | — | c | **a** | **a** | ▷ | ▷ | **a** | **a** | c | c |
| R3 | `pinned` @ adv @ step | c | c | c | — | **b** | c | **a** | — | ▷ | ▷ | **b** | **b** | c | c |
| R4 | `pinned` @ non-adv @ step | c | c | c | — | **b** | c | **a** | — | ▷ | ▷ | **b** | **b** | c | c |
| R5 | `free` @ adv @ base | c | c | c | **c** | — | **a** | c | c | ▷ | ▷ | **c** | **c** | c | c |
| R6 | `free` @ non-adv @ base | c | c | c | **a** | — | **a** | c | c | ▷ | ▷ | **a** | **a** | c | c |
| R7 | `free` @ adv @ step | c | c | c | — | **b** | **a** | c | — | ▷ | ▷ | **b** | **b** | c | c |
| R8 | `free` @ non-adv @ step | c | c | c | — | **a** | **a** | c | — | ▷ | ▷ | **a** | **a** | c | c |
| R9 | `advancing` @ adv @ base | c | **b**‡ | **b**‡ | **c**‡ | — | **c**‡ | **c**‡ | c‡ | ▷ | ▷ | **c**‡ | **c**‡ | c | c |
| R10 | `advancing` @ non-adv @ base | c | **b**‡ | **b**‡ | **c**‡ | — | **c**‡ | **c**‡ | c‡ | ▷ | ▷ | **c**‡ | **c**‡ | c | c |
| R11 | `advancing` @ adv @ step | c | c | c | — | **a** | c | c | — | ▷ | ▷ | **a** | **a** | c | c |
| R12 | `advancing` @ non-adv @ step | c | c | c | — | **b** | c | c | — | ▷ | ▷ | **b** | **b** | c | c |

### Cell census

168 cells (12 × 14): **24 a**, **16 b**, **86 c**, 18 —, 24 ▷.

**Updated by Task B2.** With the four appended `strided` rows R13–R16 (§B2.2) the table is
**224 cells (16 × 14): 24 a, 22 b, 122 c, 24 —, 32 ▷.** B2's four rows contribute 56 cells on their
own — **0 a, 6 b, 36 c, 6 —, 8 ▷** — and the absence of any `a` among them is itself a finding
(§B2.2, B2-F2): no audited site anywhere requires or demands the presence of a strided row.

**Reported divergence (the brief predicted ~40 adjudicable cells).** 86 `c` cells is a large
overshoot, and it is an artefact of the column list rather than of the code: three of the 14 columns
are *entirely* `c` by construction and account for 36 cells on their own — `WriteRowKind` (a closed
inductive cannot require or forbid anything), `commitWrite` (its own docstring states it "does NOT
call `inBoundsPerDim` before `flatIndex`: it performs no bounds recovery, trusting `checkScanPlan`"
[read]), and `runDenseScan` (validates the signature table and store arity, nothing per-row).
`classifyWriteRow` and `writeRowKinds` contribute 20 more, because both are structurally
dimension-class-blind. Excluding those five non-validating/blind columns leaves **30 `c` cells**
(4 in `baseWriteRowsOk`, 8 in `freeExtentsAgree`, 8 in `pinnedLiteralsInRange`, 4 in `writesCollide`,
3 each in `checkWrites` and `checkScanPlan`) — the same order as the prediction. The 86 collapse into
**17 adjudication groups** (§B1.3), so no group is closed by prose alone.

### How Task B2 appends a fourth row kind

The row axis is `kind × dim-class × phase` and the column axis is fixed. A fourth kind
(`strided`) appends **exactly four rows at the bottom** — `strided @ adv @ base`,
`strided @ non-adv @ base`, `strided @ adv @ step`, `strided @ non-adv @ step` — as R13–R16, with no
change to any column header, to any existing row, or to the legend.

**Two places outside the table itself must also be updated, and one of them sits BEFORE the append
marker**: the §B1.2 cell census (currently 168 cells / 24 a / 16 b / 86 c / 18 — / 24 ▷) and §B1.5's
gate summary, which restates the 16/86 split. Editing §B1.5 in place is expected and is not a
violation of the append boundary; the marker exists so B2's *new prose* lands after B1's, not to
freeze B1's counts.

Three facts B2 will need. **Facts 1 and 3 are measured here; fact 2 is a conditional forecast that
B2 must test, not inherit.**

1. **[measured] `classifyWriteRow` is the single chokepoint.** Every coefficient other than `1`, and
   every bias other than `0`/`1`, is `none` today: `classifyWriteRow 0 #[2] 0`,
   `classifyWriteRow 0 #[1,1] 0`, `classifyWriteRow 2 #[2,0] 1`, `classifyWriteRow 0 #[1] 5` all
   return `none` [snippet, S12]. A `strided` kind must be admitted there or nowhere.
2. **[CONDITIONAL — not measured; no `strided` constructor exists to measure]** *If* B2's strided
   branch of `classifyWriteRow` is **not** gated on `contextWidth` — which nothing in the current
   code forces either way, and which is a design choice B2 owns — then a strided row becomes
   emittable at **base**, unlike `advancing`. In that case: `baseWriteRowsOk`'s clause-2 `filterMap`
   is still the verbatim defect-instance-4 shape (B1-F2), so it would silently DROP the row from the
   positional cover; `freeExtentsAgree` matches only `.free` and `pinnedLiteralsInRange` only
   `.pinned`, so neither would look at it; and `commitWrite`'s `c·x + b` would then be bounded by
   nothing. The smallest shape that would exhibit it: rank-3 state, `advancingDims := #[0]`, dim0
   `.pinned 0`, dim1 strided, dim2 `.free 0`, `outputShapeSize = 1` — which passes clauses 1–3 today
   for any dim1 kind that is `some`, as G16's `#[some (.pinned 0), some (.advancing 0), some
   (.free 0)]` construction demonstrates for the *advancing* kind at exactly those parameters
   [snippet, S16].

   **B2's first obligation is therefore to decide and record whether the strided branch is
   `contextWidth`-gated, and to build the construction either way** — if gated, the cell is latent
   like B1-F2 and the gate is a third unenforced precondition; if not gated, it is live, and this is
   the five-times defect recurring for the sixth time. Do not carry this paragraph forward as a
   finding; carry it forward as the test to run.
3. **[measured] `writesCollide`'s catch-all is conservative for a new kind.** `| _, _ => false` means
   a `strided` row can never separate two writes, so two strided base writes to one state would
   always be reported as colliding [snippet, S5]. That over-rejects rather than under-rejects — safe,
   but it makes strided-plus-strided base initialization inexpressible.

---

## B1.3 — Adjudication of every `c` cell

Order used throughout, per the audit's own rule: (1) name the catching site and quote its clause;
(2) if soundness rests on a caller rather than the predicate's text, mark `‡` and route to §B1.4;
(3) build the malformed `RawScanPlan`, run `checkScanPlan`, then `runDenseScan`, and record the
observed value verbatim. **No write-path cell below is closed as "backstopped by `gatherFactor`'s
`inBoundsPerDim`".**

| Group | Cells | Site × rows | Verdict |
|---|---|---|---|
| G1 | 12 | col 1 × R1–R12 | Closed structurally. `WriteRowKind` is a closed inductive `deriving DecidableEq, BEq` [read]; a type cannot require or forbid. Its derived structural equality is what makes `baseWriteRowsOk`'s `rows.getD d none == some (.pinned 0)` and `stepWriteRowsOk`'s `== some (.advancing i)` sound, so a payload-carrying fourth constructor inherits correct equality for free. |
| G2a | 18 | cols 2–3 × R1–R4, R6–R8, R11, R12 | Closed to G3, G6, G7, G8. Both functions are **dimension-class-blind by construction**: `classifyWriteRow`'s signature is `(contextWidth : Nat) (coeffRow : Array Int) (bias : Int)` — it receives no `advancingDims` and no dimension index at all [read]. The entire dim-class axis is therefore `c` at this column pair, which is precisely why every downstream site re-derives it. |
| **G2b** | 2 | cols 2–3 × R5 (`free` @ adv @ base) | **OPEN.** Same dimension-class blindness as G2a, but its only downstream catcher is `baseWriteRowsOk`, whose own cell for this row is G4 — itself open. A group cannot be closed by deferral to an open group, so these two cells are open too, folded into **Finding B1-F4**. |
| G3 | 1 | col 4 × R2 (`pinned` @ non-adv @ base) | Closed by `pinnedLiteralsInRange`: *"`some (.pinned lit) => 0 ≤ lit && lit.toNat < stateShape.getD d 0`"*. Confirmed live: `baseWriteRowsOk #[0] 0 #[some (.pinned 0), some (.pinned 99)] = true` [snippet, S2], and `pinnedLiteralsInRange #[3,3] #[some (.pinned 0), some (.pinned 5)] = false`, `… (.pinned (-1))] = false` [snippet, S4]. Pinning a non-advancing dimension is intended — `ScanTest`'s `pointWrite`/`outOfRangePointWrite` fixtures exercise both directions [read]. |
| **G4** | 1 | col 4 × R5 (`free` @ adv @ base) | **OPEN — Finding B1-F4.** See below. |
| **G5** | 2 | col 4 × R9, R10 (`advancing` @ base) | **`c`‡ — Finding B1-F2, candidate gap 1 CONFIRMED as latent.** See below. |
| G6 | 6 | col 6 × R1–R4, R11, R12 | Closed by kind partition. `freeExtentsAgree`'s `\| _ => true` arm ignores `.pinned` and `.advancing` — `freeExtentsAgree #[3,3] #[9] #[some (.pinned 0), some (.advancing 0)] = true` even at a wildly wrong output extent [snippet, S4]. Pinned rows are caught by `pinnedLiteralsInRange` (G3). Advancing rows at **step** are caught by `stepWriteRowsOk`'s clause 2 (`rows.getD d none == some (.advancing i)` at every advancing dimension) and clause 3 (every other dimension must be `.free`), plus `checkScanPlan`'s `advancingSizeMismatch`, which *"relates `stateShape[advancingDims[i]]` to `historyExtents[i]`"* [read]. **Advancing rows at BASE are NOT covered by that argument and are excluded from this group — see G16.** |
| G7 | 6 | col 7 × R5–R8, R11, R12 | Closed by the mirror-image partition. `pinnedLiteralsInRange #[3,3] #[some (.free 7), some (.advancing 9)] = true` [snippet, S4]. Free rows → `freeExtentsAgree` (G6's converse); advancing rows at **step** → as in G6. Its docstring's justification — *"`.free`/`.advancing` rows are vacuously fine (their range is already bounded by the checked output/context shapes elsewhere)"* — is accurate for the step phase and for `.free` rows generally, but **is false for an advancing row at base**, where there is no context shape at all; those cells are excluded from this group — see G16. |
| G8 | 2 | col 8 × R5, R6 (`free` @ base) | Closed as **documented and pinned intentional**. `writesCollide`'s docstring: *"`.free`/`.advancing` always range over their full domain and can never exclude the other write. This single rule is what makes 'two full free-axis faces never disjoint' (proposal §5.1) a structural consequence rather than an asserted claim"* [read]. Pinned by green `#guard`s in `ScanTest.lean`: `writesCollide faceRows pointRows == false`, `writesCollide faceRows colFaceRows == true` [read]. Confirmed: `writesCollide #[some (.free 0)] #[some (.free 0)] = true` [snippet, S5]. |
| G9 | 2 | col 8 × R9, R10 (`advancing` @ base) | `c`‡, closed as **vacuous today**. `writesCollide` is called only inside `checkWrites`' `if isBase then` branch and inside `Compile.lean`'s base-write loop [read], and no base row can be `.advancing` (G5). So the catch-all's treatment of advancing rows is unreachable in production — see §B1.2's B2 note 3 for why that stops being true with a fourth kind. |
| G10 | 1 | col 11 × R5 | Escalation of G4 — same finding, surviving to the orchestrator. |
| G11 | 2 | col 11 × R9, R10 | Escalation of G5. |
| G12 | 1 | col 12 × R5 | Escalation of G4, surviving to the **top-level** checked entry. `checkScanPlan` adds `advancingDimOutOfRange`, `duplicateAdvancingDim`, `advancingDimCountMismatch`, `advancingSizeMismatch` and the policy gates [read] — **none of which changes any cell in the table**. That is itself the point: the three base `c` cells reach the public entry point unchanged. |
| G13 | 2 | col 12 × R9, R10 | Escalation of G5, same remark. |
| G14 | 12 | col 13 × R1–R12 | Closed by design, with one docstring gap (Finding B1-F7). `commitWrite`'s docstring is a row-by-row soundness argument with **one bullet per current constructor** — `.free p`, `.advancing i`, `.pinned lit`, three bullets for three constructors, so the argument is complete over the constructor surface [read]. Its stated premise (`out.shape` runtime vs. `block.tensorSigs[…].shape` declared, resting on `checkNonlinIO`'s shape equality) is already flagged there as load-bearing. |
| G15 | 12 | col 14 × R1–R12 | Closed by evidence-carrying construction. `CheckedScanPlan` has `private mk ::`, so the only way to obtain one is `checkScanPlan`; `runDenseScan` then reads state shapes from `c.sigs` and rejects a differing caller table (`signatureContextMismatch`) and a differing store length (`storeArityMismatch`) before allocating [read]. No per-row obligation belongs here. |
| **G16** | 4 | cols 6–7 × R9, R10 (`advancing` @ base, both value predicates) | **OPEN — `c`‡ latent, folded into Finding B1-F2.** These four cells were initially misclosed inside G6/G7 by citing a catcher that cannot fire in this phase, which is exactly the failure this audit exists to prevent. `stepWriteRowsOk` is marked **—** at base in the table above, so its clauses 2 and 3 catch nothing here; `advancingSizeMismatch` relates `stateShape[advancingDims[i]]` to `historyExtents[i]` and says nothing about an advancing row's presence or placement at base; and `pinnedLiteralsInRange`'s docstring appeal to *"the checked output/context shapes"* has no referent, because `checkScanPlan` forces `raw.baseBlock.contextShape == #[]` — verified: `S16 (non-empty base block contextShape): checkScanPlan REJECTED: … baseBlockContextNotEmpty #[2]` [snippet, S16]. Both predicates pass such a row at **any** extents: on `#[some (.pinned 0), some (.advancing 0), some (.free 0)]`, `(freeExtentsAgree #[1,3,3] #[3], pinnedLiteralsInRange #[1,3,3], freeExtentsAgree #[1,1,3] #[3], pinnedLiteralsInRange #[1,1,3])` → `(true, true, true, true)` [snippet, S16]. Held up by the same two barriers as G5 — see B1-F2. |

The 17 groups above account for all 86 `c` cells: G1 12, G2a 18, G2b 2, G3 1, G4 1, G5 2, G6 6, G7 6,
G8 2, G9 2, G10 1, G11 2, G12 1, G13 2, G14 12, G15 12, G16 4.

- **9 groups closed, 71 cells**: G1, G2a, G3, G6, G7, G8, G9, G14, G15.
- **8 groups open, 15 cells**, collapsing to two findings:
  - **B1-F4** (`free` at an advancing dim in a base write) — G2b 2, G4 1, G10 1, G12 1 = **5 cells**;
  - **B1-F2** (`advancing` at base) — G5 2, G11 2, G13 2, G16 4 = **10 cells**.

**Updated by Task B2.** B2 appends **14 further groups, G17–G30 (§B2.3)**, covering its 36 new `c`
cells: G17 4, G18 4, G19 4, G20 2, G21 2, G22 2, G23 2, G24 2, G25 2, G26 2, G27 2, G28 2, G29 2,
G30 4. Of those, **7 groups / 20 cells are closed** (G17, G18, G21, G23, G25, G28, G30) and
**7 groups / 16 cells are open** (G19, G20, G22, G24, G26, G27, G29), collapsing to a single new
finding **B2-F1**. Combined totals across both tasks: **31 groups / 122 `c` cells — 16 groups /
91 cells closed, 15 groups / 31 cells open**, collapsing to three findings: **B1-F2** (10 cells),
**B1-F4** (5 cells), **B2-F1** (16 cells).

One further group is listed for completeness but is **not** a `c` group, because its 24 cells are
marked ▷ rather than `c`:

| Group | Cells | Site × rows | Verdict |
|---|---|---|---|
| G-READ | 24 (▷, not `c`) | cols 9–10 × R1–R12 | Not write-row cells. `causalAdvancingRow` and `stateReadCausal` classify a `ReadPlan`'s coefficient rows, a disjoint vocabulary. Their own `c` cell — `stateReadCausal` imposes no obligation on a read's **non-advancing** dimensions, per its docstring *"non-advancing dimensions are ordinary reads and carry no causality obligation"* [read] — **is** a read-path cell and **is** legitimately closed as backstopped by `gatherFactor`'s `inBoundsPerDim`. It is pinned by `ScanTest`'s `nonAdvancingScan` / `stepBlockGjWild` fixture pair, which asserts `checkScanPlan` still accepts a scan whose only irregularity is a non-advancing read [read]. |

### Finding B1-F2 — candidate gap 1: `baseWriteRowsOk`, CONFIRMED as latent, not live

`baseWriteRowsOk` still carries the verbatim defect-instance-4 shape:

```
((rows.toList.filterMap (fun r => match r with | some (.free p) => some p | _ => none))
  == List.range outputShapeSize)
```

It **admits** a hand-built `.advancing` row at both dimension classes:

- `baseWriteRowsOk #[0, 1] 0 #[some (.pinned 0), some (.advancing 0)]` → `true`
- `baseWriteRowsOk #[0]    0 #[some (.pinned 0), some (.advancing 0)]` → `true` [snippet, S2]

and nothing downstream examines such a row: `writesCollide`'s catch-all is `false` (G9), and **both
value predicates pass it at any extents whatsoever** (G16). On
`#[some (.pinned 0), some (.advancing 0), some (.free 0)]` — a rank-3 state, dim0 satisfying clause 3,
dim1 carrying the advancing row, dim2 the free cover — `baseWriteRowsOk` returns `true` at **both**
dimension classes (`baseWriteRowsOk #[0,1] 1 …` and `baseWriteRowsOk #[0] 1 …`, i.e. rows R9 and R10),
and `(freeExtentsAgree #[1,3,3] #[3], pinnedLiteralsInRange #[1,3,3],
freeExtentsAgree #[1,1,3] #[3], pinnedLiteralsInRange #[1,1,3])` → `(true, true, true, true)`
[snippet, S16].

**The consequence at the worker, worked out rather than argued.** At base `commitWrite` is called with
`ctx = []`, so `iter = oc` and `applyAffine` yields `oc[p] + 1` for the advancing row. For the map
those rows come from (`coeffs := #[#[0], #[1], #[1]]`, `bias := #[0, 1, 0]`) over an output of shape
`[3]`, the three coordinates are `([0,1,0], [0,2,1], [0,3,2])`; against a `[1,3,3]` state
`inBoundsPerDim` gives `(true, true, false)`, and `flatIndex` gives the addresses `(3, 7, 11)` on a
9-element store [snippet, S16]. `commitWrite` calls no `inBoundsPerDim`, so that is: two silent writes
into cells belonging to other coordinates, then an out-of-range `Array.set!` — the verbatim F4 failure
signature. **There is no base-phase bound to appeal to**: `checkScanPlan` forces
`raw.baseBlock.contextShape == #[]`, confirmed by `S16 (non-empty base block contextShape):
checkScanPlan REJECTED: … baseBlockContextNotEmpty #[2]` [snippet, S16].

**Two independent barriers hold it up today — not one.** The earlier draft of this fragment said
"solely" of the first; that was wrong, and the correction matters forward.

*Barrier 1 — `checkWrites`' one expression:*

```
let contextWidth := if isBase then 0 else st.advancingDims.size
```

which makes `classifyWriteRow`'s advancing branch — `if c == 1 && p < contextWidth && bias == 1` —
unsatisfiable, since no `p : Nat` is `< 0`. Measured:
`(classifyWriteRow 0 #[1] 1, classifyWriteRow 0 #[1,0] 1, classifyWriteRow 0 #[0,1] 1)` →
`(none, none, none)`, while the same rows at width 2 give
`(some (.advancing 0), some (.advancing 1))` [snippet, S1]. This barrier governs **every** plan,
hand-built or compiled.

*Barrier 2 — `Compile.lean`'s base-write construction loop, for compiled programs only.* That loop
can emit exactly two row shapes: an all-zero coefficient row with the literal as bias (from
`.iterAt _ lit`), or a single `1` at position `freeSeen` with bias `0` (from `.free`/`.freeNorm`)
[read]. The advancing shape is coefficient `1` **together with** bias `1`, which the loop has no arm
that produces — so a compiled base write could not carry an advancing row even if `contextWidth` were
nonzero. This barrier is independent of barrier 1 and makes "latent" more robust for source programs
than for hand-built ones.

**Where barrier 2 disappears.** That same loop's remaining arm is
`| .iterNext _ | .affine _ =>`, which currently throws `CapabilityError.unsupportedLhsSlot` [read].
`.affine` is precisely the slot Task B2's affine LHS writes must lower. **The moment B2 gives that arm
a real lowering, barrier 2 is gone for compiled programs, and barrier 1 — a single `if isBase then 0`
whose contract is stated only in two docstrings — becomes the whole defence.** B1-F6 notes the arm;
this is the connection to B1-F2 that the earlier draft left implicit.

**Construction attempt through the real entry (step 3 of the adjudication order).** A base write whose
dim-0 row is the advancing shape (`coeffs := #[#[1], #[1]]`, `bias := #[1, 0]`) on a `[3,3]` state:
`writeRowKinds 2 0` returns `#[none, some (.free 0)]`, and clause 1 (`rows.all Option.isSome`) fires:

```
S11 (advancing-shaped base row): checkScanPlan REJECTED:
LeanNCD.Eval.Plan.ScanPlanError.writeGeometryNotAdmitted true 0
```

[snippet, S11]. So these cells are **`c`‡ — latent, not live**: unreachable today, and unreachable
only because of unenforced call-site values. The precondition is *stated* in `classifyWriteRow`'s and
`writeRowKinds`' docstrings (*"`contextWidth` is `0` for a base write"*) but is enforced by no
signature and no check, and `baseWriteRowsOk`'s own docstring does not mention it at all [read].

**Cell scope: 10 cells, not 6.** This finding covers rows R9 and R10 across columns 4, 6, 7, 11 and
12 — groups G5 (2), G11 (2), G13 (2) and G16 (4). The four G16 cells (both value predicates at base)
were added in fix round 1; the earlier draft misclosed them inside G6/G7 by citing `stepWriteRowsOk`
and `advancingSizeMismatch`, neither of which operates in the base phase. This is the
highest-confidence item in Axis B and it is the exact cell Task B2's new row kind may step into
(§B1.2, note 2).

### Finding B1-F3 — candidate gap 2: coeff-row WIDTH is unchecked but provably irrelevant (REFUTED)

Confirmed by reading: `checkWrites` guards the two **outer** dimensions only —
`writeCoeffRankMismatch` on `w.map.coeffs.size` and `writeBiasRankMismatch` on `w.map.bias.size`, both
against `stateShape.size` — and nothing anywhere compares an individual coefficient row's **length**
against `contextWidth + outputShape.size` [read].

It is nonetheless not a gap, for a three-step reason:

1. `classifyWriteRow` admits a non-pinned row only when it has **exactly one** nonzero coefficient
   **equal to 1**, and that coefficient's *index into the row* is the domain position `p` [read].
2. That position is bounded into the real domain by the geometry predicates themselves:
   `baseWriteRowsOk`'s clause 2 and `stepWriteRowsOk`'s clause 4 both require the free positions to
   equal `List.range outputShapeSize` exactly, and `stepWriteRowsOk`'s clause 2 requires an advancing
   row's position to be its own context index. So a free row's `p ∈ [contextWidth, contextWidth +
   outputShapeSize)` and an advancing row's `p ∈ [0, contextWidth)`.
3. `applyAffine`'s `(row.toList.zip iter)` drops exactly the coefficients at indices `≥ iter.length`,
   and by (1)+(2) every one of those is zero.

Measured at every step:

- `classifyWriteRow 1 #[1,0,0,0] 1` → `some (.advancing 0)`; `classifyWriteRow 1 #[0,0,0,1] 0` →
  `some (.free 2)` — over-wide rows *are* classified [snippet, S7].
- All three geometry predicates reject that out-of-domain free position:
  `(stepWriteRowsOk #[0] 0 #[some (.free 2)], stepWriteRowsOk #[0] 1 #[some (.advancing 0), some
  (.free 2)], baseWriteRowsOk #[0] 1 #[some (.pinned 0), some (.free 2)])` → `(false, false, false)`
  [snippet, S7].
- `applyAffine` truncation is a no-op: `applyAffine ⟨#[#[1,0,0,0]], #[1]⟩ [2]` → `[3]` and
  `applyAffine ⟨#[#[1]], #[1]⟩ [2,5,7]` → `[3]` [snippet, S7].
- Full-plan constructions agree byte-for-byte. A base write with 4-wide rows where the domain is
  1 wide, and a step write with 5-wide rows where the domain is 2 wide, both run and produce output
  identical to the correctly-widthed plan:
  - `S9 (over-wide base coeff rows): checkScanPlan .ok; dp = #[1,2,3, 0,1,1, 0,1,1]`
  - `S10 (over-wide step coeff rows): checkScanPlan .ok; dp = #[1,2,3, 0,1,1, 0,1,1]` [snippet]
- Moving the single `1` **outside** the real domain *is* rejected:
  `S9b (base coeff 1 outside the real domain): checkScanPlan REJECTED: … writeGeometryNotAdmitted
  true 0` [snippet].

**The free-position cover is the width guard.** The refutation carries one caveat that is not new:
step 3 relies on the declared-vs-runtime output-shape agreement that `commitWrite`'s own docstring
already names as load-bearing (`checkNonlinIO`'s shape equality plus every
`PointwiseFn.apply`/`AxiswiseFn.apply` arm being shape-preserving) [read]. A refuted candidate is a
valid audit result; recorded as refuted, with no remediation proposed.

### Finding B1-F4 — a `free` row may sit at an ADVANCING dimension in a base write (OPEN, memory-safe)

`baseWriteRowsOk` clause 2's `filterMap` records a free row's **position** and discards its
**dimension**; clause 3 demands `.pinned 0` at only *some* advancing dimension. With two advancing
dimensions a base write may therefore cover the entire extent of the second one.

Constructed and run end-to-end: state `dp` shape `#[3,3]`, `advancingDims := #[0,1]`,
`historyExtents := #[3,3]`, base write `dp[0, c] := ROWFACE[c]` (`coeffs := #[#[0],#[1]]`,
`bias := #[0,0]`), step write `dp[r+1, c+1] := T[r,c]`:

```
rows = #[some (.pinned 0), some (.free 0)]
baseWriteRowsOk #[0,1] 1 rows = true
freeExtentsAgree #[3,3] #[3] rows = true
S8 (free row at advancing dim, base): checkScanPlan .ok;
  dp = #[1.000000, 2.000000, 3.000000, 0.000000, 1.000000, 1.000000, 0.000000, 1.000000, 1.000000]
```

[snippet, S8]. **Memory-safe** — the free row's extent is bounded by `freeExtentsAgree`, which
returns `false` at any other extent (`freeExtentsAgree #[3,3] #[9] … = false`, [snippet, S4]) — and
the result is exactly what `ScanBoundaryPolicy.zeroThenBaseOverlay` specifies (*"How complete state
histories are initialized before base writes apply"* [read]): row 0 comes from the base overlay,
column 0 was never written and stays zero, the interior comes from the step block.

So this cell is **not closed** as backstopped (it is a write predicate) but **is** closed as
consistent with the declared boundary policy. What it lacks is a pin: `ScanTest.lean` exercises free
base faces only at *non-advancing* dimensions — `baseWriteRowsOk #[0] 1 faceRows` and
`baseWriteRowsOk #[1] 1 colFaceRows` [read] — so no fixture would notice if a future change started
rejecting or mis-executing this shape. Recommendation is a located pin, not a code change.

### Finding B1-F5 — base writes need touch the lower boundary of only ONE advancing dimension (OPEN, memory-safe)

**This is the finding the `§` mark on R1 × col 4 points at.** That cell is `a` for the row *class* —
`baseWriteRowsOk` genuinely demands a `.pinned 0` row at an advancing dimension and rejects its
absence — but the sub-case of *every other* advancing dimension's pinned row is unconstrained by this
site, range-checked only downstream by `pinnedLiteralsInRange`. Read the `a` as "required, but not of
every such row".

`baseWriteRowsOk`'s clause 3 is `advancingDims.any (fun d => rows.getD d none == some (.pinned 0))`.
Its docstring glosses this as *"at least one advancing dimension must be pinned to literal `0`
(touches the lower boundary)"* [read]. With more than one advancing axis that gloss is weaker than it
reads: every *other* advancing dimension's pinned literal need only be **in range**.

```
rows = #[some (.pinned 0), some (.pinned 1)]   -- dp[0,1] on a [3,3] state, advancingDims #[0,1]
baseWriteRowsOk #[0,1] 0 rows = true;  pinnedLiteralsInRange #[3,3] rows = true
S14  (base write off the boundary of advancing dim 1):  .ok; dp = #[0,7,0, 0,1,1, 0,1,1]
S14b (base write pinned to the FAR end of advancing dim 1): .ok; dp = #[0,0,7, 0,1,1, 0,1,1]
S14c (base write pinned OUT of range on advancing dim 1): REJECTED:
      ScanPlanError.writePinnedLiteralOutOfRange true 0 0 #[3, 3]
```

[snippet, S14]. Memory-safe, and the range boundary is exactly where `pinnedLiteralsInRange` puts it.
`Compile.lean`'s Phase 5 carries the **same** single-dimension rule (`baseWriteNotAtBoundary`), so a
source program inherits the same looseness — see B1-F6.

### Finding B1-F7 — `commitWrite`'s docstring is complete over constructors but STEP-scoped for `.advancing`

Treating the docstring as a predicate, per the audit's scope addition 2: it has one bullet per
current `WriteRowKind` constructor, so no row kind is missing an argument [read]. But the
`.advancing` bullet's argument is explicitly step-scoped — *"an `.advancing i` row is `ctx[i] + 1`,
with `ctx` from `mixedRadixUnrank c.stepExtents` and `stepExtents = historyExtents - 1`"* — and says
nothing about the base phase, where `commitWrite` is called with `ctx = []`. That is B1-F2's
unenforced precondition surfacing a third time: stated in `classifyWriteRow`'s docstring, absent from
`baseWriteRowsOk`'s, absent here.

---

## B1.4 — Call-site sweep

19 production call sites across the 14 audited identifiers, plus the type's own 11 signature
positions — close to the brief's ~21 estimate. Test-suite call sites are noted where they are the
only thing pinning a behavior, but are not counted. For each: how `contextWidth`, `stateRank`, and
`rows` are derived; the invariant assumed but absent from the callee's signature; and whether a new
row kind changes the answer.

| Site | Caller(s) | `contextWidth` / `stateRank` / `rows` derivation | Invariant assumed, absent from the signature | New row kind changes it? |
|---|---|---|---|---|
| `WriteRowKind` | **11** production signature positions: `classifyWriteRow`'s `Option WriteRowKind` return; `writeRowKinds`' `Array (Option WriteRowKind)` return; the `rows` parameter of `baseWriteRowsOk`, `stepWriteRowsOk`, `freeExtentsAgree` and `pinnedLiteralsInRange`; `writesCollide`'s `rowsA` and `rowsB`; `checkWrites`' return type and its `rowsByState` annotation; `Compile.lean`'s `mine` annotation | n/a | Derived `DecidableEq`/`BEq` is relied on by two `==` comparisons against literal constructors | **Yes** — 14 columns of new obligations |
| `classifyWriteRow` | `writeRowKinds` (sole caller) | `contextWidth` passed through verbatim | **That `contextWidth = 0` means "base".** The function has no way to say so and no `advancingDims` at all | **Yes** — the sole chokepoint |
| `writeRowKinds` | `checkWrites`; `Compile.lean` ×2 (base-boundary loop; base-collision `mine` builder) | `checkWrites`: `stateShape.size` from `sigs[st.destSlot].shape`, `contextWidth` from `if isBase then 0 else st.advancingDims.size`. **`Compile.lean`: `stateShape.size` from `stateShapes[…]` (its own Phase 2 derivation) and `contextWidth` a hardcoded literal `0` at both sites** | `coeffs`/`bias` already length-checked against `stateRank` — true at the `checkWrites` site (the two rank guards run immediately before) and **assumed by construction** at both `Compile.lean` sites, which run no rank guard. What that assumption buys is visible when it fails: `getD` **manufactures** rows rather than rejecting. `writeRowKinds 3 0` on a write supplying one coefficient row returns `#[some (.free 0), some (.pinned 0), some (.pinned 0)]` — two `.pinned 0` rows invented from nothing — and `writeRowKinds 1 0` on a write supplying three drops rows 1–2 silently, returning `#[some (.free 0)]` [snippet, S6] | **Yes** |
| `baseWriteRowsOk` | `checkWrites` (`if isBase then` arm) — **sole caller** | `rows` from `writeRowKinds stateShape.size 0 w`; `advancingDims` from `st.advancingDims`; `outputShapeSize` from the **declared** `block.tensorSigs[w.outputSlot].shape.size` | **`contextWidth = 0`, hence no `.advancing` row can be present** — Finding B1-F2. `Compile.lean` does **not** call this function; it re-implements clause 3 only | **Yes** — §B1.2 note 2 |
| `stepWriteRowsOk` | `checkWrites` (`else` arm) — **sole caller** | as above with `contextWidth = st.advancingDims.size` | `advancingDims` in range and duplicate-free (established earlier, in `checkScanPlan`'s state loop, not here) | **Yes** — but this predicate is fully classified today (zero `c` cells), so a new kind needs one new clause, not a rewrite |
| `freeExtentsAgree` | `checkWrites` — **sole caller**; **no source-facing counterpart in `Compile.lean` at all** | `stateShape` from `sigs[st.destSlot].shape`; `outputShape` declared | Its docstring states it: *"At its only call site it runs AFTER `baseWriteRowsOk`/`stepWriteRowsOk` have admitted the geometry … so neither `getD` default is reachable there"* | No |
| `pinnedLiteralsInRange` | `checkWrites` — **sole caller**; re-implemented inline in `Compile.lean` | as above | same post-admission precondition as `freeExtentsAgree` | No |
| `writesCollide` | `checkWrites` (base pairwise loop); `Compile.lean` (base pairwise loop) | both arrays from `writeRowKinds` for the **same** state, so equal length | **Equal-length arrays.** `writesCollide` scans `List.range rowsA.size` and reads B via `getD d none`, so it is length-blind in both directions — see B1-F8 | **Yes** — §B1.2 note 3 |
| `causalAdvancingRow` | `stateReadCausal` (sole caller) | `row`/`bias` from `f.map` via `getD … #[]`/`getD … 0` | Read-row vocabulary; `advancingDims[i]` in range for the read's own map | No |
| `stateReadCausal` | `checkScanPlan` (causality loop); `Compile.lean` (Phase 5) | `advancingDims` from the state; `contextPos` from the term | `advancingDims.size == contextPos.size` is checked **inside** the predicate (its first conjunct) — unusually, not assumed | No |
| `checkWrites` | `checkScanPlan` ×2 (`… raw.baseBlock raw.baseWrites … true` and `… raw.stepBlock raw.stepWrites … false`) | `isBase` is the discriminator that produces `contextWidth` | Block already checked (`checkPlanBlock` runs before); state loop already validated dims and dtypes | **Yes** |
| `checkScanPlan` | `EvalPlan.lean`'s `checkPlan`, `.scan` arm — **sole production caller** | `sigs := raw.tensorSigs`, the outer graph's own table | None material: it validates its own inputs and stores `sigs` in the evidence | **Yes**, transitively |
| `commitWrite` | `runDenseScan` ×2 (base loop with `ctx = []`; step loop with `ctx = q.toList.map Int.ofNat`) | `target` from the allocated state; `w` from `raw.baseWrites`/`raw.stepWrites` | **Everything** — no bounds recovery, by design. Plus `checkNonlinIO`'s shape preservation, which its own docstring flags. Base call passes `ctx = []`, which the `.advancing` bullet does not cover (B1-F7) | **Yes** — needs a fourth bullet |
| `runDenseScan` | `EvalPlan.lean`'s `runDensePlan`, `.scan` arm — **sole production caller** | store built at exactly `raw.tensorSigs.size` and handed through unchanged | None: the signature tie and store-arity check make the caller's assertions checkable | No |

**Off-contract behaviour of the four standalone predicates.** Every row above records a precondition
of the form "`rows.size` equals the state's rank" or "`advancingDims` is in range", none of which
appears in any signature. Measured directly, all four **fail closed** when the precondition is
violated: `baseWriteRowsOk #[5] 1 #[some (.free 0)]` and `stepWriteRowsOk #[5] 1 #[some (.free 0)]`
are both `false` (an out-of-range `advancingDims` entry makes `rows.getD d none` yield `none`);
`freeExtentsAgree #[3] #[3,3,3] #[some (.free 0), some (.free 1), some (.free 2)]` is `false` (a short
`stateShape` defaults to extent `0`, which matches nothing); and
`pinnedLiteralsInRange #[] #[some (.pinned 0)]` is `false` (`lit.toNat < 0` is unsatisfiable)
[snippet, S13]. So a caller that breaches these preconditions gets a rejection rather than a silent
pass — the safe direction, and worth knowing before B2 adds a clause that could invert it.

Three known instances the brief asked to re-derive rather than trust, all re-derived above and each
confirmed:

1. **`checkWrites`' `if isBase then 0`** — confirmed verbatim. It is B1-F2's **barrier 1**, covering
   rows R9 and R10 across columns 4, 6, 7, 11 and 12 (groups G5, G11, G13, G16). It is *not* the sole
   support: `Compile.lean`'s base-write construction loop is an independent barrier 2 for compiled
   programs, and B1-F2 records where barrier 2 disappears.
2. **`Compile.lean`'s two literal `0`s** — confirmed at both `writeRowKinds` calls in Phase 5. See
   B1-F6.
3. **`commitWrite` trusting `checkNonlinIO`'s shape preservation** — confirmed; already documented in
   `commitWrite`'s own docstring as load-bearing, and it is the one caveat on B1-F3's refutation.

### Finding B1-F6 — `Compile.lean`'s second call site is a strict SUBSET of `Scan.lean`'s rules

Two hand-inlined duplicates confirmed [read]:

- the `baseWriteNotAtBoundary` guard re-implements `baseWriteRowsOk`'s **clause 3** —
  `unless (stateAdvDims.getD w.stateIndex #[]).any (fun d => rows.getD d none == some (.pinned 0))`
  — without calling `baseWriteRowsOk`;
- the loop immediately after re-implements `pinnedLiteralsInRange` —
  `unless 0 ≤ lit && lit.toNat < stateShape.getD d 0` — without calling it.

Beyond the duplication, the source-facing pass is a **strict subset**: it re-implements no counterpart
of `baseWriteRowsOk`'s clauses 1 and 2, none of `stepWriteRowsOk` at all, and none of
`freeExtentsAgree`. Those hold by construction of the base and step write loops (`.iterAt _ lit` →
an all-zero coefficient row with the literal as bias; `.free`/`.freeNorm` → a single `1` at
`freeSeen`, incremented in slot order, so the cover is `List.range` by construction) — but that
construction invariant is written down nowhere, and if it ever failed, the failure surfaces from
`checkScanPlan` as `PlanCompileCause.invalidPlan`, which `Eval/AGENTS.md` documents as *"`checkScanPlan`
rejected COMPILER output, which is a compiler bug, not a source problem"* [read] — i.e. with no source
locator, which is the exact outcome the source-facing pass exists to prevent.

This is the `scatterOutDim`/`scatterOutShape` drift shape one layer over. When `Scan.lean`'s
predicates gain a row kind, the two copies will not see it, and neither will the base/step write
construction loops. Both of those loops have a catch-all arm that currently throws
`CapabilityError.unsupportedLhsSlot`, and the two arms are **not** the same pattern: the base loop's
is `| .iterNext _ | .affine _ =>` and the step loop's is `| .iterAt .. | .affine _ =>` [read]. What
they share is `.affine` — precisely the slot Task B2's affine LHS writes must lower. **Giving the base
loop's arm a real lowering is what removes B1-F2's barrier 2**; see that finding's "Where barrier 2
disappears".

### Finding B1-F8 — `writesCollide` is length-blind in both directions (REFUTED as harmful)

`writesCollide` iterates `List.range rowsA.size` and reads the second array via `rowsB.getD d none`,
so a dimension present in only one argument can never separate the writes:

```
writesCollide #[some (.pinned 0)] #[some (.pinned 0), some (.pinned 1)] = true
writesCollide #[some (.pinned 0), some (.pinned 1)] #[some (.pinned 0)] = true
```

[snippet, S5] — dimension 1 pins `0` against `1` and *would* have separated them. The failure
direction is **conservative** (over-reports collision, therefore rejects), and at both call sites
both arrays come from `writeRowKinds stateShape.size …` for the same state, so the lengths are
always equal. `c`‡, refuted as harmful; recorded because the same `getD … none` catch-all is what
makes G9 and §B1.2 note 3 true.

### Finding B1-F9 — `DSL/Ast.lean` slot functions

The four functions in scope, all probed [snippet, S15]:

- **`toReadIdx`** — the `.affine _ => none` arm (defect instance 5's home) is intact and is still the
  only non-total arm across the five `LHSSlot` constructors:
  `((.free), (.freeNorm), (.iterAt), (.iterNext), (.affine))` → `(true, true, true, true, false)`.
  Its docstring's unreachability argument (`lowerArith` reclassifies every `slotsBecomeScatter`
  `.assign` into `Stmt.scatter` before `splitStmt` runs) is unchanged [read].
- **`slotsBecomeScatter`** — `([free i, free j], [free i, free i], [free i, freeNorm i],
  [affine (2·i)], [iterNext i, free j], [iterAt i 0, iterAt i 1])` →
  `(false, true, true, true, false, false)`. The `[.free a, .freeNorm a]` case is caught (the
  2026-08-27 "fourth class-6 door" fix), and the repeated-`iterAt` case deliberately is not, matching
  its docstring's *"NOT `axisUID?` (which also counts `iterAt`/`iterNext`, whose repeats mean
  something else)"* [read].
- **`outIdx`** — total over all five constructors [read]; it is the sole input to `outExtent`.
- **`outExtent`** — **new `c` cell.** Five distinct extent conventions coexist (`.axis a` → `size`;
  `.const n` → `n+1`; `.shift a c` → `size+c`; `.scale c a` → `c·size`; `.affine c0 xs` →
  `c0 + Σ cᵢ·sizeᵢ`), measured as `(some 4, some 6, some 5, some 8, some 9)` for
  `free i` / `iterAt i 5` / `iterNext i` / `2·i` / `1 + 2·i` at `size(i) = 4`. **Every
  negative-valued form collapses to extent `0` through `Int.toNat`, with no rejection:**
  `iterAt i (-5)`, `scale (-2) i`, `shift i (-9)`, `affine (-100) [(1,i)]` → `(some 0, some 0,
  some 0, some 0)`. Contrast an unsized axis, which correctly yields `none` and fails loud
  (`(none, none)`).

  Not documented as intentional, and not pinned: the only reasoning about a zero extent is in
  `Eval.scatterOutShape`'s own comment — *"An unsized axis means it is unbound by any read (an
  upstream sizing gap), so FAIL LOUD rather than defaulting its size to 0"* — which addresses the
  `none` case and is silent on `some 0` [read]. Both callers, `Eval.scatterOutShape` and
  `SizeInfer.scatterOutputShapes`, distinguish only `some n` from `none`, so a `some 0` flows straight
  through into a shape dimension [read]. This sits directly in Task B2's path (affine LHS writes) and
  inside the `scatterOutShape`/`outExtent` sync contract `Eval/AGENTS.md` names. **Flagged for B2, not
  closed** — whether a zero-extent scatter output is subsequently rejected on the scatter path was not
  chased here.

---

## B1.5 — Gate

> Every forbidden cell needs a located test. No cell may be silently ignored.

### Finding B1-F10 — 10 of the 16 `b` cells have no located test

Measured, not inferred. **Every `#guard` on either geometry predicate in the whole test suite is a
positive (an acceptance)** — all five of them: `baseWriteRowsOk #[0] 1 faceRows`,
`baseWriteRowsOk #[0,1] 0 pointRows`, `baseWriteRowsOk #[1] 1 colFaceRows`,
`stepWriteRowsOk #[0,1] 0 dpStepRows`, `baseWriteRowsOk #[0,1] 0 outOfRangePointRows`. There is no
negative `#guard` on `baseWriteRowsOk` or `stepWriteRowsOk` anywhere [read].

Located coverage therefore rests entirely on plan-level `writeGeometryNotAdmitted` fixtures, of which
there are exactly three [read]:

- `lookAheadStepWrite` (Part 2) — a step row with bias `2`, i.e. clause 1 (`rows.all Option.isSome`)
  rejecting an unrecognized row. Not one of the 16 `b` cells: it tests the `none` case.
- `advancingAtNonAdvancingScan` (Part 8) — covers **R12** (`advancing` @ non-adv @ step), asserting
  `writeGeometryNotAdmitted false 0`, with the review's original aliasing/panic account recorded
  alongside it.
- `pinnedAtNonAdvancingScan` (Part 8) — covers **R4** (`pinned` @ non-adv @ step), same assertion.

Plus `canonicalWScan`, an acceptance control proving clause 3 does not over-reject.

So of the 16 `b` cells: **6 are located** (R4 and R12, each across columns 5, 11, 12) and **10 are
not** —

- **R3** (`pinned` @ adv @ step) and **R7** (`free` @ adv @ step), 6 cells across columns 5, 11, 12.
  Both are rejections by `stepWriteRowsOk`'s clause 2 (`rows.getD d none == some (.advancing i)` at
  every advancing dimension). The only evidence they reject is this audit's [snippet, S3]:
  `stepWriteRowsOk #[0] 1 #[some (.pinned 0), some (.free 0)] = false` and
  `stepWriteRowsOk #[0] 1 #[some (.free 0), some (.free 1)] = false`.
- **R9, R10** (`advancing` @ base) at columns 2–3, 4 cells. Located only by [snippet, S1] and
  [snippet, S11] in this audit.

Clause 2 is the clause Task B2 is most likely to touch (a strided row at an advancing dimension has
to be classified against it), and it is currently the least-pinned clause in the file.

### Summary of state against the gate

> **Updated by Task B2** (see §B2.8 for the same accounting over the appended rows). The two bullets
> immediately below state B1's 12-row figures; with R13–R16 the table stands at **22 `b` cells** —
> 6 located by repo fixtures, 10 located only by B1's spikes, and **6 not locatable by any test that
> could exist today**, since the `strided` constructor they classify does not exist (B2-F5) — and
> **122 `c` cells** across **31 groups**, 16 closed / 91 cells and 15 open / 31 cells.

- **16 `b` cells**: 6 located by repo fixtures, 10 located only by this audit's spikes (B1-F10).
- **86 `c` cells**: all adjudicated in §B1.3 across 17 groups — **9 groups / 71 cells closed**
  (structurally, by kind partition, by a quoted sibling clause, or as documented-and-pinned
  intentional) and **8 groups / 15 cells open**, collapsing to two findings: **B1-F2** (latent,
  10 cells) and **B1-F4** (live and memory-safe, 5 cells). No `c` cell was softened to "unlikely" or
  "defensive", and no write-path cell was closed as backstopped by `gatherFactor`'s `inBoundsPerDim`.
  Fix round 1 moved 4 cells (both value predicates × `advancing` @ base) out of the closed column into
  B1-F2, because their stated catcher does not operate in the base phase — see G16.
- **Findings outside the cell grid**: **B1-F1** (the audit artifact this table was supposed to append
  to does not exist), **B1-F3** (candidate gap 2, refuted with mechanism), **B1-F5** (an `a` cell
  weaker than its own docstring says), **B1-F6** (`Compile.lean`'s inline duplicates are a strict
  subset), **B1-F7** (`commitWrite`'s `.advancing` bullet is step-scoped), **B1-F8** (`writesCollide`
  length-blindness, refuted as harmful), **B1-F9** (`DSL/Ast.lean`'s `outExtent` collapses negative
  affine forms to extent `0`; flagged for B2, not closed).

Every verdict above carries either a quoted clause from the code or a construction attempt with
verbatim observed output.

---

# Axis B / Task B2 — the `strided` row kind across the write-geometry surface

Findings-only, taken at `9680b92` with a green build (`cd leanncd && "$HOME/.elan/bin/lake" build`,
**8660 jobs**) [built]. No production code was changed: the diff over `leanncd/LeanNCD/`,
`leanncd/lakefile.toml` and `leanncd/test/` is empty, and **no `strided` constructor was added to any
committed file**.

Three further spike files, each committed with its captured output alongside B1's in
`axis-b-spikes/`:

- `AxisBStridedProbe.lean` (+ `.output.txt`) — probes **S17–S22**, the strided row across the
  write-geometry predicates and `LHSSlot.outExtent`. Imports `LeanNCD.Eval.Plan.Scan` only.
- `AxisBZeroExtentProbe.lean` (+ `.output.txt`) — probes **S23–S25**, B1-F9's declined question at
  both `outExtent` callers. Imports `LeanNCD.Eval.Eval` / `LeanNCD.Eval.SizeInfer`.
- `AxisBSurfaceZeroExtentProbe.lean` (+ `.output.txt`) — probe **S26**, the same question from real
  surface syntax. Imports the `LeanNCD` umbrella, so it deliberately contains no
  `{ coeffs := …, bias := … }` record literal (`DSL/Syntax.lean` declares `"bias"` as a token).

Re-run exactly as B1's: copy into `leanncd/spikes/` and run `lake env lean spikes/<file>.lean` from
`leanncd/`. None is in `lakefile.toml` or any default build target.

**One extra evidence tag, used only in this section.** `[snippet, model]` marks an observation made
against a **transcribed model** rather than production code: a throwaway spike
(`spikes/AxisBStridedModelThrowaway.lean`) that declared a four-constructor `WRK` inductive and then
copied `baseWriteRowsOk`, `stepWriteRowsOk`, `freeExtentsAgree`, `pinnedLiteralsInRange` and
`writesCollide` **verbatim** from `Scan.lean` with no strided arm added, so that a genuinely new
constructor could be run through the current predicate text. It was **deleted before committing** and
is not in `axis-b-spikes/`; its observed output is reproduced inline below. A `[snippet, model]`
claim is weaker than a `[snippet]` one — it measures a faithful copy, not the shipped function — and
every such claim below is paired with a `[snippet]` measurement of the real clause it models.

---

## B2.1 — Fact 2 DECIDED: the strided branch is *not* phase-gated, and the base cell is LIVE

B1 tagged fact 2 `[CONDITIONAL — not measured; no strided constructor exists to measure]` and handed
the decision here. **Decision, with the assumption named.**

### The decision

> **Decision A (adopted).** `classifyWriteRow`'s strided branch carries the **domain-partition**
> guard `p ≥ contextWidth` — the identical guard `.free` already carries — and **no phase gate**. It
> is ordered **after** the advancing branch. In full:
>
> ```
> | [(c, p)] =>
>     if c == 1 && p < contextWidth && bias == 1 then some (.advancing p)
>     else if c == 1 && p ≥ contextWidth && bias == 0 then some (.free (p - contextWidth))
>     else if p ≥ contextWidth then some (.strided (p - contextWidth) c bias)
>     else none
> ```
>
> **Decision B (rejected).** The same branch additionally gated `&& contextWidth > 0`, i.e. step
> writes only — structurally the shape `.advancing`'s own `p < contextWidth` guard has.

**Consequence, stated plainly: the strided cell at base is LIVE, not latent.** Under decision A a
strided row is emittable at `contextWidth = 0`, so B1's fact-2 conditional resolves to its live
branch and this is the write-geometry defect family recurring for a **sixth** time (finding B2-F1).

### Why A and not B — the argument, and the assumption it rests on

1. **The feature wants base strided writes.** `Compile.lean` has **two** `.affine` arms to lower, not
   one: the base-write construction loop's `| .iterNext _ | .affine _ =>` and the step-write loop's
   `| .iterAt .. | .affine _ =>`, both throwing `CapabilityError.unsupportedLhsSlot` [read]. Decision
   B would leave the base arm permanently unlowerable, so a base initialization like
   `dp[0, 2*j] := ROWFACE[j]` would stay rejected — refusing half the feature to keep half a defect
   latent.
2. **A phase gate would not be a bound, only a deferral.** Barrier 1 (`checkWrites`' `if isBase then
   0`) is enforced by no signature and no check; B1 recorded it as an unenforced call-site
   precondition stated in two docstrings. Decision B would add a **third** row kind resting on that
   same unenforced value, i.e. it buys latency at the cost of one more `‡`.
3. **`p ≥ contextWidth` is required either way**, and for a reason independent of phase: the minimal
   shape the brief specifies is `strided (outputPos : Nat) (scale : Int) (offset : Int)`, coordinate
   `scale * out[outputPos] + offset`. Its payload names an **output-slice** position, so a nonzero
   coefficient sitting in the *context* half has no representation in it and must stay `none`.
   Measured on the model: a strided-shaped row at `p = 0 < contextWidth = 2` is `none` under **both**
   decisions — `(classifyA 2 #[2,0,0] 0, classifyB 2 #[2,0,0] 0)` → `(none, none)`
   [snippet, model].
4. **Ordering after the advancing branch is not cosmetic.** Coefficient `1` with bias `1` is
   `.advancing p` when `p < contextWidth` and unclassified today when `p ≥ contextWidth`; a strided
   branch placed *before* the advancing branch would swallow every advancing row. Measured on the
   real `classifyWriteRow`: `(classifyWriteRow 0 #[1] 1, classifyWriteRow 2 #[1,0,0] 1,
   classifyWriteRow 2 #[0,0,1] 1)` → `(none, some (.advancing 0), none)` [snippet, S17]; and on the
   model, with the branch ordered after, `.advancing` survives under both decisions —
   `(classifyA 2 #[1,0,0] 1, classifyB 2 #[1,0,0] 1)` → `(some (.advancing 0), some (.advancing 0))`
   [snippet, model].

**The assumption this rests on, named.** Decision A assumes the affine-LHS feature is wanted in
**base** blocks and not only in step blocks. That is an assumption about the feature's scope, not a
fact derivable from the code at `9680b92` — `Compile.lean`'s base `.affine` arm being *present and
throwing* shows only that the slot is reachable enough to need an arm, not that the feature intends
to lower it. **If the Scatter slice decides affine LHS writes are step-only, decision B is the right
one** and every `★`-marked row below becomes latent rather than live; §B2.3 gives decision B's mark
for each group that differs. This paragraph is the assumption; it is not presented as a measurement.

### The construction, built both ways

The construction the brief asked for, run under each decision so the Scatter slice inherits a tested
answer either way. Rows for the `dp[0, 2·oc₀, oc₀]` write (`coeffs := #[#[0], #[2], #[1]]`,
`bias := #[0, 0, 0]`) at base width 0:

```
decision A:  #[some (pinned 0), some (strided 0 2 0), some (free 0)]
decision B:  #[some (pinned 0), none,                 some (free 0)]

baseWriteRowsOk #[0] 1 (decision A's rows) = true      -- LIVE: admitted, strided row dropped
baseWriteRowsOk #[0] 1 (decision B's rows) = false     -- LATENT: clause 1 (rows.all Option.isSome)
```

[snippet, model]. And the same three coefficient/bias shapes at each phase:

```
decision A @ base (width 0): (some (strided 0 2 0), some (strided 0 1 3), some (strided 0 2 3))
decision A @ step (width 2): (some (strided 0 2 0), some (strided 0 1 3), some (strided 0 2 3))
decision B @ base (width 0): (none, none, none)
decision B @ step (width 2): (some (strided 0 2 0), some (strided 0 1 3), some (strided 0 2 3))
```

[snippet, model]. The corresponding **production** measurement — every one of those six shapes is
`none` at HEAD, confirming fact 1 over the exact rows the feature must admit rather than over B1's
generic `#[2]`:

```
classifyWriteRow 0 #[2] 0,  classifyWriteRow 0 #[1] 3,  classifyWriteRow 0 #[2] 3        -> (none, none, none)
classifyWriteRow 2 #[0,0,2] 0, classifyWriteRow 2 #[0,0,1] 3, classifyWriteRow 2 #[0,0,2] 3 -> (none, none, none)
```

[snippet, S17]. Through the real entry, a strided-shaped base row is rejected at HEAD by clause 1:

```
writeRowKinds 2 0 (coeffs #[#[0],#[2]], bias #[0,0]) = #[some (pinned 0), none]
baseWriteRowsOk #[0,1] 1 (those rows)                = false
S18 (strided-shaped base row, coefficient 2): checkScanPlan REJECTED:
  LeanNCD.Eval.Plan.ScanPlanError.writeGeometryNotAdmitted true 0
S18b (strided-shaped base row, coefficient 1 bias 5): checkScanPlan REJECTED:
  LeanNCD.Eval.Plan.ScanPlanError.writeGeometryNotAdmitted true 0
```

[snippet, S18].

### One shape neither decision reaches

A **two-nonzero** coefficient row — `Out[i + j]`, i.e. `.affine 0 [(1,i),(1,j)]` — stays `none` under
both decisions, because `classifyWriteRow`'s `| _ => none` arm matches on the **length** of the
nonzero list and a one-`outputPos` strided payload cannot extend it. Measured on production:
`(classifyWriteRow 0 #[1,1] 0, classifyWriteRow 0 #[2,3] 5, classifyWriteRow 2 #[0,0,1,1] 0)` →
`(none, none, none)` [snippet, S17]; and on the model, `(classifyA 0 #[1,1] 0, classifyB 0 #[1,1] 0)`
→ `(none, none)` [snippet, model]. The slot nonetheless **has an extent**:
`LHSSlot.outExtent (.affine (.affine 0 [(1,i),(1,j)])) sz` → `some 7` at `size(i)=4, size(j)=3`
[snippet, S21]. So the minimal strided kind admits a strict subset of the affine LHS forms
`outExtent` already prices — recorded as **B2-F6** below.

---

## B2.2 — The `strided` row kind appended to the table (R13–R16)

Appended exactly as §B1.2 specified: four rows at the bottom, no change to any column header, to any
existing row, or to B1's legend.

**One B2-local mark, declared here rather than added to B1's legend** (which stays as B1 wrote it):

| Mark | Meaning |
|---|---|
| **★** | on a *row label*, not a cell: every mark in this row is the mark under §B2.1's **decision A**. The letter is unchanged under decision B for columns 1, 13 and 14; for the rest, §B2.3's group entries give decision B's reading. A row-label mark contributes nothing to the cell census |

### The appended rows

| # | row kind @ dim class @ phase | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| R13 | `strided` @ adv @ base ★ | c | c | c | **c** | — | **c** | **c** | c | ▷ | ▷ | **c** | **c** | c | c |
| R14 | `strided` @ non-adv @ base ★ | c | c | c | **c** | — | **c** | **c** | c | ▷ | ▷ | **c** | **c** | c | c |
| R15 | `strided` @ adv @ step | c | c | c | — | **b** | c | c | — | ▷ | ▷ | **b** | **b** | c | c |
| R16 | `strided` @ non-adv @ step | c | c | c | — | **b** | c | c | — | ▷ | ▷ | **b** | **b** | c | c |

### Cell census for the four appended rows

56 cells (4 × 14): **0 a**, **6 b**, **36 c**, 6 —, 8 ▷. Per row: R13 and R14 are 11 c / 1 — / 2 ▷
each; R15 and R16 are 7 c / 3 b / 2 — / 2 ▷ each. Whole table after the append: **224 cells (16 ×
14) — 24 a, 22 b, 122 c, 24 —, 32 ▷**, as restated in §B1.2's census and §B1.5's gate summary.

**Reported divergence (the brief predicted ~27 adjudicable cells).** 36 `c` cells, a 33% overshoot
— far smaller than B1's 86-against-40. The mechanism is the same one B1 identified and is not new
information about the code: the five non-validating / dimension-class-blind columns (`WriteRowKind`,
`classifyWriteRow`, `writeRowKinds`, `commitWrite`, `runDenseScan`) contribute 20 of the 36 by
construction. Excluding them leaves **16 `c` cells** — 2 in `baseWriteRowsOk`, 4 in
`freeExtentsAgree`, 4 in `pinnedLiteralsInRange`, 2 in `writesCollide`, 2 each in `checkWrites` and
`checkScanPlan` — below the estimate rather than above it.

### Finding B2-F2 — not one `a` cell among 56

**No audited site requires or demands the presence of a strided row, in either phase.** All 24 `a`
cells in the combined table belong to B1's rows R1–R12. Every site either forbids a strided row
(6 `b` cells, all at step) or ignores it (36 `c` cells). That asymmetry is worth naming because
`baseWriteRowsOk`'s clause 2 and `stepWriteRowsOk`'s clause 4 are *positional-cover* clauses — they
express "these dimensions must be covered" as an `a`-style demand on `.free` rows — and a strided row
is a cover row in every sense except that no clause counts it. §B2.4 is where that gap has to be
closed, and it is why B2-F1's cells are `c` rather than `b`.

---

## B2.3 — Adjudication of every new `c` cell (G17–G30)

Same order B1 used: (1) name the catching site and **quote its clause**; (2) if soundness rests on a
caller rather than the predicate's own text, mark `‡` and route to the call-site question; (3) build
the construction and record the observed value verbatim. **No write-path cell below is closed as
"backstopped by `gatherFactor`'s `inBoundsPerDim`", and no cell is closed by naming a catcher that
cannot fire in its own phase** — the failure that cost B1 a fix round (G16). Where a group's catcher
is `stepWriteRowsOk`, the group is a **step-phase** group and that predicate does run there.

| Group | Cells | Site × rows | Verdict |
|---|---|---|---|
| G17 | 4 | col 1 × R13–R16 | **Closed structurally**, extending G1. A closed inductive cannot require or forbid. G1 anticipated exactly this constructor: *"a payload-carrying fourth constructor inherits correct equality for free"* — verified rather than assumed, since two production clauses compare against literal constructors via derived `BEq` (`baseWriteRowsOk`'s `rows.getD d none == some (.pinned 0)` and `stepWriteRowsOk`'s `== some (.advancing i)`). On a four-constructor `deriving DecidableEq, BEq` inductive, `(some (.strided 0 2 0) == some (.pinned 0), == some (.advancing 0), == some (.strided 0 2 0), == some (.strided 0 2 1))` → `(false, false, true, false)` [snippet, model] — cross-constructor comparisons are `false` and payload discrimination is exact, so neither clause silently changes meaning. |
| G18 | 4 | cols 2–3 × R15, R16 | **Closed** to G-step (col 5). Both functions are dimension-class-blind by construction — `classifyWriteRow`'s signature is `(contextWidth : Nat) (coeffRow : Array Int) (bias : Int)`, no `advancingDims` and no dimension index [read] — so the whole dim-class axis is `c` here, exactly as G2a. Unlike G2b, the downstream catcher is **not** open: `stepWriteRowsOk` clause 2 (`advancingDims.toList.zipIdx.all (fun (d, i) => rows.getD d none == some (.advancing i))`) and clause 3 (`rows.toList.zipIdx.all (fun (r, d) => advancingDims.contains d \|\| (match r with \| some (.free _) => true \| _ => false))`) between them reject a strided row at every dimension, **in the step phase, which is this group's own phase**. Measured on the model at all three placements: `(stepWriteRowsOk #[0,1] 1 #[strided, advancing 1, free 0], stepWriteRowsOk #[0] 1 #[advancing 0, strided, free 0], stepWriteRowsOk #[0] 1 #[advancing 0, free 0, strided])` → `(false, false, false)` [snippet, model]. The real clauses' behaviour on a non-`.free` non-`.advancing` `some` row at the same parameters: `(stepWriteRowsOk #[0,1] 1 #[some (.pinned 0), some (.pinned 2), some (.free 0)], stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.pinned 2), some (.free 0)])` → `(false, false)` [snippet, S19]. **Decision B**: unchanged — `classifyWriteRow` admits strided at step under both decisions [snippet, model]. |
| **G19** | 4 | cols 2–3 × R13, R14 | **OPEN — B2-F1.** Same blindness as G18, but the only downstream catcher at base is `baseWriteRowsOk`, whose own cells for these rows (G20) are open. **A group cannot be closed by deferral to an open group** — B1 established that rule at G2b, and it applies unchanged. **Decision B**: these four cells become **`b`‡** instead, on barrier 1 (`checkWrites`' `if isBase then 0`), exactly as B1 marked R9/R10 at these columns. |
| **G20** | 2 | col 4 × R13, R14 | **OPEN — B2-F1, the sixth instance.** `baseWriteRowsOk` clause 2 is the verbatim defect-instance-4 shape and its `filterMap` arm is **constructor-blind**: `((rows.toList.filterMap (fun r => match r with \| some (.free p) => some p \| _ => none)) == List.range outputShapeSize)`. The `\| _ => none` arm drops every `some` row that is not `.free`, a fourth constructor included. Measured on the model at both dimension classes: `(baseWriteRowsOk #[0] 1 #[pinned 0, strided 0 2 0, free 0], baseWriteRowsOk #[0,1] 1 (same))` → `(true, true)` [snippet, model]. Measured on the **real** clause with the two non-`.free` constructors that exist, at the identical parameters: `(baseWriteRowsOk #[0] 1 #[some (.pinned 0), some (.pinned 2), some (.free 0)], … #[some (.pinned 0), some (.advancing 0), some (.free 0)], baseWriteRowsOk #[0,1] 1 (each of those))` → `(true, true, true, true)`, against the control in which dim 1 carries a genuine second `.free` row and the cover therefore breaks: `(baseWriteRowsOk #[0] 1 #[some (.pinned 0), some (.free 1), some (.free 0)], … #[some (.pinned 0), some (.free 0), some (.free 0)])` → `(false, false)` [snippet, S19]. That control is what makes the drop a *drop* rather than an accident of the parameters. **Decision B**: **`c`‡ latent** rather than live — the rows become `#[some (.pinned 0), none, some (.free 0)]` and clause 1 fires, `baseWriteRowsOk … = false` [snippet, model]. |
| G21 | 2 | col 6 × R15, R16 | **Closed** by an in-phase catcher, not by kind partition alone. `freeExtentsAgree`'s `\| _ => true` arm ignores a strided row exactly as it ignores `.pinned`/`.advancing` [read], so the cell is `c`. It is closed because `checkWrites` runs `unless admitted do throw (.writeGeometryNotAdmitted isBase wi)` **before** `freeExtentsAgree` [read], and at step `admitted` is `stepWriteRowsOk`, which rejects a strided row at every dimension (G18's measurement). So the row never reaches this predicate in this phase — a stronger closure than G6's, and one whose catcher demonstrably fires here. Marked `c` rather than `—` to keep B1's column convention (B1 marks col 6 `c` for R3/R4/R12, all `b` at col 5). **Decision B**: unchanged. |
| **G22** | 2 | col 6 × R13, R14 | **OPEN — B2-F1.** The same `\| _ => true` arm, in the **base** phase, where nothing rejects the row first: `baseWriteRowsOk` admits it (G20), so `checkWrites` proceeds to `freeExtentsAgree` and it passes at **any** extents. Measured on the model: `(freeExtentsAgree #[1,3,3] #[3] stridedRows, freeExtentsAgree #[1,1,3] #[3] stridedRows)` → `(true, true)` — the second with dim 1 at extent **1** [snippet, model]; and on the real predicate at the same parameters with `.advancing` standing in, `(freeExtentsAgree #[1,3,3] #[3] …, freeExtentsAgree #[1,1,3] #[3] …)` → `(true, true)` [snippet, S19]. **This is the load-bearing cell of the whole task**: `freeExtentsAgree` is the *one* predicate whose job is to bound a cover row's extent against the state's own dimension, and it is the predicate a strided row must extend (§B2.4). Not closed, and specifically **not** closed by citing `stepWriteRowsOk` or `advancingSizeMismatch` — neither operates at base, which is precisely G16's error. |
| G23 | 2 | col 7 × R15, R16 | **Closed** by the same in-phase catcher as G21. `pinnedLiteralsInRange`'s `\| _ => true` arm ignores a strided row [read]; the row never reaches it at step, because `stepWriteRowsOk` rejects first and `checkWrites` throws before calling it [read]. Recorded alongside: the predicate's docstring justification — *"`.free`/`.advancing` rows are vacuously fine (their range is already bounded by the checked output/context shapes elsewhere)"* — **enumerates exactly two kinds and would not mention a strided row at all**. B1 already established that this sentence is false for an advancing row at base (G16); for a strided row it is not false so much as absent. See B2-F3. **Decision B**: unchanged. |
| **G24** | 2 | col 7 × R13, R14 | **OPEN — B2-F1.** As G22: reached in the base phase and passing. `pinnedLiteralsInRange #[1,3,3] stridedRows = true` and `pinnedLiteralsInRange #[1,1,3] stridedRows = true` [snippet, model]; the real predicate at the same parameters with `.advancing` standing in, `pinnedLiteralsInRange #[1,3,3] #[some (.pinned 0), some (.advancing 0), some (.free 0)]` → `true` [snippet, S19]. Not closed, and not closed by appeal to *"the checked output/context shapes"* — `checkScanPlan` forces `raw.baseBlock.contextShape == #[]`, so at base there is no context shape for that phrase to refer to (B1's S16 verified the rejection: `baseBlockContextNotEmpty #[2]`). |
| G25 | 2 | col 8 × R13, R14 | **Closed as conservative** — fact 3, now measured on a real fourth constructor. `writesCollide`'s catch-all is `\| _, _ => false`, so *"a dimension forces the regions apart only when BOTH writes pin it to DIFFERENT literals"* [read] and a strided row can never separate two base writes. Measured: `(writesCollide #[strided 0 2 0] #[strided 0 2 1], writesCollide #[pinned 0, strided 0 2 0] #[pinned 0, strided 0 2 5], writesCollide #[pinned 0, strided 0 2 0] #[pinned 1, strided 0 2 0])` → `(true, true, false)` [snippet, model] — the third separates only via its `.pinned 0` vs `.pinned 1` row at dimension 0, which is the clause doing its declared job. Real-predicate counterpart on the existing non-`.pinned` constructors: `(writesCollide #[some (.free 0)] #[some (.free 0)], writesCollide #[some (.advancing 0)] #[some (.pinned 1)], writesCollide #[some (.pinned 0), some (.advancing 0)] #[some (.pinned 0), some (.pinned 1)])` → `(true, true, true)` [snippet, S19]. The failure direction is **over**-rejection, hence safe. Two differences from G9 are worth recording rather than inheriting: G9 closed these cells as *vacuous today* because no base row can be `.advancing`; under decision A that ground disappears, so this group is closed on conservatism alone. And the expressiveness cost is real — **two strided base writes to one state are always reported as colliding**, so `dp[0, 2*j] := A[j]` alongside `dp[0, 2*j+1] := B[j]` is inexpressible, and disjointly so (`baseWritesOverlap`, pinned by `ScanTest.lean`'s fixture at `baseWritesOverlap 0 0 1` and by `ScanCompileTest.lean`'s two `.scan (.baseWritesOverlap "sc2" "dp" 0 1)` assertions [read]). **Decision B**: vacuous, as G9. |
| **G26** | 2 | col 11 × R13, R14 | **OPEN.** Escalation of G20 to the orchestrator: `checkWrites` calls `baseWriteRowsOk` in its `if isBase then` arm as the **sole caller** [read] and adds no strided obligation. |
| **G27** | 2 | col 12 × R13, R14 | **OPEN.** Escalation of G20 to the **public** entry. `checkScanPlan`'s own additions — `advancingDimOutOfRange`, `duplicateAdvancingDim`, `advancingDimCountMismatch`, `advancingSizeMismatch`, `baseBlockContextNotEmpty`, the four policy gates, `stateDtypeNotAdmitted`, the causality loop [read] — **change no cell in these four rows**. `advancingSizeMismatch` in particular relates `stateShape[advancingDims[i]]` to `historyExtents[i]` and says nothing about a strided row's presence, placement, or scale, at either dimension class. So B2-F1's cells reach `checkScanPlan` unchanged, exactly as B1-F2's do. |
| G28 | 2 | col 13 × R15, R16 | **Closed** by evidence-carrying construction, in-phase. `CheckedScanPlan` has `private mk ::`, so the only way to obtain one is `checkScanPlan` [read]; a step write carrying a strided row makes `checkWrites` throw `writeGeometryNotAdmitted false wi` (G18), so no checked plan carrying such a row exists and `commitWrite` never receives one in the step phase. The missing docstring bullet is still an obligation — see B2-F3 — but it is a documentation finding, not an unclosed cell. **Decision B**: unchanged. |
| **G29** | 2 | col 13 × R13, R14 | **OPEN — B2-F1.** This is where B2-F1's cells become memory unsafety. `commitWrite`'s own docstring states the premise: it *"does NOT call `inBoundsPerDim` before `flatIndex`: it performs no bounds recovery, trusting `checkScanPlan`"* [read] — and at base, per G20/G22/G24, `checkScanPlan` checked nothing about this row. Worked out rather than argued, on the `dp[0, 2·oc₀, oc₀]` map (`coeffs := #[#[0],#[2],#[1]]`, `bias := #[0,0,0]`) over an output of shape `[3]` against a `[1,3,3]` state: `applyAffine` at `ctx = []` gives `([0,0,0], [0,2,1], [0,4,2])`; `inBoundsPerDim [1,3,3]` gives `(true, true, false)`; and `flatIndex` gives the addresses `(0, 7, 14)` on a **9-element** store [snippet, S20]. Since `commitWrite` calls no `inBoundsPerDim`, that is one correct write, one silent write into a cell belonging to another coordinate, then an out-of-range `Array.set!` — the verbatim F3/F4 failure signature, and strictly worse than B1-F2's `3/7/11`, which at least stayed within one element of the store. Two further arithmetic modes measured at the same site: a `.shift`-flavoured strided row (`bias := #[0,5,0]`) is out of range at **every** coordinate — `applyAffine → [0,5,0]`, `inBoundsPerDim → false`, `flatIndex → 15` [snippet, S20]; and a **negative** offset (`bias := #[0,-2,0]`) is collapsed by `commitWrite`'s own `.map Int.toNat` — `applyAffine → [0,-2,0]`, `inBoundsPerDim → false`, `(…).map Int.toNat → [0,0,0]`, `flatIndex → 0` — so it aliases silently onto the lower boundary **in range**, with no panic to notice it by [snippet, S20]. That third mode is new to this task: B1-F2's advancing row cannot produce a negative coordinate, because its bias is fixed at `1`. |
| G30 | 4 | col 14 × R13–R16 | **Closed** by evidence-carrying construction, extending G15. `runDenseScan` reads state shapes from `c.sigs` — the table `checkScanPlan` validated the plan against — rejects a differing caller table (`signatureContextMismatch`) and a differing store length (`storeArityMismatch`) before allocating [read], and imposes no per-row obligation at all. Nothing in that argument mentions a row kind, so a fourth constructor changes none of it. **Not** offered as a bound on G29: the store-arity check fixes how long the store is, not where within it `commitWrite` writes. |

The 14 groups above account for all 36 new `c` cells: G17 4, G18 4, G19 4, G20 2, G21 2, G22 2,
G23 2, G24 2, G25 2, G26 2, G27 2, G28 2, G29 2, G30 4.

- **7 groups closed, 20 cells**: G17, G18, G21, G23, G25, G28, G30.
- **7 groups open, 16 cells**: G19 4, G20 2, G22 2, G24 2, G26 2, G27 2, G29 2 — all one finding,
  **B2-F1**.

The 8 `▷` cells (cols 9–10 × R13–R16) fall under B1's **G-READ** unchanged: `causalAdvancingRow` and
`stateReadCausal` classify a `ReadPlan`'s coefficient rows, a disjoint vocabulary, and adding a
*write*-row kind changes neither. Worth one sentence because it is not quite symmetric:
`causalAdvancingRow`'s own shape test is `match nz with | [(c, p)] => c == 1 && p == ctxPos && bias ≤ 0
| _ => false` [read], so a **strided read** row (`c ≠ 1`) is already rejected there today, by a
clause that exists and fires. A strided read is therefore not a candidate gap N+1 on the read side —
recorded so the Scatter slice does not go looking for one.

### Finding B2-F1 — the write-geometry defect family recurs for a SIXTH time, LIVE at base

**16 cells: G19 (4), G20 (2), G22 (2), G24 (2), G26 (2), G27 (2), G29 (2).**

Under §B2.1's decision A a strided row is emittable at base, and at base **nothing looks at it**:

- `baseWriteRowsOk` clause 2's `filterMap` **drops** it from the positional cover (G20), while
  clauses 1 and 3 are satisfied by the other rows;
- `freeExtentsAgree` matches only `.free` and passes it at any extents, including a state dimension
  of extent 1 against a stride of 2 (G22);
- `pinnedLiteralsInRange` matches only `.pinned` and passes it likewise (G24);
- `writesCollide`'s catch-all can only over-reject, never bound anything (G25);
- `commitWrite` performs no bounds recovery and computes `scale · out[p] + offset` against a store
  bounded by nothing, reaching flat address **14 on a 9-element store** (G29).

**Why this is the same shape as F3/F4's four instances and B1-F2's fifth**, in the words
`stepWriteRowsOk`'s own docstring uses for the family: *"a geometry predicate that says which rows
MUST be a given kind without saying which rows MAY NOT be"* [read]. Clause 2 says the `.free` rows
must cover `List.range outputShapeSize`; it does not say that no other row may occupy an output
position. A strided row occupies one — in the construction above it shares output position `0` with
the `.free` row at dimension 2 — and is invisible to the cover for exactly the reason an
`.advancing` row at a non-advancing dimension was invisible to `stepWriteRowsOk`'s clause 4 before
F4's third clause was added.

**How it differs from B1-F2, and why that matters more than the similarity.** B1-F2 is *latent*: two
independent barriers hold it up, and B1 recorded that the second disappears when B2 lowers
`Compile.lean`'s base `.affine` arm. B2-F1 is **live from the moment `classifyWriteRow` gains a
non-phase-gated strided branch** — barrier 1 does not apply to it at all (§B2.7). It is therefore not
a thing to record and defer; it is a clause the Scatter slice must write.

**What the fix is, stated as an obligation rather than as code.** `baseWriteRowsOk` needs the
counterpart of `stepWriteRowsOk`'s third clause: a statement of which rows MAY occupy an output
position, so that a strided row is either counted into the cover or rejected. And `freeExtentsAgree`
needs a strided arm computing the extent the row actually spans — which is §B2.4's subject, and the
one place this finding touches the `outExtent` sync contract.

### Finding B2-F3 — four docstrings and one AGENTS.md node enumerate the constructor set exhaustively

B1's G14/B1-F7 established that `commitWrite`'s docstring is a row-by-row soundness argument with
**one bullet per current constructor** — verified again here, at `Scan.lean`'s
`- a \`.free p\` row …` / `- an \`.advancing i\` row …` / `- a \`.pinned lit\` row …`, three bullets
[read, via `grep -n "^    - a \`\.\|^    - an \`\." leanncd/LeanNCD/Eval/Plan/Scan.lean` → lines 544,
548, 558]. A fourth constructor makes that argument **incomplete**, not merely dated: the docstring's
value is that it is exhaustive over the surface.

The same sweep surfaces three further sites in `Scan.lean` whose prose names the constructor set as a
closed list, found with
`grep -n "pinned\`/\`\.free\|free\`/\`\.advancing\|pinned to a literal" leanncd/LeanNCD/Eval/Plan/Scan.lean`
→ 4 hits, lines 6, 95, 108, 109 [read]:

1. **`WriteRowKind`'s own docstring** — *"One recognized shape for a write-map row: pinned to a
   literal, an order-preserving projection of the block's own output slice, or bound to
   `context[p] + 1` (step writes only). Anything else is an unrecognized affine geometry and must be
   rejected."* The final sentence is what a strided constructor contradicts.
2. **`pinnedLiteralsInRange`** — *"`.free`/`.advancing` rows are vacuously fine (their range is
   already bounded by the checked output/context shapes elsewhere)."* Two kinds named; for a strided
   row the clause behaves identically and the sentence says nothing (G23/G24).
3. **`writesCollide`** — *"Since every row is `.pinned`/`.free`/`.advancing`, a dimension forces the
   regions apart only when BOTH writes pin it to DIFFERENT literals."* The premise is a literal
   three-way enumeration; the conclusion survives a fourth constructor (G25 measured it) but the
   stated reason does not.

And one node outside the source: `leanncd/LeanNCD/Eval/AGENTS.md`'s `Scan.lean` row describes the
file as owning the *"write-geometry classifier (`WriteRowKind`/`writeRowKinds`)"* with the
free/pinned/advancing vocabulary threaded through its `freeExtentsAgree` and `pinnedLiteralsInRange`
glosses [read]. A repo-wide sweep for files whose prose carries both `advancing` and `pinned` —
`grep -rln "advancing" --include='*.lean' --include='*.md' leanncd/LeanNCD/ | xargs grep -l "pinned"`
→ 6 files: `Eval/Scan.lean`, `Eval/AGENTS.md`, `Eval/Plan/Scan.lean`, `Eval/Plan/Error.lean`,
`Eval/Plan/Compile.lean`, `DSL/Ast.lean` [read] — is offered as the *located starting set* for the
Scatter slice's doc pass, not as a claim that these are the only affected sites.

### Finding B2-F6 — the minimal strided kind admits a strict subset of the affine LHS forms

`LHSSlot.outExtent` prices a two-axis affine slot (`.affine c0 xs` with `xs.length ≥ 2`) and
`slotsBecomeScatter` routes it to scatter, but `classifyWriteRow`'s `| _ => none` arm cannot classify
its coefficient row under a one-`outputPos` strided payload — measured both ways in §B2.1. So after
the Scatter slice lands, the checked scan backend will admit `Out[2*i]`, `Out[i+3]` and `Out[2*i+3]`
while still rejecting `Out[i+j]`, and the rejection will surface as `writeGeometryNotAdmitted` (a
positional-IR error) rather than as a source-locating capability error, because `checkScanLHSSlot`'s
`.affine` arm will by then have been lifted. **Recorded, not remediated**: whether the strided
payload should be a coefficient *list* rather than a single `outputPos` is a design question for the
Scatter slice, and the cheap alternative — keeping a `CapabilityError` for the multi-axis case at
preflight, where a source locator still exists — is the one this audit would flag if it were asked.

---

## B2.4 — Every strided cell tied to `LHSSlot.outExtent`'s arms

`LHSSlot.outExtent` (`DSL/Ast.lean`) is the single shared scatter-extent formula both
`Eval.scatterOutShape` and `SizeInfer.scatterOutputShapes` must call; a duplicate (`scatterOutDim`,
an upper-envelope `max index + 1`) drifted from it and shipped a soundness bug — a downstream reader
sized to 3 while the evaluator materialized 4 (fix `fc10d70`, duplicate deleted `6a26825`)
[read, `Eval/AGENTS.md` Contracts].

### Which arm is which row kind's image

`LHSSlot.outIdx` is total over all five `LHSSlot` constructors and `IdxExpr` has exactly five
constructors, so `outExtent`'s five arms are exhaustive over its own input [read — both inductives
counted at `DSL/Ast.lean`'s `inductive IdxExpr` and `def LHSSlot.outIdx`]. Measured at
`size(i) = 4`, all six forms in one probe: `(some 4, some 6, some 5, some 7, some 8, some 11)`
[snippet, S21].

| `outExtent` arm | Source slot it comes from | Extent | Checked-plan row kind |
|---|---|---|---|
| `.axis a` → `sz a.uid` | `.free a` / `.freeNorm a` | 4 | **`.free p`** (coeff 1, bias 0) |
| `.const n` → `(n+1).toNat` | `.iterAt a n` | 6 at `n = 5` | **`.pinned n`** (all-zero row, bias `n`) |
| `.shift a 1` → `(s+1).toNat` | `.iterNext a` | 5 | **`.advancing i`** (coeff 1, bias 1) |
| `.shift a c`, `c ≠ 1` → `(s+c).toNat` | `.affine (.shift a c)` | 7 at `c = 3` | **`strided p 1 c`** |
| `.scale c a` → `(c·s).toNat` | `.affine (.scale c a)` | 8 at `c = 2` | **`strided p c 0`** |
| `.affine c0 [(c,a)]` → `(c0 + c·s).toNat` | `.affine (.affine c0 [(c,a)])` | 11 at `c0=3, c=2` | **`strided p c c0`** |
| `.affine c0 xs`, `\|xs\| ≥ 2` | `.affine (.affine c0 xs)` | 7 at `[(1,i),(1,j)]` | **none** — B2-F6 |

So **each of R13–R16 is the checked-plan image of exactly one of three arms** — `.shift a c` with
`c ≠ 1`, `.scale c a`, or `.affine c0 [(c,a)]` — selected by the row's `(scale, offset)` payload:
`(1, c)` → `.shift`, `(c, 0)` → `.scale`, `(c, c0)` → `.affine`. The remaining two arms are already
taken: `.axis` is `.free`'s image and `.const` is `.pinned`'s.

**One collision inside the `.shift` arm, measured.** `.iterNext a` and `.affine (.shift a 1)` are the
**same** `outIdx` and therefore the same extent: `(LHSSlot.outIdx (.iterNext axI) ==
LHSSlot.outIdx (.affine (.shift axI 1)), LHSSlot.outExtent (.iterNext axI) sz == LHSSlot.outExtent
(.affine (.shift axI 1)) sz)` → `(true, true)` [snippet, S21]. That is the surface-level sibling of
`classifyWriteRow`'s coefficient-1-with-bias-1 ambiguity (§B2.1 point 4), and it is why the strided
branch's ordering is load-bearing at the row level too: the *same* `outExtent` arm feeds both
`.advancing` and `strided p 1 1`, distinguished only by whether the coefficient lands in the context
half or the output half.

### Would the site CALL the formula, or copy it?

**It could call it, and the obstruction is not the import graph.** Every S21 probe above compiled
under `import LeanNCD.Eval.Plan.Scan` **alone** — B1's S15 imported `LeanNCD.DSL.Ast` explicitly;
`AxisBStridedProbe.lean` does not, and `(LHSSlot.outExtent (.affine (.scale 2 axI)) sz).isSome` →
`true` there [snippet, S22]. `Eval/Plan/Kernel.lean` imports `LeanNCD.DSL.Ast` and `Scan.lean`
reaches it transitively via `Block → Dense → Check → Error → Kernel` [read, each file's `import`
lines].

The real obstruction is the **argument vocabulary**: `outExtent` takes an `LHSSlot` and a
`UID → Option Nat`, and the checked plan is positional and UID-free. A synthetic-`AxisSpec` adapter
closes that gap exactly, measured: with `syntheticAxis` at uid 0 and a lookup returning the block
output's extent 3, `(outExtent (.affine (.scale 2 syntheticAxis)) (synthetic 3),
outExtent (.affine (.shift syntheticAxis 3)) (synthetic 3),
outExtent (.affine (.affine 3 [(2, syntheticAxis)])) (synthetic 3))` → `(some 6, some 6, some 9)`
[snippet, S21] — the numbers `2·3`, `3+3`, `3+2·3`.

**Finding B2-F4 — `freeExtentsAgree`'s equality is the `scale = 1, offset = 0` special case of the
shared formula, and there is no arm supplying the general one.** The clause is
`| some (.free p) => stateShape.getD d 0 == outputShape.getD p 0` [read]. Under the arm mapping above
that is precisely `stateShape[d] == outExtent(.axis a)` with `outputShape[p]` standing in for
`sz a.uid`. The strided generalization is therefore `stateShape[d] == scale · outputShape[p] +
offset`, i.e. equality against the same three arms. Measured that the current clause returns the
**wrong** verdict for the strided numbers: `freeExtentsAgree #[6,3] #[3] #[some (.free 0), some
(.free 0)]` → `false` (the state dimension a stride-2 row needs is 6, and the clause rejects it),
against `freeExtentsAgree #[3,3] #[3] (same rows)` → `true` [snippet, S21].

**The decision this hands the Scatter slice, and the trap in it.** The write-side check can be
either:

- **equality against `outExtent`'s convention** — `stateShape[d] == scale·outputShape[p] + offset`
  (6 for a stride-2 row over a 3-element output), which keeps the write side numerically identical to
  the source side and is therefore drift-free by construction; or
- **the tighter sufficient bound** — `scale·(outputShape[p] - 1) + offset < stateShape[d]` (5 for the
  same row), which is memory-sufficient and **numerically different**.

The second is memory-safe but **is the `scatterOutDim` mistake in miniature**: a second extent
formula, disagreeing with `outExtent` by `scale - 1`, with no import enforcing agreement — exactly
what `Eval/AGENTS.md` warns of (*"no import enforces this beyond both depending on the same function;
a future second formula reintroduces the drift risk"* [read]). **The audit's recommendation is the
first**, via the synthetic-`AxisSpec` adapter measured above, so that `Scan.lean` *calls* the shared
formula rather than restating it. Recorded as a recommendation, not applied.

**One further copy to keep in view.** B1-F6 found `Compile.lean`'s Phase 5 already hand-inlines
`baseWriteRowsOk`'s clause 3 and `pinnedLiteralsInRange` without calling either, and re-implements no
counterpart of `freeExtentsAgree` at all. Whatever extent rule the Scatter slice writes into
`freeExtentsAgree`, the source-facing pass will not see it, and a violation will surface as
`PlanCompileCause.invalidPlan` — which `Eval/AGENTS.md` documents as *"`checkScanPlan` rejected
COMPILER output, which is a compiler bug, not a source problem"* [read], i.e. with no source
locator. That is now **two** formulas away from `outExtent`, not one.

---

## B2.5 — B1-F9 ANSWERED: a zero-extent scatter output is not rejected on the scatter path

B1 measured that `LHSSlot.outExtent` returns `some 0` for four distinct negative affine forms —
`iterAt i (-5)`, `scale (-2) i`, `shift i (-9)`, `affine (-100) [(1,i)]` → `(some 0, some 0, some 0,
some 0)` [snippet, S15] — and deliberately left the question *"is a zero-extent scatter output
rejected further down the scatter path?"* unanswered. **Answer: no, and the negative case is not even
the reachable one.** Both `outExtent` callers were measured, and the answer splits.

### Caller 1 — `Eval.scatterOutShape` → `evalScatter`: NOT rejected, at any point

`scatterOutShape` fails loud only on `none`; its own comment scopes itself to that case (*"An unsized
axis means it is unbound by any read (an upstream sizing gap), so FAIL LOUD rather than defaulting
its size to 0"* [read]), and `some 0` is not that case. Measured, all four negative forms plus the
positive control:

```
scatterOutShape sizesI [ .shift i (-9) / .scale (-2) i / .affine (-100) [(1,i)] / .iterAt i (-5) / .scale 2 i ]
  -> (ok: [0], (ok: [0], (ok: [0], (ok: [0], ok: [8]))))
scatterOutShape sizesI [.free k]   (k unsized)
  -> error: scatterOutShape: unsized axis in scatter output coordinate for slot …free {k}
```

[snippet, S23]. Then through `evalPlain`, which is the real dispatch (`scatterOutShape` followed by
`evalScatter`):

```
S23a (Out[i - 9], extent 0):            evalPlain .ok; Out shape = [0], data = #[]
S23b (Out[-2*i], extent 0):             evalPlain .ok; Out shape = [0], data = #[]
S23c (Out[-100 + i], extent 0):         evalPlain .ok; Out shape = [0], data = #[]
S23d (Out[iterAt i (-5)], extent 0):    evalPlain .ok; Out shape = [0], data = #[]
S23e (Out[2*i], extent 8 — CONTROL):    evalPlain .ok; Out shape = [8],
                                          data = #[1, 0, 2, 0, 3, 0, 4, 0]
```

[snippet, S23]. **The mechanism is `evalScatter`'s own bounds guard**, `if (outCoordZ.zip
outShape).all (fun (z, d) => 0 ≤ z && z < (d : Int))` [read]: with `d = 0` it is false at every source
coordinate, so every write is skipped by the same rule that exists for genuine overspill
(*"Out-of-range output coordinates are skipped"* [read]). Isolated: `S23f (evalScatter at outShape
[0]): .ok; Out = [0]/#[]` [snippet, S23]. **The collision policy cannot fire either**, because
`.rejectCollisions` is only reached *inside* that guard — four source coordinates all "landing on" a
zero-extent output collide with nothing: `S23g (zero extent + rejectCollisions): .ok; Out = [0]`
[snippet, S23]. And the two gates that *do* still fire are both ordered before the shape is looked
at, so neither helps: `S25a (zero extent + relu): ERROR: evalScatter: non-identity nonlinearity on
scatter Out is unsupported` and `S25b (zero extent + UNSIZED source axis): ERROR: evalScatter:
unsized source axis uid 1` [snippet, S25].

### Caller 2 — `SizeInfer.scatterOutputShapes` → the sizing fixpoint: rejected, but only if READ

`scatterOutputShapes` publishes `some dims` and drops only `none`, so a zero dimension becomes a
downstream-readable shape: `((scatterOutputShapes sizesI [negShift])["Out"]?,
(… [control])["Out"]?, (… [unsizedAxis])["Out"]?)` → `(some [0], some [8], none)` [snippet, S24].
When something reads it, the solver **does** fail loud:

```
S24a (zero-extent scatter out, read downstream): inferAxisSizes ERROR: affine size system
  non-positive (uid 2) (value=0, reduced row=0, col=0); sources: [Out[…axis k] (scatter-out)];
  actions: [increase effective input extent or reduce negative shifts, ensure inferred output
  window size stays strictly positive]; ml-hints: [ml-hint: offset/window yields non-positive extent]
S24b (extent-8 scatter out, read downstream — CONTROL): .ok; i = some 4, k = some 8, warnings = 0
```

[snippet, S24] — `SolveFailureKind.nonPositive`, with remediation text that names the cause
correctly. **But the diagnostic blames the reader, not the writer**: `uid 2` is the *downstream* axis
`k`, and the source list names `Out[axis k] (scatter-out)`. The zero-coefficient or negative-offset
slot that produced the extent is one statement away and unmentioned.

### The case that is actually reachable from surface syntax is a ZERO coefficient, and it is LIVE

`DSL/Elab.lean`'s `elabTLLHSSlot` builds every affine LHS coefficient and offset as
`Int.ofNat n.getNat` from a `num` literal, across all four affine arms (`$x +1`, `$n * $x + $m`,
`$n * $x`, `$x + $n`), and `.iterAt` likewise [read]. **So none of the four negative forms B1
measured is surface-reachable** — they require a programmatic `Stmt`, as B1's S15 and this task's S23
both used. A **zero** coefficient is a different matter, and `outExtent`'s `.scale` arm then yields
`(0 · s).toNat = 0`. Measured end-to-end through `tlprog!{ … }` and `TLProgram.eval`:

```
S26a (Out[0*i] := X[i]):                  eval .ok; Out shape = [0], data = #[]
S26b (Out[0*i + 0] := X[i]):              eval .ok; Out shape = [0], data = #[]
S26c (Out[2*i] := X[i] — CONTROL):        eval .ok; Out shape = [8],
                                            data = #[1, 0, 2, 0, 3, 0, 4, 0]
  (slots: [[LHSSlot.affine (IdxExpr.scale 0 {i})]] and [[LHSSlot.affine (IdxExpr.scale 2 {i})]])
S26d (Out[0*i], then Y[k] := Out[k]):     eval FAILED: affine size system non-positive (uid 2) …
S26e (Out[2*i], then Y[k] := Out[k]):     eval .ok; Out = some [8], Y = some [8]
```

[snippet, S26]. So `Out[0*i] := X[i]` — four words of ordinary surface syntax, with `axis i : ℕ = 4`
— compiles, evaluates `.ok`, and returns an **empty** `Out` with all four writes silently dropped and
no diagnostic. That is **live at `9680b92`**, not latent.

### Verdict on B1-F9

**Not rejected on the scatter path.** The rejection that exists lives in the *sizing solver*, fires
only when the zero-extent output is read downstream, and attributes the failure to the reader's axis.
A zero-extent scatter output that is a program's final output evaluates `.ok` to an empty tensor with
every write dropped. Reachable from surface syntax via a zero coefficient (S26a/S26b), and from a
programmatic `Stmt` via any of B1's four negative forms (S23a–S23d).

**Cell status.** B1 recorded `outExtent` as a `c` cell outside the 14-column grid; it stays outside
the grid and is now **adjudicated rather than flagged**: `c`, **not closed**, because the catcher
(the solver's `nonPositive`) fires in only one of the two consumer paths and never in `evalScatter`
itself — the same disqualification G22/G24 face. It is not a write-path cell of the scan surface, so
it is not part of B2-F1's 16.

**Scope note, so this is not read as more than it is.** The checked-plan backend does not see a
scatter at all today: `Compile.lean` throws `scatterOrAffineLhs` at three sites and
`checkScanLHSSlot` rejects `.affine` in every scan-block statement [read]. Every measurement above is
of the **legacy** evaluator. What makes it Task B2's business is that the Scatter slice is precisely
what carries `.affine` into the checked backend, at which point `outExtent`'s `some 0` becomes a
checked-plan `outputShape` dimension and a strided row's `scale = 0` degenerate case reaches
`classifyWriteRow` — where a zero coefficient is not a singleton nonzero at all and classifies as
`.pinned bias`, which is the `.const` arm's image, not the strided one. That reclassification is
worth a fixture and is named in §B2.6.

---

## B2.6 — B1-F10 ANSWERED: the negative coverage the Scatter slice must add first

B1-F10's baseline reproduces exactly. Commands, run from `leanncd/`:

```text
grep -rn "#guard.*baseWriteRowsOk\|#guard.*stepWriteRowsOk" test/       → 5 hits, all in
                                                                          test/Eval/Plan/ScanTest.lean
grep -rn "#guard *!.*WriteRowsOk\|#guard *¬.*WriteRowsOk" test/         → 0 hits
grep -rn "baseWriteRowsOk\|stepWriteRowsOk" test/ | grep -i false       → 0 hits
grep -rn "writeGeometryNotAdmitted" test/                               → 3 assertions, all
                                                                          `.writeGeometryNotAdmitted false 0`
```

[read]. So: all five geometry `#guard`s are acceptances, there is no negated `#guard` and no
`== false` on either predicate, and every plan-level `writeGeometryNotAdmitted` assertion carries
`isBase = false` — **zero base-phase geometry-admission fixtures**, which is the phase B2-F1 lives in.

One sharpening, so B1-F10 is not read wider than it is: the *value*-predicate siblings **do** have
base-phase negative fixtures — `writeFreeExtentMismatch true 0 0 #[2,2] #[5]`,
`writePinnedLiteralOutOfRange true 1 0 #[2,2]` and `baseWritesOverlap 0 0 1` in `ScanTest.lean`, plus
two `.scan (.baseWritesOverlap "sc2" "dp" 0 1)` assertions in `ScanCompileTest.lean`
[read, `grep -rn "writeFreeExtentMismatch\|writePinnedLiteralOutOfRange\|baseWritesOverlap" test/`].
The gap is specific to **geometry admission** at base.

### Finding B2-F5 — the 6 new `b` cells are not locatable by any test that could exist today

R15 and R16 across columns 5, 11 and 12 are `b` on `stepWriteRowsOk`'s clauses 2 and 3, and **no test
can locate them at `9680b92`**, because the constructor they classify does not exist: there is no way
to write `#guard stepWriteRowsOk … #[some (.strided …)] == false`, and no source program can produce
such a row while `checkScanLHSSlot` rejects `.affine`. This is a different status from B1-F10's 10
unlocated cells (which *could* be pinned today and simply are not), and it is why these six are
counted separately in §B1.5's updated gate line.

### The negative coverage to add BEFORE touching `stepWriteRowsOk`'s clause 2

Named, not written — the brief's instruction. Ordered so that each item is a prerequisite of the
next, and each names the assertion it must make.

**Tier 1 — predicate-level `#guard`s, the first negative `#guard`s either predicate has ever had.**
These are the ones that must exist *before* clause 2 is edited, because they are what would catch a
clause-2 edit that widens acceptance:

1. `stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.strided 0 2 0), some (.free 0)] == false`
   — a strided row at a **non-advancing** dimension, rejected by clause 3 (R16).
2. `stepWriteRowsOk #[0,1] 1 #[some (.strided 0 2 0), some (.advancing 1), some (.free 0)] == false`
   — a strided row at an **advancing** dimension, rejected by clause 2 (R15).
3. `stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.free 0), some (.strided 0 2 0)] == false`
   — a strided row at the **cover** position, i.e. where clause 4's `filterMap` would silently drop
   it; asserts the rejection comes from clause 3 rather than from an accidental cover mismatch.
4. **The three positive controls those three would otherwise pass vacuously**:
   `stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.free 0)]`,
   `stepWriteRowsOk #[0,1] 1 #[some (.advancing 0), some (.advancing 1), some (.free 0)]`, and one
   acceptance of whatever strided placement the slice *does* admit at step, if any.
5. **Retrofit for B1-F10's own 10 unlocated cells while the file is open**, since they need no new
   constructor: `stepWriteRowsOk #[0] 1 #[some (.pinned 0), some (.free 0)] == false` (R3) and
   `stepWriteRowsOk #[0] 1 #[some (.free 0), some (.free 1)] == false` (R7), currently evidenced only
   by B1's S3.

**Tier 2 — base-phase geometry-admission fixtures, the family with zero members.** Each asserts
`checkScanPlan` returns `.writeGeometryNotAdmitted true wi` — the `isBase = true` form no fixture
carries:

6. A base write carrying a strided row that the slice's `baseWriteRowsOk` clause **rejects**
   (whichever way B2-F1 is fixed). This is the fixture that pins the fix.
7. **The acceptance control it needs**: the same base write with the strided row's extent agreeing
   with the state dimension per §B2.4's formula — `checkScanPlan .ok`, and `runDenseScan` producing
   the *stride-spaced* data, not merely `.ok`. Without a data assertion this fixture cannot
   distinguish "wrote the right cells" from "skipped every write", which is exactly the failure mode
   B2.5 found on the legacy scatter path.
8. A base write whose strided row's extent **disagrees** — asserting
   `writeFreeExtentMismatch true …`, joining the existing base-phase fixture for the `.free` case.
9. A base write whose strided row's coordinate would leave the state dimension at some coordinate but
   not at coordinate 0 — the `(0, 7, 14)` shape of G29. Its point is that a fixture asserting only
   the *first* coordinate lands in bounds would pass a broken clause.
10. A **negative-offset** strided base row, asserting rejection rather than the silent
    `Int.toNat` collapse onto the lower boundary that G29 measured. This one has no `.free`/
    `.advancing` analogue anywhere, because neither kind can produce a negative coordinate.

**Tier 3 — the two boundary cases §B2.1 and §B2.5 turned up, each a one-line assertion:**

11. `scale = 0` reclassification: a strided-shaped row with coefficient `0` is **not** a singleton
    nonzero and classifies as `.pinned bias` (the `.const` arm's image). Assert that, so a future
    strided branch cannot quietly claim it.
12. `scale = 1, offset = 1` at a **context** position stays `.advancing`, and at an **output**
    position becomes strided — the ordering obligation of §B2.1 point 4, and the one assertion that
    would fail if the strided branch were placed before the advancing branch.

**Tier 4 — differential, not predicate-level.** `test/Eval/Plan/DifferentialTest.lean`'s
`scanParityCheck` and `test/Eval/PropertyOracle/ScanUnroll.lean`'s `independentRun` are the
three-way gate, and `ScanUnroll.lean` *deliberately* calls no `writeRowKinds`/`applyAffine`/scan-write
helper (plan §4.8) [read]. A strided base write must be added to the oracle's own rewrite by hand for
the third leg to stay a differential — noting it here because it is the item most likely to be
skipped, and skipping it silently converts a three-way gate into a two-way one.

---

## B2.7 — Where barrier 2 disappears, and what barrier 1 alone does NOT cover

B1 established two independent barriers holding the `.advancing`-at-base case latent, and recorded
that the second disappears when B2 lowers `Compile.lean`'s base `.affine` arm. Both halves confirmed
here, and the conclusion for a **strided** row is different from the conclusion for an advancing one.

**Barrier 2, re-read and confirmed.** `Compile.lean`'s base-write construction loop emits exactly two
row shapes — an all-zero coefficient row with the literal as bias, from `.iterAt _ lit`; and a single
`1` at position `freeSeen` with bias `0`, from `.free`/`.freeNorm` — with the remaining arm
`| .iterNext _ | .affine _ =>` throwing `CapabilityError.unsupportedLhsSlot` [read]. The step loop's
catch-all is the differently-shaped `| .iterAt .. | .affine _ =>`, same throw [read]. **Lowering the
base loop's `.affine` arm is exactly what the Scatter feature must do, and it is what removes
barrier 2.**

**A third barrier B1's case did not have.** For a strided row there is also a **preflight** barrier:
`checkScanLHSSlot`'s `| .affine _ => throw (.scatterOrAffineLhs s!"{stmtName}: affine LHS slot")`
rejects an affine LHS slot in *every* base and recurrence statement of an admitted `.scan`, before
sizes exist [read]. Call it barrier 0. It is not a barrier for B1-F2, because `.iterNext` and
`.iterAt` are both *admitted* at preflight — so B1's "two independent barriers" is correct for its own
case and is not being corrected here. But the Scatter slice must lift barrier 0 **and** barrier 2 to
lower an affine LHS write at all, and lifting barrier 0 is also what turns B2-F6's multi-axis
rejection from a source-locating capability error into a positional `writeGeometryNotAdmitted`.

**What barrier 1 alone then covers, and what it does not.** Barrier 1 is one expression,
`let contextWidth := if isBase then 0 else st.advancingDims.size` [read], and its whole force is that
it makes a `p < contextWidth` test unsatisfiable, since no `p : Nat` is `< 0`. Therefore:

- **It covers exactly the `.advancing` kind** — the only current branch of `classifyWriteRow` whose
  guard is `p < contextWidth`. Measured by B1: `(classifyWriteRow 0 #[1] 1, classifyWriteRow 0 #[1,0]
  1, classifyWriteRow 0 #[0,1] 1)` → `(none, none, none)` [snippet, S1].
- **It does not cover a strided row at all**, under §B2.1's decision A. The strided guard is
  `p ≥ contextWidth`, which at `contextWidth = 0` is *satisfied by every* `p` — the opposite polarity.
  Barrier 1 is not a weakened defence for B2-F1; it is **no defence**. Measured on the model:
  `classifyA 0 #[2] 0` → `some (.strided 0 2 0)`, and the resulting rows pass `baseWriteRowsOk`
  [snippet, model].
- **It does not cover a `.free` row at an advancing dimension either** — B1-F4, live and memory-safe
  today, independent of any of this.

So after the Scatter slice lands, the base-phase picture is: `.advancing` stays latent behind barrier
1 alone (B1-F2, 10 cells, the *"single `if isBase then 0`"* B1 warned becomes the whole defence);
`.free` at an advancing dimension stays live-and-safe (B1-F4, 5 cells); and **strided becomes live
and unsafe with no barrier of any kind** (B2-F1, 16 cells). The three are independent, and only the
third is created by the feature.

---

## B2.8 — Gate, over the appended rows

> Every forbidden cell needs a located test. No cell may be silently ignored.

- **6 new `b` cells** (R15, R16 × cols 5, 11, 12): **0 located, and 0 locatable at `9680b92`** — the
  `strided` constructor they classify does not exist, so no `#guard` and no plan fixture can name
  them (B2-F5). §B2.6 items 1–4 are the tests that must exist the moment it does. Combined with B1's
  16: **22 `b` cells — 6 located by repo fixtures, 10 located only by B1's spikes, 6 not locatable.**
- **36 new `c` cells**: all adjudicated in §B2.3 across 14 groups — **7 groups / 20 cells closed**
  (structurally, by an **in-phase** catcher whose clause is quoted, by evidence-carrying
  construction, or as conservative-and-measured) and **7 groups / 16 cells open**, collapsing to one
  finding, **B2-F1**. No `c` cell was softened to "unlikely" or "defensive"; no write-path cell was
  closed as backstopped by `gatherFactor`'s `inBoundsPerDim`; and no cell was closed by naming a
  catcher that cannot fire in its own phase — every closure whose catcher is `stepWriteRowsOk` is a
  step-phase group, and the two base-phase value-predicate groups (G22, G24) are **open** for exactly
  the reason G16 was reopened.
- **0 new `a` cells** — B2-F2, a finding in its own right.
- **Findings outside the cell grid**: **B2-F2** (no site requires a strided row), **B2-F3** (four
  docstrings plus one AGENTS.md node enumerate the constructor set exhaustively and go stale),
  **B2-F4** (`freeExtentsAgree`'s equality is the shared formula's `scale=1, offset=0` case, and the
  tempting tighter bound is the `scatterOutDim` drift shape), **B2-F5** (6 `b` cells not locatable),
  **B2-F6** (the minimal strided kind admits a strict subset of the affine LHS forms `outExtent`
  prices). Plus two inherited findings **answered**: **B1-F9** (§B2.5 — not rejected on the scatter
  path; live from surface syntax via a zero coefficient) and **B1-F10** (§B2.6 — the negative
  coverage named, in four tiers).

Every verdict above carries either a quoted clause from the code, a construction with verbatim
observed output, or — where a fourth constructor was unavoidable — a `[snippet, model]` observation
against a verbatim transcription, paired with a `[snippet]` measurement of the real clause. The one
claim that is **not** a measurement is §B2.1's scope assumption, and it is labelled as such there.

<!-- END OF TASK B1 AND B2 SECTIONS — the next task appends below this line. -->

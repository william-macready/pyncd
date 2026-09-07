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

<!-- END OF TASK B1 SECTION — Task B2 appends below this line. -->

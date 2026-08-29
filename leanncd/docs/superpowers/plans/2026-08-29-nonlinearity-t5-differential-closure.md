# Slice T5 — differential documentation and closure

**Scope:** Task 5 only of
[`papers/nonlinearity_split_pair_direct_lowering.md`](../../../../papers/nonlinearity_split_pair_direct_lowering.md)
(that document's §3.7). That document remains the canonical record; this is the executable plan for
its fifth and final slice. **Read §3.7's opening blockquote first** — it records that steps 1–3 are
already satisfied and names two traps that would otherwise cause wrong edits.

**Deliberately NOT in this slice:**

| Item | Why not |
|---|---|
| Steps 1–3 of §3.7 (differential cases, key/warning comparison, the two gates) | **Already satisfied** — Task 4 built them; §0.3 re-verifies. Adding anything here is duplicate work |
| Repairing `experiments/jax_bridge/EvalPlanCodegen.lean` | pre-existing, unrelated, unscheduled |
| Any code change | this slice is documentation plus a completion record; the only Lean edit is one stale comment |

This is the last slice of the nonlinearity plan. When it lands, §3.7 gets its completion blockquote
and the master plan is fully executed.

---

## §0 Verified baseline

Executed in this worktree against `main` at `9f5cb46` on 2026-08-29. Re-run §0.1–§0.3 before
editing; a failure there is base drift, not an implementation defect.

### 0.1 A read-only audit already did the finding half — work from it

[`leanncd/docs/superpowers/briefs/2026-08-29-task5-stale-doc-audit-RESULTS.md`](../briefs/2026-08-29-task5-stale-doc-audit-RESULTS.md)
(commit `2cd1234`) classifies every candidate passage in all 24 §3.7 documents as
**STALE / STILL TRUE / UNCERTAIN**, each with the code fact that settles it. Its verdicts were
spot-checked against the tree by the controller and hold.

**That table is this slice's worklist.** Do not re-derive it. Do check each passage against the tree
as you edit it — the audit says what is wrong, not what the replacement should say, and the
replacement is where this project's recurring defect lives.

### 0.2 The §3.7 scan is necessary but NOT sufficient — this is the plan's central structural fact

The scan was run verbatim in this worktree (script preserved at `leanncd/spikes/scan.sh`, gitignored).
Observed — **10 files match, 23 matches total**:

```
LeanNCD/DSL/AGENTS.md:1        realize.md:2              SORRY_INVENTORY.md:2
../papers/eval_ir.md:2         ../papers/todo.md:1       ../papers/code_walkthrough.md:4
../papers/NaperianTypingIntegrationPlan.md:2             ../papers/NaperianTyping.md:2
../papers/leanncd.md:5         ../docs/superpowers/specs/2026-06-12-…-design.md:2
```

Two of those ten are **false positives that must not be "fixed"** (§0.4). So the scan drives fixes in
**eight** documents.

But the audit found stale claims in **twelve**. Four carry stale claims the regex structurally cannot
match — it only knows the `splitNonlins`/`LinearProgram`/`%nl` family:

| Document | Stale claim the scan cannot see |
|---|---|
| `leanncd/test/Eval/Plan/DifferentialTest.lean` | its header comment still says the corpus splits 9 / 4 / 4 |
| `papers/jax_evalplan_architecture.md` | "`Compile.lean` rejects every pointwise and axiswise nonlinear statement"; and `PlanStep` described as the `.assign`/`.scan` sum |
| `papers/copilot_code_analysis.md` | `LinearProgram` called a distinct type; `splitNonlins` lowering activations |
| `papers/wave_f_scanplan_proposal.md` | "nonlinear scan bodies still rejected"; `RawPlanBlock` as "ordered assignments"; "nonlinearities are not yet plan operations" |

Two more documents are **outside the scan's file list entirely** (§0.5).

**Consequence, and the thing most likely to go wrong in this slice: a green scan does not mean the
sweep is done.** The scan gates one family; the audit table gates the rest. Both are required by §4.

### 0.3 Steps 1–3 are satisfied — verify, do not rebuild

Re-verified directly, not taken from the audit:

| Step | Evidence |
|---|---|
| 1 — five differential cases | `nonlinearScanFixtures` in `DifferentialTest.lean` lists six groups covering all five §3.7 shapes, each run through `scanParityCheck` |
| 2 — exact source-visible keys and warning order | `scanParityCheck` does whole-environment key equality, and compares warnings with `decide (planReport.warnings = refReport.warnings)` — **list** equality, so order and payload both count |
| 3 — the two gates | `total == 3832 && accepted == 3832 && rejCounts.isEmpty`, and `total == 17 && accepted == 13 && nonlin == 0 && agg == 4`, both live assertions in `DifferentialTest.lean` |

### 0.4 The two traps — each would produce a wrong edit

**Trap 1 — scan false positives.** Two of the ten matched files are correct as written:

- `LeanNCD/DSL/AGENTS.md` matches only because the regex spans two adjacent phase-table rows. Its
  prose already states `splitNonlins` "survives only as a regression-only helper, off the production
  chain." **Correct. Do not edit.**
- `papers/todo.md`'s matches all sit inside a section carrying a permanent archival banner.
  **Correct. Do not edit.**

Because the scan cannot be made to pass on those two without damaging them, §4 requires the scan's
*residual* matches to be exactly these two files, not zero.

**Trap 2 — correctly-banner'd history is not staleness.** Two constructs must be preserved:

- `DSL/AGENTS.md`'s "runs constantly" claim is immediately followed by an inline
  **⚠️ Superseded 2026-08-26** banner stating current behaviour. The pair is correct; deleting the
  historical half destroys a deliberate record.
- `2026-08-21-wiring-loop-generalization.md` describes `RawPlanBlock.assignments` as the only node
  kind. That is accurate **history of a completed slice** (the rename happened later, in Task 3).
  Preserve it. Only that document's *active next-slice pointer* is a defect (§0.5).

### 0.5 Two documents the §3.7 Files list omits

The list predates Tasks 3–4:

- **`leanncd/docs/superpowers/plans/2026-08-21-wiring-loop-generalization.md`** — §3.7 already names
  this one: its completed record is correct, but its **active next-slice pointer aims at
  `2026-08-21-nonlinearity-in-scans.md`, which is itself permanently archived.** An active pointer to
  an archived plan is the defect; repoint it at the canonical plan.
- **`leanncd/AGENTS.md`** — the subsystem navigation doc, **not in the Files list at all**. It cites
  the `splitNonlins` `agg`-drop as a live `[fail-loud]` violation. The pass is off-chain now and the
  drop is provably vacuous (a non-sum `agg` statement has `nonlin = .identity` by construction, so
  the split never carries a droppable `agg`). The entry needs **re-framing as historical, not
  deletion** — it is still a true account of a real past bug.

### 0.6 No code defect exists to fix

The audit found none, and disposed of the only candidate: `semantic_payload_audit.md`'s
`splitNonlins` `agg`-drop is doubly dead (off-chain, and vacuous). It explicitly did **not** claim
`physicalizeOne` is clean — that is code verification beyond a documentation audit. **If this slice
finds a real code defect, that is a §3 stop condition, not a doc edit.**

### 0.7 Every path this plan names exists

`ls`-verified in this worktree: all 24 §3.7 Files-list documents, plus `leanncd/AGENTS.md`,
`2026-08-21-wiring-loop-generalization.md`, `DifferentialTest.lean`,
`jax_evalplan_architecture.md`, `copilot_code_analysis.md`, `wave_f_scanplan_proposal.md`.

---

## §1 Global constraints

- **The audit table is the worklist; the tree is the authority.** Every replacement sentence must be
  checked against a current identifier or observed value before it ships. The audit says what is
  wrong; it does not say what is right.
- **Never edit the two false positives** (`DSL/AGENTS.md`'s phase table, `todo.md`) or the two
  banner'd-history constructs (§0.4). The scan's expected residual is **exactly those two files**.
- **Archived and superseded documents keep their content.** `papers/todo.md`,
  `2026-08-21-nonlinearity-in-scans-design.md`, `2026-08-21-nonlinearity-in-scans.md`, and
  `papers/nonlinearity_split_pair_reconstruction_archived.md` are historical. Their banners are
  verified correct; touch only a banner that is missing or misdirecting.
- **The canonical record is excluded from the scan by design** — its rejected terminology is correct
  as history. Its only edit this slice is §3.7's completion blockquote.
- **No code change.** The single Lean edit is `DifferentialTest.lean`'s stale 9/4/4 header comment;
  its executable assertion is already correct and must not move.
- **Exact values that must appear correctly wherever the sweep restates them:** the corpus is
  **17 total / 13 accepted / 0 unsupportedNonlin / 4 unsupportedAgg**; the scan-free gate is
  **3,832**; `compile = compileToScheduled >>= route`; `LinearProgram` is a **deprecated alias**
  (`abbrev LinearProgram := ScanProgram`); `RawPlanBlock.steps : Array BlockStep`; `BlockStep` is
  `.assign`/`.pointwise`/`.axiswise`; `PlanStep` is `.assign`/`.scan`/`.pointwise`/`.axiswise`;
  `causalityFailure`'s second field is `blockStepIndex`; Eval lowering is **two-step**
  `assign → pointwise/axiswise`.
- **No `File.lean:NNN` line numbers** in any shipped text — identifiers only. Line numbers in the
  audit table are for locating passages during this slice, not for quoting into a document.
- **No `sorry`, `admit`, or `axiom`.** Full `Tests` and `LeanNCD` builds gate the slice.
- **Every mutation cycle is mutate → observe the named check fail → restore → observe pass.**
  Predicting a failure does not count.

---

## §2 Task breakdown

Three tasks, split by **failure mode**, which here differs sharply between document families.

| Task | Deliverable | Documents | Cycles | Risk driver |
|---|---|---:|---:|---|
| 1 | The scan-visible family: pipeline descriptions presenting `splitNonlins`/`%nl`/`LinearProgram` as live | 8 | 1 | mechanical and template-shaped, but 8 documents × several passages; the risk is a template applied where the passage needed judgment |
| 2 | The scan-invisible claims, plus the two omitted documents | 6 | 0 | **no mechanical gate** — nothing tells you when this is done except the audit table and a re-read; staged-scope and historical-record claims need judgment, not a template |
| 3 | Differential mutation cycles, completion record, closure gate, two reviews | 2 | 2 | the completion record's own accuracy claims — the exact artifact this project has repeatedly got wrong |

**Why this split.** Task 1's failure mode is *mechanical*: a wrong or over-broad substitution, and
the scan tells you if you missed one. Task 2's is *judgmental*: deciding whether
`wave_f_scanplan_proposal.md`'s "should initially admit only identity" is a stale claim or an
accurate description of a past milestone, with no gate to catch a wrong call. A reviewer could
approve the template sweep and reject a judgment call, or vice versa. Task 3 is separate because its
deliverable is a record whose claims are themselves the thing most likely to be wrong.

**What a diff cannot show here.** A review package shows the passages you *changed*. This slice's
recurring defect family is a stale claim in a passage nobody flagged — the audit's own stated
limitation is that it located candidates with a marker `rg`, so a stale claim phrased without those
markers could be missed. **Therefore each task must re-read every document it edits, end to end,
after editing** — not only the flagged passages — and record that it did. That sweep is a deliverable,
not a courtesy.

---

### Task 1 — the scan-visible family

**Outcome.** The eight scan-flagged documents no longer present `splitNonlins`, `%nl` names, or
`LinearProgram`-as-a-distinct-type as live pipeline elements. The scan's residual is exactly the two
false-positive files.

**Documents** (audit rows give the passages):

`leanncd/realize.md` · `leanncd/SORRY_INVENTORY.md` · `papers/eval_ir.md` · `papers/leanncd.md` ·
`papers/code_walkthrough.md` · `papers/NaperianTyping.md` ·
`papers/NaperianTypingIntegrationPlan.md` ·
`docs/superpowers/specs/2026-06-12-lean-dsl-tensor-logic-design.md`

**Implementation**

1. For each document, work its audit rows. The replacement must state current behaviour:
   `compileToScheduled` is logical and emits no `%nl`; public `route` performs checked private
   physicalization before the unchanged `routeCore`; `splitNonlins` survives regression-only, off the
   production chain; `LinearProgram` is a deprecated alias.
2. **`NaperianTypingIntegrationPlan.md` is scoped by §3.7 step 4**: it is a broad historical plan not
   otherwise being revised, so replace **only** its active `splitNonlins` invariant with a dated
   pointer to the canonical boundary. Do not modernise the rest of it.
3. `papers/eval_ir.md` carries the largest cluster, including the three-step lowering description and
   the "`RawPlanBlock` therefore still contains `Array AssignPlan`" claim — the latter is a Task-3
   staleness, not a Task-1 one, so the replacement must name `steps : Array BlockStep`.
4. Re-read each edited document end to end and record any stale claim the audit did not flag.

**Mutation cycle (1)** — §3.7's third: **restore one prohibited multiline active pipeline form** into
a document you just fixed (e.g. re-insert `finalizeScans → splitNonlins → schedule` into
`realize.md`), run the scan, observe it match that file, restore, observe the residual return to the
two false positives.

**Gate**

```bash
cd leanncd
bash spikes/scan.sh        # residual must be exactly DSL/AGENTS.md and ../papers/todo.md
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

Builds are unaffected by prose edits and must be unchanged; run them to prove that.

---

### Task 2 — the scan-invisible claims and the two omitted documents

**Outcome.** Every stale claim the regex cannot see is corrected, the wiring-loop pointer directs to
the canonical plan, and `leanncd/AGENTS.md`'s `agg`-drop entry is reframed as history.

**Documents**

- `leanncd/test/Eval/Plan/DifferentialTest.lean` — header comment 9/4/4 → 13/0/4. **Comment only**;
  the executable assertion is already correct.
- `papers/jax_evalplan_architecture.md` — the "rejects every pointwise and axiswise" claim, and the
  `PlanStep`-as-`.assign`/`.scan` enumeration.
- `papers/copilot_code_analysis.md` — `LinearProgram` as a distinct type; `splitNonlins` lowering
  activations.
- `papers/wave_f_scanplan_proposal.md` — three claims, and **the judgment call of this slice**: its
  "should **initially** admit only identity" passage is a staged-scope description the audit rated
  UNCERTAIN. Decide explicitly whether it reads as a historical milestone (leave, perhaps dated) or
  as current capability (correct it), and **record the reasoning** — this is exactly the kind of call
  a later reader will otherwise re-litigate.
- `leanncd/docs/superpowers/plans/2026-08-21-wiring-loop-generalization.md` — repoint the active
  next-slice pointer at the canonical plan. **Preserve** its historical `RawPlanBlock.assignments`
  account.
- `leanncd/AGENTS.md` — reframe the `agg`-drop entry as historical; it is a true account of a real
  past bug, so do not delete it.

**Implementation**

1. Work each document's audit rows, checking every replacement against the tree.
2. Re-read each end to end afterwards; this task has **no mechanical completion signal**, so the
   re-read is what stands in for one.
3. Record the `wave_f_scanplan_proposal.md` staged-scope decision and its reasoning.

**Mutation cycles:** none. Nothing here is regex-detectable, which is precisely the point — say so in
the record rather than inventing a cycle that cannot fail.

**Gate**

```bash
cd leanncd
"$HOME/.elan/bin/lake" build Eval.Plan.DifferentialTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

The `DifferentialTest` build must be green with its assertion unmoved — the edit is a comment.

---

### Task 3 — mutation cycles, completion record, closure

**Outcome.** The differential's teeth are proven, §3.7 gains its completion record and blockquote,
and the master plan is closed.

**Files**

- `leanncd/test/Eval/Plan/DifferentialTest.lean` (mutation target only — restored after each cycle)
- `papers/nonlinearity_split_pair_direct_lowering.md` (§3.7 completion record and blockquote)

**Mutation cycles (2)** — §3.7's first two, against the existing differential:

| # | Mutation | Must fail |
|---:|---|---|
| 1 | remove one logical result from a differential report before comparison | `scanParityCheck`'s environment-equality check, on a named nonlinear group |
| 2 | compare the preactivation instead of the result | a group whose preactivation and result differ in value — `group4/nonlinearBase` is the natural choice, since `relu` of its negative input makes them differ |

Both mutate code Task 4 shipped. That is deliberate: these cycles prove the differential that
underwrites the whole slice actually has teeth, and §3.7 requires them.

**Completion record.** Append to §3.7 and add the completion blockquote to the master plan, per the
convention Tasks 1–4 used. It must carry: commits, the four gate job counts, the scan's residual
(and why it is two files, not zero), each mutation cycle observed-not-predicted, the
`wave_f_scanplan_proposal.md` staged-scope decision, the end-to-end re-read results from Tasks 1–2,
and both review adjudications.

**The record's own claims are the highest-risk artifact in this task** — the `slice-plan` skill calls
this out specifically, and this project has been bitten by it repeatedly, most recently in Task 4.
Diff or grep every claim of the form "X is now Y" before writing it.

**Gate**

```bash
cd leanncd
bash spikes/scan.sh
"$HOME/.elan/bin/lake" build DSL.Pipeline.RouteWeaveTest Bridge.AcsetCodecTest Bridge.AgreementTest Bridge.RealizeTest
"$HOME/.elan/bin/lake" build Eval.Plan.DifferentialTest Eval.PropertyOracle.ScanOracle
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

**Reviews.** Two independent whole-branch lenses, per §3.7:

1. **Logical scheduling / categorical adapter / routed semantics** — do the corrected passages
   describe the actual pipeline, and is any archived or banner'd content damaged?
2. **Checked Plan / oracle independence / differential soundness / stale-doc inventory** — are the
   Plan-layer and corpus claims right, and did the sweep miss a document?

---

## §3 Stop conditions

Stop and report rather than improvise if:

- a real **code** defect surfaces — that is a separate slice, not a doc edit (§0.6);
- the scan's residual is anything other than the two known false positives, and the extra match is
  not a genuine stale passage you can fix;
- an audit row's verdict does not survive contact with the tree — the audit was spot-checked, not
  exhaustively re-verified, so a wrong row is possible and is worth reporting rather than quietly
  working around;
- a "stale" passage turns out to be load-bearing history whose removal would destroy a deliberate
  record (§0.4's trap 2 in a form this plan did not anticipate);
- `DifferentialTest.lean`'s executable assertion would have to change — only its comment is stale;
- either differential mutation cycle produces **zero** failures: the guard is vacuous, which is a
  defect in the differential, not a pass.

---

## §4 Definition of done

- All ~31 audit-flagged STALE passages corrected, each replacement checked against the tree.
- The §3.7 scan's residual is **exactly** `LeanNCD/DSL/AGENTS.md` and `papers/todo.md`, both
  documented as false positives — **not zero**.
- The four scan-invisible documents and the two omitted documents (§0.5) are corrected.
- `DSL/AGENTS.md`'s banner'd history and `wiring-loop-generalization.md`'s historical record are
  **intact**; only the latter's active pointer changed.
- Every document edited in Tasks 1–2 was re-read end to end, with any unflagged stale claim recorded.
- The `wave_f_scanplan_proposal.md` staged-scope call is made and its reasoning recorded.
- Both differential mutation cycles ran mutate/fail/restore/pass, observed not predicted.
- Archived documents and the canonical record are unchanged apart from §3.7's completion blockquote.
- `Tests` and `LeanNCD` green, unchanged by prose edits; no `sorry`.
- Both whole-branch reviews green or adjudicated.
- §3.7 carries its completion blockquote, and the master plan's status line reads fully executed.

---

## §5 Execution record

*(To be appended on execution — commits, the four gate job counts, the scan's residual, both mutation
cycles observed-not-predicted, the staged-scope decision, the end-to-end re-read findings, and both
review adjudications. Cite identifiers, never `File.lean:NNN`.)*

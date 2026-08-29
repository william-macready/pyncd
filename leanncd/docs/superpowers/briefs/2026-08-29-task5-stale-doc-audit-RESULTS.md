# RESULTS: audit of active documentation for claims made stale by Tasks 1–4

**Audit type:** read-only. Nothing below was rewritten; this is a findings report only.
**Against:** the tree at `85fa004` (this worktree's `HEAD` is exactly the brief's target SHA — verified
`git rev-parse HEAD` = `85fa0049112fac4a0f9ac584d2d98f6bf9a059d4`).
**Executed in worktree:** `pyncd.worktrees/gpt56-minimize-prompts-task-audit` (same tree/base as the
main checkout; the brief allows a branch as the delivery target).

## Method (so the next person can re-derive every verdict)

1. Established code ground-truth for Tasks 1–4 by reading the actual Lean sources (identifiers and
   line numbers below). Every verdict in Part 2 is settled by one of these facts or by an `rg`/`view`
   quoted in the row.
2. Ran §3.7's stale-recommendation scan **verbatim** (Part 1).
3. Located candidate passages in all 24 §3.7 Files-list documents with a marker `rg`, then read each
   candidate passage in context and classified it.
4. Ran the §3.7 steps 2–3 gap check against the tree.

### Code ground-truth (verified at `85fa004`)

| Fact (Task) | Evidence in the tree |
|---|---|
| **F1** `TLProgram.compile = compileToScheduled >>= route`; the schedule is **logical** | `LeanNCD/DSL/Compile.lean:20-23,41-42` ("**No `splitNonlins`**… no generated `%nl…` name") |
| **F1** `compileToScheduled` does **not** call `splitNonlins` and emits **no** `%nl` names | `%nl` is minted only at `LeanNCD/DSL/Pipeline/Lowering.lean:44` (the regression path); `Compile.lean:41-42` |
| **F1** `route` does private checked physicalization before unchanged `routeCore` | `LeanNCD/DSL/Pipeline/RouteFragments.lean` (`physicalizeOne`/`fragmentClass`); `DSL/AGENTS.md:104` |
| **F1** `splitNonlins` survives but is **regression-only, off the production chain** | `Lowering.lean:10-12` ("REGRESSION-ONLY, off the production chain"), def at `Lowering.lean:88`; `Types.lean:46,51` |
| **F1** `LinearProgram` is a **deprecated compatibility alias**, not a distinct type | `Types.lean:53` `abbrev LinearProgram := ScanProgram` (docstring `Types.lean:42-52`) |
| **F3** `RawPlanBlock` field is `steps : Array BlockStep` (was `assignments : Array AssignPlan`) | `LeanNCD/Eval/Plan/RawStep.lean:119-123` |
| **F3** `BlockStep = .assign \| .pointwise \| .axiswise` | `RawStep.lean:67-71` |
| **F3** `checkPlanBlock`/`runDenseBlock` dispatch all three kinds | `LeanNCD/Eval/Plan/Block.lean:181,250` |
| **F3** `ScanPlanError.causalityFailure`'s 2nd field is `blockStepIndex` (was `stmtIndex`) | `LeanNCD/Eval/Plan/Scan.lean:186` `causalityFailure (stateIndex blockStepIndex termIndex factorIndex : Nat)` |
| **F4** `compileScan` **admits and lowers** nonlinear scan sources | `LeanNCD/Eval/Plan/Compile.lean:70-71,439,1011` |
| **F4** differential scan split is now **total=17, accepted=13, unsupportedNonlin=0, unsupportedAgg=4** (was 9/4/4) | `test/Eval/Plan/DifferentialTest.lean:817` (`total == 17 && accepted == 13 && nonlin == 0 && agg == 4`), rationale `L803-810` |
| **F4** two-step Eval lowering `assign → pointwise/axiswise` (supersedes any "three-step") | `LeanNCD/Eval/AGENTS.md:55` ("`.plain` branch now two-step-chains… an internal `.assign` that publishes no name, immediately followed by the real `.pointwise`/`.axiswise` step") |
| **F4** independent unroller preserves `.freeNorm` | `nonlinearScanFixtures` + `scanParityCheck` three-way gate, `DifferentialTest.lean:555-583` |

### Summary of results

- **Part 1 scan:** runs clean (no error); the gate **currently FAILS (exit 1) with matches** — the
  expected pre-Task-5 state, since the doc sweep has not happened. The matched lines are (a mix of)
  the stale passages this audit classifies below.
- **Part 2:** 24 documents assessed. **~31 STALE** passages (≈30 table rows + the wiring-loop pointer),
  concentrated in the active architecture papers and `realize.md`/`SORRY_INVENTORY.md`; the three
  superseded/archived scan documents plus `papers/todo.md` all carry **correct** archival banners; the
  canonical record is excluded by design.
- **One flagged non-table item:** `wiring-loop-generalization.md`'s active next-slice pointer aims at
  the superseded plan (as §3.7 predicted).
- **Real code defects:** **none found.** (The one candidate — `splitNonlins` dropping `agg` — is
  vacuous and unreachable; see the dedicated section.)
- **Gaps in the Files list:** several active docs outside the list also carry stale `splitNonlins`
  references; see that section.

---

## Part 1 — the specified §3.7 stale-recommendation scan (verbatim)

Command run verbatim from `§3.7` ("Gate"), from `leanncd/`:

```bash
active_docs=(
  LeanNCD.lean LeanNCD/Eval/AGENTS.md LeanNCD/DSL/AGENTS.md
  experiments/jax_bridge/README.md realize.md SORRY_INVENTORY.md
  ../papers/eval_ir.md ../papers/jax_evalplan_architecture.md ../papers/leanncd.md
  ../papers/code_walkthrough.md ../papers/NaperianTyping.md
  ../papers/NaperianTypingIntegrationPlan.md ../papers/copilot_code_analysis.md
  ../papers/restructure_suggestions.md ../papers/semantic_payload_audit.md
  ../papers/todo.md ../papers/wave_f_scanplan_proposal.md
  ../docs/superpowers/specs/2026-06-12-lean-dsl-tensor-logic-design.md
)
rg -n -U --multiline-dotall \
  'finalizeScans.{0,80}splitNonlins|splitNonlins.{0,80}(schedule|route|LinearProgram)|LinearProgram.{0,80}no nonlinearity|generated .?%nl.{0,80}(shared|scheduled|source-level)' \
  "${active_docs[@]}"
```

The scan did **not** error, and it is **not** "no matches". It matched (so the gate's
`if rg …; then exit 1` fires — the gate currently **FAILS**, as expected before the Task 5 sweep).
Exact output:

```
realize.md:114:           → lowerArith → finalizeScans → splitNonlins → schedule → route
realize.md:172:After compilation (`splitNonlins` + `schedule` + `route`):
../papers/NaperianTypingIntegrationPlan.md:208:finalizeScans
../papers/NaperianTypingIntegrationPlan.md:209:splitNonlins
../papers/NaperianTypingIntegrationPlan.md:240:finalizeScans
../papers/NaperianTypingIntegrationPlan.md:241:splitNonlins
../papers/todo.md:49:-> finalizeScans
../papers/todo.md:50:-> fork
../papers/todo.md:51:     |-> logical scheduling -> Backend Eval IR
../papers/todo.md:52:     `-> splitNonlins -> route scheduling -> categorical route
LeanNCD/DSL/AGENTS.md:26:| Phases 1-5 (assignUIDs/resolveDecls/checkReadRanks/checkDtypes/checkScatterNonlin/checkScatterNoScan/lowerArith/finalizeScans) | `Structural.lean` |
LeanNCD/DSL/AGENTS.md:27:| Phase 6-8 (schedule/route/buildStep/routeCore; `splitNonlins` survives only as a regression-only helper, off the production chain) | `Lowering.lean` |
../papers/code_walkthrough.md:378:The `LHSSlot.iterNext` slot on `l` is what tells the pipeline this is a recurrence — the output is the value of `S` at step `l+1`. The read of `S[j, l]` in the RHS refers to the value at the *current* step. `finalizeScans` later pairs these into a [`ScanStmt.scan`](…) structure, and `splitNonlins` separates the linear contraction from the `relu` into two scheduled steps.
../papers/code_walkthrough.md:455:  let e ← finalizeScans d
../papers/code_walkthrough.md:456:  let f ← splitNonlins e
../papers/code_walkthrough.md:468:             >=> unifyAxes >=> lowerArith >=> finalizeScans
../papers/code_walkthrough.md:469:             >=> splitNonlins >=> schedule
../papers/code_walkthrough.md:646:- **Aspect A (transformation):** how Stage 5 computes the routed artifact (`splitNonlins`, `schedule`, `route`).
../papers/code_walkthrough.md:647:- **Aspect B (artifact inspection):** what that routed artifact (`ThreadedComposed`) contains and which invariants the bridge requires.
../docs/superpowers/specs/2026-06-12-lean-dsl-tensor-logic-design.md:441:  →[finalizeScans] ScanProgram           -- no bare iterAt/iterNext LHSSlots
../docs/superpowers/specs/2026-06-12-lean-dsl-tensor-logic-design.md:442:  →[splitNonlins]  LinearProgram         -- no nonlinearity in RHSExpr.nonlin
../papers/eval_ir.md:381:10. `splitNonlins` isolates nonlinear operations into separate statements.
../papers/eval_ir.md:382:11. `schedule` topologically orders the result and rejects cyclic dataflow.
../papers/eval_ir.md:496:  internal assignment introduced by plan compilation has no name. A generated `%nl...` statement
../papers/eval_ir.md:497:  created earlier by `splitNonlins` is itself a scheduled source-level statement and therefore does
SORRY_INVENTORY.md:245:Kleisli chain (assignUIDs → resolveDecls → unifyAxes → lowerArith → finalizeScans →
SORRY_INVENTORY.md:246:splitNonlins → schedule → route), and `tl!{ … } : ThreadedComposed` compiles all five §12.1
SORRY_INVENTORY.md:384:  detected in `finalizeScans` (BEFORE `splitNonlins` lifts nonlinearities out) via the `isAffine` flag on
../papers/NaperianTyping.md:38:- nonlinearity isolation (`splitNonlins`),
../papers/NaperianTyping.md:39:- temporal scan extraction (`finalizeScans`, `evalScan`),
../papers/NaperianTyping.md:40:- routed executable graph (`ThreadedComposed`).
../papers/NaperianTyping.md:797:finalizeScans
../papers/NaperianTyping.md:798:splitNonlins
../papers/leanncd.md:1637:structure LinearProgram where
../papers/leanncd.md:1638:  decls    : List Decl
../papers/leanncd.md:1639:  stmts    : List ScanStmt             -- no nonlinearity in RHSExpr.nonlin (split into BrBase ops)
../papers/leanncd.md:1706:             >=> finalizeScans >=> splitNonlins >=> schedule >=> route
../papers/leanncd.md:1720:  →[splitNonlins]   LinearProgram         -- nonlinearity isolated into its own step
../papers/leanncd.md:1721:  →[schedule]       ScheduledProgram      -- live stmts (DCE); root = last stmt's output
../papers/leanncd.md:1734:| **splitNonlins** | Lifts `relu`/`softmax`/`normalize` out of `RHSExpr.nonlin` … |
../papers/leanncd.md:1744:- **finalizeScans** groups by iteration-axis UID … the `isAffine` flag on `ScanStmt.scan` is set here (before `splitNonlins`) …
../papers/leanncd.md:1745:- **schedule** does backward-reachability DCE; …
```

**Note on scan false positives.** The gate is a blunt substring gate. Two matched locations are
**not** stale and must not be "fixed":

- `LeanNCD/DSL/AGENTS.md:26-27` — line 27 already states `splitNonlins` "survives only as a
  regression-only helper, off the production chain" (i.e. it is **correct**; the regex matched the
  incidental `finalizeScans … splitNonlins` span across the two table rows).
- `papers/todo.md:49-52` — inside a section carrying a permanent archival banner (see Part 2).

---

## Part 2 — per-document audit

**Category legend.** Each document is placed in exactly one category (miscategorising is the most
likely way this audit goes wrong):

- **ACTIVE** — live documentation; claims are audited for staleness.
- **SUPERSEDED-WITH-BANNER** — the question is only whether the banner correctly redirects and whether
  active prose *recommends* the superseded approach; historical content is not flagged.
- **ARCHIVED** — superseded content is correct there; not audited.
- **CANONICAL** — the decision record; rejected/historical terminology is correct; **excluded** by §3.7.

**Verdict** is exactly one of **STALE / STILL TRUE / UNCERTAIN**.

### Findings table

| Document | Passage (quoted, ≤2 lines, w/ line) | Claim it makes | Verdict | Code fact that settles it |
|---|---|---|---|---|
| **DifferentialTest.lean** (ACTIVE) | L24-25: "the curated `enumScanCases` generator splits exactly **9 accepted / 4 `unsupportedNonlin` / 4 `unsupportedAgg`**" | corpus split is 9/4/4 | **STALE** | Same file, L817: `total == 17 && accepted == 13 && nonlin == 0 && agg == 4`; rationale L803-810 (9→13, nonlin 4→0). F4. |
| **CompileExamplesTest.lean** (ACTIVE) | L17-18: "At the `route` boundary the masked-softmax statement becomes a linear pre-activation step + a `softmax` step" | split happens at the route boundary | **STILL TRUE** | Matches F1: `route`/`RouteFragments.lean` `physicalizeOne` does the split; not `splitNonlins`. |
| **LeanNCD.lean** (ACTIVE) | L88: "── compile (**8 phases**) ─▶ ThreadedComposed" | compile is 8 phases | **UNCERTAIN** | `compile = compileToScheduled >>= route` (`Compile.lean:23`); the old 8-count included `splitNonlins` (now off-chain) and omits the added `reclassifyIterSlots`/`checkScatter*` phases (`DSL/AGENTS.md:104`). Count is imprecise; not a hard nonlinearity claim. |
| **LeanNCD.lean** (ACTIVE) | L88-89: "the evaluator consumes the PRE-route `ScheduledProgram` (`compileToScheduled`)… the routed `ThreadedComposed` collapses scans and is lossy" | logical schedule feeds Eval; routed form is lossy | **STILL TRUE** | F1: `Compile.lean` `compileToScheduled : … → ScheduledProgram`; consistent with logical-schedule design. |
| **Eval/AGENTS.md** (ACTIVE) | L55: "`.plain` branch now two-step-chains a `.pointwise`/`.axiswise` statement into an internal `.assign` that publishes no name" | two-step `assign → pointwise/axiswise` | **STILL TRUE** | F4; matches `Compile.lean` residualization. |
| **Eval/AGENTS.md** (ACTIVE) | L60: "`BlockStep` (`.assign`/`.pointwise`/`.axiswise`… the element type of a local block)… `RawPlanBlock` (its `steps` field holds those)" | block holds `steps : Array BlockStep` | **STILL TRUE** | F3: `RawStep.lean:67-71,119-123`. |
| **DSL/AGENTS.md** (ACTIVE) | L27: "`splitNonlins` survives only as a regression-only helper, off the production chain" | splitNonlins is regression-only | **STILL TRUE** | F1: `Lowering.lean:10-12`. (Matched by the Part-1 scan as a false positive.) |
| **DSL/AGENTS.md** (ACTIVE) | L104: "`route` (Phase 7-8: `physicalizeForRoute` first expands each nonlinear plain statement into a private producer/consumer pair… `splitNonlins` … is no longer on this chain" | route-boundary physicalization; splitNonlins off-chain | **STILL TRUE** | F1: `RouteFragments.lean`; `Lowering.lean:10-12`. |
| **DSL/AGENTS.md** (ACTIVE) | L125 "This split path… **runs constantly**… via `TLProgram.compileToScheduled`" **immediately corrected by** L126 "**⚠️ Superseded 2026-08-26**… read this entry as HISTORY… the 'runs constantly' claim above is false as of this flip" | L125 stale, but explicitly banner'd by L126 | **STILL TRUE** (as correctly-banner'd history) | The inline banner L126 correctly states the current behavior and directs to the canonical plan; F1. |
| **realize.md** (ACTIVE) | L110-114: "`TLProgram.compile`… chains nine phases: … → finalizeScans → **splitNonlins** → schedule → route" | splitNonlins is an active production phase | **STALE** | F1: `Compile.lean:23` `compile = compileToScheduled >>= route`; splitNonlins regression-only (`Lowering.lean:10`). |
| **realize.md** (ACTIVE) | L119-122: "**`splitNonlins`** peels each nonlinearity onto its own node… Statement 2 splits into a `contract` node… and a `relu` node" | splitNonlins determines graph shape | **STALE** | F1: the split now happens at the `route` boundary in `physicalizeOne` (`RouteFragments.lean`), not via an active `splitNonlins` phase. |
| **realize.md** (ACTIVE) | L172 & L194: "After compilation (`splitNonlins` + `schedule` + `route`)" / "one primitive after `splitNonlins`" | routed artifact produced via splitNonlins | **STALE** | F1 (same as above). |
| **SORRY_INVENTORY.md** (ACTIVE) | L244-246: "`TLProgram.compile`… is the **8-phase Kleisli chain** (assignUIDs → … → finalizeScans → **splitNonlins → schedule → route**)" | compile chain includes splitNonlins | **STALE** | F1: `Compile.lean:23`; splitNonlins off-chain (`Lowering.lean:10`). |
| **SORRY_INVENTORY.md** (ACTIVE) | L383-384: "detected in `finalizeScans` (**BEFORE `splitNonlins` lifts nonlinearities out**) via the `isAffine` flag" | isAffine set before the splitNonlins phase | **STALE** (narrow) | The `isAffine`-in-`finalizeScans` part is still true, but the "before `splitNonlins`" framing presents splitNonlins as a live downstream production phase; it is off-chain (F1). |
| **eval_ir.md** (ACTIVE) | L294-297: "Nonlinearities and `LHSSlot.freeNorm` **remain unsupported inside scan blocks**; a `RawPlanBlock` therefore still contains **`Array AssignPlan`**, not general `PlanStep`s" | nonlinear scans unsupported; block is assignment-only | **STALE** (two ways) | F4: `compileScan` admits/lowers nonlinear scans (`Compile.lean:70-71`); F3: `RawPlanBlock.steps : Array BlockStep` (`RawStep.lean:119-123`). |
| **eval_ir.md** (ACTIVE) | L299-302: capability preflight returns a typed error for "…**nonlinear scan-block statements**, normalized-axis slots inside scan blocks…" | preflight rejects nonlinear scan-block statements | **STALE** | F4: `unsupportedNonlin == 0` now (`DifferentialTest.lean:817`); `compileScan` lowers nonlinear base/recurrence. |
| **eval_ir.md** (ACTIVE) | L275-282: "The `splitNonlins` phase isolates a non-identity `RHSExpr.nonlin` into two scheduled statements… a generated `%nl...` tensor… currently yields **three plan steps**: `PlanStep.assign`, `PlanStep.assign`, and `PlanStep.pointwise`/`axiswise`" | three-step lowering via splitNonlins + %nl | **STALE** | F1/F4: no `splitNonlins` on chain, no `%nl` in the schedule (`Compile.lean:41-42`); lowering is two-step `assign → pointwise/axiswise` (`Eval/AGENTS.md:55`). |
| **eval_ir.md** (ACTIVE) | L381: "10. `splitNonlins` isolates nonlinear operations into separate statements." | splitNonlins is a numbered active pipeline step | **STALE** | F1: off-chain (`Lowering.lean:10`). |
| **eval_ir.md** (ACTIVE) | L496-497: "A generated `%nl...` statement created earlier by `splitNonlins` is itself a scheduled source-level statement and therefore does have a materialized entry." | schedule contains %nl statements from splitNonlins | **STALE** | F1: `compileToScheduled` emits no `%nl` (`Compile.lean:41-42`); %nl only in regression `Lowering.lean:44`. |
| **eval_ir.md** (ACTIVE) | L814-826 (§3.3.2): "The experiment still assumes assignment-only checked nodes. It has not been migrated to the current assignment, scan, pointwise, and axiswise… **therefore does not build**" | the *experimental JAX path* lags the generalized `PlanStep` | **UNCERTAIN** | This is a self-declared "does not build" status about `experiments/jax_bridge`, not a claim about the production compiler; would need building the experiment to confirm. Not a Task 1-4 production-code staleness claim. |
| **jax_evalplan_architecture.md** (ACTIVE) | L286-288: "Neither contract admits a checked step in the new pipeline yet: `LeanNCD/Eval/Plan/Compile.lean` **rejects every pointwise and axiswise nonlinear statement via `unsupportedNonlin`**" | Compile.lean rejects all pointwise/axiswise | **STALE** | F3/F4: `Compile.lean` admits them (`checkNonlinTopLevel`/residualization → `.assign → .pointwise/.axiswise`, `Eval/AGENTS.md:55`). |
| **jax_evalplan_architecture.md** (ACTIVE) | L1319-1322: "**`PlanStep` now exists** (Wave F F3): it is the closed **`.assign`/`.scan` sum**… — F4 then made scan steps reachable" | PlanStep is the `.assign`/`.scan` sum | **STALE** (enumeration incomplete) | F3/F4: `PlanStep` is `.assign`/`.scan`/`.pointwise`/`.axiswise` (`Eval/AGENTS.md:60`). |
| **leanncd.md** (ACTIVE) | L1703-1706: `def TLProgram.compile := … >=> finalizeScans >=> **splitNonlins** >=> schedule >=> route` | compile chain includes splitNonlins | **STALE** | F1: actual `Compile.lean` uses `compileToScheduled >>= route` with no `splitNonlins`. |
| **leanncd.md** (ACTIVE) | L1637-1639: "`structure LinearProgram where … stmts : List ScanStmt -- no nonlinearity in RHSExpr.nonlin`" | LinearProgram is a distinct structure with an enforced no-nonlinearity invariant | **STALE** | F1: `Types.lean:53` `abbrev LinearProgram := ScanProgram` — an alias, invariant no longer established. |
| **leanncd.md** (ACTIVE) | L1720: "→[**splitNonlins**] LinearProgram — nonlinearity isolated into its own step" | splitNonlins produces a distinct LinearProgram stage | **STALE** | F1 (as above). |
| **leanncd.md** (ACTIVE) | L1734: "**splitNonlins** \| Lifts `relu`/`softmax`/`normalize` out of `RHSExpr.nonlin` into a separate composed step…" | splitNonlins is an active pipeline phase | **STALE** | F1: off-chain (`Lowering.lean:10`). |
| **leanncd.md** (ACTIVE) | L1744: "the `isAffine` flag on `ScanStmt.scan` is set here (**before `splitNonlins`**)" | isAffine set before an active splitNonlins phase | **STALE** (narrow) | Same as SORRY_INVENTORY L384: the flag-in-finalizeScans part is fine; "before splitNonlins" frames it as live (off-chain, F1). |
| **leanncd.md** (ACTIVE) | rg for "nonlinear scans unsupported/reject", "unsupportedNonlin", "9/4/4", "RawPlanBlock.assignments"/"assignment-only", "three-step", "causalityFailure stmtIndex" | — | **STILL TRUE (clean)** | `rg` returned no such claims in `leanncd.md`; the scan sections do not assert old counts/fields. |
| **code_walkthrough.md** (ACTIVE) | L378: "`finalizeScans` later pairs these into a `ScanStmt.scan`… and **`splitNonlins` separates the linear contraction from the `relu` into two scheduled steps**" | splitNonlins actively splits into scheduled steps | **STALE** | F1: split now at `route` boundary; splitNonlins off-chain (`Lowering.lean:10`). |
| **code_walkthrough.md** (ACTIVE) | L455-456 & L468-469: the `do`/`>=>` compile chain with "`finalizeScans` … `splitNonlins >=> schedule`" | compile/compileToScheduled chains splitNonlins | **STALE** | F1: `compileToScheduled` has no `splitNonlins` (`Compile.lean`). |
| **code_walkthrough.md** (ACTIVE) | L640, L646, L651, L657, L668-671: "The actual split… happens in Stage 5"; "Stage 5 computes the routed artifact (`splitNonlins`, …)"; "`splitNonlins` … emits two statements: 1) linear pre-activation into fresh `%nl...` tensor" | Stage 5 splits via splitNonlins into `%nl` steps | **STALE** | F1: no active `splitNonlins`, no `%nl` in schedule (`Compile.lean:41-42`); split at `route` boundary. |
| **semantic_payload_audit.md** (ACTIVE) | L13-14: "`TLProgram ─ compileToScheduled ─→ ScheduledProgram`… `route →`" | compileToScheduled → ScheduledProgram, route separate | **STILL TRUE** | F1: matches `Compile.lean`. |
| **semantic_payload_audit.md** (ACTIVE) | L91-96 (finding C): "`splitNonlins` builds the linear pre-activation step as `{ body := rhs.body, nonlin := .identity }` … without `agg := rhs.agg`" (a latent agg drop "on BOTH paths") | a live agg-drop defect via splitNonlins on both compile paths | **UNCERTAIN → not a live defect** | `splitNonlins` is regression-only (F1), so "BOTH paths" is stale; and the drop is **vacuous** — only `agg = .max` differs from sum, and such stmts have `nonlin = .identity` by construction (`leanncd.md:1734`), so the split never carries a droppable non-sum `agg`. See "Real code defects". |
| **NaperianTyping.md** (ACTIVE) | L38: "- nonlinearity isolation (`splitNonlins`)," and L420 table: "\| `splitNonlins` \| isolate nonlinearities into separate stmts \| … \| **Current pass** \|" | splitNonlins is a current pipeline pass | **STALE** | F1: off-chain (`Lowering.lean:10`). No archival banner on this doc. |
| **NaperianTyping.md** (ACTIVE) | L797-799: pipeline list "finalizeScans / **splitNonlins** / schedule" | splitNonlins on the active chain | **STALE** | F1 (as above). |
| **NaperianTypingIntegrationPlan.md** (ACTIVE, broad historical plan) | L208-209 & L240-242: "finalizeScans / **splitNonlins** / schedule" | active `splitNonlins` invariant in the compile chain | **STALE** | F1: off-chain. §3.7 step 4 explicitly names this doc: replace only its active `splitNonlins` invariant with a dated pointer to the canonical boundary. |
| **copilot_code_analysis.md** (ACTIVE) | L468-471: "`LabeledProgram`, … `LinearProgram`, and `ScheduledProgram` are **distinct types**… `LinearProgram` still stores unrestricted `ScanStmt`" | LinearProgram is a distinct type | **STALE** | F1: `Types.lean:53` `abbrev LinearProgram := ScanProgram` (an alias, not distinct). |
| **copilot_code_analysis.md** (ACTIVE) | L2904: "2. pointwise activations lowered as isolated steps by **`splitNonlins`**" | splitNonlins lowers pointwise activations | **STALE** | F1: off-chain; lowering via `physicalizeForRoute`/`compileScan`. |
| **wave_f_scanplan_proposal.md** (ACTIVE design-draft) | L214 (non-goals table): "\| `.scanPre`, callbacks, **nonlinear scan bodies**, and predicate-dispatch scan bodies \| **Still rejected** even though `PlanStep.scan` exists \|" | nonlinear scan bodies are still rejected | **STALE** | F4: `compileScan` admits nonlinear scan bodies; `unsupportedNonlin == 0` (`DifferentialTest.lean:817`). (This was the proposal's post-F3/pre-F4 scope.) |
| **wave_f_scanplan_proposal.md** (ACTIVE design-draft) | L632 (§6.2 block sketch): "`RawPlanBlock` … **ordered assignments**" | block holds ordered assignments | **STALE** | F3: field is `steps : Array BlockStep` (`RawStep.lean:119-123`). |
| **wave_f_scanplan_proposal.md** (ACTIVE design-draft) | L984-985: "Compiler-generated nonlinearity scratch remains rejected in the initial fragment because **nonlinearities are not yet plan operations**. When a later plan-kernel wave admits them…" | nonlinearities are not yet plan operations | **STALE** | F3/F4: `BlockStep`/`PlanStep` now include `.pointwise`/`.axiswise` (`RawStep.lean:67-71`, `Eval/AGENTS.md:60`); Thread 4 Task 4 admitted nonlinear scan blocks (`Compile.lean:76-90`). |
| **wave_f_scanplan_proposal.md** (ACTIVE design-draft) | L188-190: "The source compiler should **initially** admit scans only when every base and step operation is… **identity nonlinearity**…" | (staged) initial admission excludes nonlinear scans | **UNCERTAIN** | Framed as the *initial* staged scope ("should initially"); F4 later widened it. Historically accurate as a milestone description; stale only if read as current capability. |
| **wave_f_scanplan_proposal.md** (ACTIVE design-draft) | L133 & L282: "In Wave F, `RawEvalPlan.steps` becomes `Array PlanStep`" | outer-graph `RawEvalPlan.steps : Array PlanStep` | **STILL TRUE** | F3: `RawEvalPlan.steps : Array PlanStep` (this is the OUTER graph, not `RawPlanBlock`). |
| **2026-06-12-lean-dsl-tensor-logic-design.md** (ACTIVE spec, no banner) | L441-442: "→[finalizeScans] ScanProgram … →[**splitNonlins**]  **LinearProgram** — no nonlinearity in RHSExpr.nonlin" | splitNonlins produces a distinct LinearProgram stage | **STALE** | F1: off-chain; `LinearProgram` is an alias (`Types.lean:53`). |
| **todo.md** (SUPERSEDED-WITH-BANNER) | L5-10 banner: "**Permanently archived — do not execute this section.** Superseded by `nonlinearity_split_pair_direct_lowering.md`" over the sole `## Fork…` section (L3), which spans all subsections through L154 | archival redirect | **STILL TRUE (banner correct)** | Banner points to the canonical plan; every `splitNonlins`/`%nl`/three-step passage in the file (L16, L23-29, L44-52, L80, L127, L145) is inside this archived section → historical, not flagged. |
| **nonlinearity-in-scans-design.md** (SUPERSEDED-WITH-BANNER) | L3-9 banner: "**Permanently archived — do not execute or revise…** superseded by `…direct_lowering.md`. The canonical design has one logical unsplit `ScheduledProgram`…" | archival redirect + correct canonical summary | **STILL TRUE (banner correct)** | Banner redirects correctly; Status L11-15 "follow only the replacement plan." Historical three-step/pair-recognition content not flagged. |
| **nonlinearity-in-scans.md** (SUPERSEDED-WITH-BANNER) | L2-9 banner: "**Permanently archived — do not execute any task below.**… superseded by `…direct_lowering.md`" | archival redirect | **STILL TRUE (banner correct)** | Banner redirects correctly; Status L11 "retained for provenance only." |
| **nonlinearity_split_pair_direct_lowering.md** (CANONICAL) | whole document | the decision record | **EXCLUDED** | §3.7 step 7 excludes the canonical record; its rejected/historical terminology (`splitNonlins`, shared split, lost oracle floats) is correct as history, not stale. |

### The one flagged non-table item (§3.7 called it out specifically)

**`wiring-loop-generalization.md`** (ACTIVE; completed historical record — KEEP) has an **active
next-slice pointer aimed at the superseded plan**:

- L70-74: "This slice exists specifically so a later slice (**nonlinearity-in-scans, already planned at
  `2026-08-21-nonlinearity-in-scans.md`**, currently blocked on this one landing first) can extend
  `checkPlanBlock`'s dispatch to a new 3-arm `BlockStep` sum…". Reinforced at L88 and L94 ("the next
  slice's job").
  - **Verdict: FLAG (STALE pointer).** Code fact: the pointed-to `2026-08-21-nonlinearity-in-scans.md`
    itself carries "Permanently archived — do not execute any task below… superseded by
    `papers/nonlinearity_split_pair_direct_lowering.md`". So this active pointer directs a reader to an
    archived plan; per §3.7 it should point to the canonical plan instead.
- **Keep (historical record):** L81-83 & L88 describe `RawPlanBlock.assignments` as "still the only node
  kind… this slice does not rename the field." That is accurate *history of this completed slice* (the
  rename to `steps`/`BlockStep` happened in the later Task 3), so it is **STILL TRUE as history** and
  must be preserved, not flagged — even though `RawPlanBlock.assignments` is no longer a live
  identifier (`RawStep.lean:119-123` now has `steps : Array BlockStep`).

---

## §3.7 steps 2–3 gap check (report what exists; implement nothing)

- **Step 1 (five differential cases) — SATISFIED.** `DifferentialTest.lean:563-574`
  `nonlinearScanFixtures` is a 6-fixture list covering all five §3.7-named cases:
  `group3/persistentNonlinRecur` (persistent nonlinear state), `group2/interleavedAxiswise`
  (interleaved axiswise recurrence), `group5/scratchToScratchToState` (scratch-to-state),
  `group4/nonlinearBase` (nonlinear base), `group6/coupledScan` (coupled states); plus
  `group1/leadingPointwiseScratch`. Run via `scanParityCheck` in a `run_cmd` gate (L579-583).
- **Step 2 ("compare exact source-visible keys and warning order") — PRESENT.** `scanParityCheck`
  (`DifferentialTest.lean:437-501`) does point 4b whole-environment equality `envEq` ("same key set,
  `denseEq` on every key", L488-491) and point 7 "warnings compared as lists: order AND payload"
  (L500+). Scratch-privacy is asserted on all three legs (points 6a-6c). So exact source-visible keys
  and warning **order** are compared, not projected/counted.
- **Step 3 (the two gates) — PRESENT.**
  - 3,832-case scan-free gate: `DifferentialTest.lean:177` `total == 3832 && accepted == 3832 && rejCounts.isEmpty`.
  - 17-case 13/0/4 split: `DifferentialTest.lean:817` `total == 17 && accepted == 13 && nonlin == 0 && agg == 4`.
- **Nothing material appears missing from the differential.** The one documentation artifact that
  contradicts step 3 is `DifferentialTest.lean`'s own header comment (L24-25, "9/4/4"), captured as a
  STALE row above — the executable assertion (L817) is correct.

---

## Coverage

- **All 24 §3.7 Files-list documents were assessed.** Each exists (verified) and is categorized above.
- **Adjudicated conflict (Rule: surface conflicts, don't average).** `wave_f_scanplan_proposal.md`'s
  L214 ("nonlinear scan bodies… Still rejected") and L984-985 ("nonlinearities are not yet plan
  operations") *read* as STILL TRUE if one trusts the document's own in-file completion records — but
  those records are themselves stale. Settled against code, not prose: `checkNonlinScanBlock`
  (`Compile.lean:76-90`) states `.pointwise`/`.axiswise` are "**now structurally admitted** (Thread 4
  Task 4)"; commit `a75d8c1` "admit and lower nonlinear scan sources in `compileScan`"; and the
  `nonlinearBase`/`leadingPointwiseScratch` fixtures (`ScanCompileTest.lean:1074,1120`) compile and run.
  Verdict: **STALE**. This is precisely the "trust the tree, not the passage's framing" hazard §3.7
  warns about.
- **Method limitation to be transparent about.** For the large prose papers (`leanncd.md`,
  `code_walkthrough.md`, `eval_ir.md`, `jax_evalplan_architecture.md`, `NaperianTyping.md`,
  `NaperianTypingIntegrationPlan.md`, `wave_f_scanplan_proposal.md`, `copilot_code_analysis.md`,
  `restructure_suggestions.md`, `semantic_payload_audit.md`, `todo.md`), candidate passages were
  located with a marker `rg` (`splitNonlins|LinearProgram|RawPlanBlock|\.assignments|assignment-only|
  BlockStep|blockStepIndex|stmtIndex|%nl|unsupportedNonlin|9/4/4|three-step|nonlinear scan|…`) and each
  hit read in context. A stale claim phrased entirely without any of these markers could be missed;
  the marker set is the brief's own stale-marker table plus the F3/F4 identifiers, so residual risk is
  low but non-zero.
- **`restructure_suggestions.md`** was assessed for nonlinearity claims only; its nonlinearity content
  is a wave-progress ledger and hazard notes. L1560-1562 ("`Compile.lean`'s pipeline: 9 phases → 8")
  concerns a `ctx`/`CanonicalProgram` refactor, **not** the nonlinearity work, so it is out of scope
  for this audit (not classified STALE here). L1307-1309 references `splitStmt` behavior ("because
  `splitStmt` reuses slots verbatim") — now regression-only; **UNCERTAIN** as a hazard note, not a
  production-pipeline claim.

## Gaps in the §3.7 Files list (active docs with stale nonlinearity claims NOT in the list)

The list predates Tasks 3–4. A repo-wide `rg 'splitNonlins|LinearProgram' --glob '*.md'` surfaces
additional documents outside the 24. Genuinely-active reference docs among them:

- **`leanncd/AGENTS.md`** (the subsystem root/navigation doc) — L145 references "`splitNonlins`
  dropped `rhs.agg`" as one of five historical audit violations. This is a **historical bug-list
  reference**, not a stale claim that `splitNonlins` is on the production chain, so it is **not**
  clearly stale; but a Task 5 sweep should re-check whether listing the `splitNonlins` agg-drop as a
  "live violation of [fail-loud]" is still apt now that the pass is off-chain (see defects section).
  Flagging it here because the doc is active and the list omits it.
- The remaining out-of-list hits are **implementation plans / dated specs** (e.g.
  `docs/superpowers/plans/2026-08-26-nonlinearity-t1-logical-schedule.md`,
  `…-t2-route-corpus.md`, `2026-08-20-thread-4-nonlinearity.md`,
  `docs/superpowers/specs/2026-07-15-…`, `…2026-07-30-payload-carry-design-decisions.md`) and
  `papers/archive/*` / `papers/implementation_seeds/*`. These are historical planning/seed artifacts
  (the same category §3.7 treats plans as); their `splitNonlins` references describe the state at
  authoring time. They are **candidate additions** to a Task 5 sweep only if the project wants dated
  pointers added, but they are not "active reference docs asserting current architecture."

## Real code defects (reported loudly and separately, per §3.7)

**None found.** The only candidate is `semantic_payload_audit.md` finding C — that
`splitNonlins` builds its linear step `{ body := rhs.body, nonlin := .identity }` without carrying
`agg := rhs.agg` (`Lowering.lean`). This is **not a live defect**:

1. `splitNonlins` is **off the production chain** (regression-only, `Lowering.lean:10-12`), so it runs
   only in `test/DSL/Pipeline/RouteWeaveTest.lean`'s old-leg comparator.
2. The drop is **vacuous even there**: a statement's `agg` only differs from `sum` when it is `.max`
   (`maxreduce`), and such statements have `nonlin = .identity` **by construction**
   (`leanncd.md:1734`), so `splitNonlins`/`physicalizeOne` is a no-op for them — the split path never
   carries a droppable non-sum `agg`.

I did **not** find evidence that the replacement `physicalizeOne` (`RouteFragments.lean`) drops any
payload it should keep, but a full proof of that is code-verification beyond a documentation audit; I
flag it only as a "worth a glance during Task 5" item, not as a defect.

---

## Verification record

(See the reply for `git log --oneline -3` and `git status --porcelain`. This RESULTS file is the only
new/changed file; no document in the tree was modified.)

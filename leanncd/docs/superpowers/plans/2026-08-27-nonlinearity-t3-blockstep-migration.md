# Slice T3 — generalize `RawPlanBlock` to `BlockStep` (assign/pointwise/axiswise)

**Scope:** Task 3 only of
[`papers/nonlinearity_split_pair_direct_lowering.md`](../../../../papers/nonlinearity_split_pair_direct_lowering.md)
(that document's §3.5, "generalize Plan blocks"). That document remains the canonical design
record; this is the executable plan for its third slice.

**Deliberately NOT in this slice** (each is a later slice, planned only once this one lands, per
CLAUDE.md Rule 13):

| Master-plan task | Deliverable | Owned by |
|---|---|---|
| Task 4 | nonlinear Plan **scan** admission (compiler emits `.pointwise`/`.axiswise` scan sources), independent oracle, allocation/publication | a later slice — this slice's own `Compile.lean` change wraps compiler output as `.assign` only |
| Task 5 | differential documentation + stale-document sweep + closure | a later slice |
| (pre-existing) | `experiments/jax_bridge/EvalPlanCodegen.lean` build breakage | pre-existing gap, out of scope here |

This slice changes production `RawPlanBlock`/`checkPlanBlock`/`runDenseBlock`/scan causality and
their existing tests. It does **not** touch `DSL/*`, `RouteFragments.lean`, or any Task 1/Task 2
file — Tasks 1 and 2 are both already merged and their gates are re-verified untouched (§0).

---

## §0 Verified baseline

Executed in this worktree against `main` at `fe436f7` on 2026-08-27 (2 doc-only commits ahead of
the `d8ef77b` the donor seed itself was audited against — `git log fe436f7 -3 --oneline` shows both
are `papers/nonlinearity_split_pair_direct_lowering.md` edits, no Lean touched). Re-run this section
before editing; a failure here is base drift, not a transplant defect.

### 0.1 The donor seed still typechecks, byte-for-byte

```bash
cd leanncd
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/blockstep_migration/BlockStepMigrationSeed.lean
```

Observed:

```
fixture 1 pointwise result #[1.000000, 0.000000, 3.000000]
fixture 2 axiswise result #[0.166667, 0.333333, 0.500000]
```

Identical to the seed's own README table (row 1/2). All `#guard`s (fixtures 3-9, the compiler-
wrapping guard) passed silently. **The seed is live against the current tree, not a stale
snapshot.**

### 0.2 The three production gates reproduce their recorded job counts exactly

```bash
cd leanncd
"$HOME/.elan/bin/lake" build Eval.Plan.BlockTest Eval.Plan.NonlinCheckTest Eval.Plan.ScanTest Eval.Plan.ScanCompileTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

| Command | Result | Jobs (this worktree) | Jobs (seed README, `d8ef77b`) |
|---|---|---:|---:|
| Four targeted modules | pass | 8,511 | 8,511 |
| `Tests` | pass | 8,657 | 8,657 |
| `LeanNCD` | pass, one pre-existing unrelated `Agreement.lean` linter warning | 8,543 | 8,543 |

Exact match on all three counts. **No drift since the seed's own 2026-08-27 audit; Tasks 1 and 2
introduced no new Task 3 migration site**, confirming the seed README's own claim rather than
trusting it.

### 0.3 The 47-occurrence / 46-line migration inventory, re-counted independently

```bash
cd leanncd
for f in LeanNCD/Eval/Plan/RawStep.lean LeanNCD/Eval/Plan/Block.lean LeanNCD/Eval/Plan/Scan.lean \
         LeanNCD/Eval/Plan/Compile.lean test/Eval/Plan/BlockTest.lean test/Eval/Plan/ScanTest.lean \
         test/Eval/Plan/ScanCompileTest.lean test/Eval/Plan/NonlinCheckTest.lean; do
  echo "$f: $(grep -c "assignments" "$f")"
done
```

Observed: `RawStep.lean: 1`, `Block.lean: 3`, `Scan.lean: 2`, `Compile.lean: 6`,
`BlockTest.lean: 4`, `ScanTest.lean: 28`, `ScanCompileTest.lean: 10`, **`NonlinCheckTest.lean: 0`**
— total 54 raw matches, matching the seed README's "naive result is 54" exactly (46 genuine code
lines + 8 comment/docstring matches — `Block.lean`'s 3rd match and `Compile.lean`'s 4 extra matches
are all comment prose, confirmed by reading each file directly, §0.4). `NonlinCheckTest.lean`
genuinely has zero occurrences — it is fixture-donor/verification-only for this slice, not a
migration site, confirming its Files-list annotation in the master plan.

### 0.4 Every migration site's exact shape, read directly (not inferred from the count)

- **`RawStep.lean`**: exactly one field declaration, `assignments : Array AssignPlan`, inside
  `RawPlanBlock`. No other reference in this file.
- **`Block.lean`**: exactly two genuine occurrences, both inside `checkPlanBlock`'s wiring loop —
  `for h : ni in [0 : block.assignments.size]` and `let step := block.assignments[ni]`. The third
  match is prose in the module docstring. `checkPlanBlock` currently builds
  `Array (WiringNode BlockError CheckedAssignPlan)` and calls
  `checkStepGraph n block.inputs BlockError.wiring nodes` — **verified identical in shape** to the
  seed's own call, so "keep `checkStepGraph` unchanged" is a confirmed fact, not an assumption.
  `runDenseBlock` iterates `c.checkedNodes` and dispatches every node through `runDenseAssignAt`
  unconditionally — the exhaustive multi-way dispatch does not exist yet.
- **`Scan.lean`**: exactly two genuine occurrences, both inside `checkScanPlan`'s causality loop —
  `for h : ai in [0 : raw.stepBlock.assignments.size]` and `let a := raw.stepBlock.assignments[ai]`
  — followed by the existing `stateReadCausal` walk over `a.terms`/factors, unconditionally (every
  block-step element is assumed to be an assignment today, correctly, since none other exists).
- **`Compile.lean`**: exactly two genuine occurrences (the other four grep hits are the phase-3/
  phase-4 comments "base/recurrence assignments", "captures, assignments, and one
  `StateWriteMap`...", "captures, assignments in source order...", "Plain, base, and recurrence
  assignments..." — prose, not code). The two real sites are the `RawScanPlan` assembly literal's
  `baseBlock := { ..., assignments := baseAssigns, ... }` and
  `stepBlock := { ..., assignments := stepAssigns, ... }`, where `baseAssigns`/`stepAssigns` are
  already-built `Array AssignPlan` locals from phases 3/4.
- **`BlockTest.lean`**: exactly four genuine occurrences, all `RawPlanBlock` **construction** sites
  (`stepBlock`, `wrongContextBlock`, `forwardReadBlock`, `missingProductionBlock`) — no read-side
  assertion on `.assignments` anywhere in this file.
- **`ScanTest.lean`**: exactly 26 genuine lines / 28 occurrences (one line has two), **all
  construction sites** (`assignments := #[...]` or `assignments := #[]` inside a `RawPlanBlock`
  literal, or a `{ x with assignments := ... }` update) — confirmed by listing every match: no line
  reads `.assignments` for an assertion.
- **`ScanCompileTest.lean`**: exactly 10 genuine lines — **2 construction sites**
  (`selfRecurExpected`'s `baseBlock`/`stepBlock` literals) and **8 read-side assertions**
  extracting `.destinationSlot`/`.terms` from `s.stepBlock.assignments`/`s.baseBlock.assignments`
  via `.map`, `.getD n default`, where `s : RawScanPlan` comes from `scanAt p 0`.

This confirms the seed README's per-file table exactly and, further than the README goes, confirms
that **every read-side assertion needing a `.assign` unwrap lives in exactly one file**
(`ScanCompileTest.lean`) — `BlockTest.lean` and `ScanTest.lean` are pure construction, so their
migration is a mechanical `.assign`-wrap with no unwrap logic at all.

### 0.5 A new accessor this plan adds, verified to compile

The donor seed supplies `BlockStep.sourceSlots`/`.destinationSlots`/`.contextShape?` but not an
`.assign?` projection — `ScanCompileTest.lean`'s 8 read-side assertions need one to stay a
one-line `.map`/`.getD` rather than a `match` at every call site. Compiled via
`check-snippet.sh` in this exact form:

```lean
def BlockStep.assign? : BlockStep → Option AssignPlan
  | .assign a => some a
  | .pointwise _ | .axiswise _ => none
```

against a local re-declaration of `BlockStep`, together with the exact rewrite shapes
`ScanCompileTest.lean` needs:

```lean
-- was: s.stepBlock.assignments.map (·.destinationSlot)
s.stepBlock.steps.filterMap BlockStep.assign? |>.map (·.destinationSlot)

-- was: (s.stepBlock.assignments.getD 1 default).terms...
((s.stepBlock.steps.getD 1 default).assign?.getD default).terms...
```

Both compiled (`#guard`s in the snippet passed). Every compiler-produced block in this slice
contains only `.assign` steps (Task 4's job is admitting the alternative), so `filterMap`/`getD`
never silently drops or defaults a real element here — confirmed by §0.4: `Compile.lean` only ever
constructs `.assign`-wrapped steps.

### 0.6 Snippet verification

Every Lean fragment in this document (§0.5's `assign?` and the two rewrite shapes) was compiled in
its final printed form with `bash .claude/skills/slice-plan/check-snippet.sh`. All other code this
plan asks the implementer to transplant is copy-paste from the donor seed file, verbatim, by
declaration name — not retyped from this document's own rendering — so it carries the seed's own
2026-08-27 verification (§0.1) forward unedited; do not reformat while copying, or re-verify with
`check-snippet.sh` if you do.

---

## §1 Global constraints

Exact values, and what is deliberately excluded.

- **Exactly 47 field occurrences on 46 code lines across the seven files in §0.3/§0.4.** Genuine
  code lines only — the 8 comment/docstring matches (`Block.lean` ×1, `Compile.lean` ×4, and any
  incidental match discovered while editing) are prose and are not part of the migration count; if a
  comment mentions "assignments" descriptively, updating its wording is fine but is not one of the
  47.
- **`checkStepGraph` does not change.** Confirmed identical in the seed and in production
  (§0.4) — it is a generic wiring loop parameterized by `WiringNode`; only the `nodes` array's
  construction (per-step `contextCheck`/`sourceCheck`/`localCheck`) changes.
- **No nonlinear scan *source* is admitted in this slice.** `Compile.lean`'s `baseAssigns`/
  `stepAssigns` map through `.assign` only — the compiler never emits `.pointwise`/`.axiswise`.
  Every new capability this slice adds (checking, execution, causality skip) is exercised only by
  hand-built `RawPlanBlock`/`RawScanPlan` test fixtures, never by a real compiled program. That is
  Task 4's job.
- **`CheckedPlanBlock` and `CheckedScanPlan` intentionally have no `BEq`** (their constructors are
  `private mk ::` and their fields include function-shaped/checked evidence) — every fixture
  assertion pattern-matches the `Except` result directly; never write
  `checkPlanBlock x == checkPlanBlock y`.
- **Nonlinear provenance is enforced once, in `checkPlanBlock`'s `sourceCheck`, not duplicated in
  `checkScanPlan`.** `checkScanPlan` continues to cause-check only `.assign` payloads after both
  blocks are already checked — a nonlinear node can never reach the scan-causality loop as a
  causality subject, only as a captured-state *consumer* rejected earlier by
  `nonlinearSourceNotLocalAssignment`.
- **No production file outside the four listed in Task 1 changes**
  (`RawStep.lean`, `Block.lean`, `Scan.lean`, `Compile.lean`). No `lakefile.toml` edit — no new file
  is added, only existing modules change. Task 2's own production footprint is exactly one
  declaration line in `Scan.lean` (the `causalityFailure` field rename) plus `Eval/AGENTS.md`.
- **`Error.lean` is not in this slice at any point.** Its `ScanCompileError` constructors carry a
  `stmtIndex` field that means something different and is still correct; Task 2's rename must not
  reach it.
- **No `sorry`, `admit`, or `axiom`.**
- **Every mutation cycle is a production mutation** (toggle production logic, observe failure,
  restore, observe pass) — never predict a failure or mutate the assertion.

**Discoverability.** Nothing here changes what a plain top-level import reaches — `Block.lean`,
`Scan.lean`, `Compile.lean`, `RawStep.lean` are all already reachable from `import LeanNCD`. This
slice generalizes existing declarations in place; it adds no new module.

---

## §2 Task breakdown

Two tasks. Boundaries chosen by the reviewer test (*a reviewer could meaningfully reject one while
approving its neighbour*) **and** by what Lean's type system forces to land together.

| Task | Deliverable | Fixtures / assertions touched | Mutation cycles | Risk driver |
|---|---:|---:|---:|---|
| 1 | `BlockStep` type, full checker/dispatch/causality generalization, 47-occurrence migration, all EXISTING fixtures behavior-unchanged | 0 new; ~42 existing lines mechanically migrated across 6 files | 0 (nothing new to break yet) | wide blast radius, but every step is either type-forced or a byte-for-byte copy from an already-verified donor |
| 2 | 10 new fixtures proving pointwise/axiswise checking+execution, nonlinear-source provenance, and assign-only scan causality actually work; plus the `causalityFailure` field rename and the two stale `Eval/AGENTS.md` rows | 10 new (5 in `BlockTest.lean`, 5 in `ScanTest.lean`) | 7 (all mandatory) | the entire soundness claim of this slice — a provenance or causality gap here is the failure mode Task 3 exists to prevent |

**Why this is not three or four tasks, unlike Task 1's and Task 2's own slice plans.** The instant
`RawPlanBlock.assignments : Array AssignPlan` becomes `RawPlanBlock.steps : Array BlockStep`, every
one of `checkPlanBlock`'s and `runDenseBlock`'s `match`es on step **must** become exhaustive over
all three `BlockStep` constructors or the file does not compile — Lean's exhaustiveness checking
forces the checker generalization, the dispatch generalization, and the field rename to land in one
commit; there is no buildable intermediate state with the field renamed but the checker still
assignment-only. The same is true of `Scan.lean`'s causality loop and `Compile.lean`'s assembly
literal. So Task 1 is not "the mechanical part" and Task 2 "the semantic part" — Task 1 is instead
*everything the type system requires to keep `Tests`/`LeanNCD` green with unchanged behavior*, and
Task 2 is *everything that requires a fixture to observe, for the first time, that the new capability
is real and soundly guarded*. A reviewer can accept Task 1 (migration is exact, nothing changed for
existing callers, new dead-until-tested capability compiles) while rejecting Task 2 (the provenance
guard has a gap, or a causality fixture doesn't actually exercise causality) — that is the genuine
independent failure mode, not file boundaries.

**Why fixtures 1-4 and 7 go in `BlockTest.lean` and fixtures 5-6, 8-9 in `ScanTest.lean`.** This
mirrors the donor seed's own section structure exactly (`## Block fixtures 1-4 and 7` /
`## Scan donors and fixtures 5-6, 8-9`, seed lines verified in §0). Fixtures 5, 6, 8, 9 need
`checkScanPlan`, not just `checkPlanBlock`, and their donors (`stepBlockLookAheadG`,
`deepHistoryScan`) already live in `ScanTest.lean` — cloning them across files would duplicate scan
scaffolding (states, captures, writes) that `ScanTest.lean` already builds.

---

### Task 1 — `BlockStep` type, generalized checker/dispatch/causality, full migration

**Outcome.** `RawPlanBlock.steps : Array BlockStep` replaces `assignments : Array AssignPlan`
everywhere. `checkPlanBlock` checks all three step kinds (enforcing nonlinear-source provenance);
`runDenseBlock` dispatches all three to their existing Dense workers; `checkScanPlan`'s causality
walk considers only `.assign` payloads, preserving the block-step index in `causalityFailure`;
`Compile.lean` wraps every compiler-produced assignment as `.assign`. Every existing fixture in
`BlockTest.lean`, `ScanTest.lean`, and `ScanCompileTest.lean` passes with **byte-identical observed
values** to before this task — this task changes representation, not behavior.

**Files**

- `leanncd/LeanNCD/Eval/Plan/RawStep.lean`
- `leanncd/LeanNCD/Eval/Plan/Block.lean`
- `leanncd/LeanNCD/Eval/Plan/Scan.lean`
- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/test/Eval/Plan/BlockTest.lean`
- `leanncd/test/Eval/Plan/ScanTest.lean`
- `leanncd/test/Eval/Plan/ScanCompileTest.lean`

**Implementation**

1. In `RawStep.lean`, immediately before `RawPlanBlock`, add the donor's `BlockStep` inductive and
   its three accessors verbatim (copy-paste from
   `papers/implementation_seeds/nonlinearity_route_fragments/blockstep_migration/BlockStepMigrationSeed.lean`,
   the declarations `BlockStep`, `BlockStep.sourceSlots`, `BlockStep.destinationSlots`,
   `BlockStep.contextShape?`), then add this plan's own `BlockStep.assign?` from §0.5. Rename
   `RawPlanBlock.assignments : Array AssignPlan` to `steps : Array BlockStep`.
2. In `Block.lean`, transplant the donor's `CheckedBlockStepEvidence` inductive and the two new
   `BlockError` constructors (`nonlin (nodeIndex : Nat) (cause : NonlinPlanError)` and
   `nonlinearSourceNotLocalAssignment (nodeIndex : Nat) (sourceSlot : TensorSlot)`) verbatim,
   alongside the three existing constructors (`wiring`, `duplicateOutputSlot`,
   `blockContextMismatch` — unchanged). Change `CheckedPlanBlock.checkedNodes` from
   `Array CheckedAssignPlan` to `Array CheckedBlockStepEvidence`.
3. Replace `checkPlanBlock`'s wiring-node construction loop with the donor's version verbatim (the
   seed's `checkPlanBlock`, from `let mut nodes : Array (WiringNode BlockError
   CheckedBlockStepEvidence) := #[]` through the call to `checkStepGraph`) — this is the loop that
   tracks `precedingAssignmentDestinations`, builds each node's `contextCheck`/`sourceCheck`/
   `localCheck` by matching on the step kind, and enforces `nonlinearSourceNotLocalAssignment` inside
   `.pointwise`/`.axiswise`'s `sourceCheck` (after the existing range/availability check, before
   `localCheck` runs `checkPointwise`/`checkAxiswise`). Do **not** transplant the seed's six
   `enable*Mutation` toggles — those exist only to drive Task 2's mutation cycles and belong in the
   mutate-in-place production edits of §2's Task 2, never as permanent flags.
4. Replace `runDenseBlock`'s single `runDenseAssignAt`-only loop with the donor's exhaustive
   dispatch (`match node with | .assign a => ... | .pointwise p => ... | .axiswise a => ...`, using
   the existing `runDenseAssignAt`/`runDensePointwise`/`runDenseAxiswise` workers — no new Dense
   logic is written here, only wiring to what `Nonlin.lean` already provides).
5. In `Compile.lean`, change the two assembly-literal sites (§0.4) to
   `steps := baseAssigns.map .assign` and `steps := stepAssigns.map .assign`.
6. In `Scan.lean`, change `checkScanPlan`'s causality loop to iterate `raw.stepBlock.steps`
   (unfiltered — do not `.filterMap` before indexing) and pattern-match: `.assign a =>` the existing
   per-term/per-factor `stateReadCausal` body, unchanged; `.pointwise _ | .axiswise _ => pure ()`.
   Keep the loop variable name feeding `causalityFailure`'s `blockStepIndex` as the **raw** index
   into `steps` (not a filtered position), so a causality failure's locator still identifies the
   actual block-step position — this is what makes a later Task 4 causality failure locatable
   against the same block a human reads.
7. Migrate the 46 genuine lines per §0.4's per-file breakdown:
   - `BlockTest.lean` (4 lines): wrap each `assignments := #[...]` literal's elements in `.assign`,
     rename the field to `steps`.
   - `ScanTest.lean` (26 lines): same mechanical wrap — every occurrence in this file is a
     construction site (§0.4); there is no assertion to adapt.
   - `ScanCompileTest.lean` (10 lines): wrap the 2 construction sites
     (`selfRecurExpected`'s `baseBlock`/`stepBlock` literals) the same way; rewrite the 8 read-side
     assertions using the `BlockStep.assign?`-based shapes verified in §0.5 (`.steps.filterMap
     BlockStep.assign? |>.map (·.destinationSlot)` for the map-based assertion,
     `(s.stepBlock.steps.getD n default).assign?.getD default` for the indexed ones).

**Gate**

```bash
cd leanncd
"$HOME/.elan/bin/lake" build Eval.Plan.BlockTest Eval.Plan.NonlinCheckTest Eval.Plan.ScanTest Eval.Plan.ScanCompileTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

All three must be green with **no observed-value change** in any existing fixture (every
`run_cmd`/`#guard` in `BlockTest.lean`/`ScanTest.lean`/`ScanCompileTest.lean` that passed before
this task still passes; `Tests`/`LeanNCD` job counts should match §0.2's 8,657/8,543 exactly, since
this task adds no new module and no new test). A job-count change here is a signal something
outside the four listed files moved — investigate before proceeding to Task 2.

**Review.** One reviewer, focused entirely on: is the migration exact (every one of the 46 lines
accounted for, nothing missed, nothing extra); does `checkPlanBlock`'s new dispatch structurally
match the donor's already-verified version (diff against the seed file, not against the reviewer's
own re-derivation); is `checkStepGraph` genuinely untouched; does the causality loop's index still
identify a real block-step position. This reviewer does **not** need to evaluate whether the
provenance guard or causality restriction is *sound* — no fixture exercises the new capability yet,
so soundness has no evidence to review until Task 2.

---

### Task 2 — fixtures proving the new capability, and the seven mandatory mutation cycles

**Outcome.** Ten fixtures demonstrate, for the first time, that pointwise/axiswise checking and
execution work, that a nonlinear node's source must be a preceding local assignment (rejecting
direct-capture, laundering, and nonlinearity-chained sources), and that scan causality still applies
correctly to `.assign` payloads once nonlinear nodes are mixed into the same block. Seven mutation
cycles prove each of these guards has teeth. Two housekeeping items fold in here (see "Folded-in
items" below): the `causalityFailure` field rename its new fixture finally justifies, and the two
`Eval/AGENTS.md` rows Task 1's generalization made stale.

**Files**

- `leanncd/test/Eval/Plan/BlockTest.lean` (fixtures 1-4, 7)
- `leanncd/test/Eval/Plan/ScanTest.lean` (fixtures 5, 6, 8, 9, 10)
- `leanncd/LeanNCD/Eval/Plan/Scan.lean` (the `causalityFailure` field rename only)
- `leanncd/LeanNCD/Eval/AGENTS.md` (two stale rows)

**Folded-in items**

*(1) Rename `ScanPlanError.causalityFailure`'s second field from `stmtIndex` to `blockStepIndex`.*
Since Task 1 it indexes `stepBlock.steps`, not a statement list, and Task 1 left a docstring
apologising for the name instead of fixing it. Fixture 10 below is what makes the new name an
honest claim rather than a relabel.

> **Trap — do not `sed` this.** `stmtIndex` appears on **14 other constructors**, all in
> `LeanNCD/Eval/Plan/Error.lean`'s `ScanCompileError`, a different error family where the field
> genuinely still means "the offending statement's index within its own `base`/`recur` list."
> **Those must not change.** Exactly one declaration is in scope: the `causalityFailure` line in
> `Scan.lean`'s `ScanPlanError`. Verified 2026-08-27: the only other references to the old name are
> three comment lines in `ScanTest.lean` (above `stepBlockTwoAssignConstG`) and one clause in
> `Scan.lean`'s own `checkScanPlan` docstring; update those, and drop the docstring's now-obsolete
> "named `stmtIndex` for historical reasons" aside. Every fixture matches the constructor
> positionally (`.causalityFailure 0 1 0 0`), so no assertion needs rewriting.

*(2) Update the two stale rows in `leanncd/LeanNCD/Eval/AGENTS.md`.* Verified stale 2026-08-27:
the `Block.lean` row still says it "reuses `checkAssign`/`runDenseAssignAt` per node" (now also
`checkPointwise`/`checkAxiswise` and `runDensePointwise`/`runDenseAxiswise`, plus the new
`CheckedBlockStepEvidence` and the nonlinear-source provenance obligation), and the `RawStep.lean`
row's vocabulary list omits `BlockStep` entirely while still implying `RawPlanBlock` holds
assignments. The `Nonlin.lean` row's "no second local-operation representation" claim was
re-checked and remains true — do not edit it.

**Fixtures — each names its donor, `clone <existing fixture>, change <one thing>`**

| # | File | Donor + change | Expected outcome (observed in the seed, §0.1) |
|---:|---|---|---|
| 1 | `BlockTest.lean` | clone `stepBlock`, append a `.pointwise` node reading the assignment's destination, `fn := .relu` | accepted; at `ctx=[0]` with input `#[1,-2,3,4,-5,6]` (shape `[2,3]`), result `#[1, 0, 3]` |
| 2 | `BlockTest.lean` | clone fixture 1's block again, append a `.axiswise` node instead, `fn := .normalize` | accepted; with input `#[1,2,3,4,5,6]`, result is strictly increasing and sums-normalized (seed observed `#[0.166667, 0.333333, 0.500000]`) |
| 3 | `BlockTest.lean` | clone `forwardReadBlock`, replace its first operation with a `.pointwise` node reading the not-yet-produced slot | rejected: `.wiring (.invalidForwardRead 0 0 0 1)` |
| 4 | `BlockTest.lean` | restore source production (an `.assign` producing that slot), then add a second `.assign` colliding on the pointwise node's destination | rejected: `.wiring (.duplicateDestination 2 1 2)` |
| 5 | `ScanTest.lean` | clone `stepBlockLookAheadG`, replace its assignment with a `.pointwise` node sourcing the captured state slot (input slot 0) directly | rejected by `checkPlanBlock`: `.nonlinearSourceNotLocalAssignment 0 0` — the capture is not a preceding `.assign` destination |
| 6 | `ScanTest.lean` | clone `stepBlockLookAheadG`, insert a `.pointwise` node from the captured slot to a fresh slot, then make the original look-ahead assignment read that fresh slot instead of the capture directly | rejected by `checkPlanBlock`: `.nonlinearSourceNotLocalAssignment 0 0` — laundering the capture through an intermediate slot does not change *which* node is nonlinear; the rejection fires on the pointwise node itself, before scan causality is ever reached |
| 7 | `BlockTest.lean` | clone fixture 1's block, append a second nonlinear node (`.axiswise`, `fn := .normalize`) sourcing the first nonlinear node's own result | rejected: `.nonlinearSourceNotLocalAssignment 2 2` — nonlinearity chained directly onto nonlinearity, not onto a local assignment |
| 8 | `ScanTest.lean` | clone `deepHistoryScan` (causal read, `bias = -2`), append a scalar `.pointwise` (`fn := .relu`) reading the causal assignment's destination | accepted by both `checkPlanBlock` provenance and `checkScanPlan` causality |
| 9 | `ScanTest.lean` | clone `stepBlockLookAheadG`'s scan, append a scalar `.pointwise` after the look-ahead assignment | accepted by `checkPlanBlock` provenance (the pointwise node's source IS a preceding local assignment); rejected by `checkScanPlan`: `.causalityFailure 0 0 0 0` — the underlying look-ahead assignment itself is still non-causal, unchanged from before this slice |
| 10 | `ScanTest.lean` | clone `stepBlockG`, then build a **three-step** block where the indices diverge: `.assign stepAssignG` (valid, causal) at step 0, `.pointwise` sourcing its destination at step 1, and a third step `.assign { stepAssignG with destinationSlot := 3, terms := #[termConstG] }` carrying `constReadG`'s non-causal constant read at step 2. `tensorSigs` is `stepBlockG.tensorSigs ++ #[scalar, scalar]` (slots 2 and 3 are block-local scratch, never declared outputs — the same construct `stepBlockTwoAssignConstG` already uses) | `checkPlanBlock` accepts (provenance holds); `checkScanPlan` rejects with **`.causalityFailure 0 2 0 0`** — index **2**, the block-step position. **Observed 2026-08-27** by running this exact construction against production, not predicted |

**Why fixture 10 exists, and why the plan lacked it until now.** Task 1's spec required
`causalityFailure` to "retain original block-step indices," and nothing could have caught a
violation. The existing `stepBlockTwoAssignConstG` fixture was built precisely to discriminate that
field — but its block holds **two `.assign` steps**, so the block-step index and the
filtered-assignment index coincide at 1 and it cannot distinguish them. Donor fixtures 8 and 9 both
fail at index 0, where they coincide too. Fixture 10 is the first block where a nonlinear step sits
*between* two assignments, forcing the two indexings apart: correct is 2, filtered is 1. Without it,
the rename above would be a relabel with no test behind it, and mutation cycle 7 would have nothing
to fail. This is the "guard that cannot fail" shape the `slice-plan` skill warns about, found in
this plan's own Task 1 spec.

Every value above is transcribed from §0.1's already-observed seed run (fixture 10's from the
direct production run recorded in its own row), not predicted — the
implementer is copying a measured result into the production fixture location, adapting only the
surrounding `RawPlanBlock`/`RawScanPlan` scaffolding to the target file's existing donor names
(e.g. fixture 1 clones `BlockTest.stepBlock`, not the seed's own `blockAssign`/`pointwiseBlock`
locals, which exist only because the seed could not import `BlockTest.lean`).

**Mutation cycles (7, all mandatory)** — toggle the named production logic, observe the named
fixture(s) fail with the stated symptom, restore, observe pass again. Record the *observed* failure
in the completion record, not the prediction.

| # | Mutation (in production `Block.lean` unless noted) | Expected failing fixture(s) | Expected symptom |
|---:|---|---|---|
| 1 | In `runDenseBlock`, skip the `.pointwise` dispatch arm (leave the destination slot at its placeholder) | 1 | wrong/empty result at the pointwise destination |
| 2 | In `runDenseBlock`, skip the `.axiswise` dispatch arm | 2 | wrong/empty result at the axiswise destination |
| 3 | In `checkPlanBlock`'s `localCheck`, route `.pointwise`/`.axiswise` through `checkAssign` (on a placeholder `AssignPlan`) instead of `checkPointwise`/`checkAxiswise` | 1, 2 | both rejected with a `.wiring (.nodeError _ (.destinationShapeMismatch …))`-shaped error instead of accepting |
| 4 | In `checkPlanBlock`'s `sourceCheck`, remove the `precedingAssignments.contains …` guard for both `.pointwise` and `.axiswise` | 5, 6, 7 | all three wrongly **accepted** (direct capture, laundering, and nonlinearity-chaining all become admissible) |
| 5 | In `Scan.lean`'s causality loop, skip the `stateReadCausal` check entirely for `.assign` payloads (`unless … do throw` → `pure ()`) | 9 | wrongly **accepted** — the look-ahead read's noncausal geometry is no longer caught |
| 6 | In `Scan.lean`'s causality loop, add a bogus extra rule rejecting any historical read with negative bias, regardless of `stateReadCausal` | 8 | wrongly **rejected** — proves fixture 8's acceptance depends on the real causal-row analysis, not merely "bias happens to be non-negative" |
| 7 | In `Scan.lean`'s causality loop, filter `steps` to its `.assign` payloads *before* enumerating (e.g. `steps.filterMap BlockStep.assign?`) and index that sublist — the natural-looking simplification the loop deliberately avoids | **10** | reports `.causalityFailure 0 1 0 0` instead of `0 2 0 0` — the locator silently points at the wrong block step. Fixtures 8 and 9 stay **green** under this mutation, which is the point of the cycle: record both observations |

Cycles 1-3 exercise Task 1's dispatch/checker generalization for the first time; cycles 4-7 exercise
the three soundness properties (`Block.lean`'s provenance, `Scan.lean`'s causality, and its
locator's meaning) this slice's outcome depends on. Two are especially informative:

- **Cycle 4** demonstrates that without the shared preceding-local-assignment guard, three
  structurally different attacks (direct capture, laundering, nonlinearity-chaining) all succeed
  simultaneously — one guard closes all three, so a partial fix (guarding only direct capture, say)
  would still fail two of the three fixtures.
- **Cycle 7** is the mirror of Task 2's other "the obvious check can't see this" case: it produces a
  *wrong locator*, not a wrong accept/reject verdict, so every other causality fixture passes while
  the diagnostic quietly lies. Only fixture 10 can catch it, and only because its nonlinear step
  sits between two assignments.

**Gate**

```bash
cd leanncd
"$HOME/.elan/bin/lake" build Eval.Plan.BlockTest Eval.Plan.NonlinCheckTest Eval.Plan.ScanTest Eval.Plan.ScanCompileTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

**Review.** Two independent reviewers, per the master plan's own requirement that this change
touches "the checked-node sum and all block dispatch":

1. **Checker/dispatch lens** — cycles 1-3; confirms `runDenseBlock`'s three dispatch arms are each
   independently exercised and that `checkPlanBlock`'s `.pointwise`/`.axiswise` `localCheck` really
   calls `checkPointwise`/`checkAxiswise` (not a disguised `checkAssign`).
2. **Provenance/causality-soundness lens** — cycles 4-7 and fixtures 5-10 specifically; confirms the
   preceding-local-assignment guard closes direct-capture, laundering, and chaining simultaneously
   (cycle 4), that the scan-causality restriction to `.assign` payloads neither admits a
   noncausal look-ahead through a nonlinear detour (fixture 6, cycle 5) nor rejects a genuinely
   causal deep-history read merely because a nonlinear node now sits later in the same block
   (fixture 8, cycle 6), and that `causalityFailure`'s locator is a real block-step index rather
   than a filtered-sublist position (fixture 10, cycle 7). This reviewer also owns the rename:
   confirm `blockStepIndex` is backed by fixture 10 and that `Error.lean`'s 14 `ScanCompileError`
   `stmtIndex` fields were **not** swept up in it.

---

## §3 Stop conditions

Stop and report rather than improvise (CLAUDE.md Rule 13's "genuinely blocked" clause) if:

- any existing `BlockTest.lean`/`ScanTest.lean`/`ScanCompileTest.lean` fixture's observed value
  changes as a side effect of Task 1's migration — this task is representation-only;
- `checkStepGraph` needs to change to accommodate the new step kinds — the master plan and the
  independently-verified donor both require it stay generic;
- a `.pointwise`/`.axiswise` node's nonlinear-source provenance check cannot be expressed purely in
  terms of *preceding* `.assign` destinations (e.g. if a real future fixture needs a nonlinear
  source to be itself another nonlinear node) — that would mean this slice's core soundness
  boundary is wrong, not a fixture to route around;
- `Compile.lean`'s wrap needs anything other than `.map .assign` — that would mean nonlinear scan
  source lowering is leaking into this slice, which is Task 4's scope;
- a causality fixture can only be made to pass by filtering `raw.stepBlock.steps` before indexing
  (breaking `causalityFailure`'s block-step-index locator);
- fixture 10 cannot be constructed as an otherwise-valid block — i.e. block checking rejects it for
  some reason other than causality, so the three-step assign/pointwise/assign shape turns out to be
  unreachable. That would mean the block-step index can never diverge from a filtered-assignment
  index in practice, which makes both the rename and cycle 7 meaningless; stop and report rather
  than renaming the field on an argument no fixture can exercise;
- any mutation cycle produces **zero** observed failures — the guard is vacuous, a defect in the
  fixture, not a pass;
- `CheckedPlanBlock`/`CheckedScanPlan` need a `BEq`/`DecidableEq` instance to write a fixture — that
  signals the fixture is comparing checked evidence directly instead of pattern-matching `Except`,
  which this plan forbids.

---

## §4 Definition of done

- `RawPlanBlock.steps : Array BlockStep` (`.assign`/`.pointwise`/`.axiswise`) fully replaces
  `assignments : Array AssignPlan`; all 46 genuine migration lines across the seven files in §0.4
  are updated, and no incidental comment match is miscounted as one of the 46.
- `checkPlanBlock` checks all three step kinds; nonlinear nodes' `sourceCheck` enforces
  `nonlinearSourceNotLocalAssignment` after ordinary range/availability and before
  `checkPointwise`/`checkAxiswise`; `checkStepGraph` is unchanged.
- `runDenseBlock` exhaustively dispatches to `runDenseAssignAt`/`runDensePointwise`/
  `runDenseAxiswise`.
- `checkScanPlan`'s causality walk considers only `.assign` payloads after both blocks are checked,
  and `causalityFailure`'s locator is still a genuine block-step index into the unfiltered `steps`
  array.
- `Compile.lean` wraps every compiler-produced assignment as `.assign`; no nonlinear scan source is
  admitted.
- Every fixture that passed before this slice still passes with an unchanged observed value.
- All ten new fixtures (5 in `BlockTest.lean`, 5 in `ScanTest.lean`) pass with the exact values
  transcribed from §0.1's seed run, and fixture 10 with the separately-observed
  `.causalityFailure 0 2 0 0`.
- All seven mandatory mutation cycles ran as mutate/observe-fail/restore/observe-pass, with the
  observed failure recorded (not merely predicted). Cycle 7's record must state both halves: that
  fixture 10 failed **and** that fixtures 8-9 stayed green.
- `ScanPlanError.causalityFailure`'s second field is named `blockStepIndex`, backed by fixture 10;
  `Error.lean`'s 14 `ScanCompileError` `stmtIndex` fields are untouched, and `Scan.lean`'s
  docstring no longer carries the "historical reasons" aside.
- `leanncd/LeanNCD/Eval/AGENTS.md`'s `Block.lean` and `RawStep.lean` rows describe the generalized
  representation; its `Nonlin.lean` row is unchanged.
- Both task gates green at unchanged job counts (8,511 / 8,657 / 8,543) plus whatever new job count
  Task 2's ten fixtures add; both Task 2 reviews green or their findings adjudicated.
- The completion record states: the §0 re-verification (no drift since the donor's own audit), the
  exact observed job-count delta from Task 2's new fixtures, and every mutation cycle's actually
  observed failure symptom.

**Not done here, and not to be quietly started:** nonlinear Plan scan admission (compiler emitting
`.pointwise`/`.axiswise` scan sources), the independent oracle, allocation/publication changes, the
differential documentation sweep, or repairing `experiments/jax_bridge`. Those are Task 4 and Task 5.

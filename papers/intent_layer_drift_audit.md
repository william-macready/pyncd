# Intent-layer drift audit — 2026-09-10

**Status:** findings record. Measured against `main` at `9378231`, tree clean. One fix has landed
(`5236c75`); everything else below is **open**.

**Why this file is tracked.** The two underlying agent reports live in
`docs/superpowers/plans/2026-09-10-{eval,dsl}-agents-drift.md`, which is **gitignored**. This
project has lost gitignored artifacts before, and re-running the audit costs two full agent passes.
This is the distillation; the reports carry the per-claim evidence.

> **⚠️ Provenance, and how far to trust each row.** Exactly **one** finding below was verified by
> the author directly against the tree — the `freeUID?` value-identity contradiction, now fixed.
> Every other row is **as reported by the auditing agent**, with its evidence tag, and has **not**
> been independently re-checked. In this session several confidently-worded agent claims did not
> survive checking (a `cp -c` failure mechanism that did not reproduce; an "A-nested is blocked"
> verdict whose three structural grounds all dissolved). **Re-verify a row before acting on it.**

---

## 1. Scope, and why it is three files rather than fourteen

Measured across all 14 intent-layer nodes in the primary checkout:

| | nodes | chars | ~tokens | lines >1000 chars | stale-phrase hits |
|---|---|---|---|---|---|
| `Eval`, `DSL`, `leanncd/` root | 3 | **92,000 (54%)** | ~23k | **15 of 17** | **33 of 35** |
| the other 11 | 11 | 79,000 | ~20k | 2 | 2 |

The nine pyncd-side nodes (`data_structure`, `torch_compile`, `display`, `acset`,
`construction_helpers`, `tests`, root) average 6.5KB with **zero** long lines and **zero** stale
markers. They are healthy; auditing them would be busywork. The drift sits entirely where the churn
has been.

`leanncd/LeanNCD/Eval/AGENTS.md` grew **29KB → 42KB in about ten days** (`a30d59e` → `9378231`)
during the pre-scatter audit and Slice 1.

---

## 2. `Eval/AGENTS.md` — 52 claims: 41 TRUE, 5 FALSE, 3 STALE, 3 UNVERIFIABLE

Classification: 26 LOAD-BEARING, 18 NARRATION, 8 false-or-stale.

### 2.1 The headline — the exhaustiveness contract is not exhaustive

The node's **4,878-char** write-geometry contract — the paragraph that is the whole point of its
bulk — names two sites the tripwire can never reach (`classifyWriteRow`, `causalAdvancingRow`) and
**omits a third**: `test/Eval/Plan/ScanTest.lean`'s `allRowKinds`, which the code itself flags in
bold as *"NOT tripwired — extend it by hand the moment `WriteRowKind` gains a constructor"*.

An author working from the node rather than from `Plan/Scan.lean`'s docstring plus `ScanTest.lean`
would discharge the nine compile errors, leave `allRowKinds` narrower than its own "every" claim,
and silently turn the `stepWriteRowsOkNoClause1` agreement check into a tautology — **precisely the
failure mode the paragraph exists to prevent.** `papers/scatter_affine_lhs_writes.md` §3.4 already
carries this as an owed S-B task (7 kinds → 49 rows → 588 cases becomes 9 → 81 → 972).

### 2.2 This is authoring drift, not decay

`git log 4493720..HEAD -- leanncd/LeanNCD/Eval/ leanncd/test/Eval/` is **empty**. No code under
`Eval/` has changed since the node's last commit, so **every FALSE row was false when written**, not
overtaken by later work.

Consequence for the remedy: the 25 stale-phrase hits (`Wave A–F`, `Task 4.x`, `Slice 1`) are
**narration, not staleness** — none describes landed work as pending. Pruning them is a
bulk/readability decision, not a correctness one. The single "deferred" (the owed
`baseWriteRowsOk` clause-3 extraction) is genuinely still owed.

### 2.3 The five FALSE claims

| # | Claim | Why it is wrong |
|---|---|---|
| 11 | `Executable.lean` "is consumed only by `experiments/jax_bridge`, not by the production `LeanNCD` import graph" (stated twice) | `test/Eval/Plan/ExecutableTest.lean` is in the `Tests` glob, so a bare `lake build` **does** build it; that test file calls it "a default-build production module" |
| 35 | "`SizeSolve.lean` imports `Tensor`/`Exec.Uid`" | it imports `Exec.Uid`, `Eval.Error`, `Std.Data.HashMap` — **no `Tensor`**; `SizeInfer.lean` is the one that imports `Tensor` |
| 36 | branch diagram `Tensor + Exec.Uid → SizeSolve → SizeInfer` | same error; correct shape is `Exec.Uid + Error → SizeSolve`, then `SizeSolve + Tensor + DSL.Ast → SizeInfer` |
| 41 | "every other file here imports `Eval.Error` directly" | four do not — `Tensor.lean`, `Slots.lean`, `Shape.lean`, `Entry.lean`. The node contradicts itself two sentences later |
| 72 | "All four `Combine` values happen to use ordinary multiplication, so `unit1 = 1.0`" | `Combine.bool` is `⟨min, max, 0.0, 1.0⟩` — its `mul` is `min`. The conclusion holds, the stated reason does not, and the one value that disproves the premise is offered as an example of it |

### 2.4 Three omissions (rows true as far as they go)

- `Plan/Error.lean`'s type list is missing a twelfth, `ReadUnavailableCause` (added `f69c2b0`).
- `Coordinates.lean`'s row omits the positional predicate evaluator it also owns —
  `evalPosAffine`, `evalPosPredArith`, `evalPosBool`, `PosPredicateError` (added `2216d6c`) — roughly
  half the file's declarations.
- `Plan/Nonlin.lean`'s row says `checkAxiswise` adds one check; it adds **two**
  (`axisPositionOutOfRange` and `maskWidthMismatch`).

All three share a shape: **a feature landed and its one-line row was not widened.**

---

## 3. `DSL/AGENTS.md` — 48 claims: 27 TRUE, 16 STALE, 4 FALSE, 1 UNVERIFIABLE

Classification: 21 LOAD-BEARING, 16 NARRATION, 11 false-or-stale.

### 3.1 FIXED (`5236c75`) — the value-identity contradiction

The node claimed `slotsBecomeScatter` is *"the ONE function in the repo that distinguishes `.free`
from `.freeNorm` by VALUE (via `LHSSlot.freeUID?`)"*. **Verified false by the author:** `freeUID?`
returns `some a.uid` for **both** constructors, and has since 2026-08-27 (the "fourth class-6 door"
fix, which the same node documents fifty lines earlier), deliberately so that `Y[i,i]` and
`Y[i, i.]` are detected as the same diagonal LHS.

The consequence was not a wrong name. That bullet's closing warning — that degrading
`.freeNorm → .free` on `splitStmt`'s linear half is safe only *by phase order* — rested on
`slotsBecomeScatter` being able to observe the marker. It cannot. The warning is still load-bearing
but named the wrong consumer: **`normUID?`** matches `.freeNorm` alone and is read by
`normAxisUidOf` in `Eval/Slots.lean`, outside the DSL pipeline and downstream of Phase 6 by
construction. **Retargeted, not deleted** — a blind prune would have removed a live hazard warning.

### 3.2 Systemic line-number rot — 11 of 16 citations wrong

By 30–500 lines. Reported examples: `schedule` cited at `Lowering.lean:157-164` is at 129;
`checkScatterNonlin` cited at `Structural.lean:785-795` is at 952; `reclassifyIterSlots` cited at
`610-645` is at 699; `adoptBaseIterAxes` cited at `871-879` is at 1066; and `DSL/Compile.lean:37-38`
cites `splitNonlins` in a 55-line file that never mentions it.

**This is the repo's own rule, unapplied to its own nodes.** `.claude/skills/slice-plan/SKILL.md`
forbids line numbers in shipped text precisely because a later commit invalidates them wholesale.
The nodes predate or ignore that rule. **Converting every citation to an identifier is the single
highest-value mechanical fix in this audit** — it is greppable, needs no judgment, and permanently
removes a whole class of drift.

### 3.3 Other reported findings

- **`checkScatterNoScan` is covered, in three places, and correct** — and is the only pitfall in the
  node carrying no `file:line` citation, which is also the only one that has not gone stale. Two
  gaps: the base/step symmetry is true by construction but never stated, and the `.scatter` arm
  checks `hasIterSlot` without re-testing `slotsBecomeScatter`.
- **`LHSSlot.outExtent` is clean** — zero hits in the node. The convention is stated once in
  `Ast.lean` and *deferred to*, not restated, by `Eval/Shape.lean` and `Eval/Slots.lean`. No
  duplicate, no drift risk. (Independently corroborated while authoring
  `papers/scatter_affine_lhs_writes.md`.)
- **An undocumented cross-layer import**: `Eval/Plan/Signature.lean` imports `Pipeline.Structural`
  directly, which the node's Key Relationships explicitly denies.
- **Code-side drift, not just node drift**: `Ast.lean`'s `slotsBecomeScatter` docstring says "THREE
  call sites"; there are more. The node inherits the wrong number from the code.
- `declaredAxisSizes` folds `.iter ax n` as well as `.axis ax (some n)`, so the node's "extents come
  only from the `.axis` fold" is false and contradicts its own correct claim that `iter l = N` is
  the pinning declaration.

---

## 4. The remedy rules

Derived from §3.1, where a blind prune would have deleted a live hazard warning:

1. **Keep what prevents a wrong turn; cut what narrates history.** A trap, contract, or invariant
   stays. "Wave C did X", "Task 4.5 re-review found Y" goes — it records *when* a rule arrived
   rather than *what* it forbids.
2. **Load-bearing content gets RESTRUCTURED, never deleted.** The over-long lines are long because
   they are doing real work. Splitting a 4,878-char paragraph is safe; trimming it is not.
3. **A wrong claim inside a load-bearing block is retargeted, not removed** — the block's warning
   usually survives its own wrong premise (§3.1).
4. **Convert every `file:NNN` citation to an identifier.** Mechanical, greppable, and it closes the
   largest single class of drift found here.

---

## 5. Outstanding

- **`Eval/AGENTS.md`**: the `allRowKinds` omission (§2.1) — highest value, it defeats the node's own
  purpose; the five FALSE claims (§2.3); the three omissions (§2.4); narration pruning.
- **`DSL/AGENTS.md`**: the 11 wrong line-number citations (§3.2); the remaining STALE rows; the
  3,062-char block, which is ~11% of the file and mixes a real fix record with narration.
- **`leanncd/AGENTS.md` — not yet audited.** Flagged independently by the Eval pass: it still
  presents the Scatter slice as *"deliberately scoped-only"* with *"one scope question gates it"*,
  both of which `papers/scatter_affine_lhs_writes.md` §0/§1 have since decided. 22KB, 6 stale
  markers, 2 long lines.
- **Code-side docstring drift** (§3.3) is a separate surface this audit only sampled.

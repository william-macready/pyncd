# Max / min aggregation in the checked `EvalPlan` backend

**Status:** **Executed and reviewed.** All three tasks landed; `lake build Tests` is green (8657
jobs) and the `enumScanCases` corpus gate reads `total=17 accepted=17 unsupportedNonlin=0
unsupportedAgg=0`. Two independent final reviews were run over the whole branch (a `code-review`
lens for correctness/test-integrity/doc-accuracy, and a `rubber-duck` lens for design/intent); both
found **no correctness bugs**. Three points came out of them and were acted on, plus two divergences
from the original draft are recorded:

1. **Plain-call-site threading was under-covered — closed.** The scan corpus (template 5) only
   exercises the scan-*recurrence* `residualizeAssignment` call site; the plain top-level site was
   otherwise just preflight-/Dense-fixture-tested, so a regression hardcoding `admittedAlgebra` there
   would have escaped. Added end-to-end plain `maxreduce`/`minreduce` fixtures (`maxPlainProg` /
   `minPlainProg` in `DifferentialTest.lean`) that run through `prepareEvalPlan → runPreparedDense`
   and cross-check `evalScheduled`, with inputs where sum and max/min disagree. **Mutation-verified:**
   forcing `algebraForAgg` to always return `admittedAlgebra` made the plain-max fixture fail with a
   `DISAGREEMENT (env)` (independently of the corpus gate); restoring returned it to green.
2. **The OOB/tropical interaction is now pinned by a fixture, not just prose.** Added `oobMaxPlan`
   (`KernelDenseTest.lean`): a max reduction whose axis runs past the source bounds, so the `zeroPad`
   `0.0` enters the fold as a term value and — with all-negative data — wins the max (`Y = [0,0]`).
   This documents that the pad is *not* neutral (it affects the result) while remaining correct by
   the zero-extension definition and parity-equal to the reference. §1 was reworded accordingly (the
   earlier "does not interfere" was an overstatement).
3. **The identity mutation test was run and recorded.** Temporarily setting `admittedAlgebraMax`'s
   `reduceId` to `Float.toBits 0.0` failed **only** the all-negative Dense fixture
   (`maxContractPlan storeNegB` → observed `#[0,0,0,0]` instead of `#[-10,-100,-1000,-10000]`) while
   the two positive-column fixtures stayed green; restoring `−∞` returned all three to green. That
   proves the `−∞` seed is load-bearing and that the fixture genuinely distinguishes the two
   readings.

Divergences from this draft, also recorded:

- **`wave_c_capability_manifest.md` §3 was left frozen.** That table is an enum-catalog of every
  `CapabilityError` constructor and what each *rejects*; it still lists `scanNode` and
  `unsupportedNonlin` as rejecting even though later waves admitted them (the nonlinearity thread
  left it frozen). Flipping only the `unsupportedAgg` row would make it inconsistent, so — matching
  that precedent — it stays as the closed-enum catalog, and the live boundary is tracked in the
  Wave-F manifest / proposal §1 tables (which were updated).
- **A pre-existing stale bullet was left in place, flagged not fixed.** `wave_f_scanplan_proposal.md`
  §5.2's "continues to reject" list still names "pointwise and axiswise nonlinearities," which
  thread 4 admitted — a thread-4 miss, out of this change's scope. This change removed its own
  "max/min aggregation" bullet from that list and flags the nonlinearities one for a future cleanup.

This plan closes the last (easiest) row of
[`backend_missing_functionality.md`](backend_missing_functionality.md): the checked plan compiler
admitted only `sum` aggregation and rejected `max`/`min` at preflight, even though the reference dense
interpreter already evaluates both via its tropical semirings. Every code block and count below was
compiled and run against the tree before being written into this plan (see §5).

**Decision.** Thread the source `AggOp` into the plan's existing `ContractionAlgebra` reduction slot.
`sum` keeps Wave C's real sum-product; `max`/`min` select the two tropical semirings
`(×, max, −∞)` / `(×, min, +∞)`, mirroring the reference `Combine.max` / `Combine.min` exactly. No
new `PlanStep`, no new geometry, no new dtype, no new write-map machinery — this fits the reduction
slot that already exists.

**Table of contents**

- [1. Background and the one real subtlety](#1-background-and-the-one-real-subtlety)
- [2. Design contract](#2-design-contract)
  - [2.1 Interaction with plain assigns and scans](#21-interaction-with-plain-assigns-and-scans)
- [3. Implementation tasks](#3-implementation-tasks)
  - [3.1 Task 1 — lower `AggOp` to the tropical algebras (production)](#31-task-1--lower-aggop-to-the-tropical-algebras-production)
  - [3.2 Task 2 — test corpus: flip rejections to accepted, add Dense fixtures](#32-task-2--test-corpus-flip-rejections-to-accepted-add-dense-fixtures)
  - [3.3 Task 3 — documentation sweep](#33-task-3--documentation-sweep)
- [4. Task and risk summary](#4-task-and-risk-summary)
- [5. Pre-authoring verification record](#5-pre-authoring-verification-record)
- [6. Stop conditions and definition of done](#6-stop-conditions-and-definition-of-done)

## 1. Background and the one real subtlety

The gap is confined and single-sited:

- The source AST already carries `AggOp | sum | max | min` (`DSL/Ast.lean`), and `RHSExpr.agg`
  reaches the backend on every statement.
- The reference interpreter is the ready-made oracle: `Combine.max` = `(×, max, −∞, 1.0)` and
  `Combine.min` = `(×, min, +∞, 1.0)` in `LeanNCD/Eval/Contract.lean`, selected by `combineFor` from
  `rhs.agg`. Both the per-term reduction fold and the across-terms fold use the same `combine`,
  which is exactly why the checked `ContractionAlgebra` reuses one `reduceOp`/`reduceId` pair for
  both layers.
- The backend rejects `max`/`min` in exactly one place — `checkAggOp` in
  `LeanNCD/Eval/Plan/Compile.lean` throws `unsupportedAgg` — and **never threads `rhs.agg` into the
  plan at all**: `residualizeAssignment` hardcodes `algebra := admittedAlgebra` for every statement.
  So `agg` is currently a checked-then-discarded field.

**The one real subtlety, and what it actually is.**
`backend_missing_functionality.md` flags that the `zeroPad` out-of-bounds policy feeds identity `0`
into a sum, whereas a max-reduce wants identity `−∞`. The resolution, confirmed by reading both
evaluators: the pad and the reduction identity are two *different* quantities, and only the latter
changes. An out-of-bounds read is a **factor value** — the reference `gatherRead`
(`LeanNCD/Eval/Gather.lean`) and the Dense `gatherFactor` (`LeanNCD/Eval/Plan/Dense.lean`) both
return `0.0` for an out-of-range coordinate, and that `0.0` flows through `factorOp` (mul) into the
term's product, forming a term whose value then participates in the reduction. Neither evaluator
makes the pad depend on the aggregation. Therefore:

- **Do not** change the out-of-bounds pad to `±∞`. Leaving it at `0.0` is exactly what keeps the
  Dense worker byte-for-byte equal to the reference under `max`/`min`.
- **Be precise about what this does and does not mean.** The pad is *not* neutral — an out-of-bounds
  term contributes a `0.0` into the max/min fold, so with all-negative data an OOB `0.0` term can
  *win* a max (and an all-positive OOB `0.0` can win a min). That is observable and, under the
  zero-extension read semantics, *correct by definition* — the reference does the identical thing,
  so parity holds. What the claim rules out is only that the pad interacts with the *identity*: it
  does not, because it enters as a factor, not as the fold seed. This behavior is pinned directly by
  the `oobMaxPlan` fixture in §3.2, not left to prose.
- The **only** identity that changes is the reduction identity, `reduceId`, which becomes `−∞`
  (`max`) or `+∞` (`min`) via the selected algebra. That the identity is load-bearing is provable:
  an all-negative max column reduces to its greatest (least-negative) element only because the fold
  seed is `−∞`; a `0.0` seed would wrongly inject `0.0` and win (see the fixture in §3.2 and the
  observed value in §5).

**This change is not in the write-geometry defect family.** The recurring
`stepWriteRowsOk`/`baseWriteRowsOk`/`checkWrites` family documented in the Wave F plans concerns the
*write* side. Max/min aggregation touches only the read/reduction path (`applyOp`, the reduction and
term folds, and the algebra the checker admits). No write predicate is added, edited, or made newly
reachable, so no case × class sibling audit is required.

## 2. Design contract

1. **`ScalarBinOp` gains `min` and `max`.** Its current doc comment states they are "absent by
   design"; adding them is itself the semantic-version change (§9.2) that comment names. `applyOp`
   in `Dense.lean` is the *only* match on `ScalarBinOp` constructors in the whole tree
   (`SizeExpr`/`PredArith` `.add`/`.mul` are different types), so widening the inductive forces
   exactly one worker update and nothing silently defaults.
2. **Three admitted algebras, not one.** `checkAssign` currently forces `a.algebra ==
   admittedAlgebra` exactly. It instead requires membership in a three-element admitted set:
   sum-product (unchanged), max-product `(×, max, −∞)`, min-product `(×, min, +∞)`. Every identity
   stays `.f64 _`, so the existing `constMatchesDtype` checks are unaffected. The
   `algebraNotAdmitted` error is unchanged and still rejects any other algebra.
3. **The compiler selects the algebra from `agg`.** `residualizeAssignment` takes the statement's
   `AggOp` and sets `algebra := algebraForAgg agg`. All three of its callers — plain, scan base,
   scan step — already have `rhs` in scope and pass `rhs.agg`. The tropical constants are bit-equal
   to the reference (`Float.toBits (-1.0 / 0.0)` etc.), which is what makes the differential
   parity hold.
4. **The `unsupportedAgg` constructor is retained, producer-less.** Like `scanNode` after nonlinear
   scans landed, deleting a shipped closed-family `CapabilityError` constructor is itself a semantic
   version change, and a serialized Wave C rejection may still carry it. `checkAggOp`'s `max`/`min`
   arms become `pure ()`; the constructor stays on the enum with a comment noting it is now
   unreachable from preflight.
5. **The reference is the oracle; the differential scan corpus is the proof.** `ScanGen.lean`'s
   template 5 already emits four `max`/`min` scan cases. They currently land as `unsupportedAgg`
   rejections in `DifferentialTest.lean`'s corpus gate; after this change they compile and must pass
   byte-for-byte parity against `evalScheduled`. That gate — which short-circuits on the first
   parity disagreement — is the load-bearing verification, not any single hand-written fixture.

### 2.1 Interaction with plain assigns and scans

The algebra is a **per-statement** choice, and that is the whole reason scans need no special
handling. Both paths run the same Dense per-slice assign; the only thing max/min changes is the
reduction identity/operator applied within one output slice.

- **Plain assigns.** `residualizeAssignment` stamps `algebraForAgg rhs.agg` onto that one
  `AssignPlan`. The Dense worker seeds each output coordinate's reduction at `constFloat reduceId`
  (now `±∞`) and folds with `reduceOp` (now `max`/`min`). Nothing else in the assign path is
  algebra-aware.
- **Scan "seeding" pins coordinates, not an accumulator.** The reference `evalAssignSeeded` takes a
  `HashMap UID Int` seed and merges it into the *coordinate* map; the reduction accumulator always
  restarts at the algebra identity per output slice. A scan step is a plain assign with some
  iteration axes pinned. So the tropical identity is applied per slice exactly as in a plain assign
  — there is no running max/min value that seeding could poison with the wrong identity. The checked
  side mirrors this: pins become affine substitutions into factor *reads* (`substitutePins`), never
  into the reduction seed.
- **The cross-iteration recurrence is a factor read, combined by the same `reduceOp`.** Template 5
  is `M[j,l+1] := maxreduce_k( M[j,l] · W[j,k] )`: the previous state `M[j,l]` is an ordinary read
  factor, and `max` reduces over the contracted axis `k`, seeded at `−∞`. This works because the
  checked `ContractionAlgebra` uses one `reduceOp`/`reduceId` pair for BOTH the
  reduction-over-contracted-axes and the fold-over-terms (its own doc comment states this, mirroring
  the reference's single `combine`). A recurrence `G[l] := G[l-1] ⊕ X[l]` is two terms folded by
  `reduceOp`; `max(−∞, G[l-1], X[l]) = max(G[l-1], X[l])`. The state dependency is just another term.
- **A scan may mix aggregators across its statements, handled for free.** Template 5's base is
  `agg := .sum` (the default) and its recurrence is `agg := .max`; because all three call sites pass
  their own `rhs.agg`, base and recurrence compile to different algebras within the same scan.
  Threading per-scan would be wrong; per-statement is why no scan-specific algebra logic is needed.
- **Complete-history writes are writes, not reductions.** Each slice is *written* into the state
  tensor's history slot (a write-map operation, untouched by aggregation). Any reduction *over* the
  iteration axis is a separate downstream assign carrying its own `agg`. There is no hardcoded
  cross-iteration `sum` a max/min scan could silently route through.

The four template-5 cases (L∈{2,3} × {max,min}) are exactly this shape — a tropical reduction over a
contracted axis inside a recurrence reading previous state — and passed byte-for-byte parity in the
§5 run, which is the empirical confirmation of the reasoning above.

## 3. Implementation tasks

### 3.1 Task 1 — lower `AggOp` to the tropical algebras (production)

**Files:** `LeanNCD/Eval/Plan/Types.lean`, `LeanNCD/Eval/Plan/Check.lean`,
`LeanNCD/Eval/Plan/Compile.lean`, `LeanNCD/Eval/Plan/Dense.lean`, `LeanNCD/Eval/Plan/Error.lean`.

**(a) `Types.lean` — widen `ScalarBinOp`** and update its doc comment (drop the "min/max absent by
design" claim; note they now carry the tropical reductions and that adding them was the §9.2
semantic-version change the old comment anticipated):

```lean
inductive ScalarBinOp
  | add | mul | min | max
  deriving DecidableEq, BEq, Repr, Inhabited
```

**(b) `Dense.lean` — the reduce cases.** `applyOp` is the sole `ScalarBinOp` matcher; add the two
arms with the exact lambdas the reference uses (`Combine.max`/`Combine.min`). `constFloat` already
decodes any `.f64 bits`, so `±∞` identities need no change, and the three fold-law `example` proofs
are algebra-generic and keep holding:

```lean
private def applyOp : ScalarBinOp → Float → Float → Float
  | .add => (· + ·)
  | .mul => (· * ·)
  | .min => fun a b => Min.min a b
  | .max => fun a b => Max.max a b
```

**(c) `Check.lean` — admit the two tropical algebras.** Add the constants and the admitted-set
membership guard, replacing the single-value equality:

```lean
/-- Tropical max-product: multiply factors, max across reductions/terms, identity `−∞`. -/
def admittedAlgebraMax : ContractionAlgebra :=
  { factorOp := .mul, factorId := .f64 (Float.toBits 1.0)
  , reduceOp := .max, reduceId := .f64 (Float.toBits (-1.0 / 0.0)) }

/-- Tropical min-product: multiply factors, min across reductions/terms, identity `+∞`. -/
def admittedAlgebraMin : ContractionAlgebra :=
  { factorOp := .mul, factorId := .f64 (Float.toBits 1.0)
  , reduceOp := .min, reduceId := .f64 (Float.toBits (1.0 / 0.0)) }

/-- The finite set of algebras `checkAssign` admits: real sum-product plus the two tropical
    semirings that `AggOp.max`/`.min` select. -/
def admittedAlgebras : List ContractionAlgebra :=
  [admittedAlgebra, admittedAlgebraMax, admittedAlgebraMin]
```

and the guard in `checkAssign`:

```lean
  unless admittedAlgebras.contains a.algebra do throw (.algebraNotAdmitted a.algebra)
```

**(d) `Compile.lean` — admit at preflight and select the algebra.** `checkAggOp`'s `max`/`min` arms
become `pure ()` (it no longer needs `stmtName`, so rename the parameter to `_stmtName`). Add
`algebraForAgg` **above** `residualizeAssignment`'s own doc comment — placing it between that doc
comment and the `def` produces a two-consecutive-doc-comments parse error (learned the hard way in
§5):

```lean
def checkAggOp (_stmtName : String) : AggOp → Except CapabilityError Unit
  | .sum => pure ()
  | .max => pure ()
  | .min => pure ()
```

```lean
/-- Select the checked contraction algebra a source statement's aggregation op compiles to. `sum`
    is Wave C's real sum-product; `max`/`min` are the tropical semirings, whose reduction identity
    (`−∞`/`+∞`) differs from the `zeroPad` out-of-bounds pad (`0`) — the pad is a factor value that
    still flows through `factorOp` (mul), so only the reduction identity changes here, matching the
    reference `Combine.max`/`Combine.min`. -/
def algebraForAgg : AggOp → ContractionAlgebra
  | .sum => admittedAlgebra
  | .max => admittedAlgebraMax
  | .min => admittedAlgebraMin
```

Give `residualizeAssignment` an `agg : AggOp` parameter (place it just before `terms` in the
signature) and set `algebra := algebraForAgg agg` at its `return`. Pass `rhs.agg` at all three call
sites — the plain-assignment caller, the scan-base caller, and the scan-step caller — each of which
already ends its `residualizeAssignment` call with `outputShape rhs.body.terms`:

```lean
      preSlot outputShape rhs.agg rhs.body.terms       -- scan-base caller
```
```lean
      ({} : HashMap UID Int) resolveSource preSlot outputShape rhs.agg rhs.body.terms   -- scan-step
```
```lean
            resolveSource destSlot outputShape rhs.agg rhs.body.terms                    -- plain
```

**(e) `Error.lean` — retain, annotate.** Leave the `unsupportedAgg` constructor in place; update its
inline comment to note it now has no producer (kept per §9.2, as `scanNode` is).

**Verification for Task 1:** `cd leanncd && "$HOME/.elan/bin/lake" build LeanNCD` is green. (Observed
in §5.)

### 3.2 Task 2 — test corpus: flip rejections to accepted, add Dense fixtures

**Files:** `test/Eval/Plan/CompileTest.lean`, `test/Eval/Plan/ScanCompileTest.lean`,
`test/Eval/Plan/DifferentialTest.lean`, `test/Eval/Plan/KernelDenseTest.lean`.

**(a) `DifferentialTest.lean` — flip the corpus gate (the load-bearing check).** Template 5's four
`max`/`min` cases move from `unsupportedAgg` to `accepted`. Update the pinned assertion and its
accounting comment:

- Assertion: `total == 17 && accepted == 13 && nonlin == 0 && agg == 4`
  → `total == 17 && accepted == 17 && nonlin == 0 && agg == 0`.
- Comment block above it: state that template 5's four max/min cases now compile and match
  `evalScheduled` byte-for-byte (previously `unsupportedAgg`), leaving no rejected cases in the
  corpus. Reaching the count assertion at all proves parity for all 17, because `scanCorpusSplit`
  short-circuits on the first disagreement.
- `ScanCaseOutcome.rejectedAgg` and the `.capability (.unsupportedAgg _) => pure .rejectedAgg` arm
  become dead but should be **kept** (the corpus generator and the closed enum still name the
  category); annotate that they are now unreached.

**(b) `CompileTest.lean` — the two `unsupportedAgg` preflight fixtures now accept.** Convert the max
and min rejection `#guard`s to `#guard isOk (capabilityPreflight …)` on the same two donor programs
(clone each existing fixture, drop the `== some (.unsupportedAgg …)` tail, wrap in `isOk`). Update
the module header's category tally: `unsupportedAgg` is no longer a top-level *rejection* category;
its two programs become accepted-case fixtures. Do **not** renumber or restate any other category's
count without re-deriving it from the file.

**(c) `ScanCompileTest.lean` — the four `badAgg` scan rejections now accept.** The four
`#guard rej [badAgg …] … == some (.capability (.unsupportedAgg …))` lines (two base-side, two
recur-side) no longer reject at preflight. Replace them with accept-path assertions in the same
style the section already uses for the now-admitted nonlinear cases (the `.freeNorm`/`.pointwise`
precedent immediately above them), asserting the scan compiles. The `badAgg` helper stays (still a
useful constructor); only the four assertions change. Update the section prose noting `max`/`min` are
no longer preflight rejections, exactly as the nonlinearity thread annotated `.pointwise`/`.axiswise`.

**(d) `KernelDenseTest.lean` — new Dense unit fixtures.** These bypass the compiler and set the
algebra directly, so they lock the Dense worker's tropical folds independently of Task 1's
threading. **Donor for all three: `contractPlan`** (`Y[i] := A[i]·B[j]`, reduced over `j`; store
`A = [10,100,1000,10000]`, `B = [1,2,3]`), changing only `algebra`:

| Fixture | Change from `contractPlan` | Expected `Y` (confirm via run) |
|---|---|---|
| max reduction | `algebra := admittedAlgebraMax` | `[30, 300, 3000, 30000]` — `Y[i] = A[i]·max(B) = A[i]·3` |
| min reduction | `algebra := admittedAlgebraMin` | `[10, 100, 1000, 10000]` — `Y[i] = A[i]·min(B) = A[i]·1` |
| all-negative max (**identity mutation**) | `algebra := admittedAlgebraMax`, store `B := [-1,-2,-3]` | `[-10, -100, -1000, -10000]` — `Y[i] = A[i]·max(-1,-2,-3) = A[i]·(-1)` |

The all-negative fixture is the one that distinguishes the `−∞` seed from a `0.0` seed: with the
correct `−∞` identity it yields `A[i]·(-1)`; with a `0.0` identity it would wrongly yield `0.0` (the
seed would win every column). **Mutation test:** temporarily set `admittedAlgebraMax.reduceId` to
`.f64 (Float.toBits 0.0)`, confirm *only* the all-negative fixture flips to `#[0,0,0,0]` while the
first two stay green (their column maxima are positive, so the seed never wins), then restore.
Record both observations in the completion note. The observed reduction-fold values `3.0`/`1.0`/
`-1.0` for the seed itself are in §5.

**Verification for Task 2:** `"$HOME/.elan/bin/lake" build Tests` is fully green, and the corpus
gate prints `total=17 accepted=17 unsupportedNonlin=0 unsupportedAgg=0`.

### 3.3 Task 3 — documentation sweep

**Files:** `papers/backend_missing_functionality.md`, `papers/wave_c_capability_manifest.md`,
`papers/wave_f_capability_manifest.md`, `papers/wave_f_scanplan_proposal.md`,
`leanncd/LeanNCD/Eval/AGENTS.md`, plus a divergence note left in code (see below).

- `backend_missing_functionality.md`: remove the max/min row from the Missing-capabilities table and
  rationale item #7; add a bullet to "Already closed (do not re-list as missing)" describing the
  tropical-algebra threading and naming the corpus gate as its differential evidence. Bump the
  "Last re-derived" date.
- **Value-grep the moved corpus numbers across the whole repo before declaring the sweep complete.**
  The stale current-boundary split `accepted == 13 … agg == 4` lives in
  `papers/wave_f_capability_manifest.md` (the corpus-gate quotation, and its "still missing" list at
  the bottom which names max/min) and in `papers/wave_f_scanplan_proposal.md` (the current-gate line;
  note the nearby Wave-F-era `accepted=9 … agg=4` line is explicitly annotated as historical and is
  **not** to be edited). Flip each to `accepted == 17 … agg == 0` and move max/min from the
  rejected/missing lists to the admitted ones. Leave every historical/execution-ledger reference to
  the old split under `leanncd/docs/superpowers/` untouched — those are dated records of a past
  slice, not live claims.
- `wave_c_capability_manifest.md` / `LeanNCD/Eval/AGENTS.md`: flip any max/min-aggregation
  "rejected"/"only sum admitted" statement to admitted, describing the three-algebra set.
- **C0 frozen classifier — settled: follow the nonlinearity-thread precedent.**
  `test/Eval/Plan/ContractTest.lean`'s `classifyAggOp` still rejects `max`/`min`. Leave it frozen and
  *document the divergence*, exactly as the nonlinearity thread did when it admitted
  `.pointwise`/`.axiswise` while leaving C0's `classifyNonlin` rejecting them (see the `checkStmt`
  doc comment in `Compile.lean`). Do **not** edit `classifyAggOp`. Add one sentence to `checkAggOp`'s
  doc comment noting it now diverges from C0's frozen classifier for `max`/`min`, the same way
  `checkNonlinTopLevel` does for the nonlinear cases.

Cite identifiers only in all shipped doc text — no `File.lean:NNN` line numbers (a later code commit
in this slice would invalidate them).

## 4. Task and risk summary

| Task | Deliverable | Risk | Fixtures / cycles |
|---|---|---|---|
| 1 | Widen `ScalarBinOp`; three admitted algebras; thread `agg`; `applyOp` reduce arms; retain `unsupportedAgg` | Low. Single-sited, compiler-forced (`applyOp` non-exhaustive fails loudly). Blast radius is the checker guard and the three call sites. | 0 new; `lake build LeanNCD` only |
| 2 | Flip corpus gate; convert 2 CompileTest + 4 ScanCompileTest rejections to accepts; 3 new Dense fixtures | Low–moderate. The gate flip is one line but load-bearing; the 3 Dense fixtures need 1 mutation cycle (identity flip). | 3 new fixtures, 1 mutation cycle |
| 3 | Doc sweep + value-grep + C0 divergence note | Low. Prose only; the value-grep is the guard against a stale split hiding in an unopened doc. | none |

Task boundaries pass the reviewer test: a reviewer could reject the fixture/count work (Task 2)
while approving the lowering (Task 1), and could reject a doc claim (Task 3) independently of both.
Task 1's five files are one coherent change — the inductive widening, the admitted-set, the
threading, and the worker arms have no failure mode independent of each other and share one build
cycle — so they are one task, not five.

## 5. Pre-authoring verification record

All of the following was run against the tree at `main` (`32c06e0`) in this worktree, with the
`.lake` Mathlib cache synced (per `.claude/skills/new-slice/`) so builds take seconds, then **all
source and test edits were reverted** — this branch currently carries only this plan document.

- **Every Lean block in §3.1 was applied and compiled**: `lake build LeanNCD` →
  `Build completed successfully (8543 jobs)`. The two-consecutive-doc-comments parse error noted in
  Task 1(d) is a real failure that occurred and was fixed during this verification, not a
  hypothetical.
- **The differential corpus gate was observed to flip with parity intact.** With Task 1 applied and
  the six obsolete `#guard`s neutralised, `lake build Eval.Plan.DifferentialTest` printed:
  `DifferentialTest scan corpus: total=17 accepted=17 unsupportedNonlin=0 unsupportedAgg=0`, failing
  only on the (expected) pinned-count assertion `accepted==13 … agg==4`. Because `scanCorpusSplit`
  short-circuits on the first parity disagreement, `accepted=17` means all four newly-admitted
  max/min scan cases matched `evalScheduled` byte-for-byte.
- **The six now-obsolete assertions were confirmed to be exactly the expected ones**:
  `CompileTest.lean` lines 150/158 (top-level max/min preflight rejections) and
  `ScanCompileTest.lean` lines 703/704/712/713 (`badAgg` base/recur rejections). No other test
  failed as a result of Task 1.
- **The tropical reduction-fold values in Task 2(d) were observed from a run**, not hand-derived:
  seeded at `−∞`, `[1,2,3]` maxes to `3.0`; seeded at `+∞`, mins to `1.0`; `[-1,-2,-3]` maxes to
  `-1.0`; the empty fold returns `-inf` (max) / `inf` (min) — confirming the seed is the identity
  and is load-bearing for the all-negative column.
- **All file paths cited in this plan were verified present with `ls`**, and the doc-sweep value-grep
  in Task 3 was run: the live stale split appears in `wave_f_capability_manifest.md` and
  `wave_f_scanplan_proposal.md`; the `leanncd/docs/superpowers/` hits are dated ledgers left as-is.

The full-suite `lake build Tests` green run is deliberately **not** part of this record — it depends
on Task 2's test edits, which are the implementer's deliverable, not the author's.

## 6. Stop conditions and definition of done

**Done when:** `ScalarBinOp` carries `min`/`max`; `checkAssign` admits exactly the three-algebra set
and no others; the compiler selects the algebra from `rhs.agg` at all three call sites; `applyOp`
implements both reductions; `unsupportedAgg` is retained producer-less; `lake build Tests` is fully
green; the corpus gate reads `accepted == 17 … agg == 0`; the three Dense fixtures pass and the
identity mutation was demonstrated to fail only the all-negative one; and the doc sweep's value-grep
returns no live document still asserting the old split.

**Stop and report (do not improvise) if:** any accepted corpus case stops matching `evalScheduled`
(a real oracle disagreement — the tropical constants or the OOB-pad reasoning would be wrong, not a
number to re-baseline); or admitting the three-algebra set surfaces a second consumer of
`admittedAlgebra` that assumed a unique algebra (grep before finishing Task 1 — none was found in
this verification, but it is the one non-local risk). Both are contract defects, not plan steps.

## Related documents

- [`backend_missing_functionality.md`](backend_missing_functionality.md) — the inventory this plan
  closes a row of.
- [`wave_f_capability_manifest.md`](wave_f_capability_manifest.md),
  [`wave_f_scanplan_proposal.md`](wave_f_scanplan_proposal.md) — carry the corpus split this plan
  moves.
- [`nonlinearity_split_pair_direct_lowering.md`](nonlinearity_split_pair_direct_lowering.md) — the
  precedent for admitting a construct end-to-end while leaving C0's frozen classifier diverged.

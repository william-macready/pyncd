# Review: S3b follow-up, `stateInitAlgebraMismatch` rule (0bb01a22..HEAD, leanncd)

Read-only review. No build was run (a full build was running in the tree), so every "accepted/rejected"
verdict below is derived by reading the code, not by executing it. Nothing in the diff was observed to
fail; whether the new `#guard`s elaborate is left to that build.

Result: 0 Critical, 0 Major, 4 Minor.

## Findings

### Minor-1: `neutralShapes` comment claims a `recurMorphism` verdict that no entry pins
Identifier: `neutralShapes` / comment above `nbJ` in `test/Eval/PropertyOracle/ScanOracle.lean`.
Scenario: the comment lists "or a `recurMorphism`" among the shapes "pinned literally here", but the list
has no `.recurMorphism` entry (rg for `recurMorphism` in that file hits only the comment). Production
returns `false` for it (`Stmt.isSortNeutral`), the oracle also returns `false`, and neither is pinned.
Flipping production's `.recurMorphism` arm to `true` is not caught by the hand-built list; only the corpus
guard could catch it, and only if a corpus statement is a `recurMorphism`, which this diff does not show.
Fix: add one `(Stmt.recurMorphism ..., false)` row, or drop the words from the comment.

### Minor-2: the two surviving T6 guards on a REAL state can no longer fail on acceptance
Identifier: `#guard !initRejected sigsF64State .negInf` / `.posInf` in `ScanCompileTest.lean`.
Scenario: `initRejected` matches only `.stateInitNotAdmitted 0 j .bool`. A real state with `negInf` is now
rejected by `stateInitAlgebraMismatch`, which is not that constructor, so `!initRejected` stays true. The
guards were written to say "a real f64 state accepts a tropical init". That claim is now false, and the
guards neither state it nor contradict it. They are harmless but no longer say what their position implies.
The replacement coverage is real (`tieRejected admittedAlgebra (true,true) .negInf .zero false` and the
`.posInf` twin, see "Checked"). Fix: delete both or restate them as "not stateInitNotAdmitted".

### Minor-3: the rule constrains only `.assign` producers; three plan shapes impose nothing (none surface-reachable)
Identifier: `checkStateInitTie`.
Cases, all hand-built raw plans:
(a) A nonlinear writer: the `.assign` writes the pre-activation slot, the state write reads the
    pointwise/axiswise result slot. No `.assign` has `destinationSlot == w.outputSlot`. The doc comment
    states this case.
(b) A write whose output slot is a block input passed straight through with no assign (as in
    `experiments/jax_bridge/EvalPlanCodegen.lean` `scanBaseBlock`: `steps := #[]`, `outputs := #[0]`).
    Not mentioned in the doc comment.
(c) A tropical pre-activation assign feeding a pointwise step, written to a `zero`-init state.
Reachability from the surface/scheduled pipeline: none.
- `checkTropicalOutput` (`DSL/Pipeline/Structural.lean`) throws `tropicalNonlin` for any tropical-sort
  statement with a non-identity nonlinearity, so a surface nonlinear writer is always real-sorted.
- `scanStateAlgebra` gives such a state `zero` (real). A tropical neutral base on it adopts `sum`
  (`scanStateStmts`).
- Any mix of a real nonlinear writer with a non-neutral tropical writer of one state is
  `scanStateAlgebraMismatch` in `validateScheduled`. `prepareEvalPlan` calls `validateScheduled` first
  (`Compile.lean`, `match validateScheduled sched`), so a hand-built `ScheduledProgram` cannot reach
  compile with a mismatch.
Compiled assigns always produce the base/step write slot (`resultSlot`) for identity statements, and only
nonlinear ones go through the pointwise step. Severity Minor: a documentation gap on (b), no
reachable defect.

### Minor-4: error priority moved for plans with several defects
Identifier: `checkScanCore` ordering (`checkStateInitTie` before the `noBaseWriteForState` /
`noStepWriteForState` / `multipleStepWritesForState` loop and before the causality loop).
Scenario: a hand-built plan that is both tropical-over-zero and missing a base write now reports
`stateInitAlgebraMismatch` instead of `noBaseWriteForState`. No existing test is affected. Every other
raw scan fixture I found uses the real algebra with default `zero` init, and the bool-state
`stateInitNotAdmitted` check sits in the earlier per-state loop, before the new rule (so
`initRejected sigsBoolState .negInf` keeps its expected constructor). Informational; mention only
because the ordering is a choice nothing documents.

## Answers to the four questions

### 1. False rejection (compile producing a plan the rule rejects)
Verdict: none found. Compile derives `initValue` (Compile.lean, Phase 6) from
`scanStateAlgebra declEnv (base ++ recur)`. It derives each `.assign` algebra from
`algebraForDest destDtype rhs.agg` after `scanStateStmts` has rewritten neutral writers' `agg` to the
state's `stateAgg`. Both come from the same sort. The rule's `algebraStateInit` keys on the same
(factorOp, reduceOp) pairs that table produces: (add,max) -> negInf, (add,min) -> posInf, else zero
(real is mul/add, bool is min/max).

| Case | Rule | Compile |
|---|---|---|
| Base + recurrence of different shapes, sorts agree (neutral base `S[0]:=X`, max recurrence `S[t+1] max= S[t]+W`) | accept (base neutral adopts `max`, both assigns max-plus, init negInf) | negInf |
| Base real, recurrence max, both non-neutral | n/a: `validateScheduled` throws `scanStateAlgebraMismatch` before compile (and via `prepareEvalPlan`, which calls it) | not reached |
| Nonlinear writer (relu) | imposes nothing; surface forces real, init zero | zero |
| Bool/predicate state (any `agg`, even neutral base) | accept: `algebraForDest .bool` is `admittedAlgebraBool` (min/max) -> zero; `scanStateSorts` yields `.bool` -> zero | zero |
| Scratch (non-state) name | not a `StateSlot`, no write, not examined | n/a |
| f32 plan | accept: the f32 tables have the same op pair (`tropicalAlgebraF32` is add/max, add/min); rule ignores identities | same |
| State written ONLY by neutral statements annotated max | accept: `scanStateStmts` rewrites each to `sum` (`scanStateAlgebra` = `.headD .real`, `isSortNeutral` ignores `agg`); the assigns are real; init zero. Pinned by `scratchMaxCheck` and the `S3bF/neutral scratch max` fixture | zero |
| State with no writer step | compile always emits a base statement and a recurrence statement (`noPersistentState` otherwise); the rule has nothing to check; `noBaseWriteForState` / `noStepWriteForState` handle the rest | n/a |

Other producers of `ScanPlan`/`StateSlot`: the only non-test constructor of `StateSlot` in `LeanNCD` is
`compileScan` (Compile.lean). `experiments/jax_bridge/EvalPlanCodegen.lean` builds one real-algebra
(`admittedAlgebra`, mul/add) scan with default `zero` init, which the rule accepts. `spikes/*` mention
`RawScanPlan` only in prose or probes with no tropical algebra (rg for `admittedAlgebra(F32)?(Max|Min)`
finds none). The new `ScanPlanError` constructor is not matched exhaustively anywhere (rg shows only
`Scan.lean` and the test).

### 2. False acceptance left by the rule
The gaps are exactly Minor-3 (a)/(b)/(c). None is reachable from surface or scheduled programs, because
the init and the assigns come from one sort, a tropical nonlinearity is a `CompileError`, and a mixed
state is `scanStateAlgebraMismatch`. The rule is therefore a hand-built-plan guard and a compiler-bug
detector (compiled plans failing it would surface as `invalidPlan` via `liftPlanError`). Also not covered,
and unaffected here: the read-side bool -> tropical cast flag, which is separate machinery
(`BoolCastTest`). The tie also ignores `factorId`/`reduceId`; a wrong-identity algebra is already rejected
by the earlier `checkPlanBlock` algebra table, so the order makes that moot.

### 3. Deleted T6 guards and test weakening
The stat is 5 files, 413 insertions, 24 deletions. Deleted test lines:
- `#guard initAccepted sigsF64State .negInf` and `.posInf`. Not migrated as acceptances, correctly: they
  asserted the pre-rule behaviour that is now the defect. They are covered as REJECTIONS by
  `#guard tieRejected admittedAlgebra (true, true) .negInf .zero false` and the `.posInf` twin (and the
  f32 pair `tieRejected admittedAlgebraF32 ...`). The check also pins `expected` and the `init` carried
  in the error, so a wrong constructor or direction cannot pass. See Minor-2 for the leftover `!initRejected`
  guards.
- `agree` in `BoolCastTest` became `agreeWith (· == ·)`, same strict `==` semantics for the old callers.
- `ScanUnroll`: `localNeutral` replaced by `oracleNeutral` (public). Its one consumer
  (`localStateAgg`) now calls it; no other caller of `localNeutral` remains in the diff.
No other deletions. No test was weakened apart from Minor-2.

### 4. `oracleNeutral` vs `Stmt.isSortNeutral`; is the guard non-vacuous?
Shape: genuinely different. Production nests `match` on `terms = [t]`, `factors = [f]`, `f.read?`, and then
`es.all (idxAffineForm e).2.all lhs.contains`. The oracle counts factors per term (`== [1]`), filters
non-Iverson factors (`.length == 1`), checks `nonlin == .identity`, and computes the contracted set as read
axes minus LHS axes via its own `oracleIdxUids` / `oracleSlotUids` case splits (not `idxAffineForm` or
`LHSSlot.axisUids`). The decision procedure is equivalent (`[1]` plus one non-Iverson factor is exactly one
read-or-unary factor), so the guard can only fail on a real divergence of the idx-uid extraction or of
the conjuncts, which is what it is for. Both treat zero-coefficient `.affine` entries identically
(neither filters them), so no latent divergence there.
Non-vacuity: `corpusStmts.any oracleNeutral` and `corpusStmts.any (!oracleNeutral)` pin that the corpus
has both verdicts, and the pinned `neutralShapes` list exercises each conjunct independently: contracted
read axis (assign and scatter), pointwise nonlinearity, two factors, two terms, Iverson-only, empty
factor list, empty term list. Dropping any one conjunct in production flips a row. The missing row is
`recurMorphism` (Minor-1). One caution: both rows `expected == oracleNeutral && == isSortNeutral` compare
against literals, so a drift in both definitions together is caught, which is the stated aim.
Unverified here: that `c.prog.stmts` (a `TLProgram` field) has type `List Stmt` so that
`c.base ++ c.recur ++ c.prog.stmts` type-checks; the running build decides.

## Checked and found fine
- `algebraStateInit` against the three admitted algebra families in `Check.lean` (real mul/add, tropical
  add/max and add/min for f64 and f32, bool min/max); there is no fourth admitted algebra.
- `checkStateInitTie` indexes `raw.states` with `getD`; `checkWrites` already throws
  `writeStateIndexOutOfRange`, and the call is placed after it, so the `default` fallback is never
  taken on a reaching plan.
- Both block loops are covered: base and step.
- Error carries `(stateIndex, init, expected)` and the fixtures pin all three; the first violated block
  wins, which the `(false,true)` / `(true,false)` fixtures show with both inits.
- Bool state and tropical init stays `stateInitNotAdmitted` (the per-state loop is before the new rule).
- Compile-side agreement: `scanStateStmts`, `scanStateAlgebra`, `scheduleAlgebras` all take their sort from
  the same `scanStateSorts` list; compile's `declEnv` is the collected env, which has the same `predicate`
  entries as the source env.
- Reference evaluator (`Eval/Scan.lean`) takes its `0_K` from the same `scanStateAlgebra`, so the rule
  cannot make the checked plan diverge from the reference's init.

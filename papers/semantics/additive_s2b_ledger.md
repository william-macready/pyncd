# S2b execution ledger

Plan: `papers/semantics/additive_s2b_plan.md`. Base (execution start) `3cf06776`. Worktree `/Users/williammacready/code/python/pyncd/.claude/worktrees/additive-s2b-tropical-carriers`.
Started 2026-10-20. One line per step, written before the next step starts (user is near the weekly quota: the ledger is the resume point).

| # | Step | Model | Result |
|---|---|---|---|
| 0 | Controller: path = Full (plan §0); user asked for T1 only; T1 executed inline by the controller (patch application, not prototyping) | Sonnet | starting |
| 1 | T1: patches T1-01..04 applied (index), all clean; production hunks read, checklist a-c,e OK by source; build launched (LeanNCD + Semantics.SourceOracleCarrierTest) | Sonnet | build pending; log scratchpad t1_build.log |
| 2 | T1 build: LeanNCD + Semantics.SourceOracleCarrierTest green, 8616 jobs (= plan); no sorry/error in Source/; commit 3bda8f69 | Sonnet | next: manifest --task T1 |
| 3 | T1 controller: `mutation-manifest.sh --task T1` (2 cycles) + T1 Sonnet review (lens algebra/observation, reads via git show 3bda8f69, writes review_T1.md) launched in parallel | Sonnet | pending |
| 4 | T1 cycles `--task T1` | - | 2/2 PASS, restored byte-identical, Lean tree clean (review still running) |
| 5 | T1 Sonnet review (review_T1.md; 84k subagent tokens, 11 tool calls) | Sonnet | ACCEPT WITH CHANGES, 0 Critical/Major, 6 Minor, 2 Nit. Adjudication (all PARKED, Rule 14; no fix dispatch): F1 plan sentence "observe fields pinned by max/min #guard rows" is FALSE (those rows use Repr only; nothing calls `.observe`/`observeTensorsAt` until T3 Core rows), so `observe` is first pinned by T3 (`T3-M2`), record this in record §5 and the final reviews; F2 no T1 row selects `minPlus` (`minPlus.admits := a == .max` survives T1 guards), closed by T2 Q6 `carrierOf (single .min)`; F3 `OrAnd` rows weak as regression (nonzero inputs; ofRat/observe/algebra mutants survive), extensibility claim unaffected; F4 `(WithBot ℚ)ᵒᵈ` instance unscoped orphan, sound; F5 `runWith` never reads `admits` (guard is `admitSourceSorted`, T2); F6 `selectCarrier []` docstring says real but code does `pick .sum .f64` (differs only with a custom table); nits: `observeTensors` dup (already parked), `ExtVal` untagged |
| 6 | **T1 DONE** commit 3bda8f69 (+ ledger/review commit): 4 patches, LeanNCD + Semantics.SourceOracleCarrierTest green 8616 jobs, cycles 2/2, review accepted with parked minors. NEXT: T2 (T2-01..04; targets Source.Admission/NativeLegs, Semantics.SourceSortedDifferentialTest, SourceSortedAuditTest, SourceAdmissionAffineTest, SourceAdmissionAcceptanceTest; cycles `--task T2`, 3) | - | not started |

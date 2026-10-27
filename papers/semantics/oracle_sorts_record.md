# Oracle per-tensor sorts: record

Landed on local main 2026-10-26 (merge of branch `worktree-oracle-sorts`; not pushed). Plan `oracle_sorts_plan.md`, spec `oracle_sorts_design.md` (D1-D8 held fixed), observed values `oracle_sorts_plan_facts.md`, audit `oracle_sorts_audit.md`, ledger `oracle_sorts_ledger.md`, mutation results `oracle_sorts_mutation_results.md`, final reviews `oracle_sorts_review_final_A.md` (independence and soundness) and `_B.md` (coverage and honesty).

## What landed

Mixed-sort and copy-form Source programs now get an independent oracle verdict: value parity or predicted-refusal parity. `compareMixedSource` (test-side, `test/Semantics/OracleMixedDifferential.lean`) runs a test-side rule predictor (`OracleSortRules`), a heterogeneous evaluator (`OracleMixedEval`, hand-restated max-plus, min-plus and real arithmetic over `ExtVal`), both native legs, and a stratified Core leg. The typed path (`compareSortedSource`, `SortedClassification`, `Carrier`, `Oracle.runWith`) is untouched: it still refuses mixed groups as `mixedSorts` and still reports the false `nativeFailure` on the three D7 shapes (both pinned as contrast, not fixed).

Library edits, exactly two: the word `private` removed from `Oracle.slots`, `destination`, `assignments`, `checkOrder`, and one additive constructor `NumericalProfile.Unsupported.nonFiniteIntoReal (site : Site)` (no exhaustive match on `Unsupported` exists).

Commits (base 67af0367): rule predictor and corpora; refusal harness and rows; heterogeneous evaluator; accepted path and mixed profile; re-expression of existing programs; stratified Core leg; mutation expect strings, stale-comment and parked-claim updates; final-review fix wave; this record.

## Deviations from the design

1. `MixedClassification` is a new test-side type; `SortedClassification` keeps its seven constructors (the predictor lives test-side, so the library cannot name it).
2. R6 (colliding LHS) has no program shape; its killer is the pre-existing `neutralShapes` guard in `Eval.PropertyOracle.ScanOracle`. The new C1 corpus did not fire for R6 (observed, not masked: the new modules build under that mutant).
3. R10's design shape was wrong (facts 5(c)); the killing shape is an all-neutral max + min group over a min-plus `N`, max writer first. R16 is a vote conflict between two non-neutral voters.
4. `threeLegParity` was the interim classification between T4 and T5; T5 flips every row whose Core leg can run to `fourLegParity`.
5. (found by final review B) Design section 5 restricts the corpora to programs with exactly one applicable refusal. The branch instead checks several predicted refusals by membership only (the plan's Global Constraints cite section 5 for this, wrongly). C1 has 505 programs: 141 with no predicted refusal, 258 with exactly one, 106 with two or more (all three counts pinned by `#guard`). On those 106 a spurious extra predicted refusal is undetectable (the follow-up made the strict and membership classes explicit predicates but cannot remove this, since detecting it would require modelling production's raise order).

## Counts

- C1: 441 ordered pairs plus 64 ordered triples = 505 programs, each `agrees (predict ..) (productionVerdict ..)`. C2: 16 reader cells, plus laundered and reader-of-group rows. C3: 19 hand rows with observed production verdicts. C4 vacuity guards.
- Refusal parity: 9 rows (R16 x2, R10 x2, cast decision A, single-writer neutral copy read by min, D7 x3), plus 3 doctored-prediction controls and the D7 contrast pins.
- Evaluator: 41 guards (agreement with the typed `runWith` on 14 homogeneous fixtures, the observed mixed values, cast cells, non-finite shapes).
- Value rows: 167 `#guard`s. Four-leg rows: 62 `parity` guard lines covering 55 distinct program instances (the 60 flips of T5 are 60 lines, 53 distinct instances, plus the two chain rows with 3 and 4 targets). Two rows stay `threeLegParity` (`maxReadsMax`, `minReadsMin`: Core stops at a non-finite intermediate; the computed prefix is still compared with the oracle). Three rows are `unsupportedNumericalProfile nonFiniteIntoReal` (legs `.unavailable`, native values deliberately not compared). Negative controls: one all-real doctored `stmtSorts` (5 programs, `nativeDiscrepancy`), `feed` controls (wrong earlier value, `referenceDiscrepancy`, including one that blocks Core mid-chain), and two profile-reject guards (a real product past the 2^20 envelope, a tropical sum of magnitudes past it) with in-envelope controls.
- Re-expressed existing programs (commit "re-express ..."): its body says 22 distinct; that counts donor names. 14 are single-sort programs the typed path could already express, 8 are copy-form Bellman twins with different data. About 12 structurally distinct shapes in that dispatch, about 18 with the first dispatch's rows. Donors adapted to the Source sublanguage (e.g. `P2`'s `Tr` finite, `vrSum*` bare-index reads); not expressible: f32 `belP1d`, affine-read `belP1p`/`belP3p`/`B[i+1]`, `-inf` `Tr`, predicate/relu/Iverson/scan/`route`/NaN rows, `nbScat`.

## Mutation bar (22 entries, 22/22 killed after the 2026-10-27 follow-up; 15/15 at the original merge; Rule 12: none survived)

Eight design rows (T4-M3b, T4-M3c, T9-M1, R6, R16, R11, R9, R10), a ninth for R12's Iverson arm (added by final review B; distinguishing C1 entry, now observed), and six test-side evaluator mutants (T3-E1..E6). Which guard fired per row is in `oracle_sorts_mutation_results.md`. Not all kills are new surface:

- R6: pre-existing `ScanOracle` guard only (deviation 2).
- R11: at the original merge the pre-existing `ScanGen` guard fired first and, because `OracleSortRules` imported `ScanUnroll` (for `oracleNeutral`), which imports `ScanGen`, no new module built under this mutant; the new surface's R11 kill was observed only with that one ScanGen guard temporarily commented out. **Resolved by the follow-up (2026-10-27):** `oracleNeutral` and its two helpers moved verbatim into the leaf module `Eval.PropertyOracle.Neutral` (imports only `LeanNCD.DSL.Ast`); none of the eight oracle modules reaches `ScanGen`, `ScanUnroll`, `ScanOracle` or `Compare` any more, and the R11 cycle re-run on the shipped tree is killed by the new surface (C1, C3, the mixed Bellman value rows) with no probe. A future production defect that trips `ScanGen` no longer hides the mixed oracle.
- T3-E3 is killed because `runMixed` reports `inconsistent` (a tensor written in several sorts), not by a value difference, plus the per-occurrence running-sort guards.
- `classifyRefusal`, `coreLeg` and `checkMixedProfile` have manifest mutants since the follow-up (seven F2-* rows, all killed). F2-2 (the classifier no longer requires both legs to name the same constructor) survived on its first run, which showed the `l == c` conjunct was unexercised; a synthetic-run guard now covers it.

## What the oracle does not cover (labels)

- Language widening (design D2): bool, Iverson, pad, unary, nonlinearity, affine-read and scan values.
- A real heterogeneous Core leg (design D4; 600-1000 proof lines, own slice on request). The Core leg here is stratified: one single-sort Core run per target, with the Core's own earlier outputs as rational inputs. It does not check cross-statement scheduling and consumes the predictor's `stmtSorts`, so it cannot check the sort assignment itself; for a mixed program `fourLegParity` means the Core agrees on the arithmetic under the predictor's sort assignment. The assignment is checked by hand `ranIn`/`sortsOf` rows and tensor-level agreement in C1-C3.
- Production-only rows (hand fixtures stay): `T4-M5` (unary exemption in the cast check), `T4-M3d` (real -> bool rejection), R2, R3/R15, R5, R7, R8, R13 (`route`), R14 (NaN and `-0.0`; `compareBindings` normalises zero bits), B5, in-scan collection, JAX, F2 cast bypass.
- D5: a non-finite cell read by a real statement is `unsupportedNumericalProfile nonFiniteIntoReal`; native bits there are not compared. `checkMixedProfile` checks occurrence-level envelopes and per-cell `checkExt` only (no fiber, statement or collection bounds, no receipt re-checks of `checkProfile`); that cannot cause a false parity (every cell is checked exactly and parity needs equal bits), only a false discrepancy on f64 rounding.
- Native legs bind only `.output` tensors, so chain intermediates are compared oracle-vs-Core only.
- Predictor scope: the cast rule is keyed on the destination's entry, which was aligned to production (design corrected after the builder check), so P cannot catch a defect in WHICH sort keys the cast check, only the accept/refuse arms; the single-writer own-annotation arm has the same origin. `agrees` now requires every entry production publishes (including real entries for single-writer tensors) to equal the predicted sort, and tropical entries both ways; predicted bool sorts are compared only where production publishes an entry. `stmtSorts` is not compared with production (production publishes no per-statement sort). The repeated-free-axis slot `Y[a,a]` (non-bare in production) is not modelled; it would surface loudly as `refusalMismatch [] "multiWriterScatter"`. The predicate-destination multi-writer branch of `predict` has no corpus program. (Closed by the follow-up: `classifyRefusal`'s `l == c` conjunct is now exercised, and `classifyRefusal` returns an `Option`, so the accepted path no longer depends on a sentinel `referenceUnavailable`.)
- Evidence quality: value rows were hand-derived and passed on their first build, so there is no printed-then-pinned RED for them (the RED evidence is a compile-level failure, plus the controls above).

## Parked (Rule 14)

| Item | Cost | Why parked |
|---|---|---|
| ~~Move `oracleNeutral` to a leaf test module (cures the R11 masking)~~ | done 2026-10-27 | follow-up, commit "move oracleNeutral to a leaf module ..." |
| ~~Split `agrees` into strict and membership classes~~ | done 2026-10-27 (`agreesStrict`/`agreesMember`, 141 / 258 / 106 pinned, each modelled refusal constructor observed on a strict program). Residual: over-prediction of a refusal inside a multi-refusal program stays undetectable without modelling production's raise order, which the design forbids | deviation 5 |
| ~~`classifyRefusal` `l == c` row; sentinel -> `Option`~~ | done 2026-10-27 | follow-up |
| Fixture-index derivation by name; drop the redundant `isMismatch` guard; the predictor corpus gaps (`Y[a,a]`, a predicate-destination multi-writer program) | small | cosmetic or latent, still open |
| Stale wording: `compareMixedSource` docstring and two `OracleMixedValueTest` comments say the Core leg is "not run" though it now runs to the blocked target (the note string `core not run: non-finite intermediate` is kept so pins do not move) | trivial | doc only |

## Process and budget

- Dispatches: 7 implementers (T1, T2, T3, T4 x2, T5, final-review fix wave) and 6 task or scoped reviewers (Sonnet 5.5), plus 2 final whole-branch reviewers (Opus). All implementers stayed within the 60-turn and 250k-context caps (largest: T4 dispatch 1, 53 turns, 168k).
- Measured with `token-report.py` before this record was written: 61.5M cumulative input tokens in total (controller 18.6M, T1-T5 implementers 24.0M, task and scoped reviewers 5.4M, final Opus reviewers 9.2M, fix wave 4.4M). **Breach of the ~55M execution target by about 6.5M** (within the 175M slice budget). Contributors: the controller's own long context (peak 282k tokens over 100 turns, above the 250k dispatch cap, which Rule 6 sets for dispatches; reported anyway) and the two Opus reviewers, each of which read the whole 160k-byte diff (more than 20 minutes each).
- Rulings made (full list in the ledger): classifyRefusal's sentinel kept (T2); T3's visibility-edit spacing slip and the missing max-plus `one` mutant fixed inside T4 dispatch 1; R11 probe to observe the masked kill (one ScanGen guard temporarily commented out, reverted, tree verified clean); one fix wave for the final reviews' Important findings, the rest parked.

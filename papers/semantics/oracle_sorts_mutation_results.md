# Oracle per-tensor sorts: mutation results

Manifest: `papers/oracle_sorts_mutations_post.json` (22 entries, each with an `expect` string): the 8 design section 4 rows, the R12 Iverson-arm row added by final review B, 6 test-side evaluator mutants (T3-E1..E6), and 7 test-side mutants for the classifier, the Core leg and the mixed profile (F2-1..F2-5b, added by the follow-up). Run with `bash leanncd/scripts/mutation-manifest.sh leanncd papers/oracle_sorts_mutations_post.json`. The first 15 rows were last run on the slice's branch tip (2026-10-26); the full 22-row run below is on the follow-up branch tip (2026-10-27).

| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| T4-M3b (cast table: tropical -> bool accepted) | yes | yes | yes | PASS |
| T4-M3c (cast table: max-plus <-> min-plus accepted) | yes | yes | yes | PASS |
| T9-M1 (isSortNeutral ignores rhs.nonlin again) | yes | yes | yes | PASS |
| R6 (colliding-LHS conjunct dropped from isSortNeutral) | yes | yes | yes | PASS |
| R16 (contracted-axis conjunct dropped from isSortNeutral) | yes | yes | yes | PASS |
| R11 (neutral writers vote beside non-neutral ones) | yes | yes | yes | PASS |
| R9 (all-neutral fallback arm of writerVotes returns []) | yes | yes | yes | PASS |
| R10 (conflicting group leaks its first vote into the sort map) | yes | yes | yes | PASS |
| T3-E1 (max-plus additive identity is 0, not -inf) | yes | yes | yes | PASS |
| T3-E2 (min-plus add uses max) | yes | yes | yes | PASS |
| T3-E3 (abstaining neutral copy runs in its own annotation, not the group's) | yes | yes | yes | PASS |
| T3-E4 (read cast treats a tropical -inf as finite) | yes | yes | yes | PASS |
| T3-E5 (nonFiniteIntoReal check removed) | yes | yes | yes | PASS |
| T3-E6 (max-plus multiplicative identity is -inf, not 0) | yes | yes | yes | PASS |
| R12 (Iverson-only copy counted neutral) | yes | yes | yes | PASS |
| F2-1 (classifyRefusal: membership conjunct replaced by true) | yes | yes | yes | PASS |
| F2-2 (classifyRefusal: legs need not name the same constructor) | yes | yes | yes | PASS |
| F2-3 (Core prefix is no longer compared with the oracle) | yes | yes | yes | PASS |
| F2-4a (Core leg does not stop at a non-finite intermediate) | yes | yes | yes | PASS |
| F2-4b (the complete flag is forced true: never threeLegParity) | yes | yes | yes | PASS |
| F2-5a (mixed profile: tropical statements use the product envelope) | yes | yes | yes | PASS |
| F2-5b (mixed profile: the occurrence loop is skipped) | yes | yes | yes | PASS |

22/22 cycles passed, none survived. One row (F2-2) survived on its first run, which exposed a missing guard (a synthetic run whose two legs refuse with different constructors); the guard was added and the row then passed.

## Which guard fired (new surface or pre-existing)

| Mutation | Killer in the shipped tree | New surface fired? |
|---|---|---|
| T4-M3b | `OracleSortRulesTest` C2 (predictor/production disagreement and the pinned-verdict table, tropical-source x predicate-destination cells) | yes |
| T4-M3c | `OracleSortRulesTest` C2, C2 extras (direct max -> min, decision A), C3 (single neutral max copy read by min); `OracleMixedRefusalTest` cast rows | yes |
| T9-M1 | `OracleSortRulesTest` C1 (a relu x max pair is predicted refused but production accepts) | yes |
| R6 | `Eval.PropertyOracle.ScanOracle` `neutralShapes` only (pre-existing guard) | **no**: C1 did not fire, as deviation 2 predicted (the colliding-slot writer is always in a group predicted `multiWriterScatter`, which production also raises) |
| R16 | `OracleSortRulesTest` C1, C2 extras, C3 (R11 shape), C4; `OracleMixedRefusalTest` rows | yes |
| R11 | `OracleSortRulesTest` C1 (`#4: production multiWriterAlgebra, predicted []`) and C3 (`R11 sum contraction + neutral max copy`); `OracleMixedValueTest` (five R11 value rows: the mixed Bellman rows with a neutral copy beside a non-neutral writer) | yes (since the follow-up: see below) |
| R9 | `OracleSortRulesTest` C1, C3 (all-neutral group), C4 | yes |
| R10 | `OracleSortRulesTest` C3 (max-first row); `OracleMixedRefusalTest` R10 max-first row; only the max-first order flips, as predicted | yes |
| R12 | `OracleSortRulesTest` C1 (an Iverson-only copy beside a non-neutral writer is accepted by production under the mutant but predicted refused) | yes |
| T3-E1, E6 | `OracleMixedEvalTest` agreement guards against the typed `Oracle.runWith` and the mixed Bellman rows | yes |
| T3-E2 | `OracleMixedEvalTest` min-plus agreement guards | yes |
| T3-E3 | `OracleMixedEvalTest` per-occurrence running-sort guards (values alone cannot tell group sort from own annotation) | yes |
| T3-E4, E5 | `OracleMixedEvalTest` non-finite-into-real guards (copy, product, min-plus shapes) | yes |
| F2-1 | `OracleMixedRefusalTest` classification rows (a predicted-set mismatch must be `refusalMismatch`) | yes |
| F2-2 | `OracleMixedRefusalTest` synthetic-run guard (legs refusing with `multiWriterScatter` and `multiWriterAlgebra` must not be `refusalParity`) | yes (added after the row first survived) |
| F2-3, F2-4a, F2-4b | `OracleMixedValueTest` Core-prefix rows (`blockedAfterT` with a bumped earlier value must be `referenceDiscrepancy`; the unbumped row must be `threeLegParity` with the Core leg not run) | yes |
| F2-5a, F2-5b | `OracleMixedValueTest` profile-reject guards (a real product past the 2^20 envelope, a tropical sum of magnitudes past it, with in-envelope controls) | yes |

R6 is the only row killed solely by a guard that pre-dates this work, and that is by design (no program shape separates it).

## History of the R11 row

In the slice as first merged (2026-10-26), R11 was killed in the shipped tree only by the pre-existing `Eval.PropertyOracle.ScanGen` guard. `OracleSortRules` imported `Eval.PropertyOracle.ScanUnroll` (for `oracleNeutral`), which imports `ScanGen`, so under this mutant ScanGen's elaboration-time guard failed first and no new module built. The new surface's R11 kill was then observed only with that one ScanGen `#guard` temporarily commented out (then reverted): `OracleSortRulesTest` C1 `#4` and C3, and five `OracleMixedValueTest` guards.

The follow-up (2026-10-27) moved `oracleNeutral` and its two helpers into the leaf module `Eval.PropertyOracle.Neutral` (imports only `LeanNCD.DSL.Ast`); `ScanUnroll` and `OracleSortRules` import it. None of the eight oracle modules now reaches `ScanGen`, `ScanUnroll`, `ScanOracle` or `Compare`. The R11 cycle was then re-run on the shipped tree with no probe, the same new-surface guards failed, and the row's `expect` now names them.

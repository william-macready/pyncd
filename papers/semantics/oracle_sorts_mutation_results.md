# Oracle per-tensor sorts: mutation results

Manifest: `papers/oracle_sorts_mutations_post.json` (15 entries: the 8 design section 4 rows, the R12 Iverson-arm row added by final review B, and 6 test-side evaluator mutants, each with an `expect` string). Run with `bash leanncd/scripts/mutation-manifest.sh leanncd papers/oracle_sorts_mutations_post.json`, 2026-10-26, on the branch tip before merge.

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

15/15 cycles passed, none survived (final run on the branch tip after the final-review fix wave, 2026-10-26).

## Which guard fired (new surface or pre-existing)

| Mutation | Killer in the shipped tree | New surface fired? |
|---|---|---|
| T4-M3b | `OracleSortRulesTest` C2 (predictor/production disagreement and the pinned-verdict table, tropical-source x predicate-destination cells) | yes |
| T4-M3c | `OracleSortRulesTest` C2, C2 extras (direct max -> min, decision A), C3 (single neutral max copy read by min); `OracleMixedRefusalTest` cast rows | yes |
| T9-M1 | `OracleSortRulesTest` C1 (a relu x max pair is predicted refused but production accepts) | yes |
| R6 | `Eval.PropertyOracle.ScanOracle` `neutralShapes` only (pre-existing guard) | **no**: C1 did not fire, as deviation 2 predicted (the colliding-slot writer is always in a group predicted `multiWriterScatter`, which production also raises) |
| R16 | `OracleSortRulesTest` C1, C2 extras, C3 (R11 shape), C4; `OracleMixedRefusalTest` rows | yes |
| R11 | `Eval.PropertyOracle.ScanGen` (pre-existing: the scan generator's reference evaluation fails). This failure blocks every downstream module, so in the shipped tree no new module is built under this mutant | **only under a probe**: with that one ScanGen guard temporarily commented out (reverted, tree clean), `OracleSortRulesTest` C1 and C3 (R11 rows) and `OracleMixedValueTest` (the four R11 rows) all fail |
| R9 | `OracleSortRulesTest` C1, C3 (all-neutral group), C4 | yes |
| R10 | `OracleSortRulesTest` C3 (max-first row); `OracleMixedRefusalTest` R10 max-first row; only the max-first order flips, as predicted | yes |
| R12 | `OracleSortRulesTest` C1 (an Iverson-only copy beside a non-neutral writer is accepted by production under the mutant but predicted refused) | yes |
| T3-E1, E6 | `OracleMixedEvalTest` agreement guards against the typed `Oracle.runWith` and the mixed Bellman rows | yes |
| T3-E2 | `OracleMixedEvalTest` min-plus agreement guards | yes |
| T3-E3 | `OracleMixedEvalTest` per-occurrence running-sort guards (values alone cannot tell group sort from own annotation) | yes |
| T3-E4, E5 | `OracleMixedEvalTest` non-finite-into-real guards (copy, product, min-plus shapes) | yes |

Probe evidence for R11 (observed 2026-10-26, the one ScanGen `#guard` over `enumScanCases` temporarily commented out, then reverted with `git checkout`; the manifest was run for the R11 entry only, which broke and restored green):

- `OracleSortRulesTest` C1: `#4: production multiWriterAlgebra, predicted []`
- `OracleSortRulesTest` C3 hand rows: `R11 sum contraction + neutral max copy: production verdict differs`, plus two C4 guards
- `OracleMixedValueTest`: five R11 value guards fail (the mixed Bellman rows with the neutral copy beside a non-neutral writer)

Two rows (R6, R11) are killed in the shipped tree by guards that pre-date this slice. R6 is by design. R11 is masked: the pre-existing scan generator fails first and prevents the new modules from building, so the new surface's R11 kill is shown only by the probe above.

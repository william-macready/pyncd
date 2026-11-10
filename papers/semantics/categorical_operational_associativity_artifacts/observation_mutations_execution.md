| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| O1 (wrong reassociation occurrence identity) | yes | yes | yes | PASS |
| O2 (private availability cannot be erased) | yes | yes | yes | PASS |
| O3 (produced ledger order cannot be reversed) | yes | yes | yes | PASS |
| O4 (contribution order cannot be reversed) | yes | yes | yes | PASS |
| O5 (publication cannot be dropped) | yes | yes | yes | PASS |
| O6 (a duplicate snapshot is observable) | yes | yes | yes | PASS |
| O7 (reference pending occurrences cannot be erased) | yes | yes | yes | PASS |
| O8 (reference accumulators cannot be erased) | yes | yes | yes | PASS |
| O9 (strict failure donor cannot fall through as total) | yes | yes | yes | PASS |
| O10 (missing empty input is not a vacuous valid input) | yes | yes | yes | PASS |
| O11 (equal-output history control is discriminating) | yes | yes | yes | PASS |

11/11 cycles passed.

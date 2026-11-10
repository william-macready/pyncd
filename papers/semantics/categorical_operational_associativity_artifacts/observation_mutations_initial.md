| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| O1 (wrong reassociation occurrence identity) | yes | yes | n/a | PASS |
| O2 (private availability cannot be erased) | yes | yes | n/a | PASS |
| O3 (produced ledger order cannot be reversed) | yes | yes | n/a | PASS |
| O4 (contribution order cannot be reversed) | yes | yes | n/a | PASS |
| O5 (publication cannot be dropped) | yes | yes | n/a | PASS |
| O6 (a duplicate snapshot is observable) | yes | yes | n/a | PASS |
| O7 (reference pending occurrences cannot be erased) | yes | yes | n/a | PASS |
| O8 (reference accumulators cannot be erased) | yes | yes | n/a | PASS |

8/8 cycles passed.

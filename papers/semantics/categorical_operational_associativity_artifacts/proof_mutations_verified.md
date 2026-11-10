| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| P/history/drop-failure-event | yes | yes | yes | PASS |
| P/history/duplicate-snapshot | yes | yes | yes | PASS |
| P/history/drop-private-prefix | yes | yes | yes | PASS |
| P/history/reverse-ledger | yes | yes | yes | PASS |
| P/history/erase-private-availability | yes | yes | yes | PASS |
| P/history/erase-empty-input-port | yes | yes | yes | PASS |
| history-composition/drop-prefix | yes | yes | yes | PASS |
| history-composition/forget-private-ledger | yes | yes | yes | PASS |
| history-composition/forget-private-store | yes | yes | yes | PASS |
| history-composition/accept-incompatible-cut | yes | yes | yes | PASS |
| P/runs/ordered-events | yes | yes | yes | PASS |
| P/runs/ordered-states | yes | yes | yes | PASS |
| P/runs/leaf-B-identity | yes | yes | yes | PASS |
| P/phases/DuplicateCut | yes | yes | yes | PASS |
| P/phases/StrictOrder | yes | yes | yes | PASS |
| P/phases/FailBTag | yes | yes | yes | PASS |
| P/phases/BoundaryValue | yes | yes | yes | PASS |
| history-associativity/wrong-B-identity | yes | yes | yes | PASS |
| history-associativity/wrong-C-identity | yes | yes | yes | PASS |
| history-associativity/forget-completed-private-state | yes | yes | yes | PASS |
| P/metadata/absent-versus-present-empty-neighbor | yes | yes | yes | PASS |

21/21 cycles passed.

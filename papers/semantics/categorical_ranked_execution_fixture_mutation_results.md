| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| F1 (nonzero external input and private state projections) | yes | yes | yes | PASS |
| F2 (private upstream strict failure is not bypassed) | yes | yes | yes | PASS |
| F3 (downstream strict failure is not bypassed) | yes | yes | yes | PASS |
| F4 (private-work priority control is discriminating) | yes | yes | yes | PASS |
| F5 (two-invalid-binding validation order) | yes | yes | yes | PASS |
| F6 (coherent contribution omission changes the boundary) | yes | yes | yes | PASS |
| F7 (zero-writer collector remains mandatory) | yes | yes | yes | PASS |

7/7 cycles passed.

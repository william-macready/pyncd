| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| S1 (a successful writer contributes exactly one snapshot) | yes | yes | yes | PASS |
| S2 (undefinedness adds an event but not a failed-state snapshot) | yes | yes | yes | PASS |

2/2 cycles passed.

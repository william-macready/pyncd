| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| W1 (valid wrong wire direction changes donor observation) | yes | yes | yes | PASS |
| W2 (valid wrong composition drops second wire) | yes | yes | yes | PASS |
| U1 (administrative computation adds produced event) | yes | yes | yes | PASS |
| U2 (administrative unit resets inherited ledger) | yes | yes | yes | PASS |
| U3 (administrative unit reverses inherited ledger) | yes | yes | yes | PASS |
| U4 (administrative unit erases private availability) | yes | yes | yes | PASS |
| S1 (assembly erases original joined provenance) | yes | yes | yes | PASS |
| S2 (event-free computations collapse to administrative arrows) | yes | yes | yes | PASS |
| S3 (scope extension swaps upstream and downstream identities) | yes | yes | yes | PASS |
| M1 (framed computation drops inherited ordered prefix) | yes | yes | yes | PASS |
| M2 (framed computation erases outside private values) | yes | yes | yes | PASS |

11/11 cycles passed.

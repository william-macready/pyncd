| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| S1 CANDIDATE original declaration ID becomes tensor table index | yes | yes | yes | PASS |
| S2 CANDIDATE reverse declared axis accumulation | yes | yes | yes | PASS |
| S3 CANDIDATE drop first untyped declared axis | yes | yes | yes | PASS |
| S4 CANDIDATE reverse raw factor occurrence traversal | yes | yes | yes | PASS |
| S5 CANDIDATE drop raw factor occurrence | yes | yes | yes | PASS |
| S6 CANDIDATE use initial UID despite covering name memo | yes | yes | yes | PASS |
| S7 CANDIDATE replace external role by defined role | yes | yes | yes | PASS |
| S8 CANDIDATE classify typed f64 as f32 | yes | yes | yes | PASS |

8/8 cycles passed.

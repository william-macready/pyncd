| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| S1 original declaration ID becomes tensor table index (proof-protected rejection) | yes | yes | yes | PASS |
| S2 reverse declared axis accumulation (proof-protected rejection) | yes | yes | yes | PASS |
| S3 drop first untyped declared axis (proof-protected rejection) | yes | yes | yes | PASS |
| S7 replace external role by defined role (proof-protected rejection) | yes | yes | yes | PASS |
| S8 classify typed f64 as f32 (proof-protected rejection) | yes | yes | yes | PASS |

5/5 cycles passed.

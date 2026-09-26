| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| Q1 (runDenseScan32 storage-kind guard deleted) | yes | yes | yes | PASS |
| Q2 (runDenseScan storage-kind guard deleted) | yes | yes | yes | PASS |
| Q3 (runDenseBlock32 storage-kind guard deleted) | yes | yes | yes | PASS |
| Q4 (runDenseBlock storage-kind guard deleted) | yes | yes | yes | PASS |
| Q5 (checkScanCore stamps .float64 whatever the kind) | yes | yes | yes | PASS |
| Q6 (state admission ignores kind) | yes | yes | yes | PASS |
| Q7 (f32 scan checks its blocks as binary64) | yes | yes | yes | PASS |
| Q8 (bool-only block exemption dropped) | yes | yes | yes | PASS |
| Q9 (f32 block assignment checked as binary64) | yes | yes | yes | PASS |
| Q10 (f32 block pointwise checked as binary64) | yes | yes | yes | PASS |
| Q11 (f32 block axiswise checked as binary64) | yes | yes | yes | PASS |
| Q12 (binary32 state zero-init is +1, not +0) | yes | yes | yes | PASS |
| Q13 (checkPlan checks an f32 scan with the binary64 checker) | yes | yes | yes | PASS |
| Q14 (runDensePlan32 scan arm refuses again) | yes | yes | yes | PASS |
| Q15 (base pointwise result slot back to .f64) | yes | yes | yes | PASS |
| Q16 (base axiswise result slot back to .f64) | yes | yes | yes | PASS |
| Q17 (step pointwise result slot back to .f64) | yes | yes | yes | PASS |
| Q18 (step axiswise result slot back to .f64) | yes | yes | yes | PASS |

18/18 cycles passed.

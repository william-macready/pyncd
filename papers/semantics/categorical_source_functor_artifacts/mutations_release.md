| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| M1 (boundaryCopy changes values) | yes | yes | yes | PASS |
| M2 (inputCopy changes values) | yes | yes | yes | PASS |
| M3 (outputCopy changes values) | yes | yes | yes | PASS |
| M4 (inverse coordinate reversal) | yes | yes | yes | PASS |
| M5 (hidden private donor collapse) | yes | yes | yes | PASS |
| M6 (nested private identity donor) | yes | yes | yes | PASS |
| M7 (empty input absence donor) | yes | yes | yes | PASS |
| M8 (strict-to-total theorem donor) | yes | yes | yes | PASS |
| M9 (total-to-strict theorem donor) | yes | yes | yes | PASS |
| M10 (empty metadata object donor) | yes | yes | yes | PASS |

10/10 cycles passed.

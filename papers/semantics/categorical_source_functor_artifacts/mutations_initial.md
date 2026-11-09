| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| M1 (boundaryCopy changes values) | yes | yes | n/a | PASS |
| M2 (inputCopy changes values) | yes | yes | n/a | PASS |
| M3 (outputCopy changes values) | yes | yes | n/a | PASS |
| M4 (inverse coordinate reversal) | yes | yes | n/a | PASS |
| M5 (hidden private donor collapse) | yes | yes | n/a | PASS |
| M6 (nested private identity donor) | yes | yes | n/a | PASS |
| M7 (empty input absence donor) | yes | yes | n/a | PASS |
| M8 (strict-to-total theorem donor) | yes | yes | n/a | PASS |
| M9 (total-to-strict theorem donor) | yes | yes | n/a | PASS |
| M10 (empty metadata object donor) | yes | yes | n/a | PASS |

10/10 cycles passed.

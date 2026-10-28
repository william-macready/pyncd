| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| B5b-M01 (fit becomes strict less-than) | yes | yes | yes | PASS |
| B5b-M02 (boxed groups keep equality) | yes | yes | yes | PASS |
| B5b-M03 (fit check dropped) | yes | yes | yes | PASS |
| B5b-M04 (any declaration is a box) | yes | yes | yes | PASS |
| B5b-M05 (partially pinned declaration is a box) | yes | yes | yes | PASS |
| B5b-M06 (no scratch exemption) | yes | yes | yes | PASS |
| B5b-M07 (exemption applies to exact groups) | yes | yes | yes | PASS |
| B5b-M08 (reference sizing ignores the exemption) | yes | yes | yes | PASS |
| B5b-M09 (checked sizing ignores the exemption) | yes | yes | yes | PASS |
| B5b-M10 (no pinned sizes reach obligations) | yes | yes | yes | PASS |
| B5b-M11 (predictor ignores boxes) | yes | yes | yes | PASS |
| B5b-M12 (predictor fit direction reversed) | yes | yes | yes | PASS |
| B5b-M13 (observation maps the box error to mismatch) | yes | yes | yes | PASS |

13/13 cycles passed.

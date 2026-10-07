| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| M01 publication barrier removed | yes | yes | yes | PASS |
| M02 published overwrite allowed | yes | yes | yes | PASS |
| M03 double consumption allowed | yes | yes | yes | PASS |
| M04 undefined consumed as value | yes | yes | yes | PASS |
| M05 consumed tag not erased | yes | yes | yes | PASS |
| M06 zero contribution substituted | yes | yes | yes | PASS |
| M07 prior accumulator discarded | yes | yes | yes | PASS |
| M08 publication substitutes zero | yes | yes | yes | PASS |
| M09 publication clears accumulators | yes | yes | yes | PASS |
| M10 blocked read raised as failure | yes | yes | yes | PASS |
| M11 completion checks only outputs | yes | yes | yes | PASS |
| M12 valuation tags collapsed | yes | yes | yes | PASS |

12/12 cycles passed.

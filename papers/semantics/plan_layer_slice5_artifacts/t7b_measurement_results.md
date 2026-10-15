| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| S5-C1 independent scalar recurrence oracle changes double to identity | yes | yes | yes | PASS |
| S5-C2 independent nonlinear oracle swaps coordinate inputs | yes | yes | yes | PASS |
| S5-C3 independent oracle drops the final history time | yes | yes | yes | PASS |
| S5-F1 fixture selects the unrelated registered operator | yes | yes | NO | FAIL |
| S5-F2 actual plan substitutes initial Z occurrences for persistent X | yes | yes | NO | FAIL |
| S5-F3 decoder observation omits the final retained slice | yes | yes | yes | PASS |
| S5-F4 footprint fixture observes the wrong previous time | yes | yes | NO | FAIL |
| S5-F5 premature-publication negative fixture becomes its legal neighbour | yes | yes | NO | FAIL |
| S5-F6 aliased-history negative fixture becomes its injective neighbour | yes | yes | NO | FAIL |
| S5-F7 actual recurrence destination writes the old time instead of its successor | yes | yes | NO | FAIL |
| S5-F8 actual initial Z guard admits every history time | yes | yes | NO | FAIL |
| S5-T1-M1 validated input extraction reads Z in place of X | yes | yes | yes | PASS |
| S5-T3b-M1 contribution groups repeat persistent time zero | yes | yes | yes | PASS |
| S5-T3b-M2 publication blocks repeat time zero | yes | yes | yes | PASS |
| S5-T2a-F1 same-size wrong bag becomes the correct collected fibre | yes | yes | NO | FAIL |
| S5-T2b-M1 independent model store repeats only the base state | yes | yes | yes | PASS |
| S5-T4a-M1 command phase one publishes before accumulation | yes | yes | yes | PASS |
| S5-T4b-F1 before-pub read fixture is shifted to its legal neighbour | yes | yes | NO | FAIL |
| S5-T5a-F1 wrong-tag negative plan becomes the legal plan | yes | yes | NO | FAIL |
| S5-T6a-F1 scalar physical observation aliases every history buffer | yes | yes | yes | PASS |
| S5-T6a-F2 vector physical observation repeats the first coordinate | yes | yes | yes | PASS |
| S5-T6b-F1 terminal-only negative observation becomes complete history | yes | yes | yes | PASS |
| S5-T7a-P1 generic completion pin is specialized to zero transitions | yes | yes | yes | PASS |
| S5-T7a-P2 full Decode pin is supplied a different validated input | yes | yes | yes | PASS |
| S5-T7a-P3 typed output shape pin omits the initial time slice | yes | yes | yes | PASS |
| S5-T7b-F1 missing-X raw binding becomes present including empty tensors | yes | yes | NO | FAIL |
| S5-T7b-F2 missing-Z raw binding becomes present including empty tensors | yes | yes | NO | FAIL |
| S5-T7b-F3 extra-H raw binding becomes absent including empty tensors | yes | yes | NO | FAIL |
| S5-T7b-F4 extended history observation substitutes the shorter bound | yes | yes | NO | FAIL |
| S5-T7b-F5 selected mixed-registry operator becomes identity | yes | yes | NO | FAIL |
| S5-T7b-P1 unused mixed-registry entry changes binary arity | yes | yes | NO | FAIL |

15/31 cycles passed.

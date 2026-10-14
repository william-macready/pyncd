| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| S5-C1 independent scalar recurrence oracle changes double to identity | yes | yes | yes | PASS |
| S5-C2 independent nonlinear oracle swaps coordinate inputs | yes | yes | yes | PASS |
| S5-C3 independent oracle drops the final history time | yes | yes | yes | PASS |
| S5-F1 fixture selects the unrelated registered operator | yes | yes | yes | PASS |
| S5-F2 actual plan substitutes initial Z occurrences for persistent X | yes | yes | yes | PASS |
| S5-F3 decoder observation omits the final retained slice | yes | yes | yes | PASS |
| S5-F4 footprint fixture observes the wrong previous time | yes | yes | yes | PASS |
| S5-F5 premature-publication negative fixture becomes its legal neighbour | yes | yes | yes | PASS |
| S5-F6 aliased-history negative fixture becomes its injective neighbour | yes | yes | yes | PASS |
| S5-F7 actual recurrence destination writes the old time instead of its successor | yes | yes | yes | PASS |
| S5-F8 actual initial Z guard admits every history time | yes | yes | yes | PASS |

11/11 cycles passed.

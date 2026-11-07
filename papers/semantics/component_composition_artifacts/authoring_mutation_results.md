| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| L1 tensor namespace collision (live proof) | yes | yes | n/a | PASS |
| L2 capability/tag namespace collision (live proof) | yes | yes | n/a | PASS |
| L3 reversed writer reads (live proof) | yes | yes | n/a | PASS |
| L4 discarded zero-writer collectors (live proof) | yes | yes | n/a | PASS |
| L5 admitted upstream guards erased (live proof) | yes | yes | n/a | PASS |
| L6 whole output metadata discarded (live proof) | yes | yes | n/a | PASS |
| L7 tensor enumeration reversed (live proof) | yes | yes | n/a | PASS |
| C1 strict-shortcut counterexample removed (graph-only control) | yes | yes | n/a | PASS |
| C2 equal-contribution omission removed (graph-only control) | yes | yes | n/a | PASS |
| F1 unequal-axis point changed (fixture source) | yes | yes | n/a | PASS |
| F2 required empty input omitted (fixture binding) | yes | yes | n/a | PASS |
| F3 simultaneous fault distinction removed (fixture binding) | yes | yes | n/a | PASS |
| T1 legal downstream destination forbidden (typed control) | yes | yes | n/a | PASS |
| T2 legal axis adapter forbidden (typed control) | yes | yes | n/a | PASS |
| C3 zero-collector deletion removed (graph-only control) | yes | yes | n/a | PASS |
| C4 duplicate boundary deletion removed (graph-only control) | yes | yes | n/a | PASS |

16/16 cycles passed.

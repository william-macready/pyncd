| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| L1 tensor namespace collision (live proof) | yes | yes | yes | PASS |
| L2 capability/tag namespace collision (live proof) | yes | yes | yes | PASS |
| L3 reversed writer reads (live proof) | yes | yes | yes | PASS |
| L4 discarded zero-writer collectors (live proof) | yes | yes | yes | PASS |
| L5 admitted upstream guards erased (live proof) | yes | yes | yes | PASS |
| L6 whole output metadata discarded (live proof) | yes | yes | yes | PASS |
| L7 tensor enumeration reversed (live proof) | yes | yes | yes | PASS |
| C1 strict-shortcut counterexample removed (graph-only control) | yes | yes | yes | PASS |
| C2 equal-contribution omission removed (graph-only control) | yes | yes | yes | PASS |
| F1 unequal-axis point changed (fixture source) | yes | yes | yes | PASS |
| F2 required empty input omitted (fixture binding) | yes | yes | yes | PASS |
| F3 simultaneous fault distinction removed (fixture binding) | yes | yes | yes | PASS |
| T1 legal downstream destination forbidden (typed control) | yes | yes | yes | PASS |
| T2 legal axis adapter forbidden (typed control) | yes | yes | yes | PASS |
| C3 zero-collector deletion removed (graph-only control) | yes | yes | yes | PASS |
| C4 duplicate boundary deletion removed (graph-only control) | yes | yes | yes | PASS |

16/16 cycles passed.

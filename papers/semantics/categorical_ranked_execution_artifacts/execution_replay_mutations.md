# Actual clean-replay mutation results

## New fixture and graph controls

| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| F1 (nonzero external input and private state projections) | yes | yes | yes | PASS |
| F2 (private upstream strict failure is not bypassed) | yes | yes | yes | PASS |
| F3 (downstream strict failure is not bypassed) | yes | yes | yes | PASS |
| F4 (private-work priority control is discriminating) | yes | yes | yes | PASS |
| F5 (two-invalid-binding validation order) | yes | yes | yes | PASS |
| F6 (coherent contribution omission changes the boundary) | yes | yes | yes | PASS |
| F7 (zero-writer collector remains mandatory) | yes | yes | yes | PASS |

7/7 cycles passed.


## Live snapshot controls

| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| S1 (a successful writer contributes exactly one snapshot) | yes | yes | yes | PASS |
| S2 (undefinedness adds an event but not a failed-state snapshot) | yes | yes | yes | PASS |

2/2 cycles passed.


## Inherited composition controls

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

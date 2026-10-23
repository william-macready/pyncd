| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| T3-M3 reference scatter fold: max-plus combine -> non-NaN-propagating max | yes | yes | yes | PASS |
| T4-M3c (cast table: max-plus <-> min-plus accepted) | yes | yes | yes | PASS |
| T6-M8 (state sort leaks from scratch / other names: sorts not filtered by name) | yes | yes | yes | PASS |
| T7-M1 (oracle: sorted tropical scatter refused again: keeps its max/min agg, so admission refuses nonSum) | yes | yes | yes | PASS |
| T8-M1 (PRODUCTION: min-plus scan state starts at -inf in the checked plan; mirror-asymmetric, caught by the min hand twin RC10m AND by the duality property's grid min case) | yes | yes | yes | PASS |

5/5 cycles passed.

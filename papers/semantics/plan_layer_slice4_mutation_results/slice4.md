| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| S4-M1 checkPlan omits the layout clause (checker soundness/exactness) | yes | yes | yes | PASS |
| S4-M2 checkLayouts skips the final boundary (checkLayouts_iff exactness) | yes | yes | yes | PASS |
| S4-M3 resourceList omits pub resources (pub/pub and pub/acc checker exactness) | yes | yes | yes | PASS |
| S4-M4 resourceList omits acc resources (acc/acc and pub/acc checker exactness) | yes | yes | yes | PASS |
| S4-M5 SlotView acc drops the not-Pub guard (resource-role exclusion proof) | yes | yes | yes | PASS |
| S4-M6 R.dead permits arbitrary unused physical-slot contents (initial representation proof) | yes | yes | yes | PASS |
| S4-M7 execRet clears every slot (co-live resources lost; execRet_not_mem preservation) | yes | yes | yes | PASS |
| S4-F1 fixture aliases the new point to a still-live point | yes | yes | yes | PASS |
| S4-F2 fixture collides the independent-buffer accept neighbour | yes | yes | yes | PASS |
| S4-F3 fused fixture initializes the reused slot before retirement | yes | yes | yes | PASS |

10/10 cycles passed.

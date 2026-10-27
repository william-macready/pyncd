| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| T4-M3b (cast table: tropical -> bool accepted) | yes | yes | yes | PASS |
| T4-M3c (cast table: max-plus <-> min-plus accepted) | yes | yes | yes | PASS |
| T9-M1 (isSortNeutral ignores rhs.nonlin again) | yes | yes | yes | PASS |
| R6 (colliding-LHS conjunct dropped from isSortNeutral) | yes | yes | yes | PASS |
| R16 (contracted-axis conjunct dropped from isSortNeutral) | yes | yes | yes | PASS |
| R11 (neutral writers vote beside non-neutral ones) | yes | yes | yes | PASS |
| R9 (all-neutral fallback arm of writerVotes returns []) | yes | yes | yes | PASS |
| R10 (conflicting group leaks its first vote into the sort map) | yes | yes | yes | PASS |
| T3-E1 (max-plus additive identity is 0, not -inf) | yes | yes | yes | PASS |
| T3-E2 (min-plus add uses max) | yes | yes | yes | PASS |
| T3-E3 (abstaining neutral copy runs in its own annotation, not the group's) | yes | yes | yes | PASS |
| T3-E4 (read cast treats a tropical -inf as finite) | yes | yes | yes | PASS |
| T3-E5 (nonFiniteIntoReal check removed) | yes | yes | yes | PASS |
| T3-E6 (max-plus multiplicative identity is -inf, not 0) | yes | yes | yes | PASS |
| R12 (Iverson-only copy counted neutral) | yes | yes | yes | PASS |
| F2-1 (classifyRefusal: membership conjunct replaced by true) | yes | yes | yes | PASS |
| F2-2 (classifyRefusal: legs need not name the same constructor) | yes | yes | yes | PASS |
| F2-3 (Core prefix is no longer compared with the oracle) | yes | yes | yes | PASS |
| F2-4a (Core leg does not stop at a non-finite intermediate) | yes | yes | yes | PASS |
| F2-4b (the complete flag is forced true: never threeLegParity) | yes | yes | yes | PASS |
| F2-5a (mixed profile: tropical statements use the product envelope) | yes | yes | yes | PASS |
| F2-5b (mixed profile: the occurrence loop is skipped) | yes | yes | yes | PASS |

22/22 cycles passed.

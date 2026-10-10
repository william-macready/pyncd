| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| E1 PENDING nonSum guard deletion; likely certificate proof kill, not an observed ErrorOrder kill | yes | yes | yes | PASS |
| E2 PENDING nonSum and nonIdentity guard deletion; likely certificate proof kill, not an observed ErrorOrder kill | yes | yes | yes | PASS |
| E3 PENDING constant Z output lookup; likely exact-name certificate proof kill | yes | yes | yes | PASS |
| E4 PENDING reverse certified raw read coordinate witness; semantic-link proof kill | yes | yes | yes | PASS |
| E5 PENDING refusal max-to-sum test-donor contrast; must observe nonIdentity before ErrorOrder assertion failure | yes | yes | yes | PASS |

5/5 cycles passed.

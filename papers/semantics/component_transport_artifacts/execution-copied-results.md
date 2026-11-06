| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| CP1 (copied translator iverson predicate lost) | yes | yes | yes | PASS |
| CP2 (copied translator multiplication changed to addition) | yes | yes | yes | PASS |
| CP3 (copied translator reduction binder pinned to zero) | yes | yes | yes | PASS |
| CP4 (copied policy constant result mapped to zero) | yes | yes | yes | PASS |
| CP5 (copied policy raw inverse ignores argument) | yes | yes | yes | PASS |
| CP6 (zero reduction donor becomes nonzero fixture control) | yes | yes | yes | PASS |
| CP7 (empty domain gains a coordinate fixture control) | yes | yes | yes | PASS |

7/7 cycles passed.

| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| T6 boundary coordinate reversal (copied numeric) | yes | yes | yes | PASS |
| T6 zero projected output (copied numeric; witnesses intact) | yes | yes | yes | PASS |
| T6 shifted UID (copied metadata; injection retained) | yes | yes | yes | PASS |
| T6 zero present inputs (copied numeric; binding remains Some) | yes | yes | yes | PASS |
| T6 reversed external input (copied numeric) | yes | yes | yes | PASS |
| T6 negated external output (copied numeric) | yes | yes | yes | PASS |
| T6 hidden witness collapse (donor substitution; numeric) | yes | yes | yes | PASS |
| T6 audit reads output not private cell (donor locator; numeric) | yes | yes | yes | PASS |
| T6 lost right-bracket private store (donor store substitution; numeric) | yes | yes | yes | PASS |
| T6 total substituted for strict absence (donor theorem; NOT numeric) | yes | yes | yes | PASS |

10/10 cycles passed.

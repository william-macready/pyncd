| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| S3-M1 execRet is the identity (retirement frees nothing) | yes | yes | yes | PASS |
| S3-M2 execRet leaves the first member's slot (B.tail) | yes | yes | yes | PASS |
| S3-M3 checkRet always true | yes | yes | yes | PASS |
| S3-M4 checkRet drops the live clause | yes | yes | yes | PASS |
| S3-M5 checkRet drops the not-an-output clause | yes | yes | yes | PASS |
| S3-M6 checkReady over Pub instead of Live | yes | yes | yes | PASS |
| S3-M7 SlotView .pub over Pub instead of Live | yes | yes | yes | PASS |
| S3-M8 ReadyOK over Pub instead of Live | yes | yes | yes | PASS |
| S3-M9 readPub over Pub instead of Live (ignores Ret) | yes | yes | yes | PASS |
| S3-M10 RetOK drops the not-an-output conjunct | yes | yes | yes | PASS |

10/10 cycles passed.

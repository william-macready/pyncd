| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| A1-a accumulateBatch last-writer-wins (overwrite, not add) | yes | yes | yes | PASS |
| A1-b accumulateBatch skips the last member (dropLast) | yes | yes | yes | PASS |
| A1-c place collides (slot index / 2) | yes | yes | yes | PASS |
| A1-d Decode zero-fills (getD 0, no Pub/initialised check) | yes | yes | yes | PASS |
| A1-e SlotView maps acc x whenever not Pub (drops Mat guard) | yes | yes | yes | PASS |
| A3b-3 readPub ignores Pub (read view exposes raw memory) | yes | yes | yes | PASS |
| A2-a addAt overwrites the slot instead of adding | yes | yes | yes | PASS |
| A2-b EQUIVALENT (N5): commit values read raw memory, readiness still on readPub | yes | yes | yes | PASS |
| A2-c execPub writes (re-initialises the block) | yes | yes | yes | PASS |
| A2-e EQUIVALENT (N5): non-transactional acc (evaluate, commit, continue per member) | yes | yes | yes | PASS |
| A2-f scan and commit values read raw memory as a fallback | yes | yes | yes | PASS |
| A3a-a EQUIVALENT at checkPlan (N6): checkCov1Complete trivially true | yes | yes | yes | PASS |
| A3a-b checkAnn pub drops checkPubOrder (spec 29.3 condition 4) | yes | yes | yes | PASS |
| A3a-c checkAnn pub drops checkPubMat (N1) | yes | yes | yes | PASS |
| A3a-d checkInit trivially true (N2 initZero freshness) | yes | yes | yes | PASS |
| A3a-e checkSingleton trivially true (slice-1 profile) | yes | yes | yes | PASS |
| A3a-f checkAnn acc drops checkReady (spec 29.3 condition 3, N3) | yes | yes | yes | PASS |
| A3b-1 checkCov2Complete trivially true (spec 29.3 condition 2 covering) | yes | yes | yes | PASS |
| A3b-2 Valid field coverage2 unreachable by name (single-site form of the drop) | yes | yes | yes | PASS |
| A2-d fixture plan materialises only addr 1 (N1 empty fibers) | yes | yes | yes | PASS |

20/20 cycles passed.

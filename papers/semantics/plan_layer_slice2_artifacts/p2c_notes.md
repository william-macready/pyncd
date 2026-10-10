# P2c notes (slice 2, T4: case x class table at fused-command granularity)

Fixtures only (`leanncd/test/Semantics/PlanFusionCheckerTest.lean`, registered in `lakefile.toml`); no production change.
Helpers: `verdictTrio fused donor = (verdictF fused, verdict fused.expand, verdict donor)`; `runPair` =
(fused kind, donor kind, memories equal, fused slots, donor slots). All values observed (`check` throws on mismatch).

## Inventory (verified by rg, not from the notes)
| case | fixture |
|---|---|
| a1 `[acc, pub]` | EXISTS: `fused-reciprocal-acc-pub`, `fused-expand-valid-ap` (PlanFusionTest); no donor-trio equality |
| a2 `[pub, acc]` | EXISTS: `misfused-expand-rejected`, `misfused-slice1-checkSteps-vacuous` (P2a), `fusedcorr-misfused-verdicts` = pubOrder@1 (P2b); no donor trio |
| a3 intra-command read | EXISTS (valid): `fused-scalar-good`, `fusedcorr-scalar-done-decode`; trio on chain donor ADDED (`t4-a3-chainPlan`) |
| a4 read of unpublished accumulator | MISSING -> `t4-a4-chainEarly` |
| a5 re-init after consume | MISSING -> `t4-a5-reinitMid` |
| a6 duplicate occurrence | MISSING -> `t4-a6-dupGroup` |
| a7 overlapping blocks | MISSING -> `t4-a7-pubTwice` |
| a8 `[init, acc]` | EXISTS: `fused-step-success`, `fusedcorr-done-decode` (valid); no donor trio |
| a9 `[init, pub]` | MISSING -> `t4-a9-lateEmptyInit` |
| a10 `[]` | EXISTS: `fused-with-empty-commands`, `empty-step-is-identity`, `invalid-empty-command` |

## New fixtures (8). Row = trio verdict / (fused kind, donor kind, mem equal, fused slots, donor slots)
| name | donor | verdictF = verdict(expand) = verdict(donor) | run |
|---|---|---|---|
| t4-a3-chainPlan | chainPlan | (true, []) | done, done, true, [0,3,4] / [0,3,4] |
| t4-a3split-chainPlan | chainPlan | (true, []) (consumer is a LATER command than fused `acc;pub`) | done, done, true, [0,3,4] |
| t4-a3mis-chainReadFirst | chainReadFirst (acc0,acc1,pub1) | (false, [ready@2]) | stuck, stuck, FALSE, fused [0,0,0] vs donor [0,3,0] |
| t4-a4-chainEarly | chainEarly | (false, [ready@1]) | stuck, stuck, true, [0,0,0] |
| t4-a5-reinitMid | reinitMid | (false, [initFresh@2]) | done, done, true, [0,10,0] (silent wrong value) |
| t4-a6-dupGroup | dupGroup | (false, [cov1Nodup, accFresh@2]) | done, done, true, [0,16,0] |
| t4-a7-pubTwice | pubTwice | (false, [cov2Nodup, pubFresh@3]) | done, done, true, [0,14,0] |
| t4-a9-lateEmptyInit | lateEmptyInit | (true, []) | done, done, true, [0,14,0] |
D15 pair: valid = `t4-a3-chainPlan`; mis-fused (publication AFTER the read in one command) = `t4-a3mis-*`, which fails
`ready@2`, NOT `pubOrder@1` (the P2b `pubOrder@1` fixture is the other mis-fusion: publish before ITS accumulate), so both are kept.
a3mis: a fused stuck command reports the PRE-command memory (D14), the singleton donor keeps acc0's commit: the only
fixture where fused and donor memories differ; kinds still agree.
Fixtures a5/a6/a7 need no ordering inside the command to be wrong: the verdict is the same for any fusing of the donor.

## Mutations (manifest task "T4"; `--check` unfiltered: 14 entries OK; `--task T4`: 3/3 PASS, all `expect` strings seen)
All three mutate Syntax.lean definitions, so each breaks a LIBRARY proof first (Syntax.lean lines 145-169) and no fixture
flips under lake. Proof-free probe (scratch file, not committed, kept at scratchpad/ScratchProbeT4.lean): mutated function
under a new name, fixtures re-evaluated.
| label | library break (expect) | fixture flips under probe |
|---|---|---|
| S2-M12 expand reverses order within each command | Syntax.lean:145:45 Type mismatch | yes: a3 (false,[ready@1,pubOrder@2]) vs true; a3mis (false,[pubOrder@1]) vs ready@2; a4 ready@2 vs ready@1; a5 (true,[]) vs initFresh@2; a9 (false,[pubMat@2,initFresh@3]) vs true; a3split (false,[pubOrder@1]) vs true; a6, a7 unchanged (order-insensitive) |
| S2-M13 expand drops first annotation of each fused command | Syntax.lean:145:45 Type mismatch | yes: every fixture changes (cov1Complete / cov2Complete / pubMat appear), e.g. a3 (false,[cov1Complete,pubOrder@1]) vs true |
| S2-M14 offset := (commands.take pc).length | Syntax.lean:159:52 Tactic `rewrite` failed | yes, ONLY `t4-a3split-chainPlan`: mutated step position gives ("stuck", 2, [0,3,0]) vs shipped ("done", 4, [0,3,4]) |
S2-M14 is not caught by any other fixture: the offset matters only when a READING command follows a fused command (the
read view is `Pub offset`); the first draft of T4 had no such fixture, `t4-a3split` was added after reasoning about this mutant.

## Not done / notes
- a1, a2, a8 have no three-way donor-trio fixture of their own (existing P2a/P2b fixtures pin their verdicts and runs).
- The probe file is outside the repo (scratchpad); the `lakefile.toml` registration of it was reverted before the commit.

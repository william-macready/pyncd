| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| S2-M1 execAnns folds right-to-left | yes | yes | yes | PASS |
| S2-M2 failure reports the partial memory, not the pre-command memory | yes | yes | yes | PASS |
| S2-M3 every annotation reads the pre-command memory | yes | yes | yes | PASS |
| S2-M4 offset off by one (equivalent at fixture level) | yes | yes | yes | PASS |
| S2-M5 checkPlanF is the slice-1 checker on the unexpanded plan | yes | yes | yes | PASS |
| S2-M6 FValid weakened to slice-1 Valid of the fused plan | yes | yes | yes | PASS |
| S2-M7 terminal_adequacy_F drops the FValid hypothesis | yes | yes | yes | PASS |
| S2-M8 terminal_adequacy_F reports the expanded command count | yes | yes | yes | PASS |
| S2-M9 checkPlanF skips the expansion (slice-1 checker minus singleton) | yes | yes | yes | PASS |
| S2-M10 Agree drops the final-memory equality of done runs | yes | yes | yes | PASS |
| S2-M11 Agree drops the failing-occurrence equality | yes | yes | yes | PASS |
| S2-M12 expand reverses annotation order within each command | yes | yes | yes | PASS |
| S2-M13 expand drops the first annotation of each fused command | yes | yes | yes | PASS |
| S2-M14 offset counts commands instead of annotations | yes | yes | yes | PASS |

14/14 cycles passed.

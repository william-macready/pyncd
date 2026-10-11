# Slice 3 (buffer retirement), dispatch A3a notes

Scope: tests only. New `leanncd/test/Semantics/PlanRetireTest.lean` (imports `Semantics.PlanFaultsTest`),
registered in `leanncd/lakefile.toml` after `"Semantics.PlanFaultsTest"`. Nothing under `LeanNCD/` edited
(mutations were applied and restored; `git status --short` was clean of them).

Donor families: `routed chainBody` (`chainPlan`, single non-output tensor, point 1 published then read by
occurrence 1) and `scalarRole false` (`sPlan false`, tensor 1 output, tensor 2 defined non-output).
Retire of an INPUT address is not expressible (`Ann.retire` takes `DefAddr P`, a defined address; inputs
are always live, `live_input`): comment in the module, no row.

Fixture count added: 10 plans, 17 `#eval check` rows, 10 `example ... := by decide` verdicts,
1 theorem (`rtChain_valid`). No `sorry`.

## Row table (all values observed from real runs)

| row (`#eval check` name) | donor | verdict | run outcome | observed value |
|---|---|---|---|---|
| retire-valid-chain | `chainPlan` + `retire p1` after last reader (`rtChain`) | checkPlan true | done | pc 6, slots [0, none, 4] |
| retire-valid-chain-donor (control) | `chainPlan` | true | done | pc 5, [0, 3, 4] |
| retire-valid-scalar | `sPlan false` + `retire t2` last (`rtScalar`) | true | done | pc 6, [7, 2, none] |
| retire-valid-scalar-decode | `rtScalar` vs `sPlan false` | - | - | decode `some 2` both (output still decodes) |
| retire-read-after | `rtChain` with retire before occ1 (`rtReadAfter`) | false | stuck | pc 4, [0, none, 0] |
| retire-neighbour-other-address | retire p0 (unread) instead (`rtNeighbour`) | true | done | pc 6, [none, 3, 4] |
| retire-output | `rtScalar` retiring tensor 1 (`rtOutput`) | false | done | pc 6, [7, none, 3]; decode `none` |
| retire-unpublished | `sPlan false` with `retire t2` before `pub t2` (`rtUnpub`) | false | stuck | pc 5, [7, 2, none] |
| retire-fused-after-read | `[acc occ1, retire p1]` (`rtFusedOk`) | checkPlanF true | done | pc 5, [0, none, 4] |
| retire-fused-before-read | `[retire p1, acc occ1]` (`rtFusedBad`) | checkPlanF false | stuck | pc 3, [0, 3, 0] (pre-command memory) |
| retire-twice | second `retire p1` command (`rtTwice`) | false | done | pc 7, [0, none, 4] |
| retire-dup-in-block | `retire [p1, p1]` (`rtDupBlock`) | true | done | pc 6, [0, none, 4] |
| retire-fault-none | `rtChain`, no faults | - | run:done | pc 6, [0, none, 4] (= row 1) |
| retire-fault-at-retire | `rtChain`, fault at position 4 | - | error allocFail | pc 4, [0, 3, 4] (pre-command) |
| retire-fault-after-retire | `rtChain`, fault at position 5 | - | error kernelFault | pc 5, [0, none, 4] |
| retire-fault-fused-at-retire | `rtFusedOk`, fault at position 4 (the retire) | - | error allocFail | pc 3, [0, 3, 0] (whole command rolled back) |
| retire-fault-fused-none | `rtFusedOk`, no faults | - | run:done | pc 5, [0, none, 4] |

## Differences from the spec / brief predictions

- Row 4 (unpublished accumulator): predicted `done`; OBSERVED `stuck` at pc 5. `execRet` does clear the
  live accumulator (slot `none`), and the later `pub t2` then finds no value to publish, so it is `stuck`
  at the pub, not at the retire. checkPlan is false as predicted. (Only occurs because the donor
  publishes the retired address afterwards; a plan that never publishes it would end `done`.)
- Row 6 (retire twice): as predicted. checkPlan false (diagnostic half), run `done` (idempotent clear,
  same final memory as one retire). Extra row: duplicate within ONE retire block is accepted by
  checkPlan (spec 3.3 "no duplicate check inside a retire block"), observed true.
- Row 3 (retire of an output): run is `done` (not stuck), final output slot `none`, so `Decode` over it is
  `none`: the output clause is genuinely terminal-role, the static check is the only guard before Decode.
- Row 7: faults at the retire position leave the retired slot intact (pre-command memory), so those rows do
  NOT distinguish a no-op `execRet` (see mutation (a)); `retire-fault-after-retire` and the `-none` rows do.

## Hand mutation check (not committed; files restored with `git checkout --` and `git status --short` clean)

Build target `Semantics.PlanRetireTest`. Every mutant first breaks library PROOFS (so lake never reaches the
test module, same as the d7 manifest note "caught at the proofs"); to learn which ROWS fail, the broken
proofs were temporarily replaced by `sorry` (mutated files only, restored). Proof breaks listed per mutant.

(a) `execRet` = identity (`Step.lean:134-135` body replaced by `M`). Proof breaks: `Simulation.lean:334`
    (`execRet_not_mem`), `:344` (`execRet_mem`), both a failing `change`. Failing rows (12):
    retire-valid-chain, retire-valid-scalar, retire-read-after, retire-neighbour-other-address,
    retire-output, retire-unpublished, retire-fused-after-read, retire-twice, retire-dup-in-block,
    retire-fault-none, retire-fault-after-retire, retire-fault-fused-none.
    Surviving: retire-valid-chain-donor, retire-valid-scalar-decode, retire-fused-before-read,
    retire-fault-at-retire, retire-fault-fused-at-retire (none observes a cleared slot). No `example` fails
    (they are verdict-only).
(b) `checkRet` always true (`... || true`, keeping `π`; `Validity.lean:132`). Proof breaks:
    `Validity.lean:178` (`checkRet_sound`), `:346` (`checkRet_complete`), type mismatch. Failing rows (3, each
    with its `example` too): retire-output (and example at line 95), retire-unpublished (:110),
    retire-twice (:147). Retire-read-after and the fused rows survive (the reader's ReadyOK still rejects).
(c) `checkReady` over `Pub` (`Validity.lean:116`). Proof breaks: `Validity.lean:185`
    (`checkAnn_acc_sound`), `:352` (`checkAnn_acc_complete`). Failing rows (2, each with its `example`):
    retire-read-after (example line 70), retire-fused-before-read (:128). The runs of both rows are unchanged
    (the run's `readPub` still uses `Live`), only the verdict flips to true.

Seed for A3b: the manifest `expect` strings can use the first-failing proof line above for the build break
and these row names for the test-level kills. Line numbers shift with any edit to the mutated files.

## Builds
- Module: `bash leanncd/scripts/lake-build.sh <wt>/leanncd Semantics.PlanRetireTest` -> `Build completed
  successfully (2982 jobs).` (17 rows printed; the only `error` text is the existing PlanFaultsTest row name).
- Default targets: `bash leanncd/scripts/lake-build.sh <wt>/leanncd` -> `Build completed successfully
  (8793 jobs).` (8792 + the new module); no `^error` line.

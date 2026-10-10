# Plan-layer mutation manifest: run against the shipped tree

Manifest: `papers/semantics/plan_layer_mutations_post.json` (20 cycles).
Tree: the shipped T1..T5 tree (main 0bf02e47, commit f14415ed), built in the detached scratch worktree
`pyncd.worktrees/plan-layer-emit`. Runner: `leanncd/scripts/mutation-manifest.sh` from that tree.

Runs, 2026-10-10:
1. Full run: 18/20. A1-d and A2-d failed on `expect` only. Both mutants broke the build, and both
   restored builds were green and byte-identical.
2. Rerun of A1-d and A2-d after the `expect` fixes: 2/2.
3. Final full run: **20/20 cycles passed** (exit 0).

The scratch worktree's `git status --short` was empty after every run.

## EQUIVALENT cycles

A2-b, A2-e and A3a-a are labelled EQUIVALENT. They are semantically equivalent: no fixture
distinguishes them (notes N5 and N6). They are **not** build-equivalent. Each one breaks a proof
script, as the A3b consolidated table records. The manifest therefore encodes them as ordinary
cycles: the build must fail, with an `expect` naming the broken proof site. The runner has no "expected to
build" mode, and none is needed. All three failed at the recorded sites, as expected.

## Per cycle

"Observed" is the `error:` line in the mutated build log that the `expect` strings match. Line numbers
refer to the shipped tree.

| Cycle | Mutant | Result | Observed failure (`expect` matched) | Changed? |
|---|---|---|---|---|
| A1-a | `accumulateBatch` fold ignores the accumulator (`fun _ x => consume P c …`) | failed as expected | `Batch.lean:80:19: Type mismatch` (also `:88:4`, `:99:4`, `:129:4`) | no |
| A1-b | `accumulateBatch` over `G.dropLast` | failed as expected | `Batch.lean:80:19`, `:88:4`, `:99:4`, `:129:4` | no |
| A1-c | `place` index `/ 2` | failed as expected | `Memory.lean:28:91: Application type mismatch` (`place_injective`); also `:240:21` | no |
| A1-d | `Decode` zero-fills (`getD 0`, no check) | failed as expected | `Memory.lean:104:2: Tactic `split_ifs` failed: no if-then-else conditions to split` (`decode_some`) | **yes**: old `expect` `"split_ifs failed"` never occurs verbatim (Lean prints ``Tactic `split_ifs` failed``); replaced by the observed position and text |
| A1-e | `SlotView` drops the `Mat` guard | failed as expected | `Memory.lean:241:17: unsolved goals` (also `:59:28`, `:67:33` invalid projection) | no |
| A3b-3 | `readPub` ignores `Pub` (`∨ True`) | failed as expected | `Memory.lean:253:23: unsolved goals` (`readPub_eq`); also `:254:39` | no |
| A2-a | `addAt` overwrites | failed as expected | `Simulation.lean:297:18: Application type mismatch` | no |
| A2-b | EQUIVALENT: commit values read raw memory | failed as expected (proof-only) | `Simulation.lean:461:6: Tactic `rewrite` failed` | no |
| A2-c | `execPub` re-initialises | failed as expected | `Simulation.lean:512:4: Tactic `rfl` failed` | no |
| A2-e | EQUIVALENT: non-transactional acc | failed as expected (proof-only) | `Simulation.lean:451:2` and `:577:4: Tactic `split` failed` | no |
| A2-f | scan and commit read raw memory as a fallback | failed as expected | `Simulation.lean:463:92` unsolved goals, `:490:4` rfl, `:583:52` type mismatch | no |
| A3a-a | EQUIVALENT at checkPlan: `checkCov1Complete` trivial | failed as expected (proof-only) | `Validity.lean:193:19: Type mismatch` | no |
| A3a-b | `checkAnn .pub` drops `checkPubOrder` | failed as expected | `Validity.lean:179:10: Unknown identifier `hn`` | no |
| A3a-c | `checkAnn .pub` drops `checkPubMat` | failed as expected | `Validity.lean:179:10` unknown `hn`; `:174:58: unsolved goals` | no |
| A3a-d | `checkInit` trivial | failed as expected | `Validity.lean:163:9: Tactic `rcases` failed` | no |
| A3a-e | `checkSingleton` trivial | failed as expected | `Validity.lean:192:50: Application type mismatch` | no |
| A3a-f | `checkAnn .acc` drops `checkReady` | failed as expected | `Validity.lean:171:10` unknown `hn`/`hc`; `:167:75: unsolved goals` | no |
| A3b-1 | `checkCov2Complete` trivial | failed as expected | `Validity.lean:193:60: Type mismatch` | no |
| A3b-2 | `Valid` field renamed `coverage2'` | failed as expected | `Correctness.lean:33:37` and `:55:30: Invalid field `coverage2`` | no |
| A2-d | fixture plan initZero only `[addr 1]` | failed as expected | `PlanStepTest.lean:31:0: step-tagged-run: expected ("done", 3, none, [some 0, some 14, some 0]), got ("stuck", 2, none, [none, some 14, none])` (also `:33:0`, `:45:0`) | **yes**: old `expect` named `PlanSimulationTest.lean` / `plan.Mat 2 (addr 0)` (the `ok2` decide). `PlanSimulationTest` imports `PlanStepTest`, so the build stops at the `PlanStepTest` fixture first and `ok2` is never elaborated. Replaced by the observed fixture failure, which the A2 notes also record (`step-tagged-run` stuck at 2). |

## Findings

- No mutant compiled when the notes say it should fail. No cycle shows a missing fixture.
- **A1-d mutant is ill-typed in the shipped tree.** In addition to the intended `decode_some` failure,
  the mutated build reports `Memory.lean:97:52: failed to synthesize instance of type class`. The
  shipped `Decode` is generic over `K` and comes before the `AddCommMonoid` section variable
  (`Memory.lean:111`), so `0` has no instance at an output sort. Lean elaborates the `0` as an error
  term, and `decode_some` still fails for the intended reason (no `if` to split). Still, the build would break even
  without that proof. The zero-fill mutant cannot be written type-correctly at the shipped
  `Decode`. The prototype's decode fixture witness (`some [0,0,0]`) is not reproduced by this cycle. The mutant is kept
  as is, because any type-correct "fill" would be a different mutant.
- A2-d: the semantic `ok2` decide witness named in the notes is masked by the import chain. The
  fixture-level witness (`step-tagged-run`, `step-tagged-decode-vs-run`, `step-tagged-trace`) is
  observed instead.

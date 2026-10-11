# Slice 3 (buffer retirement) mutation results

Manifest: `papers/semantics/plan_layer_slice3_mutations_post.json` (10 cycles, task tag `S3`, each with
`expect` strings copied from the observed failing build). Run (against HEAD `3f09c105` code, no production
edits in this dispatch):

    bash leanncd/scripts/mutation-manifest.sh --check <leanncd> <manifest>
    -> manifest OK: 10 entries, 10 selected, every old-string unique
    bash leanncd/scripts/mutation-manifest.sh --out <this table> <leanncd> <manifest>
    -> 10/10 cycles passed.

Targets of every cycle: the mutated module plus `Semantics.PlanRetireTest`. Restored rebuild each time:
`Build completed successfully (2982 jobs).` After the run `git status --short` shows no modified tracked file.

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

## Where each mutant dies (observed `error:` lines of the mutated build)

| Mutation | Killed by | Failing locations |
|---|---|---|
| S3-M1, S3-M2 | library proofs | `Simulation.lean:334:4` (`execRet_not_mem`), `:344:4` (`execRet_mem`): `'change' tactic failed` |
| S3-M3, S3-M5, S3-M10 | library proofs | `Validity.lean:178:2` (`checkRet_sound`), `:346:2` (`checkRet_complete`): `Type mismatch` |
| S3-M4 | library proofs | same two lines as M3. (First attempt dropped `π` from the body and died on `Invalid field notation` at `:138/:175/:344`, a type-level artefact; the committed mutant keeps `π.Live` via `\|\| true`.) |
| S3-M6, S3-M8 | library proofs | `Validity.lean:185:47` (`checkAnn_acc_sound`), `:352:73` (`checkAnn_acc_complete`): `Application type mismatch` |
| S3-M7 | library proofs | `Memory.lean:59:24`, `:67:29` (`Invalid projection`), `:264:21` (`readPub_eq`, `unsolved goals`) |
| S3-M9 | library proof | `Memory.lean:263:6` (`readPub_eq`): `Tactic rewrite failed` |

## Findings

- Killed 10, equivalent 0. Every mutant is killed at a library proof, so lake never reaches
  `Semantics.PlanRetireTest` in the mutated build (same shape as the D7 manifest: "caught at the proofs").
- The candidate equivalent mutant, `readPub` ignoring `Ret` (S3-M9), is NOT equivalent: `readPub_eq` was
  weakened to a pointwise statement on `Live` and its `rw [if_pos ha]` fails when the guard is `Pub`.
- Fixture-row kills are not exercised by this manifest. They were observed by hand in A3a with the broken
  proofs temporarily `sorry`'d (see `a3a_notes.md`): execRet identity (M1) fails 12 rows, checkRet always
  true (M3) fails retire-output, retire-unpublished, retire-twice (each with its `example`), checkReady over
  Pub (M6) fails retire-read-after and retire-fused-before-read (each with its `example`).
  M2, M4, M5, M7, M8, M9, M10 were not row-level probed (only the proof-level kill is recorded).

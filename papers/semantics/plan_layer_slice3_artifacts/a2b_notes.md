# Slice 3 (buffer retirement), dispatch A2b notes

Scope: `Plan/Fusion.lean`, `Plan/FusionCorrectness.lean`, `Plan/Faults.lean` (under
`leanncd/LeanNCD/Semantics/Plan/`), then the whole `LeanNCD` library and a survey of `test/`.
No theorem statement changed. No `sorry`, no new axiom. Nothing under `test/`, `experiments/`,
`spikes/` was edited.

## Per module

### Fusion.lean (commit "Fusion R_transport over Ret/Live and the dead/retPub fields")
- `R_transport`: added `hret : ∀ a, π.Ret pc a ↔ π'.Ret pc' a` (`simp [Ret, retList, h]`) and
  `hlive : ∀ a, π.Live pc a ↔ π'.Live pc' a` (`simp only [Live, hpub, hret]`); `hsv` now
  `simp [SlotView, hpub, hmat, hlive]`; the anonymous constructor gets the two new fields
  `dead` (from `hR.dead`, via `hpub`/`hlive`) and `retPub` (from `hR.retPub`, via `hret`/`hpub`).
  Statement unchanged.
- Nothing else in the file broke: `execAnns_R`, `execAnns_failed`, `step_R_command`,
  `step_failed_command`, `stepCommand_not_stuck`, `runFrom_agree` compiled as they were (the retire
  arms arrive through `AnnOK` / `step_R` / `step_failed` of A1).
- `FValid`/`checkPlanF` live in FusionCorrectness (`FValid := π.expand.Valid`); unchanged.

### FusionCorrectness.lean (commit "FusionCorrectness decode_prefix_congr and terminal_adequacy_F over Live")
- `decode_prefix_congr`: the `readPub` equality now goes through
  `hp : π.Live pc a ↔ π'.Live pc' a` (`simp [Live, Pub, Ret, pubList, retList, h]`), `by_cases` on `Live`.
- `terminal_adequacy_F`: `outs` is now `∀ t p, π.Live π.commands.length ⟨t.val, p⟩`, obtained from
  `live_output_of_valid hv t p` (about `π.expand`, since `FValid` is `π.expand.Valid`), transported to `π`
  by `simpa [Live, Pub, Ret, pubList, retList, hp]` with `hp := prefixAnn_done ...` (already in scope).
  The previous `(hR.published _).mp (complete.2 _)` is no longer used there.
- `checkPlanF_sound/complete/iff`, `runFrom_R_F`, `runPlan_R_F`, `runPlan_agree`, `done_correct_F`,
  `failed_correct_F`, `runPlan_not_stuck_F`, `done_iff_model_F`...: unchanged and compile.

### Faults.lean
- No change needed. `rg -n "Pub|readPub|\.initZero|cases a with|decode_of_R"` finds nothing in the file;
  it only goes through `step_R`/`step_failed`/`runFrom_R`/`terminal_adequacy` family. All of `runFromE_*`,
  `done_correct_E`, `failed_correct_E`, `runPlanE_not_stuck`, `_FE` corollaries, `ErrorFreeRun`,
  `error_despite_model` compile with statements unchanged. No commit.

## Deviations
None from the brief. No statement changed. The `ReadyOK`/`checkReady` change needed nothing in Fusion*
(fused validity is `Valid` of `π.expand`).

## Other `LeanNCD` modules
`rg "\.initZero|cases a with" LeanNCD` outside the Plan files already done: none needed editing; the
full library compiled with no further edits.

## Builds (all via `leanncd/scripts/lake-build.sh <wt>/leanncd [target]`, output to scratchpad files)
- `LeanNCD.Semantics.Plan.Fusion`: first run failed (R_transport, `hsv` unsolved + 6 of 8 R fields);
  after fix `Build completed successfully (2966 jobs).`
- `LeanNCD.Semantics.Plan.FusionCorrectness`: first run 3 errors (two `rw` on `Pub` in
  `decode_prefix_congr`, `outs` type in `terminal_adequacy_F`); after fix
  `Build completed successfully (2968 jobs).`
- `LeanNCD.Semantics.Plan.Faults`: first run `Build completed successfully (2969 jobs).`
- `LeanNCD` (whole library): `Build completed successfully (8598 jobs).`
- Default targets, no argument (LeanNCD + Tests + JaxExperiment + SemanticCoreSpike per
  `lakefile.toml`): `Build completed successfully (8792 jobs).` No `^error` line in the log. The
  only `declaration uses sorry` warnings are the four pre-existing ones (Base/St.lean:171,
  Base/Br.lean:305, Core/Weave.lean:29, Instances/StBr.lean:13; see `SORRY_INVENTORY.md`).
  `rg sorry` over the three edited modules: no match.

## For A3: test modules
The whole default build, which includes the `Tests` library, compiles with the test sources untouched,
and the test modules were rebuilt (e.g. `Built Semantics.PlanFixtures`, `Built Semantics.PlanMultiSortTest`
... `PlanFusionCheckerTest` all present in the log), so the existing fixture rows still run green
(no failures). No test module fails; none needs fixing for compilation.

Plan-layer tests that mention the changed surface (A3 should be aware when adding retire fixtures):
- No test pattern-matches (`match`/`cases`) on `Ann`, so the new constructor causes no
  non-exhaustive-match failure. Tests only construct annotations: `PlanFixtures.lean` (`.initZero`,
  `.acc`, `.pub` at line 48), `PlanFusionTest`, `PlanFusionCheckerTest`, `PlanValidityTest`,
  `PlanStepTest`, `PlanSimulationTest`, `PlanMemoryTest`, `PlanBatchTest`, `PlanMultiSortTest`,
  `PlanCorrectnessTest`, `PlanFusionCorrectnessTest`, `PlanFaultsTest`.
- Use `SlotView` (now `.pub` over `Live`): `PlanMemoryTest.lean` lines 24, 27.
- Use `R_start` (now has `dead`, `retPub`): `PlanMemoryTest.lean` 31, 34; `PlanSimulationTest.lean` 52, 86.
- No test uses `readPub_eq`, `decode_of_R`, `ReadyOK`, `pubSlot`, `accSlot`, `R_transport` or the
  `R` fields directly (`rg` over `test/`; the only hit outside the above is an unrelated
  "retained-axis" string in `test/Eval/Plan/DifferentialTest.lean:2073`).
- Tests calling `readPub` (now guarded by `Live`; values on non-retired fixtures unchanged):
  `PlanCorrectnessTest.lean:17`, `PlanMemoryTest.lean:45`, `PlanStepTest.lean:65`.

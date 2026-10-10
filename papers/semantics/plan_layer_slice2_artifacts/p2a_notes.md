# P2a notes (slice 2: T1 in-place stepCommand, T2 execAnns_not_stuck + fixtures + mutations)

## Signatures changed (leanncd/LeanNCD/Semantics/Plan)
- Syntax.lean: ADDED `expand`, `offset`, `flatten_map_single`, `expand_ann`, `expand_prefixAnn`,
  `expand_commands_getElem?`, `ann_eq_append`, `prefixAnn_eq_expand`, `drop_flatten`,
  `ann_getElem?_offset` (moved from Fusion.lean; `expand_singleton` stays in Fusion.lean: needs Validity).
- Step.lean: `stepCommand (pc) (M) (cmd : Command P) : StepResult P := π.expand.execAnns ops (π.offset pc) M cmd`
  (was `| [a] => execAnn | _ => .stuck`). ADDED `execAnns`, `execAnn_prefix`, `stepCommand_single`
  (`π.stepCommand ops pc M [a] = π.execAnn ops pc M a`, any plan). `stepPlan`, `runFrom`, `runPlan`
  unchanged in text; `runFrom` already reports the pre-command memory, so no `runFromF` exists.
- Simulation.lean (the ONLY slice-1 statements changed): `step_failed` and `step_failed_no_model` now take
  `{a : Ann P}`, `hcmd : π.commands[pc]? = some [a]`, `ok : ∀ G, [a] = [.acc G] → …` instead of
  `{cmd}`, `some cmd`, `cmd = [.acc G]`. Forced: a fused command can `semFail` after earlier annotations.
  Callers (`run_R`, Fusion `execAnns_failed`) needed no edit. `step_R` statement unchanged (proof gained
  `simp only [stepCommand_single] at h`); `step_not_stuck` statement unchanged (proof uses `stepCommand_single`).
- Fusion.lean: `stepCommandF`, `runFromF`, `runPlanF`, `execAnn_prefix`, `stepCommandF_single` removed
  (`rg -n stepCommandF` finds none); `step_R_command`/`step_failed_command` now speak of `stepCommand`.
- Run.lean ADDED `execAnns_not_stuck`; Fusion.lean ADDED `stepCommand_not_stuck`.
- lakefile.toml: `"Semantics.PlanFusionTest"` added to the Tests globs. `LeanNCD.Semantics.Plan.Fusion` is not
  imported by `LeanNCD.lean`/`Plan.lean`, so it is built only through a test that imports it
  (PlanFusionTest no longer does; add `import LeanNCD.Semantics.Plan.Fusion` to Plan.lean in the real plan, or keep
  the import in the test). DECISION NEEDED by the plan writer.

## Slice-1 fixtures: three outcomes change (unavoidable: they asserted "fused/empty is stuck")
- PlanStepTest `invalid-fused` -> `fused-runs-in-slice-2`: ("stuck",0,none,[none,none,none]) -> ("done",2,none,[0,14,0]).
- PlanStepTest `step-empty-command-stuck` -> `step-empty-command-noop`: (("stuck",[]),("stuck",1,..)) ->
  (("ok",[0,0,0]),("done",4,none,[0,14,0])).
- PlanValidityTest `invalid-empty-command`: run half ("stuck",1,..) -> ("done",4,none,[0,14,0]); verdict
  (false,["singleton"]) unchanged. All other Plan fixtures (9 Plan test modules) print unchanged values.
Build: `Semantics.PlanFixtures … PlanCorrectnessTest PlanFusionTest` completed successfully (2979 jobs).

## execAnns_not_stuck (Run.lean, status: PROVED, no sorry)
`theorem execAnns_not_stuck (hv : π.Valid) : ∀ (anns : List (Ann P)) (n : Nat) (M : Memory K σ) (c : P.Running),
  π.R ops η n M c → π.refState ops η n = some c → (∀ j a, anns[j]? = some a → π.commands[n + j]? = some [a]) →
  π.execAnns ops n M anns ≠ .stuck`
Fusion.lean: `stepCommand_not_stuck (hv : π.expand.Valid) (hR : π.R ops η pc M c) (hc : π.refState ops η pc = some c)
(hcmd : π.commands[pc]? = some cmd) : π.stepCommand ops pc M cmd ≠ .stuck`. `[]` is covered (`execAnns [] = .ok`).
D16 (empty command): `step_R_command` covers `[]` (cmd.length = 0, vacuous obligations, refState unchanged).

## T2 fixtures (all values observed; PlanFusionTest.lean)
fused-step-success ("ok",[0,14,0]); fused-vs-expand-reciprocal rows ([3/4,0,0],[3/4,0,0]) expansion pc 3;
fused-vs-expand-scalar ([7,2,3],[7,2,3]); fused-with-empty-commands ("done",5,none,[0,14,0]);
empty-step-is-identity ("ok",[0,0,0]) from initMem; fused-two-acc-different-tensors ([7,2,3],3) and `-bad`
([7,0,0],1) (rollback). Inherited from P1 (now `runPlan`): fused-reciprocal-all ("done",1,..,[3/4,0,0]),
fused-failure-after ("failed",0,some(1,0),[none×3]), fused-failure-after-ap ("failed",1,..,[0,0,0]),
fused-scalar-good ("done",2,..,[7,2,3]) (intra-command read), fused-scalar-bad ("failed",1,some 2,[7,0,0]).

## Mutations (papers/semantics/plan_layer_slice2_mutations_post.json)
| label | task | observed expect |
|---|---|---|
| S2-M1 fold right-to-left | T1 | Step.lean:171:2 "No goals to be solved" (stepCommand_single) |
| S2-M2 failure reports partial memory | T2 | Run.lean:177:36 "Application type mismatch" (run_R) |
| S2-M3 pre-command memory per annotation | T1 | Step.lean:171:33 "Tactic `rfl` failed" |
| S2-M4 offset + 1 | T1 | Syntax.lean:159:52 "Tactic `rewrite` failed" |
UNRESOLVED: every mutant is killed by a PROOF in the library, upstream of the fixtures, so no fixture is shown to
flip (lake cannot build the test past a broken library). The fixtures meant to distinguish them are
fused-scalar-good (M1, M3), fused-scalar-bad / fused-two-acc-bad (M2), and fused-scalar-good (M4, may be
equivalent on fixtures since only readPub positions shift). Not verified; needs a proof-free probe.

# P2b notes (slice 2, T3: run theorems for fused plans)

## Design (chosen: RUN BRIDGE, not a direct lift of run_R)
- Bridge is short (one induction, ~45 lines): `runFrom_agree` relates `π.runFrom pc` to `π.expand.runFrom (offset pc)`
  over `l.flatten.map single`, via `runFrom_append_anns` (execAnns on singletons) and `offset (pc+1) = offset pc + cmd.length`.
  `PlanOutcome.Agree`: done = same final memory, failed = same occurrence, stuck = stuck (pc and failure memory NOT compared).
- Lift of the run lemma = `runPlan_R_F` (from `runPlan_R` on `π.expand` + Agree + `R_transport`/`refState_prefix_congr`
  along `prefixAnn π n_cmds = prefixAnn π.expand n_ann`). The six Correctness theorems then keep their proofs verbatim
  (only `terminal_adequacy_F` differs: `complete_of_refState` on the expansion, transported).
- Module split: bridge in Fusion.lean (needs only Step/Syntax; Fusion already imports Run). Lifts in NEW
  `Plan/FusionCorrectness.lean` (imports Fusion + Correctness): zero edits to Correctness.lean/Run.lean, no import cycle.
- `done m M'`: for fused π, `m = π.commands.length` (COMMANDS). The pc is never compared between π and π.expand
  (it differs: 1 vs 3 in the fixtures). Theorem 31.3 (b) compares fails / no-model only (D5; a failed fused command reports
  the PRE-command memory, D14, so snapshots differ from the singleton run).
- Not stated: a mid-run `run_R_F` from an arbitrary pc (no consumer); `runFrom_agree` gives the bridge for it.

## Statements (leanncd/LeanNCD/Semantics/Plan/{Fusion,FusionCorrectness}.lean)
```
def PlanOutcome.Agree : PlanOutcome P → PlanOutcome P → Prop            -- Fusion.lean
theorem runFrom_done_pc (π') : ∀ l pc M M' m, π'.runFrom ops pc M l = .done m M' → m = pc + l.length
theorem runFrom_append_anns (π') : ∀ anns n M ys, match π'.execAnns ops n M anns with … (runFrom of anns.map single ++ ys)
theorem runFrom_agree : ∀ l pc M, π.commands.drop pc = l →
    (π.runFrom ops pc M l).Agree (π.expand.runFrom ops (π.offset pc) M (l.flatten.map fun a => [a]))
theorem runPlan_agree (M) : (π.runPlan ops M).Agree (π.expand.runPlan ops M)
abbrev FValid (π : P.Plan) : Prop := π.expand.Valid                      -- FusionCorrectness.lean
def checkPlanF (π : P.Plan) : Bool := π.expand.checkPlan
theorem checkPlanF_sound (h : π.checkPlanF = true) : π.FValid := checkPlan_sound π.expand h
theorem prefixAnn_done (hm : m = π.commands.length) (hn : n = π.expand.commands.length) : π.prefixAnn m = π.expand.prefixAnn n
theorem decode_prefix_congr (h : π.prefixAnn pc = π'.prefixAnn pc') (M) : π.Decode pc M = π'.Decode pc' M
theorem runPlan_R_F (hv : π.FValid) (η : P.Input) : (∃ M' c', runPlan = .done π.commands.length M' ∧ refState π commands.length = some c'
    ∧ R π commands.length M' c' ∧ ∃ events, Execution …) ∨ (∃ o pc' M' c' events, runPlan = .failed o pc' M' ∧ Execution … (.failed o.1 o.2 c'))
theorem runPlan_not_stuck_F (hv : π.FValid) η pc M : π.runPlan ops (Start η) ≠ .stuck pc M
theorem terminal_adequacy_F (hv : π.FValid) η (hrun : π.runPlan ops (Start η) = .done m M') :
    m = π.commands.length ∧ ∃ c, π.refState ops η m = some c ∧ π.R ops η m M' c ∧ ∃ complete : P.Complete c,
      π.Decode m M' = some (P.outputProjection (P.finalStore c complete))
theorem done_correct_F / failed_correct_F / done_or_failed_F / done_of_model_F / done_iff_model_F   -- same shapes as slice 1, hv : π.FValid
```
Axioms (`#print axioms`, build log): every theorem above, incl. checkPlanF_sound, runPlan_agree, runPlan_R_F,
terminal_adequacy_F, done_*_F, failed_correct_F, and the fixture theorems = [propext, Classical.choice, Quot.sound]. No sorry.

## Reachability
Plan.lean now imports `Plan.Fusion` and `Plan.FusionCorrectness`; chain: LeanNCD.lean -> Semantics.Plan -> FusionCorrectness
-> {Fusion -> Run -> Validity …, Correctness}. lakefile Tests globs: + `Semantics.PlanFusionCorrectnessTest`.
(The `LeanNCD` aggregator build result is in the report.)

## Fixtures (test/Semantics/PlanFusionCorrectnessTest.lean; `check` throws on mismatch, all values observed)
| name | observed |
|---|---|
| fusedcorr-done-decode | verdictF fused (true,[]); ("done",2,none,[0,14,0]); fused Decode 2 = some [0,14,0] = plan Decode 3 |
| fusedcorr-scalar-done-decode | (true, some 2, ("complete", some 2)) |
| fusedcorr-failed-no-model | (true, ("failed",1,some 2,[7,0,0]), ("failed", some 2)); theorem scalar_bad_no_model_F |
| fusedcorr-misfused-verdicts | slice-1 verdict (false,["singleton"]); verdictF (false,["pubOrder@1"]) |
| fusedcorr-missing-publication | (false,["cov2Complete"]); ("done",2,..,[0,14,0]); Decode none (hypothesis necessity) |
| fusedcorr-valid-agrees-with-expansion | Fused/AP/`fused`: (true,("done","done",1,3,true)), (true,(..,2,3,true)), (true,(..,2,3,true)) |
| fusedcorr-failed-agrees-on-occurrence | (2,2,true) |
Props: fused_fvalid, fused_model_unique, fused_has_model, `Agree` rfl example, two NEGATIVE Agree examples (different memory,
different occurrence: pin that `Agree` is not vacuous).

## Mutations (manifest entries, task "T3"; `--check` unfiltered: 11 entries OK; `--task T3`: 7/7 PASS)
Every mutant breaks a LIBRARY proof (second column), so each also has a proof-free probe (scratch file, not committed,
kept at scratchpad/ScratchProbeT3.lean) re-evaluating the fixture with the mutated function under a new name.
| label | observed expect | fixture would flip | probe observation |
|---|---|---|---|
| S2-M5 checkPlanF := π.checkPlan | FusionCorrectness.lean:32:90 Application type mismatch | yes | done-decode: (false,[]) vs true; valid-agrees: (false,false,false) |
| S2-M6 FValid := π.Valid | FusionCorrectness.lean:32:65 Type mismatch | yes | `fused.Valid := checkPlan_sound (by decide)`: decide proved `fused.checkPlan = true` is false |
| S2-M7 terminal_adequacy_F drops hv | FusionCorrectness.lean:107:25 Unknown identifier `hv` | yes | claim "done => Decode isSome" on missing-publication: observed false |
| S2-M8 m = expand.commands.length | FusionCorrectness.lean:117:12 Application type mismatch | yes | finalPc fusedRun = 2, expand length 3 |
| S2-M9 checkPlanF = slice-1 minus singleton | FusionCorrectness.lean:33:90 Application type mismatch | yes | misfused verdict (true,..) vs (false,..): checkSteps vacuous |
| S2-M10 Agree done drops memory eq | FusionCorrectness.lean:75:28 Type mismatch | yes (negative example) | `¬ Agree10 …` no longer typechecks (`Agree10 = True`) |
| S2-M11 Agree failed drops occurrence eq | Plan/Fusion.lean:241:6 Type mismatch | yes (negative example) | same, for the failing occurrence |
M10/M11 are NOT flipped by the value fixtures (a weaker relation does not change any eval); they flip only through the
negative `Agree` examples added for this purpose.

## Unresolved
- mid-run `run_R_F` from an arbitrary pc not stated (derivable from `runFrom_agree` + `run_R` at `offset pc`).
- Plan docs/AGENTS.md for Plan/ not updated (FusionCorrectness row, `Plan.lean` import) — left to the plan writer.
- The manifest was rewritten by json.dump: P2a's four entries are unchanged in content but reformatted (multi-line arrays).

# Whole-branch spec-Lean fidelity review: Plan slice 2 (fusion)

Scope: docs sweep bc888183 (spec Part V "As formalized" paragraphs + proof-status rows, path doc 4.9,
`Semantics/Plan/AGENTS.md`) against code 187e9d15..003080b2. Read-only; findings appended as found.

## WF1 (Important): path doc says a mis-fused plan "passes `checkPlan`" and runs "with a wrong value"

- Location: `papers/semantics/lean_executable_semantics_path.md`, 4.9 "Fused commands (slice 2)":
  "The slice-1 `checkSteps` is vacuous on a fused command, so a mis-fused plan passes `checkPlan` and runs
  to `done` with a wrong value (`misfused-run-undetected`); `checkPlanF` rejects it."
- Claim vs code, two false parts:
  1. `checkPlan` = `checkSingleton && ... && checkSteps` (`Validity.lean:137-139`), and `checkSingleton`
     (`Validity.lean:91`) rejects every non-singleton command. A mis-fused plan therefore FAILS `checkPlan`;
     only the `checkSteps` component is vacuous. The fixture comment says exactly this
     (`PlanFusionTest.lean:67`: "only checkSingleton rejects; checkSteps is VACUOUSLY true"), and
     `misfused-slice1-checkSteps-vacuous` checks `checkSteps`, not `checkPlan`.
  2. `misfused-run-undetected` (`PlanFusionTest.lean:73-75`) expects `("done", 1, none, [3/4, 0, 0])`, the
     same (correct) value as `fused-reciprocal-all` (1/2 + 1/4); the comment says "same value, `done`".
     The point is that the run does not detect the invalid fusion, not that it computes a wrong value.
- Suggested fix: "The slice-1 `checkSteps` is vacuous on a fused command (`checkPlan` rejects a fused plan
  only through `checkSingleton`), and the run does not detect a mis-fused plan: `misfused-run-undetected`
  runs to `done`; `checkPlanF` rejects it (`misfused-expand-rejected`)."

## WF2 (Minor): AGENTS.md pitfall says slice-1 `checkPlan` is vacuous on a fused command

- Location: `leanncd/LeanNCD/Semantics/Plan/AGENTS.md:41`: "Slice-1 `checkPlan` is vacuous on a fused
  command (`checkSteps` accepts it): use `checkPlanF`."
- Evidence: as WF1(1): `checkPlan` rejects any fused plan via `checkSingleton`; only `checkSteps` is
  vacuous. The parenthetical is right, the headline is not. (Spec 31.1's slice-2 sentence says
  "`checkSteps` ignores a fused command", which is correct.)
- Suggested fix: "Slice-1 `checkSteps` is vacuous on a fused command (`checkPlan` rejects fused plans only
  via `checkSingleton`): use `checkPlanF`."

## WF3 (Important): spec text outside the edited paragraphs still says fused commands are unproved

Listed only (not fixed). These were not touched by bc888183 and now contradict the slice-2 rows/paragraphs:
- `tensor_logic_semantics.md:168-170` (intro): "Lemma 31.2, Theorem 31.3 and Lemma 32.1 are proved for the
  slice-1 profile (singleton commands, ...); the general results, fused commands and buffer reuse have no
  Lean proof." Contradicts proof-status rows 202-203 (`terminal_adequacy_F`, `done_correct_F`, ...).
- `:4698-4701` (proof-target list): "composite lemmas for fused commands. *Proved for the slice-1 profile's
  singleton kernels* (`step_R`, `step_failed`); composite lemmas for fused commands remain a target."
  `step_R_command`, `step_failed_command`, `stepCommand_not_stuck` (`Plan.Fusion`) are those composite lemmas.
- `:4713-4715`: "Outside the slice-1 profile (singleton commands, dense non-reused storage, no retirement)
  these are proposed contracts and proof targets, not kernel-checked results ... The slice-1 results fix one
  concrete plan representation". Fused plans are now outside "singleton" and kernel-checked.
- Incomplete but not false: `:4694`, `:4697`, `:4706`, `:4708` ("*Proved for the slice-1 profile*", no
  `checkPlanF_sound`, `runPlan_not_stuck_F`, `_F` theorems); `:4451-4455` ("For the slice-1 kernels (singleton
  commands ...) ... kernel-checked") is immediately followed by the slice-2 sentence, so acceptable.
- Path doc: heading `4.9 Part V slice 1: the singleton-command plan layer` kept (anchor stability; the body's
  first line says slice 2 extends it). Not a finding, noted for the close-out.
- Suggested fix: change "slice-1 profile (singleton commands" to "slice-1/2 profile (singleton or fused
  commands by expansion" at 169, 4713; drop "fused commands" from the no-proof list at 170; replace 4700-4701
  with the `Plan.Fusion` names; add the `_F` names at 4694/4706/4708.

## WF4 (Minor): `step_failed_command` and `stepCommand_not_stuck` described more strongly than stated

- Locations: spec 31.3 slice-2 sentence ("unlike `step_failed`, the matched reference snapshot is the state
  after those earlier annotations"); path doc theorem table rows `step_failed_command` ("matched by the
  reference run of its earlier annotations and then one `undefined` event") and `stepCommand_not_stuck`
  ("A command of an `FValid` plan is never stuck").
- Evidence: `step_failed_command` (`Fusion.lean:141-147`) concludes only
  `∃ c' events, Execution P ops events (.running c) (.failed o.1 o.2 c')`: events and snapshot `c'` are
  existential. The "earlier annotations then one undefined event" shape exists only inside the proof
  (`execAnns_failed`), unlike slice-1 `step_failed`, whose statement pins `[.undefined o.1 o.2]` and snapshot
  `c`. `stepCommand_not_stuck` (`Fusion.lean:156-158`) needs `R pc M c`, `refState pc = some c` and
  `commands[pc]? = some cmd` besides `π.expand.Valid`; the AGENTS contract stresses exactly this caveat for
  `step_R`. (Same occurrence `o`: correct in both the theorem and `runPlan_R_F`.)
- Suggested fix: spec: "the matched reference execution starts from the pre-command state and ends in
  `Failed(o, ...)`; by construction it runs the earlier annotations first (not part of the statement)".
  Path-doc rows: "...is matched by a reference execution from the related state to a failure on the same
  occurrence"; "From R and `Conf = refState pc`, a command of an `FValid` plan is never stuck".

## WF5 (Minor): "the empty command is accepted" by `checkPlanF` is unpinned; "each pinned by a fixture" overstates

- Locations: spec 31.1 slice-2 sentence "The empty command is accepted."; path doc 4.9 "The case-by-class
  table (a1-a10, b-e: ... each pinned by a fixture)".
- Evidence: `rg checkPlanF leanncd/test/Semantics` hits only `fused`, `sPlanFused`, `pPlanFused`, `pPlanAP`,
  `pPlanMisFused`; no fixture evaluates `checkPlanF`/`FValid` on a plan containing `[]` (`fusedEmpty` and
  `emptyCmd` are only run, and `emptyCmd.checkPlan = false` is the slice-1 checker). Plan table cell a10 lists
  run fixtures plus `invalid-empty-command` (slice-1 rejection); cell e is "theorem, no fixture"; cell c's
  pre-command column is "ARGUED ... not probed". The acceptance claim is true by construction
  (`expand` flattens `[]` away) but no fixture or theorem names it.
- Suggested fix: say "accepted (`checkPlanF`, by construction: the expansion drops it)" and "each pinned by a
  fixture except e (theorem) and c (argued)"; an `example : emptyCmd.checkPlanF = true := by decide` would
  pin it (park with O10/O11; not in scope of a read-only review).

## WF6 (Minor): positional wording in 29.3 and 30.4

- 30.4 slice-2 sentence: "`R` and `refState` are indexed by expanded annotations". In code `π.R ... pc` and
  `π.refState ... pc` are indexed by the COMMAND count `pc` and computed from `prefixAnn pc` (the annotations
  of the first `pc` commands; `refState` at `Memory.lean:159-160`, `R` uses `Cons pc`/`Pub pc`), which equals
  `π.expand.prefixAnn (offset pc)` (`prefixAnn_eq_expand`, `Syntax.lean:158`). Expanded indices belong to
  `π.expand`'s `R` (used inside `execAnns_R`).
- 29.3 slice-2 sentence: "conditions 1-4 are evaluated at expanded positions (`offset pc + j`)". Conditions 1
  and 2 are whole-plan (`Coverage1`/`Coverage2`, `Validity.lean:29-31`), not positional; only 3, 4 and the
  `InitOK`/`AccOK`/`PubOK` clauses are evaluated at expanded positions.
- Suggested fix: 30.4: "`R` and `refState` at command `pc` are computed from the annotations of the first
  `pc` commands, i.e. at expanded position `offset pc` of `π.expand`". 29.3: "conditions 3-4 (and the
  per-annotation clauses) are evaluated at expanded positions; conditions 1-2 over the expansion's groups and
  blocks".

## WF7 (Minor): 31.2 says the "same intermediate logical barriers" requirement is "discharged by `FValid`"

- Location: spec 31.2 slice-2 paragraph, last sentence.
- Evidence: record D13 (parked) says that spec sentence "has no formal content" and records the formalised
  CHOICE (R at expanded positions of `π.expand`, claimed only at command boundaries). No theorem states a
  barrier property; `FValid` is `π.expand.Valid` (`FusionCorrectness.lean:23`). "Discharged" asserts more than
  D13 allows. Follow-up to authoring review F-4 (which asked for a D13 pointer); the sweep added the sentence
  without it.
- Suggested fix: "The requirement 'same intermediate logical barriers' is read as validity of the expansion
  (`FValid`); the spec sentence itself has no formal content (D13)."

## WF8 (Minor): `Semantics/Plan/AGENTS.md` code map and contracts only partly updated

- `AGENTS.md:43`: results "in `papers/semantics/plan_layer_mutation_results.md`" only; slice-2 results are in
  `papers/semantics/plan_layer_slice2_mutation_results.md` (the path doc cites both).
- `AGENTS.md:28`: "Soundness rests on `checkPlan` (`checkPlan_sound ...`)" with no `checkPlanF`/
  `checkPlanF_sound` for fused plans (the path doc 4.9 profile paragraph does say both).
- Code-map rows not updated for slice-2 declarations living in slice-1 files: `Step.lean` row lacks
  `execAnns`, `stepCommand` (now the fused step), `stepCommand_single`, `execAnn_prefix`; `Run.lean` row lacks
  `execAnns_not_stuck` (new, `Run.lean:106`); `Syntax.lean` row lacks `expand`/`offset`/`prefixAnn_eq_expand`
  (pointed to from the Fusion row, so findable); `FusionCorrectness.lean` row omits `runPlan_not_stuck_F`,
  which the spec rows cite.
- Purpose line: "a plan is a list of commands (accumulate, publish, `initZero`)": a command is now a list of
  annotations of those kinds.
- Suggested fix: add the slice-2 results file and `checkPlanF` to lines 43/28; add the listed names to the
  Step/Run/FusionCorrectness rows; "a list of commands, each a list of annotations (...)".

## Checked, no finding

- Every identifier named in the slice-2 paragraphs/rows exists under `leanncd/LeanNCD/Semantics/Plan/`:
  `FValid`, `checkPlanF`, `checkPlanF_sound`, `runPlan_R_F`, `runPlan_not_stuck_F`, `terminal_adequacy_F`,
  `done_correct_F`, `failed_correct_F`, `done_or_failed_F`, `done_of_model_F`, `done_iff_model_F`
  (FusionCorrectness); `execAnns_R`, `step_R_command`, `step_failed_command`, `stepCommand_not_stuck`,
  `runFrom_agree`, `runPlan_agree`, `PlanOutcome.Agree` (Fusion); `expand`, `offset` (Syntax); `execAnns`,
  `readPub` use at expanded position via `stepCommand := π.expand.execAnns ops (π.offset pc)` (Step).
- `done m` counts commands: `terminal_adequacy_F` concludes `m = π.commands.length`; `runPlan_R_F`,
  `done_or_failed_F`, `done_of_model_F` use `π.commands.length`. Correct in spec 31.4, path doc, AGENTS.
- Failure memory: `runFrom` reports `.failed o pc M` with the pre-command `M` (`Step.lean:184`); `failed_correct_F`
  concludes only `¬ ∃ ρ, Models` (spec 31.3/31.4 "part (b) compares failure and absence of a model only": correct).
  `PlanOutcome.Agree` compares final memory (done) / occurrence (failed), ignores pc and failure memory: as AGENTS
  and path doc say. `runPlan_R_F` failed disjunct carries the same `o`: spec 31.3 citation correct.
- `step_R_command` hypotheses (`R`, `refState pc = some c`, `commands[pc]? = some cmd`,
  `π.expand.AnnOK (offset pc + j)`): spec 31.2 and path-doc row state them adequately.
- Spec 29.3 conditions 1-4 vs `FValid = π.expand.Valid`: 1 = `coverage1`, 2 = `coverage2`, 3 = `ready`
  (`Pub n` at expanded position, so read-after-publish within a command is legal), 4 = `pubOK` order (`Cons n`).
  "Before" = strictly earlier expanded position. Matches spec 29.3/31.1 slice-2 sentences (modulo WF6 wording).
- "Two slice-1 statements changed": `step_failed`, `step_failed_no_model` now take `commands[pc]? = some [a]`
  (diff 03a2372f..003080b2 of `Simulation.lean`); `step_R`, `step_not_stuck` statements unchanged. "Three slice-1
  fixtures": `invalid-fused` -> `fused-runs-in-slice-2`, `step-empty-command-stuck` -> `step-empty-command-noop`,
  `invalid-empty-command` (expected outcome changed). Correct.
- Counts: `rg -c "^#eval check"` over `Plan*Test.lean` = 18+8+7+23+8+7+1+21+8 = 101; `rg -c "^(example|theorem)\b"`
  = 2+3+30+9+16+4+6 = 70; total 171. Slice-2 files: PlanFusionTest 18, PlanFusionCorrectnessTest 7+9 = 16,
  PlanFusionCheckerTest 8: 42 (18+16+8), so slice 1 = 129. Modules: `Plan.lean` imports ten, in the AGENTS order.
  Mutation: slice-1 results label 3 EQUIVALENT (A2-b, A2-e, A3a-a), slice-2 labels S2-M4: 4 total, as stated;
  manifests 20 + 14 (key counts 60/3, 42/3; authoring review ran `--check`: 14 entries).
- Fixture names cited exist: `misfused-run-undetected`, `fused-failure-after`, `fused-scalar-bad`
  (PlanFusionTest). `fused-failure-after` (`[none,none,none]`, Start memory) and `fused-scalar-bad` (`[7,0,0]`
  vs singleton `[7,2,0]`) do separate transactional from sequential commit, as spec 31.3 says.
- Spec 32.1 / proof-status row 204: both keep the failure half singleton-only (`step_failed`); the 32.1
  paragraph and row 203 name `step_failed_command` for fused, so they no longer contradict (authoring F-3
  resolved by softening 32.1).
- Not run: no build (read-only doc review; statements read from source). Tool uses: ~33 of 50.

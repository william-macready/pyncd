# Part V Plan layer, slice 2 (fusion): execution plan

Live plan. Authoring facts and the close-out go in `papers/semantics/plan_layer_slice2_record.md`.
Sources (the only ones cited; `p1 §2` = `p1_notes.md` section 2): `papers/semantics/plan_layer_slice2_artifacts/{p1_notes,p2a_notes,p2b_notes,p2c_notes}.md`,
`.../evidence.json`, `papers/semantics/plan_layer_slice2_patches/manifest.json` and the four patches,
`papers/semantics/plan_layer_slice2_mutations_post.json`. Slice 1 is `papers/semantics/plan_layer_plan.md`
(structure template; its ids N1-N9, D1-D12, P1-P6 stay as they are).
Code lives in the four patches; this plan holds rationale, decisions, the audit table, fixtures,
mutations and the docs sweep. Lean appears only as one-line signatures copied from the patches.

## 0. Path declaration

**Process weight: Full path.** Slice 2 changes a soundness-bearing kernel (`stepCommand`, used by every
slice-1 theorem), restates two slice-1 theorems (`step_failed`, `step_failed_no_model`), changes three
slice-1 fixtures, and adds a second validity notion (`FValid`) whose silent-ignore cells are exactly the
recurring family of slice 1: a mis-fused plan runs to `done` with a wrong value (`t4-a5-reinitMid`:
`[0,10,0]`, silent) and no differential oracle sees it. The prototype (P1-P2c) and the per-task patches
exist; execution is apply + build + commit per task (slice-plan section 6).

Scope: fusion only (user decision 2026-10-10). Spec Part V, Definition 31.1 / 29.1 / 29.3 for fused
commands, over the slice-1 profile otherwise unchanged.

### What this slice does NOT do (owner)

| item | owner |
|---|---|
| Buffer reuse, retirement, aliasing, liveness for scans (spec 30.3 retirement half) | later Plan-layer slice (buffer-reuse slice) |
| Implementation errors in the step result (allocation failure, kernel error), D7 | later slice, with D7 |
| Fixtures over more than one sort, D11 (theorems are already sort-generic) | later slice, with D11 |
| `In ∩ Out` inputs that are also outputs, D12 | later slice, with D12 |
| Checker completeness (`Valid` implies `checkPlan = true`; also `FValid` implies `checkPlanF`) | not scheduled |
| Floating-point or non-exact numerics | path doc section 5.2 |
| A proof that `checkAccMat` is implied by the other clauses (observed on four plans in slice 1, unproved; `rg` finds no theorem about it) | parked since slice 1 |
| Spec edits beyond the "As formalized" restatement paragraphs and the proof-status rows (fixing the text of 29.3/31.2 for D13-D16) | parked, section 5 |
| A mid-run `run_R_F` from an arbitrary pc | no consumer, section 5 |

## 1. Profile and decisions

Profile: slice-1 profile with ONE change: a command is a finite list of annotations (possibly empty),
executed in order on the running memory. Everything else is as slice 1: dense non-reused buffers,
explicit `initZero`, one sort in fixtures, transactional failure, no implementation errors, no retirement.

Decision ids F1.. are new; each cites its source.

| id | decision | source |
|---|---|---|
| F1 | **Expansion.** `π.expand` is the plan whose commands are `π.ann.map ([·])`. Semantics of a fused command = fold of per-annotation steps (`execAnns`); validity of a fused plan = validity of its expansion (spec 29.3 "expand fused annotations in their stated order"). | p1 §3 |
| F1-rej | Rejected: (a) re-index `Valid`/`StepOK`/`Order4`/`AnnOK`/`checkSteps` by `(pc, j)` and rewrite the step lemmas, about 1500 lines for the content `π.expand` gives free; (b) pre-command snapshot semantics (every annotation reads the pre-command memory), contradicts 29.1 "sequential composition" and the 32.3 relu example and makes a3 stuck; (c) a dedicated fused kernel over the whole list, loses reuse of the per-annotation proofs. | p1 §3 |
| F2 | `FValid π := π.expand.Valid` (an `abbrev`, no new structure); `checkPlanF π := π.expand.checkPlan`; `checkPlanF_sound` is `checkPlan_sound` applied to the expansion. `Valid` and its `singleton` field are unchanged (it is the validity notion of an already expanded plan). | p1 §1 audit rows Validity, §3; p2b Statements |
| F3 | **In-place `stepCommand`.** `stepCommand` is generalised in the slice-1 file (`π.expand.execAnns ops (π.offset pc) M cmd`); slice-1 fixtures that asserted `stuck` for fused or empty commands change with T1 (F11). Rejected: a side-file `stepCommandF`/`runFromF`/`runPlanF` (zero slice-1 statement changes) because `runPlan` would stay a trap: a fused plan would silently run `stuck`. `stepCommand_single` re-bases the slice-1 proofs. | p1 §3 fallback; p2a Signatures |
| F4 | **Transactional failure, pre-COMMAND memory.** A `semFail` in any annotation of a fused command reports `failed o pc M_pre` where `M_pre` is the memory before the whole command (earlier annotations are rolled back). Free: `runFrom` already reports the pre-step memory and `StepResult.semFail` carries none. Partial failure would need `semFail` to carry memory and pins a snapshot the spec does not (D14). Matching reference segment includes the earlier annotations (`step_failed_command`). | p1 §2(d), §3 rejected; D14 |
| F5 | **R at command boundaries only.** `R` and `refState` are already indexed by expanded annotations at command boundaries (`prefixAnn pc` flattens). Inside the fold the invariant is `R π.expand n ∧ Conf = refState π.expand n`; `step_R_command` is `execAnns_R` transported by `R_transport` along `prefixAnn_eq_expand`. N9 stays (`R ∧ Conf = refState`). | p1 §2(e); p2a; D13 |
| F6 | **`done`'s pc is the command count** of the fused plan and is NOT compared with the expansion's pc (they differ: 1 vs 3 in `fused-reciprocal-all`). `PlanOutcome.Agree`: done = same final memory, failed = same occurrence, stuck = stuck; pc and failure memory are not compared. | p2b Design |
| F7 | **Run bridge, not a direct lift of `run_R`.** One induction (`runFrom_agree`) relates `runFrom` of `π` to `runFrom` of `π.expand`; `runPlan_R_F` and the six Correctness theorems then reuse the slice-1 proofs on the expansion. | p2b Design |
| F8 | **Module split.** Bridge in `Fusion.lean` (needs only Step/Syntax; split at the line `/-! ### Run bridge (T3)` — T2 creates the file above it, T3 appends below it); lifts in new `Plan/FusionCorrectness.lean`. T3 makes zero edits to `Correctness.lean` and `Run.lean`. | p2b Design; manifest.json |
| F9 | Intra-command dependency is legal: a later annotation reads the RUNNING memory (a3 legal, a4 forbidden). Checks are static, at expanded positions `n = offset pc + j`, never against pre-command sets (unsound for a2/a5, wrongly rejecting for a1/a3/a8/a9). | p1 §2(a)(c) |
| F10 | Changed slice-1 statements: exactly two, `step_failed` and `step_failed_no_model` (hypothesis `hcmd : π.commands[pc]? = some [a]` instead of an arbitrary `cmd`), forced because a fused command can `semFail` after earlier annotations. `step_R`, `step_not_stuck`, `accFlat_complete`, `Order4`, `run_R`, `terminal_adequacy`, `done_*`, `failed_correct` keep their statements. | p2a Signatures |
| F11 | Changed slice-1 fixtures: exactly three (they asserted "fused/empty is stuck"), listed in T1. | p2a |
| F12 | The empty command `[]` is a no-op stutter (`execAnns [] = .ok`, `offset` unchanged): accepted by `checkPlanF`, still rejected by slice-1 `checkSingleton` (D16). | p1 §2 a10, §5; p2a |
| F13 | **Reachability.** `Plan.lean` imports `Plan.Fusion` (T2) and `Plan.FusionCorrectness` (T3); both lines verified present in the prototype tree (`rg -n "^import LeanNCD.Semantics.Plan.Fusion" leanncd/LeanNCD/Semantics/Plan.lean` prints two lines), so `import LeanNCD` reaches them through `Semantics.lean`. Test modules are registered in the `Tests` globs of `leanncd/lakefile.toml` (one line per task T2-T4). P2a's missing-import concern is closed: `Fusion.lean` imports `Plan.Run` (which reaches Step/Simulation/Validity) and builds. | p2a Signatures; p2b Reachability; verified by `rg` at authoring |
| F14 | Task partition differs from p1 §6 (`stepCommandF` fallback and 5 tasks): in-place `stepCommand` makes T1 carry the Syntax/Step/Simulation/Run edits and the 3 changed fixtures; aggregator and lakefile edits ride with the task that creates the module (T2, T3, T4), so there is no aggregator task. | manifest.json |

Verbatim signatures (each line is checked against the patches with a script, see the record):

```lean
def expand : P.Plan := { π with commands := π.ann.map (fun a => [a]) }
def offset (pc : Nat) : Nat := (π.prefixAnn pc).length
def execAnns (n : Nat) (M : Memory K σ) : List (Ann P) → StepResult P
def stepCommand (pc : Nat) (M : Memory K σ) (cmd : Command P) : StepResult P :=
theorem expand_singleton : π.expand.Singleton := by
def PlanOutcome.Agree : PlanOutcome P → PlanOutcome P → Prop
abbrev FValid (π : P.Plan) : Prop := π.expand.Valid
def checkPlanF (π : P.Plan) : Bool := π.expand.checkPlan
theorem checkPlanF_sound (h : π.checkPlanF = true) : π.FValid := checkPlan_sound π.expand h
theorem execAnns_not_stuck (hv : π.Valid) :
```

## 2. Case x class table (spec 29.3 / 31.1 conditions at fused-command granularity)

Evaluated at expanded positions `n = offset pc + j` (static `Pub n`/`Cons n`/`Mat n`). Classes: R required
(checked and used), F forbidden (checker rejects), I SILENTLY IGNORED. Columns "slice-1 checker" (`checkSteps`
is `| _ => true` on a non-singleton command, p1 P6) and "pre-command check" (the plausible lift that
checks each command against `Pub pc`/`Cons pc`) are the two ways to get it wrong; `π.expand` removes both
(p1 §2). Fixture names were verified with `rg -n` in `leanncd/test/Semantics/Plan*Test.lean` at authoring.
"Flip" = the mutant of section 2.2 that changes this fixture's observed outcome (observed by the probes of
p2b/p2c; "-" = no manifest mutant targets the cell).

| cell | case | legal | expanded check | slice-1 checker | pre-command check | pinning fixtures (name @ file) | mutant flip |
|---|---|---|---|---|---|---|---|
| a1 | `[acc G, pub B]`, B in G (32.3 fusion) | yes | R PubOK order | I | wrongly REJECT | `fused-reciprocal-acc-pub`, `fused-expand-valid-ap` @ PlanFusionTest; AP row of `fusedcorr-valid-agrees-with-expansion` @ PlanFusionCorrectnessTest | S2-M5 (valid-agrees `(false,false,false)`) |
| a2 | `[pub B, acc G]`, G targets B | no | F PubOK order | I | I | `misfused-expand-rejected`, `misfused-slice1-checkSteps-vacuous`, `misfused-run-undetected` @ PlanFusionTest; `fusedcorr-misfused-verdicts` (`pubOrder@1`) @ PlanFusionCorrectnessTest | S2-M9 (verdict `(true,..)` vs `(false,..)`) |
| a3 | later annotation reads an address published earlier in the same command (32.3 relu) | yes | R ReadyOK at `n` | I | wrongly REJECT | `fused-scalar-good` @ PlanFusionTest; `fusedcorr-scalar-done-decode` @ PlanFusionCorrectnessTest; `t4-a3-chainPlan`, `t4-a3split-chainPlan` @ PlanFusionCheckerTest | S2-M12 (a3 `(false,[ready@1,pubOrder@2])` vs `true`), S2-M13, S2-M14 (only `t4-a3split-chainPlan`) |
| a3mis | publication AFTER the read in one command (D15 pair of a3; `[acc0, acc1, pub1]`: accumulated earlier, published later; same `ready` clause as a4) | no | F ReadyOK (`ready@2`) | I | F | `t4-a3mis-chainReadFirst` @ PlanFusionCheckerTest (fused and donor memories differ, kinds agree) | S2-M12 (`pubOrder@1` vs `ready@2`) |
| a4 | reader precedes producer: a later annotation reads an address before ANY accumulation (`[acc1, acc0]`, reader first) | no | F ReadyOK; runtime `readPub = none`, stuck, never a wrong value | I | F | `t4-a4-chainEarly` @ PlanFusionCheckerTest (`ready@1`, stuck, stuck). The "accumulated earlier, published later" instance is the a3mis fixture `[acc0, acc1, pub1]`; both fail the same `ready` clause and the fixtures pin the clause, not a difference between them | S2-M12 (`ready@2` vs `ready@1`), S2-M13 |
| a5 | `[acc G, initZero S]`, G targets S | no | F InitOK (`Cons n`) | I | I | `t4-a5-reinitMid` @ PlanFusionCheckerTest (`initFresh@2`; run `done`, `[0,10,0]`, silent wrong value) | S2-M12 (`(true,[])` vs `initFresh@2`), S2-M13 |
| a6 | `[acc G1, acc G2]` share an occurrence | no | F AccOK; also whole-plan `cov1Nodup` | I per step, caught by Nodup | I per step, caught by Nodup | `t4-a6-dupGroup` @ PlanFusionCheckerTest (`[cov1Nodup, accFresh@2]`) | S2-M13 only (order-insensitive: S2-M12 does not flip) |
| a7 | `[pub B1, pub B2]` overlap | no | F PubOK; also `cov2Nodup` | I per step, caught by Nodup | I per step, caught by Nodup | `t4-a7-pubTwice` @ PlanFusionCheckerTest (`[cov2Nodup, pubFresh@3]`) | S2-M13 only |
| a8 | `[initZero S, acc G]`, G targets S | yes | R AccOK Mat at `n` | I | wrongly REJECT | `fused-step-success` @ PlanFusionTest; `fusedcorr-done-decode` @ PlanFusionCorrectnessTest | S2-M5 (done-decode `(false,[])` vs `true`), S2-M13 |
| a9 | `[initZero B, pub B]`, empty fibers (N1) | yes | R PubOK Mat | I | wrongly REJECT | `t4-a9-lateEmptyInit` @ PlanFusionCheckerTest (`(true,[])`, `[0,14,0]`) | S2-M12 (`(false,[pubMat@2,initFresh@3])` vs `true`) |
| a10 | empty command `[]` (D16) | yes | nothing required; stutter | rejected by `checkSingleton` | n/a | `fused-with-empty-commands`, `empty-step-is-identity` @ PlanFusionTest; `step-empty-command-noop` @ PlanStepTest; `invalid-empty-command` @ PlanValidityTest | OPEN: no manifest mutant targets the empty command (cost: 1 cycle; value fixtures pin the behaviour) |
| b | Order4 per command | yes | `Order4` of `π.expand` | I | n/a | `misfused-expand-rejected` @ PlanFusionTest (a command mis-ordered for Order4 fails expanded `checkPlan`; p1 §2(b)) | S2-M9 |
| c | AccOK/PubOK/InitOK evaluated at | expanded position, static | R | I | unsound for a2/a5 | a1/a3/a8/a9 valid fixtures above (a pre-command check would reject them), a2/a5 invalid fixtures above | pre-command column is ARGUED from the definitions, not probed: OPEN (cost: one scratch probe, no shipped change) |
| d | semantic failure inside a fused command | transactional | `failed o pc M_pre` | n/a | n/a | `fused-failure-after`, `fused-failure-after-ap`, `fused-scalar-bad`, `fused-two-acc-different-tensors-bad` @ PlanFusionTest; `fusedcorr-failed-no-model`, `fusedcorr-failed-agrees-on-occurrence` @ PlanFusionCorrectnessTest | S2-M2 intended; fixture flips observed (P2d, 2.2): `fused-failure-after`, `fused-scalar-bad`, `fused-two-acc-different-tensors-bad` |
| e | R claimed | command boundaries only | `step_R_command` (proved) | n/a | n/a | theorem, no fixture; `fusedcorr-valid-agrees-with-expansion` pins the run bridge | - |

Every I cell of the slice-1 column is removed by `checkPlanF`; a2 and the `misfused-slice1-checkSteps-vacuous`
fixture (`(true, false)`) pin that the slice-1 `checkSteps` really is vacuous on a fused command.
Fixtures a5, a6, a7 do not depend on the order inside the command: their verdict is the same for any
fusing of the donor (p2c).

### 2.1 Donors of the T4 fixtures (all in `PlanFusionCheckerTest.lean`, helper `verdictTrio fused donor`)

| fixture | donor plan | verdict `verdictF = verdict(expand) = verdict(donor)` (the first equality holds BY DEFINITION, `checkPlanF π := π.expand.checkPlan`; the donor column is the independent evidence) | run (fused kind, donor kind, memories equal, fused slots / donor slots) |
|---|---|---|---|
| `t4-a3-chainPlan` | `chainPlan` | `(true, [])` | done, done, true, `[0,3,4]` |
| `t4-a3split-chainPlan` | `chainPlan` (consumer a LATER command than fused `acc;pub`) | `(true, [])` | done, done, true, `[0,3,4]` |
| `t4-a3mis-chainReadFirst` | `chainReadFirst` (acc0, acc1, pub1) | `(false, [ready@2])` | stuck, stuck, FALSE, `[0,0,0]` vs `[0,3,0]` |
| `t4-a4-chainEarly` | `chainEarly` | `(false, [ready@1])` | stuck, stuck, true, `[0,0,0]` |
| `t4-a5-reinitMid` | `reinitMid` | `(false, [initFresh@2])` | done, done, true, `[0,10,0]` |
| `t4-a6-dupGroup` | `dupGroup` | `(false, [cov1Nodup, accFresh@2])` | done, done, true, `[0,16,0]` |
| `t4-a7-pubTwice` | `pubTwice` | `(false, [cov2Nodup, pubFresh@3])` | done, done, true, `[0,14,0]` |
| `t4-a9-lateEmptyInit` | `lateEmptyInit` | `(true, [])` | done, done, true, `[0,14,0]` |

All values observed by P2c (`check` throws on mismatch); `t4-a3mis` is the only fixture where fused and donor
memories differ (a stuck fused command reports the pre-command memory, F4).

### 2.2 Mutation cycles (14; `papers/semantics/plan_layer_slice2_mutations_post.json`)

`mutation-manifest.sh --check` unfiltered: "manifest OK: 14 entries, 14 selected, every old-string unique"
(evidence.json). Task tags: T1 none; S2-M1/M3/M4 are tagged T2 although their `old` text first exists in T1,
because their `targets` (`LeanNCD.Semantics.Plan.Fusion`, `Semantics.PlanFusionTest`) first exist in T2
(evidence.json `mutation_task_tag_audit`). Split: T2 = M1-M4, T3 = M5-M11, T4 = M12-M14. One entry, S2-M4, is
labelled "equivalent at fixture level" (its manifest label; it still breaks a library proof, so the cycle passes); the other 13 are
not equivalent in any sense observed.

**Every one of the 14 mutants breaks a LIBRARY proof first** (the `expect` string names the proof or
statement that fails), so under `lake` no fixture is ever reached: the cycle passes because the build fails
with the expected error, which shows only that some proof depends on the mutated definition. Whether a
FIXTURE flips was therefore observed separately with proof-free scratch probes (mutated function under a new
name, fixture re-evaluated). The probes are NOT committed (they lived in the authoring scratchpad:
`ScratchProbeT3.lean`, `ScratchProbeT4.lean`, `ScratchProbeP2d.lean`). Observations:

| mutant | what it changes | library break (kind) | fixture flips under the probe |
|---|---|---|---|
| S2-M1 | `execAnns` folds right-to-left | `stepCommand_single`, "No goals to be solved" | yes (P2d): `fused-reciprocal-all` stuck@0 vs done@1; `fused-failure-after` stuck@0 vs failed@0; `fused-with-empty-commands` stuck@1 vs done@5; `fused-runs-in-slice-2` stuck@0 vs done@2; `misfused-run-undetected` stuck@0 vs done@1; `t4-a3-chainPlan` done@3 `[0,3,1]` vs `[0,3,4]`; `t4-a5-reinitMid` done@4 `[0,14,0]` vs `[0,10,0]`; `t4-a9-lateEmptyInit` stuck@2 vs done@3. NOT `fused-scalar-good` (the P2a intended fixture): unchanged |
| S2-M2 | failure reports the partial memory | `run_R`, "Application type mismatch" | yes (P2d), memory slots only (pc and occurrence unchanged): `fused-failure-after` `[0,0,0]` vs `[none,none,none]`; `fused-scalar-bad` and `fused-two-acc-different-tensors-bad` `[7,2,0]` vs `[7,0,0]`. `fused-failure-after-ap`: unchanged |
| S2-M3 | every annotation reads the pre-command memory | `stepCommand_single`, "Tactic `rfl` failed" | yes (P2d): every command run with an ok annotation changes (the mutant returns the pre-command memory, so a later command is stuck@1): `fused-scalar-good` stuck@1 `[7,none,none]` vs done@2 `[7,2,3]`, `fused-reciprocal-acc-pub`, `fused-two-acc-different-tensors(-bad)`, `t4-a3split-*`, `t4-a3-*`, `t4-a5`, `t4-a6`, `t4-a7`, `t4-a9`, `fused-failure-after-ap` failed@1 `[none,none,none]` vs `[0,0,0]`. `fused-failure-after`: unchanged |
| S2-M4 | `offset` + 1 | `prefixAnn_eq_expand`, "Tactic `rewrite` failed" | EQUIVALENT at fixture level (killed only by its library proof; S2-M14 is the observed offset mutant). NO fixture flips (P2d: 19 fused runs re-evaluated, all four mutants' runs listed in the record). Run-equivalent by argument: `execAnn` reads the plan only through `Pub pc`, and the extra annotation in `prefixAnn (offset + 1 + k)` is the one being executed (an `initZero`/`acc`, which is no publication, or a `pub`, which reads no view). Differs from S2-M14 (offset smaller: loses earlier publications, flips `t4-a3split-chainPlan`). Killed only by the library proof (the `expect` above) |
| S2-M5 | `checkPlanF := π.checkPlan` | `checkPlanF_sound`, "Application type mismatch" | yes: `fusedcorr-done-decode` `(false,[])` vs `true`; valid-agrees `(false,false,false)` |
| S2-M6 | `FValid := π.Valid` | `FValid`/`checkPlanF_sound`, "Type mismatch" | yes: `fused.Valid := checkPlan_sound (by decide)`: `decide` shows `fused.checkPlan = true` is false |
| S2-M7 | `terminal_adequacy_F` drops `hv` | "Unknown identifier `hv`" | yes: "done implies Decode isSome" is false on `fusedcorr-missing-publication` (hypothesis necessity) |
| S2-M8 | reports the expanded command count | `terminal_adequacy_F`, "Application type mismatch" | yes: `finalPc fusedRun = 2`, expansion length 3 |
| S2-M9 | `checkPlanF` = slice-1 checker minus singleton | "Application type mismatch" | yes: misfused verdict `(true,..)` vs `(false,..)` (`checkSteps` vacuous) |
| S2-M10 | `Agree` drops final-memory equality | "Type mismatch" | only through the NEGATIVE `Agree` example (`¬ Agree10 …` no longer typechecks); value fixtures do not flip |
| S2-M11 | `Agree` drops failing-occurrence equality | "Type mismatch" in `Fusion.lean` | only through the negative example for the occurrence |
| S2-M12 | `expand` reverses order within each command | `expand` lemmas, "Type mismatch" | yes: a3, a3mis, a4, a5, a9, a3split flip; a6, a7 unchanged (order-insensitive) |
| S2-M13 | `expand` drops the first annotation of each fused command | same | yes: every fixture changes (`cov1Complete`/`cov2Complete`/`pubMat` appear) |
| S2-M14 | `offset := (commands.take pc).length` | `prefixAnn_eq_expand`, "Tactic `rewrite` failed" | yes, ONLY `t4-a3split-chainPlan`: `("stuck", 2, [0,3,0])` vs shipped `("done", 4, [0,3,4])` |

S2-M10 and S2-M11 are caught only by the two negative `Agree` examples in `PlanFusionCorrectnessTest.lean`
(weakening a relation changes no value evaluation). S2-M14 is caught by no other fixture: the offset
matters only when a READING command follows a fused command.

## 3. Tasks

All tasks apply a patch from `papers/semantics/plan_layer_slice2_patches/`; sha256 in `manifest.json`.
Patch base (parent of T1) = `main` 4570a794. Symbols `identifier @ file` below are the manifest.json symbol
lists; implementers read 40-60-line windows around them, never whole files. Job counts are evidence.json
values at emission and move with `main`; the gate is "Build completed successfully" with no `error` line.
Context figures are ESTIMATES (not measured; Rule 6 caps: dispatch peak <= ~250k, <= ~60 turns).

### T1 — in-place `stepCommand`, `expand`, `offset`

Patch: `01-expand-step.patch` (241 lines). Base: `main` 4570a794 (T1 is the first patch).
Files: `Syntax.lean` (+39: `expand`, `offset`, `flatten_map_single`, `expand_ann`, `expand_prefixAnn`,
`expand_commands_getElem?`, `ann_eq_append`, `prefixAnn_eq_expand`, `drop_flatten`, `ann_getElem?_offset`),
`Step.lean` (+36/-4: `execAnns`, `stepCommand` generalised, `execAnn_prefix`, `stepCommand_single`),
`Simulation.lean` (+13/-14: `step_failed`, `step_failed_no_model` restated per F10; `step_R` proof gains
`simp only [stepCommand_single] at h`), `Run.lean` (+3/-3: re-based `stepCommand` sites; `step_not_stuck`
statement unchanged), `test/Semantics/PlanStepTest.lean`, `test/Semantics/PlanValidityTest.lean` (all under
`leanncd/`, `LeanNCD/Semantics/Plan/` for the first four).
Acceptance (exact):
`bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd Semantics.PlanFixtures Semantics.PlanBatchTest Semantics.PlanMemoryTest Semantics.PlanStepTest Semantics.PlanSimulationTest Semantics.PlanValidityTest Semantics.PlanRunTest Semantics.PlanCorrectnessTest`
(emission: success, 2977 jobs, 13 warnings).
Fixtures: 0 new; 3 changed (F11), observed old -> new:

| slice-1 fixture @ file | old outcome | new outcome |
|---|---|---|
| `invalid-fused` -> renamed `fused-runs-in-slice-2` @ PlanStepTest | `("stuck", 0, none, [none, none, none])` | `("done", 2, none, [some 0, some 14, some 0])` |
| `step-empty-command-stuck` -> renamed `step-empty-command-noop` @ PlanStepTest | `(("stuck", []), ("stuck", 1, none, [some 0, some 0, some 0]))` | `(("ok", [some 0, some 0, some 0]), ("done", 4, none, [some 0, some 14, some 0]))` |
| `invalid-empty-command` @ PlanValidityTest (run half; verdict `(false, ["singleton"])` unchanged) | `("stuck", 1, none, [some 0, some 0, some 0])` | `("done", 4, none, [some 0, some 14, some 0])` |

Every other slice-1 Plan fixture prints unchanged (p2a: 9 Plan test modules; the build is the check).
Mutation cycles: 0 of its own (S2-M1/M3/M4 run in T2, see 2.2). Regression gate: the whole slice-1 Plan
test set builds with two statement changes (F10); the proofs of `step_R`, `step_failed` and `step_not_stuck` also change (T1 file list).
Context estimate: about 25 turns, peak <= 120k. Commit: `feat(semantics): expand fused commands and generalise stepCommand (Plan slice 2, T1)`.
Pitfall: `step_failed` callers (`run_R`, Fusion `execAnns_failed`) need no edit; if one does, the patch did not
apply to the stated base: BLOCKED.

### T2 — fold lemmas, fused step simulation, progress

Patch: `02-fold-lemmas.patch` (363 lines). Base: T1 applied and committed.
Files: `Plan/Fusion.lean` (new, +164, part above the bridge marker: `expand_singleton`, `execAnns_R`,
`execAnns_failed`, `R_transport`, `refState_prefix_congr`, `step_R_command`, `step_failed_command`,
`stepCommand_not_stuck`), `Plan/Run.lean` (+29: `execAnns_not_stuck`), `Plan.lean` (+1: `import
LeanNCD.Semantics.Plan.Fusion`), `test/Semantics/PlanFusionTest.lean` (new, +126), `lakefile.toml` (+1:
`Semantics.PlanFusionTest` in `Tests`).
Acceptance: `bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd Semantics.PlanFusionTest`
(emission: success, 2973 jobs, 13 warnings).
Fixtures: 18 `#eval check` rows, 0 `example`/`theorem` items (counted by `rg -c "^#eval check"` on the file):
`fused-reciprocal-all`, `fused-reciprocal-acc-pub`, `fused-failure-after`, `fused-failure-after-ap`,
`fused-scalar-good`, `fused-scalar-bad`, `fused-expand-valid`, `fused-expand-valid-ap`,
`misfused-expand-rejected`, `misfused-slice1-checkSteps-vacuous`, `misfused-run-undetected`,
`fused-step-success`, `fused-vs-expand-reciprocal`, `fused-vs-expand-scalar`, `fused-with-empty-commands`,
`empty-step-is-identity`, `fused-two-acc-different-tensors`, `fused-two-acc-different-tensors-bad`.
Observed values: p1 §4 and p2a "T2 fixtures" (all from real runs; `check` throws on a mismatch).
Mutation cycles: 4 (S2-M1..M4); fixture flips observed at authoring for M1-M3, none for M4 (2.2, record P2d). Library statements proved with no
`sorry` (axioms `[propext, Classical.choice, Quot.sound]`).
Context estimate: about 30 turns, peak <= 150k. Commit: `feat(semantics): fused-command step simulation and progress (Plan slice 2, T2)`.

### T3 — run bridge and fused correctness

Patch: `03-fused-run-theorems.patch` (455 lines). Base: T2 committed.
Files: `Plan/Fusion.lean` (+92, below the marker `/-! ### Run bridge (T3)`: `PlanOutcome.Agree`,
`runFrom_done_pc`, `runFrom_append_anns`, `runFrom_agree`, `runPlan_agree`), `Plan/FusionCorrectness.lean`
(new, +193: `FValid`, `checkPlanF`, `checkPlanF_sound`, `prefixAnn_done`, `decode_prefix_congr`,
`runPlan_R_F`, `runPlan_not_stuck_F`, `terminal_adequacy_F`, `done_correct_F`, `failed_correct_F`,
`done_or_failed_F`, `done_of_model_F`, `done_iff_model_F`), `Plan.lean` (+1: `import
LeanNCD.Semantics.Plan.FusionCorrectness`), `test/Semantics/PlanFusionCorrectnessTest.lean` (new, +127),
`lakefile.toml` (+1/-1: `Semantics.PlanFusionCorrectnessTest`).
Acceptance: `bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd LeanNCD Semantics.PlanFusionCorrectnessTest`
(emission: success, 8606 jobs, 62 warnings; `LeanNCD` proves the aggregator reaches the new modules).
Fixtures: 7 `#eval check` rows + 9 `example`/`theorem` items = 16: rows `fusedcorr-done-decode`,
`fusedcorr-scalar-done-decode`, `fusedcorr-failed-no-model`, `fusedcorr-misfused-verdicts`,
`fusedcorr-missing-publication`, `fusedcorr-valid-agrees-with-expansion`, `fusedcorr-failed-agrees-on-occurrence`;
items `fused_fvalid`, `fused_model_unique`, `fused_has_model`, `sFused_bad_fvalid`, `scalar_bad_no_model_F`,
and four anonymous `example`s (the `Agree` rfl example, two NEGATIVE `Agree` examples, one more). Axioms of
every theorem above and the fixture theorems: `[propext, Classical.choice, Quot.sound]` (p2b).
Mutation cycles: 7 (S2-M5..M11), 7/7 PASS under `--task T3` at emission; M10/M11 only via the negative examples.
Context estimate: about 35 turns, peak <= 180k (full `LeanNCD` build log is long: read only the tail).
Commit: `feat(semantics): fused plans run and are correct via the expansion (Plan slice 2, T3)`.

### T4 — checker fixtures for the case x class table

Patch: `04-checker-fixtures.patch` (132 lines). Base: T3 committed. Files: `test/Semantics/PlanFusionCheckerTest.lean`
(new, +113), `lakefile.toml` (+1/-1: `Semantics.PlanFusionCheckerTest`; the line also carries the
pre-existing cosmetic whitespace run, section 5). No production code.
Acceptance: `bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd Semantics.PlanFusionCheckerTest`
(emission: success, 2980 jobs, 13 warnings).
Fixtures: 8 `#eval check` rows (table 2.1, donors named). Mutation cycles: 3 (S2-M12..M14), 3/3 PASS at
emission; fixture flips observed (2.2).
Context estimate: about 25 turns, peak <= 120k. Commit: `test(semantics): fused-command checker fixtures, case x class table (Plan slice 2, T4)`.

### T5 — docs sweep (no patch)

Commands in section 4. One docs commit `docs(semantics): Plan slice 2 (fusion) restatements, path doc, intent layer`.
Context estimate: about 40 turns (spec edits are small; the value-grep dispositions dominate).

### Risk table

| task | production files | new fixtures | changed fixtures | mutation cycles | split? | main risk |
|---|---|---:|---:|---:|---|---|
| T1 | 4 (Syntax, Step, Simulation, Run) | 0 | 3 | 0 (3 retagged to T2) | no | the kernel under every slice-1 theorem; guard: all slice-1 Plan tests build |
| T2 | 2 + aggregator line | 18 | 0 | 4 (flips observed M1-M3; M4 EQUIVALENT at fixture level) | no | M4 has no flipping fixture, killed only by its library proof (2.2; S2-M14 is the observed offset mutant) |
| T3 | 2 + aggregator line | 16 | 0 | 7 | no | full `LeanNCD` build time; D5/D14 wording of `done`/`failed` |
| T4 | 0 | 8 | 0 | 3 | no | `t4-a3split` is the sole catcher of S2-M14 |
| T5 | 0 | 0 | 0 | 0 | no | stale values in a document nobody reopened (section 4(d)) |
| totals | | 42 | 3 | 14 | | slice-1 manifest (20 cycles) may need `expect` repair after T1 (UNVERIFIED, section 5) |

New fixture total, measured at the prototype head (`rg -c "^#eval check"` and `rg -c "^(example|theorem)\b"` over
`leanncd/test/Semantics --glob "Plan*Test.lean"`): 101 `#eval check` rows + 70 items = 171 (the same count on
main 4570a794 gives 68 + 61 = 129, the slice-1 figure). The executor re-measures after T4 (4(d)).

## 3.1 Landing and execution procedure (controller)

Every subagent brief opens with the shell preamble of `.claude/skills/new-slice/SKILL.md` (plain separate
commands, absolute paths, `/usr/bin/git -C`, builds only through `lake-build.sh`, `rg -n` and 40-60-line
windows, explicit stage paths, never stage `.claude/settings.json`). Never push (Rule 13): `main` ends ahead of
`origin/main`.

1. Land the docs-only commits on local `main` first. The branch `worktree-plan-layer-slice2` also carries
   prototype Lean commits and must NOT be merged. Gates before any `checkout` or `commit`: `branch --show-current`
   prints `main` and `status --short` prints nothing (otherwise stop).

```sh
/usr/bin/git -C /Users/williammacready/code/python/pyncd branch --show-current
/usr/bin/git -C /Users/williammacready/code/python/pyncd status --short
/usr/bin/git -C /Users/williammacready/code/python/pyncd checkout worktree-plan-layer-slice2 -- papers/semantics/plan_layer_slice2_plan.md papers/semantics/plan_layer_slice2_record.md papers/semantics/plan_layer_slice2_mutations_post.json papers/semantics/plan_layer_slice2_patches papers/semantics/plan_layer_slice2_artifacts
/usr/bin/git -C /Users/williammacready/code/python/pyncd diff --cached --stat
/usr/bin/git -C /Users/williammacready/code/python/pyncd commit -m "docs(plan-slice2): plan, patches, mutation manifest and authoring artifacts" -m "Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

   Gate: `diff --cached --stat` lists only paths under `papers/semantics/plan_layer_slice2_*`; no `.lean`, no
   `lakefile.toml`. The commit message ends with the `Co-Authored-By` trailer.
2. New worktree from local `main`: `EnterWorktree`, then
   `bash .claude/skills/new-slice/prepare-worktree.sh --base main` (no `--plan`: it only copies a gitignored plan, and
   step 1 committed this one to `main`).
   Call it `<exec>`. The prototype worktree stays untouched until close-out. If `main` moved since 4570a794,
   `git apply --check` decides; a failure is BLOCKED, not a hand-merge.
3. Per task T1 -> T4 (ONE commit per task, only the task's files, no edits to patched files):

```sh
shasum -a 256 <exec>/papers/semantics/plan_layer_slice2_patches/<NN-name>.patch
/usr/bin/git -C <exec> apply --check <exec>/papers/semantics/plan_layer_slice2_patches/<NN-name>.patch
/usr/bin/git -C <exec> apply --index <exec>/papers/semantics/plan_layer_slice2_patches/<NN-name>.patch
bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd <targets of the task>
/usr/bin/git -C <exec> diff --cached --stat
/usr/bin/git -C <exec> commit -m "<message of the task>" -m "Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

   The sha256 must equal the `sha256` of that patch in the manifest; read it with
   `rg -n -A2 "<NN-name>.patch" <exec>/papers/semantics/plan_layer_slice2_patches/manifest.json` (the `sha256` key follows
   the `patch` key within three lines). Patch names in order: `01-expand-step`, `02-fold-lemmas`,
   `03-fused-run-theorems`, `04-checker-fixtures`.
4. Mutation cycles, run by the controller per task after that task's commit (T2, T3, T4; T1 has none and
   `--task T1` would be an empty selection, an error):

```sh
bash <exec>/leanncd/scripts/mutation-manifest.sh --out <exec>/papers/semantics/plan_layer_slice2_mutation_results_T<k>.md --task T<k> <exec>/leanncd <exec>/papers/semantics/plan_layer_slice2_mutations_post.json
```

   At the end, once, unfiltered: `bash <exec>/leanncd/scripts/mutation-manifest.sh --out <exec>/papers/semantics/plan_layer_slice2_mutation_results.md <exec>/leanncd <exec>/papers/semantics/plan_layer_slice2_mutations_post.json`
   (expect 14/14 PASS, every file restored byte-identical) and the slice-1 manifest as a regression
   (`.../plan_layer_mutations_post.json`, expect 20/20; a mismatch of an `expect` string caused by T1 is a manifest
   repair by the Direct path, recorded, not BLOCKED). Result files: the per-task
   `plan_layer_slice2_mutation_results_T<k>.md` are scratch (delete them before the task commits; each task commit stays "only the
   task's files"); the final unfiltered `plan_layer_slice2_mutation_results.md` is staged by explicit path in the docs-sweep
   commit (step 6).
5. Fixture flips of S2-M1..M4: observed at authoring, see record "S2-M1..M4 proof-free probes (P2d)"; the
   manifest runs of step 4 remain the T2 gate.
6. Docs sweep T5 (section 4), then the forbidden-token grep, then the full `lake build` (no target argument,
   "Build completed successfully", no `error` line):

```sh
rg -n "\b(sorry|admit|axiom|native_decide)\b" <exec>/leanncd/LeanNCD/Semantics/Plan <exec>/leanncd/LeanNCD/Semantics/Plan.lean <exec>/leanncd/test/Semantics --glob "Plan*"
bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd
```

7. Two whole-branch review lenses (soundness; spec-Lean fidelity), each a dispatch that writes its findings
   INCREMENTALLY to `<exec>/papers/semantics/plan_layer_slice2_artifacts/wb_review_soundness.md` and
   `wb_review_fidelity.md`; findings adjudicated, fixes one dispatch per finding group.
8. Integration (Rule 13, no menu): merge to local `main` with
   `/usr/bin/git -C /Users/williammacready/code/python/pyncd merge --no-ff worktree-plan-layer-slice2-exec`
   (the exec branch name `prepare-worktree.sh` reports), confirm the `leanncd` tree equals the prototype
   (`git diff --stat worktree-plan-layer-slice2 HEAD -- leanncd` shows only docs-sweep Lean-free paths: empty),
   tag the prototype branch BEFORE deleting it, then remove branches and worktrees:

```sh
/usr/bin/git -C /Users/williammacready/code/python/pyncd tag plan-layer-slice2-proto worktree-plan-layer-slice2
/usr/bin/git -C /Users/williammacready/code/python/pyncd worktree remove /Users/williammacready/code/python/pyncd/.claude/worktrees/plan-layer-slice2
/usr/bin/git -C /Users/williammacready/code/python/pyncd branch -D worktree-plan-layer-slice2
```

   Git refuses to delete a branch that is checked out in a worktree, so the worktree goes FIRST, the branch second (`-D` for
   the unmerged prototype branch: the tag keeps its history). Check `git status` in a worktree before removing it (the
   `new-slice` skill's "Finishing the slice"; its `--force` is needed only for untracked leftovers you have identified).
   Same order for the exec worktree after `ExitWorktree` with `keep`: `worktree remove <exec>`, then `branch -d
   worktree-plan-layer-slice2-exec` (merged, so `-d` suffices); both are this slice's own. Do NOT push.
9. Fill the record's close-out (measured token total with `python3 .claude/skills/slice-plan/token-report.py <session-id>`;
   Rule 6 execution budget <= ~175M; an overrun is stated, not hidden).

## 4. Docs sweep T5 (commands)

Run in `<exec>` after T4. Locate every anchor with `rg -n`; never edit by line number. No `File.lean:NNN`
reference goes into any shipped text (identifiers only); exit grep below.

### (a) Spec `papers/semantics/tensor_logic_semantics.md`

```sh
rg -n "As formalized \(slice-1 profile" <exec>/papers/semantics/tensor_logic_semantics.md
rg -n "^### (29\.3|30\.2|30\.4|31\.1|31\.2|31\.3|31\.4|32\.1) " <exec>/papers/semantics/tensor_logic_semantics.md
rg -n "^\| (Lemma 31\.2|Theorem 31\.3|Lemma 32\.1) " <exec>/papers/semantics/tensor_logic_semantics.md
```

At authoring: 9 hit lines (8 with the heading ending `no retirement).**` and 1 two-line variant), one each in
29.3, 30.2, 30.4, 31.1, 31.2, 31.3 (two: the Lemma 31.2 paragraph and the failure-matching paragraph), 31.4, 32.1.
Edit ONLY these paragraphs: replace the heading with `**As formalized (slice-1 and slice-2 profile: fused commands by
expansion, dense non-reused storage, no retirement).**` (keep the variant's trailing words) and append, after each
slice-1 paragraph's last sentence, the slice-2 sentence from the table. Nothing general is replaced.

| section | appended slice-2 wording (drafted from p1/p2b and the proved statements) |
|---|---|
| 29.3 | A command is a finite, possibly empty, list of annotations executed in order; conditions 1-4 are evaluated at expanded positions (`offset pc + j`) on the static sets `Pub n`/`Cons n`/`Mat n`, so "before" inside a command is the expanded order (D15). The plan is valid when its expansion is valid (`FValid`, `checkPlanF`). |
| 30.2 | Fusion adds no new storage rule: a later annotation of a command reads the running memory through `readPub` at its expanded position; the published-only view is `Pub n`. |
| 30.4 | `R` and `refState` are indexed by expanded annotations; `R` is claimed at command boundaries only (`step_R_command`); the intermediate states of a fused command exist only inside the fold (D13). |
| 31.1 | Definition 31.1 for a fused plan is Definition 31.1 of its expansion (`FValid`); the slice-1 `checkSteps` ignores a fused command, so the checker for fused plans is `checkPlanF` (sound: `checkPlanF_sound`). The empty command is accepted (D16). Runtime execution still does not detect an invalid fusion (`misfused-run-undetected`). |
| 31.2 | Successful-step simulation for a command is the fold of the per-annotation steps: from `R ∧ Conf = refState pc`, and `AnnOK` at each expanded position `offset pc + j` of the command, `stepCommand = ok` gives `R` and the reference state at `pc + 1` (`step_R_command`); progress holds under `FValid` (the validity of the expansion: `stepCommand_not_stuck`). The "same intermediate logical barriers" requirement is discharged by `FValid` (31.1 row, D13). |
| 31.3 (failure) | A failing annotation of a fused command rolls back the whole command: `failed o pc M_pre` carries the pre-command memory (D14). The reference runs the earlier annotations of the command and then fails with the same occurrence `o` (`step_failed_command` per command; `runPlan_R_F` for the run); unlike slice-1 `step_failed`, the matched reference snapshot is the state AFTER those earlier annotations. Transactional vs sequential commit, which slice 1 did not tell apart by any fixture, is told apart by fused plans (`fused-failure-after`, `fused-scalar-bad`). |
| 31.3 (Lemma 31.2) | `terminal_adequacy_F`: at `done m M'` the count `m` is the number of COMMANDS; the Need_pub argument is the slice-1 argument on the expansion. |
| 31.4 | Theorem 31.3 for `π.FValid`: `done_correct_F`, `failed_correct_F`, `done_or_failed_F`, `done_of_model_F`, `done_iff_model_F`; part (b) compares failure and absence of a model only (D5, D14). |
| 32.1 | Lemma 32.1 is unchanged; a fused command may contain `acc G` followed by `pub B` (the 32.3 example). The fused failure relation is `step_failed_command` (`Plan.Fusion`); the Lemma 32.1 failure half itself stays as proved (`step_failed`, singleton). |

Proof-status rows (`### Proof status and numbered results`): append to the `Lemma 31.2`, `Theorem 31.3` rows
"Fused plans: `terminal_adequacy_F`" / "`done_correct_F`, `failed_correct_F`, `done_or_failed_F`, `done_of_model_F`,
`done_iff_model_F`, `runPlan_not_stuck_F` (`Plan.FusionCorrectness`)"; `Lemma 32.1` row unchanged (it names the singleton `step_failed`;
`step_failed_command` is a per-command statement and is cited in the 31.3 row, not claimed as the Lemma 32.1 failure half).
New spec-defect rows: D13-D16 are recorded in `plan_layer_slice2_record.md` section "Spec defects D13-D16", the place slice 1
used (`plan_layer_record.md` section "Spec defects recovered"); the spec text carries no D-id rows, none is added.
Exit greps (each prints nothing):

```sh
rg -n "As formalized \(slice-1 profile" <exec>/papers/semantics/tensor_logic_semantics.md
rg -n "[A-Za-z]+\.lean:[0-9]+" <exec>/papers/semantics/tensor_logic_semantics.md
```

### (b) Path doc `papers/semantics/lean_executable_semantics_path.md`

```sh
rg -n "^### 4\.9 |^#### (Slice-1 profile|What slice 1 does not do)|Non-singleton \(fused\)|Not yet done: fused|129 fixtures|20 mutation cycles|slice-1 plan layer" <exec>/papers/semantics/lean_executable_semantics_path.md
```

- Under `### 4.9`: add `- Plan/Fusion` and `- Plan/FusionCorrectness` module bullets and a `#### Fused commands (slice 2)`
  sub-section (F1, F4-F6, the case x class summary); add theorem-table rows for `step_R_command`, `step_failed_command`,
  `stepCommand_not_stuck`, `runPlan_agree`, `checkPlanF_sound`, `terminal_adequacy_F`, `done_correct_F` ... `done_iff_model_F`.
  Keep the 4.9 title (its anchor `#49-part-v-slice-1-the-singleton-command-plan-layer` is linked from several places in the file); add the
  sentence "Slice 2 extends the layer to fused commands."
- Rename `#### Slice-1 profile, fixtures and mutations` to `#### Slice 1 and 2 profile, fixtures and mutations` and
  `#### What slice 1 does not do` to `#### What slices 1 and 2 do not do`; update the two TOC lines (the only references to their anchors:
  `rg -n "slice-1-profile-fixtures-and-mutations|what-slice-1-does-not-do"` over `*.md` at authoring hit only those two TOC lines) and add one
  TOC line for the new `####`.
- Remove `- Non-singleton (fused) commands.` from the does-not-do list; replace "Not yet done: fused (non-singleton) commands;" in `### 5.2`
  by nothing (the other items stay); "Slice 1 of the plan layer has landed" -> "Slices 1 and 2 of the plan layer have landed ... singleton and fused commands".
- Counts: "129 fixtures (96 ..., 27 ..., 6 ...)" -> the measured total from (d) with "+ 42 in slice 2 (18 + 16 + 8)";
  "20 mutation cycles, of which 3 are labelled equivalent" -> "34 mutation cycles (20 in slice 1, 14 in slice 2), of which 4 are labelled equivalent (3 in slice 1; S2-M4 at fixture level)".
  Snapshot paragraph near the top: same two numbers, and "Lean as of" SHA refreshed to the merge head.
- Check the TOC rule (second count is the first minus 1; record both before and after):

```sh
rg -c "^#{2,4} " <exec>/papers/semantics/lean_executable_semantics_path.md
rg -c "^ *- \[" <exec>/papers/semantics/lean_executable_semantics_path.md
```

### (c) Intent layer

```sh
sed -n '/^## Pitfalls/,$p' <exec>/leanncd/LeanNCD/Semantics/Plan/AGENTS.md | wc -c
wc -c <exec>/leanncd/LeanNCD/Semantics/Plan/AGENTS.md
```

At authoring (slice-1 file): whole file 3978 bytes; sections Purpose 935, Code Map 1181, Contracts 839, Pitfalls 997. The hook-injected part
(Pitfalls; there are no Checks/Patterns/Context sections) is 997 bytes: record before and after; gate <= ~3000.
Edit `Plan/AGENTS.md`: Purpose ("slice-1" -> "slices 1-2", delete "fused (multi-annotation) commands" from Does not own); Code Map: "eight
modules" -> "ten", rows `Fusion.lean` (`expand`/`offset` live in `Syntax.lean`; `execAnns` in `Step.lean`; Fusion owns `execAnns_R`,
`step_R_command`, `step_failed_command`, `stepCommand_not_stuck`, `runFrom_agree`, `runPlan_agree`) and `FusionCorrectness.lean` (`FValid`,
`checkPlanF(_sound)`, `runPlan_R_F`, `terminal_adequacy_F`, `done_*_F`); Contracts: a fused plan is valid iff its expansion is (`FValid`),
`done m` counts commands; Pitfalls: add (1) slice-1 `checkPlan` is vacuous on a fused command (`checkSteps`), use `checkPlanF`; (2) a fused
`failed` reports the pre-command memory and `Agree` ignores pc; Mutation line: add `plan_layer_slice2_mutations_post.json` (14 cycles).
`leanncd/LeanNCD/Semantics/AGENTS.md` (it lists Plan: "Part V slice 1: singleton commands over dense memory, `checkPlan`, ..."): change to
"slices 1-2: singleton and fused commands (by expansion) over dense memory". `leanncd/AGENTS.md` row `Semantic explorations`: "Part V slice-1 plan
layer" -> "Part V slice 1-2 plan layer". Reachability: `Plan.lean` imports `Plan.Fusion` and `Plan.FusionCorrectness` (patches 02 and 03; verified
by `rg -n "^import" leanncd/LeanNCD/Semantics/Plan.lean`), `Semantics.lean` imports `Plan`, so `import LeanNCD` reaches them.

### (d) Value-grep of the whole repo (run, then fill the disposition column in the record)

```sh
for p in "129 fixtures" "20 mutation cycles" "20 cycles" "non-singleton" "singleton" "fused" "Slice-1 profile" "slice-1 profile" "slice-1 plan layer" "invalid-fused" "step-empty-command-stuck" "invalid-empty-command"; do rg -c -F --hidden -g '!**/.lake/**' -g '!.git' -g '!papers/semantics/plan_layer_slice2_*' -- "$p" <exec>; done
rg -c "^#eval check" <exec>/leanncd/test/Semantics --glob "Plan*Test.lean"
rg -c "^(example|theorem)\b" <exec>/leanncd/test/Semantics --glob "Plan*Test.lean"
```

Dispositions at authoring (hit files, by value; vocabulary hits in unrelated trees are not edits):
- `129 fixtures`: `lean_executable_semantics_path.md` (EDIT, b), `plan_layer_record.md` (historical slice-1 record: keep).
- `20 mutation cycles`: `lean_executable_semantics_path.md` (EDIT, b). `20 cycles`: `Plan/AGENTS.md` (EDIT, c), `plan_layer_mutation_results.md` and
  `plan_layer_record.md` (historical: keep), `papers/f32c_evalplan.md` (unrelated F32 text: keep).
- `non-singleton`: `lean_executable_semantics_path.md` (EDIT, b), `PlanStepTest.lean` and `PlanFusionCorrectnessTest.lean` (comments in the
  patched files: keep), `plan_layer_record.md` (historical: keep).
- `Slice-1 profile`: `Plan/AGENTS.md`, path doc (EDIT); `Memory.lean`, `Step.lean`, `Syntax.lean`, `Validity.lean` doc comments: keep except the
  `Step.lean` header comment, which says "slice-1 profile: validated Start, singleton commands, and three kernels" (O6: stale after T1, parked).
- `slice-1 profile`: 18 hits in the spec (9 headings EDIT in (a); the other 9 sit inside the same paragraphs, re-read each: still true statements
  about slice-1 theorems stay, others get the slice-2 sentence); path doc (EDIT); `plan_layer_mutation_results.md`, `plan_layer_mutations_post.json`,
  `Plan/*.lean` comments (keep).
- `singleton` / `fused`: the unrelated trees (`papers/f32*`, `papers/future_ideas.md`, `leanncd/LeanNCD/Eval/**`, `torch_compile/AGENTS.md`,
  other `papers/semantics/*` plans and patches) use the words for other concepts (singleton sets, fused kernels in the Eval backend): keep, listed
  as "unrelated vocabulary" in the record. Plan-relevant hits to re-read: spec (24 `singleton`, 7 `fused`), path doc, `leanncd/LeanNCD/Semantics/AGENTS.md`,
  `Plan/AGENTS.md`, the Plan test files (changed or new in T1-T4).
- `invalid-fused`: one hit at the prototype head, `PlanValidityTest.lean` (a different fixture with the same name: verdict only,
  `(false, ["singleton"])`, unchanged: keep); T1 renames the PlanStepTest fixture of that name, so any hit in a document is stale.
  `step-empty-command-stuck`: no hit at the prototype head (renamed to `step-empty-command-noop` by T1; a hit after T1 is stale);
  `invalid-empty-command`: `PlanValidityTest.lean` (name kept, run half changed, verdict unchanged).
- Measured new fixture total: replace "129" with the sum of the two `rg -c` totals above (expected 171 = 101 + 70; state the measured value in the
  record, and if it differs from 171 explain before editing any document).

### (e) Close-out template and memory/roadmap

Fill the "Close-out" section of `papers/semantics/plan_layer_slice2_record.md` (blanks prepared there): per-task commits and job counts,
docs-sweep commit, mutation results (14/14, slice-1 20/20), the two review files, token total, merge SHA, tag `plan-layer-slice2-proto`.
Then update the auto-memory index entry "Part V Plan-layer slice 1" with the slice-2 state (merged SHA, unpushed, parked items of section 5).

## 5. Open items and parked work (each re-verified against the tree at authoring)

| id | item | status at authoring | cost |
|---|---|---|---|
| O1 | D13-D16 spec-text fixes (31.2 "same intermediate logical barriers", failed-fused snapshot, "before" = expanded order, empty command) | spec unedited; defects recorded in the record | 1 Direct docs commit |
| O2 | `lakefile.toml` whitespace run inside the `Tests` list (line holding `Semantics.PlanFusionCheckerTest` then eight spaces before `Semantics.SourceBindingUIDTest`) | present in the prototype tree; cosmetic | 1 line, Direct |
| O3 | S2-M10/M11 caught only by the negative `Agree` examples | by design (2.2) | none |
| O4 | mid-run `run_R_F` from an arbitrary pc not stated | no consumer; derivable from `runFrom_agree` + `run_R` at `offset pc` | 1 theorem if ever needed |
| O5 | fixture flips of S2-M1..M4: CLOSED by P2d (M1-M3 flip fixtures, M4 flips none: EQUIVALENT at fixture level, 2.2); still open: the pre-command-check column of 2 (cell c) is argued, not probed | cell c only: open, optional | about 1 small dispatch, no shipped change |
| O6 | the `Step.lean` header comment still says "slice-1 profile ... singleton commands" | present; `Step.lean` doc comment only | 1 comment edit + rebuild (cost not measured) |
| O7 | D7, D11, D12, buffer reuse/retirement, checker completeness, `checkAccMat` proof | unchanged from slice 1 (section 0) | later slices |
| O8 | slice-1 manifest `expect` strings after T1's edits to Step/Simulation/Run | NOT RUN at authoring (UNVERIFIED) | controller runs it at the end (3.1 step 4); repair = Direct path |
| O9 | P2a's missing-import concern for `Fusion.lean` | CLOSED: imports `Plan.Run`; whole chain built (T2 2973 jobs, T3 8606 jobs) | none |
| O10 | no mutant targets the empty command (a10) | open; value fixtures pin it | 1 cycle if wanted |
| O11 | no fixture puts a reading annotation after an EMPTY command; offset correctness with empty commands rests on the proof `prefixAnn_eq_expand` (no emptiness hypothesis); `fused-with-empty-commands` has no annotation reading the published view | open (review S-3, parked) | closing it needs one T4 fixture and regenerating patch 04 + manifest sha, about 1 small dispatch |

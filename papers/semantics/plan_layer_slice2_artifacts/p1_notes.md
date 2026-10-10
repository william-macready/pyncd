# Plan layer slice 2 (fusion): P1 notes (audit, design, core prototype)

Worktree `plan-layer-slice2`, base main 4570a794. Prototype files (all compile, no `sorry`):
`leanncd/LeanNCD/Semantics/Plan/Fusion.lean` (not yet in the aggregator `Plan.lean`),
`leanncd/test/Semantics/PlanFusionTest.lean` (not yet in the lakefile `Tests` globs).
Spec quotes are from `papers/semantics/tensor_logic_semantics.md` (not edited).

## 1. Audit: where singleton is assumed

Key fact found by reading the code: `prefixAnn pc = (commands.take pc).flatten`, so `Pub/Cons/Mat/SlotView/R/refState`
are ALREADY defined over expanded annotations at command boundaries. `refState_succ` (any `cmd`) and `prefixAnn_succ`
are already general. Only the step kernel, the per-position side conditions and their consumers assume `[a]`.

| site | assumption | what breaks for `[a1, a2, ...]` | replacement |
|---|---|---|---|
| Step.lean `Singleton`, `stepCommand` | `| [a] => execAnn pc M a`, else `.stuck` | a fused command is stuck, `runPlan` reports `stuck` | `execAnns` fold over annotations at expanded positions `offset pc + j` on the running memory (Fusion.lean, `stepCommandF`) |
| Step.lean `execAnn pc M a` | `pc` is the command prefix; `readPub pc` = `Pub pc` | for `a_j`, j>0, `pc` would be pre-command, so a read of what `a_{j-1}` published is `none`, i.e. `stuck` | index by expanded position `n`; `execAnn_prefix`: `execAnn` depends on the plan only through `prefixAnn` at its position |
| Simulation.lean `StepOK pc`, `Order4`, `AnnOK pc` | quantify `commands[pc]? = some [a]` | for fused commands the conditions are vacuous (silently ignored) | state them at expanded positions: apply to `π.expand` (every command a singleton, `expand_singleton`) |
| Simulation.lean `accFlat_complete (single : π.Singleton)` | uses singleton to locate the publishing command | none for `π.expand` (`expand_ann : π.expand.ann = π.ann`, same `accFlat`/`pubFlat`) | statement unchanged, applied to `π.expand` |
| Simulation.lean `refState_succ_single` (D4) | `[a]` | not needed for fusion; `refState_succ` is the general form | unchanged |
| Simulation.lean `step_R` | `commands[pc]? = some [a]`, `AnnOK pc a` | does not apply to a fused command (R only at command boundaries) | statement unchanged; `execAnns_R` folds it over `π.expand` (prototype, closed); `step_R_command` for `π` |
| Simulation.lean `step_failed`, `step_failed_no_model` | `cmd` general, `ok : cmd = [.acc G] → ...`, `match cmd` with a `_ => stuck` case | with `stepCommand` generalised, `semFail` on a fused `cmd` is no longer excluded, and the conclusion `Execution [undefined o] c (failed o c)` is FALSE for a fused command (earlier annotations must run first) | restrict hypothesis to `hcmd : commands[pc]? = some [a]` (statement change, 2 theorems); fused version `step_failed_command` (prototype, closed) |
| Validity.lean `Valid.singleton`, `initFresh/accOK/pubOK/ready` (`= some [.x _]`) | per-singleton fields | fused commands unchecked | `FValid π := π.expand.Valid` (no new structure); `Valid` unchanged |
| Validity.lean `checkSingleton`, `checkSteps` (`| _ => true`), `checkPlan` conjunct | `checkSteps` vacuous on non-singleton (P6) | the checker accepts/ignores any fusion that `checkSingleton` does not already reject; today only `checkSingleton` stops it | `checkPlanF π := π.expand.checkPlan`; `checkPlan_sound` applies verbatim (`checkSingleton` is trivially true on `π.expand`) |
| Validity.lean `nodup_prefixAnn_flatMap (hs)`, `checkPlan_nodup_redundant` | singleton | none for `π.expand` | unchanged |
| Run.lean `step_not_stuck`, `run_R` (`hv.singleton`, `stepCommand ops pc M [a]`) | singleton | fused commands out of scope of the induction | statement unchanged; fused versions via the bridge (T3) |
| Correctness.lean `cov1_of_cov2_pubOrder`, `terminal_adequacy`, `done_*`, `failed_correct` | `hv.singleton` passed to `accFlat_complete`; `runPlan` | none for singleton `Valid` | fused versions: hypothesis `π.expand.Valid`, run through the bridge `runPlan π ~ runPlan π.expand` |

`stepCommand` occurrences to patch when generalised in place: Run.lean 4, Simulation.lean 2, Step.lean 3, tests PlanStepTest 3,
PlanValidityTest 1 (counted by `rg -c`).

## 2. Case x class table (spec 29.3/31.1 conditions at fused-command granularity)

Evaluated against EXPANDED positions (static prefix sets `Pub n/Cons n/Mat n`, `n = offset pc + j`). Classes: R = required (checked and used),
F = forbidden (checker rejects), I = SILENTLY IGNORED by the slice-1 checker on a fused command (`checkSteps` is `| _ => true`, P6) or by a
checker that evaluates a fused command against the PRE-command sets ("pre-cmd" column).

| # | case (inside one command) | legal? | class under expanded-position check | slice-1 checker on the fused plan | pre-command-set check |
|---|---|---|---|---|---|
| a1 | `[acc G, pub B]`, B's occurrences in G (spec 32.3 fusion) | yes | R: PubOK order (`Cons n` contains G) | I (only `checkSingleton` rejects) | would REJECT (wrongly: `Cons pc` lacks G) |
| a2 | `[pub B, acc G]`, G targets B (publish before consume) | no | F: PubOK order | I. Observed: slice-1 `checkSteps` true, expanded false; run undetected (N4) | I (both sets lack G) |
| a3 | later annotation reads a footprint address published by an EARLIER annotation of the same command (spec 32.3 relu example) | yes (29.1: sequential composition; 29.3 "before" is in expanded order) | R: ReadyOK at `n` (`Pub n` contains it) | I | would REJECT (wrongly) |
| a4 | later annotation reads an address only ACCUMULATED (not published) earlier in the command | no | F: ReadyOK; at runtime `readPub` is `none` => stuck, never a wrong value | I | F (same) |
| a5 | `[acc G, initZero S]`, G targets S (re-init after consume) | no | F: InitOK (`Cons n` contains G) | I | I (pre-command `Cons` lacks G): wipes accumulated contributions (`reinitMid` class) |
| a6 | `[acc G1, acc G2]`, G1 and G2 share an occurrence | no | F: AccOK (`¬Cons n`); also whole-plan `cov1Nodup` | I per-step, caught by whole-plan Nodup | I per-step, caught by Nodup |
| a7 | `[pub B1, pub B2]` overlapping | no | F: PubOK (`¬Pub n`); also `cov2Nodup` | I per-step, caught by Nodup | I per-step, caught by Nodup |
| a8 | `[initZero S, acc G]`, G targets S | yes | R: AccOK Mat at `n` (`Mat n` contains S) | I | would REJECT (wrongly) |
| a9 | `[initZero B, pub B]`, empty fibers (N1) | yes | R: PubOK Mat | I | would REJECT (wrongly) |
| a10 | empty command `[]` | yes (finite sequence) | nothing required; no-op stutter, `offset` unchanged | rejected by `checkSingleton` | n/a |
| b | Order4 per command | `Order4` must be about expanded positions | `Order4` of `π.expand` | I | n/a |
| c | AccOK/PubOK/InitOK evaluated at | expanded position (static sets, memory independent) | R | I | pre-command is unsound for a2/a5 |
| d | semantic failure inside a fused command | transactional: whole command rolled back | `failed o pc M_pre` | n/a | n/a |
| e | R claimed | command boundaries only | `step_R_command` | n/a | n/a |

Cells marked SILENTLY IGNORED (I): every "slice-1 checker" cell of a1-a9, and the "pre-command" cells of a2, a5, a6, a7. The first
column is the danger of leaving `checkSteps` as is; the second is the danger of a plausible-looking lift ("check each command against
`Pub pc`/`Cons pc`"); both are removed by checking `π.expand`.

(a) Intra-command dependency is legal. 29.1: "A fused command may have a finite sequence of these annotations. Its contract is their sequential
composition, even if intermediate states exist only in its proof." 29.3: "Expand fused annotations in their stated order." 32.3: "collecting the two
`Pre` occurrences, publishing `Pre`, and then evaluating ReLU can be fused if those logical barriers are respected internally." So later annotations
read the RUNNING memory (a3 legal, a4 forbidden).

(b) Order4 on expanded positions: `Order4 π.expand`. Observed: `[initZero B, pub B, acc G]` fails expanded `checkPlan` (misfused-expand-rejected).

(c) Static, so memory-independent. At RUNTIME the later annotation reads the running memory through `readPub n M`; the view is `Pub n`.

(d) Transactional (decision, consistent with D5): `runFrom` already reports the PRE-step memory, and `StepResult.semFail` carries none,
so transactional failure is free; partial failure would need `semFail` to carry memory. `step_failed_command` says: from `R pc M c` with
`c = refState pc`, the reference runs the earlier annotations of the command (each succeeds by `step_R` at its expanded position) and then
`Execution _ (running c) (failed o.1 o.2 c')` for some `c'` (c' is the reference state after the earlier annotations, not `c`). Observed:
failureAfter fused whole = `failed pc 0` with all slots `none` (singleton: `failed pc 1`, slots `[0,0,0]`).

(e) R only at command boundaries; `refState pc` is already indexed by expanded positions (`prefixAnn pc` flattens), `refState pc = refState
π.expand (offset pc)` (`refState_prefix_congr`). N9 stays: `step_R_command` assumes `R ∧ Conf = refState pc`; inside the fold the invariant is
`R π.expand n ∧ Conf = refState π.expand n`. Simulation lemma: `step_R_command` = `execAnns_R` (fold of `step_R` over `π.expand`) transported by
`R_transport` along `prefixAnn_eq_expand`.

## 3. Design

Chosen: EXPANSION. `π.expand` is the plan whose commands are `π.ann.map ([·])`. Fusion semantics = fold of per-annotation steps; validity of a
fused plan = validity of its expansion (exactly spec 29.3's "expand fused annotations"). New definitions (Fusion.lean, split as marked there):
```lean
def expand : P.Plan                                   -- Syntax.lean
def offset (pc : Nat) : Nat := (π.prefixAnn pc).length -- Syntax.lean
def execAnns (n : Nat) (M : Memory K σ) : List (Ann P) → StepResult P   -- Step.lean
def stepCommand (pc) (M) (cmd) : StepResult P := π.expand.execAnns ops (π.offset pc) M cmd  -- replaces the slice-1 def (prototype name: stepCommandF)
theorem execAnn_prefix (h : π.prefixAnn pc = π'.prefixAnn pc') M a : π.execAnn ops pc M a = π'.execAnn ops pc' M a
theorem stepCommandF_single : π.stepCommandF ops pc M [a] = π.execAnn ops pc M a        -- lets slice-1 proofs re-base
theorem R_transport (h : π.prefixAnn pc = π'.prefixAnn pc') (hR : π.R ops η pc M c) : π'.R ops η pc' M c
theorem refState_prefix_congr (h : ...) : π.refState ops η pc = π'.refState ops η pc'
theorem execAnns_R (π') : ∀ anns n M M' c, π'.R .. n M c → π'.refState .. n = some c → (∀ j a, anns[j]? = some a → π'.commands[n+j]? = some [a] ∧ π'.AnnOK (n+j) a) → π'.execAnns ops n M anns = .ok M' → ∃ c', π'.refState .. (n+anns.length) = some c' ∧ π'.R .. (n+anns.length) M' c' ∧ ∃ events, Execution P ops events (.running c) (.running c')
theorem execAnns_failed (π') : ... = .semFail o → ∃ c' events, Execution P ops events (.running c) (.failed o.1 o.2 c')
theorem step_R_command (hR) (hc : π.refState ops η pc = some c) (hcmd : π.commands[pc]? = some cmd) (ok : ∀ j a, cmd[j]? = some a → π.expand.AnnOK (π.offset pc + j) a) (h : π.stepCommand ops pc M cmd = .ok M') : ∃ c', π.refState ops η (pc+1) = some c' ∧ π.R ops η (pc+1) M' c' ∧ ∃ events, Execution P ops events (.running c) (.running c')
theorem step_failed_command ... (h : ... = .semFail o) : ∃ c' events, Execution P ops events (.running c) (.failed o.1 o.2 c')
```
(`step_R_command` and `step_failed_command` and the folds compiled in the prototype; `ok` is discharged from `hv.stepOK` for `hv : π.expand.Valid`.)
To add in the plan (not prototyped): `execAnns_not_stuck` (fold of `step_not_stuck`'s per-annotation facts, needs R from `execAnns_R`'s step),
the bridge `runPlan π ~ runPlan π.expand` (done/failed/stuck correspond; failed carries a different pc and memory), `FValid π := π.expand.Valid`,
`checkPlanF`/`checkPlanF_sound`, and the fused Lemma 31.2 / Theorem 31.3 corollaries.

Slice-1 theorem statements that change: `step_failed`, `step_failed_no_model` (hypothesis `hcmd : commands[pc]? = some cmd` plus
`ok : cmd = [.acc G] ...` becomes `commands[pc]? = some [a]`; only if `stepCommand` is generalised in place). `Valid` keeps its `singleton`
field and is NOT changed (it is then the validity notion of the already-expanded plan); `accFlat_complete`, `Order4`, `step_R`, `terminal_adequacy`,
`done_iff_model`, `done_correct`, `failed_correct`, `done_or_failed`, `done_of_model`, `run_R`, `runPlan_R`, `step_not_stuck` keep their statements
(fused versions are new theorems about `π.expand.Valid`). Fallback with ZERO slice-1 statement changes: keep `stepCommand`/`runFrom` and add
`stepCommandF`/`runFromF`/`runPlanF` (the prototype as written) plus `runPlanF_eq_runPlan_of_singleton`; rejected as the main route because
`runPlan` would stay a trap (a fused plan runs `stuck` silently).

Rejected alternatives (<= 3 lines each):
- Re-index `Valid`/`StepOK`/`Order4`/`AnnOK`/`checkSteps` by `(pc, j)` and rewrite the step lemmas over commands: about 1500 lines of churn for the same content as `π.expand`, and it re-proves what the expansion gets for free.
- Pre-command snapshot semantics (all annotations of a command read the pre-command memory): contradicts 29.1 ("sequential composition") and the 32.3 relu example (the consumer reads the producer's publish), and makes case a3 stuck.
- A dedicated fused kernel taking the whole annotation list (batch all groups): loses reuse of the per-annotation proofs (Rule: maximize reuse) and needs a new simulation proof per combination.
- Partial (non-transactional) failure: needs `semFail` to carry memory, and weakens `failed pc M` to a snapshot that the spec does not pin (D5/D14); transactional is already the slice-1 profile.

## 4. Observed fixtures (`PlanFusionTest.lean`, all printed by `lean-file.sh`, equal to hand-computed values)

| fixture | observed | note |
|---|---|---|
| fused-reciprocal-all (`[[initZero, acc, pub]]`) | `("done", 1, none, [3/4, 0, 0])` | same memory as singleton plan, pc counts commands |
| fused-reciprocal-acc-pub (`[[initZero],[acc, pub]]`) | `("done", 2, none, [3/4, 0, 0])` | |
| fused-failure-after (whole plan one command) | `("failed", 0, some (1,0), [none, none, none])` | singleton: pc 1, `[0,0,0]`; fused rolls back initZero too |
| fused-failure-after-ap | `("failed", 1, some (1,0), [0,0,0])` | pre-command memory = post-initZero |
| fused-scalar-good (intra-command read, a3) | `("done", 2, none, [7,2,3])` | singleton `done 5` same values |
| fused-scalar-bad | `("failed", 1, some 2, [7,0,0])` | singleton `failed 3, [7,2,0]`: statement 1's committed acc is rolled back |
| fused-expand-valid / -ap | `true`, `true` | `checkPlan` of the expansion |
| misfused-expand-rejected | `false` | a2 |
| misfused-slice1-checkSteps-vacuous | `(true, false)` | slice-1 `checkSteps` vs expanded: the silently-ignored cell |
| misfused-run-undetected | `("done", 1, none, [3/4,0,0])` | N4 again: the run does not detect the invalid fusion |

Not run: a5/a6/a7/a8/a9 as fixtures (table is by definition of the checks); full `lake build` (only the target `LeanNCD.Semantics.Plan.Fusion`
and the one test file were built, since neither is in the aggregator/globs yet).

## 5. New spec defects (continue from D13; spec text NOT edited)

- D13: 31.2 "A fused command must justify the same intermediate logical barriers as its annotation sequence" has no formal content: R_Pi is only defined at command boundaries (30.4), "intermediate states exist only in its proof" has no relation. Formalised choice: R at expanded positions of `π.expand`, claimed only at command boundaries.
- D14: failed fused command: 30.1/31.3 pin neither the concrete memory after `PlanFailed(o)` nor the snapshot of the matching `Failed(o, sigma', alpha', U')`, so transactional vs partial rollback of the earlier annotations of the same command is unspecified (extends D5). Chosen: transactional (pre-command memory); the matching reference segment includes the earlier annotations.
- D15: 29.3 conditions 3 and 4 say "before" without saying that it is the expanded order for same-command annotations (the 29.3 header sentence says so once). Intra-command read-after-publish (a3) is legal by the text but 32.3 only discusses acc+pub fusion; a kernel that reads a pre-command snapshot would violate condition 3 at runtime while the static check passes (implementation obligation, "respected internally").
- D16: 29.3 says nothing on an empty command (`[]`, a finite sequence of zero annotations); harmless no-op, currently rejected by `checkSingleton`, accepted by `checkPlanF`.
- Parked (not spec defects): 32.3 "concurrent updates within a kernel" / aliasing implementation arguments (outside the exact-model scope).

## 6. Proposed task partition (for the plan author)

| task | content | fixtures | mutation cycles |
|---|---|---|---|
| T1 | Syntax/Step: `expand`, `offset`, expansion lemmas, `execAnns`, generalise `stepCommand` in place, `execAnn_prefix`, `stepCommand_single`; re-base the 10 `stepCommand` sites; restrict `step_failed`/`step_failed_no_model` | 0 new (all slice-1 fixtures must print unchanged: regression) | 3 (`offset` ignores prefix, `execAnns` index not advanced, failure not propagated) |
| T2 | Simulation: `R_transport`, `refState_prefix_congr`, `execAnns_R`, `execAnns_failed`, `step_R_command`, `step_failed_command`, plus `execAnns_not_stuck` (not prototyped, about 40 lines) | 6 fused run fixtures of section 4 | 4 |
| T3 | Validity/Run/Correctness bridge: `FValid`, `checkPlanF(_sound)`, `runPlan ~ runPlan π.expand`, fused Lemma 31.2 and Theorem 31.3 | 4 (fused `Valid` instances, done/failed/model, `done_iff_model`) | 3 |
| T4 | Case x class fixtures for the checker (a1-a9, a10) as clause rows; the pre-command mutant | 10 | 3 |
| T5 | Docs: Definition 31.1 / 29.1 / 31.2 / 31.3 restatement, AGENTS.md, record, D13-D16, aggregator + lakefile Tests glob | 0 | 0 |

Total about 20 fixtures and 13 mutation cycles, 5 tasks.

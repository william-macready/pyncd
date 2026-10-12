# Whole-branch review: R regression net (worktree-r-net, main..HEAD)

Range: `main..HEAD` = aa882476 (test) + 5494d5e1 (docs). Read-only review; evidence from the diff, the
library definitions (`Plan/Step.lean` `stepPlan`/`runFrom`/`execPub`/`execRet`, `Plan/Syntax.lean`
`prefixAnn`/`Pub`/`Ret`/`Live`, `Plan/Fusion.lean` `step_R_command`, `Plan/Memory.lean` `R`), the build
log `rnet4.log`, and the controller's probe logs `rnet_ma.log` / `rnet_mc.log` / `rnet_me.log`.

### F1 [Important] `dead`/`retPub` preservation through `step_init`/`step_acc` is only instantiated vacuously; the net omits the one valid plan with an `acc` after a retire

- Where: `PlanRetireTest.lean` section 9 (choice of plans); `plan_layer_slice3_plan.md` "Also pinned" paragraph
  ("preservation in `step_init`, `step_acc`, `step_pub` ... the R-net follow-up ... now also instantiates
  them on concrete plans") and O4 ("RESOLVED"); record section "R regression net".
- What: `dead : Pub pc a -> not Live pc a -> M (place a) = none` and `retPub : Ret pc a -> Pub pc a` are
  vacuous whenever `Ret pc` is empty (`Live = Pub and not Ret`, so `Pub` plus `not Live` forces `Ret`). In
  all three net plans the retire is followed ONLY by a `pub` (`rtChain`/`rtMulti`: retire is command 4,
  then `pub` command 5; `rtFusedOk`: the retire is the last annotation of command 3, then `pub` command 4).
  So at every boundary before the retire the two fields hold vacuously, and the only non-vacuous
  preservation step the net exercises is `step_pub`. No `init` or `acc` runs while an address is retired.
- Actual: the existing VALID plan `rtNeighbour` (section 2: `retire [cAddr 0]` at command 3, then
  `acc [cOcc 1]`, then `pub [cAddr 2]`; `checkPlan = true` by `decide`) is exactly the acc-after-retire
  case and is not in the net. Nothing anywhere has an `init` after a retire, which is the shape the
  buffer-reuse slice (the stated reason for the net) will introduce. A reader of the plan paragraph or of
  "O4 RESOLVED" would believe `step_acc`/`step_init` preservation of `dead`/`retPub` is now exercised on a
  concrete run with a retired address present; it is not.
- Fix: add `rtNeighbour_valid` + `rtNeighbour_R_every_pc` (pc <= 6, same `interval_cases k <;> rfl`
  pattern) and read `dead` for `cAddr 0` at pc 5 (after the `acc`), plus an independent `rfl` example
  `chainMem rtNeighbour 5 (place (cAddr 0).addr) = none`. Reword the plan paragraph / O4 / record to say
  non-vacuous preservation is exercised through `step_pub` (and `step_acc` once `rtNeighbour` is added),
  and that no fixture has an `init` after a retire (left to the reuse slice).

### F2 [Minor] The "Honest limit" (and the section-9 header) both overstate and understate what the `R` instances can catch; the wipe probe's kill list omits the three instances

- Where: record "R regression net", the "Hand mutation probes ... Honest limit" paragraph; the section 9
  header comment in `PlanRetireTest.lean` ("so a change to `R` ... or to a step kernel that breaks them
  on a real plan fails here, not only in a distant proof").
- Overstatement: "the `R` instances ... will fail to compile if the reuse slice changes `R` in a way a
  concrete run no longer satisfies". If a concrete valid run does not satisfy a new `R`, the library
  lemmas (`step_R`, `step_R_command`, `R_start`) cannot be proved soundly, so the failure is in the
  library first; if they are `sorry`ed, the instances still compile (as the same sentence's first half
  says). Independently of the library, the instances fail only on shape/signature changes (fields
  `dead`/`retPub` renamed or removed, changed hypotheses of `step_R`/`step_R_command`/`Valid.stepOK`).
  The `#print axioms` lines would show `sorryAx`, but they only print; nothing fails on them.
- Understatement: "the independent computed checks are what make the net able to fail on its own" omits
  that the instances themselves carry computed checks: the `hstep` side goals (`interval_cases k <;> rfl`,
  "every step of the actual run returns `ok`") and validity by `decide` (`checkPlan_sound`/
  `checkPlanF_sound`). The controller's own wipe-everything probe proves it: `rnet_me.log` has
  `PlanRetireTest.lean:280:81`, `:284:81`, `:288:87` "Tactic `rfl` failed" (the three `*_R_every_pc`
  instances: the next `pub` is stuck because `execPub` requires `isSome`), in addition to the p0 example
  (`:336`) and the three `retire-net-*` rows. The record lists only the latter four.
- Fix: in the record, add the three instance kills to the wipe probe and restate the limit as: the
  instances fail on their own only if a step of the run stops returning `ok`, the plan stops being valid,
  or `R`'s/the step lemmas' shape changes; a semantic violation of `R` is caught by the library proofs (or
  masked by `sorry`). Adjust the section-9 header the same way.

### F3 [Minor] Probe naming: "the `rtChain` live-neighbour example" collides with the `retire-net-*-live-neighbour` rows

- Where: record, wipe probe sentence.
- What: the killed example is `chainMem rtChain 5 (place (cAddr 0).addr) = some 0` (point 0); the rows named
  `...-live-neighbour` check point 2. A reader cross-referencing names could think the `retire-net-chain`
  row was meant. Fix: say "the `rtChain` point-0 (`some 0`) example".

## Verified clean

- (a) Soundness of the net. `hn : π.commands.length = n` is not vacuous (used for `hlt`; closed by `rfl`
  with n = 6, 6, 5, matching the 6/6/5 commands of `rtChain` (lines 29-31), `rtMulti` (174-176),
  `rtFusedOk` (115-117)). `hstep` is not circular: `chainMem (k+1)` is `match stepPlan k (chainMem k) with
  | .ok M => M | _ => chainMem k`, so `stepPlan k (chainMem k) = .ok (chainMem (k+1))` holds by `rfl`
  iff the step actually returns `.ok` (a `.stuck`/`.semFail` gives mismatched constructors); confirmed
  empirically by the wipe probe killing all three instances at their `hstep`. `interval_cases k` over
  `k < n` covers every k. `chainMem` is the actual run: `stepPlan pc M = stepCommand pc M commands[pc]`,
  and `runFrom` iterates `stepCommand` with pc from 0 over `π.commands`, so the two coincide while every
  step is `ok`. `R_every_pc_F_of` uses `step_R_command`, whose conclusion is `π.R ... (pc+1)` with `R`
  indexed by `prefixAnn pc = (commands.take pc).flatten`, i.e. command boundaries; the per-annotation `ok`
  obligation comes from `FValid = expand.Valid` via `Valid.stepOK` at the expanded index. Conclusion covers
  every `pc <= n`. Axioms (rnet4.log 432-436): only `propext`, `Classical.choice`, `Quot.sound`; the 5
  printed theorems transitively cover all 10 new theorems.
- (b) Indices and facts. `rtChain`/`rtMulti`: retire is command 4, so `Ret 5` holds (decide over
  `prefixAnn 5`); `rtFusedOk`: retire inside command 3, so `Ret 4`. Addresses: `cAddr 1` for `rtChain`
  and `rtFusedOk`, `cAddr 0`/`cAddr 1` for `rtMulti` (its block is `[cAddr 0, cAddr 1]`). Conclusions
  match the doc comments (rtMulti/rtFused omit `Pub` from the conclusion but use `retPub` internally,
  as the record says).
- (c) Independent checks do not go through `R` (plain `rfl` on `chainMem` / `#eval check`). Memory at pc 5
  (pc 4 fused) equals the final row because `execPub` returns `M` unchanged: `retire-valid-chain`
  `[some 0, none, some 4]`, `retire-multi-distinct` `[none, none, some 4]`, `retire-fused-after-read`
  `[some 0, none, some 4]` (rnet4.log 408, 425, 416); new rows print `some 4` (429-431). Probe claims
  match the logs: no-op (`rnet_mc`) kills the 4 examples at 335/337/338/339; first-member-only
  (`rnet_ma`) kills only 338 (rtMulti point 1); wipe (`rnet_me`) kills 336 and the 3 rows (plus the
  instances, F2). The "3 + 1 is not kernel-`rfl`-normalisable" remark was not independently checked (no
  builds run).
- (d) Counts: `#eval check` rows sum 146 (18+8+7+23+13+24+12+7+1+4+21+8); `example|theorem` items sum 107
  (2+3+30+29+7+9+16+1+4+6); PlanRetireTest 24 rows, 18 examples, 29 - 18 = 11 theorems, 53 total.
  Snapshot SHA `aa882476` is the test commit. `git diff --stat main HEAD -- leanncd/LeanNCD
  leanncd/lakefile.toml` is empty (test-only). No `File.lean:NNN` citation in the three changed docs.
  No stale 235/143/92/35 counts remain in the path doc, spec or `Plan/AGENTS.md`; the older record lines
  calling O4 parked (129, 143, 154) are history, superseded by the new section's title.

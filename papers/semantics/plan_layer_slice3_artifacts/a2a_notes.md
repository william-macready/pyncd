# Slice 3 (buffer retirement), dispatch A2a notes

Scope: `Plan/Validity.lean`, `Plan/Run.lean`, `Plan/Correctness.lean` (under
`leanncd/LeanNCD/Semantics/Plan/`). Fusion, FusionCorrectness, Faults, tests NOT touched. No edits to
A1's modules (no bug found there).

## Per module

### Validity.lean
- `ReadyOK` now ranges over `π.Live pc a` (was `Pub`). Docstring updated.
- `Valid` gets field `retOK : ∀ pc B, π.commands[pc]? = some [.retire B] → π.RetOK pc B` (last field,
  after `ready`). Anonymous-constructor proofs of `Valid` must append it.
- `Valid.stepOK`: arm `| retire B => exact h.retOK pc B ha`.
- `checkRet (pc : Nat) (B : List (DefAddr P)) : Bool :=
     B.all fun x => decide (π.Live pc x.addr) && decide (P.output x.1.val = false)`.
- `checkReady` uses `decide (π.Live pc a)`.
- `checkAnn` arm `| .retire B => π.checkRet pc B`.
- New lemmas:
  `checkRet_sound {pc} {B} (h : π.checkRet pc B = true) : π.RetOK pc B`;
  `checkRet_complete {pc} {B} (h : π.RetOK pc B) : π.checkRet pc B = true`
  (both `simp only [checkRet, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]` then `exact h`).
- `checkAnn_acc_sound`/`_complete` unchanged in text (the `simp only` set just unfolds `checkReady`;
  `Live` matches definitionally through `ReadyOK`).
- `checkPlan_sound`: 8th `Valid` field `fun pc B ha => π.checkRet_sound (π.checkSteps_ann hst ha)`.
- `checkPlan_complete`: `retire B` arm via `checkRet_complete (h.retOK pc B hc)`.
- `checkPlan_nodup_redundant`: `retire B` arms (`simp [Ann.groups]` / `simp [Ann.blocks]`).
- `checkAccMat_of_rest`: `retire` arms in the two `cases` (publish-block case: `Ann.blocks`, init case:
  `Ann.inits`). Hypotheses UNCHANGED (still `hs h2c hinit hpub`); no retire hypothesis needed.
- `nodup_prefixAnn_flatMap`, `checkPlan_eq_core`, `fresh_of_nodup_flatMap`, `checkPlan_iff`: no change
  needed (generic in `f` / no case split).
- `checkPlan_iff : π.checkPlan = true ↔ π.Valid` still holds, the checker is still an exact decision
  procedure.

### Run.lean
- `readPub_isSome` takes `ha : π.Live pc a` (was `Pub`), uses `ha.pub` for `hR.published`.
- `step_not_stuck`: arm `| retire B => simp [stepCommand_single, execAnn]`.
- Nothing else changed: `execAnns_not_stuck` and `run_R` go through `step_not_stuck`/`step_R`;
  `run_R`'s `step_failed` call needs no retire case (A1 handled it inside `step_failed`; `cases hG`
  there is on the `acc` hypothesis form and compiled unchanged). `readPub_isSome` callers: only
  `step_not_stuck` in Run.lean (grep in Fusion*/Faults should be checked by A2b).

### Correctness.lean
- `Valid.order4`: arm `| retire B => cases hy`.
- NEW `live_output_of_valid {π} (hv : π.Valid) (t : {t : σ.Tensor // P.output t = true})
     (p : Coord (σ.signature t.val).axes) : π.Live π.commands.length ⟨t.val, p⟩`.
  Placed before the `variable [DecidableEq ...]` line (needs no instance), after `cov1_of_cov2_pubOrder`.
  Its type is exactly the `outs` hypothesis of `decode_of_R` (`∀ t p, π.Live pc ⟨t.val, p⟩` at
  `pc = π.commands.length`), so a caller passes `(live_output_of_valid hv)` directly.
  Proof: input output -> `live_input`; defined output -> Pub via `coverage2` (as in
  `complete_of_refState`), not Ret via `mem_prefixAnn` + `singleton` + `retOK` (member x retired at an
  index would have `P.output x.1.val = false`, but `x.1.val = t` and `P.output t = true`).
  (Used `mem_prefixAnn`, `hv.singleton`; did not need `prefixAnn_length` for the Ret half, only for Pub.)
- `terminal_adequacy`: the local `outs` (a `Pub` proof from `complete`) is deleted; calls
  `π.decode_of_R ops hR (live_output_of_valid hv)`. `hR.published`/`complete.2` no longer used there
  but `complete` is still used in the conclusion. Statement unchanged; `done_correct`, `failed_correct`,
  `done_or_failed`, `done_of_model`, `done_iff_model` unchanged and compile.

## Deviations
None from the brief. One tiny proof fix: `RetOK` is a `∀ x ∈ B, ...` so the `.2` projection goes on the
application `(hv.retOK i B hc x hxz).2`, not on `hv.retOK i B hc`.

## Builds
`bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd LeanNCD.Semantics.Plan.{Validity,Run,Correctness}`
-> `Build completed successfully (2964 jobs).`, `(2965 jobs).`, `(2966 jobs).` respectively. `rg sorry`
over the three files: no match. `#print axioms` for `checkRet_sound`, `checkRet_complete`,
`live_output_of_valid`: propext, Quot.sound only; `terminal_adequacy`: propext, Classical.choice,
Quot.sound. No new axiom.

## For A2b (Fusion, FusionCorrectness, Faults)
- Any anonymous-constructor `Valid` needs the new last field `retOK`. `ReadyOK`/`checkReady` are over
  `Live`, so `FValid`/`checkPlanF` ready-clauses become Live statements (via expansion they should be
  free, but check any hand-written `Pub` ready proof).
- `readPub_isSome` now needs `Live` (callers pass `hready` which is already Live).
- `decode_of_R` callers must pass `live_output_of_valid` (for `π.expand`'s validity, apply it to the
  expanded plan's `Valid`; length = `π.expand.commands.length`).
- `Ann` cases: `Valid.order4`-style `cases a` need a `retire` arm.

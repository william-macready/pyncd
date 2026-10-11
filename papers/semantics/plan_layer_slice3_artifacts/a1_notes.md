# Slice 3 (buffer retirement), dispatch A1 notes

Scope: `Plan/Syntax.lean`, `Plan/Memory.lean`, `Plan/Step.lean`, `Plan/Simulation.lean` (all under
`leanncd/LeanNCD/Semantics/Plan/`). Validity, Run, Correctness, Fusion*, Faults NOT touched.

Build: `bash leanncd/scripts/lake-build.sh <worktree>/leanncd LeanNCD.Semantics.Plan.Simulation`
-> `Build completed successfully (2963 jobs).` No `sorry` (rg over the 4 modules: no match), no new axiom
(every `#print axioms` line for the four modules lists only propext/Classical.choice/Quot.sound).
Tip: lake-build output is huge (replays); redirect to a file and `tail -n 1`, then `rg "error"`.

## Per module

### Syntax.lean
- `Ann.retire (B : List (DefAddr P))` (4th constructor).
- `Ann.rets : Ann P → List (DefAddr P)` (wildcard arm like groups/blocks/inits; groups/blocks/inits
  already had `| _ => []` so needed no new arm); `Ann.keys` gets `| .retire _ => []`;
  `keys_perm_aux` gets a `retire B` arm (same `simpa` as initZero).
- `retList (pc) := (π.prefixAnn pc).flatMap Ann.rets`.
- `Ret (pc) (a : Address σ) : Prop := a ∈ (π.retList pc).map DefAddr.addr`.
- `Live (pc) (a : Address σ) : Prop := π.Pub pc a ∧ ¬ π.Ret pc a`.
- Decidable instances for `Ret` and `Live` next to Pub/Mat (section Decidable).
- Lemmas: `ret_zero (a) : ¬ π.Ret 0 a`; `live_zero (a) : π.Live 0 a ↔ P.input a.1 = true`;
  `Live.pub (h : π.Live pc a) : π.Pub pc a`; `live_input (pc) (a) (h : P.input a.1 = true) : π.Live pc a`.
- `ret_succ` is in Simulation.lean next to `pub_succ` (that is where pub_succ/mat_succ live), not in Syntax.

### Memory.lean
- `SlotView pc (.pub a)` and `readPub` guard on `π.Live pc a`. `slotView_injective` repaired (`hp.1`).
- `postAnn _ (.retire _) = some c`; `postAnn_execution` retire arm (`⟨[], .nil _⟩`).
- `R` gets TWO new fields after `retain`:
  - `dead : ∀ a, π.Pub pc a → ¬ π.Live pc a → M (place a) = none`  (R5, as in the spec)
  - `retPub : ∀ a, π.Ret pc a → π.Pub pc a`  (R6, NOT in the spec; see Deviations)
- `R_start` proves both (`ret_zero`).
- `readPub_eq` CHANGED STATEMENT: now pointwise on live addresses:
  `readPub_eq (h : π.R ops η pc M c) {a} (ha : π.Live pc a) : π.readPub pc M a = c.published a`.
  (The old `readPub pc M = c.published` is false once a retired address keeps its ghost value in
  `c.published` but reads `none`.)
- `decode_of_R`: hypothesis `outs : ∀ t p, π.Live pc ⟨t.val, p⟩` (was Pub); conclusion unchanged.

### Step.lean
- `execRet (B : List (DefAddr P)) (M : Memory K σ) : Memory K σ :=
    B.foldl (fun M x => Function.update M (place x.addr) none) M`.
- `execAnn _ _ _ (.retire B) = .ok (execRet B M)`.
- `execAnn_prefix`: `hp` now compares `Live` (via `simp [Live, Pub, Ret, pubList, retList, h]`); the
  hypothesis `π.prefixAnn pc = π'.prefixAnn pc'` is unchanged (equal prefixAnn already gives both).

### Simulation.lean
- New in the `Succ` section: `ret_succ`, `pub_succ_of (hb : a.blocks = [])`, `ret_succ_of (hr : a.rets = [])`,
  `live_succ_of (hb) (hr)`. All take the `h : π.commands[pc]? = some [a]` first, as `pub_succ` does.
- `slotView_pub : SlotView pc (.pub b) = some (place b) ↔ π.Live pc b` (was Pub).
- `RetOK (pc) (B : List (DefAddr P)) : Prop := ∀ x ∈ B, π.Live pc x.addr ∧ P.output x.1.val = false`
  (flag shape: `P.output : σ.Tensor → Bool`, `P.output t = true` in Decode).
- `AnnOK` arm `.retire B => π.RetOK pc B`. `StepOK` needs no change (it quantifies over AnnOK).
- `postAnn_bookkeeping` retire arm.
- New helpers: `readPub_le (hR) (a) (v) (h : readPub pc M a = some v) : c.published a = some v`;
  `execRet_not_mem (B M) (h : ∀ x ∈ B, x.addr ≠ b) : execRet B M (place b) = M (place b)`;
  `execRet_mem (B M) (hy : y ∈ B) : execRet B M (place y.addr) = none`;
  `evalReady_of_le (p q : PartialStore) (hpq : ∀ a v, p a = some v → q a = some v) e γ
     (h : evalReady ops p e γ = .evaluated w) : evalReady ops q e γ = .evaluated w`;
  `delta_congr (h : ∀ x ∈ G, v x = w x) : delta P G v = delta P G w`.
- `step_retire {B} (hR) (hc) (hcmd : π.commands[pc]? = some [.retire B]) (ok : π.RetOK pc B) :
     π.refState ops η (pc+1) = some c ∧ π.R ops η (pc+1) (execRet B M) c ∧ Execution P ops [] (.running c) (.running c)`
  (same shape as `step_init`).
- `step_init`/`step_acc`/`step_pub` preserve `dead` and `retPub`. Their statements are unchanged.
- `step_acc` no longer rewrites with `readPub = c.published`: it shows readiness on `c.published` via
  `evalReady_of_le` + `readPub_le`, and equates the per-member values (`hvals`) and `delta` via `delta_congr`.
- `step_failed` uses `evalReady_of_le` the same way (statement unchanged; no ReadyOK needed).
- `step_R` has a `retire` arm; `step_failed` has a `retire` arm; `step_failed_no_model` unchanged.
- `AccOK` comment now says "read from Live". Statements of all other theorems unchanged.

## Deviations from the spec
1. Extra R field `retPub` (R6: `Ret pc a → Pub pc a`). Needed because `step_pub` must show a freshly
   published member is `Live` (so its `Ret` is false), and `step_init`/`step_acc` must show a retired
   address is not an unpublished write target. `R` has no memory of earlier steps' `RetOK`, so without
   it neither is derivable from `StepOK pc` alone. Cheap: every preservation proof is a one-liner.
2. `readPub_eq` statement changed (pointwise on Live) instead of staying an equality of functions;
   added `readPub_le` for the "no spurious values" direction used in `step_acc`/`step_failed`.
3. `step_acc` AccOK still has no readiness clause: that is derived from the run (`scanGroup` success)
   exactly as before, but through `evalReady_of_le` rather than through `readPub = published`.
4. `ret_succ` lives in Simulation.lean (with `pub_succ`), not Syntax.lean.

## Surprising
- Everything compiled first time except two tiny proof fixes (`Function.update_of_ne` argument order,
  a closed second `split_ifs` goal). `live_input` needed only `simp_all`.
- R5 (`dead`) was cheap (about 1 turn per step kernel); no need to drop it.

## What A2 must adapt (downstream; I did NOT edit these)
Full `LeanNCD` build stops at Validity (lake does not reach later modules). First errors:
- Validity.lean: `Alternative retire has not been provided` at lines 44, 241, 249, 354, 413, 425 and
  `Missing cases: (Ann.retire _)` at 127 (checkAnn). Needs `checkRet`, `RetOK` clause (`Valid.retOK`),
  `ReadyOK` over `Live`, `checkReady` over `Live`, `checkPlan_sound/complete/iff` arms. `Valid.stepOK`
  must produce `AnnOK` for `.retire`.
Known-to-break by reading (not compiled; lake stopped at Validity):
- Run.lean: `readPub_isSome` (line 54) takes `ha : π.Pub pc a` and uses `slotView_pub`; must become
  `Live` (and `hready` must be over `Live`). `step_not_stuck` `cases a` at line 77 needs a `retire` arm
  (`execAnn` is `.ok (execRet ..)`, never stuck). Also check lines ~108-185 for any `cases`.
- Correctness.lean: `cases a` at line 25 needs a `retire` arm; `decode_of_R ... outs` at line 74 now needs
  `∀ t p, π.Live pc ⟨t.val, p⟩` (needs the new lemma "Live at every output at pc = m" from
  `RetOK.2`: no retired member is an output, and outputs are Pub at m).
- Fusion.lean: `R_transport` (line 102-114) is an anonymous-constructor proof of `R`; needs `hret`
  (Ret iff from `prefixAnn` equality: `simp [Ret, retList, h]`), `hlive`, and the two new fields
  `dead`, `retPub`. `hsv` proof (`simp [SlotView, hpub, hmat]`) needs `Live`.
- FusionCorrectness.lean: line 56-59 (`readPub` equality via `Pub` iff) -> use `Live`/`Ret` iff
  (as `execAnn_prefix` in Step.lean now does); line 150 `decode_of_R ... outs` -> Live.
- Faults.lean: no constructor-case or readPub/SlotView sites found by grep; expected to follow
  Run/Correctness.
- The `LeanNCDTest` / fixture modules were not inspected.

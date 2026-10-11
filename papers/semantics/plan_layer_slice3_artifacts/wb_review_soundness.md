# Whole-branch review, soundness lens (Plan slice 3, buffer retirement, 097ebeff..ca512754)

Summary: no Critical or Important finding. No plan accepted by `checkPlan`/`checkPlanF` was found that
produces a wrong result, gets stuck, or breaks a theorem premise. Four Minor findings: one about how
complete the table is, two about fixture strength, one about a docstring label.

### F1 [Minor] Case x class table: "retire an unpublished address" is not always stuck; retiring before `initZero` is silently ignored
- Where: plan `plan_layer_slice3_plan.md`, case x class table, row "retire an unpublished address"
  (run-time effect "later `pub` `stuck`", silent "no (stuck, late)"); `execRet` @ `Plan/Step.lean`.
- What: what the run does depends on whether the slot is materialised yet. `execRet` on a slot that is
  still `none` (before `initZero`) does nothing. The later `initZero`/`acc`/`pub` then fill the slot as
  normal, and `execPub` checks the raw slot (`isSome`), not `Live`. If no later reader exists, the run
  ends `done` with the correct outputs. Only `checkPlan` rejects it (the `Pub` half of `RetOK`).
- Scenario: `scalarRole false`, plan `[[.retire [t2]], [.initZero [t1,t2]], [.acc [occ1]], [.pub [t1]],
  [.acc [occ2]], [.pub [t2]]]`. `checkPlan = false`. The run is `done` with memory `[7, 2, 3]` and
  decode `some 2`. The "retired" slot t2 holds 3 at the end, so R5's intent fails in this invalid
  run. With a later reader of the address, it is stuck at that reader instead (`Ret` persists, so
  `readPub` is `none`). Retiring an output before init gives the existing `retire-output` behaviour
  (`done`, decode `none`).
- Judgement: acceptable (no wrong output, and `Valid` rejects it). But the table row is incomplete:
  this is a third silently-ignored cell, besides `retire-output` and `retire-twice`. It has no fixture.
  Spec/plan: plan text after the table says "The two YES cells ... are the silently-ignored cells".

### F2 [Minor] No fixture retires a block of two or more distinct addresses; "first member only" variants of `execRet`/`checkRet` pass every row
- Where: `leanncd/test/Semantics/PlanRetireTest.lean` (every `.retire` block is a singleton, or `[cAddr 1, cAddr 1]`).
- What: `retire-dup-in-block` repeats one member. So any `execRet` that clears at least one member
  (head only, `B.tail` on a duplicate pair, last only) gives the same row. A `checkRet` that checks
  only `B.head?` would also accept or reject every fixture the same way.
- Scenario: replace `execRet B M` by `B.take 1 |>.foldl ...`. Every `#eval check` row in
  `PlanRetireTest` still matches. The mutant is killed only at the library proof `execRet_mem`. A
  head-only `checkRet` is killed at `checkRet_sound`.
- Judgement: the theorems still guarantee correctness (`step_retire`/`execRet_mem` hold for every
  member), so `Valid => correct` is unaffected. This is a gap in fixture strength only. The plan
  already records that S3-M2 (`B.tail`) "was not row-probed".

### F3 [Minor] Four fault rows add no retirement-specific pin
- Where: `PlanRetireTest.lean`, rows `retire-fault-at-retire`, `retire-fault-fused-at-retire`,
  `retire-fault-none`, `retire-fault-fused-none`.
- What: (a) `-at-retire` and `-fused-at-retire` report the pre-command memory, which is the same
  under a no-op `execRet` (the plan admits this for the first; the second has the same property:
  the whole command 3 is rolled back). They pin only position accounting (a `retire` takes one
  annotation position in `offset`/`faultIn`). (b) `-none` and `-fused-none` follow from the proved
  `runPlanE_noFault` plus rows `retire-valid-chain` / `retire-fused-after-read`. They can fail only
  if a proved theorem fails, so they repeat existing pins.
- Scenario: S3-M1 (`execRet` = identity) leaves rows (a) unchanged. Only `retire-fault-after-retire`
  among the fault rows shows the cleared slot.
- Judgement: acceptable. The plan's Review Focus item 5 says this for the unfused row; extend the
  note to the fused at-retire row, and say the `-none` rows are regression duplicates.

### F4 [Minor] `RetOK` docstring calls the whole `Live` conjunct "the safety half"; only its `Pub` half is consumed
- Where: `RetOK` docstring @ `leanncd/LeanNCD/Semantics/Plan/Simulation.lean:86`.
- What: `step_retire` uses only `(ok x hx).1.1` (the `Pub` half): in `notB` for `accSlot`
  preservation, and in `retPub`. The `not Ret` half is never used by any theorem. Plan D8 labels it
  diagnostic, and `retire-twice` confirms the run is harmless. The docstring "(published and not yet
  retired, the safety half)" can be read as saying the `not Ret` half carries safety.
- Scenario: none at run time. A reader who trusts the docstring might keep the `not Ret` check as
  load-bearing, or drop the `Pub` half thinking the two halves are equivalent.
- Judgement: a doc label only. It differs from D8's role table.

## Declined to judge
- Whether R5 (`dead`) has any role beyond being exported inside `R`: it is consumed only by its own
  preservation proofs (`step_*`, `R_transport`) and reaches users only as a conjunct of the `R` that
  `terminal_adequacy` returns. The design (sections 2 and 6) treats it as the starting point for the
  later reuse slice, so it is a deliberate guarantee and not dead weight. Whether it should be named
  as a diagnostic or guarantee clause in the role table is a documentation choice for the owner.
- I did not check the spec amendment in `papers/semantics/tensor_logic_semantics.md` line by line
  (outside the soundness lens).

## Verified clean
1. Valid clauses consumed / checker exactness: `retOK`'s `Pub` half is consumed by `step_retire`
   (`(ok x hx).1.1`, in `notB` and `retPub`). Not-an-output is consumed by `live_output_of_valid`
   (`(hv.retOK i B hc x hxz).2`), which feeds `terminal_adequacy` and `terminal_adequacy_F`.
   `ReadyOK` over `Live` is consumed by `step_not_stuck` (Run.lean:90-97, via `readPub_isSome` over
   `Live`). `checkRet` is literally `B.all (Live && output = false)`. `checkRet_sound` and
   `checkRet_complete` are `simp only [...]; exact h` both ways. `checkPlan_iff` is in the build log,
   axioms `[propext, Classical.choice, Quot.sound]`.
2. R5/R6 preservation: read in full in the Simulation.lean diff. `step_init`/`step_acc` touch only
   unpublished slots (`execInit_not_mem` with InitOK not-Pub; `commit_other` with `dest_not_pub`).
   `step_pub` derives `Ret pc b` from `Pub(pc+1)` and not-`Live(pc+1)` (Ret unchanged), gets
   `Pub pc b` from R6, and uses M' = M. `step_retire` splits on b in B (`execRet_mem`) and b not in B
   (`execRet_not_mem` with `dead`). R6 is never assumed from the plan: `R_start` makes it vacuous
   (`ret_zero`), `step_retire` gets it from `RetOK`'s `Pub` half, and the other steps keep it by
   `Pub` monotonicity (`pub_succ .inl`).
3. `readPub_eq`: the only uses are `decode_of_R` (pointwise, with `outs` over `Live`) and
   `readPub_le` (rg `readPub_eq` over LeanNCD and test). The remaining `funext` on `readPub` (in
   `execAnn_prefix` and `decode_prefix_congr`) compares two plans with equal prefixes over `Live`,
   not memory against `c.published`. The theorem statements of `terminal_adequacy`, `done_correct`
   and `step_R` are unchanged (Correctness diff touches proof bodies only).
4. `execRet` interactions: under `Valid`, members are `Pub`, so by `place_injective` they are never
   an accumulator slot (`SlotView .acc` needs not-`Pub`), an `addAt` destination (`dest_not_pub`
   plus R6), an `initZero` target (InitOK not-`Pub`), or a `pub` target (PubOK not-`Pub`). `execPub`'s
   raw `isSome` check therefore never meets a retired slot in a valid plan.
5. Fused: `FValid := π.expand.Valid` and `checkPlanF := π.expand.checkPlan`
   (FusionCorrectness.lean:24,31), so a fused retire is judged at its expanded position.
   `R_transport` carries `hret`/`hlive`/`dead`/`retPub` (Fusion.lean diff). `execAnns_R` goes
   through `step_R`, which has the `retire` case.
6. `Faults.lean` unchanged is justified: `runFromE` checks `faultIn` before `stepCommand` and is
   independent of the annotation kind (Faults.lean:60-69). A fault at a retire position returns the
   pre-command memory, and R holds there by the unchanged prefix induction. A targeted build of
   `LeanNCD.Semantics.Plan.Faults` succeeded (2969 jobs).
7. Case x class table: `retire-output` and `retire-twice` are the silent cells the plan names. Both
   are harmless at run time (no wrong value from a valid plan) and both are rejected by the checker.
   The one missing silent cell is F1.
8. Fixtures: the other rows pin something. `retire-valid-*`, `retire-read-after`,
   `retire-unpublished`, `retire-twice` and `retire-fault-after-retire` all show the cleared slot.
   `retire-output` decode `none` would flip under `readPub` over `Pub`. `retire-fused-before-read`
   pins the `Live` view. Weak rows: F2, F3.
9. Axioms: no added `sorry`/`admit`/`axiom`/`native_decide`/`implemented_by` in the diff
   (`git diff 097ebeff HEAD -G ... --stat -- leanncd` is empty). The replayed build log for the
   Faults target has 0 `sorryAx` (rg -c). The axiom lines of `ret_zero`, `live_input`, `readPub_le`,
   `execRet_mem`, `execRet_not_mem`, `evalReady_of_le`, `step_retire`, `step_R`, `step_failed`,
   `checkRet_sound`, `checkRet_complete`, `checkPlan_iff`, `live_output_of_valid`,
   `terminal_adequacy`, `terminal_adequacy_F` and `done_correct` are all subsets of
   `[propext, Classical.choice, Quot.sound]`.

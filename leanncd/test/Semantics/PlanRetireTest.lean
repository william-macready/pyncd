import Semantics.PlanFaultsTest

/- Slice 3 (buffer retirement) fixtures: `Ann.retire` on plans cloned from existing valid donors,
   each checked against BOTH the static checker (`checkPlan`, or `checkPlanF` for fused plans) and
   the run (`runPlan`, or `runPlanE` under a fault oracle). Every asserted value was observed from
   a real run; where behaviour differed from the spec's prediction it is noted at the row.
   Two program families, both donors of earlier slices:
   * `routed chainBody` (single NON-output tensor; statement 1 reads point 1, published by
     statement 0): the published intermediate is point 1, its last reader is occurrence 1.
   * `scalarRole false` (tensor 0 input, tensor 1 output, tensor 2 defined non-output): outputs
     still decode after tensor 2 is retired.
   Retiring an INPUT address is not expressible: `Ann.retire` takes `DefAddr P`, and a `DefAddr`
   names a defined (non-input) tensor, so there is no row for it (inputs are always live,
   `live_input`). -/

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

def chainRow (π : (routed chainBody).Plan) :=
  outcomeRow (π.runPlan ops (Start chainInput))
def chainRowE (π : (routed chainBody).Plan) (faults : Faults) :=
  eRow (π.runPlanE ops faults (Start chainInput))

/-! ### 1. valid retire after the last reader of a published intermediate -/

-- donor: chainPlan ([init; acc occ0; pub p1; acc occ1; pub p0,p2]) plus `retire p1` after the
-- last reader (occ 1, which reads point 1).
def rtChain : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0]], [.pub [cAddr 1]], [.acc [cOcc 1]],
    [.retire [cAddr 1]], [.pub [cAddr 0, cAddr 2]]]

#eval check "retire-valid-chain" (rtChain.checkPlan, chainRow rtChain)
  (true, ("done", 6, none, [some 0, none, some 4]))
-- the un-retired donor ends with the full row [0, 3, 4] (step-chain): only the retired slot differs.
#eval check "retire-valid-chain-donor" (chainPlan.checkPlan, chainRow chainPlan)
  (true, ("done", 5, none, [some 0, some 3, some 4]))
example : rtChain.checkPlan = true := by decide
theorem rtChain_valid : rtChain.Valid := rtChain.checkPlan_sound (by decide)

-- donor: sPlan false ([init 1,2; acc 1; pub 1; acc 2; pub 2]) plus `retire t2` last. Tensor 1 is
-- the output; it still decodes (to 2, as in `step-scalar-good`) and the retired slot is `none`.
def rtScalar : (scalarRole false).Plan :=
  scalarPlan false [[.initZero [sAddr false 1 rfl, sAddr false 2 rfl]], [.acc [sOcc false 1 rfl]],
    [.pub [sAddr false 1 rfl]], [.acc [sOcc false 2 rfl]], [.pub [sAddr false 2 rfl]],
    [.retire [sAddr false 2 rfl]]]

def sDecodeOf (π : (scalarRole false).Plan) : Option ℚ :=
  match π.runPlan ops (Start (scalarInput false)) with
  | .done pc M => (π.Decode pc M).map (fun out => out sOut ())
  | _ => none

#eval check "retire-valid-scalar" (rtScalar.checkPlan, sRowEP false rtScalar fun _ => none)
  (true, ("run:done", 6, none, [some 7, some 2, none]))
#eval check "retire-valid-scalar-decode" (sDecodeOf rtScalar, sDecodeOf (sPlan false))
  (some 2, some 2)
example : rtScalar.checkPlan = true := by decide

/-! ### 2. read after retire, and the accept-neighbour -/

-- donor: rtChain with the retire moved BEFORE the last reader: occ 1's footprint (point 1) is
-- retired when it runs: ReadyOK over Live fails, and the run is stuck at the reader (pc 4) with
-- the memory after the retire.
def rtReadAfter : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0]], [.pub [cAddr 1]], [.retire [cAddr 1]],
    [.acc [cOcc 1]], [.pub [cAddr 0, cAddr 2]]]

#eval check "retire-read-after" (rtReadAfter.checkPlan, chainRow rtReadAfter)
  (false, ("stuck", 4, none, [some 0, none, some 0]))
example : rtReadAfter.checkPlan = false := by decide

-- accept-neighbour (nearest legal program): retire a DIFFERENT published address (point 0, read by
-- nobody) at the same position; the later reader of point 1 keeps working.
def rtNeighbour : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0]], [.pub [cAddr 0, cAddr 1]], [.retire [cAddr 0]],
    [.acc [cOcc 1]], [.pub [cAddr 2]]]

#eval check "retire-neighbour-other-address" (rtNeighbour.checkPlan, chainRow rtNeighbour)
  (true, ("done", 6, none, [none, some 3, some 4]))
example : rtNeighbour.checkPlan = true := by decide

/-! ### 3. retire of an output address -/

-- donor: rtScalar with `retire t1` (the OUTPUT tensor) in place of `retire t2`, after pub 1.
-- RetOK's not-an-output clause rejects it (terminal role: Decode needs every output live); the run
-- itself is not stuck, and Decode over the retired output reads `none`.
def rtOutput : (scalarRole false).Plan :=
  scalarPlan false [[.initZero [sAddr false 1 rfl, sAddr false 2 rfl]], [.acc [sOcc false 1 rfl]],
    [.pub [sAddr false 1 rfl]], [.acc [sOcc false 2 rfl]], [.pub [sAddr false 2 rfl]],
    [.retire [sAddr false 1 rfl]]]

#eval check "retire-output"
  (rtOutput.checkPlan, sRowEP false rtOutput fun _ => none, sDecodeOf rtOutput)
  (false, ("run:done", 6, none, [some 7, none, some 3]), none)
example : rtOutput.checkPlan = false := by decide

/-! ### 4. retire of an unpublished accumulator -/

-- donor: sPlan false with `retire t2` between acc 2 and pub 2: address 2 is defined (initZero'd,
-- accumulated) but not yet in Pub, so the Pub half of Live (safety) rejects it. Observed (not the
-- predicted `done`): `execRet` does clear the live accumulator, so the later `pub` finds no value
-- in the slot and the run is `stuck` at the pub (pc 5) with the slot `none`.
def rtUnpub : (scalarRole false).Plan :=
  scalarPlan false [[.initZero [sAddr false 1 rfl, sAddr false 2 rfl]], [.acc [sOcc false 1 rfl]],
    [.pub [sAddr false 1 rfl]], [.acc [sOcc false 2 rfl]], [.retire [sAddr false 2 rfl]],
    [.pub [sAddr false 2 rfl]]]

#eval check "retire-unpublished" (rtUnpub.checkPlan, sRowEP false rtUnpub fun _ => none)
  (false, ("run:stuck", 5, none, [some 7, some 2, none]))
example : rtUnpub.checkPlan = false := by decide

/-! ### 5. fused command: retire after / before the read in ONE command -/

-- donor: rtChain with `acc occ1; retire p1` fused into one command (retire after the read).
def rtFusedOk : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0]], [.pub [cAddr 1]],
    [.acc [cOcc 1], .retire [cAddr 1]], [.pub [cAddr 0, cAddr 2]]]
-- the same two annotations in the other order (retire before the read, inside one command).
def rtFusedBad : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0]], [.pub [cAddr 1]],
    [.retire [cAddr 1], .acc [cOcc 1]], [.pub [cAddr 0, cAddr 2]]]

#eval check "retire-fused-after-read" (rtFusedOk.checkPlanF, chainRow rtFusedOk)
  (true, ("done", 5, none, [some 0, none, some 4]))
#eval check "retire-fused-before-read" (rtFusedBad.checkPlanF, chainRow rtFusedBad)
  (false, ("stuck", 3, none, [some 0, some 3, some 0]))
example : rtFusedOk.checkPlanF = true := by decide
example : rtFusedBad.checkPlanF = false := by decide

/-! ### 6. retire twice -/

-- donor: rtChain with a second `retire p1` as its own command. Live's not-retired half is a
-- diagnostic clause (re-retiring is harmless): the checker rejects, yet the run is `done`.
def rtTwice : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0]], [.pub [cAddr 1]], [.acc [cOcc 1]],
    [.retire [cAddr 1]], [.retire [cAddr 1]], [.pub [cAddr 0, cAddr 2]]]
-- duplicate inside ONE retire block: no duplicate check there (clearing is idempotent), so the
-- checker accepts.
def rtDupBlock : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0]], [.pub [cAddr 1]], [.acc [cOcc 1]],
    [.retire [cAddr 1, cAddr 1]], [.pub [cAddr 0, cAddr 2]]]

#eval check "retire-twice" (rtTwice.checkPlan, chainRow rtTwice)
  (false, ("done", 7, none, [some 0, none, some 4]))
#eval check "retire-dup-in-block" (rtDupBlock.checkPlan, chainRow rtDupBlock)
  (true, ("done", 6, none, [some 0, none, some 4]))
example : rtTwice.checkPlan = false := by decide
example : rtDupBlock.checkPlan = true := by decide

/-! ### 7. retire under the fault oracle (donor `PlanFaultsTest`) -/

-- rtChain (unfused): the retire is annotation/position 4. No fault: row 1's result. A fault AT the
-- retire: error at pc 4 with the pre-command memory (nothing retired yet: point 1 still holds 3).
#eval check "retire-fault-none" (chainRowE rtChain fun _ => none)
  ("run:done", 6, none, [some 0, none, some 4])
#eval check "retire-fault-at-retire" (chainRowE rtChain (faultAt 4 .allocFail))
  ("error", 4, some .allocFail, [some 0, some 3, some 4])
-- a fault AFTER the retire (position 5, the last pub): error at pc 5, the retired slot stays none.
#eval check "retire-fault-after-retire" (chainRowE rtChain (faultAt 5 .kernelFault))
  ("error", 5, some .kernelFault, [some 0, none, some 4])
-- fused donor `rtFusedOk` (expanded positions: init 0, acc 1, pub 2, acc 3, retire 4, pub 5): a
-- fault at the retire (position 4) rolls back the WHOLE command 3, so the memory is the one
-- after command 2 (point 2 not yet written).
#eval check "retire-fault-fused-at-retire" (chainRowE rtFusedOk (faultAt 4 .allocFail))
  ("error", 3, some .allocFail, [some 0, some 3, some 0])
#eval check "retire-fault-fused-none" (chainRowE rtFusedOk fun _ => none)
  ("run:done", 5, none, [some 0, none, some 4])

/-! ### 8. rows added for the deferred whole-branch review minors -/

-- donor: rtNeighbour. TWO DISTINCT addresses in one retire block, both after their last reader:
-- an `execRet` that only handled the first member would differ here. (A checker that looked only at
-- the first member would NOT: both members are legal; `retire-multi-second-unpublished` pins that side.)
def rtMulti : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0]], [.pub [cAddr 0, cAddr 1]], [.acc [cOcc 1]],
    [.retire [cAddr 0, cAddr 1]], [.pub [cAddr 2]]]

#eval check "retire-multi-distinct" (rtMulti.checkPlan, chainRow rtMulti)
  (true, ("done", 6, none, [none, none, some 4]))
example : rtMulti.checkPlan = true := by decide

-- donor: rtMulti with the retire block changed to `[p1, p2]`: the first member stays legal and the
-- second is point 2, accumulated but not yet
-- published: the Pub half of Live rejects the block through its second member only (a checker that
-- looked at the first member would accept). The run clears the live accumulator, so the later `pub`
-- is stuck (as in `retire-unpublished`).
def rtMultiBad : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0]], [.pub [cAddr 0, cAddr 1]], [.acc [cOcc 1]],
    [.retire [cAddr 1, cAddr 2]], [.pub [cAddr 2]]]

#eval check "retire-multi-second-unpublished" (rtMultiBad.checkPlan, chainRow rtMultiBad)
  (false, ("stuck", 5, none, [some 0, none, none]))
example : rtMultiBad.checkPlan = false := by decide

-- donor: sPlan false with `retire t2` placed BEFORE the `initZero` of t2: at run time clearing an
-- empty slot is a no-op, so the run ends `done` with every value correct (decode `some 2`); only the
-- checker rejects it (t2 is not yet published). A run-time-silent defect, pinned here.
def rtEarly : (scalarRole false).Plan :=
  scalarPlan false [[.retire [sAddr false 2 rfl]],
    [.initZero [sAddr false 1 rfl, sAddr false 2 rfl]], [.acc [sOcc false 1 rfl]],
    [.pub [sAddr false 1 rfl]], [.acc [sOcc false 2 rfl]], [.pub [sAddr false 2 rfl]]]

#eval check "retire-before-init"
  (rtEarly.checkPlan, sRowEP false rtEarly fun _ => none, sDecodeOf rtEarly)
  (false, ("run:done", 6, none, [some 7, some 2, some 3]), some 2)
example : rtEarly.checkPlan = false := by decide

-- donor: `retire-fault-fused-at-retire` with the fault moved to the LAST pub (position 5, command 4),
-- i.e. AFTER the command that fused the retire: unlike the fault rows at the retire itself, the
-- memory shown is the one after the fused command, so the retired slot must already be `none`
-- (a no-op `execRet` inside a fused command would show `some 3` there).
#eval check "retire-fault-fused-after-retire" (chainRowE rtFusedOk (faultAt 5 .kernelFault))
  ("error", 4, some .kernelFault, [some 0, none, some 4])

/-! ### 9. R at every command boundary (regression net for the `dead` and `retPub` fields of `R`)

   `R` is proved in general (`step_R`, `step_retire`), but `dead` (a retired slot is `none`) and
   `retPub` (a retired address is published) only ever appear inside those proofs. These theorems
   instantiate `R` on concrete retire plans at EVERY command boundary along the actual run and read the
   two fields off the intermediate states, so a change to `R` (the buffer-reuse slice will reshape it)
   or to a step kernel that breaks them on a real plan fails here, not only in a distant proof.
   The pattern is `PlanSimulationTest.tagged_R_every_pc`, with the per-step side conditions taken from
   `Valid` (`Valid.stepOK`) instead of written by hand. -/

/-- The memory after the first `n` commands of the actual run (a command that does not return `ok`
    leaves the memory unchanged; the lemmas below require every step to be `ok`). -/
def chainMem (π : (routed chainBody).Plan) : Nat → Memory Carrier declarations
  | 0 => Start chainInput
  | n + 1 =>
    match π.stepPlan ops n (chainMem π n) with
    | .ok M => M
    | _ => chainMem π n

/-- R holds at every boundary of a valid singleton plan whose run steps through `ok` memories. -/
theorem R_every_pc_of (π : (routed chainBody).Plan) (hv : π.Valid) (n : Nat)
    (hn : π.commands.length = n)
    (hstep : ∀ k, k < n → π.stepPlan ops k (chainMem π k) = .ok (chainMem π (k + 1))) :
    ∀ pc, pc ≤ n → ∃ c, π.refState ops chainInput pc = some c ∧
      π.R ops chainInput pc (chainMem π pc) c := by
  intro pc
  induction pc with
  | zero => intro _; exact ⟨_, rfl, π.R_start ops chainInput⟩
  | succ k ih =>
    intro hk
    obtain ⟨c, hc, hR⟩ := ih (by omega)
    have hlt : k < π.commands.length := by omega
    have hcmd0 : π.commands[k]? = some π.commands[k] := List.getElem?_eq_getElem hlt
    obtain ⟨a, ha⟩ := hv.singleton _ (List.mem_of_getElem? hcmd0)
    have hcmd : π.commands[k]? = some [a] := by rw [hcmd0, ha]
    obtain ⟨c', hc', hR', -⟩ :=
      step_R ops hR hc hcmd (hv.stepOK k a hcmd) (hstep k (by omega))
    exact ⟨c', hc', hR'⟩

/-- The same for a valid FUSED plan, at command boundaries (`R` is claimed there only). -/
theorem R_every_pc_F_of (π : (routed chainBody).Plan) (hv : π.FValid) (n : Nat)
    (hn : π.commands.length = n)
    (hstep : ∀ k, k < n → π.stepPlan ops k (chainMem π k) = .ok (chainMem π (k + 1))) :
    ∀ pc, pc ≤ n → ∃ c, π.refState ops chainInput pc = some c ∧
      π.R ops chainInput pc (chainMem π pc) c := by
  intro pc
  induction pc with
  | zero => intro _; exact ⟨_, rfl, π.R_start ops chainInput⟩
  | succ k ih =>
    intro hk
    obtain ⟨c, hc, hR⟩ := ih (by omega)
    have hlt : k < π.commands.length := by omega
    have hcmd : π.commands[k]? = some π.commands[k] := List.getElem?_eq_getElem hlt
    have hs : π.stepCommand ops k (chainMem π k) π.commands[k] = .ok (chainMem π (k + 1)) := by
      have h := hstep k (by omega)
      simpa [stepPlan, hcmd] using h
    obtain ⟨c', hc', hR', -⟩ := π.step_R_command ops hR hc hcmd
      (fun j a hj => Valid.stepOK hv _ a (π.expand_commands_getElem? (π.ann_getElem?_offset hcmd hj))) hs
    exact ⟨c', hc', hR'⟩

theorem rtMulti_valid : rtMulti.Valid := rtMulti.checkPlan_sound (by decide)
theorem rtFusedOk_valid : rtFusedOk.FValid := rtFusedOk.checkPlanF_sound (by decide)

theorem rtChain_R_every_pc : ∀ pc, pc ≤ 6 → ∃ c, rtChain.refState ops chainInput pc = some c ∧
    rtChain.R ops chainInput pc (chainMem rtChain pc) c :=
  R_every_pc_of rtChain rtChain_valid 6 rfl (by intro k hk; interval_cases k <;> rfl)

theorem rtMulti_R_every_pc : ∀ pc, pc ≤ 6 → ∃ c, rtMulti.refState ops chainInput pc = some c ∧
    rtMulti.R ops chainInput pc (chainMem rtMulti pc) c :=
  R_every_pc_of rtMulti rtMulti_valid 6 rfl (by intro k hk; interval_cases k <;> rfl)

theorem rtFusedOk_R_every_pc : ∀ pc, pc ≤ 5 → ∃ c, rtFusedOk.refState ops chainInput pc = some c ∧
    rtFusedOk.R ops chainInput pc (chainMem rtFusedOk pc) c :=
  R_every_pc_F_of rtFusedOk rtFusedOk_valid 5 rfl (by intro k hk; interval_cases k <;> rfl)

/-- After the retire of `rtChain` (command 4, so from pc 5 on) point 1 is retired: `retPub` makes it
    published, it is no longer live, and `dead` says its slot is free, which the concrete memory
    confirms. -/
theorem rtChain_retired_slot_free :
    ∃ c, rtChain.refState ops chainInput 5 = some c ∧
      rtChain.R ops chainInput 5 (chainMem rtChain 5) c ∧
      rtChain.Pub 5 (cAddr 1).addr ∧ ¬ rtChain.Live 5 (cAddr 1).addr ∧
      chainMem rtChain 5 (place (cAddr 1).addr) = none := by
  obtain ⟨c, hc, hR⟩ := rtChain_R_every_pc 5 (by omega)
  have hRet : rtChain.Ret 5 (cAddr 1).addr := by decide
  have hPub := hR.retPub _ hRet
  have hnl : ¬ rtChain.Live 5 (cAddr 1).addr := fun h => h.2 hRet
  exact ⟨c, hc, hR, hPub, hnl, hR.dead _ hPub hnl⟩

/-- A block of two distinct addresses: both are retired, no longer live and free at pc 5. -/
theorem rtMulti_retired_slots_free :
    ∃ c, rtMulti.refState ops chainInput 5 = some c ∧
      rtMulti.R ops chainInput 5 (chainMem rtMulti 5) c ∧
      (¬ rtMulti.Live 5 (cAddr 0).addr ∧ chainMem rtMulti 5 (place (cAddr 0).addr) = none) ∧
      (¬ rtMulti.Live 5 (cAddr 1).addr ∧ chainMem rtMulti 5 (place (cAddr 1).addr) = none) := by
  obtain ⟨c, hc, hR⟩ := rtMulti_R_every_pc 5 (by omega)
  have free : ∀ a : Fin 3, rtMulti.Ret 5 (cAddr a).addr →
      ¬ rtMulti.Live 5 (cAddr a).addr ∧ chainMem rtMulti 5 (place (cAddr a).addr) = none :=
    fun a hRet => by
      have hPub := hR.retPub _ hRet
      have hnl : ¬ rtMulti.Live 5 (cAddr a).addr := fun h => h.2 hRet
      exact ⟨hnl, hR.dead _ hPub hnl⟩
  exact ⟨c, hc, hR, free 0 (by decide), free 1 (by decide)⟩

/-- Fused: the retire sits inside command 3 (`[acc occ1, retire p1]`), so it has run at pc 4. -/
theorem rtFusedOk_retired_slot_free :
    ∃ c, rtFusedOk.refState ops chainInput 4 = some c ∧
      rtFusedOk.R ops chainInput 4 (chainMem rtFusedOk 4) c ∧
      ¬ rtFusedOk.Live 4 (cAddr 1).addr ∧
      chainMem rtFusedOk 4 (place (cAddr 1).addr) = none := by
  obtain ⟨c, hc, hR⟩ := rtFusedOk_R_every_pc 4 (by omega)
  have hRet : rtFusedOk.Ret 4 (cAddr 1).addr := by decide
  have hPub := hR.retPub _ hRet
  have hnl : ¬ rtFusedOk.Live 4 (cAddr 1).addr := fun h => h.2 hRet
  exact ⟨c, hc, hR, hnl, hR.dead _ hPub hnl⟩

-- Independent of `R` (so they can fail on their own): the memories the run actually computes have the
-- retired slots free and every live neighbour untouched. In `rtChain` at pc 5 the memory is
-- `[some 0, none, some 4]` (point 1 retired), as in the row `retire-valid-chain`. The slots holding `4`
-- (= 3 + 1 in exact rationals, which kernel `rfl` cannot normalise) are `#eval check` rows below.
example : chainMem rtChain 5 (place (cAddr 1).addr) = none := rfl
example : chainMem rtChain 5 (place (cAddr 0).addr) = some 0 := rfl
example : chainMem rtMulti 5 (place (cAddr 0).addr) = none := rfl
example : chainMem rtMulti 5 (place (cAddr 1).addr) = none := rfl
example : chainMem rtFusedOk 4 (place (cAddr 1).addr) = none := rfl

#eval check "retire-net-chain-live-neighbour" (chainMem rtChain 5 (place (cAddr 2).addr)) (some 4)
#eval check "retire-net-multi-live-neighbour" (chainMem rtMulti 5 (place (cAddr 2).addr)) (some 4)
#eval check "retire-net-fused-live-neighbour" (chainMem rtFusedOk 4 (place (cAddr 2).addr)) (some 4)

/-! `dead` and `retPub` hold trivially until something has been retired (`Live = Pub ∧ ¬ Ret`), so the
   steps that matter are the ones that run AFTER a retire. `rtNeighbour` has an `acc` after its retire;
   `rtInitAfter` has an `initZero` after its retire, the shape the buffer-reuse slice will introduce. -/

-- donor: rtNeighbour. Retire p0 (command 3), THEN `initZero [p2]` (command 4), then the accumulation
-- into p2 and its publication: the `init` and `acc` kernels run with a retired slot present.
def rtInitAfter : (routed chainBody).Plan :=
  unitPlan [[.initZero [cAddr 0, cAddr 1]], [.acc [cOcc 0]], [.pub [cAddr 0, cAddr 1]],
    [.retire [cAddr 0]], [.initZero [cAddr 2]], [.acc [cOcc 1]], [.pub [cAddr 2]]]

#eval check "retire-init-after-retire" (rtInitAfter.checkPlan, chainRow rtInitAfter)
  (true, ("done", 7, none, [none, some 3, some 4]))
example : rtInitAfter.checkPlan = true := by decide

theorem rtNeighbour_valid : rtNeighbour.Valid := rtNeighbour.checkPlan_sound (by decide)
theorem rtInitAfter_valid : rtInitAfter.Valid := rtInitAfter.checkPlan_sound (by decide)

theorem rtNeighbour_R_every_pc : ∀ pc, pc ≤ 6 → ∃ c, rtNeighbour.refState ops chainInput pc = some c ∧
    rtNeighbour.R ops chainInput pc (chainMem rtNeighbour pc) c :=
  R_every_pc_of rtNeighbour rtNeighbour_valid 6 rfl (by intro k hk; interval_cases k <;> rfl)

theorem rtInitAfter_R_every_pc : ∀ pc, pc ≤ 7 → ∃ c, rtInitAfter.refState ops chainInput pc = some c ∧
    rtInitAfter.R ops chainInput pc (chainMem rtInitAfter pc) c :=
  R_every_pc_of rtInitAfter rtInitAfter_valid 7 rfl (by intro k hk; interval_cases k <;> rfl)

/-- `dead` and `retPub` read off the state AFTER a later `acc` (command 4 of `rtNeighbour`, so pc 5). -/
theorem rtNeighbour_dead_after_acc :
    ∃ c, rtNeighbour.refState ops chainInput 5 = some c ∧
      rtNeighbour.R ops chainInput 5 (chainMem rtNeighbour 5) c ∧
      ¬ rtNeighbour.Live 5 (cAddr 0).addr ∧ chainMem rtNeighbour 5 (place (cAddr 0).addr) = none := by
  obtain ⟨c, hc, hR⟩ := rtNeighbour_R_every_pc 5 (by omega)
  have hRet : rtNeighbour.Ret 5 (cAddr 0).addr := by decide
  have hPub := hR.retPub _ hRet
  have hnl : ¬ rtNeighbour.Live 5 (cAddr 0).addr := fun h => h.2 hRet
  exact ⟨c, hc, hR, hnl, hR.dead _ hPub hnl⟩

/-- The same after a later `initZero` (command 4, pc 5) and after the following `acc` (command 5, pc 6). -/
theorem rtInitAfter_dead_after_init_and_acc :
    ∀ pc, 5 ≤ pc → pc ≤ 6 → ∃ c, rtInitAfter.refState ops chainInput pc = some c ∧
      rtInitAfter.R ops chainInput pc (chainMem rtInitAfter pc) c ∧
      ¬ rtInitAfter.Live pc (cAddr 0).addr ∧
      chainMem rtInitAfter pc (place (cAddr 0).addr) = none := by
  intro pc h5 h6
  obtain ⟨c, hc, hR⟩ := rtInitAfter_R_every_pc pc (by omega)
  have hRet : rtInitAfter.Ret pc (cAddr 0).addr := by
    interval_cases pc <;> decide
  have hPub := hR.retPub _ hRet
  have hnl : ¬ rtInitAfter.Live pc (cAddr 0).addr := fun h => h.2 hRet
  exact ⟨c, hc, hR, hnl, hR.dead _ hPub hnl⟩

-- Independent of `R`: p0 stays free while the later `init` and `acc` kernels run, and they did run.
example : chainMem rtNeighbour 5 (place (cAddr 0).addr) = none := rfl
example : chainMem rtInitAfter 5 (place (cAddr 0).addr) = none := rfl
example : chainMem rtInitAfter 6 (place (cAddr 0).addr) = none := rfl
example : chainMem rtInitAfter 4 (place (cAddr 2).addr) = none := rfl
example : chainMem rtInitAfter 5 (place (cAddr 2).addr) = some 0 := rfl
#eval check "retire-net-neighbour-acc-ran" (chainMem rtNeighbour 5 (place (cAddr 2).addr)) (some 4)
#eval check "retire-net-init-after-acc-ran" (chainMem rtInitAfter 6 (place (cAddr 2).addr)) (some 4)

#print axioms R_every_pc_of
#print axioms R_every_pc_F_of
#print axioms rtChain_retired_slot_free
#print axioms rtMulti_retired_slots_free
#print axioms rtFusedOk_retired_slot_free
#print axioms rtNeighbour_dead_after_acc
#print axioms rtInitAfter_dead_after_init_and_acc

end LeanNCD.Semantics.PlanFixtures

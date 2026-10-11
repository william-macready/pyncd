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

end LeanNCD.Semantics.PlanFixtures

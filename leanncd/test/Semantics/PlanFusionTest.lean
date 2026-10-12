import Semantics.PlanStepTest

/- PROTOTYPE (slice 2, P1): hand-checked fused fixtures, cloned from PlanStepTest.
   Each fused plan is a singleton plan of PlanStepTest with commands merged. -/

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

/-! ### reciprocal(2)+reciprocal(4): [initZero; acc; pub] fused into ONE command -/

def pPlanFused (n : Nat) (body) : (program n body).Plan :=
  unitPlan [[.initZero (pBlock n body), .acc ((List.finRange n).map (pOcc n body)),
    .pub (pBlock n body)]]
/-- Only acc and pub fused (Section 32.3's accumulate-and-publish kernel). -/
def pPlanAP (n : Nat) (body) : (program n body).Plan :=
  unitPlan [[.initZero (pBlock n body)], [.acc ((List.finRange n).map (pOcc n body)),
    .pub (pBlock n body)]]
def pRunF (n : Nat) (body) :=
  (pPlanFused n body).runPlan ops ((pPlanFused n body).Start (pInput n body))
def pRunAP (n : Nat) (body) :=
  (pPlanAP n body).runPlan ops ((pPlanAP n body).Start (pInput n body))

-- singleton (PlanStepTest) gives ("done", 3, none, [3/4, 0, 0]); fused: same memory, pc = #commands.
#eval check "fused-reciprocal-all" (outcomeRow (pRunF 2 reciprocalBody))
  ("done", 1, none, [some (3 / 4), some 0, some 0])
#eval check "fused-reciprocal-acc-pub" (outcomeRow (pRunAP 2 reciprocalBody))
  ("done", 2, none, [some (3 / 4), some 0, some 0])

-- failureAfterBody: singleton run reports ("failed", 1, (1,0), [0,0,0]) (memory after initZero).
-- Fused: the WHOLE command is rolled back, so the memory is the pre-command (Start) memory.
#eval check "fused-failure-after" (outcomeRow (pRunF 2 failureAfterBody))
  ("failed", 0, some (1, 0), [none, none, none])
-- acc+pub fused after a separate initZero: pre-command memory is the post-initZero one.
#eval check "fused-failure-after-ap" (outcomeRow (pRunAP 2 failureAfterBody))
  ("failed", 1, some (1, 0), [some 0, some 0, some 0])

/-! ### scalarRole: intra-command dependency (annotation 3 reads what annotation 2 published) -/

def sPlanFused (bad : Bool) : (scalarRole bad).Plan :=
  scalarPlan bad [[.initZero [sAddr bad 1 rfl, sAddr bad 2 rfl]],
    [.acc [sOcc bad 1 rfl], .pub [sAddr bad 1 rfl], .acc [sOcc bad 2 rfl], .pub [sAddr bad 2 rfl]]]
def sRunF (bad : Bool) := (sPlanFused bad).runPlan ops ((sPlanFused bad).Start (scalarInput bad))
def sRowF (bad : Bool) : String × Nat × Option Nat × List (Option ℚ) :=
  let row (M : Memory Carrier (sPlanFused bad).allocation) :=
    [readSlot (sPlanFused bad).allocation M ⟨0, ()⟩,
      readSlot (sPlanFused bad).allocation M ⟨1, ()⟩,
      readSlot (sPlanFused bad).allocation M ⟨2, ()⟩]
  match sRunF bad with
  | .done pc M => ("done", pc, none, row M)
  | .failed o pc M => ("failed", pc, some o.1.val.val, row M)
  | .stuck pc M => ("stuck", pc, none, row M)

-- singleton: good ("done", 5, [7,2,3]); bad ("failed", 3, some 2, [7,2,0]).
#eval check "fused-scalar-good" (sRowF false) ("done", 2, none, [some 7, some 2, some 3])
-- bad: statement 2 fails; the committed accumulate of statement 1 is rolled back with the command.
#eval check "fused-scalar-bad" (sRowF true) ("failed", 1, some 2, [some 7, some 0, some 0])

/-! ### the checker sees fused plans only through `expand` (static) -/

-- mis-fused: pub BEFORE acc inside the command.
def pPlanMisFused (n : Nat) (body) : (program n body).Plan :=
  unitPlan [[.initZero (pBlock n body), .pub (pBlock n body),
    .acc ((List.finRange n).map (pOcc n body))]]

#eval check "fused-expand-valid" (pPlanFused 2 reciprocalBody).expand.checkPlan true
#eval check "fused-expand-valid-ap" (pPlanAP 2 reciprocalBody).expand.checkPlan true
#eval check "misfused-expand-rejected" (pPlanMisFused 2 reciprocalBody).expand.checkPlan false
-- slice-1 checker on the fused plan: only checkSingleton rejects; checkSteps is VACUOUSLY true
-- on the mis-fused command (the silently-ignored cell), while expanded checkSteps is false.
#eval check "misfused-slice1-checkSteps-vacuous"
  ((pPlanMisFused 2 reciprocalBody).checkSteps, (pPlanMisFused 2 reciprocalBody).expand.checkSteps)
  (true, false)
-- the run of the mis-fused plan is NOT detected (N4): same value, `done`.
#eval check "misfused-run-undetected"
  (outcomeRow ((pPlanMisFused 2 reciprocalBody).runPlan ops
    ((pPlanMisFused 2 reciprocalBody).Start (pInput 2 reciprocalBody))))
  ("done", 1, none, [some (3 / 4), some 0, some 0])

/-! ### T2 additions: the step, equality with the expansion, empty commands, two accumulates -/

-- (1) One fused step: `initZero block; acc group` as a single command from `Start`.
#eval check "fused-step-success"
  (stepRow (fused.stepCommand ops 0 (fused.Start η0) [.initZero block, .acc group])) ("ok", [some 0, some 14, some 0])

-- (4) A fused plan and its expansion (all singleton) end on the same memory; only pc differs.
def rowOf {P : Program Carrier declarations registry} {A : Allocation P}
    (out : PlanOutcome P A) : List (Option ℚ) :=
  (outcomeRow out).2.2.2
#eval check "fused-vs-expand-reciprocal"
  (rowOf ((pPlanFused 2 reciprocalBody).runPlan ops
     ((pPlanFused 2 reciprocalBody).Start (pInput 2 reciprocalBody))),
   rowOf ((pPlanFused 2 reciprocalBody).expand.runPlan ops
     ((pPlanFused 2 reciprocalBody).expand.Start (pInput 2 reciprocalBody))),
   finalPc ((pPlanFused 2 reciprocalBody).expand.runPlan ops
     ((pPlanFused 2 reciprocalBody).expand.Start (pInput 2 reciprocalBody))))
  ([some (3 / 4), some 0, some 0], [some (3 / 4), some 0, some 0], 3)
#eval check "fused-vs-expand-scalar"
  ((sRowF false).2.2.2,
   (sPlanFused false).expand.runPlan ops ((sPlanFused false).expand.Start (scalarInput false)) |> fun out =>
     let row (M : Memory Carrier (sPlanFused false).allocation) :=
       [readSlot (sPlanFused false).allocation M ⟨0, ()⟩,
         readSlot (sPlanFused false).allocation M ⟨1, ()⟩,
         readSlot (sPlanFused false).allocation M ⟨2, ()⟩]
     row (finalMemory out))
  ([some 7, some 2, some 3], [some 7, some 2, some 3])

-- (5) Empty commands inside a fused plan are no-ops (D16): `step_R_command` covers `[]`
-- (`cmd.length = 0`, no annotation obligations).
def fusedEmpty : taggedOut.Plan :=
  unitPlan [[], [.initZero block, .acc group], [], [.pub block], []]
#eval check "fused-with-empty-commands" (outcomeRow (fusedEmpty.runPlan ops (fusedEmpty.Start η0)))
  ("done", 5, none, [some 0, some 14, some 0])
#eval check "empty-step-is-identity"
  (stepRow (fused.stepCommand ops 0 initMem []))
  ("ok", [some 0, some 0, some 0])

-- (6) Two accumulates of DIFFERENT tensors in one command (tensor 2 reads the published
-- tensor 1, so the publication sits between them).
def sPlanTwoAcc (bad : Bool) : (scalarRole bad).Plan :=
  scalarPlan bad [[.initZero [sAddr bad 1 rfl, sAddr bad 2 rfl]],
    [.acc [sOcc bad 1 rfl], .pub [sAddr bad 1 rfl], .acc [sOcc bad 2 rfl]],
    [.pub [sAddr bad 2 rfl]]]
def sRowTwo (bad : Bool) : List (Option ℚ) :=
  let row (M : Memory Carrier (sPlanTwoAcc bad).allocation) :=
    [readSlot (sPlanTwoAcc bad).allocation M ⟨0, ()⟩,
      readSlot (sPlanTwoAcc bad).allocation M ⟨1, ()⟩,
      readSlot (sPlanTwoAcc bad).allocation M ⟨2, ()⟩]
  row (finalMemory ((sPlanTwoAcc bad).runPlan ops ((sPlanTwoAcc bad).Start (scalarInput bad))))
#eval check "fused-two-acc-different-tensors"
  (sRowTwo false, finalPc ((sPlanTwoAcc false).runPlan ops ((sPlanTwoAcc false).Start (scalarInput false))))
  ([some 7, some 2, some 3], 3)
#eval check "fused-two-acc-different-tensors-bad"
  (sRowTwo true, finalPc ((sPlanTwoAcc true).runPlan ops ((sPlanTwoAcc true).Start (scalarInput true))))
  ([some 7, some 0, some 0], 1)

end LeanNCD.Semantics.PlanFixtures

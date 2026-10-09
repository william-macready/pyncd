import Semantics.PlanFixtures

/- Observed-value checks for the concrete plan step (spec 30.1): runPlan on
   one plan per donor program, compared with the reference executor's `run`,
   plus one invalid plan per class. -/

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

/-- Kind, stopping pc, failing occurrence (statement, valuation), raw slot row. -/
def outcomeRow {P : Program Carrier declarations registry} (out : PlanOutcome P) :
    String × Nat × Option (Nat × Nat) × List (Option ℚ) :=
  let row (M : Memory Carrier declarations) :=
    [M (place ⟨(), point 0⟩), M (place ⟨(), point 1⟩), M (place ⟨(), point 2⟩)]
  match out with
  | .done pc M => ("done", pc, none, row M)
  | .failed o pc M => ("failed", pc, some (o.2.1.val, o.2.2.val.val), row M)
  | .stuck pc M => ("stuck", pc, none, row M)

def finalMemory {P : Program K σ r} : PlanOutcome P → Memory K σ
  | .done _ M | .failed _ _ M | .stuck _ M => M

def finalPc {P : Program K σ r} : PlanOutcome P → Nat
  | .done pc _ | .failed _ pc _ | .stuck pc _ => pc

/-! ### taggedOut: [initZero p0..p2; acc group; pub p0..p2] -/

def taggedRun := plan.runPlan ops (Start η0)

#eval check "step-tagged-run" (outcomeRow taggedRun)
  ("done", 3, none, [some 0, some 14, some 0])
#eval check "step-tagged-decode-vs-run"
  ((decodeRow (plan.Decode 3 (finalMemory taggedRun))).map (·.map some),
    (taggedResult.outcome.kind, vectorStore (snapshot taggedResult.outcome)))
  (some [some 0, some 14, some 0], ("complete", [some 0, some 14, some 0]))

-- Per-pc concrete states versus refState, observed with stepPlan.
def taggedTrace : List (Option (List (Option ℚ))) :=
  let m1 := match plan.stepPlan ops 0 (Start η0) with | .ok M => some M | _ => none
  let m2 := m1.bind (fun M => match plan.stepPlan ops 1 M with | .ok M => some M | _ => none)
  let m3 := m2.bind (fun M => match plan.stepPlan ops 2 M with | .ok M => some M | _ => none)
  [some (Start η0), m1, m2, m3].map (fun m => m.map (fun M =>
    [M (place (addr 0).addr), M (place (addr 1).addr), M (place (addr 2).addr)]))
#eval check "step-tagged-trace" taggedTrace
  [some [none, none, none], some [some 0, some 0, some 0],
   some [some 0, some 14, some 0], some [some 0, some 14, some 0]]

/-! ### Two-statement donors over `program n body` -/

def pOcc (n : Nat) (body) (s : Fin n) : OccRef (program n body) := ⟨⟨(), rfl⟩, tag n body s⟩
def pAddr (n : Nat) (body) (i : Fin 3) : DefAddr (program n body) := ⟨⟨(), rfl⟩, point i⟩
def pBlock (n : Nat) (body) : List (DefAddr (program n body)) := [0, 1, 2].map (pAddr n body)
def pPlan (n : Nat) (body) : (program n body).Plan :=
  unitPlan [[.initZero (pBlock n body)], [.acc ((List.finRange n).map (pOcc n body))],
    [.pub (pBlock n body)]]
def pInput (n : Nat) (body) := noInput (program n body) (fun _ => rfl)
def pRun (n : Nat) (body) := (pPlan n body).runPlan ops (Start (pInput n body))

-- reciprocal(2) + reciprocal(4) collected = 3/4, not reciprocal(2 + 4) = 1/6.
#eval check "step-reciprocal" (outcomeRow (pRun 2 reciprocalBody), summarize 2 reciprocalBody)
  (("done", 3, none, [some (3 / 4), some 0, some 0]),
    ("complete", 5, [some (3 / 4), some 0, some 0], 0))
#eval check "step-reciprocal-readview"
  ([0, 1, 2].map (fun i => (pPlan 2 reciprocalBody).readPub 3
    (finalMemory (pRun 2 reciprocalBody)) (pAddr 2 reciprocalBody i).addr))
  [some (3 / 4), some 0, some 0]

-- failureAfterBody: lit 2 then reciprocal(0), both into point 0. The
-- transactional kernel fails on statement 1 with NOTHING committed.
def failureRefRow : String × Option (Nat × Nat) :=
  match failureAfterResult.outcome with
  | .failed _ o _ => ("failed", some (o.1.val, o.2.val.val))
  | out => (out.kind, none)
#eval check "step-failure-after" (outcomeRow (pRun 2 failureAfterBody), failureRefRow)
  (("failed", 1, some (1, 0), [some 0, some 0, some 0]), ("failed", some (1, 0)))

/-! ### scalarRole: input 0, defined 1 (output) and 2 -/

def sAddr (bad : Bool) (t : Fin 3) (h : (scalarRole bad).input t = false) :
    DefAddr (scalarRole bad) := ⟨⟨t, h⟩, ()⟩
def sOcc (bad : Bool) (t : Fin 3) (h : (scalarRole bad).input t = false) :
    OccRef (scalarRole bad) := ⟨⟨t, h⟩, ⟨0, ⟨0, rfl⟩⟩⟩
def sPlan (bad : Bool) : (scalarRole bad).Plan :=
  scalarPlan bad [[.initZero [sAddr bad 1 rfl, sAddr bad 2 rfl]], [.acc [sOcc bad 1 rfl]],
    [.pub [sAddr bad 1 rfl]], [.acc [sOcc bad 2 rfl]], [.pub [sAddr bad 2 rfl]]]
def sRun (bad : Bool) := (sPlan bad).runPlan ops (Start (scalarInput bad))
def sRow (bad : Bool) : String × Nat × Option Nat × List (Option ℚ) :=
  let row (M : Memory Carrier scalarDeclarations) :=
    [M (place ⟨0, ()⟩), M (place ⟨1, ()⟩), M (place ⟨2, ()⟩)]
  match sRun bad with
  | .done pc M => ("done", pc, none, row M)
  | .failed o pc M => ("failed", pc, some o.1.val.val, row M)
  | .stuck pc M => ("stuck", pc, none, row M)
def sRefRow (bad : Bool) : String × Option Nat :=
  match (scalarResult bad).outcome with
  | .failed t _ _ => ("failed", some t.val.val)
  | out => (out.kind, none)
def sOut : {t : scalarDeclarations.Tensor // (scalarRole false).output t = true} := ⟨1, rfl⟩
def sDecode : Option ℚ :=
  ((sPlan false).Decode 5 (finalMemory (sRun false))).map (fun out => out sOut ())

#eval check "step-scalar-bad" (sRow true, sRefRow true)
  (("failed", 3, some 2, [some 7, some 2, some 0]), ("failed", some 2))
#eval check "step-scalar-good" (sRow false, sDecode, sRefRow false)
  (("done", 5, none, [some 7, some 2, some 3]), some 2, ("complete", none))

-- Validated Start mirrors runValidated's input check (donor expectations).
def startRow (η : InputBinding (K := Carrier) (σ := scalarDeclarations)) : String × Nat :=
  match (scalarPlan false []).startValidated η with
  | .error t => ("error", t.val)
  | .ok _ => ("ok", 99)
#eval check "step-start-validated"
  [startRow scalarBinding, startRow (fun _ => none), startRow extraDefined,
    startRow simultaneous]
  [("ok", 99), ("error", 0), ("error", 1), ("error", 0)]

/-! ### routed chainBody: statement 1 reads point 1 (published) and adds 1 -/

def cOcc (s : Fin 2) : OccRef (routed chainBody) := ⟨⟨(), rfl⟩, ⟨s, ⟨0, rfl⟩⟩⟩
def cAddr (i : Fin 3) : DefAddr (routed chainBody) := ⟨⟨(), rfl⟩, point i⟩
def cAll : List (DefAddr (routed chainBody)) := [cAddr 0, cAddr 1, cAddr 2]
def chainPlan : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 0]], [.pub [cAddr 1]], [.acc [cOcc 1]],
    [.pub [cAddr 0, cAddr 2]]]
-- Reading an accumulator that is not yet published: the read view hides it.
def chainEarly : (routed chainBody).Plan :=
  unitPlan [[.initZero cAll], [.acc [cOcc 1]], [.acc [cOcc 0]], [.pub cAll]]

#eval check "step-chain"
  (outcomeRow (chainPlan.runPlan ops (Start chainInput)),
    chainResult.outcome.kind, vectorStore (snapshot chainResult.outcome))
  (("done", 5, none, [some 0, some 3, some 4]), "complete", [some 0, some 3, some 4])
#eval check "invalid-read-unpublished"
  (outcomeRow (chainEarly.runPlan ops (Start chainInput)))
  ("stuck", 1, none, [some 0, some 0, some 0])

/-! ### Invalid plans: runPlan does not check validity -/

-- Publish before accumulate: the run completes and decodes 14, but the
-- reference post-state at pc 2 does not exist (fiber premise fails).
def earlyStep : taggedOut.Plan := unitPlan [[.initZero block], [.pub block], [.acc group]]
#eval check "invalid-publish-before-acc"
  (outcomeRow (earlyStep.runPlan ops (Start η0)), (earlyStep.refState ops η0 2).isSome)
  (("done", 3, none, [some 0, some 14, some 0]), false)

-- Missing initZero: the accumulate kernel has no slot to add into.
def noInit : taggedOut.Plan := unitPlan [[.acc group], [.pub block]]
#eval check "invalid-missing-init" (outcomeRow (noInit.runPlan ops (Start η0)))
  ("stuck", 0, none, [none, none, none])

-- Missing initZero for the empty-fiber coordinates only (N1): publish is stuck.
def partialInit : taggedOut.Plan := unitPlan [[.initZero [addr 1]], [.acc group], [.pub block]]
#eval check "invalid-missing-init-empty-fiber" (outcomeRow (partialInit.runPlan ops (Start η0)))
  ("stuck", 2, none, [none, some 14, none])

-- One occurrence in two groups: counted twice (16); reference post-state at pc 3 fails.
def dupGroup : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc group], [.acc [occ 0 0]], [.pub block]]
#eval check "invalid-duplicate-member"
  (outcomeRow (dupGroup.runPlan ops (Start η0)), (dupGroup.refState ops η0 3).isSome)
  (("done", 4, none, [some 0, some 16, some 0]), false)

-- A fused (non-singleton) command is stuck in slice 1.
def fused : taggedOut.Plan := unitPlan [[.initZero block, .acc group], [.pub block]]
#eval check "invalid-fused" (outcomeRow (fused.runPlan ops (Start η0)))
  ("stuck", 0, none, [none, none, none])

end LeanNCD.Semantics.PlanFixtures

import Semantics.PlanRunTest

/- Theorem 31.3 comparison fixtures (A3b): runPlan versus the reference
   executor's `run` on every valid fixture plan. Done cases assert equal
   published/decoded values; failing cases assert "both fail". The failure
   snapshot is recorded, not compared (D5: the plan's acc kernel is
   transactional, the executor's snapshot is not). -/

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

/-- Plan side: kind, stopping pc, and the read view of points 0..2 at that pc. -/
def planRow {P : Program Carrier declarations registry} (π : P.Plan) (out : PlanOutcome P) :
    String × Nat × List (Option ℚ) :=
  let view (pc : Nat) (M : Memory Carrier declarations) :=
    ([0, 1, 2] : List (Fin 3)).map fun i => π.readPub pc M ⟨(), point i⟩
  match out with
  | .done pc M => ("done", pc, view pc M)
  | .failed _ pc M => ("failed", pc, view pc M)
  | .stuck pc M => ("stuck", pc, view pc M)

/-- Executor side: kind and the published points 0..2 of its final snapshot. -/
def refRow {P : Program Carrier declarations registry} (out : Outcome P ops) :
    String × List (Option ℚ) :=
  (out.kind, vectorStore (snapshot out))

/-! ### Done cases: equal published values -/

-- taggedOut (outputs = all of point 0..2): Decode versus the `tagged` donor run.
#eval check "cmp-tagged"
  (planRow plan taggedRun, decodeRow (plan.Decode 3 (finalMemory taggedRun)),
    refRow taggedResult.outcome)
  (("done", 3, [some 0, some 14, some 0]), some [0, 14, 0],
    ("complete", [some 0, some 14, some 0]))

def reciprocalRef := run (program 2 reciprocalBody) ops (schedule 2 reciprocalBody)
  (pInput 2 reciprocalBody)

#eval check "cmp-reciprocal"
  (planRow (pPlan 2 reciprocalBody) (pRun 2 reciprocalBody), refRow reciprocalRef.outcome)
  (("done", 3, [some (3 / 4), some 0, some 0]), ("complete", [some (3 / 4), some 0, some 0]))

#eval check "cmp-chain"
  (planRow chainPlan (chainPlan.runPlan ops (Start chainInput)), refRow chainResult.outcome)
  (("done", 5, [some 0, some 3, some 4]), ("complete", [some 0, some 3, some 4]))

-- scalarRole false: output tensor 1 only.
def sRefOut (bad : Bool) : String × Option ℚ :=
  match (scalarResult bad).outcome with
  | .complete c _ => ("complete", c.published ⟨1, ()⟩)
  | out => (out.kind, none)

#eval check "cmp-scalar-good" (finalPc (sRun false), sDecode, sRefOut false)
  (5, some 2, ("complete", some 2))

-- The done cases agree value for value (plan view = executor published).
#eval check "cmp-done-agree"
  [(planRow plan taggedRun).2.2 == (refRow taggedResult.outcome).2,
    (planRow (pPlan 2 reciprocalBody) (pRun 2 reciprocalBody)).2.2 ==
      (refRow reciprocalRef.outcome).2,
    (planRow chainPlan (chainPlan.runPlan ops (Start chainInput))).2.2 ==
      (refRow chainResult.outcome).2,
    sDecode == (sRefOut false).2]
  [true, true, true, true]

/-! ### Failing cases: both fail; snapshots recorded, not compared (D5) -/

-- failureAfterBody: lit 2 then reciprocal(0) into point 0. Plan: nothing
-- committed (slot 0 stays 0). Executor snapshot: the accumulator of point 0.
def failureAccRef : ℚ := (snapshot failureAfterResult.outcome).accumulators ⟨(), rfl⟩ (point 0)

#eval check "cmp-failure-after"
  ((planRow (pPlan 2 failureAfterBody) (pRun 2 failureAfterBody)).1,
    finalMemory (pRun 2 failureAfterBody) (place ⟨(), point 0⟩),
    failureAfterResult.outcome.kind, failureAccRef)
  ("failed", some 0, "failed", 2)

#eval check "cmp-scalar-bad" ((sRow true).1, (sRefRow true).1) ("failed", "failed")

/-! ### Theorem 31.3 instantiated -/

theorem plan_tagged_done : plan.runPlan ops (Start η0) = .done 3 m3 := rfl

/-- 31.3 (a) on taggedOut: the model is unique and Decode is its output projection. -/
theorem tagged_model_unique : ∃ ρ, (∀ ρ', taggedOut.Models ops η0 ρ' ↔ ρ' = ρ) ∧
    plan.Decode 3 m3 = some (taggedOut.outputProjection ρ) := by
  obtain ⟨c, success, hmod, hd, -⟩ := done_correct ops plan_valid η0 plan_tagged_done
  exact ⟨_, hmod, hd⟩

/-- 31.3 (b) on scalarRole true: the plan fails, so no model exists. -/
theorem scalar_bad_no_model : ¬ ∃ ρ, (scalarRole true).Models ops (scalarInput true) ρ :=
  failed_correct ops sPlan_bad_valid (scalarInput true)
    (rfl : (sPlan true).runPlan ops (Start (scalarInput true)) =
      .failed (sOcc true 2 rfl) 3 (finalMemory (sRun true)))

/-- 31.3 (b)+(c) on taggedOut: done, hence a model exists. -/
theorem tagged_has_model : ∃ ρ, taggedOut.Models ops η0 ρ :=
  (done_iff_model ops plan_valid η0).mp ⟨3, m3, plan_tagged_done⟩

/-! ### New negative fixture: a defined address never published -/

/-- Coverage2: point 2 is never published. Every safety/progress clause holds,
    so the run is `done`, but Decode fails: point 2 is not in Pub 3. -/
def missingPub : taggedOut.Plan :=
  unitPlan [[.initZero block], [.acc group], [.pub [addr 0, addr 1]]]

#eval check "invalid-missing-publication"
  (verdict missingPub, outcomeRow (missingPub.runPlan ops (Start η0)),
    decodeRow (missingPub.Decode 3 (finalMemory (missingPub.runPlan ops (Start η0)))))
  ((false, ["cov2Complete"]), ("done", 3, none, [some 0, some 14, some 0]), none)

example : missingPub.checkPlan = false := by decide
example : missingPub.checkCov1Complete = true := by decide

#print axioms tagged_model_unique
#print axioms scalar_bad_no_model
#print axioms tagged_has_model

end LeanNCD.Semantics.PlanFixtures

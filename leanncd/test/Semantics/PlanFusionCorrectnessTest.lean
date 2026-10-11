import Semantics.PlanCorrectnessTest
import Semantics.PlanFusionTest

/- Slice 2 (T3) fixtures: Lemma 31.2 / Theorem 31.3 for FUSED plans (`FusionCorrectness.lean`).
   Every asserted value was observed from a real run. Cloned from PlanCorrectnessTest (done and
   failing comparisons) and PlanFusionTest (fused plans). -/

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

/-- The slice-2 verdict: `checkPlanF` and the failing clauses of the EXPANSION. -/
def verdictF {K : S → Type} {σ : Declarations S} {r : Registry K} {P : Program K σ r}
    [DecidableEq σ.Tensor] (π : P.Plan) : Bool × List String :=
  (π.checkPlanF, (clauseRow π.expand).filterMap fun (n, b) => if b then none else some n)

/-! ### (1) a valid fused plan: runPlan is `done`, Decode is the model's output projection -/

def fusedRun := fused.runPlan ops (Start η0)

-- `fused` = [[initZero; acc], [pub]] (2 commands); the singleton `plan` ends at pc 3.
#eval check "fusedcorr-done-decode"
  (verdictF fused, outcomeRow fusedRun, decodeRow (fused.Decode 2 (finalMemory fusedRun)),
    decodeRow (plan.Decode 3 (finalMemory taggedRun)))
  ((true, []), ("done", 2, none, [some 0, some 14, some 0]), some [0, 14, 0], some [0, 14, 0])

theorem fused_fvalid : fused.FValid := fused.checkPlanF_sound (by decide)

/-- Theorem 31.3 (a) on the fused plan: the model is unique, and the fused plan's Decode (at
    pc = number of COMMANDS) is its output projection. -/
theorem fused_model_unique : ∃ ρ, (∀ ρ', taggedOut.Models ops η0 ρ' ↔ ρ' = ρ) ∧
    fused.Decode 2 (finalMemory fusedRun) = some (taggedOut.outputProjection ρ) := by
  obtain ⟨c, success, hmod, hd, -⟩ := done_correct_F ops fused_fvalid η0
    (rfl : fusedRun = .done 2 (finalMemory fusedRun))
  exact ⟨_, hmod, hd⟩

theorem fused_has_model : ∃ ρ, taggedOut.Models ops η0 ρ :=
  (done_iff_model_F ops fused_fvalid η0).mp ⟨2, finalMemory fusedRun, rfl⟩

/-- A fused scalar plan: Decode of the fused run against the executor's published value. -/
def sFusedDecode : Option ℚ :=
  ((sPlanFused false).Decode 2 (finalMemory (sRunF false))).map (fun out => out sOut ())

#eval check "fusedcorr-scalar-done-decode"
  ((sPlanFused false).checkPlanF, sFusedDecode, sRefOut false)
  (true, some 2, ("complete", some 2))

/-! ### (2) a fused plan that fails: fails / no model (D5, D14: not the occurrence or snapshot) -/

-- fused-scalar-bad reports the PRE-command memory ([7,0,0]); the singleton plan reports [7,2,0].
#eval check "fusedcorr-failed-no-model"
  ((sPlanFused true).checkPlanF, (sRowF true), (sRefRow true))
  (true, ("failed", 1, some 2, [some 7, some 0, some 0]), ("failed", some 2))

theorem sFused_bad_fvalid : (sPlanFused true).FValid :=
  (sPlanFused true).checkPlanF_sound (by decide)

theorem scalar_bad_no_model_F : ¬ ∃ ρ, (scalarRole true).Models ops (scalarInput true) ρ :=
  failed_correct_F ops sFused_bad_fvalid (scalarInput true)
    (rfl : (sPlanFused true).runPlan ops (Start (scalarInput true)) =
      .failed (sOcc true 2 rfl) 1 (finalMemory (sRunF true)))

/-! ### (3) a fused plan with an INVALID expansion (publish before accumulate in one command) -/

-- Slice-1 verdict on the unexpanded plan: only `singleton` fails (checkSteps is vacuous on a
-- non-singleton command); slice-2 verdict: the expansion fails `pubOrder@1`.
#eval check "fusedcorr-misfused-verdicts"
  (verdict (pPlanMisFused 2 reciprocalBody), verdictF (pPlanMisFused 2 reciprocalBody))
  ((false, ["singleton"]), (false, ["pubOrder@1"]))

example : (pPlanMisFused 2 reciprocalBody).checkPlanF = false := by decide

-- Hypothesis necessity: a fused plan that omits publication of point 2 runs to `done` but
-- Decode fails (the fused analogue of `invalid-missing-publication`); FValid fails `cov2Complete`.
def fusedMissingPub : taggedOut.Plan :=
  unitPlan [[.initZero block, .acc group], [.pub [addr 0, addr 1]]]

#eval check "fusedcorr-missing-publication"
  (verdictF fusedMissingPub, outcomeRow (fusedMissingPub.runPlan ops (Start η0)),
    decodeRow (fusedMissingPub.Decode 2 (finalMemory (fusedMissingPub.runPlan ops (Start η0)))))
  ((false, ["cov2Complete"]), ("done", 2, none, [some 0, some 14, some 0]), none)

/-! ### (4) a valid fused plan agrees with its expansion on the final memory -/

/-- Kinds, stopping pcs (commands vs annotations) and whether the final points agree. -/
def agreeRow {P : Program Carrier declarations registry} (π : P.Plan) (η : P.Input) :
    String × String × Nat × Nat × Bool :=
  let a := outcomeRow (π.runPlan ops (Start η))
  let b := outcomeRow (π.expand.runPlan ops (Start η))
  (a.1, b.1, a.2.1, b.2.1, a.2.2.2 == b.2.2.2)

#eval check "fusedcorr-valid-agrees-with-expansion"
  ((pPlanFused 2 reciprocalBody).checkPlanF, agreeRow (pPlanFused 2 reciprocalBody) (pInput 2 reciprocalBody),
    (pPlanAP 2 reciprocalBody).checkPlanF, agreeRow (pPlanAP 2 reciprocalBody) (pInput 2 reciprocalBody),
    fused.checkPlanF, agreeRow fused η0)
  (true, ("done", "done", 1, 3, true), true, ("done", "done", 2, 3, true),
    true, ("done", "done", 2, 3, true))

-- Failing runs agree on the failing occurrence (not on pc or memory).
#eval check "fusedcorr-failed-agrees-on-occurrence"
  (match (sRunF true), (sPlanFused true).expand.runPlan ops (Start (scalarInput true)) with
    | .failed o _ _, .failed o' _ _ => (o.1.val.val, o'.1.val.val, o == o')
    | _, _ => (0, 0, false))
  (2, 2, true)

example : PlanOutcome.Agree fusedRun (fused.expand.runPlan ops (Start η0)) := rfl

-- `Agree` is not vacuous: different final memories and different failing occurrences disagree.
example : ¬ PlanOutcome.Agree fusedRun (.done 3 (Start η0)) := by
  intro h
  have e : finalMemory fusedRun (place ⟨T, point 1⟩) = Start η0 (place ⟨T, point 1⟩) :=
    congrFun (h : finalMemory fusedRun = Start η0) _
  revert e
  decide

example : ¬ PlanOutcome.Agree (sRunF true) (.failed (sOcc true 1 rfl) 0 (Start (scalarInput true))) := by
  intro h
  have e : (2 : Nat) = 1 := congrArg (fun o : OccRef (scalarRole true) => o.1.val.val)
    (h : (sOcc true 2 rfl) = (sOcc true 1 rfl))
  omega

#print axioms fused_fvalid
#print axioms fused_model_unique
#print axioms fused_has_model
#print axioms scalar_bad_no_model_F

end LeanNCD.Semantics.PlanFixtures

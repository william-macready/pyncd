import LeanNCD.Semantics.Plan
import Semantics.ExecutableReferenceTest

/- D11 (multi-sort `K`): the Plan-layer theorems are generic over `K : S → Type`, but every
   other Plan fixture has one sort. Here sort `false` carries ℤ and sort `true` carries ℚ, with
   per-sort `ScalarOps`, so slot types, `Start`, `execAcc` accumulation, publication, `Decode`
   and the validity checker all run at two different carriers. The registry is empty (no
   primitive crosses sorts), so this checks sort-indexed storage and accumulation, not
   cross-sort reads. Donor: ExecutableReferenceFixtures.scalarRole/scalarSchedule. -/

namespace LeanNCD.Semantics.PlanMultiSort

open Program Program.Executor Program.Plan ExecutableReferenceFixtures

@[reducible] def KS : Bool → Type
  | false => ℤ
  | true => ℚ

instance (b : Bool) : AddCommMonoid (KS b) :=
  match b with
  | false => inferInstanceAs (AddCommMonoid ℤ)
  | true => inferInstanceAs (AddCommMonoid ℚ)

def msOps : (s : Bool) → ScalarOps (KS s)
  | false => ⟨0, 1, (· + ·), (· * ·)⟩
  | true => ⟨0, 1, (· + ·), (· * ·)⟩

@[reducible] def msRegistry : Registry KS where
  Op := Empty
  arity := fun f => nomatch f
  input := fun f => nomatch f
  output := fun f => nomatch f
  domain := fun f => nomatch f
  meaning := fun f => nomatch f

/-- Tensor 0 is a scalar over ℤ, tensor 1 a scalar over ℚ. -/
@[reducible] def msDeclarations : Declarations Bool :=
  ⟨Fin 2, fun t => t.val, fun _ _ h => Fin.ext h, fun t => ⟨t.val == 1, []⟩⟩

/-- Statement bodies, evaluated through `msOps`: statement 0 is `a + b`, statement 1 is `a * b`.
    Tensor 0 (ℤ): 2 + 3 = 5 and 2 * 3 = 6, accumulating to 11.
    Tensor 1 (ℚ): 1/2 + 1/4 = 3/4 and 1/2 * 1/4 = 1/8, accumulating to 7/8. -/
def bodyOf {Γ : Type} :
    (t : Fin 2) → Fin 2 → Expr KS msDeclarations msRegistry Γ (.scalar (msDeclarations.signature t).sort)
  | 0, s => .binary (if s = 0 then .add else .mul) (.lit (2 : ℤ)) (.lit (3 : ℤ))
  | 1, s => .binary (if s = 0 then .add else .mul) (.lit (1 / 2 : ℚ)) (.lit (1 / 4 : ℚ))

@[reducible] def prog : Program KS msDeclarations msRegistry where
  tensors := inferInstance
  input := fun _ => false
  output := fun _ => true
  output_defined := fun _ _ => rfl
  statements := fun _ => 2
  valuations := fun _ _ => 1
  guard := fun _ _ _ => true
  destination := fun _ _ _ => ()
  body := fun t s => bodyOf t.val s

def η : prog.Input := ⟨fun _ => none, by intro t; rfl⟩

def occ (t s : Fin 2) : OccRef prog := ⟨⟨t, rfl⟩, ⟨s, ⟨0, rfl⟩⟩⟩
def addr (t : Fin 2) : DefAddr prog := ⟨⟨t, rfl⟩, ()⟩

def pl : prog.Plan where
  tensors := [0, 1]
  tensors_nodup := by decide
  tensors_complete := by intro t; fin_cases t <;> simp
  commands :=
    [[.initZero [addr 0, addr 1]],
     [.acc [occ 0 0, occ 0 1, occ 1 0, occ 1 1]],
     [.pub [addr 0, addr 1]]]

theorem pl_valid : pl.Valid := pl.checkPlan_sound (by
  have hl : pl.checkLayouts = true := pl.checkLayouts_iff.mpr
    (fun pc _ => pl.layoutOK_of_place_injective
      (place_injective pl.tensors pl.tensors_nodup pl.tensors_complete) pc)
  rw [checkPlan, hl, Bool.and_true]
  decide)

def msSchedule : Schedule prog where
  tensors := [0, 1]
  tensors_nodup := by decide
  tensors_complete := by intro t; fin_cases t <;> simp
  keys := [.occurrence ⟨0, rfl⟩ ⟨0, ⟨0, rfl⟩⟩, .occurrence ⟨0, rfl⟩ ⟨1, ⟨0, rfl⟩⟩,
    .publication ⟨0, rfl⟩ (),
    .occurrence ⟨1, rfl⟩ ⟨0, ⟨0, rfl⟩⟩, .occurrence ⟨1, rfl⟩ ⟨1, ⟨0, rfl⟩⟩,
    .publication ⟨1, rfl⟩ ()]
  keys_nodup := by simp [List.nodup_cons, Key.occurrence.injEq, Key.publication.injEq]
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨t, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      have hv' : v = 0 := Subsingleton.elim _ _
      subst v
      fin_cases t <;> fin_cases s <;> simp
    | publication t p =>
      rcases t with ⟨t, ht⟩
      cases p
      fin_cases t <;> simp

def planRun := pl.runPlan msOps (pl.Start η)

/-- Plan side: the two published values, each at its own carrier. -/
def planRow : String × Nat × Option ℤ × Option ℚ :=
  match planRun with
  | .done pc M => ("done", pc, (readSlot pl.allocation M ⟨0, ()⟩ : Option ℤ),
      (readSlot pl.allocation M ⟨1, ()⟩ : Option ℚ))
  | .failed _ pc _ => ("failed", pc, none, none)
  | .stuck pc _ => ("stuck", pc, none, none)

/-- Reference side: the executor's published values. -/
def refRow : String × Option ℤ × Option ℚ :=
  match (run prog msOps msSchedule η).outcome with
  | .complete c _ => ("complete", (c.published ⟨0, ()⟩ : Option ℤ), (c.published ⟨1, ()⟩ : Option ℚ))
  | out => (out.kind, none, none)

def decodeRow : Option (ℤ × ℚ) :=
  match planRun with
  | .done pc M => (pl.Decode pc M).map fun out => (out ⟨0, rfl⟩ (), out ⟨1, rfl⟩ ())
  | _ => none

#eval check "multisort-plan" planRow ("done", 3, some 11, some (7 / 8))
#eval check "multisort-reference" refRow ("complete", some 11, some (7 / 8))
#eval check "multisort-decode" decodeRow (some (11, 7 / 8))
-- Plan and reference agree value for value.
#eval check "multisort-agree"
  (planRow.2.2 == (refRow.2.1, refRow.2.2)) true

end LeanNCD.Semantics.PlanMultiSort

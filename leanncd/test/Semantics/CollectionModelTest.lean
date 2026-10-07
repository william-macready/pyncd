import Semantics.ExpressionTest
import LeanNCD.Semantics.Models

namespace LeanNCD.Semantics.CollectionModelFixtures
open Fixtures

@[reducible] def expressionProgram (n : Nat) (d : Fin n → Fin 3) (keep : Bool)
    (b : (Γ : Type) → Fin n → Scalar Γ) :
    Program Carrier declarations registry where
  tensors := inferInstance
  input := fun _ => false
  output := fun _ => false
  output_defined := by intros; rfl
  statements := fun _ => n
  valuations := fun _ _ => 1
  guard := fun _ _ _ => keep
  destination := fun _ s _ => point (d s)
  body := fun _ s => b _ s

@[reducible] def vectorProgram (n : Nat) (d : Fin n → Fin 3) (v : Fin n → ℚ) :=
  expressionProgram n d true (fun _ s => .lit (v s))

def target : (vectorProgram n d v).Defined := ⟨(), rfl⟩
def prior : Store Carrier declarations := fun _ => 99

def literals_admitted (n : Nat) (d : Fin n → Fin 3) (v : Fin n → ℚ) :
    (vectorProgram n d v).AdmEnv ops prior := by
  intro t o
  rfl

def duplicate := vectorProgram 2 (fun _ => 0) (fun _ => 2)
def collision := vectorProgram 3 (fun s => if s = 2 then 2 else 0)
  (fun s => ![2, 7, 5] s)
def noStatements := vectorProgram 0 Fin.elim0 Fin.elim0
def swapped : Fin 3 ≃ Fin 3 := Equiv.swap 0 2
def occurrenceSwap (t : collision.Defined) : collision.Occurrence t ≃ collision.Occurrence t :=
  Equiv.sigmaCongr swapped (fun _ => Equiv.refl _)

-- NEW finite tagged collection; donor scalar operations/coordinates: Fixtures.ops/point.
#guard duplicate.collect ops prior (literals_admitted _ _ _) target (point 0) == 4
#guard collision.collect ops prior (literals_admitted _ _ _) target (point 0) == 9
#guard collision.collect ops prior (literals_admitted _ _ _) target (point 1) == 0
#guard noStatements.collect ops prior (literals_admitted _ _ _) target (point 0) == 0
#guard duplicate.collect ops prior (literals_admitted _ _ _) target (point 0) != prior ⟨(), point 0⟩ + 4
#guard collision.relabeledCollect ops occurrenceSwap prior (literals_admitted _ _ _)
  target (point 0) == 9 &&
  collision.relabeledCollect ops occurrenceSwap prior (literals_admitted _ _ _)
    target (point 2) == 5

@[reducible] def partialProgram (keep : Bool) (legal : Bool) :=
  expressionProgram 1 (fun _ => 0) keep (fun _ _ => .binary .mul (.lit 0)
    (if legal then .lit 2 else .prim (r := registry) Op.recip (fun _ => .lit 0)))

-- Clone Fixtures.zeroStrict/bad, restrict its context before demand.
theorem excluded_undefined : (partialProgram false false).AdmEnv ops prior := by
  intro t o
  have h := o.2.property
  contradiction

theorem active_zero_undefined : ¬ (partialProgram true false).AdmEnv ops prior := by
  intro h
  have bad := h ⟨(), rfl⟩ ⟨0, ⟨0, rfl⟩⟩
  change false = true at bad
  contradiction

#guard (partialProgram true true).outcome ops prior ⟨(), rfl⟩ ⟨0, ⟨0, rfl⟩⟩ == some 0

-- Clone Fixtures.heterogeneous; Boolean argument in a rational collection.
@[reducible] def mixedProgram :=
  expressionProgram 1 (fun _ => 0) true (fun _ _ => .prim (r := registry) Op.mixed (by
      intro i
      refine Fin.cases (.lit 4) (fun j => ?_) i
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact .lit true))
def mixed_admitted : mixedProgram.AdmEnv ops prior := by intro t o; rfl

#guard mixedProgram.collect ops prior mixed_admitted ⟨(), rfl⟩ (point 0) == 14

-- Clone Fixtures.registry Op.recip; compare primitive before and after sum.
@[reducible] def reciprocalProgram :=
  expressionProgram 2 (fun _ => 0) true (fun _ s => .prim (r := registry) Op.recip
    (fun _ => .lit (if s = 0 then 2 else 4)))
def reciprocal_admitted : reciprocalProgram.AdmEnv ops prior := by
  intro t o
  rcases o with ⟨s, v⟩
  change Fin 2 at s
  fin_cases s <;> rfl

#guard reciprocalProgram.collect ops prior reciprocal_admitted ⟨(), rfl⟩ (point 0) == (3 / 4 : ℚ) &&
  interpret ops prior (.prim (r := registry) Op.recip (fun _ => .lit 6)) () == some (1 / 6 : ℚ)

#eval [
  duplicate.collect ops prior (literals_admitted _ _ _) target (point 0),
  collision.collect ops prior (literals_admitted _ _ _) target (point 0),
  collision.collect ops prior (literals_admitted _ _ _) target (point 1),
  noStatements.collect ops prior (literals_admitted _ _ _) target (point 0),
  collision.relabeledCollect ops occurrenceSwap prior (literals_admitted _ _ _) target (point 0),
  collision.relabeledCollect ops occurrenceSwap prior (literals_admitted _ _ _) target (point 2),
  mixedProgram.collect ops prior mixed_admitted ⟨(), rfl⟩ (point 0),
  reciprocalProgram.collect ops prior reciprocal_admitted ⟨(), rfl⟩ (point 0)]

-- NEW role fixture; donor empty shape: Fixtures.emptyShape.
@[reducible] def roleDeclarations : Declarations ScalarSort :=
  ⟨Fin 3, fun t => t.val, fun _ _ h => Fin.ext h,
    fun t => ⟨.rational, if t = 0 then emptyShape.axes else []⟩⟩

@[reducible] def roleProgram : Program Carrier roleDeclarations registry where
  tensors := inferInstance
  input := fun t => t == 0
  output := fun t => t == 1
  output_defined := by intro t h; fin_cases t <;> simp_all
  statements := fun _ => 0
  valuations := fun _ s => nomatch s
  guard := fun _ s => nomatch s
  destination := fun _ s => nomatch s
  body := fun _ s => nomatch s

def presentEmpty : Program.InputBinding (K := Carrier) (σ := roleDeclarations) :=
  fun t => if h : t = 0 then some (by
    subst t
    exact fun p => Fin.elim0 p.1) else none
def omittedEmpty : Program.InputBinding (K := Carrier) (σ := roleDeclarations) := fun _ => none
def extraDefined : Program.InputBinding (K := Carrier) (σ := roleDeclarations) :=
  fun t => if t = 0 then presentEmpty t else some (fun _ => 0)

theorem present_valid : roleProgram.ValidInput presentEmpty := by
  unfold Program.ValidInput
  decide
theorem omitted_empty_rejected : ¬ roleProgram.ValidInput omittedEmpty := by
  unfold Program.ValidInput
  decide
theorem defined_binding_rejected : ¬ roleProgram.ValidInput extraDefined := by
  unfold Program.ValidInput
  decide

def supplied : roleProgram.Input := ⟨presentEmpty, present_valid⟩
def zeroStore : Store Carrier roleDeclarations := fun _ => 0
def internalNonzero : Store Carrier roleDeclarations := fun a => if a.1 = 2 then 7 else 0
def role_admitted (ρ : Store Carrier roleDeclarations) : roleProgram.AdmEnv ops ρ := by
  intro t o
  exact Fin.elim0 o.1

def empty_agreement (ρ : Store Carrier roleDeclarations) :
    roleProgram.InputAgreement supplied ρ := by
  intro t f h p
  fin_cases t
  · exact Fin.elim0 p.1
  · cases h
  · cases h

-- NEW: non-output equations cannot be projected away.
theorem nonoutput_not_model : ¬ roleProgram.Models ops supplied internalNonzero := by
  rintro ⟨h, _, equations⟩
  have eq := equations ⟨2, rfl⟩ ()
  have collected : roleProgram.collect ops internalNonzero h ⟨2, rfl⟩ () = 0 := by
    simp [Program.collect, pushforward, roleProgram]
  rw [collected] at eq
  change (7 : ℚ) = 0 at eq
  norm_num at eq

-- NEW: admissibility alone is not the simultaneous equations.
theorem admissible_not_model :
    roleProgram.AdmEnv ops internalNonzero ∧
      ¬ roleProgram.Models ops supplied internalNonzero :=
  ⟨role_admitted _, nonoutput_not_model⟩

theorem zero_model : roleProgram.Models ops supplied zeroStore := by
  refine ⟨role_admitted _, empty_agreement _, ?_⟩
  intro t p
  simp [zeroStore, Program.collect, pushforward, roleProgram]

theorem zero_fixedpoint :
    roleProgram.equationOperator ops zeroStore (role_admitted _) = zeroStore :=
  ((roleProgram.models_fixedpoint ops supplied zeroStore).mp zero_model).2.choose_spec

end LeanNCD.Semantics.CollectionModelFixtures

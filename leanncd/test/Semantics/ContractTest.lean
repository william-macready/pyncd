import LeanNCD
import Semantics.ExpressionTest
import Semantics.NativeTest
import LeanNCD.Semantics.TensorLogicSemanticCoreSpike

namespace LeanNCD.Semantics.Fixtures

abbrev Guarded := {i : Fin 3 // i.val < 2}
def guardedRead : Scalar Guarded :=
  direct (fun γ => ⟨γ.val.val + 1, by have := γ.property; omega⟩)

#guard interpret ops store guardedRead ⟨0, by decide⟩ == some 5
#guard interpret ops store guardedRead ⟨1, by decide⟩ == some 7
#guard match strictPolicy.resolve (fun _ => 3) with
  | .reject => true | _ => false
#guard match strictPolicy.resolve (fun _ => -1) with
  | .reject => true | _ => false

theorem dtype_mismatch_rejected : True := by
  fail_if_success
    have wrong : E Unit (.scalar .flag) := direct (fun _ => 0)
  trivial

theorem shape_mismatch_rejected : True := by
  fail_if_success
    have wrong : E Unit (.array .rational emptyShape) := tabulated
  trivial

theorem unknown_tensor_rejected : True := by
  fail_if_success
    have wrong : NativeFixtures.noTensors.Tensor := (1 : Nat)
  trivial

theorem invalid_coordinate_rejected : True := by
  fail_if_success
    have wrong : Fin 3 := ⟨3, by decide⟩
  trivial

theorem unknown_index_rejected : True := by
  fail_if_success
    have wrong : Unit → Int := fun γ => γ.2
  trivial

@[reducible] def scalarDeclarations : Declarations ScalarSort :=
  ⟨Unit, fun _ => 8, fun a b _ => by cases a; cases b; rfl,
    fun _ => ⟨.rational, []⟩⟩
def scalarPolicy : ReadPolicy ℚ [] :=
  ⟨fun _ => .at (), by intro p; cases p; rfl⟩
def scalarTensor : Expr Carrier scalarDeclarations registry Unit (.scalar .rational) :=
  .read () ⟨scalarPolicy, fun _ => Fin.elim0,
    fun _ => .at (), by intro _; rfl⟩
#guard interpret ops (fun _ => 17) scalarTensor () == some 17

def reorderedShape : Shape := [⟨2, 3⟩, ⟨1, 3⟩]
theorem axis_identity_and_order : ([⟨1, 3⟩, ⟨2, 3⟩] : Shape) ≠ reorderedShape := by decide

def cartesianShape : ArrayShape := ⟨[⟨60, 2⟩, ⟨61, 3⟩], by decide⟩
def cartesianTab : E Unit (.array .rational cartesianShape) :=
  .tab cartesianShape (canonicalLayout _)
    (.binary .mul (direct (fun γ => γ.2.2.1))
      (.binary .add (.iverson (fun γ => γ.2.1.val == 1)) (.lit 1)))
def cartesianSelect : Scalar Unit := .at cartesianTab (fun _ => (1, (2, ())))
#guard scalarObservation cartesianSelect == some 14
#guard (footprint cartesianTab ()).length == 6

theorem reduction_exact_bound_values :
    interpret ops store (.reduce 3 (direct (fun γ : Unit × Fin 3 => γ.2))) () =
      some (∑ i : Fin 3, store ⟨(), point i⟩) := by
  apply interpret_reduce_sum ops store rfl rfl
  intro i
  rfl

theorem empty_reduction_exact_without_body :
    interpret ops store emptyReduction () = some (∑ i : Fin 0, (Fin.elim0 i : ℚ)) := by
  apply interpret_reduce_sum ops store rfl rfl
  intro i
  exact Fin.elim0 i

#print axioms reduction_exact_bound_values
#print axioms empty_reduction_exact_without_body

theorem nonselected_lane_obligation (p : PartialStore Carrier declarations)
    (v : Coord vectorShape.axes → ℚ)
    (h : evalWith ops p
      (.tab vectorShape (canonicalLayout _)
        (.prim (r := registry) Op.recip
          (fun _ => .iverson (fun γ => γ.2.1.val == 0)))) () = some v) : False := by
  have hc := (tab_complete _ _ _ _ _ _ _).mp h (point 1)
  have hn : evalWith ops p
      (.prim (r := registry) Op.recip
        (fun _ => .iverson (fun γ : Unit × Coord vectorShape.axes => γ.2.1.val == 0)))
      ((), point 1) = none := rfl
  rw [hn] at hc
  contradiction

def signedRaw (x : Int) : Int := -2 * x + 3
theorem existing_stmat_seam (x : Int) :
    signedRaw x = TensorLogicSemanticCoreSpike.integerCoordinate x :=
  (TensorLogicSemanticCoreSpike.integerCoordinate_eq x).symm

#guard signedRaw 2 == -1
#print axioms nonselected_lane_obligation
#print axioms existing_stmat_seam

end LeanNCD.Semantics.Fixtures

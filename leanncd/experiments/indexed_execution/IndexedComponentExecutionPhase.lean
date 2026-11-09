import IndexedComponentComposition
import IndexedComponentModelInputs

namespace IndexedComponentExecution

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open IndexedOpenComposition
open IndexedComponentTransport
open IndexedComponentComposition

variable {σA σB : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB) (wire : Boundary A B)

structure UpstreamState (source : State σA) (target : State (declarations A B)) : Prop where
  available : ∀ a, target.available ((upstream A B).address a) = source.available a
  downstream : ∀ a : Address σB, B.program.input a.1 = false →
    target.available ((downstream A B wire).address a) = none
  produced : target.produced = source.produced.map (fun row => (upstreamId row.1, row.2))

structure DownstreamState (completed : State σA) (source : State σB)
    (target : State (declarations A B)) : Prop where
  upstream : ∀ a, target.available ((upstream A B).address a) = completed.available a
  available : ∀ a, target.available ((downstream A B wire).address a) = source.available a
  produced : target.produced =
    completed.produced.map (fun row => (upstreamId row.1, row.2)) ++
      source.produced.map (fun row => (downstreamId row.1, row.2))

theorem initial_upstream (η : A.program.Input) :
    UpstreamState A B wire (initial η.val)
      (initial (liftInput A B wire η).val) := by
  refine ⟨?_, ?_, rfl⟩
  · intro a
    rfl
  · intro a ha
    rcases a with ⟨t, p⟩
    change B.program.input t = false at ha
    have hnone : (liftInput A B wire η).val ((downstream A B wire).tensor t) = none := by
      change (liftInput A B wire η).val (downstreamTensor A B wire t) = none
      rw [downstreamTensor_defined A B wire ⟨t, ha⟩]
      rfl
    change Option.map _ ((liftInput A B wire η).val
      ((downstream A B wire).tensor t)) = none
    rw [hnone]
    rfl

theorem graph_steps_standalone :
    (compose A B wire).graph.steps =
      A.graph.steps.map (mapStep (upstream A B) upstreamId) ++
        B.graph.steps.map (mapStep (downstream A B wire) downstreamId) := by
  change (graph A B wire).steps = _
  rw [graph_steps, (close_success_canonical A.matched.close_ok).2,
    (close_success_canonical B.matched.close_ok).2]

theorem boundary_available {completed : State σA} {target : State (declarations A B)}
    (related : UpstreamState A B wire completed target)
    (ρA : Store RationalReference.Carrier σA)
    (full : ∀ a, completed.available a = some (ρA a)) (a : Address σB) :
    target.available ((downstream A B wire).address a) =
      (initial (boundaryInput A B wire ρA).val).available a := by
  rcases a with ⟨t, p⟩
  by_cases ht : B.program.input t = true
  · rw [downstream_input_address A B wire ⟨t, ht⟩ p, related.available, full]
    simp [IndexedOpenComposition.initial, boundaryInput, ht]
  · have hf : B.program.input t = false := Bool.eq_false_iff.mpr ht
    rw [related.downstream ⟨t, p⟩ hf]
    simp [IndexedOpenComposition.initial, boundaryInput, ht]

theorem downstream_at_cut {completed : State σA} {target : State (declarations A B)}
    (related : UpstreamState A B wire completed target)
    (ρA : Store RationalReference.Carrier σA)
    (full : ∀ a, completed.available a = some (ρA a)) :
    DownstreamState A B wire completed
      (initial (boundaryInput A B wire ρA).val) target := by
  refine ⟨related.available, boundary_available A B wire related ρA full, ?_⟩
  simpa [IndexedOpenComposition.initial] using related.produced

theorem boundary_input_presence (ρA : Store RationalReference.Carrier σA) (t : σB.Tensor) :
    ((boundaryInput A B wire ρA).val t).isSome = B.program.input t :=
  (boundaryInput A B wire ρA).property t

theorem boundary_input_exact (ρA : Store RationalReference.Carrier σA)
    (t : σB.Tensor) (ht : B.program.input t = true) :
    (boundaryInput A B wire ρA).val t =
      some (fun p => ρA
        ⟨(wire.matched ⟨t, ht⟩).val, (wire.domain ⟨t, ht⟩).coord p⟩) := by
  simp [boundaryInput, ht]

end IndexedComponentExecution

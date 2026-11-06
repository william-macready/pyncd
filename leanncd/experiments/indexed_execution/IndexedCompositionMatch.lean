import IndexedOpenComposition

namespace IndexedOpenComposition

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]

abbrev SourceOccurrence
    (P : Program RationalReference.Carrier σ RationalReference.registry) :=
  (t : P.Defined) × P.Occurrence t

def collectorCapabilities (contract : Contract σ) (a : Address σ) : List Nat :=
  letI := Program.Executor.addressEq (σ := σ)
  ((contract.collectors.find? fun row => decide (row.1 = a)).map Prod.snd).getD []

def keyStep (P : Program RationalReference.Carrier σ RationalReference.registry)
    (contract : Contract σ) (fragment : Fragment σ)
    (index : SourceOccurrence P ≃ Fin fragment.writers.length) : Key P → Step σ
  | .occurrence t o => .write fragment.writers[index ⟨t, o⟩]
  | .publication t p => .collect ⟨t.val, p⟩ (collectorCapabilities contract ⟨t.val, p⟩)

structure SourceContractMatch
    (P : Program RationalReference.Carrier σ RationalReference.registry)
    (schedule : Schedule P) (contract : Contract σ) (fragment : Fragment σ)
    (graph : Closed σ) where
  close_ok : close contract fragment = .ok graph
  input_roles : contract.input = P.input
  tensor_order : contract.tensors = schedule.tensors
  outputs_exact : ∀ a : Address σ, a ∈ contract.outputs ↔ P.output a.1 = true
  sourceToWriter : SourceOccurrence P ≃ Fin fragment.writers.length
  writer_destination : ∀ o : SourceOccurrence P,
    fragment.writers[sourceToWriter o].destination =
      ⟨o.1.val, P.destination o.1 o.2.1 o.2.2⟩
  writer_reads : ∀ o : SourceOccurrence P,
    fragment.writers[sourceToWriter o].reads =
      footprint (P.body o.1 o.2.1) o.2.2
  eval_agrees : ∀ (o : SourceOccurrence P)
      (store : PartialStore RationalReference.Carrier σ),
    evalReady RationalReference.ops store
        fragment.writers[sourceToWriter o].body () =
      evalReady RationalReference.ops store (P.body o.1 o.2.1) o.2.2
  priority : schedule.keys.map (keyStep P contract fragment sourceToWriter) = graph.steps

variable {P : Program RationalReference.Carrier σ RationalReference.registry}
variable {schedule : Schedule P} {contract : Contract σ} {fragment : Fragment σ}
variable {graph : Closed σ}

def SourceContractMatch.writer
    (M : SourceContractMatch P schedule contract fragment graph)
    (o : SourceOccurrence P) : Writer σ :=
  fragment.writers[M.sourceToWriter o]

def SourceContractMatch.capability
    (M : SourceContractMatch P schedule contract fragment graph)
    (o : SourceOccurrence P) : Nat :=
  (M.writer o).capability

def SourceContractMatch.tag
    (M : SourceContractMatch P schedule contract fragment graph)
    (o : SourceOccurrence P) : Nat :=
  (M.writer o).tag

def SourceContractMatch.step
    (M : SourceContractMatch P schedule contract fragment graph) : Key P → Step σ :=
  keyStep P contract fragment M.sourceToWriter

structure LedgerInvariant
    (M : SourceContractMatch P schedule contract fragment graph) (g : State σ) : Prop where
  nodup : (g.produced.map Prod.fst).Nodup
  valid : ∀ cap value, (cap, value) ∈ g.produced →
    ∃ o : SourceOccurrence P, M.capability o = cap

structure Relation
    (M : SourceContractMatch P schedule contract fragment graph)
    (g : State σ) (c : P.Running) : Prop where
  published : g.available = c.published
  pending : ∀ t (o : P.Occurrence t),
    o ∈ c.pending t ↔ producedValue g (M.capability ⟨t, o⟩) = none
  accumulators : ∀ t (p : Coord (σ.signature t.val).axes),
    c.accumulators t p =
      (letI := coordDecidableEq (σ.signature t.val).axes
       ∑ o : P.Occurrence t,
         if P.destination t o.1 o.2 = p then
           (producedValue g (M.capability ⟨t, o⟩)).getD 0 else 0)

theorem initial_related
    (M : SourceContractMatch P schedule contract fragment graph) (η : P.Input) :
    LedgerInvariant M (initial η.val) ∧ Relation M (initial η.val) (P.initial η) := by
  constructor
  · constructor
    · simp [initial]
    · intro cap value h
      simp [initial] at h
  · constructor
    · rfl
    · intro t o
      simp [Program.initial, initial, producedValue]
    · intro t p
      simp [Program.initial, initial, producedValue]

def invalidInputTensor (contract : Contract σ)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ)) : Option σ.Tensor :=
  contract.tensors.find? (fun t => (η t).isSome != contract.input t)

theorem validation_first_error
    (M : SourceContractMatch P schedule contract fragment graph)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ)) (t : σ.Tensor) :
    validate P schedule η = .error t ↔ invalidInputTensor contract η = some t := by
  have same : invalidInputTensor contract η =
      schedule.tensors.find? (fun t => (η t).isSome != P.input t) := by
    simp only [invalidInputTensor, M.tensor_order, M.input_roles]
  rw [same]
  unfold validate
  split <;> simp_all

theorem initial_related_raw
    (M : SourceContractMatch P schedule contract fragment graph)
    (η : InputBinding (K := RationalReference.Carrier) (σ := σ)) (input : P.Input)
    (accepted : validate P schedule η = .ok input) :
    invalidInputTensor contract η = none ∧
      LedgerInvariant M (initial η) ∧ Relation M (initial η) (P.initial input) := by
  have input_eq := validate_preserves P schedule η input accepted
  have no_error : invalidInputTensor contract η = none := by
    cases h : invalidInputTensor contract η with
    | none => rfl
    | some t =>
      have error := (validation_first_error M η t).mpr h
      rw [accepted] at error
      contradiction
  subst η
  exact ⟨no_error, initial_related M input⟩

end IndexedOpenComposition

import IndexedCompositionMatch
import IndexedCompositionParityTest
import IndexedCompositionValidated

namespace IndexedCompositionFixtureProof

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor
open IndexedOpenComposition
open IndexedCompositionParityTest
open IndexedOpenComposition.Correspondence

def graph (other : ℚ) : Closed D :=
  ⟨contract,
    [.write ((fragment other).writers.get ⟨0, by simp [fragment]⟩),
      .write ((fragment other).writers.get ⟨1, by simp [fragment]⟩),
      .collect pre [101, 102],
      .write ((fragment other).writers.get ⟨2, by simp [fragment]⟩),
      .collect out [201],
      .write ((fragment other).writers.get ⟨3, by simp [fragment]⟩),
      .collect audit [301]]⟩

theorem square_context {Γ : Type} (store : PartialStore RationalReference.Carrier D)
    (γ : Γ) :
    evalReady RationalReference.ops store (squareBody Γ) γ =
      evalReady RationalReference.ops store (squareBody Unit) () := by
  rfl

theorem audit_context {Γ : Type} (other : ℚ)
    (store : PartialStore RationalReference.Carrier D) (γ : Γ) :
    evalReady RationalReference.ops store (auditBody other Γ) γ =
      evalReady RationalReference.ops store (auditBody other Unit) () := by
  rfl

def occurrenceIndex (other : ℚ) (o : SourceOccurrence (reference other)) : Fin 4 :=
  if o.1.val.val == 0 then
    if o.2.1.val == 0 then 0 else 1
  else if o.1.val.val == 1 then 2 else 3

def indexedOccurrence (other : ℚ) (i : Fin 4) : SourceOccurrence (reference other) :=
  if i.val == 0 then ⟨⟨0, rfl⟩, ⟨0, ⟨0, rfl⟩⟩⟩
  else if i.val == 1 then ⟨⟨0, rfl⟩, ⟨1, ⟨0, rfl⟩⟩⟩
  else if i.val == 2 then ⟨⟨1, rfl⟩, ⟨0, ⟨0, rfl⟩⟩⟩
  else ⟨⟨2, rfl⟩, ⟨0, ⟨0, rfl⟩⟩⟩

theorem occurrenceIndex_indexedOccurrence (other : ℚ) (i : Fin 4) :
    occurrenceIndex other (indexedOccurrence other i) = i := by
  fin_cases i <;> rfl

theorem indexedOccurrence_occurrenceIndex (other : ℚ)
    (o : SourceOccurrence (reference other)) :
    indexedOccurrence other (occurrenceIndex other o) = o := by
  rcases o with ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
  have hv' : v = 0 := Subsingleton.elim _ _
  subst v
  fin_cases t <;> fin_cases s <;> rfl

def occurrenceEquiv (other : ℚ) :
    SourceOccurrence (reference other) ≃ Fin (fragment other).writers.length where
  toFun := occurrenceIndex other
  invFun := indexedOccurrence other
  left_inv := indexedOccurrence_occurrenceIndex other
  right_inv := occurrenceIndex_indexedOccurrence other

def suppliedMatch (other : ℚ) :
    SourceContractMatch (reference other) (refSchedule other)
      contract (fragment other) (graph other) where
  close_ok := by rfl
  input_roles := rfl
  tensor_order := rfl
  outputs_exact := by
    rintro ⟨t, p⟩
    cases p
    fin_cases t <;> simp [contract, reference, out]
  sourceToWriter := occurrenceEquiv other
  writer_destination := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    have hv' : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases t <;> fin_cases s <;> rfl
  writer_reads := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    have hv' : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases t <;> fin_cases s <;> rfl
  eval_agrees := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩ store
    have hv' : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases t <;> fin_cases s <;> rfl
  priority := by rfl

def strictMatch := suppliedMatch 0
def totalMatch := suppliedMatch 4

def input (other : ℚ) : (reference other).Input :=
  ⟨fun _ => none, by intro t; rfl⟩

theorem strict_correspondence : ValidatedCorrespondence strictMatch (fun _ => none) :=
  default_run_correspondence strictMatch (fun _ => none)

theorem total_correspondence : ValidatedCorrespondence totalMatch (fun _ => none) :=
  default_run_correspondence totalMatch (fun _ => none)

theorem strict_execution :
    ExecutionCorrespondence strictMatch (graphRun 0) ((reference 0).initial (input 0))
      (Executor.run (reference 0) RationalReference.ops (refSchedule 0) (input 0)) :=
  accepted_run_correspondence strictMatch (input 0)

theorem total_execution :
    ExecutionCorrespondence totalMatch (graphRun 4) ((reference 4).initial (input 4))
      (Executor.run (reference 4) RationalReference.ops (refSchedule 4) (input 4)) :=
  accepted_run_correspondence totalMatch (input 4)

end IndexedCompositionFixtureProof

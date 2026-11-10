import IndexedOperationalHistoryComposition
import IndexedOperationalObservationLaws

namespace IndexedOperationalUnits

open IndexedOperationalHistory

namespace History

variable {S E F A B : Type*}

def returning : IndexedOperationalHistory.History.Continuation S E F A A :=
  ⟨fun s a => .done s a, fun _ _ => rfl⟩

theorem done_bind (s : S) (a : A)
    (k : S → A → IndexedOperationalHistory.History S E F B) :
    (IndexedOperationalHistory.History.done s a).bind k = k s a := rfl

theorem bind_done (h : IndexedOperationalHistory.History S E F A) :
    h.bind (fun s a => .done s a) = h := by
  induction h <;> simp_all [IndexedOperationalHistory.History.bind]

theorem done_splice (s : S) (a : A)
    (k : IndexedOperationalHistory.History.Continuation S E F A B) :
    (IndexedOperationalHistory.History.done s a).splice k = k.run s a := rfl

theorem splice_returning (h : IndexedOperationalHistory.History S E F A) :
    h.splice returning = h := bind_done h

theorem returning_shared (s : S) (a : A) :
    ((returning (E := E) (F := F)).run s a).start = s := rfl

theorem returning_states (s : S) (a : A) :
    ((returning (E := E) (F := F)).run s a).states = [s] := rfl

theorem returning_events (s : S) (a : A) :
    ((returning (E := E) (F := F)).run s a).events = [] := rfl

theorem returning_map {T D G C : Type*}
    (s : S → T) (e : E → D) (f : F → G) (a : A → C) (x : S) (y : A) :
    ((returning (E := E) (F := F)).run x y).map s e f a =
      (returning (E := D) (F := G)).run (s x) (a y) := rfl

theorem failure_bind (h : IndexedOperationalHistory.History S E F A)
    (k : S → A → IndexedOperationalHistory.History S E F A)
    {s : S} {f : F} (failed : h.finish = .error (s, f)) :
    h.bind k = h := by
  induction h with
  | done => cases failed
  | failed => rfl
  | step s e tail ih =>
      exact congrArg (IndexedOperationalHistory.History.step s e) (ih failed)

theorem splice_normalization (h : IndexedOperationalHistory.History S E F A)
    (k : IndexedOperationalHistory.History.Continuation S E F A B) :
    (h.splice returning).splice k = h.splice k := by
  rw [splice_returning]

end History

open IndexedOperationalHistory.History
open IndexedOperationalHistory.Fixtures

example : (first.splice History.returning).splice second = first.splice second := by
  exact History.splice_normalization first second

example : ((.done 0 () : IndexedOperationalHistory.History Nat Nat Nat Unit).splice
    ⟨fun s _ => (first.map (fun x => s + x) id id id), fun _ _ => rfl⟩).events =
      [10] := rfl

example : (first.splice History.returning).states = [0, 1] := rfl
example : (first.splice History.returning).states ≠ [0, 1, 1] := by decide

example : (privateFailure.splice History.returning).events = [10, 11, 99] := rfl
example : (privateFailure.splice History.returning).states = [0, 1, 2] := rfl
example : (privateFailure.splice History.returning).finish = .error (2, 7) := rfl
example : (privateFailure.splice second) = privateFailure :=
  History.failure_bind privateFailure second.run rfl

example : ((History.returning (E := Nat) (F := Nat)).run ledgerLeft ()).start.produced =
    [(101, 1), (102, -1)] := rfl
example : ((History.returning (E := Nat) (F := Nat)).run ledgerRight ()).start.produced =
    [(102, -1), (101, 1)] := rfl
example : ((History.returning (E := Nat) (F := Nat)).run privateAvailable ()).start.available
    ⟨0, ()⟩ = some 42 := rfl
example : ((History.returning (E := Nat) (F := Nat)).run privateAvailable ()).states =
    [privateAvailable] := rfl

example : ((History.returning (E := Nat) (F := Nat)).run privateAvailable ()).start.produced ≠
    [] := by decide
example : ((History.returning (E := Nat) (F := Nat)).run privateAvailable ()).start.produced ≠
    [(102, -1), (101, 1)] := by decide
example : ((History.returning (E := Nat) (F := Nat)).run privateAvailable ()).start.available
    ⟨0, ()⟩ ≠ none := by decide

example : swapping.apply (privateFailure.splice History.returning) =
    (swapping.apply privateFailure).splice History.returning := by
  rw [History.splice_returning, History.splice_returning]

open LeanNCD.Semantics IndexedOpenComposition
open IndexedComponentCompositionPortFixtures

def presentEmpty : CompleteObservation emptyProducerDeclarations Unit :=
  ⟨emptyMetadata, .done (initial emptyMetadata.input) (), .done _⟩

def absentEmpty : CompleteObservation emptyProducerDeclarations Unit :=
  ⟨MetadataLawFixtures.absentEmptyMetadata,
    .done (initial MetadataLawFixtures.absentEmptyMetadata.input) (), .done _⟩

example : presentEmpty.history.events = absentEmpty.history.events := rfl

example : presentEmpty.history = absentEmpty.history := by
  have available : (initial emptyMetadata.input).available =
      (initial MetadataLawFixtures.absentEmptyMetadata.input).available := by
    funext a
    exact Fin.elim0 a.2.1
  exact congrArg (fun values => IndexedOperationalHistory.History.done
    (State.mk values []) ()) available

example : ¬presentEmpty.Agrees (MetadataTransport.refl emptyProducerDeclarations)
    (Equiv.refl Unit) absentEmpty := by
  intro h
  have lengths := congrArg List.length h.1.1
  have impossible : (0 : Nat) = 1 := by
    simpa only [List.length_map] using lengths
  contradiction

theorem actual_leaf_right_unit {σ : Declarations Unit}
    [Fintype σ.Tensor] [DecidableEq σ.Tensor]
    (A : IndexedComponentComposition.MatchedComponent σ) (η : A.program.Input)
    (rank : A.program.RankCertificate) :
    ∃ h : GraphHistory σ, h.Admissible ∧
      h.start = initial η.val ∧
      h.toRun = runChecked A.contract A.fragment η.val ∧
      GraphHistory.toRun (h.splice History.returning) =
        runChecked A.contract A.fragment η.val := by
  obtain ⟨h, admitted, actual, start⟩ := GraphHistory.ranked_default_exists A η rank
  refine ⟨h, admitted, start, actual, ?_⟩
  rw [History.splice_returning, actual]

#eval ((first.splice History.returning).events,
  (first.splice History.returning).states)
#eval ((privateFailure.splice History.returning).events,
  (privateFailure.splice History.returning).states,
  (privateFailure.splice History.returning).finish)
#eval (((History.returning (E := Nat) (F := Nat)).run privateAvailable ()).start.produced,
  ((History.returning (E := Nat) (F := Nat)).run privateAvailable ()).start.available ⟨0, ()⟩)
#eval (presentEmpty.history.events.length, absentEmpty.history.events.length,
  presentEmpty.metadata.inputs.length, absentEmpty.metadata.inputs.length)

#print axioms History.bind_done
#print axioms History.failure_bind
#print axioms History.returning_map
#print axioms History.splice_normalization
#print axioms actual_leaf_right_unit

end IndexedOperationalUnits

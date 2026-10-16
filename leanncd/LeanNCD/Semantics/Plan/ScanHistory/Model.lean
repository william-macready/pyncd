import LeanNCD.Semantics.Plan.ScanHistory.Coverage
import LeanNCD.Semantics.Plan.ScanHistory.Evaluation

namespace LeanNCD.Semantics.Program.Plan.ScanHistory

variable {V : Type} {d N : Nat} {r : Registry (Carrier V)}

theorem persistent_outcome (f : RegisteredF r d)
    (ops : (s : Unit) → ScalarOps (Carrier V s))
    (ρ : Store (Carrier V) (declarations d N)) (i : Fin d) (l : Fin (N + 1)) :
    (program f N).outcome ops ρ (historyDefined f N) (persistentOccurrence f N i l) =
      some (ρ ⟨.X, stateCoord i⟩) := by
  simp [Program.outcome, program, historyDefined, persistentOccurrence, statementBody,
    persistentID, interpret, evalWith, directRead]
  rw [valuationPair_index (N := N) i l]

theorem initial_outcome (f : RegisteredF r d)
    (ops : (s : Unit) → ScalarOps (Carrier V s))
    (ρ : Store (Carrier V) (declarations d N)) (i : Fin d) :
    (program f N).outcome ops ρ (historyDefined f N) (initialOccurrence f N i) =
      some (ρ ⟨.Z, stateCoord i⟩) := by
  simp [Program.outcome, program, historyDefined, initialOccurrence, statementBody,
    persistentID, initialID, interpret, evalWith, directRead]
  rw [valuationPair_index (N := N) i 0]

theorem recurrence_outcome (f : RegisteredF r d)
    (ops : (s : Unit) → ScalarOps (Carrier V s))
    (ρ : Store (Carrier V) (declarations d N)) (i : Fin d) (k : Fin N) :
    (program f N).outcome ops ρ (historyDefined f N) (recurrenceOccurrence f N i k) =
      some (f.transition (fun j => ρ (historyAddress d N j k.castSucc)) i) := by
  simp only [Program.outcome, program, historyDefined, recurrenceOccurrence,
    statementBody, persistentID, initialID, recurrenceID]
  simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    ↓reduceIte]
  rw [recurrenceBody_interpret]
  dsimp only
  rw [valuationPair_index (N := N) i ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩]
  rfl

theorem program_admEnv (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s))
    (ρ : Store (Carrier V) (declarations d N)) :
    (program f N).AdmEnv ops ρ := by
  intro t o
  obtain rfl := defined_eq_history f t
  rcases occurrence_cases f ⟨historyDefined f N, o⟩ with
    ⟨i, l, h⟩ | ⟨i, h⟩ | ⟨i, k, h⟩
  · have ho : o = persistentOccurrence f N i l := by simpa using h
    rw [ho, persistent_outcome]
    rfl
  · have ho : o = initialOccurrence f N i := by simpa using h
    rw [ho, initial_outcome]
    rfl
  · have ho : o = recurrenceOccurrence f N i k := by simpa using h
    rw [ho, recurrence_outcome]
    rfl

theorem history_destination_iff (f : RegisteredF r d)
    (o : (program f N).Occurrence (historyDefined f N))
    (i : Fin d) (l : Fin (N + 1)) :
    (program f N).destination (historyDefined f N) o.1 o.2 = historyCoord i l ↔
      OccRef.target (⟨historyDefined f N, o⟩ : OccRef (program f N)) =
        historyDefAddr f N i l := by
  simp only [OccRef.target, historyDefAddr, Sigma.mk.injEq, heq_eq_eq, true_and]

theorem zero_fibre_iff (f : RegisteredF r d) (i : Fin d)
    (o : (program f N).Occurrence (historyDefined f N)) :
    (program f N).destination (historyDefined f N) o.1 o.2 = historyCoord i 0 ↔
      o = persistentOccurrence f N i 0 ∨ o = initialOccurrence f N i := by
  rw [history_destination_iff]
  constructor
  · intro ht
    rcases occurrence_cases f ⟨historyDefined f N, o⟩ with
      ⟨j, l, h⟩ | ⟨j, h⟩ | ⟨j, k, h⟩
    · rw [h, persistent_target, historyDefAddr_inj] at ht
      rcases ht with ⟨rfl, rfl⟩
      left
      simpa using h
    · rw [h, initial_target, historyDefAddr_inj] at ht
      obtain rfl := ht.1
      right
      simpa using h
    · rw [h, recurrence_target, historyDefAddr_inj] at ht
      exact (Fin.succ_ne_zero k ht.2).elim
  · rintro (rfl | rfl)
    · exact persistent_target f i 0
    · exact initial_target f i

theorem succ_fibre_iff (f : RegisteredF r d) (i : Fin d) (k : Fin N)
    (o : (program f N).Occurrence (historyDefined f N)) :
    (program f N).destination (historyDefined f N) o.1 o.2 = historyCoord i k.succ ↔
      o = persistentOccurrence f N i k.succ ∨ o = recurrenceOccurrence f N i k := by
  rw [history_destination_iff]
  constructor
  · intro ht
    rcases occurrence_cases f ⟨historyDefined f N, o⟩ with
      ⟨j, l, h⟩ | ⟨j, h⟩ | ⟨j, m, h⟩
    · rw [h, persistent_target, historyDefAddr_inj] at ht
      rcases ht with ⟨rfl, rfl⟩
      left
      simpa using h
    · rw [h, initial_target, historyDefAddr_inj] at ht
      exact (Fin.succ_ne_zero k ht.2.symm).elim
    · rw [h, recurrence_target, historyDefAddr_inj] at ht
      obtain rfl := ht.1
      have hm : m = k := Fin.succ_inj.mp ht.2
      subst m
      right
      simpa using h
  · rintro (rfl | rfl)
    · exact persistent_target f i k.succ
    · exact recurrence_target f i k

variable [AddCommMonoid V]

theorem collect_zero (f : RegisteredF r d)
    (ops : (s : Unit) → ScalarOps (Carrier V s))
    (ρ : Store (Carrier V) (declarations d N)) (h : (program f N).AdmEnv ops ρ)
    (i : Fin d) :
    (program f N).collect ops ρ h (historyDefined f N) (historyCoord i 0) =
      ρ ⟨.X, stateCoord i⟩ + ρ ⟨.Z, stateCoord i⟩ := by
  letI : Fintype ((program f N).Occurrence (historyDefined f N)) := inferInstance
  classical
  letI := coordDecidableEq (historyShape d N)
  have hf :
      (Finset.univ.filter fun o : (program f N).Occurrence (historyDefined f N) =>
        (program f N).destination (historyDefined f N) o.1 o.2 = historyCoord i 0) =
      {persistentOccurrence f N i 0, initialOccurrence f N i} := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact zero_fibre_iff f i o
  have hne : persistentOccurrence f N i 0 ≠ initialOccurrence f N i := by
    intro he
    have hs := congrArg Sigma.fst he
    exact (by decide : persistentID ≠ initialID) hs
  have hsum :
      (∑ o ∈ Finset.univ.filter (fun o : (program f N).Occurrence (historyDefined f N) =>
        (program f N).destination (historyDefined f N) o.1 o.2 = historyCoord i 0),
        (program f N).contribution ops ρ h (historyDefined f N) o) =
      ρ ⟨.X, stateCoord i⟩ + ρ ⟨.Z, stateCoord i⟩ := by
    rw [hf, Finset.sum_pair hne]
    simp only [Program.contribution, persistent_outcome, initial_outcome, Option.get_some]
  rw [Finset.sum_filter] at hsum
  refine Eq.trans ?_ hsum
  unfold Program.collect pushforward
  apply Finset.sum_congr rfl
  intro o _
  split_ifs <;> rfl

theorem collect_succ (f : RegisteredF r d)
    (ops : (s : Unit) → ScalarOps (Carrier V s))
    (ρ : Store (Carrier V) (declarations d N)) (h : (program f N).AdmEnv ops ρ)
    (i : Fin d) (k : Fin N) :
    (program f N).collect ops ρ h (historyDefined f N) (historyCoord i k.succ) =
      ρ ⟨.X, stateCoord i⟩ +
        f.transition (fun j => ρ (historyAddress d N j k.castSucc)) i := by
  letI : Fintype ((program f N).Occurrence (historyDefined f N)) := inferInstance
  classical
  letI := coordDecidableEq (historyShape d N)
  have hf :
      (Finset.univ.filter fun o : (program f N).Occurrence (historyDefined f N) =>
        (program f N).destination (historyDefined f N) o.1 o.2 = historyCoord i k.succ) =
      {persistentOccurrence f N i k.succ, recurrenceOccurrence f N i k} := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact succ_fibre_iff f i k o
  have hne : persistentOccurrence f N i k.succ ≠ recurrenceOccurrence f N i k := by
    intro he
    have hs := congrArg Sigma.fst he
    exact (by decide : persistentID ≠ recurrenceID) hs
  have hsum :
      (∑ o ∈ Finset.univ.filter (fun o : (program f N).Occurrence (historyDefined f N) =>
        (program f N).destination (historyDefined f N) o.1 o.2 = historyCoord i k.succ),
        (program f N).contribution ops ρ h (historyDefined f N) o) =
      ρ ⟨.X, stateCoord i⟩ +
        f.transition (fun j => ρ (historyAddress d N j k.castSucc)) i := by
    rw [hf, Finset.sum_pair hne]
    simp only [Program.contribution, persistent_outcome, recurrence_outcome, Option.get_some]
  rw [Finset.sum_filter] at hsum
  refine Eq.trans ?_ hsum
  unfold Program.collect pushforward
  apply Finset.sum_congr rfl
  intro o _
  split_ifs <;> rfl

def historyStore (f : RegisteredF r d) (N : Nat) (η : (program f N).Input) :
    Store (Carrier V) (declarations d N)
  | ⟨.X, c⟩ => inputX η c.1
  | ⟨.Z, c⟩ => inputZ η c.1
  | ⟨.H, c⟩ => history f.transition (inputX η) (inputZ η) c.2.1.val c.1

theorem historyStore_models (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input) :
    (program f N).Models ops η (historyStore f N η) := by
  refine ⟨program_admEnv f N ops _, ?_, ?_⟩
  · intro t g hg c
    cases t with
    | X =>
        have he := (Option.some_get (η.property .X)).trans hg
        obtain rfl := Option.some.inj he
        rcases c with ⟨i, u⟩
        cases u
        rfl
    | Z =>
        have he := (Option.some_get (η.property .Z)).trans hg
        obtain rfl := Option.some.inj he
        rcases c with ⟨i, u⟩
        cases u
        rfl
    | H =>
        have presence := η.property .H
        simp [hg, isInput] at presence
  · intro t c
    obtain rfl := defined_eq_history f t
    rcases c with ⟨i, l, u⟩
    cases u
    change historyStore f N η (historyAddress d N i l) =
      (program f N).collect ops (historyStore f N η) _
        (historyDefined f N) (historyCoord i l)
    refine Fin.cases ?_ (fun k => ?_) l
    · rw [collect_zero]
      rfl
    · rw [collect_succ]
      rfl

theorem models_iff_historyStore (f : RegisteredF r d) (N : Nat)
    (ops : (s : Unit) → ScalarOps (Carrier V s)) (η : (program f N).Input)
    (ρ : Store (Carrier V) (declarations d N)) :
    (program f N).Models ops η ρ ↔ ρ = historyStore f N η := by
  constructor
  · rintro ⟨h, agree, equations⟩
    have hx (i : Fin d) : ρ ⟨.X, stateCoord i⟩ = inputX η i :=
      agree .X _ (Option.some_get (η.property .X)).symm (stateCoord i)
    have hz (i : Fin d) : ρ ⟨.Z, stateCoord i⟩ = inputZ η i :=
      agree .Z _ (Option.some_get (η.property .Z)).symm (stateCoord i)
    have hh : ∀ (l : Fin (N + 1)) (i : Fin d),
        ρ (historyAddress d N i l) =
          history f.transition (inputX η) (inputZ η) l.val i := by
      intro l
      refine Fin.induction ?_ ?_ l
      · intro i
        change ρ ⟨(historyDefined f N).val, historyCoord i 0⟩ = _
        rw [equations (historyDefined f N) (historyCoord i 0), collect_zero, hx, hz]
        rfl
      · intro k ih i
        have slice :
            (fun j => ρ (historyAddress d N j k.castSucc)) =
              history f.transition (inputX η) (inputZ η) k.val := funext ih
        change ρ ⟨(historyDefined f N).val, historyCoord i k.succ⟩ = _
        rw [equations (historyDefined f N) (historyCoord i k.succ),
          collect_succ, hx, slice]
        rfl
    funext a
    rcases a with ⟨t, c⟩
    cases t with
    | X =>
        rcases c with ⟨i, u⟩
        cases u
        exact hx i
    | Z =>
        rcases c with ⟨i, u⟩
        cases u
        exact hz i
    | H =>
        rcases c with ⟨i, l, u⟩
        cases u
        exact hh l i
  · rintro rfl
    exact historyStore_models f N ops η

def history_output (f : RegisteredF r d) (N : Nat) (η : (program f N).Input) :
    (program f N).Output :=
  (program f N).outputProjection (historyStore f N η)

theorem history_output_coord (f : RegisteredF r d) (N : Nat)
    (η : (program f N).Input) (i : Fin d) (l : Fin (N + 1)) :
    history_output f N η ⟨.H, rfl⟩ (historyCoord i l) =
      history f.transition (inputX η) (inputZ η) l.val i := rfl

#print axioms historyStore_models
#print axioms models_iff_historyStore
#print axioms history_output_coord
#print axioms persistent_outcome
#print axioms initial_outcome
#print axioms recurrence_outcome
#print axioms program_admEnv
#print axioms history_destination_iff
#print axioms zero_fibre_iff
#print axioms succ_fibre_iff
#print axioms collect_zero
#print axioms collect_succ

end LeanNCD.Semantics.Program.Plan.ScanHistory

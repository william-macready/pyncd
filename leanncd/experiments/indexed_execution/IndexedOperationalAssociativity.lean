import IndexedOperationalObservationLaws
import IndexedOperationalRuns

namespace IndexedOperationalAssociativity

open LeanNCD.Semantics
open IndexedComponentTransport IndexedComponentComposition IndexedComponentExecution
open IndexedOpenComposition IndexedWitness IndexedOperationalHistory
open IndexedOperationalReassociation

variable {σA σB σC : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable [Fintype σC.Tensor] [DecidableEq σC.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB)
variable (C : MatchedComponent σC) (ab : Boundary A B) (bc : Boundary B C)

def graphTransport :
    GraphTransport (declarations (compose A B ab) C) (declarations A (compose B C bc)) :=
  ⟨addressEquiv A B C ab bc, identityEquiv⟩

def metadataTransport :
    MetadataTransport (declarations (compose A B ab) C)
      (declarations A (compose B C bc)) where
  toGraphTransport := graphTransport A B C ab bc
  tensor := tensorEquiv A B C ab bc
  domain := (embedding A B C ab bc).domain
  address_eq := fun a => (embedding_address A B C ab bc a).symm

theorem port_ext {σ : Declarations Unit} (p q : Port σ) (h : p.tensor = q.tensor) :
    p = q := by
  rcases p with ⟨t, s, ax, hs, ha⟩
  rcases q with ⟨u, v, bx, hv, hb⟩
  dsimp only at h
  subst u
  cases hs
  cases hv
  cases ha
  cases hb
  rfl

theorem metadata_inputs :
    (rightBracket A B C ab bc).inputs =
      (leftBracket A B C ab bc).inputs.map (metadataTransport A B C ab bc).port := by
  change A.inputs.map _ = ((A.inputs.map _).map _).map _
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  apply port_ext
  rfl

theorem metadata_outputs :
    (rightBracket A B C ab bc).outputs =
      (leftBracket A B C ab bc).outputs.map (metadataTransport A B C ab bc).port := by
  apply List.ext_getElem
  · simp [leftBracket, rightBracket, compose, outputPorts]
  · intro i hi hj
    apply port_ext
    simp [leftBracket, rightBracket, compose, outputPorts, outputPort,
      MetadataTransport.port, metadataTransport, tensorEquiv]
    rfl

def leftMetadata (η : A.program.Input) :=
  GraphMetadata.ofComponent (leftBracket A B C ab bc)
    (liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc) (liftInput A B ab η))
    (ab, bc)

def rightMetadata (η : A.program.Input) :=
  GraphMetadata.ofComponent (rightBracket A B C ab bc)
    (liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η)
    (ab, bc)

theorem nested_metadata (η : A.program.Input) :
    (metadataTransport A B C ab bc).Agrees (Equiv.refl (Boundary A B × Boundary B C))
      (leftMetadata A B C ab bc η) (rightMetadata A B C ab bc η) := by
  refine ⟨metadata_inputs A B C ab bc, metadata_outputs A B C ab bc,
    input_roles A B C ab bc, ?_, rfl⟩
  rintro ((t | t) | t)
  · change η.val t = (η.val t).map (fun values p => values p)
    cases η.val t <;> rfl
  · rfl
  · rfl

theorem state_transport
    {s : State (declarations (compose A B ab) C)}
    {t : State (declarations A (compose B C bc))}
    (related : IndexedOperationalRuns.StateRelated (embedding A B C ab bc) identityEquiv s t) :
    t = (graphTransport A B C ab bc).mapState s := by
  obtain ⟨available, produced⟩ := IndexedOperationalRuns.stateRelated_full
    (embedding A B C ab bc) identityEquiv (addressEquiv A B C ab bc)
    (embedding_address A B C ab bc) related
  cases s
  cases t
  simp only [GraphTransport.mapState, graphTransport, State.mk.injEq]
  exact ⟨funext available, produced⟩

theorem event_transport (e : Event (declarations (compose A B ab) C)) :
    mapEvent (embedding A B C ab bc) identityEquiv e =
      (graphTransport A B C ab bc).mapEvent e := by
  cases e <;> simp only [mapEvent, GraphTransport.mapEvent, graphTransport,
    embedding_address]

theorem run_transport
    {s : Run (declarations (compose A B ab) C)}
    {t : Run (declarations A (compose B C bc))}
    (related : IndexedOperationalRuns.RunRelated (embedding A B C ab bc) identityEquiv s t) :
    t = (graphTransport A B C ab bc).mapRun (tensorEquiv A B C ab bc) s := by
  rcases s with ⟨so, se, ss⟩
  rcases t with ⟨targetOutcome, te, ts⟩
  rcases related with ⟨eventRelation, stateRelation, outcomeRelation⟩
  dsimp only at eventRelation stateRelation outcomeRelation
  have states : ts = ss.map (graphTransport A B C ab bc).mapState := by
    induction stateRelation with
    | nil => rfl
    | cons h hs ih => exact congrArg₂ List.cons (state_transport A B C ab bc h) ih
  have events : te = se.map (graphTransport A B C ab bc).mapEvent := by
    rw [eventRelation]
    exact List.map_congr_left fun e _ => event_transport A B C ab bc e
  have outcome : targetOutcome = (graphTransport A B C ab bc).mapOutcome
      (tensorEquiv A B C ab bc) so := by
    cases outcomeRelation with
    | complete h => exact congrArg Outcome.complete (state_transport A B C ab bc h)
    | failed tag h => exact congrArg (Outcome.failed _) (state_transport A B C ab bc h)
    | blocked missing h =>
        simp only [GraphTransport.mapOutcome]
        congr 1
        · exact state_transport A B C ab bc h
        · apply List.map_congr_left
          intro row _
          congr 1
          exact List.map_congr_left fun a _ => embedding_address A B C ab bc a
    | exhausted h => exact congrArg Outcome.exhausted (state_transport A B C ab bc h)
    | contractMismatch tag h =>
        exact congrArg (Outcome.contractMismatch _) (state_transport A B C ab bc h)
    | collectorMismatch a h =>
        simp only [GraphTransport.mapOutcome]
        congr 1
        · exact embedding_address A B C ab bc a
        · exact state_transport A B C ab bc h
  simp only [GraphTransport.mapRun, Run.mk.injEq]
  exact ⟨outcome, events, states⟩

theorem nested_histories (η : A.program.Input)
    (rankA : A.program.RankCertificate) (rankB : B.program.RankCertificate)
    (rankC : C.program.RankCertificate) :
    ∃ (l : GraphHistory (declarations (compose A B ab) C))
      (r : GraphHistory (declarations A (compose B C bc))),
      l.Admissible ∧ r.Admissible ∧
      l.toRun = runChecked (leftBracket A B C ab bc).contract
        (leftBracket A B C ab bc).fragment
        (liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc)
          (liftInput A B ab η)).val ∧
      r.toRun = runChecked (rightBracket A B C ab bc).contract
        (rightBracket A B C ab bc).fragment
        (liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η).val ∧
      r = (graphTransport A B C ab bc).history.apply l := by
  obtain ⟨l, hl, lr, _⟩ := GraphHistory.ranked_default_exists (leftBracket A B C ab bc)
    (liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc) (liftInput A B ab η))
    (leftRank A B C ab bc rankA rankB rankC)
  obtain ⟨r, hr, rr, _⟩ := GraphHistory.ranked_default_exists (rightBracket A B C ab bc)
    (liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η)
    (rightRank A B C ab bc rankA rankB rankC)
  refine ⟨l, r, hl, hr, lr, rr, GraphHistory.toRun_injective ?_⟩
  rw [GraphHistory.toRun_transport (graphTransport A B C ab bc) (tensorEquiv A B C ab bc),
    lr, rr]
  exact run_transport A B C ab bc (IndexedOperationalRuns.nested_default_runs A B C ab bc η)

theorem nested_observations (η : A.program.Input)
    (rankA : A.program.RankCertificate) (rankB : B.program.RankCertificate)
    (rankC : C.program.RankCertificate) :
    ∃ (l : CompleteObservation (declarations (compose A B ab) C)
        (Boundary A B × Boundary B C))
      (r : CompleteObservation (declarations A (compose B C bc))
        (Boundary A B × Boundary B C)),
      l.metadata = leftMetadata A B C ab bc η ∧
      r.metadata = rightMetadata A B C ab bc η ∧
      l.history.toRun = runChecked (leftBracket A B C ab bc).contract
        (leftBracket A B C ab bc).fragment
        (liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc)
          (liftInput A B ab η)).val ∧
      r.history.toRun = runChecked (rightBracket A B C ab bc).contract
        (rightBracket A B C ab bc).fragment
        (liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η).val ∧
      CompleteObservation.Agrees (metadataTransport A B C ab bc) (Equiv.refl _) l r := by
  obtain ⟨l, r, hl, hr, lr, rr, eq⟩ := nested_histories A B C ab bc η rankA rankB rankC
  exact ⟨⟨leftMetadata A B C ab bc η, l, hl⟩,
    ⟨rightMetadata A B C ab bc η, r, hr⟩,
    rfl, rfl, lr, rr, nested_metadata A B C ab bc η, eq⟩

end IndexedOperationalAssociativity

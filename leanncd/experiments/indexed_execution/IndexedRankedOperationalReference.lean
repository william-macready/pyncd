import IndexedRankedOperationalCore
import IndexedOperationalUnits

namespace IndexedRankedOperationalReference

open LeanNCD.Semantics IndexedOpenComposition IndexedComponentComposition
open IndexedOperationalHistory IndexedRankedOperationalCore

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]

noncomputable def actualReferenceObservation (A : MatchedComponent σ)
    (origin : Origin A) (η : A.program.Input) (rank : A.program.RankCertificate) :
    ReferenceObservation A.matched origin.Adapters where
  observation := actualObservation A origin η rank
  start := A.program.initial η
  result := Program.Executor.run A.program RationalReference.ops A.schedule η
  correspondence := by
    change Correspondence.ExecutionCorrespondence A.matched
      (actualHistory A η rank).toRun _ _
    rw [(actualHistory_spec A η rank).2.1]
    exact Correspondence.accepted_run_correspondence A.matched η

theorem actual_reference_states (A : MatchedComponent σ)
    (origin : Origin A) (η : A.program.Input) (rank : A.program.RankCertificate) :
    List.Forall₂
      (fun state running => LedgerInvariant A.matched state ∧
        Relation A.matched state running)
      (actualReferenceObservation A origin η rank).observation.history.states
      (Correspondence.referenceSnapshots (A.program.initial η)
        (Program.Executor.run A.program RationalReference.ops A.schedule η).events) :=
  ReferenceObservation.full_relations _

noncomputable def rightUnitReference {D : Type*}
    {P : Program RationalReference.Carrier σ RationalReference.registry}
    {schedule : Program.Executor.Schedule P} {contract : Contract σ}
    {fragment : Fragment σ} {graph : Closed σ}
    {matched : SourceContractMatch P schedule contract fragment graph}
    (reference : ReferenceObservation matched D) : ReferenceObservation matched D where
  observation :=
    { metadata := reference.observation.metadata
      history := reference.observation.history.splice
        IndexedOperationalUnits.History.returning
      admissible := by
        rw [IndexedOperationalUnits.History.splice_returning]
        exact reference.observation.admissible }
  start := reference.start
  result := reference.result
  correspondence := by
    simpa only [IndexedOperationalUnits.History.splice_returning]
      using reference.correspondence

#print axioms actualReferenceObservation
#print axioms actual_reference_states
#print axioms rightUnitReference

end IndexedRankedOperationalReference

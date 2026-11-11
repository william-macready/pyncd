import IndexedRankedWitnessBoundaryTest

namespace IndexedRankedWitnessControlTest

open IndexedWitness CategoryTheory IndexedRankedWitnessCategoryTest

def strictFailureRow := IndexedRankedWitnessOutcomeTest.leafRow 0

#eval show IO Unit from do
  unless strictFailureRow.1 == "failed" do
    throw (IO.userError "P01 strict private failure: observed non-failed endpoint")

theorem exterior_legs {X : WholeInterface} (F : Span X X)
    (before after : X.Env ≃ X.Env) (w : F.W) :
    (F.rebase before after).left w = before.symm (F.left w) ∧
      (F.rebase before after).right w = after (F.right w) := ⟨rfl, rfl⟩

theorem source_composition_diagram (X : IndexedRankedOperationalSource.Object)
    (f g : IndexedRankedOperationalSource.Term X X) :
    route (.seq f g) =
      (IndexedRankedWitnessSource.erase ⋙ IndexedSource.semantics).map
        (IndexedRankedOperationalSource.arrow f) ≫
      (IndexedRankedWitnessSource.erase ⋙ IndexedSource.semantics).map
        (IndexedRankedOperationalSource.arrow g) := by
  rw [route_diagram]
  exact (IndexedRankedWitnessSource.erase ⋙ IndexedSource.semantics).map_comp
    (IndexedRankedOperationalSource.arrow f) (IndexedRankedOperationalSource.arrow g)

end IndexedRankedWitnessControlTest

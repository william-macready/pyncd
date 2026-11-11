import IndexedRankedWitnessOutcomes

/-!
Nondefault ranked operational-to-complete-witness comparison entry point.
`IndexedRankedWitnessComparison.comparison` and `IndexedRankedWitnessSource.diagram`
retain complete component-owned stores and both exterior legs, forgetting histories,
failure diagnostics and assembly origins. No unranked extension or faithfulness
is asserted. Acceptance controls live in the three `IndexedRankedWitness*Test` modules.
-/

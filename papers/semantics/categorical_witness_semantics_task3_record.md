# Prototype task 3: nested witness-span coherence

## Result

The bounded prototype proves a span isomorphism between the two *actual*
nested component composites, rebased to `A`'s input and `C`'s output. It does
not identify their fresh tensor IDs, raw programs, executions, or events.
No existing shared source, lakefile, git index, or commit was changed by this
task. The controller's previously modified lakefile and the peer's
`IndexedWitnessPartial*.lean` files were left untouched.

## Owned Lean files and symbols

- `leanncd/experiments/indexed_execution/IndexedWitnessCoherence.lean`:
  `rightInputIndexEquiv`, `leftNestedBoundary`, `rightNestedBoundary`,
  `left_boundary_square`, `right_boundary_square` explicitly derive the
  nested typed boundary matches, inherit the original certified coordinate
  domains, and prove both environment-transport squares.
  `leftBracketInputEquiv`, `rightBracketInputEquiv`,
  `leftBracketOutputEquiv`, `rightBracketOutputEquiv` transport external
  interfaces; `leftBracketSpan` and `rightBracketSpan` rebase the two actual
  component spans at the original endpoints.
  `CompatiblePair`, `wiredPairEquiv`, `compositePairEquiv`,
  `compositePair_input`, and `compositePair_output` retain complete model
  stores and verify both legs of the pair comparison.
  `CompatibleTriple` and `tripleSpan` retain exactly three complete component
  witnesses and both original AB/BC environment equations.
  `leftTripleEquiv`, `rightTripleEquiv`, `leftTripleIso`, and `rightTripleIso`
  identify each nested composite witness with that same triple and prove
  both outer legs. `bracketSpanIso` and `bracket_hom` give the span
  isomorphism and equality of quotient homs.
- `leanncd/experiments/indexed_execution/IndexedWitnessCoherenceTest.lean`:
  generic checks of both typed derived boundaries, two outer-leg laws, the
  bracket span isomorphism, and quotient equality; focused axiom audit and
  printed axioms for the new boundary, triple, and final coherence symbols.

## Observed validation and limits

`bash <prototype>/leanncd/scripts/lake-build.sh <prototype>/leanncd -q IndexedWitnessCoherence`
and the same command targeting `IndexedWitnessCoherenceTest` both exited 0.
The test build's first uncached attempt printed that its new symbols depend
only on `propext`, `Classical.choice`, and `Quot.sound`, and the namespace
axiom audits reported only standard axioms. The last targeted test build
also exited 0. No full experiment or whole-repository build was run.
There is no concrete nonconstant-coordinate/private-witness coherence
fixture: the generic theorem does retain the private complete stores, but
the fixture expansion was not attempted within this bounded task.
No source category, source functor, or process/event equivalence is claimed.

The requested aim of 40 actions and hard cap of 60 actions were exceeded
while iterating on dependent Lean proof elaboration (approximately 70 tool
actions, excluding this report). The retained context did not approach
250k tokens. This budget breach is explicit; there are no remaining
unproved obligations in the compiled generic nested-coherence module.

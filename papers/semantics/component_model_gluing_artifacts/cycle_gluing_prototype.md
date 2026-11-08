# Cyclic and hidden-store component models (authoring prototype)

Source: `leanncd/experiments/indexed_execution/IndexedComponentModelCycleTest.lean`.
This is a non-default rational **complete-store model** experiment, not a
generic gluing theorem or a claim that execution resolves a cycle.

## Case 6: downstream selection

The donor `cycleUpstream` has two models of `upstreamInput false`:
`scalarStore 0 0` and `scalarStore 1 1`, but its input is not admissible
(`cycle_upstream_not_admissible`). `cycle_boundary_zero` and
`cycle_boundary_one` compute their transported boundary inputs as
`downstreamInput true 0` and `downstreamInput true 1`. The first has no
downstream model (`cycle_zero_not_compatible` and
`cycle_zero_no_composite_extension`); the latter extends via
`reciprocal_one_model` to `cycleOneStore`. `cycle_one_model` proves its full
composite `Models` obligations by `models_glue_iff` and
`cycle_one_restrictions` checks both pullbacks. Crucially,
`cycle_composite_unique` quantifies over **every** composite complete store:
the producer equation forces its private scalar to be 0 or 1, the strict
consumer rules out 0, and `reciprocal_one_unique` identifies the remaining
consumer store. Thus `cycle_composite_admissible` holds even though the
upstream `AdmInput` does not. No rank or cycle-solving executor is asserted.

Main exports and premises: `cycle_zero_no_composite_extension` excludes any
composite `Models` witness whose `restrictUpstream` equals `scalarStore 0 0`;
`cycle_one_model` supplies a `Models` witness for the lifted `upstreamInput
false`; `cycle_composite_unique (ρ) (h : Models liftedInput ρ)` proves
`ρ = cycleOneStore`; `cycle_composite_admissible` packages existence and
uniqueness as composite `AdmInput`. The one-store gluing premises are
`cycle_upstream_one_model`, `reciprocal_one_model` transported by
`cycle_boundary_one`, and the consumer's `InputAgreement` from that model.
The uniqueness proof additionally uses both complete-store equations,
`reciprocal_zero_no_model`, and `reciprocal_one_unique`.

## Case 7: hidden multiplicity

`hiddenUpstream` produces boundary zero independently of its private scalar.
`hidden_same_boundary_via_output` transports the equality of the two producer
output projections into equal downstream inputs. Both
`scalarStore 0 0` and `scalarStore 1 0` pair with the *full* downstream model
`scalarStore 0 1` at `downstreamInput false 0`. `hidden_zero_model` and
`hidden_one_model` prove complete composite `Models` via `models_glue_iff`.
`hidden_restrictions` and `hidden_witnesses_roundtrip` recover both distinct
upstream witnesses and their common downstream witness through the generic
`witnessesEquiv`. `hidden_private_values` identifies the retained private
coordinates (0 and 1), `hidden_stores_distinct` proves store inequality, while
`hidden_final_outputs_equal` follows from `outputProjection_transport`;
`hidden_final_value` identifies the common scalar output as 1. This retains
the hidden tensor rather than existentially discarding its model.

Main exports and premises: `hidden_zero_model` and `hidden_one_model` are
complete `Models` witnesses for the lifted `upstreamInput true`, using
`hidden_upstream_zero_model`/`hidden_upstream_one_model` respectively and
`total_zero_model` at the transported boundary zero. `hidden_stores_distinct`
compares the two full stores; `hidden_final_outputs_equal` identifies their
whole final output projections; `hidden_witnesses_roundtrip` proves each
`witnessesEquiv.symm (witnessesEquiv witness) = witness`, and
`hidden_witnesses_distinct` proves their transported compatible pairs differ.

## Validation and mutation candidates

The donor's existing executable checks observed `(some 0, some 1)` for the
square body, `(none, some 1)` for the reciprocal, and `(0, 0, some 1)` for
the hidden boundary and total body; see `cycles_prototype.md`. These are body
observations, not executor observations.

Candidate single-replacement mutations (not executed; no diagnostics claimed):

- In `cycle_composite_unique`, replace `reciprocal_zero_no_model ⟨_, hB⟩`
  with `reciprocal_one_unique _ hB`, which should fail the zero-branch
  downstream-input type.
- In `hidden_private_values`, replace
  `hiddenOneStore ⟨.inl privateTensor, ()⟩ = 1 := by` with
  `hiddenOneStore ⟨.inl privateTensor, ()⟩ = 0 := by`; this would falsify the
  observed private value.
- In `hidden_final_value`, replace
  `⟨boundaryTensor, rfl⟩) () = 1 := by` with
  `⟨boundaryTensor, rfl⟩) () = 0 := by`; this would falsify the total output.

Validation: Witnesses was declared READY after its Lake build. Both
`lean-file.sh` on the exact source and `check-snippet.sh` on its source copy
passed without warnings. The in-source `#print axioms` audit for composite
admissibility, exclusion of the zero extension, both hidden models, final
output equality, and both witness-equivalence claims reported only
`propext`, `Classical.choice`, and `Quot.sound` (no `sorryAx`).
These checks do not constitute a Lake build of this non-default test file.
Estimated authoring effort was approximately 38 tool turns, below the
50-turn compiled checkpoint and 60-turn ceiling; token totals were not
measured, so no numerical context-usage claim is made.

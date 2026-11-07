# Complete-model witness prototype

Source: `leanncd/experiments/indexed_execution/IndexedComponentModelWitnesses.lean`.
This is the rank-independent witness step only; it does not assert existence,
uniqueness, execution completion, or a denotation law.

## Exported API

- `models_restrict_iff (η : A.program.Input) (ρ : Store K (declarations A B))`:
  composite `Models` on `liftInput η` iff the upstream restriction models `η`
  and the downstream restriction models `boundaryInput` of that upstream
  restriction. No model or boundary-agreement premise is required.
- `models_restrictInput_iff (η : (program A B wire).Input) (ρ : Store K (declarations A B))`:
  the same iff for any validated composite input, using `restrictInput η`.
- `models_glue_iff (η : A.program.Input) (ρA : Store K σA) (ρB : Store K σB)
  (agree : B.program.InputAgreement (boundaryInput A B wire ρA) ρB)`:
  the glued store models `liftInput η` iff `ρA` models `η` and `ρB` models
  `boundaryInput ρA`. The agreement premise ensures the downstream restriction
  of the glued store is *all* of `ρB`, including its input coordinates.
- `CompositeWitness A B wire η`: subtype of composite whole stores satisfying
  `Models` on the lifted input.
- `CompatibleWitnesses A B wire η`: dependent `Sigma` of an upstream whole
  model witness and a downstream whole model witness indexed by that upstream
  witness's transported boundary input.
- `witnessesEquiv (η : A.program.Input)`:
  `CompositeWitness A B wire η ≃ CompatibleWitnesses A B wire η`;
  both `left_inv` and `right_inv` are explicit, using whole-store inverse
  equations and proof irrelevance only for model certificates.
- `downstreamOutputIndex` maps a downstream output index to its composite
  output index; `outputIndexEquiv` gives the inverse equivalence of *all*
  composite output indices with downstream output indices.
- `outputProjection_downstream (ρ) (t) (p)` equates the composite projection at
  the mapped downstream output and coordinate with the downstream projection
  of `restrictDownstream ρ`; `liftOutput` transports a downstream output
  assignment to a composite assignment, and `outputProjection_transport (ρ)`
  states equality of those complete output functions. Output identity is
  selected by `program.output` and `output_defined`, never inferred from
  coordinate enumeration, so empty outputs retain their index.

## Proof dependencies and validation

The model iff reuses `admEnv_components` and `equations_components` (which
preserve every actual occurrence and every defined coordinate, including
private tensors and zero-writer fibers), together with
`inputAgreement_lift_iff` and `boundaryInput_restrictions`. The latter
depends on the certified `downstream_input_address` wiring equation.
The inverse uses `restrictUpstream_glueStore`,
`restrictDownstream_glueStore`, and `glueStore_restrictions`.
Output transport uses `downstream_defined_address`.

Successful command (final source, no warnings):
`bash /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/leanncd/scripts/lean-file.sh /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/leanncd experiments/indexed_execution/IndexedComponentModelWitnesses.lean`.
The same command with temporary
`#print axioms` probes appended to this source also passed, then those probes
were removed and the final source rechecked. All seven audited declarations
(`models_restrict_iff`, `models_restrictInput_iff`, `models_glue_iff`,
`witnessesEquiv`, `outputIndexEquiv`, `outputProjection_downstream`,
`outputProjection_transport`) depend only on `propext`, `Classical.choice`,
and `Quot.sound`; no `sorryAx`, `native_decide`, or custom axiom appeared.
No prohibited proof shortcuts occur in the final source.

Remaining outside this owned prototype: controller registration/build and
explicit-path commit; independent denotation corollary, fixtures, and
whole-branch review. No Lake build or commit is claimed here. The work stayed
below the 50-turn/200k hard checkpoint and the 60-turn/250k ceiling.

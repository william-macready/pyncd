# Whole-branch review — model-theorem soundness

Base `2212263c`; reviewed HEAD `e1553bb7fd45eb5f9111c06aba736e74935b6400`.
Read-only review of the finite `Unit`/rational matched-component model theorem; no
source edits, staging, commits, builds, or mutation runs.

## Findings

No load-bearing model-theorem soundness findings.

## Coverage log

- Handoff §§2–4 and targeted source map §5 read. Checked original
  `Program.Models`, `AdmInput`, output projections, `AdmEnv`/`collect`, component
  declarations and address embeddings against all four new production modules.
- `liftInput`/`restrictInput` preserve tensor-level `Option` presence, including
  empty inputs; `boundaryInput` presents each downstream input by construction.
  `glueStore` and both restrictions cover upstream whole stores and downstream
  defined tensors, with downstream input compatibility proved separately.
- `admEnv_components` ranges over every actual occurrence; `collect_*` compares
  the original finite occurrence sums, not output projections, preserving
  zero-writer equations and multiplicities. `models_restrict_iff` and
  `witnessesEquiv` explicitly include both whole stores and their inverse laws.
- `AtMostOneModels` asserts uniqueness only, not existence; the denotation-domain
  equivalence establishes the required existence using `AdmInput` witnesses.
  Output identity is carried by `outputIndexEquiv`, not only a vacuous equation.
- Local fixtures prove strict reciprocal work fails for *every* store at
  `other = 0`, despite the exhibited visible `Out = 0` equation; `other = 4`
  carries the explicit `Pre = 0`, `Out = 0`, `Audit = 1/2` complete model.
  The zero-writer producer forces its scalar to zero in any complete model.
- Geometry fixtures separately prove `some` presence for empty input tensors
  and preserve an empty output index. Axis transport gives `5,2` versus
  flattened `3,4`, although the selected total is `14` either way; the
  corresponding downstream whole model and composite gluing are checked.
- Cycle fixtures establish upstream `t=t²` models at `0` and `1`; reciprocal
  input `0` has no model, input `1` has a unique model, and the composite
  has precisely the latter witness despite upstream non-admissibility.
  Hidden-internal fixture establishes two distinct whole composite models
  (`private=0,1`) with the same boundary and final output `1`.

## Soundness assessment

- `IndexedComponentModelInputs.lean`: tensor-level presence comes from the
  validated `Input` subtype, rather than coordinatewise agreement;
  downstream input address equality uses the certified `Boundary.domain`.
  The glued store keeps upstream *private* tensors. Restriction/gluing
  inverses do not silently identify different upstream stores.
- `IndexedComponentModelTransport.lean`: `outcome_upstream` and
  `outcome_downstream` invoke existing expression-transport semantics.
  `admEnv_components` checks both summands of the *entire* defined-tensor
  type. `collect_upstream`/`collect_downstream` retain the same actual
  occurrence index (guard-true valuation subtype) and use `Finset.sum_congr`,
  retaining repeated equal-valued writers as distinct summands. The
  underlying `pushforward` in `Collection.lean` sums an empty fiber to `0`;
  `equations_components` covers every defined coordinate, not merely
  outputs. The upstream identity and downstream defined-tensor identity
  destination/adapters were checked against `CompositionProgram.lean` and
  `CompositionMatch.lean`.
- `IndexedComponentModelWitnesses.lean`: `models_restrict_iff` includes
  `AdmEnv`, input agreement, and all equations for both components; the
  downstream agreement is guaranteed for a restricted composite store.
  `models_glue_iff` requires genuine boundary compatibility. The dependent
  `CompatibleWitnesses` family retains the whole upstream model and
  downstream model at *that* upstream store's boundary; both inverse laws
  are store equalities, with proof terms ignored only by subtype equality.
  `outputIndexEquiv` preserves empty-output metadata; `liftOutput` preserves
  values on every downstream output.
- `IndexedComponentModelDenotation.lean`: `AtMostOneModels` is quantified
  over every validated input and does not entail existence; the two
  component hypotheses establish uniqueness only after a compatible
  witness exists. `admInput_lift_iff` and `admInput_restrictions_iff`
  establish the *domain* biconditional; `denotation_successive` uses the
  corresponding models and the whole-store output projection for values.
  No composite rank, phase, execution completion, model existence, or
  unrestricted uniqueness assumption is present.
- Checked all seven handoff cases against the source programs, donor
  boundaries, reciprocal primitive and fixture proofs; no output-only
  relation substitutes for the generic witness equivalence. There is no
  broader backend or root-DSL audit here.

## Validation and budget

Source/git inspection only, as requested. The controller's reported
8-task replay, 8,898-job build, namespace audits, and 12 mutation controls
were not rerun by this review. Stayed under the hard 40-turn/150k review
return limit and 60-turn/250k ceiling; an exact cumulative-token count is
unavailable, so no numerical token-compliance claim is made. Release and
integration review remain outside this lens.

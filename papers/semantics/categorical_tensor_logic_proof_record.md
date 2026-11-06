# Conditional source-contract execution correspondence

[Theorem brief](categorical_tensor_logic_theorem_brief.md) |
[Prototype results](categorical_tensor_logic_lean_prototype.md)

## Result

The conditional theorem is implemented, not inferred from fixture parity.
`IndexedOpenComposition.Correspondence.default_run_correspondence` compares
the actual `IndexedOpenComposition.runChecked` and
`Program.Executor.runValidated` default executions.

Its sole correspondence premise is a supplied `SourceContractMatch`, which
includes successful canonical closure and the local obligations below.
Intermediate simulation lemmas' capability-injectivity and collector-fiber
premises are discharged from closure and occurrence matching, not retained as
assumptions of the final theorem.

The proof layer is under
[`leanncd/experiments/indexed_execution/`](../../leanncd/experiments/indexed_execution/).
It is registered only with non-default `IndexedExecutionExperiment`, not
imported into production `LeanNCD`.

## Retained assumptions and boundaries

- Shared finite typed declarations, one exact-rational scalar sort, and
  `RationalReference.registry`/`ops`.
- Equal input roles and ordered tensor enumeration, including empty inputs;
  exact output-address coverage.
- A bijection of actual guard-admitted source occurrences and writer-list
  positions, matching destinations and ordered full read lists.
- Equal local `evalReady` results for every partial store, including readiness
  and undefinedness, at source valuation versus writer unit context.
- Equality of the entire mapped reference priority list and canonical graph
  step list. Selected-action equality is derived, never assumed.
- Default budgets. The internal same-fuel lemma also relates exhausted debug
  runs, but no arbitrary unequal-debug-fuel equivalence is claimed.

Closure does not infer a source contract. Public forged `Closed` data are not
the theorem's target. Output denotation uses the reference program's tensor
roles and `outputProjection`, retaining empty-output identity without adding a
standalone graph decoder. No rank is required for correspondence or finite
termination; a supplied rank certificate is required only to exclude blocking.
Blocking does not establish absence of a model.

## Proof inventory

| Module | Proved content |
| --- | --- |
| `IndexedCompositionClosure` | Successful closure's canonical graph, tensor/collector coverage, unique tags/capabilities, writer destination/read checks and collector membership iff destination |
| `IndexedCompositionMatch` | Local `SourceContractMatch`, valid duplicate-free ledger, published/pending/accumulator relation, first invalid tensor and initial agreement |
| `IndexedCompositionFibers` | `SourceContractMatch.capability_injective` and `collectorFiber`, derived from accepted closure |
| `IndexedCompositionRunner` | Strict remaining-work decrease, default graph nonexhaustion, no collector mismatch, append-only production and immutable established availability throughout recorded states |
| `IndexedCompositionSteps` | Contribution sum insertion and preservation; exact writer eligibility and undefinedness |
| `IndexedCompositionPublication` | Fiber emptiness/readiness equivalence, finite-sum reindexing and publication preservation, including empty fibers |
| `IndexedCompositionSelection` | First-eligible agreement derived from ordered lists; equal default budgets |
| `IndexedCompositionTerminal` | Full completion equivalence, carrying validated input availability separately from the ledger relation |
| `IndexedCompositionDiagnostics` | Ordered blocked-read diagnostics; pending ready observations cannot occur at a blocked endpoint |
| `IndexedCompositionCorrespondence` | `runFuel_correspondence`: matched outcomes, ordered events and related normalized intermediate snapshots by induction |
| `IndexedCompositionValidated` | Actual default entry-point correspondence, runtime mismatch exclusion, both default budgets sufficient, whole-store model/uniqueness/output denotation, failure implies no model, ranked no-blocking corollary |
| `IndexedCompositionSemanticResults` | Transfer through existing reference result soundness and ranked dichotomy |
| `IndexedCompositionFixtureProof` | Actual local matches and strict/total instances of the general theorem |
| `IndexedCompositionProofAudit` | Namespace axiom checks and explicit main-theorem/instance axiom reports |

`referenceSnapshots` omits the reference-only final failed wrapper.
Undefinedness still contributes its event and preserves the last running
data. No literal equality of raw machine-state lists is claimed.

The independently authored `Pre`/`Out`/`Audit` source and contract remain
unchanged. `suppliedMatch other` is inhabited for every rational `other`;
`strict_correspondence`/`strict_execution` instantiate `0`, and
`total_correspondence`/`total_execution` instantiate `4`. These are applications
of the general proof, not additional Boolean parity certificates. Their
observed six-event failure and seven-event completion, including internal
`Audit`, remain executable observations. Shared expression helpers are not
independent verification of expression interpretation.

## Executable changes

`stepFuel` and `execute` are exposed for proofs. The former inline writer
validation loop is extracted into ordered `validateWriter`/`validateWriters`
helpers, at the same position in `close`. Checks, first-error order,
collector generation, interpreter and budgets are unchanged.

A separate generic equivalence theorem against a copied legacy `Id` loop was
not completed. Behavior preservation is checked by the existing executable
suite, review of the extraction, and all seven mutation controls below.

## Validation

- Controller preparation and project-owned olean refresh succeeded without
  cold-building Mathlib.
- Controller `lake-build.sh leanncd LeanNCD Tests IndexedExecutionExperiment`
  passed. The baseline was re-observed as 93 executable rows:
  36 baseline, 12 strict-effect, 29 open-composition and 16 independent parity.
- `IndexedCompositionProofAudit` passed. The general theorem and both actual
  execution instances use only `propext`, `Classical.choice`, and `Quot.sound`.
  The namespace audit rejects non-standard axioms; no new axioms, `sorry`,
  unsafe proof shortcuts or `native_decide` were introduced.

| Mutation | Intended break observed | Restored target green | Byte-identical source |
| --- | --- | --- | --- |
| P1 collector identity | yes | yes | yes |
| P2 full-footprint readiness | yes | yes | yes |
| E1 strict array selection | yes | yes | yes |
| C1 complete collector barrier | yes | yes | yes |
| C2 capability closure | yes | yes | yes |
| C3 canonical public-run collectors | yes | yes | yes |
| V1 reference-only strict-Audit bypass | yes | yes | yes |

Final controller single-file/default builds and whole-branch review results
are recorded at close-out below.

## Process accounting

The closure-extraction follow-up **exceeded its 50-turn dispatch budget**.
The agent reported the breach but did not measure peak context. Its compiled
generic closure facts were retained; the controller completed the missing
source-match capability and fiber wrappers.

The repository token-report script reported no transcript for this Copilot
SDK session. Cumulative input-token totals and peak context could therefore
not be measured with that tool; compliance with the 175M slice budget is not
claimed from an unavailable measurement. Other proof dispatches reported
staying within their requested turn bounds.

## Close-out

Pending final single-file/default build and two whole-branch review lenses.
No remote push is authorized.

# Concrete metadata/observation laws — authoring prototype (a)

## Result and scope

The precise existing `IndexedOperationalHistory.MetadataTransport.Agrees`
and `CompleteObservation.Agrees` now have concrete identity, inverse,
composition and equality-congruence laws. Neither relation was changed or
replaced. The only source added by this dispatch is
`leanncd/experiments/indexed_execution/IndexedOperationalObservationLaws.lean`.
The controller separately registered that module. No completed history,
transport, runner, lakefile or actual-associativity source was edited here.

Base requested: `8268da1f`. The patch requires the controller's existing
`IndexedOperationalHistory` prototype and dependencies; it is not a standalone
patch applicable to a base without that prerequisite.

## Exact proved API

In `IndexedComponentTransport`:

- `Domain.symm` constructs an inverse with inverse axis, coordinate and raw
  equivalences, proving extent preservation, `raw_axis` and `coherent`.

In `IndexedOperationalHistory`:

- `MetadataTransport.refl`, `inverseDomain`, `symm`, `trans` construct actual
  metadata transports. Every constructor proves `address_eq`; composition
  uses `Domain.comp`, not cardinality/shape-based axis matching.
- `MetadataTransport.port_refl`, `port_symm`, `port_trans` identify whole
  dependent `Port` values. Tensor equality suffices only because their
  stored sort/axes are certified against the declarations; no uncertified
  port metadata is erased.
- `MetadataTransport.agrees_refl`, `agrees_symm`, `agrees_trans` prove the
  existing five-part relation: ordered full input ports, ordered full output
  ports, all input roles, all Option-valued tensor inputs with coordinate
  pullback, and adapter data via the supplied equivalence.
- `MetadataTransport.history_refl`, `history_symm`, `history_trans` connect
  the concrete constructors to the existing full-history transport.
- `CompleteObservation.agrees_refl`, `agrees_symm`, `agrees_trans` combine
  the exact metadata laws with exact full-history equality.
- `MetadataTransport.agrees_congr` substitutes equal metadata records.
  `CompleteObservation.agrees_congr` substitutes equal metadata and histories
  independently; admissibility-proof identity is irrelevant. These are
  equality-congruence laws, not a new sequencing theorem.

The laws quantify over arbitrary declarations, metadata, complete observations
and adapter types/equivalences. Their symmetry/transitivity hypotheses are
exactly the existing agreement judgments, not assumed universal agreement.
Complete observations still require `history.Admissible`. No new run
existence premise, input/history linkage or admissibility strengthening was
introduced.

## Controls actually compiled

`MetadataLawFixtures` clones `Fixtures.emptyMetadata`:

1. Identity agrees on the original metadata, including its empty tensor.
2. `absentEmptyMetadata` changes input ports/roles/presence consistently,
   retaining outputs. Agreement is disproved directly by input-list length.
3. Every graph address nevertheless sees equal initial availability, because
   the original empty tensor has no coordinates.
4. The same candidate agreement is independently disproved using its
   Option-input conjunct at `emptyExternalInput` (`none` cannot equal `some`).

Thus the controls distinguish metadata from address-only equality and inspect
both the full-port and Option-input conjuncts. These are kernel-checked
positive/negative controls, not dynamic mutation runs. No new mutation cycle
or claim of full runner/triple-integration validation is made.

## Observed verification

All commands used the prescribed absolute wrapper paths:

- Refresh `IndexedOperationalHistory` with `lake-build.sh`: exit 0.
- Compile exactly `experiments/indexed_execution/IndexedOperationalObservationLaws.lean`
  with `lean-file.sh`: exit 0; final `compile.log` contains only axiom reports.
- Named `lake-build.sh` build of `IndexedOperationalObservationLaws`: exit 0,
  `Build completed successfully (3002 jobs)`, captured in `build.log`.
  Dependencies replay existing warnings; the new module has none.
- The printed constructor and agreement/congruence theorem axiom sets are
  `[propext, Quot.sound]`, with no `sorryAx`, new axiom or added proof
  assumption. Source contains no `sorry` or `admit`.
- `prototype.patch` was generated mechanically using `git diff --no-index`
  from `/dev/null` to the final compiled source. Diff exit 1 denotes the
  expected addition. `git apply --check --reverse prototype.patch`: exit 0.

Final source SHA-256:
`9b99fe102c012800e500f11d0453cf99d9d71310d4edd5f9e7a36e913bfcadc9`.

## Remaining work and limits

No obligation remains for the requested concrete metadata/complete-observation
equivalence and equality-congruence laws. This does not reprove
`nested_metadata`/`nested_observations`, generic splice associativity, or the
common-leaf actual-run splice theorem; those remain with their owning work.
No independent whole-branch review or full experiment build was run here.
No commit, stage, merge or push was performed.

Manual accounting is fewer than 45 assistant/tool rounds. Exact peak-context
and cumulative-token telemetry is unavailable: the prescribed token-report
command for session `e513127c-9c86-44d6-9ad8-bf82d0bb54c1` returned
`no transcript for session ...`. This is not a measured budget pass.

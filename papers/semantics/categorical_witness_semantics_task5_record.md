# Task 5 — bounded composition observations

## Deliverable and validation

Prototype checkout: `categorical-witness-semantics-prototype`, starting detached
at `0a3b8e97` (slice base `a9c9a647`). The only prototype source addition is
`leanncd/experiments/indexed_execution/IndexedWitnessCompositionTest.lean`;
production witness APIs, core donors, and the already-present experiment glob
were not changed. This controller record lives in the setup checkout.
Committed explicitly as `2cbf39e9` (`test(semantics): discriminate witness
composition observations`), with the requested Copilot coauthor trailer.

Validation:

- `bash <prototype>/leanncd/scripts/lake-build.sh <prototype>/leanncd IndexedExecutionExperiment`
  succeeded: 8653 jobs.
- Subsequent `bash <prototype>/leanncd/scripts/lean-file.sh <prototype>/leanncd experiments/indexed_execution/IndexedWitnessCompositionTest.lean`
  succeeded without file-local warnings.
- `#audit_axioms IndexedWitnessCompositionTest` checked 223 constants against
  the standard-axiom whitelist. No `sorry`, `admit`, `native_decide`, custom
  axiom, or fabricated missing-input/undefined model is used.
- Six scenario fixtures in three grouped workitems; 36 named theorems,
  including complete-model/compatibility prerequisites.

## Workitem 1 — strict/total and hidden compatible witnesses

Exact donors:

- `IndexedComponentModelLocalFixtures.producerInput`, `producerStore`,
  `totalStore`, `producer_model`, `total_model`, `strict_no_model`.
- `IndexedComponentModelLocalTest.totalCompositeStore`,
  `total_composite_model`.
- `IndexedComponentModelCycleTest.hiddenZeroStore`, `hiddenOneStore`,
  `hidden_zero_model`, `hidden_one_model`, together with
  `IndexedComponentModelCycleFixtures.hiddenUpstream`, `totalDownstream`,
  `hiddenBoundary`, `privateTensor`, `boundaryTensor`.

Delta: promote actual composite complete models to the **all-input**
`componentSpan.W` and apply `allInputWiredEquiv`, rather than repeat
fixed-input `witnessesEquiv` roundtrips.

| Fixture identifiers (under `IndexedWitnessCompositionTest`) | Kernel-checked observations |
|---|---|
| `Audit.strict`, `strict_span_empty`, `strict_wired_empty` | Neither composite span nor wired pullback has a complete witness, at any input. |
| `Audit.totalSpanWitness`, `totalWired`, `total_wired_observation` | Wired downstream private audit cell is `1/2`; final output cell is `0`. |
| `Hidden.zero`, `one`, `zeroWired`, `oneWired`, `private_observations`, `distinct_wired`, `equal_final_env` | Upstream private cells remain `0` and `1`; both final cells are `1`; whole final environments are equal but wired witnesses are unequal. |

The hidden distinction is observed on actual wired stores, not on proof terms,
and would be lost by an output-only relation.

## Workitem 2 — empty ports and directional geometry

Exact donors:

- `IndexedComponentCompositionPortFixtures.emptyProducerComponent`,
  `emptyConsumerComponent`, `emptyBoundary`, `emptyConsumerOut`.
- `IndexedComponentCompositionAxisFixtures.axisProducer`, `axisConsumer`,
  `axisBoundary`.
- `IndexedComponentModelGeometryFixtures.Axis.producerInput`, `producerStore`,
  `producer_model`, `consumerInput`, `transportedPre`, `flattenedPre`.
- `IndexedComponentModelGeometryTest.Axis.compositeStore`, `composite_model`.
- `IndexedComponentTransportTest.srcShape`, `dstShape`, `swapDomain`, `p`, `q`.

Delta: inspect interface port membership and UID/axes metadata explicitly,
and evaluate the actual `boundaryEnvEquiv`, `allInputWiredEquiv`, and
`compositeWiredIso` legs at discriminating coordinates.

| Fixture identifiers | Kernel-checked observations |
|---|---|
| `Empty.outputPort`, `output_port_present`, `output_port_identity` | Required composite empty output is in the interface port list; output-index transport returns exactly `emptyConsumerOut`; retained UID is `3`, axes are `[⟨51, 0⟩]`. |
| `Empty.env_singleton`, `producer_env_singleton`, `metadata_not_equal` | Both output Env carriers are singleton. Producer output interface (UID `0`) is nevertheless not equal to the composite output interface (UID `3`). |
| `Axis.sourceEnv`, `witness`, `wired`, `directional_cells`, `boundary_leg_cells` | Forward boundary at `p=(0,2)` is `5`, at `q=(1,0)` is `2`. |
| `Axis.wrongFlattened`, `flattened_fails_boundary_leg` | Canonical flattening gives `(3,4)`, not `(5,2)`. |
| `Axis.wrongReversed`, `reversed_cells`, `reversed_fails_boundary_leg` | A well-typed reverse-style control—swap followed by incorrect canonical-layout unflattening of the downstream input—gives `(4,3)`, not `(5,2)`. This is not an ill-typed literal use of `coord.symm`. |
| `Axis.both_legs` | Actual iso's original-input legs agree; both final-output legs observe `14`. |

Limit: the donor axis producer has no input ports, so its original-input leg
alone is vacuous. The triple below supplies nonconstant original-input leg
controls. The donor scalar output `14` is unchanged by flattening
(`selected_sum_does_not_distinguish`); scalar-output-only tests would miss this
bug. Boundary cells, not just the selected sum, are essential.

## Workitem 3 — concrete three-source bracketings

The existing axis consumer has only scalar output, so it cannot be the middle
component of a triple with two nontrivial coordinate boundaries. This is an
explicit donor extension, not a claim that the existing producer/consumer pair
already has a shaped downstream output.

Exact donor patterns/values:

- `IndexedComponentCompositionAxisFixtures.producer`: six per-coordinate
  statements, canonical coordinate enumeration, occurrence/writer matching,
  ordered publication schedule, and contract construction.
- Its consumer's read-footprint/matching pattern, and
  `IndexedComponentTransportTest.pointPolicy`.
- Typed `swapDomain.policy` transports that policy for the reversed shape.
- Geometry `producerStore` and `transportedPre` seed the nonconstant values.
- `IndexedComponentCompositionAxisFixtures.axisConsumer` is reused unchanged
  as the third component; a fresh offset input/store has a kernel-proved model
  for the existing consumer program.

Delta: **two** test-only matched affine-copy instances, not merely a transported
third scalar consumer:

- `Triple.A = copyComponent false`: shape `srcShape` (`2×3`), UIDs `40/41`,
  pointwise input plus `10`.
- `Triple.B = copyComponent true`: shape `dstShape` (`3×2`), UIDs `70/71`,
  pointwise input plus `20`.
- `Triple.C = axisConsumer`: existing scalar-output consumer.
- `Triple.ab` uses `reverseDomain` (the typed inverse of `swapDomain`);
  `Triple.bc` uses `swapDomain`. Both coordinate maps genuinely transpose.
  No core-language extension or production program is changed.

Models `a_model`, `b_model`, `c_model`, and whole-environment compatibility
`ab_compatible`, `bc_compatible` construct `Triple.triple :
CompatibleTriple A B C ab bc`. Actual bracket witnesses come from
`leftTripleEquiv.symm` and `rightTripleEquiv.symm`.

| Fixture identifiers | Kernel-checked observations |
|---|---|
| `boundary_observations` | AB at `swapDomain.coord p/q`: `(15,12)`; BC at `p/q`: `(35,32)`. |
| `flattened_boundary_controls` | Wrong canonical flattening at AB: `(14,13)`; at BC: `(33,34)`. Both boundaries discriminate independently. |
| `triple_leg_observations`, `bracket_original_input_cells`, `left_leg_cells`, `right_leg_cells` | Original input `(5,2)` and final output `134`, through both bracketings and the actual applied `bracketSpanIso`. |
| `left_transport_cells`, `right_transport_cells` | Nested left boundary square observes `35`; nested right boundary square observes `15`. |
| `bracket_applied`, `returned_private_stores` | Applied bracket iso returns exactly `rightWitness`; subsequent right-triple extraction returns the complete original triple, not just its output. |
| `source_private_cells`, `bracket_private_observations`, `returned_bracket_private_cells` | Distinguishable source/private output cells `15`, `35`, `134` survive in both bracket stores and the actually returned witness. |
| `bracket_private_identities` | Left bracketing UIDs: `(164,286,3)`; right bracketing UIDs: `(82,285,7)` for A/B/C output tensors. Equal denotation does not identify fresh private tensor IDs. |

The two affine-copy fixtures are deliberately nonidentity computations.
Administrative identity graph spans are not core-copy programs. No event,
trace, schedule/process-equivalence, or runtime phase-barrier claim is made.

## Controller mutation controls and limits

Public proofs are compiled observations, not a copied-program mutation probe.
The controller can mutate copied actual map bodies next and re-run the numeric
controls: hidden upstream cells, empty output UID/port metadata, geometry
forward cells, both triple boundaries, bracket private stores, and original
input cells. No mutation run is claimed here.

Acceptance 3 (cyclic downstream selection), generic category/identity laws,
and existing empty-input presence tests remain in `IndexedWitnessPartialTest`
and `IndexedWitnessTest`; they were not duplicated.

Budget: the 40-turn aim was exceeded during finite dependent-coordinate
schedule proofs. Close-out remains within the hard 60-turn / 250k context
limits; no nested agents were launched. A measured cumulative token-report
total is unavailable for this noninteractive dispatch. The full compiled
subset is the delivered file, not a silently truncated group.

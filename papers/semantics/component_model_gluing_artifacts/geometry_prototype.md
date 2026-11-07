# Empty/axis whole-store geometry prototype

Scope: handoff acceptance cases **4–5 only**, authored in
`follow-directions-component-model` against base `2212263c`.
Source: `leanncd/experiments/indexed_execution/IndexedComponentModelGeometryFixtures.lean`.
No controller modules, Lake registration, generic gluing, restrictions, or model
bijection are implemented or imported here.

## Verified construction and observations

- Empty donors: `emptyProducerComponent`, `emptyConsumerComponent`,
  `emptyValidatedInput`, and `emptyBoundary` from
  `IndexedComponentCompositionPortFixtures`.
  Both complete stores eliminate the first zero-extent axis. Model admission
  eliminates the zero statement index; input agreement and equations eliminate
  the first coordinate axis. Binding validity is proved separately by finite
  tensor cases. Lifted external and boundary-transported input bindings are
  explicitly `some`, and the missing binding is explicitly invalid.
  Output roles and original tensor UIDs remain true/`0` and true/`1`.
- Axis donors: `axisProducer`, `axisConsumer`, `axisBoundary`, `producerCoord`,
  `producer`, `consumer`, `readPre`, and `consumerBody` from
  `IndexedComponentCompositionAxisFixtures`.
  The entire producer store is the inverse canonical destination enumeration
  index plus one, matching the six actual producer statement literals.
  The downstream input reads that store through **the actual boundary's**
  matched tensor and coordinate equivalence. The whole consumer store retains
  all six input cells and scalar output `14`.
  Admission explicitly enumerates defined tensors, statements, and admitted
  valuations; no guard-admitted source occurrence is omitted.
- Producer enumeration: `[1, 2, 3, 4, 5, 6]`.
  Intended transposition: `p=(0,2) ↦ (2,0) ↦ 5`,
  `q=(1,0) ↦ (0,1) ↦ 2`; corner inputs `(0,0)=1`, `(1,2)=6`.
  Wrong flattening: `p ↦ (1,0) ↦ 3`, `q ↦ (1,1) ↦ 4`.
  Both repeated-read sums are `14`, but the input families are provably distinct.
  Thus an output-total-only observation cannot discriminate this defect.

Observed source-copy output:

```text
(true, true)
([1, 2, 3, 4, 5, 6], (5, 2), (3, 4), 14)
```

## Exported names and signatures

All names below have the prefix `IndexedComponentModelGeometryFixtures.`.
Signatures use the same open donor namespaces as the source; `Axis` also opens
`IndexedComponentTransportTest (srcShape dstShape p q)`. No implicit parameters
are added to these concrete exports.

The following are API signature transcriptions, not executable Lean snippets.

### `Empty` definitions

```text
liftedInput : InputBinding (K := RationalReference.Carrier)
  (σ := declarations emptyProducerComponent emptyConsumerComponent)
producerStore : Store RationalReference.Carrier emptyProducerDeclarations
transportedPre : Coord [⟨51, 0⟩] → ℚ
consumerInput : emptyConsumer.Input
consumerStore : Store RationalReference.Carrier emptyConsumerDeclarations
```

### `Empty` theorems

```text
producer_input_present :
  emptyValidatedInput.val emptyExternalInput = some (fun p => Fin.elim0 p.1)
lifted_input_present :
  liftedInput (.inl emptyExternalInput) = some (fun p => Fin.elim0 p.1)
transported_input_present :
  consumerInput.val emptyConsumerPre = some transportedPre
missing_not_valid : ¬ emptyProducer.ValidInput emptyMissingInput
producer_model :
  emptyProducerComponent.program.Models RationalReference.ops
    emptyValidatedInput producerStore
consumer_model :
  emptyConsumerComponent.program.Models RationalReference.ops
    consumerInput consumerStore
output_roles_and_identity :
  emptyProducerComponent.program.output emptyProducerPre = true ∧
  emptyConsumerComponent.program.output emptyConsumerOut = true ∧
  emptyProducerDeclarations.uid emptyProducerPre = 0 ∧
  emptyConsumerDeclarations.uid emptyConsumerOut = 1
```

### `Axis` definitions

```text
producerInput : producer.Input
producerStore : Store RationalReference.Carrier producerDeclarations
transportedPre : Coord srcShape → ℚ
consumerInput : consumer.Input
consumerStore : Store RationalReference.Carrier consumerDeclarations
flattenedPre : Coord srcShape → ℚ
```

### `Axis` theorems

```text
producer_admitted : producer.AdmEnv RationalReference.ops producerStore
producer_model :
  axisProducer.program.Models RationalReference.ops producerInput producerStore
consumer_admitted : consumer.AdmEnv RationalReference.ops consumerStore
consumer_model :
  axisConsumer.program.Models RationalReference.ops consumerInput consumerStore
producer_statement_values :
  (List.finRange 6).map (fun i => producerStore ⟨0, producerCoord i⟩) =
    [1, 2, 3, 4, 5, 6]
transported_input_present : consumerInput.val 0 = some transportedPre
transported_distinguishing_values :
  transportedPre p = 5 ∧ transportedPre q = 2 ∧
  transportedPre (0, 0, ()) = 1 ∧ transportedPre (1, 2, ()) = 6
consumer_values :
  consumerStore ⟨0, p⟩ = 5 ∧ consumerStore ⟨0, q⟩ = 2 ∧
  consumerStore ⟨1, ()⟩ = 14
flattened_distinguishing_values : flattenedPre p = 3 ∧ flattenedPre q = 4
coordinate_transport_distinct : flattenedPre ≠ transportedPre
selected_sum_does_not_distinguish :
  transportedPre p + (transportedPre q + (transportedPre p + transportedPre q)) = 14 ∧
  flattenedPre p + (flattenedPre q + (flattenedPre p + flattenedPre q)) = 14
```

## Validation and proposed mutation

`lean-file.sh` passed after the construction and again after the presence and
coordinate-discrimination additions. The final complete source passed
`check-snippet.sh`, including the observations above. The four model witnesses
and `coordinate_transport_distinct` each reported only
`[propext, Classical.choice, Quot.sound]`. Proofs use source tactics and
`decide +kernel`; no `native_decide` or sorry is used.
No Lake build was requested: baseline donor oleans were already available,
and source-copy checking did not mutate controller modules.

Proposed unique replacement in **`Axis.transportedPre` only**:

```text
-- Original:
fun c => producerStore
  ⟨(axisBoundary.matched ⟨0, rfl⟩).val, (axisBoundary.domain ⟨0, rfl⟩).coord c⟩
-- Candidate replacement:
fun c => producerStore
  ⟨0, (canonicalLayout dstShape).enumerate
    ((canonicalLayout srcShape).enumerate.symm c)⟩
```

This candidate is compiled as the separate `flattenedPre` definition and
its concrete counterexample is proved. **No replacement mutation cycle was
run, and no diagnostic kill is claimed.** Future integration can consume these
whole-store witnesses and presence facts when wiring ModelInputs gluing and
restrictions; this prototype does not depend on those new modules.

Budget: approximately 20 tool-interaction rounds and under 25k retained context
tokens (estimate, not a measured token-report). Neither the 50-turn/200k
checkpoint nor the 60-turn/250k hard cap was reached.

# Component-composition port fixture prototype

This is a compiled authoring artifact, **not a live implementation plan**.
The real module is
`leanncd/experiments/indexed_execution/IndexedComponentCompositionPortFixtures.lean`,
namespace `IndexedComponentCompositionPortFixtures`.
It supplies exactly three related local fixture pairs. It does not construct,
match, execute, or count events of a composite.

## Donors and changed fields

1. **Scalar pair.** `IndexedComponentCompositionLocalFixtures` supplies the
   genuine `producer`, `consumer other`, schedules, contracts, fragments,
   graphs, and `producerMatch`/`consumerMatch other`; every one is reused.
   Only whole-port packaging and an explicit boundary are added.
   `producerPre : Fin 1 = 0` is the producer's sole declared tensor, UID 0,
   scalar axes `[]`, no inputs, output Pre, with the existing +1/-1 occurrences.
   Consumer `Fin 3` names are `consumerPre = 0`, `consumerOut = 1`,
   `strictAudit = 2`, UIDs 0/1/2, all scalar. Input Pre and output Out are exact
   whole-port lists. Audit remains private **and defined**, with the donor's
   strict expression intact. The boundary is a singleton port equivalence
   and `Domain.id []`, not name- or address-matching.

2. **Zero-writer scalar pair.** Reuses the producer's `Fin 1` declarations,
   scalar Pre identity, input=false/output=true roles, and the local consumer
   at `other = 4`. The new upstream program has statements=0; all dependent
   occurrence fields eliminate `Fin 0`. The schedule contains exactly its
   scalar publication. Its fragment has no writers; its contract has the
   **singleton Pre collector with empty capabilities** and scalar output Pre.
   Closure and a standalone source/contract match are proved locally.
   There is neither a forward-copy writer nor a removed collector.

3. **Whole empty pair.** Donor:
   `Semantics.ExecutableReferenceTest.emptyDeclarations`, `emptyRole`,
   `emptySchedule`, and `presentEmpty` (lines 345–381).
   Changes: each side declares `Fin 2`, input index 0 and defined output index 1,
   rather than the donor's single tensor/non-output role. Upstream UIDs
   10/0 name external input/Pre, axes `[⟨41, 0⟩]`. Downstream UIDs
   0/1 independently name input Pre/output Out, axes `[⟨51, 0⟩]`.
   The executable follow-up changed only these UID functions and their
   metadata observation from 410/411 and 510/511: append order now yields
   composite UIDs `[20, 0, 3]`, distinguishing it from UID sorting.
   Both have statements=0 and no keys, writers, address collectors, readable
   addresses, or address outputs: their domains have no coordinates.
   Exact singleton **whole-tensor** inputs/outputs nevertheless survive in
   each `MatchedComponent`, including output sort/axes metadata.
   `emptyDomain` explicitly pairs the sole axes, proves equal zero extents,
   and supplies coherent coordinate/raw-coordinate equivalences between
   the differently identified shapes. It is not an address-only stand-in.

## Exports and premises

- `producerComponent`, `consumerComponent (other : ℚ)`,
  `scalarBoundary (other : ℚ)`: the donor local matches are their only match
  inputs; no additional premise or composite match is assumed.
- `zeroProducer`, `zeroProducerSchedule`, `zeroProducerContract`,
  `zeroProducerFragment`, `zeroProducerGraph`, `zeroProducer_close`,
  `zeroProducerMatch`, `zeroProducerComponent`, `zeroBoundary`.
  `zeroBoundary` has type `Boundary zeroProducerComponent (consumerComponent 4)`.
- `emptyProducerDeclarations`, `emptyConsumerDeclarations`, their named
  tensor identities, `emptyProducer`/`emptyConsumer`, corresponding
  `Schedule`, `Contract`, `Fragment`, `Graph`, `_close`, and `Match` exports;
  `emptyProducerComponent`, `emptyConsumerComponent`, `emptyDomain`,
  `emptyBoundary`. All matches are standalone and premise-free.
- Raw bindings: `emptyPresentInput`, `emptyMissingInput`, and
  `emptyConsumerPresentInput`. `emptyValidatedInput` retains upstream
  tensor-presence evidence. `emptyMissing_rejected` proves that upstream
  tensor validation returns `.error emptyExternalInput`;
  `emptyPresent_validated` proves `.ok emptyValidatedInput`.
  These controls use existing tensor validation, not fabricated addresses.
- `audit_private other` preserves the private defined role.
  `zeroProducer_publication` proves the sole event is `.sealed Pre 0`.
  `zeroProducerRun`, `emptyProducerRun`, and `emptyConsumerRun` are local runs.

## Observed standalone outputs

| Observation | Checked result |
|---|---|
| Scalar producer | complete; 3 local events; published Pre = 0 |
| Scalar consumer, Pre bound to 0, `other=0` | failed; 3 local events |
| Scalar consumer, Pre bound to 0, `other=4` | complete; 4 local events; Pre/Out/Audit = 0/0/1⁄2 |
| Zero-writer upstream | complete; 1 publication, value 0; no produced event |
| Zero-writer source executor | complete; 1 local event |
| Present empty upstream/downstream, source and checked local executors | complete; 0 events on each side |
| Missing empty upstream input | tensor validation rejects external input; checked run is invalidInput |
| Empty whole metadata | inputs/outputs UIDs [10]/[0], [0]/[1]; output axes retain zero extents and distinct axis identities |

The actual registered module build and `check-snippet.sh` on its **exact
bytes** pass. `port_fixtures.patch` is mechanically generated from the module
diff, with its reverse applicability checked; it is not a handwritten plan
patch. No `sorry`, new axiom, `native_decide`, or `unsafe` occurs.
The follow-up refreshed this patch as a complete new-file payload and
rechecked the changed fixture's exact bytes.

**Initial checkpoint:** composites were not tested here. The follow-up
`port_composite_prototype.md` records actual assembled graph and source
execution for these same three shapes; correspondence still requires the
genuine match constructor. No broad checker, ranks, phase theorem, model
gluing, category, extra fixture shape, or mutation machinery was added.

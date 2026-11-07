# Constructed graph/source executable checkpoint

Real module: `IndexedComponentCompositionTest.lean`, namespace
`IndexedComponentCompositionTest`, importing the genuine assembly and local
port fixtures. This is a bounded prototype receipt, not an implementation
plan or a composite correspondence proof.

## Construction and donors

Every tested contract, fragment, and graph is the corresponding
`IndexedComponentComposition.contract`, `fragment`, and `graph` applied to
the existing components/boundary. Each source program/schedule is the
actual `program`/`schedule` constructor on those same arguments.
`scalarClose_ok other`, `zeroClose_ok`, and `emptyClose_ok` apply the genuine
assembled `close_ok` theorem. Graph observations execute the **constructed
graph's own steps** with `execute`, not a separately authored graph or
an addition of local event counts. Source observations use `runValidated`
on the actual whole constructed source.

Donors are the three shapes in `IndexedComponentCompositionPortFixtures`.
Scalar producer/consumer source, strict-array helpers, and matches are
unchanged. Zero upstream retains its singleton empty-capability collector.
The only fixture changes are empty declaration UID functions and the exact
metadata observation: upstream input/Pre now have UIDs 10/0 (formerly
410/411); downstream inputPre/Out now have UIDs 0/1 (formerly 510/511).
Uniqueness is proved coherently. Roles, signatures, occurrences, ports,
and boundary adapter are unchanged.

`graphEventRow`/`sourceEventRow` are deterministic event display projections,
not admission or runtime checkers. All scalar coordinates are unit and
valuations are singleton; source rows identify tensor UID and statement.
Graph rows retain writer tag/capability or publication tensor UID.
Expected values are checked through the existing failure-raising `check`.

## Actual observations

### Scalar strict and total

The exact constructed writer census is
`[(20,202,0), (22,204,0), (41,403,3), (61,603,5)]`
(tag, capability, destination UID).
Collectors are `[(0,[202,204]), (3,[403]), (5,[603])]`.
The exact graph step order is write20, write22, publishPre0, writeOut41,
publishOut3, writeAudit61, publishAudit5: **4 writers + 3 publications**.
There is no forwarding-copy writer or duplicate boundary collector.
The only address output is downstream Out UID3; Audit UID5 is not output.

| Run | Actual ordered graph events | Published Pre / Out / Audit |
|---|---|---|
| `other=0` | write20:+1, write22:−1, publish0:0, write41:0, publish3:0, undefined61 | 0 / 0 / absent |
| `other=4` | write20:+1, write22:−1, publish0:0, write41:0, publish3:0, write61:1⁄2, publish5:1⁄2 | 0 / 0 / 1⁄2 |

The actual source has the corresponding entire event sequence, with
occurrences `(UID0,stmt0)`, `(UID0,stmt1)`, `(UID3,stmt0)`,
`(UID5,stmt0)`. It independently fails on event **6**, after publication
of Out, or completes after **7** events. Both source final snapshots are
asserted, including private Audit availability.

### Zero-writer upstream

Constructed writers are only `[(41,403,3), (61,603,5)]`.
Collectors are `[(0,[]), (3,[403]), (5,[603])]`.
The actual graph and source both complete with **5** events:
publishPre0:0, writeOut:0, publishOut3:0, writeAudit:1⁄2,
publishAudit5:1⁄2. Exact source/graph event sequences and final
Pre/Out/Audit = 0/0/1⁄2 are asserted. The first event publishes the
empty-writer sum; Audit work has not been removed.

### Empty boundary/output and external-input presence

The constructed whole input port is upstream external input UID20.
The exact constructed whole output is **downstream Out**:
`emptyOutputs.map Port.tensor = [emptyOutTensor]`, with tensor
`.inr ⟨emptyConsumerOut, rfl⟩`, UID3, sort unit, axes `[⟨51,0⟩]`.
Its actual program output role is true; upstream Pre UID0's role is false.
Separately, `emptyContract.outputs = []`: an empty address list does not
erase the whole output metadata.

Actual present-empty binding is accepted by the source and constructed
graph; both complete with **0** events. Omitting the required upstream
empty input rejects at tensor validation, UID20, before execution.
This tests tensor presence, not vacuous coordinate readiness.

The two-fault binding **simultaneously** omits upstream required input
UID20 and supplies an unexpected binding for downstream defined Out UID3;
both Boolean presence/role mismatches are asserted. The actual append
order is `[20,0,3]`, not UID sorted. Validation reports:

- actual append-order schedule: UID20;
- reversed (downstream-first) schedule: UID3;
- explicitly supplied UID-sorted schedule `[0,3,20]`: UID3.

All three rejection identities are also proved by reduction. The sorted
schedule retains the actual source keys and proves tensor coverage and
nonduplication; it is only the validation-order control for this same shape.

## Exact proof-only integration API

All names below are in namespace `IndexedComponentCompositionTest`.
Scalar aliases take `(other : ℚ)`; zero and empty aliases take no arguments.

| Family | A / B / wire (in PortFixtures namespace) | Constructed exports |
|---|---|---|
| Scalar | `producerComponent` / `consumerComponent other` / `scalarBoundary other` | `scalarDeclarations`, `scalarProgram`, `scalarSchedule`, `scalarContract`, `scalarFragment`, `scalarGraph`, `scalarRawInput`, `scalarGraphRun`, `scalarSourceResult`, `scalarSourceObservation`, `scalarPre`, `scalarOut`, `scalarAudit`, `scalarClose_ok` |
| Zero | `zeroProducerComponent` / `consumerComponent 4` / `zeroBoundary` | `zeroDeclarations`, `zeroProgram`, `zeroSchedule`, `zeroContract`, `zeroFragment`, `zeroGraph`, `zeroRawInput`, `zeroGraphRun`, `zeroSourceResult`, `zeroSourceObservation`, `zeroPre`, `zeroOut`, `zeroAudit`, `zeroClose_ok` |
| Empty | `emptyProducerComponent` / `emptyConsumerComponent` / `emptyBoundary` | `emptyDeclarations`, `emptyProgram`, `emptySchedule`, `emptyContract`, `emptyFragment`, `emptyGraph`, `emptyPresentRaw`, `emptyMissingRaw`, `emptyBothFaultsRaw`, `emptyGraphRun`, `emptySourceResult`, `emptyInputTensor`, `emptyPreTensor`, `emptyOutTensor`, `emptyInputs`, `emptyOutputs`, `emptyClose_ok` |

Empty control proofs: `emptyOutput_provenance`, `emptyOutput_role`,
`emptyPre_private`, `emptyAddressOutputs`, `emptyMissing_rejection`,
`emptyBothFaults_rejection`, `emptyBothFaults_reverse_rejection`,
`emptyBothFaults_sorted_rejection`. `emptyUidSortedSchedule` is the explicit
UID-order control.

The common constructors' `input_roles`, `tensor_order`, `outputs_exact`,
and `graph_steps` specialize directly to each row's A/B/wire; no local
composite match is assumed or hand-authored.

## Verification and exact patches

The changed real PortFixtures module build is green. The real new Test
module and exact-byte snippet checks are green. Test registration is
requested from the parent (lakefile is not owned by this actor).
`port_composite_test.patch` is a mechanically generated new-file payload;
`port_fixtures.patch` is refreshed as the complete current PortFixtures
new-file payload. Both reverse-check against the actual files.

**Not proved:** composite `SourceContractMatch`, default-run correspondence,
model gluing, rank/phase properties, or category laws. The match actor's
compiled partial does not yet export `compose_match`; executable agreement
here is not substituted for that proof. No waiting/polling, extra shape,
new axiom, `sorry`, `native_decide`, `unsafe`, or new runtime checker is used.

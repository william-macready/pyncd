# Compiled foundational prototype (not a composition match)

The three new modules are registered only in `IndexedExecutionExperiment`.
They were compiled using `bash leanncd/scripts/lake-build.sh
<worktree>/leanncd IndexedExecutionExperiment` (8619 jobs, green, including
the separately owned `IndexedComponentClosureFacts` registration). Its
targeted wrapper build also succeeded (2962 jobs). These observations establish
typechecking, not a closed composite or execution agreement. No `sorry`,
`native_decide`, `unsafe` or new axioms are used.

## Scope and checked premises

`IndexedComponentCompositionScope` exports `Port`, `MatchedComponent`,
`Boundary`, `Tensor`, `declarations`, `upstream`, `downstream`,
`downstreamTensor_input`, `downstreamTensor_defined`,
`downstream_no_upstream_write`, `upstream_no_downstream_read`,
`upstreamId`, `downstreamId`, their injectivity proofs and `ids_disjoint`.
`MatchedComponent σ` requires `[Fintype σ.Tensor]` and
`[DecidableEq σ.Tensor]`, and packages an actual `Program`, `Schedule`,
`Contract`, `Fragment`, `Closed`, and supplied `SourceContractMatch`.
Its ordered input/output port lists are duplicate-free and exact against
the program predicates. Each port stores sort and axes with equality to
the declared signature; axes record empty domains as well.

`Boundary A B` supplies an explicit equivalence from B input tensors to A
output tensors and a `Domain` adapter per input. The output role is
necessarily defined by `Program.output_defined`. The composite declaration
tensor type is exactly `σA.Tensor ⊕ B.program.Defined`, with checked even
and odd UID partitions. The A embedding maps to `inl`; the B embedding
maps inputs through the boundary into A output tensors and defined tensors
to `inr`. The proven structural noninterference facts apply to all B
defined destinations and all A tensor reads. Natural occurrence tags and
capabilities can use `upstreamId`/`downstreamId` without collision; the
writer and collector transports that apply them remain to be built.

## Source and ordering

`IndexedComponentCompositionProgram` exports `program A B wire`,
`upstreamDefined`, `downstreamDefined`, `definedEquiv`, and
`occurrenceEquiv` (a genuine equivalence with the disjoint union of *all*
guard-admitted source occurrences). It branches on the exact disjoint
tensor summands and retains the component statement counts, valuation
counts, guards and dependent destination/body contexts. The bodies are
transported by `IndexedComponentTransport.transport` using the respective
embeddings. `upstream_body`, `downstream_body`,
`upstream_destination`, `downstream_destination`,
`upstream_footprint` and `downstream_footprint` are proved equations,
including ordered repeated reads. Composite input roles are A's and
output roles are B's. `inputPorts`/`outputPorts` preserve the exact
whole-tensor metadata and have separate exactness and Nodup proofs,
including for empty output tensors.

`IndexedComponentCompositionSchedule` exports `keyEquiv` (both occurrence
and coordinate-publication keys), `definedTensor?`,
`tensorOrder`/`tensorOrder_nodup`/`tensorOrder_complete`,
`keyOrder`/`keyOrder_nodup`/`keyOrder_complete`, and `schedule`.
Tensor order appends A's full order to B's original order filtered to
defined tensors. Key order appends A's original key order to B's original
key order using inverse `keyEquiv`; no keys or zero-writer publication
coordinates are dropped, synthesized or sorted.

## Next bounded dependency split

1. Transport the two component fragments and full contract (including
   all noninput collectors, zero-writer fibers, ordered capability lists,
   readable addresses and output addresses), using parity renaming for
   both tags and capabilities. Prove mapping and concatenation properties.
2. Derive composite `close_ok` from the component closure facts and the
   independently supplied generic `IndexedComponentClosureFacts`; derive
   canonical priority for the appended `keyOrder`. No match premise may
   be introduced for this step.
3. Construct `SourceContractMatch` using `occurrenceEquiv`, the transported
   fragment equivalences, footprint and evaluation transport, and the
   derived closure/priority facts. Only then run the split producer/consumer
   fixture and discriminate private collisions, unequal-axis adapters,
   empty ports, zero-writer collectors and repeated contributions.

The parent re-observed the **whole donor fixture**, not this composition:
six events ending in `Audit` failure for `other = 0`, and seven-event
completion for `other = 4`. These observations do not constitute a split
component example or a composite match. No fragment, composite contract,
closed graph, composite `SourceContractMatch`, or execution theorem is
claimed in this prototype.

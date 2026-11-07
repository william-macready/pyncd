# Concrete component assembly prototype

This is compiled prototype authoring, **not** a verified implementation plan
or a composite `SourceContractMatch`. The source is
`leanncd/experiments/indexed_execution/IndexedComponentCompositionAssemble.lean`;
its `IndexedComponentCompositionAssemblyAudit.lean` is in the nondefault
`IndexedExecutionExperiment` target. Nothing is imported into production.

## Exact exported API

All symbols below are in `IndexedComponentComposition`. Implicit parameters
are `{σA σB : Declarations Unit}` with `[Fintype σA.Tensor]`,
`[DecidableEq σA.Tensor]`, `[Fintype σB.Tensor]`, and
`[DecidableEq σB.Tensor]`. Explicit parameters are
`(A : MatchedComponent σA) (B : MatchedComponent σB)` and, where shown,
`(wire : Boundary A B)`.

| Symbol | Result / statement |
|---|---|
| `compositeFintype A B` | `Fintype (declarations A B).Tensor`, using the actual `σA.Tensor ⊕ B.program.Defined` partition |
| `compositeDecidableEq A B` | `DecidableEq (declarations A B).Tensor` |
| `contract A B wire` | `Contract (declarations A B)`; exactly `assembledContract (upstream A B) (downstream A B wire) upstreamId downstreamId (tensorOrder A B) (program A B wire).input A.contract B.contract` |
| `fragment A B wire` | `Fragment (declarations A B)`; exactly `assembledFragment (upstream A B) (downstream A B wire) upstreamId downstreamId A.fragment B.fragment` |
| `graph A B wire` | `Closed (declarations A B)`; exactly `assembledGraph` at those embeddings, IDs, tensor order, input predicate, local contracts and fragments |
| `closureScope A B wire` | `ClosureScope (upstream A B) (downstream A B wire) (program A B wire).input A.contract B.contract` |
| `tensorOrder_length A B` | `(tensorOrder A B).length = Fintype.card (declarations A B).Tensor` |
| `close_ok A B wire` | `close (contract A B wire) (fragment A B wire) = .ok (graph A B wire)` |
| `input_roles A B wire` | `(contract A B wire).input = (program A B wire).input` |
| `tensor_order A B wire` | `(contract A B wire).tensors = (schedule A B wire).tensors` |
| `outputs_exact A B wire z` | `z ∈ (contract A B wire).outputs ↔ (program A B wire).output z.1 = true`, for every `z : Address (declarations A B)` |
| `canonical_steps A B wire` | `canonicalSteps (contract A B wire) (fragment A B wire) = (canonicalSteps A.contract A.fragment).map (mapStep (upstream A B) upstreamId) ++ (canonicalSteps B.contract B.fragment).map (mapStep (downstream A B wire) downstreamId)` |
| `graph_steps A B wire` | `(graph A B wire).steps` equals that same appended mapped list |

`canonical_steps` is a direct instantiation of
`canonicalSteps_assembled`, not a new priority/source-match proof.

## Derived scope premises

The five fields of `closureScope` are proved, not additional hypotheses:

1. `upstream_roles`: composite input at `.inl t` equals `A.contract.input t`,
   by the actual program definition and `A.matched.input_roles`.
2. `downstream_defined`: if `B.contract.input t = false`, the mapped tensor
   is `.inr ⟨t, …⟩`, whose actual composite input is false.
3. `defined_partition`: **every** noninput target address, including each
   coordinate, has an A-defined preimage if its tensor is `.inl`, or a
   B-defined preimage if it is `.inr`. The latter uses the actual embedding's
   coordinate equivalence (`address_lift`), not an assumed inverse or a
   tensor-only coverage claim.
4. `defined_disjoint`: A-defined tensors map to `.inl`; B-defined tensors
   map to `.inr`. Hence their address images cannot intersect.
5. `boundary_collector`: every B-input address maps to an A collector. The
   boundary pairs its tensor with an A output; `A.program.output_defined`,
   `A.matched.input_roles`, and
   `(ClosureFacts.of_close A.matched.close_ok).collector_iff` establish the
   collector at the corresponding A address. `address_lift` provides that
   coordinate using the upstream embedding and the boundary's mapped tensor.

Thus `close_ok` uses only both **local** `matched.close_ok` proofs, the
checked parity injections/disjointness, `tensorOrder_nodup`,
`tensorOrder_length`, and these five derived fields. In particular no
composite `close`, `validateWriters`, or `SourceContractMatch` is a premise.
`tensorOrder_length` follows from `tensorOrder_complete`, Nodup, and
`toFinset = Finset.univ`. Empty-domain address obligations are vacuous only
when there is no coordinate; `inputPorts`/`outputPorts` and their exactness
lemmas in `IndexedComponentCompositionProgram` retain whole-port metadata
even for zero-coordinate tensors.

## Next bounded match task

Construct a `SourceContractMatch (program A B wire) (schedule A B wire)
(contract A B wire) (fragment A B wire) (graph A B wire)`. Its first four
fields are the exact exported `close_ok`, `input_roles`, `tensor_order`,
and `outputs_exact` above. The remaining fields require an equivalence
`SourceOccurrence (program A B wire) ≃ Fin (fragment A B wire).writers.length`,
then `writer_destination`, ordered `writer_reads`, `eval_agrees`, and
`priority`. Reuse `occurrenceEquiv A B wire`, the two local
`matched.sourceToWriter`, `assembled_writer_length` and its indexed
upstream/downstream lemmas, transported destination/footprint/evaluation
facts, `keyEquiv`/`keyOrder`, and `canonical_steps`/`graph_steps`.
No composite match or source priority has been proved here.

## Verification

Both `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd
IndexedComponentCompositionAssemblyAudit` and the same command with
`IndexedExecutionExperiment` completed successfully (8600 and 8623 jobs,
respectively). The audit prints only `propext`, `Classical.choice`, and
`Quot.sound` for `closureScope`, `tensorOrder_length`, `close_ok`,
`canonical_steps`, and `outputs_exact`, and checks the namespace with
`#audit_axioms`. No `sorry`, new axioms, `unsafe`, or `native_decide`.

`assembly_prototype.patch` is generated mechanically from the committed
source, audit, target registration, and this note; it is not hand-edited.

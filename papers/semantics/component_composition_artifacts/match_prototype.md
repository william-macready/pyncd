# Indexed component composition match prototype

Status: compiled coherent partial, **not** a constructed `SourceContractMatch`.
The non-default `IndexedComponentCompositionMatch` target builds successfully.

- `sourceToWriter A B wire` composes the actual composite occurrence split,
  both component matches' occurrence-to-writer equivalences, `finSumFinEquiv`,
  and the assembled writer-list length. `writer_upstream` and
  `writer_downstream` prove the indexed entries of that assembled list.
- `writer_destination_upstream` transports the upstream destination.
  `writer_reads_upstream` and `writer_reads_downstream` use the ordered
  footprint transport; `writer_reads` covers every composite occurrence.
  `eval_agrees_upstream` and `eval_agrees_downstream` restrict **any** partial
  store by the appropriate embedding, then apply the local match and
  `evalReady_transport`; `eval_agrees` covers every composite occurrence.
- **Next proof:** establish the defined-downstream address identity
  `(downstream A B wire).address ⟨t.val, p⟩ = ⟨.inr t, p⟩`
  for `t : B.program.Defined`, using `t.property`. In the attempted
  `writer_destination_downstream`, the mapped writer/local destination
  reduction succeeds, but `simp [downstream, downstreamTensor, t.property,
  Domain.id]` leaves a dependent `cast` around the identity domain's `coord`.
  The heterogeneous equality between the downstream domain at `t.val` and
  `Domain.id (σB.signature t.val).axes` is provable, but eliminating it directly
  fails because the domain's codomain depends on the embedded tensor. Prove
  the address identity without assuming destination equality, then derive
  `writer_destination_downstream` and dispatch the two cases for
  `writer_destination`.
- **After that:** prove composite collector-capability lookup from the
  complete disjoint mapped collector images; prove each mapped `keyStep`
  equation, then use component `matched.priority`, `keyOrder`, and
  `graph_steps` for full `priority`. Assemble `compose_match` with
  `close_ok`, `input_roles`, `tensor_order`, `outputs_exact`, and the proven
  writer fields. No execution, reached-store, rank, or fiber premise is needed.

The attached patch is generated from committed source bytes, not a proposed
unverified proof. This receipt does not claim that match construction is done.

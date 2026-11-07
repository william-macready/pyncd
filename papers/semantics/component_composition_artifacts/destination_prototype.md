# Indexed component composition destination prototype

Status: the complete composite `writer_destination` equation is compiled in
`IndexedComponentCompositionMatch.lean`. This does not construct
`SourceContractMatch` or establish priority.

All exported declarations below are in `IndexedComponentComposition`, with
implicit `{σA σB : Declarations Unit}`, finite decidable tensor types, and
explicit `(A : MatchedComponent σA) (B : MatchedComponent σB)`
`(wire : Boundary A B)`.

- `downstream_defined_address A B wire t p` proves
  `(downstream A B wire).address ⟨t.val, p⟩ =
  ⟨(downstreamDefined A B wire t).val, p⟩` for **every**
  `t : B.program.Defined` and `p : Coord (σB.signature t.val).axes`.
- `writer_destination_downstream A B wire o` proves that the assembled writer
  indexed by `sourceToWriter A B wire ((occurrenceEquiv A B wire).symm (.inr o))`
  has destination
  `⟨((occurrenceEquiv A B wire).symm (.inr o)).1.val,
  (program A B wire).destination
    ((occurrenceEquiv A B wire).symm (.inr o)).1 o.2.1 o.2.2⟩`.
- `writer_destination A B wire o` proves, for **every**
  `o : SourceOccurrence (program A B wire)`,
  `(fragment A B wire).writers[sourceToWriter A B wire o].destination =
  ⟨o.1.val, (program A B wire).destination o.1 o.2.1 o.2.2⟩`.

The defined-downstream address proof first identifies its domain
heterogeneously with `Domain.id` via `t.property`. Its private generic
`domain_coord_of_heq_id` transports that equality across the dependent shape
equality before `Sigma.ext` checks the tensor and arbitrary coordinate.
The downstream writer equation uses the local component's
`B.matched.writer_destination`, the actual mapped writer and that address
identity. The full equation dispatches the actual `occurrenceEquiv` cases,
reusing the already-compiled upstream equation. No composite match, closure,
execution agreement, rank hypothesis, or extra premise was introduced.

Verification: `bash <worktree>/leanncd/scripts/lake-build.sh
<worktree>/leanncd IndexedComponentCompositionMatch` succeeds. An exact
`#print axioms` audit after rebuilding reports only `propext`,
`Classical.choice`, and `Quot.sound` for both
`downstream_defined_address` and `writer_destination`; temporary audit
commands were removed. The accompanying `match_prototype.patch` was
mechanically regenerated from `/dev/null` against the complete current
173-line Match source, retaining all previously compiled partial proofs.

Budget: the <=30-action-turn target was exceeded while resolving the dependent
domain cast; the 60-turn/250k-context hard limits were not exceeded.

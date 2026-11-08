# Task 2 prototype status

Worktree: `/Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-prototype`, detached at `3fc437a28834d614ca730caaa78c1026c658efd0` (base `a9c9a647a04e260e21c8e5c624a0bac3fa13ef20`).

`leanncd/experiments/indexed_execution/IndexedWitnessComposition.lean` introduces
`boundaryEnvEquiv`, its directional `boundaryEnv_apply`, `Span.graph`,
`SpanIso.graphIdentity`, `SpanIso.graphComp`, `graphHom_identity`,
`graphHom_comp`, `Span.rebase`, `SpanIso.rebaseGraphs`,
`compositeInputEquiv`, `compositeOutputEquiv`, and checked exterior
input/output and boundary-projection lemmas. That portion compiled with
`bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd IndexedWitnessComposition`
before the unfinished all-input comparison was added. The boundary
equivalence uses `Equiv.piCongrLeft'` over the explicit port matching and
`Equiv.piCongrRight` over the per-port coordinate equivalences; no
interface equality is assumed.

The same file contains **uncompiled draft** definitions `wiredSpan`,
`toWired`, `fromWired`, `fromWired_toWired`, `toWired_fromWired`,
`allInputWiredEquiv`, `compositeRebasedSpan`, `compositeWiredIso`, and
`composition_hom`. The current targeted build fails at
`toWired_fromWired`: the nested pullback witness must be normalized
using its two compatibility proofs, the indexed `witnessesEquiv` inverse,
and subtype/Sigma proof irrelevance. `fromWired_toWired` compiles using
`Subtype.heq_iff_coe_eq` to handle the changed input index. The drafted
composition equation has *not* been established, and neither focused
composition tests nor the namespace axiom audit were run.

No commit was made. The intended task-2 complete-model span comparison
is **not** proved. The investigation exceeded the requested 40-turn aim
and 60-turn hard budget; retained context remained below 250k tokens.

## Controller repair

The controller reproduced the failed inverse goal, then normalized the
graph witness and downstream input with the two pullback compatibilities.
It proved the inverse by `restrictInput_liftInput`,
`restrictUpstream_glueStore` and `restrictDownstream_glueStore`, using
subtype heterogeneous extensionality for the dependent model predicates.
The targeted `IndexedWitnessComposition` build passed. This is a direct
repair of the unresolved obligation, not a new design or erased failure.
`IndexedWitnessTest` now imports the composition module and prints the
axioms of `boundaryEnvEquiv`, `allInputWiredEquiv`, `compositeWiredIso`
and `composition_hom`; its existing whole-namespace audit covers the
new declarations. Validation and commit receipts follow in the plan record.

# Whole-branch review — LENS1 categorical/model soundness

Scope: `e7102517227546d4aa8f1b04d2db14a453641bda..72888777b619779bb6aad35d7cf97cdb51f26df4`, actual replay source. Read-only review; no fixes or commits.

## Findings

**Clean — no high-confidence, load-bearing categorical/model soundness findings.**

## Checked surfaces

- `WholeInterface` retains typed whole ports and empty-tensor presence; `inputEquiv` reconstructs validated bindings.
- `SpanIso` relates full witness apexes over **both** legs; quotient pullback congruence, both units and associativity use span isomorphisms rather than raw pair equality.
- `componentSpan` indexes every validated input and complete `Models` store; authoritative `Models` includes body-definedness, input agreement and all defined equations.
- `boundaryEnvEquiv` uses downstream-to-upstream `Boundary.matched` and coordinate transport in the correct opposite direction on environments; graph identity/composition and exterior rebasing leave distinct metadata-bearing objects distinct.
- `toWired`/`fromWired` use indexed restriction/gluing and inverse input lifts. `compositeWiredIso` and `composition_hom` account for both exterior legs, including downstream output projection.
- Nested boundaries and both adapter squares reconcile the two tagged source bracketings with the **same** `CompatibleTriple`; both triple isos commute with the original input and final output legs. No raw UID or raw pair equality is asserted.
- Restricted domain/value extraction requires injective left legs. `component_injective_iff` tests complete-store uniqueness, `component_composite_domain`/`component_composite_value` assume at-most-one for **both** components and connect to authoritative admissibility/successive-denotation; absent witnesses yield `none`.
- Tests exercise strict failure versus total survival, two distinct private witnesses with equal output, empty-interface metadata/presence, the downstream-selection counterexample, nonconstant/reversed/flattened boundary cells, and a three-model triple with distinct bracketed private UIDs and concrete private values. The test-only observation copy and parity modules were checked at their declaration surfaces.
- The changed synthesis, interface document and Lean discoverability text keep source functor, event/process identity, execution sequencing and arbitrary-span partial extraction outside the proved scope.

## Limits

This lens is source-level and did not rerun Lean: the separate full three-target build was in progress and was deliberately neither polled nor duplicated. Existing replay/targeted-build/mutation receipts were treated as reported evidence, not independently reproduced here. The one requested token-headroom check returned “no transcript” for this sub-agent session ID, so a measured token count is unavailable; the review remained below the 40-turn aim and 60-turn stop boundary.

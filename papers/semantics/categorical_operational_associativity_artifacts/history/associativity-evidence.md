# Actual structural history associativity

New sole source: `IndexedOperationalHistoryAssociativity.lean`, under
`leanncd/experiments/indexed_execution/`. No finalized source or lakefile edited.
The controller registered this module and its named dependencies.

## Result

`binary_associativity` closes the previously recorded common-leaf flattening
gap. Given arbitrary supplied histories with structural `BinaryHistory`
witnesses for A–B and then (A–B)–C, and local B/C rank certificates, it constructs
a structural A–(B–C) witness and proves EXACT history equality after the
controller's actual `graphTransport`. Composite execution agreement is NOT
a premise. The proof does not invoke nested run isomorphism, `run_transport`,
`nested_default_runs`, `nested_histories`, or final-store agreement.

`actual_nested_histories` instantiates this law on the actual default
`runChecked` histories of BOTH named constructors. It returns admission proofs,
the supplied A history, both left structural binary witnesses, the right
structural witness, both exact actual runner equalities, and the transported
full history equality. Ranks are constructed by `compositeRankCertificate`.
`right_nested_tree` exposes the actual B–C structural witness inside any
successful right outer witness, with the original A–B boundary-derived B input.

## Common space and algebra, not a run-iso shortcut

The common space is the RIGHT constructor's complete state/event space.
`state_A`, `state_B`, `state_C` prove full availability-function and ORDERED
ledger equality for all source states under the actual address/identity maps.
The C equation explicitly retains completed A and B private availability and
both ordered ledger prefixes. These are not output-only projections.
`event_A/B/C` use actual `address_A/B/C` and `identity_A/B/C`, preserving every
ordered production/publication/undefinedness event.
`lift_A/B/C` lift these equalities to entire reusable histories.

`right_input` proves the right outer boundary input is the actual lifted
original A–B boundary input. `boundary_C` proves the original B–C C-input square
using complete-state reconstruction and full stores; it reuses
`RunsPhases.original_bc_input`, not assumed input agreement.
`shared_right` transports the actual full shared cut, with no synthetic event,
stuttering or duplicate cut.

For reached A/B joins, the proof constructs three common-space leaf histories,
their two binary intermediate histories and BOTH nested shared-cut splicing
certificates, then applies the reusable
`SharedSplice.associative_eq` DIRECTLY.
The source events/states/terminal failure are never reordered or discarded.
Empty phases need no positive cut-length premise; all shared equalities remain
valid for coincident cuts.

Failure handling is explicit in the GENERAL theorem, not delegated to fixtures:

- A failure immediately yields the right failed-prefix constructor using
  `lift_A`. No B/C histories, stores or boundary-derived inputs are constructed.
- After A success, B failure yields the failed B–C witness; no C history/input
  or completed B store is required. Prefix transport and map/append laws give
  equality. Existing `BinaryHistory.splices` exposes the `.none` absorbing case.
- Only after both A and B succeed are C histories compared through the proven
  original boundary square, and the three-leaf associative law applied.
  C failure and C success are BOTH covered by that law: it places no success
  premise on C's terminal outcome.

`BinaryHistory.sound` validates the constructed right tree against the actual
right default runner. It is not used to derive left/right history equality;
that equality has already been proved by structural common-leaf algebra.

## Verification and artifacts

Named dependency build and final
`bash .../scripts/lake-build.sh .../leanncd IndexedOperationalHistoryAssociativity`
exited 0. The final output is `associativity-build.log`.
Source-package/control script: `associativity_verify.py`.
Separate additive patch: `associativity.patch`; source hash:
`associativity_source.json`. Original history/composition patches are untouched.

The script checks copied-source destructive identity/private-state controls,
records actual diagnostics in `associativity_mutations.json`, and removes its
generated module. Registered full mutation-manifest execution remains a
controller release gate; this report does not claim that full gate was run.
Printed axiom reports cover the structural theorem, right tree and actual
instantiation; only the ordinary Lean axioms are permitted.

## Scope and telemetry

This closes the actual structural associativity/instantiation obligation from
`composition-evidence.md`, rather than merely restating the parent run-iso
result. Concrete whole-metadata observation laws belong to the separate
metadata-laws agent and are not changed here. Full reference/cut transport and
the four actual run phase cases remain supplied by the already compiled parent
and sibling modules.

Bounded follow-up: at most 50 assistant/tool rounds. Exact peak/cumulative
telemetry is unavailable (the prescribed earlier tool found no Copilot
transcript); no context warning occurred. No commits/merge/push.

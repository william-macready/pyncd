# New-session brief: a source category and witness-semantics functor

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

## Copyable launch instruction

```text
Read papers/semantics/categorical_source_functor_handoff.md on latest
local main. Prepare and verify one implementation plan, then execute it,
for a source category of the existing sealed matched components and
certified administrative wires, with a genuine Lean functor into the
completed witness-span category.

Audit the source presentation, arrow equivalence, wire geometry and
universe levels before freezing the plan. Connect source composition
to the actual IndexedComponentComposition.compose constructor, not just
to an unrelated free category. Preserve complete-model witnesses and
explicit interface transports. Do not reimplement the witness category,
change core Program semantics, or begin ranked phase/trace work.

Keep this to one denotational slice. Preserve unrelated edits/worktrees,
use the repository release gates, merge locally when green and reviewed,
and do not push. Report any load-bearing design blocker rather than
weakening the deliverable or expanding the scope.
```

**Process weight for implementation: Full.** This adds a source presentation,
new categorical laws and a functor soundness surface.
This is a session brief, not a verified execution plan: new source types,
module names, compiled patches and mutation controls remain to be authored
and checked. The present brief does not implement or certify these goals.

## 1. Starting state and reading order

The witness-category formalization has landed on local main. It supplies:

- Metadata-bearing whole interfaces and validated environment equivalences.
- Complete-model spans across all inputs, modulo span isomorphism.
- Pullback composition, quotient congruence, identities and associativity.
- Component composition comparison commuting with both exterior legs.
- Actual nested component coherence through compatible model triples.
- The restricted injective-left partial-map interpretation.

Start from latest **local** main, not a stale remote base.
The witness integration `f2abbe8a` and synthesis `11ca0fc1` are provenance,
not required future starting HEADs. Recheck actual declarations.
The missing result is a source category and source functor, not another
proof of target-category laws.

Read [the synthesis](categorical_tensor_logic_semantics.md), Sections 6.10,
10.2-10.3 and Appendix A.9; [the witness completion record](categorical_witness_semantics_record.md);
and [the Lean instructions](../../leanncd/AGENTS.md).
Use [the landed-witness handoff](categorical_witness_semantics_handoff.md)
for targeted prerequisite verification, not a separate implementation task.

## 2. Source presentation: representation audit

Prefer a small, explicit presentation of **sealed matched-component syntax
with administrative wires**, rather than all Tensor Logic syntax or a
general St/Br/PROP library.
Audit and justify the following decisions before drafting executable tasks:

1. **Objects:** retain the existing `WholeInterface` metadata. Use a distinct
   source-object type, for example a thin wrapper, so its source homs do not
   install a competing category instance on the target's `WholeInterface`.
   The functor's object map returns the underlying interface.
2. **Generators:** include actual `MatchedComponent` leaves, explicit
   administrative wires, and typed composition. Leaves include the supplied
   local match; do not infer matches or require model existence, uniqueness,
   execution success or ranking.
3. **Wire geometry:** carry an explicit port bijection and certified
   coordinate-domain transport, with direction, inverses and empty-port
   metadata accounted for. Reuse `Domain` where applicable. UID renaming
   must be explicit; names and equal extents are not an adapter.
   An arbitrary environment bijection can transform values and is not by
   itself evidence of an administrative coordinate wire.
4. **Arrow equivalence:** give a stated syntactic/generated congruence,
   covering units, associativity, wire identity/composition/inverses and
   the constructor-assembly comparison below. Prove it is an equivalence
   compatible with composition, and descend operations to quotient arrows.
   Do not define source equality merely as equality of target denotations:
   that would evade the source-law obligation.
5. **Size and imports:** audit the new source universes against the existing
   `Category.{1} WholeInterface` target and pinned Mathlib functor API.
   Do not assert same-universe local smallness or finite rational model sets.
   Keep new modules in the nondefault experiment with a discoverable entry
   point, not production `LeanNCD`.

A typed term/word presentation with a generated congruence is a recommended
starting point, not a preverified implementation. Explain precisely which
equations define that presentation and prove each is sound under interpretation.
Logical proof shortcuts are forbidden; inductive relation generators are
definitions of source syntax/equivalence, not permission to add Lean axioms.

## 3. Required connection to actual component assembly

For actual components $A,B$ and a supplied `Boundary`, let $L(A)$ denote
their source leaf, and let $C$ be the existing constructed composite.
The source presentation must express its assembly comparison, including:

- $i$: upstream input interface to the composite input interface.
- $b$: upstream output interface to downstream input interface.
- $o$: composite output interface to downstream output interface.

The required source-arrow comparison has the following direction
(ordinary right-to-left composition):

```math
\operatorname{wire}(o)\circ L(C)\circ\operatorname{wire}(i)
\;\sim\;
L(B)\circ\operatorname{wire}(b)\circ L(A).
```

Construct source wires whose induced environment maps agree with
`compositeInputEquiv`, `boundaryEnvEquiv` and `compositeOutputEquiv`.
Do not silently replace these maps by convenient identity maps.
State whether the comparison is a generating assembly equation or a derived
source theorem; in either case prove its interpretation using
`composition_hom` and its complete-witness comparison.

For three components, connect both **actual** constructor bracketings to
the same source composite after the inherited interface transports.
Reuse the boundary squares and `bracket_hom` to prove semantic soundness.
Source associativity must not assert literal equality of fresh UIDs, nested
declarations or raw `Program` values.

A free category on leaves alone is insufficient if its composition is never
related to this existing assembly constructor.

## 4. Functor and exact semantic scope

Supply an actual Mathlib `Functor`, not a function called an interpretation:

- The object map returns the source object's whole interface.
- A component leaf maps to the quotient arrow of its existing `componentSpan`.
- A certified administrative wire maps to `graphHom` of its induced
  environment equivalence.
- Typed composition maps to target composition.
- Prove well-definedness for every source congruence generator, then identity
  and composition preservation on quotient arrows.

Reuse target `graphHom_identity`, `graphHom_comp`, `composition_hom` and
the existing nested coherence instead of duplicating span proofs.
The leaf interpretation must retain all validated inputs and complete
private stores, including strict body-definedness and hidden multiplicity.
Do not reduce it to an output-only relation.

The result is a denotational functor for this specified source presentation
in the finite decidable `Declarations Unit`, exact-rational, explicitly
wired matched-component profile. It does not make arbitrary core programs
into a category, solve cycles, prove faithfulness, or establish process laws.

## 5. Discriminating acceptance goals

These are proposed goals, not newly compiled fixtures or measured controls.
The verified plan must give exact donor/delta, fixture and mutation counts,
and observed failure diagnostics:

| Goal | Existing donor and required distinction |
| --- | --- |
| Both source units and wire composition/inversion | Use the nonconstant `Axis` case in [witness composition tests](../../leanncd/experiments/indexed_execution/IndexedWitnessCompositionTest.lean); a reversed adapter or omitted wire must differ |
| Actual assembly equation and both exterior legs | Extend `Axis.sourceEnv` and `Axis.wrongReversed` donors from those tests; check the source comparison and interpreted arrow, not just an apex bijection |
| Empty interfaces retain metadata and input presence | Extend `Empty.metadata_not_equal` in those tests and `emptyInputEnv` in [witness tests](../../leanncd/experiments/indexed_execution/IndexedWitnessTest.lean); singleton environment carriers must not identify source objects automatically |
| Two actual bracketings of three components | Extend the `Triple` fixture, especially `bracket_applied`, `returned_private_stores` and `bracket_private_identities`, in witness composition tests; retain nontrivial maps and distinct nested private IDs |
| Complete-witness rather than output-only leaf meaning | Use `hidden_witnesses_distinct`/`hidden_outputs_equal` in witness tests and `strict_no_domain`/`total_domain` in [partial-map tests](../../leanncd/experiments/indexed_execution/IndexedWitnessPartialTest.lean) |

Add generic source-category and functor-law proof instances and namespace
axiom audits. Use independent source construction where practical; a test
that restates the interpreter's own definition is not a discriminating oracle.
Do not call an administrative source identity event-free execution, or add
a core copy to obtain units.

## 6. Targeted source map

Use `rg -n`, then approximately 40-60-line windows. Avoid whole large modules.

| Identifiers @ file | Purpose |
| --- | --- |
| `WholeInterface`, `inputInterface`, `outputInterface`, `inputEquiv`, `outputEquiv` @ [IndexedWitnessInterface.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessInterface.lean) | Source-object metadata and functor object map |
| `Domain`, `Domain.id`, `Domain.comp` @ [IndexedComponentTransport.lean](../../leanncd/experiments/indexed_execution/IndexedComponentTransport.lean) | Certified wire geometry; audit missing inverse/coherence helpers before adding them |
| `MatchedComponent`, `Boundary` @ [IndexedComponentCompositionScope.lean](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionScope.lean); `compose` @ [IndexedComponentComposition.lean](../../leanncd/experiments/indexed_execution/IndexedComponentComposition.lean) | Actual leaves and assembly constructor |
| `WitnessHom`, `homComp`, `componentSpan` @ [IndexedWitnessSpan.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessSpan.lean) | Existing target arrows and leaf interpretation |
| `graphHom`, `graphHom_identity`, `graphHom_comp`, `boundaryEnvEquiv`, `compositeInputEquiv`, `compositeOutputEquiv`, `composition_hom` @ [IndexedWitnessComposition.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessComposition.lean) | Administrative interpretation and assembly soundness |
| `leftNestedBoundary`, `rightNestedBoundary`, `left_boundary_square`, `right_boundary_square`, `bracket_hom` @ [IndexedWitnessCoherence.lean](../../leanncd/experiments/indexed_execution/IndexedWitnessCoherence.lean) | Actual nested constructor comparison |

## 7. New-session execution discipline and exclusions

Use `slice-plan` and `new-slice`. Work in an isolated latest-local-main
worktree with verified warm Mathlib; refresh project-owned oleans through
`lake-build.sh` before single-file checks. Never run Lake from the repo root.
Keep one source-category/functor plan, with records separate from its live
execution instructions. Use a proposed `categorical_source_functor` artifact
prefix; new Lean names and module splits must be verified during authoring.

Prototype on the real module split, then author the plan from verified
artifacts in a fresh bounded context. Ship mechanically generated per-task
patches and observed mutation manifests. Compile every new Lean block with
`check-snippet.sh`. Size tasks by fixtures/cycles, at most roughly three work
items per dispatch; split before approximately 60 turns or 250k context.
Authoring targets roughly 50M cumulative input tokens; execution caps at
175M. Measure with `token-report.py` and disclose overruns or unavailable data.

The controller runs the actual unfiltered mutation manifests, source/probe
checks and namespace audits, plus the full
`LeanNCD Tests IndexedExecutionExperiment` build through the wrapper.
Use two final whole-branch review lenses: source-presentation/functor
soundness, and integration/observation boundaries. Update the synthesis and
Lean entry-point documentation only for proved results. After green gates
and adjudicated findings, integrate locally and clean up only this slice's
branch/worktree. Preserve the primary checkout's existing edits; do not push.

**Excluded:** rank stitching, phase/state/trace projection, event-sensitive
process identities, backend/numerical refinement, broader interfaces,
automatic leaf matching, St/Br/PROP/monoidal extensions, and unrelated
coverage/accounting repairs. Do not change the core language, runners,
registry or production imports.

Close-out must identify the source objects, generators, congruence and laws;
the actual functor and its maps; the constructor comparison and nested
transports; assumptions, evidence and remaining process/backend gaps.

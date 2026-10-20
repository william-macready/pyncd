# Lean executable reference - 1. Purpose, authority, and current position

[Previous: Introduction](lean_executable_semantics_path.md) | [Contents](README.md) | [Next: 2. One notation, two presentations](lean_executable_semantics_path_part_2.md)

## In this part

- [1. Purpose, authority, and current position](#1-purpose-authority-and-current-position)

## 1. Purpose, authority, and current position

This document connects the mathematics of
[Tensor Logic: Operational and Denotational Semantics](tensor_logic_semantics.md)
to the landed Lean definitions and proofs, and describes the remaining path to
an executable reference that we can debug and validate. It is a roadmap and
code correspondence guide, not an implementation plan or a new semantic contract.
The specification remains authoritative.

**Snapshot: 2026-10-12, merged and pushed through `e9ae73f1`, including buffer review fixes and fixture-probe closure: the Part V slice-1 to slice-4 plan layer
(`Semantics/Plan/`), on top of bounded source correspondence
(`6a90baff`), nested-reduction reindexing (`705280cd`), successful-permutation
agreement (`ca642b3d`), and raw-source admission, on top of the verified
executor (`6026f0b`).** The expression/readiness,
collection/model, reference-machine soundness, and coordinate-ranks/finite-measure
developments have landed, including maximal-run correspondence. The computable
validated reference executor and its exact-rational fixtures are now verified;
both final whole-branch code-review lenses are clean.
The Part V slice-1 plan layer ([Section 4.9](lean_executable_semantics_path_part_4.md#49-part-v-slice-1-the-singleton-command-plan-layer))
is in the snapshot above, extended by slice 2 to fused commands, slice 3 to retirement
and slice 4 to typed static same-sort physical reuse with boundary-local layout
injectivity: eleven modules under `Semantics/Plan/`, proving Lemma 31.2,
Theorem 31.3 and Lemma 32.1 for that profile, with 367 inherited fixtures.
Slice 5 adds certified bounded full-history scans: generic schedule validity,
all-command physical value retention, unconditional completion and full typed
Decode. The current Plan inventory is 516 fixtures (239 evaluated, 277 proof).
The four inherited manifests contain 54 cycles (20 + 15 + 9 + 10);
slice 4 adds 10 controls. Exact ordered patch replay from `4ffdc342` to `deb4fecd`
is controller-verified (isolated-index final git diff exit 0). All 64 production
controls pass with exact failure-site expectations. The supplemental source-copy
probes pass 17/17 (16 computed components and one independent unused-slot
consumer); they neither admit proofs nor claim complete mutated executor runs.
The latest controller full build passed 8796 jobs, and the actual axiom audit
checked 5994 constants with standard axioms. Four pre-existing `sorry` warnings
outside Plan remain unchanged. Slice 4 landed via `c44f8a21`, review fixes via
`b9b25055`, and probe closure via `e9ae73f1`; all are on `origin/main`.
Review findings are closed. See the [slice-4 record](plan_layer_slice4_record.md)
and [retirement probe close-out](plan_layer_slice3_record.md#o3-reconciled-and-closed-independent-component-mutation-probes).
Earlier clean review statements above refer to the landed reference executor.
The public entry is
[`LeanNCD.Semantics`](../../leanncd/LeanNCD/Semantics.lean), imported by
[`LeanNCD`](../../leanncd/LeanNCD.lean). They are a semantic validation layer,
separate from the production DSL evaluator and execution backends.

The central distinction is:

- **Expressions already have computational interpretation.** For concrete
  computable carriers, operations, and registries, Lean can evaluate
  `interpret`, `footprint`, and `evalReady`. Concrete finite collections also
  compute, as the existing guards demonstrate.
- **Models are a mathematical relation.** `Models` and `AdmInput` are
  propositions; `denotation` selects a unique model nonconstructively. It is
  not an executable equation solver.
- **The reference relation now has a computable refinement.** `Step` still
  specifies legal transitions and `Reaches` finite reachability. The executor
  refines its noncomputable updates, selects exactly its eligible edges, and
  retains typed selected-event paths and exact endpoints. It uses function-valued
  stores and supplied complete ordered schedules, not synthesized schedules.
- **Reached-run soundness is proved.** Any reached success yields the unique
  complete model; any reached ready-undefined failure excludes every model.
- **Termination and ranked correspondence are proved.** Every reached prefix
  has a terminal extension; finite bounds hold without ranks. A coordinate-rank
  certificate excludes reachable blocking, and every maximal ranked run succeeds
  or explicitly fails according to model existence. These are relational
  proofs. The default executor has a proved sufficient finite budget; a supplied
  address-rank certificate excludes reachable blocking in that actual run.
  Exact-rational runtime fixtures distinguish success, ready failure, blocking,
  invalid input, and debug exhaustion without supplying a model witness.

The intended path is therefore:

```text
typed expressions + strict interpretation + read stability       LANDED
                         |
tagged additive collection + complete model relation              LANDED
                         |
reference transitions + conservation + reached-run soundness      LANDED
                         |
coordinate ranks + finite measure + maximal-run correspondence    LANDED
                         |
computable state/step selection + validated reference executor    LANDED
                         |
bounded source correspondence + differential debugging             LANDED
                         |
Part V slices 1-3 (singleton + fused + retirement)                 LANDED
                         |
Part V slice 4 (typed static buffer reuse + layout safety)         LANDED / PUSHED
                         |
buffer review fixes + fixture-level probe reconciliation         CLOSED / PUSHED
                         |
general compiled storage/backend refinement                      LATER
```

The generic executor still accepts directly constructed admitted core programs.
The `LeanNCD.Semantics.Source` layer additionally admits resolved finite read-only
sum-products and constructs complete multi-target schedules automatically.

The [source correspondence + differential debugging plan](source_correspondence_plan.md)
now has implemented and tested source binding, admission, normalized-body/fiber
proofs, execution-backed whole-store equations, typed diagnostics, and four-leg
comparison. All 79 named fixtures, exactly 18 generated programs, 39/39
implementation mutations, the controller full build (8,763 jobs), ordered
six-patch replay and both final whole-branch review lenses pass. This lands only
the bounded read-only sum-product fragment, not general backend refinement.
Exact scope, observed fixtures, mutation classifications and
historical authoring receipts are in the separate
[source correspondence record](source_correspondence_record.md).

The bounded raw-source/admission follow-up now proves actual resolver name coverage,
original declaration and indexed occurrence correspondence, and applicability of the
existing semantic results. Its conditional endpoints and separate validation receipts
are in the [raw-source/admission record](raw_source_admission_record.md).
Two smaller follow-ups have also landed: `interpret_contract_reindex` (a contraction
is independent of the enumeration of its bound coordinates) and
`StatementPermutation.successful_results` (two complete rational runs of a
permuted source reach the same final store).

---

[Previous: Introduction](lean_executable_semantics_path.md) | [Contents](README.md) | [Next: 2. One notation, two presentations](lean_executable_semantics_path_part_2.md)

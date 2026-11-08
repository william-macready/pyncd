# Next-session briefing: witness-preserving categorical semantics

## Launch instruction

Prepare and verify one implementation plan for the denotational
witness-span interpretation of the existing component semantics, then
execute it through the repository's release gates. Preserve existing edits.
Do not rerun the completed transport, static-composition or model-gluing plans.

**Process weight: Full.** This adds a categorical interpretation and laws.
This briefing is not a verified execution plan: it supplies no new Lean
implementation, compiled task patches or mutation manifests.

This is the next **denotational** categorification slice, not the independent
ranked operational phase/projection slice. Do not imply that witness-span
isomorphism preserves execution events or individual internal representations.

## 1. Starting state and reading order

The following prerequisites have landed on local main:

- Typed declaration/context transport.
- Conditional graph/reference execution correspondence.
- Static scoped composition and composite-match construction.
- Rank-independent whole-model restriction/gluing.
- Restricted domain and successive-denotation laws under both components'
  explicit at-most-one-model hypotheses.

The categorization roadmap and progress ledger landed in `39a6b26e`.
The model-gluing integration record is `bda29954`.
These are provenance, not required future implementation HEADs.
Start from latest local main and verify the actual APIs.

Read:

1. [Synthesis](categorical_tensor_logic_semantics.md), Sections 9.2-9.3 and
   10, especially the distinction between denotational and process laws.
2. [Interface design](categorical_tensor_logic_component_interfaces.md),
   Sections 6-7, including the core identity obstruction.
3. [Model-gluing record](component_model_gluing_record.md) and
   [static-composition record](component_composition_record.md).
4. The targeted source map in Section 6 below.

The main checkout is `/Users/williammacready/code/python/pyncd`.
Its existing semantics-contents edits and all other worktrees are protected.
Use an isolated latest-local-main worktree.
Use GPT Sol with high reasoning effort for difficult design decisions,
with bounded objectives and targeted source windows.

## 2. Semantic objects, witnesses and observations

A **whole-tensor interface** records tensor identities, value sorts and full
coordinate domains, including empty tensors. For an interface $X$,
$\mathsf{Env}(X)$ denotes its valid environment space. Do not identify
interfaces merely because their environment carriers are isomorphic or their
extents/cardinalities happen to coincide.

Work within the existing finite decidable `Declarations Unit`,
`RationalReference.Carrier`, registry and operations.
Finiteness of tensor identities and coordinate domains does **not** make
the set of rational environments or complete models finite.

For a component $P$ with input interface $X$ and output interface $Y$,
define $W_P$ to contain every pair $(\eta,\rho)$ of validated input $\eta$
and complete model store $\rho$ satisfying `P.Models` on that input.
The model store retains all private values and actual body-definedness
obligations. Different proofs of the same store are not different witnesses.

The proposed interpretation is the **witness span**

$$
\mathsf{Env}(X)
\leftarrow
W_P
\rightarrow
\mathsf{Env}(Y).
$$

The left leg returns the input; the right leg projects the complete model
to its outputs. Build this across **all** validated inputs: the existing
`witnessesEquiv` is indexed by an upstream input and is an ingredient,
not already this categorical interpretation.

Use **span isomorphism** as the preferred denotational equivalence:
a bijection of witness sets commuting with both boundary legs.
It cannot collapse distinct witnesses in a fiber to one, but it does not
certify equal event traces or coordinate-by-coordinate equality of different
private representations. A stronger provenance/process equivalence is a
different proposal and must not be silently substituted.

## 3. Representation decision and category laws

Prefer a small concrete semantic category whose arrows are witness spans
up to span isomorphism. Composition is a **pullback**: compatible witness
pairs whose boundary values agree after the specified interface transport.

Before freezing the plan, audit the representation:

- Typed interfaces must retain identity/domain/empty-tensor metadata.
- An explicit boundary supplies an environment isomorphism; neither names
  nor equal extents supply it. Preserve its direction and inverse.
- Raw span/pullback data are associative only up to isomorphism, not literal
  equality of nested dependent pairs.
- For an ordinary category, prove the span-isomorphism relation and that
  composition/identities descend to its quotient.
- If a weak/bicategorical representation is genuinely preferable, justify
  the changed deliverable before execution and provide associator/unit
  coherence, not merely isolated bijections.
- Audit Lean universe/size levels. Do not assert same-universe local
  smallness or enumerate all models. Reuse suitable existing infrastructure,
  but do not build an unrelated general span/category library.

The target identity is the **identity span** on $\mathsf{Env}(X)$,
with both legs identity maps.
Prove both unit laws and associativity at the chosen equivalence.
For associativity, both bracketings must correspond to the same compatible
triple of complete witnesses, with coherent interface transports.

Checked even/odd UID allocation makes bracketings' raw tensor/tag IDs differ.
Do not prove coherence by numerical coincidence or claim raw source-program
equality. Account for the interface and witness reindexings explicitly.

## 4. Connect the category to actual component meaning

Define a component's witness-span interpretation from its authoritative
`Program.Input`, complete model predicate and whole output projection.
If interface environment spaces use a new representation, prove their
equivalence to those existing input/output types, including empty values.

Lift the existing model-gluing equivalence across validated inputs.
Show that the denotation of `compose A B wire` is isomorphic to the
pullback composite of the component spans over the explicit boundary.
The comparison must commute with **both** input and output legs:

- Input lifting/restriction identifies the constructed composite's input
  with the upstream input.
- `boundaryInput`/`boundaryFromOutput` identify the consumer's input with
  the explicitly transported upstream output.
- Output-index/projection transport identifies composite outputs with
  downstream outputs.
- `witnessesEquiv` supplies the full compatible-witness bijection.

Do not replace those leg-commutation proofs by an unstructured equivalence
of witness sets or by agreement at one successful input.

The semantic category and the source presentation are different:
core `Program` components do not automatically contain identity morphisms.
`output_defined` forbids input aliases as core outputs.
If the source syntax itself needs units, use administrative interface wires
outside core computations and prove their transport laws.
Do not insert a copy and call it an event-free identity.

A source **functor** may be claimed only after its source category and laws
are actually supplied. Otherwise state the more limited, but useful, result:
a composition-preserving interpretation of the existing core constructor
into the semantic target category. Do not silently claim a source category
because the target category has identities.

### Restricted partial-map view

Under `AtMostOneModels`, the witness span's input leg is injective and
describes a partial input-output map. Prove the correspondence for this
restricted interpretation and connect it to the already proved admissibility
domain and successive-denotation laws.

At most one model does not imply model existence. Do not define a purported
functor on arbitrary witness spans by selecting uniquely populated fibers:
downstream constraints can select one of several upstream witnesses, so
unique-model extraction is not compositional without the restriction.

## 5. Discriminating examples and boundaries

These are proposed acceptance goals, not newly compiled fixtures.
The verified plan must name exact donors/deltas and observed controls.

1. **Strict versus total private work:** reuse the existing `Audit` cases.
   The strict visible output equation cannot create a witness when internal
   work is undefined; the total complete witness survives interpretation.
2. **Hidden multiplicity:** reuse the cyclic hidden-model case. Two private
   complete stores with equal boundary/final outputs must remain distinct
   compatible witnesses; an output-only relation is not the intended span.
3. **Downstream selection:** reuse the upstream $t=t^2$ / reciprocal case.
   The general span composition remains correct, while unrestricted
   unique-model extraction must not satisfy the partial-map law.
4. **Empty interfaces:** retain required empty-input presence and
   empty-output identity. A singleton environment carrier alone must not
   cause automatic identification of unrelated interface metadata.
5. **Nonconstant boundary transport:** reuse unequal-axis model donors;
   wrong flattening or a reversed adapter must differ from the intended
   environment map and fail a leg-commutation check.
6. **Associativity:** use three compatible components with nontrivial
   coordinate maps and distinguishable private identities/values. Avoid a
   fixture where every map is identity or every value constant, masking
   incorrect reindexing.
7. **Identity versus computation:** administrative wires and identity spans
   satisfy the declared denotational unit law. A pure copy can have identity
   denotation after explicit interface transport while still adding events.
   Do not conflate that semantic isomorphism with process equivalence.

No zero/default witness may be fabricated for undefined or missing data.
Do not hide internal models before testing uniqueness, or count proof terms
as model multiplicity. Preserve strict complete-array interpretation.

## 6. Targeted source map

Locate symbols with `rg -n` and read roughly 40-60-line windows.
Do not survey unrelated backends or whole large files.

| Identifiers | File |
| --- | --- |
| `Port`, `MatchedComponent`, `Boundary`, `declarations`, `upstream`, `downstream` | [IndexedComponentCompositionScope.lean](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionScope.lean) |
| `program`, input/output port constructors and their exact-role laws | [IndexedComponentCompositionProgram.lean](../../leanncd/experiments/indexed_execution/IndexedComponentCompositionProgram.lean) |
| `compose_match`, `compose` | [IndexedComponentComposition.lean](../../leanncd/experiments/indexed_execution/IndexedComponentComposition.lean) |
| `Input`, `ValidInput`, `Models`, `AdmInput`, `Output`, `outputProjection`, `denotation` | [Models.lean](../../leanncd/LeanNCD/Semantics/Models.lean) |
| `liftInput`, `restrictInput`, their inverse laws, `boundaryInput`, `boundaryFromOutput`, `boundaryInput_outputProjection` | [IndexedComponentModelInputs.lean](../../leanncd/experiments/indexed_execution/IndexedComponentModelInputs.lean) |
| `CompositeWitness`, `CompatibleWitnesses`, `witnessesEquiv`, `outputIndexEquiv`, `liftOutput`, `outputProjection_transport` | [IndexedComponentModelWitnesses.lean](../../leanncd/experiments/indexed_execution/IndexedComponentModelWitnesses.lean) |
| `AtMostOneModels`, `admInput_restrictions_iff`, `denotation_successive` | [IndexedComponentModelDenotation.lean](../../leanncd/experiments/indexed_execution/IndexedComponentModelDenotation.lean) |
| Strict/total/zero-writer complete-model cases | [IndexedComponentModelLocalTest.lean](../../leanncd/experiments/indexed_execution/IndexedComponentModelLocalTest.lean) |
| Empty and unequal-axis model/input/store cases | [IndexedComponentModelGeometryTest.lean](../../leanncd/experiments/indexed_execution/IndexedComponentModelGeometryTest.lean) |
| Downstream-selection and hidden-model multiplicity cases | [IndexedComponentModelCycleTest.lean](../../leanncd/experiments/indexed_execution/IndexedComponentModelCycleTest.lean) |

No witness-span category, interpretation or functor declaration is already
provided by these files. Names and module splits for new work must be chosen
and verified during plan authoring.

## 7. Next-session discipline and exclusions

Use `slice-plan` and `new-slice`. Prepare an isolated latest-local-main
worktree with a verified warm Mathlib cache, then refresh project-owned oleans.
Use `lake-build.sh` and `lean-file.sh`; never invoke Lake from the repository
root. Preparation discovers caller cwd; do not pass `--plan` until its
primary-checkout copy source actually exists.

Audit the category/equivalence and size decisions before prototype dispatch.
Use bounded real-split prototypes, then a fresh artifact-only plan author.
Ship mechanically generated compiled patches, exact source locators,
fixture/cycle counts, donors plus deltas, and meaningful observed controls.
Every Lean block must pass `check-snippet.sh`. Do not invent values,
diagnostics, categorical instances or proof-status receipts.

Use a proposed `categorical_witness_semantics` prefix under
`papers/semantics/` for the plan and separate records/artifacts.
Keep the experiment nondefault and discoverable; update the synthesis's
progress ledger only for results actually proved. A target-category law
does not close an unproved source/process-category law.

Execute every verified task with task reviews and checkpoints. The controller
runs actual unfiltered manifests, exact patch/probe checks, namespace audits
and `lake-build.sh <checkout>/leanncd LeanNCD Tests IndexedExecutionExperiment`.
Complete two final whole-branch lenses, categorical/model soundness and
integration/observations. After green gates and fixed/adjudicated findings,
merge locally and remove only the task's branch/worktree. Do not push.

Use the `new-slice` shell-harness preamble for every dispatch.
Target roughly 40 turns and at most three work items; split before
approximately 60 turns/250k retained context. Authoring targets approximately
50M cumulative input tokens; execution caps at 175M. Report overruns or
unsupported transcript accounting without claiming unmeasured compliance.

**Excluded:** rank stitching, runtime phase/trace-projection, event-exact
process category laws, numerical/backend refinement, general St/Br/PROP
interpretations, wider interfaces, automatic leaf matching and old coverage/
accounting repairs. Do not change the core language, runners or registry.

Close-out must state the category's objects, arrows, equivalence, composition,
units and laws; the component interpretation's exact scope and commuting
boundary maps; and the restriction to partial maps. Explicitly record any
source-category or process claims still open.

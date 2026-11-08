# Witness-span semantics: historical design audit and current status

**Current status:** all seven verified tasks have actually executed and
committed in the controller checkout, with builds, post-edit snippets,
exact source checks and direct task reviews. Final whole-branch reviews,
release reruns and local integration are still pending. This is not
a completed release or a source/process-category claim.

The verified prototype proves the metadata-bearing whole-interface span
category, its quotient/unit/associativity laws, all-input complete-model
interpretation and composition comparison with both legs, actual nested
source-bracket coherence through one compatible triple, and the injective-left
restricted partial-map connection. See
`categorical_witness_semantics_plan.md` for execution and
`categorical_witness_semantics_plan_record.md` for exact package identities,
verification receipts, repaired failures, limitations and accounting.
Final unfiltered populated `_post` mutations passed 10/10, separately from
the earlier invalid proposal attempts; the final table is
`categorical_witness_semantics_artifacts/authoring_verified_mutations.md`.

Everything below is the **historical, design-only audit**, preserved as the
reasoning that preceded implementation. Its future tense and then-open gates
do not describe remaining denotational prototype work. The worktree was clean
at the start of that audit; no Lean source, existing documentation, or build
configuration was changed during the audit itself.

## Historical representation decisions

1. Use a port-only `WholeInterface` object: a declaration of its *port*
   tensor type, injective UID, complete signature (sort and axes), and an
   exhaustive, duplicate-free port roster. Construct an input/output object
   from the corresponding role subtype of a `MatchedComponent` and its
   existing port list. Do not retain the component's unrelated private
   declarations in the interface object. Do not quotient interfaces by
   carrier equivalence, matching extents, or matching names. `Env X` is a
   dependent function assigning a value at every coordinate of every port.
   The port remains in the index type when its coordinate type is empty.
   Prove `Env (inputInterface A) ≃ A.program.Input` using `inputs_exact`,
   `ValidInput`, and tensor-level `some`/`none`; prove
   `Env (outputInterface A) ≃ A.program.Output` using `outputs_exact`.
   Check these equivalences for empty tensors, not just inhabited coordinates.
2. Use concrete spans `X.Env ← W → Y.Env` with **arbitrary** apex `W : Type`
   and quotient each hom by a span isomorphism: an `Equiv W W'` commuting
   with both legs. Define the setoid (reflexivity, inverse, composition of
   equivs), its identity span, and pullback composition with apex
   `{(w, v) : W × V // right w = left v}` (or an equivalent dependent
   sigma). The compatibility equality is proof-irrelevant; distinct stores,
   even with identical boundary values, are not. Show that apex isomorphisms
   induce a pullback-apex isomorphism commuting with *both* outer legs;
   this is the congruence needed to descend composition to quotient homs.
   Prove the two unit isomorphisms by forgetting the identity witness and
   reconstructing it from the boundary leg. Prove associativity by taking
   `((wA,wB),wC)` and `(wA,(wB,wC))` to the same compatible triple, transporting
   the two equality proofs and checking the first and last legs. Only then
   install Mathlib's ordinary `Category` instance; raw nested pairs are not
   judgmentally associative.
3. **Size is a design constraint, not a finiteness argument.**
   `Declarations Unit` and an interface containing a `Tensor : Type` live
   in `Type 1`; the fixed rational environment, complete store, and
   all-input witness apex live in `Type 0`. Quantifying over *all* `Type 0`
   apexes makes the span and its quotient hom live in `Type 1`, not `Type 0`.
   Target `Category.{1}` on the `Type 1` interface objects; do **not** claim
   `SmallCategory` or same-universe local smallness, enumerate rational
   stores, or shrink arbitrary apexes without a separate justification.
   The focused infrastructure check found Mathlib's `CategoryStruct` /
   `   Category` in `Mathlib/CategoryTheory/Category/Basic.lean`,
   and no ready generic span category in the checked `CategoryTheory`
   files. Reuse those classes, `Equiv` and `Quotient`, and the concrete
   dependent-pair pullback; an unrelated general span/bicategory library
   is unnecessary. Verify the proposed universe annotation in a prototype.

## Explicit interfaces and the component comparison

4. An existing `Boundary A B` is **not** an equality of objects: its
   `matched` goes from *B input tensors* to *A output tensors*, and
   `domain i` maps *B input coordinates* to *A output coordinates*.
   Construct the forward environment equivalence
   `eAB : Env (outputInterface A) ≃ Env (inputInterface B)`
   by `out (matched i) ((domain i).coord p)`; construct the inverse with
   `matched.symm` and `coord.symm`, proving both function equalities,
   including the empty-port case. Represent the explicit boundary as its
   **graph span** `outputInterface A ⟶ inputInterface B`, with legs
   `id` and `eAB`. Never use an implicit coercion or identify these
   distinct interface objects. `Domain.comp` already supplies composable
   certified axis/coordinate adapters where required.
5. For every validated input, form the witness apex
   `Σ η : A.program.Input, {ρ : Store K σ //
     A.program.Models RationalReference.ops η ρ}`. Its left leg is the
   validated input via the inverse input-interface equivalence; its right
   leg is `A.program.outputProjection ρ` via the output-interface
   equivalence. `Models` requires admissibility, input agreement and all
   defined-tensor equations; no output-only existential image or
   successful-run filter is allowed. Subtype/Sigma equality makes proof
   terms irrelevant while keeping all distinct private complete stores.
6. Lift `witnessesEquiv A B wire η` **over all** `η` using
   `restrictInput`/`liftInput` inverse laws. Compare
   `⟦A⟧ ≫ graph(eAB) ≫ ⟦B⟧` with `⟦compose A B wire⟧` after inserting
   the necessary explicit graph spans at its *exterior*:
   `inputInterface (compose A B wire)` is a tagged copy of A's input
   interface; `outputInterface (compose A B wire)` is a tagged copy of B's
   output interface, not literally the same objects. State the theorem at
   the same endpoints using these port/environment equivalences. The
   composite-input leg must commute by `restrictInput_liftInput` and
   `liftInput_restrictInput`; the middle compatibility must commute by
   `boundaryInput_outputProjection` and `boundaryFromOutput`; the
   composite-output leg must commute by `outputIndexEquiv`,
   `liftOutput`, and `outputProjection_transport`. Check both outer legs
   of the *all-input* witness equivalence, not merely its apex bijection
   or the equality of outputs on one admissible input.

## Coherence and restricted view

7. Prove target-span associativity **before** claiming anything about
   source bracketings. For A, B, C with explicit AB and BC boundaries,
   derive the two boundaries needed by the two nested `compose` calls from
   `inputPort`/`outputPort`, role exactness, and the original certified
   adapters; compare each nested model-gluing equivalence with the same
   triple `(ρA, ρB, ρC)` and both boundary compatibility equations.
   Prove the resulting input/output adapter squares and associativity of
   environment reindexing (using equivalence composition and `Domain.comp`),
   then the composite witness comparison to the target associator. The
   nested `Sum`/`Defined` tensor tags and even/odd UIDs are different;
   index by original component provenance and explicit transport, **not**
   equality of raw IDs or nested programs. If the nested source
   boundaries cannot be constructed with the public port API, report that
   load-bearing obstruction before claiming source associativity.
8. For the restricted partial-map view, prove `AtMostOneModels A` iff
   the witness span's left leg is injective (using input-interface
   equivalence and subtype/Sigma extensionality). Identity and graph
   spans have injective left legs, and pullback composition preserves this
   property. Associate an injective-left span with the partial function
   whose domain is `∃ w, left w = x`, and whose value is `right w` for
   its unique witness. This is a restricted construction, with quotient
   invariance and domain/value composition proved, not a functor from
   arbitrary spans. Connect the component domain and value statements to
   `admInput_restrictions_iff` and `denotation_successive`; absence of a
   model remains undefined, never a default/zero witness. Hidden
   multiplicity and downstream selection must prevent an unrestricted
   unique-model law.
9. Target identity spans are semantic units; the core `Program` has no
   event-free identity (`output_defined` disallows an input/output alias).
   No source category or functor has been supplied by this audit. The
   deliverable can honestly be a composition-preserving interpretation
   of the existing constructor with explicit boundary and exterior
   adapters. A source functor would additionally require administrative
   wire syntax and proved source identity/associativity laws. Span
   isomorphism says nothing about event traces, execution schedules, or
   individual intermediate representations.

## Historical verified inputs and subsequent proof gates

Stable identifiers replace the audit's now-invalid line-number locators:

- `Port`, `MatchedComponent`, `Boundary`, `declarations`, `upstream`,
  `downstream` @ `IndexedComponentCompositionScope.lean`: directional
  boundaries, tagged declarations, UID allocation and embeddings.
- `inputPort`, `outputPort` and exact-role laws @
  `IndexedComponentCompositionProgram.lean`; `compose_match`, `compose` @
  `IndexedComponentComposition.lean`: constructed matched component.
- `Declarations`, `Store` @ `LeanNCD/Semantics/Types.lean`;
  `Input`, `ValidInput`, `Models`, `Output`, `outputProjection` @
  `LeanNCD/Semantics/Models.lean`: authoritative complete semantics.
- `Domain.coord`, `Domain.id`, `Domain.comp` @
  `IndexedComponentTransport.lean`: certified coordinate equivalences.
- `liftInput`, `restrictInput`, `restrictInput_liftInput`,
  `liftInput_restrictInput`, `boundaryInput`, `boundaryFromOutput`,
  `boundaryInput_outputProjection` @ `IndexedComponentModelInputs.lean`.
- `witnessesEquiv`, `outputIndexEquiv`, `liftOutput`,
  `outputProjection_transport` @ `IndexedComponentModelWitnesses.lean`.
- `AtMostOneModels`, `admInput_restrictions_iff`, `denotation_successive` @
  `IndexedComponentModelDenotation.lean`.

Prototype gates, in order: metadata/exterior equivalences (especially
empty input presence); universe check plus setoid/quotient and target
category laws; boundary graph equivalence; all-input component comparison
with **both** legs; provenance-indexed triple coherence; injective-left
partial-map restriction and the existing strict/total, hidden-multiplicity,
downstream-selection, unequal-axis and empty-port controls. No prototype,
new fixture, theorem check, or build was run during this design audit.
These gates were subsequently discharged in the verified final prototype;
its current evidence and still-pending release gates are separated above.

Historical design-audit accounting: 44 tool calls exceeded the 20-call aim.
The prescribed Copilot token reporter has no transcript for this session;
measured cumulative/peak budget compliance is unavailable, not asserted.

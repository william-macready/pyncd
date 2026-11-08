# Bounded prototype: whole interfaces and witness-span category

Status: **compiled and committed**, first prototype group only. Detached base
`a9c9a647a04e260e21c8e5c624a0bac3fa13ef20`; prototype commit
`3fc437a28834d614ca730caaa78c1026c658efd0` in
`categorical-witness-semantics-prototype` (detached HEAD, clean). This commit
is a task patch, not a finished categorical interpretation slice.

## Patch contents

- `leanncd/experiments/indexed_execution/IndexedWitnessInterface.lean`:
  `WholeInterface` retains a port-only tensor type, injective UID, complete
  signature (sort and full shape), and an exhaustive duplicate-free roster.
  `roleInterface` makes the role subtype of the matched component's tensor
  declaration the port type; its finite roster enumerates **whole ports**,
  including ports with no coordinates. `inputInterface`, `outputInterface`,
  `inputEnv`, `envInput`, `inputEquiv`, and `outputEquiv` relate these objects'
  environments to the authoritative `Program.Input` and `Program.Output`.
  The output equivalence is definitional because both types are the same
  dependent function. The input inverse checks tensor-level `Option`
  presence independently of coordinate inhabitedness. Environment
  equivalence is not used as equality of interface objects.
- `leanncd/experiments/indexed_execution/IndexedWitnessSpan.lean`:
  `Span`, `SpanIso`, `spanSetoid`, `WitnessHom`, `Span.identity`,
  `Span.pullback`, the raw `SpanIso.refl/symm/trans/pullback/leftUnit/rightUnit/
  assoc` constructors, `homId`, `homComp`, an ordinary Mathlib `Category.{1}`
  instance, and `componentSpan`. A witness is a dependent pair of a
  validated input and a subtype of a **complete** model store satisfying
  `Models`; proofs are irrelevant, private stores are not erased. The left
  and right legs use the interface input equivalence and whole output
  projection. Pullback compatibility is equality of middle environments;
  both legs commute under raw isomorphism. The quotient composition is
  well-defined, and identity/associativity hold in the quotient, never as
  equality of differently nested raw witness pairs.
- `leanncd/experiments/indexed_execution/IndexedWitnessTest.lean`:
  focused category law/type checks, empty-tensor presence, hidden-witness
  multiplicity with equal outputs, and public namespace axiom audits.
- `leanncd/lakefile.toml`: only the nondefault
  `IndexedExecutionExperiment` globs gained the three modules. The default
  production `LeanNCD` import was not changed.

**Universe decision:** `WholeInterface : Type 1` because its port type is a
`Type`; each concrete environment and witness apex is `Type 0`, but `Span`
quantifies over arbitrary `W : Type` and therefore quotient homs live in
`Type 1`. An explicit Lean example checks `Category.{1} WholeInterface`.
No locally-small/same-universe claim or enumeration of rational models.

## Verified controls and limits

All commands used the target worktree's wrappers. The initial targeted
`LeanNCD IndexedComponentComposition IndexedComponentModelTest` build
refreshed project/import oleans after the verified warm Mathlib cache and
passed. `lean-file.sh` checked each new module (including the test fixture)
after imports were built. Targeted `IndexedWitnessInterface`,
`IndexedWitnessSpan`, `IndexedWitnessTest`, and the entire nondefault
`IndexedExecutionExperiment` all passed through `lake-build.sh`.
`git diff --cached --check` passed; all four changed paths were staged
explicitly. No new source has `sorry`, `admit`, `axiom`, or `native_decide`.

The test donor `IndexedComponentCompositionPortFixtures.emptyProducerComponent`
has the `emptyExternalInput` port with a zero-extent axis: its environment's
coordinate function is empty, but `inputEquiv` still produces `some` for the
tensor. The donor
`IndexedComponentModelCycleFixtures.hiddenUpstream` supplies two different
complete `scalarStore` witnesses on the same validated input; the focused
test proves they are unequal although their projected outputs agree. These
are added *controls over existing donors*, not expanded source fixtures.
Category left/right unit and associativity examples elaborate against the
ordinary Mathlib instance. `#audit_axioms IndexedWitness` checked 126
definitions/theorems and `#audit_axioms IndexedWitnessTest` checked 7:
only `propext`, `Classical.choice`, and `Quot.sound` occur. Public
`#print axioms` controls cover `inputEquiv`, pullback/associator/unit
isomorphisms, quotient composition, and `componentSpan`.

No mutation cycle was run. Intended future mutation targets, **not observed
diagnostics**, are `roleInterface` UID/signature or roster completeness,
`envInput`'s empty-tensor `some`, `componentSpan`'s `Models` subtype or
output projection, `Span.pullback`'s middle-leg equality,
`SpanIso.pullback`'s right-leg proof, and `SpanIso.assoc`'s rebracketing.
Existing `Semantics.AxiomAudit` is reused instead of introducing a new
audit mechanism.

**Not in this prototype:** boundary graph spans and explicit environment
transport, all-input component model-gluing comparison, nested source
coherence, the injective-left partial-map restriction, and any fixture
expansion. In particular, this commit proves a target category and defines
component denotations, but **does not claim** the denotation preserves
component composition, source functoriality, or trace equivalence. The
`indexed_execution` directory has no existing README to update.
The `leanncd/AGENTS.md` build/mutation hook spans substantially more than
the requested small reading window (over ~3k of text); the controller may
want a separately scoped trim, but this patch does not rewrite it.

Budget: bounded prototype finished without the stated ~60-turn/250k-context
hard-checkpoint breach.

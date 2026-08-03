# LeanNCD code analysis

## Table of contents

- [Executive assessment](#executive-assessment)
- [Evidence and validation](#evidence-and-validation)
- [Validated findings](#validated-findings)
  - [Immediate correctness failures](#immediate-correctness-failures)
  - [Categorical interfaces and proof surface](#categorical-interfaces-and-proof-surface)
  - [Executable and compiler design](#executable-and-compiler-design)
  - [Cross-layer semantics](#cross-layer-semantics)
  - [Testing and trust automation](#testing-and-trust-automation)
  - [Regression specifications](#regression-specifications)
- [Assessment and revised restructuring plan](#assessment-and-revised-restructuring-plan)
  - [Spike 3 assessment](#spike-3-assessment)
  - [Missing work beyond Spike 3](#missing-work-beyond-spike-3)
  - [Spike 4 assessment](#spike-4-assessment)
  - [Operational guarantees](#operational-guarantees)
  - [Staged implementation roadmap](#staged-implementation-roadmap)
- [Conclusion](#conclusion)
  - [Architectural constraints to preserve](#architectural-constraints-to-preserve)
  - [Immediate decisions](#immediate-decisions)
- [Appendix A: JAX as an evaluation backend](#appendix-a-jax-as-an-evaluation-backend)

## Executive assessment

This review covers the two layers described by `LeanNCD/LeanNCD.lean`:

1. the noncomputable categorical tower for colored PROPs, \(D\)-graded structure, weaves,
   temporal structure, algebras, and the \(D=\mathrm{St}, C=\mathrm{Br}\) instance; and
2. the computable tensor-logic frontend, compiler pipeline, evaluator, ACSet codec, and bridge back
   into the categorical tower.

The split is sensible. The proof-oriented and executable representations serve genuinely different
purposes, and the three representations documented in `LeanNCD/LeanNCD.lean:59-75` should not be
collapsed merely to remove apparent duplication.

The executable layer has several good design choices: algebraic data types replace sentinels
(`Wire`, `BrOp`), errors are explicit (`CompileError`), compiler phases have distinct record types,
and the applicative axis traversal centralizes a previously repetitive operation. The categorical
layer also contains valuable work, especially the dependent `StMat` representation and the
free-symmetric-monoidal presentation of `Br`.

The main concern is that the public surface currently overstates what is established. Some central
theorems do not follow from their stated hypotheses, the flagship graded instance is entirely
axiom-backed except for its shape map, and several executable paths silently change or erase
semantics. These should be addressed before investing in ergonomic proof refactors.

## Evidence and validation

The initial review was followed by a second, high-effort validation pass. I built the complete
library and test suite, wrote three isolated Lean artifacts outside the repository, and ran them
against the current source:

```text
cd LeanNCD && lake build LeanNCD       # passed: 8,520 jobs
cd LeanNCD && lake build Tests         # passed: 8,607 jobs
cd LeanNCD && lake env lean <artifact>
```

The artifacts are retained under the session directory:

- `files/WeaveCountermodel.lean`: constructs lawful `ColoredPROP`, `Elemental`, and
  `DGradedColoredPROP` instances, then proves
  `¬ Subsingleton (Weave g)`;
- `files/InterfaceCounterexamples.lean`: constructs a lawful `ColoredPROP` whose advertised
  `toList`/`ofList` are not inverse, and defines a generic function that retags any
  `TargetActegory D V R` as `TargetActegory D V S`;
- `files/RuntimeRegressions.lean`: executes nonlinear scatter, an unsized surface-language scan,
  `recurMorphism`, and compound-size CSV serialization regressions;
- `files/Spike4Regressions.lean`: executes the seeded-assignment missing-size default, the
  contracted-axis `getD 1` default, and the plain-versus-scan predicate contraction divergence.

Evidence labels used below:

- **Disproved interface claim**: a compiled Lean countermodel satisfies the current assumptions and
  refutes the claim.
- **Reproduced runtime bug**: an executable Lean example observes the behavior.
- **Verified source defect**: control/data flow establishes the issue, but no semantic theorem was
  attempted.
- **Design risk**: an improvement recommendation, not a demonstrated incorrect result.

The fact that `lake build Tests` passes is significant: the runtime bugs below are missing test
cases or accepted gaps, not failures already visible in the current suite.

## Validated findings

The findings are organized from immediate observed failures, through the proof and executable
interfaces that permit them, to the cross-layer semantic and testing gaps that make them difficult to
detect. The numbering is retained so later roadmap sections can refer back to specific evidence.

### Immediate correctness failures

#### 1. `weave_unique` is false under the encoded assumptions

**Evidence: disproved interface claim.**

`Weave` stores arbitrary intermediate objects, an arbitrary morphism `f`, a degree, and two arbitrary
boundary maps (`LeanNCD/LeanNCD/Core/Weave.lean:11-23`). Nothing records that `f` is a base or
degree-trivial operation, that the factorization is cartesian, or what equivalence identifies two
factorizations. Likewise, `broadcast_gen` only asserts existence of an unrestricted factorization
(`Core/Graded.lean:87-92`).

`Elemental` says that points separate parallel morphisms (`Base/ColoredPROP.lean:93-96`). It does not
make arbitrary factorizations unique. Consequently,

```lean
Subsingleton (Weave (D := D) g)
```

at `Core/Weave.lean:29-32` does not follow from the current assumptions.

`WeaveCountermodel.lean` makes this precise. Let both object types be `List Unit`, let every hom-set
be `Unit`, and let the action ignore its degree argument. This model satisfies `ColoredPROP`,
`Elemental`, every current `DGradedColoredPROP` field, and `broadcast_gen`. For the unique
endomorphism of `[]`, however, there are distinct weave records with

```lean
P := Opposite.op []
P := Opposite.op [()]
```

and the artifact proves these records unequal by projecting `Weave.P`. It then proves:

```lean
example : ¬ Subsingleton (Weave (D := Obj) g) := ...
```

The artifact compiles with exit code zero. Thus the admitted theorem is inconsistent with the class
interface in the ordinary model-theoretic sense: if its `sorry` were replaced by a proof from only
the listed hypotheses, Lean would prove `False` in the countermodel.

**Recommended refactor**

- Define the relevant projection/fibration explicitly.
- Represent a weave using a `Cartesian` predicate or a chosen cleavage, rather than an unrestricted
  factorization record.
- State uniqueness up to the appropriate vertical isomorphism or setoid. Raw record equality is
  usually too strict because equivalent cartesian lifts can differ by coherence isomorphisms.
- Encode “degree-trivial” as a predicate or a separate base-morphism type and require it in `Weave`.

This follows the standard “make illegal states unrepresentable” principle: the type of a weave should
contain exactly the evidence needed by the uniqueness theorem.

#### 2. The flagship \(D=\mathrm{St}, C=\mathrm{Br}\) instance is not yet verified

**Evidence: build diagnostics and axiom inspection.**

`Instances/StBr.lean:13-24` supplies `sorry` for `act`, all coherence isomorphisms, all action and
distributivity laws, and `broadcast_gen`. Any specialization through this instance therefore relies
on `sorryAx`. Additional open assumptions include the two `St` hexagons
(`Base/St.lean:269-270`), `brCancelPoint` (`Base/Br.lean:305-307`), and weave uniqueness.

The codebase already labels many of these as deliberate milestones, which is good. However, the
instance is globally available, so downstream declarations can look proved while inheriting these
axioms.

The clean build confirms warnings for `Base/St.lean`, `Base/Br.lean`, `Core/Weave.lean`, and
`Instances/StBr.lean`. The complete test suite still passes because tests such as
`test/Core/WeaveTest.lean:8-10` and `test/Instances/StBrTest.lean:8-12` check that declarations
elaborate, not that their axiom closure excludes `sorryAx`.

**Recommended refactor**

- Keep an interface-only declaration for downstream signature development, but move the admitted
  flagship instance into an explicitly named namespace or module such as `Experimental` or
  `Axiomatic`.
- Do not import that module from the default `LeanNCD.lean` umbrella until its core laws are proved,
  or expose it under a scoped instance so importing unrelated modules cannot select it silently.
- Add CI checks that fail if selected “trusted core” declarations contain `sorryAx`. `#print axioms`
  in `test/Core/GradedTest.lean:29-31` is diagnostic output, not a test assertion.

The useful boundary is not “files containing no `sorry`”; it is a named theorem/API set whose axiom
closure is checked.

#### 3. Nonlinear scatter expressions are evaluated as linear expressions

**Evidence: reproduced runtime bug.**

`lowerArith` preserves `rhs` when turning an affine assignment into a scatter
(`DSL/Pipeline/Structural.lean:773-789`). `splitStmt` then deliberately leaves every scatter
untouched (`DSL/Pipeline/Lowering.lean:29-45`). Finally, `evalScatter` computes the sum of products
but never applies `rhs.nonlin` (`Eval/Scatter.lean:15-50`).

Thus an expression such as

```text
Out[2*i] := relu(X[i])
```

is accepted but produces negative values when `X[i]` is negative. Current scatter tests only exercise
identity nonlinearities (`test/Eval/ScatterTest.lean:7-49`).

The regression artifact evaluates a one-element input `X = [-2]` with `rhs.nonlin := .relu` and an
affine scatter target. `evalScatter` returns `Out[0] = -2`, proving that the activation is erased.

**Recommended fix**

Choose and enforce one semantic rule:

- either reject non-identity nonlinearities on scatters during validation; or
- define whether the nonlinearity applies before collision reduction or after it, represent those two
  cases distinctly if both are needed, and implement the chosen semantics in lowering and evaluation.

Rejecting the unsupported form is preferable to silently erasing it.

#### 4. `recurMorphism` loses its payload during lowering

**Evidence: reproduced compile/evaluation mismatch plus verified source defect.**

`scanPre` owns a prebuilt `ThreadedComposed`, but its representative statement, step statements, and
input reads are all empty (`DSL/Pipeline/Lowering.lean:293-347`). `toBrBaseP` consequently builds a
new near-empty `.scanPre` operation rather than embedding or interpreting the supplied graph
(`Lowering.lean:461-494`); `buildStep` only checks that the original graph has at least one step
(`Lowering.lean:500-508`). Both evaluators explicitly reject this form
(`Eval/Eval.lean:46,65`; `Eval/Scan.lean:68-72`).

The regression artifact supplies a nonempty `ThreadedComposed` payload. `TLProgram.compile` accepts
the program, while `TLProgram.eval` fails with `scanPre unsupported`. Acceptance therefore does not
mean the construct has either preserved or executable semantics.

**Recommended fix**

Treat the escape hatch as one of:

- an opaque, validated primitive whose semantics are supplied to routing, realization, and evaluation;
- an inlined subgraph with explicit boundary ports; or
- an unsupported feature rejected by `compile`.

The current middle state—accepted, partially inspected, then semantically discarded—is unsafe.

#### 5. Missing scan sizes produce an empty tensor and runtime panics

**Evidence: reproduced runtime bug; stronger than the initial finding.**

`evalScan` maps an absent axis size to `0` (`Eval/Scan.lean:73-76`), after which
`List.range (L - 1)` performs no recurrence steps. `outputShape` independently defaults the same
missing UID to `0` (`Eval/Shape.lean:467-473`). The behavior is explicitly recorded as accepted in
`test/Eval/Portfolio/RejectTest.lean:119-121`.

The isolated surface-language program

```text
tensor X(j)
G[j, 0]    := X[j]
G[j, l +1] := G[j, l]
```

with input `X.shape = [2]` returns `G.shape = [2, 0]` and empty data. While writing the base slice,
Lean also emits two `Error: index out of bounds` panics from `DenseTensor.set!`. The process still
exits successfully and evaluation returns a value. This is worse than a merely empty scan: an
expected-error path crosses an unchecked array operation and leaks runtime panics without becoming
an `EvalError`.

An unspecified extent is not the same thing as an extent of zero. Require every iteration-axis UID
to be present in the inferred or explicit size environment before allocation. Return an `EvalError`
that names the missing axis. `DenseTensor.set!` should also have a checked boundary API so malformed
coordinates cannot emit a panic while the enclosing evaluator reports success.

#### 6. Boundary decoders and realizers use meaning-changing defaults

**Evidence: verified source defect; CSV case reproduced at runtime.**

Several total functions recover from malformed external data by constructing unrelated valid values:

- `realizeStMat` fills missing matrix entries with zero (`Bridge/Realize.lean:22-28`);
- `realizeBrBaseP` fills missing reindexings and weave entries with defaults
  (`Bridge/Realize.lean:44-60`);
- the ACSet decoder turns missing sizes, positions, operation names, and wires into zero, tiled,
  empty, or external-zero values (`Bridge/AcsetCodec.lean:236-305`);
- `realizeSBr` turns any malformed decoded graph into the empty identity morphism
  (`Bridge/SBr.lean:8-20`).

These are not neutral defaults: they alter the represented program while returning a success-shaped
result.

The CSV instance is executable evidence of the general pattern. `encodeSize (.add (.lit 2) (.lit 3))`
returns an error, but `writeSBr` emits the row `RawAxis:0,` and returns normally. This proves that a
known serialization failure is converted into corrupt output.

**Recommended refactor: parse, then validate**

Use a two-stage API:

```lean
def decodeSBr : SBrInstance → Except DecodeError UncheckedThreadedComposed
def validate  : UncheckedThreadedComposed → Except ValidationError CheckedThreadedComposed
def realize   : CheckedThreadedComposed → ...
```

Similarly, give `StMatP` a smart constructor or checked wrapper. `StMatP.validate`
(`DSL/Target.lean:19-33`) already defines the invariant; realization should consume evidence of that
invariant instead of accepting every `StMatP`.

This is the “parse, don’t validate” pattern in its useful typed form: convert untrusted data once into
a type whose consumers no longer need defaults or repeated checks.

### Categorical interfaces and proof surface

The immediate proof failures are symptoms of underconstrained public interfaces. This group separates
those interface-level problems from the executable pipeline defects below.

#### 7. `ColoredPROP` does not enforce the free object monoid it documents

**Evidence: disproved interface claim.**

The class claims that objects form the free monoid on `gen`, but provides unrelated `toList`,
`ofList`, `tensor`, and `unit` fields with no inverse laws or compatibility laws
(`Base/ColoredPROP.lean:40-53`). Therefore an instance can satisfy the class without being free on
`gen`. In particular, `sh_star` folds over `toList` (`Core/Graded.lean:8-13`) without a general
theorem connecting that fold to `ColoredPROP.tensor`.

`InterfaceCounterexamples.lean` constructs a valid instance with `ob := Unit`, `gen := Bool`,
`toList _ := []`, and `ofList _ := ()`. All current class laws hold, yet the artifact proves:

```lean
ColoredPROP.toList
  (ColoredPROP.ofList (ob := BadObj) [true]) ≠ [true]
```

This is not only a missing convenience theorem. It demonstrates that `ColoredPROP` currently means
“a strict symmetric monoidal category with two list conversion functions,” not the documented
“symmetric strict monoidal category whose object monoid is free on `gen`.”

**Recommended refactor**

Prefer one of:

1. make PROP objects definitionally `List gen`; or
2. bundle an equivalence `ob ≃ List gen` and derive `tensor`, `unit`, `toList`, and `ofList` from it.

The first option is simplest and matches `StObj` and `BrObj`. The second is useful only if genuinely
different object representations are required.

#### 8. The graded action laws are manually bundled and incomplete

**Evidence: verified source/interface gap.**

`DGradedColoredPROP` stores object-indexed isomorphism families and large conjunctions of equations
(`Core/Graded.lean:26-92`). `dist_coh` gives naturality of `δ` in the two `C` arguments and
naturality of `δ0` in the degree, but not naturality of `δ` in degree morphisms, nor the full
compatibility of `δ`/`δ0` with the action associator and unitor (`Core/Graded.lean:71-86`).
`TargetActegory` duplicates the same encoding (`Algebra/Target.lean:14-65`).

This style is verbose and makes omissions difficult to detect.

**Recommended refactor**

- Package each fixed-degree action as a functor and its tensor preservation as a strong monoidal
  functor.
- Package `υ`, `α`, and distributors as natural isomorphisms rather than functions plus separate
  naturality equations.
- Define the action as a monoidal functor from \(D^{op}\) into an appropriate category of monoidal
  endofunctors when Mathlib support makes this practical.
- If that abstraction is too expensive today, introduce small named structures (`ActionLaws`,
  `StrongMonoidalActionLaws`) rather than conjunction-valued fields. Named fields improve projection,
  error messages, and incremental proof construction.

This is an application of algebraic interface design: laws should live beside the operation they
govern, and standard structures should replace parallel hand-written encodings.

#### 9. Algebra equivariance is only natural in one variable

**Evidence: verified source/interface gap.**

`Algebra.equivar` is indexed by both `X` and `P`, but `equivar_nat` only states naturality in `X` at a
fixed `P` (`Algebra/Algebra.lean:21-33`). `F_ev_p` is then carried as an additional law
(`Algebra/Algebra.lean:74-83`), although preservation of degree reindexings should follow from full
naturality in \(C \times D^{op}\).

Define `equivar` as a natural isomorphism between the two composite functors out of
\(C \times D^{op}\). This both strengthens the definition and removes a source of duplicated proof
obligations.

#### 10. The semiring parameter is phantom in `TargetActegory`

**Evidence: compiled parametricity witness.**

`TargetActegory D V R` requires `[CommSemiring R]`, but no field or law mentions values of type `R`
(`Algebra/Target.lean:14-65`). The same categorical structure can therefore be reused for arbitrary
semirings without witnessing the claimed change in contraction semantics.

`InterfaceCounterexamples.lean` defines, without assumptions beyond the two semiring instances:

```lean
def changeSemiring
    (t : TargetActegory D V R) : TargetActegory D V S := {
  actV := t.actV
  ...
}
```

Every field is copied unchanged. This is a mechanically checked witness that `R` carries no
information in this class.

Either:

- remove `R` from this purely categorical action interface; or
- add a separate enriched/linear tensor semantics interface that genuinely relates `V`, its homs or
  tensor objects, and scalar operations in `R`.

Separating the shape action from scalar semantics is likely clearer than forcing both concerns into
one typeclass.

#### 11. Generic adapter instances can create typeclass diamonds

**Evidence: design risk, not a reproduced failure in current instances.**

`Seam/Adapter.lean` globally derives `Category`, `MonoidalCategory`, and `SymmetricCategory` instances
for every type carrying `ColoredPROP` (`Seam/Adapter.lean:8-17,53-95,105-157`). If a type also has
independently defined Mathlib category instances, Lean may select structures that are propositionally
equivalent but not definitionally identical.

Prefer either:

- making `ColoredPROP` extend the Mathlib structures directly; or
- a bundled adapter type/newtype with local or scoped instances.

The second option preserves the current lightweight base model while making instance selection
explicit.

#### 12. Temporal iteration is data, not yet a recursion scheme

**Evidence: verified source/interface gap.**

`TemporalGraded.iterate` and `trace` are arbitrary morphism families with no zero, successor, fusion,
or trace compatibility laws (`Mixins/Temporal.lean:31-41`). The theorem named
`scan_catamorphism` proves only that postcomposition with identity restriction changes nothing
(`Props/Generic.lean:50-62`).

This should not be advertised as a catamorphism theorem yet.

**Recommended refactor**

- Add `iterate_zero` and `iterate_succ` laws, or define bounded iteration by `Nat.rec` when the model
  permits it.
- Add a fusion law and the trace/prefix restriction law needed by the paper.
- Rename the current theorem to something like `iterate_restrict_refl` until the universal property is
  encoded.

These are standard recursion-scheme interfaces: constructors and a fusion/universal law provide the
induction principle that an opaque `iterate` field does not.

#### 13. Stub structures should not masquerade as established mathematics

**Evidence: verified source/interface gap.**

`structuralCongruence` is currently `True` and `Dat` is constantly `Unit`
(`Grothendieck/Split.lean:8-50`). `RouteStructure` and `SymmetryGraded` add no fields beyond their
parent (`Mixins/Stubs.lean:10-19`).

These placeholders are clearly commented, but they still elaborate as ordinary definitions and can
make vacuous theorems appear meaningful.

Move them under an explicit `Stub`/`Experimental` namespace, or replace them with interfaces whose
constructors are not exported until real data is available. Avoid proving named mathematical claims
against `True` and `Unit` placeholders.

### Executable and compiler design

These findings concern local representation and phase design in the computable frontend. They become
cross-layer correctness issues when lowering or bridge code discards the information described here.

#### 14. Phase types are useful, but most invariants remain comments

**Evidence: verified source design limitation.**

`LabeledProgram`, `ResolvedProgram`, `LoweredProgram`, `ScanProgram`, `LinearProgram`, and
`ScheduledProgram` are distinct types (`DSL/Pipeline/Types.lean:20-53`), which is a good start.
However, several comments describe properties not encoded by their fields. For example,
`LinearProgram` still stores unrestricted `ScanStmt`, and `LoweredProgram` still stores unrestricted
`Stmt`.

Do not immediately index the entire AST with many dependent proofs; that would make ordinary compiler
work cumbersome. Instead, introduce small phase-specific node types only where downstream code
currently relies on partial matches or defaults:

- `LinearStmt` with no embedded nonlinearity;
- `ValidatedScatter` with an explicit collision policy and supported nonlinearity placement;
- `SizedScan` carrying nonempty iteration axes and their resolved extents;
- `CheckedBrBaseP`/`CheckedThreadedComposed` for bridge inputs.

This is a pragmatic typestate design: refine at high-risk boundaries rather than making every syntax
tree fully dependent.

#### 15. Minimize effects per compiler phase

**Evidence: design recommendation.**

Every phase is expressed in `FreshM = EStateM CompileError Nat`
(`Exec/Uid.lean:38-46`), even phases that only validate or transform without allocating UIDs.
This broad effect makes proof statements and reuse more complicated than necessary.

Use the weakest sufficient effect:

- pure functions for total transformations;
- `Except CompileError` for validation;
- `StateT Nat (Except CompileError)` only for UID-generating phases.

Lift the smaller effects when composing the full pipeline. This follows the functional-programming
principle that effect types are part of the specification: a phase that cannot mutate freshness state
should say so in its type.

#### 16. The applicative traversal is a strong pattern worth extending carefully

**Evidence: positive pattern, supported by equivalence regressions.**

`DSL/TraverseAxes.lean:49-126` implements van Laarhoven-style applicative traversals over the syntax
tree. It correctly supports both rebuilding (`Id`) and collection (`ConstL`) and has equivalence tests.
This is one of the clearest abstractions in the executable layer.

Possible small improvements:

- replace the list-specific `ConstL` with a generic `Const M` when a monoid is available, unless the
  local version materially improves elaboration;
- define traversal laws/tests: identity and composition, plus order preservation for collectors;
- use the same pattern for other repeated syntax walks only when they truly share traversal order and
  coverage. The explicit distinction between masked and unmasked RHS traversal
  (`TraverseAxes.lean:91-102`) is important and should not be abstracted away.

#### 17. CSV serialization discards errors

**Evidence: reproduced runtime bug.**

`encodeSize` correctly returns an error for compound expressions (`Acset/Csv.lean:66-82`), but
`writeSBr` converts failures to empty strings using `.toOption.getD ""`
(`Acset/Io.lean:13-18`). This creates corrupt output while reporting success.

Make row builders and `writeSBr` return `Except CsvError ...`, and combine independent field checks
with `mapM`/applicative traversal. Serialization is a boundary where explicit failure is preferable
to a total function.

#### 18. Dtype semantics disappear at the bridge

**Evidence: verified source defect.**

The frontend validates predicate outputs and axis kinds (`DSL/Pipeline/Structural.lean:707-745`), but
`BrBaseP` carries no dtype (`DSL/Target.lean:89-99`) and `weaveToArrayType` hard-codes every array to
`.reals` (`Bridge/Realize.lean:38-42`).

Carry an explicit dtype or scalar-semantics tag in the target IR and preserve it through routing,
ACSet encoding, and realization. Do not reconstruct it from operation names or default to real
values. This also gives the currently phantom semiring discussion a concrete executable counterpart.

### Cross-layer semantics

The local findings above converge on one architectural problem: scheduled evaluation and routed
realization do not yet share a semantics-preserving intermediate representation.

#### 19. There is no single semantic IR

**Evidence: verified architecture gap.**

`TLProgram.compile` and `TLProgram.eval` deliberately diverge:

```text
TLProgram
  ├─ compileToScheduled ──> ScheduledProgram ──> evaluator
  └─ compileToScheduled ──> ScheduledProgram ──> route ──> ThreadedComposed ──> realize
```

`DSL/Compile.lean:30-34` explains that `ThreadedComposed` collapses scan bodies and cannot be
evaluated. `Eval/Eval.lean:69-73` therefore evaluates `ScheduledProgram`, not the artifact returned by
`compile`. `Bridge/Agreement.lean` proves structural facts about successful routing and realization,
but not that scheduled evaluation agrees with the denotation of the realized routed morphism.

This creates two meanings of “the compiled program”:

- the rich scheduled IR used for executable behavior; and
- the lossy routed IR used for categorical realization and serialization.

The `recurMorphism` result is a direct symptom: enough data survives to accept the routed form, while
the evaluator has no semantics for it. Scan bodies are another explicit loss point.

**Recommended refactor**

Choose one of two architectures:

1. **Semantics-preserving lowering.** Make `ThreadedComposed` rich enough to carry scan bodies,
   scalar/dtype semantics, and opaque primitive payloads. Define evaluation and realization from this
   common IR, then prove lowering preserves interpretation.
2. **Explicit abstraction boundary.** Keep the routed IR intentionally abstract, but define a
   simulation/denotation relation between `ScheduledProgram` and `ThreadedComposed`. Every lossy
   operation must carry a semantic summary sufficient to prove the relation.

The core theorem should be a commuting diagram, not merely shape agreement:

```text
evalScheduled (compileToScheduled p) inputs
    ≈ interpret (realize (route (compileToScheduled p))) inputs
```

Without such a theorem, bridge correctness can establish well-typed wiring while semantic fields
such as activation, dtype, recurrence, or reduction policy disappear.

#### 20. Defaults are being used as implicit error recovery

**Evidence: quantitative source inspection plus reproduced failures.**

There are 262 `getD` occurrences under `LeanNCD/LeanNCD`; the concentration is notable:
`Bridge/AcsetCodec.lean` contains 138 and `Bridge/Realize.lean` contains 27. Many uses are harmless in
proofs after a bounds hypothesis, but boundary code repeatedly combines:

- list representations with documented length invariants;
- derived `Inhabited` instances;
- `getD` with semantically meaningful defaults (`0`, `[]`, `.external 0`, or `default`); and
- total APIs that cannot report malformed input.

This combination is an anti-pattern: `Inhabited` is being used to satisfy indexing rather than to
represent a legitimate domain default. It weakens the benefit of earlier phase checks because later
code can still manufacture a value when evidence is absent.

Use three explicit forms:

```lean
structure RawStMatP       -- external/untrusted lists
structure CheckedStMatP   -- raw value plus dimensional proof
structure DenseStMatP     -- vectors or `Fin`-indexed functions, no missing entries
```

At proof-heavy boundaries, prefer `Vector`, `Fin`, or `List.get` with a proof. At executable external
boundaries, prefer `Except` with a path-rich error. Reserve `getD` for algorithms where the default is
part of the actual mathematics, not a substitute for an invariant.

### Testing and trust automation

The current suite validates many structural properties but does not yet enforce the semantic and trust
boundaries identified above.

#### 21. Test semantic preservation, not only elaboration

**Evidence: full current suite passes despite all reproduced runtime bugs.**

Several proof-layer tests only `#check` declarations (`test/Core/WeaveTest.lean:8-10`,
`test/Instances/StBrTest.lean:8-12`). Add tests for:

- absence of `sorryAx` in the trusted API;
- countermodels or negative compile tests for overly strong interfaces;
- end-to-end semantic preservation across parse, scheduled evaluation, routing, ACSet round-trip, and
  realization for each supported operation class;
- nonlinear scatter and missing scan-size regressions;
- malformed ACSet/CSV inputs returning errors rather than identities/default-filled programs.

Property tests are especially appropriate for codec round trips and affine reindexing. The existing
property-oracle infrastructure is a good foundation.

#### 22. Generate the `sorry` inventory

**Evidence: build diagnostics contradict the hand-maintained status text.**

`SORRY_INVENTORY.md` contains historical contradictions: it correctly records the `St` hexagon
obligations at lines 3-5 and 25-27, then says "`St` is fully sorry-free again" at line 122 even though
`Base/St.lean:269-270` still contains both `sorry`s.

Generate this report from source and selected `#print axioms` output in CI. Hand-maintained proof
status documents become stale quickly and are risky in a verification-oriented project.

Several source comments are stale for the same reason; for example, `Seam/Adapter.lean:42-52` and
`97-104` still describe obligations that the implementations below now discharge.

### Regression specifications

The isolated artifacts should be converted into repository tests after the intended behavior is
chosen. The important assertions are:

#### Nonlinear scatter

```lean
-- X = [-2], affine placement, rhs.nonlin = relu
match evalScatter env sizes "Out" slots rhs opts [2] with
| .ok (_, out) => assert! out.get! [0] == 0.0
| .error e => fail e
```

This currently observes `-2.0`.

#### Unsized scan

```lean
match TLProgram.eval (tlprog!{
  tensor X(j)
  G[j, 0]    := X[j]
  G[j, l +1] := G[j, l]
}) inputs with
| .error e => assert! e.contains "unsized iteration axis"
| .ok _    => fail "expected size error"
```

This currently emits two bounds panics and returns a tensor with shape `[2, 0]`.

#### `recurMorphism`

Until semantics exist, compilation itself should reject the construct:

```lean
match p.compile.run 0 with
| .error (.unsupportedRecurMorphism _) _ => pure ()
| _ => fail "accepted a construct with no evaluator/realizer semantics"
```

Currently compilation succeeds and evaluation later reports `scanPre unsupported`.

#### CSV compound sizes

```lean
match writeSBr instWithCompoundSize with
| .error (.unsupportedSizeExpr _) => pure ()
| .ok _ => fail "serialization erased encodeSize failure"
```

Currently `writeSBr` is total and emits `RawAxis:0,`.

#### Trusted-core axiom closure

Add a small executable CI checker over declarations intended to be trusted. Textual `#print axioms`
is useful to humans but does not fail a build. At minimum, the checker should reject `sorryAx` in:

- the exported `St` and `Br` category instances;
- `DGradedColoredPROP` flagship instances;
- generic propositions advertised as proved; and
- bridge agreement theorems.

The weave countermodel should remain as a model test even after redesign: it should fail to construct
the new cartesian/normalized `Weave`, demonstrating that the corrected interface excludes the old
countermodel for the relevant reason rather than through an unrelated stronger axiom.

Together, these findings provide the evidence base for evaluating the existing restructuring proposal.
The next part does not introduce a separate critique; it translates the findings into changes to Spike
3, missing work in the broader plan, enforceable guarantees, and a dependency-ordered roadmap.

## Assessment and revised restructuring plan

The restructuring document is directionally strong. In particular, it is right to preserve the
proof/execution representation boundary, replace repeated AST walks with one applicative traversal,
keep externally visible serialization tags explicit, and use distinct phase types instead of one
large record with progressively meaningful fields. Its emphasis on small spikes and permanent
equivalence tests is also appropriate for a codebase where definitional unfolding currently appears
in proofs.

The main gap is prioritization. Several items described as deferred investigations or optional
cleanup are already demonstrated correctness failures or confirmed semantic erasures. Conversely,
some proposed refactors improve constructor coverage without repairing the boundary at which the
covered data is later discarded. The plan should distinguish:

1. **representation closure**: every constructor is classified by an exhaustive match;
2. **semantic closure**: every source operation has enough data in the target IR to be interpreted;
3. **boundary validity**: malformed external values cannot be silently converted into valid-looking
   internal values; and
4. **proof validity**: theorem statements actually follow from the advertised interfaces.

Spike 3 substantially improves the first item. It does not, by itself, establish the other three.

### Spike 3 assessment

This first group evaluates the proposed `Nonlin` restructuring on its own terms: what it improves,
which current files it actually touches, and which correctness problems remain outside its scope.

#### Spike 3 traceability to the four guarantees

The concrete Spike 3 suggestions should be read as a set of obligations against the four guarantee
buckets, not as unrelated cleanup tasks:

| Spike 3 suggestion | Primary guarantee | Concrete enforcement | What remains after Spike 3 |
|---|---|---|---|
| Group `Nonlin` into `PointwiseFn` and `AxiswiseFn` | **Representation closure** | closed enums; exhaustive matches; no semantic `_` arms | does not provide evaluator or target semantics for a newly added function |
| Migrate every post-E1 traversal, lowering, evaluator, and test site | **Representation closure** and local **proof validity** | Lean exhaustiveness plus independent traversal/fusion theorems | does not repair unrelated categorical interfaces or admitted proofs |
| Split pointwise and axiswise syntax categories | **Representation closure** and source **boundary validity** | invalid pointwise masks are unrepresentable or rejected by a total elaborator | does not validate resolved output axes or imported target data |
| Introduce `ResolvedNonlin` with a checked `NormAxis` | **Boundary validity** | `Except`-returning resolution; evaluators consume only the checked axis | does not preserve masks/axes in `BrBaseP` or the codec |
| Reject nonlinear scatter until semantics are chosen | **Semantic closure by explicit exclusion** and **boundary validity** | capability preflight returns a named error before evaluation/lowering | full semantic closure requires a typed scatter/nonlinearity policy later |
| Centralize `PointwiseFn.toBrOp` and `AxiswiseFn.toBrOp` | **Representation closure** | adding an enum constructor makes target classification fail to compile | a `BrOp` tag alone does not preserve masks or other payload |
| Keep stable explicit `brOpIdx` tags and make decoding partial | **Boundary validity** | `brOpOfIdx?`/`Except`; unknown tags cannot become `.contract` | full raw/checked bridge validation is Stage 5 |
| Preserve independent traversal-equivalence and fusion proofs | local **proof validity** | proofs compare production traversal with independent references | categorical proof validity still requires interface repair and axiom-closure CI |
| Defer Spike 3c until `UnaryOp` lowering is designed | **Semantic closure** | do not erase the distinction before its target representation is known | choose intermediate lowering, typed scalar payload, or explicit routed rejection |

This table also states the limit of Spike 3 precisely:

- after Spike 3a/3b, **representation closure** may be claimed for the `Nonlin` family;
- selected source **boundary validity** may be claimed for keyword/mask shape, norm-axis resolution,
  nonlinear-scatter rejection, and operation-tag decoding only if those checks land;
- **semantic closure** may be claimed only as "supported operations are preserved; unsupported ones are
  explicitly rejected," not as full routed support for every nonlinearity; and
- **proof validity** may be claimed for the migrated traversal/fusion results only, not for
  `weave_unique`, the flagship graded instance, or the categorical interfaces.

#### The proposed grouping is useful but its claim should be narrower

The proposed shape

```lean
inductive PointwiseFn
  | relu | sigmoid | tanh | gelu | leakyrelu

inductive RowwiseFn
  | softmax | normalize | l2normalize

inductive Nonlin
  | identity
  | pointwise : PointwiseFn -> Nonlin
  | rowwise   : RowwiseFn -> Option BoolExpr -> Nonlin
```

is a real improvement over the flat nine-constructor `Nonlin`. It makes a pointwise function carrying
a mask unrepresentable and moves the important pointwise-versus-axis-reducing distinction into the
type. That directly removes the wildcard-classification hazard currently documented in
`Eval/Eval.lean:30-41` and duplicated in `Eval/Scan.lean:42-49`.

`AxiswiseFn` would be a more precise name than `RowwiseFn`. These operations act along a designated
axis of an arbitrary-rank tensor; that axis is not intrinsically a matrix row. The current evaluator's
`perRow` implementation is an implementation view, not the source-language invariant. If "rowwise"
is already established project terminology, keep it but document this meaning explicitly.

The new enums need the same derives required by their enclosing AST and macro tests:

```lean
deriving DecidableEq, Repr, Lean.ToExpr, Inhabited
```

More importantly, the document's statement that a new rowwise function will "automatically flow
through mask collection, norm-axis lookup, and nonlin-split at every site" is too strong. Grouping
forces category-level handling, but a new concrete function still requires:

- evaluator semantics;
- a total mapping to the target primitive (`BrOp`);
- a stable serialization-tag decision;
- syntax and elaboration support;
- direct and scan evaluator tests; and
- target/codec tests.

The type prevents a new operation from being *misclassified as pointwise*. It cannot manufacture the
operation's semantics. This is still valuable, but the acceptance criterion should say exactly that.

**Guarantee linkage.**

- **Representation closure:** this is the primary benefit. The category of each nonlinearity is
  encoded once in the constructor rather than rediscovered by wildcard-prone matches.
- **Semantic closure:** not yet established. Every new enum case still needs evaluator dispatch,
  target payload, codec support, and an agreement test, or a capability-specific rejection.
- **Boundary validity:** improved only insofar as pointwise functions can no longer carry masks in the
  AST. Norm-axis and external-data validity require separate checked forms.
- **Proof validity:** the datatype change creates new exhaustiveness obligations, but proves no
  categorical theorem by itself.

#### Plan against the current post-E1 tree

The line references and affected-site count in the proposal predate the E1 traversal work. The
current migration surface includes more than the obvious evaluator matches:

- `DSL/Ast.lean`: the datatype and `Stmt.nonlinOf`;
- `DSL/TraverseAxes.lean`: the authoritative exhaustive traversal;
- `DSL/Pipeline/Structural.lean`: `nonlinAxisUidFusion`;
- `DSL/Pipeline/Lowering.lean`: splitting and `BrOp` selection;
- `Eval/Nonlin.lean`: operation semantics;
- `Eval/Eval.lean` and `Eval/Scan.lean`: norm-axis resolution;
- `DSL/Syntax.lean` and `DSL/Elab.lean`: surface constructors;
- `test/DSL/TraverseAxesEquiv.lean`: independent `Nonlin.mapUID_ref`; and
- `test/DSL/TraverseAxesSpike.lean`: the independent collector and exhaustive proof.

The last two are not disposable migration scaffolding. Their file headers explicitly describe them
as permanent regression certificates. They should remain independent references rather than being
rewritten to call the new production helpers, which would make the equivalence tests tautological.
`Structural.lean`'s fusion proof must also be updated; changing only the traversal implementation
will not complete Spike 3.

The clean production traversal after grouping should have only the semantic distinction:

```lean
def Nonlin.traverseAxes [Applicative f]
    (g : AxisSpec -> f AxisSpec) : Nonlin -> f Nonlin
  | .identity          => pure .identity
  | .pointwise fn      => pure (.pointwise fn)
  | .rowwise fn mask   =>
      Nonlin.rowwise fn <$> Traversable.traverse (BoolExpr.traverseAxes g) mask
```

By contrast, the independent references in the tests should still be written directly enough to
catch a production traversal that accidentally drops the mask.

**Guarantee linkage.**

- **Representation closure:** migrating every listed site prevents an old match from remaining as an
  untracked second classifier.
- **Proof validity:** `nonlinAxisUidFusion`, `Nonlin.mapUID_eq_ref`, and
  `traverseAxes_const_eq_specsNonlin` are the local certificates that the new representation preserves
  traversal meaning.
- **Semantic closure:** evaluator parity tests prevent this refactor from changing existing supported
  behavior, but they do not show that routed lowering preserves the mask or norm axis.
- **Boundary validity:** this migration has no external-boundary claim.

#### Keep syntax categories typed too

Spike 3b's keyword table reduces copy-paste, but one generic `tl_nonlin_kw` category merely moves the
invalid pointwise-mask combination from the AST into elaboration. A stronger and simpler grammar uses
separate closed categories:

```text
tl_pointwise_kw := relu | sigmoid | tanh | gelu | leakyrelu
tl_axiswise_kw  := softmax | normalize | l2normalize
```

Only the axiswise category should admit a `where` mask. This follows the "parse, do not validate"
principle: syntax that cannot denote an AST value should preferably fail before semantic
elaboration. If a generic category is retained to produce a better custom error, its classifier must
return `Except`/`Option` and must not have a default function. Either design should retain regression
tests for:

- `softmax(sum)` and the analogous unmasked normalization forms;
- all three masked axiswise forms;
- rejection of `relu(where ...)` with a clear diagnostic;
- every pointwise keyword without a marked norm axis; and
- unknown or misspelled keywords.

Lean's grammar remains statically declared even if the spelling-to-enum conversion is table-driven.
The proposal should therefore distinguish a centralized closed keyword table from genuinely
extensible operation registration. The former is useful and sufficient here; it is not an open
plugin mechanism.

**Guarantee linkage.**

- **Representation closure:** separate closed keyword categories must map exhaustively to the
  corresponding closed enums.
- **Boundary validity:** malformed source combinations such as `relu(where ...)` fail at the language
  boundary rather than becoming a partially valid AST.
- **Semantic closure:** syntax acceptance must not imply routed support; capability validation still
  decides whether an elaborated operation can be evaluated, routed, serialized, or realized.
- **Proof validity:** parser tests are evidence about syntax behavior, not theorem validity.

#### Norm-axis validity needs a resolved form

Grouping identifies which operations *need* a reduction axis, but it does not establish that the
marked output axis exists or identify its position. Today `Eval/Eval.lean` and `Eval/Scan.lean`
recompute this fact independently and fail at runtime.

This is a good candidate for the light typestate proposed later in E2. Keep the surface AST convenient,
but have a resolution/validation phase produce an internal form such as:

```lean
inductive ResolvedNonlin
  | identity
  | pointwise : PointwiseFn -> ResolvedNonlin
  | axiswise  : AxiswiseFn -> NormAxis -> Option BoolExpr -> ResolvedNonlin
```

`NormAxis` should contain a position or UID already checked against the output axes. In a list-based
executable IR it can be a checked wrapper constructed by `Except`; a more dependent IR can use
`Fin outputRank` or a membership proof. The important point is that evaluation should consume the
resolved fact rather than search again. This is precisely the kind of local refinement E2 should
introduce early: it eliminates a real malformed state without indexing the entire compiler by every
possible invariant.

**Guarantee linkage.**

- **Boundary validity:** this is the principal bucket. `resolveNonlin` should be the only constructor
  of an axiswise resolved operation and should return `Except` when the marker is absent, duplicated,
  or not among the output axes.
- **Representation closure:** `ResolvedNonlin.axiswise` makes the required `NormAxis` field
  constructor-specific rather than optional data interpreted by convention.
- **Semantic closure:** scheduled evaluation becomes closed with respect to norm-axis lookup once both
  plain and scan evaluators consume `ResolvedNonlin`; routed semantic closure still requires carrying
  that resolved axis into the target.
- **Proof validity:** if a proof uses norm-axis membership, it should consume the checked wrapper's
  evidence rather than repeat an unproved list-index assumption.

#### Spike 3 does not fix nonlinear scatter

The current semantic bug remains unchanged by constructor grouping:

- `splitStmt` passes `.scatter` through unchanged
  (`DSL/Pipeline/Lowering.lean:29-45`);
- `evalScatter` evaluates `rhs.body` but never applies `rhs.nonlin`
  (`Eval/Scatter.lean:15-50`); and
- the full test suite passes while the retained runtime regression observes `relu(-2) = -2`.

The comment that no example needs nonlinear scatter is not a validity condition. The AST accepts the
combination, so it needs semantics or an explicit rejection. The simplest behavior-safe policy for
Spike 3 is to reject every non-identity scatter during validation and make the evaluator retain a
defensive error. Supporting it requires a design decision: does the activation apply to each source
value before collision reduction, or to the completed output after fill/reduction? Axiswise
normalization makes those interpretations even less interchangeable. The plan should not choose one
implicitly.

This should be part of Spike 3's acceptance criteria because the refactor will otherwise make the
nonlinearity code look closed while a whole statement constructor still erases it.

**Guarantee linkage.**

- **Semantic closure:** until pre- versus post-reduction semantics are defined and represented,
  nonlinear scatter must be outside the supported fragment. Named rejection is the honest intermediate
  closure property.
- **Boundary validity:** validation must reject the unsupported constructor combination before
  `splitStmt`, `evalScatter`, or routed lowering can return a success-shaped value.
- **Representation closure:** the validator must match `.scatter` explicitly; a `_ => accepted`
  fallback would recreate the current bug.
- **Proof validity:** any future scatter law must state which ordering of nonlinearity, fill, and
  collision reduction it proves. Tests alone cannot choose that law.

#### Use total semantic mappings and preserve stable tags

The grouped enums should own total mappings:

```lean
def PointwiseFn.toBrOp : PointwiseFn -> BrOp
def AxiswiseFn.toBrOp  : AxiswiseFn -> BrOp
```

and equivalent evaluator dispatch. `ScanStmt.toBrBaseP` should delegate to these functions rather
than duplicate every concrete constructor. Exhaustive matching then forces a new function to receive
a target classification.

This does not justify deriving serialization indices from constructor order. The document is correct
to preserve the explicit `brOpIdx` table. Add tests or theorems for:

- `brOpOfIdx? (brOpIdx op) = some op`;
- distinct supported operations receiving distinct tags; and
- existing tags remaining unchanged when a source enum is reorganized.

The decoder should be partial on untrusted data. Current `brOpOfIdx` maps every unknown number to
`.contract` (`Bridge/AcsetCodec.lean:85-103`), which changes corrupt input into a valid contraction.
Keep the round-trip theorem, but expose `brOpOfIdx? : Nat -> Option BrOp` or an `Except` decoder at the
ACSet boundary rather than a meaning-changing default.

**Guarantee linkage.**

- **Representation closure:** total enum-to-`BrOp` functions ensure that adding a source operation
  creates a compile-time target-classification obligation.
- **Semantic closure:** classification is necessary but insufficient. The target constructor must
  carry all operation-specific payload, and `evalBrBaseP` must interpret it.
- **Boundary validity:** partial tag decoding prevents malformed ACSet input from silently acquiring
  contraction semantics.
- **Proof validity:** `brOpOfIdx? (brOpIdx op) = some op` and tag injectivity are the appropriate local
  codec theorems; they do not prove end-to-end numerical agreement.

#### Concrete Spike 3 acceptance checklist

Spike 3 should not be marked complete until each bucket's bounded acceptance criteria pass:

**Representation closure**

1. `PointwiseFn`, `AxiswiseFn`/`RowwiseFn`, and `Nonlin` have the required derives and no wildcard
   semantic dispatch.
2. All current source and test matches listed above have migrated.
3. `PointwiseFn.toBrOp`, `AxiswiseFn.toBrOp`, evaluator dispatch, and syntax classification are
   exhaustive.

**Semantic closure for the Spike 3 supported fragment**

4. Pointwise and axiswise scheduled semantics agree before and after the refactor in both plain
   statements and scan slices.
5. Nonlinear scatter is either rejected explicitly or given documented, tested semantics.
6. Any nonlinearity whose mask or resolved axis cannot survive routed lowering is rejected by the
   routed capability validator; it is not downgraded to an unparameterized `BrOp`.
7. Spike 3c remains deferred until `UnaryOp` has a preservation or explicit-rejection design.

**Boundary validity**

8. Masked and unmasked axiswise syntax has positive tests; pointwise masks and missing norm axes have
   negative tests.
9. Unknown serialized operation tags return an error rather than `.contract`.
10. The enum-to-`BrOp` mappings are total and existing serialized tags are unchanged.

**Proof validity**

11. Permanent traversal-equivalence and fusion proofs compile as independent checks.
12. Codec round-trip and tag-injectivity theorems cover supported `BrOp` tags.
13. No new `sorryAx` enters the declarations changed by Spike 3.
14. The completion report states that these are local AST/traversal/codec proof obligations and does
    not claim that the categorical proof gaps have been repaired.

Items 9 and 12 touch `AcsetCodec` rather than the core `Nonlin` refactor. They may be split into the
Stage 5 bridge-hardening commit if that keeps Spike 3 reviewable. If split, the Spike 3 completion
statement must say:

```text
source syntax/AST boundaries are checked;
imported ACSet operation tags remain outside the validated boundary until Stage 5.
```

It must not claim general boundary validity merely because source keyword classification is total.

Spike 3c, merging `Factor.unaryFn` into `Factor.read`, should remain deferred. The representation
cleanup is reasonable, but the more urgent question is whether the unary operator survives lowering
at all. Changing the source constructor before resolving that question risks making the loss less
visible without changing it.

### Missing work beyond Spike 3

The next group collects issues that constructor regrouping cannot solve. These are the missing
semantic, validation, and proof obligations that determine how Spike 3 should fit into the broader
restructuring effort.

#### The target IR currently erases operation payloads

E5 and E13 treat semantic evaluation and `BrOp` closure as future investigations. Source inspection
already establishes a stronger result: `BrBaseP` is not semantically complete for the current DSL.
It contains only:

```text
op, degree, inputWeaves, outputWeaves, reindexings
```

The following source payloads do not survive in that record:

- the `BoolExpr` mask for `softmax`, `normalize`, or `l2normalize`;
- the `UnaryOp` attached to a `Factor.unaryFn` (including division's `recip`);
- `ScatterOpts.fill` and `ScatterOpts.reduce`;
- output dtype/scalar semantics; and
- scan bodies (an already documented loss).

For example, `BrOp.softmax` is commented as supporting an optional mask, but `BrOp` and `BrBaseP`
have no field in which that mask can be stored. `AcsetCodec` explicitly emits
`opPredicate := none`, and `toBrBaseP` chooses an operation tag from `Stmt.nonlinOf` while deriving
its inputs only from tensor read factors. Likewise, an inline `log(X[i])` and a plain `X[i]` have the
same input name and reindexing; no target field records the `log`.

Therefore an `evalBrBaseP` can agree with scheduled evaluation only on a deliberately restricted
fragment. Before E5, add a **semantic payload audit** covering every source constructor and recording:

1. where its data is represented in the target;
2. how the ACSet codec preserves it;
3. how realization interprets it; and
4. which theorem or property test checks the path.

Any unsupported source form should fail lowering, not compile to a similar-looking primitive.
Alternatively, enrich the target primitive with typed payloads, for example a pointwise function,
axiswise function plus compiled mask, contraction operator, or scatter policy. This need not collapse
the proof and executable representations; it makes the executable presentation honest.

This also changes E13's starting point. The question is not only whether the *names* in `BrOp` form a
closed set. It is whether the parameterized primitive data required by those names is closed and
preserved. On the current source, the answer is already "no."

#### Promote E5 from optional architecture work

The lack of agreement between scheduled evaluation and routed realization is not merely a future
optimization concern. It is the mechanism by which masks, unary operations, scatter policy, dtype,
and recurrence can disappear while structural bridge theorems still pass.

E5 should move earlier, but in two stages:

1. define an executable denotation for the fragment the current target genuinely represents and make
   lowering reject everything outside that fragment; then
2. expand the target and the agreement theorem operation by operation.

The first commuting test should be small and explicit--for example plain contraction and ReLU--rather
than claiming all of `TLProgram`. Each newly supported operation class should add an end-to-end test
from source AST through routing and codec round-trip to target evaluation. Masked normalization,
unary reads, scatter, and scans should each remain visibly unsupported until their payloads survive.

This approach follows the document's own GHC Core analogy more closely: a small Core is useful only
when every accepted surface construct desugars into it without semantic loss.

#### E2 light typestate should move before the broad cleanup spikes

The proposal is cautious about typed IR because a fully indexed compiler could create proof overhead.
That caution is justified. However, a small resolved layer would already eliminate several observed
failures:

- axiswise nonlinearities without a marked norm axis;
- unsized scan axes;
- malformed affine matrices;
- unsupported `recurMorphism` evaluation; and
- nonlinear scatter under the reject-until-defined policy.

These are not speculative refinements. They are checks downstream code currently assumes or
rediscovers. Introduce checked wrappers only at these boundaries and keep the rest of the pipeline
ordinary data. This is the functional "make illegal states unrepresentable" pattern applied
selectively, not a request to dependent-type the whole compiler.

#### Boundary validation is under-scheduled

The plan treats proof-friendly dense matrices and some default elimination as optional because routed
values are normally well formed. That argument covers internal constructors, not imported ACSet/CSV
data. The current bridge APIs intentionally accept arbitrary structures and then use `getD` defaults.
Confirmed examples include:

- unknown operation tags becoming `.contract`;
- missing wires becoming `.external 0`;
- malformed matrix entries becoming zero;
- missing axes/weaves becoming empty/default values;
- compound size serialization becoming an empty field; and
- realization filling missing values rather than rejecting the presentation.

These defaults are meaning-changing even when no theorem consumes the result. A user can execute or
serialize the wrong graph. Move raw/checked wrappers and `Except`-returning decoders ahead of
proof-oriented matrix refactors:

```text
external rows -> Raw presentation -> validate -> Checked presentation -> realize/evaluate
```

`getD` can remain inside a proof whose index bound is already known. It should not define recovery
semantics for malformed external input.

#### The proof-track schedule omits disproved and phantom interfaces

Spike 7 says to park `weave_unique` because it is double-gated. The countermodel changes that
assessment: the theorem is false under the current assumptions. It should be removed from the trusted
surface or explicitly quarantined now, even if the replacement theory is deferred. A false theorem
does not become safer because few declarations currently consume it.

The replacement likely needs a chosen cartesian lift/cleavage, a predicate identifying vertical or
degree-trivial arrows, and uniqueness up to the appropriate vertical isomorphism or setoid. A raw
`Subsingleton (Weave g)` is too strong because the record contains arbitrary representatives.

The proof schedule also has no explicit work item for two compiled interface counterexamples:

- `ColoredPROP` documents a free object monoid but does not require `toList` and `ofList` to be
  inverse; and
- `TargetActegory D V R` can be retagged from any commutative semiring `R` to any other semiring
  because `R` appears in no field or law.

E3's executable semiring parameterization does not repair the second issue; it concerns a different
layer. The proof-track plan should decide separately whether `TargetActegory` should contain
`R`-dependent enrichment/action data or drop the parameter. Similarly, `ColoredPROP` should either
fix objects to `List gen` or store an actual equivalence with coherence laws.

The existing gaps in graded action coherence and algebra equivariance also remain outside the
restructuring schedule. They need not block Spike 3, but they should be visible proof-track milestones
rather than being hidden by progress on executable code.

#### Correct the cospan diagnosis

E13 describes non-bijective wiring as a missing generator of `Br`. There is an important distinction:
`copyW` and `delW` already are constructors in the `Br.Hom` syntax. The demonstrated limitation is
that the current `NData`/normal-form wiring representation uses a bijection and therefore cannot
model those existing constructors faithfully.

The immediate task is thus to extend the normalization/semantic model to non-bijective wiring, unless
the intended redesign genuinely changes the source `Hom` presentation. Calling every normal-form
limitation a missing syntax generator risks changing the wrong layer. The System-FC analogy remains
useful, but the writeup should say whether it proposes:

- a new `Hom` constructor;
- a richer normal form for existing constructors; or
- a semantic model/interpretation capable of representing copying and deletion.

Those are different proof obligations.

#### Add generated trust checks to the restructuring plan

The document carefully tracks completed spikes by date, but hand-maintained proof-status prose has
already become stale elsewhere in the repository. Add a generated CI check for the axiom closure of
the intended trusted API. At minimum, exported category instances, graded instances, bridge
agreement theorems, and generic theorems advertised as proved should fail CI if their axiom set
contains `sorryAx`.

This check should accompany, not replace, source-level `sorry` searching: a declaration can inherit an
admission transitively from an instance without containing `sorry` itself. It will also prevent a
future restructuring from moving an admission behind a cleaner interface and accidentally making the
trusted surface look more complete.

### Spike 4 assessment

Spike 4 correctly identifies substantial duplication in the evaluator, but it should not be executed
as nine independent cleanup tasks. Three items expose current semantic defects (4a, 4c, and 4g), three
change the contracts on which later generalization depends (4b, 4d, and 4h), and two overlap directly
with planned IR work (4f with E2/E4 and 4g with E3/target payload repair). Only the import extraction
part of 4i is an almost purely mechanical cleanup.

The intended JAX destination changes more than the motivation. It changes several proposed internal
contracts:

- E4's `EvalPlan` should move from optional optimization experiment to an early backend boundary;
- executable operation records must be closed, serializable data rather than collections of Lean
  callbacks;
- shape, dtype, normalization-axis, collision, and scan-order facts must be resolved before backend
  execution;
- backend capability rejection must be distinct from source invalidity; and
- reports must identify the plan, backend, device, numeric mode, and compilation-cache behavior.

Appendix A, [JAX as an evaluation backend](#appendix-a-jax-as-an-evaluation-backend), evaluates the
`lean4-mlir/jax` precedent and gives concrete lowering algorithms. Spike 4 should establish the
checked, backend-neutral meaning that an early E4 `EvalPlan` carries to JAX or PyTorch. It should not
put JAX arrays, functions, or tracing behavior into the source AST.

The current-source assessment is:

| Item | Current finding | Principal guarantee | Recommendation |
|---|---|---|---|
| **4a** | Confirmed duplication, plus two silent size defaults | boundary validity | Unify, but validate contracted and seeded axes as well as free axes |
| **4b** | Confirmed hard-coded product identity | semantic closure | Add `unit1`, use closed serializable operation tags, and distinguish RHS contraction from scatter collision reduction |
| **4c** | Confirmed semantic divergence for predicate scan states | semantic closure | Replace both paths with one dtype-aware seeded assignment worker |
| **4d** | Confirmed duplicate runtime lookup | boundary validity | Resolve once before evaluation; do not merely move the same lookup into `applyNonlin` |
| **4e** | Confirmed mixed responsibilities; current file is 475 lines | representation closure | Separate inference, checked tensor signatures, and backend capability validation |
| **4f** | Confirmed four-phase scan implementation and update-order sensitivity | semantic closure | Freeze a plan-level recurrence contract suitable for `lax.scan`; do not extract around mutable evaluator state |
| **4g** | Confirmed unknown strings silently mean overwrite | boundary and semantic validity | Introduce separate typed RHS aggregation and collision-reduction policies |
| **4h** | Confirmed string-only errors and eagerly rendered solver diagnostics | boundary validity | Separate compile, shape, plan, capability, and backend failures; avoid string catch-alls |
| **4i** | Confirmed compile import and warning side effect | boundary validity | Return an `EvalReport` with reproducibility and backend metadata rather than tracing warnings |

#### Corroborating examples

`files/Spike4Regressions.lean` compiles against the current source and records three behaviors that the
existing suite does not reject:

1. Calling `evalAssignSeeded` with an unseeded free output axis absent from `sizes` succeeds with an
   empty tensor of shape `[0]`.
2. Calling `evalAssignWith` with a contracted axis absent from `sizes` evaluates that axis at extent
   one. For `sum k, X[k]` with `X = [1,2,3]`, it returns `1` rather than rejecting the malformed
   evaluation context or returning `6`.
3. A predicate contraction with two satisfying assignments returns `1` through
   `evalAssignDtyped`, but the identical RHS returns `2` through `evalStmtSliceSeeded`. The scan path
   cannot select Boolean contraction because it receives no declarations and manually selects only by
   `rhs.agg`.

These are boundary and semantic counterexamples, not stylistic arguments. They also show why a
line-count-only refactor is insufficient: combining two partial evaluators can centralize the wrong
defaults unless the new worker's preconditions are made explicit.

#### 4a: unify assignment around a checked evaluation context

The core observation is correct: unseeded assignment is seeded assignment with an empty seed. The new
API should pass the `Combine` record proposed by 4b rather than three functions and should make the
seed an ordinary parameter:

```lean
def evalAssignCore
    (ops   : Combine)
    (env   : TensorEnv)
    (sizes : CheckedAxisSizes)
    (seed  : AxisCoord)
    (name  : String)
    (slots : List LHSSlot)
    (rhs   : RHSExpr) :
    Except EvalError (String × DenseTensor)
```

The important addition is `CheckedAxisSizes`/`AxisCoord`, or an equivalent validation step. The
proposal notices the missing free-axis check in the seeded path, but both current implementations also
use `(sizes[u]?).getD 1` for every term-local contracted axis. That silently changes a missing
dimension into a one-element contraction. The unified worker must require:

- a size for every non-seeded free output axis;
- a size for every contracted axis in each term;
- a declared size for every seeded axis;
- `0 <= seed[u] < sizes[u]` for each seed coordinate; and
- consistency between the output shape and the tensor allocated for it.

Term-local contraction scoping should remain: each term contracts only the axes it mentions. The
refactor must not replace this with one union of contracted axes across the whole sum.

There are two reasonable implementation boundaries:

1. make `evalAssignCore` internal and consume already checked `ScheduledProgram` data; or
2. keep it public for tests and direct use, but validate its raw maps at entry.

The current hybrid--public raw arguments plus assumptions established only by the compiler--is what
allows direct calls to produce valid-looking wrong tensors. E2 light typestate is therefore a natural
home for the checked wrappers, but 4a should at least add explicit `Except` checks now rather than wait
for a fully typed core IR.

JAX makes the checked form non-optional. A missing dimension cannot be left for tracing to discover:
it would either fail in Python or, worse, compile and cache a function specialized to an accidental
zero/one extent. `evalAssignCore` and the future plan compiler should consume the same
`CheckedAxisSizes`; only tensor contents should remain dynamic at backend invocation. Backend input
shape checks must compare actual arrays against the checked signature before device transfer.

**Acceptance tests:**

- empty seed gives the same shape, data, and error constructor as the unseeded wrapper;
- missing free, contracted, and seeded axis sizes each produce a distinct error;
- a negative or out-of-range seed coordinate is rejected;
- terms with disjoint contracted-axis sets preserve current per-term semantics; and
- sum, max, min, and predicate contraction agree between seeded and unseeded calls.

**Guarantee effect:** exhaustive use of one worker improves representation closure, but the size checks
are what establish boundary validity. Numerical parity tests are required for semantic closure.
These checks are also the precondition for JAX tracing; see
[Static shapes, tracing, and compilation caching](#static-shapes-tracing-and-compilation-caching).

#### 4b: model both identities, but do not overstate the algebra

Adding `unit1` is necessary. An empty factor list denotes the multiplicative identity of a term, while
an empty term list denotes the additive/aggregation identity of the expression. Those are different
values for the proposed min-plus interpretation:

```text
real sum-product:  unit1 = 1,   unit0 = 0
Boolean OR-AND:    unit1 = 1,   unit0 = 0
max-times:         unit1 = 1,   unit0 = -infinity
min-times:         unit1 = 1,   unit0 = +infinity
min-plus:          unit1 = 0,   unit0 = +infinity
```

For the immediate Lean evaluator, use one record at call sites:

```lean
structure Combine where
  mul     : Float -> Float -> Float
  combine : Float -> Float -> Float
  unit1   : Float
  unit0   : Float
```

This prevents callers from accidentally pairing `max` with zero or addition with negative infinity.
The product folds in both `Contract.lean` and `Scatter.lean` must start from `unit1`.

However, this function-valued record should not be the E4/backend representation. Lean functions are
not a closed serializable vocabulary and cannot be translated exhaustively to JAX. Define the semantic
description using operation tags and constants:

```lean
inductive ScalarBinOp
  | add | mul | min | max | logicalAnd | logicalOr

structure ContractionAlgebra where
  factorOp : ScalarBinOp
  factorId : ScalarConst
  reduceOp : ScalarBinOp
  reduceId : ScalarConst
```

`Combine` may be the reference evaluator's interpretation of `ContractionAlgebra`, or the evaluator can
match the tags directly. The important invariant is that `ScheduledProgram -> EvalPlan` produces
closed data that both Lean and JAX interpret. An arbitrary user-supplied function belongs outside the
initial JAX-capable fragment unless it has a separately registered, validated backend implementation.

The proposal needs one qualification: `evalScatter` contains two separate combinations:

1. multiplication within a product and aggregation of RHS terms; and
2. reduction of multiple source coordinates that collide at one output coordinate.

They need not use the same operation. `rhs.agg` controls the first; `ScatterOpts.reduce` controls the
second. Threading one `Combine` through scatter does not repair the current fact that scatter
hard-codes sum/product for the RHS and separately interprets a string collision policy. E3 should
model these as separate typed fields.

It would also be premature to expose a lawful Lean `Semiring` instance over `Float`. NaN, infinities,
and approximate equality complicate the advertised laws. The immediate type should describe
interpreter operations and identities; property tests can check the finite test domain used by the
evaluator. A later generic scalar backend can require the appropriate algebraic typeclasses over a
lawful scalar type.

**Acceptance tests:**

- zero-term and zero-factor expressions for every built-in `Combine`;
- all-negative max and all-positive min cases, preserving the current infinity identities;
- a synthetic min-plus case whose empty product must be `0`, proving that `1.0` is gone; and
- scatter tests that vary RHS aggregation and collision reduction independently.

**Guarantee effect:** `unit1` closes a semantic payload required by E3. It contributes to proof validity
only if later generic theorems state and use explicit algebraic laws; a record of Float functions alone
is not a semiring proof.
The corresponding backend choices are detailed in
[Contractions are not all `einsum`](#contractions-are-not-all-einsum).

#### 4c: one dtype-aware seeded assignment path

The proposal's predicate diagnosis is confirmed. `evalPlain` uses `evalAssignDtyped`, which calls
`combineFor decls name rhs.agg`; `evalStmtSliceSeeded` manually matches only the aggregation and cannot
observe whether the destination declaration is `.predicate`. Consequently, predicate states in scans
use real sum-product rather than Boolean OR-AND.

The shared operation should be assignment-specific, not a general `Stmt` function that accepts cases
it cannot execute:

```lean
def evalAssignDtypedSeeded
    (decls : DeclEnv)
    (env   : TensorEnv)
    (sizes : CheckedAxisSizes)
    (seed  : AxisCoord)
    (name  : String)
    (slots : List LHSSlot)
    (rhs   : ResolvedRHS) :
    Except EvalError (String × DenseTensor)
```

`evalPlain` passes an empty seed. Scan evaluation passes the step seed. Both therefore select
aggregation, dtype, and nonlinearity through the same function. `evalScan` must receive declarations
or, preferably, consume a resolved statement that already contains scalar semantics. Passing the
original `List Decl` is the smaller interim change; passing `DeclEnv` avoids repeated linear lookup.

The resolved statement and eventual plan must carry dtype explicitly. The JAX lowerer should not look
up declarations, inspect values, or infer that a numeric `0/1` tensor is a predicate. A first-class
`ScalarDType` can lower predicates to JAX `bool`, with explicit Iverson casts into numeric tensors.
This makes the plain/scan repair the local instance of a cross-backend rule: scalar semantics are plan
data, not evaluator context.

Scatter should not be forced through this function. It has different placement and collision
semantics and should share only the lower-level expression evaluator once those semantics are typed.
Likewise, `recurMorphism` must retain a named unsupported error until an evaluator exists.

**Acceptance tests:**

- the compiled predicate example above as both a plain assignment and a one-step scan state;
- real sum, max, and min parity across plain and scan placement;
- pointwise and axiswise nonlinearity parity after 4d;
- empty-seed equivalence with the plain wrapper; and
- a mutation test replacing `combineFor` in the scan path with `Combine.real`, which the predicate test
  must fail.

The existing scan-unrolling oracle is useful here, but its generated cases must include predicate
states and non-sum aggregators before it can guard this change. Its current success on real-valued
scan templates does not cover dtype dispatch.

**Guarantee effect:** this directly repairs semantic closure for predicate assignment inside scans.
Using one exhaustive dispatch also improves representation closure. It does not establish routed
semantic closure because dtype is still absent from `BrBaseP`.
Appendix A's [Predicate representation and dtype discipline](#predicate-representation-and-dtype-discipline)
explains why this metadata must be explicit before JAX lowering.

#### 4d: resolve nonlinearities before evaluation

Moving the duplicate match into `Nonlin.lean` is an improvement only if it changes the phase at which
failure occurs. An `Except`-returning `applyNonlin` that searches raw `LHSSlot`s during every evaluation
still leaves malformed syntax inside the scheduled evaluator.

The stronger design is the `ResolvedNonlin` boundary proposed in the Spike 3 assessment:

```lean
inductive ResolvedNonlin
  | identity
  | pointwise : PointwiseFn -> ResolvedNonlin
  | axiswise  : AxiswiseFn -> NormAxis -> Option BoolExpr -> ResolvedNonlin
```

`resolveNonlin` should check exactly one marked axis when an axiswise function requires one, reject a
marker for a pointwise function, and store a checked position or `Fin outputRank`. Then:

```lean
def applyNonlin : ResolvedNonlin -> DenseTensor -> Except EvalError DenseTensor
```

does not need raw slots or a dummy `axisPos` ignored by most constructors. It should still return
`Except`, because applying a checked axis to a tensor of an inconsistent runtime rank is an internal
invariant failure that must not become an out-of-range list default.

Keep `ResolvedNonlin` backend-neutral and serializable: store a closed function tag, static axis
position, compiled mask expression, and explicit all-masked/zero-denominator policy. Do not store a
Lean callback or JAX callable. JAX requires the reduction axis to be static at trace time, and its
library defaults do not by themselves specify LeanNCD's all-masked result. The plan compiler should
therefore translate `ResolvedNonlin` without rediscovering any semantic choice.

This ordering also avoids building a temporary `normMask?` classifier that Spike 3a immediately
replaces. Land Spike 3a's grouped constructors, then the resolver, then switch both plain and scan
evaluation through 4c.

**Acceptance tests:**

- missing, duplicate, and non-output norm markers are rejected by resolution;
- pointwise operations reject a norm marker if the language declares that combination invalid;
- every axiswise constructor preserves its mask and selected axis;
- plain and scan execution consume the same resolved value; and
- mutating the resolved position changes an asymmetric tensor result, so the test is sensitive to axis
  selection.

**Guarantee effect:** exhaustive classification is representation closure; constructing
`ResolvedNonlin.axiswise` only after checks is boundary validity; preserving the axis and mask through
execution is local semantic closure. Target/codec closure remains a separate Stage 6 obligation.
This resolved form supplies exactly the static axis and mask information required by
[Masked normalization and differentiation](#masked-normalization-and-differentiation).

#### 4e: split shape code around contracts, not historical line ranges

`Eval/Shape.lean` is still a mixed-responsibility module, although it is now 475 rather than the
proposal's 521 lines. It contains:

- constraint and exact-row-reduction internals;
- structured-but-private solver failures and diagnostics;
- diagnostic rendering and remediation text;
- inference from tensor reads and statements;
- scatter output-shape propagation;
- norm-axis lookup; and
- an `outputShape` helper that defaults missing sizes to zero.

The proposed three-file split is directionally right, but `Eval/Slots.lean` should not become a second
AST utility module. `LHSSlot.outExtent` already lives in `DSL/Ast.lean`, and Spike 2 centralizes slot
and read vocabulary there. Keep datatype-local total projections with the datatype.

A more stable split is:

```text
Eval/Size/Diagnostic.lean  -- SolveFailureKind, SolveDiagnostic, rendering
Eval/Size/Constraint.lean  -- SizeConstraint construction/canonicalization
Eval/Size/Solve.lean       -- exact solver
Eval/Size/Infer.lean       -- env/statement inference and warnings
Eval/Shape.lean            -- checked concrete tensor signatures
Eval/Plan/Validate.lean    -- semantic plan invariants
Backend/Jax/Validate.lean  -- JAX capability, not source validity
```

This supports 4h without a dependency cycle: the solver can return `SolveDiagnostic`; the evaluator
error layer can wrap it as `.shape`; rendering stays at the outer boundary. Diagnostics should become
non-private because they cross the module boundary, but helper row representations can remain private
to the solver.

The last three boundaries must remain distinct. Shape inference answers whether a source program has
concrete, consistent tensor signatures. Plan validation answers whether the operation payload is
semantically complete. JAX capability validation answers whether the current backend version supports
that valid plan. For example, a valid non-injective ordered-overwrite scatter may be unsupported by
the first JAX backend without being mislabeled as a malformed source program. Typed
`CapabilityError`s should reject such plans before Python tracing.

Do not preserve `outputShape`'s `(sizes[u]?).getD 0` merely because 4e is described as a file move.
Create a checked `Except`-returning shape query first or retain the old helper under an explicitly
unsafe/private name until 4a/4f migrate. Otherwise the split canonizes the same missing-size behavior
that 4a is intended to eliminate.

The exact diagnostic text tests should remain during the move, but they are compatibility tests, not
the primary correctness tests after 4h. Once errors are structured, test the constructor and fields,
plus a smaller set of rendering snapshots.

**Guarantee effect:** module splitting alone provides no semantic guarantee. Exported diagnostic ADTs
and checked shape APIs improve representation closure and boundary validity; solver correctness still
requires its existing examples and, ideally, independent solver properties.

#### 4f: decompose scans only after freezing the state-transition contract

The four phases in `evalScan` are real:

1. derive iteration lengths and allocate full state tensors;
2. evaluate/write base slices;
3. evaluate recurrence slices for every grid coordinate; and
4. return the state tensors.

The `work`/`stepEnv` ordering is semantically significant. Every recurrence statement at a given grid
coordinate must read the same pre-step snapshot, while writes accumulate into `work` for the next
coordinate. Replacing `stepEnv` with incrementally updated `work` would turn simultaneous coupled-state
updates into sequential ones.

The proposal should freeze more than this ordering before extraction:

- which base statements may read other state tensors;
- whether recurrence statements at one coordinate are simultaneous;
- the traversal order for multiple iteration axes;
- the meaning of zero-length iteration axes;
- whether every base/recur state name must have an allocated state tensor;
- how heterogeneous state shapes are rejected; and
- whether out-of-bounds slice writes are impossible by validation or are runtime errors.

Current defaults make a nominally behavior-neutral extraction risky:

- missing scan-axis sizes become length zero via `getD 0`;
- `outputShape` can insert zero for a missing state axis;
- missing state tensors fall back to `DenseTensor.zeros []`; and
- slice reads/writes use `get!`/`set!`, relying on upstream shape invariants.

These should not be copied into `allocStates` and `runRecurStep` as if they were intended semantics.
First add named errors and tests, then extract helpers whose types carry the checked scan shape and
state set.

E2 and E4 also affect the right abstraction. If E2 introduces a `Recurrence`/`CoreStmt.scan` carrying
validated state names and axes, `allocStates` should consume that type. If E4 introduces an
`EvalPlan`, `runRecurStep` should execute planned assignment bodies rather than recreating a second
interpreter API. Decide those scopes before investing in a public helper decomposition.

The JAX destination makes that decision more concrete. A plan-level scan should record:

- the fixed shape and dtype of each state leaf;
- one immutable pre-step state consumed by all coupled updates;
- base-state construction and complete output-history layout;
- static iteration lengths and exact cartesian order; and
- predecessor/boundary rules already certified by validation.

A one-axis instance can lower to
[`jax.lax.scan`](https://docs.jax.dev/en/latest/_autosummary/jax.lax.scan.html) with the coupled states
as a pytree carry. A general multi-axis instance can first lower to one flattened lexicographic scan
over fixed-shape full state tensors. This is another reason not to extract the public abstraction
around the current mutable `HashMap`: the reusable contract is the pure state transition, not its
present storage mechanism.

**Acceptance tests:**

- coupled states whose simultaneous and sequential updates differ;
- two-axis traversal with asymmetric dimensions;
- missing and zero-length scan-axis policies;
- missing/mismatched base and recurrence states;
- base and recurrence slice shape mismatch;
- predicate and max/min states after 4c; and
- differential agreement with the independent scan-unrolling oracle.

**Guarantee effect:** decomposition improves representation closure only if each scan phase has an
explicit typed input/output. Semantic closure comes from state-transition and unrolling agreement
tests, not from reducing function length. Fail-loud allocation and slice checks establish boundary
validity.
The proposed `lax.scan` and multi-axis strategies are evaluated in
[Coupled and multi-axis scans](#coupled-and-multi-axis-scans).

#### 4g: type scatter policy at both boundaries

The current `Option String` is unsafe: any value other than `"sum"` or `"max"` reaches the overwrite
arm. Replacing it with an enum is necessary, but the proposed
`ReduceOp | sum | max | overwrite` leaves two questions implicit:

1. Is `none` semantically overwrite, or does `none` mean "collisions statically forbidden"?
2. Is this operation the RHS contraction aggregator or only the output-collision reducer?

Use a name such as `CollisionReduce` and choose the first policy explicitly:

```lean
inductive CollisionReduce
  | rejectCollisions
  | overwrite
  | sum
  | max
```

If structural validation proves a scatter map injective, `rejectCollisions` is appropriate and an
actual collision indicates an invariant failure. If overwrite is intentionally user-visible, retain it
as a distinct constructor. Do not let absence silently select it.

The parser/elaborator should produce this enum directly. External codecs should decode it partially,
and `BrBaseP` needs to preserve it before routed scatter is claimed supported. `rhs.agg` must remain a
separate typed `AggOp`; the scatter evaluator should use the 4b operations for RHS expression
evaluation and `CollisionReduce` only when writing an occupied output coordinate.

JAX turns collision policy into an explicit backend capability:

- injective set may lower to `.at[idx].set` only after validation proves uniqueness;
- sum and max may lower to associative scatter/segment reductions;
- out-of-range writes may use drop semantics only because the plan says so; and
- non-injective ordered overwrite should be rejected initially because JAX documents conflicting
  update order as implementation-defined and potentially nondeterministic.

If ordered overwrite remains part of LeanNCD, implement it later by selecting the maximal canonical
source-order rank per destination, not by assuming `.at.set` is stable. The plan should carry the
injectivity result so a backend cannot assert `unique_indices=True` without evidence.

The proposal also omits the existing nonlinear-scatter issue. A typed reduction enum does not decide
whether `rhs.nonlin` occurs before or after collision reduction. Until that order is specified, checked
scatter construction should reject non-identity nonlinearities.

**Acceptance tests:**

- every collision constructor on a deliberately colliding map;
- unknown textual and serialized reduction tags fail at their boundary;
- `rejectCollisions` reports the output coordinate and conflicting source coordinates;
- RHS `max` with collision `sum` differs from RHS `sum` with collision `max`;
- injective scatter is independent of collision policy; and
- nonlinear scatter is rejected until its ordering is defined.

**Guarantee effect:** the enum and exhaustive evaluator match provide representation closure. Partial
decoding provides boundary validity. Preserving independent RHS and collision policies through route,
codec, and evaluation is required for semantic closure.
This is a backend blocker, not merely an AST cleanup; see
[Scatter collisions, ordering, and determinism](#scatter-collisions-ordering-and-determinism).

#### 4h: structure errors and warnings by phase

Replacing `EvalError := String` is high value, but the proposed constructor list is still too porous.
In particular, `unsupported String` recreates stringly typed dispatch inside the error ADT, and
`domainError (UnaryOp, Float)` omits the factor/tensor/coordinate context needed to locate a failure.

Prefer layered causes:

```lean
inductive PlanError
  | incompleteOperationPayload ...
  | invalidStateTransition ...
  | inconsistentTensorSignature ...

inductive CapabilityError
  | unsupportedOperation ...
  | dynamicShapeRequired ...
  | nondeterministicCollisionPolicy ...

inductive BackendError
  | protocol ...
  | traceFailure ...
  | compileFailure ...
  | deviceFailure ...
  | executionFailure ...

inductive ShapeError
  | unsizedAxis ...
  | sizeConflict ...
  | solveFailure (diagnostic : SolveDiagnostic)
  | invalidOutputShape ...

inductive EvalError
  | compile (cause : CompileError)
  | shape (cause : ShapeError)
  | plan (cause : PlanError)
  | capability (backend : BackendKind) (cause : CapabilityError)
  | backend (backend : BackendKind) (cause : BackendError)
  | unknownTensor (name : String)
  | invalidSeed ...
  | invalidTensor ...
  | unaryDomain (op : UnaryOp) (value : Float) (context : EvalContext)
  | invalidNormAxis ...
  | scatterCollision ...
  | unsupportedRecurMorphism ...
  | internalInvariant ...

inductive EvalWarning
  | paddedAccess ...
  | underconstrainedButResolved ...
```

The exact constructors can remain modest, but each unsupported language form should have a closed
case rather than an arbitrary string. `CompileError` should be nested, not flattened by
`s!"compile failed: {repr e}"`. Shape diagnostics should remain structured until the CLI/editor
boundary. Include statement/tensor/axis context where users can act on it.

These layers prevent backend limitations from contaminating source semantics. A valid plan rejected
because the first JAX backend lacks ordered overwrite produces `CapabilityError`, not `ShapeError`.
A JAX `ConcretizationTypeError` after capability validation is normally `BackendError.traceFailure`
and evidence of a lowering defect, because dynamic-shape requirements should already have been
detected. Retain the plan hash and failing step in backend errors without exposing arbitrary Python
objects.

Warnings must migrate with errors. Otherwise 4i merely returns `List String`, preserving the same
substring coupling in a second channel. A structured `EvalWarning` also lets callers filter or elevate
specific warnings without parsing prose.

Migration should occur in three passes:

1. define the ADTs and rendering with compatibility snapshots;
2. convert throw sites and make tests match constructors/fields; and
3. improve wording independently after structural assertions no longer depend on it.

Byte-identical output is useful during the first pass but should not be a permanent requirement for
every diagnostic. Keep snapshots for a few complete user-facing messages and field-level tests for the
rest.

**Guarantee effect:** structured failure is part of boundary validity because malformed states cannot
be mistaken for unrelated strings or successful values. Exhaustive rendering improves representation
closure. It does not prove evaluator semantics, and changing error representation has no bearing on
categorical proof validity.

#### 4i: separate entry, worker, and diagnostic result

Moving `TLProgram.eval` out of `Eval/Eval.lean` is a clean dependency improvement. The resulting layers
should be:

```text
DSL compile                         -- TLProgram -> ScheduledProgram
Eval scheduled worker               -- ScheduledProgram -> EvalReport
Eval entry wrapper                  -- compile, evaluate, preserve typed causes
UI/CLI rendering                    -- errors and warnings -> text
```

The report should make warnings first-class:

```lean
structure EvalReport where
  env      : TensorEnv
  warnings : List EvalWarning
  backend  : BackendInfo
  timing   : Option EvalTiming
```

`evalScheduled` should return `Except EvalFailure EvalReport`, with warnings carried on both
outcomes. A detailed entry point can compile and evaluate without flattening `CompileError`. Do not
retain an output-only compatibility entry: callers can inspect `EvalReport.env` after handling the
complete outcome, without creating a second API that silently discards warnings. Likewise, do not
retain `dbg_trace`.

`BackendInfo` should identify the reference/JAX/PyTorch worker, backend and device versions, numeric
profile, canonical plan hash, and compilation-cache hit. Timings should separate plan compilation,
backend compilation, transfer, and execution where available. This data is required to reproduce
float32/float64 differences and to distinguish JAX compile latency from steady-state evaluation.

The worker boundary should be backend-neutral:

```text
ScheduledProgram -> EvalPlan -> EvalBackend.eval -> EvalReport
```

The first JAX implementation may use the auditable one-shot generated-script pattern demonstrated by
`lean4-mlir/jax`; a later persistent Python worker can cache jitted functions by plan hash. Neither
transport should force `TLProgram.eval` to parse human-readable stdout or flatten JAX exceptions into
ordinary evaluator strings.

This split is also the correct boundary for E4. `EvalPlan` compilation belongs between scheduled input
and the worker; `TLProgram.eval` should not know whether the worker interprets statements directly or
executes a plan. It is not, however, evidence that E4 is correct. Differential tests must compare both
workers.

**Acceptance tests:**

- compile errors remain inspectable as `EvalFailure.error = EvalError.compile cause`;
- shape warnings are returned exactly once and no `dbg_trace` is required;
- importing the scheduled worker does not import `DSL.Compile`; and
- entry and worker produce identical complete outcomes on an already compiled schedule;
- JAX capability rejection occurs before process launch; and
- JAX reports preserve plan hash, device/profile, cache hit, and separated compile/execute timings.

**Guarantee effect:** preserving typed causes and warnings strengthens boundary validity. The explicit
worker interface gives E4 a stable semantic comparison point. Import decoupling alone does not improve
any of the four guarantees.
The worker/process alternatives and result protocol are specified in
[Lean-to-Python execution boundary](#lean-to-python-execution-boundary).

#### Revised Spike 4 sequencing

The current `4a -> 4b -> 4c -> 4d -> 4e...` order is too linear. Use dependency waves:

1. **Freeze failures and policies.**
   - Land the three compiled regressions above.
   - Add missing contracted-size, invalid seed, predicate-scan, unknown scatter reduction, coupled
     simultaneous-state, and warning-return tests.
   - Decide zero-length scan and overwrite-versus-reject collision semantics.
2. **Build the shared contraction foundation (4b, then 4a).**
   - Add both identities, define closed `ContractionAlgebra` tags, and interpret them through one
     reference `Combine`.
   - Unify seeded/unseeded evaluation while rejecting every missing axis size and invalid seed.
   - Keep wrappers temporarily so callers migrate in reviewable steps.
3. **Land Spike 3a and the light resolved boundary, then 4d and 4c.**
   - Group nonlinearity constructors.
   - Construct `ResolvedNonlin` and checked shapes once.
   - Route plain and scan assignments through one dtype-aware seeded worker.
4. **Prototype the backend-neutral E4 boundary.**
   - Define a minimal canonical `EvalPlan` with concrete tensor signatures, closed contraction
     operations, plan validation, and typed capability rejection.
   - Run scan-free real sum-product plans through both `DenseTensor` and a generated JAX function.
   - Keep JAX outside the AST evaluator; this milestone tests the boundary created by 4a-4d.
5. **Type scatter policy (4g) with E3/Stage 6 design.**
   - Separate RHS aggregation from collision reduction.
   - Reject unsupported nonlinear scatter.
   - Carry injectivity and collision policy into `EvalPlan`; the initial JAX capability admits only
     injective set, sum, and max.
   - Carry policy into the routed target only when routed scatter support is added.
6. **Stabilize diagnostics and module ownership (4e and 4h).**
   - Move solver diagnostics to a stable module.
   - Introduce structured shape, plan, capability, backend, evaluator errors, and warnings.
   - Split solver/inference code without preserving unsafe defaults as public APIs.
7. **Extract the entry wrapper and return reports (4i).**
   - The import move can happen earlier if useful.
   - Warning-return work should use the structured types from wave 6.
   - Reports include plan hash, backend/device/profile, cache behavior, and separated timings.
8. **Use the established E4 boundary before 4f.**
   - Define the plan-level pure state transition before extracting scan phases.
   - If E2 recurrence lands first, make helpers consume the checked recurrence type.
   - Lower one-axis coupled scans to `lax.scan`, then add a flattened multi-axis semantic lowering.
   - Keep private evaluator helpers only where they implement the same plan-level contract.

The dependency summary is:

```text
4b -> 4a -> 4c
Spike 3a -> resolved Nonlin (4d) -> 4c
4b + 4a + 4c + 4d -> minimal EvalPlan -> JAX stateless oracle
4b -> E3
4g -> EvalPlan scatter capability -> routed scatter payload work
4e diagnostic split -> 4h -> warning half of 4i
minimal EvalPlan + E2 recurrence decision -> 4f -> JAX scan lowering
4c + 4f -> scan evaluator ready for broader E5 agreement
```

#### Spike 4 completion gates by guarantee

**Representation closure**

1. One assignment worker handles empty and non-empty seeds.
2. `ContractionAlgebra`, `ScalarDType`, `CollisionReduce`, `ResolvedNonlin`, plan steps, errors, and
   warnings are closed data matched exhaustively without semantic wildcard arms.
3. Plain and scan dispatch do not maintain independent dtype/aggregation/nonlinearity matches.
4. Shape diagnostics have one structured representation and one outer renderer.
5. `EvalPlan` is canonical, versioned, serializable, and contains no Lean or backend callbacks.

**Semantic closure for scheduled evaluation**

6. Seeded and unseeded assignment agree when the seed is empty.
7. Plain and scan assignment agree for real/predicate dtype, sum/max/min aggregation, and every
   supported nonlinearity.
8. Both term and expression identities come from the contraction algebra; no evaluator product fold
   starts at a literal `1.0`.
9. Scatter RHS aggregation and collision reduction vary independently and are preserved.
10. Coupled scan updates agree with the independent unrolling oracle.
11. Unsupported nonlinear scatter and `recurMorphism` remain named rejections.
12. For the declared initial JAX fragment, the plan interpreter and jitted JAX lowering agree with
    `DenseTensor` on shapes, dtypes, and values within the numeric profile's tolerance.

These claims cover scheduled evaluation and the explicitly declared initial `EvalPlan`/JAX fragment.
Routed semantic closure still requires Stage 6/7 payload and agreement work.

**Boundary validity**

13. Missing free, contracted, scan, or seeded axis sizes cannot produce a tensor.
14. Invalid seeds, tensor shapes, slice shapes, norm axes, and scatter collisions return structured
    errors.
15. Unknown reduction spellings/tags fail at parse/decode boundaries.
16. Shape warnings are returned as data, not emitted through `dbg_trace`.
17. Output-shape and scan-allocation code contains no meaning-changing `getD 0` fallback for required
    values.
18. Valid but unsupported plans return `CapabilityError` before Python/JAX execution.
19. Backend input tensors are checked against plan signatures before transfer; tracing failures are
    reported as backend defects, not source errors.

**Proof validity**

20. Spike 4 makes no new categorical theorem claim.
21. If algebraic laws are added for generic contraction, they are stated over a lawful scalar
    abstraction, not asserted for raw Float behavior with NaN/infinity.
22. Any checked wrapper theorem states exactly what its constructor validated--for example, size
    coverage and seed bounds--and its axiom report contains no `sorryAx`.
23. Property and differential tests are described as executable evidence, not as proofs of categorical
    agreement.

With these gates, Spike 4 becomes more than deduplication: it establishes one honest scheduled
interpreter boundary and the first checked backend boundary. It still does not make the routed target
semantically complete, validate external ACSet data, or repair the categorical interfaces identified
earlier.

### Operational guarantees

The restructuring should be evaluated by explicit guarantees, not by the number of completed spikes.
This section defines how each guarantee is enforced and when the project may accurately claim it.

The schedule should be judged against the four properties named earlier:

1. **Representation closure:** every constructor in a declared closed datatype is handled by every
   operation that interprets or transforms that datatype.
2. **Semantic closure:** for each capability, every accepted source operation either reaches a target
   representation carrying all of its meaning or is rejected before a success-shaped target is
   produced.
3. **Boundary validity:** untrusted or list-based presentations become internal values only through
   validation; malformed data cannot acquire semantics through defaults.
4. **Proof validity:** exported theorems are kernel-checked consequences of their advertised
   assumptions, with no hidden admission, and the assumptions express the property the theorem needs.

Two auxiliary notions make semantic closure testable:

- **capability closure:** `eval`, routed compilation, serialization, and realization each have an
  explicit supported fragment and reject everything else; and
- **agreement:** on the intersection of those fragments, scheduled and routed interpretations
  produce equivalent results.

#### How the four buckets differ

The buckets ask different questions about the same compiler path:

```text
surface syntax
  -> source AST
  -> resolved/validated AST
  -> scheduled IR
  -> routed target IR
  -> encoded external form
  -> decoded checked target
  -> evaluator / categorical realization
```

| Bucket | Question answered | Quantifies over | Typical failure |
|---|---|---|---|
| **Representation closure** | Have all possible forms of this datatype been structurally accounted for? | constructors × consumers/transforms | a new constructor falls through `_`, loses a mask during traversal, or is never handled by lowering |
| **Semantic closure** | Does every form accepted by this capability retain and receive its intended meaning? | accepted programs × semantic capabilities | lowering keeps `.softmax` but drops its mask; `log(X)` becomes indistinguishable from `X` |
| **Boundary validity** | Can only values satisfying the next phase's assumptions cross into that phase? | raw inputs × boundary invariants | an unknown op tag becomes `.contract`; a missing wire becomes `.external 0`; an absent norm axis is discovered during evaluation |
| **Proof validity** | Are formal claims both derivable and stated over adequate assumptions? | theorem statements × assumptions × axiom closure | `weave_unique` is admitted or proved only after hiding the needed cartesian-lift hypothesis |

A useful shorthand is:

```text
representation closure = every case is accounted for
semantic closure       = every accepted case keeps its meaning
boundary validity      = every admitted value satisfies the next phase
proof validity         = every exported claim is justified by its stated assumptions
```

The buckets are related but not interchangeable:

- An exhaustive match gives **representation closure**, but an arm can still return the wrong result,
  so it does not imply semantic closure.
- A numerically correct evaluator can give **semantic closure** for well-formed values, while a decoder
  can still manufacture malformed values, so it does not imply boundary validity.
- A validator can guarantee **boundary validity**, while the checked target still lacks a field for a
  source mask, so it does not imply semantic closure.
- Tests can provide strong evidence for all three executable buckets, but only a kernel-checked proof
  over adequate assumptions gives **proof validity** for a theorem.
- Conversely, a theorem about matrix dimensions or route shape can be fully valid while saying
  nothing about whether masked softmax computes the same values before and after lowering.

Each claim must therefore name its scope. Avoid statements such as "the compiler is closed" or "the
bridge is valid." Prefer:

```text
Nonlin traversal is representation-closed over the current Nonlin constructors.

Routed evaluation is semantically closed for scan-free real sum contractions and
isolated pointwise activations.

ACSet decoding is boundary-valid for CheckedThreadedComposed.

weave_cartesian_unique is proof-valid relative to the explicit cleavage and
vertical-isomorphism assumptions listed in its signature.
```

The scope has two dimensions:

1. **domain:** which datatype, source fragment, external format, or theorem family is covered; and
2. **consumer:** which traversal, evaluator, router, codec, realizer, or proof uses the guarantee.

For example, `Nonlin` may be representation-closed for `traverseAxes` but not for serialization if
serialization has a separate wildcard match. Likewise, a `TLProgram` may be semantically supported by
`evalScheduled` but not by `route`. Closure is not a global property inherited automatically by every
consumer.

#### One operation through all four buckets

Suppose a future operation is added:

```lean
AxiswiseFn.maskedLogSoftmax
```

with a mask and a selected normalization axis. The four buckets impose separate obligations:

1. **Representation closure**
   - `AxiswiseFn.toBrOp`, evaluator dispatch, syntax classification, `Nonlin.traverseAxes`, reference
     traversals, pretty-printing, and tag tables all need explicit cases.
   - If one is missing, Lean should reject the build or an independent constructor-coverage test should
     fail.
   - Passing this bucket means every relevant function knows the constructor exists. It does **not**
     mean any implementation is mathematically correct.

2. **Semantic closure**
   - Lowering must preserve `maskedLogSoftmax`, its mask, and its resolved axis.
   - Routed evaluation must compute log-softmax rather than ordinary softmax.
   - Encoding/decoding must distinguish it from `.softmax` and preserve its payload.
   - Scheduled and routed evaluation must agree on examples where changing the mask or axis changes the
     result.
   - If the target cannot yet express it, `resolveForRoute` must reject it. Accepting it as `.softmax`
     would violate semantic closure even though representation closure passed.

3. **Boundary validity**
   - Source elaboration rejects a pointwise use or malformed mask syntax.
   - Resolution rejects a missing or invalid norm axis.
   - Decoding rejects a missing mask payload, unknown tag, invalid axis position, or malformed
     reindexing.
   - The evaluator receives a checked operation and does not recover missing information with
     `getD`, axis `0`, or an empty mask.
   - These checks ensure the semantic implementation runs only on values satisfying its preconditions.

4. **Proof validity**
   - Local codec theorems prove the new tag/payload round-trip without admissions.
   - Any route theorem includes the new constructor and proves its stated structural invariant.
   - Any mathematical theorem about log-softmax states the needed domain, axis, and mask assumptions.
   - CI verifies the relevant declarations' transitive axiom closure.
   - Passing numerical tests is useful evidence but does not, by itself, turn the semantic claim into a
     theorem.

This example shows the intended progression:

```text
the case exists everywhere
  -> its complete meaning survives
  -> only well-formed instances can reach consumers
  -> formal claims about it are justified
```

That progression is not an implication chain: each arrow requires additional design and evidence.

The plan does not make all four properties true immediately. It installs a concrete enforcement
mechanism and an exit gate for each:

| Property | Enforcing mechanism | Required evidence | First stage that can claim it |
|---|---|---|---|
| Representation closure for `Nonlin` | closed enums, centralized total functions, no wildcard semantic matches | compiler exhaustiveness + independent traversal references | Stage 1 |
| Representation closure for the routed source fragment | exhaustive capability validator over `Stmt`/`Factor`/`Nonlin`/`AggOp` | every constructor reaches `preserve` or `reject` in tests | Stage 3 |
| Semantic closure for one routed operation class | typed target payload + exhaustive target evaluator + codec preservation | lowering/codec tests and E5 numerical agreement | Stages 6-7 |
| Source/phase boundary validity | syntax separation, `ResolvedNonlin`, capability-specific checked wrappers | negative source tests and direct-constructor tests | Stages 2-4 |
| External target boundary validity | `Raw* -> Except Error Checked*`; consumers accept only `Checked*` | malformed-input tests and valid round trips | Stage 5 |
| Local proof validity for Spike 3 | independent traversal/fusion and codec theorems; no new admissions | full build plus axiom check for changed declarations | Stages 1-2 |
| Categorical proof validity | corrected interfaces, removal of false theorems, generated axiom-closure manifest | countermodels/model tests + axiom closure + kernel-checked proof | parallel proof track |

#### How representation closure is enforced

**Meaning.** Representation closure is a structural completeness property. Given a closed datatype
`T` and a declared set of operations over it, every operation has defined behavior for every
constructor of `T`, including semantic data nested inside that constructor.

Formally, if `Constructors(T)` is the set of constructors and `Consumers(T)` is the set of functions
that inspect or transform `T`, the review obligation is the matrix:

```text
for every f in Consumers(T):
  for every c in Constructors(T):
    f has an explicit, appropriate case for c
```

For `Nonlin`, consumers include more than evaluators. They include traversal, UID remapping,
collection, splitting, lowering, syntax elaboration, target classification, serialization, display,
and independent reference tests. Closure is lost if any one of these consumers silently omits a
constructor or one of its fields.

There are three useful levels:

1. **Constructor closure:** every top-level constructor is handled.
2. **Payload closure:** every semantically relevant field inside the constructor is traversed or
   preserved. A `.axiswise fn mask` arm that returns `.axiswise fn none` is constructor-complete but
   not payload-complete.
3. **Consumer closure:** every relevant operation over the datatype uses the centralized total
   functions or has its own exhaustive match.

This bucket does **not** ask whether the selected behavior is mathematically right. Both of these are
representation-closed:

```lean
| .sigmoid => sigmoidT t
| .sigmoid => reluT t       -- exhaustive but semantically wrong
```

It also does not mean the datatype is extensible without work. The point of a closed enum is the
opposite: adding a constructor deliberately creates compile-time obligations at every exhaustive
consumer.

For a closed inductive, Lean's exhaustiveness checker is useful only if semantic matches do not use
catch-all arms. The plan therefore needs a repository rule: **no `_` arm in a function whose purpose
is to classify, lower, serialize, or evaluate a closed semantic enum.** Wildcards remain reasonable
for genuinely irrelevant structure, but not for `Nonlin`, `PointwiseFn`, `AxiswiseFn`, `UnaryOp`,
`AggOp`, `Stmt`, `Factor`, `BrOp`, or `Wire`.

Spike 3 concretely replaces distributed classification such as:

```lean
match rhs.nonlin with
| .relu | .sigmoid | .tanh | .gelu | .leakyrelu => ...
| _, some axis => ...
| _, none => ...
```

with total operations at the datatype boundary:

```lean
def PointwiseFn.toBrOp : PointwiseFn -> BrOp
  | .relu      => .relu
  | .sigmoid   => .sigmoid
  | .tanh      => .tanh
  | .gelu      => .gelu
  | .leakyrelu => .leakyrelu

def AxiswiseFn.toBrOp : AxiswiseFn -> BrOp
  | .softmax    => .softmax
  | .normalize  => .normalize
  | .l2normalize => .l2normalize

def Nonlin.traverseAxes ... : Nonlin -> f Nonlin
  | .identity => ...
  | .pointwise fn => ...
  | .axiswise fn mask => ...
```

Adding `.elu` to `PointwiseFn` then produces compile errors in `toBrOp`, pointwise evaluation,
serialization tests, and the independent reference match until each obligation is supplied. It cannot
silently fall through an axiswise/default arm.

Central helpers alone are insufficient if some consumer bypasses them. Stage 3 therefore adds an
exhaustive capability validator at the source-to-routed boundary. Its shape should be closer to:

```lean
def lowerRoutedStmt : ResolvedStmt -> Except CompileError RoutedStmt
  | .contract out agg terms => lowerContract out agg terms
  | .nonlin out fn input    => lowerNonlin out fn input
  | .scatter out map rhs policy =>
      throw (.unsupportedForRoute "scatter")
  | .recurrence ... =>
      throw (.unsupportedForRoute "recurrence")
  | .recurMorphism ... =>
      throw (.unsupportedForRoute "recurMorphism")
```

and `lowerContract` must in turn match every `Factor`, `UnaryOp`, and `AggOp` without a semantic
wildcard. This function is an executable support matrix: every source constructor ends in either a
typed routed value or a named rejection. The Markdown payload table documents the result but is not
the enforcement mechanism.

The verification should include one test per constructor family that exercises both branches:

- every currently supported constructor lowers to the expected typed target operation;
- every unsupported constructor returns its named `CompileError`; and
- adding a constructor makes at least the exhaustive production match and an independent test
  reference fail to compile.

The last check is already approximated well by `TraverseAxesEquiv.lean` and
`TraverseAxesSpike.lean`; preserve that independent-match pattern for target classification rather
than testing `fn.toBrOp` by comparing it to itself.

**Scope qualification:** Stage 1 establishes representation closure for the `Nonlin` family, not for
the whole compiler. The broader claim is earned only after Stage 3 audits and exhaustively validates
all constructor families that can reach routed lowering.

#### How semantic closure is enforced

**Meaning.** Semantic closure is a meaning-preservation property for a named capability. It says that
every operation the capability accepts has a complete denotation in that capability, and every
translation on the way to that denotation preserves all distinctions that can affect observable
results.

For a lowering `L : Source -> Target`, source interpretation `evalS`, and target interpretation
`evalT`, the intended condition on the supported fragment is:

```text
evalT (L p) inputs ~= evalS p inputs
```

where `~=` states the chosen observable equivalence: same output names and shapes, equal discrete
values, and floating-point values within an explicit tolerance. If categorical realization is in
scope, its denotation must join the same commuting diagram.

Semantic closure has four parts:

1. **Operation coverage:** every accepted operation has an interpretation.
2. **Payload preservation:** every field that can change meaning--mask, axis, aggregator, unary
   function, scatter policy, dtype, recurrence body--survives every translation.
3. **Compositionality:** multi-step routing and composition mean the composition of the individual
   operations, not merely the right per-step labels.
4. **Observable agreement:** an independent oracle confirms that the translated program computes the
   same result.

This is stronger than "there is a `BrOp` constructor with the same name." A tag establishes only
classification. A semantically closed axiswise operation must retain the selected function, mask,
norm axis, scalar semantics, and input/output routing needed to evaluate it.

There are two legitimate notions of completion:

- **closed supported fragment:** the backend explicitly defines a smaller input language and rejects
  everything outside it; and
- **full source closure:** every public source operation is represented and interpreted.

The first is the recommended incremental state. Named rejection prevents false success, but it should
not be described as full source-language semantic closure. The supported fragment must be explicit in
types, validators, tests, and documentation.

Semantic closure must be relative to a capability. The source language may legitimately support
scheduled evaluation of a construct that the routed or categorical backend cannot yet represent. The
required invariant is:

```text
for every source operation x and capability c:
  validate_c(x) = accepted
    implies every semantic field of x is represented and interpreted by c
  otherwise validate_c(x) returns a named error before c produces output
```

This avoids two bad interpretations of "closure":

- requiring every backend to support every source feature immediately; or
- allowing a backend to claim support after retaining only the operation's name while dropping its
  parameters.

The concrete API boundary should express the distinction:

```lean
def resolveForEval  : TLProgram -> Except CompileError EvaluableProgram
def resolveForRoute : TLProgram -> Except CompileError RoutableProgram
def route           : RoutableProgram -> Except CompileError CheckedThreadedComposed

def evalScheduled : EvaluableProgram -> Inputs -> Except EvalError Outputs
def evalThreaded  : CheckedThreadedComposed -> Inputs -> Except EvalError Outputs
```

`EvaluableProgram` and `RoutableProgram` need not initially be deeply dependent types. They can be
opaque/checked wrappers constructed only by their validators. The important fact is that `route`
cannot be called on an arbitrary `TLProgram`, and `evalThreaded` cannot be called on an unchecked
presentation.

For each operation class, semantic closure requires a typed target payload. A concrete direction is:

```lean
inductive RoutedOp
  | contract  : AggOp -> RoutedOp
  | pointwise : PointwiseFn -> RoutedOp
  | axiswise  : AxiswiseFn -> ResolvedNormAxis -> CompiledMask -> RoutedOp
  | scatter   : ScatterPolicy -> RoutedOp
  | scan      : CheckedRecurrence -> RoutedOp

structure BrBaseP where
  op           : RoutedOp
  degree       : StObjP
  inputWeaves  : List WeaveShapeP
  outputWeaves : List WeaveShapeP
  reindexings  : List StMatP
```

This is illustrative rather than a required final encoding, but it demonstrates the invariant:
`RoutedOp.axiswise` cannot exist without its resolved axis and mask, and `RoutedOp.scatter` cannot
exist without its fill/reduction policy. By contrast, the current flat `BrOp.softmax` and
`BrOp.scatter` carry none of those payloads.

An operation class is not marked supported until all four preservation points exist:

1. source-to-target lowering stores every semantic field;
2. target evaluation consumes those fields;
3. codec encode/decode preserves them; and
4. realization either interprets them or explicitly rejects that target operation.

The following concrete tests establish that these fields are load-bearing rather than decorative:

- two masked softmax programs differing only in mask lower to unequal target values and evaluate
  differently;
- two scatters differing only in fill or reduction policy survive codec round trip distinctly;
- `log(X[i])` and `X[i]` do not lower to the same routed program;
- predicate and real-valued outputs retain different scalar/dtype tags; and
- mutating a preserved payload causes the E5 agreement test to fail.

Until those tests pass, the routed validator rejects the corresponding feature. This is how the plan
prevents an incomplete target from silently approximating the source.

Finally, Stage 7 supplies an independent semantic oracle:

```text
evalScheduled (resolveForEval p) inputs
  ~= evalThreaded (route (resolveForRoute p)) inputs
  ~= evalThreaded (decode (encode (route (resolveForRoute p)))) inputs
```

Agreement is checked only when `p` belongs to the declared intersection of supported fragments. This
does not prove categorical correctness, but it catches payload erasure and misrouting that shape
theorems cannot detect.

**Scope qualification:** semantic closure is incremental. After the initial Stage 7, the correct
claim is "the routed backend is semantically closed for scan-free real sum contractions and isolated
pointwise operations," not "LeanNCD is semantically closed." Each later operation class expands that
sentence only after passing the same gate.

If the desired end state is the literal global claim "every source operation is interpretable in the
target IR," then named rejection is only an intermediate safety property, not completion. Full
semantic closure is reached when the Stage 3 audit has no `reject/repair` rows for the public routed
language and every row passes the Stage 6-7 payload/codec/agreement gate. An alternative honest end
state is to define a smaller `RoutableProgram` language explicitly and document that it is a strict
subset of `TLProgram`; in that case closure is global for `RoutableProgram`, not for all source syntax.

#### How boundary validity is enforced

**Meaning.** Boundary validity is a precondition-establishment property. A boundary is any transition
where the next phase assumes facts that the previous representation does not enforce. The boundary is
valid when it checks those facts exactly once, reports failure explicitly, and produces a type that
downstream code can trust.

Relevant boundaries are not limited to external files:

1. **Surface boundary:** syntax to AST--keywords, mask placement, and source-level well-formedness.
2. **Phase boundary:** unresolved AST to evaluator/routed AST--norm-axis membership, legal statement
   combinations, supported capability fragment.
3. **Runtime boundary:** inputs to execution--tensor ranks/shapes, inferred scan-axis sizes, predicate
   and scalar compatibility.
4. **Serialization boundary:** internal target to CSV/ACSet--encodable sizes and complete operation
   payloads.
5. **Import boundary:** CSV/ACSet to internal target--known tags, valid references, matrix dimensions,
   routing arities, and payload presence.
6. **Proof/execution bridge:** computable presentation to dependent categorical object--all invariants
   needed to construct the latter.

Validation itself has four dimensions:

- **structural validity:** lengths, ranks, and required fields match;
- **referential validity:** names, wires, UIDs, slots, and axes refer to existing objects;
- **capability validity:** the selected consumer actually supports the operation;
- **dynamic validity:** input-dependent facts such as inferred axis sizes hold for this execution.

A boundary is not valid merely because a `validate` function exists. Three API properties are needed:

```text
raw values cannot be passed directly to checked consumers
successful validation returns a distinct checked type
failed validation cannot emit a partial or default-filled success value
```

Boundary validity does not require eliminating every default. It distinguishes **domain defaults**
from **recovery defaults**. A declared scatter fill of zero is semantic input. Replacing a missing
wire with `.external 0` or an unknown operation with `.contract` invents meaning and is invalid.

Boundary validity requires more than calling `validate` by convention. The types must prevent
unchecked data from reaching semantic consumers:

```lean
structure CheckedStMatP where
  raw : StMatP
  wellFormed : raw.wellFormed

structure CheckedThreadedComposed where
  raw : ThreadedComposed
  valid : raw.Valid

def checkStMat :
    StMatP -> Except BridgeError CheckedStMatP

def decodeSBr :
    RawSBr -> Except BridgeError CheckedThreadedComposed

def realize :
    CheckedThreadedComposed -> ...
```

The constructors for checked wrappers should not be part of the ordinary public API; callers obtain
them through smart constructors/validators. If proof-carrying wrappers are too expensive at a
particular executable boundary, use an opaque checked structure whose fields are built only in the
validation module. What must not remain is a type alias that lets arbitrary raw lists masquerade as
validated data.

Validation is structural and path-aware. For example, decoding step `i`, input `j` checks:

- operation tag is known;
- output/input/degree weave counts match their rows;
- every reindexing has `codLen` rows, each of `domLen` coefficients;
- bias length equals `codLen`;
- every wire references an existing external input or earlier producer slot;
- every referenced producer slot exists;
- required operation payload is present and well-formed; and
- size expressions are supported by the selected serialization/realization capability.

On failure it returns an error such as:

```text
equation[3].input[1].reindexing.coeffs[2]:
expected 4 coefficients, found 3
```

It must not insert `0`, `[]`, `.external 0`, `.contract`, `.reals`, or an empty string. Defaults may
remain only where the mathematical semantics explicitly define a default, such as a user-selected
scatter fill.

The decisive API tests are:

- malformed operation tags cannot construct `CheckedThreadedComposed`;
- deleting a wire, matrix row, bias, axis, or payload produces a specific error;
- unknown size expressions fail serialization without emitting partial CSV;
- valid values still round-trip;
- `realize`/`evalThreaded` have signatures accepting checked values only; and
- searches over boundary modules find no `getD`/`get!` use unless immediately justified by a proved
  bound or a documented mathematical default.

The last item should be reviewed semantically rather than enforced by a blind global ban: `getD` in a
proof after a length theorem is different from `getD (.external 0)` in an untrusted decoder.

**Scope qualification:** Stage 4 validates source/runtime capability assumptions; Stage 5 validates
external target representations. Boundary validity is not established until both sides are checked.

#### How proof validity is enforced

**Meaning.** Proof validity is the formal-claims counterpart of the other three buckets. A theorem is
valid only when:

1. Lean's kernel checks its proof term;
2. its transitive dependencies contain no unintended admissions or project axioms;
3. its hypotheses actually express the mathematical conditions needed for the conclusion; and
4. its conclusion states the correct equality/equivalence notion.

These requirements separate two common failure modes:

- **trust failure:** the statement may be correct, but the declaration depends on `sorryAx`; and
- **specification failure:** the declaration may have a proof only because the interface is vacuous,
  inconsistent, or stronger/weaker in the wrong way, or the statement claims raw equality where only
  equivalence up to isomorphism is justified.

Proof validity therefore has several evidence layers:

| Evidence | What it establishes | What it does not establish |
|---|---|---|
| Example/unit test | one computation behaved as expected | universal correctness |
| Property test | many generated computations satisfy a law | kernel-checked theorem |
| Lean theorem | conclusion follows from encoded assumptions | assumptions model the intended mathematics |
| Axiom-closure check | no hidden admission enters the proof | statement adequacy |
| Positive model | assumptions are satisfiable and non-vacuous | theorem is strong enough for all intended uses |
| Countermodel | a proposed statement/interface is too weak or false | the replacement interface is correct |

For compiler results, proof validity may concern structural facts such as shape, routing, codec
round-trip, or semantic simulation. The theorem name and documentation must identify which one. A
route-shape theorem must not be presented as semantic preservation; a numerical agreement test must
not be presented as a categorical theorem.

Operationally, the four conditions above divide into two review tracks:

1. **derivability:** Lean accepts a proof term without `sorryAx` or an unlisted project axiom; and
2. **adequacy:** the theorem's stated interface contains the mathematical hypotheses that justify the
   claim.

The first is mechanical. Maintain a checked manifest of declarations intended to be trusted:

```text
LeanNCD.St.instCategory
LeanNCD.Br.instCategory
LeanNCD.StBr.instDGradedColoredPROP
LeanNCD.Bridge.<agreement theorems>
...
```

CI recursively inspects each declaration's axiom closure and rejects `sorryAx` and project-specific
axioms not present on an explicit allowlist. Standard Lean foundations such as quotient soundness,
propositional extensionality, and classical choice should be listed deliberately rather than confused
with admissions. This catches transitive admissions hidden behind instances, which source grep alone
misses.

The second cannot be supplied by axiom scanning. It requires changing the interfaces and theorem
statements:

- remove or quarantine `weave_unique` now, because the current assumptions admit a compiled
  countermodel;
- define cartesian lifts/cleavage and vertical morphisms before stating uniqueness;
- state uniqueness at the correct level--typically unique vertical isomorphism or equality in a
  quotient/setoid, not raw equality of records containing chosen representatives;
- make the free-object claim in `ColoredPROP` data/laws, e.g. `C.Obj ≃ List gen` with coherence, or
  define `Obj := List gen`;
- either remove `R` from `TargetActegory` or add fields/laws that actually mention `R`; and
- expose any stronger assumptions as explicit theorem parameters rather than obtaining them from an
  unrelated global instance.

Each repaired theorem should have three kinds of verification:

1. **positive model:** construct at least one nontrivial instance satisfying the redesigned interface,
   guarding against vacuous or inconsistent assumptions;
2. **negative/countermodel regression:** show why the old countermodel fails the new hypothesis--for
   example, its proposed weave is not a cartesian lift--rather than merely observing that an unrelated
   field is missing; and
3. **axiom closure:** verify the theorem and the instances used by the positive model contain no
   admissions beyond the trust allowlist.

For weave uniqueness, the concrete dependency order is therefore:

```text
define Vertical
  -> define IsCartesianLift / chosen cleavage
  -> define equivalence of lift representatives
  -> prove existence
  -> prove uniqueness up to that equivalence
  -> only then export the theorem
```

A theorem does not pass merely because its body no longer contains `sorry`; nor does a plausible
interface pass merely because it excludes the existing countermodel. Both derivability and adequacy
must be checked.

**Scope qualification:** the executable E5 agreement tests contribute evidence about compiler
semantics, but they are not substitutes for categorical proofs. Conversely, structural RouteSpec
theorems do not establish numerical semantic agreement. The plan keeps those claims separate.

Spike 3 should claim only representation closure for the `Nonlin` family. The stages below add the
other properties deliberately rather than allowing them to be inferred from a cleaner datatype.

### Staged implementation roadmap

The roadmap now applies the guarantees above in dependency order. Each stage has a bounded purpose,
concrete work, explicit exclusions, and an exit gate. A later stage may rely only on guarantees whose
earlier exit gates have passed.

#### Stage 0: freeze the current failures as tests and decide policy

**Purpose:** prevent the Spike 3 and Spike 4 refactors from preserving or hiding known bad behavior.

**Guarantees advanced:** semantic closure (define the accepted/rejected behavior before refactoring),
boundary validity (fail before returning wrong values), and proof validity only insofar as the
countermodel/axiom tests establish the pre-change trust baseline. This stage does not establish
representation closure; it supplies the behavioral oracle against which Stage 1 is checked.

Before changing `Nonlin` or evaluator dispatch, move the relevant isolated examples into repository
tests. At minimum:

- a scatter whose RHS is `relu(X[i])`, with a negative input;
- an unmarked pointwise activation, proving that no norm axis is required;
- masked and unmasked softmax/normalization;
- a rowwise operation without a marked norm axis, proving that it fails clearly;
- an unsized scan axis, proving that evaluation returns an error rather than an empty tensor;
- a seeded assignment with an unsized non-seeded free axis, proving that it errors rather than
  returning shape `[0]`;
- a contraction with a missing contracted-axis size, proving that it errors rather than using extent
  one;
- one predicate contraction evaluated as a plain statement and as a scan slice, proving both use
  Boolean aggregation; and
- an unknown scatter reduction spelling, proving it cannot acquire overwrite semantics;
- `recurMorphism` through both public capabilities: routed compilation may accept it, while
  `TLProgram.eval` must reject it before partially evaluating the program; and
- compound-size CSV output, proving that serialization returns an error.

For nonlinear scatter, make an explicit semantic decision before the refactor. The recommended
short-term policy is:

```text
scatter + identity nonlinearity     accepted
scatter + non-identity nonlinearity rejected during validation
```

This is preferable to inventing semantics during a datatype cleanup. Supporting the combination later
requires choosing whether nonlinearity occurs before collision reduction or after the output has been
filled/reduced. Add a dedicated `CompileError`/validation error rather than relying on `evalScatter`
to notice it. Keep a defensive evaluator check as well, because programmatic callers can construct
AST values without using the surface compiler.

**Exit gate:**

- each known failure has a repository regression test;
- the tests encode the chosen behavior, not the current accidental result;
- the nonlinear-scatter policy is written in an AST or validation comment; and
- the complete pre-refactor suite result is recorded.

This is a small preparatory change and should be a separate commit from Spike 3, so a reviewer can
distinguish behavioral policy from mechanical constructor migration.

#### Stage 1: close and group the `Nonlin` AST (Spike 3a)

**Purpose:** make pointwise-versus-axiswise classification exhaustive and reusable.

**Guarantees advanced:** representation closure for `Nonlin` is the primary deliverable. Evaluator
parity supplies regression evidence for existing scheduled semantics, and the migrated traversal/fusion
theorems preserve local proof validity. This stage does not establish target semantic closure or
external boundary validity.

Change only the internal AST and its direct consumers. Keep the existing surface grammar initially,
so parser behavior is not mixed into the constructor migration.

Concrete work:

1. Introduce `PointwiseFn` and `AxiswiseFn` (or retain `RowwiseFn` with an explicit terminology
   comment), with all derives required by `Nonlin` and `tlprog!`.
2. Replace the flat constructors with `.identity`, `.pointwise fn`, and
   `.axiswise fn mask`.
3. Add small total helpers owned by the new enums:

   ```lean
   PointwiseFn.toBrOp : PointwiseFn -> BrOp
   AxiswiseFn.toBrOp  : AxiswiseFn -> BrOp
   PointwiseFn.apply  : PointwiseFn -> DenseTensor -> DenseTensor
   ```

   Axiswise evaluation may remain in `Eval.Nonlin`, but dispatch on `AxiswiseFn` must be exhaustive.
4. Migrate all production sites:
   `DSL/Ast.lean`, `DSL/TraverseAxes.lean`, `DSL/Pipeline/Structural.lean`,
   `DSL/Pipeline/Lowering.lean`, `Eval/Nonlin.lean`, `Eval/Eval.lean`, and `Eval/Scan.lean`.
5. Migrate syntax elaboration only enough to construct the new AST; do not yet redesign grammar
   categories.
6. Update the permanent independent references in `TraverseAxesEquiv.lean` and
   `TraverseAxesSpike.lean`. Preserve their hand-written character.
7. Update constructor-based unit tests and macros without weakening assertions to mere successful
   elaboration.

`Nonlin.traverseAxes` should become the single production implementation for mask traversal. The
fusion and equivalence theorems should remain independent checks around it. `toBrBaseP` should call
the total enum-to-`BrOp` helpers rather than repeat concrete operation arms.

**Exit gate:**

- no wildcard match classifies a `Nonlin`, `PointwiseFn`, or `AxiswiseFn`;
- all permanent traversal equivalence/fusion proofs compile;
- plain and scan evaluation produce the same numerical results as the pre-refactor tests;
- `brOpIdx` values are unchanged;
- the nonlinear-scatter regression follows the Stage 0 policy; and
- `lake build LeanNCD` and `lake build Tests` both pass.

**Not included:** syntax-table redesign, `Factor.unaryFn`, target payload repair, semiring
generalization, or `EvalPlan`. Keeping these out makes Stage 1 mostly mechanical and reviewable.

#### Stage 2: make the surface syntax reflect the new distinction (Spike 3b)

**Purpose:** prevent invalid pointwise-mask syntax and remove duplicated elaborator dispatch without
changing evaluation semantics.

**Guarantees advanced:** representation closure at the syntax-to-AST mapping and boundary validity at
the source-language boundary. This stage does not say that every syntactically valid nonlinearity is
supported by every backend; capability validation remains Stage 3/4.

Prefer separate `tl_pointwise_kw` and `tl_axiswise_kw` syntax categories. If the better diagnostic from
a shared category is considered more important, use a total classifier returning `Except`; do not
default an unknown keyword to a valid operation. Preserve the current `atomic("(" "where")`
lookahead behavior for unmasked forms such as `softmax(sum)`.

Test at three levels:

1. **Parser shape:** unmasked `softmax(sum)` is parsed as an axiswise wrapper around a sum, not as the
   start of a malformed `where` clause.
2. **Elaboration:** every keyword maps to the expected enum; masks are retained structurally.
3. **Negative behavior:** pointwise masks and unknown keywords fail with stable, specific diagnostics.

Run these parse/elaboration tests before the full suite because grammar failures can otherwise produce
large, indirect macro errors.

**Exit gate:**

- all supported spellings have positive tests;
- all invalid mask placements have negative tests;
- there is one total spelling-to-enum mapping per keyword category;
- no operation keyword has a fallback constructor; and
- the Stage 1 evaluator and traversal tests remain unchanged and green.

#### Stage 3: perform a source-to-target semantic payload audit

**Purpose:** determine the actual supported fragment before adding another evaluator or reorganizing
more source constructors.

**Guarantees advanced:** this stage extends representation closure from `Nonlin` to an exhaustive
source-to-routed capability decision and establishes the safe intermediate form of semantic closure:
preserve all payload or reject. It also defines the boundary between `TLProgram` and
`RoutableProgram`. It audits proof obligations but does not itself repair categorical proof validity.

Create a maintained table in the target/bridge design documentation, with one row per semantic source
feature:

| Source feature | Scheduled eval | `BrBaseP` field | Codec field | Realization | Status |
|---|---|---|---|---|---|
| sum contraction | yes | `BrOp.contract` + reindexings | encoded | partial | candidate |
| pointwise activation | yes | `BrOp` only | tag | partial | candidate |
| axiswise mask | yes | missing | forced `none` | missing | reject/repair |
| unary factor op | yes | missing | missing | missing | reject/repair |
| scatter fill/reduce | yes | missing | missing | missing | reject/repair |
| dtype/predicate output | checked | missing | missing | defaults real | reject/repair |
| scan body | yes | collapsed | missing | missing | explicitly unsupported |

The table should cite the exact lowering, codec, and evaluator functions. Add a
`SupportedRoutedFragment` predicate or, preferably, executable validation returning a path-rich
`CompileError`. The routed compile API must call it before constructing a success-shaped
`ThreadedComposed`.

This audit is a decision gate for `Factor.unaryFn`. A unary function nested in a product may require
more than another `BrOp` tag: the current `BrOp` labels a whole step, while `UnaryOp` labels one
factor within an expression. Decide among:

1. lower unary factors into explicit intermediate pointwise steps;
2. enrich the target with a scalar-expression/kernel payload; or
3. reject unary factors on the routed path while retaining scheduled evaluation.

Only after this decision should Spike 3c merge `.unaryFn` into `.read`. Otherwise the refactor can
make a target-level semantic loss harder to see.

**Exit gate:**

- every AST constructor and semantic field has an audit row;
- each row is classified as preserved, explicitly unsupported, or scheduled for a named repair;
- routed compilation rejects all unsupported rows;
- no "supported" row relies on reconstructing payload from an operation name; and
- the exact initial fragment for E5 is named.

This stage is analysis plus validation, not a target redesign. It should be short and should avoid
adding placeholder fields whose semantics are not yet known.

#### Stage 4: add light typestate at capability boundaries

**Purpose:** validate assumptions once and make downstream consumers accept only checked forms.

Do not begin with the heavy `Prog (phase : Phase)` design. Introduce only refinements tied to observed
failures:

1. **Resolved nonlinearity.** After output slots are known, convert an axiswise operation into a form
   containing a checked norm-axis position/UID. Pointwise operations need no such field. Both plain
   and scan evaluators consume this result instead of independently searching slots.
2. **Validated statement combinations.** Reject non-identity nonlinear scatter, unsupported routed
   unary factors, and unsupported `recurMorphism` capabilities before lowering/evaluation.
3. **Runtime shape environment.** Scan sizes may depend on concrete inputs, so they cannot all be
   resolved at source compile time. After `inferAxisSizes`, construct a checked runtime shape
   environment in which every scan iteration axis and every scatter source/output axis has a size.
   `evalScan` and `evalScatter` should consume that checked environment and must not use zero/default
   sizes.
4. **Capability-specific entry points.** Distinguish "can route/realize" from "can evaluate." A
   programmatic `recurMorphism` can remain legal for routed compilation while `TLProgram.eval`
   rejects it during preflight. One universal validation pass would incorrectly erase that
   distinction.
5. **Backend capability validation.** After producing a semantically complete `EvalPlan`, validate
   backend-specific restrictions separately. The first JAX capability may require concrete shapes,
   static reduction axes, supported dtypes, and deterministic collision policies without declaring a
   rejected plan invalid for the reference or PyTorch evaluator.

After these narrow forms work, decide whether E2's larger `CoreStmt` is still warranted. If adopted,
introduce it after `splitNonlins` with distinct constructors for contraction, nonlinearity application,
scatter, and recurrence. Make `eval` and `route` pattern-match on those constructors rather than
recovering categories from combinations of `rhs.nonlin`, `rhs.agg`, and statement kind.

Do not redesign recurrence and decompose `finalizeScans` simultaneously. Decide the `CoreStmt`/
`Recurrence` representation first; otherwise Spike 5 will carefully refactor code whose parallel
base/recur-list representation E2 then removes.

**Exit gate:**

- norm-axis lookup occurs once during resolution, not separately in plain and scan evaluation;
- missing runtime scan/scatter sizes return `Except` errors before allocation or iteration;
- each public consumer performs the validation appropriate to its capability;
- JAX-unsupported but semantically valid plans return typed capability errors before Python starts;
- downstream evaluator/lowering functions no longer contain defensive semantic defaults for these
  checked facts; and
- direct constructors are covered by negative tests, not only surface syntax.

#### Stage 5: harden serialization and realization boundaries

**Purpose:** ensure E5 evaluates validated target data rather than defaults synthesized from malformed
external input.

Split external and internal representations:

```text
CSV/ACSet rows
  -> RawSBr / raw presentation
  -> validate : RawSBr -> Except BridgeError CheckedSBr
  -> decode/realize/evaluate CheckedSBr
```

Concrete changes:

- make operation-tag decoding partial (`brOpOfIdx?` or `Except`) instead of mapping unknown tags to
  `.contract`;
- reject missing/invalid wire labels instead of using `.external 0`;
- validate matrix row counts, coefficient widths, bias lengths, weave counts, and routing arities
  before decoding;
- propagate `encodeSize` failures through row builders and `writeSBr`;
- make realization consume checked `StMatP`/`BrBaseP`/`ThreadedComposed` values;
- retain total decoders only as explicitly named lossy/debug utilities, not production entry points;
  and
- add malformed-input tests for each former default path.

Spike 6b's pure `RouteSpec` consolidation can proceed independently if it does not alter boundary
types. Spike 6c/6d work in `AcsetCodec` should wait for or include this raw/checked split; otherwise
the consolidation will entrench the total/defaulting API and cause another migration.

**Exit gate:**

- arbitrary external data cannot produce a checked routed artifact without validation;
- every former meaning-changing default has a negative test;
- valid encode/decode round trips still pass;
- malformed values report the field/path that failed; and
- realization APIs cannot be called with unchecked decoded structures.

#### Stage 6: repair target payloads one operation class at a time

**Purpose:** expand target closure without designing a universal target in one step.

Start with the smallest fragment already close to complete:

1. plain sum contraction with affine reads;
2. pointwise activations lowered as isolated steps by `splitNonlins`; then
3. other aggregators only after their identity/combine semantics are explicit.

For each next class, add the necessary typed payload before marking it supported:

- axiswise functions need the function, norm axis, and a compiled/preserved mask;
- scatter needs fill and a typed reduction policy (not `Option String`);
- unary factors need either explicit intermediate steps or scalar-expression payload;
- dtype/predicate operations need scalar semantics carried through `BrBaseP`, the codec, and
  realization; and
- scans need a body/recurrence representation rather than only `.scan`/`.scanAffine` tags.

Avoid one increasingly optional `BrBaseP` record where operation-specific fields can be absent.
Prefer an operation payload ADT whose constructors carry exactly their required data, while common
shape/routing fields remain in `BrBaseP`. Each constructor should define:

- validation;
- scheduled semantics;
- routed semantics;
- codec round trip; and
- realization interpretation or an explicit unsupported result.

**Exit gate for each operation class:**

- lowering preserves every payload identified by Stage 3;
- codec round-trip tests preserve that payload;
- malformed payloads cannot construct a checked operation;
- an E5 agreement test exists for the class; and
- removing or mutating the payload makes that test fail.

This per-class gate prevents a broad `BrOp` enum from being mistaken for a semantically closed target.

#### Stage 7: E5 -- establish executable agreement incrementally

**Purpose:** test that routed lowering preserves meaning, not only shape and wiring.

Define `evalBrBaseP` and `evalThreaded` only over the checked target representation. Begin with the
fragment closed in Stage 6; do not implement unsupported operations using identity/default behavior.

The first agreement suite should state its domain explicitly:

```text
scan-free
sum contraction
affine reads whose reindexings validate
real-valued tensors
optional isolated pointwise activation
no masks, unary factors, scatter, predicates, or recurMorphism
```

For each program in that fragment compare:

1. `compileToScheduled` followed by `evalScheduled`;
2. routed lowering followed by `evalThreaded`; and
3. routed artifact -> ACSet encode/decode -> `evalThreaded`.

Compare shapes and tensor values with an explicit floating-point tolerance. Include generated affine
maps and multi-step routing, not only hand-written identity reindexings. A failure should print the
source program, scheduled result, routed result, and decoded artifact.

Then widen the declared fragment one operation class at a time using Stage 6's exit gate. Masked
axiswise operations, unary factors, scatter, and scans must remain rejected until their payloads and
agreement tests land.

**Exit gate:**

- the supported-fragment predicate and routed validator agree;
- every accepted fragment program can be evaluated on both paths;
- route and codec round trips preserve numerical behavior, not only structure;
- unsupported programs fail before producing a routed success value; and
- RouteSpec's structural theorems and E5's semantic tests cover complementary claims.

Only after this stage is it accurate to call the routed artifact an executable semantic IR.

#### Stage 8: optimize or generalize only the established semantic path

**Purpose:** avoid optimizing an incomplete or unstable representation.

Do not defer all of Spike 4 to this optimization stage. Follow the
[revised Spike 4 sequencing](#revised-spike-4-sequencing): 4b/4a can follow Stage 0, 4d/4c should
consume the Stage 1/4 resolved forms, 4g belongs with typed scatter payload work, and 4e/4h/4i can
proceed once their diagnostic boundaries are chosen. The minimal backend-neutral `EvalPlan` and scan-free JAX oracle now land earlier, after Stages 3/4 and
the foundational Spike 4 work. Stage 8 contains optimization and generalization of that established
boundary:

- **E4 `EvalPlan`:** optimize and widen the early scan-free contraction prototype. Generate affine
  plans from the same checked reindexing data consumed by route, and differential-test the generic
  plan worker, optimized JAX lowering, scheduled evaluation, and `evalThreaded` wherever their
  declared fragments overlap.
- **E3 semiring generalization:** do this after contractions/scatter carry an explicit operation
  policy. Otherwise hard-coded real arithmetic will survive in side paths while the main interface
  appears generic.
- **Spike 5 scan decomposition:** schedule after the E2 recurrence representation decision.
- **E10 code generation:** begin only when `EvalPlan` or the checked routed IR has agreement coverage
  for the operations the generated backend claims to support.
- **Spike 3c:** perform only after unary-factor target lowering has a chosen, tested representation.

The early E4 boundary does not need every future operation, but it does need a stable, explicitly
named fragment and the `DenseTensor` semantic oracle. Stage 8 must not change plan meaning to suit an
optimization. E10 has a stronger prerequisite: generated code must reject operations outside its
covered fragment rather than silently emit approximations.

#### Parallel proof track

The categorical work can proceed in parallel because most files do not overlap with Spike 3, but its
own dependencies should be explicit:

1. **Trust boundary first.** Add generated axiom-closure CI and remove/quarantine `weave_unique` from
   the trusted API. Keep the countermodel as a regression.
2. **Interface decisions second.** Decide whether `ColoredPROP` fixes objects to `List gen` or stores
   an equivalence, and whether `TargetActegory` removes `R` or adds genuinely `R`-dependent data.
   These are API decisions; do not build more theorems on the current underconstrained forms.
3. **Independent proof repair.** The `St` hexagon proof spike may proceed independently once its
   axiom closure is visible in CI.
4. **Weave redesign.** Specify cartesian lifts/cleavage, vertical arrows, and the equivalence under
   which lifts are unique before restating a uniqueness theorem.
5. **Cospan/normal-form spike.** First determine whether non-bijective wiring enriches `BrNF`/`NData`,
   the semantic model, or `Br.Hom` itself. Only then use it as an E13 prerequisite.

The proof-track exit criterion is not merely fewer `sorry`s. It is that the trusted exported
declarations have generated axiom reports and that disproved statements are no longer available as
ordinary theorems.

#### Recommended commit and review boundaries

The stages above should not land as one restructuring branch. Suggested review units are:

| Change | Behavioral? | Main verification |
|---|---:|---|
| Stage 0 regressions and policy | yes | focused tests + full baseline |
| Spike 3a AST migration | intended no, except chosen scatter rejection | traversal proofs + evaluator parity |
| Spike 3b syntax tables | syntax diagnostics only | parser/elaborator positive and negative tests |
| Payload audit and routed validator | yes, rejects false successes | supported/unsupported compile tests |
| Light typestate/runtime shape checks | yes, earlier failures | direct-constructor and runtime error tests |
| Raw/checked bridge split | yes, rejects malformed input | malformed cases + round trips |
| One target payload class | yes, expands support | codec + E5 agreement for that class |
| EvalPlan/JAX prototype | intended no | scheduled vs plan vs jitted-JAX differential oracle |

Each review should state which of the four closure claims at the start of this section it advances.
This makes progress measurable: a refactor is not described as a semantics improvement unless its
exit gate actually checks semantic preservation.

## Conclusion

The recommended restructuring is conservative about the codebase's strongest existing choices while
being strict about unsupported semantics, malformed boundaries, and unproved claims.

### Architectural constraints to preserve

- **The proof/execution split.** Noncomputable dependent objects and computable presentation records
  should remain separate.
- **Dependent dimensions in `StMat`.** `Base/St.lean:16-30` uses `Fin` indices to enforce matrix
  arity at the proof level. Bounds preservation can be layered on without discarding this encoding.
- **The free SMC syntax for `Br`.** `Hom` plus the `Rel` quotient
  (`Base/Br.lean:53-141`) is much more faithful than pretending syntax trees are definitionally
  equal. Factoring it into a reusable signature-to-free-SMC construction would be valuable.
- **ADTs instead of sentinels.** `Wire` and `BrOp` in `DSL/Target.lean:51-118` prevent ambiguity and
  stringly typed dispatch.
- **Explicit failures.** The compiler's `CompileError` type and recent fail-loud checks are the right
  direction; the same policy should be extended to all bridges and serializers.
- **Applicative traversals.** They are concise, compositional, and aligned with established
  functional-programming practice.

### Immediate decisions

The detailed order and exit criteria are in the
[staged implementation roadmap](#staged-implementation-roadmap). The immediate decisions are:

1. Land [Stage 0](#stage-0-freeze-the-current-failures-as-tests-and-decide-policy) first, including an
   explicit reject-until-defined policy for nonlinear scatter.
2. Execute [Spike 3a](#stage-1-close-and-group-the-nonlin-ast-spike-3a) and
   [Spike 3b](#stage-2-make-the-surface-syntax-reflect-the-new-distinction-spike-3b) as separate,
   reviewable changes. Claim representation closure for `Nonlin`, not end-to-end semantic closure.
3. Perform the [semantic payload audit](#stage-3-perform-a-source-to-target-semantic-payload-audit)
   before Spike 3c, the minimal E4 backend boundary, or E10. Unsupported routed constructs must become
   named compile errors.
4. Execute the [Spike 4 dependency waves](#revised-spike-4-sequencing): establish both contraction
   identities and one checked seeded worker first; route plain/scan assignments through one resolved,
   dtype-aware path; prototype a scan-free `EvalPlan`/JAX oracle; and defer scan helper extraction until
   that plan boundary and the E2 recurrence decision are established.
5. In parallel, begin the [proof track](#parallel-proof-track) by quarantining `weave_unique` and
   adding generated axiom-closure checks.
6. Proceed to checked boundaries and E5 only after the supported routed fragment is explicit. Expand
   that fragment one operation class at a time, with payload, codec, and numerical-agreement tests.

The unifying principle is **honest boundaries**: closed datatypes must be handled exhaustively,
accepted operations must retain their semantics, malformed external data must fail validation, and
exported theorems must expose and satisfy the assumptions on which they depend.

## Appendix A: JAX as an evaluation backend

This appendix evaluates JAX as an eventual execution backend for LeanNCD and turns the principal
integration hurdles into concrete design choices. The recommendation is not to replace the current
Lean evaluator immediately. Keep it as the small, inspectable reference semantics, compile checked
programs to a backend-neutral `EvalPlan`, and lower that plan independently to JAX and PyTorch:

```text
TLProgram
  -> compile and validate
  -> ScheduledProgram
  -> EvalPlan
       |-> DenseTensor reference worker
       |-> JAX lowering -> jit -> execute
       `-> PyTorch lowering -> compile/eager -> execute
```

If JAX and PyTorch require different meanings for an `EvalPlan` constructor, the constructor is
underspecified. Backend-specific optimization metadata is acceptable; backend-specific mathematical
semantics is not.

### What `lean4-mlir/jax` establishes

The relevant precedent is Brett Koonce's
[`lean4-mlir/jax`](https://github.com/brettkoonce/lean4-mlir/tree/main/jax). Its
[`README`](https://github.com/brettkoonce/lean4-mlir/blob/main/jax/README.md) describes a Lean
metaprogram that walks a neural-network `NetSpec` and emits readable JAX Python. The generated program
uses JAX autodiff, JIT compilation, accelerator dispatch, and sharding. The implementation is divided
between:

- [`Jax/Codegen.lean`](https://github.com/brettkoonce/lean4-mlir/blob/main/jax/Jax/Codegen.lean),
  which generates a complete Python trainer; and
- [`Jax/Runner.lean`](https://github.com/brettkoonce/lean4-mlir/blob/main/jax/Jax/Runner.lean),
  which writes that program below `.lake/build`, launches Python, and streams its output.

The subproject has a real
[`lakefile`](https://github.com/brettkoonce/lean4-mlir/blob/main/jax/lakefile.lean) with model and
oracle executables. Its
[`jax.yml` workflow](https://github.com/brettkoonce/lean4-mlir/blob/main/.github/workflows/jax.yml)
builds the emitter/executables and runs 14 small generated programs on CPU JAX. The accompanying
[`ci_smoke.sh`](https://github.com/brettkoonce/lean4-mlir/blob/main/jax/tests/vjp_oracle/ci_smoke.sh)
is especially careful about its claim: a green run shows that generated code parses, executes, and
produces a finite loss; it does **not** establish agreement with the separate hand-derived VJPs.

That is meaningful engineering evidence, but the supported source vocabulary is a closed collection
of neural-network layers. It does not demonstrate LeanNCD's general:

- named, arbitrary-rank axes and integer-affine reads;
- per-term sum, max, min, and Boolean contraction;
- masked axiswise operations with explicit all-masked behavior;
- scatter fill and collision policies;
- coupled and multi-axis recurrences; or
- structured transfer of tensor results and diagnostics back into Lean.

The reusable lesson is the auditable generated-code workflow and its evidence discipline, not
`NetSpec` as an intermediate representation. LeanNCD should generate JAX from `EvalPlan`; translating
through neural-network layers would create a second, semantically incomplete IR.

### Required `EvalPlan` contract

The JAX lowerer should accept only a plan whose dynamic values are tensor contents. Structural choices
must already be resolved:

```lean
structure TensorSig where
  name  : String
  shape : Array Nat
  dtype : ScalarDType

structure EvalPlan where
  version     : Nat
  inputs      : Array TensorSig
  outputs     : Array TensorSig
  steps       : Array PlanStep
  numericMode : NumericMode
```

Each `PlanStep` should carry constructor-specific data rather than a collection of optional fields:

- affine gather: source, output iteration shape, affine map, and out-of-bounds policy;
- contraction: factors, per-term reduction axes, factor operation/identity, and term
  operation/identity;
- nonlinearity: function, resolved axis, mask, and exceptional-row policy;
- scatter: destination map, output shape, fill, collision operation, out-of-bounds policy, and
  injectivity result;
- scan: ordered state signatures, base plan, step plan, static iteration shape/order, and causality
  certification.

The plan needs a canonical encoding and hash. Names used only for diagnostics should not perturb the
semantic hash; shapes, dtypes, operations, constants, policies, and iteration order must. The hash is
both the JIT cache key and the identity printed in backend errors.

### Static shapes, tracing, and compilation caching

**Hurdle.** JAX transforms pure functions and traces array programs before compilation. Its
[`jit` documentation](https://docs.jax.dev/en/latest/_autosummary/jax.jit.html) requires non-array
structural arguments to be static and notes that changing static values triggers recompilation.
JAX's documented
[`ConcretizationTypeError`](https://docs.jax.dev/en/latest/errors.html#jax.errors.ConcretizationTypeError)
also shows why output shapes and reduction axes cannot normally depend on tensor values. Boolean
selection that changes array length is similarly incompatible with JIT.

**Proposed solution.**

1. Treat shape inference as a Lean compilation phase, never as JAX runtime logic.
2. Specialize one JAX function per canonical plan hash and concrete tensor signature.
3. Close over plan constants in the generated function rather than passing a mutable Python plan
   object as a static argument.
4. Pass only arrays at invocation time. Verify their shape/dtype against `TensorSig` before device
   transfer.
5. Initially reject value-dependent shape, data-dependent axis selection, and runtime-varying scan
   length as unsupported capabilities.
6. Cache both the generated Python function and its jitted callable by
   `(planHash, backend, deviceKind, numericMode)`.

Shape polymorphism available through
[`jax.export`](https://docs.jax.dev/en/latest/export/export.html#shape-polymorphic-export) can be
investigated later for declared symbolic dimension families. It should not weaken the first backend's
concrete-shape contract.

**Acceptance gate.** Every supported plan succeeds under `jax.jit`; malformed or unresolved shapes
fail in Lean before Python starts; repeated execution with the same signature produces a cache hit;
changing a static shape produces a distinct plan hash and compilation.

### Affine gather and zero padding

**Hurdle.** LeanNCD defines out-of-range reads as zero padding. JAX's documented default differs:
ordinary out-of-bounds reads are clipped, while indexed updates are dropped. The
[`Array.at` API](https://docs.jax.dev/en/latest/_autosummary/jax.Array.at.html) also wraps negative
indices unless explicitly disabled.

**Proposed solution.**

For the first lowerer, materialize the output coordinate grid from the plan's static output shape,
apply the integer-affine map to obtain one index array per source dimension, and compute:

```python
valid = logical_and.reduce(
    [(0 <= idx[d]) & (idx[d] < source.shape[d]) for d in range(source.ndim)]
)
safe = [jnp.clip(idx[d], 0, source.shape[d] - 1) for d in range(source.ndim)]
value = jnp.where(valid, source[tuple(safe)], jnp.asarray(0, source.dtype))
```

Clipping is only a memory-safe implementation detail; `valid` supplies the semantics. An alternative
for directly supported index forms is:

```python
source.at[index].get(
    mode="fill", fill_value=0, wrap_negative_indices=False
)
```

The explicit mask is preferable initially because compound affine maps and multiple index arrays can
be tested uniformly. Later, large grids can lower to `lax.gather` or tiled/vmapped workers to avoid
materializing every coordinate. That optimization must consume the same affine map and validity
predicate.

Empty source dimensions require a separate plan-time decision because clipping into an empty axis is
invalid. Either reject zero-sized source dimensions in the supported JAX fragment or lower the whole
gather to an output-shaped zero tensor.

**Acceptance gate.** Differential tests cover every boundary face, negative indices, positive
overflow, shifts, strides, multi-axis affine expressions, empty dimensions, and asymmetric shapes.
Replacing the fill path with JAX's default clipping must make at least one test fail.

### Contractions are not all `einsum`

**Hurdle.** `jnp.einsum` naturally implements ordinary sum-product but not Boolean OR-AND,
max-times, min-times, min-plus, or LeanNCD's rule that each sum term contracts only the axes that term
mentions.

**Proposed solution.**

Represent operations as closed plan enums with explicit identities:

```lean
inductive ScalarBinOp | add | mul | min | max | logicalAnd | logicalOr

structure ContractionAlgebra where
  factorOp  : ScalarBinOp
  factorId  : ScalarConst
  reduceOp  : ScalarBinOp
  reduceId  : ScalarConst
```

Lower each term independently:

1. affine-gather each factor over the term's complete iteration space;
2. combine factors from `factorId` using `factorOp`;
3. reduce only that term's contracted axes from `reduceId`;
4. combine the resulting output-shaped terms using the RHS term operation.

Use `einsum`/`dot_general` only as a verified fast path for compatible sum-product terms. Use
`jnp.max`, `jnp.min`, `jnp.any`, or `jnp.all` for other closed algebras. Empty factor and reduction
domains must return plan identities explicitly; do not rely on backend defaults, some of which reject
empty reductions.

This generic broadcast implementation is intentionally not the final performance design. It is the
simple semantic backend against which optimized einsum and fused lowerings are differentially tested.

**Acceptance gate.** Test zero factors, zero terms, zero-length reduction axes, disjoint
term-contraction sets, repeated reads, and all built-in algebras. Compare generic and optimized JAX
lowerings as well as the Lean reference.

### Predicate representation and dtype discipline

**Hurdle.** LeanNCD currently stores predicate values in `DenseTensor` numerically, while JAX has a
native Boolean dtype. Implicitly treating `0/1` floats as Booleans would recreate the current
plain-versus-scan dispatch bug and make mixed predicate/numeric operations backend-dependent.

**Proposed solution.**

- Give each plan tensor an explicit `ScalarDType`, initially `f64`, `f32`, or `bool`.
- Lower predicate declarations to JAX `bool` arrays and Boolean contraction to
  `logical_and`/`logical_or`.
- Introduce explicit plan casts for Iverson embedding (`bool -> scalar`) and, only if the language
  defines it, scalar comparison (`scalar -> bool`).
- Reject arithmetic on predicate tensors unless a typed operation specifies the conversion.
- Keep the Lean reference's numeric predicate representation behind its own explicit adapter so that
  agreement compares meanings, not storage formats.

An alternative is to keep numeric `0/1` predicates in every backend. That reduces initial transport
changes but permits invalid non-Boolean values and loses JAX's dtype checking. Native Boolean plan
values are the stronger boundary.

**Acceptance gate.** Predicate contractions agree inside and outside scans; invalid mixed-dtype plans
fail validation; round trips preserve Boolean dtype; tests include values for which real sum and
Boolean OR produce different answers.

### Masked normalization and differentiation

**Hurdle.** JAX's stock softmax does not by itself encode LeanNCD's mask convention, all-masked-row
result, or zero-denominator behavior. JIT also rejects dynamically-sized Boolean indexing; JAX
recommends fixed-shape three-argument `where` in its
[`NonConcreteBooleanIndexError` guidance](https://docs.jax.dev/en/latest/errors.html#jax.errors.NonConcreteBooleanIndexError).
If differentiation is later enabled, an undefined expression in an inactive `where` branch can still
produce NaN gradients, as documented in the
[`where` gradient FAQ](https://docs.jax.dev/en/latest/faq.html#gradients-contain-nan-where-using-where).

**Proposed solution.**

Lower masks as fixed-shape Boolean arrays broadcastable to the input. For masked softmax:

1. replace masked values with `-inf`;
2. compute a stable maximum over valid entries;
3. replace the all-masked maximum with a finite safe value before subtraction;
4. exponentiate only a finite, safe operand;
5. force masked exponentials to zero;
6. divide by a safe denominator; and
7. return zero where the denominator is zero.

Normalize and L2-normalize should similarly sanitize the denominator *inside* the division:

```python
safe_den = jnp.where(den != 0, den, jnp.ones_like(den))
y = jnp.where(mask & (den != 0), x / safe_den, 0)
```

Store the all-masked/zero-denominator policy in the plan even if the only initial policy is `zero`.
This prevents backend library defaults from defining source-language semantics.

**Acceptance gate.** Test masks selecting none, one, and many elements; different resolved axes;
extreme logits; zero and signed inputs; eager versus jitted output; and finite forward/reverse
derivatives on the declared differentiable subset.

### Scatter collisions, ordering, and determinism

**Hurdle.** JAX's
[`Array.at` documentation](https://docs.jax.dev/en/latest/_autosummary/jax.Array.at.html) says that all
duplicate updates are applied and that their order may be implementation-defined or nondeterministic.
That supports associative sum/max reductions, but not LeanNCD's current loop-observable "last source
coordinate wins" overwrite. Out-of-bounds and negative-index behavior must also be selected explicitly.

**Proposed solution.**

First flatten each destination coordinate into a static output segment ID and retain a validity mask.
Then lower by collision policy:

- `rejectCollisions`: validate injectivity in Lean when sizes are concrete; retain a defensive
  duplicate check in the debug Python worker.
- `sum`: initialize with `fill`, then use `.at[id].add(value, mode="drop")` or
  [`jax.ops.segment_sum`](https://docs.jax.dev/en/latest/_autosummary/jax.ops.segment_sum.html) with a
  static `num_segments`. Specify whether `fill` participates at touched coordinates; the plan must not
  leave this implicit.
- `max`: initialize with `fill`, then use `.at[id].max(value, mode="drop")`.
- `overwrite` on an injective map: use `.at[id].set(value)` with `unique_indices=True` only after the
  checker establishes that promise.
- non-injective ordered overwrite: reject in the first backend.

If ordered overwrite is later required, implement it explicitly: attach each source value's canonical
source-order rank, compute the maximal rank per output segment, and gather the value at that rank.
This is deterministic but adds sorting/segment work and needs a stated tie/order convention. Do not
assume `.at.set` implements it.

Always use `wrap_negative_indices=False`; use `mode="drop"` only because the plan declares
out-of-range writes to be ignored. Nonlinear scatter remains rejected until the plan states whether
the nonlinearity is before or after collision reduction.

**Acceptance gate.** Test injective writes, every collision policy, nonzero fill, duplicate indices,
negative/out-of-range destinations, CPU/GPU agreement, and repeated-run determinism. A plan marked
`unique_indices` without proof must be impossible to construct.

### Coupled and multi-axis scans

**Hurdle.** [`jax.lax.scan`](https://docs.jax.dev/en/latest/_autosummary/jax.lax.scan.html) scans one
leading iteration dimension and requires a carry with fixed pytree structure, shape, and dtype. That
fits one-axis coupled state, but LeanNCD also has base slices, complete state outputs, multiple
advancing axes, zero-default boundaries, and a defined cartesian order.

**Proposed solution.**

For a one-axis scan:

- represent all coupled current-state slices as one pytree carry;
- package external per-step slices as `xs`;
- have the body read one immutable `oldCarry`, compute every next state, then return one `newCarry`;
- return state slices as `ys`, allowing `lax.scan` to stack the full output history; and
- incorporate the base slice either as the initial carry plus a prepended output or by scanning
  exactly the remaining `L - 1` steps.

This structure enforces the `stepEnv` rule: every coupled update reads the same pre-step snapshot.

For multi-axis scans, prototype two lowerings:

1. **Flattened lexicographic scan:** statically enumerate the cartesian coordinates in LeanNCD order,
   carry fixed-shape full state tensors, and use dynamic indexed reads/writes for predecessor/current
   cells.
2. **Nested scans:** generate one `lax.scan` per iteration axis when the recurrence dependence and
   output layout factor cleanly.

Use the flattened form as the general semantic implementation because it makes order explicit. Select
the nested form only after differential tests establish equivalence for a recognized plan pattern.
Zero-length axes, unreachable boundary cells, base coverage, and multi-axis predecessor rules must be
resolved during plan validation.

Reverse-mode memory may become large because scans retain intermediates. Only after forward agreement
should the backend consider `jax.checkpoint`/rematerialization or custom VJPs.

**Acceptance gate.** Cover one-axis self recurrence, simultaneous coupled states, asymmetric two-axis
grids, boundary cells, zero-length policy, and external reads indexed by iteration axes. Compare the
JAX result to both `DenseTensor` evaluation and the independent scan-unrolling oracle.

### Numeric modes and reproducibility

**Hurdle.** JAX defaults to 32-bit values and normally disables 64-bit array creation; the
[`default dtype documentation`](https://docs.jax.dev/en/latest/default_dtypes.html) describes
`jax_enable_x64` as a process-global setting. JIT/XLA may also reassociate or simplify floating-point
expressions, so even jitted and eager JAX can differ; see the
[`jit` numerics FAQ](https://docs.jax.dev/en/latest/faq.html#jit-changes-the-exact-numerics-of-outputs).

**Proposed solution.**

Define two explicit profiles:

| Profile | JAX configuration | Purpose |
|---|---|---|
| `reference64` | CPU, `jax_enable_x64=True`, deterministic seeds | differential correctness |
| `performance32` | accelerator-default float32, optional later bf16 | deployment and benchmarks |

Include the profile in the cache key and result metadata. Specify index width, overflow behavior,
NaN/Inf policy, reduction tolerance, and comparison method. Use absolute-plus-relative tolerance and
operation-sensitive bounds; reductions need a tolerance that accounts for accumulation length.

Do not compare only final model loss. Compare every named plan step in a debug mode, which localizes
the first semantic divergence. Benchmarks must call `block_until_ready()` so asynchronous dispatch is
not mistaken for completed execution.

**Acceptance gate.** Reference64 matches Lean within tight declared tolerances; performance32 has
separate tolerances; tests include cancellation, large reductions, infinities, and all-masked rows;
reports state backend/device/JAX version/profile.

### Lean-to-Python execution boundary

**Hurdle.** `lean4-mlir`'s runner is intentionally simple: write a script, spawn Python, and print
stdout/stderr. It does not return typed tensors or errors, and its current `runJax` prints a nonzero
exit rather than returning an `Except`. Repeating that process for every evaluation would also lose
JIT cache reuse.

**Proposed solution.**

Use two stages:

1. **One-shot conformance runner.** Generate an auditable Python file beside a versioned plan manifest,
   run it in a pinned environment, and read a result manifest plus raw tensor files. This is ideal for
   early tests and bug reproduction.
2. **Persistent worker.** Once semantics stabilize, run a long-lived Python process with a
   length-prefixed request/response protocol. Cache jitted functions by plan hash and accept repeated
   tensor invocations.

The protocol should reserve stdout for framed responses and stderr for logs. Every request contains a
request ID, protocol version, plan hash or plan definition, input tensor descriptors, backend/profile,
and requested outputs. Every response is one of:

```text
compiled(planHash, cacheHit, compileMillis)
evaluated(planHash, outputs, warnings, executeMillis)
rejected(phase, typedCode, planStep, message, backendDetails)
```

For the prototype, JSON metadata plus little-endian raw tensor buffers is sufficient and easy to
inspect. Validate byte length, shape product, dtype, endianness, names, and duplicate fields before
constructing Lean tensors. Do not deserialize arbitrary Python objects or execute externally supplied
generated code.

Map Python/JAX exceptions into a closed `BackendError` family (`protocol`, `unsupportedPlan`,
`shapeMismatch`, `traceFailure`, `compileFailure`, `deviceFailure`, `executionFailure`) while retaining
sanitized backend details. This is why Spike 4h/4i should land before the backend becomes public.

**Acceptance gate.** Nonzero Python exits become `Except` errors; malformed result files are rejected;
timeouts and cancellation terminate only the owned child; repeated plans demonstrate cache hits; no
warning or tensor result is inferred by parsing human-readable logs.

### Export and StableHLO

**Hurdle.** JAX can export a jitted function as StableHLO plus metadata using
[`jax.export`](https://docs.jax.dev/en/latest/export/export.html), but this is a deployment artifact,
not a substitute for LeanNCD's semantic plan. The documentation gives bounded compatibility windows,
warns that serialized artifacts must be trusted, and restricts portability for custom calls.

**Proposed solution.**

Defer export until a JAX function already passes differential tests. Keep:

- `EvalPlan` as the semantic, versioned source of truth;
- generated Python/JAX as one lowering;
- exported StableHLO as a cache/deployment artifact tied to the plan hash, JAX/jaxlib version,
  target platforms, numeric profile, and export format version.

Avoid custom calls and Pallas kernels in the first backend. If an operation eventually needs one,
mark the plan capability accordingly and test export support separately. Never load an untrusted
exported artifact.

**Acceptance gate.** Export, serialize, deserialize, and execute the supported fragment; compare it to
the non-exported jitted function; reject metadata/hash mismatches; test every claimed target platform;
retain a fallback that regenerates the artifact from `EvalPlan`.

### Automatic differentiation is a separate capability

**Hurdle.** JAX makes `grad` easy to call, but it does not decide LeanNCD's derivative semantics for
max/min ties, predicates, hard masks, scatter collisions, domain-checked unary functions, or recurrence.
Forward agreement does not imply gradient agreement.

**Proposed solution.**

Define `supportsVjp : EvalPlan -> Except CapabilityError DifferentiablePlan`. Initially admit smooth
real sum-product contraction, affine gather, and selected pointwise/normalization operations. Reject
predicate outputs, ordered overwrite, and operations whose subgradient policy is undecided. Record
tie-breaking and masked-value conventions before adding max/min/scatter VJPs.

Use JAX autodiff as an executable oracle, as `lean4-mlir` does, but compare it against finite
differences and any independently derived Lean VJP. Preserve the distinction made by
`ci_smoke.sh`: "the generated gradient program ran" is weaker than "the gradients agree."

**Acceptance gate.** Primal agreement passes first; directional finite differences agree away from
nondifferentiable points; unsupported plans fail capability validation; NaN-gradient regression cases
cover masks and domain-sensitive functions.

### Differential testing and evidence

The backend test matrix should make each claim explicit:

| Tier | Evidence |
|---|---|
| emit | generated Python parses and imports |
| eager | JAX function executes on small concrete inputs |
| jit | the same plan traces, compiles, and executes |
| reference agreement | named outputs agree with `DenseTensor` |
| transformation agreement | generic and optimized lowerings agree |
| cross-backend agreement | JAX and PyTorch agree with the same plan |
| device agreement | CPU and selected accelerators agree within policy |
| export agreement | rehydrated export agrees with the jitted function |
| VJP agreement | autodiff agrees with an independent oracle on the supported subset |

Generated small programs should vary rank, dimensions including zero/one, affine coefficients and
offsets, masks, per-term contraction sets, collision multiplicity, dtypes, and scan topology. Preserve
failing seeds and the canonical plan in test output. Add mutation tests for the high-risk policies:
clipping instead of fill, wrong contraction identity, real instead of Boolean aggregation, sequential
instead of simultaneous scan updates, and unordered overwrite.

### Phased implementation

1. **Backend contract:** finish Spike 4's checked sizes, `Combine`, dtype-aware assignment,
   `ResolvedNonlin`, typed scatter, structured errors, and `EvalReport`.
2. **Plan prototype:** define canonical `EvalPlan`; compile the smallest scan-free real sum-product
   fragment; execute it with both `DenseTensor` and a one-shot generated JAX script.
3. **Stateless closure:** add affine zero-padded gather, Boolean/max/min contraction, pointwise
   functions, and masked normalization one class at a time.
4. **Scatter:** add injective set, sum, and max; keep ambiguous overwrite and nonlinear scatter
   rejected.
5. **Scans:** add one-axis coupled `lax.scan`, then flattened multi-axis scans.
6. **Worker:** replace per-call Python startup with a versioned persistent worker and plan cache.
7. **Optimization:** add einsum/dot-general and recognized nested-scan fast paths, each guarded by
   generic-lowering differential tests.
8. **Gradients and export:** add independently gated VJP support and StableHLO deployment artifacts.

The first milestone should not be "JAX runs a model." It should be:

```text
For the declared scan-free reference64 fragment, every checked EvalPlan either:
  (a) produces matching DenseTensor and jitted-JAX outputs, or
  (b) is rejected before backend execution with a typed capability error.
```

### JAX versus PyTorch

PyTorch is likely the faster first implementation path because eager tensors tolerate ordinary Python
control flow and simplify semantic debugging. This repository already contains a
`torch_compile/torch_compile.py` prototype. JAX's stricter purity/static-shape model is valuable once
the checked plan exists, and [`lax.scan`](https://docs.jax.dev/en/latest/_autosummary/jax.lax.scan.html)
is a strong fit for fixed-shape coupled recurrence.

Neither backend removes the need for typed scatter and shape semantics. PyTorch's
[`scatter_reduce_`](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.scatter_reduce_.html)
also documents backend and gradient constraints, while
[`torch.compile`](https://docs.pytorch.org/docs/stable/generated/torch.compile.html) introduces its
own graph-capture and dynamic-shape behavior. Therefore:

- use PyTorch eager mode to bring up plan semantics quickly;
- require JAX JIT as the stricter static backend;
- retain `DenseTensor` as the independent reference;
- lower all three from the same plan; and
- measure compile latency, steady-state execution, memory, and numerical agreement separately.

The backend choice should follow evidence per operation class. It should not change the language's
meaning.

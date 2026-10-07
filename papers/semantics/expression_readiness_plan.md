# Expression/readiness semantic validation slice

**Authoring verification complete.** Both final review lenses are clear; the
execution-base finding was corrected and confirmed resolved. This plan ships
verified artifacts, not a released implementation. See the authoring record
for exact evidence and limits.

## 1. Goal and process

**Full path:** a new typed expression presentation and proof surface require
ordered patches, discriminating fixtures, mutation replay, and two final lenses.
This is ONE semantic-validation slice, not a production-backend redesign.
Its immediate purpose is confidence in beginning the written expression semantics.
It does not establish that all starting semantics are bug-free.

The specification anchors are [tensor_logic_semantics.md](tensor_logic_semantics.md)
Sections 13.2-13.4, expression admissibility in Section 14, Sections 18.1-18.4,
and Sections 23.2-23.3; the candidate boundary anchors are
[tensor_logic_boundary_policies.md](tensor_logic_boundary_policies.md) Sections 2.5
and 5.6. Implement the verified semantic presentation, not a broader source checker.

Mechanical patches are the code source of truth. Do not hand-transcribe Lean.
Candidate files not yet created in this plan-only tree are shown as monospaced
repository-relative planned paths; use the corresponding patch links for their code.
Use [the authoring record](expression_readiness_authoring_record.md) for provenance,
verification history, telemetry limitations, and final review outcomes.
Final reviews and publication remain controller responsibilities.

## 2. Global constraints and claim boundaries

- Scalar sorts `S` and carrier family `K : S -> Type` remain open.
  The single-carrier prose is the specialization to a singleton sort.
  Heterogeneous primitive signatures are supported; existing backend acceptance
  and production evaluator behavior are unchanged.
- `ScalarOps` supplies operations, not algebraic laws. Native `Float32` and
  `Float` use ordered numerical interpretation, never invented semiring instances.
  Exact Mathlib `Complex` is kernel-checked and noncomputable, not native complex64.
- Shapes are ordered axis metadata using existing `UID` and extents.
  `Coord` is the full product of bounded `Fin` coordinates; rank zero is `Unit`.
  `ArrayShape` excludes rank zero but permits zero extents.
  Metadata retains UID/order; it is not a proof of global source-signature consistency.
- `Layout.enumerate` is a checked `Fin count` equivalence with `Coord`, not an
  unchecked enumeration list. `canonicalLayout` reuses Mathlib `finProdFinEquiv`.
  Complete function arrays choose no backend storage format.
- Declaration keys already belong to `Declarations.Tensor`; signatures are total
  and declaration UIDs injective. Reads retain typed, correctly ranked raw signed
  coordinates, their value-independent policy, resolved outcome, and admission proof.
- `ReadPolicy.inBounds` preserves valid coordinates. `AdmittedRead` excludes
  resolver rejection on its supplied valuation space. Resolved `At` reads use
  the resolved address; typed `Const` contributes no source address.
- Contexts are typed valuation spaces (Gamma), with product binder extensions.
  Guard-admitted contexts can be subtypes. Binder positions are not axis UIDs.
  Index maps and predicates are semantic callbacks, not checked named affine syntax.
  Source well-formedness and its connection to this presentation are supplied premises.
- `Expr.at` accepts an already bounded coordinate map. Declaration references and
  bounded coordinates are expression-level obligations. Complete input binding,
  including checking required empty inputs, is program-level and deferred.
- The public semantic classification paths are `interpret` on complete stores
  and `evalReady` on partial stores. `evalWith` is a low-level helper: its `none`
  conflates an unavailable read with undefinedness when used without readiness.
  Do not present it as an execution-eligibility classifier.
- `evalReady` distinguishes `notReady`, ready undefinedness (`evaluated none`),
  and ready success. This is not a backend error-priority or diagnostic contract.
- Footprints retain duplicate list entries, but membership determines readiness.
  They are sufficient structural dependencies, not minimal dependence claims.
  They traverse every actual binder coordinate and every primitive operand.
- Strictness requires both scalar operands, every actual reduction body, complete
  tabulations, the whole array before selection, and all typed primitive arguments.
  No zero-annihilation, selected-lane-only, or unavailable-value fallback shortcut.
- Empty reductions return the supplied zero without body instances; empty tabulations
  produce complete empty arrays. An outer primitive still applies its own domain rule.

**Explicit exclusions:** named affine syntax checking, parsing or source DSL adapters;
capture-avoiding syntactic substitution and full context reindex/weakening/renaming laws;
proof of all Section 14 judgments; runtime access-rejection ordering; writes, occurrences,
collection, models, publication, ranked scheduling, JAX, and full categorical algebra.
The signed seam is only raw-coordinate equality against an existing realized `StMat`,
not a D-graded functor or a categorical interpretation of the new expression grammar.
Do not add any of these exclusions as extra tasks or silently claim them completed.

## 3. Specification-to-deliverable map

All identifiers below are in `LeanNCD.Semantics` unless otherwise qualified.

| Anchor | Deliverable and limit |
| --- | --- |
| 13.2 | `Ty`, `Value`, `Signature`, dependent `Registry` signatures; open sorts generalize the fixed carrier, without changing backends. |
| 13.3 | `Expr.lit/read/iverson/binary/reduce/tab/at/prim` represent the admitted scalar/array constructors. |
| 13.4 | Product extensions and distinct projections model semantic binding; `nested` versus `nestedSwapped` discriminates binder positions. No syntactic substitution theorem. |
| 14.1-14.2 admissibility | Typed declarations, matching expression types/shapes, bounded selection, `AdmittedRead`, guarded subtype contexts, full binder domains. Source judgments are not implemented as a syntax checker. |
| 18.1 | `interpret` returns `Option (Value K ty)` over a complete typed store; `none` means mathematical undefinedness on this path. |
| 18.2 | Literal/read/Iverson clauses and strict scalar combination; `zeroStrict` pins undefinedness despite a zero operand. |
| 18.3 | Strict reduction and complete Cartesian tabulation; `reduce_defined_iff`, `reduce_empty`, exact sum theorems, and `tab_complete`. |
| 18.4 | `at_some_iff` requires whole-array success; `prim_some_iff` requires all typed arguments, domain truth, and the declared meaning. |
| 23.2 | `footprint` traverses all constructor dependencies; constants have no address, remapped reads use resolved coordinates. |
| 23.3 | `evalWith_stable`, `interpret_stable`, `ready_consistent`, `notReady_iff`, and a mathematical complete-extension witness. Values and undefinedness are covered. |
| Boundary 2.5 | Structurally admitted read side only: valid `At`, typed `Const`, in-bounds preservation, explicit rejection exclusion. Not the full read/write/profile/backend contract. |
| Boundary 5.6 | Expression readiness usable as a future demanded-body premise. No demanded-task set, writes, evaluate-only execution, publication, or completion theorem. |

### Proof acceptance conditions

The proofs must say more than that two wrappers call the same interpreter.

- `sequence_some_iff`: successful dependent sequencing iff each argument equals
  the corresponding successful value.
- `tab_complete`: tabulation equals a complete value iff **every actual coordinate**
  body equals that cell's successful value, for any supplied checked layout.
- `foldValues_defined_iff` and `reduce_defined_iff`: success iff all actual
  inputs/bodies succeed; the latter is vacuous on an empty binder.
- `reduce_empty`: empty reduction succeeds with `ops.zero` independently of its body.
- `foldValues_some_map_sum`, `reduce_sum`, `interpret_reduce_sum`: require ONLY
  `AddCommMonoid` on the selected scalar sort, zero/add agreement with mathematical
  zero and addition, and successful per-body values. No multiplicative laws,
  no laws on every other sort, and no native-float algebraic instance.
  There is NO reverse inference from aggregate equality to individual summands.
- `at_some_iff`: existence of a successful complete array and equality at the
  bounded selected coordinate, not success of a selected body alone.
- `registry_apply_some_iff` and `prim_some_iff`: domain true and meaning equals
  the result; the latter also supplies successful values for every typed argument.
- `evalWith_stable` and `interpret_stable`: store agreement on the resolved
  footprint preserves the entire result, including undefinedness, for all constructors.
- `ready_consistent`: agreement with a complete store on the footprint suffices;
  agreement outside it is unnecessary. `notReady_iff` matches failure of `Ready`.
- `ready_complete_extension`: preserve all available cells and provide a complete
  mathematical store. Its use of `ops.zero` fills only a witness, never a runtime read.

Inspect axiom prints: only standard `propext`, `Quot.sound`, and where needed
`Classical.choice`; no `sorryAx` or added axioms. Leave existing dependency warnings visible.

## 4. Execution preparation and budgets

Start in an isolated execution worktree prepared by the normal new-slice workflow,
which fast-forwards to published local `main`. An artifact-only descendant is also
permitted after the source guards below. The commit
`44296ad56e11b3b296c265119466b91aef8200e0` is verified REHEARSAL provenance,
not a requirement that execution HEAD equal that old commit.
The published plan, patches, and manifest are inherited by normal preparation;
no artifact-copy from the old pin is needed. The authoring branch publishes
artifacts, not candidate implementation files. Do not merge the scratch prototype.

Before patch 00, require a clean git status, the rehearsal baseline as an ancestor
of HEAD, and no baseline-to-HEAD changes to code/configuration/affected guidance or
the listed specification inputs. Status output must be empty; both subsequent
guards must exit zero. Any guard failure, meaningful protected-path diff, or ordered
patch conflict stops execution for controller adjudication: no passive port or rebase.

```bash
/usr/bin/git -C <execution-worktree> status --porcelain
/usr/bin/git -C <execution-worktree> merge-base --is-ancestor 44296ad HEAD
/usr/bin/git -C <execution-worktree> diff --exit-code 44296ad HEAD -- leanncd papers/semantics/tensor_logic_semantics.md papers/semantics/tensor_logic_boundary_policies.md papers/semantics/tensor_logic_semantic_core_spike_record.md
```

In commands below, replace `<execution-worktree>` with the controller's absolute
prepared worktree path. It is a template, not a directory to create literally.
Artifact commands use the delivered files inherited in that execution worktree.
Use separate commands, no shell variables. Ordered `apply --check` remains required
for 00, 01, 02, and 03 against the actual prepared source state.
Do not rerun authoring scratch mutations as a substitute for execution verification.

**Controller preflight, before dispatch 1:** apply
[00-context-preflight.patch](expression_readiness_patches/00-context-preflight.patch).
Files: [leanncd/AGENTS.md](../../leanncd/AGENTS.md) and
`leanncd/AGENTS_REFERENCE.md`.
This reduces root hook sections from 6,957 to 2,882 characters while preserving
the full Patterns section verbatim in the reference. It is budget preparation,
not a fourth semantic task. Confirm the prepared hook remains about 3k characters
or less; the local semantic guidance must also fit that bound.

```bash
/usr/bin/git -C <execution-worktree> rev-parse HEAD
/usr/bin/git -C <execution-worktree> apply --check <execution-worktree>/papers/semantics/expression_readiness_patches/00-context-preflight.patch
/usr/bin/git -C <execution-worktree> apply <execution-worktree>/papers/semantics/expression_readiness_patches/00-context-preflight.patch
/usr/bin/git -C <execution-worktree> add <execution-worktree>/leanncd/AGENTS.md <execution-worktree>/leanncd/AGENTS_REFERENCE.md
```

Controller checkpoints the two preflight files before dispatch 1; do not leave the
reference unstaged for T3 to overlook. Execution commits follow repository style
and include `Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>`.

Read each named symbol with `rg -n` and 40-60-line file windows, not broad exploration.
Each implementer/reviewer/fixer dispatch: at most about 60 turns and 250k peak context.
Slice execution ceiling: approximately 175M cumulative input tokens.
Authoring target: approximately 50M cumulative input tokens, not a measured promise.
Use the repository token report when a matching transcript exists; otherwise report
the unavailable meter and distinguish observed SDK snapshots from aggregate usage.
Surface breaches; never infer compliance from missing telemetry.

T3 may use two fresh dispatches: fixture/public integration, then validation, **the same
task and slice**. Use the split handoff discipline, with exact state, symbols,
remaining commands, and restored-file status. Schedule long validation without
turn-by-turn polling. No mutation may start before all T3 fixture/config patches land.

| Unit | Reviewer-rejectable outcome | Concrete fixture assertions | Manifest cycles | Main risk |
| --- | --- | --- | --- | --- |
| Preflight | Loss of hook guidance or oversized injection | 0 | 0 | Controller prerequisite, not semantic work. |
| T1 | Typed admitted expression representation | 0 | 0 | Semantic callbacks mistaken for a source checker. |
| T2 | Strict interpretation and independent clause/locality proofs | 0 | 0 | Weak wrapper-only proofs or excess exact-sum hypotheses. |
| T3 | Discriminating fixtures and complete public/default integration | 47 (36 guards, 11 theorems) | 27 | All fixtures/config required before cycles; split validation if needed. |

There are 13 evidence fixture categories, not 13 exhaustive semantic judgments.
The two exact-reduction theorem fixtures are included in T3's 11, not additional counts.
Five theorem fixtures test elaboration rejection with `fail_if_success`; they are
structural admission contrasts, not runtime diagnostic tests.

## 5. Task 1: typed admitted expression presentation

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Prerequisite: Section 4 source guards passed on the prepared published-main or
artifact-only-descendant worktree, followed by completed controller preflight 00.
Apply [01-types-expr.patch](expression_readiness_patches/01-types-expr.patch).
No behavioral fixtures or manifest cycles in T1; they depend on later interpretation
and all T3 integration. Compilation is the typed-construction check.

**Files and symbol windows**

- `Axis`, `Shape`, `Coord`, `RawCoord`, `Coord.raw`, `Layout`, `canonicalLayout`,
  `ArrayShape`, `Ty`, `Value`, `ScalarOps`, `Signature`, `Declarations`, `Address`,
  `Cell`, `Store`, `PartialStore`, `ReadOutcome`, `Resolved`, `Resolved.outcome`,
  `ReadPolicy`, `AdmittedRead`, `Registry`, `Registry.apply` @
  `leanncd/LeanNCD/Semantics/Types.lean`.
- `Bin`, `ScalarOps.combine`, `Expr` and its eight constructor names @
  `leanncd/LeanNCD/Semantics/Expr.lean`.

**Prior art/donors:** existing `UID` from
[LeanNCD/Exec/Uid.lean](../../leanncd/LeanNCD/Exec/Uid.lean);
Mathlib `finProdFinEquiv` supplies the coordinate equivalence.
No old fixture is copied here; all concrete construction/rejection cases arrive in T3.

**Reject if:** sorts erased, arrays sparse, layout unchecked, raw coordinates lose
signedness/rank, admission permits rejection, binders use axis identity rather than
product position, or claims exceed structurally admitted semantic forms.

```bash
/usr/bin/git -C <execution-worktree> apply --check <execution-worktree>/papers/semantics/expression_readiness_patches/01-types-expr.patch
/usr/bin/git -C <execution-worktree> apply <execution-worktree>/papers/semantics/expression_readiness_patches/01-types-expr.patch
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd LeanNCD.Semantics.Expr
/usr/bin/git -C <execution-worktree> add <execution-worktree>/leanncd/LeanNCD/Semantics/Types.lean <execution-worktree>/leanncd/LeanNCD/Semantics/Expr.lean
```

Per-task review checks the above outcomes and the actual patch; record its result
and compile status before proceeding. Fixture count 0; mutation count 0.
Commit only the explicit task files, with repository message style and required trailer.

## 6. Task 2: strict interpretation and clause/locality proofs

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Prerequisite: accepted T1. Apply
[02-interpretation-readiness.patch](expression_readiness_patches/02-interpretation-readiness.patch).
Compile the umbrella and all generic proofs. Concrete clause instantiations and
mutation cycles are deliberately deferred to T3, not skipped permanently.
The core proof inventory is 19 named theorems: 5 in `Readiness` and 14 in
`Completeness`. These are generic proofs, not additional concrete fixture assertions.

**Files and symbol windows**

- `sequence`, `foldValues`, `footprint`, `evalWith`, `interpret` @
  `leanncd/LeanNCD/Semantics/Interpret.lean`.
- `evalWith_stable`, `interpret_stable`, `Ready`, `checkReads`, `ReadyResult`,
  `evalReady`, `checkReads_iff`, `ready_consistent`, `notReady_iff` @
  `leanncd/LeanNCD/Semantics/Readiness.lean`.
- `sequence_sound`, `sequence_complete`, `sequence_some_iff`, `tab_complete`,
  `foldValues_defined_iff`, `reduce_defined_iff`, `reduce_empty`,
  `foldValues_some_map_sum`, `reduce_sum`, `interpret_reduce_sum`, `at_some_iff`,
  `registry_apply_some_iff`, `prim_some_iff`, `ready_complete_extension` @
  `leanncd/LeanNCD/Semantics/Completeness.lean`.
- Umbrella imports @ `leanncd/LeanNCD/Semantics.lean`.

**Prior art/donors:** structural induction pattern from `evalWith_stable` and
partial-store agreement in `ready_consistent` @
[TensorLogicSemanticCoreSpike.lean](../../leanncd/LeanNCD/Semantics/TensorLogicSemanticCoreSpike.lean).
New proofs cover typed arrays and dependent heterogeneous operand families;
the old scalar proof is a design donor, not an independent array oracle.
`Completeness` is a separate small module because clause equivalence is a different
obligation from locality/readiness. No behavioral fixtures in this task.

**Reject if:** any condition in Section 3's proof acceptance list is weakened,
selected coordinates bypass complete arrays, primitive arguments are non-strict,
empty domains evaluate phantom bodies, locality drops undefinedness, `evalWith`
is documented as a classifier without preconditions, or witness zero becomes fallback.

```bash
/usr/bin/git -C <execution-worktree> apply --check <execution-worktree>/papers/semantics/expression_readiness_patches/02-interpretation-readiness.patch
/usr/bin/git -C <execution-worktree> apply <execution-worktree>/papers/semantics/expression_readiness_patches/02-interpretation-readiness.patch
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd LeanNCD.Semantics
/usr/bin/git -C <execution-worktree> add <execution-worktree>/leanncd/LeanNCD/Semantics/Interpret.lean <execution-worktree>/leanncd/LeanNCD/Semantics/Readiness.lean <execution-worktree>/leanncd/LeanNCD/Semantics/Completeness.lean <execution-worktree>/leanncd/LeanNCD/Semantics.lean
```

Per-task review checks exact hypotheses and axiom output, not only a green build.
Fixture count 0; mutation count 0. Record accepted proof scope before proceeding.

## 7. Task 3: fixtures and public/default integration

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Prerequisite: accepted T2. Apply the ENTIRE
[03-fixtures-integration.patch](expression_readiness_patches/03-fixtures-integration.patch)
before any manifest check or cycle. Its three coherent work items are:
(1) strict expressions/binders/arrays and clause instantiations;
(2) boundary/type-admission/categorical contrasts;
(3) native carriers and public/default discovery, followed by controller validation.

**Files and symbol windows (also the phase-2 validation handoff list)**

- `Carrier`, `ops`, `registry`, `strictPolicy`, `constantPolicy`, `wrapPolicy`,
  `direct`, `constRead`, `remapRead`, `store`, `partialStore`, `zeroStrict`,
  `emptyReduction`, `emptyTab`, `outsideEmpty`, `nullary`, `heterogeneous`,
  `strictArgument`, `tabulated`, `selected`, `nonselectedUndefined`, `arrayPrimitive`,
  `nested`, `nestedSwapped`, `scalarObservation`, `readyObservation` @
  `leanncd/test/Semantics/ExpressionTest.lean`.
- `Guarded`, `guardedRead`, `dtype_mismatch_rejected`, `shape_mismatch_rejected`,
  `unknown_tensor_rejected`, `invalid_coordinate_rejected`, `unknown_index_rejected`,
  `scalarTensor`, `axis_identity_and_order`, `cartesianTab`, `cartesianSelect`,
  `reduction_exact_bound_values`, `empty_reduction_exact_without_body`,
  `nonselected_lane_obligation`, `signedRaw`, `existing_stmat_seam` @
  `leanncd/test/Semantics/ContractTest.lean`.
- `unaryRegistry`, `rounding`, `reciprocal`, `fn32`, `fn64`, `ops32`, `ops64`,
  `result32`, `result64`, `complexOps`, `complexSquare`, `complex_square` @
  `leanncd/test/Semantics/NativeTest.lean`.
- Root import @ [LeanNCD.lean](../../leanncd/LeanNCD.lean);
  default `Tests` globs @ [lakefile.toml](../../leanncd/lakefile.toml).
- Downlink @ [leanncd/AGENTS.md](../../leanncd/AGENTS.md);
  scope/classification guidance @ [Semantics/AGENTS.md](../../leanncd/LeanNCD/Semantics/AGENTS.md);
  historical coverage qualification @
  [tensor_logic_semantic_core_spike_record.md](tensor_logic_semantic_core_spike_record.md).

### Fixture requirements and donors

Counts: `ExpressionTest` 23 guards; `ContractTest` 8 guards and 10 theorem fixtures;
`NativeTest` 5 guards and 1 theorem fixture. Total 36 guards + 11 theorems = 47.
Three `#eval` observations and five axiom-print commands are not extra fixtures.
Unless a donor is explicitly named below, these are NEW specification fixtures,
not clones of an old source fixture. Preserve the verified patch constructions.

| Cases / identifiers | Required discrimination or observed assertion | Donor |
| --- | --- | --- |
| `direct`, `scalarTensor` | Vector coordinate 1 gives 5; rank-zero tensor gives 17. | New specification fixtures. |
| `constRead`, `remapRead` | Raw -1: constant 9/no footprint versus wrapped coordinate 2/value 7/footprint [2]. | New boundary fixtures. |
| `partialStore`, `readyObservation` | Only coordinate 0 is available; remapped 2 is `notReady`, never its raw-to-Nat coordinate 0 or zero. | Spike `partialStore` design donor. |
| `zeroStrict`, `strictArgument` | Zero times reciprocal zero is undefined; ready undefined is not waiting; false mixed flag cannot suppress undefined rational argument. | Spike `zeroStrict` design donor; mixed primitive new. |
| `emptyReduction` | Unreachable undefined body succeeds with zero. | Spike `emptyBad` design donor. |
| `emptyTab`, `outsideEmpty` | Successful empty array/no reads; outside primitive's own false domain still rejects it. | New specification fixtures. |
| `nested`, `nestedSwapped` | Different binder projections give 42 versus 28. | New specification fixtures. |
| `cartesianTab`, `cartesianSelect` | 2x3 complete array; selection (1,2) gives 14 and footprint length 6. | New specification fixtures. |
| `selected`, `arrayPrimitive`, `nonselectedUndefined` | Values 6 and 8; selecting defined lane 0 cannot bypass undefined lane 1; partial array cannot be selected as complete. | New specification fixtures. |
| `nullary`, `heterogeneous` | Nullary value 13; rational 4 plus true flag gives 14; complete array argument preserved. | New dependent-signature fixtures. |
| Five rejection theorems; `axis_identity_and_order` | Wrong sort, shape, undeclared key, invalid `Fin`, and unavailable context projection fail elaboration; axis reordering remains distinct. | New structural fixtures, not a source checker. |
| `guardedRead`, `strictPolicy`, `existing_stmat_seam` | Guarded i+1 gives 5/7; raw 3 and -1 reject; signedRaw(2)=-1; actual old `StMat` raw-coordinate equality. | Guard fixtures new; spike `signed_coordinate`, `integerCoordinate_eq` reused. |
| `result32`, `result64`, `fn32`, `fn64` | (2^24+1)-2^24: bits 0 versus 0x3ff0000000000000; reciprocal(2) bits 0x3f000000/0x3fe0000000000000; f32 reciprocal(0) undefined. | Spike `roundingExpr`, `rounding32/64`, `valueBits32/64`, native reciprocal guards over `readSeven`, `float32Ops/floatOps`. |
| `complex_square` | Exact Mathlib I*I=-1, kernel checked, not executed complex64. | Spike `complexOps`/Mathlib `Complex.I_mul_I` design donor. |
| Exact reduction theorems; `nonselected_lane_obligation` | Conditional sum over every bound read; empty sum without a body; `tab_complete` independently forces failure at lane 1. | New clause instantiations; rational operations/store pattern from spike `rationalOps`/`exactStore`. |

All spike donors are identifiers @
[TensorLogicSemanticCoreSpike.lean](../../leanncd/LeanNCD/Semantics/TensorLogicSemanticCoreSpike.lean).
Native wrappers reuse actual `UnaryOp.applyChecked`/`applyChecked32` @
[LeanNCD/Eval/Error.lean](../../leanncd/LeanNCD/Eval/Error.lean).
No existing numerical backend fixture is promoted into an additivity oracle.

### Unchanged siblings and discoverability audit

This introduces a separate semantic layer, not a repair of every evaluator sibling.
Audit the interfaces below; do not silently retrofit their different contracts.

| Case | Required in new layer | Forbidden inference / unchanged sibling boundary |
| --- | --- | --- |
| Missing resolved read | `evalReady` returns `notReady`. | Low-level `evalWith none` alone is not a classifier; witness filling is not fallback. |
| Ready primitive failure | `evaluated none`; stability preserves failure. | Not missing input, boundary `Reject`, or successful zero. |
| Empty binder / nullary call | No phantom body/operand reads; primitive domain still applies. | No waiver of unconditional program input/configuration obligations. |
| Complete array selection | Every body and its footprint are required. | No selected-lane-only interpretation. |
| Scalar/native reuse | Existing checked unary APIs and old spike witnesses reused. | No backend acceptance changes or float algebraic laws. |
| Old spike `eval`, `evalReady`, `footprint` | Keep existing scalar/`Except` implementation unchanged. | Do not equate its diagnostics with the new `Option`/readiness API. |
| Source syntax / writes / publication | Explicitly deferred supplied premises or later program work. | Not silently ignored admitted judgments or claimed correspondence. |

After T3, `import LeanNCD` reaches the new umbrella. Default `Tests` registers
all THREE new modules. `ContractTest` imports the old spike for its actual `StMat`
witness, so default tests now check the spike INDIRECTLY. Root `LeanNCD` still
does not import the spike. Preserve the coverage qualification in the historical
record and guidance; do not repeat a non-default-only coverage claim.

### Apply, build, sweep, then verify

```bash
/usr/bin/git -C <execution-worktree> apply --check <execution-worktree>/papers/semantics/expression_readiness_patches/03-fixtures-integration.patch
/usr/bin/git -C <execution-worktree> apply <execution-worktree>/papers/semantics/expression_readiness_patches/03-fixtures-integration.patch
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd Semantics.ExpressionTest Semantics.NativeTest Semantics.ContractTest
rg -n "8,676|8676|8,686|8686|default builds do not typecheck|non-default.*only" <execution-worktree> --glob '*.md'
rg -n "complex64|semiring|substitution|evalWith|TensorLogicSemanticCoreSpike" <execution-worktree>/leanncd/LeanNCD/Semantics/AGENTS.md <execution-worktree>/papers/semantics/tensor_logic_semantic_core_spike_record.md
/usr/bin/git -C <execution-worktree> add <execution-worktree>/leanncd/test/Semantics/ExpressionTest.lean <execution-worktree>/leanncd/test/Semantics/NativeTest.lean <execution-worktree>/leanncd/test/Semantics/ContractTest.lean <execution-worktree>/leanncd/LeanNCD.lean <execution-worktree>/leanncd/lakefile.toml <execution-worktree>/leanncd/AGENTS.md <execution-worktree>/leanncd/LeanNCD/Semantics/AGENTS.md <execution-worktree>/papers/semantics/tensor_logic_semantic_core_spike_record.md
```

Classify sweep matches as current, explicitly historical, or stale; retain accurate
historical build counts. Documentation sweep is part of T3, not a heavy new dispatch.
Reject T3 if any discriminating construction is weakened, default discovery is missing,
type controls are called runtime checking, or the narrow signed seam is overstated.

## 8. Mutation protocol and controller completion gates

Use ONLY [expression_readiness_mutations_post.json](expression_readiness_mutations_post.json).
All 27 entries have verification task `3`; `owner_task` explains where source was added,
not when a cycle may run. No pre manifest is needed: candidate implementation is new.
Observed `expect` strings are supplied by the manifest; do not derive replacements or
diagnostic line numbers. A passing cycle requires intended failure, green restoration,
and byte-identical restored files. Generic proofs may detect a mutation before a guard.

| Class | Count | Manifest labels |
| --- | --- | --- |
| Implementation/proof | 11 | `read-footprint`, `const-footprint`, `resolved-versus-raw`, `missing-default`, `operand-undefined`, `empty-identity`, `bound-footprint`, `tab-footprint`, `selection-footprint`, `whole-array-obligation`, `primitive-undefined-operand` |
| Type-admission contrast controls | 5 | `dtype-admission`, `shape-admission`, `unknown-admission`, `coordinate-admission`, `scope-admission` |
| Fixture/registry/metadata contract perturbations | 11 | `read-value`, `empty-primitive-domain`, `binder-position`, `nullary-domain`, `heterogeneous-operand`, `axis-order`, `guard-coordinate`, `strict-reject`, `signed-seam`, `native-rounding`, `complex-operation` |

The admission controls replace illegal terms with legal neighbors inside
`fail_if_success`: their expected failure verifies the control, not an implementation
regression. Fixture perturbations test discriminating contracts, not 11 additional
source-code bugs. Do not report all 27 as implementation regressions or as exhaustive
individual mutation coverage of all 47 assertions.

Preserve the strengthened anchors: constant-footprint mutation is well typed with a
positive layout-count guard; raw-versus-resolved uses toNat **before** modulo to differ
at raw -1; missing-default targets actual `evalReady`; primitive-undefined-operand
bypasses source argument sequencing. Do not replace them with ill-typed/no-op mutations.

After all T3 patches and targeted checks, the CONTROLLER runs:

```bash
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --check --task 3 <execution-worktree>/leanncd <execution-worktree>/papers/semantics/expression_readiness_mutations_post.json
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --task 3 --out <execution-worktree>/papers/semantics/expression_readiness_execution_mutation_results.md <execution-worktree>/leanncd <execution-worktree>/papers/semantics/expression_readiness_mutations_post.json
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd
```

`--check` alone is insufficient. Keep the execution results artifact out of task code
commits unless the controller explicitly publishes it. Full default build must include
all three semantic modules and indirect old-spike coverage; do not suppress warnings.

Require two DISTINCT whole-branch review lenses after implementation:

1. **Semantic/proof fidelity:** specification map and exclusions, strictness/emptiness,
   independent clause theorems, exact hypotheses, values plus undefinedness,
   complete-extension versus runtime fallback, and discriminatory fixtures.
2. **Types/backend/categorical/reuse:** sort/shape/declaration/admission boundaries,
   bounded coordinates and metadata scope, native checked API reuse and precision,
   exact/noncomputable Complex, narrow actual `StMat` seam, public/default discovery,
   untouched production siblings, and qualified historical coverage.

Reviewers use named symbols and 40-60-line windows, record findings incrementally
in controller session artifacts, and report budget headroom. No broad re-exploration.
Fixes are one bounded dispatch per finding group; verify changed fixtures/anchors
and replay affected cycles, then the controller reruns final full gates as needed.

Completion requires accepted per-task outcomes, actual 27/27 controller cycles,
green full default build, both final reviews clean or findings explicitly adjudicated,
and candid budget/telemetry reporting. Parent controls publication/integration;
this authoring dispatch performs none. No task ships `File.lean:NNN` citations,
uncompiled Lean snippets, silent skips, or claims that deferred program semantics are proved.

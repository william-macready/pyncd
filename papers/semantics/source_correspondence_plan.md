# Source correspondence + differential debugging: first complete slice

## 1. Status and front gate

**Full path: new source capability and proof surface. DESIGN PLAN WITH VERIFIED
PARTIAL PROTOTYPE; NOT EXECUTION-READY.** Authoring Phase B, 2026-10-08.
Production stays unchanged. This is one plan for the first complete slice:
UID-based source elaboration, pure-einsum correspondence, source-linked
diagnostics, and differential tests for bounded scalar read sum-products.

**Do not dispatch implementation from this document yet.** These required seams
have not been prototyped:

- True UID-keyed dependent valuations, their coordinate bijection, and
  capture-avoiding generated-binder renaming/index substitution.
- Automatically computed term support partitions and a resolved production-AST
  adapter with explicit tensor roles, multiple statements, and stable provenance.
- General multi-tensor elaboration, tag-preserving statement permutation, and
  complete computational source-generated schedules.
- Public diagnostic/differential APIs, independent input packing/oracle tests,
  the exact production numerical profile, and implementation-mutation kills.

Readiness completion must rehearse these seams on the real module split, emit
new per-task patches, observe every new fixture family, mutate implementations,
and pass the two review lenses below. The retained patches are seed evidence,
**not** a recipe to apply three patches and declare this slice finished.

Authority: corrected [semantics](tensor_logic_semantics.md), Proposition 19.1;
[roadmap](lean_executable_semantics_path.md); retained
[semantic evidence](source_correspondence_artifacts/evidence.json) and
[production observations](source_correspondence_artifacts/production_evidence.json).
Receipts and limitations belong in the separate
[record](source_correspondence_record.md), not this live execution plan.
No Lean snippets are transcribed here. The compiled seed is
[patch 1](source_correspondence_patches/0001-feat-semantics-prototype-UID-contexts-and-core-contr.patch),
[patch 2](source_correspondence_patches/0002-feat-semantics-prototype-pure-einsum-Program-corresp.patch),
and [patch 3](source_correspondence_patches/0003-test-semantics-verify-rational-source-correspondence.patch).

## 2. Accepted endpoint and hard scope

The future public import is `LeanNCD`. A caller supplies a resolved finite source
program, explicit tensor roles/shapes, all declared inputs, and optional debug
fuel. Admission either returns a typed, source-linked error or an existing typed
`Program` plus identity/provenance maps and a deterministic complete `Schedule`.
The rational core accepts arbitrary rationals; production comparison has a
separate restricted numerical profile.
`compareSource` additionally accepts an independently checked fixture dependency
order for its exact acyclic oracle leg. That order is not borrowed from production
scheduling; without one, the oracle leg reports an explicit unavailable reason.

The adapter accepts scalar `.sum` / `.identity` assignments with read factors
only, finite pinned domains, bounded reads, and ordered UID slots. It computes
each term's contracted UIDs independently. Standard pure einsum is identified
separately from general read-only broadcasting. Repeated read/output slots,
diagonal writes, and duplicate additive terms are legitimate. Empty sum and
empty product lists are direct AST/core identity cases; do not invent parsed
numeric literal syntax. Existing `Factor` has read, iverson, and unary-function
forms, not numeric literals.

Multiple definitions contribute separately in the reference collection model.
All defined coordinates, including nonoutputs and unwritten cells, have
publication keys. A successful reached execution implies the existing whole-store
model through `result_model`; it is not merely an output-array comparison.
An optional rank certificate can establish stronger progress results, but is
not required to start a core debug run. Unranked runs may honestly block.
Debug fuel may exhaust; neither blocking nor exhaustion is a no-model claim.
Any failure/no-model claim must use the existing reached-state theorem, not a
renderer-created or arbitrary failed snapshot.

**Excluded:** scans, marked arrays/slices, affine writes, nonlinear primitives,
guards/Iverson factors, native floats in the semantic core, backend proofs,
dimension inference, parser changes, dense-storage refinement, general schedule
search/rank synthesis, full source-expression substitution, and production fixes
or new production tracing. No general floating-point correctness or bitwise
schedule-independence claim. Unsupported forms get explicit typed refusal.

## 3. Interfaces and proof obligations

### 3.1 UID contexts, binding, and provenance

A context has unique resolved UIDs and a finite domain for each UID. A UID
valuation assigns a member of that UID's domain, not a value at a list position.
Prove a two-sided bijection to the typed `Coord` for the chosen enumeration.
Reordering enumeration transports valuations; equal names never merge UIDs.
Repeated slots reference one UID valuation. Rename the seed's positional
`NamedVal` / `namedEquiv` to explicitly positional names; do not keep a
misleading public compatibility alias.

Generated reduction binders alone may be alpha-renamed. Use an injective,
domain-preserving UID transport; choose fresh generated identities outside the
entire finite source/output/free/generated support. Prove freshness, absence of
capture, and interpretation preservation. Index substitution is a pullback of
UID assignments along a domain-preserving map, including repeated lookup slots.
Reject domain-changing substitutions. This is not a theorem about arbitrary
DSL expressions, nonlinear binding, or all source substitution.

Attach original statement ordinals **before** any grouping or reordering.
Term/factor/slot ordinals are within that original statement. Maintain inverse
maps between original identities and target-local typed statement tags.
Tensor addresses carry stable tensor UID and ordered coordinate values.
Axis identity comes from existing `assignUIDs` / `resolveDecls` results: never
remint an already resolved UID using its display name. Tensor-name bindings map
to a stable declaration-identity table; they are not an excuse to match axes by
name. Raw name resolution's intentional name binding is distinct from semantics
over already resolved UIDs. Same-name/distinct-UID core cases need not be
expressible through the name-based front end.

The adapter entry is a resolved snapshot plus roles/shapes/input bindings.
The convenience raw-`TLProgram` entry obtains that snapshot through existing
resolution. Validate the accessible resolution seam in readiness rehearsal;
no duplicate resolver or production modification is authorized.
AST nodes have no source spans: report original IDs, never fabricated locations.

### 3.2 Admission and support partition

For each statement, enumerate distinct output UIDs in first-slot order, retaining
the full destination slot list separately. For each term, collect read support
and compute contracted support as read UIDs minus output UIDs. Order contracted
UIDs deterministically from the resolved context. Prove disjointness, exact
coverage, and preservation of each read/output projection.
Standard pure classification requires every output UID in that term's read
support; output-only terms are general broadcast, not silently dropped.
Empty identity terms use the same explicit classification.

Require equality of **full slot domains**, not overlap or common-prefix bounds.
Repeated output UIDs share a value but retain repeated destination slots.
Keep tensor role, logical domain, input shape, and buffer-length validation
separate; all declared inputs must be present, including unused/empty tensors.
No production zero-padding is imported into semantic read admission.

T2 must deliver a case-by-class audit: required / forbidden / silently ignored
for axis/tensor/binder declarations, output slots, read slots, support, roles,
inputs, and unsupported forms. Audit siblings `resolveRef`, `resolveSlots`,
`admitRead`, `admitTerm`, `admitOutput`, and `admitPure` from the seed; compare
existing structural resolution, `gatherRead`, and checked input signatures.
Each silently ignored cell is resolved or explicitly refused before readiness.
Pin validation order with a case violating domain and rank/input constraints
simultaneously; assert the documented first error and its original slot identity.

### 3.3 Elaboration, collection, and schedule

Lower into the **existing** typed expression/program machinery. Each term gets
its own product and nested `Expr.reduce` binders; only then are terms added.
Every read uses bounded `AdmittedRead`. Prove body interpretation and read
footprint agree with the admitted source term; guard is true for this fragment;
destination is the ordered source projection. Roles determine input/defined/
output sets, not the seed's single-target rule.

For statement permutation, construct a bijection on tagged occurrences and use
`Program.collect_relabel`. Connect bodies, footprints, guards, destinations,
and original-ID maps through that bijection. Do not deduplicate identical
statements or contributions. Collection and final model invariance do not imply
trace/event order invariance.

Construct finite schedules computationally: deterministic tensor declaration-UID
order, target-local tagged statements, lexicographic valuations, and every
defined tensor's full canonical coordinate domain. Prove coverage and nodup for
both occurrence and publication keys, and tensor-list coverage/nodup.
Use finite canonical layouts and `List.finRange`, not `Classical.toList` or a
noncomputable enumeration in an executable definition. A nonoutput intermediate
and a defined tensor with no statements must still be published.
Call unranked `runValidated` with validated inputs; reuse its actual endpoint and
soundness. Default finite-budget coverage and optional ranked progress remain
separate obligations; do not manufacture a rank/model witness to start execution.

### 3.4 Proposition 19.1 bridge

Generalize the seed's genuine `pure_correspondence`, not its one-target wrapper.
The left side is collection of the **actual checked normalized nested-reduction
body**. The right side is an independently specified global-fiber sum of operand
products over UID valuations, filtered by the ordered destination projection.
The global formula must not be defined as the lowering/collection result.

Prove the output/contracted valuation partition equivalence, product and nested
reduction interpretation, occurrence relabeling, finite-sum reindexing, and then
the statement/program collection equation. Handle rank zero, zero extents,
repeated output slots/empty fibers, and per-term contraction domains explicitly.
Use the appropriate generic semiring result, specializing to exact `Rat`.
Do not install or assume a floating-point `AddCommMonoid` to reuse that theorem.
Machine completion connects through existing `result_model` / denotation
results, not a theorem that merely unfolds two identical definitions.

## 4. Diagnostic and differential contract

Proposed public typed interfaces, finalized and compiled during readiness:
`admitSource`, `elaborateSource`, `sourceSchedule`, `runSourceDebug`,
`renderSourceDiagnostic`, and `compareSource` in the future semantic modules.
Return data first; rendering does not control execution or erase typed causes.

| Variant | Mandatory payload |
|---|---|
| Semantic admission rejection | Stage, typed cause, declaration/statement/term/factor/slot origin as applicable, offending UID, expected/actual domain/shape/length |
| Unsupported source / shared-fragment refusal | Exact unsupported form or profile condition; preserve semantic result if reference accepted |
| Complete | Actual reached result, events, all defined published cells, source identity maps |
| Failed | Actual ready-undefined occurrence and pre-failure snapshot, source identity, reachedness evidence only where present |
| Blocked | Actual blocked snapshot, pending keys/missing reads, no no-model inference |
| Exhausted | Actual snapshot, remaining eligible work and fuel, no no-model inference |
| Production compile / preparation / runtime failure | Leg and phase, original typed cause, original warnings, source mapping if available |
| Shape / value discrepancy | Compared legs, tensor UID, exact shapes/lengths, first actual differing coordinate and both observed values/encodings |
| Known contract difference | Explicit nonshared condition, both observations where run, no parity-success label |
| Unsupported numerical profile | Failed exact-integer/envelope check and offending input/intermediate, never tolerance success |

Event/observation data includes stable address/tensor UID, original statement ID,
target-local tag, output valuation assignments as `(UID, value)`, event kind and
payload, contribution value/undefinedness, and missing-read addresses.
Where term evaluation is observed, include that term's contracted assignments
and factor/slot origins; otherwise mark unavailable instead of inventing them.
Keep display names optional metadata. No fake spans, guessed term attribution,
or generic success string replacing an original cause.
A failed occurrence is ready, so its own footprint has no missing reads.
This read-only source fragment has no partial primitives: reached ready-undefined
failure coverage remains in the existing generic core tests, not a fabricated
source failure. Renderer protocol fixtures must not claim such reachability.

Compare canonical **per-occurrence contributions** using original statement ID
and UID assignments, and compare final published cells by address. Do not zip
traces by event index: valid executions can order events differently.
Canonical tensor/coordinate order defines "first differing cell".
Shape/length mismatches precede value comparison; do not truncate with `zip`.
Backend environments contain inputs too: compare declared result bindings and
report missing/extra bindings separately rather than treating an input as output.

Localization is evidence-limited. Body, collection, readiness, publication, and
backend-arithmetic layers each return observed agreement/disagreement or
`unobserved`. Production exposes outputs/errors here, not semantic event hooks.
Its first differing output is observable; a supposed first body/readiness/
arithmetic cause is **unobserved** unless an actual existing hook supplies it.
Do not modify production to make a prettier diagnostic.

### 4.1 Four differential legs and independence

1. Independent canonical global-fiber exact oracle: direct resolved UID
   assignment enumeration, slot lookup, products, and fiber sums.
2. Actual rational admitted-core executor with the generated complete schedule.
3. Legacy `TLProgram.eval`.
4. Checked `prepareEvalPlan` then `runPreparedDense`, preserving compile/preparation
   distinctions and warnings.

The runtime oracle may share validated source data, not the lowering, bridge
implementation, production contraction/shape helpers, or dense indexing helpers.
Its packing/index formula is independently tested using asymmetric axes and
nonuniform cells. Establish oracle vs core while elaboration is in flux, before
adding production comparison. Pin theorem-to-runtime correspondence separately.
The global-fiber formula takes a total store; it is not itself a solver for
cyclic source programs. Acyclic differential fixtures supply an explicit
fixture dependency order for independent exact evaluation. Blocked/cyclic debug
cases test observed reference outcomes; unavailable final-value oracle/backend
legs carry explicit reasons and never count as four-leg parity. No model witness
or general scheduling/rank synthesis is added to make those cases compare.

The shared production fragment has explicit f64 declarations for **every** real
read/written tensor name, pinned finite domains, bounded read-only sum-products
with `.sum` / `.identity`, and one definition per target.
Diagonal writes and within-statement duplicate terms are REQUIRED members.
Unique lhs permits mapping original IDs in this fragment; attach IDs before
compilation. Reference-only multiple definitions retain every original ordinal.
Production overwrite behavior across statements is a known contract difference,
not an excuse to alter reference collection or fix production.

### 4.2 Exact numerical envelope

Never convert arbitrary rationals to `Float` and accept `approxEq`.
Production-comparable inputs are integers, with only finite addition and
multiplication. Check at runtime that each exact intermediate has absolute value
at most `2^20`, not just final outputs. Use explicit f64 source declarations.
Check input bounds and a conservative absolute-product/partial-sum bound as well
when production's intermediate order is opaque: cancellation or multiplication
by a later zero must not hide an oversized earlier intermediate. The bound
must cover all involved factors and contraction/collection additions.
If that safety check cannot certify a case, return unsupported numerical profile.

Binary64 represents these bounded integers exactly. Independently encode each
expected integer to binary64 and compare exact shape, buffer length, and every
cell's `Float` bits. Normalize numeric zero to prescribed positive-zero encoding
on both comparison sides; retain original bits in diagnostic payloads.
Use a nonnegative base corpus and separate negative/zero-policy fixtures.
This is a checked test profile, not a general backend refinement or schedule
independence theorem. Arbitrary rational core runs remain available.

## 5. Task graph, files, and bounded dispatches

All paths in this section are repository-relative. Existing donor/core/production
paths are checked in the planning tree. The entire `Semantics/Source/` tree and
`SourceCorrespondenceTest.lean` are **future outputs**, present only in the seed
patches. Additional proposed files below do not yet exist.
Production DSL/Eval files are read-only donors, not mutation targets.

| Task | Prerequisites | Three implementation work items | Planned fixtures / implementation cycles | Risk / split |
|---|---|---|---|---|
| T1 UID binding | None | UID bijection; scoped rename/pullback; positional rename + proofs | 8 / 4 | High; implementation then fixtures |
| T2 admission/AST | T1 | Resolved/provenance adapter; support/domain admission; roles/input validation + audit | 18 / 8 | High; implementation then fixture bundles |
| T3 Program/schedule | T1, T2 | Multi-target lowering; permutation bijection; computational complete schedule/run | 12 / 6 | High; implementation then fixture bundles |
| T4 correspondence | T1, T2, T3 | Independent fiber/partition; actual body bridge; collection/model specialization | 8 / 4 | High; proof then fixtures |
| T5 diagnostics/harness | T2, T3, T4 | Typed observations; source renderer; four-leg/profile comparison | 15 / 8 | High; API then fixture bundles |
| T6 corpus/review/docs | T1, T2, T3, T4, T5 | Deterministic corpus; implementation cycles; integrated review/docs | 18 / 9 | High; corpus bundles then integration |

Totals: **79 named fixture entrypoints and 39 implementation-mutation cycles**,
all planned/unobserved. F16 additionally expands exactly 18 generated cases.
These counts do not include the six completed fixture-input contrasts.
No fixture dispatch takes more than three numbered fixture IDs/families.
Split larger tasks into successive bundles of at most three; a reviewer may
reject a task independently of its neighbor. No dispatch owns all of T2/T5/T6.
Use the [split handoff](../../.claude/skills/slice-plan/split-handoff-template.md).

### 5.1 File/symbol briefs

Read 40-60-line windows around these identifiers with `rg -n`; never whole-file
reads over 20k characters. Seed symbols refer to compiled patches, not current
planning-tree definitions. Proposed identifiers are specifications, not verified
exports. Final readiness briefs must replace proposed locators with observed ones.

- **T1:** seed `Context`, `Ref.get`, `resolveRef`, `Slots.project`, `NamedVal`,
  `namedEquiv`, `appendEquiv` @ `leanncd/LeanNCD/Semantics/Source/Context.lean`;
  proposed `UIDVal`, `uidCoordEquiv`, `renameBinders`, `indexPullback` @ same file.
  Tests: future `leanncd/test/Semantics/SourceBindingTest.lean`.
- **T2:** seed `admitRead`, `admitTerm`, `admitOutput`, `admitPure` @
  `leanncd/LeanNCD/Semantics/Source/Admission.lean`;
  proposed `resolveSource`, `SourceOrigin`, `supportPartition` @ future
  `leanncd/LeanNCD/Semantics/Source/Adapter.lean`;
  `assignUIDs` / resolution seam @ `leanncd/LeanNCD/DSL/Pipeline/Structural.lean`;
  `Factor` @ `leanncd/LeanNCD/DSL/Ast.lean`.
  Tests: future `leanncd/test/Semantics/SourceAdmissionTest.lean`.
- **T3:** seed `product`, `contract`, `interpret_contract` @
  `leanncd/LeanNCD/Semantics/Source/Lowering.lean`;
  `elaborate`, `occurrenceEquiv`, `collect_elaborate` @
  `leanncd/LeanNCD/Semantics/Source/Statement.lean`;
  existing `Program.collect_relabel` @ `leanncd/LeanNCD/Semantics/Program.lean`;
  proposed `elaborateSource`, `sourceSchedule` @ future
  `leanncd/LeanNCD/Semantics/Source/Program.lean`;
  existing `runValidated`, `result_model` @
  `leanncd/LeanNCD/Semantics/ReferenceExecutor.lean`.
  Tests: future `leanncd/test/Semantics/SourceProgramTest.lean`.
- **T4:** seed `canonicalFiber`, `pure_correspondence`, `interpret_sumBody` @
  `leanncd/LeanNCD/Semantics/Source/Statement.lean`;
  proposed generalized correspondence @ future
  `leanncd/LeanNCD/Semantics/Source/Correspondence.lean`.
  Tests: future `leanncd/test/Semantics/SourceCorrespondenceTest.lean`.
- **T5:** proposed `runSourceDebug`, `renderSourceDiagnostic` @ future
  `leanncd/LeanNCD/Semantics/Source/Diagnostics.lean`;
  `compareSource` @ future `leanncd/LeanNCD/Semantics/Source/Differential.lean`;
  existing `TLProgram.eval` @ `leanncd/LeanNCD/Eval/Entry.lean`,
  `prepareEvalPlan` @ `leanncd/LeanNCD/Eval/Plan/Compile.lean`,
  `runPreparedDense` @ `leanncd/LeanNCD/Eval/Plan/Adapter.lean`.
  Tests: future `leanncd/test/Semantics/SourceDiagnosticTest.lean`.
- **T6:** proposed independent oracle/corpus @ future
  `leanncd/test/Semantics/SourceDifferentialTest.lean`;
  import/default targets @ existing `leanncd/LeanNCD.lean`,
  `leanncd/LeanNCD/Semantics.lean`, `leanncd/lakefile.toml`, future
  `leanncd/LeanNCD/Semantics/Source.lean`; discoverability @ existing
  `leanncd/AGENTS.md`, `leanncd/LeanNCD/Semantics/AGENTS.md`;
  additive plan link @ `papers/semantics/lean_executable_semantics_path.md`.

Introduce the independent oracle in T3's fixture phase, extend it in T4/T5,
and consolidate in T6; do not postpone independence testing until close-out.
Default/public imports and minimal test targets are wired as each module lands.
No refactor of existing executor or production behavior is authorized.

## 6. Fixture matrix and implementation mutations

Donor notation below names identifiers and files, including patch-only donors.
Each row is one named fixture entrypoint; sub-assertions do not increase counts.
Clone the donor and make the stated change. New expected values/errors must be
observed during readiness completion; none of these planned rows is a receipt.

Donors:
- **M:** `matrixShapes`, `matrixStore`, `pureRun`, `sameName` @
  `leanncd/test/Semantics/SourceCorrespondenceTest.lean` (seed patch 3).
- **S:** `scalarStore`, `pureRun` @ that seed file.
- **E:** `emptyShapes`, `emptyStore`, `pureRun` @ that seed file.
- **W:** `diagonalShapes`, `diagonalStore`, `pureRun` @ that seed file.
- **B:** `biasRun`, `biasShapes`, `biasStore` @ that seed file.
- **A:** `checkAdmission`, `diagnostic`, `resolveSlots` calls @ that seed file.
- **C:** `vectorProgram`, `collision` @
  `leanncd/test/Semantics/CollectionModelTest.lean` (retained donor inventory).
- **X:** `program`, `schedule`, `summarize`, `checkSmoke` @
  `leanncd/test/Semantics/ExecutableReferenceTest.lean` (retained inventory).
- **N:** `direct`, `nested` @ `leanncd/test/Semantics/ExpressionTest.lean`
  (retained inventory).
- **P:** `compare`, `rhs`, `mkAxis`, `dense`, `renderCause` @
  [production_probe.lean](source_correspondence_artifacts/production_probe.lean);
  select its named `compare` invocation below, not nonexistent fixture functions.

| ID | Clone/change | Requirement pinned |
|---|---|---|
| V1 | M; unequal assignments to same-name distinct UIDs | Real UID lookup, not positional/name aliasing |
| V2 | M; repeat one UID in both read slots | Shared assignment/diagonal |
| V3 | M; reverse context with unequal extents and values | Two-sided valuation/Coord transport |
| V4 | M; domain-preserving generated-UID renaming | Interpretation invariant, metadata transported |
| V5 | B; requested binder name/UID collides with free/output support | Freshening avoids capture |
| V6 | A; substitute UID with unequal full domain | Typed domain-changing rejection |
| V7 | M; same-domain pullback to a different UID | Legal substitution neighbor |
| V8 | S/E; empty context then a zero-extent context | Unique empty valuation vs no valuation |
| A1 | A full-slot-domain; larger domain shares prefix | Full equality rejection |
| A2 | A1; restore exact domain | Nearest valid neighbor |
| A3 | A ordered-output-domains; violate rank too | Domain/slot identity and documented error order |
| A4 | A ordered-output-accept | Ordered destination acceptance |
| A5 | A broadcast-general; add a second term covering the first term's missing output UID | Per-term broadcast classification, no union-support pure label |
| A6 | M; every output UID read | Standard pure classification |
| A7 | S; direct empty product AST | Identity without invented Factor literal |
| A8 | S; direct empty term list AST | Empty additive identity |
| A9 | A; duplicate resolved axis declaration | Duplicate UID declaration error |
| A10 | A; duplicate tensor declaration | Stable offending declaration, no shadowing |
| A11 | P scalar; explicitly mark written Y as input | Role mismatch |
| A12 | P matmul; remove pinned k domain | Missing domain, no inference |
| A13 | P scalar; add unused declared input, omit binding | All declared input presence |
| A14 | E; omit declared empty input binding | Presence not inferred from zero cells |
| A15 | P matmul; shorten W buffer | Exact length rejection |
| A16 | P matmul; swap unequal W dimensions and shorten buffer | Shape error precedes length; no accidental equal-size pass |
| A17 | P scalar; replace read with iverson | Typed unsupported form with factor origin |
| A18 | P scalar; replace read with unaryFn | Typed unsupported form with factor origin |
| P1 | C/X; two defined targets with a read dependency | Multi-tensor elaboration/run |
| P2 | C collision; two original statements same target | Separate source/tag maps |
| P3 | P2; reorder after attaching original IDs | Tagged collection permutation |
| P4 | P2; identical statement bodies | Multiplicity, no dedup |
| P5 | P1; intermediate is nonoutput | Intermediate publication |
| P6 | P1; declared defined tensor has no statements | Full unwritten domain publication |
| P7 | X schedule; unequal ranks/extents across defined tensors | Complete/nodup computational key enumeration |
| P8 | A13/A14; provide unused and empty input bindings | Valid input-presence neighbor |
| P9 | N nested; unequal nested bounds/nonuniform reads | Actual body and full read footprint |
| P10 | X program; self-dependent bounded read | Honest unranked blocked outcome |
| P11 | X schedule; insufficient explicit debug fuel | Exhausted, not semantic failure |
| P12 | S/E/W; general schedule for scalar/empty/repeated output | Exact domain coverage without one-target shortcut |
| B1 | S | Rank-zero normalized-body/fiber theorem and run |
| B2 | E | Zero contraction with nonempty output |
| B3 | W | Repeated output and empty off-diagonal fibers |
| B4 | B; unequal contracted extents per term | No union contraction of bias |
| B5 | M; unequal axes and nonuniform slot values | Independent global fiber vs actual lowering |
| B6 | C collision; duplicate contributions | Collection multiplicity in bridge |
| B7 | V3/V4; transport partition under context rename | UID partition equiv, not positional tautology |
| B8 | N nested; specialize generic proof to Nat and Rat | Legitimate semiring proof; no Float instance |
| D1 | A3; retain all original origin fields | Typed admission cause/slot rendering |
| D2 | X summarize; complete run with nonoutput/unwritten cells | Complete result and whole publication payload |
| D3 | X summarize; inject typed failed result into renderer | Failure/missing reads preserved; not a reached-source failure receipt |
| D4 | P10; render actual blocked run | Pending keys/source addresses, no no-model claim |
| D5 | P11; render actual exhausted run | Fuel/pending payload |
| D6 | P3; reverse permissible event ordering | Compare by source occurrence, not zipped index |
| D7 | B5; discrepancy only at a later nonzero coordinate | First actual address/value, asymmetric packing |
| D8 | P matmul; unequal output shapes and equal-prefix cells | Shape comparison before cell comparison |
| D9 | P2; statement origins distinct despite equal lhs | Original ordinals survive grouping |
| D10 | A17; request unsupported production/shared profile | Refusal is not admission/parity success |
| D11 | P compare; source violates structural compile constraint | Actual compile phase/cause/warnings |
| D12 | P default-dtype-outside-f64-profile | Actual preparation cause retained |
| D13 | P renderCause; inject an actual runtime-error constructor | Runtime renderer protocol only, not an observed backend failure |
| D14 | P diagonal-write; corrupt a compared output observation | Output discrepancy observed; internal production layers unobserved |
| D15 | P compare; inject warning-bearing typed leg result | Warning preservation, no silent default |
| F1 | P matmul | Four-leg asymmetric matrix comparison |
| F2 | P term-local-bias | Independent per-term contraction |
| F3 | P diagonal-read | Repeated read slots |
| F4 | P diagonal-write | Required shared-fragment diagonal writes |
| F5 | P empty-contraction | Empty contraction, full output |
| F6 | P scalar | Scalar shape and exact product |
| F7 | P within-statement-duplicates | Required shared-fragment multiplicity |
| F8 | P matmul; reorder unequal slots/input packing | Noncommuting locator/order witness |
| F9 | V4/P matmul; consistent source alpha transport | Same source identities transported, no name matching |
| F10 | A7/A8; run direct AST identities | Reference identities; production eligibility observed or refused explicitly |
| F11 | P scalar; negative integers and signed-zero observations | Exact negative profile/zero normalization |
| F12 | P scalar; intermediate envelope boundary and overshoot | Runtime checked envelope/refusal, not final-value tolerance |
| F13 | P default-dtype-outside-f64-profile | Both typed dtype failures, no rewriting |
| F14 | P cross-statement-known-contract | Known overwrite-vs-collection difference |
| F15 | P3/P4; permute multiple definitions with stable IDs | Reference-only tagged comparison, no production parity claim |
| F16 | P scalar/matmul; deterministic 18-case grid below | Bounded generated corpus, independent packing/oracle |
| F17 | P1; distinct single-defined targets in an acyclic chain | Four legs or explicit eligibility refusal; complete reference run |
| F18 | M; resolved same-name distinct UIDs with skewed assignments | Reference-only UID identity; front-end limitations explicit |

F16 enumerates two scalar programs (factor count 1..2), then rank 1..2,
common extent 0..3, and factor count 1..2: exactly 18 structurally distinct
candidate programs, deterministic nonnegative integer cells and pinned shapes.
Do not repeat a rank-zero program for four irrelevant extent choices.
Each has one full-slot output term; factor slots follow that output shape.
Observe eligibility per leg; a refusal is reported, never counted as parity.
Extra skewed-axis/asymmetric cases are F1/F8, not hidden random generation.

Future implementation cycles, one mutant per cycle, with intended fixture IDs:
- T1 (4): UID lookup changed to position/name (V1); wrong inverse permutation
  (V3); freshness skips free/output support (V5); domain check removed (V6).
- T2 (8): prefix-domain acceptance (A1); output slot reorder (A3/A4);
  union-of-terms support (A5/B4); duplicate declaration shadow (A9/A10);
  role guard removed (A11); absent domain inferred (A12);
  skip unused/empty input presence (A13/A14); skip exact shape/length (A15/A16).
- T3 (6): single-target role shortcut (P1); original tag overwritten by new
  ordinal (P3); duplicate occurrence dedup (P4); nonoutput publication omitted
  (P5); unwritten coordinates omitted (P6); nested-read footprint lost (P9).
- T4 (4): reduction bound lost (B2/B5); destination repeated slot changed
  (B3); bias contracted with another term's binders (B4); multiplicity removed
  (B6). Mutate executable lowering/collection, not expected oracle values.
- T5 (8): trace-index zip (D6); wrong differing coordinate (D7); prefix-shape
  comparison (D8); source ordinal dropped (D9); compile/prepare/runtime causes
  collapsed (D11-D13); warnings discarded (D15); guessed causal localization
  (D14); tolerance/final-only envelope comparison (F11/F12).
- T6 (9): independent packing transposed (F8); oracle UID merged (F18);
  diagonal write wrongly refused (F4); terms deduped (F7); zero domain made
  singleton (F5); zero normalization removed (F11); f32 source silently changed
  (F13); multi-definition marked shared (F14/F15); publication scan truncated
  (F17/P6). No mutation of production.

Keep the existing [six contrasts](source_correspondence_artifacts/mutations.json)
unchanged as fixture-input discriminators. Create future
`papers/semantics/source_correspondence_mutations_post.json` only after real
implementation-mutant failures are observed. Copy `expect` from those failures;
never fabricate expected strings or add unobserved cycles to completed receipts.
For each cycle require the intended fixture assertion or specifically identified
proof-obligation failure, restored byte identity, and restored build success.
Unrelated compile errors do not count. Prefer executable adapter/harness seams
with an independent oracle. If a proof-protected mutant fails at its intended
proof obligation before execution, record that class explicitly; it is an
implementation kill, not a differential runtime-fixture kill.

## 7. Readiness, execution, review, and documentation protocol

1. Complete real-split rehearsal for T1-T6 on a compatible baseline. Seed patches
   retain their historical base; reconcile them explicitly with current local
   main. Emit a fresh ordered patch series covering every task and its tests.
2. Observe every matrix row and exact typed payload, and all 39 implementation
   cycles. Produce/verify the post manifest **before** execution readiness.
   Check public import/default targets and the resolution seam without DSL/Eval
   modifications. Update the record with observations, not inferred values.
3. Two independent final review lenses: (a) soundness, UID binding, support,
   provenance, schedule completeness; (b) oracle/input-packing independence,
   numerical envelope, differential classifications, receipts/mutations.
   Reviewers use 40-60-line windows, append findings incrementally to session
   artifacts, and can reject task boundaries separately. Fix by finding group.
4. Controller independently runs the full build and mutation manifests,
   including observed `expect` and restored-byte checks. Only then change this
   status to execution-ready. Partial patch review/full build alone is insufficient.
5. Future implementation uses prepared isolated worktrees via the
   [new-slice skill](../../.claude/skills/new-slice/SKILL.md), no cold Mathlib build.
   Review each task and its bundles; integrate only after controller full build,
   manifest execution, and both whole-branch lenses are clean/adjudicated.
   This Phase B authoring does not implement, dispatch agents, commit, merge,
   or perform remote operations.

Every future brief begins with this shell preamble:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Each dispatch: at most three work items/families, approximately 60 turns and
250k peak context. Expected overrun means split before dispatch; unexpected
overrun is surfaced in its report. Execution total ceiling approximately 175M.
Authoring target approximately 50M cumulative input, also 60 turns/250k peak
per dispatch. Telemetry is unavailable here, not measured zero.
Before edits, measure hook-injected Pitfalls/Checks/Patterns/Context in both
covering AGENTS nodes; trim if above approximately 3k characters, preserving
contracts/discoverability. Current file size does not establish hook size.

Documentation is incremental work within T6, not another heavyweight dispatch.
Phase B adds this plan link to the roadmap without moving LANDED/REMAINING
markers or copying an inherited gap list. Add actual public import/API/test discoverability
to the covering AGENTS nodes after implementation exists. Value-grep any changed
capability counts across the repository before declaring the sweep complete.
The stale f64 AST/DSL comments remain parked: code/latest tests win; cleanup is
not required here (one Direct documentation dispatch if separately authorized).

Commands below are future controller commands, not Phase B receipts. Replace
`/path/to/worktree` with one literal absolute path before execution; no variables
or chained commands. Use actual target names registered during rehearsal.

```sh
bash /path/to/worktree/leanncd/scripts/lake-build.sh /path/to/worktree/leanncd +Semantics.SourceCorrespondenceTest
bash /path/to/worktree/leanncd/scripts/lake-build.sh /path/to/worktree/leanncd +Semantics.SourceDifferentialTest
bash /path/to/worktree/leanncd/scripts/lake-build.sh /path/to/worktree/leanncd
bash /path/to/worktree/leanncd/scripts/mutation-manifest.sh --check /path/to/worktree/leanncd /path/to/worktree/papers/semantics/source_correspondence_mutations_post.json
bash /path/to/worktree/leanncd/scripts/mutation-manifest.sh --out /path/to/session-files/source-correspondence-post-results.md /path/to/worktree/leanncd /path/to/worktree/papers/semantics/source_correspondence_mutations_post.json
rg -n 'source_correspondence|LANDED|REMAINING' /path/to/worktree/papers/semantics/lean_executable_semantics_path.md
rg -n 'SourceCorrespondence|SourceDifferential|runSourceDebug|compareSource' /path/to/worktree/leanncd/AGENTS.md /path/to/worktree/leanncd/LeanNCD/Semantics/AGENTS.md
```

The six historical contrast cycles are replayable on the exact seed-compatible
tree, not automatically on the final redesigned source modules. Retain their
manifest/receipts unchanged; if replayed, use a separately identified seed replay
worktree. The 39-cycle post manifest must target and run on the final integrated
implementation tree, not just pass schema checking on the prototype.

Close-out records measured usage where available, controller commands/results,
all classifications/skips/refusals, observed manifest receipts, and adjudicated
review findings. Do not call an unobserved layer tested, an injected renderer
error an actual backend failure, or a known contract difference parity success.

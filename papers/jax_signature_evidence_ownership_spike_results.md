# JAX signature/evidence ownership spike results

## Baseline

- Branch: `agents/jax-signature-evidence-ownership-spike`
- Task 0 / local `main`: `c8ed1027feb3a08c106ffc43a4ea479b7c20570c`
- Cache donor recorded by the SDD ledger: `/Users/williammacready/code/python/pyncd`
- Mathlib cache: 8,101 `.olean` files / 8,094 `.lean` sources = 100.09%; no cold build.
- Host concurrency: 12 logical CPUs. Lake selected its default job count.
- Preflight (`git diff --check`, conflict-marker scan, tracked-plan checks): exit 0. The only initial
  status entry was the prepared, gitignored `.superpowers/` SDD ledger.
- `lake build`: exit 0, 8,659 jobs, 6.64 s replay (user 3.69 s, sys 5.24 s).
- `lake build JaxExperiment Eval.Plan.ExecutableTest`: exit 0, 8,513 jobs, 6.61 s replay
  (user 3.75 s, sys 5.15 s).
- `lake env lean experiments/jax_bridge/EvalPlanAffineCorpus.lean` exposed a pre-existing,
  non-default-driver failure at `c8ed102`: four projections of `.plan` from
  `CheckedPlanStepEvidence` no longer elaborate. Both candidate prototypes include the required
  temporary caller migration and the final revert restores this starting behavior; no retained
  production repair is claimed by this disposable spike.

## Task 1 shared harness

The disposable checker diff changes only a read-source check: `.f64` becomes `.f64 || .bool` and the
source/destination dtype-equality check is removed. Destination `.f64`, admitted algebra/constants,
all rank/shape/affine/OOB checks, and `.f32` rejection are unchanged.

| Fixture | Construction | Current observation under shim |
|---|---|---|
| F1 | Existing `idSigs`/`idAssign` | Existing all-real guards and both candidate validators pass; affine evidence is `orderedReference64`. |
| F2 | Only source slot 0's tag changes from `f64` to `bool`; Float data and real destination/algebra are unchanged | `checkAssign`, Dense, every public semantic renderer/lowerer, both candidates, both kernel validators, plan lowering, and executable construction pass. This is the hole. |
| F3 | Four slots; external slot 2 is Boolean; step 0 reads real slot 0 to slot 1; step 1 reads Boolean slot 2 to slot 3 | `checkPlan` and current executable construction pass. Harness locator is exactly `(step=1, term=0, factor=0, slot=2)`, so step and slot cannot be confused. |
| F4 | F2 `PreparedPlan` owns the Boolean table; a manually built same-shape kernel is checked with all-real `idSigs` | Current executable validation accepts the substitute because it checks only count/kernel shape/aggregation. |

Harness mutations:

| ID | Mutation | Observed failure | Restore |
|---|---|---|---|
| H1 | Restore `.f64`-only reads and dtype equality | Exit 1; three `ExecutableTest` F2 guards plus Codegen F2/F3/F4 guards fail | Restored; targeted builds pass |
| H2 | Put F3's Boolean-read assignment at step 0 while retaining expected step 1 | Re-run after the review fix: exit 1; `firstBoolReadLocation ... == some (1,0,0,2)` fails | Restored; Codegen builds |

## Complete Task 1 public-definition inventory

Classification: **E** semantic public entry (must receive/derive support context), **H** semantic
helper (make private or context-bearing), **D** dtype-independent data/primitive renderer, **T**
test-only fixture. “Nearest gate” identifies why a D row cannot emit or certify an assignment.

### `LeanNCD/Eval/Plan/Executable.lean`

| Definition | Class | Reason / nearest gate |
|---|---:|---|
| `ExecutionEvidence` | D | Claim vocabulary only; private validated constructors gate claims. |
| `AffineTableReadCandidate` | D | Data record only; affine validator gates it. |
| `OrderedAffineTableKernelCandidate` | E | Public semantic candidate; must carry (A) or be validated with (B) context. |
| `EinsumExperimentKernelCandidate` | E | Public semantic candidate; same ownership choice. |
| `JaxKernelCandidate` | E | Public candidate sum; kernel validator gates it. |
| `candidateEvidenceLabel` | E | Current public pre-validation claim is the direct bypass; must become private/post-validation. |
| `recomputeAffineFactorTable` | H | Validator implementation; table geometry alone is dtype-blind. |
| `affineFactorTableValid` | H | Validator implementation; nearest gate is `validateAffineTable`. |
| `affineTermTablesValid` | H | Validator implementation; nearest gate is `validateAffineTable`. |
| `validateAffineTable` | E | Public candidate validator must check support context. |
| `validateEinsum` | E | Public candidate validator must check support context. |
| `kernelWellFormedBool` | H | Combined semantic validator; must be indexed by/derive context. |
| `JaxKernelWellFormed` | E | Evidence proposition must include support context. |
| `Decidable JaxKernelWellFormed` | D | Decision procedure for the contextual proposition. |
| `JaxKernel` | E | Private-constructor validated value; must retain checkable context. |
| `SomeJaxKernel` | E | Existential validated value; exposes only validated evidence. |
| `validateAndConstructKernel` | E | Public construction gate; context required before evidence. |
| `aggregateEvidenceList` | D | Pure fold over already validated evidence values. |
| `JaxExecutableCandidate` | E | Plan candidate; source-plan authority must be tied per step. |
| `JaxExecutableWellFormed` | E | Plan-level evidence proposition; must tie context and assignment per step. |
| `Decidable JaxExecutableWellFormed` | D | Decision procedure for that proposition. |
| `JaxExecutable` | E | Private-constructor executable. |
| `SomeJaxExecutable` | E | Existential executable wrapper. |
| `validateAndConstructExecutable` | E | Final plan construction gate with located step checking. |

### `experiments/jax_bridge/EvalPlanCodegen.lean` production surface

| Definition | Class | Reason / nearest gate |
|---|---:|---|
| `JaxCodegenError` | D | Closed diagnostic vocabulary. |
| `pyStrLit` | D | String escaping only; nearest semantic gate is a public generator. |
| `pyShapeTuple` | D | Shape literal only. |
| `pyUInt64ListLit` | D | Bit-list literal only. |
| `pyNatListLit` | D | Nat-list literal only. |
| `pyIntListLit` | D | Int-list literal only. |
| `pyBoolListLit` | D | Bool-list literal only. |
| `pyTensorEntry` | D | Concrete fixture-data renderer, not executable assignment semantics. |
| `labelTable` | D | Static alphabet. |
| `rowProjectionTarget` | D | Pure affine-row recognizer. |
| `lowerFactor` | H | Assignment semantic helper; make private behind contextual `lowerAssign`. |
| `TermLowering` | H | Publicly constructible semantic IR feeds a Python renderer; renderer must become private behind a contextual gate. |
| `lowerTerm` | H | Assignment semantic helper; make private. |
| `NodeLowering` | H | Publicly constructible semantic IR feeds destination-writing Python; renderer must become private. |
| `lowerAssign` | E | Standalone/raw semantic lowerer; require complete context. |
| `lowerPlan` | E | Complete checked-plan lowerer; derive `raw.tensorSigs`. |
| `renderTermLine` | H | Emits `jnp.einsum` from publicly constructible IR; make private behind contextual lowering. |
| `renderNodeLines` | H | Emits destination writes from publicly constructible IR; make private behind contextual lowering. |
| `renderShapeCheckLine` | D | Shape-only input guard; generator is semantic gate. |
| `renderSlotInitLines` | D | Shape/init lines only; generator is semantic gate. |
| `renderOutputLines` | D | Name/slot projection only. |
| `generateForward` | E | Plan-level Python emitter; derives authoritative table. |
| `renderInputConstants` | D | Input fixture constants only; emits no assignment. |
| `renderExpectedOutputConstants` | D | Expected fixture constants only. |
| `renderCompileCause` | D | Diagnostic renderer only. |
| `buildFactorTable` | D | Coordinate table primitive; candidate/assignment caller must gate support. |
| `renderAffineFactor` | H | Emits factor semantics; make private behind contextual assignment renderer. |
| `renderAffineTerm` | H | Emits term semantics; make private. |
| `renderAffineNode` | H | Emits raw assignment semantics; make private. |
| `renderAffineNodesArray` | H | Emits plan nodes; make private. |
| `renderBindingList` | D | Names/slots only. |
| `renderAffinePlanPositional` | E | Checked-plan emitter; derives authoritative table. |
| `renderAffinePlanNamed` | E | Prepared-plan emitter; derives authoritative table. |
| `renderAffineAssign` | E | Standalone assignment emitter; explicit complete table required. |
| `buildAssignFixture` | E | Existing table argument becomes its explicit semantic authority. |
| `LoweringMode` | D | Mode tag only. |
| `generateNamed` | E | Public plan emitter; derives authoritative table. |
| `loweringToAffineTableCandidate` | E | Standalone candidate conversion; explicit complete table required. |
| `loweringToEinsumCandidate` | E | Standalone candidate conversion; explicit complete table required. |
| `lowerCheckPlanToCandidate` | E | Plan candidate conversion; derives only `PreparedPlan.plan.raw.tensorSigs`. |

Every remaining public definition in this module is a **T** row:

| Definition | Class | Definition | Class |
|---|---:|---|---:|
| `idSigs` | T | `idRead` | T |
| `idAssign` | T | `idRaw` | T |
| `testAffineLoweringValid` | T | `testEinsumLoweringValid` | T |
| `testLowerCheckPlanToCandidateValid` | T | `spikeExceptOk` | T |
| `boolSourceSigs` | T | `boolSourceRaw` | T |
| `boolSourceStore` | T | `boolSourcePrepared?` | T |
| `testCurrentBoolSourcePublicPathsAccepted` | T | `locatedStep0Read` | T |
| `locatedStep1Read` | T | `locatedStep0Assign` | T |
| `locatedStep1Assign` | T | `locatedBoolSigs` | T |
| `locatedBoolRaw` | T | `locatedBoolPrepared?` | T |
| `firstBoolReadLocation` | T | `testCurrentLocatedBoolExecutableAccepted` | T |
| `allRealSubstituteSigs` | T | `testCurrentPlanAuthoritySubstitutionAccepted` | T |
| `rejectSigs` | T | `pointwiseStep` | T |
| `pointwiseRejectRaw` | T | `axiswiseStep` | T |
| `axiswiseRejectRaw` | T | `scanState` | T |
| `scanBaseBlock` | T | `scanBaseCapture` | T |
| `scanBaseWrite` | T | `scanStepReadX` | T |
| `scanStepReadS` | T | `scanTermX` | T |
| `scanTermS` | T | `scanStepAssign` | T |
| `scanStepBlock` | T | `scanStepCaptureX` | T |
| `scanStepCaptureS` | T | `scanStepWrite` | T |
| `scanPlanStep` | T | `scanRejectSigs` | T |
| `scanAssignRead` | T | `scanAssign` | T |
| `scanRejectRaw` | T | `rejectsLocatedAt1` | T |
| `testPointwiseStepRejectedLocated` | T | `testAxiswiseStepRejectedLocated` | T |
| `maskInclude` | T | `maskedAxiswiseStep` | T |
| `maskedAxiswiseRejectRaw` | T | `testMaskedAxiswiseStepRejectedLocated` | T |
| `testScanStepRejectedLocated` | T | `idIversonPred` | T |
| `idIversonAssign` | T | `idIversonRaw` | T |
| `testIversonPlanChecks` | T | `iversonRejectedUnder` | T |
| `testIversonEinsumRejectedLocated` | T | `testIversonAffineRejectedLocated` | T |

Current external callers are: `EvalPlanSmoke.generateNamed`; `EvalPlanAffineSmoke`'s
`renderAffinePlanNamed`, `renderAffinePlanPositional`, and ten `buildAssignFixture` calls;
`EvalPlanAffineCorpus.generateNamed`; and `ScalingProbe.buildAssignFixture`.

## Variant measurements

### Variant A — candidate-owned complete context

Commits: implementation `f57430b`; per-entry mutation guards `d7975a7`.

Measured public signatures:

```text
lowerAssign (sigs : Array TensorSignature) (nodeIndex : Nat) (checked : CheckedAssignPlan)
renderAffineAssign (sigs : Array TensorSignature) (c : CheckedAssignPlan)
loweringToAffineTableCandidate (sigs : Array TensorSignature) (nodeIndex : Nat)
  (assign : CheckedAssignPlan) : Except JaxCodegenError OrderedAffineTableKernelCandidate
loweringToEinsumCandidate (sigs : Array TensorSignature) (nodeIndex : Nat)
  (assign : CheckedAssignPlan) : Except JaxCodegenError EinsumExperimentKernelCandidate
```

After specification review, the standalone `lowerAssign` signature was tightened to take
`checked : CheckedAssignPlan` rather than raw `AssignPlan`; it cannot bypass structural
`checkAssign`. `validateAndConstructKernel` now returns
`Except JaxKernelValidationError SomeJaxKernel`, where
`JaxKernelValidationError.unsupported` retains exact term/factor/slot `JaxSupportError` payloads.
Direct guards observe F1 `.ok ()`, F2 `.sourceDType 0 0 0 .bool`, unary `.unaryFactor 0 0`, and
Iverson `.iversonFactor 0 1`. `JaxSupportError` is public diagnostic data;
`checkJaxAssignSupport` is the context-bearing public cross-module helper; `jaxAssignSupported` and
the raw evidence-label helper are private. `JaxKernelValidationError` is diagnostic data.

`lowerPlan`, `generateForward`, both affine plan renderers, `generateNamed`, and
`lowerCheckPlanToCandidate` retain direct plan-level signatures and derive only
`PreparedPlan.plan.raw.tensorSigs` (or the same table from `CheckedEvalPlan.raw`). `lowerFactor`,
`lowerTerm`, `renderTermLine`, `renderNodeLines`, and the affine factor/term/node/array renderers
became private. `candidateEvidenceLabel` became private. Both candidate records gained
`signatureContext : Array TensorSignature`; validator signatures stayed direct because they inspect
that stored table.

Every candidate therefore owns one complete table value. A two-step plan has two candidate fields
containing the complete table (Lean arrays may structurally share at runtime, but the API/proof
surface duplicates authority per step). Per kernel, well-formedness re-runs `checkAssign` under the
stored table, checks JAX destination/algebra/source support, and checks affine/einsum structure.
Executable well-formedness adds two step obligations: candidate table equals the prepared table and
candidate assignment equals the corresponding checked assignment. The first mismatch is reported
at the real outer index.

All-real caller migration: inline candidate tests pass one complete `idSigs`/`mixedSigs` table at
the conversion boundary; plan-level callers remain one-argument/direct. The two non-default affine
drivers also needed temporary adaptation to the current `CheckedPlanStepEvidence` sum and existing
`Except` render signatures; those failures existed at the Task 0 SHA and are not attributed to the
ownership prototype.

Validation:

- Production/check/test/Jax builds: exit 0. Warm timings: 8,497 jobs in 6.50 s; 8,514 jobs in
  6.46 s. Direct `EvalPlanAffineCorpus.lean` elaboration: exit 0 after its temporary caller migration.
- `run-evalplan.sh`: exit 0, 27.37 s; einsum eager/JIT/gradient smoke passed.
- `run-evalplan-affine.sh`: exit 0, 31.69 s; 20 fixtures eager/JIT bit-identical to Dense.
- `run-evalplan-affine-corpus.sh`: exit 0, 743.70 s; 3,832 cases, zero eager mismatches,
  65 JIT cases, artifact 3,424,195 bytes.
- `run-scaling-probe.sh`: exit 0, 28.28 s; 177,547-byte artifact; eager/JIT bit-identical.

Variant A mutation cycles:

| ID | Concrete mutation | Observed fail | Restored pass |
|---|---|---|---|
| A1 | Replace source-dtype rejection with `pure ()` while retaining destination/algebra checks | Exit 1: both kernel-kind F2 guards, every rendering-mode aggregate, IO fixture, and F3 guard fail | `ExecutableTest` + Codegen pass |
| A2 | At the plan conversion boundary, replace `PreparedPlan.plan.raw.tensorSigs` with a same-shape all-`f64` mapped table | Exit 1: direct `lowerCheckPlanToCandidate` F2 gate and F3 exact-step gate fail | Codegen passes |
| A3 | Remove complete-table equality from executable step correspondence | Exit 1: F4 step-0 substitution and F3 step-1 context-substitution guards fail | Codegen passes |
| A4 | Rotate the single contextual dominator through all retained entries: remove `lowerAssign` gate, affine-node gate, affine-candidate gate, then einsum-candidate gate | Named direct guards fail respectively for `lowerAssign`/`lowerPlan`/`generateForward`/einsum `generateNamed`; both affine plan renderers/standalone renderer/affine `generateNamed`/`buildAssignFixture`; affine conversion/plan conversion; einsum conversion | Each rotation restored; all 11 direct guards pass |
| A5 | Make `candidateEvidenceLabel` public and assert F2 cannot observe ordered evidence | Exit 1: F2 directly returns `orderedReference64` before validation | `ExecutableTest` passes; helper private again |
| A6 | Emit outer index `0` for every support failure | Exit 1: F3 exact step-1 guard fails | Codegen passes |

An additional assignment-correspondence attack replaced the per-step assignment equality with
`true`; the step-0-kernel-reused-at-step-1 guard failed, then passed after restoration. For A4, the
four rotations are the four real contextual dominators, not four exemplar APIs: their named errors
cover all eleven retained entry assertions. Removing the source policy itself after review produced
individual failures for all eleven guards in one build, confirming none was hidden by the aggregate.

Variant A reviews:

| Lens | Finding | Resolution |
|---|---|---|
| Specification | Candidate validator returned generic text; `lowerAssign` accepted raw plans; new public helper inventory absent | Fixed in `6a8d4ac`: structured exact support errors, checked standalone input, inventory delta/direct policy guards added here |
| Specification | A2/A3 mutation meanings and A4 rotation evidence were unclear | A2 and A3 re-run separately as specified; assignment tie attacked separately; every A4 entry has a named failure |
| Code quality | Unary and Iverson were not rejected by the shared support policy | Fixed with located support errors; existing codegen Iverson locator preserved |
| Code quality | Einsum validator does not recompute exact projection/output axes | Adjudicated pre-existing at `c8ed102`, unrelated to signature ownership and carrying only `optimizationExperiment`; neither prototype changes or weakens it, and all temporary code is reverted. Production follow-up remains warranted. |

Both specification and code-quality re-reviews after `6a8d4ac` reported no significant remaining
ownership issue. Default build, targeted JAX/Executable build, and direct corpus elaboration all
returned exit 0 after the fixes.

### Variant B — validator-supplied complete context

Commits: implementation `2b1d361`; direct validator guards `0f87b88`.

Measured public signatures:

```text
lowerAssign (sigs : Array TensorSignature) (nodeIndex : Nat) (checked : CheckedAssignPlan)
renderAffineAssign (sigs : Array TensorSignature) (c : CheckedAssignPlan)
loweringToAffineTableCandidate (sigs : Array TensorSignature) (nodeIndex : Nat)
  (assign : CheckedAssignPlan) : Except JaxCodegenError OrderedAffineTableKernelCandidate
loweringToEinsumCandidate (sigs : Array TensorSignature) (nodeIndex : Nat)
  (assign : CheckedAssignPlan) : Except JaxCodegenError EinsumExperimentKernelCandidate
validateAffineTable (sigs : Array TensorSignature) (kernel : OrderedAffineTableKernelCandidate)
validateEinsum (sigs : Array TensorSignature) (kernel : EinsumExperimentKernelCandidate)
kernelWellFormedBool (sigs : Array TensorSignature) (candidate : JaxKernelCandidate)
JaxKernelWellFormed (sigs : Array TensorSignature) (candidate : JaxKernelCandidate)
validateAndConstructKernel (sigs : Array TensorSignature) (candidate : JaxKernelCandidate)
  : Except JaxKernelValidationError SomeJaxKernel
```

Raw `OrderedAffineTableKernelCandidate` and `EinsumExperimentKernelCandidate` retain their original
fields: neither stores signatures. `JaxKernel` privately stores the one complete
`signatureContext` used by its validator together with
`valid : JaxKernelWellFormed signatureContext candidate`; evidence therefore remains checkable from
the validated value. `JaxExecutableWellFormed` compares each validated kernel's stored context to
`PreparedPlan.plan.raw.tensorSigs` and its assignment to the corresponding checked step.
Plan-level renderers/conversion retain direct one-plan signatures and derive that table internally;
no caller-selectable parallel table exists.

The standalone API adds one complete-table argument at each nearest public semantic boundary.
Context is not repeated through recursive helpers, which are private. Existing raw candidate types
do not change. A plan still has one stored table value in each validated kernel witness (needed to
make evidence checkable), but it does not also put the table in public raw candidates. All-real
inline validator calls add one `idSigs`/`mixedSigs` argument; all plan-level JAX drivers remain
direct.

Validation:

- Production/check/test/Jax builds: exit 0. Warm timings: 8,497 jobs in 6.23 s; 8,514 jobs in
  6.25 s. Direct corpus elaboration: exit 0.
- `run-evalplan.sh`: exit 0, 20.67 s; eager/JIT/gradient smoke passed.
- `run-evalplan-affine.sh`: exit 0, 30.58 s; all 20 fixtures passed bit-identically.
- `run-evalplan-affine-corpus.sh`: exit 0, 730.74 s; 3,832 cases, zero eager mismatches,
  65 JIT cases, artifact 3,424,195 bytes.
- `run-scaling-probe.sh`: exit 0, 27.60 s; 177,547-byte artifact; eager/JIT bit-identical.

Variant B mutation cycles:

| ID | Concrete mutation | Observed fail | Restored pass |
|---|---|---|---|
| B1 | Skip source dtype rejection while retaining destination/algebra/unary/Iverson policy | Exit 1: direct `checkJaxAssignSupport`, affine/einsum validator, contextual well-formedness, private constructor, all renderer/lowerer, IO fixture, and F3 guards fail | `ExecutableTest` + Codegen pass |
| B2 | Temporarily add a caller table to plan conversion and pass F4's same-shape all-`f64` substitute | Exit 1: `testVariantBPlanAuthoritySubstitutionRejected` fails specifically at the plan boundary | Codegen passes after restoring the deriving-only signature |
| B3 | Change the plan conversion signature to accept caller context and supply all-real context only for F3 | Exit 1: exact F3 plan-boundary guard fails | Codegen passes after restoring the one-argument, deriving API |
| B4a | Remove `lowerAssign`'s support gate | Named failures: `lowerAssign`, `lowerPlan`, `generateForward`, einsum `generateNamed` | Each named guard passes after restore |
| B4b | Remove affine-node support gate | Named failures: positional/named plan render, standalone render, affine `generateNamed`, `buildAssignFixture` | Each named guard passes after restore |
| B4c | Remove affine candidate-conversion gate | Named failures: affine conversion, plan conversion, F3 exact-step guard | Each named guard passes after restore |
| B4d | Remove einsum candidate-conversion gate | Named failure: einsum conversion | Guard passes after restore |
| B4e | Stop re-running `checkAssign` under standalone supplied context | All four mismatched-shape context guards fail: `lowerAssign`, standalone affine render, both candidate conversions | All four pass after restore |
| B5 | Skip support validation and validate/construct with an all-real forged table before assigning evidence | Exit 1: both candidate-kind F2 guards and plan context/assignment guards fail; affine candidate can otherwise expose `orderedReference64` | `ExecutableTest` + Codegen pass |
| B6 | Compare only the first validated kernel's cached context, then ignore later kernel contexts | Exit 1: F3 step-1 context-substitution guard fails; F4's step-0 check remains intact | Codegen passes |

Variant B reviews:

| Lens | Finding | Resolution |
|---|---|---|
| Specification | No significant issue | No change |
| Code quality | Standalone supplied tables checked dtype support but were not re-run through structural `checkAssign` | Fixed in `063436d`; `invalidSignatureContext` is located and four mismatched-shape guards fail/restore/pass under B4e |
| Code quality | Three context-free affine validation helpers remained public | Fixed in `063436d`; helpers are private behind contextual `validateAffineTable` |
| Code quality | B2 did not directly trip F4; B4 record was aggregate | B2 re-run with a caller-table mutation against the F4 guard; B4a-e now record each named fail/restore/pass rotation |

The post-`063436d` code-quality re-review reported no significant remaining issue. Default build,
targeted JAX/Executable build, and direct corpus elaboration returned exit 0 after the fixes.

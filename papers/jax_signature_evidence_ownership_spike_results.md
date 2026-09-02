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

To be completed after both independently compiled prototypes and all mutations.

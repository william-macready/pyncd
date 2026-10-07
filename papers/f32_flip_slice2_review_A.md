# f32 flip slice 2 — Reviewer A findings (lens: wrongly reject / accept valid programs)

Review package: `git diff 44296ad HEAD -- leanncd/LeanNCD` + test migrations. Read-only review.
No Critical findings.

## F1 (Minor) — `Eval.evalScatter` silently computes binary64 for a default-f32 (undeclared / plain) destination

- File/identifier: `leanncd/LeanNCD/Eval/Scatter.lean` `evalScatter`; contract prose in
  `leanncd/LeanNCD/Eval/Contract.lean` ("every public entry refuses it outright").
- Claim: `evalScatter` is a public, `decls`-taking reference entry that runs `rejectComplexDecls` but NOT
  `rejectUnsupportedStorage`. Before the flip this let only an explicit `tensor f32` scatter through
  (pre-existing gap). After the flip, every undeclared or plain-`tensor` scatter destination/source is an
  f32 name by `storageConstraintOfName?`, and `evalScatter` evaluates it in `Float` with no diagnostic,
  while every sibling entry (`evalPlain`, `evalAssignDtyped*`, `evalStmtSliceSeeded`, `evalScan`,
  `evalScheduled`) now refuses the same program with `unsupportedDtype`.
- Failure scenario: `evalScatter [] env sizes "Out" [.affine (.scale 2 i)] rhs {} [4]` (the exact shape used
  in `test/Eval/ScatterTest.lean`, `test/Eval/Portfolio/ScatterNonlinRejectTest.lean`) returns `.ok` with a
  binary64 answer for a program the rest of the reference evaluator now calls binary32. No production
  caller is exposed: `evalPlain` (`Eval/Eval.lean`) refuses before dispatching to `evalScatter`, and the scan
  scatter arm is behind `evalStmtSliceSeeded`'s guard. `test/Eval/ExplicitF64.lean` wraps every direct
  entry except `evalScatter`, consistent with it never refusing.
- Fix options (not applied): add `rejectUnsupportedStorage decls (stmtStorageNames (.scatter nm slots rhs opts))`
  to `evalScatter` (would then require the ScatterTest fixtures to declare `f64`), or document `evalScatter`
  as a worker-tier helper exempt from the per-entry rule.
- Verified by: `rg` of `rejectUnsupportedStorage` callers (Contract/Eval/Scan only), reading
  `Scatter.lean` lines 21-55, `rg "evalScatter "` call sites.

## F2 (Minor) — `InputSignature.ofDenseInputs` usage guidance is now wrong for unannotated programs

- File/identifier: `leanncd/LeanNCD/Eval/Plan/Signature.lean` `InputSignature.ofDenseInputs` doc comment.
- Claim: the doc still says "callers that already know their program declares no predicate-typed name keep
  this simpler, non-declaration-aware constructor". After the flip that is only true for programs whose
  every real external is spelled `tensor f64`; for an unannotated, predicate-free program it yields
  `.f64` signatures that `prepareEvalPlan` Step B rejects as `inputSignature (dtypeMismatch nm .f32 .f64)`
  (pinned at `test/Eval/Plan/CompileTest.lean` `dtypeMismatch "X" .f32 .f64`). Typed rejection, not a
  silent bug, but the doc steers callers into it. "Wave C's only admitted dtype" is pre-existing staleness.
- Verified by reading `Signature.lean` lines 23-30 and `Compile.lean` Step B (`expected := dtypeOfDecl ...`).

## F3 (Minor) — the "consistency edit" flipped one dead dtype fallback but left its two siblings at `.f64`

- File/identifier: `leanncd/LeanNCD/Eval/Plan/Compile.lean` `compileScan` (`stateSigs` uses
  `stateDtypes.getD si .f32`; the step-capture `.state si` arm still uses `stateDtypes.getD si .f64`) and
  `prepareEvalPlan` scan publish (`compiled.stateSigs.getD si { shape := #[], dtype := .f64 }`).
- Claim: all three are DEAD (verified, see A1), so no behavior difference; but after the edit the same
  per-state dtype array has two different unreachable defaults within one function. Either flip all three
  or leave all three; mixing them invites a future reader to believe they mean something.
- Verified by: see A1 below.

## A1 — remaining `.f64`/`.float64` defaults; dead fallbacks; three-way storage-kind agreement — NO LIVE ISSUE

- Dead fallbacks VERIFIED dead (not trusted from the plan):
  - `stateDtypes`: pushed as the FIRST statement of `for h : si in [0 : stateNames.size]` (Phase 2), one push per
    iteration, and any `throw` in the body aborts `compileScan`; `stateShapes`/`stateAdvDims` pushed as the
    last two statements of the same loop. `stateNames` is `let mut` but only pushed in Phase 1 (before Phase 2).
    So all three arrays have size `stateNames.size` on every successful path.
  - `.state si` capture sources are minted only from `stateNames.findIdx? (· == rn)`, so `si < stateNames.size`:
    `stateShapes.getD si #[]` / `stateDtypes.getD si .f64` are dead.
  - `stateSigs := (Array.range stateNames.size).map ...` with `.getD si .f32`: dead by the same size argument.
  - `compiled.stateSigs.getD si {.., .f64}` in `prepareEvalPlan` iterates `si in [0 : compiled.stateNames.size]`
    and `stateSigs.size = stateNames.size` by construction: dead.
- Other slot-indexed `.getD slot { dtype := .f64 }` fallbacks (`Adapter.lean` `packBodyOf`, `Block.lean`,
  `EvalPlan.lean`, `Scan.lean`, `Compile.lean` base/step `resolveSource`/`outerSigs.getD`) read only `.shape`
  or index slots already bounded by `checkStepGraph`; none supplies a dtype for a NAME.
- `dtypeOfDecl`'s `.axis`/`.iter` -> `.f64` arms vs `storageConstraintOfDecl`'s `none` for the same: unreachable
  through any env lookup, because `buildDeclEnv` (`DSL/Ast.lean`) never inserts axis/iter decls. No disagreement.
- Three derivations: Step 0b `scheduleStorageKind` (used names = external reads ++ every write incl. scan scratch,
  `storageConstraintOfName?`, bool-only -> `.float64`); `checkPlan` (`EvalPlan.lean`) `deriveStorageKind` over
  `tensorSigs` (bool-only -> `.float64`, then falls back to first real scan-block slot); block gate in
  `Block.lean`. Every plan slot's dtype is `dtypeOfDecl` of its name (externals via Step B's forced equality,
  destinations/states/scratch directly), and `dtypeOfDecl` and `storageConstraintOfName?` now agree arm by arm
  (`tensor`/`linear`/undeclared/`f32` -> f32; `f64` -> f64; `predicate` -> bool/none). An all-predicate program
  is `.float64` in both Step 0b and `checkPlan` (unchanged by the flip). No live disagreement found.
- Bool-only defaults (`deriveStorageKind`, `scheduleStorageKind`) left at `.float64`: consistent with each other;
  an all-predicate program therefore still needs `runPreparedDense` (Float) and is refused by
  `runPreparedDense32` — pre-existing, unchanged, documented in `Signature.lean` `checkDeclCarriers`.

## A2 — mixed-precision rejection symmetry — NO ISSUE

- `scheduleStorageKind` (`DSL/Pipeline/ScheduledValidation.lean`) is direction-agnostic: first constrained used
  name establishes `k0`, first `k != k0` throws that name. No arm compares against a literal `.float64`.
- f32-declared + undeclared: both `.float32` -> homogeneous, accepted (CompileTest `f32UndeclaredSched`).
  f64-declared + undeclared: externals first in used-name order, so undeclared `X` establishes `.float32` and
  declared `Y` (f64) throws `"Y: mixed f32/f64 storage in one schedule"` (CompileTest `f64MixedUndeclaredSched`).
  f32 + f64 explicit: rejected as before.
- Carrier side (`checkDeclCarriers`, `Signature.lean`) compares `storageConstraintOfName?` to the constructor's
  carrier with `!=`, symmetric for both constructors.
- Step B: for `.float64` storage runs `dtypeAdmitted` then `expected == ts.dtype`; for `.float32` skips admission
  but still enforces `expected == ts.dtype`. The skip's justification was rewritten correctly (plain/undeclared
  externals of an f32 schedule now also answer `.f32` from `dtypeOfDecl`). No asymmetry that relied on the
  old default.

## A4 — Float inputs vs default-f32 programs — NO ISSUE (typed, no reinterpretation)

- `ofDenseInputs` (decl-blind, all `.f64`) + unannotated program -> Step 0b `.float32`, Step B
  `inputSignature (dtypeMismatch nm .f32 .f64)` (typed; pinned CompileTest `dtypeMismatch "X" .f32 .f64`).
- `ofDenseInputsForDecls` (Float carrier) + undeclared/plain name -> `storageKindMismatch nm .float64 .float32`
  from `checkDeclCarriers` (pinned SignatureTest).
- A `.float32` PreparedPlan handed to the Float runner: refused by `runPreparedDenseOf`/`packBodyOf`
  (`Adapter.lean`, `plan.plan.storageKind == StorageCarrier.kind α` first statement) with
  `storageKindMismatch .float64 .float32`, and defensively again at every worker door (`runDensePlan`,
  `runDenseAssignAt`, `runDenseScatter`, `Block.lean`, `Scan.lean`, `Nonlin.lean`); mirror guards on the
  binary32 side. No panic path (`set!`/`[i]!` not involved in the guards), no silent reinterpretation.
- Note: `DefaultF32Test` itself exercises only the Float32 carrier (explicit/plain/undeclared equivalence);
  the Float-carrier rejection is pinned elsewhere (CompileTest, SignatureTest, AdapterTest), not in that module.

## A5 — other behavior changes for previously-valid programs — only the documented regressions, plus F1

- Explicit `tensor f32` / `tensor f64` programs: classification arms for `.typedTensor`/`.typedLinear` untouched,
  so their storage kind, signatures and plans are unchanged.
- Plain `tensor`/`linear`/undeclared programs: now f32 end to end. Rejections observed by reading are all
  typed and within the four documented regressions: JAX `einsumOnly` refuses `.float32`
  (`experiments/jax_bridge/EvalPlanCodegen.lean` `requireModeStorage` -> `unsupportedStorageKind .float32`);
  `runPreparedDense` refuses an f32 plan; Float `InputSignature`s rejected; reference evaluator refuses
  (`rejectUnsupportedStorage`/`scheduleFloat32Name?`).
- The one inconsistency beyond those is F1 (`evalScatter` accepts instead of refusing).
- No production site outside `Eval/Plan`, `DSL/Ast.lean`, `ScheduledValidation.lean`, `Eval/Contract.lean`
  classifies storage (`rg StorageKind|storageConstraint|ScalarDType.f64` file list); `Elab.lean` maps
  `f64`/`f32` keywords only.

## A3 — capability-ordering (`capabilityBeforeInputScatter`) — NO ISSUE (not class iii)

- Severity: none (record correction, Minor at most).
- `capabilityPreflight` (`Eval/Plan/Compile.lean`) is declaration-blind for statements: `checkScanStmt` ->
  `checkScanBlockStmt` -> `checkScanScatterLHSSlot` -> `checkScatterAffineExpr` decides `multiAxisScatterLhs`
  purely from the `IdxExpr` (normalized coefficient count > 1). Declarations enter preflight only through
  `checkDecl` (complex element types) and the `predicateScatterDest` post-pass. No dtype or declaration-
  presence input can turn the scatter's `.affine (j + k2)` row into `scatterOrAffineLhs`.
- What a DECLARED f64 `S` actually changes: `explicitF64Decls` declares `S` at its first write's rank
  (okBase `[.iterAt axL 0]` -> rank 1); the scatter writes `S` at rank 2; Step 0 (`validateScheduled` ->
  `checkScheduledReadRanks` -> `checkReadRanksIn`'s "declared destination" loop, `DSL/Pipeline/Structural.lean`)
  throws `sourceInvariant (rankMismatch "S" 1 2)` BEFORE Step A. This matches the 5b probe table in
  `papers/f32_flip_files/plan_modules.md` ("explicitF64Decls (first-write rank) -> sourceInvariant rankMismatch").
- The 5a "observed `scatterOrAffineLhs`" is almost certainly a misattribution: the 5a probe was a `dbgTrace`
  in `rej`, but `capabilityBeforeInputScatter`'s guards call `causeOf (prepareEvalPlan ... emptySig)` directly,
  never `rej`. The `scatterOrAffineLhs "S: affine LHS slot"` lines the probe printed come from the
  `rej [badAffineLhs "S"] ...` fixtures (an `.assign` with an affine slot, `checkScanLHSSlot`), which pin
  exactly that constructor and pass. plan_modules.md itself says the probe-to-row mapping "was not captured
  line by line".
- Only dtype-dependent ordering in this region: Step 0b (mixed storage, `unsupportedDtype`) precedes Step A.
  Pre-existing by design, unchanged by the flip (only WHICH programs are mixed changed).
- Verified by reading: `Compile.lean` `checkScatterAffineExpr`/`checkScanScatterLHSSlot`/`checkScanLHSSlot`/
  `capabilityPreflight`/`prepareEvalPlan` step order; `Structural.lean` `checkReadRanksIn`;
  `test/Eval/ExplicitF64.lean` `useSiteAxes`; `ScanCompileTest` `rejSchedRaw`/`rejSched`/`okBase`/fixture.

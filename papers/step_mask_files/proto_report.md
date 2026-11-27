# Step-aware `where` masks: prototype report (stage 1, Lean side)

Branch `proto-step-mask`, base `a96744ee`, production commit `c8cee803`
("feat(plan): step-aware axiswise masks (Lean side)"). Everything below is observed in this
worktree on 2026-11-26 unless marked [judgment].

## (a) Measured build cost

Wall clock from `date +%s` around `scripts/lake-build.sh`; "jobs" is the job total lake printed;
"rebuilt" counts `Built` lines (modules actually compiled).

| Build | What had changed | Wall s | Jobs | Rebuilt | Result |
|---|---|---|---|---|---|
| targeted `LeanNCD.Eval.Plan.Nonlin` | `Plan/Nonlin.lean` only | 29 | 8488 | 1 (13 s compile) | green |
| targeted `LeanNCD.Eval.Plan.Compile` | + `Block.lean`, `Compile.lean` (chain from `Nonlin` to `Compile`) | 133 | 8511 | chain | green |
| targeted `LeanNCD.Eval.Plan.Compile` | `Compile.lean` only (second edit) | 48 | 8511 | 1 (16 s compile) | green |
| library `LeanNCD` | after the targeted builds above, plus `Structural.lean`, `Eval/Nonlin.lean`, `Eval/Scan.lean` (not yet built) | 348 | 8615 | 42 | green |
| library `LeanNCD` | `Compile.lean` only | 106 | 8615 | 8 | green |
| `JaxExperiment` | first run (rank set on every step mask, see (h)) | 57 | 8526 | 2 + 1 failed | FAILED (`ScanAffineEmitTest`) |
| `JaxExperiment` | final production | 44 | 8526 | 3 | green |
| single test module `Eval.Plan.ScanTest` | final production | 33 | 8495 | 1 | green |
| full `Tests` | final production, library already built | 837 | 8842 | 149 | FAILED (2 modules, see (e)) |

Cost model [judgment from these numbers]: a lake invocation costs about 25-30 s of overhead even
for one module; a `Plan/Nonlin.lean` change costs about 6 minutes of library rebuild; the full
`Tests` run about 14 minutes. Tests was blocked behind two failing modules, so a green `Tests`
run (more modules compiled) will take at least as long.

## (b) Edit list (production commit)

- `RawAxiswisePlan.maskContextRank : Nat := 0` @ `LeanNCD/Eval/Plan/Nonlin.lean`: new field, docstring updated.
- `NonlinPlanError.maskContextRankMismatch (contextRank actual : Nat)` @ `LeanNCD/Eval/Plan/Nonlin.lean`: new constructor.
- `checkAxiswiseCore` @ `LeanNCD/Eval/Plan/Nonlin.lean`: new `contextRank` argument; refuses a rank that is neither 0 nor `contextRank`; leaf width is `shape.size + maskContextRank`.
- `checkAxiswise`, `checkAxiswiseF32` @ `LeanNCD/Eval/Plan/Nonlin.lean`: trailing `(contextRank : Nat := 0)`; the top-level caller (`EvalPlan.lean`) is unchanged and so requires 0.
- `axiswiseIncluded` @ `LeanNCD/Eval/Plan/Nonlin.lean`: takes `ctx : List Int`; evaluates on `tensorCoord ++ ctx` when rank > 0 (rank 0 ignores `ctx`); a `ctx` whose length differs from the rank fails as `predicateWidthMismatch`.
- `axiswiseIncludedPredicate` @ `LeanNCD/Eval/Plan/Nonlin.lean`: passes `[]`; rank-0 behaviour byte-identical, rank > 0 refused.
- `runDenseAxiswiseAt`, `runDenseAxiswiseAt32` @ `LeanNCD/Eval/Plan/Nonlin.lean`: NEW workers taking `ctx`; `runDenseAxiswise`/`runDenseAxiswise32` keep their signature as wrappers passing `[]` (DEVIATION from the brief, which said to change the worker signatures: this keeps the 17 test call sites and the `EvalPlan.lean`/`Dense32.lean` callers unchanged).
- `checkPlanBlockCore` `.axiswise` arm @ `LeanNCD/Eval/Plan/Block.lean`: passes `block.contextShape.size`.
- `runDenseBlockWith`, `runDenseBlock`, `runDenseBlock32` @ `LeanNCD/Eval/Plan/Block.lean`: the axiswise worker takes `ctx`; the block passes its own `ctx`.
- `lowerMaskPredicate` @ `LeanNCD/Eval/Plan/Compile.lean`: trailing `(contextUids : List UID := [])` appended to the basis; the base and top-level sites are unchanged (partial application fills the default).
- `compileScan` scan-step `.axiswise` arm @ `LeanNCD/Eval/Plan/Compile.lean`: basis `outputUids ++ ctxUids` and `maskContextRank := ctxUids.length` ONLY when the mask mentions an iteration axis (`BoolExpr.traverseAxes`); otherwise rank 0 and an unchanged plan. Per-step intermediates go through this same loop (`recurParts`, `scratchSlotOf`) [read].
- `finalizeScans` mask guard @ `LeanNCD/DSL/Pipeline/Structural.lean`: new local `stepScanAxes` (state recurrence: its component; per-step intermediate: the component holding its `dep`); visible set = own `.free`/`.freeNorm` axes ++ `stepScanAxes`.
- `coordMap`, `AxiswiseFn.apply`, `applyNonlin` @ `LeanNCD/Eval/Nonlin.lean`: optional `context : HashMap UID Int := {}` used as the base map.
- `evalStmtSliceSeeded` @ `LeanNCD/Eval/Scan.lean`: optional `maskContext := {}` passed to `applyNonlin`; `evalScan`'s STEP loop passes `(maskContext := seed)`, the base loop passes nothing.
- `JaxCodegenError.axiswiseContextMask (nodeIndex maskContextRank : Nat)` and `buildAxiswiseInclude` @ `experiments/jax_bridge/EvalPlanCodegen.lean`: refuses any `maskContextRank ≠ 0` first; both renderers (`renderAffinePlanNamed` via `renderAxiswiseNode`, and `renderScanBlockNodes`) funnel through it [read].

Diff: 7 files, +134 / -60.

## (c) Consumers of `RawAxiswisePlan` / an axiswise mask

Class: R = must change and did; F = must refuse rank > 0 and does; I = ignores the mask or the rank (does it stay correct with the default?).

| Site | Class | Correct with the default field? |
|---|---|---|
| `checkAxiswiseCore`/`checkAxiswise`/`checkAxiswiseF32` @ `Plan/Nonlin.lean` | R | yes; default context rank 0 |
| top-level `checkAxiswise raw.tensorSigs a` @ `EvalPlan.lean` | F (via the default) | yes, unchanged source |
| `checkPlanBlockCore` `.axiswise` arm @ `Block.lean` | R | yes |
| `axiswiseIncluded` / `axiswiseIncludedPredicate` @ `Plan/Nonlin.lean` | R / F | yes; rank 0 byte-identical |
| `runDenseAxiswise(32)` top-level callers @ `EvalPlan.lean`, `Dense32.lean` | F (wrapper passes `[]`, a rank > 0 plan fails `predicateWidthMismatch`; unreachable because the top-level check requires 0) | yes, unchanged source |
| `runDenseBlockWith` @ `Block.lean` | R | yes |
| `runDenseScanWith` @ `Plan/Scan.lean` (passes `q` as `ctx` to the step block, `[]` to the base block) | I, correct | yes; ctx is the step tuple in `axes` order, the same order as `ctxUids` and the reference `axUids` [read] |
| `checkScanCore` raw-step walks @ `Plan/Scan.lean` (two `.pointwise _ \| .axiswise _ => pure ()` arms) | I, SILENTLY IGNORED | yes for this slice; a mask-aware causality rule (B) must look here |
| `.axiswise _ => pure ()` @ `Executable.lean` | I, SILENTLY IGNORED | assumed yes (not inspected in depth) |
| slot/kind helpers @ `EvalPlan.lean` (source/dest slots, step kind, readiness arms), `RawStep.lean` (slots, `contextShape? = none`) | I | yes; no mask use |
| `compileScan` base-block site and top-level site @ `Compile.lean` | I (rank 0 by default) | yes, intended |
| `buildAxiswiseInclude` @ `EvalPlanCodegen.lean` | F | yes |
| `lowerPlan`/`generateForward` einsum path @ `EvalPlanCodegen.lean` (`.axiswise _ => unsupportedStep`) | F (all axiswise) | yes |
| 4 hand-built `RawAxiswisePlan` in `EvalPlanCodegen.lean`, `EvalPlanNonlinSmoke.lean` (rewraps steps whole), `EvalPlanAffineCorpus.lean` | I | yes (`JaxExperiment` green) |
| test constructions: `NonlinCheckTest` 12, `NonlinDenseTest` 3, `NonlinDense32Test` 1, `GraphCheckTest` 1, `BlockTest` 2, `ExecutableTest` 1 | I (rank 0) | yes: all compiled and passed in the `Tests` run |
| source-level `Nonlin.axiswise` arms (`Lowering`, `RouteFragments`, `TraverseAxes`, `ScanUnroll`, `ParseLayer34Test`, ...) | not `RawAxiswisePlan` | n/a; `ScanUnroll` is item (g) |

## (d) Exhaustive-match sites forced by the new constructors

None. `NonlinPlanError` and `JaxCodegenError` are consumed only through derived `DecidableEq, BEq, Repr`
and by tests matching single constructors (`.maskWidthMismatch 1 3`, `.axiswiseIncludeRefused ...`);
no hand-written renderer or exhaustive match exists in `LeanNCD`, `test` or `experiments`
[read: grep for every constructor name]. Both builds were green without any further edit.

## (e) Full `Tests` run (one run, 837 s)

Two modules FAILED; every other module that was attempted built green.

| Module | Guard (identifier) | First message |
|---|---|---|
| `DSL.Pipeline.StructuralTest` | `compileErrOf maskOwnAxisAfterScan == some (CompileError.maskAxisNotOutput "Zz" "l")` | did not evaluate to `true` |
| `DSL.Pipeline.StructuralTest` | `layoutOf maskInterScanAxis == Except.error (CompileError.maskAxisNotOutput "Pa" "l")` | did not evaluate to `true` |
| `DSL.Pipeline.StructuralTest` | `layoutOf maskStepScanAxis == Except.error (CompileError.maskAxisNotOutput "S" "l")` | did not evaluate to `true` |
| `DSL.Pipeline.StructuralTest` | `compileErrOf maskInterScanAxis == some (CompileError.maskAxisNotOutput "Pa" "l")` | did not evaluate to `true` |
| `Eval.Plan.ScanCompileTest` | T5.3 `seededAxisZero` | `got [3, 2]/#[1.0, 3.0, 0.25, 0.75, 0.0, 0.0], expected [3, 2]/#[1.0, 3.0, 0.25, 0.75, 0.25, ...]` (values shortened; the last row now differs) |

NOT VERIFIED (blocked): lake does not build the modules that import a failed one. Direct importers
of `Eval.Plan.ScanCompileTest` that were therefore NOT compiled: `Eval.Plan.DifferentialTest`
(the expected T5.4 structural/parity failure is NOT observed), `Eval.Plan.AdapterTest`,
`Eval.Plan.ScanJaxGateTest`, `Eval.Plan.CollectPlanTest`, `Eval.ScanTest`, plus their transitive
importers. Nothing in the log imports `DSL.Pipeline.StructuralTest`. Stage 2 must re-run `Tests`
after fixing these two modules to learn the rest of the flip list.

## (f) Base-statement parity

Resolution: extend the reference mask environment ONLY for step statements. `evalStmtSliceSeeded`
takes an optional `maskContext` (default empty); `evalScan` passes `seed` only from its step loop.
So a base statement's mask over its pinned axis still reads 0 on the reference, exactly as on the
plan's base site (rank 0, empty pins). Why: it is the least invasive option (no change to the plan
base site, no change to base behaviour at all), it is exactly the owner's decision 3 (base masks stay
refused at the source, so only hand-built schedules can reach this case), and it keeps every
existing base fixture byte-identical. The alternative (feed the literal into the plan base site via
pins) would have changed a third `lowerMaskPredicate` site for a case the source refuses.

## (g) The unrolled differential

The substitution lives in `maskSubst` @ `test/Eval/PropertyOracle/ScanUnroll.lean` (imported by
`DifferentialTest`; its caller chain is `rewriteNonlin` ← `rewriteRHS`): for a scan axis that is not
a `.free`/`.freeNorm` slot of the statement it returns `some 0`. To substitute the step literal,
`rewriteRHS` already receives `stepCoord : Option (List Nat)` (`some` in the step leaf); pass
`stepCoord.isSome` into `rewriteNonlin` and `maskSubst` and return `σ u` instead of `some 0` when it
is a step (a per-step intermediate has NO iteration slot, so the slot form alone cannot tell a step
from a base; the flag is needed). The `#guard`s right after `maskSubst` (`scanAxisMask` over
`.iterAt sx 0` and `.free sx`) stay; add one for the step case. Estimate [judgment]: 6-10 changed
lines in `ScanUnroll.lean` plus 2-4 guard lines, before any `DifferentialTest` fixture change; the
T5.4 structural check that asserts no unrolled mask carries the seeded UID must be re-stated
(not read here, blocked, see (e)).

## (h) Risks and what was not verified

- First design set the rank on EVERY masked step statement; `JaxExperiment` then failed in
  `ScanAffineEmitTest` (5 guards: the transformer scan fixture's masked step was refused by the new
  `axiswiseContextMask`). Fixed by giving rank > 0 only to a mask that mentions an iteration axis;
  this keeps every existing JAX scan fixture byte-identical. It also means a later JAX slice only
  has to handle genuinely step-aware nodes.
- No new test was written (stage 1 rule), so the new semantics are exercised only by the flipped
  `seededAxisZero` fixture; reference/plan agreement on a step-aware mask is NOT verified, nor is
  the f32 worker on a step-aware mask, nor `maskContextRankMismatch` firing.
- `Eval.Plan.DifferentialTest` and other importers of `ScanCompileTest` were not compiled (see (e)).
- The Python JAX runtime and `.py` corpus were not touched or run; the Lean codegen refuses the
  only new plan shape, so no emitted artefact should change [judgment, not observed].
- `Executable.lean`'s `.axiswise _ => pure ()` arm was not read in depth.
- Docs not updated: `LeanNCD/Eval/Plan/AGENTS.md` code-map row for `Nonlin.lean`, the
  `jax_scan_record.md` section 26 policy text and the `StructuralTest` header comment still state
  the coordinate-0 rule (Rule 14: parked for stage 2, about one dispatch with the tests).

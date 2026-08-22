# Authoring report — nonlinearity-in-scans plan (2026-08-21)

## What this covers

A scratch report for the plan at `2026-08-21-nonlinearity-in-scans.md`. Not part of the plan itself.

## What was verified

Read in full: the design spec (`docs/superpowers/specs/2026-08-21-nonlinearity-in-scans-design.md`),
the Thread 4 plan (`2026-08-20-thread-4-nonlinearity.md`, for structure/rigor calibration), and the
following production files directly (not summarized from memory or from the design doc's own
citations): `LeanNCD/Eval/Plan/Compile.lean` (in full — `checkNonlin*`, `checkScanLHSSlot`,
`checkLHSSlot`, `checkStmt`/`checkScanBlockStmt`, `freeUidOrFail`, `resolveNonlinAxis`,
`residualizeAssignment`, all six phases of `compileScan`, `prepareEvalPlan`'s `.plain` branch),
`LeanNCD/Eval/Plan/Block.lean`, `RawStep.lean`, `Nonlin.lean`, `Scan.lean` (in full), `EvalPlan.lean`
(in full), `LeanNCD/DSL/Pipeline/Lowering.lean`'s `splitStmt`/`splitScan`, `LeanNCD/DSL/Ast.lean`'s
`LHSSlot`/`Nonlin`/`RHSExpr`/`ProdTerm`/`Factor`/`readFactors`, `Error.lean`'s `ScanCompileError`/
`NonlinCompileError`, `test/Eval/Plan/BlockTest.lean` (in full), plus targeted reads of
`ScanTest.lean`, `ScanCompileTest.lean`, `CompileTest.lean`, `ScanContractTest.lean`,
`NonlinCheckTest.lean`, `NonlinCompileTest.lean`, `NonlinDenseTest.lean`, `DifferentialTest.lean`,
`ScanGen.lean`, `ScanUnroll.lean`, `ScanOracle.lean`, `LeanNCD/Eval/AGENTS.md`, and
`papers/jax_evalplan_architecture.md`.

Six Lean snippets were drafted and compiled via `.claude/skills/slice-plan/check-snippet.sh`, all
green in their final (post-rename) form:

1. **Split-pair recombination** — run against the REAL `splitStmt` (not a hand-simulated shape): a
   genuine `Stmt.assign "Y" [.free i, .freeNorm j] {nonlin := .axiswise .softmax none}` was run
   through the real `splitStmt`, confirming its exact output shape (a `%nl`-prefixed linear half with
   `.freeNorm` degraded to `.free`, a trivial-read nonlin half keeping the original marker), then fed
   through the drafted `recombineNonlinSplitPairsCore`, confirming it reconstructs the original
   statement's `name`/`slots`/`nonlin`/`body` exactly.
2. **`retainedAxisPos`** (the local-axis remap) — six cases, including the design doc's own worked
   example (iteration slot before the marker) and a multi-axis, non-trailing-advancing-dimension
   case.
3. **`chainNonlinStep`/`NonlinChainedStep`** (the shared chaining helper) — three cases against the
   real `AssignPlan`/`RawPointwisePlan`/`RawAxiswisePlan`.
4. **`WiringNode`/`checkStepGraph`** (the generalized wiring loop) — instantiated independently
   against the block call site's real types (`BlockError`/`CheckedAssignPlan`/`checkAssign`) and the
   outer call site's real types (`PlanStepError`/`CheckedPlanStepEvidence`/`checkPointwise`),
   confirming one signature serves both — this directly resolves the design doc's own open item
   about this signature (left unspecified there) rather than guessing at one.
5. **`BlockStep`/`CheckedBlockStepEvidence`** — compiled alongside snippet 4, against the real
   `AssignPlan`/`RawPointwisePlan`/`RawAxiswisePlan`/`CheckedAssignPlan`/`CheckedPointwisePlan`.
6. **`allocateBlockSlots`** (the running slot-accounting scheme `compileScan`'s Phase 3/4 needs once
   a statement can consume one or two physical slots) — verified order-general via both a forward
   and a reversed statement sequence.

After final assembly into the plan document, two identifiers were renamed for clarity
(`recombineNonlinSplitPairsLoop` → `recombineNonlinSplitPairsCore`, `runWiringLoop` →
`checkStepGraph`); per the skill's own re-verification rule, both renamed snippets were re-compiled
in their final form before the plan was considered done — both green.

## What corrected or extended the design doc

The design doc itself held up well — no factual claim in it was found wrong. Three findings go
beyond what it explicitly states:

1. **A concrete signature for the wiring-loop generalization** (the design doc's own first "open
   item," deliberately left unresolved there). Resolved by noticing that every `PlanError`-shaped
   failure at both existing call sites is *already* embedded through exactly one caller-supplied
   wrapper function — collapsing what could have been a six-callback sketch into a single
   `liftWiring : PlanError → E` plus four per-node fields (context/destination/source/local-check).
   Verified against both real call sites independently (see snippet 4).
2. **A causality-loop dispatch gap** in `Scan.lean`'s `checkScanPlan`, not named in the design doc:
   once `RawPlanBlock.steps` becomes `Array BlockStep`, the existing per-term/per-factor causality
   loop must skip `.pointwise`/`.axiswise` entirely (their `sourceSlot` is always a freshly-allocated
   internal slot from the immediately-preceding `.assign`, never a capture) — found by re-deriving
   the chaining helper's own slot-allocation scheme, not by reading the design doc.
3. **A concrete, verified numeric prediction for `test/Eval/Plan/DifferentialTest.lean`'s
   `scanCorpusSplit` guard**, which the design doc does not attempt: `ScanGen.lean`'s `template2`
   (four of the corpus's current `unsupportedNonlin` cases) is a `.pointwise .relu` directly on a
   persistent state, carrying no `.freeNorm` marker — exactly the shape this plan admits. The pinned
   split is predicted to move from `total=17 accepted=9 nonlin=4 agg=4` to `total=17 accepted=13
   nonlin=0 agg=4`, and Task 7 is written to treat a disagreement with this prediction as a genuine
   defect to investigate, not a number to silently accept — inverting Thread 4's own "confirmatory,
   unchanged" framing for the identical guard, which was appropriate there but would be wrong here.

Two smaller, more mechanical findings, also independent of the design doc's own text: the exact
`.freeNorm` inventory (the design doc directly confirmed only the step-block `outputUids` site; this
pass independently confirmed the base-block analogue, both write-map sites, and the scratch
context-axis check — five sites total, none beyond its own list); and the exact import chain
(`Block.lean → Dense.lean → Check.lean → Graph.lean → RawStep.lean → Nonlin.lean`) that lets
`CheckedBlockStepEvidence` live directly in `Block.lean` without needing to move downstream the way
`CheckedPlanStepEvidence` had to.

## Task count and reasoning

**7 tasks**, one more than the design doc's own suggested 6-task sketch (§11), which the brief asked
to be verified/adjusted rather than copied. The design doc's own suggested task 5 bundled "relax
`checkScanLHSSlot`, merge `checkNonlin`" together with "wire `compileScan`'s Phase 3/4 to the
helper" — split here into Task 4 (preflight relaxation) and Task 6 (Phase 2/3/4 integration), because
the reviewer test genuinely separates them: Task 4's own fixtures (preflight now admits
`.pointwise`/`.axiswise`/`.freeNorm` inside a scan) are testable and independently reviewable via
`capabilityPreflight` alone, with no dependency on whether `compileScan` itself correctly compiles
what preflight now admits. A reviewer could approve Task 4 while Task 6 still has a bug, or vice
versa. Every other task boundary matches the design doc's own suggested shape (wiring-loop
generalization / `BlockStep` addition / chaining helper / Phase 1 recombination / Phase 2-4
integration / closure), each independently justified via the fixture/mutation-count criterion in its
own risk-table row.

## Confirmation

Every Lean code block in the shipped plan was `check-snippet.sh`-verified, including both renamed
identifiers in their final form. No fixture value was hand-derived without a real run backing it
(the `splitStmt` output shape, the `scanCorpusSplit` prediction, and all `retainedAxisPos`/
`chainNonlinStep`/`allocateBlockSlots` cases were checked against real code or real, verified
computation). No line numbers appear anywhere in the plan's shipped task text, completion-record
instructions, or AGENTS.md/doc-correction instructions.

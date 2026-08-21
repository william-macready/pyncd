# Thread 4 nonlinearity plan review

**Plan reviewed:** `leanncd/docs/superpowers/plans/2026-08-20-thread-4-nonlinearity.md`  
**Committed revision reviewed:** `514e2ba`

## Overall assessment

The plan is substantially better than most implementation plans: it verifies existing control flow,
names fixture donors, records mutation checks, distinguishes compile-tier from checker-tier failures,
and requires whole-branch review. However, it should be revised before execution. There are two
architectural/build blockers and several test-design inconsistencies.

## Blocking concerns

### 1. The three new test modules are absent from the default build

The plan creates:

- `NonlinCheckTest.lean`
- `NonlinDenseTest.lean`
- `NonlinCompileTest.lean`

but no task edits `leanncd/lakefile.toml`. The test library uses an explicit `globs` list, so the
final `lake build` gate will not include these tests unless they are added there.

This undermines the main definition-of-done claim: a green full build could silently exclude all
new nonlinearity tests.

**Recommended revision:**

- Add `leanncd/lakefile.toml` to Tasks 1-3, adding each new module as it lands.
- Make the production file discoverable when first introduced, rather than waiting until Task 7 to
  import it from `LeanNCD.lean`.
- Add a gate confirming that the new modules appear in the test glob list and are exercised by the
  default build.

### 2. The numeric-contract design conflicts with the normative architecture

Task 4 deletes `NumericMode` and `RawEvalPlan.numericMode`. But
`papers/jax_evalplan_architecture.md` says:

- the raw plan carries `reference64SumProduct`;
- nonlinear steps are governed by a distinct `reference64Transcendental` contract;
- separate nonlinear steps carry that evidence independently;
- closing `reference64SumProduct` as a `NumericMode` is completed architecture work.

Task 5 proposes editing only two passages, leaving many normative sections and appendices false
after deletion. More fundamentally, the proposed raw nonlinearity plans contain only `fn`; they do
not represent the `reference64Transcendental` contract or evidence at all.

The plan also says named Lean ULP constants will exist, but no task, file list, fixture, or
definition-of-done item creates them.

**Recommended revision: choose one coherent design.**

1. Prefer retaining the existing numeric contract and explicitly representing the nonlinear
   contract/evidence on the new checked step types; or
2. Make numeric-mode deletion a separate architecture migration, with a repository-wide
   documentation audit and a replacement representation for both sum-product and transcendental
   semantics.

At minimum, Task 4 should not remain a "mechanical cleanup" inside this slice. It changes the
semantic model central to the feature.

## Important correctness and test concerns

### 3. The self-aliasing regression fixture expects the wrong error path

The proposed fixture chains:

```text
.assign destinationSlot := 1
.pointwise sourceSlot := 1, destinationSlot := 1
```

and expects `invalidForwardRead`.

But the assignment has already produced slot 1. `checkPlan` checks destinations before sources, so
the pointwise step will fail as `duplicateDestination`, not `invalidForwardRead`.

The plan's mutation case then proposes adding an "actually already-produced" slot, but the original
fixture already has one.

**Recommended revision:** use two separate fixtures:

- A pointwise step with `sourceSlot == destinationSlot` where that slot is initially unavailable,
  proving `invalidForwardRead`.
- A chain where the slot was produced earlier, proving `duplicateDestination`.

### 4. `resolveNonlinAxis` intentionally changes legacy semantics without identifying the change

The proposed resolver rejects:

- `.freeNorm` on identity or pointwise nonlinearities;
- multiple `.freeNorm` markers.

The existing legacy resolver always admits identity and pointwise without inspecting markers, and
uses the first marked axis for axiswise nonlinearities.

The new behavior may be preferable, but it is not merely "consistency checking"; it narrows the
accepted source language relative to `evalScheduled`. That matters because the plan advertises
differential agreement with the legacy evaluator.

**Recommended revision:**

- Explicitly decide whether Backend Eval IR preserves legacy acceptance or intentionally tightens
  it.
- If tightening, document the semantic delta and add fixtures showing `evalScheduled` accepts while
  `prepareEvalPlan` rejects for the intended reason.
- Include multiple-marker axiswise and marked pointwise/identity cases in the case matrix.

### 5. Mask handling is architecturally incomplete and internally contradictory

The plan deliberately omits masks from `RawAxiswisePlan`, while the architecture says the axiswise
step mirrors the AST and carries its optional predicate explicitly.

There is also a direct prose contradiction:

- masked axiswise is rejected with `NonlinCompileError.maskedAxiswiseNotSupported`;
- shortly afterward, the plan says `CapabilityError.maskOrPredicate` is reused verbatim.

The UID-free predicate-lowering problem is real, but the plan must distinguish:

- representing a mask in raw IR;
- validating or lowering it;
- executing it in Dense.

If mask representation is intentionally deferred, revise the architecture and describe this slice
as implementing the **unmasked admitted subset**, rather than claiming that the new cases mirror
`Nonlin`'s AST shape.

## Plan execution improvements

### 6. Fixture and mutation counts are materially understated

Task 1 is estimated at approximately six fixtures, but its fixture list contains at least:

- two passing baselines;
- two slot-range failures;
- two dtype failures;
- two shape failures;
- one axis-range failure;
- scalar pointwise and axiswise cases.

That is roughly 10-11 assertions before delegation and mutation coverage.

Also, `dtypeMismatch` is classified as vacuous, yet the mutation instructions say to remove every
guard and observe its corresponding fixture fail. No fixture can reach `dtypeMismatch` while
`dtypeNotAdmitted` rejects non-`f64` values first.

**Recommended revision:** state exact assertion and mutation-cycle counts, and classify
`dtypeMismatch` as structurally unreachable under the current dtype vocabulary rather than
promising an impossible mutation test.

### 7. Task 3's gate contradicts its own risk section

Task 3's gate runs only its two compile-test modules plus `LeanNCD`. Later, the risk section
correctly says Task 3 **must run the full `Eval.Plan.*` suite** because it modifies the sole
production compiler path.

The stronger requirement should be in Task 3's actual gate.

### 8. The dependency graph is optimistic

Task 2 edits the file created by Task 1 and needs Task 1's raw and checked types, so it is not
genuinely parallel with Task 1. "Can start drafting" is not a task dependency model.

Similarly, Task 5 writes that support "landed" but is shown as independent of Tasks 1-3. It should
either depend on the implementation or be folded into closure. The doc-only task is too small to
justify a separate dispatch and risks describing a design that changes during Task 3.

### 9. Discoverability updates are incomplete

Task 7 updates the Plan file table and "Add a new nonlinearity," but
`LeanNCD/Eval/AGENTS.md` also documents every `PlanCompileCause` category. Adding `.nonlin` without
updating that row leaves the primary error-triage entry point stale.

### 10. Clean up contradictory or stale drafting text

Before execution, correct:

- The self-correcting error-wrapping paragraph, which first instructs
  `.assign (.nodeError ...)` and then reverses itself to `.nonlin` in the same item.
- `shape := #[2]` being described as rank 2 with valid positions 0-1; it is rank 1.
- The axiswise fixture's phrase "`#[1,3,2,2]`-shaped source"; that appears to confuse tensor data
  with shape.
- The manual downstream orphan `BEq` instances. Adding `BEq` at the enum definitions in
  `DSL/Ast.lean` is cleaner ownership and avoids future duplicate-instance conflicts.

## Recommended revision order

1. Resolve the numeric-contract and mask-representation decisions.
2. Add `lakefile.toml` wiring and move discoverability imports earlier.
3. Correct the self-alias fixture and source-semantics policy.
4. Recompute exact fixture and mutation counts and strengthen Task 3's gate.
5. Simplify the task graph, especially by folding documentation into closure.
6. Re-run snippet verification after revising the assembled plan.

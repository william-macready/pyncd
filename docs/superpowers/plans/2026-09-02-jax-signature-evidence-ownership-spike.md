# JAX Signature and Evidence Ownership Spike Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: use
> `superpowers:subagent-driven-development`. Run every implementer and reviewer
> with GPT-5.6 Sol, high effort, and long/1M context. This is a disposable API
> spike: commit each temporary variant so it is auditable, revert it before
> testing the other variant, and retain only the measured decision record.

**Goal:** Decide where JAX source-dtype support context must live so no
Boolean-source assignment can be rendered, converted into a candidate, or
stamped `orderedReference64`, while all-real standalone and plan-level APIs
remain usable.

The spike compares two real, compiling production-API prototypes:

- **Variant A - candidate-owned context:** every standalone kernel candidate
  owns the complete signature table and the evidence invariant is checked from
  that stored semantic context.
- **Variant B - validator-supplied context:** standalone renderers and
  validators require explicit signature context, while plan-level paths derive
  it from `PreparedPlan.plan.raw.tensorSigs`; validated kernels retain enough
  context for their evidence proposition to remain checkable.

The preferred hypothesis is Variant B because it can preserve one plan-level
signature authority instead of copying a complete table into every candidate.
That is not the decision: Variant B wins only if the plan-authority
substitution, public-entry-point mutations, and all-real ergonomics gates
below pass.

**Execution model:** Four sequential review units after controller setup.
Variants A and B start from the same temporary Boolean-source admission
baseline and are independently rejectable. The final task retains evidence and
removes every temporary Lean change.

**Authored against:** `199dc4a`.

## Scope

### Included

- One temporary checker shim admitting a `bool` source into an `f64`
  real-sum-product assignment. This is the minimum future Slice 4 behavior
  needed to construct the support hole; it does not admit Boolean destinations.
- One shared identity-assignment harness with all-real, Boolean-source, located
  two-step, and plan-authority substitution cases.
- Compiling Variant A and Variant B changes across every public semantic path
  in `Executable.lean` and `EvalPlanCodegen.lean`.
- Call-site migration for every current JAX driver so ease of use is measured
  rather than guessed.
- Fail/restore/pass mutations proving that source dtype, standalone context,
  plan-level authority, public entry points, and evidence construction are
  actually gated.
- A retained results paper and a measured update to Task 5 of
  `papers/boolean_predicate_output_evalplan.md`.

### Excluded

- No production Boolean-output algebra, constants, destination admission,
  declaration resolution, scan signature work, or corpus expansion.
- No JAX execution for Boolean, tropical, unary, Iverson, nonlinear, or scan
  semantics.
- No native Boolean storage, truth-value validation, coercion, or `f32`.
- No deletion of standalone assignment APIs. Low-level helpers may become
  private only when their nearest retained public caller is tested.
- No weakening of `ExecutionEvidence`, private constructors, affine-table
  validation, einsum validation, or plan-level step correspondence.
- No redesign of `CheckedAssignPlan`. For standalone APIs, the candidate-owned
  or explicitly supplied signature table is the semantic authority. For
  plan-level APIs, `PreparedPlan.plan.raw.tensorSigs` is the authority.

All temporary files and edits under `leanncd/` are reverted in Task 4. The
final implementation branch diff is documentation-only.

## Re-derived current boundary

- `CheckedAssignPlan` privately stores only `raw : AssignPlan`; it does not
  retain the `Array TensorSignature` passed to `checkAssign`.
- Both kernel candidate records store `semanticAssignment :
  CheckedAssignPlan`, but neither stores or indexes signature context.
- `candidateEvidenceLabel` returns `orderedReference64` for any affine-table
  candidate before validation.
- `validateAffineTable`, `validateEinsum`, `kernelWellFormedBool`,
  `JaxKernelWellFormed`, and `validateAndConstructKernel` inspect assignment
  structure but cannot inspect a source slot's dtype.
- `JaxExecutableCandidate.source : PreparedPlan` does retain the authoritative
  `plan.raw.tensorSigs`, but `JaxExecutableWellFormed` checks only step count,
  kernel well-formedness, and evidence aggregation. It does not tie each
  kernel's semantic context to the corresponding checked plan step.
- Plan renderers can reach complete signatures, while standalone
  `CheckedAssignPlan` renderers cannot. Raw helpers such as `lowerAssign` and
  `renderAffineNode` have even less context.
- The current checker rejects every non-`f64` read. The spike therefore cannot
  honestly demonstrate the JAX hole without the temporary admission shim.
- All current checked-plan storage remains Float-backed. The Boolean-source
  fixture changes only a signature tag; its Dense value and real destination
  algebra remain unchanged.

## Public surface inventory to classify

Task 1 must create a complete table with one row for every non-private
definition in these two modules. Each row is classified as:

1. **semantic public entry:** must receive or derive support context and reject
   the Boolean-source fixture;
2. **semantic helper:** make private or give it support context, then test the
   nearest public entry;
3. **dtype-independent primitive/data renderer:** may stay context-free, with a
   written reason why it cannot emit or certify an executable assignment;
4. **test-only fixture:** not production API.

At minimum, the semantic matrix includes:

| Layer | Definitions |
|---|---|
| Einsum lowering/rendering | `lowerFactor`, `lowerTerm`, `lowerAssign`, `lowerPlan`, `generateForward`, `generateNamed` |
| Affine rendering | `renderAffineFactor`, `renderAffineTerm`, `renderAffineNode`, `renderAffineNodesArray`, `renderAffineAssign`, `renderAffinePlanPositional`, `renderAffinePlanNamed`, `buildAssignFixture` |
| Candidate lowering | `loweringToAffineTableCandidate`, `loweringToEinsumCandidate`, `lowerCheckPlanToCandidate` |
| Candidate evidence/checking | `candidateEvidenceLabel`, `validateAffineTable`, `validateEinsum`, `kernelWellFormedBool`, `JaxKernelWellFormed`, `validateAndConstructKernel` |
| Executable evidence/checking | `JaxExecutableWellFormed`, `validateAndConstructExecutable` |

The inventory must separately adjudicate `TermLowering`, `NodeLowering`,
`renderTermLine`, `renderNodeLines`, `buildFactorTable`,
`recomputeAffineFactorTable`, `affineFactorTableValid`,
`affineTermTablesValid`, input/output constant renderers, and every public
utility. Do not infer safety from absence in the parent plan's list.

## Shared invariants and attacks

Both variants must enforce all of these:

1. Support is checked from the assignment destination algebra/dtype and every
   factor read's source dtype. For this spike, only `f64` destination, real
   sum-product algebra, plain `f64` reads, and no Iverson factors are supported.
2. Slot lookup is total and fail-loud. A missing source or destination
   signature is an error, never `f64` by default.
3. Standalone context is part of the semantic source against which evidence is
   claimed. The API must make that authority explicit; it need not remember
   which signature table was passed to an earlier `checkAssign` call because
   `CheckedAssignPlan` does not retain that history.
4. Plan-level context is exactly `PreparedPlan.plan.raw.tensorSigs`. A kernel
   with copied or supplied context that differs from that table cannot enter a
   `JaxExecutable`.
5. Rejection happens before Python text, candidate evidence, or executable
   construction is returned.
6. Original outer step, term, factor, and slot positions are preserved. The
   two-step fixture places the unsupported read at step 1 so a hard-coded zero
   locator cannot pass.
7. `orderedReference64` remains derivable only after support validation.
   Renaming a pre-validation label as "evidence" does not satisfy this rule.

## Task map

| Task | Purpose | Fixtures | Mutation cycles | Depends on |
|---|---|---:|---:|---|
| 0 | Prepare and baseline the isolated worktree | 0 | 0 | None |
| 1 | Inventory APIs and establish the shared future-admission harness | 4 | 2 | 0 |
| 2 | Prototype and measure candidate-owned context | Reuse 4 | 6 | 1 |
| 3 | Revert A, prototype and measure validator-supplied context | Reuse 4 | 6 | 2 reviewed |
| 4 | Decide, update Task 5, revert all Lean changes, and review | Re-run 4 | Re-run 12 | 2-3 reviewed |

Tasks 2 and 3 intentionally cannot run concurrently: both edit the same API
surface, and Variant B must start only after Variant A's revert restores the
Task 1 baseline.

## Risk sizing

| Task | Main risk | Fixtures | Mutation cycles | Reviewer rejection boundary |
|---|---|---:|---:|---|
| 1 | The future-admission shim is too broad, or the API inventory misses a bypass | 4 | 2 | The harness/inventory can be rejected before either API design is considered |
| 2 | Copied candidate context drifts from the enclosing plan or leaves a public bypass | 4 reused across all paths | 6 | Variant A can be rejected while the common harness remains valid |
| 3 | Explicit context is only advisory, is lost after validation, or is caller-selectable at plan level | 4 reused across all paths | 6 | Variant B can be rejected independently of Variant A |
| 4 | The comparison overstates evidence or temporary implementation survives | 4 rerun | 12 rerun | The decision/reversion record can be rejected without disputing either measured prototype |

The cost is dominated by rotating the context-removal mutation across every
retained public semantic entry, not by production line count. Do not split type
additions from the validator/proposition that gives them meaning.

---

## Task 0: Prepare the isolated worktree and establish the baseline

**Files:** No source edits.

- Confirm both planning documents are tracked and present:

```bash
test -f docs/superpowers/plans/2026-09-02-jax-signature-evidence-ownership-spike.md
test -f papers/boolean_predicate_output_evalplan.md
git ls-files --error-unmatch docs/superpowers/plans/2026-09-02-jax-signature-evidence-ownership-spike.md
git ls-files --error-unmatch papers/boolean_predicate_output_evalplan.md
```

- Create an isolated worktree/branch for the spike and run:

```bash
bash .claude/skills/new-slice/prepare-worktree.sh \
  --plan docs/superpowers/plans/2026-09-02-jax-signature-evidence-ownership-spike.md
```

- Require at least 95% Mathlib `.olean` coverage, then refresh project-owned
  oleans before any direct elaboration:

```bash
cd leanncd && "$HOME/.elan/bin/lake" build LeanNCD
```

- Record branch, starting SHA, local `main` SHA, donor, source/olean counts,
  percentage, exact commands, exits, warnings, elapsed time, and job counts.
- Run the preflight and both current baselines:

```bash
git status --short
git diff --check
git worktree list
rg -n '^(<<<<<<<|=======|>>>>>>>)' . --glob '!leanncd/.lake/**'
(cd leanncd && "$HOME/.elan/bin/lake" build)
(cd leanncd && "$HOME/.elan/bin/lake" build JaxExperiment Eval.Plan.ExecutableTest)
```

Any baseline failure blocks the spike. Do not repair unrelated JAX behavior.

---

## Task 1: Inventory APIs and establish the shared harness

**Temporary files**

- `leanncd/LeanNCD/Eval/Plan/Check.lean`
- `leanncd/test/Eval/Plan/ExecutableTest.lean`
- `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`

**Retained working artifact**

- Start `papers/jax_signature_evidence_ownership_spike_results.md` with the
  baseline, API inventory, fixture definitions, and current-hole observations.

### 1.1 Temporary future-admission shim

- Change only assignment read admission in `checkAssign`: allow `.f64` and
  `.bool` source signatures and temporarily remove source/destination dtype
  equality, while retaining destination `.f64`, real/tropical algebra
  admission, all shape checks, and `.f32` rejection.
- Do not add Boolean constants, algebra, destination support, or Dense changes.
- Mark the edit as disposable spike infrastructure and record its exact diff.

### 1.2 Four shared fixtures

| ID | Donor and minimal change | Required observation |
|---|---|---|
| F1 | `ExecutableTest.idRaw` / `EvalPlanCodegen.idRaw`, unchanged | Every retained all-real public API still succeeds and affine candidates receive `orderedReference64`. |
| F2 | Clone `idSigs`; change only source slot 0 from `f64` to `bool`, keep destination `f64`, `idAssign`, real algebra, and Float input unchanged | `checkAssign` and Dense semantics succeed under the shim; current JAX renderers/validators also succeed, proving the hole before either variant. |
| F3 | Clone `mixedRaw`; add a second external input slot with `bool`, make only step 1 read it, and keep step 0 all-real | Rejection must locate outer step 1; plan-level validation must use the complete plan table rather than the first assignment's context. |
| F4 | Embed F2 in a one-step `PreparedPlan` whose authoritative table marks source slot 0 `bool`; at the plan-level JAX boundary, attempt to substitute an all-`f64` table of identical shapes | The plan-level API derives context from `PreparedPlan` and rejects F2. Accepting a caller-supplied parallel table is a spike failure. |

F3 must keep step 0 and step 1 structurally valid under `checkPlan`; use unequal
source slots so step index and slot index cannot accidentally coincide.

### 1.3 Current-hole proof and inventory

- Exercise F2 through every currently public semantic path in the inventory,
  using the Boolean table as the explicit authority for standalone paths and
  F4's `PreparedPlan` for plan-level paths. Record which paths return Python, a
  candidate, an evidence label, a validated kernel, or an executable.
- Populate every row in the public-surface table. For helpers classified
  dtype-independent, state what semantic decision occurs at the nearest caller.
- Record all current call sites in `EvalPlanSmoke.lean`,
  `EvalPlanAffineSmoke.lean`, `EvalPlanAffineCorpus.lean`, and
  `ScalingProbe.lean`.

### 1.4 Two harness mutations

| ID | Mutation | Must fail |
|---|---|---|
| H1 | Restore the current `.f64`-only read check | F2 construction, proving the shim is what exposes the future hole |
| H2 | Move F3's Boolean read from step 1 to step 0 without changing the expected locator | F3 locator assertion |

Restore both mutations and rerun. Commit the Task 1 temporary baseline. An
independent reviewer must verify that the shim is no broader than planned, F4
is a real same-shape plan-authority substitution, and the API inventory has no
blank row.

---

## Task 2: Prototype candidate-owned context (Variant A)

**Temporary production/API files**

- `leanncd/LeanNCD/Eval/Plan/Executable.lean`
- `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean`

**Temporary tests and caller migrations**

- `leanncd/test/Eval/Plan/ExecutableTest.lean`
- `leanncd/experiments/jax_bridge/EvalPlanSmoke.lean`
- `leanncd/experiments/jax_bridge/EvalPlanAffineSmoke.lean`
- `leanncd/experiments/jax_bridge/EvalPlanAffineCorpus.lean`
- `leanncd/experiments/jax_bridge/ScalingProbe.lean`

### 2.1 Required shape

- Give both kernel candidate records one complete signature-context value, not
  per-slot copied dtype flags.
- Make candidate well-formedness re-establish `checkAssign` for the same raw
  assignment under that stored context and then enforce the JAX support policy.
- Tie every plan-level kernel context to the corresponding assignment in
  `PreparedPlan.plan.raw.tensorSigs`; step count alone is insufficient.
- Make pre-validation evidence labeling unavailable as a public success-shaped
  result. Either make the raw label helper private or require a validated
  support witness.
- Thread candidate-owned context through every public renderer/lowerer that
  emits assignment semantics. Context-free semantic helpers must become
  private and be covered through their nearest public caller.
- Update every current all-real JAX driver call site. Record repeated full-table
  copies and proof obligations per plan step.

### 2.2 Six mutation cycles

| ID | Mutation | Must fail |
|---|---|---|
| A1 | Skip source-slot dtype validation but retain destination/algebra validation | F2 across both rendering modes and both candidate kinds |
| A2 | Allow F4's all-real candidate context to differ from `PreparedPlan.plan.raw.tensorSigs` | F4 plan-authority assertion |
| A3 | Remove the equality/tie between a step candidate's context and `PreparedPlan.plan.raw.tensorSigs` | F3 executable construction |
| A4 | Leave one retained public semantic renderer or lowering helper context-free | Its direct F2 entry-point assertion |
| A5 | Restore public pre-validation `candidateEvidenceLabel` behavior | F2 must be able to observe `orderedReference64`, so the gate fails |
| A6 | Hard-code rejection locator 0 | F3 exact step-1 payload |

For A4, rotate through every retained public semantic entry, not one exemplar.
Record each failure and restored pass. Build all callers after every API-shape
change.

### 2.3 Variant A decision data

Record exact public signatures, structures changed, candidate size/context
duplication, caller edits, proof obligations, error locators, commands, and
mutation observations. Commit Variant A and run independent specification and
code-quality reviews. Then create an explicit revert commit that restores the
Task 1 tree exactly; verify with a scoped diff before Task 3.

---

## Task 3: Prototype validator-supplied context (Variant B)

Use the same files, fixtures, commands, and reviewers as Task 2. Start only
after Variant A's revert is proven to restore the Task 1 baseline.

### 3.1 Required shape

- Keep complete signatures outside the raw public candidate records.
- Require explicit signature context at standalone semantic render/lower and
  candidate-validation boundaries.
- Derive plan-level context only from
  `PreparedPlan.plan.raw.tensorSigs`; callers cannot substitute a parallel
  table on that path.
- Retain sufficient context in the validated `JaxKernel`/`SomeJaxKernel`
  witness, or index its well-formedness by that context, so
  `orderedReference64` remains checkable from the stored validated value.
- Tie each stored kernel context and assignment to the corresponding
  `PreparedPlan` step in `JaxExecutableWellFormed`.
- Treat the explicitly supplied standalone table as that API's semantic
  authority, but do not expose a second caller-selectable table at plan-level
  boundaries.
- Keep all-real call sites direct: one explicit context at the nearest public
  boundary, not repeated dtype arguments at each recursive helper.

### 3.2 Six mutation cycles

| ID | Mutation | Must fail |
|---|---|---|
| B1 | Skip source-slot dtype validation | F2 across both rendering modes and candidate kinds |
| B2 | Accept a caller-supplied all-real table at F4's plan-level boundary instead of deriving the table from `PreparedPlan` | F4 plan-authority assertion |
| B3 | Let plan-level callers provide context instead of deriving it from `PreparedPlan` | F3 executable construction with a substituted all-real table |
| B4 | Drop context at one retained standalone semantic API | Its direct F2 entry-point assertion |
| B5 | Construct `JaxKernel .orderedReference64` from structure-only validation before support validation | F2 kernel/evidence assertion |
| B6 | Validate every executable step with one cached first-step context | F3 exact step-1 rejection |

Rotate B4 through the complete retained public surface. Record each failure and
restored pass.

### 3.3 Variant B decision data

Record the same measurements as Variant A, plus the number of explicit context
arguments and whether validated kernels duplicate or reference context. Commit
Variant B and run independent specification and code-quality reviews. Do not
select B merely because it was the preferred hypothesis.

---

## Task 4: Decide, update Task 5, revert, and review

### 4.1 Selection criteria

Apply these in order:

1. No public path can return Python, a reference candidate/evidence value, a
   validated kernel, or an executable for F2 or F3.
2. F4 cannot override plan-level support context; the evidence proposition is
   checkable from the candidate or validated kernel's own stored semantic
   source/context.
3. Plan-level context has one authority:
   `PreparedPlan.plan.raw.tensorSigs`.
4. Direct standalone APIs fail loud and keep complete locators.
5. F1 callers remain straightforward, with no repeated per-helper context
   plumbing.
6. The design changes the fewest stable public types without hiding the hole
   behind private, untested entry points.

If neither variant satisfies criteria 1-4, report **STOP** and do not invent a
third architecture inside this spike. If both do, use criteria 5-6 and report
the measured tradeoff.

### 4.2 Retained evidence

Complete `papers/jax_signature_evidence_ownership_spike_results.md` with:

- baseline and temporary-shim SHAs;
- the complete public-definition classification table;
- F1-F4 constructions and observed current/A/B results;
- every public signature tested in both variants;
- all 12 mutation fail/restore/pass records;
- Variant A and B commits/reverts, caller diffs, build jobs/times, context
  duplication, and proof-obligation counts;
- reviewer findings and fixes/adjudications;
- the selected signatures and invariant;
- **GO A**, **GO B**, or **STOP**, with evidence.

Update `papers/boolean_predicate_output_evalplan.md` only from measured results:

- replace the section 2.5 unknown with the selected context/evidence invariant;
- replace Task 5's provisional API checklist with exact chosen signatures,
  public/private decisions, fixtures, and mutations;
- mark section 8's required spike resolved and link the results paper;
- revise Task 5 files or risk count if the measured design requires it.

Do not change semantic requirements for Tasks 1-4.

### 4.3 Revert every temporary Lean change

Revert Variant B, then the Task 1 harness/shim. Remove all temporary fixtures
and restore all JAX drivers. Keep the temporary commits and explicit revert
commits in history for audit.

Set `TASK0_SHA` to the recorded starting SHA, then verify:

```bash
(cd leanncd && "$HOME/.elan/bin/lake" build)
(cd leanncd && "$HOME/.elan/bin/lake" build JaxExperiment Eval.Plan.ExecutableTest)
git diff --check
git diff --exit-code "$TASK0_SHA" -- leanncd
git status --porcelain=v1 --untracked-files=all -- leanncd
git diff --name-status "$TASK0_SHA"...HEAD
```

The final `leanncd` diff must be empty. The final branch diff may contain only:

- `papers/jax_signature_evidence_ownership_spike_results.md`;
- `papers/boolean_predicate_output_evalplan.md`.

### 4.4 Final whole-branch reviews

Run two independent GPT-5.6 Sol, high-effort, long/1M-context reviews:

1. **Evidence ownership and API completeness:** verify F4 plan authority,
   plan-level signature authority, every non-private definition's
   classification, all public entry gates, evidence construction, locators,
   and the A/B decision.
2. **Mutation integrity, reversion, and plan accuracy:** verify all 12
   fail/restore/pass cycles, exact restoration to Task 0 under `leanncd/`,
   measured rather than predicted claims, and the updated Task 5 checklist.

Fix or explicitly adjudicate every finding, rerun the affected mutations and
both builds, then repeat the relevant review lens.

## Validation commands

Build edited production modules before any importing test or JAX target:

```bash
(
  cd leanncd
  "$HOME/.elan/bin/lake" build \
    LeanNCD.Eval.Plan.Check \
    LeanNCD.Eval.Plan.Executable
  "$HOME/.elan/bin/lake" build \
    Eval.Plan.KernelCheckTest \
    Eval.Plan.ExecutableTest \
    JaxExperiment
  "$HOME/.elan/bin/lake" env lean \
    experiments/jax_bridge/EvalPlanAffineCorpus.lean
)
```

For each variant, also run the existing all-real drivers:

```bash
(
  cd leanncd
  experiments/jax_bridge/run-evalplan.sh
  experiments/jax_bridge/run-evalplan-affine.sh
  experiments/jax_bridge/run-evalplan-affine-corpus.sh
  experiments/jax_bridge/run-scaling-probe.sh
)
```

These runner paths were verified at authoring time. If one moves before
execution, update this plan in the primary branch before dispatch rather than
silently substituting a command.

## Stop conditions

Stop rather than improvise if:

- F2 cannot be constructed without Boolean destination/algebra work or a
  broader checker change than the source-read shim;
- F4 can still substitute plan-level signature authority;
- any public semantic path cannot receive/derive context and cannot safely be
  made private behind a tested public caller;
- plan-level validation cannot tie kernel context to the corresponding
  `PreparedPlan` step without redesigning checked-plan storage;
- either variant weakens private-constructor evidence, affine/einsum semantic
  validation, or all-real behavior;
- a mutation remains green;
- a final reviewer finds a load-bearing evidence or API-completeness defect.

## Authoring verification record

- All existing paths named in task file lists and all four runner paths were
  verified present at `199dc4a`. The results paper is intentionally a new
  retained deliverable.
- The current boundary was re-derived from `CheckedAssignPlan`, both candidate
  records, both validator chains, `JaxExecutableWellFormed`, and the public
  definitions/call sites in `EvalPlanCodegen.lean`; it was not copied from the
  parent plan.
- The temporary shim requirement was checked against `checkAssign`: both the
  `.f64`-only source admission and source/destination equality must change for
  a `bool` source to reach a real destination.
- F3 distinguishes step location by placing a valid all-real step before the
  Boolean read. F4 distinguishes standalone context from plan authority by
  using equal-shaped Boolean and all-real tables while fixing the authoritative
  table inside `PreparedPlan`.
- This plan contains no Lean code block, so `check-snippet.sh` is not
  applicable. Bash blocks name existing repository commands and paths.

## Completion record

| Field | Required evidence |
|---|---|
| Base | Task 0 SHA, local `main` SHA, worktree branch |
| Cache/baseline | donor, source/olean counts, percentage, commands, exits, timings, job counts |
| Harness | shim diff, F1-F4, current-hole observations, complete API inventory |
| Variant A | commit/revert, exact signatures, 6 mutations, caller migration, two reviews |
| Variant B | commit/revert, exact signatures, 6 mutations, caller migration, two reviews |
| Plan authority | F4 substitution rejected or unconstructible in the selected design |
| Revert | empty `leanncd` diff from Task 0 and green default/JAX builds |
| Documentation | results paper and exact parent Task 5 update |
| Final reviews | reviewers, findings, fixes/adjudications |
| Recommendation | GO A / GO B / STOP with ordered-criteria evidence |

The spike is complete only when both variants compiled against the same
harness, all 12 mutations failed at their named fixtures and passed after
restoration, the selected design closes F4, all temporary Lean changes are
reverted, both final builds are green, and both whole-branch reviews are clean
or adjudicated.

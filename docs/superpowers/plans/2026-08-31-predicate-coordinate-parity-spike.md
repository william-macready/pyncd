# Predicate Coordinate-Parity Spike Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: use
> `superpowers:subagent-driven-development`. Run every implementer and reviewer
> with GPT-5.6 Sol, high effort, and long/1M context. This is a disposable
> semantic spike: commit temporary Lean work so it is auditable, then revert it.

**Goal:** De-risk the two different coordinate environments that predicate
consumers require before the production `FactorPlan` migration:

- Iverson factors use the ordered basis `context ++ output ++ per-term
  reduction`, with base pins substituted into every affine leaf.
- Axiswise masks use only the statement's local non-seeded output coordinate.
  A seeded scan UID is absent and therefore evaluates as zero; a non-seeded
  free slot remains visible.

Determine whether one minimal UID-free positional predicate representation and
one evaluator can support both policies without semantic drift.

**Execution model:** Three sequential review units after controller setup.
Tasks 1 and 2 are intentionally independently rejectable. Task 3 retains
evidence but removes every temporary implementation change.

**Authored against:** `1982cde`.

## Scope

### Included

- A temporary positional predicate representation, lowerer, and evaluator.
- Two explicit lowering entry points with different coordinate policies.
- A temporary coordinate-inclusion adapter around the existing nonlinear math.
- Temporary independent scan-unroller rewrites for both Iverson factors and
  masks.
- Ten discriminating fixtures and eleven single-fault mutation cycles.
- A retained measured-results paper that can revise the later Slice 5 plan.

### Excluded

- No production `FactorPlan`.
- No change to `TermPlan.factors`.
- No source admission and no removal of predicate or masked-axiswise
  capability rejections.
- No production mask field in `RawAxiswisePlan`.
- No Boolean tensors, dtype work, Boolean contraction algebra, corpus-count
  changes, or item 4 work.
- No JAX repair or JAX gate. `JaxExperiment` is measured pre-existing red and
  is outside this semantic spike.

All temporary files and edits under `leanncd/` are reverted in Task 3. The
final branch diff contains documentation only.

## Verified constraints

- `substitutePins` is private in
  `LeanNCD/Eval/Plan/Compile.lean`. Exercise that implementation in place or
  expose it temporarily; do not duplicate it.
- `DifferentialTest.sameAxisNameSched` and its axes are private. Temporarily
  expose those exact donors or colocate the check. Do not replace the donor
  with a weaker same-name fixture.
- Production preflight rejects Iverson factors, and `resolveNonlinAxis`
  rejects masked axiswise operations. Spike fixtures call temporary helpers or
  the source evaluator directly; they do not widen production admission.
- `ScanUnroll.rewriteFactor` currently rejects `.iverson`.
- The scan source evaluator removes seeded UIDs before calling the nonlinear
  evaluator. Because `evalIdx` maps a missing UID to zero, a recurrence mask
  cannot see the live iteration coordinate.
- A non-seeded scan axis carried by `.free`/`.freeNorm` remains in the source
  slice coordinate. If the unroller encodes that axis into a leaf name, its
  mask occurrence must be replaced by the enumerated coordinate, not zero.
- The independent unroller cannot simply preserve masks and call this result
  an independent check. It must make the source slice-coordinate policy
  explicit when it eliminates scan coordinates.
- `docs/superpowers/plans/` is tracked, but `prepare-worktree.sh` copies the
  requested plan from the primary checkout. This plan and
  `papers/predicate_boolean_backend_parity.md` must exist in the primary
  checkout before Task 0.

## Task map

| Task | Purpose | Fixtures | Mutations | Depends on |
|---|---|---:|---:|---|
| 0 | Prepare and baseline the isolated worktree | 0 | 0 | None |
| 1 | Prototype positional predicates and both lowering policies | 5 | 4 | 0 |
| 2 | Share nonlinear math and prototype independent scan rewrites | 5 | 7 | 1 |
| 3 | Close mutations, record evidence, revert, and review | Re-run 10 | Re-run 11 | 1-2 reviewed |

Tasks 1 and 2 overlap the temporary test module and cannot run concurrently.

---

## Task 0: Prepare the isolated worktree and establish the baseline

**Files:** No source edits.

- [ ] Confirm the primary checkout contains both required documents:

```bash
test -f docs/superpowers/plans/2026-08-31-predicate-coordinate-parity-spike.md
test -f papers/predicate_boolean_backend_parity.md
git ls-files --error-unmatch docs/superpowers/plans/2026-08-31-predicate-coordinate-parity-spike.md
git ls-files --error-unmatch papers/predicate_boolean_backend_parity.md
```

- [ ] Invoke `EnterWorktree` for a new branch named for the predicate-coordinate
  spike. Do not execute this plan in the primary checkout.

- [ ] From the new linked worktree root, run exactly:

```bash
bash .claude/skills/new-slice/prepare-worktree.sh \
  --plan docs/superpowers/plans/2026-08-31-predicate-coordinate-parity-spike.md
```

Require exit 0 and Mathlib `.olean` coverage of at least 95%. The script must
report a real donor and must use its plain `rsync -a` path when the destination
cache is incomplete. Stop on a missing donor, a diverged branch, a missing
plan, or sub-95% coverage.

- [ ] Before any `lake env lean`, snippet checker, or test target, refresh the
  copied project-owned oleans:

```bash
cd leanncd && "$HOME/.elan/bin/lake" build LeanNCD
```

If output suggests a cold Mathlib build--large-scale `Mathlib.*` compilation
or thousands of dependency jobs--stop immediately. Repair/re-run cache
preparation; do not wait for a cold build.

- [ ] Perform the SDD preflight conflict and ownership scan:

```bash
git status --short
git diff --check
git worktree list
rg -n '^(<<<<<<<|=======|>>>>>>>)' . --glob '!leanncd/.lake/**'
```

- [ ] Record the worktree branch, starting SHA, local `main` SHA, cache donor,
  Mathlib source/olean counts and percentage, commands, exits, warnings,
  elapsed times, and reported build job counts in the SDD ledger.

- [ ] Establish the default baseline:

```bash
cd leanncd && "$HOME/.elan/bin/lake" build
```

Any default-target failure blocks the spike. Do not run or repair
`JaxExperiment`; record its exclusion.

**Task 0 review gate:** Verify the linked-worktree guard, local-main
fast-forward, cache evidence, project-olean refresh, preflight scan, and green
default baseline before dispatching Task 1.

---

## Task 1: Prototype the positional predicate core and two lowering policies

**Temporary production files**

- `leanncd/LeanNCD/Eval/Plan/Kernel.lean`
- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/LeanNCD/Eval/Plan/Dense.lean`

**Temporary test files**

- Add `leanncd/test/Eval/Plan/PredicateCoordinateSpikeTest.lean`.
- Edit `leanncd/lakefile.toml` to add
  `Eval.Plan.PredicateCoordinateSpikeTest` to `Tests.globs`.
- Edit `leanncd/test/Eval/Plan/DifferentialTest.lean` only if exact private
  donor visibility or a colocated guard is needed.

### 1.1 Minimal representation and evaluator

- [ ] Add temporary positional arithmetic in `Plan/Kernel.lean`: one scalar
  affine leaf (coefficient array plus integer bias), multiplication, and integer
  absolute value.
- [ ] Add temporary positional Boolean expressions: relations using the
  existing `RelOp`, conjunction, disjunction, negation, and integer equality.
- [ ] Derive only the equality/representation support needed by the spike.
  Positional values contain no `AxisSpec`, UID, axis name/kind, tensor name,
  tensor slot, source `IdxExpr`, source `PredArith`, or source `BoolExpr`.
- [ ] Leave `TermPlan.factors : Array ReadPlan` byte-for-byte unchanged.
- [ ] Add the positional evaluator in `Plan/Dense.lean`. It consumes a
  positional coordinate and returns a Boolean (plus a thin `0.0`/`1.0`
  Iverson conversion for tests). It imports/calls neither `Eval.Gather` nor the
  source `evalPred`/`evalBool`.
- [ ] Fail loudly on affine-row/coordinate width mismatch. Do not use truncating
  zip behavior or a default coordinate.

### 1.2 Shared lowering core and explicit policies

- [ ] Beside private `substitutePins` in `Plan/Compile.lean`, add one temporary
  recursive source-to-positional lowering core. For every arithmetic affine
  leaf, call existing `idxToRow` and then existing `substitutePins`; recursively
  preserve every `PredArith` and `BoolExpr` constructor.
- [ ] Return enough temporary test evidence to inspect initial basis, residual
  basis, coefficient rows, and biases. UIDs may appear in this disposable
  lowering evidence, never in the positional expression itself.
- [ ] Add two named, test-visible policy wrappers. Do not expose one ambiguous
  wrapper whose caller selects an undocumented basis:
  - **factor policy:** derive the term's first-encountered contracted UIDs using
    existing `termAxisUIDs`, construct `context ++ output ++ per-term
    reduction`, and pass the real base-pin map;
  - **mask policy:** accept the local non-seeded output UID list as the complete
    basis and pass an empty pin map. A source UID absent from this basis lowers
    as coordinate zero, matching `evalIdx`'s missing-UID behavior.
- [ ] Keep `substitutePins` private and put pin-sensitive guards in
  `Compile.lean` if practical. If temporary exposure is unavoidable, record it
  and restore privacy in Task 3.

### 1.3 Five fixtures

| ID | Exact donor and minimal change | Distinguishes |
|---|---|---|
| T1-F1 | Clone `Portfolio/RelationalTest` RL1 exactly: `I[i,j] := [i=j]`, empty inputs, shape `[3,3]`. Compare the source tensor with the positional factor-policy evaluator. | Predicate-only axes are represented by the output basis; no tensor read is needed. |
| T1-F2 | Clone `Portfolio/RecurrenceTest` RC3 exactly. Lower `[j <= i]` with output `i` and per-term reduction `j`; evaluate at at least one coordinate whose truth changes if positions are swapped. | Output precedes reduction in `[i,j]`. |
| T1-F3 | Derive from `CompileTest.multiReductionSched`; append `[j < k]` as the last factor of its one term and inspect/evaluate the predicate over `[i,j,k]`. Use unequal `j,k`. | First-encountered reduction order is `j` then `k`, not reversed; predicate factor order is retained. |
| T1-F4 | Use the exact private axes and schedule from `DifferentialTest.sameAxisNameSched`; append a predicate comparing the context `"l"` UID with the distinct output `"l"` UID. Evaluate at unequal coordinates. | Identity and basis membership are by UID, never name; context precedes output. |
| T1-F5 | Derive from the second base assignment in `ScanCompileTest.multiBaseSched`. Add an Iverson predicate `abs(r * (r - 2)) = 1` using its existing `r := 1` pin. | Both nested affine leaves substitute the base pin; `r` disappears from the residual basis and the expression remains true. |

RL1 and RC3 are LSpec cases, not reusable definitions. Copy only their
program/input/expected constructions into the disposable module. T1-F4 may be
colocated with its private donor.

Every ordering/identity claim above has a differentiating construction:
T1-F2 uses unequal output/reduction coordinates; T1-F3 uses unequal reduction
coordinates; T1-F4 uses equal names but unequal UIDs and coordinates; T1-F5
has a nonzero pin and two occurrences of the pinned UID.

### 1.4 Four mutation cycles

| ID | Mutation in the temporary implementation | Must fail |
|---|---|---|
| M1 | Swap the output and reduction regions in the factor basis. | T1-F2 |
| M2 | Reverse the two reduction positions while retaining the output position. | T1-F3 |
| M3 | Replace UID densification in the temporary lowerer with a deliberately name-based basis lookup. | T1-F4 |
| M4 | Bypass `substitutePins` for predicate affine leaves. | T1-F5, by width/structure or value |

For each mutation: show the diff, run the target, record the failing diagnostic
and values, restore the correct implementation, and record the passing rerun.

### 1.5 Validation and review

```bash
cd leanncd && "$HOME/.elan/bin/lake" build \
  LeanNCD.Eval.Plan.Kernel \
  LeanNCD.Eval.Plan.Compile \
  LeanNCD.Eval.Plan.Dense \
  Eval.Plan.PredicateCoordinateSpikeTest \
  Eval.Plan.DifferentialTest
```

Success requires all five fixtures and all four fail/restore/pass mutation
cycles. Stop if the prototype needs `FactorPlan`, changes `TermPlan.factors`,
widens source admission, duplicates `substitutePins`, retains source AST in
positional data, or silently tolerates row-width mismatch.

Commit the temporary implementation/tests. Run an independent specification
review and code-quality review before Task 2. The reviewers must verify that
the two policy wrappers cannot be accidentally interchanged and that every
claimed order has an observably unequal fixture.

---

## Task 2: Share nonlinear math and prototype independent scan rewrites

**Temporary production files**

- `leanncd/LeanNCD/Eval/Nonlin.lean`
- `leanncd/LeanNCD/Eval/Plan/Nonlin.lean`

**Temporary test/oracle files**

- `leanncd/test/Eval/Plan/PredicateCoordinateSpikeTest.lean`
- `leanncd/test/Eval/PropertyOracle/ScanUnroll.lean`

`Plan/Compile.lean` may change only to reuse Task 1's existing mask-policy
wrapper. Do not add a second lowerer.

### 2.1 One nonlinear implementation, two predicate adapters

- [ ] Refactor the existing row worker in `Eval/Nonlin.lean` around a callback
  from a row entry's full tensor coordinate to **included?** Boolean.
- [ ] Preserve all public source-facing signatures and behavior. Their adapter
  constructs the current UID coordinate map and calls source `evalBool`;
  `none` always includes.
- [ ] Make only the callback-based axiswise choke point visible enough for the
  temporary Plan adapter.
- [ ] In `Plan/Nonlin.lean`, add a temporary adapter that accepts a positional
  mask separately from `RawAxiswisePlan`, evaluates it against the full local
  output coordinate, and calls the same callback-based axiswise choke point.
- [ ] Do not add a field to `RawAxiswisePlan`, copy any softmax/normalize/L2
  formula, or change checked-plan admission.

### 2.2 Independent scan-unroller policies

- [ ] Add independent recursive source-AST substitution helpers for
  `PredArith` and `BoolExpr` in `ScanUnroll.lean`. They may reuse that file's
  independent `substIdx`; they must not call checked predicate lowering,
  positional evaluation, or checked scan-worker helpers.
- [ ] For `.iverson`, substitute every eliminated scan coordinate with its
  actual coordinate from the unroller's `sigma`, preserving factor position.
- [ ] For an axiswise mask, derive substitution from the original statement's
  source seed set and LHS slots before constructing its unrolled leaf:
  - every UID in the source seed map receives zero, including a recurrence scan
    UID absent from a scratch statement's LHS;
  - an eliminated, non-seeded `.free`/`.freeNorm` scan slot receives its actual
    enumerated coordinate because it was visible in the source slice
    coordinate;
  - a non-eliminated output UID remains an axis expression.
- [ ] Recursively rewrite the optional mask with that substitution. Preserve
  the axiswise function and all non-mask RHS fields.
- [ ] Add structural checks that the rewritten recurrence mask contains no
  seeded scan UID. Runtime parity alone is insufficient: leaving the mask
  unchanged also evaluates missing UIDs as zero in the unrolled source
  evaluator and would make an omitted rewrite look correct.

The oracle is independent of checked lowering, positional evaluation, and the
checked scan worker. It is intentionally not independent of the source AST,
the source `evalScheduled` entry point, or `ScanUnroll`'s existing independent
substitution machinery.

### 2.3 Five fixtures

| ID | Exact donor and minimal change | Distinguishes |
|---|---|---|
| T2-F1 | Clone `Portfolio/NormTest` NM4 unchanged. Compare the public source wrapper and temporary positional-mask adapter. | Inclusion polarity and local output basis. |
| T2-F2 | Clone NM4; change only `normalize` to `softmax`, and change the already excluded first-row value `A[0,0]` from `1` to `1000`. | Excluded values do not participate in the softmax maximum. |
| T2-F3 | Clone `ScanCompileTest.maskedAxiswiseRecur`; change only the recurrence mask to `where l = 0` using `p15l`. Compare source scan evaluation, a manual per-slice application of the positional adapter with output basis `[p15i]`, and independent unrolling. Inspect the rewritten mask. | The seeded recurrence UID is zero/missing, not live; the mask rewrite is explicit rather than accidental. |
| T2-F4 | Derive from `ScanCompileTest.okBase` plus `badIverson "S" nextL`; change the constant predicate to `l = 0`. Compare source scan evaluation with independent unrolling. Inspect the rewritten factor. | Iverson receives actual scan substitution, so later iterations differ from an unreplaced/missing-UID predicate. |
| T2-F5 | Derive from `ScanGen.template6`: add one retained axis `i` of extent two to `G`, `Z`, and `A`; mark `i` as `.freeNorm`; put `normalize(where r != 0)` on the base assignment; use nonzero `Z` rows. Compare source evaluation and independent unrolling at both `r = 0` and `r = 1`, and inspect the rewritten base masks. | Eliminated non-seeded free scan axis `r` receives its actual enumerated coordinate; substituting zero makes the `r = 1` slice incorrectly all-masked. |

T2-F3 and T2-F4 deliberately use the same `l = 0` shape with opposite
policies. At a later recurrence step, the mask still sees zero while the
Iverson factor sees the actual iteration coordinate.

### 2.4 Seven mutation cycles

| ID | Mutation | Must fail |
|---|---|---|
| M5 | Invert callback inclusion polarity. | T2-F1 |
| M6 | Include masked values when computing the softmax maximum. | T2-F2 |
| M7 | Pass a live seeded coordinate into the positional mask adapter instead of omitting it from the output basis. | T2-F3 adapter parity |
| M8 | Substitute the live seeded scan coordinate in the unroller's mask rewrite instead of zero. | T2-F3 unrolled runtime parity |
| M9 | Leave recurrence Iverson predicates unreplaced in `ScanUnroll`. | T2-F4 runtime and structural checks |
| M10 | Leave axiswise masks unreplaced in `ScanUnroll`. | T2-F3 structural no-seeded-UID check, even if runtime still agrees |
| M11 | Substitute zero for an eliminated non-seeded free scan UID instead of its enumerated coordinate. | T2-F5 runtime and structural checks |

Record explicitly that M10 is expected to demonstrate why value parity alone
cannot prove the mask rewrite occurred.

### 2.5 Validation and review

```bash
cd leanncd && "$HOME/.elan/bin/lake" build \
  LeanNCD.Eval.Nonlin \
  LeanNCD.Eval.Plan.Nonlin \
  Eval.NonlinTest \
  Eval.Plan.NonlinDenseTest \
  Eval.Plan.PredicateCoordinateSpikeTest \
  Eval.Plan.ScanCompileTest \
  Eval.PropertyOracle.ScanUnroll \
  Eval.PropertyOracle.ScanOracle
```

Success requires five fixture comparisons, all structural rewrite checks, all
existing nonlinear behavior in the listed targets, and all seven
fail/restore/pass mutation cycles.

Stop if parity requires exposing live seeded context to masks, changing
`RawAxiswisePlan`, duplicating nonlinear formulas, calling checked lowering
from the oracle, preserving a seeded UID in a rewritten mask, or weakening
source wrappers.

Commit the temporary Task 2 work. Run independent specification and
code-quality reviews. Reviewers must separately adjudicate factor substitution,
mask substitution, callback polarity, and the oracle's precise independence
boundary.

---

## Task 3: Close mutations, record evidence, revert the spike, and review

### 3.1 Complete mutation matrix

Re-run all eleven mutations against the exact Task 1 or Task 2 command. A
mutation cycle counts only when:

1. the intended mutation is visible in the diff;
2. the named differentiating fixture fails;
3. the exact command, exit, diagnostic, structural form, and observed values
   are recorded;
4. the mutation is restored;
5. the same target and fixture pass.

If a named fixture remains green, strengthen the fixture or mark the spike
blocked. Never report an unobserved mutation as evidence.

Use this table in the retained results paper:

| ID | Task | Mutation/identifier | Tree or commit | Exact command | Fixture | Failing exit, diagnostic, and values | Restore SHA | Passing exit and values | Reviewer |
|---|---|---|---|---|---|---|---|---|---|

### 3.2 Retained evidence

- [ ] Create `papers/predicate_coordinate_parity_spike_results.md`.
- [ ] Record Task 0 and checkpoint SHAs; cache donor and coverage; all baseline
  and targeted commands, exits, warnings, elapsed times, and job counts.
- [ ] Record all ten donor/delta pairs and their source, positional, and
  unrolled observed values.
- [ ] Record positional structural forms: ordered basis, residual basis,
  coefficient widths/order, and pin-adjusted biases.
- [ ] Record both unroller structural forms and the full eleven-cycle mutation
  log.
- [ ] Audit imports/calls to show that `ScanUnroll` does not call checked
  predicate lowering, positional evaluation, or checked scan-worker code.
- [ ] Classify the factor and mask policies independently as **confirmed**,
  **revised**, or **blocked**.
- [ ] Give the later Slice 5 plan a **GO**, **REVISE**, or **STOP**
  recommendation and list unresolved risks.
- [ ] Record the JAX exclusion without attempting a repair.
- [ ] Update `papers/predicate_boolean_backend_parity.md` only if measurements
  alter its architecture, task split, fixtures, or stop conditions. Otherwise
  leave it byte-for-byte unchanged.

Do not invent expected values in advance. The results paper records values
observed from the executed fixtures.

### 3.3 Revert every temporary implementation change

Revert Task 2, then Task 1, preferably with explicit revert commits so the
experimental history remains auditable. Remove/restore all of:

- positional predicate AST and evaluator;
- source-to-positional helpers, wrappers, evidence, and guards;
- any privacy changes;
- callback visibility and temporary Plan nonlinear adapter;
- both `ScanUnroll` rewrites and structural checks;
- `PredicateCoordinateSpikeTest.lean`;
- its `Tests.globs` entry;
- any temporary donor visibility.

Commit the retained result documentation after the reverts and before the
final verification.

Set `TASK0_SHA` to the recorded pre-spike implementation SHA, then verify:

```bash
cd leanncd && "$HOME/.elan/bin/lake" build
git diff --check
git diff --exit-code "$TASK0_SHA" -- leanncd
git diff --name-status "$TASK0_SHA"...HEAD
git status --porcelain=v1 --untracked-files=all -- leanncd
test ! -e test/Eval/Plan/PredicateCoordinateSpikeTest.lean
```

The default build must pass and the `leanncd` diff must be empty. The final
branch diff may contain only:

- `papers/predicate_coordinate_parity_spike_results.md`;
- optionally `papers/predicate_boolean_backend_parity.md`, with every change
  tied to measured evidence.

The ten temporary fixtures are expected to disappear after reversion. Their
commands, values, and mutation observations persist in the results paper.

### 3.4 Final whole-branch reviews

Run two independent GPT-5.6 Sol, high-effort, long/1M-context reviews:

1. **Semantic evidence:** Verify that the record distinguishes factor versus
   mask environments, basis order, UID identity, pin substitution, callback
   polarity, masked maximum behavior, and both oracle rewrites.
2. **Reversion and documentation:** Verify that no temporary implementation
   remains, every conclusion cites a recorded command/value/structure, the
   oracle-independence claim is narrowly accurate, and the final diff is
   documentation-only.

Fix or explicitly adjudicate every finding before completion.

## Completion record

| Field | Required evidence |
|---|---|
| Base | Task 0 SHA, local `main` SHA, worktree branch |
| Cache | donor, source/olean counts, percentage, no cold build |
| Baseline | exact commands, exits, warnings, elapsed time, job counts |
| Task 1 | temporary commit, five fixtures, four mutations, two reviews |
| Task 2 | temporary commit, five fixtures, seven mutations, two reviews |
| Oracle | actual-coordinate Iverson rewrite, source-slice mask rewrite, import/call audit |
| Revert | revert SHAs and empty `leanncd` diff from Task 0 |
| Final build | exact default command, exit, warnings, elapsed time, job count |
| Documentation | retained paths and evidence for any overview change |
| Final reviews | reviewers, findings, fixes/adjudications |
| Recommendation | GO / REVISE / STOP with evidence |

The spike is complete only when all ten fixtures passed before reversion, all
eleven mutations produced recorded fail/restore/pass cycles, the restored
default build is green, no temporary implementation remains, the final diff is
documentation-only, and both whole-branch reviews are clean or adjudicated.

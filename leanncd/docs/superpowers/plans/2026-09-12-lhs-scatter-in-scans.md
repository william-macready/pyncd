# S-B — affine LHS scatter writes inside scans

**Scope:** the second slice of
[`papers/scatter_affine_lhs_writes.md`](../../../../papers/scatter_affine_lhs_writes.md):
admit positive, single-source-axis affine placement rows in scan-state base and recurrence writes,
without adding a `BlockStep.scatter`.

> **✅ S-B IS IMPLEMENTED AND LANDED — this is a completed record, not pending work.** Affine scatter
> writes into scan state are admitted for the bounded fragment this plan specifies; see the "Already
> closed" list in
> [`papers/backend_missing_functionality.md`](../../../../papers/backend_missing_functionality.md),
> which names this document as what closed that row. **Every status line, baseline commit, build
> count, capability claim, and "still rejected" list below is the authoring-time snapshot and is
> retained unmodernized** as the record of the design that was executed; do not read any of it as a
> current statement about the tree. One later fact this plan predates: the f32 slice made
> `ScalarDType.f32` a live binary32 carrier, but every scan form — scan-local scatter included — is
> refused in a binary32 schedule (slice F32-C), so nothing in this plan is reachable at binary32.

**Status (authoring-time snapshot, superseded — see the banner above):** implementation-ready. S-A
(top-level `PlanStep.scatter`) is already merged. This plan
supersedes the exact `scale * n + offset` extent rule parked in the overview's §3.2: the user chose
the stride-aligned global `LHSSlot.outExtent` design so `2*j` and `2*j+1` can initialize one state.

---

## 0. Authoring verification record

This plan was derived from the tree at `b8c0a2c` on branch
`agents/lhs-scatter-implementation-plan-scans`, with no tracked changes.

- The worktree was warm-started with the repository's standard
  `.claude/skills/new-slice/prepare-worktree.sh` path: 8,101 Mathlib oleans and 188 project oleans
  were copied from the primary checkout.
- `lake build` passed: **8,663 jobs**.
- `lake build JaxExperiment` passed: **8,514 jobs**.
- The generated scan corpus remained **17/17 accepted**.
- The scan-free generated differential corpus remained **3,832/3,832 accepted**.
- S-A's curated `scatterPrograms` corpus contains **8** source-generated cases.
- The global extent design below was compiled with
  `.claude/skills/slice-plan/check-snippet.sh` against the real `DSL/Ast.lean` API. All fourteen
  edge cases in §3.1 evaluated to the values recorded there.
- A second compiled probe removed only `checkScatterNoScan` from the real source pipeline. A complete
  base-plus-recurrence scan with affine LHS slots reached `route` successfully; the old
  `RouteFragmentDiagnosticTest.case11`, which has no base statement, moved from `scatterInScan` to
  the already-correct `missingBaseCase`. This proves route needs no scatter-specific scan change.
- Every production/test/document path named below was checked in this worktree.

### 0.1 Corrections to the parked overview

The overview remains authoritative for the slice split, the `WriteRowKind.strided` classifier,
the nine-site exhaustiveness tripwire, and the equal-scale residue collision rule. Three details are
replaced or narrowed here:

1. **Extent equality uses stride-aligned `LHSSlot.outExtent`, not the old
   `scale * n + offset` result.** For `n = 3`, both `2*i` and `2*i+1` have extent `6`.
2. **The shared extent helper is already `scatterDestExtent`.** It reconstructs a positional
   `LHSSlot` and calls `LHSSlot.outExtent`; S-B must reuse it. Do not add the overview's separate
   `synthAxis`/`stridedExtent` helper.
3. **A classifier witness cannot have both context widths for every constructor.**
   `.advancing` is intentionally unclassifiable at `contextWidth = 0`. Require both widths for
   `.free` and `.strided`, positive width plus an explicit width-zero rejection for `.advancing`,
   and width-insensitive witnesses for `.pinned`.

### 0.2 Corrections from review

Two changes made after an independent review of this plan, before any task was dispatched:

1. **Task 2's `classifyWitness` work now also closes two pre-existing, previously-unpinned
   `classifyWriteRow` checks** — the `.advancing` branch's `bias == 1` requirement and the `.free`
   branch's `bias == 0` requirement, both flagged by the original parked overview's audit as real
   but unpinned (empty firing set), and never closed since. Neither is required for `.strided` to
   work and neither predates this plan, but `classifyWitness` is being written fresh in Task 2
   regardless, so the two missing negative witnesses are added at the same cost rather than left
   open a second time. See Task 2 step 3 and its Fixtures/Mutation cycles sections.
2. **Task 1's gate now also runs `lake build JaxExperiment`**, not only Task 7's final gate.
   Nothing in Task 1 is JAX-facing, so this is a cheap, immediate confirmation rather than a
   7-task-deferred one, matching S-A's own per-task convention of checking this gate wherever it is
   plausibly reachable.

---

## 1. Goal and non-goals

### 1.1 In scope

- A global, normalized, stride-aligned extent for positive one-axis affine LHS writes.
- `WriteRowKind.strided outputPos scale offset`, admitted in both scan base and step writes.
- Exact extent checking for free and strided write rows through the shared
  `LHSSlot.outExtent` contract.
- Sound equal-scale modular disjointness for multiple base writes.
- Reference dense scan evaluation of compute-then-place scan scatters.
- Independent scan-free unrolling of the same fragment.
- Source lowering, checked-plan compilation, execution, and three-way parity for:
  - strided base writes;
  - strided recurrence writes;
  - several disjoint strided base writes to one state;
  - contractions computed densely before placement;
  - arbitrary positions of the scan dimension in state shape; and
  - more than one non-advancing affine placement dimension.

### 1.2 Deliberately out of scope

- **No `BlockStep.scatter`.** A scan statement computes a dense logical source slice through the
  existing `AssignPlan`; its `StateWriteMap` alone performs affine placement into persistent state.
- **No multiple recurrence writes per state.** `checkScanPlan` continues to require exactly one
  step write. Even/odd interleaving is therefore a base-initialization capability in S-B.
- **No diagonal scan-state writes.** Repeating one source UID across LHS dimensions remains
  `duplicateAxisInLhs`; top-level S-A diagonal scatter is unchanged.
- **No multi-axis expression within one affine slot.** `Out[i+j]` remains
  `multiAxisScatterLhs`.
- **No affine scan-context output.** An affine slot may name only a non-context placement axis.
  Context dimensions remain `.iterAt`, `.iterNext`, or the existing whole-axis `.free` base face.
- **No scatter-shaped block-local scratch.** Scratch has no persistent `StateWriteMap`; treating its
  dense source slice as its scattered destination would be a silent semantic mismatch.
- **No zero/negative stride or negative offset admission in scans.** The global extent function
  preserves their old values, but `classifyWriteRow` rejects them.
- **No non-default collision reduction and no nonlinear scatter.** Existing
  `checkScatterReduce` and `checkNonlinScatter` rules remain.
- **No nonzero scan-scatter fill.** Scan state is initialized by
  `ScanBoundaryPolicy.zeroThenBaseOverlay`; a hand-built `.scatter` with `fill != 0` is rejected
  at capability tier rather than silently ignored by state placement.
- **No predicate/bool scatter destination.** The top-level `predicateScatterDest` restriction also
  applies inside scans until the ordinary scatter evaluator is dtype-aware.
- **No broader different-scale collision theorem.** Different scales remain conservatively
  colliding even when a particular pair of finite images is disjoint.
- **No JAX scan or scatter execution.** The experimental backend remains fail-loud.

---

## 2. Global constraints

1. **One extent owner.** `LHSSlot.outExtent` remains the sole production extent formula.
   `Eval.scatterOutShape`, `SizeInfer.scatterOutputShapes`, `scatterDestExtent`, scan compilation,
   and reference scan allocation must call it rather than copy its arithmetic.
2. **Normalize by UID before selecting the aligned case.** Duplicate and cancelling terms must be
   classified by their normalized coefficient, while every syntactically mentioned UID must still
   have a size. Normalization must not turn a missing-size failure into success.
3. **The aligned case is narrow.** It applies only when normalization leaves exactly one nonzero
   coefficient `c`, `c > 0`, bias `b >= 0`, and source extent `n > 0`.
4. **The exact aligned extent is**
   `c*n + floor(b/c)*c`, equivalently `c*n + b - (b mod c)`, equivalently the smallest multiple of
   `c` strictly above the maximum written coordinate.
5. **Every fallback keeps legacy behavior.** `.const`, zero source extent, zero/negative normalized
   coefficient, negative bias, no nonzero coefficient, missing sizes, and genuinely multi-axis
   forms retain the pre-S-B result.
6. **Canonical values are fixed.**

   | Slot over `i : 3` | Extent after S-B |
   |---|---:|
   | `2*i` | 6 |
   | `2*i+1` | 6 |
   | `2*i+3` | 8 |
   | `i+2` | 5 |
   | `0*i` | 0 |
   | `-2*i+1` | 0 (legacy fallback) |

7. **Classifier order is fixed:** advancing, free, strided, reject. Moving strided before advancing
   is a correctness bug.
8. **Strided classification is exact:** one nonzero coefficient at `p >= contextWidth`,
   `coefficient > 0`, and `bias >= 0`; payload is
   `.strided (p - contextWidth) coefficient bias`.
9. **Zero coefficient remains pinned.** It produces no nonzero term and must never be classified
   as strided.
10. **Both scan phases admit strided non-advancing rows.** Advancing dimensions still require their
    exact `.advancing` rows; all other state dimensions must be `.free` or `.strided`, in ordered
    one-to-one correspondence with the dense block output basis.
11. **Bounds come from extent equality.** A strided row's required state extent is obtained by
    calling `scatterDestExtent` with its output position, scale, and offset. Do not add a
    max-coordinate formula beside it.
12. **Base disjointness rule:** two strided rows prove a dimension disjoint only when their positive
    scales are equal and their offsets have different residues modulo that scale. All other new
    pairings remain conservatively colliding.
13. **The write worker stays generic.** `applyAffine`, `commitWrite`, and `runDenseScan` need no new
    row-kind branch.
14. **Exactly one step write per state remains enforced.**
15. **All source-facing failures stay typed and located.** Capability checks precede shape,
    scan-specialization, and checked-plan failures. New scan errors identify scan name, destination,
    phase, and original statement index where applicable.
16. **No wildcard is added at any `WriteRowKind` consumer.** The nine existing exhaustiveness sites
    remain compile-time tripwires.
17. **The independent oracle must not call** `runDenseScan`, `evalScan`, `writeRowKinds`,
    `scatterDestExtent`, `LHSSlot.outExtent`, `applyAffine`, `commitWrite`, compiler
    residualization helpers, or scan-worker placement helpers.

---

## 3. Architecture

### 3.1 Stride-aligned global extent

`LHSSlot.outExtent` first resolves every raw term's size and computes the existing linear boundary.
It then normalizes coefficients by UID solely to decide whether the aligned case applies.

Observed results from the compiled design probe:

| Input | Result |
|---|---:|
| `2*i`, `i : 3` | `some 6` |
| `2*i+1`, `i : 3` | `some 6` |
| `2*i+3`, `i : 3` | `some 8` |
| `i+2`, `i : 3` | `some 5` |
| duplicate terms `i+i+1`, `i : 3` | `some 6` |
| cancelling terms `i-i+1`, `i : 3` | `some 1` |
| multi-axis `2*i+j+1`, sizes `3,4` | `some 11` |
| negative bias `2*i-1`, `i : 3` | `some 5` |
| negative coefficient `-2*i+1`, `i : 3` | `some 0` |
| `2*i+1`, `i : 0` | `some 1` |
| `0*i`, `i : 3` | `some 0` |
| `0*i+3`, `i : 3` | `some 3` |
| zero coefficient naming an unsized axis | `none` |
| `.const 3` (the `iterAt` output-index form) | `some 4` |

This is deliberately not the normalized-gcd proposal. A gcd rule would also alter genuine
multi-axis expressions such as `2*i+4*j+3`, even though both S-A and S-B reject that placement form.

### 3.2 Checked scan geometry

`WriteRowKind.strided` records the dense output position and the placement coefficient/bias. A
shared output-position projection treats `.free p` and `.strided p _ _` uniformly for ordered
cover checks. A shared row-extent check treats:

- `.free p` as the identity placement extent at `outputShape[p]`; and
- `.strided p c b` as `scatterDestExtent outputShape row b`, where `row[p] = c`.

Pinned and advancing rows have their existing, separate obligations. The checker does not inspect
which AST constructor created a row.

The case audit required in Task 2 is:

| Predicate | pinned | free | advancing | strided | none |
|---|---|---|---|---|---|
| base advancing dimension | allowed; boundary/range checked | allowed; covered | **forbidden** | **forbidden** | forbidden |
| base non-advancing dimension | allowed; range checked | allowed; covered | **forbidden** | allowed; covered | forbidden |
| step advancing dimension | forbidden | forbidden | required at matching context position | forbidden | forbidden |
| step non-advancing dimension | forbidden | allowed; covered | forbidden | allowed; covered | forbidden |
| output extent | ignored | exact identity extent | checked by history extent | exact shared affine extent | rejected earlier |
| pinned range | checked | ignored | ignored | ignored only because positive-stride extent equality proves bounds | rejected earlier |
| base collision | differing pins can separate | conservative | conservative | differing equal-scale residues can separate | conservative |

The explicit base prohibitions close two latent dimension-class cells. `contextWidth = 0` currently
makes `.advancing` unclassifiable, but `baseWriteRowsOk` itself must not silently admit a synthetic
one. A `.strided` row is reachable at base phase, so the predicate must separately reject it when
its state dimension belongs to `advancingDims`; only dense `.free` faces and pinned boundary
coordinates may span scan-advancing dimensions.

### 3.3 Compute, then place

For a scan statement such as `S[l+1, 2*j+1] := A[j,k] · B[k]`:

1. the local block computes a dense logical slice over `j`, contracting `k`, through the existing
   `AssignPlan`;
2. the block publishes that dense slice;
3. `StateWriteMap` maps `(context, j)` to `(l+1, 2*j+1)`; and
4. `commitWrite` overlays it into zero-initialized persistent state.

This is why adding `BlockStep.scatter` or directly invoking top-level `evalScatter` before
contraction would be wrong.

### 3.4 Source/compiler geometry

For each scan block statement, derive the dense output basis from LHS placement axes in first-seen
UID order, excluding axes only when their slot role is `.iterAt`/`.iterNext`. Do **not** exclude by
UID membership in the scan context: an existing base boundary face such as `.free c` over context
axis `c` is a real dense output dimension and must remain in the basis. RHS-only axes remain
reductions.

For each state placement dimension:

- `.iterAt`/`.iterNext`, and the existing free context-axis base face, use the full history extent;
- a non-context `.free`/`.freeNorm`/`.affine` slot uses `LHSSlot.outExtent`;
- an affine slot naming a scan context axis is rejected;
- all placements for one state must agree in rank, advancing-dimension position, and extent.

Placement rows use the same dense output basis:

- `.iterAt` → zero row plus literal bias;
- `.iterNext` → its context position with coefficient `1`, bias `1`;
- `.free`/`.freeNorm` → its output position with coefficient `1`, bias `0`;
- `.affine` → `idxToRow` over the output basis, prefixed by zero context coefficients in the step
  block.

The emitted block operation remains `.assign`; only the write map is strided.

### 3.5 Three genuinely different execution legs

1. **Checked plan:** dense `AssignPlan` plus `StateWriteMap`, executed by `runDenseScan`.
2. **Legacy scan evaluator:** evaluate the dense source slice with seeded assignment semantics, then
   independently place it by evaluating the original LHS index expressions.
3. **Independent scan-free oracle:** eliminate scan coordinates; for a scatter, emit a dense
   temporary assignment that performs contraction followed by a top-level scatter leaf that reads
   only that temporary; evaluate the result through the scan-free evaluator; and independently
   reconstruct histories. It separately derives expected state-slice extents, so a shared bad
   `outExtent` cannot pass merely because leaf evaluation used it.

No two legs may share a new scan-placement helper.

---

## 4. Task graph and review weight

```text
Task 1: global aligned extent ─┬─> Task 2: checked write geometry ───────────────┐
                               ├─> Task 3: legacy scan semantics ────────────────┤
                               └─> Task 4: independent oracle ───────────────────┤
                                                                                ├─> Task 6: compileScan
Task 5: DSL/preflight reachability ──────────────────────────────────────────────┘
                                                                                     │
                                                                                     ▼
                                                                                Task 7: differential,
                                                                                docs, closure
```

Tasks 2–5 are independently reviewable after Task 1. Task 4 is intentionally early: it is the
expensive independent implementation and should be available while compiler behavior is still
being built, not after every production decision has hardened. Task 6 depends on Tasks 2–5.

| Task | Outcome | Planned fixtures / mutation cycles | Risk |
|---|---|---:|---|
| 1 | Global aligned extent and S-A rebaseline | 14 edge assertions, 4 affected source/value fixtures; 4 cycles | High: global semantic boundary |
| 2 | Sound `.strided` checked geometry | 13 classifier assertions (2 closing pre-existing gaps), 9 geometry, 4 collision checks, one 102,400-case exhaustive run; 11 cycles | High: recurring write-soundness surface |
| 3 | Legacy compute-then-place semantics | 5 execution fixtures; 4 cycles | High: new reference semantics |
| 4 | Independent scan-free oracle support | 5 structural/value fixtures; 5 cycles | High: independent implementation |
| 5 | DSL and capability reachability | 12 acceptance/rejection/precedence fixtures; 4 cycles | Moderate |
| 6 | Source-to-`RawScanPlan` lowering | 8 acceptance, 10 rejection, 3 locator/order fixtures; 8 cycles | Highest: compiler centerpiece |
| 7 | Three-way corpus, docs, closure | 7 curated cases; 3 cycles; two final reviewers | High |

Counts are planned test artifacts, not production-line estimates. If an existing assertion can be
extended rather than duplicated, preserve the count by recording which listed case it replaced.

---

## Task 1 — change the global extent contract and rebaseline S-A

### Outcome

Positive one-axis affine writes use the exact stride-aligned rule in §2; every fallback remains
byte-for-byte equivalent to the old rule. Existing S-A code and tests agree on the new destination
shape.

### Files

- `LeanNCD/DSL/Ast.lean`
- `LeanNCD/Eval/Plan/Kernel.lean` (contract comment)
- `LeanNCD/Eval/Plan/Check.lean` (contract comment; no second formula)
- `test/Eval/Plan/ScatterCheckTest.lean`
- `test/Eval/Plan/ScatterDenseTest.lean`
- `test/Eval/Plan/ScatterCompileTest.lean`
- `test/Eval/Plan/DifferentialTest.lean`

### Implementation

1. Factor the affine-arm calculation inside `LHSSlot.outExtent`; do not change `.const`.
2. Resolve every raw term before normalization.
3. Normalize by UID with the existing coefficient-normalization primitive.
4. Apply the aligned rule only to the exact case in §2; otherwise return the legacy linear
   boundary's `.toNat`.
5. Update comments that name `scale * n + offset` as the universal contract.
   In the same pass, remove the now-false `checkScatterNoScan` reachability claims in
   `Check.lean`, `ScatterCheckTest.lean`, and `ScatterCompileTest.lean`.
6. Rebaseline `Out[2*i+1] := X[i]` from:
   - shape `[7]`, data `[0,1,0,2,0,3,0]`
   - to shape `[6]`, data `[0,1,0,2,0,3]`.
7. Add that shifted-stride case to `scatterPrograms` as SA9 and change its length guard **8 → 9**.
   Donor: clone SA1, change only the LHS bias and expected data.

### Tests and mutations

- Port the fourteen §3.1 observations into direct `LHSSlot.outExtent` guards.
- Mutation 1: restore old `c*n+b`; shifted-stride extent/value/corpus fixtures must fail.
- Mutation 2: skip coefficient normalization; duplicate-term fixture must fail.
- Mutation 3: stop resolving zero/cancelled raw terms; missing-size fixture must fail.
- Mutation 4: apply alignment to multi-axis or zero-size inputs; fallback fixtures must fail.

### Gate

```bash
cd leanncd
lake build Eval.Plan.ScatterCheckTest Eval.Plan.ScatterDenseTest Eval.Plan.ScatterCompileTest
lake build Eval.Plan.DifferentialTest
lake build LeanNCD
lake build JaxExperiment
```

Run `JaxExperiment` here too, not only at Task 7's final gate: nothing in this task should touch
it (the extent change lives entirely in `DSL/Ast.lean`/`Eval/Plan/Kernel.lean`/`Check.lean`
comments, none of it JAX-facing), so a clean run is a cheap, immediate confirmation rather than a
7-task-deferred one — matching S-A's own per-task convention of checking this gate whenever it is
plausibly reachable, not only at closure.

---

## Task 2 — admit `.strided` in checked scan geometry

### Outcome

Hand-built `RawScanPlan`s with positive strided base or step placement check and execute safely;
malformed geometry and unsound overlaps fail before `commitWrite`.

### Files

- `LeanNCD/Eval/Plan/Scan.lean`
- `LeanNCD/Eval/Plan/Compile.lean` (the seventh production exhaustiveness site only)
- `test/Eval/Plan/ScanTest.lean`

### Implementation

1. Add `.strided (outputPos : Nat) (scale offset : Int)` to `WriteRowKind`.
2. Extend `classifyWriteRow` in the fixed order from §2.
3. Add an exhaustive `classifyWitness` in `ScanTest.lean`:
   - `.pinned`: width `0` and positive-width witnesses, with the same result;
   - `.free`: width `0` and positive-width output-half witnesses;
   - `.advancing`: positive-width witness and explicit width-0 rejection;
   - `.strided`: width `0` and positive-width output-half witnesses.

   **Close two pre-existing, previously-unpinned checks while this function is already being
   touched and exhaustively witnessed.** The original parked overview's audit found two `classifyWriteRow`
   value checks with an empty firing set — real but unpinned by any fixture: the `.advancing` branch's
   `bias == 1` requirement, and the `.free` branch's `bias == 0` requirement. Neither is new to S-B,
   and fixing them is not required for `.strided` to work — but `classifyWitness` is being written
   fresh right here, so add the two missing negative witnesses at the same time rather than leaving
   a known gap unclosed for a second time:
   - `.advancing`-shaped input with `bias ≠ 1` must NOT classify as `.advancing` (must fall to `none`
     or a different constructor, per the fixed classifier order in §2 item 7).
   - `.free`-shaped input with `bias ≠ 0` must NOT classify as `.free`.
4. Generalize base and step positional covers to count free and strided output positions.
5. Add an explicit base dimension-class clause: forbid `.advancing` in every base row rather than
   relying on the caller's `contextWidth = 0`, and forbid `.strided` at dimensions listed in
   `advancingDims`. Preserve `.free` at an advancing dimension because multi-axis boundary faces use
   it; `.strided` is admitted only at non-advancing dimensions.
6. Replace `freeExtentsAgree` with a shared output-row extent predicate, or add a sibling whose
   implementation delegates strided rows to `scatterDestExtent`. Preserve a distinct, locatable
   checker error for an extent mismatch.
7. Keep pinned range checking unchanged; add an explicit strided arm whose justification points to
   positive classification plus exact shared extent equality.
8. Extend `writesCollide` with only the equal-positive-scale/different-residue disjoint rule.
9. Extract the boundary-touch predicate from `baseWriteRowsOk` and make `Compile.lean` call it,
   removing the final inlined copy without changing `baseWriteNotAtBoundary`'s payload.
10. Extend both frozen `stepWriteRowsOkNoClause1` matches and `allRowKinds`; re-pin
    **7 → 9 values**, **49 → 81 row pairs**, and **588 → 972** agreement cases.

### Fixtures

- Classifier donors: the existing `classifyWriteRow` chokepoint guards; add the eight witnesses
  listed above plus direct rejection checks for negative scale, negative bias, and two nonzero
  coefficients, plus the two closure witnesses (`.advancing` with `bias ≠ 1`; `.free` with
  `bias ≠ 0`) that close the previously-unpinned pre-existing checks.
- Base/step acceptance donors: clone `faceWrite` and `dpStepWrite`, replacing one free row with
  scale `2`, offsets `0` and `1`.
- Extent mismatch donors: for base, clone `freeExtentMismatchScan`; for step, clone
  `linearScan`/`dpStepWrite` and change only the non-advancing row plus its block-output extent.
- Forbidden-kind donors: clone Part 9's hand-assembled clause-isolation arrays.
- Base advancing-dimension donor: hand-assemble
  `[.pinned 0, .strided 0 2 0, .free 1]` with `advancingDims := #[0, 1]` and output width `2`.
  It satisfies recognition, ordered output cover, and lower-boundary touch, so only the new
  dimension-class clause can reject it. Also guard that moving the strided row to a
  non-advancing dimension is accepted.
- Collision donors: clone `faceRows`/`pointRows`; cover even/odd disjoint, same-residue collide,
  different-scale conservative collide, and free-versus-strided conservative collide.
- Exhaustive soundness: enumerate scales `1..5`, offsets `0..7`, and source extents `0..7` for both
  rows (**102,400 tuples**). Whenever the modular rule says disjoint, direct finite-image
  intersection must be empty.

### Mutation cycles

Independently remove: positive-scale guard, nonnegative-offset guard, context-half guard, strided
cover arm, base `.advancing` prohibition, base advancing-dimension `.strided` prohibition, strided
extent equality, modular disjointness, boundary predicate reuse, the `.advancing` branch's
`bias == 1` requirement, and the `.free` branch's `bias == 0` requirement. Each named fixture must
fail; restore and rerun. (The last two cycles close the two pre-existing gaps step 3 flags above —
dropping either requirement must now fail its new closure witness, where before nothing did.)

### Gate

```bash
cd leanncd
lake build Eval.Plan.ScanTest Eval.Plan.ScanCompileTest
lake build LeanNCD
```

Complete one soundness-focused review before Task 6.

---

## Task 3 — add legacy scan compute-then-place semantics

### Outcome

`Eval.evalScan` independently evaluates admitted scan scatters rather than rejecting them or
mistaking the dense source slice for the persistent destination slice.

### Files

- `LeanNCD/Eval/Scan.lean`
- `test/Eval/ScanTest.lean`

### Implementation

1. Generalize `evalStmtSliceSeeded` to accept `.scatter` while retaining `.assign` behavior.
2. For a scatter, derive the non-seeded LHS source-axis basis in first-seen UID order and call the
   seeded assignment evaluator over plain projection slots. This performs RHS contraction and
   aggregation before placement.
3. Add a scan-specific full-state shape helper:
   - iteration slots use their declared history extent;
   - every other slot calls `LHSSlot.outExtent`;
   - missing sizes fail through the existing `ShapeError` path.
4. Replace insertion-only `writeSliceAtMulti` use with a scan-statement placement routine that
   evaluates every original LHS expression against the seed plus dense source coordinate.
   Preserve source-order base overlay.
5. Keep ordinary assignment behavior identical. Do not call `Eval.evalScatter`: it would recompute
   RHS contraction at the wrong boundary and would couple the two reference paths.
6. Reject scatter-shaped scratch loudly; it is outside S-B.

### Fixtures

- Clone the first linear scan in `test/Eval/ScanTest.lean`:
  1. strided base, dense recurrence;
  2. dense base, strided recurrence;
  3. even/odd base interleave;
  4. strided base whose RHS has one contracted-only axis;
  5. a non-trailing scan dimension relative to the affine state dimension.
- Assert complete shape and data, not only success.

### Mutation cycles

- Write the dense source coordinate directly instead of evaluating the LHS: strided cases fail.
- Place before contracting: contraction case fails.
- Reinitialize state before each base contribution: interleave fails.
- Drop the bias: odd-offset cases fail.

### Gate

```bash
cd leanncd
lake build Eval.ScanTest
lake build Tests
```

Complete a reference-semantics review before Task 7.

---

## Task 4 — extend the independent scan-free oracle early

### Outcome

`PropertyOracle.independentRun` handles the admitted S-B fragment without importing any checked
geometry/compiler/worker helper and produces an independently reconstructed full history.

### Files

- `test/Eval/PropertyOracle/ScanUnroll.lean`
- `test/Eval/PropertyOracle/ScanOracle.lean`

### Implementation

1. Replace `rhsOf` with a statement-parts view that preserves `.scatter` RHS/options rather than
   rejecting them.
2. Generalize `StateGeom` from plain `freeSlots` to non-advancing placement geometry and derive
   state-slice extents with an oracle-local implementation of §2's rule. Mint collision-free
   synthetic axes for the complete non-advancing state slice, and carry their extents in `Unrolled`
   so `independentRun` can extend the leaf schedule's explicit-size map.
3. During unrolling, eliminate only scan-context slots:
   - ordinary source statements emit ordinary leaf assignments;
   - affine source statements emit a dense temporary assignment over the LHS source-axis basis,
     followed by a top-level leaf scatter with the original non-context placement expressions and
     a single read of that temporary. This separation is mandatory: directly placing the original
     RHS in `evalScatter` would treat RHS-only axes as scatter-source axes and collide instead of
     contracting.
4. Give each base contribution its own leaf name. Independently enumerate each contribution's
   destination coordinates and reject overlap; do not call `writesCollide`.
5. Before emitting any recurrence leaf, emit one ordinary assignment per live base history
   coordinate that pointwise sums its disjoint, zero-filled contribution tensors over the synthetic
   state-slice axes into the canonical `stateLeafName`. Recurrence reads resolve to this merged leaf,
   not to a contribution reserved for final reconstruction. Pointwise sum is valid here precisely
   because scan-scatter fill is fixed at zero and the oracle independently proved the contributions
   disjoint.
6. Step history coordinates still have one canonical state contribution because multiple step
   writes remain rejected.
7. Validate each contribution, merged base leaf, and step leaf shape against the oracle-local
   expected state-slice shape before
   history reconstruction. This is the independent check against a faulty global `outExtent`.
8. Keep the generated program scan-free and preserve the existing predicate-leaf behavior for
   non-scatter cases. Generated dense temporaries are private, tuple-qualified, dependency ordered,
   and absent from the reconstructed environment.

### Fixtures

- Clone the Task 3 cases for:
  1. even/odd interleave;
  2. strided recurrence;
  3. RHS contraction;
  4. non-trailing advancing dimension;
  5. two affine non-advancing dimensions.
- Assert emitted assignment-then-scatter constructor pairs, contribution-to-canonical merge
  statements, private temporary names, and exact reconstructed tensors.
- Extend `ScanOracle.lean` feature-presence guards so the S-B corpus cannot silently lose every
  `.scatter` leaf.

### Mutation cycles

- Replace oracle-local aligned extent with old `c*n+b`: shifted interleave fails shape validation.
- Collapse base contributions to one name: interleave fails.
- Remove the contribution-to-canonical merge: the first recurrence read after an interleaved base
  fails or disagrees.
- Drop affine bias during leaf emission: odd-offset fixture fails.
- Reconstruct as if the advancing dimension trailed: positional fixture fails.

### Gate

```bash
cd leanncd
lake build Eval.PropertyOracle.ScanUnroll Eval.PropertyOracle.ScanOracle
```

Complete an independence review before Task 6. Any need to import a forbidden production helper is
a stop condition, not a convenience refactor.

---

## Task 5 — lift the DSL guard and define scan-scatter capability

### Outcome

Surface affine LHS scan statements reach `lowerArith`/`finalizeScans`; the routed compiler remains
opaque over the completed scan node; unsupported scan-scatter forms fail at the correct typed tier.

### Files

- `LeanNCD/DSL/Compile.lean`
- `LeanNCD/DSL/Pipeline/Structural.lean`
- `LeanNCD/DSL/Pipeline/RouteFragments.lean` (stale guard-description comment only)
- `LeanNCD/Exec/Uid.lean` (producerless-constructor comment only)
- `LeanNCD/Eval/Plan/Compile.lean` (preflight only)
- `test/DSL/Pipeline/StructuralTest.lean`
- `test/DSL/Pipeline/RouteWeaveTest.lean`
- `test/DSL/Pipeline/RouteFragmentDiagnosticTest.lean`
- `test/Eval/Plan/CompileTest.lean`
- `test/Eval/Plan/ScanCompileTest.lean`

### Implementation

1. Remove `checkScatterNoScan` from both production compile chains and the test-local logical chain;
   delete the phase if no caller remains.
2. Retain `CompileError.scatterInScan` as a producerless compatibility constructor and update its
   comment. Do not reuse it for a narrower downstream error.
3. Add a scan-scatter slot checker that admits iteration slots plus S-A's single-axis affine forms.
   Keep `.affine (.const _)` and normalized multi-axis expressions rejected.
4. Make `checkScanBlockStmt` accept `.scatter` only after checking slots, aggregation,
   identity nonlinearity, factors, and options in the same sub-construct order as top-level
   scatter. The scan-specific option rule is exactly `fill == 0` and
   `reduce == .rejectCollisions`; both other cases use `scatterOptsNotAdmitted`.
5. Extend the capability post-pass into scan base/recur lists so predicate destinations and
   hand-built unlowered scatter-shaped `.assign`s remain rejected there too.
6. Re-pin `RouteFragmentDiagnosticTest.case11` from `scatterInScan` to `missingBaseCase`; it must not
   be rewritten into a success case because it genuinely has no base statement.
7. Add a complete base-plus-recurrence routed fixture proving `TLProgram.compile` succeeds and emits
   one opaque scan fragment. No `RouteFragments.lean` production change is expected; change it only
   if that fixture proves the measured probe wrong.

### Fixtures and mutations

- Donors: the two existing `StructuralTest` `checkScatterNoScan` fixtures, route diagnostic case 11,
  S-A's `checkScatterLHSSlot` negatives, and `ScanCompileTest`'s four deferred S-B rejections.
- Pin base and recurrence reachability separately.
- Pin predicate destination, nonlinear scatter, non-default reduce, constant affine, multi-axis
  affine, nonzero fill, and unlowered affine assignment rejections inside a scan. Put the nonzero
  fill once in base and once in recurrence so both traversals are pinned.
- Add one dual-defect fixture proving form rejection precedes missing input/shape validation.
- Mutate each removed chain site back in independently; the corresponding base/recurrence
  reachability fixture must fail.

### Gate

```bash
cd leanncd
lake build DSL.Pipeline.StructuralTest DSL.Pipeline.RouteWeaveTest
lake build DSL.Pipeline.RouteFragmentDiagnosticTest Eval.Plan.CompileTest Eval.Plan.ScanCompileTest
lake build LeanNCD
```

---

## Task 6 — lower scan scatters into dense block assignments plus write maps

### Outcome

`prepareEvalPlan` compiles every admitted S-B source program into a checked `PlanStep.scan` whose
block steps are dense assignments and whose `StateWriteMap`s carry the affine placement.

### Files

- `LeanNCD/Eval/Plan/Error.lean`
- `LeanNCD/Eval/Plan/Compile.lean`
- `test/Eval/Plan/ScanCompileTest.lean`

### Implementation

1. Keep `assignPartsOrFail` unchanged for ordinary top-level assignments. Add a scan-block
   destructurer accepting `.assign` and admitted `.scatter` so the plain compiler cannot
   accidentally treat a scatter as an assignment.
2. Track whether each base/recur triple originated as scatter; use it to reject scatter-shaped
   scratch with a new located `ScanCompileError`.
3. Derive each statement's dense output UID basis from LHS index expressions, excluding context
   **slots** (`.iterAt`/`.iterNext`) rather than excluding all UIDs declared as context. This
   preserves an existing base `.free` context-axis face. Reject:
   - a normalized duplicate UID across placement dimensions (diagonal scan write);
   - an affine expression naming a context UID; and
   - any form that cannot classify into the §2 row table.
4. Rework state geometry to find advancing dimensions from context-role slots and compute all other
   dimension extents through `LHSSlot.outExtent`. Preserve existing rank, advancing-position, and
   cross-placement extent diagnostics.
5. Feed the dense output basis to `residualizeAssignment`; do not include RHS-only contraction axes.
6. Factor one placement-row builder shared by base and step emission. It lowers affine rows with
   `idxToRow` and pads step rows with the context prefix.
7. Emit only `.assign` block steps. Do not add or simulate `BlockStep.scatter`.
8. Reuse Task 2's boundary, extent, range, and collision predicates for source-facing validation.
   Keep original base/recur statement indices; do not report indices in a filtered scatter-only list.
9. Let `checkScanPlan` re-check the fully assembled raw plan as the internal safety net.

Add exactly these source-located constructors rather than stringly or generic fallbacks:

- `scanWriteRowNotAdmitted (scan name : String) (isBase : Bool) (stmtIndex dim : Nat)
  (coeffs : Array Int) (bias : Int)` — owns zero/negative coefficient, negative offset, and any
  otherwise unclassifiable emitted row;
- `scatterScratchNotAdmitted (scan name : String) (stmtIndex : Nat)`; and
- `contextAxisAsAffineOutput (scan name : String) (isBase : Bool) (stmtIndex : Nat) (uid : UID)`.

`inconsistentStateExtent` continues to own disagreement between individually valid placements;
`multiAxisScatterLhs` continues to own an affine expression with more than one normalized UID.

### Acceptance fixtures

Each must assert `stateSigs`, dense `AssignPlan.outputShape`, block-step kind, `StateWriteMap`
coefficients/bias, and final value:

1. Base stride `2*j`, dense recurrence. Donor: `selfRecurSched`.
2. Dense base, recurrence stride `2*j+1`. Donor: the same fixture with phases exchanged.
3. Canonical even/odd two-base interleave with dense recurrence. Donor: `multiBaseSched`.
4. Strided base with an RHS-only contraction axis. Donor: the existing contraction scan.
5. Scan dimension first. Donor: `selfRecurSched`, adding one non-advancing dimension.
6. Scan dimension last. Donor: `axisPosSched`.
7. Two distinct affine non-advancing dimensions. Donor: `axisPosSched`, adding a second
   non-advancing axis and placement row.
8. More than one scan node, one containing S-B. Donor: `twoScanSched`.

### Rejection fixtures

Clone the nearest existing S-A or scan-geometry donor and change one field:

1. zero coefficient;
2. negative coefficient (hand-built schedule);
3. negative bias (hand-built schedule);
4. one affine slot naming two UIDs;
5. diagonal/repeated UID across LHS dimensions;
6. affine context-axis output;
7. scatter-shaped scratch;
8. inconsistent aligned state extent;
9. colliding same-residue base writes;
10. different-scale base writes, conservatively rejected.

Retain the existing multiple-step-write rejection unchanged.

### Locator and order fixtures

1. Put an unrelated valid base statement between two colliding writes; the error must name the
   original base indices, not indices in a filtered per-state list.
2. Make a recurrence scatter both malformed in geometry and non-causal in its state read; geometry
   must win.
3. Make a scan scatter both capability-invalid and dependent on a missing input; capability must
   win.

### Mutation cycles

Break independently: source-axis basis extraction, context-prefix padding, affine bias, state
extent derivation, base/step phase selection, original statement locator, scratch rejection, and
the dense-compute-before-placement boundary. Each named fixture must fail.

### Gate

```bash
cd leanncd
lake build Eval.Plan.ScanCompileTest Eval.Plan.ScanTest
lake build Eval.Plan.AdapterTest
lake build LeanNCD
```

Complete one compiler review and one independent write-geometry review before Task 7.

---

## Task 7 — three-way differential, documentation, and closure

### Outcome

Every admitted S-B shape agrees across checked plan, legacy scan evaluation, and independent
scan-free unrolling; active capability documentation reflects the new boundary; the branch is
fully reviewed and green.

### Files

- `test/Eval/Plan/DifferentialTest.lean`
- `test/Eval/PropertyOracle/ScanOracle.lean`
- `LeanNCD/DSL/AGENTS.md`
- `LeanNCD/Eval/AGENTS.md`
- `AGENTS.md`
- `docs/test_portfolio.md`
- `../papers/scatter_affine_lhs_writes.md`
- `../papers/backend_missing_functionality.md`
- `../papers/wave_f_capability_manifest.md`

### Curated S-B corpus

Add a separate `scanScatterPrograms` list; do not alter the generated 17-case scan corpus or the
3,832-case scan-free corpus. Pin its length at **7**:

1. strided base;
2. strided recurrence;
3. even/odd base interleave;
4. dense contraction before placement;
5. non-trailing advancing dimension;
6. two affine non-advancing dimensions;
7. two scans with one S-B node.

For every entry, `scanParityCheck` (or a generalized sibling) must compare:

- exact materialized key set;
- exact state shapes and values;
- warning list order and payload;
- unchanged external inputs;
- scratch/private-name absence; and
- all three execution legs.

### Mutation cycles

1. Drop the odd base contribution: interleave fails in checked-versus-both-reference legs.
2. Restore old shifted extent in one leg only: shape parity fails.
3. Compare only values while ignoring shape/key inventory: the corpus's explicit shape/key guard
   must still fail, proving the differential is not weakened to a partial comparison.

Record mutate/fail/restore/pass observations; predictions are not evidence.

### Documentation sweep

1. Replace the overview's old §3.2 extent statement with the chosen aligned contract and record S-B
   completion without rewriting S-A history.
2. Update active capability inventories from “S-B open/rejected” to the exact admitted subset and
   preserve the non-goals in §1.2.
3. Update `DSL/AGENTS.md`'s production pipeline: no `checkScatterNoScan` phase.
4. Update `Eval/AGENTS.md`'s extent and nine-site tripwire text for `.strided`, the shared
   `scatterDestExtent` rule, and the three execution legs.
5. Add S-B cases to `test_portfolio.md`.
6. Re-derive every inherited “still rejected” bullet before retaining it.
7. Value-grep the whole repository for the boundary values that moved:
   - `shape=[7]`;
   - `some 7`;
   - `extent 7`;
   - `scale * n + offset` / `scale * size + offset`;
   - `scatterPrograms.length == 8`;
   - `checkScatterNoScan`;
   - `scatterInScan`;
   - “scatter inside scans rejected” variants.
8. Archived plans and historical audit records stay historical. Add a supersession note when an
   active-looking old rule would otherwise mislead; do not rewrite measured history.

### Final gate

```bash
cd leanncd
lake build Eval.Plan.ScatterCheckTest Eval.Plan.ScatterDenseTest Eval.Plan.ScatterCompileTest
lake build Eval.ScanTest Eval.Plan.ScanTest Eval.Plan.ScanCompileTest Eval.Plan.AdapterTest
lake build Eval.PropertyOracle.ScanUnroll Eval.PropertyOracle.ScanOracle Eval.Plan.DifferentialTest
lake build Tests
lake build LeanNCD
lake build JaxExperiment
```

Then run both final whole-branch reviews:

1. **Soundness lens:** row classification, case table, bounds, extent equality, collisions,
   write-map rank/width assumptions, worker safety, and locator/check order.
2. **Semantic-independence lens:** source reachability, compute-then-place semantics, legacy versus
   oracle independence, differential teeth, routed opacity, and stale capability prose.

---

## 5. Stop conditions

Stop and report rather than improvise if:

- the aligned global extent makes any fallback in §3.1 change;
- accepting a complete scan scatter requires a new routed/categorical representation rather than
  the measured opaque scan copy;
- scan scatter cannot be represented as dense `AssignPlan` plus `StateWriteMap` without adding
  `BlockStep.scatter`;
- safe execution requires allowing more than one recurrence write per state;
- the independent oracle needs any forbidden production helper;
- equal-scale modular disjointness produces a false “disjoint” result in the exhaustive check;
- a new source form can reach `commitWrite` without positive stride, nonnegative offset, exact
  extent equality, and ordered output-basis cover;
- a locator/order fixture cannot distinguish original statement indices from filtered indices; or
- either final reviewer finds a load-bearing issue that cannot be repaired within this scope.

---

## 6. Definition of done

- `LHSSlot.outExtent` implements §2's exact normalized, stride-aligned rule and every fallback is
  pinned.
- S-A shifted-stride fixtures and `scatterPrograms` are intentionally rebaselined; all other S-A
  behavior remains green.
- `WriteRowKind.strided` is handled explicitly at all nine tripwire sites.
- The classifier witness, 972-case clause-1 oracle, and 102,400-case collision soundness check pass.
- The `.advancing` branch's `bias == 1` requirement and the `.free` branch's `bias == 0`
  requirement are each pinned by a dedicated closure witness (pre-existing gaps, closed per §0.2).
- Base and step strided writes both compile and execute.
- Canonical even/odd base interleaving produces one six-cell state slice with no trailing padding
  cell.
- Dense computation, including contraction, precedes affine state placement.
- No `BlockStep.scatter` exists and exactly one step write per state remains required.
- Unsupported diagonal, multi-axis-expression, context-affine, scratch-scatter, predicate,
  nonlinear, reduction-policy, sign, and overlap forms fail loudly with typed located errors.
- Checked, legacy, and independent-oracle results agree for all seven curated S-B cases.
- Generated corpus counts remain **17** and **3,832**; S-A's curated corpus is **9** and S-B's is
  **7**.
- Every planned mutation has an observed failure and restored pass.
- Active docs describe the admitted subset and deliberate exclusions; stale-value grep is
  adjudicated.
- Full `lake build` and `lake build JaxExperiment` pass with no `sorry`.
- Both whole-branch reviews are clean or every finding is explicitly adjudicated.

---

## 7. Execution record

*(Append during implementation: task commits, exact targeted/full build job counts, all mutation
fail/pass observations, corpus counts, stale-value grep adjudication, and both final review
outcomes. Cite identifiers, never line numbers.)*

### Task 1 — global aligned extent and S-A rebaseline

- **Commit identifier:** `feat(leanncd): align affine scatter extents` (the Task 1 commit containing
  this record).
- **Fixtures:** all fourteen §3.1 `LHSSlot.outExtent` observations are direct guards in
  `ScatterCheckTest`; the shifted-stride check, dense value, and source-compile parity fixtures now
  expect shape `[6]` / data `[0,1,0,2,0,3]`; `DifferentialTest.scatterPrograms` adds `SA9` and pins
  length `9`.
- **M1 — restore legacy `c*n+b`:** mutation exit `1`. `ScatterCheckTest`'s shifted/aligned guards,
  `ScatterDenseTest` fixture 2, and `ScatterCompileTest` S2 failed. A focused
  `DifferentialTest` rerun also reported `SCATTER PARITY CORPUS (S-A Task 6) FAILED`. Both
  seven-file hash restoration checks passed; restored builds passed at 8,527 and 8,524 jobs.
- **M2 — skip UID coefficient normalization:** replacing `idxDensify cf us` with raw coefficients
  exited `1`; the duplicate and cancelling-term guards failed. Hash restoration passed; restored
  `ScatterCheckTest` passed at 8,492 jobs.
- **M3 — skip raw-term size resolution:** bypassing the all-raw-UID size check exited `1`; the
  zero-coefficient unsized-axis guard failed. Hash restoration passed; restored
  `ScatterCheckTest` passed at 8,492 jobs.
- **M4 — apply alignment to zero-size inputs:** removing `n > 0` exited `1`; the zero-source-extent
  fallback guard failed. Hash restoration passed; restored `ScatterCheckTest` passed at 8,492 jobs.
- **Final Task 1 gates** (all invoked with `/Users/williammacready/.elan/bin/lake`):
  - `build Eval.Plan.ScatterCheckTest Eval.Plan.ScatterDenseTest Eval.Plan.ScatterCompileTest`:
    pass, 8,520 jobs.
  - `build Eval.Plan.DifferentialTest`: pass, 8,524 jobs; generated corpus
    `total=3832 accepted=3832 rejected=0`, scan corpus `total=17 accepted=17`, curated scatter
    corpus `9`.
  - `build LeanNCD`: pass, 8,544 jobs (only replayed pre-existing warnings/sorries outside Task 1).
  - `build JaxExperiment`: pass, 8,514 jobs.
- **Stop conditions:** none. Task 2 was not started.

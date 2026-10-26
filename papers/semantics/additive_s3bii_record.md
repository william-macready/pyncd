# S3b-ii record: tropical multi-writer collection (top level), shared writer-vote rule, D1 coerce, D2 vote

Executed 2026-10-24/25 on `worktree-additive-s3bii-tropical-collect` from main `04e2aef0`. Design `additive_s3bii_design.md`, plan `additive_s3bii_plan.md`, audit `additive_s3bii_audit.md`, final reviews `additive_s3bii_review_final_semantics.md` and `additive_s3bii_review_final_rejections.md`. Merge hash: see the decision note (added after the merge).

## 1. What landed (one commit per task; every task left the tree fully green)

| Task | Commit | Content | Full `Tests` |
|---|---|---|---|
| T1 | c1e8f427 | `writerVotes`/`writerSort?` in `DSL/Ast.lean`; `scanStateSorts`/`scanStateAlgebra` and `scheduleAlgebras` route through it; an all-neutral scan state's annotation votes (D2) | 8825 green |
| T2 | ccde7604 | top-level all-max / all-min multi-writer groups collect with max / min (`Collect.lean`: group sort from `writerSort?`, collector agg, abstaining neutral writers rewritten with `Stmt.withAgg`); `scheduleAlgebras` enters the agreed tropical sort so `checkSortCasts` covers the group's writers and readers | 8825 green |
| T3a/T3b | 3a29df70, 65fa1181 | D1: `real -> bool` reads coerce (stored != 0; NaN true): reference `boolReadCast` destination-aware; plan `ReadPlan.realToBool`, `residualizeAssignment` `destIsBool`, `gatherFactorWith`, `castNotAdmitted` admission. Bare reads only; never the out-of-range pad or a unary read | 8825 green (T3a alone left `DifferentialTest` T4.3/7 red by design) |
| T4 | 08f022ac | Bellman programs P1/P1'/P2/P3/P5 as value fixtures on reference, plan f64, plan f32; refusal neighbours; reader fixtures; oracle rows | 8825 green |
| T5 | eba3dda1 | docs sweep | n/a |
| review follow-up | e9aba9dd, 0fb5f019, b6561559 (comment), 7b533b0b | pins for gaps the reviews found; comment/docstring/doc corrections | final build below |

Final gate: full `Tests` on the final tip and `JaxExperiment`: see section 5.

## 2. Old -> new expectations (each with its reason)

| Fixture | Old | New | Reason |
|---|---|---|---|
| `parkedAllNeutralScanState` (renamed `allNeutralScanState`, `DualityTest`) | `[[4,4],[0,0]]` | `[[4,4],[-inf,-inf]]` | D2: an all-neutral state's non-sum annotation votes (reference, plan f64, f32 bits) |
| `ScanCompileTest` "S3bF/neutral scratch max" / "min" | tail 0 | tail -inf / +inf | D2 (scratch is its own destination; sum unchanged) |
| `CollectTest` C6, `c6min` | `multiWriterAlgebra` | admitted (collector agg max / min) | S3b-ii |
| `CollectEvalTest` J4, `j4m` | compile refusal | values `[6,8]` / `[1,3]` | S3b-ii; observed equal to the plan's hand values |
| `CompileTest` (d) multi-writer tropical set | `multiWriterAlgebra "W"` | `sortCastUnsupported "W" "N"` | the group now has a sort-map entry |
| `DifferentialTest` T4.3/7 boolean scalar non-binary (corpus entry and direct check) | 0.75 | 1.0 | D1: F=[0.25,0.75] real into a predicate coerces to {1,1} |
| `CollectTest` C6b, C6c, `c6bm`, `c6cm` | sum copy + max/min writer refused | rewritten with a NON-neutral contracted sum writer, still refused; the old neutral-copy shapes are now accept fixtures `c6bN`, `c6cN`, `c6bmN`, `c6cmN`, `c6dN` | PLAN CORRECTION: the plan's KEEP list was wrong; under the abstain rule (user decision D5) a sum copy beside a max writer is the accepted Bellman form |

No test was weakened; the reviewers confirmed every changed value has its stated reason.

## 3. Decisions and the author's calls

User decisions 2026-10-24 (design section 2): D1 coerce, D2 vote, D3 F2 stays option A, D4 top level only, D5 abstain. Author's call: ONE shared vote rule for scan states and top-level groups (neutral writers abstain beside non-neutral ones whatever their annotation; all-neutral groups vote by non-sum annotation; max vs min conflict is refused). Consequences found by the reviews and pinned: an abstaining copy's rewrite changes how it reads a PREDICATE (false/true read as 0_K/1_K, not 0/1: `cpMax` `[0,-4]`), not only its pad; a neutral `maxreduce`/`minreduce` copy beside a non-neutral SUM writer is accepted and runs as sum (annotation dropped; it used to be refused: `vrSumMax`); a relu or Iverson-only copy beside a max writer is refused (`vrRelu`, `vrIv`); D2 newly refuses scan programs where a bool or min-plus statement reads an all-neutral max scratch, or such a scratch reads a min-plus tensor (`sortCastUnsupported`); `route` accepts tropical multi-writer programs (and a bool reader of the collected tensor) without any cast check (pinned `routedOps`).

## 4. Findings and parked

Final reviews: 0 Critical, 0 Major; 5 + 8 Minor, all fixed (fixtures or text) except as parked below. Parked (unchanged owners): in-scan multi-writer collection (separate scan-body desugar in both backends; ~one slice, only on request); B5 multi-writer scatter; F3 scan-local overwrite (not needed: the collector uses no scatter); F2 cast bypass (option A kept; revisit B/C when writer agreement or in-scan collection needs it); the unary-fn OOB `f(0)` in a tropical reduction (closed by commit c0867dd9); neutral `Out[i+j]` collision shape (closed by commit 669ce30e); JAX/Python tropical; oracle per-tensor sorts (CLOSED 2026-10-26 on local main, `papers/semantics/oracle_sorts_record.md`: `compareMixedSource` gives mixed and copy-form groups a value or predicted-refusal verdict; the typed `compareSortedSource` still refuses them as `mixedSorts`) and cast/padding oracle coverage (still open for bool, Iverson, pad, unary, nonlinearity, affine-read and scan values); the plan scatter caller of `residualizeAssignment` can never carry a predicate destination, so its D1 flag is unobservable (no fixture, no mutation possible); D1 collapses `-0.0` and NaN by the `!= 0` convention (pinned, not endorsed); the tropical collector returns +0.0 for an all `-0.0` input.

## 5. Verification and cost

Hand mutations per item are in each commit body (T1: 2, T2: 3, T3a: 2 reference callers (top-level, scan base and scan step share one call site; scatter is the other), T3b: per plan caller plus gather and checker, T4: 2, follow-up: sort-map leak). No manifest entries added (Full-lite plan). Final `Tests` and `JaxExperiment` results are appended below by the controller.
Cost (Rule 6): S3b-ii dispatches, cumulative input tokens by `token-report.py`: audit 5.9M, T1 5.1M, T2 5.7M, T3a 6.4M, T3b 6.4M, T4 7.8M, T5 3.4M, reviews 11.7M, fix dispatches 9.0M: about 61M plus the controller's share (the session total including the S3b follow-up batch and this slice is 141.7M; the controller alone 40.8M for the whole session, peak 344k context). Authoring (audit, design, plan) cost about 6M in dispatches against S3b's 159M: no prototype patch series and no hand mutation cycles in the audit. Rule 6 per-dispatch notes: T1 53, T2 52, T3a 61, T3b 57 (self-reported 52), T4 60, fixtures-B 59, T5 34 turns; no dispatch exceeded ~250k context (peak 214k).

Final gate (controller): full `Tests` on the final tip: Build completed successfully (8825 jobs), 0 errors, no `sorryAx`, every `depends on axioms` line a subset of propext / Classical.choice / Quot.sound. `JaxExperiment`: Build completed successfully (8515 jobs) (also after T4). No red target at any task gate.

## 6. Review of the minors fixes (2026-10-25)

Review of c0867dd9 (tropical OOB unary read is `0_K`) and 669ce30e (two-axis LHS slot is never sort-neutral): `additive_minors_review.md`, 0 Critical, 0 Major, 7 Minor, 3 Nit. Fixed in the follow-up commit: m1 (stale `ReadPlan` comment), m2 (live docs and parked lists), m3 (now pinned: an out-of-range `log`/`recip` under max/min used to be a domain error and is now `0_K`; BoolCastTest (k) k10-k13, with the real-statement contrast k14/k15). Parked per Rule 14 (nothing below changes behaviour or is needed for the goal):

| Item | What | Cost | Status |
|---|---|---|---|
| m4 | "Tropical" is decided four ways (reference `zero != 0.0`, plan `factorOp == .add`, `Check.lean` cast admission, `Scan.lean` `algebraStateInit`). No production program has the flags differ; the reference sentinel is fragile for a custom semiring passed to the public `evalAssignWith`/`evalAssignSeeded` (e.g. `(x, max, -inf, 1)`) | ~1 Direct dispatch (thread one explicit flag, or one `SortAlgebra.isTropical`) | parked |
| m5 | An unwritten cell INSIDE the extent still has the unary applied to its `0_K` (max-plus `sin` gives NaN, `recip` lets the empty cell win, min-plus `recip(+inf) = 0` wins): "absent" means two things under a unary | ~1 design note + 1 Direct fixture; a fix needs a presence mask | parked |
| m6 | OOB unary times a stored `+inf` is NaN in max-plus (`-inf + inf`); same class as the bare OOB read, +inf is outside the carrier | doc line only, ~0 dispatches | parked |
| m7 | Bool statements keep `f(0)` wins (`exp(0)` is true and wins the exists; a unary bool read is not coerced); by requirement | doc line only | parked |
| n1 | Min-plus fixtures cannot tell "`0_K` unapplied" from "`f` applied to `0_K`" under `exp`; a min-plus `recip` twin would | ~1 Direct fixture | parked |
| n2 | `isSortNeutral` counts raw slot UIDs, the plan's `multiAxisScatterLhs` normalized coefficients (`.affine 0 [(1,i),(-1,i)]`, `.affine 0 [(1,i),(0,j)]` differ); not surface-reachable, no value affected | ~1 Direct dispatch | parked |
| n3 | `neutralShapes` has no duplicate-UID row (`2*j`); dropping `eraseDups` survives | ~1 Direct fixture row | parked |

Conventions deliberately left (each already pinned): NaN reads true under `!= 0`; `-0.0` becomes `+0.0` through the tropical collector; the D1 scatter-caller flag is unobservable; the route is semantics-free.

# S3b P1 findings (T1: the semiring flip for tropical ⊗ and NaN)

Branch `proto-s3b-p1` (worktree left checked out on it). Base 5415b890.
Commits: `a8fed5ff` T1-01 production, `c9c8f537` T1-02 tests.
Patches: `T1-01-production.patch` (5415b890..a8fed5ff), `T1-02-tests.patch` (a8fed5ff..c9c8f537), same directory.
`git diff --stat`: T1-01 = 6 files, +93/-48 (Contract, Error, Plan/Check, Plan/Compile, Plan/Dense, Plan/Types).
T1-02 = 6 files, +284/-56 (ContractTest, KernelDense32Test, KernelDenseTest, GnnScatterTest, RecurrenceTest, TropicalTest).

## (f) Audit / design corrections (read first)

1. KernelDenseTest "all-negative B" row (audit §8a: becomes A+(-1)) NO LONGER separates the -inf seed. With A > 0 and B = [-1,-2,-3] the
   max-plus sums are positive, so a 0 seed would still be right. The seed-load-bearing fixture needs NEGATIVE A as well:
   `storeNegA_NegB` under max-plus gives [-11,-101,-1001,-10001] (0 seed would give 0s). Added in both f64 and f32. A plan author who
   only "migrates the value" silently loses the identity-mutation fixture. The min-plus twin of the load-bearing fixture is the existing
   A,B>0 min-plus row (sums all positive).
2. TR5 was not "a gap needing new syntax": after the flip `minreduce(D[i,j] · D[j,k])` IS min-plus, same surface. It became a plain value
   test (3-node shortest path). The header comment of TropicalTest (still said "max-times") was rewritten.
3. Single-factor tropical statements are NOT bitwise unchanged: product fold is now `0.0 + v` (was `1.0 * v`), which normalises `-0.0`
   to `+0.0`. Values compare equal, bit patterns differ only for -0.0 inputs. No existing fixture exercises it; flag if a later bit-exact f32
   fixture feeds -0.0 through a tropical statement.
4. Audit §8f.4 worry (ScanUnroll hard-codes real zeros, ScanGen template 5) did NOT materialise in T1: `PropertyOracleScanTest`,
   `DifferentialTest` (sweep total=3832 accepted=3832, scan corpus 17/17) all pass unchanged. Template 5 needs no edit in T1.
5. Among the Source* sorted-differential tests only `SourceSortedDifferentialTest` goes red. `SourceSortedAuditTest`, `SourceOracleCarrierTest`,
   `SourceRawCorrespondenceTest`, all other Source* tests pass untouched. (Do not budget T7 for more files from T1's flip alone.)
6. Lake 5.0.0 (Lean 4.35) has no `--keep-going`. Default behaviour already builds every independent target and prints the complete red list
   ("Some required targets logged failures:"), so the one `Tests` run gives the full list.
7. `KernelDense32Test` imports `KernelDenseTest`. A red `KernelDenseTest` blocks the f32 module from building, so mutation checks must
   split f64 and f32 batches (done below).
8. Audit §8c "become rejections" / §8d were not touched in T1 (as designed); AGG1/AGG2 etc. did not go red.

## (a) Observed old -> new

| File | Label | Old | New | Why |
|---|---|---|---|---|
| test/Eval/Portfolio/TropicalTest.lean | TR3 best-path (maxreduce P·P) | [0.72,0,0,0.72] | [1.7,0.9,0.8,1.7] | ⊗ = + |
| same | TR7 (minreduce A·B) | [4,2] | [5,3] | ⊗ = + |
| same | TR5 min-plus shortest path | documented gap | [0,1,3, 5,0,2, 3,4,0] (new value test) | expressible |
| test/Eval/Portfolio/RecurrenceTest.lean | RC5 | [2,6,18] | [2,5,8] | M_{l+1} = M_l + 3 |
| same | RC7 | [2,4,8] | [2,4,6] | M_{l+1} = M_l + 2 |
| same | RC10 | [2,0,5,6] | [2,0,5,5] | G[1,1] = max(2+1,2+3); G[0,1] unwritten cell still observed 0 (spec 0_K = -inf: T6) |
| test/Eval/Plan/KernelDenseTest.lean | maxContractPlan (A·B, B=[1,2,3]) | [30,300,3000,30000] | [13,103,1003,10003] | A + 3 |
| same | minContractPlan | [10,100,1000,10000] | [11,101,1001,10001] | A + 1 |
| same | maxContractPlan, B=[-1,-2,-3] | [-10,-100,-1000,-10000] | [9,99,999,9999] | A - 1 |
| same | oobMaxPlan | [0,0] | [0,0] (unchanged, pad untouched) | verified |
| test/Eval/Plan/KernelDense32Test.lean | fixtures 7, 8 (f32 bits) | 3240099840.. / 1092616192.. | 1095761920,1120796672,1148895232,1176259584 (13..) ; 1093664768,1120534528,1148862464,1176257536 (11..) | A+3 / A+1 |
| same | fixture 9 (f32 oob) | [0,0] | [0,0] unchanged | verified |
| test/Eval/Portfolio/GnnScatterTest.lean | GN4 | [3,4,3,4] | observed [4,5,4,5] (RED, left unchanged) | bool cast is T5 |
| MaxReduceTest, Adapter32Test, DifferentialTest single-factor rows, ScanGen template 5 | | | unchanged, green | verified |

## (b) Red-target classification (full `Tests`)

| Target | First error | Class |
|---|---|---|
| Eval.Portfolio.GnnScatterTest | `GN4 max-aggregation: Expected to be equal: 'false' and 'true'` (observed [4,5,4,5]) | (ii) deferred to T5 (bool->max-plus cast). Test comment added; expectation left as is (it is the spec value once T5 lands) |
| Semantics.SourceSortedDifferentialTest | `:104 Docstring on #guard_msgs does not match: knownContractDifference (tropicalMultiFactor ...) vs fourLegParity` (11 error sites: 104,106,191,193,196,242,262,264,266,269,272...) | (ii) deferred to T7 (apparatus deletion). Cause: production now agrees with the oracle on multi-factor tropical programs |
UNEXPECTED: none.

## (c) Job count
Full `Tests`: 8823 jobs (both runs, before and after mutation restore). Exactly 2 red targets above; LeanNCD library alone is 8614 jobs.

## (d) Where the NaN helpers live
`maxNaN`, `minNaN`, `maxNaN32`, `minNaN32` in `LeanNCD/Eval/Error.lean` (namespace LeanNCD.Eval), right after `UnaryOp.applyChecked32`.
Reason: that file is already the shared scalar oracle (`UnaryOp.applyChecked`/`applyChecked32`), `Contract.lean` imports it directly and
`Plan/Dense.lean` reaches it through `Plan.Error`, so one definition serves both layers with no new import. `Eval/Tensor.lean` was also importable by both
layers but was rejected because its header declares it pure runtime data, with no scalar semantics. Both layers use the same def;
Combine.bool, Combine.max/min, floatOps and float32Ops all call these.
Production shape: `Combine.tropical op zero` (Contract), `tropicalAlgebra`/`tropicalAlgebraF32` private helpers (Check). `admittedAlgebraMax/Min/F32Max/F32Min`
keep their names (ExecutableTest pins them by name; it stays green).

## (e) Fixtures, donors, mutations (all reverted afterwards; production verified clean by the final full build)

| Fixture | Donor | Mutation witnessed |
|---|---|---|
| ContractTest `#guard` block: Combine.max/min mul/unit pins, real accept-neighbour, duality of mul/combine/unit0 | TropicalTest TR3/TR7 semantics | Combine.tropical mul `+` -> `*`: ContractTest 213/214/222 fail |
| TropicalTest TR3d, TR7d, TR5, TR5d (twins), TR9/TR9d (single-factor accept-neighbour) | TR3, TR7 | same mutation: TR3,TR3d,TR5,TR5d,TR6,TR7,TR7d,TR9,TR9d and RC5,RC7,RC10 all red (single factor too: unit1 is 0, so `0*v = 0`) |
| KernelDenseTest rows 63,68,77 (migrated) + twins 86,92 + load-bearing 99; constants pins 131-136 | maxContractPlan/minContractPlan/storeNegB | tropicalAlgebra factorOp `.add`->`.mul`: 63,68,77,86,92,99 and pins 133,136 red |
| KernelDense32Test fixtures 7,7b,7c,8,8b,8c (lines 250-275) + pins 280-285 | KernelDense32Test fixtures 7,8 | tropicalAlgebraF32 factorOp `.add`->`.mul`: 250-275 and pins 282,285 red; factorId `0x0`->`0x3f800000`: 250-275, pins 280,283, NaN control rows 312/313, oob fixture 335 red |
| NaN plan rows (f64: KernelDenseTest nanPlan rows 171,172,175; f32: KernelDense32Test 312,313,314); rows `[NaN,1]`,`[1,NaN]`,`[2,1]` for max-plus, min-plus, bool | oobMaxPlan geometry | maxNaN -> Max.max: ContractTest 231,234,236 and KernelDenseTest 171,175 red; floatOps min arm -> Min.min: 172 red; minNaN32 -> Min.min: ContractTest 239 and KernelDense32Test 313 red; float32Ops max arm -> Max.max: 312,314 red |
| ContractTest NaN `#guard`s: Combine.max/min/bool both argument orders, helpers f64 and f32, non-NaN accept-neighbour | Combine fields | covered by the maxNaN / minNaN32 mutations above |
Notes: a NaN at position 0 or 1 of a 2-step fold covers both argument orders at plan level (`Max.max` drops a NaN second operand, `Min.min` drops a NaN first operand), so each row catches a different unfixed operator. Row 240 (`minNaN32` second operand) passes under Min.min, as expected; 239 carries that mutation.

## (g) Turns / context
About 75 tool calls (over the ~60 budget: the three mutation batches, a full-Tests rerun and two mistaken reads of build logs cost ~12). Peak context about 180k; two
accidental Reads of a 600-line build log cost ~35k of it. Lesson: never Read a build output file; use `rg -n "error|✖"`.

## (h) Facts for the T2 author
- Reference: `gather` (Eval/Gather.lean:71) has ONE caller in Eval/Contract.lean (`evalAssignSeeded`, line ~133); Iverson arm at Gather.lean ~72 returns hard `1.0`/`0.0`; `gatherRead` (Gather.lean:43) does the OOB `.ok 0.0`. Re-grep for Scatter/Scan callers of `gather` before T2 (my grep was truncated).
- Plan: `gatherFactorWith` (Plan/Dense.lean:129) has ONE caller (`denseValueAtWith`, line 234); `ops.zero` used at three places (133, 137, 138); Iverson arm at line 239 uses `ops.one`/`ops.zero`; scatter fill uses `reduceId` at line 382. Factor fold seed/`reduceId` are already decoded at lines 222-223.
- `ScalarKernelOps.zero`/`.one` remain as the carrier's real 0/1 (used by decodeConst for `.bool`); T2 should add a tropical pad from the decoded `reduceId`, not repurpose `zero`.
- After T1 the reference and plan agree on multi-factor tropical programs, which is why only the sorted differential goes red; T7 deletions can be sequenced any time after T1.
- RC10's G[0,1] unwritten cell (observed 0) is the T6 value to flip to -inf; `approxEq` does not compare infinities (audit §8f.3) so T6 needs the `x == y || ...` fix first.
- Dense.lean comment at ~126-128 ("padded 0 beats an all-negative column") and Check.lean `admittedAlgebras` doc ("a later S3b task changes the tropical pad to 0_K") are the two sentences T2 must update.
- Scratch probes (gitignored) are in `leanncd/spikes/s3b_t1_probe_*.lean`; they are self-contained and can be re-run with `lean-file.sh`.

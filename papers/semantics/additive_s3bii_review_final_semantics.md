# S3b-ii final review: semantic fidelity lens

Reviewer: Opus 5.5, read-only, 2026-10-25. Range `04e2aef0..b6561559`. Nothing built or run (a full build was running in the tree);
every claim below is code reading plus hand re-derivation from the S3b/S3b-ii semantics. Findings are appended as found.

## Findings

### F1 (Minor) `tcopyMin` / `j4m` comments state wrong "sum would give" values
Identifiers: `CollectPlanTest` doc comment of `tcopyMax`/`tcopyMin` ("resp. `[6, 13]`"), `CollectEvalTest` J4m comment ("the sum would be [4, 8]").
Scenario: `tcopyMin`, B = [[5,2],[7,4]], A = [1,9]: min_j B = [2,4]; a sum collector gives [2+1, 4+9] = [3, 13], not [6, 13].
`j4m`, A = [[1,2],[3,4]], B = [[5,6],[7,8]]: min_j A = [1,3], min_j B = [5,7]; a sum collector gives [6, 10], not [4, 8].
Evidence: the asserted values ([1,4] and [1,3]) are right; only the explanatory "wrong-collector" numbers are wrong (the max twins, [-3,-13] and [8,12], are right).
Comment-only; no behaviour depends on it.

### F2 (Minor) Design §4/§5 and the `Collect.lean` module doc understate what a neutral copy's annotation changes
Identifiers: design §4 ("a neutral copy's annotation cannot change values, only its out-of-range pad"), `Collect.lean` module doc
("so a copy's bare out-of-range read pads the group's `0_K`").
Scenario: max group `Vn[s] := maxreduce(Q[s,a])` plus neutral copy `Vn[s] := minreduce(P[s])` with `predicate P`. As written (min-plus) the
copy reads P false as `+inf`; after the abstain rewrite (`withAgg .max`) it reads P false as `-inf` and true as `0`. With P = [0, 1] and
max_a Q = [3, 3] the user's annotation would give Vn = [+inf, 3]; the collected program gives [3, 3]. Same for a real group (F3): a neutral
`maxreduce(P[i])` copy beside a sum writer reads P as 1/0 instead of 0/-inf.
Evidence: the bool -> tropical read cast is selected by the statement's `agg` in both backends (`boolReadCast`, `ReadPlan.boolToTropical :=
tropical && isBoolSlot`), and the rewrite changes `agg`. The behaviour is the intended D5 rule and matches the scan side, whose own doc
(`scanStateStmts`) correctly names BOTH effects ("out-of-bounds pad and ... the bool -> tropical read cast"). Only the S3b-ii prose omits the
second; no fixture pins a neutral copy of a predicate source in a collected group. Doc fix: name both effects.

### F3 (Minor) A real (sum) group silently absorbs a `maxreduce`/`minreduce` NEUTRAL copy; accepted by the rule, unpinned, and section 6 reads as if refused
Identifiers: `writerVotes`, `checkWriterGroup`, design §6 "STAY: mixed groups (... sum+max ...)".
Scenario: `Y[i] := A[i, j]` (non-neutral, sum) plus `Y[i] := maxreduce(B[i + 1])` (neutral). Pre-slice: `multiWriterAlgebra "Y"`. Now:
votes = [real], agreed real, copy rewritten to `.sum`, collector sum: Y = sum_j A[i,j] + B[i+1] with a REAL `0` pad at the last cell
(and a predicate B would read 1/0, F2). No algebras entry (real group), so `checkSortCasts` does not check either writer.
Evidence: §4 says neutral writers abstain beside ANY non-neutral writer, so this is rule-conformant (and the scan mirror is pinned:
"neutral max base + min recurrence = min-plus"). But §6's "sum+max STAY" list and the CollectTest/CollectPlanTest refusal fixtures only
cover a NON-neutral max writer (C6b/C6c were edited from a neutral copy to `A[i, j]` precisely because the old neutral form now passes).
No fixture on any backend pins the real-group-absorbs-neutral-tropical-copy direction (only tropical-group-absorbs-neutral-sum-copy). Suggest
one accept fixture (values + pad 0) so the direction is a decided, observed behaviour rather than an implication.

### F4 (Minor) BoolCastTest j5 "pad not coerced" cannot distinguish coerced from uncoerced
Identifier: `BoolCastTest` (j) `j5 pad not coerced`.
Scenario: under the bool algebra the out-of-range pad is `0`, and coerce(0) = (0 != 0) = 0, so a backend that DID coerce the pad gives the
same `[0, 1, 0]`. The fixture cannot fail on the property its label names.
Evidence: `gatherFactorWith` pad path (`padV`) and reference `gatherCast` both bypass the cast; that is correct by reading. The property is
unobservable for the bool algebra (it is only observable for the tropical cast, where the pad is 0_K and a cast would map it to 1_K or 0_K
by truth: -inf != 0 -> 1_K = 0, which IS observable and is the S3b fixture). So the label overclaims; no behaviour gap.

### F5 (Minor) NaN through the tropical collector is correct by reading but pinned on no backend
Identifiers: `collectorStmt` (agg = agreed), reference `Combine.max`/`Combine.min` (`maxNaN`/`minNaN`), plan `ScalarKernelOps` reduce
(`maxNaN`/`minNaN`, `maxNaN32`/`minNaN32`).
Scenario: max group `Y[i] := maxreduce(A[i, j])`, `Y[i] := maxreduce(B[i, j])` with A = [[NaN, 1], [2, 3]], B = [[0, 0], [0, 0]]: by the
semantics Y = [NaN, 3] (writer 1 is NaN at i = 0 and max propagates NaN), on all three backends.
Evidence: the collector is an ordinary multi-term statement, so its fold is the same NaN-propagating `combine` the per-writer fold uses;
none of `tmax`/`tmin`/`tpad*`/`tinf*`/`tcopy*`/P1-P3 or `CollectEvalTest` J4/j4m carries a NaN. A one-row fixture (ref, plan f64, plan f32)
would close the lens item; no code change expected.

## Re-derived expectations (from the semantics, not the code)

All re-derived independently; every asserted value is RIGHT (only the F1 comments are wrong).

| Fixture | Inputs | Derivation | Asserted | OK |
|---|---|---|---|---|
| `CollectEvalTest` J4 | A=[[1,2],[3,4]], B=[[5,6],[7,8]] | max(max_j A, max_j B) = max([2,4],[6,8]) | [6,8] | yes |
| `CollectEvalTest` j4m | same | min([1,3],[5,7]) | [1,3] | yes |
| `CollectPlanTest` tmax / tmin | A=[[-5,-2],[-7,-4]], B=[[-9,-6],[-3,-8]] (negated for min) | max([-2,-4],[-6,-3]); min([2,4],[6,3]) | [-2,-3]; [2,3] | yes (writer 2 wins in one cell: discriminates first/last-writer mutants) |
| tpadMax / tpadMaxR / tpadMin | B 3x2, A=[-10,-1,-8] (negated for min), copy `A[i+1]` | [max(-2,-1), max(-4,-8), max(-6,-inf)] ; [min(2,1), min(4,8), min(6,+inf)] | [-1,-4,-6]; [1,4,6] | yes (0 pad would give 0) |
| tinfMax / tinfMin (all-neutral, sum copy abstains) | A=[-10,-1,-8], B=[-20,-30,-40] | [max(-1,-30), max(-8,-40), max(-inf,-inf)] | [-1,-8,-inf]; [1,8,+inf] | yes |
| tcopyMax / tcopyMin | A=[-1,-9], B=[[-5,-2],[-7,-4]] | [max(-2,-1), max(-4,-9)]; [min(2,1), min(4,9)] | [-1,-4]; [1,4] | yes (comment F1) |
| P1 / P1c / P5 | Q=[[1,5],[2,3]], Term=[4,1] | [max(5,4), max(3,1)]; P5: max over terms is idempotent over `a` | [5,3] | yes |
| P2 / P2c | R=[[1,2],[0,3]], V=[10,20], Tr one-hot with -inf, Term=[5,100] | s=0: max(1+0+10, 2+0+20)=22 vs 5; s=1: max(0+10, 3+20)=23 vs 100 | [22,100] | yes |
| P3 / P3c / P5m | W=[[0,4],[1,0]], D0=[3,1], S=[2,9] | v=0: min(0+3,1+1,2)=2; v=1: min(4+3,0+1,9)=1 | [2,1] | yes |
| belP1p / belP3p | Q neg, Term=[-10,-20]; S=[2,9] shifted | [max(-2,-20), max(-4,-inf)]; [min(2,9), min(1,+inf)] | [-2,-4]; [2,1] | yes |
| rdMax / rdReal | Q as P1, Term=[9,1] | Vn=[9,3]; Z=max copy=[9,3]; Tot = sum_s Vn = 12 (collected Vn, not writer 1's 8: readiness) | [9,3]; [12] | yes |
| Oracle `bellman` (SourceSortedDifferentialTest) | Z rows [-5..-3],[5..7],[15..17],[25..27], X=[20,2,3,40] | max: [max(-3,20), max(7,2), max(17,3), max(27,40)]; min: [min(-5,20), min(5,2), min(15,3), min(25,40)] | [20,7,17,40]; [-5,2,3,25] | yes |
| `DifferentialTest` T4.3/7 | F=[[0.25,0.75]], edge = I2, `Result[] := F[t,i]·F[t,j]·edge[i,j]` predicate | coerce F -> [1,1]; OR over (i,j) of 1∧1∧edge = 1 | 1.0 (was 0.75) | yes |
| `DualityTest` allNeutral max/min/sum/sum+max | X0=[3,4], `M[j,0] := X0[j+1]`, copy recurrence | row j=0 = 4,4; row j=1 = pad of voted sort | [4,4,-inf,-inf] / +inf / 0 / -inf; f32 bits 0xff800000, 0x7f800000 | yes |
| `ScanCompileTest` neutral scratch max/min, D2 all-neutral state | X0=[3,4]; S[j,0]=X0[j], S[j,m+1]=T[j], T[j]=X0[j+1] | j=0: [3,4,4]; j=1: [4,pad,pad] (S real copies the max-plus T's -inf) | [3,4,4,4,-inf,-inf] etc. | yes |
| `BoolCastTest` j1-j7, `ContractTest`/`ScanTest`/`ScatterTest` D1 | X={0.25,0.75,0,NaN,-2} | truth = v != 0 (NaN true): {1,1,0,1,1}; bool source identity under max(0,min(1,v)): {0.25,0.75,0,NaN,0}; sqrt unary not coerced: [0.5,1]; scan base/step layouts j-major | as asserted | yes (j5 see F4) |

## Checked and found fine

1. Collector value: `collectorStmt` now takes `sort.stateAgg`; reference folds terms with `combineFor decls T agg` (Combine.max/min,
   NaN-propagating), plan with the algebra's `reduceOp` (maxNaN/minNaN, f32 siblings). Private clones `T#k` are cloned declarations
   (`Decl.cloneAs`, predicate stays predicate, real stays real) or undeclared (default carrier), so the collector's reads of `T#k` take no
   cast in either backend (`isPredicateDest src` false / `isBoolSlot` false for a real clone). Unwritten cells cannot occur (bare free slots);
   a writer's own 0_K cells (empty reduction, OOB pad) are neutral for max/min. Readiness (collector after the last writer, readers after
   the collector: `rdReal` = 12) and hiding (`keysOf`, `privateSlots`) unchanged from slice 1.
2. Neutral-copy rewrite: applied to the renamed `T#k` only when `isSortNeutral` (slots unchanged by the rename), to `sort.stateAgg`
   (`bool`/`real` -> `sum`, so predicate and real groups are byte-identical to before except F3's newly admitted case).
3. Vote rule, both consumers, every §4 case: non-neutral voters (scan: `writerSort?` -> `scanStateAlgebraMismatch`; top level: ->
   `multiWriterAlgebra`); neutral abstains beside a voter whatever its annotation (scan pin "neutral max base + min recurrence = min-plus"
   unchanged; top level `c6dN`); all-neutral non-sum votes agree -> that sort (Duality/ScanCompile; `tinfMax`); all-neutral max vs min ->
   refusal on both (`allNeutralMismatch`, `c6eN`/`c6fN`, CompileTest "all-neutral max + min"); only sum -> real (both). Predicate
   destinations always vote `bool` (`ownAlgebra?` first arm), so the all-neutral branch never sees one. Mixed scan states take exactly the
   pre-slice path (`filterMap ownAlgebra?` non-empty); `localStateAgg`'s non-neutral branch is behaviour-identical to the old one; the
   S3bF and S3b T6 pins are untouched in the diff.
4. Init / pad / cast keys agree: scan init `scanStateAlgebra` (= first vote) and the `scanStateStmts` rewrite are idempotent (a rewritten
   all-neutral state re-votes the same sort), so evaluating on original or rewritten statements gives one sort; the cast-check key is
   `writerSort?` (scan) / the tropical group entry (top level), the same helper on the same writer list (`writerGroups` and
   `scheduleAlgebras` select the same plain writers; a non-`.assign` writer means no entry and collection refuses or votes real).
   Real/bool groups get no entry and `checkSortCasts` skips their writers, which is harmless (a real statement accepts every source).
5. D1 call sites: reference `boolReadCast` takes the destination at all three callers (`evalAssignDtypedSeeded`: top-level plain, scan
   base/step and the scan-scatter projection; `Eval.lean` scatter `pre`; `evalScatter`); the identity-cast `evalAssignWith`/`evalAssign`
   have no production caller. Plan: one `ReadPlan` constructor sets `realToBool` (grep), all four `residualizeAssignment` callers pass
   `dtypeOfDecl (declEnv[nm]?) == .bool`; source boolness is the slot dtype, which `prepareEvalPlan` forces equal to `dtypeOfDecl`
   (InputSignature `dtypeMismatch`), so reference (declaration) and plan (slot) agree on "source is bool". Only `gatherFactorWith`
   consumes the flag (bare in-bounds only; pad and missing slot bypass; `.unaryFn` builds its own ReadPlan with the flag false). The JAX
   executable gate refuses bool destinations/algebra, so it cannot silently drop the flag. NaN: `isTrue` is `v != 0` in f64 and f32 (NaN
   true, -0.0 false in both). Contracted predicate: ContractTest and DifferentialTest T4.3/7.
6. D1 on collected predicates: writer `P#k := X[i]` (P#k predicate clone) coerces once; the collector's reads of `P#k` are bool -> bool
   (identity) in both backends, so there is no double coerce; a unary predicate writer stays uncoerced and the collector's OR keeps its
   raw value, matching the single-writer program.
7. D1 vs tropical: a `predicate`-named destination under `agg = max` (raw reference only; `predicateAgg` blocks the surface) keeps the
   identity, consistent with `combineFor` choosing by agg first. Tropical -> bool stays `sortCastUnsupported`; the D3 one-copy bypass
   (`C := M[i]` real, then `P := C[i]`) now reads a max-plus `-inf` as TRUE, which is the documented D3 consequence.

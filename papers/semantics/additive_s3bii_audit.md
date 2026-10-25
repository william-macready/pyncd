# S3b-ii audit (read-only): tropical multi-writer collection

Main at 04e2aef0. Identifiers, not line numbers. Nothing here was run (no lake, no build): every claim is from reading code or tests. "Unobserved" = hand-derived.

## 1. Sum collection today, and the minimal change

Path: `validateScheduled` -> `checkScheduledDtypes` (incl. `checkPredicateOutput`, `checkTropicalOutput`) -> `scheduleAlgebras` -> `checkSortCasts` -> topology -> `collectDefinitions` -> `desugarMultiWriters` (Pipeline/Collect.lean).

- `writerGroups`: names written by >= 2 nodes, all `.plain` `.assign`/`.scatter`. `scanWriterConflict?` (any name with >= 2 writer nodes of which one is a scan node) throws `multiWriterScan` first.
- `checkWriterGroup` order: (1) `.scatter` or `slotsBecomeScatter` -> `multiWriterScatter`; (2) `.assign _ _ r => unless r.agg == .sum do throw (.multiWriterAlgebra g.name)`; (3) shape: every slot has `freeUID?` equal to writer 1's, same length, else `writerShapeMismatch name k pos`.
- Rename: writer k (1-based schedule order) becomes `T#k` (`collectorName`), in place. One collector is inserted right after the last writer: `T[producerSlots firstSlots] := T#1[idx] + ... + T#n[idx]` (`collectorStmt`: n one-read monomials, `nonlin := .identity`, `agg := .sum`). Source comment: "Sound only because `checkWriterGroup` rejects every non-sum writer; lifting `multiWriterAlgebra` must thread the writers' agreed annotation here."
- `reservedNameCollision` last. Clones: `Decl.cloneAs` gives each DECLARED T one clone per writer (same constructor, so a `predicate T` gets predicate clones); undeclared T gets none.
- Readiness: `eligible` counts publications == number of writer nodes, so readers wait for ALL writers; the collector is inserted after the last writer so readers follow it.
- Predicate T: the collector is `.sum` but `combineFor` / `algebraForDest` pick Boolean OR from the declaration. A predicate writer with max/min never reaches collection: `checkPredicateOutput` throws `predicateAgg` first (Structural.lean, `else if !(rhs.agg == .sum) then throw (CompileError.predicateAgg nm)`).

Minimal change (Collect.lean only, ~20 lines):
- Replace `unless r.agg == .sum` with an agreement test: every `.assign` writer has the same `agg`. Add one helper `writerGroupAgg? : List Stmt -> Option AggOp` (some a iff all writers share `a`).
- Disagreement (max+min, sum+max, max+sum, min+sum) keeps `multiWriterAlgebra g.name`; no new constructor. All-max, all-min, all-sum are admitted.
- `collectorStmt` takes the agreed agg: `agg := agreed`. Keep `nonlin := .identity` (tropical writers already have identity nonlin: `checkTropicalOutput` -> `tropicalNonlin` runs before collection, inside `checkScheduledDtypes`).
- Predicate T: agreed agg is `.sum` by the earlier `predicateAgg`, so unchanged.

Is the collector then an ordinary single-writer tropical statement? Yes, verified in both evaluators:
- Reference: `evalAssignSeeded` loops `for t in rhs.body.terms do ... acc := combine acc termAcc`, with `combineFor decls nm rhs.agg` = `Combine.max`/`Combine.min` for agg max/min (agg is tested BEFORE the predicate lookup). A one-read monomial gives `mul unit1 v = 0 + v = v`, so the collector is exactly `max(T#1, ..., T#n)` (NaN-propagating `maxNaN`), seeded with `unit0 = -inf`.
- Checked plan: `denseValueAtWith`, "§2.2 fold 3: the completed TERMS ... Uses `reduceOp`/`reduceId` again", and `algebraForDest destDtype rhs.agg` selects max-plus or min-plus (f64 and f32 tables). `residualizeAssignment` sets `boolToTropical` only for a `.bool` source slot; the `T#k` clones are real, so no cast.
- No backend change. The collector is not neutral (several terms), and it never passes through `checkSortCasts` (collection runs after it).

Two non-backend changes ARE needed (see 2c): the `algebras` map entry for the agreed sort, and docs/tests.

## 2. Soundness traps

a. Unwritten cells / 0_K: `checkWriterGroup` forces bare free slots on writer 1's axis UIDs, so every writer's `T#k` has the full declared extent and every cell is computed (acc starts at `unit0 = -inf`/`+inf`; a cell with only out-of-range bare reads pads `zeroPad` = the algebra's `reduceId` = 0_K). So no unwritten cell exists, and any 0_K cell is neutral for the collector's max/min. Partially covering writers (affine, const, diagonal, `iterAt`) are refused: `multiWriterScatter` or `writerShapeMismatch` (`freeUID?` is none for `iterAt`/`iterNext`). Extents differ only if axis UIDs differ -> `writerShapeMismatch`.
b. Neutral writers (`Stmt.isSortNeutral`: one term, one read, no contracted axis, identity nonlin): neutrality is used ONLY inside scan nodes (`scanStateStmts`, `scanStateSorts`). At top level `scheduleAlgebras` uses `.plain s => s.algebra env`, the annotation as written. `checkWriterGroup` today tests `r.agg == .sum` on every writer, neutral or not, so `Vn[s] := maxreduce(Term[s])` is refused. Under the minimal change a neutral writer's annotation COUNTS in agreement (consistent with top-level `s.algebra`). Its `T#k` is a pure copy, so value-wise harmless. Open design question (not decided here): should a neutral SUM-annotated copy (`D[v] := S[v]`) abstain, so it can pair with a `minreduce` writer? Strict agreement refuses it. Recommend strict (simplest; the user's two target programs annotate both writers). D2 does not interact: it only changes scan-state votes, and multi-writer names with a scan writer stay refused.
c. Sort map and casts (the real trap): `scheduleAlgebras` skips top-level names with 2+ writers (`if (stmts.filter ...).length == 1`), and `checkSortCasts` skips a destination with no entry ("A destination with no entry (a multi-writer name) has no single sort"). Today unreachable for tropical sets; after S3b-ii it is reachable: (i) a writer reading a min-plus N into a max-plus T would not be cast-checked; (ii) a bool or other-tropical reader of T would see `algebras["T"]? = none` -> `declAlgebra` = real, so a bool statement reading max-plus T is accepted (and -inf reads as true), the C21 hazard. Fix: `scheduleAlgebras` inserts the agreed sort for a multi-writer group (same `writerGroupAgg?` helper, then `AggOp.algebra`; use `Stmt.algebra env` so a `predicate` stays bool; insert no entry on disagreement so collection's `multiWriterAlgebra` stays the refusal). The private `T#k`/collector are never seen by `checkSortCasts` (source schedule only); `algebraOf T#k` falls through to real by the clone declaration, fine since only the collector reads them.
d. Scatter writers: refused first (`multiWriterScatter`), stays (B5). Scan-node writers: `multiWriterScan`, stays. A `.recurMorphism` writer: skipped by `writerGroups` (not traced; unchanged).
e. Nonlinearity: `tropicalNonlin` is thrown in `checkScheduledDtypes` before `collectDefinitions`, so a relu/softmax tropical writer never reaches collection.
f. Pre-existing, inherited unchanged: under `unaryFn` an out-of-range read pads real `f(0)` and can win a tropical reduction (parked minor in the S3b record section 9). A writer with such a read passes its value to the collector verbatim.
g. Declared f32/f64: clones copy the declaration; `-inf` is representable in both. Mixed storage is refused by `scheduleStorageKind` as today.
h. Readers: Bellman programs read `Vn` after the collector via all-writers readiness. No new ordering issue.

## 3. Is F3 needed?

No, for top-level collection. The collector writes full bare-free cells; no scatter and no scan-local placement is involved. Evidence the scan path never needed it: `writeScanStmtSlice` doc, "The checked scan path admits only injective, in-range placements (`multiAxisScatterLhs`, `duplicateAxisInLhs`, `classifyWriteRow`)", and the scan checkers reject a second producer: reference `checkRecurProducers` throws `duplicateStateResult` / `duplicateScratchProducer`; plan `Compile.lean` throws the same constructors; `checkWrites` throws `duplicateWriteForOutput`.
Consequence for "inside scans if feasible": two statements writing one state or scratch name inside a scan body are refused by BOTH backends today (ScanTest pins `duplicateStateResult "S" "S" 0 1`, `duplicateScratchProducer "S" "T" 0 2`). In-scan multi-writer collection would need a new scan-body desugar (private per-step scratch `T#k` plus a collector, inside the recurrence) and is NOT part of the minimal change. It still would not need F3 (no scatter). Today's in-scan workaround is a single multi-term statement: `V[s, t+1] := maxreduce(Q[...] + Term[s])` (per-term contraction scoping in `evalAssignSeeded`, `termContr` per term; plan `residualizeAssignment` per term). F3 only matters if scatter writers (B5) or neutral `Out[i+j]` collisions (parked) are pulled in.

## 4. D1 and D2 impact

### D1: real -> bool read coerces via (stored != 0)
Code sites (reference):
- `boolReadCast decls c agg` (Eval/Contract.lean): the `.sum` arm is `fun _ v => v`; the `.max | .min` arm tests `isPredicateDest decls nm` on the SOURCE. It does not know the destination. A coerce needs the destination name: for `.sum` with `isPredicateDest decls dest`, `fun src v => if isPredicateDest decls src then v else (if v != 0.0 then c.unit1 else c.unit0)`.
- Callers: `evalAssignDtypedSeeded` (has `nm`; also serves scans via `Scan.evalStmtSliceSeeded`) and `Eval/Scatter.lean` (`gatherCast c.unit0 c.unit1 (boolReadCast decls c rhs.agg)`; reference accepts predicate scatter, ScatterTest).
Code sites (plan):
- `residualizeAssignment` (Compile.lean) sets `boolToTropical := tropical && isBoolSlot sourceSlot`; it has `agg` but not the destination dtype (the dest algebra is overridden later by `algebraForDest`). Needs a destination-is-bool parameter at its top-level plain call site and the scan base/step call sites, and a new `ReadPlan` flag (Kernel.lean) beside `boolToTropical`.
- `gatherFactorWith` (Dense.lean; shared f64/f32 via `ScalarKernelOps.isTrue`, which exists for both) applies it; `checkAssign` (Check.lean, `castNotAdmitted` branch) must admit it only for a bare read, bool algebra, non-bool source.
- Raw-plan kernel tests (`KernelDenseTest`, `KernelDense32Test`, `AdapterTest`) build `ReadPlan`s directly; a flag defaulting to false leaves them unchanged.
Fixtures (rg of the test tree: 44 files mention a predicate declaration; only a few read a real tensor from a predicate statement with non-{0,1} values; I did NOT classify every statement of the 44):
- FLIPS: `DifferentialTest` "T4.3/7 boolean scalar non-binary" (`predicatePrograms`, expected `0.75`) and its direct `checkBoolScalar ... boolScalarInputsNonBinary 0.75`: F=[0.25,0.75] real source into predicate `Result` -> coerced F=[1,1] -> Result = 1.0 (hand-derived, unobserved). Its explanatory comment ("not a value coerced to {0,1}") needs rewriting.
- COMMENT/PIN CHANGE: `CompileTest` "predicate reads a real tensor (parked decision 1: real -> bool is the identity)" (accept, still accepted); `BoolCastTest` section (c) "neighbours: bool -> real and real -> tropical are the identity" (real -> bool is not in that list, add a case); the Adapter32 non-binary "uncoerced" block (inside a comment).
- BINARY-VALUED, unchanged (values 0/1): `WaveBRegressionTest` #3, `Eval/ContractTest` (predicate `Result` over `F = [1,1]`), `EvalExamplesTest` #6 (`Result` is NOT a predicate; only `edge` is).
- Collection: `CollectEvalTest` V4 and `CollectPlanTest` h3/h3d32 (`predicate R; R := A; R := B` with real A,B) are binary-valued; unchanged. The collector reads predicate clones, so no coerce there.
- Oracle: not touched (the oracle has no bool destination reads in the sorted legs; unverified).
Interaction with S3b-ii: none functionally; D1 makes a real-sum multi-writer predicate set with non-binary inputs agree with its OR-of-truths meaning.

### D2: all-neutral scan state's annotation votes
- Current rule: `scanStateAlgebra env ss nm = (scanStateSorts env ss nm).headD .real`, where `scanStateSorts` = `filterMap Stmt.ownAlgebra?` (neutral writers return none). `scanStateStmts` rewrites each neutral writer's agg to `(scanStateAlgebra ...).stateAgg`. Consumers: `Eval/Scan.lean` (`scanStateStmts`; `combineFor ... .stateAgg).unit0` state init), `Eval/Plan/Compile.lean` (`scanStateStmts declEnv base recur`; `initValue := match scanStateAlgebra ...`), `scheduleAlgebras` (agreement via `scanStateSorts`, so a vote conflict throws `scanStateAlgebraMismatch` for free).
- Change point is one definition: `scanStateSorts`/`scanStateAlgebra` in DSL/Ast.lean: when the non-neutral list is empty, take the non-sum `agg.algebra` of the neutral statements as votes. All backends and the agreement check follow.
- Pinned fixtures that flip: (1) `DualityTest` `parkedAllNeutralScanState`: M = [4,4,0,0] on ref and plan -> [4,4,-inf,-inf] (the fixture's own comment states this alternative). (2) `ScanCompileTest` "S3bF/neutral scratch max" and "...min": expected `[3,4,4,4,0,0]` -> max `[3,4,4,4,-inf,-inf]`, min `[3,4,4,4,+inf,+inf]` (scratch T votes tropical; real state S copies T; hand-derived, unobserved). "neutral scratch sum" unchanged. (3) The independent property oracle `localStateAgg` and `oracleNeutral` guards in `PropertyOracle/ScanUnroll.lean`/`ScanOracle.lean` must be restated (`localStateAgg` today: first non-neutral annotation, else `.sum`), plus the duality-property corpus entries whose states are all-neutral (not enumerated).
- Not flipping: `CompileTest` scan-agreement fixtures use `scanRecur`, a two-term body (non-neutral), so neutral bases there still abstain.
- Independent of S3b-ii (no scan multi-writer). Relevant to the Bellman-in-scan single-statement form only if a state or scratch is all-neutral.

D3 stays: nothing in the minimal change needs the cast rejections lifted; a max/min disagreement between writers is refused outright, and bypass by a real copy is unchanged.

## 5. Tests pinning the refusal

| Test | Now | S3b-ii |
|---|---|---|
| `CollectTest` C6 (`Y := maxreduce(A[i,j])` x2) | `multiWriterAlgebra "Y"` | FLIP: now admitted; assert `dests` = ["Y#1","Y#2","Y"] and collector agg `.max` |
| `CollectTest` `c6min` | same | FLIP likewise (agg `.min`) |
| `CollectTest` C6b, C6c (sum+max, max+sum), `c6bm`, `c6cm` (sum+min, min+sum) | `multiWriterAlgebra` | KEEP (mixed). Add max+min both orders |
| `CollectEvalTest` J4, `j4m` | `compile failed: ... multiWriterAlgebra "Y"` | FLIP to value tests: A=[[1,2],[3,4]], B=[[5,6],[7,8]] -> Y = [max(2,6), max(4,8)] = [6,8] (max), min-plus [1,3]; hand-derived, unobserved |
| `CompileTest` (d) "multi-writer tropical set keeps multiWriterAlgebra" (`W := N`, `W := B`, N min-plus) | `multiWriterAlgebra "W"` | FLIP to `sortCastUnsupported "W" "N"` once `scheduleAlgebras` gives W its entry (writer 1 reads min-plus N into max-plus W) |
| `CompileTest` `s3bPins` ("two-writer name no entry", real W) | no entry | changes only if entries are inserted for sum groups too. Insert for tropical groups only (or accept the pin change) |
| `CompileTest` C20/C21 prose, S3b plan table rows | "backstop" | rewrite |
| `CollectTest` C5 (`multiWriterScatter "S"`), scan-writer block (`multiWriterScan`), priority tests (~L348-537), `CollectEvalTest` S/scan pins | refusals | KEEP |

`rg multiWriterAlgebra` over `.lean`: only the sites above plus `Collect.lean`, `Exec/Uid.lean`. Must stay refused: mixed sorts (incl. sum+tropical), scatter writers (B5), scan-node writers, nonlinear tropical writers, shape mismatches.

## 6. Oracle (Semantics/Source)

- The oracle collects by target: `Oracle.lean` iterates declaration targets and takes every statement whose `output.tensor` declaration equals the target; the model is `Program.collect_grouped` (sum of per-statement collections with the semiring's ⊕). Admission has no multi-writer refusal for bare writes; `detectConditions` flags only non-bare multi-writers (`multiWriterScatter`, a REAL-harness "known" difference).
- Sorted path: `admitSourceSorted` picks ONE carrier from `sortKeys` (every statement's agg and element type); a mix is `sortSelection (mixedSorts ..)`. A Bellman program whose statements are all `maxreduce` (or all `minreduce`) is single-sort, so the max-plus/min-plus carrier's ⊕ = max/min should collect the two writers with no oracle code change.
- No existing sorted fixture has two writers of one tensor (the "multi" fixtures in `SourceSortedDifferentialTest` are multi-FACTOR, `multiY`/`multiV`). Not verified that nothing downstream (`NativeLegs`, classification of production outcomes) mis-tags it.
- Least work: no oracle change; add 2-3 fixtures (Bellman max, shortest-path min, plus mixed refusal expected as `mixedSorts` on the oracle side vs `multiWriterAlgebra` in production, which needs a classification decision). Honest fallback if the harness mis-classifies: production-only coverage (CollectEvalTest/CollectPlanTest/DifferentialTest ref-vs-plan f64/f32), as S3b did for duality.
- Caveat: a Bellman program mixing a sum statement (e.g. an input-normalisation copy) is outside the single-sort oracle.

## 7. Bellman target programs (hand-derived, unobserved; syntax per `tlprog!`: product is ` · `, axes `axis s : ℕ = 2, a : ℕ = 2`)

P1 continuing vs terminal (refused today, `multiWriterAlgebra`):
```
axis s : ℕ = 2, a : ℕ = 2
Vn[s] := maxreduce(Q[s, a])
Vn[s] := maxreduce(Term[s])
```
Q=[[1,5],[2,3]], Term=[4,1] -> Vn = [max(5,4), max(3,1)] = [5, 3]. Collected: `Vn#1=[5,3]`, `Vn#2=[4,1]`, collector max.

P2 with a deterministic transition (inputs carry -inf as 0_K):
```
Vn[s] := maxreduce(R[s, a] · Tr[s, a, t] · V[t])
Vn[s] := maxreduce(Term[s])
```
R=[[1,2],[0,3]], Tr[s,a,t] = 0 if t=a else -inf, V=[10,20], Term=[5,100]. Vn[0]=max(1+10, 2+20, 5)=22; Vn[1]=max(0+10, 3+20, 100)=100 -> [22,100].

P3 shortest paths with source init (refused today):
```
axis u : ℕ = 2, v : ℕ = 2
D[v] := minreduce(W[u, v] · D0[u])
D[v] := minreduce(S[v])
```
W=[[0,4],[1,0]] (W[u,v]), D0=[3,1], S=[2,9]: D[0]=min(0+3, 1+1, 2)=2; D[1]=min(4+3, 0+1, 9)=1 -> [2,1].

P4 refusal neighbours (expected `multiWriterAlgebra "Y"` before and after): `Y[i] := maxreduce(A[i,j]); Y[i] := minreduce(B[i,j])` and sum+max. B5 neighbour (`multiWriterScatter`): two affine `S[2*i]` writers.

P5 single-statement equivalent that should parse and run TODAY (also inside scans, since it is one statement): `Vn[s] := maxreduce(Q[s, a] + Term[s])`, same value [5,3] as P1 by per-term contraction scoping (read from `evalAssignSeeded`, unobserved). Worth stating to the user: the target semantics already has a one-statement form, so the multi-writer feature buys ergonomics outside scans, not expressiveness.

P6 scan form (believed to parse; scan syntax from `Bridge/RealizeTest`: `iter l = 3`, `G[j, l +1] := ...`): base `V[s, 0] := maxreduce(V0[s])`, recurrence `V[s, t +1] := maxreduce(R[s, a] · Tr[s, a, u] · V[u, t] + Term[s])`. Not hand-evaluated; base slot form `V[s, 0]` unverified.

## 8. Size, risks, unverified

Size (patches, Direct vs plan per slice-plan section 0; this is above Direct):
1. `Collect.lean`: `writerGroupAgg?`, agreement in `checkWriterGroup`, `collectorStmt` agg, doc comment; flips C6/c6min (~1 patch).
2. `ScheduledValidation.lean`: agreed-sort entry in `scheduleAlgebras`; flips CompileTest (d); new C20/C21 fixtures (~1 patch).
3. Value tests both backends and f32: J4/j4m flips, P1-P3, mixed refusals, readers of T by bool/other-tropical (`sortCastUnsupported`), predicate and scatter/scan-writer neighbours (~1-2 patches).
4. Four-leg or three-way fixtures (DifferentialTest, SortedDifferential), or the production-only fallback (~1 patch).
5. Docs and mutation manifest (decision note, AGENTS rows, record, `papers/max_min_aggregation.md`, `backend_missing_functionality.md`) (~1 patch).
Folded decisions as separate Direct-sized tasks: D1 (~2 patches: reference + plan flag/check + one fixture flip + comment pins), D2 (~1-2 patches: `scanStateSorts` + `ScanUnroll`/`ScanOracle` restate + 3 flips). In-scan collection: separate slice, only on request. Total about 5 core + 3-4 for D1/D2.

Top 3 risks:
1. Missing `algebras` entry for multi-writer tropical names: silently disables cast checks for writers and readers (2c). Must ship with the collection change, with fixtures for both directions.
2. Writer agreement for neutral/copy writers (strict vs abstain): wrong choice either refuses a natural program (`D[v] := S[v]` sum copy + min writer) or blurs the sort rule; needs a user ruling.
3. Oracle/classification harness: a refused-vs-admitted mismatch (mixed writers: oracle `mixedSorts` vs production `multiWriterAlgebra`) or an untested multi-writer path in `NativeLegs` could make four-leg parity cost more than planned; fallback is production-only.

NOT verified: anything by execution; whether `route`/`RouteFragments` (calls `desugarMultiWriters` directly) classifies a multi-term tropical collector like other multi-term tropical statements (existing fixtures suggest yes); the complete set of predicate-destination fixtures reading real non-binary values (only the listed modules were inspected); that the oracle or `NativeLegs` accept a two-writer sorted program; exact scan syntax in P6; `.recurMorphism` writer handling in `writerGroups`; docs/AGENTS rows that mention the refusal (not grepped beyond `papers/semantics`).

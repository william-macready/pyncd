# S3b read-only audit (tropical sorts become true max-plus / min-plus)

Date 2026-10-22, tree = main 740bd4f8 (clean). Read-only: no edits, no builds. Every claim cites file:line that was read
this session. Paths are relative to `/Users/williammacready/code/python/pyncd/leanncd/` (`LeanNCD/...` = sources,
`test/...` = tests) unless prefixed `papers/` (repo root). UNVERIFIED marks anything I did not read.

Budget: about 60 tool turns used; Q6 (Python/JAX) and Q9 (docs) are enumerations by grep, not full reads.

## 0. Greps used (re-runnable from `leanncd/`)

```
# Q1/Q2 production sites
grep -rn 'algebraForAgg\|algebraForDest\|algebraForAggF32\|admittedAlgebra\|combineFor\|isPredicateDest\|Combine\.\(max\|min\|bool\|real\)' --include=*.lean LeanNCD
grep -rn 'AggOp\|\.agg\b\|agg :=\|maxreduce\|minreduce' --include=*.lean LeanNCD
grep -rn 'factorOp\|factorId' --include=*.lean LeanNCD test
grep -rn 'Float32.ofBits\|0xff800000\|0x7f800000\|0x3f800000' --include=*.lean LeanNCD
grep -rn 'Max.max\|Min.min' --include=*.lean LeanNCD
grep -n 'DenseTensor.zeros\|replicate\|0\.0\|zeroPad' LeanNCD/Eval/Plan/*.lean LeanNCD/Eval/*.lean
# Q5
grep -rn 'mul_add\|add_mul\|CommSemiring\|\[Semiring\|ScalarOps' LeanNCD/Semantics/*.lean LeanNCD/Semantics/Plan
grep -rn -i 'tropical\|distribut\|factorOp\|max-plus\|max-times' --include=*.lean LeanNCD/Semantics LeanNCD/Algebra ...
# Q6
grep -rn 'maxreduce\|minreduce' --include=*.lean LeanNCD/Bridge LeanNCD/DSL LeanNCD/Seam
grep -n -i 'max\|min\|tropical\|algebra\|reduce' experiments/jax_bridge/*.py experiments/jax_bridge/README.md
# Q7
grep -n -i 'tropicalMultiFactor\|tropicalScatterFill\|unexplainedAgree\|confirmsSorted\|scatterFillNotIdentity\|zeroV\|tropical' LeanNCD/Semantics/Source/*.lean test/Semantics/*.lean
# Q8 (coarse; lines saved in scratchpad/grep8.txt, 109 lines)
grep -rnE 'maxreduce|minreduce|agg *:= *\.(max|min)|\brhs[A-Za-z0-9_]* *\.(max|min)\b|AggOp\.(max|min)|admittedAlgebra(F32)?(Max|Min)|algebraForAgg|Combine\.(max|min)|scatterFillNotIdentity|scatterOptsNotAdmitted|\(\.(max|min)\)' --include=*.lean test
grep -rnw 'gather' --include=*.lean LeanNCD test
for fn in evalPlain evalAssignDtyped evalScatter evalStmtSliceSeeded evalScan combineFor prepareEvalPlan ...; do grep -rw "$fn" ...; done
# Q9
grep -rlniE 'max-times|max-product|min-product|min-times|×, max|\(×, ?min|\(max, ?×|tropical|-inf identity|−∞ identity' --include=*.md .
```

Caveat on Q8: the regex only finds tests that write `maxreduce`, `agg := .max`, `rhs .max`, the algebra constants, or the
refusal constructors. A test building a max statement through a differently named helper would be missed (UNVERIFIED that none exist).

---

## 1. Constant / identity / padding sites

Legend: ALG = reads the algebra (Combine / ContractionAlgebra fields); HARD = literal 0.0 / 1.0 / Float zero.

| # | Site | What it produces | ALG or HARD | S3b change |
|---|---|---|---|---|
| 1 | Eval/Gather.lean:50-51 (`gatherRead`) | out-of-bounds read pad | HARD `0.0` | bare read: pad with 0_K of the statement sort. Under `.unaryFn` (Gather.lean:74-76, via `gatherRead`): keep 0.0 (A6), apply f, then cast |
| 2 | Eval/Gather.lean:72 | Iverson true/false | HARD `1.0`/`0.0` | must return 1_K/0_K (tropical: `0.0` / `∓∞`) |
| 3 | Eval/Contract.lean:119,128,131 | accumulator, per-term accumulator, empty product | ALG (`unit0`/`unit1` params of `evalAssignSeeded`, Contract.lean:88-89) | none by itself; follows the new `Combine` |
| 4 | Eval/Contract.lean:160 `Combine.real`, :163 `Combine.bool` (`⟨min,max,0.0,1.0⟩`), :167 `Combine.max` (`×`,max,−∞,1.0), :171 `Combine.min` | the semiring records | ALG definitions | tropical records become `(+, max⊕NaN, ∓∞, 0.0)`; share one definition parameterised by (⊕, 0_K) |
| 5 | Eval/Contract.lean:150 `evalAssign := evalAssignWith (·*·) (·+·) 0.0 1.0` | real default | HARD but real-only | none |
| 6 | Eval/Scatter.lean:58 `DenseTensor.ofFn outShape (fun _ => 0.0)` | scatter fill / empty fibre | HARD `0.0` | init with `c.unit0` (0_K of destination) |
| 7 | Eval/Scatter.lean:63,65 | per-source-coord value | ALG (`c.unit0`/`c.unit1`) | follows `Combine` |
| 8 | Eval/Scatter.lean:57,77 | collision fold | HARD: `Max.max` if `isPredicateDest` else `prev + val` | fold with `c.combine` (real `+`, bool `max`, tropical `max`/`min`). The `boolDest` special case then disappears |
| 9 | Eval/Scan.lean:318 `DenseTensor.zeros stateShape` (zeros def Eval/Tensor.lean:56) | scan state init = value of every unwritten/boundary cell | HARD `0.0` | init with 0_K of the state's sort. This is what turns RC10's G[0,1] into −∞ (decision note A10) |
| 10 | Eval/Scan.lean:326,344 `getD (DenseTensor.zeros [])` | defensive default for a missing state | HARD, empty shape | none (shape `[]`, not reachable as data) |
| 11 | Eval/Scan.lean:102-117 (`writeScanStmtSlice`) | scan write: skip if out of range, overwrite on collision | not an identity site | unchanged by S3b-i (parked F3, see Q4) |
| 12 | Plan/Dense.lean:48-51, 78-79, 107-108 (`ScalarKernelOps.zero/one`: 0.0/1.0 and `+0`/`0x3f800000`) | carrier exact 0/1 | HARD (by design: "the CARRIER's own exact zero") | keep as the real-sort constants; stop using them for pad and Iverson in tropical statements |
| 13 | Plan/Dense.lean:131-138 (`gatherFactorWith`): `none`/OOB gives `ops.zero` | OOB pad | HARD via `ops.zero`. NOTE: the doc comment at :126-128 says the pad is "never the algebra's reduction identity ... which is what makes a padded 0 beat an all-negative column under tropical max". That is the exact design S3b reverses | bare read: pad with decoded `reduceId`; unary read (Dense.lean:139-141): keep `ops.zero` |
| 14 | Plan/Dense.lean:235-239 | Iverson true -> `ops.one`, false -> `ops.zero` | HARD via `ops` | true -> decoded `factorId`, false -> decoded `reduceId` (already decoded at :222-223) |
| 15 | Plan/Dense.lean:219-223, 241, 244, 249 | factor fold seed `factorId`; reduce/term fold seed `reduceId` | ALG | none: empty product = `factorId`, empty sum / zero-extent reduction = `reduceId` fall out once the algebra constants change |
| 16 | Plan/Dense.lean:384, 391 (`runDenseScatterWith`) | scatter fill `reduceId`, collision fold `reduceOp` | ALG | none. The checked scatter worker is already algebra-generic (S3a). Only the guards block tropical scatter |
| 17 | Plan/Check.lean:37-39 `admittedAlgebra`; :44-46 `admittedAlgebraMax` (`.mul`, 1.0, `.max`, −∞); :50-52 `Min`; :67-69 `admittedAlgebraBool`; :104-106, :110-112 `F32Max` (`reduceId` 0xff800000), :116-118 `F32Min` (0x7f800000) | algebra constants (f64 via `Float.toBits`, f32 as bit patterns) | the definitions | tropical: `factorOp := .add`, `factorId := .f64 (toBits 0.0)` / `.f32 0x00000000`; `reduceOp`/`reduceId` unchanged. `ScalarBinOp.add` exists (Plan/Types.lean:84-86) |
| 18 | Plan/Check.lean:75-76, 90-93, 121-122, 130-133 | tables `admittedAlgebras`, `admittedAlgebrasFor`, F32 twins | table membership (`checkAssignCore`, Check.lean:262-270) | keep shape; contents follow #17 |
| 19 | Plan/Types.lean:49-52 `OutOfBoundsPolicy.zeroPad`; Check.lean:317 requires it | policy name | name only | name now misleading for tropical (pads 0_K). Either rename or document; every `ReadPlan` literal in tests mentions `.zeroPad` |
| 20 | Plan/Scan.lean:742 (state init `Array.replicate ... zero`), :780 `runDenseScanWith 0.0`, :788 `(0.0 : Float32)`, :687 (`commitWrite` default `zero`) | checked scan state init | HARD zero passed in | per-state 0_K; needs the state's sort in `CheckedScanPlan` / `ScanStatePlan` (UNVERIFIED which struct: I did not read `ScanStatePlan`) |
| 21 | Plan/Compile.lean:652-654 (doc), :655-658, :664-667, :693-697, :775 | selection of algebra from `agg` (see Q2) | n/a | Q2 |
| 22 | Plan/Executable.lean:259-260 | JAX gate `a.algebra == realAlgebra` | comparison to the real algebra | none; tropical stays refused (README.md:217) |
| 23 | Semantics/Plan/* and Semantics/*.lean | abstract machine over `ScalarOps (K s)` per sort (Semantics/Types.lean:50-54) | parametric | none (see Q5) |

Not found: any f32-specific padding code other than #12-#16 and #17 (Adapter32.lean / Dense32.lean contain no `0.0`/algebra
literals, grep over Plan/*.lean). f32 reaches the same `denseValueAtWith` via `float32Ops` (Dense.lean:101-115), so the f32
change is (a) the three constants in #17, (b) the `Float32` min/max NaN behaviour.

`Max.max`/`Min.min` sites (NaN-propagation, A9): Contract.lean:163 (bool), :167, :171; Scatter.lean:77; Dense.lean:83-84 and
:112-113 (both `ScalarBinOp.min/max` arms). The bool algebra uses the same two `ScalarBinOp`s (Check.lean:67-69), so making
`.min/.max` NaN-propagating changes bool behaviour on non-binary NaN inputs too. Decide whether that is acceptable or whether
tropical gets its own op (see Q11).

---

## 2. Algebra-selection sites

| Site | Today | Switch to "sort derived from writer annotation" |
|---|---|---|
| Eval/Contract.lean:179-184 `isPredicateDest decls nm` | first tensor-bearing decl match is `.predicate` | `algebraOf nm == .bool` (A5) |
| Eval/Contract.lean:189-193 `combineFor decls nm agg` | `.max`->`Combine.max`, `.min`->`Combine.min`, `.sum`-> bool if predicate else real | `Combine.of (algebraOf nm)` |
| Eval/Contract.lean:247-253 `evalAssignDtypedSeeded` | calls `combineFor decls nm rhs.agg` | single choke point for plain assign AND scan assign AND scan-local scatter (Scan.lean:62, :70) |
| Eval/Scatter.lean:54,57 | `combineFor` + `isPredicateDest` | as above |
| Eval/Eval.lean:32-35 `checkScatterAgg`, :57 | refuses `.max/.min` top-level scatter | delete guard (and `EvalError.scatterFillNotIdentity`, Eval/Error.lean:359, once unreferenced) |
| Eval/Eval.lean:144 `validateScheduled`, :148 f32 refusal, :178/:181 `evalPlain`/`evalScan` with `sched.decls` | reference entry takes `decls` only | the natural home for `algebraOf` is `CheckedScheduledProgram` (ScheduledValidation.lean:144-149: fields `program, declEnv, explicitSizes, extNames, privateNames`; constructor private, built at :163-167). Add `algebras : HashMap String Algebra` there; both entries already go through `validateScheduled` (Eval.lean:144; Compile.lean:1387-1391) |
| DSL/Pipeline/Structural.lean:980-988 `checkPredicateOutput` (predicateNonlin, predicateAgg) | rejects predicate + non-identity nonlin or non-sum agg | keep; add new checks next to it in `checkScheduledDtypes` (Structural.lean:1016-1020): writer agreement (A4), nonlin != identity with tropical (A8), cast legality (A7) |
| DSL/Pipeline/Collect.lean:100 (`multiWriterAlgebra` unless `agg == .sum`), :115-121 (`collectorStmt`, comment: "Sound only because `checkWriterGroup` rejects every non-sum writer; lifting `multiWriterAlgebra` must thread the writers' agreed annotation here") | rejects tropical multi-writer; collector is `agg := .sum` | S3b-ii only; collector must carry the agreed `agg` |
| DSL/Pipeline/Lowering.lean:472-474 | `BrOp` label from `s.agg` | label only (Q6) |
| DSL/Pipeline/Lowering.lean:64-70, DSL/Pipeline/RouteFragments.lean:271-275 | split a nonlinear statement into a linear step (keeps `agg`) and a `.sum` nonlin step | `splitNonlins` is regression-only (Lowering.lean:3, DSL/Compile.lean:20), but `RouteFragments.physicalizeOne` still splits; a programmatic `relu(maxreduce)` would become two statements whose intermediate is tropical and whose consumer is real. Any A8 rejection must run BEFORE that split, i.e. on the original statement (LoweringTest AGG1/AGG2, test/DSL/Pipeline/LoweringTest.lean:163-166, depends on this) |
| Plan/Compile.lean:207-210 `checkAggOp` | admits all three | stays (admits) |
| Plan/Compile.lean:349-361 (`capabilityPreflight` `isPredicateName`, rejects predicate scatter dest) | decl scan | unchanged |
| Plan/Compile.lean:655-658 `algebraForAgg`, :664-667 `algebraForAggF32`, :693-697 `algebraForDest destDtype agg` | map `agg` -> algebra, bool override by destination dtype | `algebraForDest storage alg` (A5). 8 call sites: :775 (default inside `residualizeAssignment`, overwritten later), :1098/:1111 (scan base), :1206/:1213 (scan step), :1588/:1592/:1595 (top-level scatter + guard `scatterAggOrFail` :545-547), :1641/:1655, :1672, :1690 (plain identity / pointwise / axiswise) |
| Plan/Signature.lean:62-69 `dtypeOfDecl` | destination dtype from decl (`.predicate` -> bool, f32/f64 from storage) | the sort (maxPlus/minPlus) is NOT representable in `ScalarDType` (Plan/Types.lean:26-28: `f64 | f32 | bool`) or `TensorSignature` (Types.lean:35-38). Two options: (a) extend `ScalarDType` (touches `deriveStorageKind` Check.lean:213-224, `storageConstraintOfDtype`, `dtypeAdmitted*` :168-181, `constMatchesDtype` :151-155, both algebra tables, JAX gates, ~every test signature), or (b) keep `ScalarDType` and carry the sort per `AssignPlan.algebra` + a per-read cast field. (b) is the smaller change; see Q3 |
| Plan/Check.lean:262-270 (`algebraNotAdmitted`) | `algebras.contains a.algebra` by destination dtype | unchanged under (b) |
| Plan/Scan.lean:742,780,788 | state init zero | needs per-state sort |
| Semantics/Source/Carrier.lean:121-133 `selectCarrier`; Admission.lean:910-915, 929-950 | oracle picks ONE carrier per program from statement `(agg, elementType)` keys; mixed aggs refused (`mixedSorts`, Carrier.lean:111) | oracle stays single-sort; production becomes per-tensor-sort. Mixed-sort programs have no oracle (Q7) |

Where `algebraOf` would be computed: `validateScheduled` (ScheduledValidation.lean:155-167) on the COLLECTED program. It
needs, per tensor: any `.predicate` decl -> bool; else the annotation of its writers (`Stmt.agg` Lowering.lean:183-184 for
`.plain`; for scans, base ++ recur statements of that state name); else real. Consumers:

- reference: `evalPlain`/`evalScan` need the map. They currently take `decls`. Callers: `evalPlain` 15 src lines / 17 test
  lines in 5 files, `evalScatter` 23 src / 32 test lines in 8 files, `evalStmtSliceSeeded` 10/11 in 5, `evalScan` 24/16 in 6,
  `combineFor` 13/10 in 5, `evalAssignDtyped` 5/8 in 4 (greps in section 0). Cheaper alternative for S3b-i: keep the
  per-statement entry points on `decls` + the statement's own `agg` (single-writer: the writer annotation IS the sort), and
  thread the map only where it is needed (read casts, scan state init, sort-neutral scan bases).
- checked plan: `prepareEvalPlan` (Compile.lean:1387-1405) already has `declEnv`; add the map next to it.

---

## 3. Cast sites (statement reads a tensor of another sort)

Today there is no sort metadata at reads, so every case is "read the stored Float and apply the statement's algebra":

| Case | Reference today | Checked plan today | Needed |
|---|---|---|---|
| bool (predicate) tensor read in a max statement | `gatherRead` returns the stored 0.0/1.0 (Gather.lean:53), then `×` (Combine.max `mul`, Contract.lean:167). GN4 (test/Eval/Portfolio/GnnScatterTest.lean:50) works because 0*X, 1*X | `checkAssignCore` is dtype-blind for sources: "an f64 source may feed a predicate destination and a bool source may feed a real one" (Check.lean:296-300); worker multiplies | after the flip identity-cast would compute `1+X`. Cast false->0_K, true->1_K (A7) |
| tropical tensor read in a real statement | stored value (e.g. −∞) read raw | same | identity (nothing to do) |
| tropical tensor read in a bool statement | raw Float read, then `min/max` | allowed (dtype-blind) | reject `sortCastUnsupported` (A7). Note: real -> bool is ALSO allowed today and A7's table is silent about it (Q11) |
| max-plus read in a min-plus statement | raw | raw | reject |
| bool read in a real statement | raw 0.0/1.0 | raw | unchanged (same as homomorphism) |

Where the cast lives:

- Reference: per-read value mapping must happen in or around `gather` (Gather.lean:71-76). `gather` has only two production
  callers (Contract.lean:133, Scatter.lean:67) and no test calls it directly (grep). Cleanest: add `(zero one : Float)` parameters
  (callers already hold `unit0`/`unit1`: Contract.lean:88-89, Scatter.lean:63-65). For the bool->tropical cast either (a)
  `gather` consults a per-tensor source-sort map, or (b) `evalPlain`/the scan step builds a cast copy of the bool tensors a
  tropical statement reads (false -> 0_K, true -> 1_K) once per statement. (b) touches two call sites instead of `gather`'s
  signature. UNVERIFIED which is smaller in practice.
- Checked plan: `denseValueAtWith` (Dense.lean:217-218) sees `store` only, not signatures, so a source's bool-ness is not
  available at gather time even though `TensorSignature.dtype = .bool` records it (Check.lean:296-300 reads `srcSig`). So a
  read-cast must be a plan field: `ReadPlan` (Plan/Kernel.lean:35-41: `sourceSlot, map, sourceShape, oobPolicy, unary`) gets a
  `cast : Option ...` filled in by `residualizeAssignment` (Compile.lean:723-776, the three factor arms :744-771). The rejections
  (tropical->bool, maxPlus<->minPlus) cannot be decided by `checkAssignCore` under option (b) of Q2 because the source's sort is
  not in `TensorSignature`; they belong in `validateScheduled` (shared by both entries), which is also where the reference gets
  them for free.
- The cast must apply to `.read` and, for `.unaryFn`, after the unary (the unary is a real primitive, A6/A8).
- Oracle cannot validate any cast: predicate declarations (Source/Adapter.lean:424), Iverson factors (Admission.lean:508) and
  unary factors (Admission.lean:509) are all `.unsupported`, and affine reads are refused (Admission.lean:485-486). Casts,
  Iverson values and OOB padding therefore have NO oracle coverage today and none after S3b unless the oracle admits them.

---

## 4. Scan and scatter specifics

Scan bodies with `maxreduce`/`minreduce` exist and are tested: RC5, RC7, RC10 (test/Eval/Portfolio/RecurrenceTest.lean:85-132),
ScanGen template 5 (test/Eval/PropertyOracle/ScanGen.lean:157-175, `agg := if useMax then .max else .min` on the recurrence,
unannotated base `M[j,0] := X0[j]`), ScanTest "Shape 1" (test/Eval/ScanTest.lean:1064-1135).

How scan statements pick algebras:
- Reference: base and recurrence statements both go through `evalAssignDtypedSeeded` (Scan.lean:62) -> `combineFor decls nm rhs.agg`
  (Contract.lean:252). A scan-local `.scatter` is evaluated as an assign over its source axes (Scan.lean:66-70), then placed.
- Checked: base (Compile.lean:1098, :1111) and step (:1206, :1213) use `algebraForDest destDtype rhs.agg`.
- So the algebra is per statement from its own `agg`. Hard-coded: state allocation = zeros (Scan.lean:318; Plan/Scan.lean:742,
  :780, :788) as in Q1 #9, #20. Everything else reads the algebra.

Is a tropical scan-local scatter reachable? Yes in the reference: ScanTest.lean:1103-1117 evaluates a scan-local `.scatter`
with `agg := .max` and expects `#[3, 7]` ("ACCEPT: the SCAN-LOCAL max-reduce scatter (the checked path accepts it ...)").
In the checked plan a scan-local scatter is a scan statement (`scanPartsOrFail`, Compile.lean:459) compiled through the same
`algebraForDest` call sites, so also reachable. The oracle refuses it (Admission.lean:910-915, `scatterPolicy`).
Write semantics are overwrite/skip in the reference (Scan.lean:102-117, doc at :91-100) and overwrite in the checked plan
(`commitWrite`, Plan/Scan.lean:680-689). S3b-i changes only the contraction algebra of those statements and the
state init; parked F3 (reference overwrites rather than ⊕-sums on a collision) is unchanged. The checked scan path admits only
injective in-range placements (Scan.lean:96-100 comment: "audited, not proved").

Top-level scatter, what must change to accept max/min with 0_K fill:
1. Reference `evalScatter` (Eval/Scatter.lean): init `out` with `c.unit0` instead of `0.0` (:58); fold collisions with
   `c.combine` instead of `if boolDest then Max.max else +` (:77); drop `boolDest` (:57). With `c` from the destination's
   sort. This also fixes F4 (reference sums from 0, checked maxes from ∓∞): after the change both start from 0_K and fold
   with ⊕. Note `evalScatter`'s `c` is selected from `rhs.agg` (:54) and is correct only while destination sort == statement
   annotation (true for single-writer).
2. Reference guard: delete `checkScatterAgg` (Eval/Eval.lean:32-35) and its call (:57).
3. Checked worker: nothing (Dense.lean:369-392 already uses `reduceId`/`reduceOp`).
4. Checked guard: delete `scatterAggOrFail` (Compile.lean:545-547) and its call (:1595). `PlanError`/`CapabilityError.scatterOptsNotAdmitted`
   (Plan/Error.lean:282-296) becomes producer-less.
5. Tests pinned to the refusal: ScanTest.lean:1064-1112 (Shape 1 REJECT donors), CompileTest.lean:1288-1308, Oracle side
   `SortedDifferential.confirmsSorted` `tropicalScatterFill` arm matches `scatterFillNotIdentity` / `scatterOptsNotAdmitted "...: fill"`
   (SortedDifferential.lean:218-228).
6. Doc comments that state the opposite: Dense.lean:353-361, Eval.lean:23-31, Scatter.lean:11-19, Kernel.lean:167-168.

Empty-fibre cells: after S3b a tropical scatter leaves 0_K = ∓∞ in unwritten cells (Dense.lean:384 already does this for raw plans).

---

## 5. Plan layer and proofs

| Where | What it assumes | Kind | Action |
|---|---|---|---|
| Semantics/Types.lean:50-54 (`ScalarOps`: `zero one add mul`, no laws) and every `ops` argument in Semantics/*.lean, Semantics/Plan/*.lean (grep) | nothing about `×` over max | statement-level generic | none |
| Semantics/Completeness.lean:94-100 (`foldValues_some_map_sum`, `zero = 0`, `add = (+)`) and `reduce_sum` | additive laws for the selected sort only (comment at :101-102) | proof | none |
| Semantics/Collection.lean (pushforward over `AddCommMonoid K`) | commutative monoid ⊕ only | proof | none |
| Semantics/Plan/Fusion.lean, FusionCorrectness.lean, Faults.lean, Plan/AGENTS.md | no hit for `mul_add|add_mul|CommSemiring|distribut|factorOp|tropical` (greps of section 0) | none found | none (UNVERIFIED beyond grep: I did not read these files line by line) |
| Algebra/Target.lean:15, Algebra/Algebra.lean:13 `[CommSemiring R]`; Algebra/Construct.lean `semiring_choice_split` | abstract `R`; bool case discussed | proof, generic | none |
| Plan/Dense.lean:126-128, Check.lean:72-74, Compile.lean:652-654, Types.lean:76-83, Check.lean:41-43 | text: "pad flows through `factorOp` (mul)", "max-product", "mirrors Combine.max" | comments | rewrite |
| Plan/Dense.lean:353-361 | text: tropical scatter refused, divergences F4 | comment | rewrite |
| Plan/Check.lean:44-52, 110-118 | `factorOp := .mul` for tropical | runtime constants | the change itself |
| test/Eval/Plan/KernelCheckTest.lean:69-70 (`{admittedAlgebra with factorOp := .add}` -> `algebraNotAdmitted`) | real algebra with `.add` factor stays unadmitted | runtime test | unchanged (real algebra is untouched; the new tropical algebra is a different record) |
| Plan/Executable.lean:259-260 | JAX admits only the real algebra | runtime check | unchanged |

No proof I found assumes `factorOp = .mul` or distributivity of `×` over max/min. The "R regression net / fusion /
retirement / Faults" the memory index mentions live in `LeanNCD/Semantics/Plan/` (an abstract machine), not in `Eval/Plan/`;
`Eval/Plan/` has no fusion/retirement code (file list of Eval/Plan: Adapter, Block, Check, Compile, Coordinates, Dense, Dense32,
Error, EvalPlan, Executable, Graph, Kernel, Nonlin, Prepared, RawStep, Scan, Signature, Types).

---

## 6. Route / bridge / JAX / Python

- `BrOp.maxreduce` doc: "tropical max contraction (×, max, −∞)" and `minreduce` "(×, min, +∞)" (DSL/Target.lean:56, :64).
  Its only producer is `Lowering.lean:472-474`; the only consumers are `toString` (Target.lean:74-75) and the numeric codes in
  Bridge/AcsetCodec.lean:70,78 (encode) and :94,102 (decode). `Bridge/Realize.lean:54` carries `b.op.toString` as a string.
  No Lean code in `Bridge/`, `Seam/` or `DSL/Pipeline/Route*.lean` interprets the label's semantics (grep). So the route/bridge change
  is documentation only. The comment at Target.lean:52 says "the string the Python execution layer dispatches on";
  I found no Python or TS file in this repo containing `maxreduce`/`minreduce` (grep over *.py, *.ts). Other repos: UNVERIFIED.
- JAX (`experiments/jax_bridge/`): only real sum-product is implemented. `evalplan_affine_runtime.py:112-131` hard-codes `acc * stacked[k]`
  for factors and `acc + row[k]` from 0.0 for reduction. The Lean gate rejects tropical (Executable.lean:259-260; README.md:217
  "tropical max/min ... forbidden (`unsupportedAlgebra`)"; Executable tests pin it at test/Eval/Plan/ExecutableTest.lean:658-670,
  :1260-1263, :1869-1873). Nothing maps `ContractionAlgebra` fields to JAX ops. S3b does not change JAX; the gate compares against
  `jaxRealCarrier` (Executable.lean:220), so the changed tropical records stay rejected automatically.
- Docs in that directory mention tropical in README.md:217, :272.

---

## 7. Oracle and differential

The oracle is already `⊗ = +` (Carrier.lean:48-86: `MinPlus = Tropical (WithTop ℚ)`, `MaxPlus = Tropical (WithBot ℚ)ᵒᵈ`,
Mathlib `CommSemiring`), selected per program by `selectCarrier` (Carrier.lean:121-133). It admits only: no predicates
(Adapter.lean:424), no Iverson (Admission.lean:508), no unary (:509), no affine reads (:485-486), no nonlinearity (:663-664, :883-884),
one sort per program (`mixedSorts`), and refuses tropical scatter (`scatterPolicy`, Admission.lean:910-915).

Conditions that exist only to explain production's divergence:

| Item | Where | After S3b-i |
|---|---|---|
| `StructuralCondition.tropicalMultiFactor` | NumericalProfile.lean:30-32 (doc "production multiplies"); detect SortedDifferential.lean:187-190; confirm :212-217; ignored in the real harness Differential.lean:254-255 | obsolete: production = oracle on multi-factor. Delete, plus tests (test/Semantics/SourceSortedDifferentialTest.lean:182-196, :228-296) |
| `StructuralCondition.tropicalScatterFill` | NumericalProfile.lean:33-37; detect SortedDifferential.lean:184-186 (`Differential.nonBareWrite`, Differential.lean:186); confirm :218-228 | obsolete once the two refusals go (Q4). Affine tropical writes become `fourLegParity` candidates |
| `unexplainedAgree` / `othersAgree` masking | SortedDifferential.lean:196-205, :266-279 | only existed to localise multi-factor mismatches; delete with `tropicalMultiFactor` |
| `confirmsSorted`, `detectSortedConditions`, `knownContractDifference` classification arm | SortedDifferential.lean:175-191, :210-229, :288-290 | whole known-difference apparatus for sorted programs is empty; `SortedClassification.knownContractDifference` may become unused for sorted runs (the real harness's own conditions are separate, Differential.lean:250-255) |
| `scatterPolicy` refusal | Admission.lean:910-915; Adapter.lean:33-34 | remove once tropical scatter accepted by the oracle: `fill : Int` cannot be ±∞ but S3a deleted `fill`, so the stated reason ("`fill : Int` cannot be the carrier zero") is stale; the oracle already yields ±inf in unwritten cells (NumericalProfile.lean:34-37) |
| zero-factor `zeroV` row | test/Semantics/SourceSortedDifferentialTest.lean:244-266: asserts `nativeDiscrepancy` because empty product is `0` for the oracle and `1.0` for production | flips to parity once `factorId` = 0.0; rewrite expectation to `fourLegParity`/`parity` |
| `scatterFillNotIdentity` match | SortedDifferential.lean:222 | goes with the constructor |
| Real-harness conditions (`multiWriterScatter`, `scatterExtentOverridesDeclared`, `usedDType`) | NumericalProfile.lean:24-30 | unrelated |

What replaces them: tropical programs expected to be `fourLegParity` (core = oracle = legacy = checked, bit-compared
`compareBindings`, SortedDifferential.lean:124-135). Note the tropical profile only needs "finite integers + ±inf classes"
(SortedDifferential.lean:38-45), unchanged. The oracle cannot cover bool->tropical casts, Iverson factors, OOB padding or
mixed-sort programs (see Q3), so those need production-only tests (legacy-vs-checked `planAgrees`, hand expectations).
Also verify `test/Semantics/SourceDifferentialCorpusTest.lean` and `SourceOracleCarrierTest.lean:168` (it rewrites `agg := .max` on
statements) for tropical expectations: UNVERIFIED, not read.

---

## 8. Tests whose expected values change

Coarse per-file line counts of the section-0 regex (109 lines, 33 files; full list in scratchpad `grep8.txt`):
SourceSortedDifferentialTest 10, RecurrenceTest 10, ExecutableTest 10, CompileTest 9, MaxReduceTest 9, ScanTest 8, TropicalTest 7,
DifferentialTest 5, CollectTest 5, Adapter32Test 4, KernelDenseTest 3, KernelDense32Test 3, LoweringTest 3, ScatterTest 2, ConvPoolTest 2,
CollectEvalTest 2, and 1 each in SourceSortedAuditTest, SourceRawCorrespondenceTest, SourceOracleCarrierTest, SourceAdmissionAcceptanceTest,
ScanGen, RejectTest, KnownGapTest, GnnScatterTest, ClassicalMLTest, ScatterDenseTest, ScatterDense32Test, ScatterCheckTest, ContractTest,
EvalExamplesTest, StructuralTest, RouteFragmentDiagnosticTest, RouteFragmentCorpusTest.

### 8a. VALUE changes (multi-factor, bool cast, OOB, scatter fill, empty/unwritten)

| Test | Why | In A10? |
|---|---|---|
| test/Eval/Portfolio/TropicalTest.lean:21 TR3, :35 TR7 (TR5 :39 becomes expressible) | multi-factor | yes |
| test/Eval/Portfolio/RecurrenceTest.lean:85 RC5, :105 RC7, :129 RC10 (G[0,1] 0 -> −∞) | multi-factor; unwritten cell init | yes |
| test/Eval/PropertyOracle/ScanGen.lean:157-175 template 5 (and ScanOracle / ScanUnroll, see 8f) | multi-factor in scan | yes (ScanGen only) |
| test/Eval/Portfolio/GnnScatterTest.lean:50 GN4 | bool->max-plus cast; unchanged value only under the homomorphism | yes |
| test/Eval/Plan/KernelDenseTest.lean:60-65 (`maxContractPlan`, `minContractPlan` on `A[i]·B[j]`: [30,300,..] / [10,100,..] become A+3 / A+1), :71-75 (all-negative B: [-10,...] becomes A+(-1)), :77-103 (`oobMaxPlan` pinned to [0.0, 0.0] as "the plan's central subtlety": padded 0.0 wins the max; after S3b the pad is −∞ so the result is max of valid cells, [-1,-3]) | factor op, OOB pad | NO |
| test/Eval/Plan/KernelDense32Test.lean:218-220 (`F32Max/Min` contract), :247-258 (`oobMaxPlan` f32) | same, f32 | NO |
| test/Eval/Plan/ScatterDenseTest.lean:248, ScatterDense32Test.lean:111, ScatterCheckTest.lean:102 (raw tropical `upScatter` plans) | scatter with tropical algebra; values depend on whether the compute half multiplies | NO (check whether single-factor: UNVERIFIED, not read) |

### 8b. Value changes only through f32 constants

test/Eval/Plan/Adapter32Test.lean:381-391 (single-factor max/min, `tensor f32`): values unchanged, plan carries new `factorId` bits.
test/Eval/Plan/DifferentialTest.lean:349-362 (`planAgrees` on single-factor max/min, f64): unchanged values. Both listed in A10. Any golden check
of the `AssignPlan.algebra` literal (ExecutableTest.lean:658-670 pins `unsupportedAlgebra 0 admittedAlgebraMax` by reference to the constant, so it follows the redefinition).

### 8c. Become rejections

nonlin != identity with `agg := .max` (A8): LoweringTest.lean:163-166, RouteFragmentCorpusTest.lean:602-606, CompileTest.lean:1497 (`pointwise .relu`+`.max`; the test
starts earlier, A10 says :1434), StructuralTest.lean:493, SourceRawCorrespondenceTest.lean:93 (these last two use an empty body, so check what error they expect).
Not read in detail: UNVERIFIED which constructor each expects today.

### 8d. Become acceptances (REFUSAL pins that flip) -- none of these are in A10

- test/Eval/ScanTest.lean:1064-1112: `scatterFillNotIdentity "Out" .max/.min` rejections (3 cases incl. the two-term joined case).
- test/Eval/Plan/CompileTest.lean:1288-1308: `scatterOptsNotAdmitted "Y: fill"` for `.max` and `.min` (f32 programs).
- test/Semantics/SourceSortedDifferentialTest.lean:164-262: scatterFill known-difference rows (also the `fills` confirmer tests :213-228).
- test/Eval/Plan/DifferentialTest.lean:115 (classifier string for `scatterOptsNotAdmitted`).
- test/Eval/ScatterTest.lean:57-72 "4g regression": direct `evalScatter` with `.max` over two single-factor terms, expected [10,5,2]: value
  preserved (single factors) but its comment ("evalScatter ... hardcodes real sum") is stale and fill/fold change.

### 8e. Unaffected (single factor, no Iverson/OOB/scatter/unwritten cell)

EvalExamplesTest.lean:370, ConvPoolTest.lean:44 (CV5, no OOB: X=[1,3,2,5], p in {0,1}), ClassicalMLTest.lean:71 (CM3 `maxreduce(Q[s,a])`), TropicalTest.lean:28 (TR6),
SourceAdmissionAcceptanceTest.lean:196, ScanTest.lean:1120-1124 (plain max over a contraction axis), RouteFragmentDiagnosticTest.lean:127 (route label only),
RejectTest.lean:23 (not read; likely a rejection of another kind, UNVERIFIED), KnownGapTest.lean:30 (comment), ContractTest.lean:182 (classifier),
CollectTest.lean:125-129, :190-202 and CollectEvalTest.lean:157-165 (J4/C6/C6b/C6c): multi-writer max refusals, UNCHANGED in S3b-i, flip in S3b-ii.
test/DSL/MaxReduceTest.lean: see correction below.

### 8f. Corrections to the decision note A10, and extra work it does not list

1. **MaxReduceTest.lean:90-101 does NOT change value.** The three evaluation blocks call `evalAssignWith (· * ·) floatMax negInf 1.0 ...`
   directly (MaxReduceTest.lean:67, :84, :105), passing their own `mul`, so the test never reads `Combine.max`. It keeps passing as long as `evalAssignWith`
   keeps the `(mul combine unit0 unit1)` parameters; its comments (":90 Multi-factor max: A·B") describe max-times, which it still computes. Remove it from A10.
2. A10 omits the plan-level fixtures in 8a (KernelDenseTest, KernelDense32Test, probably the three Scatter*Test files) and the refusal pins in 8d.
3. **`DenseTensor.approxEq` cannot compare infinities.** `Float.abs (x - y) < ε` (LeanNCD/Eval/Tensor.lean:89): for x = y = −∞ the difference is NaN and
   the test is false. `evalEqB` (test/Eval/Portfolio/Harness.lean:87-93) uses it. RC10's new expected cell G[0,1] = −∞ and any tropical test with an
   empty reduction cannot be written with `evalEqB` as is. Needs a bits- or inf-aware compare in the harness.
4. **ScanUnroll (test oracle, 1299 lines) hard-codes real zeros.** test/Eval/PropertyOracle/ScanUnroll.lean:366-368, :750-755 (zero leaf = empty-term assign, i.e. 0),
   :766-780 (merge statements sum disjoint zero-filled base contributions, `agg` default `.sum`), header :37-41 ("aggregation carried through unchanged ... tropical
   aggregation still unrollable"). With tropical state sorts the zero leaf and the merge must use 0_K / the state's ⊕. ScanOracle (test/Eval/PropertyOracle/ScanOracle.lean:88-94)
   and ScanGen template 5 depend on it. Template 5 covers every cell (base fills l=0, steps fill l>=1), so it does not exercise the unwritten-cell path; RC10 does.
5. Count of `.scatterFillNotIdentity`/`scatterOptsNotAdmitted` consumers: SortedDifferential.lean:222,226; DifferentialTest.lean:115; Eval/Error.lean:356-359; Plan/Error.lean:282-296.

---

## 9. Docs to update (grep of section 0, count of matching lines)

Live / intent-layer docs that state or imply (max, ×) or "tropical" divergence:
- `leanncd/LeanNCD/Semantics/AGENTS.md` lines 116-138 (tropical carriers, "Production multiplies where tropical ⊗ adds", `tropicalMultiFactor`, `tropicalScatterFill`, `scatterPolicy`).
- `leanncd/LeanNCD/Eval/AGENTS.md:47` (dtype->semiring dispatch), :60 (scatter `Combine` selected by `rhs.agg`), :16.
- `leanncd/LeanNCD/Eval/Plan/AGENTS.md:39` (bool tag), :46 and :54 (`scatterAggOrFail`, JAX).
- `leanncd/AGENTS.md:231` (JAX rejects tropical; unchanged but wording), :235.
- `leanncd/experiments/jax_bridge/README.md:217, :272` (tropical forbidden; unchanged).
- Source comments quoted in 1, 4, 5: Dense.lean:126-128, :353-361; Compile.lean:200-210, :652-654; Check.lean:41-43, :48-49, :72-74, :108-109; Types.lean:58-63, :76-83; Eval.lean:23-31; Scatter.lean:11-19, :49-56; Contract.lean:162-171, :233-239; Target.lean:56, :64; Plan/Error.lean:282-296; Kernel.lean:167-168; Collect.lean:117-120.
- `leanncd/docs/test_portfolio.md` (15 hits; §11 "Tropical / max-times", line 84-88, 121, 204).
- `papers/max_min_aggregation.md` (22), `papers/leanncd.md` (4), `papers/boolean_predicate_output_evalplan.md` (7), `papers/backend_missing_functionality.md` (7), `papers/scatter_affine_lhs_writes.md` (4), `papers/predicate_boolean_backend_parity.md` (4), `papers/wave_f_scanplan_proposal.md` (4), `papers/wave_f_capability_manifest.md` (3),
  `papers/semantics/lean_executable_semantics_path_part_4.md` (10), `.../tensor_logic_boundary_policies.md` (7), `.../tensor_logic_semantics_part_i.md` (4), `.../tensor_logic_semantic_gap_audit.md` (4), `.../additive_production_decision_note.md` (27: mark S3b rows, correct A10 per 8f).
- Historical records (additive_s2b_plan/record/reviews/ledger/artifacts, oracle_extension_s2_design, s2a/s3a/b6 records): leave as records, add a pointer from the decision note.
- Not in the `AGENTS.md` hierarchy at repo root: root CLAUDE.md "Global Pitfalls" has no tropical entry (grep of CLAUDE.md, */AGENTS.md returned nothing).

---

## 10. Proposed task breakdown

Assumes the decisions in the brief. Sizes are "files touched / fixtures". The ~60-turn / ~250k-context cap is flagged **RISK** where I expect a breach based on S3a's record (T1 81 turns, T3b-2 102 turns; papers/semantics/additive_s3a_record.md:56-62).

**Prototype first (before any task):** one scratch file importing only rebuilt modules (mutant-probe pitfall in memory) that evaluates RC5, GN4, KernelDense oobMaxPlan and an Iverson/OOB max statement under the new records on BOTH backends, to confirm the cast design (reference cast copy vs gather map; plan `ReadPlan.cast`). Cost: ~1 dispatch.

S3b-i, ordered:

| # | Task | Files | Fixtures | Risk |
|---|---|---|---|---|
| T0 | Decision gate: resolve the Q11 user questions (real->bool, NaN op scope, sort-neutral pad) | none | none | |
| T1 | Shared definitions: `Algebra` inductive (DSL/Ast.lean), `Combine.maxPlus/minPlus` from one `Combine.tropical (⊕, 0_K)`, NaN-propagating `maxNaN/minNaN`; plan side one `admittedAlgebraTropical dir` for f64 and one for f32 replacing `admittedAlgebraMax/Min/F32Max/F32Min`; update `ScalarKernelOps.binOp` for `.max/.min` in both carriers | Contract.lean, Check.lean, Dense.lean, Compile.lean (algebraForAgg*) ~4 | new: NaN-order fixtures both carriers, f32 bit pins, duality twin helper | moderate; NaN op decision |
| T2 | Constants and padding in both backends: `gather` takes (zero, one) and uses them for bare-read pad and Iverson (unary keeps 0.0); Dense worker decodes `reduceId`/`factorId` for bare-read pad and Iverson; delete the doc comments that assert the opposite | Gather.lean, Contract.lean, Scatter.lean (arg only), Dense.lean | ~8 (OOB max, OOB min, Iverson max/min, unary-under-max, empty product, empty sum, zero-extent reduction) both backends + f32 | moderate |
| T3 | Sort derivation and checks: `algebras` field in `CheckedScheduledProgram`, writer agreement `writerAlgebraMismatch` with sort-neutral exemption, `sortCastUnsupported`, tropical+nonlin rejection (before the split, Q2), new `CompileError` ctors + render | ScheduledValidation.lean, Structural.lean (`checkScheduledDtypes`), Ast/Error files, ToExpr/AcsetCodec if `CompileError` is serialised (UNVERIFIED) | ~12 rejection + accept-neighbour fixtures | **RISK** (new error constructors propagate to exhaustive matches; S3a's T3b-2 hit 14 files from arity edits) |
| T4 | Casts: reference (cast copy or gather map), `ReadPlan.cast` + `residualizeAssignment` + `denseValueAtWith` | Eval.lean, Scan.lean, Gather.lean, Kernel.lean, Compile.lean, Dense.lean, Check.lean (field checks) | ~8: GN4 both backends, bool->min-plus, bool->real unchanged, in a scan, f32 | **RISK**; adding a field to `ReadPlan` touches every raw-plan literal in tests (`ReadPlan` literals: KernelDenseTest etc., UNVERIFIED count) |
| T5 | Scan state init at 0_K: reference `Scan.lean:318` and checked `Plan/Scan.lean:742,780,788` + per-state sort in the scan plan | Scan.lean x2, Compile.lean, Plan/Kernel or Scan structs | ~6 (RC10-shaped 2-D tropical, max and min, f32, sum scan unchanged) | moderate; needs `ScanStatePlan` read first |
| T6 | Top-level tropical scatter accepted: `evalScatter` init and fold from `Combine`; delete `checkScatterAgg`, `scatterAggOrFail`; keep scan-local overwrite (F3 stays parked) | Scatter.lean, Eval.lean, Compile.lean, Error files | flip ~8 refusal pins (8d) to value tests; F4 fixture: direct `evalScatter` vs raw plan with contracted source axis | moderate |
| T7 | Oracle/differential: delete `tropicalMultiFactor`, `tropicalScatterFill`, `unexplainedAgree`, scatterPolicy refusal; sorted corpus classified `fourLegParity`; keep `compareSortedSource` | Semantics/Source x4-5 | rewrite SourceSortedDifferentialTest (~35 `#guard`s) | **RISK** (likely 2 dispatches) |
| T8 | Test migration with negation-duality twins: for each max-plus fixture add the min-plus twin by `min-plus(x) = -max-plus(-x)` (property checked in a small generator); migrate 8a values; fix `approxEq`/`evalEqB` for infinities; update ScanUnroll zero leaf/merge for tropical states; update ScanGen template 5 | ~15 test files + Harness + ScanUnroll | ~30 | **RISK, split**: (a) portfolio/DSL tests, (b) Plan kernel fixtures, (c) ScanUnroll/ScanGen/ScanOracle |
| T9 | Docs: AGENTS.md nodes (inside the plan, per memory "use-intent-layer-in-planning"), decision note (A10 corrections), `max_min_aggregation.md`, Target.lean doc | ~10 | none | low |

Process weight: this is Full path (shared semantics change across two backends, f32, oracle, ~40 files), not Direct; matches the B6 record ("Full path, needs a design note first", additive_b6_record.md:40).

S3b-ii (tropical multi-writer collection, writer-agreement A4), from Collect.lean:
- Delete the `multiWriterAlgebra` throw (Collect.lean:99-101) and replace it with writer agreement: all annotated writers equal; sort-neutral writer exemption (one term, one read/unaryFn factor, no contracted axis).
- `collectorStmt` (Collect.lean:115-121): carry the agreed `agg` instead of `.sum` (the file's own comment at :117-120 says exactly this). The collector reads `T#k` (private tensors, each a tropical-sorted single writer) and combines them with ⊕ = max/min, over `termAxisUIDs` empty (identity reads).
- Private names `T#k` need sorts in `algebras` (they are cloned decls, ScheduledValidation.lean:151-153): derived from their writer's annotation; an unannotated sort-neutral writer's `T#k` must adopt T's sort.
- Note `checkWriterGroup` still rejects any scatter writer (`multiWriterScatter`, Collect.lean:79-82): out of scope (B5).
- Tests to flip: CollectTest.lean:125-135 (C6), :190-202 (C6b, C6c), CollectEvalTest.lean:157-165 (J4), SortedDifferential has no multi-writer corpus (UNVERIFIED).
- New fixtures: two `maxreduce` writers, max+min mismatch -> `writerAlgebraMismatch`, sum+max mismatch -> same, sort-neutral + maxreduce accepted and reads as T's sort, oracle parity if the oracle admits multi-writer sorted programs (it does take the max per s2b record:168 — papers/semantics/additive_s2b_record.md:168-170, UNVERIFIED beyond that line).
- Size: ~5 source files, ~15 fixtures, one dispatch group; low risk once T3 exists.

---

## 11. Surprises, and items needing a user decision

Contradictions with the decision note / records:

1. **A10 is wrong about MaxReduceTest:90-101** (it passes `(· * ·)` itself, MaxReduceTest.lean:67,84,105; never reads `Combine.max`). A10 also omits the plan-level fixtures KernelDenseTest/KernelDense32Test (and probably ScatterDense*/ScatterCheckTest) and all the refusal pins that flip (8d).
2. **KernelDenseTest.lean:77-103 documents "padded 0.0 wins the max" as the plan's central, deliberate subtlety**, and Dense.lean:126-128 / Check.lean:72-74 / Compile.lean:652-654 state the same as design. S3b reverses a documented intentional decision; reviewers will see it as a regression unless the docs/tests say so explicitly.
3. **A6's pointer "Dense.lean:126-138 uses `reduceId`" is not what the code does**: it uses `ops.zero` (Dense.lean:133, :137, :138), the carrier's real 0. `reduceId` is decoded at :223 but is not used for pad. The change is therefore a real edit in `gatherFactorWith`, which currently has no access to the algebra (it takes `ops`, `store`, `f`, `iter`, Dense.lean:129-130).
4. **`DenseTensor.approxEq` is false for equal infinities** (Tensor.lean:89), so the harness cannot state RC10's new −∞ cell or any empty-reduction expectation.
5. **ScanUnroll (the independent scan oracle) hard-codes real zeros and `.sum` merge** (ScanUnroll.lean:366-368, :750-780). It is not listed in A10 or the S2b/S3a records I read; it needs rework for tropical states.
6. **The checked plan has no per-tensor sort representation**: `ScalarDType` is `f64|f32|bool` (Plan/Types.lean:26-28) and the sort lives only in `AssignPlan.algebra`. The note's "checked plan adds a read-cast field" (A7) is the right minimal move, but the tropical->bool / maxPlus<->minPlus rejections then cannot live in `checkAssignCore`; they must live in `validateScheduled`.
7. **Scan state init is a new site not named in A1-A10** (Scan.lean:318; Plan/Scan.lean:742,780,788); the note only mentions its effect on RC10 in A10.
8. **The reference evaluator's per-statement entry points take `decls`, not the checked program** (Eval.lean:178,181 pass `sched.decls`), so threading `algebraOf` has real churn (counts in Q2). For S3b-i a per-statement `agg` suffices except scan states and casts.
9. `scatterFillNotIdentity`/`scatterOptsNotAdmitted` are kept alive only because the sorted differential matches them (SortedDifferential.lean:222-226); delete them together with the conditions.
10. The Semantics/Plan fusion/retirement/Faults layer is generic in `ScalarOps` and does not need changes (greps only; I did not read those files line by line).

Needs a user decision (not a judgment call):

- **real -> bool read.** The brief's A7 table covers bool->real, bool->tropical, tropical->real, and rejects tropical->bool and maxPlus<->minPlus, but is silent on real->bool. Today it is accepted in both backends (Check.lean:296-300). Reject, or keep as identity?
- **NaN-propagating `ScalarBinOp.max/min` is shared with the bool algebra** (Check.lean:67-69 uses `.min/.max`; Dense.lean:83-84, 112-113). Change both, or give tropical distinct ops? Also whether this counts as a semantic-version change (Plan/Error.lean:78 mentions the notion; I found no version constant).
- **Pad value for a sort-neutral writer** (e.g. the scan base `M[j,0] := X0[j]` of a max-plus state): pad with the destination tensor's 0_K (−∞) or with real 0? A6 says "0_K of the sort being computed"; for a sort-neutral writer that adopts T's sort this means the statement algebra must come from `algebraOf T`, not from its own `agg`, which forces the map into the reference per-statement path after all.
- **Rename/retain `OutOfBoundsPolicy.zeroPad`** (Plan/Types.lean:49-52, required by Check.lean:317, appears in every raw-plan test literal).
- **Mixed-sort programs have no oracle** (Carrier.lean:111 `mixedSorts`): accept production-only coverage for them, or extend the oracle to per-tensor sorts as a follow-up?
- **Scan-local overwrite vs ⊕ (parked F3)**: unchanged by S3b-i; confirm it stays parked.

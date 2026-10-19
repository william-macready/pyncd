# Additive production semantics: decision note

**Summary.** Production Lean (DSL → Pipeline → reference `Eval` / checked `Eval.Plan` / `route`) moves to the
spec's additive collection (§9, §19, §20). Decisions already made are marked **FIXED**. **PROPOSED** items
need user approval, and **OPEN** items need a user decision. The core proposals are as follows. A tensor's
algebra stays a *destination* property, derived from `predicate` or from `maxreduce`/`minreduce` used as
annotations that all writers must agree on, so no new declaration syntax is needed. The one `collectDefinitions`
desugar is the identity on single-writer schedules. Slice 1 admits only real-sum and predicate plain
bare-slot writers, and fails loud on every other multi-writer set, all of which are silently overwritten
today. Boolean→tropical reads use the semiring homomorphism (all four open questions were decided on 2026-10-14; see §F). Out-of-range writes become a static error in
the checked plan and a dynamic error in the reference evaluator, and both reject the same programs. Probes
cited as "probe" were run on 2026-10-14 (scratch `chk4.lean`, `lake env lean`, primary checkout).

Evidence from the probes (behaviour on 2026-10-14, before slice 1; slice 1 landed the real-sum plain
bare-slot collection and the supplied-input rejection, see "Landed as" under §C):

| Program | Today | Spec |
| --- | --- | --- |
| `predicate R(i); R[i]:=A[i]; R[i]:=B[i]`, A=[1,0], B=[0,1] | R=[0,1] (overwrite) | [1,1] |
| `S[2*i]:=X[i]; S[2*i+1]:=Y[i]` | S=[0,10,0,20] (X lost) | [1,10,2,20] |
| `predicate edge; H[i,f]:=maxreduce(edge[i,j]·X[j,f])`, X<0 | row 1 = [−0,−0] | [−3,−4] |
| `C[i]:=maxreduce(X[j]·[j≤i])`, X=[−1,−2,−3] | [−0,−0,−1] | [−1,−1,−1] |
| input `T` supplied and `T[i]:=A[i]` | supplied T silently replaced | In ∩ Def = ∅ (§13.6) |
| Lean `Float`: `max(nan,1)`, `max(1,nan)`, `min(nan,1)`, `min(1,nan)`; `−∞+∞`; `−∞·0` | NaN, 1, 1, NaN; NaN; NaN | — |

## A. Sorts

**A1. FIXED.** Overwrite is removed. Collection everywhere uses ⊕ of the destination's sort, and the empty
fiber is 0_K. Tropical sorts are max-plus and min-plus. False Iverson values and out-of-bounds read padding
are 0_K of the sort being computed. Real↔tropical identity casts are implicit.

**A2. Sort table (exact carriers).**

| Sort | Carrier | ⊕ | ⊗ | 0_K | 1_K | Laws |
| --- | --- | --- | --- | --- | --- | --- |
| real | ℝ | + | × | 0 | 1 | commutative semiring |
| bool | 𝔹 | ∨ | ∧ | false | true | commutative semiring, ⊕ idempotent |
| max-plus | ℝ∪{−∞} | max | + | −∞ | 0 | commutative semiring, ⊕ idempotent |
| min-plus | ℝ∪{+∞} | min | + | +∞ | 0 | commutative semiring, ⊕ idempotent |

What the spec needs (§2.3, L494-530) is narrower. Parts III–IV need only the commutative monoid (K,⊕,0_K)
on each defined tensor's sort. §15.2 and §17.1–17.3 add the coherence condition, and §17.4–17.6 need the
full semiring.

Today's `Combine.max`/`.min` (Contract.lean:167-171) and `admittedAlgebraMax`/`Min` (Check.lean:44-52) use
(max, ×, −∞, 1). That is a valid collection monoid but not a semiring: −∞ is not absorbing (−∞·0 = NaN, see
probe), and × does not distribute over max for negative factors. The switch is what makes §17 apply. Also,
max and min are exact on non-NaN IEEE values, so tropical collection is bit-exact in any order. Real
collection is not.

**A3. PROPOSED: representation.**
- Add `inductive Algebra | real | bool | maxPlus | minPlus` in `DSL/Ast.lean`.
- A tensor's sort is `Algebra × storage`. Storage is unchanged: `StorageKind` comes from the declaration
  (Ast.lean:291-311). `bool` stays a tag over the schedule's real carrier (Plan/Types.lean:15-28).
- **No new declaration syntax.** `validateScheduled` derives `algebraOf : String → Algebra` once:
  - a `predicate` declaration gives `bool`;
  - otherwise the writers' annotation gives `maxPlus` (`maxreduce`) or `minPlus` (`minreduce`);
  - otherwise `real`;
  - a never-written input is `bool` if declared `predicate`, else `real`. Tropical inputs are not needed,
    because the real→tropical cast is the identity.
- Store the result as `CheckedScheduledProgram.algebras` (a new field; the constructor is private,
  ScheduledValidation.lean:111).

**A4. PROPOSED: what replaces `RHSExpr.agg`.**
- Keep the field and the keywords (Ast.lean:120-142, Syntax.lean:207-212, Elab.lean:237-249). This avoids
  churn across `ToExpr`, `AcsetCodec` and roughly 20 test files.
- Reinterpret the field as an *annotation of the destination's algebra*, not as a per-statement contraction
  operation.
- Agreement rule: every writer of T must carry the same annotation (`writerAlgebraMismatch T` otherwise),
  with one exemption. A **sort-neutral** writer may be unannotated and adopts T's sort. Sort-neutral means
  one term, one `read`/`unaryFn` factor, and no contracted axis, so neither ⊗ nor ⊕ is ever applied.
  - This keeps the scan bases of RC5/RC7/RC10 and ScanGen template 5 valid unedited (`M[j,0] := X0[j]`).
  - It also blocks the footgun where an unannotated `A[i]·B[i]` silently becomes `A[i]+B[i]` because
    another writer said `maxreduce`.
- `predicate` combined with `maxreduce` stays rejected (`predicateAgg`, Structural.lean:980-988).

**A5. PROPOSED: code migration (slice S3).**
- `combineFor decls nm agg` (Contract.lean:189-193) becomes `Combine.of : Algebra → Combine`, with
  `Combine.maxPlus := ⟨(·+·), maxNaN, −∞, 0.0⟩` and `minPlus` likewise. Workers receive the algebra instead
  of re-scanning `decls`.
- `isPredicateDest` (Contract.lean:179-184) and the scatter `boolDest` (Scatter.lean:58) become
  `algebraOf nm == .bool`.
- Checked plan:
  - `algebraForDest destDtype agg` (Compile.lean:736-740) becomes `algebraForDest storage alg`;
  - `admittedAlgebraMax`/`Min` and their F32 twins (Check.lean:44-52, 110-118) become
    `factorOp := .add, factorId := 0.0` (f32 `0x00000000`). `ScalarBinOp` already has `add`
    (Types.lean:84-86), so no semantic-version bump is needed;
  - `admittedAlgebrasFor` keeps its shape (Check.lean:90-93).
- `BrOp.maxreduce`'s documentation, "(×, max, −∞)" (DSL/Target.lean:56), must be updated. The route/bridge
  realization of that label is **inferred** to change meaning as well.

**A6. PROPOSED: constants.**
- There are no scalar literal factors (`Factor` is `read | iverson | unaryFn`, Ast.lean:128-132). Constants
  therefore come only from Iverson values (1_K/0_K), the empty product (1_K) and the empty sum (0_K), all
  in the statement's sort. The `fill` constant is deleted.
- In tropical sorts, `[true]` = 0.0 and `[false]` = ∓∞. The reference does this through `gather`
  (Gather.lean:72). The checked worker does it by decoding `factorId`/`reduceId` instead of
  `ops.one`/`ops.zero` (Dense.lean:235-239).
- Out-of-bounds padding is 0_K of the sort *at the read position*:
  - a bare read is padded with the statement sort's 0_K (Gather.lean:43-53; Dense.lean:126-138 uses
    `reduceId`);
  - a read under a `unaryFn` is padded with 0.0, the real input sort of the primitive. The primitive is
    then applied, and the result is cast.
  - This matches boundary-policies §8.4.3 (L1174, "Const of the selected additive identity").

**A7. PROPOSED: casts.**

| Reads → statement sort | Rule |
| --- | --- |
| real → tropical, tropical → real | identity on values (FIXED) |
| bool → real | false ↦ 0, true ↦ 1 (the same values as today's stored 0/1; **FIXED**, one rule with the next row) |
| bool → tropical | false ↦ 0_K (∓∞), true ↦ 1_K (0.0): the unique semiring homomorphism from bool into the target sort (**FIXED**, Q1 decided 2026-10-14) |
| tropical → bool, max-plus ↔ min-plus | rejected (`sortCastUnsupported`) |

- The cast is "elaborator-inserted" in the spec's sense: a registered primitive.
- Production needs no AST node, because the identity cast is free. Only bool→tropical maps values: the
  reference does it in `gather`, keyed by the source's algebra, and the checked plan adds a read-cast field
  on the factor (**inferred** cost: small).
- Evidence for the homomorphism: GN4 (GnnScatterTest.lean:50) keeps its current expected answer under the
  homomorphism and becomes correct for negative X (see probe). Under an identity cast it would compute 1+X.

**A8. PROPOSED: nonlinearities and unary functions.**
- real: unchanged.
- bool: identity only (existing rule, Structural.lean:985).
- Tropical destinations: `Nonlin.identity` only. `gelu(−∞) = NaN`, and softmax over all-−∞ gives 0/0.
  Surface syntax cannot combine `relu(…)` with `maxreduce(…)` anyway (Syntax.lean:210-211). Write the
  nonlinearity on a real intermediate that reads the tropical tensor instead.
- `unaryFn` factors are admitted in every non-bool statement as real primitives (A6). `log` of −∞ fails
  loud through the existing domain check (Gather.lean:62-63).

**A9. PROPOSED: float edge cases.**
- ⊗ = IEEE `+`. +∞ is outside the max-plus carrier and arises only from data, so (−∞)+(+∞) = NaN propagates
  exactly as real 0·∞ does today (**FIXED**, Q3 decided 2026-10-14: accept).
- Tropical ⊕, and also `ScalarBinOp.max`/`min` in both backends, should use NaN-propagating max/min. Lean's
  `Max.max`/`Min.min` are order-dependent with NaN (see probe). Without this, the source-order fold of a
  collector could hide a NaN.
- ±0 continue to be compared after normalization (NumericalProfile.lean:70-71).

**A10. Existing multi-factor `maxreduce`/`minreduce` programs (complete grep of `leanncd/`).** All of these
change value (S3):
- TropicalTest.lean:21 TR3. Max-times becomes max-plus; the expected value [0.72,0,0,0.72] becomes
  [1.7,0.9,0.8,1.7].
- TropicalTest.lean:35 TR7, min-times. TR5, min-plus shortest path (L41-43), becomes expressible and closes
  the KG-min gap.
- RecurrenceTest.lean:88 RC5: [2,6,18] becomes [2,5,8].
- RecurrenceTest.lean:108 RC7: [2,4,8] becomes [2,4,6].
- RecurrenceTest.lean:132 RC10: G[1,1] 6 becomes 5, and the unwritten G[0,1] goes from 0 to −∞.
- MaxReduceTest.lean:90-101.
- ScanGen.lean:157, template 5 (property-oracle generator).
- GnnScatterTest.lean:50: value preserved only under Q1's homomorphism.

Single-factor uses do not change unless they carry an Iverson factor or an out-of-bounds read:
- EvalExamplesTest:370, ConvPoolTest:44, ClassicalMLTest:71;
- DifferentialTest:349-355, Adapter32Test:381-388 (but the f32 `factorId` constants change);
- SourceAdmissionAcceptanceTest:196.

Programmatic `nonlin ≠ identity` combined with `agg := .max` becomes a rejection under A8: LoweringTest:163-166,
RouteFragmentCorpusTest:602, CompileTest:1434, StructuralTest:493 and SourceRawCorrespondenceTest:93.
`papers/max_min_aggregation.md` and about 15 other `papers/*.md` files need doc-only edits.

## B. Roles and shapes (minimal, for slice 1)

**B1. PROPOSED: roles stay derived through S1–S3.**
- An input is a name that is read and never written. Today that is `externalReadNames` (Structural.lean:761-764)
  and `orderedExternalNames` (ScheduledValidation.lean:58-63).
- A defined tensor is one that is written.
- Every visible defined tensor is an output (`EvalReport.env`).
- Explicit roles (F03, W07) are a separate slice that is not scheduled. The oracle already takes roles as
  side data (`TensorSpec.role`, Source/Adapter.lean:24-26, 66-70).

**B2. Defined tensor with no writer.** The spec says it is the zero tensor (§19.2 L2799-2801). Production
cannot express it, because there is no Def role:
- a declared, unwritten name that is read is treated as an input;
- one that is never read is simply absent.

Slice 1 does **not** change this. It stays a recorded divergence.

**B3. PROPOSED (S1, separable): write-to-input.**
- With derived roles, a statement cannot target an input. The only way to "write an input" is a supplied
  input whose name is a defined tensor, which both backends silently replace today (Eval.lean:158-163;
  Adapter.lean:135-139, 195; see probe).
- Reject this in both entries (`inputIsDefined nm`).
- Unrelated extra inputs still pass through unchanged (ContractTest ~L358).

**B4. Shape today.**
- Declared tensor axes fix **rank only** (Structural.lean:868-871, 891-898).
- Sizes come from reads of inputs and scatter outputs (SizeInfer.lean:113-131), plus `axis`/`iter` pins.
- Assign outputs are never a shape source, which is why mismatched assign writers truncated silently.

**B5. PROPOSED: agreement rule.**
- **S1, assign writers only.** Every writer is a `.plain (.assign)` with only `.free`/`.freeNorm` slots, and
  each position has the same `freeUID?` across writers (FIXED rule). Equal UIDs imply equal sizes, so a
  static check suffices. A mismatch gives `writerShapeMismatch T k pos`.
- **S1, scatter or mixed sets.** Any `.scatter` writer in a multi-writer set is rejected
  (`multiWriterScatter T`) until S3.
- **S3.** Each writer's realized shape (assign: slot sizes; scatter: `outExtent`) must equal T's single
  shape:
  - the collector slots are T's declared axes if declared, otherwise the first assign writer's axes;
  - an all-scatter set needs a declaration (`multiWriterNeedsDeclaredShape`);
  - scatter-vs-scatter extent conflicts already fail as `sizeConflict` through the collector's bare reads
    (SizeInfer.lean:139-144);
  - assign-vs-declared-axis needs an explicit post-inference size comparison.
- `explicitSizes` are unaffected, because clones are tensor declarations, not axis declarations.

**B6. FIXED (A), PROPOSED placement: out-of-range writes are an error (S3).**
- Reference: the silent skip at Scatter.lean:77 becomes `scatterWriteOutOfRange nm oc srcCoord`.
- Checked: `checkScatterCore` (Check.lean:421-433 defers range to the worker today) rejects statically. It
  computes each destination dimension's affine image over the source box (min and max are attained at
  corners; an empty source box is vacuously in range).
- Both backends then reject exactly the same programs, and the dense skip (Dense.lean:339) becomes an
  internal error.
- Surface affine slots cannot produce out-of-range writes against their own derived extent
  (Elab.lean:264-280; `outExtent`, Ast.lean:459-480). The error is reachable only through programmatic
  ASTs or S3 shape mismatches.

## C. The collector (PROPOSED unless noted)

1. **Placement (FIXED).** One `collectDefinitions : ScheduledProgram → Except CompileError (ScheduledProgram × List String)`
   is called:
   - by `validateScheduled` after `isTopoOrdered` (ScheduledValidation.lean:118-127);
   - by `route` before `physicalizeForRoute` (Lowering.lean:567-569).
   It is the identity on any schedule where each name has at most one writer, so every current
   single-writer program is byte-identical through all phases. This is an S1 acceptance check.
2. **Readiness (FIXED).** `eligible` (ScheduledValidation.lean:26-32) changes: a read r is ready when the
   number of emitted publications of r equals the number of nodes that write r.
   - Scan scratch is still never emitted, so it is still never ready.
   - `schedule`'s `topoSort` (Lowering.lean:130) uses the same predicate. A surface `T:=A; U:=T; T:=B` is
     reordered and gives U = A+B; today the evaluator gives U=A and `route` rejects it.
   - A hand-built direct schedule in that order is rejected as `cyclicDataflow` ("not in
     producer-before-consumer order").
3. **Form.**
   - Writer k of T (1-based, schedule order) is renamed `T#k` in place. Schedule order is source order
     unless `topoSort` must delay a writer whose input is defined later; e.g. `T:=V; T:=A; T:=C; V:=B`
     gives `T#1=A, T#2=C, T#3=V`, and the collector folds in that order.
   - The collector is `.plain (.assign T slots' {body := ⟨[⟨[.read "T#1" idx]⟩, …]⟩, nonlin := .identity, agg := a})`.
     It is inserted immediately after the last writer, which precedes every reader by rule 2.
   - `slots'` is `producerSlots` applied to the first writer's slots (Ast.lean:435-438), `idx` is
     `slots'.map (.axis ·)`, and `a` is the writers' agreed annotation.
   - For a predicate T, `Combine.bool` already makes the collector an OR.
   - Assert `isTopoOrdered` on the result.
4. **Declarations.**
   - If T is declared, add one clone per writer with the same constructor, element type and axes under
     `T#k`. This preserves storage-kind uniformity and `checkPredicateOutput`.
   - If T is undeclared, add no clone (both default to f32, Ast.lean:308-311).
5. **Freshness.**
   - Names are `T#k`.
   - Reject `reservedNameCollision` if any generated name is already in the source inventory
     (`routeNameInventory`, RouteFragments.lean:138-140) or two generated names coincide.
   - Route's own all-`#` names stay fresh by length, because they are computed after the desugar
     (RouteFragments.lean:148-149).
6. **Algebra.** S1 admits only `agg = .sum` multi-writer sets (real or predicate), which the Source oracle
   validates (Admission.lean:468 refuses non-sum). A max/min multi-writer set is `multiWriterAlgebra` until
   S3. It is silently overwritten today.
7. **Nonlinearity (FIXED).** Each `T#k` keeps its own nonlinearity, and the collector is the identity
   (spec §15.3, §19.4). So `relu(A)` and `relu(B)` give relu(A)+relu(B).
8. **Hiding (FIXED).**
   - `CheckedScheduledProgram` gains `privateNames`.
   - `evalScheduled` erases them from `env` (Eval.lean:157-170).
   - `prepareEvalPlan` omits them from `materializedNames` (push sites Compile.lean:1626, 1683, 1703, 1725;
     assembled at 1765).
   - With one binding per public name, the last-wins folds in `unpack` (Adapter.lean:195) and the JAX
     runtime (`experiments/jax_bridge/evalplan_affine_runtime.py:177-187`) become moot (**inferred**).
   - Diagnostics may name `T#k`.
9. **Scans (FIXED).** If any writer of T sits in a `.scan` or `.scanPre` node, the desugar does nothing.
   - Mixing plain and scan writers stays fail-loud (verified 2026-10-14: `duplicateScratchProducer`).
   - Plain statements absorbed as scan scratch stay parked.
10. **Self-reads (FIXED).** A writer that reads T can never satisfy all-writers readiness, so it is rejected
    as `cyclicDataflow` before the desugar.

**Correctness argument.** `T#k` is the single-statement collection V_s. The collector computes
⊕_k V_{s_k}[p]. That equals Collect(T)[p] by the grouped form (spec §19.2 L2782-2788; Lean
`Program.collect_grouped`, Semantics/Program.lean:60-67), so the desugared models restricted to the
original names are in bijection with the original models.

**Landed as (slice 1, 2026-10-16).** Slice 1 implemented the sum-algebra bare-slot fragment of this section.
Deviations from the text above:

- `collectDefinitions` is the wrapper in `ScheduledValidation.lean` (it runs `desugarMultiWriters` from
  `Pipeline/Collect.lean` and asserts the result is topologically ordered); `route` calls
  `desugarMultiWriters` directly, because `routeCore`'s `routableInOrder` stays the single topology gate.
- Readiness counts nodes through `ScanStmt.publications` (`outputs`, once per node), not `writes`:
  all-writers readiness compares emitted publications with the number of nodes writing the name.
- Plain + scan and scan + scan writers of one name are rejected `CompileError.multiWriterScan`, where item 9
  said the desugar "does nothing". The other rejections are `multiWriterScatter`, `multiWriterAlgebra`,
  `writerShapeMismatch` and `reservedNameCollision`.
- `PlanBindings` gained `privateSlots` and `definedNames`, and `PreparedBindingsError` gained
  `privateSlotUnpublished`; `privateSlots` is unauthenticated (hardening parked).
- B3 is `EvalError.inputIsDefined` (reference evaluator, after the f32 refusal, where `collectorOwner` names the
  public tensor of a private clone) and `InputBindingError.inputIsDefined` (plan path): run time only on the
  checked side at run time, and at prepare time `InputSignatureError.definedName` (landed after S1, Direct path).

Not landed (S2/S3): scatter, max/min and scan multi-writer sets, the oracle for affine write slots and
tropical carriers, out-of-range write errors, `CollisionReduce`/fill deletion, max-plus.

## D. Spec and document amendments (checklist)

- [x] `tensor_logic_semantics.md` §2.1 table (L445-450): add the max-plus and min-plus rows from A2.
- [x] §2.4 (L532-553): name the concrete sort family {real, bool, max-plus, min-plus}.
  - Replace "Still excluded are implicit conversion between sorts" (L551-552) with: surface elaboration
    inserts registered cast primitives (real↔tropical identity on shared values; 𝔹→K the semiring
    homomorphism), so "a primitive is the only way a value changes sort" still holds in the core.
  - Note that tropical ⊕ is exact on non-NaN floats.
- [x] Scope paragraph (L168-172): padding and implicit conversion move from "outside" to "defined by a
  stated surface profile". Padding stays outside the core in-bounds read rule (§14.2). Add a zero-extension
  read profile: Const(0_K of the sort at the read position), citing boundary-policies §8.4.3.
- [x] §8 Iverson (L923-932): add per-sort values (tropical true = 0, false = ∓∞).
- [x] §13.6 (L1471-1488) and §19.2 (L2799-2801): add an implementation note.
  - Production roles are derived (In = read-and-unwritten).
  - Defined-but-unwritten zero tensors and unused designated inputs (W07) are not realized.
- [x] §19.2: add an implementation note on collection by private per-statement tensors plus a collector,
  justified by the grouped form.
- [x] Claim boundary (new paragraph near §23.4, L3303): production readiness is **tensor-level** (a tensor is
  ready when all its writers have run). Its acyclicity is a strict subset of the coordinate-ranked
  fragment. Scans, §11.1 boundary writers, explicit roles and scatter collection are out of scope for S1.
- [x] §14.3 condition 4 (L1629): note that production now enforces in-bounds writes (S3); the drop policy
  remains long-term option C.
- [x] `lean_executable_semantics_path.md` L959-975 ("one definition per left-hand side"; known contract
  difference; F14/F15 values) and L1304-1312: rewrite after S1 so multi-definition programs are
  value-compared. Done by slice 1 (numerical profile, known contract differences, §5.1).
- [x] Gap audit: the baseline (L29-48), the G04 rows (L90, L307) and F01 (L316-331) are marked closed for the
  plain bare-slot sum fragment (S1). Scatter and tropical closure is marked at S3. F03 and W07 stay open.
  Done by slice 1; the audited-code findings are kept as "as audited before slice 1".

Status, 2026-10-16: slice 1 landed and every item above is applied (`[x]`). The path doc and gap audit
describe the landed state for the plain bare-slot sum fragment; scatter, max/min, scan multi-writer sets,
the oracle for affine write slots and tropical carriers, out-of-range write errors and max-plus remain
planned (S2/S3). The spec remarks on roles (§13.6) and production readiness (§23.4) say that both
backends reject a supplied input that names a defined tensor and that a reader waits for every writer.

## E. Slice outline

Costs are rough, measured against the Rule 6 budget of about 175M per slice.

| Slice | Content | Rough cost | Biggest risk |
| --- | --- | --- | --- |
| **S1** (landed 2026-10-16, see "Landed as" under §C) | §C collector; all-writers readiness; hiding; B3 (optional); S1 rejections (scatter or non-sum multi-writer, UID mismatch, reserved names); remove the oracle profile's `crossStatementOverwrite` refusal (removed in slice 1) | 4–6 dispatches, ~80–120M | The desugar must agree across three entries (`schedule` sort, `validateScheduled`, `route`). Private names could leak through `materializedNames`. |
| **S2** | Oracle extension: affine write slots in Source admission and correspondence (the default `admitSource` still refuses scatter; `admitSourceAffine` admits policy-checked scatter); exact tropical carriers (e.g. `WithBot ℚ` with ⊗ = +); per-sort `AddCommMonoid` (Program.lean:52 already per sort) | ~150M+; likely S2a slots / S2b carriers. **S2a** (affine write slots, sum-only scatter in the oracle): landed on local main, merge 7a551faa (record: `additive_s2a_record.md`); S2b not started | Proof cost in `RawCorrespondence` (34.6K) |
| **S3** | Scatter ⊕ (Scatter.lean:59-92, Dense.lean:392-409, Check.lean:437-441); delete `CollisionReduce`, `ScatterOpts.reduce/fill`, `checkScatterFill` (Eval.lean:23-39), `scatterFillOrFail`, `overlappingScatter` const-collapse (Structural.lean:1099-1118); out-of-range error (B6); multi-writer scatter (B5); A3–A9 | ~150–175M; **PROPOSED** split into S3a (scatter/fill/range) and S3b (sorts/casts/constants) | Lockstep meaning change: reference, checked plan, f32 tables, `BrOp`/bridge and the JAX runtime must flip together, and tests are numerous |

**Tests asserting old behaviour.**

S1:

- ContractTest.lean:325-357: the "true overwrite" mutation inverts.
- DifferentialTest.lean:292-337: Y = Z = A+B.
- CompileTest.lean:604-660: `materializedNames` goes from `["Y","Y","Z"]` to `["Y","Z"]`; signatures become
  `[(Y,bool),(Z,f64)]`.
- Adapter32Test.lean:118-150: the two `Y` entries become one.
- SourceDifferentialPolicyTest.lean F14 (L164), F15 (L246): `knownContractDifference` becomes agreement.
- SourceDiagnosticAdmissionTest.lean:72-95 (`acceptedNonshared`): same change.

S3 (grep counts of `CollisionReduce`/`ScatterOpts`/fill/collision references):

- ScanTest 28, ScatterTest 12, CompileTest 10, ScatterCheckTest 9, ScanUnroll 8, ScatterDense32Test 8,
  ScatterDenseTest 6.
- Two or fewer: GraphCheck, RouteWeave, ComplexElementType, Compare, ScatterNonlinReject, ScatterCompile,
  Scatter32Oracle, ScanDense32, GraphDense, Executable, DefaultF32.
- Also `overlappingScatter` (StructuralTest, CompileTest), the A10 list, and Eval/AGENTS.md L47, L60-61, L69,
  L82.

## F. Decisions taken on the open questions (2026-10-14)

All four questions were answered by the user; none remain open.

1. **Boolean→tropical cast: DECIDED.** Casting always uses the target sort's own identities: false ↦ 0_K of the
   target (the ⊕ identity) and true ↦ 1_K (the ⊗ identity). That is the unique semiring homomorphism from bool.
   For real this reproduces today's 0/1 values, for max-plus it gives −∞/0.0, and for min-plus +∞/0.0. This is the
   same rule that gives false Iverson values and out-of-bounds padding the value 0_K.
2. **Unannotated writers of a tropical T: DECIDED.** A sort-neutral writer inherits T's algebra (A4).
3. **Infinities outside the carrier: DECIDED.** Accept IEEE: (−∞)+(+∞) = NaN. NaN-propagating max/min (A9) is
   adopted regardless.
4. **Supplied input naming a defined tensor: DECIDED.** Reject it with an error (B3). It rides in S1.

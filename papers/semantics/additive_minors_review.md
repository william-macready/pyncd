# Review: S3 minors Direct changes (c0867dd9, 669ce30e)

Diff reviewed: `git diff ccc5c9ae HEAD` on `worktree-s3-minors-direct`. Read-only. No build was run (a full
build was running in the tree), so every fixture value below was re-derived by hand from the semantics,
not observed.

**Counts:** 0 Critical, 0 Major, 7 Minor, 3 Nit.

---

## Findings

### m1 (Minor): `ReadPlan` doc comment still says an OOB unary read contributes `f(0)` "matching the reference exactly"

**Where:** `ReadPlan` doc comment, `LeanNCD/Eval/Plan/Kernel.lean`. It says `unary` is "applied to the gathered value
AFTER the out-of-bounds zero-pad, so an out-of-bounds read contributes `f(0)`, matching the reference `gather`
exactly."
**Why:** c0867dd9 updated the matching text in `Types`, `Compile`, `Check`, `Dense`, `Gather` and the AGENTS nodes,
but missed this one. It is the IR record's own contract, and it is now wrong for a max-plus or min-plus
`AssignPlan`. `Plan/AGENTS.md`'s `Kernel.lean` row was updated, so the node and the code now disagree.
**Fix:** qualify it as the other sites do ("in a real or Boolean statement; in a tropical one an OOB unary read is
the algebra's 0_K, unapplied").

### m2 (Minor): live docs still state the old rule; parked lists not closed

These live docs still state the old rule. All but the last were touched by ccc5c9ae as live docs:
- `papers/max_min_aggregation.md` (header blockquote): "(an OOB read under a `unaryFn` keeps the real `0.0`)".
- `papers/semantics/additive_production_decision_note.md` A5: "a read under a `unaryFn` is padded with 0.0 ... The
  primitive is then applied".
- `papers/backend_missing_functionality.md` (Unary factor functions bullet), and `papers/eval_ir.md` (ReadPlan
  paragraph): "an out-of-bounds read contributes `f(0)`", with no sort qualification.
- `leanncd/docs/test_portfolio.md`: the ConvPoolTest row lists CV5u/CV5ud but not the new CV5ur. The BoolCastTest
  coverage paragraph lists (j) but not the new (k) section (k1-k9, three-way).
- The parked lists in `papers/semantics/additive_s3bii_record.md` §4 and `additive_s3b_record.md` still list "the
  unary-fn OOB `f(0)` in a tropical reduction" and "neutral `Out[i+j]` collision shape" as parked. Neither has a
  closing note pointing at c0867dd9 or 669ce30e.

`additive_s3b_plan.md` §2 (the row "OOB read under a `unaryFn` ... in every sort") and `additive_s3b_design.md` are
historical records. They need at most a "superseded by c0867dd9" pointer.

### m3 (Minor): OOB `log`/`recip` in a tropical statement changed from a fail-loud error to a value, unannounced and unpinned

**Scenario:** `axis i : ℕ = 3; H[i] := maxreduce(log(X[i + 1]))`, X = [1, 2, 3].
- **Before:** the lane `i = 2` padded 0.0 and called `log(0.0)`. That is `EvalError.unaryDomain` (reference,
  `applyChecked` `.log` with `v ≤ 0`) and `PositionalInputError.unaryDomain` (plan f64/f32), so the run failed.
- **Now:** `H = [log 2, log 3, -inf]` with no error.
- `recip` is the same: `recip(0)` used to be a domain error.
- Real statements still fail loud on the same read (KernelDense32Test fixture 2.6 pins `.unaryDomain32 .log 0 0` for
  the real algebra).

**Assessment:** the new value follows from the stated rule (the term is absent, so `f` is never evaluated), so it
is not wrong. But it widens acceptance: a program that used to be refused now runs. Neither the commit message nor
any doc says so, and no fixture pins it in either backend. A mutation that applied `f` to the tropical pad only to
detect domain errors would go unnoticed.
**Fix:** one three-way row in BoolCastTest (k), e.g. `maxreduce(log(X[i+1]))` → `[.., -inf]` with no error. Also add
one sentence in the doc that states the rule.

### m4 (Minor): "tropical" is decided four different ways; the reference uses a sentinel value

**Where:**
- reference `gatherCast`: `zero == 0.0` means real/bool, otherwise tropical.
- plan `denseValueAtWith`: `alg.factorOp == .add`.
- `Check.lean` cast admission: `factorOp == .add && reduceOp ∈ {max, min}`.
- `Plan/Scan.lean` `algebraStateInit`: matches `(.add, .max)` / `(.add, .min)`.

**Soundness today (question 1), checked caller by caller:**
- Every production `gatherCast` caller gets `zero` from `combineFor`. That covers `evalAssignSeeded` (plain,
  `evalPlain`, scan base and step through `evalAssignDtypedSeeded`) and `Scatter.lean` (the scatter compute half).
  `combineFor` returns only `Combine.real` (unit0 0.0), `Combine.bool` (0.0), `Combine.max` (-inf) and `Combine.min`
  (+inf).
- The multi-writer collector, and both backends' neutral adoption (`scanStateStmts` in `Eval/Scan.lean` and
  `Plan/Compile.lean`; `withAgg` in `desugarMultiWriters`), only rewrite `agg`. So both backends see the same
  annotation.
- A predicate destination with `maxreduce` would be misclassified: the reference `combineFor` puts agg first (max),
  but the plan's `algebraForDest .bool` gives the bool algebra. Both pipelines reject it first (`checkPredicateOutput`
  → `predicateAgg`), and the bare pad already disagreed there before this change, so nothing new.
- f64 and f32 share `gatherFactorWith`, and the tropical f32 algebras have `factorOp := .add` (Check.lean).
- Conclusion: there is no production program where the two flags differ.

**Fragility:** `evalAssignWith`/`evalAssignSeeded` are public and take an arbitrary `(mul, combine, unit0, unit1)`.
Any non-tropical Combine whose `unit0 ≠ 0.0` would silently get "OOB unary = unit0, unapplied", for example a
`(×, max, -inf, 1)` max-times semiring. So would a future `Combine` added with such an identity. The only custom
Combine in tests (ContractTest's min-plus) happens to be tropical.
**Fix (cheap):** thread an explicit flag, as the plan does. Or derive both from one `SortAlgebra.isTropical`. Rule 7:
pick one recognition and flag the others for cleanup.

### m5 (Minor, design observation): the "f(pad) wins" hazard remains for IN-RANGE 0_K cells, so results now depend on in-extent vs out-of-extent absence

The fix covers out-of-extent reads only. An unwritten cell inside the extent also holds 0_K: an unwritten
scatter/scan-state cell (in both backends), and a collected tensor's shifted-copy pad once it is materialised.
Under a unary function that cell is fed to `f`, as the new GatherTest row "stored -inf in range, exp(-inf) = 0"
pins. For `exp` in max-plus this is harmless, because exp(-inf) = 0 < exp(any finite). For other functions it is
not:
- **max-plus `sin`/`cos`:** `Out[2*i] := maxreduce(X[i])` with i:2 and X = [-1, -3] gives Out = [-1, -inf, -3, -inf].
  Then `M := maxreduce(sin(Out[k]))` over k:4 is `sin(-inf) = NaN`, and maxNaN poisons the whole M.
- **max-plus `recip`:** `maxreduce(recip(Out[k]))` gives max(-1, -0.0, -1/3, -0.0) = -0.0. The unwritten cell wins.
- **min-plus `recip`:** recip(+inf) = 0 beats every positive candidate.

Reading the same absent position one cell past the extent now gives 0_K. This is intended per the brief and the
commit ("in-range stored -inf under a unary is still applied normally"), and both backends agree. It is still worth
one parked line: "absent" now has two meanings under a unary.

### m6 (Minor, informational): NaN reach widened (same class as the bare OOB pad, nothing new in kind)

Max-plus, `axis i : ℕ = 3; H[i] := maxreduce(exp(X[i + 1]) · R[i])` with R = [0, 0, +inf]:
- **Before:** H[2] = exp(0) + inf = +inf.
- **Now:** H[2] = -inf + inf = NaN.

The bare-read twin `maxreduce(X[i+1] · R[i])` already gives NaN at that lane, so the hazard is the existing one:
+inf is outside the max-plus carrier R ∪ {-inf}, and IEEE does not make -inf annihilate it. The unary path now has
it too. Min-plus is the mirror (-inf in a min-plus factor). No action unless +inf in a max-plus input is meant to
be supported, but neither the doc nor a fixture records it.

### m7 (Minor, scope note): Boolean statements keep the same "f(0) wins" defect, by requirement

`predicate B(i); B[i] := exp(X[i+1])`: the OOB lane is exp(0) = 1, which is **true**, while a bare OOB read is false.
In a ∃-reduction (`B[i] := exp(X[i+p])` over p) the padded lane makes B true regardless of data. This is exactly the
tropical bug class c0867dd9 fixes. Boolean statements were required to stay unchanged, and k6/CV5ur pin that
deliberately. Under a unary, bool reads are also not coerced (k6 expects B[0] = 0.1353, a non-Boolean value in a
predicate tensor). So the bool + unary corner is ill-formed in two ways. Park it explicitly. Today it is only
implied by "real and bool unchanged".

### n1 (Nit): the min-plus fixtures cannot tell "0_K unapplied" from "f applied to 0_K"

With `exp`, exp(+inf) = +inf = 0_K, so every min-plus row (GatherTest posInf, KernelDenseTest min, KD32 2.3b min, k2,
k4, CV5ud) would also pass under the mutation `applyUnaryFn op zero` (pad with 0_K, then apply). The max-plus twins do
distinguish the two (exp(-inf) = 0 ≠ -inf), and the code is shared, so coverage holds. A min twin over `recip`
(recip(+inf) = 0) would make the duality pair symmetric.

### n2 (Nit): `isSortNeutral` counts raw slot UIDs, while the plan's `multiAxisScatterLhs` counts normalized coefficients

`ls.all (l.axisUids.eraseDups.length ≤ 1)` keeps zero coefficients and does not cancel duplicates. Two hand-built
slots show the gap:
- `.affine 0 [(1,i),(-1,i)]` is "neutral", yet all writes collide on cell 0.
- `.affine 0 [(1,i),(0,j)]` is "not neutral" but injective.

Neither form is elaborated from surface syntax. `Out[0*i]` is surface-reachable and is neutral under both readings,
but its destination extent is 0, so every write is a B6 range error. No value is affected. `oracleNeutral` makes the
same raw-UID choice, so the agreement guard cannot see this.

### n3 (Nit): `neutralShapes` has no duplicate-UID row

No row covers a duplicate UID in one slot (`.affine 0 [(1,j),(1,j)]`, i.e. `2*j`, expected neutral). A mutation
that drops `eraseDups` from either definition survives.

---

## Checked and found fine

**(1) Classification per caller.** Covered under m4: plain, scan base, scan step (both via
`evalAssignDtypedSeeded`), the scatter compute half (`Scatter.lean` `combineFor`), the multi-writer collector, a
predicate/bool statement (unit0 0.0, so real path) and a real statement (unit0 is always 0.0). No production
`Combine` other than the four exists. The plan has one gather site (`gatherFactorWith`, reached from
`runDenseAssignAt` for plain, scan base/step blocks and scatter compute). The JAX gate (`Executable.lean`) refuses
unary reads outright. Source semantics (`Semantics/Source/Admission.lean`) rejects `.unaryFn`. f64 and f32 have the
same flag.

**Real/bool unchanged.**
- Reference: the `.unaryFn` arm with `zero == 0.0` is `applyUnaryFn ctx op 0.0`, identical to the old
  `gatherRead ... 0.0` then bind. The in-range arm is unchanged, and no cast is applied to unary reads, as before.
- Plan: the real/bool `none` arm is `ops.applyUnary op ops.zero`, identical to the old `padV = ops.zero`. The
  missing-slot branch behaves exactly like OOB, as before. The bare-read arm is `cell.getD pad`, identical to old.
  The cast is still applied inside the `some` arm, exactly where it was.

**(2) Semantics.**
- OOB under unary = 0_K: in both sorts the factor is ⊗-absorbing for finite co-factors, so the term is absent. It
  matches the bare-read rule.
- An in-range stored -inf under exp is applied (GatherTest row → 0.0). That is intended, see m5.
- An OOB read of a scan STATE under a unary: the reference reads `env`'s state tensor, gets `gatherCell` `none` and
  returns `zero`. The plan's step gather goes through the same `gatherFactorWith` and returns `pad`. They agree by
  construction, though no fixture reads the state itself under a unary (k7 reads `E`).

**(3) Fixtures re-derived** (all correct):
- **GatherTest:** padExp max/min → -inf/+inf; real exp(0) = 1; in-range exp(5); stored -inf → 0.
- **KernelDenseTest:** unaryPlan max/min last lane → -inf/+inf (factor fold 0 + (∓inf), reduce from ∓inf).
- **KD32 2.3b:** 0xff800000 = 4286578688 and 0x7f800000 = 2139095040.
- **ConvPool:**
  - CV5u: P[1] = max(e^-2, e^-5, absent) = 0.1353352832366127.
  - CV5ud: min(e^2, e^5, absent) = 7.38905609893065.
  - CV5ur: real sum, X = 0, gives [3, 3] (an absent pad would give 2).
- **BoolCastTest:**
  - k1 [e^-2, e^-3, -inf]; k2 [e^2, e^3, +inf].
  - k3 [e^-1, e^-2]; k4 [e, e^2].
  - k5/k6 last lane 1.
  - k7: row 0 is -1, -1 + exp(0) = 0, 0 + e. Row 1 is -2, then -inf (E[2,·] is OOB).
  - k8: S[0,·] = e^-2, e^-2 + 0, e^-2 + 1. S[1,·] = -inf. The base is itself neutral and keeps max.
  - k9: Out extent 2·2 = 4, giving [e^-3, -inf, -inf, -inf].

  Each max case differs from the pre-fix value.

**Nothing weakened or dropped.** Tests: 72 insertions, 27 deletions. The deleted lines are the 2 GatherTest padExp
guards, the 2+2 KernelDense/KD32 tropical rows and the 2 CV5u/CV5ud expectations, all flipped to new values and not
removed, plus comment rewrites. No guard was deleted without replacement.

**(4) Change 2 reach.**
- `Out[i+j]` does not parse: LHS slots are single-axis affine, see EdgeCaseTest EC9 and KnownGapTest KG-reshape.
- The plan rejects a multi-axis LHS row (`multiAxisScatterLhs`).
- Multi-writer groups reject non-free slots (`multiWriterScatter` / `writerShapeMismatch`) before `writerSort?`.
- For a single-writer name, neutral vs non-neutral yields the same sort: an all-neutral vote uses the annotation,
  a non-neutral vote its own sort, and a predicate is bool either way.

So no surface program changes value or acceptance, which matches the commit's "no existing fixture changed value".
The agreement guard is non-vacuous: `neutralShapes` pins literal expectations, and rows such as `S[j+k] := X[j]` and
`S[j+k] := X[j,k]` (sum and max) flip from true to false without the new conjunct. `oracleNeutral` is restated with
its own case split (`oracleSlotUids`/`oracleIdxUids`, not `idxAffineForm`/`axisUids`).

**(5) Code comments.**
- Updated correctly: `Gather.lean`, `Dense.lean` (`ScalarKernelOps.zero`, `gatherFactorWith`, binary32 header),
  `Types.lean` `OutOfBoundsPolicy`, `Check.lean` `admittedAlgebras`, `Compile.lean` `algebraForAgg` and the
  residualize comment, `Eval/AGENTS.md`, `Plan/AGENTS.md`, `DSL/AGENTS.md`.
- Remaining stale text: m1 (code) and m2 (docs).
- `DifferentialTest`'s `exp(0) = 1.0` comment is a real statement, so it is correct.

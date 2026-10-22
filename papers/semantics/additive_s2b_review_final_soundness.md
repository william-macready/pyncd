VERDICT: APPROVE WITH FINDINGS

Whole-branch review, lens (a) semantics soundness, of `main...HEAD` (merge-base `82ad3df9`, tip `7be1da16`). I only read
code. I did not run lake or lean, and edited nothing but this file. Items marked (predicted) are reasoned, not executed.
The T4B review's M1/M2 are not repeated here (see m5).

## Findings

### Critical
None. No path I found makes a wrong production result read as `fourLegParity`, because parity compares against the
exact oracle bit for bit.

### Major
M1. The sorted harness runs REAL (`sum`) programs under the tropical numerical profile. This profile is not enough for
sum-product, so production gets blamed for correct IEEE results. `compareSortedSource` (SortedDifferential.lean:213-263)
accepts any program that `selectCarrier` maps to `real` (the plan §2 fixture `sum Z[a,b]` is `fourLegParity`). It then
calls `checkSortedProfile` (:68-92), which bounds only the per-occurrence `Σ|reads|` and the output cells. The real
`checkProfile` also bounds partial products, fibers and statements (NumericalProfile.lean:167-290). With three factors,
`Σ|reads| ≤ 2^20` still allows products up to about 2^55.
Concrete input (predicted). Axes `a` (1) and `b` (2). Inputs f64 `A,B,C[a,b]` with `A=[349525,349524]`,
`B=[349525,349525]`, `C=[349525,-349526]`. Statement `Y[a] := A[a,b]*B[a,b]*C[a,b]` (sum).
- Exact result: 349525³ − 349524·349525·349526 = 349525.
- Binary64 (checked in Python): each 2-factor partial product is exact (≤2^38) and the final product rounds once, so
  every multiplication order gives fl(P) − fl(Q) = 349528. With FMA the result is still ≠ 349525.
- The sorted profile accepts it: both occurrences have Σ|reads| = 1048575 ≤ 2^20 and the output is in the envelope.
- So both legs `mismatch` and the run is classified `nativeDiscrepancy`.
- `compareSource` on the same program refuses with `outsideEnvelope … partialProduct` (349525² > 2^20).
A real program run through the sorted harness also skips the real harness's oracle-receipt re-check and the S2a
structural conditions (a colliding sum scatter ends as `nativeFailure`, not `scatterCollisionRejected`).
Fix (one of):
- Refuse or redirect `real` in `compareSortedSource` to `compareSource`, and move the `sum Z` rows there.
- Add a per-carrier profile hook to `Sorted`, with real using the product/fiber bounds.
- At minimum, document that a real classification from the sorted harness is not authoritative.

### Minor
m1. Tropical multi-writer programs are a third known contract difference with no condition. Two `max` statements writing
the same `Y`: the oracle and Core combine them with `⊕` = max (Oracle.lean `runWith` total, the Core publication sum).
Production refuses with `CompileError.multiWriterAlgebra` (DSL/Pipeline/Collect.lean:100). The run ends as
`nativeFailure` with no condition. That is the loud direction, but plan §3 and the docs ("the structural conditions" = two)
leave it out. Park it with S3b or add a row.
m2. (predicted) A zero-factor term is a sibling of `tropicalMultiFactor` that detection misses. `detectSortedConditions`
fires on `factors.length ≥ 2` (SortedDifferential.lean:181). `admitTerm` admits an empty read list (Admission.lean:256).
For such a term the oracle gives `1_K` = `fin 0`, while production starts from `unit1 = 1.0` (Eval/Contract.lean:167,171).
Only hand-built snapshots are likely to reach this, and the result is a loud `nativeDiscrepancy`. The condition should be
`length ≠ 1`, or the case should be documented.
m3. The independence-caveat wording claims too much. The oracle and Core share the `[Semiring K]` instance, and also
`C.ofRat` and `C.observe`: both legs take them from the same `S.carrier` (SortedDifferential.lean:35, 218, 222;
Schedule.lean `sourceInputBindingAt`). Core-vs-oracle parity therefore checks scheduling and WHERE embedding/observation
are applied, not the embedding or observation functions themselves. The plan §0 says it checks "input binding and
observation". The AGENTS node and part_4 say it checks "scheduling and observation". The functions are pinned elsewhere:
- SourceOracleCarrierTest:142-152.
- Bits on the extent-0 production rows, SourceSortedDifferentialTest:151-159.
So there is no gap, only wording. Also, production agreement on single-factor rows pins `⊕`, `0_K` and `1_K⊗x = x`, but
never `⊗ = +` (production multiplies by design). `⊗` is pinned only by the hand rows CarrierTest:61, 66 and
SortedDifferentialTest:89.
m4. The extensibility claim holds for the oracle, Schedule, selection and the Core leg, but not for the differential.
Three pieces are tropical-specific:
- The tropical-scatter refusal in Admission (Admission.lean:913, `sorted && rhs.agg != .sum`).
- `detectSortedConditions` (`agg != .sum` means tropical).
- `checkSortedProfile`, which assumes `⊗` is `+`.
A fourth carrier run through `compareSortedSource` would be judged by tropical rules. Also, "one carrier record plus one
table entry" leaves out the `Semiring`/`DecidableEq`/`Repr` instances that `Sorted` requires
(CarrierTest:80-104 supplies them). The docs should scope the claim to oracle and Core.
m5. T4B review M1/M2 are still open in the code: `confirmsSorted` does not require the two legs to agree with each other
(SortedDifferential.lean:192-195), and `compareBindings` stops at the first mismatching binding (:103-112). Until those
are fixed, part_4's "confirmed only when both native legs show the predicted outcome at the condition's own tensor"
claims too much.
Nits:
- Ten real Schedule names were deleted rather than restated (T3 review). They have no callers (grep is empty).
- AGENTS says "the real names are its rational instance". That is true for the schedule names, but `runSource` is not
  `runSourceAt Carrier.real`. It uses `RationalReference.ops`/`registry`, which has the same arithmetic.
- The global unscoped `LinearOrderedAddCommMonoidWithTop (WithBot ℚ)ᵒᵈ` instance is documented (Carrier.lean:63-71).

## Answers to the numbered checks
1. Correct. In Mathlib's Tropical, `+` is `min` (Tropical/Basic.lean:235), `*` is `+` (:334), `0` is `trop ⊤` (:202)
   and `1` is `trop 0` (:348). With `R = (WithBot ℚ)ᵒᵈ`, `min` in the dual is `max` in `WithBot ℚ`, and `⊤ᵒᵈ` is `⊥`.
   That gives 0_K = −inf, 1_K = 0, ⊕ = max, ⊗ = +.
   - The class (Order/AddGroupWithTop.lean:36-40) has exactly two non-parent fields. The instance proves both:
     `top_add'` by `WithBot.bot_add` and regularity by `WithBot.add_left_cancel`. It overrides no data, so there is
     no diamond.
   - `observe`: max-plus maps `⊥` to `negInf`; min-plus maps `⊤` to `posInf`; `↑q` maps to `fin q`.
   - Pinned at CarrierTest:143-148.
2. Correct in both legs. In the oracle, the `termFiber` total, the `contribution` fold and the `runWith` cell total all
   start at `0 : K`, so an empty fiber or empty reduction is `0_K`. The Core leg uses `semiringOps`. Both are pinned:
   strided `∓inf` (SortedDiffTest:91, 93) and extent-0 `∓inf`, with production parity (:151-159).
3. The caveat is correct in substance, but see m3. The hand-valued fixtures pin the algebra independently of the shared
   instance: expected values are built with `ofRat`, not with semiring operations. Contraction [101..104] / [2..5]
   separates `max` from `min` and `+` from `*`. `observe 0` pins `0_K`.
4. `observe ∘ ofRat = fin` holds definitionally for all three carriers (pinned at 5 and 3/2). `ExtVal` derives
   `DecidableEq`. `compareTensors`/`compareCells` only gained the type parameter, with `V := ℚ` as the default, so real
   callers are unchanged.
5. Verified by `git diff main...HEAD --stat`. ProgramCorrespondence, RawSemanticConnection, RawCorrespondence and
   Permutation are absent. `admitStatement` (Admission.lean:654-680) and `admitStatement_fields` (:697) lie outside every
   hunk, and with `sorted = false` the rhs is unchanged (:908). The real schedule names are `abbrev`s of the `…At` forms,
   plus four one-line restated theorems (Schedule.lean ~152-169). `elaborateSource` changed from def to abbrev
   (Program.lean:120). No test file was edited. The build was not checked by me (full `Tests` build in progress).
6. Yes for the oracle, selection and Core. The toy is a test-only carrier plus `withToy`, with no edit to the
   Oracle/Schedule/Admission sources, and it runs through `runWith` and `runSourceAt` (CarrierTest:112-114, 183-185). It
   also needs semiring instances and does not extend to the differential (m4).
7. The profile is sufficient for tropical carriers:
   - Single-factor rows do no arithmetic (`0 + x`; `⊕` only selects), so they are exact.
   - For a future max-plus production, partial sums are ≤ Σ|reads| ≤ 2^20 < 2^53.
   - Multi-factor runs are a confirmed condition today.
   - The `±inf` bits `0xFFF0…`/`0x7FF0…` are correct, pinned against `Float.toBits` (:121-122), and meet production in
     the extent-0 rows.
   It is NOT sufficient for the real carrier, which the same harness accepts (M1).
8. Overclaims, all minor except as tied to M1:
   - The docs call the profile "tropical" without saying it also gates `sum` programs (M1).
   - "Checks … observation" (m3).
   - The extensibility scope (m4).
   - "Confirmed only when both legs…" (m5).
   - The two-condition list leaves out multi-writer (m1).
   - The rest of the S2b paragraphs (AGENTS, part_4, part_5, gap audit) match the code.

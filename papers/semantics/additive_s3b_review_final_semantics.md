# S3b final review: semantic table fidelity (lens a)

Read-only review of `740bd4f8..be4d888d` (branch `worktree-additive-s3b-tropical-flip`). No build and no mutation were run.
Each value claim below comes from reading source and doing the arithmetic by hand, not from execution.
Intended semantics: max-plus `(⊗ +, ⊕ max, 0_K -inf, 1_K 0)` and min-plus `(⊗ +, ⊕ min, 0_K +inf, 1_K 0)`.

Counts: Critical 0, Major 1, Minor 6.

---

## M1 (Major): a sort-neutral scan statement that carries a nonlinearity escapes `tropicalNonlin` and is evaluated tropically under `relu`/`softmax`

**Where:** `Stmt.isSortNeutral` and `scanStateStmts` (`LeanNCD/DSL/Ast.lean`); `checkTropicalOutput` (`LeanNCD/DSL/Pipeline/Structural.lean`).
The two backends apply the same rewrite: `evalScan` in `LeanNCD/Eval/Scan.lean`, and `compileScan` with `residualizeAssignment` in `LeanNCD/Eval/Plan/Compile.lean`.

**Mechanism:**
- `isSortNeutral` looks only at the RHS shape: one term, one `read`/`unaryFn` factor, no contracted axis. It ignores `rhs.nonlin`.
- `checkTropicalOutput` tests `s.algebra env`, which is the statement's OWN annotation.
- `scanStateStmts` runs after validation. It rewrites a neutral statement's `agg` to the state's sort, so a `sum`-annotated neutral base carrying `relu` becomes a max-plus statement carrying `relu`.
- Design decision A8 (`tropicalNonlin`) exists to forbid exactly that combination, and nothing rejects it here. The pad and the bool cast are the only sort-dependent parts of a neutral statement, and both feed into the nonlinearity, so the value changes.

**Failure scenario (accepted by `validateScheduled`; both backends agree on the surprising value):**
```
predicate P(j)            -- P = [0, 1]
M[j, 0]    := relu(P[j])                      -- agg sum, neutral
M[j, l+1]  := maxreduce(M[j, l] · W[j, k])    -- max-plus: state sort = maxPlus
```
- The base is rewritten to `.max`, and `boolReadCast` / `ReadPlan.boolToTropical` cast `P` to `[-inf, 0]`. Then `relu` gives `M[:,0] = [0, 0]`.
- Under the user's own annotation (real), the base is `relu([0,1]) = [0, 1]`.
- The softmax variant is also accepted and changes value:
  - Program: `M[j,0] := softmax_j(X0[j+1])`, with X0 of extent 2 and j of extent 2.
  - The OOB cell is now padded with `-inf`, so `exp(-inf) = 0`. Real semantics pads with `0`, so `exp(0) = 1`.
  - Result: the base row becomes `[1, 0]` instead of `[e^x/(e^x+1), 1/(e^x+1)]`.

**Evidence:**
- `checkTropicalOutput` uses `(s.algebra env).isTropical`, which is false for a `sum` base.
- `scheduleAlgebras` lets only non-neutral statements vote, so the recurrence alone fixes `maxPlus`.
- `checkSortCasts` accepts bool -> maxPlus.
- No parked row in plan §2 / §3 mentions nonlin on a neutral writer, and the design notes are silent on it (grep).
- The duality property skips exactly these cases ("`enumScanCases` 17 ... 4 skipped: template 2 `relu`", plan §2), so nothing would observe it.

**Suggested resolution (owner's call):**
- Option 1: make `isSortNeutral` require `rhs.nonlin == .identity`. A statement with a nonlinearity then votes with its own annotation, and the example becomes a `scanStateAlgebraMismatch`.
- Option 2: run `checkTropicalOutput` on the post-`scanStateStmts` statements.
- Either way, add one rejection fixture.

---

## m1 (Minor): the bool -> tropical cast turns a stored NaN into TRUE (`1_K`) and the NaN disappears

**Where:** `boolReadCast` (`Eval/Contract.lean`), `ScalarKernelOps.isTrue` (`floatOps`, `float32Ops` in `Eval/Plan/Dense.lean`).

**Scenario:** `predicate edge(i,j)`, input `edge = [[NaN, 1],[0, 1]]`, `H[i,f] := maxreduce(edge[i,j] · X[j,f])`.
- `NaN != 0.0` is true, so `edge[0,0]` reads as `0.0` (1_K) and `H[0,:]` is a finite max.
- If the same predicate is read by a bool statement, `minNaN`/`maxNaN` propagate the NaN.
- If it is read by a real statement (identity cast), the NaN also survives.

The slice states "a NaN never vanishes from a reduction" as the reason for `maxNaN` (`Eval/Error.lean` doc). The cast is the one path where a NaN input to a tropical statement vanishes.

The two backends agree, so this is a convention gap, not a divergence. Either document "NaN in a predicate is true" next to "stored != 0", or map NaN to NaN.

## m2 (Minor): a unary read's OOB pad (`f(0.0)`) can win a tropical reduction, which is the failure mode T2 removed for bare reads

**Where:** the `.unaryFn` arm of `gatherCast` (`Eval/Gather.lean`, pad `0.0`); `gatherFactorWith`'s `padV` (`Eval/Plan/Dense.lean`, `ops.zero`).

**Scenario:** `Y[i] := maxreduce(cos(X[i, j]))`, with `j` extent 3 and `X` 2 wide, `X = [[3.14159, 3.14159]]`.
- The valid cells give `cos ≈ -1`.
- The OOB cell gives `cos(0) = 1`, so `Y = [1]`. Under "OOB is absent (0_K)" the answer is `-1`.
- Same with `exp(X)` where `X << 0`: the OOB term `exp(0) = 1` dominates.
- A `log` read OOB fails loud (`log(0.0)` is a domain error) in every sort.

Plan §2 states this rule explicitly ("OOB read under a `unaryFn`: 0.0 ... in every sort"), so it is a stated decision, not a code bug. The design is still inconsistent: what a padded SOURCE cell holds depends on whether a function is applied (`0_K` of the statement for a bare read, real `0` under `f`). Recommend recording the rationale and this counter-example in the design note.

## m3 (Minor): the cast rejections are not transitive; one real copy launders max-plus -> min-plus (and tropical -> bool)

**Where:** `checkSortCasts` (`DSL/Pipeline/ScheduledValidation.lean`).

**Scenario:**
```
Y[i]  := maxreduce(Z[i, k])          -- maxPlus
T[i]  := Y[i]                        -- real (tropical -> real: identity, accepted C9)
Z2[i] := minreduce(T[i] · W[i, j])   -- real -> minPlus: identity, accepted C4
```
- Writing `Z2[i] := minreduce(Y[i] · W[i,j])` directly is `sortCastUnsupported "Z2" "Y"` (C12).
- Through `T`, every `-inf` (the max-plus 0_K) arrives in a min-plus statement, where it absorbs every `min`.
- Likewise `predicate P(i); P[i] := T[i]` (real -> bool, parked decision 1) stores `-inf` in a predicate. A later bool -> tropical cast then reads it as TRUE (`-inf != 0`): the max-plus zero becomes 1_K.

This follows from the table (both legs are identity casts) and from parked decision 1. Flag it so that nobody relies on C10/C12/C14 as a soundness guarantee. The rejection is a lint on the immediate source only.

## m4 (Minor): the raw scan checker does not tie `StateSlot.initValue` to the step algebra

**Where:** `checkScan` (`Eval/Plan/Scan.lean`), around `stateInitNotAdmitted`.

The only check is "no `±inf` init on a `.bool` state". A raw plan with a max-plus step algebra and the default `initValue := .zero` is admitted, and its unwritten state cells read as real `0`. That is the pre-S3b behaviour, and it can beat an all-negative valid cell in a later `max`. A real-algebra state with `.negInf` is admitted too.

`compileScan` always sets `initValue` from `scanStateAlgebra`, so the compiled path is consistent; this is raw-plan (R7) only. The default `.zero` was chosen deliberately so old literals keep compiling (record §3 call 13). Even so, the checker cannot tell that call apart from a mistake. Optional: reject an `initValue` that is not the `reduceId` of every step writing that state.

## m5 (Minor, latent): neutrality treats a multi-source-axis affine scatter slot as "no contraction", although its collisions combine

**Where:** `Stmt.isSortNeutral` (`DSL/Ast.lean`), via `LHSSlot.axisUids` of `.affine`.

`Out[i + j] := maxreduce(X[i, j])` is classified neutral, because `i` and `j` are both "on the LHS". Collisions on `i+j` are an ⊕-fold, so the statement's sort decides the value: sum and max differ.

This is unobservable today:
- At top level, neutrality is not consulted.
- In a scan, the checked path refuses multi-axis scatter slots, and the reference scan scatter overwrites (F3).

It becomes live with S3b-ii (A4: neutral writers adopt the group's sort) or with an F3 fix. Recommend that S3b-ii's design define neutrality as "no combining at all", which also excludes affine slots that name more than one source axis.

## m6 (Minor, documentation): an annotated neutral SCRATCH statement in a scan evaluates REAL, not "in its state's sort"

**Where:** plan §2 "Statement-sort rule" and the parked row "Annotated NEUTRAL scratch statement in a scan evaluates in its state's sort".

A scratch name's only writer is that statement. `scanStateSorts` is therefore `[]`, so `scanStateAlgebra` is `real` and `scanStateStmts` rewrites `maxreduce` to `.sum`.

Example: `T[j] := maxreduce(X[j+1])` as a recurrence scratch pads with `0`. The same statement at top level pads with `-inf`. This is the parked all-neutral case under another name. The parked row's wording ("its state's sort") hides that the outcome is always REAL, so the wording should say so.

---

## Checked and found fine

**Constants, f64 (both backends):**
- Reference: `Combine.max` / `Combine.min` = `tropical maxNaN (-1/0)` / `tropical minNaN (1/0)`, with ⊗ `+`, `unit1 = 0.0`. `Combine.bool` = `⟨minNaN, maxNaN, 0, 1⟩`.
- Plan: `admittedAlgebraMax` / `Min` have `factorOp .add`, `factorId Float.toBits 0.0`, `reduceId ∓inf`. `admittedAlgebraBool` decodes to `1.0` / `0.0` in `floatOps`.

**Constants, f32:**
- `tropicalAlgebraF32`: `factorId 0x00000000`, `reduceId 0xff800000` / `0x7f800000`. Real ⊗ id is `0x3f800000`.
- Scan init: `Float32.ofBits 0xff800000` / `0x7f800000`.
- `.bool` decodes to `0x3f800000` / `0`.

**⊗ / ⊕ / fold order:**
- Reference `evalAssignSeeded`: prod from `unit1`, termAcc from `unit0`, acc from `unit0`.
- Plan `denseValueAtWith`: the three `foldScalars` with the same seeds and order.
- Scatter collision: reference `c.combine prev val` and plan `reduceOp (data[fi]) val` use the same argument order, so even the `±0` sign agrees.

**0_K on unwritten scatter cells:**
- Reference: `DenseTensor.ofFn outShape (fun _ => c.unit0)`.
- Plan: `Array.replicate .. reduceId`.
- The `boolDest` special case is gone, and predicate collisions still use `maxNaN`.

**Scan init and the neutral rule:**
- Reference init: `combineFor decls nm (scanStateAlgebra ..).stateAgg).unit0`.
- Plan init: `initValue` from the same `scanStateAlgebra` (`.bool` -> `.zero`).
- Both backends run `scanStateStmts` before evaluating or compiling. `scanStateSorts` stays neutral-aware after the rewrite, because neutrality is shape-based and `agg`-independent.
- Parked pin `parkedAllNeutralScanState`, re-derived: `M[j,0] = X0[j+1]` with `X0 = [3,4]` gives `[4, pad]`. Under real the pad is 0, so `M = [[4,4],[0,0]]`. Correct, and parked as stated.

**NaN on max/min paths:**
- `git grep` of `Max.max|Min.min|max a b|min a b` over `LeanNCD/{Eval,Exec,DSL,Semantics/Source}` finds only:
  - the helpers themselves;
  - `Eval/Nonlin.lean`'s `NonlinOps.max` (relu/softmax), reachable only from real statements (`tropicalNonlin`, `predicateNonlin`), except through M1;
  - `Nat` uses.
- Every ⊕ and bool ⊗ goes through `maxNaN` / `minNaN` (`32`).
- The `-inf` seed is the first argument, and `maxNaN(-inf, NaN) = NaN`, so the order does not matter.

**IEEE note (not a finding):**
- `0_K ⊗ x` is not absorbing for the opposite infinity: `-inf + +inf = NaN`.
- So a masked or padded max-plus cell meeting a `+inf` factor poisons the reduction. Example: GN4 with `X[0,0] = +inf` gives `H[1,0] = NaN`, not 3.
- This is the exact analogue of real `0 · inf = NaN` and lies outside the semiring carrier. Both backends agree.

**Cast (C5–C8, C19, C24 at the value level):**
- Reference `boolReadCast` keys on `agg ≠ sum` and on the source being declared `predicate`. Plan keys on `agg ≠ sum` and the `.bool` slot dtype.
- Neither casts the OOB pad, and neither casts under `unaryFn` (the checker refuses `castNotAdmitted`).
- Truth is "stored != 0" in both (`-0.0` is false in both).

**OOB pad:**
- Bare read: reference `gatherRead .. zero`, plan `pad = reduceId`.
- Unary read: `0.0` / `ops.zero`.
- Iverson: true gives `one` / `factorId`, false gives `zero` / `reduceId`.

**`approxEq`:** `x == y || |x-y| < ε`. Equal infinities are equal, opposite infinities are not, and NaN is never equal.

**Re-derived migrated expectations (record §2), all correct by hand:**
- **Tropical portfolio:**
  - TR3: `[1.7,0.9,0.8,1.7]`.
  - TR7: `[5,3]`.
  - TR5: all 9 cells of `[0,1,3,5,0,2,3,4,0]`.
  - TR10: `[-3,-1,-1]`.
- **Recurrences:**
  - RC5: `[2,5,8]`.
  - RC7: `[2,4,6]`.
  - RC10: `[2,-inf,5,5]`; RC10m: `[-2,+inf,-5,-5]`.
- **KernelDense, f64:**
  - `maxContractPlan`: A+3; `minContractPlan`: A+1; NegB: A-1.
  - Twins: NegA_NegB under min gives A-3, NegA_PosB under min gives A+1, NegA_NegB under max gives A-1.
- **f32 bits:**
  - Fixtures 7/8: 13, 103, 1003, 10003 = `1095761920, 1120796672, 1148895232, 1176259584`; 11, 101, 1001, 10001 = `1093664768, 1120534528, 1148862464, 1176257536`. Each recomputed from the IEEE fields.
  - Fixture 9: -1, -3 = `3212836864, 3225419776`.
  - `oobMaxPlan`: `[-1,-3]`.
- **GNN:** GN4 `[[3,4],[3,4]]`, GN4m `[[-3,-4],[-1,-2]]`. The "raw read" alternatives `[[4,5],[4,5]]` and `[[-2,-3],[-3,-4]]` also check out.
- **ScanTest shape 1:**
  - max: `[-1,-inf,-2,-inf,-3,-inf]`; min: `[1,+inf,2,+inf,3,+inf]`.
  - Joined: `[10,5,2]` / `[-10,-5,-2]`.
- **SourceSortedDifferential T7 rows:**
  - `collide`: `[-3,-inf,7,-inf,17,-inf,27,-inf]` / `[-5,+inf,5,..]`.
  - `contract`: `[97,107,117,127]` / `[-4,6,16,26]`.
  - `zeroY`: `[0,0,0,0]`.
  - `product` with X negative: `[99,98,97,96]` / `[0,-1,-2,-3]`.
  - `product` with default X: `[101..104]`.
  - `strided`: `[1,-inf,2,-inf,3,-inf,4,-inf]`.
- **ScatterDense32 1.6c:** `[0xff800000, 0x42ca0000, 0x42cc0000, 0x42ce0000]` and the min twin.

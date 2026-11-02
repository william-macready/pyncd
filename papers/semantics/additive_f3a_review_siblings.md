# F3-a review, lens 1: wrongly rejected or changed valid programs, observers of the reference scan

Branch `worktree-scatter-f3a`, commits `8742d84f`, `6c6198b2`, `043e3beb` over `0ce996c3`. Read-only review.
Probe: `leanncd/spikes/ReviewF3a_L1_A.lean` (untracked, deleted after the run). Outputs below are copied from that run.

Counts: P1 0, P2 1, P3 2.

## Observer table

Every caller of the reference scan (`evalScan`, `writeScanStmtSlice`) found by `rg`:

| Observer | Path to `evalScan` | Programs whose outcome changes | Checked path accepts them? | Verdict |
|---|---|---|---|---|
| `TLProgram.eval` (`Eval/Entry.lean`) | `compileToScheduled` then `evalScheduled` (`Eval/Eval.lean:173`) | (1) a real-sort state written with `-0.0`: bits change from `-0.0` to `+0.0` (F1). (2) `S[l+1, a+b]`-style multi-axis scan slots: the value changes from overwrite to sum | (1) yes; (2) no (`multiAxisScatterLhs`) | (1) bit-level change, see F1. (2) intended |
| Source differential legacy leg (`Semantics/Source/NativeLegs.lean` `legacyWithInputs` via `TLProgram.eval`) | as above | as above | as above | No classification changes. Scans are outside the numerical profile, so the classification stops at `unsupportedNumericalProfile` before the native legs are compared. When the checked leg fails, the result is `nativeFailure` whatever the legacy leg does. Bit comparisons use `normalizeZeroBits` |
| `evalScanF64` (`test/Eval/ExplicitF64.lean`), `test/Eval/ScanTest.lean`, `ComplexElementTypeTest` | direct, hand-built | hand-built collisions and out-of-range writes (intended, covered by the new fixtures) | no | intended |
| `ScanOracle`/`ScanGen`/`DifferentialTest` `scanParityCheck` (`evalScheduledF64`, `TLProgram.eval`) | `evalScheduled` | none: the curated templates have injective in-range writes and no `-0.0` | yes | no change, and the build is green |
| JAX bridge (`experiments/`) | no match for `evalScan`, `evalScheduled` or `TLProgram.eval` | none | n/a | not an observer |

Verdict: no admitted program is newly rejected. One admitted program family changes value at the bit level only (F1). Every other changed outcome is a program that the checked path and `compileToScheduled` already refuse.

## Findings

### F1 (P2): a real-sort state loses a written `-0.0`, so a program both backends accept now differs bitwise
- **Where:** `writeScanStmtSlice` @ `leanncd/LeanNCD/Eval/Scan.lean:119`. The docstring there (lines 95-97) says a cell "holds the written value".
- **Scenario:** a hand-built `TLProgram` run through `compileToScheduled`, with no hand-built schedule: `S[j,0] := leakyrelu(X[j])` and `S[j,l+1] := S[j,l]`. Here j=1, l=2, `X = [-5e-324]` (bits `0x8000000000000001`). `leakyrelu` gives `0.01 * -5e-324`, which rounds to `-0.0`. The slice bits observed were `9223372036854775808`.
  - Observed: `REF [1, 2] [0.000000, 0.000000] bits [0, 0]` and `CHK [1, 2] [-0.000000, 0.000000] bits [9223372036854775808, 0]`.
  - Before F3-a the reference stored the slice value (`-0.0`) and matched the checked path. It now computes `0.0 + (-0.0) = +0.0`.
  - This answers the brief's question: a `-0.0` does reach the write. The route is a pointwise nonlinearity (`leakyrelu`, and likely `gelu`) applied after contraction, and the `0`-seeded contraction does not stop it.
- **Only the real sort is affected:** `maxNaN(-inf, -0.0)`, `minNaN(+inf, -0.0)` and the bool `maxNaN(0.0, -0.0)` all return `-0.0` under Lean's `max`/`min`.
- **Why tests miss it:**
  - `ScanTest` uses `approxEq`, and Float `==` treats `-0.0` and `+0.0` as equal.
  - The source differential normalises zero bits and excludes scans from its profile.
  - `/` by zero raises a domain error, so no downstream operator in the language can turn the sign into a visible value. The only thing that observes it is a bitwise comparison.
- **Fix:**
  - (a) Docs only, cheap. Qualify the docstring to say a cell holds the written value up to the sign of zero, under the real sort. This is the same `0_K`-fold behaviour as the top-level `evalScatter` (S3a). Add a fixture that pins the bits that are chosen.
  - (b) Exact parity, about 15 lines. Thread a per-state "written" mask through `evalScan` and copy on a cell's first write.
  - Recommendation: (a) now, and decide (b) together with F3-b, when the checked scan path starts folding too.

### F2 (P3): the docstring's list of programs that reach a scan collision is incomplete; two more cross-call shapes exist
- **Where:** `writeScanStmtSlice` docstring @ `Scan.lean:98-100`, and `Eval/AGENTS.md:64`. They list only "a slot naming two source axes, a constant slot, or a repeated axis UID". The claim that "only hand-built programs reach it" still holds.
- **Scenario D:** a 1-D scan whose recurrence writes the CURRENT cell (`S[l] := S[l]·X`, `.free l`, seeded). This direct `evalScan` call is hand-built. X=2 and L=3.
  - Observed: `[6, 0, 0]`. Old overwrite would give `[4, 0, 0]`.
  - The step folds onto the base-filled cell, so this is a cross-call collision.
  - `compileToScheduled` refuses it (`scanProjectionUnsupported "S"`, observed), and so does `stepWriteRowsOk` on the checked side.
- **Scenario E:** a 2-D scan `[r, c]` whose state `S[r]` omits `c`, with `S[r+1] := S[r] + X`. X=1, r=3, c=4.
  - Observed: `[1, 6, 15]`. Old overwrite gives `[1, 2, 3]`.
  - The sum depends on iteration order. 15 = 3 + 5 + 7, because the step loop interleaves the r values inside each c.
  - The reference admits it because `baseTouchesBoundary` deliberately accepts a missing axis, and `checkStatePlacements` does not check advancing-axis presence.
  - Refused by `finalizeScans` (`inconsistentScanAxes`) and by the checked path (`advancingAxisNotInLhs`).
- **Why tests miss it:** the new fixtures cover only in-call collisions (`S[j+q]`, constant, repeated UID).
- **Fix:** add D and E to the docstring list and say E's value depends on iteration order. Docs only. Optionally, a reference guard for "a state omits a scan axis", mirroring `advancingAxisNotInLhs`. That is a separate decision, outside F3-a's scope.

### F3 (P3): the error payload for the rank-mismatch and scan-local cases is misleading
- **Where:** the out-of-range arm @ `Scan.lean:116-121`, and the `scatterWriteOutOfRange` doc and render @ `Eval/Error.lean:324-329, 426`.
- **Reachability:** not reachable through `compileToScheduled`. A base `S[j,0]` (rank 2) with a step `S[l+1]` (rank 1) is refused at compile time: observed `CompileError.rankMismatch "S" 2 1` on both legs.
- **Scenario:** hand-built `evalScan` on that same program. Observed message: `evalScatter S: write to output coord [1] (from source coord []) is outside the destination extent`.
  - Coordinate `[1]` lies inside dimension 0's extent (2). The real fault is the rank mismatch.
  - The message names `evalScatter`, although the scan-local write raised it.
  - The source coordinate is the unseeded slice coordinate, so the step's scan indices are absent: `[]` here, and also in D/E-style writes.
  - The constructor doc still describes only the B6 top-level site ("`scatterSourceAxes` order").
- **Why tests miss it:** the new out-of-range fixtures (negative base or bias) match on the constructor, not on the rendered text, and none of them is a rank mismatch.
- **Fix:** document the scan site and its slice-order source coordinate in the constructor doc. Either keep the rank-mismatch arm under this constructor and say so, or render "rank" when `outCoord.length != extent count`. Cheap.

## Unconfirmed
- Parity between the top-level checked scatter and the reference on `-0.0`: not probed. If the top-level checked plan copies a single write, F1 already exists at top level since S3a, and the F1 decision should cover both sites.
- `gelu(-5e-324)` producing `-0.0`: inferred from rounding, not observed. `leakyrelu` alone is enough for F1.

## Checked and clean
- **`stateCombine nm` is the old expression.** The `git diff` shows `combineFor decls nm (scanStateAlgebra denv (base ++ recur) nm).stateAgg` unchanged: same `denv`, same `base ++ recur`, keyed only on the tensor name. A name that is both a base and a recurrence destination gets the same `Combine` for allocation, base fill and step writes.
- **NaN and infinity folds are exact from `0_K`:** `0 + NaN`, `0 ± inf`, `maxNaN(-inf, NaN)` and `minNaN(+inf, NaN)` all return the written value.
- **Bool state:** I tried to get a value outside {0,1} into a predicate state with `sin` of a negative real source (probe B/B'). The base slice is already `0.0` (bits 0), both legs give `[0, 0]`, and the `∃` fold never sees a negative value.
- **Admitted programs have no collisions:**
  - Steps write `index+1` on every advancing axis. `finalizeScans` requires the full axis set and `stepWriteRowsOk` requires `.advancing i`.
  - Bases pin some advancing dimension to 0, so they never meet steps.
  - Bases are pairwise separated (`baseWritesOverlap`, using the residue rule).
  - Writes within one call are injective: `duplicateAxisInLhs`, multi-axis slots refused, and `scanScatterSourceAxes` drops zero-coefficient axes, so `S[l+1, 0*i + j]` does not iterate `i`.
- **Admitted programs have no out-of-range writes:**
  - `iterNext` stays at most `L-1`.
  - Free and strided extents come from the shared `outExtent`.
  - Pinned literals are range-checked on the checked side (`pinnedLiteralsInRange`).
- **Anti-goals:**
  - No axis-name dependence in the change. `nm` is a tensor name used for `combineFor` and the error.
  - No second extent or placement formula.
  - `rg -n -i "skip|overwrit"` on `Scan.lean` finds the docstring's "never a silent skip" and line 197. Line 197 is the pre-existing different-rank skip in `checkStatePlacements` validation, not a write. It is why the F3 hand-built rank mismatch reaches the write arm at all.
- **Out-of-range arm:** a write that used to be skipped and is now an error is reachable only by hand-built programs. Through the pipeline, negative biases are not spellable, constant scan slots are refused (`overlappingScatter`), and rank mismatches are refused (`rankMismatch`).

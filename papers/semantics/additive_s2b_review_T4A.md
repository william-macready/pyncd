# S2b T4A review (commit 79524517)

VERDICT: APPROVE (two Minor findings, no Critical/Major)

## Findings

1. Minor. `compareSortedSource` classification arm `.unavailable, _ | _, .unavailable => .nativeUnavailable` precedes the
   failure/mismatch arms (SortedDifferential.lean, the `match legacy, checked` block). A program where one leg is `mismatch` and
   the other `unavailable` reports `nativeUnavailable`, not `nativeDiscrepancy`. Loud (never parity), but the mismatch cell is
   dropped from the verdict. `unavailable` arises only when `runNative` errors (both legs) or a native leg itself is unavailable,
   so the mixed case is narrow. Order is a design choice; worth one docstring line, not a fix.
2. Minor. `compareBindings` iterates the production bindings, not the oracle cells, so coverage of declared outputs rests on
   `NativeLegs` (missing/extra/shape issues become `.error issues` -> `LegResult.failure`, NativeLegs.lean ~118-141), not on
   this function. That is sound today (checked: every missing output is an issue), but the real `compareNative` re-checks
   duplicates/desired-vs-actual structure and this one does not. Intermediates (non-input, non-output) are compared Core vs
   oracle only, never against production; same as the real harness (`outputOrigins`).
3. Note (not a defect). Confirmed gap by design: no row compares a +-inf cell against production bits.

## Questions

1. Files touched: `Source.lean` (+1 import line), new `Source/SortedDifferential.lean`, test file. `Differential.lean`,
   `NumericalProfile.lean`, `NativeLegs.lean` are absent from `git show 79524517 --stat`; real path unchanged. YES.
2. `checkSortedProfile`: `bound` starts `0`, updated `bound := bound + |q|` per finite read (sum, not product), reset per
   occurrence, checked with `checkValue site .subsetProductBound bound`. `checkValue` (NumericalProfile.lean:106-114) tests
   `den == 1` and `num.natAbs <= limit` with `limit = 2^20`, so `<=` is the intended inclusive bound, no off-by-one (the fixture
   1048576+1 -> 1048577 trips; a sum equal to 2^20 passes). Sum of |reads| bounds |occurrence value| (terms are pure read products,
   `Admission.Term.sourceReads`, no coefficients), so every finite cell <= 2^20 << 2^53; output cells additionally pass
   `checkValue .tensorCell`. Non-finite reads hit `| _ => pure ()` (skipped). `negInf/posInf` bits are `0xFFF0..`/`0x7FF0..`.
   Fiber/statement/collection bounds are intentionally absent (max/min select, add nothing). No false parity via exactness.
3. Parity requires `published = .ok .agreement` (Core vs oracle, definedOnly) AND `profile = .ok` AND `legacy = .agrees` AND
   `checked = .agrees`. Every other arm is a non-parity constructor; Core/oracle disagreement -> `referenceDiscrepancy`,
   unobserved -> `referenceDiscrepancy`, error -> `referenceUnavailable`. `.agrees` needs `compareBindings = none`, which loops
   every binding and every cell with a length check; bindings cover all declared outputs via the issue mechanism. No arm returns
   parity with a differing cell. Tensors compared: all non-input tensors (published), all outputs (native).
4. `product .max` -> `nativeDiscrepancy` with expected 4636807660098813952 (101.0) vs observed 4636737291354636288 (100.0); `product .min`
   -> 2.0 vs 1.0; `strided .max` -> `nativeFailure` with the legacy scatter-fill message. All are positive assertions of divergence,
   so a production fix flips the `#guard_msgs` loudly. Matches plan section 2 table and T4B (which later turns these into
   `knownContractDifference`). Intended design.
5. The pin uses `(-(1.0 / 0.0) : Float).toBits` and `(1.0/0.0 : Float).toBits`, independent of the source hex constants. YES.
   (Caveat: guards check only the two constants against each other's sign, which is what the plan asks.)
6. Rows: `single .sum/.max/.min` parity rows would flip if the algebra or bits changed; the product/strided rows pin exact bits;
   the 1048577 row pins origin, assignment and kind; the `compareSource` row pins `.nonSum` refusal. None vacuous. No row compares a
   +-inf cell with production bits (confirmed from the file and plan section 2); acceptable because production refuses programs
   yielding +-inf, and the pin covers the constants; residual risk is the classify path for an inf cell being untested end to end
   (`legOf`/`compareBindings` with `ExtClass.bits`), which S3b should cover when production can emit inf.

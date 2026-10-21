VERDICT: APPROVE WITH FINDINGS

# S2b whole-branch review, lens (b): regression and differential

Branch `worktree-additive-s2b-tropical-carriers` at `7be1da16`, base `main` = merge-base `82ad3df9` (32 commits).
Read-only: no lake/lean run. All claims below come from reading the code at HEAD and from `git diff main...HEAD`.

## Findings

### Critical
None.

### Major
**M1. `tropicalMultiFactor` hides divergences in output tensors declared after the condition's tensor.**
`SortedDifferential.lean:103-112` (`compareBindings`) returns at the FIRST mismatching cell over all bindings, and bindings
come in declaration order (`NativeLegs.lean:83-90`, `outputOrigins`). `confirmsSorted` (`:192-196`) confirms when both legs'
first mismatch is at the origin's declaration, and `compareSortedSource` (`:255-256`) then classifies the whole run as
`knownContractDifference` before it looks at either leg's result. So when the multi-factor tensor is declared first, no
later output is ever compared.
Concrete input: `snap2 [a] [a] [multiY, bareV]` (`SourceSortedDifferentialTest.lean:194`, Y = decl 6 multi-factor, V = decl 7
single-factor). Any production error in `V` is never compared, and the result is still `multiFactor (some 6)`.
The docstring at `:159-161` says "an unrelated native divergence stays `nativeDiscrepancy`/`nativeFailure`", which is false
for this case. The record (§5, T4B paragraph) admits only same-tensor and two-multi-factor-output cases. The plan's T4B
reviewer lens (`additive_s2b_plan.md:371-372`) asked for "a fixture with the condition's shape AND an unrelated mismatch",
and none exists. `!multi 6` (`:244`) checks the reverse direction.
Fix (small, ~1 dispatch): have `compareBindings` return the first mismatch per binding. Confirm `tropicalMultiFactor` only
when every mismatching declaration is the origin of a detected multi-factor condition (or at least only when the origin's
binding is the ONLY mismatching one). Then add a guard that drives `confirmsSorted` with an extra hand-built mismatch on
another declaration. The alternative is to weaken the docstring and record the masking as S2a records
`scatterExtentOverridesDeclared` (`Differential.lean:182-185`). That choice belongs to the user (Rule 7/14).

### Minor
**m1. Head-only confirmation gives a false `nativeDiscrepancy` when statement order differs from declaration order.**
`compareSortedSource` `:243-246` confirms only `detectSortedConditions`' head, which is in statement order. The first mismatch
is in declaration order. Input: `snap2 [a] [a] [multiV, multiY]`. The head is `multiFactor` at decl 7, but the first mismatch
is at Y (decl 6), so the run is `nativeDiscrepancy`, although both tensors are known differences. This fails loud, not by
masking. The M1 fix covers it.
**m2. The real carrier in the sorted harness uses the tropical envelope.** `checkSortedProfile` (`:68-92`) bounds only
Σ|read| per occurrence and output cells, while `compareSource` bounds Π max(1,|read|) plus fiber, statement and collection
sums (`NumericalProfile.lean:196-203`). A sum program selected as `real` through `compareSortedSource` with a 3-factor term
of reads ~1000 passes here but is `unsupportedNumericalProfile` in the real harness. The two harnesses classify the same
real program differently. The effect is only ever a false alarm, never a mask: an inexact f64 shows as a mismatch.
Document that `compareSortedSource` is not the real program's harness, or apply the real envelope when `S.name = "real"`.
**m3. `legOf` (`:143-155`) reports an OBSERVED leg as `.unavailable` when the profile errors.** Classification
short-circuits on `unsupportedNumericalProfile` first, so the result is unaffected, but the rendered `SortedRun.legacy/checked`
misstates what the leg did. This is display-only.
**m4. Public lemmas removed from `Schedule.lean`.** `sourceValuations_nodup/_complete`, `sourceOccurrences_nodup/_complete` and
`sourceOccurrenceKeys`/`sourcePublicationKeys` with their `_nodup`/`_complete` lemmas are gone; only their `...At` forms
remain. I grepped `leanncd/` and `papers/` and found no references, so this is not a regression, only an API narrowing not
mentioned in the record.

## Checks

1. **Fixtures not edited or weakened: PASS.** `git diff main...HEAD --numstat -- leanncd/test` shows 3 new files
   (`SourceOracleCarrierTest` +188, `SourceSortedDifferentialTest` +247, `SourceSortedAuditTest` +104), 0 deleted lines, no
   M/D/R entries. The `LeanNCD/` diff has no added or removed `#guard`, `#guard_msgs`, `info:`, `-- =>` or `example` lines.
   The only test-relevant type changes are defaulted parameters (`TensorObservation (V := ℚ)`, `ComparisonCause`,
   `TensorDifference`, `Oracle.Result (K := ℚ)`, ...). Derived `Repr` does not print type arguments, so existing
   `#guard_msgs` renderings stay identical. `Oracle.run` became `runWith Carrier.real` with `ofRat = id`, and Mathlib's ℚ
   semiring has the same ops, so values are unchanged.
2. **Loud `nonSum` refusals: PASS.** `Admission.lean:662` (`admitStatement`) and `:882` (`admitAffineWrite`) are untouched.
   The branch changes nothing above line 899. `admitSource` (`:752`) is unchanged. `admitSourceAffine` gains
   `(sorted : Bool := false)` (`:922`). `compareSource` -> `sourceDebugAffine` -> `admitSourceAffine` uses the default.
   Pinned by `SourceSortedDifferentialTest.lean:114-117` (bare, site 1) and `SourceSortedAuditTest.lean:71-72` (affine,
   site 2). The raw default is still pinned at `SourceAdmissionAcceptanceTest.lean:212`.
3. **`sorted` flag: PASS.** It is read only at `Admission.lean:910` (`if sorted then ... else rhs`) and `:913`
   (`sorted && ...`), and both are the identity when it is `false`. Call sites: `NativeLegs.runNative` (default false;
   its only real caller is `Differential.lean:464`, which uses the default), `Provenance.lean:80`, `Observation.lean`
   (`sourceDebugAffine`), and `SortedDifferential.lean:229` (`true`). `admitSourceSorted` passes `true`. The new
   `NativeSource.sorted` field is read nowhere except to type `admission`. The `.scatter` arm does not rewrite `rhs`, so with
   `sorted := true` a tropical scatter is refused either way (`scatterPolicy`, or `nonSum` if the guard were dropped). A sum
   program through the sorted entry is admitted unchanged (audit row 10).
4. **§3 starred rows: PASS.** Each one is reasoned against the arm's removal:
   row 3 (`SourceOracleCarrierTest:132`): without `| [_], ts =>` the key falls to `mixedSorts [sum]` and the guard fails.
   Row 4 (`:134`): table `[]` -> `noCarrier`. Row 5 (`:135`): without `| [], _ =>` the empty key list gives `mixedSorts []`
   and the guard fails.
   Row 7 (`SourceSortedAuditTest:56`): without the `sorted && agg != sum` disjunct the max scatter reaches
   `admitAffineWrite` -> `nonSum`, and selecting before admission would give `sortSelection`; either makes `isPolicy` false.
   Row 9 (`:62-63`): the bare scatter -> `admitStatement` -> `nonSum` and the guard fails. Row 10 (`:67`): an over-refusing
   flag makes `selected` "refused ..." and the guard fails. Row 13 (`:71-72`): without `:882` the strided max is admitted and
   `causeIs` returns false.
   Unstarred rows 1, 2, 6, 8, 11, 12 and 14 point at existing rows (`SourceSortedDifferentialTest:74-81, 91-93`;
   `SourceOracleCarrierTest:123-128`).
5. **Sorted differential: FINDINGS (M1, m1-m3).** `tropicalScatterFill` cannot hide value divergences, because both legs fail
   before any output exists. It is bound to the owner on both legs (`:197-209`) and pinned by `:228-233`.
   `compareBindings` coverage is sound: `observeBindings` (`NativeLegs.lean:116-141`) refuses missing, extra or misshaped
   outputs, and `compareBindings` re-checks per-binding cell count (`:107-108`).
   The classification order (published, then profile, then confirmed condition, then legs) matches the real harness.
   `.unavailable` takes precedence over `.failure`, as in `Differential.lean:351-352`; both legs share `availableInputs`.
   A `runNative` `.error` cannot occur after `admitSourceSorted` succeeds, because both make the same `admitSourceAffine ...
   true` call.
6. **`Differential.lean`: PASS.** `nonBareWrite`/`ownedBy` changed only from private to public; their bodies are unchanged
   and nothing clashes with them (`Observation.lean:275` is a constructor, used only by dot-notation). The new
   `confirms` arm `| .tropicalMultiFactor _ | .tropicalScatterFill _ => false` cannot be reached on the real path:
   `detectConditions` (`:217-241`) never builds those constructors, and `NumericalProfile` throws only `usedDType`
   structurally. `elaborateSource` changing from `def` to `abbrev` changes reducibility only, not computed values.
7. **Imports: PASS.** `LeanNCD.lean:156` imports `Semantics`, `Semantics.lean:7` imports `Source`, and `Source.lean` imports
   `SortedDifferential`, which imports `Differential`. `Carrier` is reached through `Adapter`, `Oracle` and `Schedule`.
   `Carrier` imports only `DSL.Ast` and Mathlib, and `DSL/` imports nothing from `Semantics`, so there is no cycle.
   `lakefile.toml` `Tests.globs` gains all 3 new modules. `LeanNCD` is built from its root import, so the new modules need
   no lakefile entry.
8. **Mutation manifest: PASS.** 18 entries. Every `old` string occurs exactly once in its file (checked with a script).
   Every `expect` resolves to a `#guard` or `#guard_msgs` line in the HEAD test files. For each cycle I traced the kill
   mechanism, and every listed line fails for the intended reason:
   - T2-M1/M3 change the carrier or refusal of 71/73/75.
   - T2-M2 turns 56/62/63/80 into `nonSum`.
   - T3-M1/M2 change the Core values; 105 becomes `referenceDiscrepancy`.
   - T4-M1: the bound stays 0, so 111 trips `tensorCell` instead.
   - T4-M3 kills only 244; 245 survives through `_, _ => false`.
   - T4-M4/M5/M6 kill 230-233, 232 and 233 respectively, as their labels say.
   Expect matching is by substring (`mutation-manifest.sh:185`), and no expect string is a substring of another line's
   locator. T3-M1 and T3-M3 share old/new strings but target different modules, which is intended.

# S2a T2 review (commit 8cbdacb1), lens: refusal completeness

Read only via `git show 8cbdacb1` (Admission.lean, Adapter.lean, SourceAdmissionAffineTest.lean). Nothing built.

## Findings

- **Major (test gap, impl correct by reading): no guard exercises a NEGATIVE image or a mixed-sign form.**
  Location: `SourceAdmissionAffineTest`, all 28 guards; code: `formFits` (`decide (0 ≤ writeValue f v) && ...`).
  Evidence: every form in the file uses constants {0,1,2,3} and coefficients {1,2}; `.shift a 1`, `.scale 2 a`,
  `.const 2/3`, `.affine 0 [(1,a),(1,b)]`, `.shift a 0`, `.scale 1 a`. Every `writeOutOfRange` guard fails the UPPER bound.
  Why it matters: deleting the `0 ≤` conjunct (a negative image such as `Y[a-1]` would then become `Int.toNat` 0 in
  `fitIndex`, silently aliasing a negative write onto cell 0) leaves all 28 guards green; likewise a corner-only
  enumeration replacing `coordAll` passes every fixture because all coefficients are non-negative (max at the far corner).
  Fix: add `Y[a-1]` (`.shift a (-1)`) refused at slot 0 with a large `k`, neighbour `.shift a 0`/`Y[a]` admitted;
  add `.affine 0 [(1,a),(-1,b)]` (min at corner (0, max)) refused, neighbour `.affine 1 [(1,a),(-1,b)]`-style admitted.

- **Major (test gap): scatter policy is not tested on a BARE-slot scatter.**
  Location: `admitAffineStatement` `.scatter` arm; guards (d).
  Evidence: the four `scatterPolicy` refusals all use `scatter opts = snap 3 [k] (.scatter "Y" [.affine (.scale 2 a)] ...)`;
  the only bare-slot scatter guard is the ADMITTED `{ reduce := .sum }` one. The code checks policy first
  (`if opts.fill != 0 || !(opts.reduce == .sum || ...) then .error ... else if slots.all isFree then admitStatement ...`),
  which is correct, but a mutant that moved the policy test inside the non-bare branch (bare `.scatter "Y" [.free a] ... {reduce := .max}`
  then admitted as `.assign`) passes every committed guard. Answers Q4: implementation OK, evidence missing.
  Fix: one guard `.scatter "Y" [.free a] readX { reduce := .max }` refused `scatterPolicy` and one with `fill := 1`.

- **Major (test gap): `.freeNorm` and scan slots under the NEW entry have no guard.**
  Location: private `outputForms` (second copy of `outputIndices`), `admitAffineWrite`.
  Evidence: `rg admitSourceAffine` over `leanncd` hits only `SourceAdmissionAffineTest`; that file contains no `.freeNorm`, `.iterAt`, `.iterNext`.
  The existing `.marked`/`.scanSlot` guards (`SourceAdmissionAcceptanceTest` lines ~172, ~176) call `admitSource`, i.e. `outputIndices`, not `outputForms`.
  Code reading: `.freeNorm _ => throw ... (.unsupported .marked)` and `.iterAt .. | .iterNext _ => throw ... (.unsupported .scanSlot)`
  are present and run BEFORE `admitAffineOutput` (so a scan slot cannot be masked by `writeOutOfRange`). Also `.iter` declarations die earlier in `checkAxes`.
  Why it matters: Q3 is satisfied by the code but is one deleted match arm (or a `| _ => pure (.single ...)` wildcard) from silently
  admitting a scan/marked slot as a plain write; nothing would notice. Fix: guards `[.affine (.shift a 0), .freeNorm a]`-style
  (marked) and `[.free a, .iterNext l]` (scanSlot) under `admitSourceAffine`, each with an admitted neighbour (`.free`).

- **Minor (test gap): statement-level refusals duplicated in `admitAffineWrite` are unexercised under the new entry.**
  Evidence: `admitAffineWrite` copies `nonSum`, `nonIdentity`, `undeclaredTensor`, `role .input` checks from `admitStatement`
  (SourceRawCorrespondenceTest lines ~100/133/135 test them only through `admitSource`). Drift risk between the two copies; no guard on the new copy.

- **Minor (test gap): zero-support write and zero-extent behaviour unexercised.**
  `Y[2] := sum_a X[a]` (all `.const`, `formsSupport = []`, `shape = []`, `coordAll [] p = p ()`) is a distinct path
  (empty `outputContext`, all axes contracted); fixture `Y[2, a]` has support `[a]`. Code appears total, so low risk.

- **Question: asymmetry on `.free` slots in a mixed write.**
  Location: `outputForms` `.free a => ... pure (.single a.uid)`; `admitOutput` (bare path) vs `admitAffineOutput`.
  Evidence: bare path calls `resolveSourceSlots ... (σ.signature dst).axes ids`, refusing a slot whose axis uid/extent differs from the
  destination axis (`.domain`); the affine path only range-checks the value, so `Y[a, a+1]` into `Y` over `[k, k']` with `|k| >= |a|` is admitted
  while `Y[a, b]` (all free) into the same `Y` is refused `domain`. Not unsound (refusal direction is the conservative one and the admitted
  output is well formed), but a refusal-completeness reader should know the all-free and mixed paths disagree. Presumably intended (scatter semantics).

- **Question / known: policy is dropped after admission; contracted-axis `rejectCollisions` is not detected.**
  `AdmittedStatement`/`AdmittedOutput` carry no scatter options, so `rejectCollisions` and `sum` are indistinguishable downstream.
  Plan line 177 (review F11) already records bare-slot `rejectCollisions` with a contracted axis as parked (~1 dispatch); not a T2 defect, noted for completeness.

- **Minor: no AxiomAudit coverage in this commit** for the new theorems (`coordAll_spec`, `admitOutput_formsSpec`,
  `admitAffineOutput_formsSpec`, `AdmittedOutput.formsSpec_of_forms`); commit does not touch `AxiomAudit`. Check T-later or the plan's final audit owns it.

## Answers to the lens questions

1. Well-formedness of `admitSourceAffine` outputs: no hole found. `shape = supportShape source ids` with `ids = formsSupport forms`
   (`firstUIDs`, nodup); `supportShape_uids` ties `shape` uids to `indices`; every form uid is in `ids` (`mem_formsSupport`) and was
   checked bound via `sourceAxis` over `idxAxes` (which matches `idxAffineForm`'s uid set for all five `IdxExpr` cases), so
   `supportShape`'s `getD 0` is unreachable. `dest` is total because `coordAll_spec` discharges `formsFit` for every support coordinate;
   `admitAffineOutput_formsSpec` proves `FormsSpec`. Non-bare outputs are not `IsBare`, so raw-chain theorems excluded by design (`admitSource` unchanged).
2. Image check: `coordAll` enumerates the whole support box (`List.finRange a.extent` per axis, recursively), `formsFit` conjoins every
   destination slot, `formFits` checks both `0 ≤` and `< extent`. Exhaustive in code; the lower bound and mixed signs are NOT evidenced by fixtures (Major above).
3. `.freeNorm` refused `.marked` and scan slots `.scanSlot` in `outputForms` before any range check; affine READ refused via unchanged
   `readIndices` (`.const/.scale/.shift/.affine` -> `.unsupported .affine`) under both entries. Code OK; `.freeNorm`/scan unguarded under new entry (Major above); affine READ guarded under both.
4. Policy checked first for every `.scatter` (bare or not) before slot dispatch: yes in code; bare-slot refusal unguarded (Major above).
5. Accept-neighbours: all `writeOutOfRange` refusals (shift/scale/const/a+b/slot-1), the four policy refusals (neighbours `sum`, `rejectCollisions`,
   default fill), the affine-READ refusals (neighbour `readX` fixtures) and the two rank refusals (neighbour `Y[2*a]` matching rank / `Y[2,a]`)
   each have one. `admitSource` refusals have pre-existing accept-neighbours. Refusal guards lacking a neighbour for their dimension:
   none lacks one outright; missing are whole dimensions (negative images, bare-slot policy, marked/scan) listed above.
6. No `sorry`, `axiom`, `native_decide`, `unsafe`, `partial`, `implemented_by`, `ofReduceBool` in Admission.lean, Adapter.lean or the new test (rg over the commit).
   Count check: the test file has exactly 28 `#guard`.

## Verdict

ACCEPT WITH CHANGES: implementation is sound on all six questions by reading, but three refusal dimensions (negative/mixed-sign images,
bare-slot scatter policy, `.freeNorm`/scan under the new entry) have no guard, so a mutant could pass; add about 6 guards (~1 small dispatch).

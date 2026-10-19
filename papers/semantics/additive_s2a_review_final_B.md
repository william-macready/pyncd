# S2a final whole-branch review, lens (b): regression / differential

Branch tip 42013f71, base 6fad5161. Code read only via `git show 42013f71:` / `git diff 6fad5161 42013f71`.

## Findings

- (check 1, no finding) Pre-existing tests: `git diff --stat 6fad5161 42013f71 -- leanncd/test` touches four new files and
  `SourceRawCorrespondenceTest.lean` only; that file's diff is exactly the forced `DonorOutputConnection` line pair
  (`statement.output.sourceSlots.project ...` wrapped in `statement.output.dest (...)`). No other existing test edited.
  `lakefile.toml` only adds the four new modules to the `Tests` globs.

- **Minor (docs vs code)**, plan §2 bullet "New test modules": "the single forced edit is two lines in
  `SourceRawCorrespondenceTest` (T1: the conjunct now takes `.1`)". The shipped edit in `DonorOutputConnection` takes
  no `.1`; it wraps the projection: `Coord.raw (statement.output.dest (statement.output.sourceSlots.project ...))`.
  Matters only because a reader verifying the "no semantic test edit" claim from the plan would be looking for the
  wrong change. Fix: reword the parenthetical.

- (check 2, no finding) `compareSource` via `sourceDebugAffine` -> `admitIdentifiedSourceAffine` -> `admitSourceAffine`.
  Refusal walk: `admitAffineStatement` sends every `.assign` whose slots are all `.free` (including `[]`) and every
  non-assign/non-scatter statement to the unchanged `admitStatement`, so on every base-accepted program (which contains
  no scatter and no affine LHS) admission is the identical computation. For an `.assign` with a `.freeNorm`/scan slot
  and NO affine slot, `admitAffineWrite` checks nonSum, nonIdentity, undeclaredTensor, role in the same order as
  `admitStatement`, then `outputForms` raises the same cause at the same slot as `outputIndices` (first failing slot,
  `marked`/`scanSlot`/`sourceAxis`). Only programs with an affine LHS slot (cause can move, e.g. `[.affine, .freeNorm]`
  now blames slot 1 `marked`) or a scatter (any statement) change outcome: the two exempt classes. The runtime `Nodup`
  branch of `admitIdentifiedSourceAffine` is unreachable on adapted sources. Downstream on bare rows: `Oracle.destination`
  with `forms = indices.map single` gives the old coordinate (range check passes because admission's domain check fixes
  source extent = destination extent); `normalizeOracleContribution`'s new `nonBareWrite` guard passes;
  `OracleRow.occurrences = occurrence.toList` so `oracleContributions`' `flatMap` equals the old `filterMap`;
  `checkFiber`'s `bare` branch is the old code; `detectConditions` emits nothing (every condition requires
  `nonBareWrite`, false for `admitOutput`'s `forms = ids.map single`, `indices = ids`, diagonals included), so
  `classification`'s new head-condition step is skipped. `runNative`'s switch to `admitSourceAffine` is identical on the
  same programs. Existing differential corpus (`SourceDifferentialCorpusTest`, F16-F18) is bare-only. No regression
  path found.

- (check 3, no finding beyond the known items) `confirms` per condition at the tip:
  `scatterCollisionRejected` needs legacy `.failure` with `.scatterCollision nm` and `ownedBy native origin.declaration nm`
  (name AND declaration) AND checked runtime `scatterCollision` (cause-only, documented) or a preparation
  `multiAxisScatterLhs`/`scatterOrAffineLhs` whose context head before `": "` is owned; `multiWriterScatter` needs
  compile-phase `scanAxisNotIter` on legacy (string) and `sourceCompilation (.scanAxisNotIter _)` on checked (cause-only,
  documented); `scatterExtentOverridesDeclared` needs BOTH legs `.observed` with a NONEMPTY issue list whose every issue
  is `.shape`/`.length` on the condition's declaration with `actual == derived`. So the extent condition cannot fire
  without shape issues on both legs; any unavailable/failed leg makes every `confirms` false and falls through to
  `nativeUnavailable`/`nativeFailure`. Every confirmed condition replaces only an outcome in which no value of the
  program is observable (native failure, or the documented binding-issue case), so no confirmed condition hides an
  observed VALUE divergence other than the documented extent case. T4-08 same-kind/different-origin: `fOriginL`
  (legacy `evalScatter Z: collision` is rejected by `ownedBy` for Y's declaration 5) and `fOriginC` (checked context
  `"Z: constant affine LHS slot"` rejected) both fall to `nativeFailure`, with accept-neighbours `known:collision`; the
  neighbours also carry an unconfirmed extent condition for Y (`|k| = 6` vs derived 7) behind the collision head, which
  is harmless. `fMask`: Y and Z both detected (Z's constant slot collides and has an extent mismatch); head is Y, legacy
  fails at compilation, so `nativeFailure`. Detection/confirmation residuals (F9, F11, head-only, cause-only legs) all
  appear in plan §2.

- (check 4, no finding) Recomputed from the test text (`X = [1,2,3,4]`, `W = [1,10,100]`): `fD` `Y[a+b]`, `|k| = 7`:
  cells 1; 2+10=12; 3+20+100=123; 4+30+200=234; 40+300=340; 400; 0. `fD'` `Y[3]`, `|k| = 4`: 1+2+3+4=10 at cell 3.
  `fN` `Y[a+4b]`, `|k| = 16` (production-derived 4+12=16, so no binding issue): 1..4, 10..40, 100..400, four zeros.
  `fN'` `Y[2a]`, `|k| = 8`: 1,0,2,0,3,0,4,0. All match the guards. The guards can fail: `legacyCells`/`oracleCells`
  return `none` unless the leg is observed and binds declaration 5, `legacyMatchesOracle` requires a nonempty list,
  bit equality and `legacyComparison = .compared (.ok .agreement)`; a last-write-wins legacy makes `fD'` 4 and `fD`
  cell 1 = 10, failing 235/237/239/241 and not the collision-free neighbours (matches the plan's A2-M3 account).
  `fD`/`fD'` derived extents (7, 4) equal the declared ones, so they are not accidentally under the extent condition.
  The tamper pair `dropOccurrence` (`occurrences 3 2`) is consistent with `fE` cell 0 having a=0, b in {0,1,2}.

- (check 5, no finding) `Provenance.admitIdentifiedSourceAffine` matches its §3 row (runtime `Nodup`, misleading
  `.duplicateTensor "statement originals not unique"`); `NativeSource.admission : admitSourceAffine snapshot = .ok
  admitted` is consumed only to build `NativeSource` in `runNative` (no library proof uses it). `rg` of
  `output\.(indices|shape|slots|forms|dest|sourceSlots)` over `Source/*.lean` at the tip finds consumers only in
  Admission, Statement, Fiber, Correspondence, ProgramCorrespondence, RawCorrespondence, RawSemanticConnection, Oracle,
  Observation, NumericalProfile, Differential: all covered by a §3 row (Observation's extra hit is a docstring).
  Nothing outside `Source/` consumes `AdmittedOutput`.

- **Minor (docs: stale `File.lean:NNN` in an S2a-edited line)**, `papers/semantics/additive_production_decision_note.md`
  §E table, row S2: the slice appended its status to the row but left "(Admission.lean:462 refuses scatter today)". At
  the tip line 462 is inside `admitOutput`; the scatter refusal is `admitStatement`'s `.scatter` arm, and it is now true
  only of the default entry (`admitSourceAffine` admits policy-checked scatter). Plan T5: "No `File.lean:NNN` in any
  shipped text; cite identifiers." Fix: replace with "`admitStatement` refuses scatter (default entry)".

- **Minor (docs overstate condition precision)**, `leanncd/LeanNCD/Semantics/AGENTS.md` ("A condition is confirmed only
  when the native legs show exactly the predicted outcome") and `lean_executable_semantics_path.md` additive bullet
  ("only when both native legs show exactly the predicted outcome"); `tensor_logic_semantic_gap_audit.md` S2a paragraph
  ("the differential classifies the production contract differences as structural conditions"). In code the checked
  runtime collision and both `multiWriterScatter` legs are cause-only, only the head condition is tried, and the F11
  divergence (`fF11`) plus the capability refusals of `fD`/`fD'` classify `nativeFailure` with no condition. These
  limitations are recorded in plan §2 and in `Differential.lean`'s section docstring, but the two
  discoverability documents do not point to them, so "exactly" and "the differences" read as complete. Also the node
  describes `multiWriterScatter` as "a scatter among several writers", while detection is any tensor with two or more
  writers of which one is non-bare (`fG` is two affine `.assign`s, no `.scatter`). This reports the wording only; the
  code limitations themselves are known. Fix: add "(two legs are cause-only and only the first condition is tried;
  see plan §2)" and "non-bare write" in place of "scatter".

## Verdict

APPROVE (lens b): 0 Critical, 0 Major, 3 Minor (all documentation). No regression path for base-compared programs, no
undocumented masking, and the legacy-vs-oracle collision guards are correct and able to fail.

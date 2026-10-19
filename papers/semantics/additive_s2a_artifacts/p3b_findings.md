# S2a P3b findings

Branch `proto-s2a-p3` (continues P3). Commits: 7aebc2dd (count check + conditions), ff7a2172 (guards,
masking negative, tamper fixture, stage ordering), plus the close-out commit (redundant phase check removed,
docs). Patches: `p3_patches/` (continued numbering).

**Budget breach (fail loud).** About 80 harness tool calls against a budget of ~55 (stop point 40 was
passed): roughly 15 of them were polling the 25-minute full `Tests` build and the mutation batch. Context
peak under 200k. All deliverables were finished; the budget was NOT respected.

## Per-file change

| File | Change |
|---|---|
| leanncd/LeanNCD/Semantics/Source/NumericalProfile.lean | `checkFiber`: occurrence-count check RESTORED for non-bare rows (enumerate `Oracle.coordinates` of the support axes, count assignments whose `formsAt` image equals the cell; a negative image never matches); 3 new `StructuralCondition` arms |
| leanncd/LeanNCD/Semantics/Source/Differential.lean | `nonBareWrite`, `rejectsCollisions`, `writeCollides`, `derivedShape`, `detectConditions`, `legacyCollision`, `legacyCompile`, `checkedCollision`, `shapeOnly`, `confirms`; `ComparisonRun.conditions` (last field, default `[]`, set by `compareSource`); `classification` consults the head condition after the native legs |
| leanncd/test/Semantics/SourceDifferentialScatterTest.lean | scaffold `#eval`s replaced by 17 `#guard`s + tamper guards (+118 lines) |

`renderSourceComparison`/`renderComparisonRun` use derived `Repr`, so the new arms need no render change
(build confirmed). Renderer does not print `conditions` (not added: not requested).

## Observed table

See `p3_observed.md` (full per-leg table, 17 rows). Headline: (a)(b)(c) parity; (d)/(d') legacy sums like the
oracle but the CHECKED plan refuses multi-axis and constant affine slots by capability; (e)/(f) production
collides (legacy `evalScatter` collision, checked runtime `scatterCollision` or capability refusal); (g)
refuses at COMPILE with `scanAxisNotIter "a"`, NOT a `multiWriterScatter`; (h6) oracle `writeOutOfRange`;
(h9) both native legs value with shape issues 9 vs 8; (i) constant slot under assign fails at compile
with `overlappingScatter` whatever the RHS (P0's scan error did not reproduce; cause undetermined).

## Conditions (source-only detection, native-confirmed)

* `scatterCollisionRejected origin`: non-bare write, original statement is `.assign` or `.scatter` with
  `reduce = rejectCollisions`, and two distinct assignments of the support axes (form uids plus every
  term's read indices, so a contracted axis counts) share a destination image. Confirmed iff legacy is a
  `scatterCollision` failure AND checked is runtime `scatterCollision` OR a preparation `capability` refusal
  (the checked plan refuses multi-axis/constant slots before reaching the collision).
* `multiWriterScatter declaration`: a declaration written by >= 2 statements with at least one non-bare
  write. Confirmed iff legacy fails in COMPILATION mentioning `scanAxisNotIter` AND checked is
  `sourceCompilation (scanAxisNotIter _)`.
* `scatterExtentOverridesDeclared origin declaration derived`: single-writer non-bare write whose declared
  shape differs from `derivedShape` (`c0 + sum coef*extent`, `c0+1` for a constant; inferred from the
  observations, enforced by the confirm check). Confirmed iff BOTH native legs are observed with binding
  issues that are all `shape`/`length` issues of that declaration whose actual shape equals `derived`.
* Conditions are ordered by pipeline stage (multi-writer: compile, collision: evaluation, extent: output
  binding) and only the head is confirmed: a later-stage condition cannot be observed once an earlier one
  fires (fixture F detects collision AND extent; evaluation fails before binding).
* Correction to the brief: the `usedDType` path does NOT check the native outcome. It is decided in
  `checkRunProfile` before any native leg is read. The new conditions are stricter (decided after the
  native legs and only when `confirms` holds). Consequence: `usedDType` can still mask a native
  divergence; flagged, not changed.
* Masking negative `fMask` (guard at line 151): `Y[2*a] := X[a]*W[b]` (collision, condition detected) plus
  `Z[3] := X[a]` (constant slot, legacy compile `overlappingScatter`): legacy fails in COMPILATION, not
  with the predicted collision, so classification stays `nativeFailure`. Mutation M4 kills a bypassed
  post-check at it (and at 140, 147, 148).

## Fixtures (file lines of `SourceDifferentialScatterTest.lean`; donor `SourceOracleAffineTest.snap`)

Defs 106-128 (fA fB fC fD fD' fE fF fF' fG fH6 fH9 fI1 fI2 fMask); guards: A 130, B 131, C 132, D 134, D'
135, E 137, F 138, F' 140 (non-colliding neighbour of F), G 142, single-writer neighbour of G 143, H9 144,
H6 145 (refusal), I1 147, I2 148, mask 151, `dropOccurrence false` 182, `dropOccurrence true` 183 (tamper:
one occurrence of a fiber dropped, all sums consistent, expect `occurrences 3 2`). Line numbers read from
`rg -n "^#guard"` on the final file. Accept-neighbours: E vs A (one RHS factor), F vs F' (b coefficient 1 to
4), G vs single writer, H9 vs A (declared 9 to 8).

## Mutation cycles (`p3_mutations_draft.json`, task T4, target `Semantics.SourceDifferentialScatterTest`)

| cycle | outcome | failing guards |
|---|---|---|
| M1 collision predicate inverted | killed | 137, 138, 144 |
| M2 multi-writer detection removed | killed | 142 |
| M3 extent condition removed | killed | 144 |
| M4 native-outcome post-check removed | killed | 140, 147, 148, 151 (masking negative) |
| M5 restored count check removed | killed | 183 (tamper) |
| M6 `oracleOccurrences` to `[]` | killed | 10 lines printed (130-144): possibly truncated |
| M7 legacy `phase == scheduledEvaluation` check removed | SURVIVED | none |

M7 is an equivalent mutant: `scatterCollision` is only raised during evaluation, so the phase test was
redundant with the constructor match. I removed the redundant check from `legacyCollision` instead of
adding a fixture (it cannot be distinguished). M7 is not in the manifest (the manifest requires killed
mutants). Restore hashes verified by `mutation-cycle.sh` (restore_hash_exit=0, restored_build_exit=0).

## Builds

* `LeanNCD.Semantics.Source.Differential`: 8553 jobs, green (twice).
* `Semantics.SourceDifferentialScatterTest`: 8558 jobs, green (all guards).
* Full `LeanNCD Tests` after the final code state (with M7's removal): 8818 jobs, "Build completed
  successfully" (baseline 8818: unchanged job count, no existing test edited). `Semantics.AxiomAudit`
  prints only `propext`, `Classical.choice`, `Quot.sound`; grep for `sorryAx`/`ofReduceBool`/`^error`
  over the whole log finds nothing.

## Not done / caveats

* `Provenance.admitIdentifiedSourceAffine` still reports a misleading `.duplicateTensor "statement
  originals not unique"` on an unreachable branch: `SourceCause` has no accurate constructor; adding one
  means editing `Adapter.lean` and its renderers (not a one-line change), so only reported.
* The checked plan's capability refusals of multi-axis/constant affine slots ((d), (d'), (f)) are not
  conditions: observed, decidable, not requested; with them no scatter-sum collision fixture reaches
  four-leg parity (legacy-only agreement).
* `multiWriterScatter` encodes the single observed pair (`scanAxisNotIter` on both legs); other
  multi-writer shapes (e.g. two hand-built scatters) were not run.
* p3_observed.md line 30 table row has extra pipe cells flagged by the markdown linter (cosmetic).

# S2a P3 findings (INCOMPLETE: stopped at the tool-call limit)

Branch `proto-s2a-p3` from `proto-s2a-p2b` (b4adbfe0). Harness tool calls: about 57 (budget 60, stop
point 45 was passed while reading code before the first edit; the count is an estimate).
Context peak under 250k.

## Done (compiles)

Code commit "differential reads oracle occurrences for non-bare rows; compareSource uses affine
admission". Single target `LeanNCD.Semantics.Source.Differential` built green (8553 jobs).

| File | Change |
|---|---|
| Observation.lean | `OracleRow` gains `occurrences : List ContributionObservation` (bare = `occurrence.toList`); `normalizeOracleContribution` sets it; new `normalizeOracleRow` (bare: unchanged; `nonBareWrite`: `occurrence := none`, `occurrences := oracleOccurrences`); `normalizeOracle` maps `normalizeOracleRow`; `sourceDebug` refactored into `sourceDebugFrom` + `sourceDebug` (default entry, unchanged behaviour) + `sourceDebugAffine` |
| Provenance.lean | `admitIdentifiedSourceAffine`: `admitSourceAffine` plus a RUNTIME `Nodup` check of statement originals (the proof needs the private `admitAffineWrite`; the failing branch is unreachable but unproved and reports `.duplicateTensor`, a misleading cause: flagged) |
| Diagnostics.lean | `oracleContributions` uses `flatMap (·.occurrences)` (was `filterMap (·.occurrence)`: identical on bare rows) |
| NumericalProfile.lean | `checkFiber`: `bare` guard; non-bare rows use the forms' uids as support, `formsAt` (new, evaluates write forms over the occurrence assignment) for the destination check, and SKIP the per-fiber occurrence-count check (no closed form; collection sums are still checked in `checkOracle`). GAP: a missing oracle occurrence of a non-bare fiber is not caught by the profile |
| Differential.lean | `compareSource` calls `sourceDebugAffine` (the reference leg previously refused every affine/scatter statement at the default admission) |

Observation test scaffold `test/Semantics/SourceDifferentialScatterTest.lean` (registered in
lakefile.toml after `SourceDifferentialPolicyTest`) has the snapshot helper (donor:
`SourceOracleAffineTest.snap`), `observe` and three `#eval`s. It has NO `#guard` yet.

## Observed (see p3_observed.md)

(a) and (b), non-colliding affine writes whose declared extent equals the derived extent, reach
`fourLegParity` on all four legs through the new pipeline (oracleOccurrences + profile + both native
legs). This is the first end-to-end evidence that the switch works.

## NOT done (fail loud)

- Steps 2 (rest of the observed table: c, d, e, f, g, h9, i; h6 output unread), 3 (no structural
  condition added, `StructuralCondition` still has only `usedDType`; no masking-negative fixture),
  4 (no guards; final line numbers undefined), 5 (NO mutation cycles run; no
  p3_mutations_draft.json), the full `LeanNCD Tests` build (NOT run, so "existing tests green with
  no edits" is UNVERIFIED; risks: `OracleRow` is constructed only in Observation.lean, and the
  `compareSource` switch could change a refusal expected by an existing test: tests with
  `compareSource` calls were checked for `.affine`/`.scatter` only in Policy/Fixtures/Geometry and
  SourceDiagnosticAdmissionTest, none found).
- The `observe` `#eval`s must be replaced by `#guard`s before this is a test.
- Axiom audit not run.

## To resume

1. Add the remaining fixtures to the `#eval` list, record outcomes in p3_observed.md (a hand-built
   scatter is `.scatter "Y" slots rhs { reduce := .sum }`).
2. Add conditions only for observed, source-predictable divergences, with a native-outcome post-check
   and a masking negative.
3. `#guard`s, mutation cycles (target `Semantics.SourceDifferentialScatterTest`), one full `Tests`.

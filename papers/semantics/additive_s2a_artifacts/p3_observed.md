# S2a P3/P3b observed outcomes

Produced by `SourceDifferentialScatterTest.observe` / `tag` (`compareSource s (some [5])`) after the
differential was switched to `oracleOccurrences` / affine admission. Inputs `X=[1,2,3,4]`,
`W=[1,10,100]` (`W=[5]` when `|b|=1`). `Y` is declared over `k` (or the axes named); the oracle's shape is
the DECLARED extent, production derives its own from the write forms. Everything below is read off the
tool output, not predicted. "raw" is the classification with no structural condition; "final" is what
`compareSource(...).classification` reports after P3b's conditions.

Production's derived extent per destination dimension (inferred from these runs, then enforced by
`confirms`): `c0 + sum coef*extent`, `c0+1` for a constant: `2*a` (|a|=4) gives 8, `a+2` gives 6,
`a+b` (|a|=4,|b|=3) gives 7, `a+4b` gives 16, constant `3` gives 4. It over-approximates the true
`max+1` (`2*a` writes at most coordinate 6 but derives 8).

| fixture | declared k | oracle Y | legacy | checked | raw | final |
|---|---|---|---|---|---|---|
| (a) `Y[2*a] := X[a]` | 8 | [8]: 1,0,2,0,3,0,4,0 | same | same | parity | parity |
| (b) `Y[a+2] := X[a]` | 6 | [6]: 0,0,1,2,3,4 | same | same | parity | parity |
| (c) diagonal `Y[a,a] := X[a]` (`.free a, .free a`, Y over [a,a]) | 4x4 | [4,4] diagonal 1,2,3,4 | same | same | parity | parity |
| (d) `.scatter Y [a+b] X[a]*W[b] {reduce:=.sum}`, real collisions | 6 | [6]: 1,12,123,234,340,400 | value: binding issues shape [6] vs [7] (derived 7) | preparation `capability multiAxisScatterLhs "Y: affine LHS slot"` | nativeFailure | nativeFailure |
| (d) same, declared 7 | 7 | [7]: 1,12,123,234,340,400,0 | VALUE = oracle (production sums) | preparation `capability multiAxisScatterLhs` | nativeFailure | nativeFailure |
| (d') `.scatter Y [const 3] X[a] {reduce:=.sum}` | 5 | [5]: 0,0,0,10,0 | binding issues shape [5] vs [4] | preparation `capability scatterOrAffineLhs "Y: constant affine LHS slot"` | nativeFailure | nativeFailure |
| (d') same, declared 4 | 4 | [4]: 0,0,0,10 | VALUE = oracle | preparation `capability scatterOrAffineLhs` | nativeFailure | nativeFailure |
| (e) `Y[2*a] := X[a]*W[b]` (b contracted under the write, reject policy) | 8 | [8]: 111,0,222,0,333,0,444,0 | failure scheduledEvaluation: `evalScatter Y: collision writing output coord [0], source coords [0,0] and [0,1]` | runtime `execution scatterCollision [0] [0,0] [0,1]` | nativeFailure | known:collision |
| (f) surface `.assign` `Y[a+b] := X[a]*W[b]` (real collision) | 6 | [6]: 1,12,123,234,340,400 | failure scheduledEvaluation: collision at coord [1], sources [0,1] and [1,0] | preparation `capability multiAxisScatterLhs` (before any collision is reached) | nativeFailure | known:collision |
| (f') neighbour `Y[a+4b] := X[a]*W[b]` (no collision) | 12 | [12]: 1,2,3,4,10,20,30,40,100,200,300,400 | binding issues shape [12] vs [16] | preparation `capability multiAxisScatterLhs` | nativeFailure | nativeFailure (no condition) |
| (g) two `.assign` writers of Y: `Y[2*a] := X[a]`, `Y[a+1] := X[a]` | 8 | [8]: 1,1,4,3,7,0,4,0 | failure COMPILATION `scanAxisNotIter "a"` | sourceCompilation `scanAxisNotIter "a"` | nativeFailure | known:multiWriter |
| (h6) `Y[2*a] := X[a]` declared 6 | 6 | none: admission refuses `writeOutOfRange` (stage output, declaration 5, statement 0, slot 0) | - | - | (compareSource error) | refused:writeOutOfRange |
| (h9) same, declared 9 | 9 | [9]: 1,0,2,0,3,0,4,0,0 | value: binding issues shape [9] vs [8] and length 9 vs 8 | the same issues | nativeDiscrepancy | known:extent |
| (i1) `Y[3] := W[b]`, `|b|=1` (assign, constant slot) | 5 | [5]: 0,0,0,5,0 | failure COMPILATION `overlappingScatter "Y"` | sourceCompilation `overlappingScatter "Y"` | nativeFailure | nativeFailure |
| (i2) `Y[3] := X[a]` (assign, constant slot, 4 writers) | 5 | [5]: 0,0,0,10,0 | failure COMPILATION `overlappingScatter "Y"` | sourceCompilation `overlappingScatter "Y"` | nativeFailure | nativeFailure |
| (mask) (e) plus `Z[3] := X[a]` (independent constant slot on Z) | 8 | n/a (see below) | failure compilation (the Z statement), no collision | sourceCompilation | nativeFailure | nativeFailure (condition detected, NOT confirmed) |

Notes.

* (g): the observed refusal is a COMPILE failure `scanAxisNotIter "a"` on both native legs, not a
  `multiWriterScatter`-named error (no such name was seen). The condition `multiWriterScatter` encodes
  exactly this observed pair; another multi-writer shape may refuse differently and would then be
  reported as a mismatch, not explained.
* (i): the constant-slot statement fails at COMPILE with `overlappingScatter "Y"` whatever the RHS
  (size-1 axis `W[b]` or `X[a]`), so P0's `evalScan: scan node has no iteration axis` did NOT reproduce
  through the source pipeline. The surface elaboration of `S[3]` (P0 used `tlprog!`) vs the hand-built
  `.affine (.const 3)` slot here was not compared; cause of the P0 difference NOT determined. The
  constant slot is only exercised with the sum policy as a scatter ((d')): legacy sums like the
  oracle, the checked plan refuses it by capability.
* (d)/(d')/(f): the checked plan refuses every multi-axis or constant affine slot at preparation
  (`multiAxisScatterLhs` / `scatterOrAffineLhs`), so those fixtures can never reach four-leg parity
  today; legacy is the only native leg that sums collisions. No condition is added for that capability
  gap (it is a refusal, decidable but not requested; flagged for the next slice).
* (mask): with `fixtureDependencyOrder = [5]` the oracle refuses `omittedTarget 6` (classification
  `oracleUnavailable`); the fixture passes `[5, 6]`.
* The S1 `usedDType` classification is decided from the source alone in `checkRunProfile` (it returns
  before any native outcome is consulted); the new conditions are stricter than that precedent: they
  are decided in `ComparisonRun.classification` AFTER the native legs and only if `confirms` holds.

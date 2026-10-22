# B6 record: an out-of-range scatter write is an error (landed 2026-10-22)

Process weight: **Direct** (slice-plan §0): no plan document. B6 is decision-note §B6 (user decision 2026-10-14, option A): the silent
skip of an out-of-range scatter write was a vestige of overwrite semantics and is replaced by an error in both backends. The Source oracle
already errored (`writeOutOfRange`) against the declared shape. Branch `worktree-b6-range-error`, base `db812255` (S3a landed and pushed).

## 1. What changed

- **Reference.** `evalScatter` (Eval/Scatter.lean) throws `EvalError.scatterWriteOutOfRange nm outCoord sourceCoord` instead of skipping.
- **Checked plan.** `checkScatterCore` (Eval/Plan/Check.lean, so `checkScatter` and `checkScatterF32`) rejects statically with
  `PlanError.scatterWriteOutOfRange dim minImage maxImage extent`. The check is a second loop AFTER every dimension's width, unknown-extent and
  `scatterDestExtentMismatch` clauses, so a wrong declared extent at a later dimension wins over a range error at an earlier one. Each
  destination dimension's affine image over the source box has its min and max at the corners (`scatterImageBounds`); the box is
  `compute.outputShape` (what the worker enumerates), and an empty box is vacuously in range. The dense worker's skip is now
  `PositionalInputError.scatterPlacementOutOfRange`, unreachable for a checked plan.
- **Surface reach.** Only a zero coefficient: `Out[0*i]` derives extent 0 and `Out[0*i+5]` derives extent 5, so every write is outside.
  Negative coefficients and biases need hand ASTs. A slot with at least one positive coefficient is always inside its own derived extent.
  Through `prepareEvalPlan` the surface error arrives as `invalidPlan (assign (nodeError 0 (scatterWriteOutOfRange ...)))`.
- **Tests.** Reference pins B6-a..i (ScatterTest) with accept-neighbours; checked pins with a min/max-corner off-by-one pair
  (ScatterCheckTest) and an f32 twin; S9/S9b both-backends-reject (ScatterCompileTest); `evalErrorEq` learned the new arm; differential
  fixture `fR` (`Y[0*a+5]`, declared extent 6, derived 5: oracle `[0,0,0,0,0,10]`, legacy and checked both refuse, class `nativeFailure`, no new
  condition constructor; the existing `scatterExtentOverridesDeclared` is predicted but never confirmed, pinned by `conditionCount fR == 1`)
  with accept-neighbour `fR1`. Two pins the S3a review found missing: the checked `.min` refusal (`f32ScatterMinFillProg`) and
  collision SUMMATION ORDER with order-sensitive values (f64 S10b: source order `[0,0,12,0,1,0]` vs reversed `[1,0,12,0,0,0]`; f32 1.6b:
  `[0,0,4]` vs reversed `[1,2,3]`), each failing when a fold is reversed.

Commits (oldest first): `fea8d620` reference; `11ef480c`, `92382c08` checked plan and flipped fixtures; `b865f1e2` docs sweep;
`334b9a75` differential; `7e6b4626` the two pins; `ccde9269` this record and the `writeScanStmtSlice` doc note; a final review-fix
commit (stale comments, `conditionCount fR == 0`); merge hash on the close line.

## 2. Parked, with cost

| Item | Cost |
| --- | --- |
| Scan-local reference write `writeScanStmtSlice`: still SKIPS an out-of-range write and OVERWRITES on a collision. COLLISION: the scan-local audit (scratch `f3_audit.md`) found it reachable only through hand-built programs the checked backend refuses before running (slot naming two source axes such as `S[j+q]`; repeated axis UID in a hand `.assign`); for what both backends accept the placement is injective, so overwrite = ⊕. Observed: base `.scatter S[j+q,l=0] := Z[j,q]` returns overwrite values, the checked plan refuses with `multiAxisScatterLhs`. OUT OF RANGE: hand-built negative base or bias (`ScanCompileTest` `s6NegBase`, `s6NegBiasBase`) is refused by the checked path, so the reference would skip; no further audit of that arm. Documented in the function's docstring. Making the reference refuse those programs (mirroring `multiAxisScatterLhs`/`duplicateAxisInLhs`) is optional hardening. | ~3 reject fixtures, 1 Direct dispatch |
| The surface `Out[0*i]` error reaches the user as `invalidPlan` (the compiler-bug channel), not a typed user-facing capability or shape error | ~1 Direct dispatch |
| `evalErrorEq` (test/Eval/PropertyOracle/Compare.lean) has no arm for 11 `EvalError` constructors (`baseWriteNotAtBoundary` .. `inputIsDefined`); equal errors of those kinds compare unequal, i.e. a false divergence, never a false pass; its comment about the catch-all is inaccurate (pre-existing) | ~1 Direct dispatch |
| `evalScatter` still truncates silently if `slots.length ≠ outShape.length` (direct hand call only) | tiny |
| B5 multi-writer scatter, `.assign`-arm const guard, `UnsupportedSource.scatterPolicy` rename, `scatterFillNotIdentity` render text (see the S3a record §4) | unchanged |
| Tropical sorts, casts, constants (S3b) | next, Full path, needs a design note first |

## 3. Cost and process

See the close line at the end. Dispatch turns vs the ~60 cap: reference 52, checked plan ~62, differential and pins 40.

# S2a T3 review (commit 801d4edf), lens: independence and silent wrongness

Read via `git show 801d4edf:<path>` only; nothing built.

- Verified (Q1, oracle independence). `Oracle.termFiber` computes the destination only through
  `destination origin shape assignment statement.output.forms`, where `shape` is
  `(table.entry statement.output.tensor).axes.map extent` (the declared destination), and its support is
  `forms.flatMap WriteForm.uids ++ reads`. No use of `output.dest`, `sourceSlots`, `output.shape`
  (the virtual write shape) or `output.indices` anywhere in Oracle.lean. The tamper fixtures
  (`tampered`) replace only `forms` and leave `dest` intact; an oracle consulting `dest` would ignore the
  tamper and the `.writeOutOfRange` guards would fail, so those guards are a real independence test.
  The range check runs for EVERY assignment before the `output == coordinate` filter, so an out-of-range
  image is never silently skipped.
- Minor (independence is partial by construction). Executor `dest` is `coordOfForms sig forms` built from
  the same admission-produced `forms` (`admitAffineOutput`, `idxAffineForm`), so a bug in
  `idxAffineForm` is shared by oracle and executor; only the HAND values (`r.y == y`, `occurrences`) are
  independent. Hand values are right for const, scale, shift, positive multi-axis affine and coef-0, but no
  fixture has a NEGATIVE coefficient (`Y[3 - a]`); sign handling in `idxAffineForm` / `destination`
  (`value + coef * (p.2 : Int)`) is exercised only by the constant `-1` tamper. Evidence: grep of
  `SourceOracleAffineTest` forms: scale 2, const, `affine 1 [(0,a)]`, `affine 0 [(1,a),(1,b)]`, `shift a 2`,
  `shift b 1` only.
- Verified (Q2, oracleOccurrences). Keys are `statement.output.context.axes.map uid`, the same list
  `Provenance.outputAssignments` uses for the executor key (`c.uidEquiv i` over `c.axes`), so order matches;
  `context` = `outputContext` of `formsSupport forms` (includes coef-0 uids, so `Y[1 + 0*a]` has key `(a)`
  with 4 occurrences, as fixture 2b expects). Diagonal `Y[a,a]`: `forms == indices.map single`, so it takes
  the existing bare path (`assign` consistency check); off-diagonal cells give no occurrence. `Y[a,a]` through
  the affine path (`indices = [a]`, forms `[single a, single a]`) fails the bare guard and is handled
  correctly by the assignment restriction. Constant slot (2a, 8): keys are the read/context axes only; fine.
  A missing context uid in an oracle assignment throws `.missingAssignment uid` (loud), never defaults.
  Merging by sum happens only over contracted axes and over terms; keys are unique per cell, so no merge
  crosses cells.
- Verified. `normalizeOracleContribution` throws `.nonBareWrite` (after the ambiguity check, so earlier
  errors keep their precedence) when `forms != indices.map single`; `oracleOccurrences` catches exactly that
  cause and re-throws every other error. No exhaustive match on `NormalizationCause` exists elsewhere
  (grep: only `==` comparisons and `mapError`), so the two new constructors break nothing.
- Minor (untested branch). The cross-TERM merge in `oracleOccurrences` (same key from two different
  `row.terms`, summed) has no fixture: every T3 fixture has one term per statement (`rhs` is always called
  with a single product term). By hand it is right when the executor emits one contribution per
  (statement, output assignment) valued by the sum over terms (`observeOccurrence` lists all
  `statement.terms` on one occurrence; `Event.contribution t o value` is one per occurrence). E.g.
  `Y[2*a] := X[a] + W[b]` would need `X[i] + 111` per key. A one-statement two-term affine fixture would
  pin this; a mutation that merges per term separately would currently survive unless the manifest covers it.
- Minor (documented, loud direction). Extent-0 contracted axis: oracle has no occurrence, executor has one
  valued 0, so `rowsAgree` is false (false negative, not a silent accept). Documented in the doc comment.
- Minor (dead code). `| _ => throw ... unknownStatement` in `oracleOccurrences` is unreachable
  (`normalizeOracleContribution` already established exactly one statement); `row.origin.statement.getD 0`
  likewise. Harmless.
- Question. `Differential.lean` and `NumericalProfile.lean` call `normalizeOracle` (not
  `oracleOccurrences`); on an affine-admitted source they now return `.nonBareWrite` (loud). Intended for
  S2a (they use `admitSource`), but confirm no later task routes affine sources there without switching.
- Verified (Q3, fixture discrimination). Inputs X=[1,2,3,4] (uid 7, |a|=4), W=[1,10,100] (uid 8, |b|=3);
  all hand values recomputed and correct (conv s0..s5 = 1,12,123,234,340,400; fixture 9 = 1,3,6,9,7,4; the
  fiber-of-cell-2 guard: X0*W2=100, X1*W1=20, X2*W0=3).
  * Fixture 9 (`Y[a+b] := X[a]`) is the only fixture where a form uid is not read: with
    `support := [] ++ reads` the oracle has no `b` in its assignment, `destination` throws
    `missingUID 8`, `report` returns `.error`, `parity` false. If a mutant defaulted `b` to 0 instead, Y would
    be [1,2,3,4,0,0] vs hand [1,3,6,9,7,4], also different. Other fixtures: 3 reads a and b, 7 `affineB` reads
    b, 2b reads a (coef 0), 8 has no form uids; none exercises a form-only uid. Claim confirmed.
  * `(g.1, o.value)` (overwrite instead of `(g.1, g.2 + o.value)`): merging happens only when a key receives
    more than one oracle occurrence, i.e. a contracted axis: fixture 6 (b contracted; per key X[i],10X[i],
    100X[i]) gives last-wins 100X[i] = [100,200,300,400] vs sum 111X[i] = [111,222,333,444]; first-wins
    gives X[i]. Fixture 8 (W[b] = 1,10,100): last-wins 100, first-wins 1, sum 111. All three readings differ
    in both fixtures, so the inputs are non-symmetric enough. Fixtures 2b/3/9 have unique `(a)`/`(a,b)` keys
    (no merge), so they cannot distinguish. Claim confirmed (only 6 and 8, plus neither is hit by the
    cross-term case above).
  * Also, fixtures 6 and 8 are the only ones whose reads contain an axis outside the form support, so they
    additionally kill a form-uids-only support mutant (missingUID on the read).
- Verified (Q4, out-of-range guards). `[2*a]` (extent 4): first image at a=2 is 4 = extent, so
  `.writeOutOfRange 0 4 4` tests the upper bound exactly at the boundary (a `value <= extent` mutant would
  run without error and fail the guard). `[a - 1]`: a=0 gives -1, tests the lower bound exactly at the
  boundary (a `value >= -1` mutant would wrap via `toNat` and fail the guard). The accept-neighbour
  `[a]` exercises both edge-accepts (0 and extent-1 = 3) and asserts `isSome`. Origin is asserted too
  (`writeOrigin`, slot 0). Gap (Minor): only slot 0 and a rank-1 destination are tested, so a wrong slot
  index in `zipIdx` (error origin/`slot` argument) for slot >= 1 and the `coordinateRank` forms-length guard
  in `destination` are unexercised.
- Verified (Q5). No `sorry`, `axiom`, `native_decide`, or `decide :=` in Oracle.lean, Observation.lean or
  `SourceOracleAffineTest.lean` (grep exit 1). Fixture count is 16 `#guard`, matching the plan. The test file
  is registered in `lakefile.toml` next to `SourceOracleTest`.

Verdict: APPROVE. No Critical or Major findings; the oracle is independent of `dest`/`sourceSlots`/virtual
`shape`, `oracleOccurrences` is correct on the checked cases, fixtures 6, 8 and 9 discriminate as claimed.
Recommended (optional, cheap): add a negative-coefficient fixture and a two-term affine fixture.

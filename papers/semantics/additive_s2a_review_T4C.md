# S2a T4 stage C review (commit e54795e9: T4-07 A2 guards, T4-08 A1 origin binding)

Lens: origin-bound confirmation; legacy-vs-oracle collision guards. All code read from `git show e54795e9:<path>`.

- **(Q1 binding, OK)** `Differential.lean` `confirms` `.scatterCollisionRejected origin`: both legs get
  `ownedBy native origin.declaration`, which requires a table entry with `e.name == nm` AND
  `some e.declaration == origin.declaration`. `legacyCollision` passes the `nm` of
  `Eval.Error.scatterCollision nm ..`; that `nm` is `evalScatter`'s destination parameter
  (`Eval/Scatter.lean`, `throw (.scatterCollision nm oc firstSrc sc)`), i.e. the statement's tensor.
  The checked arm passes the text before the first `": "` of the capability context; in
  `Eval/Plan/Compile.lean` `checkStmt` the context is built from the statement's own `nm`
  (`checkScatterAffineExpr`/`checkLHSSlot`: `s!"{stmtName}: affine LHS slot"`,
  `s!"{stmtName}: constant affine LHS slot"`). Bound to the destination TENSOR on both legs, as
  specified.
- **(Q1 string matching, OK)** Matching is exact string equality on a whole token, not prefix/substring:
  legacy `nm` is compared whole; checked takes `splitOn ": "` head, so `"Y2: affine LHS slot"` gives
  `"Y2"` and `"XY: ..."` gives `"XY"`, neither `== "Y"`. The only way to mis-split is a tensor name
  containing `": "`, which is not an identifier. The declaration conjunct additionally pins the entry.
  (Residual: two table entries sharing one name would both be accepted by name, inherent to a
  name-only native error; not reachable with unique declaration names.)
- **(Q1 narrowing, OK, no missed confirmation found)** For a detected collision the statement is
  non-bare (affine forms) with `rejectCollisions`. `checkStmt` checks slots FIRST; the only
  slot-attributed capability errors for an affine slot are `scatterOrAffineLhs` (const, or an
  `.assign` affine slot via `checkLHSSlot`) and `multiAxisScatterLhs` (`checkScatterAffineExpr`);
  `unsupportedLhsSlot` is `iterAt`/`iterNext` only, and scan slots are refused at admission
  (`Admission.lean` `.unsupported .scanSlot`). `checkScatterReduce` passes for `rejectCollisions`. Any
  other constructor (`checkAggOp`, `checkNonlinScatter`, `checkFactor`) is a refusal for a cause
  other than the slot/collision, so `nativeFailure` is the CORRECT classification there (pre-A1 it
  was absorbed). `freeUidOrFail`/`assignPartsOrFail` raise `scatterOrAffineLhs context` with a
  non-`{tensor}:` context but are documented unreachable post-preflight. So the narrowing cannot
  produce a false `nativeFailure` for a single-condition source. Note: the positive
  `scatterOrAffineLhs`-names-own-tensor arm is probably unreachable on the source path for a
  collision condition (const-slot statements stop at `lowerArith` `overlappingScatter`, fixtures
  `fI1`/`fI2`), so it is harmless but unexercised; the narrowing itself is uncovered by any cycle,
  as the plan (T4-A1) already parks (~0.5 dispatch).
- **Minor (new under-confirmation from binding + head-only):** `detectConditions` lists collisions in
  statement order and `classification` confirms only the head. With TWO detected collisions on
  different tensors, if the legs fail on the non-head one (e.g. legacy evaluates head `Y`'s
  single-axis collision, while the checked preflight refuses a later multi-axis `Z` slot first,
  since preflight precedes all runtime), the checked leg names `Z`, `ownedBy` for `Y` is false, and
  the run is `nativeFailure` although both divergences are known conditions. Pre-A1 the cause-only
  arm would have confirmed. Safe direction (no masking), and the analogous two-tensor extent case is
  already parked in the plan's §2 row (review F9); this collision case is not listed there and
  should be added to that row.
- **Minor (doc overclaim):** the section comment above `nonBareWrite` still says `confirms` makes it so
  "a condition can never explain away an unrelated native divergence". After A1 that holds only for
  the origin-bound legs; the checked runtime collision and both `multiWriterScatter` legs remain
  cause-only (as their own docstrings now say). Suggest qualifying the sentence.
- **(Q2, OK)** Cause-only legs are documented: `checkedCollision` docstring ("The runtime collision is
  CAUSE-ONLY: `PositionalInputError.scatterCollision` carries coordinates and no tensor or
  statement"); `legacyCompile` docstring (multi-writer `scanAxisNotIter` names an AXIS only); the
  checked `scanAxisNotIter` arm is inline in `confirms`, covered by the `confirms` docstring
  ("`multiWriterScatter` stays cause-only on both legs"). `fF11` pins the positional runtime cause
  (`PositionalInputError.scatterCollision [0] [0, 0] [0, 1]`).
- **(Q3, OK)** Hand values recomputed from `snap` (X=[1,2,3,4], W=[1,10,100]):
  `fD` `Y[a+b] += X[a]W[b]`, |k|=7: c0=1, c1=2+10=12, c2=3+20+100=123, c3=4+30+200=234, c4=40+300=340,
  c5=400, c6=0 = `[1,12,123,234,340,400,0]`. `fD'` `Y[3] += X[a]`: 10 at cell 3, |k|=4 = `[0,0,0,10]`.
  `fN` `Y[a+4b]`, |k|=16: cells a+4b distinct (a<4), values 1..4, 10..40, 100..400, then four 0s:
  matches. `fN'` `Y[2a] += X[a]`, |k|=8: `[1,0,2,0,3,0,4,0]`: matches. Extents agree with
  `derivedShape` (7, 4, 16, 8). Neighbours differ in construction: `fN` changes `b`'s coefficient
  1 -> 4 (injective image), `fN'` replaces the constant slot with `2a` (injective); both keep
  `.scatter` + `sumOpts`. `legacyMatchesOracle` is non-vacuous (nonempty, bitwise `==`, and
  `legacyComparison = .compared (.ok .agreement)`); `fD`/`fD'` additionally pin `oracleCells` to the
  hand bits.
- **(Q4, OK)** `fOriginL` = `[zBare, Y[a+b] := X W]`: `zBare` is bare so `detectConditions` skips it;
  `Y` (decl 5) is the head condition. Legacy fails first on `Z` (`evalScatter Z: collision`, same
  kind `scatterCollision`); checked preflight names `Y` (`multiAxisScatterLhs "Y: affine LHS slot"`,
  pinned). Under cause-only legacy both legs pass -> `known:collision`; bound -> `nativeFailure`.
  Isolates the legacy binding. `fOriginC` = `[Z[3] += X (sum), Y[2a] := X W]`: `Z` not detected
  (sum policy; single writer; derived [4] = declared [4]); legacy sums `Z` then names `Y`; checked
  preflight names `Z` (`scatterOrAffineLhs "Z: constant affine LHS slot"`, pinned). Cause-only
  `.capability _` would confirm; bound -> `nativeFailure`. Isolates the checked binding. Both
  accept-neighbours replace `Z` with the plain `Z[a] := X[a]` and pin `known:collision` (`fOriginL`'s
  neighbour confirms via the bound `multiAxisScatterLhs "Y..."` arm, `fOriginC`'s via the cause-only
  checked runtime arm). Guard count: T4-07 10 + T4-08 11 = 21, as the plan states.
- **(Q5, OK)** `git show e54795e9 -G "sorry|axiom|native_decide"` matches nothing; all new checks are
  `#guard` (evaluated, not `native_decide`).

**Verdict: APPROVE with two Minors** (park the two-collision under-confirmation in the §2 F9 row;
qualify the "can never explain away" section comment). No Critical/Major findings.

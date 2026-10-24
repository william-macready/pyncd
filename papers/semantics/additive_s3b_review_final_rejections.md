# S3b final whole-branch review, lens (b): false rejections and regressions

Reviewer: Opus, READ-ONLY (no build, no mutation run). Range `740bd4f8..be4d888d`. Findings are appended as found.

## F1 (Major): `tropicalNonlin` keys on the statement's own annotation, not the sort it is evaluated in; a scan's neutral writer evades A8 from SURFACE syntax, and the converse is a false rejection

Files / identifiers: `checkTropicalOutput` @ `LeanNCD/DSL/Pipeline/Structural.lean` (uses `Stmt.algebra`, i.e. the raw `agg`);
`scanStateStmts` / `Stmt.withAgg` @ `LeanNCD/DSL/Ast.lean` (rewrites a neutral writer's `agg` to the state's sort AFTER validation, in
`compileScan` @ `Eval/Plan/Compile.lean` and `evalScan` @ `Eval/Scan.lean`). `Stmt.isSortNeutral` only looks at the term/factor/axis shape, not at
`rhs.nonlin`, so a neutral writer may carry `relu`/`sigmoid`/`softmax`.

(a) False ACCEPTANCE, surface-reachable. Design §3 says the A8 rejection concerns "programmatic statements only, since `relu(maxreduce(..))` has no surface
form" (`tl_rhs` is either `tl_nonlin(...)` or `tl_agg(...)`, `DSL/Syntax.lean`). But a neutral base needs no `maxreduce` of its own:

```
iter l = 3
M[j, 0]    := relu(P[j])                         -- P declared `predicate`; neutral (one bare read, j on LHS); agg = sum
M[j, l +1] := maxreduce(M[j, l] · W[j, k])       -- state M is max-plus
```

`checkDtypes` and `checkScheduledDtypes` see the base with `agg = .sum` -> `checkTropicalOutput` passes. `scheduleAlgebras` gives `M` maxPlus
(the base contributes no sort). Both backends then run the base through `scanStateStmts`, i.e. as a max-plus statement WITH `relu`:
the bare read of predicate `P` is cast (false -> -inf, true -> 0.0), then `relu` gives `0` in every cell, so row `l = 0` is `[0, ..]` whatever `P` is
(a reader of the source, or the real sort, gets `P`'s 0/1). Same shape with an OOB pad: `M[j,0] := sigmoid(X0[j+1])` pads with `-inf` (state sort) and
yields `sigmoid(-inf) = 0` at the boundary cell instead of `sigmoid(0) = 0.5`. A non-identity nonlinearity is executed in a tropical sort, which is exactly
what A8 forbids, and the value depends on the sort-specific cast/pad. Plan §3(iii)'s closing claim "the `tropicalNonlin` rule has NO S cell at R1, R2, R3,
R4, R6" is false for this shape at every one of those entries (R1/R2/R6 cannot see the scan grouping at all; R3/R4 check the pre-rewrite statement).

(b) False REJECTION (raw `ScheduledProgram` only). Base `.assign "S" [.free j, .iterAt l 0] {X[j], nonlin := .pointwise .relu, agg := .max}` with
recurrence `S[j,l+1] := S[j,l] * W[j,k]` (agg `.sum`). The base is neutral, so per plan §2 "its annotation is IGNORED" and the state is `real`
(`scanStateAlgebra`; `scanStateStmts` would rewrite the base to `.sum`). `checkTropicalOutput` nevertheless sees `Stmt.algebra = maxPlus` with `relu` and
throws `tropicalNonlin "S"` from `validateScheduled`; the identical program with the base annotated `.sum` is accepted and evaluates to the same values.
Nearest accept neighbour pinned: `CompileTest` "neutral base whose own agg DISAGREES with the recurrence" (`scanBase .identity .max` + `.min` recur) is
accepted ONLY because it carries `.identity`.

Evidence: no fixture combines a neutral scan writer with a non-identity nonlinearity (grep of `CompileTest` S3b block, `ScanCompileTest`, `RecurrenceTest`,
`BoolCastTest`); the T4 tropicalNonlin fixtures are all top-level `s3bStmt`. Fix direction (not done): in `validateScheduled`, run the A8 check on the
`scanStateStmts`-rewritten scan statements (or on `algebraOf` of the destination for neutral writers); the surface `checkDtypes` cannot see scans, so
either accept that R1/R2/R6 miss it (and correct §3(iii) and design §3) or reject a non-identity nonlinearity on a neutral writer of a tropical state there.

## F2 (Major, needs user adjudication): the two cast rejections are not closed under the identity casts the design admits, and they refuse previously-accepted programs whose values the flip does not change (minimax)

Files / identifiers: `checkSortCasts` @ `LeanNCD/DSL/Pipeline/ScheduledValidation.lean` (`a.isTropical && (k == .bool || (k.isTropical && a != k))`);
`scheduleAlgebras` (a top-level single writer's entry is `Stmt.algebra`, its annotation). Decision note A7 marks the "tropical -> bool, max-plus <-> min-plus
rejected" row PROPOSED (the other three rows are FIXED); design §3 adopted it.

Scenario (valid, natural mixed program, accepted before S3b, refused now):
```
M[i] := maxreduce(A[i, j])        -- row maxima, max-plus
Z    := minreduce(M[i])           -- min of the row maxima (minimax / bottleneck value)
```
`validateScheduled` -> `sortCastUnsupported "Z" "M"`. Both statements are single-factor, so their values are identical under max-times (pre-S3b) and
max-plus: nothing in the flip changes what this program computes, yet it moves from accepted to refused. Same for `P[i] := M[i]` with `P` a predicate
(tropical -> bool), accepted pre-S3b.

The rejection does not protect anything, because one identity copy through a real tensor launders it (both legs are FIXED identity casts):
```
M[i] := maxreduce(A[i, j])
R[i] := M[i]                      -- sum annotation: entry real; real reads max-plus = identity (accepted)
Z    := minreduce(R[i])           -- min-plus reads real = identity (accepted)
```
`Z` is the same value bit for bit, including any `-inf` cell of `M` (a real tensor may hold `-inf`; real -> min-plus is the identity, so a max-plus
`0_K` reaches the min-plus statement unchanged either way). Likewise `R[i] := M[i]; P[i] := R[i]` reaches a predicate (real -> bool is accepted, parked
decision 1). So `max-plus <-> min-plus` and `tropical -> bool` are refused only when adjacent, which makes them a style rule, not a semantic guard.

Evidence: no pre-S3b test pinned a minimax program (record §2 lists no flipped accept), so the regression is unobserved by the suite; the T4 accept
neighbours (`CompileTest` "real reads tropical, min-plus reads min-plus") accept each half of the laundering chain separately. Not a code defect
against the plan; flagged so the user decides between (i) keeping the rule and documenting the laundering and the minimax regression, (ii) admitting
max-plus <-> min-plus as the identity (what real already does), or (iii) making the rule transitive (track the sort through identity copies).

## F3 (Minor): `DSL/AGENTS.md` says `algebraOf` is "the per-tensor sort every backend reads"; no backend reads it

File / identifier: `leanncd/LeanNCD/DSL/AGENTS.md` row for `ScheduledValidation.lean` ("`CheckedScheduledProgram.algebras`/`algebraOf`, the per-tensor sort
every backend reads"). `git grep -n "algebraOf\|\.algebras"` over `leanncd/LeanNCD` finds them only in `ScheduledValidation.lean` (definition, field,
`validateScheduled`); the only readers are `test/Eval/Plan/CompileTest.lean` pins. The backends derive the sort independently: the reference from
`combineFor decls nm rhs.agg` / `boolReadCast decls c rhs.agg` (`Eval/Contract.lean`) plus `scanStateStmts`/`scanStateAlgebra` in `evalScan`; the checked
plan from `algebraForDest destDtype rhs.agg`, `residualizeAssignment`'s `tropical := agg != .sum`, and `scanStateAlgebra` for `initValue`
(`Eval/Plan/Compile.lean`). Scenario: a later slice changes `scheduleAlgebras` (e.g. per-tensor sorts for S3b-ii multi-writer names) believing the
backends follow; they do not, and the validator and the evaluators silently diverge. Fix: reword to "the sort the validator checks casts against;
backends recompute it from `agg` + declaration + `scanStateStmts` (kept consistent by construction, not by sharing)".

## F4 (Minor): `papers/backend_missing_functionality.md` S3b update overstates "no `max`/`min` scatter is refused"

File: `papers/backend_missing_functionality.md` (S3b update block). A top-level `max`/`min` scatter is still refused when it is multi-writer
(`multiWriterScatter`), carries a nonlinearity (`tropicalNonlin` first, programmatic only), has a predicate destination (`predicateAgg`), or writes out of
range (`scatterWriteOutOfRange`, B6). Intended meaning is "no longer refused for being max/min"; say that.

## F5 (Minor): the scan unroller's "independent" state-sort derivation copies production's neutrality rule verbatim

File / identifier: `localNeutral` / `localStateAgg` @ `leanncd/test/Eval/PropertyOracle/ScanUnroll.lean`. Its doc says it "deliberately calls neither
`scanStateAlgebra`/`scanStateSorts`" so that agreement is "a real check", but `localNeutral` is a line-for-line copy of `Stmt.isSortNeutral`
(`LeanNCD/DSL/Ast.lean`: same `read?` test, same `LHSSlot.axisUids`/`idxAffineForm` membership). A defect in the neutrality definition itself (hypothetical
example, NOT traced: if a recurrence scratch whose LHS omits the scan axis reads `H[j, l]`, the definition counts `l` as contracted) is replicated, not
detected; only the head-of-non-neutral selection and the zero-leaf `agg` are independent. Together with the parked "contracted-axis condition has no
dedicated fixture" this leaves the neutral rule with no independent oracle. Fix: say so in the doc comment, or derive neutrality in the unroller from the
unrolled leaf shape instead.

## Checked and found fine

- §3(iii) entry x rule, walked by reading: R1/R2/R6 reach `checkTropicalOutput` through `checkDtypes` (call site added beside `checkPredicateOutput`);
  R3/R4 through `validateScheduled` -> `checkScheduledDtypes` + `scheduleAlgebras` + `checkSortCasts` (both called before topology and collection);
  R5 untouched (`RouteFragments`, `Lowering`, `LoweringTest`, `RouteFragmentCorpusTest` absent from the diff); R7 `castNotAdmitted` keys on
  `factorOp == .add && reduceOp in {max,min}`, so the f32 tropical algebras are not falsely refused; `stateInitNotAdmitted` is unreachable from source
  (a predicate state's `ownAlgebra?` is `bool` -> `.zero`); R8 (`Executable.lean`) untouched. Caveat: F1 is the one S cell §3(iii) does not list.
- `tropicalNonlin` top-level fixtures vs neighbours (`relu + sum`, `max + identity`, predicate precedence `predicateNonlin`/`predicateAgg`) are right;
  surface syntax cannot combine `tl_nonlin` and `tl_agg`, so outside F1 the rule is programmatic-only as designed.
- `scanStateAlgebraMismatch`: neutral bases (RC5/RC7/RC10 shapes, `X0[j]`, `Z[r]`, `iterNext`/`iterAt` slot UIDs) are neutral; scratch has one producer, so
  it cannot mismatch; a scratch name reused across two scans is refused by `multiWriterScan` (`routeWrites` includes scratch), so the "no entry" fallback
  is not a hole. "Non-neutral real base (two-factor or contracted) + max recurrence" is refused by design; the workaround (a top-level real statement
  read by a neutral base) is accepted, so no expressible program is lost.
- `sortCastUnsupported`: `unaryFn` and Iverson factors exempt; multi-writer names have no entry and fall back to the declaration (no false rejection);
  a multi-writer PREDICATE name does get an entry (the declaration loop inserts `bool` first), so its writers ARE cast-checked, contrary to the framing of
  §3(i) C20, but harmless: tropical -> bool is refused on every path. A top-level neutral `maxreduce(A[i])` is max-plus (its annotation counts at top
  level), as plan §2 states; casts from it follow.
- `evalScan`'s new `buildDeclEnv` adds no rejection (`rejectUnsupportedStorage` throws the same `.compile e` first).
- Multi-writer pins: `Collect.lean` untouched; C6/C6b/C6c/J4 keep `multiWriterAlgebra`, min twins `c6min`/`c6bm`/`c6cm`/`J4m` added; `CompileTest` (d) pins that
  a multi-writer max set that also reads min-plus still reports `multiWriterAlgebra` (no entry -> no cast check). Route stays semantics-free.
- Oracle apparatus: `knownContractDifference`, `tropicalMultiFactor`, `tropicalScatterFill`, `detectSortedConditions`, `confirmsSorted`, `unexplainedAgree`,
  `scatterPolicy` all gone; `compareSortedSource` now has no masking arm (a checked preparation refusal or runtime error is `nativeFailure`, a value
  mismatch `nativeDiscrepancy`); the real harness's `confirms` arms for the deleted conditions went with them and its own
  `Differential.Classification.knownContractDifference` is untouched. The sorted flag still refuses a mixed program: `sortKeys`'s `stmtAgg` reads a
  `.scatter`'s `agg`, pinned by SourceSortedAuditTest Row 7 (`snap [k]` sum assign + max scatter -> `mixedSorts`).
- Sorted snapshots now declare `k` extent 8 (record §2 T7 row, call 17): a stated migration, not a mask. Consequence only: no sorted row pins a tropical
  affine write whose declared extent is smaller than production's derived one (it would surface loudly as `nativeFailure` via a binding shape issue).
- Test diff (`git diff --stat 740bd4f8 HEAD -- leanncd/test`, every removed `#guard`/`run_cmd` expectation read): each is re-valued or flipped with its
  reason in a comment and in record §2 (GatherTest re-signatured; KernelDense/KernelDense32 fixtures 7/8/9 re-valued, the no-longer-separating
  `storeNegB` row replaced by the `NegA_NegB` seed fixture; RC5/RC7/RC10, TR3/TR7 re-valued, TR5 un-gapped; ScanTest shape-1 rejects -> value tests
  with min twins, sum neighbour kept; CompileTest f32 max/min scatter rejects -> acceptance pinned on algebra + `destShape` only, values covered by
  ScatterDense32Test 1.6c; SourceAdmissionAffine/SourceSortedAudit policy refusals -> view/selection equalities; SourceSortedDifferential
  known-difference rows -> `fourLegParity`; DifferentialTest classifier arm removed with its constructor). No silently weakened expectation found.
- Docs: Eval/AGENTS, Eval/Plan/AGENTS (pitfall scoped to the two deleted constructors), Semantics/AGENTS, leanncd/AGENTS, test_portfolio.md and
  max_min_aggregation.md updates match the code, apart from F3 and F4.

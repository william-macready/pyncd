# Scatter geometry B execution review — lens 2

Review scope: `fd922285..f7c731f4146c6fab1e481e79dfe0273c2770748a`, in
`/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec`.
This report alone may be edited. No production, documentation, patch or fixture
changes; no mutation reruns; no inspection of concurrent close-out documents.

## Checkpoint 1 — contract and baseline

- Read plan sections 2, 3, 5 and 6, T5/T6 requirements and hard rules.
- Baseline status was clean; branch diff contains 26 paths.
- Known parked cases in section 2 are exclusions, not new blockers.
- Review in progress: grammar/constructor preservation, degenerate fixture
  truth, all four T5 sweeps and added citation checks.
- No findings adjudicated yet.

## Checkpoint 2 — surface and fixture inspection

- `Syntax.lean` requires at least two axis terms; its atomic `+ term` loop
  rewinds before a numeral bias. `elabTLAxisTerm` preserves source order and
  coefficients. The new elaboration arms do not alter the old arms.
- `ParseProgramTest` U2 pins all seven old constructors together, including
  `x +1`, spaced shift, scale-plus-bias, normalization and numeral scan base;
  U1/U3 pin multi-term order/coefficient/bias and `=3` versus `3`.
- U5 pins unmerged `a+a` and retained zero coefficients; `aaSurf`/`zcSurf`
  check acceptance and three-leg cells. `scanBase`, `scanConstStep`,
  `scanConstBase`, `scanMultiStep`, `r1Surf` and `r2Surf` contain the advertised
  admission/refusal/shape guards.
- `+1` is an existing literal token, so both `a + b +1` and `a+b+1`
  fail the new rule; spaced `a + b + 1` is the bias spelling.
  `bias` is already reserved by `tl_linear_item`, not a new scatter
  restriction. No negative-parse fixture is claimed here or added.
- T5 sweeps have run: deleted names **3 hits / 1 file**; slice tense
  **10 hits / 8 files**; capability markdown **6 hits / 3 files**;
  added patch citations **0 hits** (exit 1).
- **Adjudication S-1 (no defect / rejected):** suspected old-constructor
  ambiguity. Evidence: disjoint two-axis grammar and exact U2 guards;
  new-vs-parked: neither, no regression found. Verdict **reject**.
- **Adjudication S-2 (known parked behavior / not a blocker):** repeated/zero
  coefficients and no-placing-term slots are section 2 exclusions, not new
  findings. Verdict **park**, existing ~1-dispatch validation scope; zero
  coefficient groups separately ~0.2. No redesign requested.

Sweep output and remaining whole-diff/document-pin verification follow.

## Finding S-3 — P3: shape summary still omits the retained D5 exception

- **Evidence:** `leanncd/LeanNCD/Semantics/AGENTS.md`, paragraph beginning
  “Since slice B a single constant or multi-axis writer into a destination
  with every axis pinned publishes the DECLARED shape in production too”.
  This is unconditional as written. `ScatterSurfaceTest.r1Surf` has every
  destination axis pinned, a constant placement plus identity `b`, and
  explicitly pins derived `[4, 3]` in all three legs, not declared `[8, 3]`.
  `Collect.boxedSingleGroups` excludes any declared source axis, identity
  included. The new detailed comments in `Collect` and `Differential` state
  that exception correctly.
- **New vs parked:** new documentation omission in the T5 text, not a new
  production defect and not a request to change the section 2 parked D5
  semantics.
- **Proposed verdict:** **fix now**, ~0.1 dispatch, wording only: append
  “unless a declared axis occurs among the writer's source axes (D5,
  including identity slots; see r1Surf/r2Surf)”. No redesign; not BLOCKED.
  This reviewer leaves the documentation untouched as instructed.

Targeted validation passed:
`bash /Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd DSL.ParseProgramTest Eval.Plan.ScatterSurfaceTest`
ended `Build completed successfully (8524 jobs).` (exit 0; cached/replayed
dependencies, no mutation cycles rerun).

## T5 sweep transcript (saved for close-out)

Absolute search roots substitute for running from the execution-worktree root;
patterns and glob filters are unchanged. Standard output below is normalized only to remove volatile source line numbers; original output is retained in the session evidence.

### Sweep 1 — deleted names

Command:
```text
rg -n "boundedScatter|isConstUnit|constUnitPrefix|checkReservedAxisNames|reservedAxisName" /Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd --glob "*.lean" --glob "*.md" --glob "!docs/superpowers/**"
```

Exit **0**, **3 hits / 1 file**:
```text
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/test/Eval/Plan/ScatterGeometryTest.lean:(Slice A history; reversed in slice B, see the pins below.) `IdxExpr.isConstUnit` recognised the unit
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/test/Eval/Plan/ScatterGeometryTest.lean:(published `[2]` instead of `[8]`); `checkReservedAxisNames` rejected the spelling. Both are deleted. -/
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/test/Eval/Plan/ScatterGeometryTest.lean:-- does: collected into the declared box, eight cells in every leg (it used to be `reservedAxisName`).
```

Read each hit and its surrounding history/pins: all three explicitly describe
deleted or reversed slice A behavior. No live deleted-name claim remains.

### Sweep 2 — slice B tense

Command:
```text
rg -n "slice B|Slice B" /Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD
```

Exit **0**, **10 hits / 8 files**:
```text
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/DSL/AGENTS.md:26:| Additive collection (`desugarMultiWriters`): assign/scatter writer `k` of `T` becomes private `T#k`, followed by one full-domain collector in the agreed sort. Neutral writers adopt that sort via `Stmt.withAgg`; conflicting votes give `multiWriterAlgebra`. Legacy all-bare groups keep positionwise UID agreement (`writerShapeMismatch`). B5 admits bounded real/tropical scatters using shared `scatterAffineClass`/`LHSSlot.collectable` from `Ast.lean` (single-axis, multi-axis and lowered-constant slots; slice B); predicate destinations, a raw `.affine (.const _)` and unlowered scatter-shaped assigns keep `multiWriterScatter`. `writerGroupBasis` selects distinct declared axes (`multiWriterRepeatedBasis`) or the first ordinary bare assign, never an explicit scatter (`multiWriterNeedsDeclaredShape` otherwise). `collectorShapeObligations` retains original shapes and a `boxed` flag (declared destination, every axis pinned in `declaredAxisSizes`) for the post-inference check: fit inside a box, equality otherwise. Scan conflicts/freshness checks stay unchanged; single-writer identity is preserved. B5c collects a single non-identity writer of a boxed destination like a group of one (`boxedSingleGroups`, `collectDefinitions` only, fed by `declaredAxisSizes`; excluded: unpinned or undeclared, predicate destinations, a raw `.affine (.const _)` slot, a declared axis the writer uses as a source axis (the `tensor Out(i)` + `Out[2*i]` idiom keeps the derived shape; this also covers identity and transposed writers)), so a pinned declaration decides the published shape for every writer count. Public `route` refuses B5 groups with `routeUnsupportedMultiWriter` and does not see single boxed writers; the experimental JAX codegen refuses a boxed single bare assign (collector padded read, `labelExtentMismatch`), but legacy tropical all-bare routing still omits cast checks. Imports `RouteFragments` only | `Collect.lean` |
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/DSL/AGENTS.md:105:- **LHS slot grammar (`tl_lhs_slot`, `Syntax.lean`; `elabTLLHSSlot`, `Elab.lean`)**: `x` `.free`; `x .` `.freeNorm`; `n` scan base case `.iterAt`; `x +1` `.affine (.shift x 1)`; `n*x`, `x + n`, `n*x + m` single-axis `.affine`; NEW (slice B) `a + b`, `2*a + b`, `a + 2*b + 3` (>= 2 axis terms from category `tl_axis_term`, each `x` or `n*x`, optional numeral bias) `.affine (.affine bias [(c, axis), …])`, terms unmerged and zero coefficients kept (`a + a`, `0*a + b` are accepted, behaving as `2*a` and `b`: in `0*a + b` the axis `a` becomes a summed collision axis and the shape comes from `b` alone, whereas the single-axis `S[0*a]` is refused (extent 0); a slot with NO placing term, `0*a + 0*b` or `0*a + 0*b + 3`, compiles but every leg fails at run time with a range error, since its extent is the bias and the write lands at the bias; `=k` has extent k+1); NEW `=n` `.affine (.const n)`. Coefficients and biases are non-negative numerals. Inside a scan, a surface constant slot fails `overlappingScatter` (compile) and a multi-axis slot `multiAxisScatterLhs` (preflight).
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/DSL/Ast.lean:    (`boxedSingleGroups`) take this slot? Slice B (B-D1): every slot whose extent `LHSSlot.outExtent`
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/Semantics/AGENTS.md:174:Since slice B a single constant or multi-axis writer into a destination with every axis pinned publishes the
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/Semantics/Source/Differential.lean:/-- B5c + slice B (B-D3): production publishes the DECLARED shape for a single write whose destination
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/DSL/Pipeline/Structural.lean:    axis identity is the UID and nothing reads the name, slice B B-D2). The
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/Eval/Plan/Error.lean:      `tl!{…}` surface syntax since slice B added the multi-axis slot (`elabTLLHSSlot`): a scan
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/Eval/Plan/AGENTS.md:37:- **B5 is native collection, not a new scatter worker.** Bounded real/max-plus/min-plus groups use the declared distinct-UID basis, or first ordinary bare assign when undeclared; predicate-destination groups remain refused; multi-axis and lowered-constant writers are admitted (slice B), and a boxed single such writer publishes the declared shape. `CheckedScheduledProgram.shapeObligations` enforces exact writer/basis extents, with existing inference errors allowed first. Both f64 and native f32 run; undeclared fallback is checked f32 only, not reference f64 evidence. `Eval.Plan.B5NativeTest` / `B5BoundaryTest` pin values, precision, payloads, unsized/rank errors and privacy. `route` explicitly refuses B5; the JAX codegen fixture requires actual prepared scatter nodes to refuse before emission. Current scope/evidence: `papers/semantics/additive_b5_record.md`.
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/Eval/Plan/AGENTS.md:56:| Why was a source scatter rejected? | `lowerArith` (`DSL/Pipeline/Structural.lean`) reclassifies an affine/diagonal LHS into `Stmt.scatter`. Top level: constant and multi-axis placements are admitted (`lowerArith` rewrites a constant slot to a placement over a synthetic size-1 `#const<uid>` axis; a multi-axis row takes the exact-reach extent `LHSSlot.outExtent`); nonlinear placement and predicate destinations fail at capability tier; colliding writes are summed, never rejected. Since slice B constant/multi-axis writers are also collected in multi-writer groups and into a boxed single writer's declared box (`LHSSlot.collectable`; a raw `.affine (.const _)` still gives `multiWriterScatter`), and the surface spells them (`S[a + b]`, `S[=3]`); scan-local constant/multi-axis slots stay refused (F3: `scatterOrAffineLhs`, `multiAxisScatterLhs`). In a scan, only positive one-axis affine placement with nonnegative bias in non-advancing state dims and identity nonlinearity is admitted; other failures are typed `ScanCompileError`s |
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/DSL/Pipeline/Collect.lean:    * an explicit scatter whose every slot is `LHSSlot.collectable` (slice B, B-D1: single-axis,
```

Read every hit in context: none describes the implemented surface capability
as future work. `NEW (slice B)` labels the landed addition rather than a
promise. The unconditional shape sentence is finding S-3. The detailed
collector/oracle comments preserve D5 correctly.

### Sweep 3 — remaining capability markdown

Command:
```text
rg -n "multiWriterScatter|multiAxisScatterLhs|scatterOrAffineLhs" /Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD --glob "*.md"
```

Exit **0**, **6 hits / 3 files**:
```text
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/DSL/AGENTS.md:26:| Additive collection (`desugarMultiWriters`): assign/scatter writer `k` of `T` becomes private `T#k`, followed by one full-domain collector in the agreed sort. Neutral writers adopt that sort via `Stmt.withAgg`; conflicting votes give `multiWriterAlgebra`. Legacy all-bare groups keep positionwise UID agreement (`writerShapeMismatch`). B5 admits bounded real/tropical scatters using shared `scatterAffineClass`/`LHSSlot.collectable` from `Ast.lean` (single-axis, multi-axis and lowered-constant slots; slice B); predicate destinations, a raw `.affine (.const _)` and unlowered scatter-shaped assigns keep `multiWriterScatter`. `writerGroupBasis` selects distinct declared axes (`multiWriterRepeatedBasis`) or the first ordinary bare assign, never an explicit scatter (`multiWriterNeedsDeclaredShape` otherwise). `collectorShapeObligations` retains original shapes and a `boxed` flag (declared destination, every axis pinned in `declaredAxisSizes`) for the post-inference check: fit inside a box, equality otherwise. Scan conflicts/freshness checks stay unchanged; single-writer identity is preserved. B5c collects a single non-identity writer of a boxed destination like a group of one (`boxedSingleGroups`, `collectDefinitions` only, fed by `declaredAxisSizes`; excluded: unpinned or undeclared, predicate destinations, a raw `.affine (.const _)` slot, a declared axis the writer uses as a source axis (the `tensor Out(i)` + `Out[2*i]` idiom keeps the derived shape; this also covers identity and transposed writers)), so a pinned declaration decides the published shape for every writer count. Public `route` refuses B5 groups with `routeUnsupportedMultiWriter` and does not see single boxed writers; the experimental JAX codegen refuses a boxed single bare assign (collector padded read, `labelExtentMismatch`), but legacy tropical all-bare routing still omits cast checks. Imports `RouteFragments` only | `Collect.lean` |
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/DSL/AGENTS.md:105:- **LHS slot grammar (`tl_lhs_slot`, `Syntax.lean`; `elabTLLHSSlot`, `Elab.lean`)**: `x` `.free`; `x .` `.freeNorm`; `n` scan base case `.iterAt`; `x +1` `.affine (.shift x 1)`; `n*x`, `x + n`, `n*x + m` single-axis `.affine`; NEW (slice B) `a + b`, `2*a + b`, `a + 2*b + 3` (>= 2 axis terms from category `tl_axis_term`, each `x` or `n*x`, optional numeral bias) `.affine (.affine bias [(c, axis), …])`, terms unmerged and zero coefficients kept (`a + a`, `0*a + b` are accepted, behaving as `2*a` and `b`: in `0*a + b` the axis `a` becomes a summed collision axis and the shape comes from `b` alone, whereas the single-axis `S[0*a]` is refused (extent 0); a slot with NO placing term, `0*a + 0*b` or `0*a + 0*b + 3`, compiles but every leg fails at run time with a range error, since its extent is the bias and the write lands at the bias; `=k` has extent k+1); NEW `=n` `.affine (.const n)`. Coefficients and biases are non-negative numerals. Inside a scan, a surface constant slot fails `overlappingScatter` (compile) and a multi-axis slot `multiAxisScatterLhs` (preflight).
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/DSL/AGENTS.md:115:- **A constant LHS slot is a placement over a synthetic size-1 axis, and nothing may read that axis's NAME** — `lowerConstSlots` (Structural) spells it `#const<uid>` for display only; axis identity is the UID. `LHSSlot.collectable` (Ast) admits it into groups and boxed single writers by constructor (a RAW `.affine (.const _)` is refused, `multiWriterScatter`; only a hand-built schedule that skipped `lowerArith` carries one). Any new predicate over slot forms must be mirrored in `declaredShapeWins` (Semantics/Source/Differential) and the test-side `OracleSortRules`.
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/Eval/Plan/AGENTS.md:56:| Why was a source scatter rejected? | `lowerArith` (`DSL/Pipeline/Structural.lean`) reclassifies an affine/diagonal LHS into `Stmt.scatter`. Top level: constant and multi-axis placements are admitted (`lowerArith` rewrites a constant slot to a placement over a synthetic size-1 `#const<uid>` axis; a multi-axis row takes the exact-reach extent `LHSSlot.outExtent`); nonlinear placement and predicate destinations fail at capability tier; colliding writes are summed, never rejected. Since slice B constant/multi-axis writers are also collected in multi-writer groups and into a boxed single writer's declared box (`LHSSlot.collectable`; a raw `.affine (.const _)` still gives `multiWriterScatter`), and the surface spells them (`S[a + b]`, `S[=3]`); scan-local constant/multi-axis slots stay refused (F3: `scatterOrAffineLhs`, `multiAxisScatterLhs`). In a scan, only positive one-axis affine placement with nonnegative bias in non-advancing state dims and identity nonlinearity is admitted; other failures are typed `ScanCompileError`s |
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/Semantics/AGENTS.md:155:B5 removed the blanket `multiWriterScatter` allowance: `fG` still reports
/Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/leanncd/LeanNCD/Semantics/AGENTS.md:178:sum rule for a multi-axis slot (unexercised; parked). Scan-local multi-axis/constant slots stay refused by capability (`scatterOrAffineLhs`, `multiAxisScatterLhs`, F3). See the
```

Read all six in context. Their capability/refusal claims match section 2:
predicate/raw-constant groups remain refused; surface scan constants fail at
compile while hand-built scan constants can reach capability refusal; scan
multi-axis slots reach `multiAxisScatterLhs`. `fG` names its remaining
`scanAxisNotIter` cause, not a lingering multi-writer refusal. The predictor's
legacy sum extent is explicitly parked.

### Sweep 4 — added patch citations

Command:
```text
rg -n "^\+.*[A-Za-z]+\.lean:[0-9]+" /Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/papers/semantics/additive_scatter_geometry_b_patches
```

Exit **1**, **0 hits**, stdout empty, stderr empty.

Also checked the complete `git diff --unified=0
fd922285..f7c731f4146c6fab1e481e79dfe0273c2770748a` by passing captured stdout
to `rg -n "^\+[^+].*[A-Za-z]+\.lean:[0-9]+"` (Python subprocesses, no shell
pipeline or scratch file). Exact output:
```text
Added .lean:line citations in complete branch diff:
hits: 0 rg exit: 1
```

Thus neither patches nor added branch documentation/comments introduce such
citations.

## Documentation-to-pin audit

All eight `ScatterSurfaceTest` references in production documentation and
portfolio text were searched and read, as was the geometry test header:

| Claim source | Existing pin and scope |
| --- | --- |
| `Eval/Plan/Error.lean` multi-axis scan preflight | `scanMultiStep`, exact `multiAxisScatterLhs "G: affine LHS slot"` guard |
| `Collect.lean` and `Differential.lean` D5 writer-count contrast | `r1Surf` / `r2Surf`, exact `[4,3]` / `[8,3]` shapes in all three legs and exact bitwise cells |
| `KnownGapTest`, both `EdgeCaseTest` mentions, `test_portfolio` KG-reshape/EC9 rows | `convSurf`, `biasSurf`: two-axis summing placement and coefficient/bias run through all three legs; U1/U2 in `ParseProgramTest` separately pin constructors |
| `ScatterGeometryTest` header | `convSurf`/`convProg` shape-and-cell equality plus independent expected values; `constPinSurf` and `f1Surf` pin constant slots |

These are pins of the slot grammar and summing-scatter capability, not a
claim that the literal dense-source program `Out[i+j] := X[i,j]` or a full
reshape/Kronecker/im2col portfolio program is in this fixture. Those larger
programs are expressly not claimed by the updated portfolio text.

`agree` was read: it requires actual `some expectedBits` in reference f64,
checked f64 and checked f32; failures cannot pass by `none == none`.
The separate `cells`/shape guards and rank-1 cell counts substantiate the
advertised shapes. U5 `a+a` has the documented stride-aligned eight-cell
result; `0*a+b` has three cells, with `a` summed away.

**Adjudication S-4 (no defect / rejected):** suspected missing advertised
surface pins. Evidence is the table above and passing targeted build.
New-vs-parked: neither; verdict **reject**, because the advertised slot-form,
scan-refusal and D5 pins exist. No claim is made that negative parsing of
`+1` or reserved `bias` is itself guard-pinned; those cases were checked
structurally against the grammar/token declarations, not re-probed at runtime.

## Completion

- Whole branch diff read across all 26 paths (large stdout divided into
  bounded windows); all three lens work items complete.
- **0 P1, 0 P2, 1 P3 new finding (S-3, wording-only fix-now proposed).**
  No load-bearing design finding; **not BLOCKED**. The report does not
  adjudicate the parent's eventual fix/park decision.
- All four prescribed sweeps complete with exact outputs saved above.
  Their counts match authoring; one shape-summary omission remains S-3.
- Targeted parser/surface build green, 8524 jobs. Full final build belongs
  to the parent; mutation cycles were not rerun. No nested agents, commits,
  production/doc/fixture edits, or new probe files.
- Usage measurement attempt:
  `python3 /Users/williammacready/code/python/pyncd/.claude/worktrees/scatter-geometry-b-exec/.claude/skills/slice-plan/token-report.py 69471b59-4948-4b98-bd3a-aa925cdbc8f1`
  returned `no transcript for session 69471b59-4948-4b98-bd3a-aa925cdbc8f1`
  (exit 0). That utility reads Claude transcripts, so this Copilot dispatch
  has no measurable cumulative/peak token count through it. Fewer than 25
  assistant response rounds at handoff; no observed budget breach, but the
  250k peak cannot be instrumentally certified with that tool.

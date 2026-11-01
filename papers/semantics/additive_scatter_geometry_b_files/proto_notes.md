# Scatter geometry slice B: prototype notes, dispatch 1 (engine half)

Worktree `proto-scatter-geometry-b`, base local `main` 759bbf56. Engine only: `DSL/Syntax.lean` and
`DSL/Elab.lean` untouched. Every value below was read from a real build or `lean-file.sh` run.

## Commits

| Commit | Content |
| --- | --- |
| `a5de2c61` | E1+E2+E3 production code and the minimum guard re-pins. Full build `LeanNCD Tests JaxExperiment`: green, 8843 jobs. |
| next | New fixtures F1-F8 in `ScatterGeometryTest.lean` + mutation manifest. |
| next | `conditionCount fI2 == 0` guard (found by mutant 04, below) + manifest expects copied from observed failures. |
| last | This ledger. |

## Production changes (commit 1)

* E1: deleted `constUnitPrefix`, `IdxExpr.isConstUnit` (`DSL/Ast.lean`), `checkReservedAxisNames`
  (`DSL/Pipeline/Structural.lean`) and its two uses in `DSL/Compile.lean` (`TLProgram.compile`,
  `compileToScheduled`), `CompileError.reservedAxisName` (`Exec/Uid.lean`; no match arms existed).
  `lowerConstSlots` (Structural.lean) now spells the synthetic axis `"#const" ++ toString u` as a bare
  literal, display only; nothing reads it.
* E2: `LHSSlot.boundedScatter` renamed `LHSSlot.collectable` (`DSL/Ast.lean`): `.free`/`.freeNorm` true,
  `.affine (.const _)` false (by constructor), any other `.affine _` true, scan slots false. Callers
  `boxedSingleGroups` (scatter arm) and `checkWriterGroup` (`DSL/Pipeline/Collect.lean`) renamed; the doc
  comment on `boxedSingleGroups` updated. Rename cost: 3 call sites + 1 doc + AGENTS.md (not touched, T3).
  `checkCollectorShapes` needs no new arithmetic: it calls `LHSSlot.outExtent` per slot, and F1-F4 pass.
  Raw `.affine (.const _)` reachability: NOT reachable through `compile`/`compileToScheduled`.
  `lowerArith` lowers every raw constant of a plain `.assign`/`.scatter` (`lowerConstSlots`); the only
  statements that keep a raw constant carry a scan slot, and `plainAt?` (the group collector's view) does
  not see scan bodies. Pinned by F8 on a hand-built schedule (`validateScheduled`), `multiWriterScatter "S"`.
* E3: `declaredShapeWins` (`Semantics/Source/Differential.lean`) is now just `!sourceUIDs.any
  destUIDs.contains` (the `bounded` filter deleted). Caveat: it does not test `!declaredAxes.isEmpty`
  like production's `boxed`; for a rank-0 destination with a non-empty write it is vacuously true
  (pre-existing for single-axis forms; now also constants). Other predicates restating the collector rule:
  `derivedShape`, `nonBareWrite`, `detectConditions` do NOT (they call `outExtent`; `detectConditions` only
  restricts to single-writer tensors). The restating ones are in TEST code:
  `test/Semantics/OracleSortRules.lean` `bounded` (predictor of refusals, used by `predict` and
  `singleBoxed`), updated here to `free | freeNorm | affine _ => true`. A shared predicate with
  `boxedSingleGroups` did NOT fall out cheaply (the oracle works from `AdmittedStatement` forms, the
  predictor from `LHSSlot`s, collector from `LHSSlot`s with env): parked, about 0.5 dispatch, low value.
* E4: scan-local constant/multi-axis stays refused; existing pins were already present
  (`StructuralTest.lean` "A statement that carries a scan slot..." and the two pins after it:
  `overlappingScatter` in `lowerArith`, preflight `checkScanScatterLHSSlot`). No new pin added (F9).

## P1: guards that failed after E1+E2+E3, and their re-pins

Full build after E1-E3 failed (`error: build failed`). Lake SKIPPED dependents: `B5bBoxTest`,
`B5cSingleBoxTest`, `ScatterGeometryTest` never ran until `B5BoundaryTest` was fixed, so a second round of
failures appeared only after the first fixes. Failing modules and re-pins (before -> after):

| Guard | Pinned before | After (intent kept / changed) |
| --- | --- | --- |
| `StructuralTest` ~253 | synthetic axis name starts with `constUnitPrefix` | `u == u'` only (the slot axis is the declared synthetic axis; the name test is gone) |
| `B5BoundaryTest` 78-79 `twoAxes`, `explicitConstant` | group refused `multiWriterScatter` | `sourceError == none` (admitted) |
| `SourceDifferentialScatterTest` `fI1`,`fI2`,`fMask [5,6]` | tag `known:extent` | `parity` (observed) |
| same, `conditionCount fFbig` / `tag fFbig` | 1 / `known:extent` | 0 / `parity` |
| `OracleSortRulesTest` C1 class counts | `[222,195,88]` | `[281,186,38]` (same 505 programs) |
| same, `concreteC1.length` and histogram | 81, `[writerExtentExceedsBox 81]` | 99, `[writerExtentExceedsBox 99]` |
| same, supplemental row "explicit constant scatter groups remain unsupported" | `.error multiWriterScatter` | admitted, `.ok []`, `runs := [real, real]` |
| same, `strictC1Tags` contains `multiWriterScatter`; pair with `writer 4 .max` tagged `multiWriterScatter` | true / true | `multiWriterScatter` dropped from the C1 list (+ negative guard); the pair is `accepted`. Strict coverage of the constructor is the predicate row (`uncoveredStrict` still passes) |
| `OracleMixedRefusalTest` 149-150,156-157,171,194,197 | `multiAxis`/`constant` groups were the `multiWriterScatter` refusal controls (parity, typed path false `nativeFailure`, split-leg mismatch) | accept neighbours (`classOf == "none"`, mismatch vs `"accepted"`); the false-`nativeFailure` rows deleted; the split-leg pair uses `castDirect` vs `r16a` (`sortCastUnsupported` vs `multiWriterAlgebra`). No refusal control for `multiWriterScatter` remains in this file: the only surviving source of it is a predicate destination, which the source oracle refuses (`UnsupportedSource.predicate`), so a source-admitted program cannot reach it |
| `ScatterGeometryTest` `convTwo`; `convBoxed` shapes/groups; `S3` boxed shapes/groups; the three `multiWriterScatter` group pins; plan-field decl list; A2 reserved-name pins | refusal / derived shape `[6]`,`[4]` / not collected / `reservedAxisName "#constUser"` | `none` / declared `[8]` all legs / collected `["S"]` / `#constUser` compiles through both chains and behaves as an ordinary axis (F7 reversal) |
| `B5cSingleBoxTest` 138-141 `groupsOf` list | `multiAxisOne`, `constOne` -> `[]` | -> `["S"]` |

Harness hazard: those two `groupsOf` entries were `[]` partly because `multiAxisOne` has an undeclared
axis `j`; it now yields `["S"]`, so it compiles (observed), not vacuous.

## P2: accepted programs whose published shape changes (B-D3)

Observed through the re-pins: `convBoxed` (`a+b`, `k = 8`): `[6]` -> `[8]`; `S3` pinned 8 (`S[3]`): `[4]` ->
`[8]` (both `.scatter` and `.assign` spellings); `SourceDifferentialScatterTest` `fI1`, `fI2`, `fMask`,
`fFbig` (declared-too-big constant / multi-axis single writers): derived shape -> declared shape, so
`known:extent` -> `parity`. No other existing accepted program moved (the full build is green with only
the re-pins above). Programs now ACCEPTED that were refused: every group containing a multi-axis or
constant writer (`twoAxes`, `explicitConstant`, `convTwo`, `S3` pairs, C1 corpus 59 more programs).

## P3: other users of the deleted names

`rg -n` over the repo excluding `papers/` and `.lake`: only `leanncd/test/Eval/Plan/ScatterGeometryTest.lean`,
`leanncd/test/DSL/Pipeline/StructuralTest.lean` (both re-pinned) and `leanncd/LeanNCD/DSL/AGENTS.md` lines 26
and 114 (docs for T3: the Collect row says explicit-constant and multi-axis keep `multiWriterScatter`, and
the Pitfalls entry describes the marker and the reservation; both now false). Nothing in `leanncd/spikes`.
`papers/` also mentions the marker (slice A record and design notes: history, not edited).

## Fixtures (commit 2), all in `test/Eval/Plan/ScatterGeometryTest.lean`

All pass on reference, checked f64 and checked f32 through `agree` (bit equal). Values were first written
from the arithmetic and then CONFIRMED by the real run (the guards pass; no value was adjusted to fit), so
they are observed outputs, not only derivations. Helper donors: `cstProg`/`pinAll` -> `grpN`, `convOf`'s
slot -> `sumSlot`, `cst`, `facA`/`facAB`, `shapesOf`, `refShape`/`planShape` (B5NativeTest).

| Id | Program | Observed |
| --- | --- | --- |
| F1 | `S(k)`, `k=8`: `S[3]:=A[a]` twice + `S[a]:=A[a]` | shape `[8]`; `[1,2,3,24,0,0,0,0]` (24 = 10+10+4; overwrite readings give 4 or 10) |
| F2 | `S[a+b]:=A*B`, `S[3]:=A[a]`, `S[a]:=A[a]` | shape `[8]`; `[2,14,126,248,340,400,0,0]` |
| F3 | tropical: `S[a+b]` max-plus conv, `S[6]:=maxA` | `[2,11,101,102,103,104,4,-inf]` |
| F4 | boxed single const (`pinAll 8 S3`) / multi-axis (`convBoxed`) | `[0,0,0,10,0,0,0,0]` / `[1,12,123,234,340,400,0,0]`; exceed box: const box 3 -> `writerExtentExceedsBox "S" 1 0 3 4`, `a+b` box 5 -> `writerExtentExceedsBox "S" 1 0 5 6` (reference and checked f64 and f32) |
| F5 | `S(a)` + `S[a+b]` (D5, multi-axis) | shape `[6]` (derived) in all legs, `groupsOf == []` |
| F6 | unpinned `conv` + bare `S[a]` | `writerExtentMismatch "S" 2 0 6 4` (reference and checked); two `conv` writers accepted, `[2,24,246,468,680,800]` |
| F7 | `#constUser` axis | compiles through `compile` and `compileToScheduled`; `[1,2,0,0,0,0,0,0]` all legs |
| F8 | raw `.affine (.const 3)` writers in a hand-built schedule | `validateScheduled` -> `multiWriterScatter "S"` |
| F9 | scan-local constant | already pinned (E4), none added |

## Mutants (manifest `additive_scatter_geometry_b_mutations_post.json`, 9 entries, `--check` OK)

First run (expects copied from observed logs afterwards): mutated build FAILED for 8 of 9. Mutant 04
(oracle excludes constant writers again) SURVIVED: `tag` guards cannot see the predictor, because the native
legs now publish the declared shape and never `confirm` a predicted condition. Fixed by
`#guard conditionCount fI2 == 0`. KILL SITES (the first failing guard):
01 `B5BoundaryTest:80`, 02 `B5BoundaryTest:81`, 03 `B5cSingleBoxTest:139`, 04 (after the fix)
`SourceDifferentialScatterTest:185`, 05 `SourceDifferentialScatterTest:181`, 06 `B5cSingleBoxTest:113`,
07 `ScatterGeometryTest:474` (F8), 08 `B5bBoxTest:61`, 09 `B5NativeTest:182`.

MASKING (important for the plan): `ScatterGeometryTest` imports `B5cSingleBoxTest` <- `B5bBoxTest` <-
`B5BoundaryTest` <- `B5NativeTest`. When a mutant breaks an upstream module, Lake never builds
`ScatterGeometryTest`, so only mutant 07 is killed BY the new fixtures; for 01-03, 06, 08, 09 the kill is
by an upstream (re-pinned or pre-existing) guard and the F1-F6 fixtures' independent kill power is
UNVERIFIED by the runner. Whether F1-F6 would also kill each was not measured (would need per-file
`lean-file.sh` against each mutant, about one extra dispatch). Final run (`mutation-manifest.sh`, all 9 entries, corrected expects): 9/9 killed, every verdict PASS; the
tree was clean afterwards. (An accidental first launch with stale expects was stopped with TaskStop and the
tree verified clean before the real run.)

## Surprises and parked

* Stale predictor: `OracleSortRules.predictedExtent` still uses the legacy sum rule for a multi-axis slot
  (`a+b` over 4,3 -> 7, production gives the exact reach 6). Unexercised today (no shaped corpus program
  has a multi-axis writer reaching it; the 99 concrete C1 programs all fail the box test either way) but
  now reachable since groups admit multi-axis. Parked, about 0.3 dispatch.
* `declaredShapeWins` ignores rank-0 destinations (see E3).
* Stale comment in `SourceDifferentialScatterTest` above `fI1` (lines ~150-156) still says "slice B closes
  it"; the pins below it are correct. Docs sweep for T3 with the AGENTS.md lines.
* The oracle path cannot reach `multiWriterScatter` any more (predicate destinations are refused earlier).
* `lake build` of one module does not print the failing value of a `#guard`; use `#eval` or `lean-file.sh`.

## Budget

BREACH: well over 60 tool calls (about 125) and a large context (the Intent-Layer hook re-attached a long
AGENTS.md excerpt on every `Edit` of a DSL file, which dominated). The reason was the re-pin ripple:
15 guards in 7 test modules, one of them (OracleMixedRefusalTest) needing a redesign. The plan should split
the re-pins into their own task (T1a) from the fixtures (T1b).

## Dispatch 2 (surface)

### Identifiers @ file, per commit
Commit 3 (`feat(dsl): ... surface`):
* `declare_syntax_cat tl_axis_term`; `syntax:max ident : tl_axis_term`; `syntax num "*" ident : tl_axis_term`;
  `syntax:55 tl_axis_term (atomic("+" tl_axis_term))+ ("+" num)? : tl_lhs_slot`;
  `syntax:max "=" num : tl_lhs_slot` @ `leanncd/LeanNCD/DSL/Syntax.lean` (just above the `tl_lhs_slot` rules).
* `elabTLAxisTerm` (new, `Syntax -> MetaM (Int x AxisSpec)`) and two new FIRST arms of `elabTLLHSSlot`
  (multi-axis via `$t:tl_axis_term $[+ $ts:tl_axis_term]* $[+ $b:num]?`; constant via `= $n:num`)
  @ `leanncd/LeanNCD/DSL/Elab.lean`. Every pre-existing arm is byte-unchanged.
* Parse/elab pins U1, U2, U3, U5 (elaboration half) appended to `leanncd/test/DSL/ParseProgramTest.lean`
  (helper `slotsOf`, axes `axA axB axC axX` built from the file's `ax0`).
* NO guard re-pins were forced (the full build is green with no existing test edited).
Commit 4: `leanncd/test/Eval/Plan/ScatterSurfaceTest.lean` (imports only `Eval.Plan.B5NativeTest`), registered in
`leanncd/lakefile.toml` after `Eval.Plan.ScatterGeometryTest`; 8 mutants SGB-T3-01..08 appended to
`papers/semantics/additive_scatter_geometry_b_mutations_post.json`; this section.

### Observed parse results (verbatim `#eval`, AxisSpec shown as `a`=`{name:="a",uid:=0,kind:=real}`)
* `S[a + b]` -> `.affine (.affine 0 [(1,a),(1,b)])`; `S[2*a + b]` -> `[(2,a),(1,b)]`, bias 0;
  `S[a + 2*b + 3]` -> bias 3, `[(1,a),(2,b)]`; `S[a + b + c]` -> three terms; `S[a + b + 3*c + 5]` -> bias 5, `[(1,a),(1,b),(3,c)]`.
* `S[=3]` and `S[= 3]` BOTH -> `.affine (.const 3)`; `S[3]` -> `.iterAt {name:="",uid:=0,kind:=nat} 3`.
* Existing forms, one program: `x`->`.free`, `x .`->`.freeNorm`, `3`->`.iterAt`, `x +1`->`.affine (.shift x 1)`
  (NOTE: not `.iterNext`; the `elabTLLHSSlot` docstring says `.iterNext`, which is pre-existing and wrong),
  `x + 2`->`.affine (.shift x 2)`, `2*x`->`.affine (.scale 2 x)`, `2*x + 3`->`.affine (.affine 3 [(2,x)])`.
* `S[a + a]` -> `[(1,a),(1,a)]` (two terms, not merged at parse); `S[0*a + b]` -> `[(0,a),(1,b)]`.
* `S[a + b +1] := ...` is a PARSE ERROR (`unexpected token '+1'; expected ']'`): `+1` is a single token that
  wins the tokenizer, so a trailing spaced `+1` cannot be a bias. `a + b + 1` (spaced) is fine.

### Precedence / ambiguity findings
* No ambiguity observed. The new rule needs >= 2 axis terms, and a lone `num` is not a `tl_axis_term`, so
  `x + n` and `n*x + m` can never match it; the new rule is the only one matching `2*a + b` and `a + 2*b`
  (the old `n*x+m` / `x+n` rules fail at `b`; longest match decides). The `atomic("+" tl_axis_term)` is
  needed: without it the many1 loop would commit to `+` and die on the bias numeral `a + b + 3`.
* Precedence `:55` for the new rule is not load-bearing (its leading item is a category, not `tl_lhs_slot`).
* `bias` is a reserved token (from `linear ... bias`): a Lean local named `bias` in the elab arm fails to parse
  (cost one rebuild); the arm uses `c0`. An axis NAMED `bias` cannot appear in a slot (pre-existing).
* `$[+ $ts:tl_axis_term]*` works as the quotation pattern for the `(...)+` (many1) loop.

### `[=3]` tokenization
`S[=3]` tokenizes and parses without a space; `S[= 3]` also does. No fallback needed, no existing parse changed
(`axis a : N = 3` uses `=` in other categories; the full build is green).

### Fixtures: observed values, donors
* U1/U2/U3/U5-parse: `ParseProgramTest` (values above). Donors: the pre-change arms for U2.
* U4 `convSurf` (`S[a + b] := A[a] . B[b]`, a=4,b=3, A=[1,2,3,4], B=[1,10,100]): shape [6], cells
  [1,12,123,234,340,400] in ref, checked f64, checked f32; bit-equal to hand-built `convProg` (donor `ScatterGeometryTest.convOf sumSlot`).
* `biasSurf` (`S[2*a + b + 1]`): shape [10], cells [0,1,10,102,20,203,30,304,40,400] in all three legs.
* U4 `f1Surf` (donor F1: `S[=3]`, `S[=3]`, `S[a]` into `k = 8`): shape [8], [1,2,3,24,0,0,0,0] in all three legs; `compErr == none`.
* `constPinSurf` (`S[=5] := A[a]`, k=8): [0,0,0,0,0,10,0,0] in all three legs.
* `constLoneSurf` (`S[3] := A[a]`): `preflight CapabilityError.noAdvancingAxis "S"` (the lone numeral is a scan base).
* U5 observed (no new validation): `a + a` ACCEPTED, behaves as `2*a`: shape [8], [111,0,222,0,333,0,444,0]
  in all legs (the repeated axis is merged downstream, stride-2 rule). `0*a + b` ACCEPTED: shape [3], [10,100,1000]
  (`a` becomes a collision axis; contrast the single-axis `Out[0*i]`, rejected out of range). Unsized `a, b`
  (no `= n`) -> same cells as `convSurf`. Empty axis `b = 0` with `B = []` -> shape [4], all zeros, all legs.
  An empty axis with a NON-empty input `B` (shape mismatch) makes all three legs return `none` (not pinned).
* U6 (linear scan bodies; with `relu` the nonlinear-scatter refusal `unsupportedNonlinScatter "G"` fires FIRST and masks):
  baseline `G[j,0]; G[j,l +1]` accepted. `G[=2, l +1]` -> `compile CompileError.overlappingScatter "G"`;
  `G[=1, 0]` base -> `overlappingScatter "G"`; `G[j + k, l +1]` -> `preflight CapabilityError.multiAxisScatterLhs "G: affine LHS slot"`.
  So the SURFACE-built constant slot in a scan is refused by `overlappingScatter` (compile), not by the
  programmatic `checkScanScatterLHSSlot` constant refusal that `CompileTest:188` pins on a hand-built schedule
  (the surface route lowers the constant first). Both fail loudly; pinned in `ScatterSurfaceTest`.

### Mutants (`--check`: 17 entries OK; real run over all 17: 17/17 PASS, file byte-identical, restore build green)
Engine entries SGB-T1-01..09: 9/9 still PASS. New:
* SGB-T3-01 drop bias: ParseProgramTest + ScatterSurfaceTest (both seen failing).
* SGB-T3-02 reverse term order: ParseProgramTest ONLY (the affine function is order-invariant, so surface cells are unchanged; stated honestly).
* SGB-T3-03 drop terms after the first: ParseProgramTest + ScatterSurfaceTest.
* SGB-T3-04 coefficient ignored: ParseProgramTest + ScatterSurfaceTest.
* SGB-T3-05 `=n` -> `.iterAt`: ParseProgramTest + ScatterSurfaceTest.
* SGB-T3-06 `x + n` through the multi-axis constructor, T3-07 `n*x` through it, T3-08 `n*x + m` loses its bias: ParseProgramTest only.
`expect` strings are the prefix `error: test/DSL/ParseProgramTest.lean:` (resp. `.../ScatterSurfaceTest.lean:`), NOT a line number:
the manifest output only showed the first failing guard line for T3-08 (`ParseProgramTest.lean:202:0`); line pins would be brittle
against the plan's edits to those files. Weaker than the engine entries' line pins; the plan author may tighten after the patch lands.
Not killed in the T3 manifest (no upstream test is built by its targets): a mutant that breaks `Out[0*i]` single-axis behaviour
is covered by CompileTest/ScatterCompileTest S9 in the full build only.

### S-D: docs that now lie or enumerate slot forms (value-grep, counts from `rg` over leanncd/*.lean, *.md)
* `leanncd/LeanNCD/Eval/Plan/Error.lean:279`: "`elabTLLHSSlot` parses only `n*x+m`-shaped single-axis slots; surface ..." (1) LIES now.
* `leanncd/test/Eval/Plan/ScatterGeometryTest.lean:6`: "(the surface cannot say a multi-axis slot; slice B adds it)" (1) LIES now;
  also its header comments on the programmatic `cst`/`sumSlot` donors say they are the only way to build these.
* `leanncd/LeanNCD/DSL/Elab.lean` `elabTLLHSSlot` docstring (list `x`, `x .`, `n`, `x +1`, `n*x, x+n, n*x+n`) (1): omits multi-axis and `=n`;
  its `x +1 -> .iterNext` line was already wrong (code gives `.affine (.shift x 1)`).
* `leanncd/LeanNCD/DSL/Syntax.lean` header lines 215-223 area: no header enumerates slot forms beyond the rules themselves (0 stale); the new comments are mine.
* `leanncd/LeanNCD/DSL/AGENTS.md` (9 hits for `multi-axis|constant slot|slice B|surface`; line 114 and the "constant LHS slot ... until slice B"
  Pitfall bullet) (>= 2): the Pitfall says a constant slot is "a placement over a `#const` unit axis ... until slice B" (engine half already made it stale,
  surface now adds `S[=n]`); no entry for the new `tl_axis_term` category.
* `leanncd/LeanNCD/Semantics/Source/Differential.lean:201` ("whatever the writer's slot forms (single-axis, ...") (1): check wording, likely still true.
* `leanncd/test/DSL/Pipeline/CollectTest.lean:350,452` ("programmatic only", "The surface cannot reach these shapes") (2): unrelated (generated names / scan names); do NOT edit.
* `leanncd/test/DSL/SyntaxTest.lean`, `leanncd/AGENTS.md`: 0 hits for any slot-form enumeration; `docs/test_portfolio.md`: 0 relevant.
* Lean-source `tl_lhs_slot|elabTLLHSSlot` hits: Elab.lean 12, Syntax.lean 12 (mostly new), ParseProgramTest 1.

### Parked (Rule 14)
* Validation of degenerate slots (repeated axis `a + a`, zero coefficient `0*a + b`): not needed by the goal; behaviour pinned as observed.
  If wanted: a `checkSlotTerms`-style guard in `elabTLLHSSlot` or `lowerArith`, ~1 dispatch (Direct path) plus re-pins of the two U5 pins.
* Fix the pre-existing wrong `x +1 -> .iterNext` docstring line: 0 dispatches beyond the docs task.
* Tighten the T3 `expect` strings to line pins: ~0.3 dispatch after the plan's patches fix line numbers.
* `S[a + b +1]` parse error is a token-level surprise; document in the docs task (no code change).

### Budget
Tool calls: about 66 (over the 60 cap; the overrun is three scratch-observation rounds, one unusable `bias` rebuild, and four manifest waits).
Context peak not measured by the harness here; estimated well under 250k (no whole large files read; the Intent-Layer excerpt re-attached on 5 DSL edits).

### Full build
`lake-build.sh <lncd> LeanNCD Tests JaxExperiment` on the final tip: Build completed successfully (8844 jobs; engine tip 8843, +1 = ScatterSurfaceTest).

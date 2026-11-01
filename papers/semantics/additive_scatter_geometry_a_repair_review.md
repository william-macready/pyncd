# Review of 19046d3d..deae5c78 (scatter geometry slice A repair: A1 outExtent, A2 reserved `#const`)

Read-only review; about 35 tool calls. Items 1, 2, 3 found no defect; items 4, 5, 6 found P3 nits only.

## Item 1 (A1 completeness): none found

`LHSSlot.outExtent` multi-axis arm now tests emptiness over `nonzero` only. Traced each probe:
- Sparse slot vs dense row (`scatterPlacementSlot` over `scatterSourceAxes` = slot axes ++ read axes, every axis sized):
  `legacy` is `c0 + sum c*size` over `cf`; a zero-coefficient or repeated entry contributes the same total
  to both forms. The single-nonzero arm reads only `sz u` of the nonzero axis, so other empty axes are inert.
  `a + a - b`: `idxDensify` coalesces to `[2,-1]` on both sides. `a - a` coalesces to `[0]`, `nonzero = []`,
  falls to `_ => some legacy` on both sides.
- Negative coefficients: `affineImageBounds` is a commutative fold over (coefficient, size) pairs, so
  term order (first-seen sparse vs positional dense) is irrelevant. Nonzero axis of size 0: `legacy` on both.
- `.const n` arm: the dense side always builds `.affine`, but `lowerArith` rewrites the constant to a unit-axis
  placement whose stride-aligned extent is `n+1`; a negative constant clamps to 0 on both (`(c0+1).toNat`).
- Unsized zero-coefficient axis: sparse form gives `none` (`unsizedScatterOutput`); the checked path fails first in
  `resolveSizeOrFail` on the same axis (all slot axes are in `srcUids`). Two rejections, no extent disagreement.
No counterexample.

## Item 2 (A2 completeness): none found

`checkReservedAxisNames` uses `TLProgram.axisNames` = `axisSpecs` = `TLProgram.traverseAxes`, which visits every
`Decl` (axis, iter, tensor axis lists) and every `Stmt` (LHS slots, RHS factors, masks, `recurMorphism` axis). Scans
are not a source `Stmt` constructor (`finalizeScans` derives them), so no axis hides inside a scan body.
Paths to `isConstUnit`/`boundedScatter` (`boxedSingleGroups`, `checkWriterGroup`):
1. `TLProgram.compile`, `TLProgram.compileToScheduled` (used by `Eval/Entry.lean`, `NativeLegs.checkedWithInputs`,
   all tests/experiments): covered, check is first.
2. Hand-built `ScheduledProgram` into `prepareEvalPlan`/`evalScheduled`/`route` (which reach
   `collectorShapeObligations`/`desugarMultiWriters`): not covered; documented residual.
3. Oracle `resolveSource` (`Semantics/Source/Adapter.lean`: `assignUIDs` then `resolveDecls`): not covered, but it
   never calls `isConstUnit`; `declaredShapeWins` (`Differential.lean`) is structural (`f.2.isEmpty`, nonzero-axis
   count), not a name test, so the oracle is unaffected by the spelling.
4. `test/DSL/Pipeline/RouteWeaveTest.lean` has a private re-spelled chain without the phase (test only, no claim of
   equality with `compileToScheduled`).
Pipeline-minted names: only `constUnitPrefix ++ toString u` (lowerArith, after the check). Other `#` names are
`T#k` tensor names (Collect), and `###..` fixed names (RouteFragments), neither an axis, neither starts `#const`.

## Item 3 (phase placement, CompileError matches, oracle): nothing wrong; one note (F5)

`compile` is `do let p <- checkReservedAxisNames p; assignUIDs p ...` and `compileToScheduled` is
`checkReservedAxisNames >=> assignUIDs >=> ...`: same position (first), so the `Bridge/Agreement.lean` unfolding is
sound. No exhaustive `match` on `CompileError` exists (the only matches in `Adapter.resolutionOrigin` and tests use
wildcard or equality arms; Repr/DecidableEq/BEq/Inhabited are derived).

## Item 4 (fixtures)

Under A1 revert (terms over every `coeffs.zip us` entry):
- `scatterDestExtent #[4,3,0] #[1,1,0] 0 == some 6`: FAILS (gives 7). Discriminates.
- `scatterDestExtent #[4,3,0] #[1,1,1] 0 == some 7`: passes both ways (neighbour guarding over-fix). Pins nothing about A1.
- `emptyShapesOf convEmptyC == (some [6], some [6], some [6])`: FAILS on the two checked legs (7). Discriminates.
- `agree convEmptyC ...` zero cells: FAILS (checked publishes 7 cells). Discriminates.
- `emptyShapesOf convEmptyFree == [6,0]` x3: FAILS (dense row of the `a+b` slot over `[4,3,0]` is `[1,1,0]`, so 7 not 6). It does
  discriminate A1, but through the same dense-row mechanism as `convEmptyC`; its added value is only the empty axis
  being a real nonzero-coefficient axis of a sibling slot.
A2: the `constUser` accept row passes with the check disabled (no `#`), so it pins only that ordinary spelling is
unaffected. The `#cons` row also passes with the check disabled; it only guards prefix drift. The two reject rows
(`compileToScheduled`, `compile`) FAIL with the check disabled. Discriminating.

## Findings

F1 | P3 | leanncd/LeanNCD/Eval/Eval.lean `scatterOutShape` docstring | The edited docstring keeps "(`sizes[u]` defaults to 0 for an unseen UID.)", contradicting the code directly below it: `outExtent` returns `none` for an unsized axis and `scatterOutShape` throws `unsizedScatterOutput` ("FAIL LOUD rather than defaulting"). Pre-existing sentence, but the commit rewrote this docstring and left it. | `sizes[u]?` is the lookup, `none` -> `throw (.shape (.unsizedScatterOutput sl))` | Delete the parenthetical or say "an unseen UID is an `unsizedScatterOutput` error".

F2 | P3 | leanncd/LeanNCD/DSL/AGENTS.md (constant LHS slot bullet) and leanncd/LeanNCD/Eval/AGENTS.md ("Every scatter extent MUST equal `LHSSlot.outExtent`") | (a) The DSL bullet edited by this commit still says "groups and boxed single writers still refuse it (`multiWriterScatter`, derived shape wins)"; only groups throw `multiWriterScatter` (`checkWriterGroup`); a boxed single writer is silently not collected (`boxedSingleGroups`, `ls.all boundedScatter` false). The sibling sentence the same commit wrote in `Eval/Plan/AGENTS.md` is precise, so the two now disagree. (b) `Eval/AGENTS.md` says "other forms keep the linear fallback", which has been false for 2+ nonzero axes since M1 (exact reach). Not in the diff; A1 touches that very rule. | `rg multiWriterScatter` shows throws only in `Collect.lean` `checkWriterGroup`; `ScatterGeometryTest` `pinAll 8 S3` publishes `[4]` with no error | Reword (a) to "groups throw `multiWriterScatter`; a boxed single writer is not collected"; add the multi-axis arm to (b).

F3 | P3 | leanncd/LeanNCD/DSL/Compile.lean `TLProgram.compileToScheduled`; leanncd/LeanNCD/Eval/Plan/Compile.lean `capabilityPreflight` docstring | Two edited lines run past the surrounding 100-column wrap (the `compileToScheduled` chain first line is about 118 columns; the `FORM error (`scatterOrAffineLhs`) rather than ... rest of this file's` line is over 130). | visual | Re-wrap.

F4 | P3 | leanncd/test/Eval/Plan/ScatterGeometryTest.lean (A1/A2 sections) | Fixture gaps, not defects: (a) no program-level accept-neighbour with the empty axis at a NONZERO coefficient (`S[a+b+c]`, `|c|=0`, legacy extent 7 on every leg); only the helper-level `scatterDestExtent ... [1,1,1]` row pins it. (b) No negative-coefficient row (`a - b + 2` with an unrelated empty axis) and no coalescing row (`a + b + 0*c`), which exercise the same `nonzero` filter. (c) No reject row for a reserved name that occurs only in a decl or only in a statement slot (the traversal covers both, but unpinned), nor a contains-but-not-prefix name (`x#const`) pinning `startsWith` over `contains`. | n/a | Add rows if cheap; optional.

F5 | P3 | leanncd/LeanNCD/Semantics/Source/NativeLegs.lean, Differential.lean | A source containing a `#const...` axis passes the oracle's `resolveSource` (no phase check) but both native legs fail (legacy `.compile (reservedAxisName ..)`, checked `.sourceCompilation`). `classify` then returns the generic `.nativeFailure`, not a `knownContractDifference`; the rendered text carries `cause=reservedAxisName`, so it is diagnosable and is not misread as `nativeDiscrepancy`/`referenceDiscrepancy`. No generator produces such a name. Accepted residual; only worth a line in `Semantics/AGENTS.md` if the corpus could ever spell it. | `Differential.lean` classify: `.failure _, _ | _, .sourceCompilation _ ... => .nativeFailure` | None required.

## Item 5 (docs commit deae5c78): all edited sentences true except noted above

Verified against code: `scatterOrAffineLhs` is thrown for the raw `.constant` class (`checkScatterAffineExpr`), so the corrected `capabilityPreflight` example is right; `multiAxisScatterLhs` is scan-local only; `multiWriterScatter` is thrown by `checkWriterGroup` for constant/multi-axis writers; the "boxed single writer runs with the derived shape, ignoring the pinned declaration" claim holds (`pinAll 8 S3` gives `[4]` on all legs, `groupsOf == []`); `s6ZeroBase` (ScanCompileTest) asserts `.scan (.scanWriteRowNotAdmitted "bad" "S" true 0 0 #[] 0)`, matching "slot admitted, whole scan refused". Only F1 and F2(a) are stale/imprecise.

## Item 6 (anything else): F3 only

Mutation manifest strings match the source text exactly. New phase runs before `assignUIDs`, so a program with both a reserved axis and another early error now reports `reservedAxisName` first; harmless.

VERDICT: PASS (no P1/P2; five P3 nits)

# Scatter-geometry slice A plan: authoring record

Evidence for [the plan](additive_scatter_geometry_a_plan.md). Kept out of the live plan so the plan stays
short. Written by dispatch 6 of 6 (plan author), from existing artifacts only: no Lean was run, no patch or
manifest was edited, no behaviour changed.

## Inputs read

The B5c plan and record (format exemplar), the design note (sections 1-8 with P0 results), the replay
verification record, the prototype ledger copy (`additive_scatter_geometry_a_files/proto_notes.md`, read in
four windows), the six patch file lists (`^diff --git` lines only, no Lean read), the manifest keys (label,
task, file, targets, expect; the T3b-01 entry) and the superseded tropical brief (first 70 lines).

## Checks run and results

- Replay head: `git log` shows `ef02e256` (verification artifacts) on top of `ef48df69` (task 5), base
  `6715e128`. The verification record's "code head" `ef48df69` and the controller's `ef02e256` are both right
  (the second adds only papers artifacts); the plan names both.
- Identifier existence (`rg -n -w` against the replay head `leanncd/`): found: `affineImageBounds`,
  `lowerConstSlots`, `isConstUnit`, `constUnitPrefix`, `isScanSlot`, `isRawConst`, `derivedShape`,
  `declaredShapeWins`, `scatterImageBounds`, `scatterRangeViolation`, `checkScatterAffineExpr`,
  `checkScatterLHSSlot`, `checkScanScatterLHSSlot`, `scatterAffineClass`, `boundedScatter`,
  `overlappingScatter`, `scatterDestExtent`, `boxedSingleGroups`, `groupsOf`, `compareSortedSource`, `classOf`,
  `yCore`, `snapG`, `conv23`, `constSc`, `constAs`, `fourLegParity`, `fD`, `fFbig`, `fI1`, `fI2`, `fMask`,
  `fOriginC`, `fSign`, `fSignOk`, `convWide`, `convMax`, `convTwo`, `convBoxed`, `crossSlot`, `bypass`,
  `scanSurface`, `scanSurfaceConst`, `twoAxes`, `explicitConstant`, `multiAxisOne`, `identityOne`,
  `transposeOne`, `zeroScale`, `s6ZeroBase`, `diagonal`, `collide`, `strided`, `checkScatterCore`,
  `freshNonZero`, `prepareEvalPlan`, `compileToScheduled`, `multiWriterScatter`, `writerExtentExceedsBox`,
  `scatterImageOutOfRange`, `scatterWriteOutOfRange`, `scatterOrAffineLhs`, `multiAxisScatterLhs`,
  `multiAxisAdmitted` (cited from the ledger, found by the identifier sweep over `Compile.lean`).
- **Not found:** `emptySource` (the ledger's case x class table names it as a B5NativeTest fixture); it was
  dropped from the plan. `LHSSlot.collapses` is correctly absent as a definition; one stale comment in
  `leanncd/test/Eval/Plan/ScatterCompileTest.lean` still names it (plan sections 2, 6 and 8 park it, 0.1 dispatch).
- `ScatterGeometryTest` exists (`ls`, 19.6K) and its glob is in `leanncd/lakefile.toml`; `SourceSortedDifferentialTest`
  glob present. The scripts `lake-build.sh`, `mutation-manifest.sh`, `lean-file.sh`, `prepare-worktree.sh`,
  `SKILL.md` of `new-slice` exist.
- Paths: each of the 20 paths in the plan's hash table comes from the verification table and appears in a patch
  `diff --git` line (the T1 patch lists 7 paths, T2 4, T3a 8, T3b 3, T4 1, T5 7).
- Added lines of all six patches contain no `File.lean:NNN` (`rg` exit 1); the plan itself has none and no code
  fences (both `rg` checks exit 1).
- Value-grep gate pre-run at authoring: `legacy linear` hits at `Ast.lean` (doc of the fall-through) and
  `B5NativeTest` (a comment); `collapses` hits are English prose except the stale `ScatterCompileTest` comment;
  `extent 7` hits in `ScatterCheckTest` (correct) and `SourceSortedAuditTest` (unrelated); no `derives 7` or
  `derives 16` anywhere; `overlappingScatter` appears in `Structural.lean` (4 hits) and `Uid.lean`.
- Numbers: every value in the plan was copied from the ledger or the verification record, none derived.
  The one hand-derived remark I wrote (a max-times comparison at cell 1) was removed and turned into review
  question (b).

## Contradictions between inputs (surfaced, not averaged; Rule 7)

1. The dispatch brief says Task 2 adds `ScatterGeometryTest` and its lakefile glob; the patches and the
   verification table say Task 1's patch does (lakefile owner T1; `T1-extent.patch` contains the new file and
   the glob). The plan follows the patches; Task 2 only extends the module.
2. The superseded tropical brief (precondition 1) says the single remaining `overlappingScatter` throw sits in
   the scan branch of `lowerConstSlots`; the replay head has it in `lowerArith`'s `.assign` arm (scan slot plus
   raw constant), and `lowerConstSlots` only skips scan statements. The plan describes the head.
3. The ledger names tasks and patches differently from the final structure (T3b-scan-pin, T5-tropical,
   T4-docs; ledger T5 expect strings carry line numbers). Final: pin folded into T3b, tropical is Task 4, docs
   Task 5, expect strings have no line numbers (verification record). The plan follows the final structure.
4. The ledger's self-reported budgets (about 115, 60, 29 calls) differ from the controller's harness counts (138,
   118, 53 then 83, 29). The plan uses the harness counts.
5. The design note says (d), (d'), (f') become parity fixtures; the ledger shows the constant fixtures with a
   declared extent above `n+1` (`fI1`, `fI2`, `fMask`) become `known:extent`, not parity. The plan states the
   ledger's observed values.
6. Per-task job counts: the ledger's 8841 (T1, T2) are `LeanNCD Tests` targets and 8843 includes `JaxExperiment`;
   this is my inference, not measured on the replay, so the plan quotes only the final 8843.

## Not done

No review lens has read the diff. Authoring tokens were not measured. Per-task builds were not replayed. The plan
is longer than its 300-line target (about 540 lines after the long observed-value paragraphs; under the 800 cap).
Not verified by me: that the manifest `expect` strings still match (the controller ran them); the exact module
list of each targeted build (taken from the ledger and the patches' test files, not run).

## Authoring discipline applied

Read-before-write, windows only, identifiers grepped, paths listed, numbers copied. Tool calls used: 40 of the
40 budget (the 32-call stop line was passed during the verification greps; the plan body was complete before
then). Sizes: plan about 540 lines, this record about 75 lines.

# f32 flip slice 2 - Reviewer B (do the migrated tests still mean what they meant)

Base 44296ad, HEAD 0911c8f. Read-only review by diff; no builds run (controller's green build trusted).

## Findings

No Critical findings. No Important findings that change a verdict.

### Minor 1 - line-number reference in added text
- File: `leanncd/test/Eval/Plan/DifferentialTest.lean`, comment above `checkEntry`.
- Claim: the added comment says "Gen's own guard (`Gen.lean` line 165)". The slice rule is no `File.lean:NNN` style references in added text; this is the same kind of brittle pointer in prose form.
- Failure scenario: any edit to `test/Eval/PropertyOracle/Gen.lean` makes the pointer wrong with no build signal.
- Verified: rg of added diff lines for `\.lean:[0-9]|[Ll]ines? [0-9]+` - exactly one hit. No `File.lean:NNN` in any added .md line.
- Fix: name the construct (`Gen`'s `explicitF64` guard) instead of a line.

### Minor 2 - accidental whitespace edits in CompileTest (commit 77eac42)
- File: `leanncd/test/Eval/Plan/CompileTest.lean`: `def isOk:` (space before colon removed), `decls :=[` in `multiReductionSched` and `cacheSchedWith`.
- Claim: unrelated formatting changes, violates "every changed line traces to the task". Harmless to semantics.
- Verified: `git diff 77eac42^ 77eac42`.

### Minor 3 - leanncd/AGENTS.md rewrites two unrelated "Concrete precedent" paragraphs
- File: `leanncd/AGENTS.md` (Small subsystems section: Wave-B unification and S-A scatter precedents condensed from ~7+14 lines to ~3+7).
- Claim: not part of the flip (scope gate, Rule 14). Content stays factually consistent but drops detail (e.g. "Two bugs, opposite lessons" sentence). If it was a size-budget compaction it should be said so; otherwise it is scope creep inside a doc node.
- Verified: `git diff 44296ad HEAD -- leanncd/AGENTS.md`.

### Minor 4 - residual plain `.tensor "Y"` in rejection fixtures, now f32 next to explicit-f64 X
- File: `CompileTest.lean`, `plainAxisKindSched` users ("plain iterAt on a real axis", "plain iterNext on a real axis", "plain freeNorm on a nat axis", "axis kind before predicate output", `dtypeSourceOrderSched`), `scanAxisKindSched`, `rankSched` users.
- Claim: `plainAxisKindSched`'s `X` was changed to `.typedTensor .f64` while these fixtures' `Y` stays plain `.tensor` (now f32), so they are dual-defect (axis-kind + mixed precision). The exact pinned errors (`iterAxisNotNat`, `normAxisNotReal`, `predicateNonlin`) still fire first, so they are not vacuous (removing the axis-kind check would surface `unsupportedDtype` and fail the exact pin). Cosmetic inconsistency only; making Y `.typedTensor .f64` like `validAxisKindSched` would make each fixture single-defect.
- Verified: read CompileTest 2436-2515; the pins are unchanged context lines.

### Minor 5 - `retag32` in EvalPlanAffineSmoke32 changes which outputs get declared; docstring and now-dead loop
- File: `leanncd/experiments/jax_bridge/EvalPlanAffineSmoke32.lean`, `retag32`.
- Claim: `explicitF64` declares EVERY undeclared used name (outputs included, axes derived from first write, affine LHS too), then `.typedTensor .f64` is retagged f32. The following `outDecls` loop (declare outputs over `.free` LHS axes) now finds every output already declared and is dead; the docstring ("every undeclared statement output gets a binary32 declaration over its own LHS axes", "undeclared extra inputs are dropped") is partly stale. Behavior difference: outputs with non-`.free` LHS slots were previously left undeclared (and so mixed-precision/rejected in the f32 path); they may now be declared and accepted, so the stride-sampled `enumPrograms` slice can differ from before. The commit message says all four drivers "exit 0 on the flipped tree", so nothing crashes; I could not run them.
- Verified: read `retag32` and `ExplicitF64.lean` (`explicitF64Decls` header). Ordering explicitF64-then-retag is correct: plain `.tensor` decls still retag via the first arm, `explicitF64`-added and explicit `.typedTensor .f64` via the new arm.

### Minor 6 - (note, not a defect) production flip count
- The brief says the production diff is only 4 flips. Production changes are: `storageConstraintOfDecl` (.tensor/.linear), `storageConstraintOfName?` (none), `dtypeOfDecl` (.tensor/.linear/none), and `compileScan`'s `stateDtypes.getD si .f32` (a fifth default site, in `Compile.lean`), plus comment edits and a lakefile glob. The `compileScan` `getD` default is only reached if `stateDtypes` is missing an index; I could not tell it is reachable, so no mutation can be expected to catch it. Worth a one-line note in the close-out.

## Answers B1-B7

B1. Every removed `#guard`/`run_cmd` was checked (24 removed assertion lines in the module diffs; list from `-.*#guard` rg). Replacements: `dtypeOfDecl`/`storageConstraintOfDecl` `.tensor`/`.linear` pins flipped to f32 in SignatureTest with the `.f64` spelling kept pinned; `ofDenseInputsForDecls []` split into an explicit-`f64` acceptance pin plus a new default pin `.storageKindMismatch "X" .float64 .float32`; `ofDenseInputs32ForDecls [.tensor "X"]` rejection became `.typedTensor .f64` rejection plus a new acceptance pin; CompileTest `f32MixedUndeclaredSched` inverted to `f32UndeclaredSched` (accept) plus `f64MixedUndeclaredSched` (the same mixed-precision error, pinned text unchanged); f64==plain equalities became plain==f32 / plain!=f64 / f64 pinned to an absolute value; `f32LinearMixedSched` replaced by `f32LinearPlainXSched` (accept) plus two reject pins with explicit `.typedLinear .f64`. StructuralTest (b) flipped to `.float32` with a new (b') f64 pin; fixture (d) `.tensor C/B` to `.typedTensor .f64` keeps the first-disagreeing-name pin meaningful. No assertion was weakened; the remaining removed guards (ScanCompileTest) only changed the call wrapper, the pinned `== some (...)` lines are untouched context. Discriminating power is preserved or strengthened throughout.

B2. Verified: all 8 `rejF32`/`rejSchedRaw` fixtures keep byte-identical pin lines (the diff shows only the `rej`->`rejF32`, `rejSched`->`rejSchedRaw`, `rejSig`->`rejSigF32` call-site lines; the `== some (.scan ...)`/`.capability` lines are context). They are not vacuous: a new baseline pair pins that the same playground (`okBase`/`okRecur`) compiles under `rejSigF32` with every tensorSig f32 (`rejF32 [okBase] [okRecur] == none`), so under an all-f32 schedule the only defect in each fixture is the malformed LHS; a homogeneous schedule cannot produce a dtype error, so no first-error shadowing is possible. The docstring's reason (any declared rank for `S` yields `rankMismatch` first) is plausible and consistent with the controller's green run. Two of the eight are `capabilityBeforeInputScatter` fixtures with `emptySig`, which fire at capability preflight before any signature or dtype logic.

B3. ScanCompileTest/AdapterTest/Adapter32Test/DifferentialTest changes are wrapper-only (`explicitF64`, `explicitF64Sched`, `tensor f64`); nothing in them was a default pin (B4 grep). Default coverage per site: `storageConstraintOfDecl .tensor`: SignatureTest pin, StructuralTest (b), CompileTest `plainIdentityPrepared` storageKind == float32, DefaultF32Test `plain` variant (4 independent places); `.linear`: SignatureTest pin, CompileTest `plainLinearPrepared` (storageKind, tensorSigs, algebra), DefaultF32Test (linear re-spelled plain in lin-scan etc.); `storageConstraintOfName?` undeclared: CompileTest `f32UndeclaredSched` and `f64MixedUndeclaredSched`, DefaultF32Test `undeclared` variant, ScanCompileTest 5b default pin; `dtypeOfDecl .tensor`/`.linear`: SignatureTest pins, CompileTest plain-spelling controls, DefaultF32Test; `dtypeOfDecl none`: SignatureTest `ofDenseInputsForDecls []` pin, CompileTest `declaredBSched` (`dtypeMismatch "A" .f32 .bool`), DefaultF32Test, ScanCompileTest 5b. Flip #1 (storageConstraintOfDecl arms) is caught by more than SignatureTest's 2 pins and StructuralTest, by inspection, via CompileTest storageKind guards and DefaultF32Test (this is by reading, not by mutation; I did not run any build).

B4. rg for `default|plain|untyped|undeclared|unannotated` near `explicitF64`/`.f64`/`tensor f64` in `test/Eval/Plan` returned only comments and two false friends (`maxPlainProg`/`minPlainProg` and `scratchThenPlainReadSched`/`statePlainReadSched`, where "plain" means non-scan/plain read, not the default). The default pins (`plainIdentitySched`, `plainLinearSched`, `f32UndeclaredSched`, `declaredBSched`, 5b playground, DefaultF32Test) are all unwrapped.

B5. `«bias»` rewrite: read the full 380bffc word diff for ScanCompileTest - every hunk is `bias :=` to `«bias» :=` inside `AffineMap` literals, nothing else (the AGENTS.md note that importing `Eval.ExplicitF64` makes `bias` a keyword token explains it). Experiments edits are all added `tensor f64 ...` declaration lines or `.explicitF64`; mechanical (see Minor 5 for retag32).

B6. See Minor 5: ordering (explicitF64 then retag) is right and plain `.tensor` decls still retag f32; the corpus the f32 driver exercises can differ for outputs with non-`.free` LHS, the `outDecls` loop is dead and the docstring partly stale. Compile-only drivers reported exit 0.

B7. Docs are consistent with code: default binary32 (`storageConstraintOfDecl`, `storageConstraintOfName?`, `dtypeOfDecl`), bool-only defaults and the reference evaluator unchanged (matches the unchanged `deriveStorageKind`/`scheduleStorageKind` and the StructuralTest (c) pin), four regressions listed identically in the DSL and Eval/Plan nodes. No `File.lean:NNN` in added markdown; one prose line reference in a test comment (Minor 1) and an unrelated condensation of two paragraphs in `leanncd/AGENTS.md` (Minor 3).

## Tool calls: about 29

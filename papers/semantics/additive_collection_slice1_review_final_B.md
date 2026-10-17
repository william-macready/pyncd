VERDICT: APPROVE WITH MINORS (no Critical; 1 Major, process-only (the mutation manifest), not a code defect; 3 Minor)

Final whole-branch review, lens (b): regression, wrongly rejected valid programs, test and doc integrity.
Code read from git objects 1088b200 (tip) and b0d37f2f (base) only.

## Hunt summary

1. **Single-writer identity: holds (CONFIRMED by reading the definitions).** `desugarMultiWriters` returns
   `(sched, [])` itself when `writerGroups` is empty. `scanWriterConflict?` cannot fire when every name
   has at most one writer node. So for such programs `validateScheduled` rebuilds `declEnv`,
   `explicitSizes` and `extNames` from the very same `ScheduledProgram`: they are identical. `route` sees the
   identical value too. `eligible`: for a name with 0 writers, `count == 0` matches the old
   `all.all (!writes)` (publications are a subset of writes). For 1 writer, `count r == 1` matches
   the old `emitted.contains r`, because `publications` dedups. Scratch is unchanged (never emitted on
   either side). B3: the base surface corpus never supplies a defined name; the only existing test that
   did is `CompileTest` (orderedTwinSched supplying `Z`). Its edit is a deliberate flip that keeps an
   accept-neighbour (`erase "Z"`). Supplying a scan's initial state has no legal use (`missingBaseCase`
   forces a base face in the node). Two scans sharing scratch, and plain + intermediate, are already
   rejected upstream (`finalizeScans`: spans-multiple-components / `duplicateScratchProducer`).
   `Unused` extra inputs pass because B3 looks only at `writes`. `DifferentialTest.checkEntry` turns any
   run error into a hard failure, so a B3 rejection inside the 3,832-case sweep could not pass silently.
2. **New rejections on route/compile: none in the corpus (CONFIRMED by script).** I parsed every
   `tlprog!`/`tl!` block under `leanncd/test`, `leanncd/LeanNCD` and `papers` at b0d37f2f. Only three
   programs have a repeated plain left-hand side: Adapter32Test fixture 4, ContractTest
   `repeatAssignProg` and DifferentialTest `repeatProg`, all `Y[i]` twice, all migrated. Every other
   repeat is a scan base + recurrence pair. `enumPrograms` writes `Y` then `Z`, never the same name.
   No program uses two scatters on one name. Base `evalScatter` builds a fresh fill-initialized tensor,
   so the old behaviour was a wrong whole-tensor overwrite; it now fails loud as `multiWriterScatter`.
3. **Scans: no change to the accepted set for legal scans (CONFIRMED).** `scanWriterConflict?` counts
   writer NODES, so base + recurrence and multi-face bases (`outputs = [G,G]`, `publications = [G]`)
   are one writer. `.scanPre` is one writer. Two scans writing one state is the parked §8 item and is
   not re-reported.
4. **f32 path: no new rejection (CONFIRMED).** An undeclared `T` gives undeclared clones, and both
   default to f32. A declared `T` gives clones of the same constructor and type (`Decl.cloneAs`).
   `explicitF64`/`evalScheduledF64` add their declarations BEFORE collection, so the clones become f64.
   The one wart is the diagnostic naming (F2).
5. **Test integrity: no weakening (iii) found.** Every edited old-behaviour assertion is a deliberate
   flip (i) with an exact replacement value, plus additions (ii):
   - ContractTest: A+B; the first write now contributes.
   - CompileTest: `#["Y","Z"]`, `privateSlots`, `definedNames`, sizes 5→6, the B3 flip plus erase-Z
     agreement.
   - DifferentialTest: values, plus a reference cross-check and the env size.
   - Adapter32Test: f32 bits for 101/202, inventory size 4, hidden slots.
   - ExecutableTest: comment only.
   - SourceDifferentialPolicyTest: F14/F15 value-compared, plus F14f32.
   - SourceDiagnosticAdmissionTest: D10 is now `fourLegParity`, 3→6.
   - RouteFragmentCorpusTest G21: the old-pipeline payload moved to `schedule`; acceptance is unchanged.
   - AcsetCodecTest: addition.

   The manifest, however, is stale; see F1.
6. **Docs: mostly true; wording issues are in F3.** No new `File.lean:NNN` reference was added to
   shipped prose. The decision note's S1 table row keeps a pre-existing `NumericalProfile.lean:120-123`
   in a line the branch edited, and those lines no longer exist (F3).

### F1 [Major] Mutation manifest expect positions for CollectTest are stale at the tip (15 entries)
`papers/additive_collection_slice1_mutations_post.json` was written for the prototype and updated only
once (f493a5e0 appended A3-M7). The fix groups then INSERTED fixtures into
`test/DSL/Pipeline/CollectTest.lean`: +1 line after line 73, +83 after 141, +11 after 158, +11 after 220,
and +51 after 245 (f4bfb667, f493a5e0, 7fa81ec1). Every CollectTest `expect` past line 73 now points at
the wrong line. CONFIRMED by reading the lines at b1e32963, where the positions were right, and at the
tip:
- A1-M2 `95`/`109` and A1-M3 `122`, A1-M4 `130`, A1-M5 `139`, A1-M7 `81` now point at `}` lines.
- A1-M6 `151` now points at the C7b guard, not the C8 guard.
- A2-M1 `176`/`181`/`194` now point at a tlprog line, the C10b guard and `def c6b`.
- A2-M2 `215` now points at `| .freeNorm _ => true`.
- A4-M1/2/3 `235`/`237`/`240`/`241` point at C8/C8c lines.
- A6-M1 `273`/`282`/`292` now point at comment lines, and `313`/`324` at mid-expression lines.

The plan's Finish step runs the FULL manifest unfiltered and treats a non-matching expect as a finding,
so these 15 entries will be reported as unkilled, or someone will have to wave them through by eye.
Either way the recorded kill evidence no longer verifies the guards it names. The tests themselves are
fine: the guards still exist at the shifted lines. Positions in CollectEvalTest, CollectPlanTest,
CompileTest, RouteFragmentDiagnosticTest, SourceDifferentialPolicyTest (328-331),
SourceDiagnosticAdmissionTest (175), AcsetCodecTest (97) and Adapter32Test (138) are correct at the
tip.
**Fix (mechanical, verified at the tip):** in the manifest, change only the CollectTest line numbers:

| Old line | New line |
|---|---|
| 81 | 82 |
| 95 | 96 |
| 109 | 110 |
| 122 | 123 |
| 130 | 131 |
| 139 | 140 |
| 151 | 235 |
| 176 | 271 |
| 181 | 276 |
| 194 | 289 |
| 215 | 310 |
| 235 | 341 |
| 237 | 343 |
| 240 | 346 |
| 241 | 347 |
| 273 | 430 |
| 282 | 439 |
| 292 | 449 |
| 313 | 470 |
| 324 | 481 |

Lines 57/58/59/72 are unchanged. Then re-run the manifest unfiltered.

### F2 [Minor] Checked-plan mixed-storage diagnostic now names a private clone `T#1` (common default-f32 case)
`Eval/Plan/Compile.lean` `prepareEvalPlan` Step 0b runs `scheduleStorageKind declEnv sched.stmts` on the
COLLECTED program. Its used-name order is externals first, then writes `T#1, …, T#n, T`, so the first
conflicting name is the clone. CONFIRMED by tracing. Scenario:
```
tlprog!{
  axis i : ℕ = 2
  tensor f64 A(i), B(i)
  Y[i] := A[i]
  Y[i] := B[i]
}
```
`Y` is undeclared, so it is f32 by default. Before the branch: `.capability (.unsupportedDtype "Y: mixed
f32/f64 storage in one schedule")`. Now: `"Y#1: mixed f32/f64 storage in one schedule"`. The reference
evaluator maps the same situation back through `collectorOwner` (FG2, T3-F2), so the two backends now
name different tensors for one program. The same happens with a declared `tensor f32 Y(i)`. Decision
note §C.8 permits diagnostics to name `T#k`, so this is not a contract violation. It is a user-visible
regression in the most common f32 mistake (inputs spelled `f64`, output left undeclared), and an
asymmetry the FG2 fix closed on one side only.
**Fix:** in Step 0b, `let shown := if checked.privateNames.contains nm then collectorOwner nm else nm`,
mirroring `evalScheduled`. Add one f64-inputs/undeclared-`Y` fixture to CollectPlanTest pinning `"Y: mixed…"`.

### F3 [Minor] Doc wording: "checked evaluator" for the reference evaluator; owner labels; stale line reference
- `papers/semantics/tensor_logic_semantics.md` (the In/Def disjointness remark) and the decision note's
  "Landed as" bullet both say "`EvalError.inputIsDefined` on the checked evaluator". `EvalError` is the
  REFERENCE evaluator's (`evalScheduled`); "checked" is this repo's word for the plan path, so the
  sentence names the same backend twice in different words. Fix: say "reference evaluator".
- `tensor_logic_semantic_gap_audit.md` header: "scatter, max/min, scan and tropical closure are S3".
  The plan §2 table assigns scan multi-writer collection to "parked (scan collection)", not S3, and
  the affine-write-slot oracle to S2. Fix: "scatter, max/min and tropical closure are S3; scan
  multi-writer collection is parked".
- The decision note's S1 table row (edited by the branch) still cites `NumericalProfile.lean:120-123`
  for the refusal that the branch deleted. Fix: drop the line reference or write "(deleted in slice 1)".

### F4 [Minor] PLAUSIBLE: tests that accept ANY evaluation error could now pass on B3 for a different reason
Not traced exhaustively, because of the turn budget. B3 runs before size inference and execution. An
existing fixture that (a) supplies a name the program writes and (b) asserts only `.isError` or a
generic `| .error _ => true` would now pass because of `inputIsDefined`, not the error it was written
for. I found no such fixture: the corpus scan above found no surface program supplying a defined name,
and `checkEntry` hard-fails on errors. I did not, however, grep every `run_cmd` input map in the
Portfolio/Reject tests.
**Probe for the controller:** `git grep -n -E "\| \.error _ => (true|pure \(\))" 1088b200 -- leanncd/test/Eval`.
For each hit, check whether its input map contains a name the program writes. Expected: none.

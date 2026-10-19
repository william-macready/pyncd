# Independent review of the S2a plan (`additive_s2a_plan.md`)

Reviewer: independent (Opus 5.5), 2026-10-18. Read-only against `proto-s2a-p3` (ddbd82c5) and the 17 patches.
Findings are appended as they are made. Severity: Critical / Major / Minor / Question.

Summary: Critical 0, Major 2 (F1 cause-only condition confirmation can absorb another statement's failure; F4 the
§0 goal "S3a can claim scatter-collision semantics validated" has no asserting fixture), Minor 8 (F2, F3, F5-F10),
Question 1 (F11). The plan is executable as written: patch files, order, targets and counts check out.

## Findings

### F1. Major: `confirms` is cause-only, not origin-bound: a collision/multi-writer condition can absorb a native failure from a different statement (Lens B(e))
- Where: plan §4 T4 "Conditions (detected from source, native-confirmed ...)" and reviewer lens "no masking"; patch
  `T4-04` `confirms`, `legacyCollision`, `checkedCollision`, `legacyCompile`; `T4-06` (phase check dropped).
- Claim: the T4-04 docstring says "a condition can never explain away an unrelated native divergence"; plan §5(b)
  asks the final review to confirm "no condition masks a native divergence".
- Evidence: `confirms (.scatterCollisionRejected _)` = `legacyCollision native.legacy && checkedCollision native.checked`.
  `legacyCollision` matches ANY `.scatterCollision ..` (after T4-06, in any phase); `checkedCollision` accepts ANY
  runtime `scatterCollision` OR ANY `.preparation` with a `.capability _` cause. Neither inspects the failing
  tensor/statement against the condition's `origin`. Same for `.multiWriterScatter _` (any `scanAxisNotIter` compile
  error, `legacyCompile` is a `toString`-substring match). `classification` returns `.knownContractDifference c` as soon
  as the HEAD condition is confirmed (T4-05 changed `conditions.all confirms` to `confirms native c`).
- Failure scenario: source with S0 = a bare-slot `scatter S[i] := X[i, j]` with `reduce := rejectCollisions` (admitted
  as plain `.assign` by `admitAffineStatement`; the oracle sums over `j`; `detectConditions` skips it because
  `nonBareWrite` is false) and S1 = `Y[a+b] := X[a]*W[b]` (detected collision). If production rejects S0 (the
  `writeCollides` docstring says production counts a contracted axis as a collision), legacy fails with
  `scatterCollision` on S0 and the checked plan refuses S1's multi-axis slot by `capability` at preparation: the S1
  condition is "confirmed" and the run is `knownContractDifference`, while S0 is an unexplained divergence. More
  generally any production bug raising `scatterCollision` (or any `capability` refusal on the checked leg: that
  disjunct alone is very broad) is absorbed. The `fMask` fixture only tests a different error KIND (compile vs
  evaluation), never same-kind/different-origin.
- Fix: bind confirmation to the condition's tensor/statement (the legacy `scatterCollision` and checked
  `scatterCollision` carry a destination; the capability refusal should name the statement/slot), or at minimum add
  this as a parked row in §2 and a negative fixture (two statements, collision kind from the undetected one). Also
  record in §2 that bare-slot scatters with a contracted axis under `rejectCollisions` are admitted and summed by the
  oracle with no condition (whether production rejects them is unprobed).

### F2. Minor: "independence by construction" is independence from `dest` only; the forms come from production's own `idxAffineForm` (Lens A(1), B(d))
- Where: plan §0 bullet "The oracle's independence from `dest` is by construction"; §5(a) "the independence-by-construction
  claim of the oracle".
- Evidence: `git grep idxAffineForm proto-s2a-p3 -- leanncd/LeanNCD`: defined in `DSL/Ast.lean`, used by
  `DSL/Pipeline/Lowering.lean`, `Eval/Plan/Compile.lean`, `Eval/Scan.lean`, `Eval/SizeInfer.lean` AND by
  `Admission.outputForms` (`.affine e => ... pure (idxAffineForm e)`). Both `forms` (oracle) and `dest` (core, via
  `coordOfForms`) are computed from that same output. The claim as worded (oracle never mentions `dest`/`sourceSlots`/
  admitted `shape`) is TRUE: `Oracle.lean` at proto tip has no `.dest`, no `sourceSlots`, and its `shape` is
  `(admitted.source.table.entry statement.output.tensor).axes.map (·.extent)`.
- Consequence: a defect in `idxAffineForm` (sign of `.shift`, a dropped coefficient) is shared by the reference and
  both native legs and is invisible to every differential row; only the T3 hand values (`[1,0,2,0,3,0,4]`,
  `[1,12,123,234,340,400]`, `[0,0,111,0]`) pin it, and they cover `.scale`, `.affine` of two unit axes and `.const`
  only (no negative coefficient, no `.shift` value fixture beyond the T2 range refusal).
- Fix: one sentence in §0 and the T5 AGENTS.md entry: "independent of `dest`, NOT of the shared form extractor
  `idxAffineForm`; the hand-valued T3 fixtures are the only check on it". Optionally a hand-valued `.shift`/negative
  coefficient fixture (park if not wanted).

### F3. Minor: `FormsSpec`-violating outputs exist in the repo itself; agreement evidence is exactly "the two builders" (Lens B(a))
- Evidence: `SourceAffineDestinationTest.retarget` (proto tip, test line 28) builds `{ o with tensor := t, dest := d }`
  from an `admitSource` output, so `forms = indices.map single` while `dest` is affine: `FormsSpec` is false for it,
  and `nonBareWrite`/`Observation`/`NumericalProfile` would treat it as BARE while `Term.value` uses the affine `dest`.
  `git grep` finds no other `AdmittedOutput` construction in `leanncd/LeanNCD` (only `admitOutput` and
  `admitAffineOutput`; no transport/renaming rebuilds an output), so no library path is affected today.
- Assessment: the design is sound as documented, but the oracle-vs-core parity (T3) is evidence about the two builders
  only, and there is no statement-level `FormsSpec` theorem for `admitSourceAffine` (§2 row "Unproved ... (1)"). The plan
  should say in §0 that hand-built/retargeted outputs carry no forms/dest agreement and must never reach the oracle or
  `Observation` (today true because only T1's proof test builds one). No fix needed beyond wording.

### F4. Major: the slice's stated purpose (S3a can claim scatter-collision semantics validated) is not backed by any assertion (Lens A(5), B(d))
- Where: plan §0 Goal, "so that S3a can claim scatter-collision semantics validated against an independent reference";
  design note §4.6 ("non-colliding scatter, `reduce := sum`, diagonal writes and constant slots should agree on all four
  legs today. These fixtures are the first validation of S3a's target semantics").
- Evidence: `git grep` of `SourceDifferentialScatterTest.lean` at proto tip: the only `.scatter` fixtures are `fD`
  (`[.scatter "Y" [convSlot] readXW sumOpts]`) and `fD'` (constant slot), guarded only by `tag fD == "nativeFailure"`
  and `tag fD' == "nativeFailure"` (lines 134, 135). "legacy sums like the oracle" is a COMMENT (line 133), recorded in
  `p3_observed.md`, not an assertion. The four-leg parity rows A, B, C (lines 130-132) are all `.assign`, non-colliding.
  §2 already admits "the oracle never runs a `.scatter` statement in a four-leg parity fixture" and "no scatter-sum
  collision fixture reaches four-leg parity", but §0 still states the goal as met.
- Failure scenario: S3a cites S2a as validation of collision-sum semantics; a regression in legacy `evalScatter`'s sum
  (or in the oracle's collision sum on `.scatter`) leaves every S2a guard green, because `nativeFailure` is the
  classification whatever the legacy values are.
- Fix: either (a) add guards to `T4-05` that assert the legacy leg's tensor values equal the oracle's for `fD`/`fD'`
  (legacy-only agreement, explicitly named as such), or (b) rewrite the §0 goal to "S2a supplies the reference;
  agreement on collision sums is observed (legacy only) but not asserted; S3a must add the assertion" and add the row
  to §2/§6. (a) is ~1 small fix dispatch.

### F5. Minor: §3 sibling-audit cells and omissions (Lens A(2))
- `Differential.detectConditions` row, `indices` cell = S is wrong: `nonBareWrite` is
  `st.output.forms != st.output.indices.map WriteForm.single` (Differential.lean:186 at proto tip), so `indices` is R
  (the bare/non-bare decision depends on it). Same predicate in `Observation` line 291 and `NumericalProfile` line 219
  (those rows mark `indices` R; consistent).
- Raw-chain row, `slots`/`sourceSlots` = F: `RawCorrespondence.lean:618,678` and `RawSemanticConnection.lean:140-155`
  READ `statement.output.sourceSlots.uids` / `.project` and `statement.output.dest`; they are R-under-`IsBare`, not
  "forbidden". The F label hides that the raw chain consumes the generalised fields.
- Omitted consumers: `AdmittedStatement.destination_pullback` (statement CHANGED in `T1-01` to include `dest`; not in
  checklist (c)'s theorem list) and the new `destination_bare`; `pure_correspondence`, `Term.output_global_support`,
  `Term.globalFiber_reenumerate` (all take an `AdmittedOutput`); `Observation.sourceDebugFrom`/`sourceDebugAffine`
  (entry consumers: the entry table names only `sourceDebug` and "`compareSource` (via `sourceDebugAffine`)");
  `Differential.writeCollides`/`derivedShape` read `forms` (folded into the detectConditions row: fine);
  `SourceAffineDestinationTest.retarget` (a test-side builder, see F3). None changes a conclusion; add them so the T2/T4
  reviewer's "record any consumer not in this table" step does not produce false alarms.
- Verified: `NativeSource.admission` has no library consumer (`git grep "\.admission"` over Provenance, NativeLegs,
  Differential, Observation, Diagnostics, NumericalProfile finds only the field declaration), so its S cell holds;
  `Oracle.lean` has no `.dest`/`sourceSlots`/`output.shape`.

### F6. Minor: T4 split labels and the owner of mutation cycles are inconsistent (Lens A(3), A(7))
- `T4-05` edits `Differential.lean` (single-writer gate for the extent condition, `multi ++ collisions ++ extents`
  stage order, and `conditions.all (confirms native)` -> `confirms native c`, i.e. head-only confirmation) and `T4-06`
  edits `Differential.lean` (drops the legacy phase check). Dispatch B ("T4-05, T4-06 + cycles") therefore carries the
  most masking-relevant production change of the slice, while dispatch A is labelled "(production)" and contains the
  `T4-03` test scaffold. The dispatch-B reviewer must be told to review `classification`/`confirms` (F1).
- §1 says mutation cycles are a CONTROLLER step "(not the implementer)"; the T2 row says "(apply + build + cycles)" and
  the T4 row puts "+ cycles" in implementer dispatch B. Pick one; P3b (60 turns, at the cap) spent ~15 calls polling
  the cycles and Tests, so putting cycles in dispatch B risks the cap.

### F7. Minor/Question: job-count statements in §2 do not match the record (Lens A(7))
- §2: "Per-task job counts at intermediate states are UNMEASURED" and "8818 jobs (four new test modules, one per task)".
- Evidence: `p1_findings.md` line 137: Tests at `a5fc0677` (= the T1 task state exactly) 8816 (+2 for ONE module);
  `p2a_findings.md` line 184: 8817 at `b6e39e58` (T2 + T4-01); `p2b_findings.md` line 130: 8818 at `d1dfd0e4`;
  `p3b_findings.md` line 87: 8818 at the tip, "unchanged job count" although `T4-03` registers
  `Semantics.SourceDifferentialScatterTest` in the `Tests` globs (verified in the patch). So the increments are 2, 1, 1, 0,
  not 1 per module; the total 8818 is measured and is the right expectation, but the stated reason is wrong, and the
  zero increment for a newly registered module is unexplained.
- Fix: cite the measured series; tell the executor the total is the check, and confirm the T4 module was built in the
  final Tests log by grepping its name (not by the job count). Question for the authors: was the tip Tests run done
  with the scatter test present (it should add a job)?

### F8. Minor: mutation evidence: which fixtures are effectively unmeasured (Lens B(f))
- T1: all 3 guards (plan says so; correct).
- T2: `T2-M2` (off-by-one) and `T2-M7` (shift READ admitted) are PROOF kills, so (i) the range accept-neighbours (test
  lines 71, 80, 86, 93, 150) are never shown to kill anything: a proof-compatible STRICTER check (e.g.
  `decide (writeValue f v + 1 < a.extent)`, which `fitIndex`'s `omega` still accepts) would be the mutation they exist
  for, and it is not in the manifest; (ii) the affine-READ refusal guards (133, 134, 136) are unmeasured. The plan's T2
  text names the proof kills but, unlike T1, does not say which guards are thereby unmeasured.
- Expect-list fidelity: `T2-M9` (blames first FITTING axis) must also fail guard 148 after `T2-03` (slot 0 fits, slot 1
  out of range), but its `expect` lists only line 89 (recorded in P2c, before `6d35f5cd`). Harmless, because
  `mutation-manifest.sh` checks that every expect string is present (subset, line 185), but §4 T2's "the manifest records
  the observed killing positions" is not exact. §1's parenthetical names `T2-M7` as the Admission-position entry;
  `T2-M2` (`Admission.lean:343:68`) is one too (still valid: T3/T4 do not edit `Admission.lean`).
- T4: the "no masking" property rests on M4 (bypass) with negatives that differ in error KIND; no fixture probes
  same-kind/different-origin (F1).

### F9. Minor: detection over-approximates and confirmation under-approximates in ways not recorded (Lens B(b), B(e))
- `writeCollides` enumerates the union of ALL terms' read axes plus form axes, so a multi-term statement such as
  `Y[2*a] := X[a] + W[b]` is "colliding" because of `b`, which only the second term reads. Over-detection plus
  cause-only confirmation (F1) widens the masking window. Unprobed what production does here.
- Two single-writer extent conditions on different tensors are never confirmed: `shapeOnly` requires EVERY binding issue
  to belong to the head's declaration, so the second tensor's issue fails it and the run falls through to a generic
  classification (a false divergence, safe direction). Not recorded in §2.
- `derivedShape` is the observed formula `c0 + sum coef*extent` (`c0+1` for a constant); with a negative coefficient it
  goes through `Int.toNat` and is very likely wrong, but confirmation then fails (safe direction). Record as unprobed.
- Size: the admission range check (`coordAll` over the support box), the oracle, and `writeCollides`
  (`images.eraseDups`, quadratic in the box size) all enumerate; fine for fixtures, unusable for large boxes. Empty
  extents behave correctly (vacuous `coordAll`, empty `Oracle.coordinates`, no collision); a destination axis of extent
  0 with a non-empty box is a `writeOutOfRange` refusal; `Int.toNat` is only applied after the `0 <= value` check
  (`fitIndex`, `Oracle.destination`).

### F10. Minor: T5 sweep names a document it does not identify
- T5 step 5: "Sync the master-plan completion blockquote": no file named; `rg -c "master"` over the six docs T5 lists
  finds no hit. Name the master-plan document (memory `feedback-proactive-master-plan-doc-sync` refers to one).
- T5 step 1: `leanncd/LeanNCD/Semantics/AGENTS.md` and `leanncd/AGENTS.md` contain none of 8814/8816/8818 (0 hits), so
  that step is a no-op there; the real edit is step 2/discoverability. All other files/identifiers in T5 exist (`ls`).

### F11. Question: bare-slot `.scatter` with `rejectCollisions` and a contracted axis
- `admitAffineStatement` sends an all-`.free` `.scatter` (policy OK) to `admitStatement (.assign ...)`, so
  `scatter S[i] := X[i, j]` with `reduce := rejectCollisions` is admitted and summed over `j` by the oracle, and
  `detectConditions` skips it (`nonBareWrite` false). The `writeCollides` docstring says production counts a contracted
  axis as a collision. Is this shape probed? If production rejects it, it is an un-conditioned divergence (honest
  `nativeFailure` alone, but maskable per F1). Add to §2 either way.

## Verified OK (evidence)

- §0 `IsBare` is exactly the witness form stated (`T1-01` lines 25-28); `isBare_of_identity`, `admitOutput_identity`,
  `admitOutput_bare` exist (`T1-01`). `FormsSpec` is a `def ... : Prop` (`T2-01` line 190), not a field; `forms` is the
  last structure field (`T2-01` line 161); proved for both builders (`admitOutput_formsSpec`,
  `admitAffineOutput_formsSpec`).
- `admitSource`/`admitStatement` accept/refuse behaviour unchanged: `T1-01`/`T2-01` only add `shape := signature`,
  `dest := id`, `forms := ids.map single` to `admitOutput`; `outputIndices` still refuses `.affine`, `admitStatement` still
  refuses `.scatter` (base `Admission.lean` lines 339-347, 460-463). `StatementFields` is strengthened (conjunct paired
  with `IsBare`), not weakened.
- `admitAffineWrite` is a faithful copy of `admitStatement`'s `.assign` body (base 466-486 vs `T2-01` 319-340).
- T1 theorems (`Term.globalDestination_partition`, `Term.fiber_partition`, `Term.collectedBody_correspondence`,
  `Term.empty_fiber`): names unchanged; each new statement quantifies over every `dest`, so the old statement is the
  `dest = id` instance (via the `shape` cast); bare recovery for the statement destination is `destination_bare`.
- Oracle semantics match the core fiber sum: per-term support = form uids ++ the term's read indices (core: output
  context = `formsSupport`, plus term-local read axes); collisions and zero coefficients sum (fixture line 89,
  `.affine 1 [(0, a)]`); empty fiber 0; same-tensor statements sum in `run`; out-of-range throws, never wraps.
- Patch file lists, per-task files and dependencies match the diff headers; T2-01 needs only `T1-01`; T3 does not need
  `T4-01` (the T3 `parity` helper calls `admitSourceAffine` and `Debug.canonicalContributions` directly, not
  `NativeSource`). Only `T4-01` touches `NativeLegs.lean`. No T3/T4 patch touches `Admission.lean`; no later task edits an
  earlier task's test file; T1-M* files (Fiber/Correspondence/ProgramCorrespondence) are untouched after T1.
- Chronology vs task order: the prototype applied `b6e39e58` (T4-01) before T3; the T3 task state never existed in the
  prototype but nothing in T3's targets depends on `NativeSource`.
- Guard counts (`git grep "^#guard"` at proto tip): T1 3 (+2 `example`), T2 28, T3 16, T4 17. Manifest: 28 entries,
  T1 3 / T2 10 / T3 9 / T4 6, labels unique; spot-checked `expect` positions T2-M3 116, T2-M4 119, T2-M5 93, T2-M1 148,
  T2-M10 157/159, P2b-ix 168, P3b-M5 183, P3b-M2 142 all point at the guard the mutation should break. Old strings for
  T3 (`Observation` `unless statement.output.forms == ...`, `(g.1, g.2 + o.value)`) are introduced by `T3-01`, not T4.
- §2 fixed values: `[1,12,123,234,340,400]` = `sum_{a+b=k} X[a] W[b]` with X=[1,2,3,4], W=[1,10,100] (checked by hand);
  `[1,0,2,0,3,0,4]` and `[0,0,111,0]` likewise.
- §4 turn figures match the record's token-report table (P1 77, P2a 52, P2c 30, P2b 35, P3 34, P3b 60).

## Not checked

- No build, no mutation run (forbidden). Lean elaboration of each intermediate task state (only reasoned from patch
  contents and the prototype's chronological builds).
- `IdxExpr`/`idxAffineForm` internals (only that it is shared); `p3_observed.md` row-by-row; Diagnostics hunk of `T4-02`.


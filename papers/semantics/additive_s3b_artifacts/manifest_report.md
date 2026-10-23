# S3b mutation manifest report

Manifest: `scratchpad/s3b_patches/additive_s3b_mutations_post.json` (48 entries; `--check` OK, every `old` unique at the tip).
Per task: T1: 6, T2: 6, T3: 6, T4: 7, T5: 9, T6: 7, T7: 2, T8: 5.

## (a) Coverage gaps and surviving mutants (FIRST)

- Surviving mutants: NONE. Run 1 (53 proposed/converted entries, empty `expect`, tip 43e86c5d) exited 0:
  every mutation broke the build, every file was restored byte-identical, every restored rebuild was green.
  Hence NO missing-fixture finding (class ii) and NO equivalent mutant surfaced by the run itself.
- Equivalent mutants identified BEFORE running (not run, dropped): T4-M7 (predicate/tropical check order swap;
  Stmt.algebra is predicate-aware so the order is unobservable; T4-M7b is the replacement and is kept),
  T5-M5b (reference casting REAL sources is bit-identical: true->1.0, false->0.0; p5 finding 2).
- Bad mutation text found by the run (class iii), FIXED: proposed T3-M3 replaced the collision combine by
  `Max.max` for EVERY agg, so it was killed by plain sum rows ("reduce sum wrong", ScatterTest 31/82/97...) and not
  by the NaN fixtures it was meant for. Replaced by a max-plus-only variant
  (`if c.unit0 == -1.0 / 0.0 then Max.max prev val else c.combine prev val`); run 2 shows it now fails exactly
  `S3b NaN must propagate through the collision fold` (ScatterTest:151).
- Observation (not a gap): T4-M2 (scan-state mismatch rule removed) and the dropped T4-M4b produce the same failing
  fixtures (CompileTest `scan base max / recurrence min`, 3 lines); the contracted-axis condition of the neutral-writer
  definition has no fixture of its own. Dropped as non-independent (see c); a dedicated fixture would be a small
  Direct-path add if wanted.
- Observation: the T4 neutral-writer exemption mutant (T4-M4) cannot be stated once for both tips: at the T4 tip the
  text lives in `DSL/Pipeline/ScheduledValidation.lean`, at the final tip in `DSL/Ast.lean` (`Stmt.ownAlgebra?`, T6
  refactor). The same production behaviour is covered at the tip by T8-M5 (targets DualityTest + CompileTest). If the
  T4 task cycle must exercise it at the T4 tip, the executor needs the T4-M4 text from p4_mutations.json for that tip only.
- Caveat on `expect`: the script prints only the first 10 `error:` lines per cycle, so I derived `expect` from the
  visible lines; a target past the cut-off (e.g. ScatterTest/DifferentialTest under the T3-M1 fold mutation) is not
  claimed. `expect` strings are test-file anchors `error: test/<path>.lean:` (no line numbers, so they hold at earlier
  task tips) plus one fixture label where the message carries one. Label strings may also appear in `info:` output of
  passing fixtures, so the file anchor is the load-bearing part.

## (b) Final table

Run 1: all cycles PASS (53 entries before pruning). Run 2 (filtered re-run of the five entries whose expect was not
derived from an unchanged mutation or that carry special strings: T3-M3 new text, T4-M3c, T6-M8, T7-M1, T8-M1): 5/5 PASS.
All other expect strings were verified by string match against the run-1 per-entry output (script not re-run for them,
to avoid a second ~3 h pass); verification script: `verify_expect.py` (0 strings missing). Task-tip check of those
anchors and labels (`tipexpect.py`): all exist at each entry's task tip (the two `DUALITY VIOLATED ...` messages are
built at runtime, observed at the T8 tip).

| Label | Task | expect | Result |
|---|---|---|---|
| T1-M1 reference Combine.tropical multiplies factors with * (not +) | T1 | `error: test/Eval/ContractTest.lean:`<br>`error: test/Eval/Portfolio/TropicalTest.lean:`<br>`error: test/Eval/Portfolio/RecurrenceTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T1-M2 checked plan f64 tropical factorOp back to .mul | T1 | `error: test/Eval/Plan/KernelDenseTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T1-M3 checked plan f32 tropical factorOp back to .mul | T1 | `error: test/Eval/Plan/KernelDense32Test.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T1-M4 maxNaN loses NaN propagation (Max.max) | T1 | `error: test/Eval/ContractTest.lean:`<br>`error: test/Eval/Plan/KernelDenseTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T1-M5 minNaN32 loses NaN propagation (Min.min) | T1 | `error: test/Eval/ContractTest.lean:`<br>`error: test/Eval/Plan/KernelDense32Test.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T1-M6 plan f64 floatOps min arm bypasses minNaN (Min.min) | T1 | `error: test/Eval/Plan/KernelDenseTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T2-M1 plan bare OOB pad -> ops.zero (real 0) instead of the statement's 0_K | T2 | `error: test/Eval/Plan/KernelDenseTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T2-M2 plan unary OOB pad -> pad (0_K) instead of the real zero | T2 | `error: test/Eval/Plan/KernelDenseTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T2-M3 plan Iverson false -> ops.zero (real 0) instead of 0_K | T2 | `error: test/Eval/Plan/KernelDenseTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T2-M4 plan Iverson true -> decoded real one instead of 1_K | T2 | `error: test/Eval/Plan/KernelDenseTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T2-M5 reference gather bare OOB pad -> 0.0 instead of the statement's 0_K | T2 | `error: test/Eval/GatherTest.lean:`<br>`error: test/Eval/Portfolio/ConvPoolTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T2-M6 reference Combine.tropical (unit0, unit1) -> (0.0, 1.0): empty sum / empty product | T2 | `error: test/Eval/ContractTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T3-M1 reference scatter fold: combine -> + (max/min collisions summed) | T3 | `error: test/Eval/Plan/ScatterDenseTest.lean:`<br>`error: test/Eval/Plan/ScatterCompileTest.lean:`<br>`S11 Out[2*i] := maxreduce(X[i, j])`<br>`error: test/Eval/ScanTest.lean:`<br>`shape 1 max` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T3-M2 reference scatter init: unit0 -> 0.0 | T3 | `error: test/Eval/ScatterTest.lean:`<br>`error: test/Eval/ScanTest.lean:`<br>`S3b max collision` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T3-M3 reference scatter fold: max-plus combine -> non-NaN-propagating max | T3 | `error: test/Eval/ScatterTest.lean:` | PASS (run 2, expect verified by the script) |
| T3-M5 checked worker fill: reduceId -> ops.zero | T3 | `error: test/Eval/Plan/ScatterDenseTest.lean:`<br>`error: test/Eval/Plan/ScatterCompileTest.lean:`<br>`S11 Out[2*i] := maxreduce(X[i, j])` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T3-M6 checked worker fold: reduceOp -> overwrite | T3 | `error: test/Eval/Plan/ScatterDenseTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T3-M7 compile: scatter step algebra ignores agg | T3 | `error: test/Eval/Plan/CompileTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T4-M1 (tropicalNonlin removed from checkScheduledDtypes) | T4 | `error: test/Eval/Plan/CompileTest.lean:`<br>`relu on a max-plus statement` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T4-M2 (scanStateAlgebraMismatch removed) | T4 | `error: test/Eval/Plan/CompileTest.lean:`<br>`scan base max / recurrence min` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T4-M3b (cast table: tropical -> bool accepted) | T4 | `error: test/Eval/Plan/CompileTest.lean:`<br>`predicate reads a max-plus tensor` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T4-M3c (cast table: max-plus <-> min-plus accepted) | T4 | `error: test/Eval/Plan/CompileTest.lean:`<br>`max-plus statement reads a min-plus` | PASS (run 2, expect verified by the script) |
| T4-M3d (cast table: real -> bool also rejected, parked decision 1 broken) | T4 | `error: test/Eval/Plan/CompileTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T4-M5 (unaryFn exemption removed: unary read cast-checked like a bare read) | T4 | `error: test/Eval/Plan/CompileTest.lean:`<br>`unaryFn read of a min-plus tensor` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T4-M7b (Stmt.algebra ignores the predicate declaration: predicate-ness dropped from the sort) | T4 | `error: test/Eval/Plan/CompileTest.lean:`<br>`predicate reads a max-plus tensor` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T5-M1 (cast removed in reference gather: bare read) | T5 | `error: test/Eval/Portfolio/GnnScatterTest.lean:`<br>`error: test/Eval/Plan/BoolCastTest.lean:`<br>`a1 max: reference` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T5-M2 (cast removed in plan Dense) | T5 | `error: test/Eval/Plan/BoolCastTest.lean:`<br>`a1 max: plan f64` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T5-M3 (truth convention flipped, plan Dense) | T5 | `error: test/Eval/Plan/BoolCastTest.lean:`<br>`a1 max: plan f64` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T5-M4b (cast applied under unary, plan compile) | T5 | `error: test/Eval/Plan/BoolCastTest.lean:`<br>`prepare64 failed` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T5-M5 (cast applied for real statements, plan compile: tropical guard dropped) | T5 | `error: test/Eval/Plan/BoolCastTest.lean:`<br>`prepare64 failed` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T5-M6 (cast applied to the OOB pad, reference) | T5 | `error: test/Eval/Plan/BoolCastTest.lean:`<br>`g1 oob max: reference` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T5-M7 (cast field not filled: scan base caller) | T5 | `error: test/Eval/Plan/BoolCastTest.lean:`<br>`d3 scan max: plan f64` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T5-M9 (cast field not filled: scatter caller) | T5 | `error: test/Eval/Plan/BoolCastTest.lean:`<br>`d1 scatter max: plan f64` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T5-M11 (checker: castNotAdmitted rejection removed) | T5 | `error: test/Eval/Plan/BoolCastTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T6-M1 (reference state init back to zeros) | T6 | `error: test/Eval/Plan/BoolCastTest.lean:`<br>`T6-a1 state max-plus: reference`<br>`error: test/Eval/Portfolio/RecurrenceTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T6-M2 (plan f64 state init back to 0.0) | T6 | `error: test/Eval/Plan/BoolCastTest.lean:`<br>`T6-a1 state max-plus: plan f64` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T6-M7 (neutral writers forced real in both backends: pad and cast key lose the state's sort) | T6 | `error: test/Eval/Plan/BoolCastTest.lean:`<br>`T6-c1 neutral oob max: reference` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T6-M8 (state sort leaks from scratch / other names: sorts not filtered by name) | T6 | `error: test/Eval/Plan/ScanCompileTest.lean:`<br>`T6/scratchMax: the state stays real` | PASS (run 2, expect verified by the script) |
| T6-M9 (compile: max-plus state gets zero init) | T6 | `error: test/Eval/Plan/BoolCastTest.lean:`<br>`T6-a1 state max-plus: plan f64` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T6-M11 (checker: stateInitNotAdmitted rule removed) | T6 | `error: test/Eval/Plan/ScanCompileTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T6-M12 (checker: rule rejects tropical init on every state, not only bool) | T6 | `error: test/Eval/Plan/ScanCompileTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T7-M1 (oracle: sorted tropical scatter refused again: keeps its max/min agg, so admission refuses nonSum) | T7 | `error: test/Semantics/SourceSortedAuditTest.lean:`<br>`error: test/Semantics/SourceAdmissionAffineTest.lean:`<br>`error: test/Semantics/SourceSortedDifferentialTest.lean:` | PASS (run 2, expect verified by the script) |
| T7-M5 (oracle: empty-fibre total starts at 1_K, i.e. real 0 in a tropical carrier) | T7 | `error: test/Semantics/SourceOracleCarrierTest.lean:`<br>`error: test/Semantics/SourceSortedDifferentialTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T8-M1 (PRODUCTION: min-plus scan state starts at -inf in the checked plan; mirror-asymmetric, caught by the min hand twin RC10m AND by the duality property's grid min case) | T8 | `error: test/Eval/Plan/DualityTest.lean:`<br>`DUALITY VIOLATED on checked plan f64` | PASS (run 2, expect verified by the script) |
| T8-M3 (PRODUCTION: predicate read casts false to 0.0 in BOTH tropical sorts; 0.0 is negation-fixed and predicate programs are outside the property, so ONLY the one-sort BoolCastTest hand fixtures catch it, and GN4/GN4m do not discriminate unless the masked row would win) | T8 | `error: test/Eval/Portfolio/GnnScatterTest.lean:`<br>`error: test/Eval/Plan/BoolCastTest.lean:`<br>`a1 max: reference` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T8-M4 (ORACLE test-side: the independent unrolling's zero leaf / merge go back to the real sum, i.e. state init back to 0) | T8 | `error: test/Eval/PropertyOracle/ScanOracle.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T8-M5 (PRODUCTION: a sort-neutral writer votes for the state's sort; flips the PARKED all-neutral pin, and RC10-style neutral-base behaviour where annotations disagree) | T8 | `error: test/Eval/PropertyOracle/ScanGen.lean:`<br>`error: test/Eval/Plan/CompileTest.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |
| T8-M6 (PRODUCTION: binary32 min-plus reduce identity is -inf; asymmetric f32-only bug; caught by the property's plan32 leg AND by Adapter32Test fixture 9 min) | T8 | `error: test/Eval/Plan/DualityTest.lean:`<br>`DUALITY VIOLATED on checked plan f32`<br>`error: test/Eval/Plan/Adapter32Test.lean:` | cycle PASS in run 1 (no expect); expect strings checked against run-1 output text, not re-run |

## (c) Dropped entries and reasons

- T1 float32Ops max arm -> Max.max (hand mutation): twin of T1-M6 in the other carrier, same property; the f32 NaN
  property stays covered by T1-M5 (minNaN32, via KernelDense32Test 332).
- T1 f32 factorId 0 -> 0x3f800000 (run, killed): fails the same KernelDense32Test fixture set as T1-M3 (212,213,269..), so
  not an independent behaviour.
- T2 reference unary pad -> zero, reference Iverson -> old 1.0/0.0, approxEq old body: ref twins of kept plan mutants
  (T2-M2/M3/M4) or a probe without a recorded mutation text (approxEq: spike only).
- T3-M1b..e, T3-M2b, T3-M5b: same production edit as T3-M1/M2/M5, merged into ONE entry each with several targets.
- T3-M4 and T7-M2, T7-M3, T8-M2 and T7-M4: same production text as T1-M1 / T1-M2 / T2-M6 (tropical mul back to `*`;
  f64 factorOp back to `.mul`; empty product 1.0). Kept at the earliest task; later task tests add rows but not behaviour.
- T4-M1b (checkDtypes twin of T4-M1), T4-M3 (whole cast table removed: dominated by T4-M3b/M3c/M3d), T4-M4 (not valid at
  both tips, see a), T4-M4b (same failures as T4-M2), T4-M6 (multi-writer no-entry rule), T4-M7 (equivalent), T4-M8
  (check precedence), T4-M9 (min-plus sort; reached by M3c/M1 families): not run; quality-over-count pruning, not
  evidence of redundancy except where stated. T4-M4b was run (killed, same set as M2).
- T5-M3b (reference twin of T5-M3), T5-M4 (reference twin of T5-M4b), T5-M5b (equivalent), T5-M6b (plan twin of T5-M6),
  T5-M8, T5-M10 (scan step / plain caller twins of M7/M9; the same four d1..d4 fixtures cover all four callers):
  pruned, not run.
- T6-M3, T6-M10, T6-M4, T6-M6: f32/min/decode/plan twins of M2/M9/M9/M7; T6-M5 (reference annotation only) run and killed,
  but fails the same fixture (T6-c1 neutral oob max) as T6-M7, which covers both backends at the shared site.
- T7-M6 (test-fixture mutation, not production), T7-M2/M3/M4 (above).
- T8-M2 (duplicate of T7-M4/T2-M6 text).

## (d) Entries adjusted for task-tip uniqueness

None needed: every kept `old` occurs exactly once at its task's last commit (c9c8f537, 398d197b, 281a1719, ccf9f745,
6b0cb23b, 3476f129, 7473023d, 43e86c5d) AND at the final tip (`tipcheck.py`, all 53 OK; all target test files exist at
the task tip). Exceptions: T4-M4 (valid at T4 tip only) dropped, see (a). Text changes for conversion: T2-M5 uses the
shorter `gatherRead env coord zero nm es` so it is unique before and after T5 added `(castOf nm)`.

## (e) Cost

Run 1: 53 cycles = 106 builds; run 2: 5 cycles = 10 builds; total 116 builds. Wall time: run 1 roughly 2.5 to 3 hours
(about 3 min per cycle on core files), run 2 about 15 min. Tool calls about 75 (about 25 of them were wait loops);
context peak well under 200k (largest items: reading the six proposal files and the run-1 output summary).

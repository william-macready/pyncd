# Step-aware `where` masks: prototype report 2 (test/pin batch, Lean side)

Branch `proto-step-mask`. Production frozen at `c8cee803` (stage 1); stage-1 report commit `a51020d1`.
Test commit `c787920f` ("test: step-aware mask pins and unrolled-differential flip"); patch
`papers/step_mask_files/patches/0002-test-step-aware-mask-pins-and-unrolled-differential-.patch`.
Everything below was observed in this worktree on 2026-11-26 unless marked [judgment]. No production
file was edited (`git diff c8cee803 -- leanncd/LeanNCD` is empty; mutants were applied and reverted).

## (a) Build times (wall seconds, `scripts/lake-build.sh`, one build at a time)

| # | Targets | Result | Wall s | Note |
|---|---|---|---|---|
| b1 | ScanCompileTest, StructuralTest, NonlinCompileTest, ScanUnroll | 3 green, ScanCompileTest FAILED | 52 | first run was killed by the interrupt (empty log); this is the rerun. `bias` parse error, base at literal 1 refused |
| b2 | same | ScanCompileTest FAILED | 30 | `bias` is a keyword here; the file spells it `«bias»` |
| b3 | same | ScanCompileTest FAILED | 31 | f32 block: `algebraNotAdmitted` (needs `admittedAlgebraF32`) |
| b4 | same | green (8527 jobs) | 33 | |
| b5 | DifferentialTest, ScanAffineEmitTest (+ AdapterTest built on the way) | DifferentialTest FAILED, the other two green | 53 | independent unroller fails on program (i), see (e) |
| b6 | DifferentialTest | green (8529 jobs) | 40 | |
| final | `Tests JaxExperiment` (one run, after the mutants were restored) | GREEN, `Build completed successfully (8846 jobs)` | 61 | only 9 `Built` lines: the targeted and mutant builds had already compiled almost every module (lake hashes, so the result is valid for the committed tree), so 61 s is NOT a cold full-suite time; stage 1 measured about 14 min cold |

## (b) Pins (each value observed in a green build; source values match the independent script)

Independent script: `papers/step_mask_files/expected_step_mask.py` (plain Python, no numpy, no Lean).
Its output (verbatim):

```
inter S[3,4] [0.0, 1.0, 0.7310585786300049, 0.4736311417473898, 0.0, 0.0, 0.2689414213699951, 0.2983632427253241, 0.0, 0.0, 0.0, 0.22800561552728602]
inter ctx0 [0.0, 1.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
step S[2,4] [0.0, 0.25, 0.37754066879814546, 0.0, 1.0986122886681098, 0.75, 0.6224593312018546, 0.0]
kv causal Yh[3,4] [0.0, 1.0, 0.7310585786300049, 0.6652409557748218, 0.0, 0.0, 0.2689414213699951, 0.09003057317038046, 0.0, 0.0, 0.0, 0.24472847105479764]
kv window Yh[3,4] [0.0, 1.0, 0.7310585786300049, 0.0, 0.0, 0.0, 0.2689414213699951, 0.2689414213699951, 0.0, 0.0, 0.0, 0.7310585786300049]
kv causal ctx0 [0.0, 1.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
block ctx 0 [1.0, 0.0, 0.0]
block ctx 1 [0.2689414213699951, 0.7310585786300049, 0.0]
```

1. `test/DSL/Pipeline/StructuralTest.lean` (mask section). Flipped to ACCEPT:
   `compileErrOf maskOwnAxisAfterScan == none`; `layoutOf maskInterScanAxis == .ok ["scan base=[S] body=[Pa, S]"]`;
   `layoutOf maskStepScanAxis == .ok ["scan base=[S] body=[S]"]`; `compileErrOf maskInterScanAxis == none`;
   added `compileErrOf maskStepScanAxis == none`. New accept neighbour `maskStepScanAndOutput`
   (`S[j., l +1] := softmax(where j ≤ l)(S[j, l])`, scan axis and output axis in one mask): layout
   `["scan base=[S] body=[S]"]`, `compileErrOf == none`. Kept: `maskBaseAtZero`/`maskBaseAtOne`
   (`maskAxisNotOutput "S" "l"`), `maskContractedAxis` (`"Y" "k"`), `maskUnboundAxis` (`"Y" "z"`),
   `maskOtherScanAxisFree == none` and all accept neighbours. Section header comment rewritten to the
   new rule; the base comment and the `maskOtherScanAxisFree` comment restated.
2. `test/Eval/Plan/ScanCompileTest.lean`.
   - T5.3 `seededAxisZero` restated: expected `[3,2]/[1,3,0.25,0.75,0,0]` (observed in b4; the
     docstring explains: `l = 0` true at step 0, false at step 1, so that row is all-masked; the old
     coordinate-0 value was `[1,3,0.25,0.75,0.25,0.75]`).
   - (a) `maskContextRankMismatch`: block with context rank 1 and mask rank 2 →
     `.nonlin 1 (.maskContextRankMismatch 1 2)`; top level (`checkAxiswise`, default context rank 0,
     the `EvalPlan` caller's path) with rank 1 → `.maskContextRankMismatch 0 1`. Accept neighbours:
     ranks 0 and 1 check. NOTE: the top-level pin goes through `checkAxiswise` directly, not a whole
     `checkGraph`/`prepareEvalPlan`; the source cannot produce a top-level rank > 0.
   - (b) block run: `Y[o] := X[ctx,o]` then `softmax` masked `o ≤ ctx` (rank 1, leaves width 2),
     `X = [[1,2,3],[4,5,6]]`: `runDenseBlock` ctx=[0] → `[1,0,0]`, ctx=[1] →
     `[0.2689414213699951, 0.7310585786300049, 0]` (tol 1e-12; a ctx-as-0 reading gives `[1,0,0]` at
     ctx=1). binary32 sibling (`checkPlanBlockF32`/`runDenseBlock32`, assign retagged to
     `admittedAlgebraF32`) agrees within 1e-7.
   - (c) base parity: NOT reachable on the plan. A hand-built base at literal 1
     (`S[l=1, i.] := normalize(where l = 0)(X[i])`) is refused by the plan compiler with
     `ScanCompileError.baseWriteNotAtBoundary "S" "S" 0` (observed b1); the pin now asserts that
     refusal. At the only reachable base literal, 0, "reads 0" and "reads the literal" coincide, so
     a value pin cannot distinguish them. The reference's base loop (no `maskContext`) was therefore
     not exercised at a nonzero literal.
3. `test/Eval/Plan/NonlinCompileTest.lean` Section 6, each through `diffEqB` (checked plan AND
   reference evaluator against the script's tensor): (i) `stepMaskInter`, (ii) `stepMaskStep`,
   (iii) `kvMaskCausal` (natural spelling `softmax(where s ≤ t)(Kw[s, k] · Qr[t, k])`, 3 slots,
   3 steps, no V cache, `Yh[s,t+1] := Pa[s]` records the weights), (iv) `kvMaskWindow`
   (`where s ≤ t ∧ s > t - 2`; at step 2 slot 0 leaves the window: column 3 is `[0, .269, .731]`).
   All four green in b1/b4. The Iverson-factor fixture comment there ("a `where` mask over a scan axis
   is refused at the source") was restated, since this file was already being edited.
4. Unrolled differential.
   - `test/Eval/PropertyOracle/ScanUnroll.lean`: `maskSubst` gains `(step : Bool := false)`; a seeded
     scan axis returns `σ u` when `step`, `some 0` otherwise. `rewriteNonlin` takes `step`;
     `rewriteRHS` passes `stepCoord.isSome`. Two new `#guard`s: `[.iterNext sx, .freeNorm sy]` and
     `[.freeNorm sy]` (per-step intermediate, no iteration slot) with `step := true` give `5 = 5`.
     The two existing guards kept (base `.iterAt` still gives `0 = 5`).
   - `test/Eval/Plan/DifferentialTest.lean` T5.4: the structural check keeps "no unrolled mask carries
     the seeded UID" (still true) and ADDS "some unrolled mask is `[1 = 0]`" (the step-1 literal).
     Three-way `scanParityCheck` `"T5.4 seededAxisZero"` comment restated; it passes with the new value.
   - New three-way: program (ii) `stepMaskStepProg` through `scanParityCheck` (plan, `evalScheduled`,
     independent unrolling): green (b6). Program (i) is NOT three-way, see (e).
5. JAX refusal: `experiments/jax_bridge/ScanAffineEmitTest.lean` (see (f) for why there):
   `smStepProg` (step mask `where j ≤ l`) → `renderAffinePlanNamed` = `.error (.axiswiseContextMask _ 1)`;
   neighbour `smOutputProg` (`where j ≤ 1`) renders `.ok`. Green in b5.

Counts: new/flipped `#guard`/`run_cmd` pins: StructuralTest 4 flipped + 3 new; ScanCompileTest
1 restated + 4 `#guard` + 2 `run_cmd` (block f64+f32 in one) ; NonlinCompileTest 4; ScanUnroll 2;
DifferentialTest 1 structural clause + 1 three-way; ScanAffineEmitTest 2.

## (c) Mutation table

Script: `/private/tmp/.../scratchpad/stepmask2/mutants.py` (apply, build ONE killer module, restore
by inverse edit, then `git diff --stat` must be empty).

| Mutant | Exact edit | Killer module built | Wall s | Result | First failing message (future `expect`) | Restored |
|---|---|---|---|---|---|---|
| M1 contracted axis accepted | `Structural.lean` `finalizeScans`: `find? (fun a => !visible.contains a.uid)` → `find? (fun a => !visible.contains a.uid && a.name != "k")` | `DSL.Pipeline.StructuralTest` | 80 | KILLED | `StructuralTest.lean:1114:0: Expression compileErrOf maskContractedAxis == some (.maskAxisNotOutput "Y" "k") … did not evaluate to true` | diff empty |
| M2 context uids before output uids | `Compile.lean` `lowerMaskPredicate`: `(outputUids ++ contextUids)` → `(contextUids ++ outputUids)` | `Eval.Plan.NonlinCompileTest` | 97 | KILLED | `NonlinCompileTest.lean:458:0: Expression diffEqB stepMaskInter … did not evaluate to true` | diff empty |
| M3 `axiswiseIncluded` ignores ctx | `Plan/Nonlin.lean`: `else ctx` → `else ctx.map (fun _ => 0)` | `Eval.Plan.ScanCompileTest` | 172 | KILLED | `ScanCompileTest.lean:1921:0: T5.3 seededAxisZero: got [3, 2]/#[1, 3, 0.25, 0.75, 0.25, 0.75], expected …0, 0` (also `:1973: step-aware block: ctx0 #[1,0,0], ctx1 #[1,0,0]`) | diff empty |
| M4 reference step loop drops `maskContext` | `Eval/Scan.lean`: `evalStmtSliceSeeded … seed s (maskContext := seed)` → `… seed s` | `Eval.Plan.ScanCompileTest` | 190 | KILLED | `ScanCompileTest.lean:1921:0: T5.3 seededAxisZero: SOURCE got [3, 2]/#[1, 3, 0.25, 0.75, 0.25, 0.75], expected …0, 0` (the reference leg; the plan leg agreed) | diff empty |
| M5 revert the `maskSubst` flip | `ScanUnroll.lean`: `else if step then σ u else some 0` → `else some 0` | `Eval.Plan.DifferentialTest` (requested) | 81 | KILLED | `ScanUnroll.lean:608:0: Expression substBool (maskSubst maskTestGeom pinX [iterNext sx, freeNorm sy] true) scanAxisMask == … (const 5) (const 5) did not evaluate to true` (and `:610`) | diff empty |

All 5 killed; each restore by inverse edit left `git diff --stat` empty. NOTE M5: it is killed by
`ScanUnroll`'s own new `#guard`s, an upstream module, so `DifferentialTest` was never compiled under
M5; whether the T5.4 `[1 = 0]` clause and the step three-way would also kill it is NOT observed
[judgment: the `[1 = 0]` clause should, since the unrolled masks would all be `[0 = 0]`]. A manifest
entry for M5 should `expect` the ScanUnroll guard. Mutant wall times include the library rebuild of
the mutated production module chain (M3/M4 about 3 min).

## (d) `Executable.lean` `.axiswise` arm (read-only)

The only `.axiswise` arm is in `checkJaxScanSupport` (`LeanNCD/Eval/Plan/Executable.lean:437`,
`| .pointwise _ | .axiswise _ => pure ()`), which walks `checkedNodes` of both the BASE and the STEP
block. It CAN see a step-block axiswise node with `maskContextRank > 0` (that is exactly where a
step-aware mask lives), and it ADMITS it without looking: the JAX support gate says "supported" and the
refusal only happens later, in the renderer (`buildAxiswiseInclude` → `axiswiseContextMask`). So it is
not refused earlier. Consequence [judgment]: no wrong answer (the renderer fails loudly), but the gate
and the renderer disagree on this plan shape; any caller that trusts `checkJaxScanSupport` alone (a
routing decision or a gate test) will route a step-aware plan to JAX and then fail at render time. A
one-line gate (`.axiswise a => unless a.raw.maskContextRank == 0 do throw ...`) is a production change
for the plan to decide (Rule 14: parked, about one dispatch with a pin in `ScanJaxGateTest`).

## (e) Risks, failures and what is unverified

- Program (i) (per-step intermediate `Pa[j.] := softmax(where j ≤ l)(S[j, l])`) fails the
  INDEPENDENT unroller: `independent run: the unrolled scan-free program failed: evalAssign %T_Pa_0:
  output axis (uid 2) has no inferable size (it appears in no read position)`. It is pinned two-way
  (plan vs reference) only. NOT verified whether this fails before the `maskSubst` flip too (no run
  made); [judgment] it looks like a size-inference gap for a scratch whose only read is substituted,
  not a mask issue. The kv programs (iii)/(iv) were not tried three-way.
- M1's mutant is a narrow stand-in ("accept an axis named `k`"), because the guard has no separate
  contracted-axis branch to drop: contracted and unbound axes fail the same `visible` test.
- Base parity (c) is unreachable on the plan (`baseWriteNotAtBoundary`); only the refusal is pinned.
- Top-level rank > 0 is pinned at `checkAxiswise`, not through `prepareEvalPlan`.
- Python JAX runtime / `.py` corpus not run (Lean renderer refuses the only new shape).

## (f) Why `experiments/jax_bridge/ScanAffineEmitTest.lean` was edited

`renderAffinePlanNamed`, `JaxCodegenError` and `axiswiseContextMask` live in
`experiments/jax_bridge/EvalPlanCodegen.lean`, which is part of the `JaxExperiment` target; the
`Tests` modules (including `Eval.Plan.ScanJaxGateTest`) do NOT import it (`ScanJaxGateTest` imports
`Executable`, `Entry`, `Adapter32`, `ScanCompileTest` only and tests the support GATE, not the
renderer). `ScanAffineEmitTest` is the existing renderer test module in `JaxExperiment` and already has
the `brPrepared?`/`renderAffinePlanNamed` helpers, so the refusal pin and its accept neighbour (2
`#guard`s, 2 small programs) went there. It is a test module, not production; `EvalPlanCodegen.lean`
was not touched.

## (g) Stale prose still stating the old rule (list only; nothing edited except test comments above)

| File | Identifier / section | Sentence to change |
|---|---|---|
| `leanncd/LeanNCD/Eval/Plan/Compile.lean:685` | `lowerMaskPredicate` neighbourhood docstring | "the mask policy (local non-seeded output basis, empty pins)": add the step-site context uids |
| `leanncd/LeanNCD/Eval/Plan/Compile.lean:1311` | `compileScan` STEP `.axiswise` arm comment | "Mask policy: local non-seeded output basis (`outputUids` — this recurrence's …": now `outputUids ++ ctxUids` when the mask mentions an iteration axis |
| `leanncd/LeanNCD/Eval/Plan/Compile.lean:1210, 1793` | base / top-level mask comments | still right (base and top level keep the non-seeded basis); check wording only |
| `leanncd/LeanNCD/Exec/Uid.lean:51` | `CompileError.maskAxisNotOutput` comment | says a mask mentioning a non-output axis is refused; add "except the statement's own scan axes in a recurrence body" |
| `leanncd/LeanNCD/Eval/Plan/AGENTS.md` | code-map row for `Nonlin.lean` (stage-1 note) | add `maskContextRank` / `maskContextRankMismatch` |
| `leanncd/LeanNCD/DSL/AGENTS.md:53` | `finalizeScans` bullet | mentions the mask guard; state the step-scan-axes visibility |
| `leanncd/test/Eval/Plan/ScanCompileTest.lean:1845-1849` | Fixtures 14-15 header | "local NON-SEEDED output basis, empty pins" (still true for these trivial masks; add the step-aware exception) |
| `leanncd/test/Eval/Plan/NonlinCompileTest.lean:115-117` | 1d admission comment | "local non-seeded output basis, empty pins" |
| `leanncd/test/DSL/Pipeline/StructuralTest.lean:1097-1100` | contracted/unbound comment | "read coordinate 0 on both backends" is history; fine, or mark as former behaviour |
| `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean:1439` | Slice 5.3 masked-axiswise note | add that rank > 0 is refused (`axiswiseContextMask`) |
| `papers/backend_missing_functionality.md:252` | mask lowering line | "`lowerMaskPredicate` (local non-seeded output basis, empty pins)" |
| `papers/semantics/jax_scan_record.md:306` | scan exclusions | "an axiswise `where=` mask over a scan axis is not inspected" |
| `papers/semantics/jax_scan_record.md:1619-1633` | section 26 (silent wrong answer, fix) | "refused a mask over a scan axis in a state's step statement, a per-step intermediate …"; "reads coordinate 0 on both backends": now step-aware on Lean, refused only on JAX |
| `papers/semantics/jax_scan_record.md:2633` | later section | "still fails `maskAxisNotOutput`" (check which program; may now be accepted) |
| `papers/semantics/jax_layers_time_session_brief.md:27` | item 1 | "A `where` mask that mentions a scan axis is REFUSED" |
| `papers/semantics/jax_kv_window_session_brief.md:18, 41` | scope / item 1 | "needs a step-aware `where` mask"; "A `where` mask over the scan axis is refused" (now Lean-accepted, JAX-refused) |
| `papers/semantics/jax_skew_fixtures_session_brief.md:35` | item 2 | "no `where` mask over a scan axis, which is refused" |

Session briefs are historical records [judgment]: the plan may annotate rather than rewrite them.

## (h) Tool calls

About 69 harness-counted tool calls across both runs (36 before the accidental interrupt, about 33
after), against a budget of about 60: OVER by about 9. The overrun came from three compile-fix rounds on
ScanCompileTest (`«bias»` keyword, f32 algebra, unreachable base parity), the DifferentialTest
oracle failure, and waits on the mutant builds that the harness moved to the background. Not
measured: the context-token total (no `token-report.py` run).

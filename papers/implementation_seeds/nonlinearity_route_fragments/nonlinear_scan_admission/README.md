# Task 4 nonlinear scan admission seed — stopped in Phase 2

This directory is a current-tree rehearsal for Task 4 of
`papers/nonlinearity_split_pair_direct_lowering.md` (§1.2 and §3.6). It is outside Lake's target
graph and contains the only two files created by this rehearsal.

- **Base commit:** `2e1b8e8`
- **Date:** 2026-08-27
- **Status:** **STOPPED AT THE PHASE-2 BOUNDARY. MULTIPLE REQUIRED SOURCE PROGRAMS WERE NOT
  RECOVERED.**

## Ordered phase status

| Phase | Status | Evidence |
|---|---|---|
| 1 — `retainedAxisPos` | EXECUTED | Three guards cover leading, interleaved, and trailing local-axis positions. |
| 2 — recover and reproduce source programs | STOPPED | Exact donors were inspected; only donor candidates survive, not the six spike source/input pairs. |
| 3 — independent-unroller change | **NOT EXECUTED** | No unroller was cloned and no `.freeNorm` oracle change was implemented. |
| 4 — nonlinear `compileScan` | **NOT EXECUTED** | No lowering, slot allocation, or publication logic exists here. |
| 5 — negative/write-safety fixtures | **NOT EXECUTED** | No fixtures 14–19 were built. |
| 6 — differential/corpus rebaseline | **NOT EXECUTED** | No `13/0/4` claim was made. |
| 7 — mutations/closure | **NOT EXECUTED** | No mutation hooks or completion claim exists. |

This is the mandated stop. It is not a partial Phase-3 implementation and contains no transplant
claim.

## Artifact

`NonlinearScanAdmissionSeed.lean` contains only:

1. the Phase-1 `retainedAxisPos` rehearsal;
2. a faithful local clone of private `DSL/Pipeline/ScanAffineTest.reluScan` source syntax;
3. direct references to the public donors required by §3.6;
4. legacy `evalScheduled` executions of the three public `ScheduledProgram` donors that also retain
   their exact donor inputs;
5. an explicit Phase-2 stop message.

It contains no independent scan unroller, oracle implementation, nonlinear Plan lowering,
allocation/publication helper, or mutation toggle.

## Phase 2 source-recovery findings

The governing requirement is a recovered **source construction and inputs**, executed through legacy
`evalScheduled`. Matching a retained output by inventing a program or fitting inputs is not recovery.
Under that standard, none of the six §3.6 recorded-value groups is reproduced here.

### Exact named donors

| Required donor | Exactly recovered evidence | What it does not recover |
|---|---|---|
| private `ScanAffineTest.reluScan` | Source syntax was cloned byte-for-byte: `S[j,0] := X[j]`; `S[j,l+1] := relu(S[j,l] · A[j,k])`. It compiles to a logical schedule. | The donor defines no inputs. Assigning values chosen to hit groups 1 or 3 would be fitting. |
| public `ScanCompileTest.coupledSched` / `coupledInputs` | Reused directly and executed through legacy `evalScheduled`; raw values are below. | It is a linear, two-iteration-axis structural donor, not the missing scalar nonlinear/linear coupled source for group 6. |
| public `ScanCompileTest.scratchSched` / `scratchInputs` | Reused directly and executed through legacy `evalScheduled`; raw value is below. | It has one linear scratch and produces `[1,2,6]`; it is not group 5's missing nonlinear scratch→scratch→state source. |
| public `ScanCompileTest.multiBaseSched` / `multiBaseInputs` | Reused directly and executed through legacy `evalScheduled`; raw value is below. | It is a linear multiple-base-write donor, not the missing nonlinear-base group 4 source. |
| `NonlinCompileTest.sampleMask` | Exact mask expression is checked in the seed. | It is an expression fragment, not a `TLProgram`/`ScheduledProgram`, and cannot be run through `evalScheduled` alone. |
| `NonlinDenseTest.axiswisePlan` | Exact axis position/function are checked in the seed. | It is Plan IR using `.normalize`, not a legacy source program and not group 2's missing interleaved-softmax recurrence. |
| Task-1 `RouteWeaveTest.freeNormAxiswiseProg` | Exact public source compiles and retains one logical statement. | It is a top-level normalization with no scan and no inputs; it is not the group-2 source. |

Task 1's private `f8AxiswiseScan` was also inspected. It is a normalization self-scan with no inputs,
not the recorded interleaved softmax source/input pair. It was therefore not copied.

### Six recorded groups

| # | Recorded group | Recovery result |
|---:|---|---|
| 1 | leading pointwise `[2,3,20,300,200,30000]` | ReLU source-shape donor survives; exact spike inputs/source orientation do not. **Not reproduced.** |
| 2 | interleaved axiswise history ending `[..., .991521, .008479]` | No source/input pair survives. **Not reproduced; Phase-2 stop trigger.** |
| 3 | leading persistent nonlinear `[1,0,0,2,6,18]` | ReLU source-shape donor survives without inputs. **Not reproduced.** |
| 4 | nonlinear base `[0,3,0,3]` | Only the linear `multiBaseSched` structural donor survives. **Not reproduced.** |
| 5 | scratch→scratch→state `[1,5,5,2,0,0]` | Only the one-scratch linear `scratchSched` donor survives. **Not reproduced.** |
| 6 | coupled `G=[1,0,0]`, `H=[1,1,0]` | Exact public coupled donor is a different linear, two-axis program. **Not reproduced.** |

### Retained-history audit

- Registered worktrees were searched for the exact group-2 value and “interleaved axiswise.” Matches
  were only the design record and superseded drafts of this seed.
- Reachable refs/history were searched commit-by-commit. Matches were versions of
  `papers/nonlinearity_split_pair_direct_lowering.md`, not a source fixture.
- Every Git blob, including unreachable objects, was scanned for exact float
  `9915205505990216`: 82 blobs matched, classified as 71 design-record versions and 11 superseded
  seed drafts. No original spike source blob was found.
- The retained session store had no turn containing the exact float or “interleaved axiswise.”

This establishes “not recoverable from retained evidence,” not mathematical impossibility.

## Direct seed output

Command, from `leanncd/`:

```bash
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/nonlinear_scan_admission/NonlinearScanAdmissionSeed.lean
```

Raw observed output:

```text
PHASE 1 COMPLETE: retainedAxisPos guards passed
PHASE 2 exact public donor coupledSched: G shape [3, 2, 3] = #[1.000000, 0.000000, 0.000000, 2.000000, 0.000000, 0.000000, 0.000000, 1.000000, 0.000000, 0.000000, 2.000000,
  0.000000, 0.000000, 0.000000, 1.000000, 0.000000, 0.000000, 2.000000]
PHASE 2 exact public donor coupledSched: H shape [3, 3] = #[7.000000, 0.000000, 0.000000, 0.000000, 10.000000, 0.000000, 0.000000, 0.000000, 13.000000]
PHASE 2 exact public donor scratchSched: S shape [3] = #[1.000000, 2.000000, 6.000000]
PHASE 2 exact public donor multiBaseSched: dp shape [3, 3] = #[1.000000, 2.000000, 3.000000, 7.000000, 1.000000, 2.000000, 0.000000, 7.000000, 1.000000]
PHASE 2 STOP: exact source-program/input pairs for multiple §3.6 groups were not recovered
PHASES 3–7 NOT EXECUTED
```

These are donor-candidate observations only, not substitutions for the six required records.

## Required baseline and gates

The exact required baseline command is:

```bash
lake build Eval.Plan.BlockTest Eval.Plan.NonlinCheckTest Eval.Plan.ScanTest Eval.Plan.ScanCompileTest
```

Raw observed output:

```text
Build completed successfully (8511 jobs).
```

Aggregate gates:

```bash
lake build Tests
```

```text
Build completed successfully (8657 jobs).
```

```bash
lake build LeanNCD
```

```text
Build completed successfully (8543 jobs).
```

The earlier draft's 8525/8505 commands were different exploratory module sets. They are not
replacement gates and are not used to characterize the required 8511 baseline.

## Required later tables — not executed

| §3.6 requirement | Status |
|---|---|
| Positional/execution fixtures 1–5 | **NOT EXECUTED** beyond Phase-1 position arithmetic |
| Publication/dependency fixtures 6–10 | **NOT EXECUTED** |
| Base fixtures 11–13 | **NOT EXECUTED** |
| Negative/write-safety fixtures 14–19 | **NOT EXECUTED** |
| Independent-oracle six-group table | **NOT EXECUTED** |
| 9 production + 4 oracle mutation cycles | **NOT EXECUTED** |
| Three-way legacy/Plan/oracle comparison | **NOT EXECUTED** |
| Corpus rebaseline to 13/0/4 | **NOT EXECUTED** |
| Phase-7 closure/completion | **NOT EXECUTED** |

## Limitations

- This artifact proves only the Phase-1 helper cases and the raw behavior of three unchanged public
  donor schedules under legacy evaluation.
- It does not prove any recorded spike value, nonlinear scan admission, independent-oracle
  agreement, Plan execution, publication/write safety, diagnostics, or mutation sensitivity.
- The ReLU and top-level axiswise source donors lack retained inputs; the other exact donors have
  different semantics from the six recorded groups.
- No program or input was reverse-engineered from the recorded floats.
- Production and existing tests are untouched; the seed is imported by nothing.

## Task 4 estimate

The plan's **3–4 focused engineer-days** within the broader 13–18 day effort remains appropriate.
This rehearsal settles the small `retainedAxisPos` helper but does not reduce the main work:
recovering/re-authorizing exact semantic fixtures, implementing nonlinear scan block allocation and
result-only publication, extending the independent oracle, exercising 13 mutation cycles, and
running two focused reviews.

Until authentic source/input pairs are recovered or the governing plan explicitly replaces the six
recorded fixtures, Task 4 must remain stopped at Phase 2.

## Oracle fixture authoring

These are fresh observed oracles, not attempts to recover or reproduce the superseded §3.6 floats.
The four authored fixtures are logical `ScheduledProgram`s run directly by the seed, so their
required slot/write structure and observed values are reported there. The two adopted fixtures are
not transcribed or imported into the seed: it invokes Lean on each original source test file, which
executes that file's inline `run_cmd` assertions. The seed relays child stdout/stderr, fails on a
nonzero exit, and treats exit 0 only as confirmation of the values asserted by those source commands.

### Fixture 1 — leading pointwise scratch

| Field | Record |
|---|---|
| Program source (verbatim) | <pre><code>def fixture1 : ScheduledProgram :=<br>  { decls := [.iter f1l 3]<br>  , stmts := [.scan "S" [f1l]<br>      [.assign "S" [.free f1i, .iterAt f1l 0] (rhs "X" [.axis f1i])]<br>      [ .assign "T" [.free f1i]<br>          (rhs2 "S" [.axis f1i, .axis f1l] "K" [.axis f1i] (.pointwise .relu))<br>      , .assign "S" [.free f1i, .iterNext f1l] (rhs "T" [.axis f1i]) ]<br>      false]<br>  , env := {}<br>  , extNames := {"X", "K"}<br>  , explicitSizes := ({} : HashMap UID Nat).insert f1l.uid 3 }</code></pre> |
| Inputs (verbatim) | <pre><code>def fixture1Inputs : HashMap String DenseTensor :=<br>  (({} : HashMap String DenseTensor).insert "X" (tensorOf [2] [-1, 2])).insert<br>    "K" (tensorOf [2] [-2, 3])</code></pre> |
| Observed legacy value | `S shape [2, 3] = #[-1.000000, 2.000000, 0.000000, 2.000000, 6.000000, 18.000000]` |
| Structural facts | Scratch `T` has LHS slots `[0: .free f1i]`: its local axis is at index 0 and there is no `.iterAt` slot. Across base and recurrence, `T` has exactly one writing statement. The following state write reads `T`. All are asserted in the seed. |

### Fixture 2 — interleaved axiswise

| Field | Record |
|---|---|
| Program source (verbatim) | <pre><code>def fixture2 : ScheduledProgram :=<br>  { decls := [.iter f2l 3, .iter f2m 3]<br>  , stmts := [.scan "S" [f2l, f2m]<br>      [.assign "S" [.iterAt f2l 0, .free f2i, .iterAt f2m 0] (rhs "X" [.axis f2i])]<br>      [.assign "S" [.iterNext f2l, .freeNorm f2i, .iterNext f2m]<br>        (rhs "S" [.axis f2l, .axis f2i, .axis f2m] (.axiswise .normalize none))]<br>      false]<br>  , env := {}<br>  , extNames := {"X"}<br>  , explicitSizes :=<br>      (({} : HashMap UID Nat).insert f2l.uid 3).insert f2m.uid 3 }</code></pre> |
| Inputs (verbatim) | <pre><code>def fixture2Inputs : HashMap String DenseTensor :=<br>  ({} : HashMap String DenseTensor).insert "X" (tensorOf [2] [1, 3])</code></pre> |
| Observed legacy value | `S shape [3, 2, 3] = #[1.000000, 0.000000, 0.000000, 3.000000, 0.000000, 0.000000, 0.000000, 0.250000, 0.000000, 0.000000, 0.750000, 0.000000, 0.000000, 0.000000, 0.250000, 0.000000, 0.000000, 0.750000]` |
| Structural facts | Recurrence LHS slots are `[0: .iterNext f2l, 1: .freeNorm f2i, 2: .iterNext f2m]`. Thus the normalized local axis is strictly after one genuine iteration axis and strictly before the other. The nonlinearity is `.axiswise .normalize none` (unmasked). |

### Fixture 3 — adopted leading persistent nonlinear

| Field | Record |
|---|---|
| Adopted source command (verbatim; executed in place) | <pre><code>run_cmd do<br>  let j := ax "j" 1; let l := ax "l" 9<br>  let X := tensorOf [1] [1]; let A := tensorOf [1] [-1]<br>  let env : HashMap String DenseTensor := (({} : HashMap String DenseTensor).insert "X" X).insert "A" A<br>  let sizes := (({} : HashMap UID Nat).insert 1 1).insert 9 2<br>  let base : Stmt := .assign "S" [.free j, .iterAt l 0] { body := { terms := [{ factors := [.read "X" [.axis j]] }] }, nonlin := .identity }<br>  let recur : Stmt := .assign "S" [.free j, .iterNext l] { body := { terms := [{ factors := [.read "S" [.axis j, .axis l], .read "A" [.axis j]] }] }, nonlin := .pointwise .relu }<br>  match evalScan [] env sizes (.scan "S" [l] [base] [recur] false) with<br>  | .error e => throwError (toString e)<br>  | .ok outs => match outs.find? (·.1 == "S") with<br>    | some (_, S) => unless DenseTensor.approxEq S (tensorOf [1,2] [1, 0]) do throwError s!"relu scan wrong: {repr S.data}"<br>    | none => throwError "no S"</code></pre> |
| Inputs | `X = [1]`, `A = [-1]`, with `j = 1` and `l = 2`; the exact source declarations are included in the command above. |
| Adopted assertion confirmed | `test/Eval/ScanTest.lean` exited 0, confirming its exact inline command's assertion `S = [1, 0]`. The adopted command emits no value on success; this is not a seed-authored output. |
| Structural facts | Persistent `S` has both a base write and a recurrence write; the base is `.identity` and its own recurrence is `.pointwise .relu`. |

The seed runs `lake env lean test/Eval/ScanTest.lean`, so the original command above—not a
transcription—still confirms the recorded `S = [1, 0]`.

### Fixture 4 — nonlinear base

| Field | Record |
|---|---|
| Program source (verbatim) | <pre><code>def fixture4 : ScheduledProgram :=<br>  { decls := [.iter f4l 3]<br>  , stmts := [.scan "S" [f4l]<br>      [.assign "S" [.free f4i, .iterAt f4l 0]<br>        (rhs "X" [.axis f4i] (.pointwise .relu))]<br>      [.assign "S" [.free f4i, .iterNext f4l]<br>        (rhs2 "S" [.axis f4i, .axis f4l] "A" [.axis f4i])]<br>      false]<br>  , env := {}<br>  , extNames := {"X", "A"}<br>  , explicitSizes := ({} : HashMap UID Nat).insert f4l.uid 3 }</code></pre> |
| Inputs (verbatim) | <pre><code>def fixture4Inputs : HashMap String DenseTensor :=<br>  (({} : HashMap String DenseTensor).insert "X" (tensorOf [2] [-2, 3])).insert<br>    "A" (tensorOf [2] [2, -1])</code></pre> |
| Observed legacy value | `S shape [2, 3] = #[0.000000, 0.000000, 0.000000, 3.000000, -3.000000, 3.000000]` |
| Structural facts | The base statement's `nonlin` is `.pointwise .relu`; the recurrence's is `.identity`. This is the opposite placement from fixtures 1 and 3. |

### Fixture 5 — scratch → scratch → state

| Field | Record |
|---|---|
| Program source (verbatim) | <pre><code>def fixture5 : ScheduledProgram :=<br>  { decls := [.iter f5l 3]<br>  , stmts := [.scan "S" [f5l]<br>      [.assign "S" [.iterAt f5l 0] (rhs "X" [])]<br>      [ .assign "T" [] (rhs2 "S" [.axis f5l] "A" [.axis f5l] (.pointwise .relu))<br>      , .assign "U" [] (rhs2 "T" [] "B" [.axis f5l])<br>      , .assign "S" [.iterNext f5l] (rhs "U" []) ]<br>      false]<br>  , env := {}<br>  , extNames := {"X", "A", "B"}<br>  , explicitSizes := ({} : HashMap UID Nat).insert f5l.uid 3 }</code></pre> |
| Inputs (verbatim) | <pre><code>def fixture5Inputs : HashMap String DenseTensor :=<br>  ((({} : HashMap String DenseTensor).insert "X" (tensorOf [] [1])).insert<br>    "A" (tensorOf [3] [2, -3, 4])).insert "B" (tensorOf [3] [3, 2, 1])</code></pre> |
| Observed legacy value | `S shape [3] = #[1.000000, 6.000000, 0.000000]` |
| Structural facts | Destinations are `T → U → S` in dependency order. `T` and `U` have no base write; `S` does. `T` is `.pointwise .relu`, `U` reads `T`, and the state write reads `U`; all are asserted. |

### Fixture 6 — adopted coupled states

| Field | Record |
|---|---|
| Adopted source command (verbatim; executed in place) | <pre><code>run_cmd do<br>  let e0 : HashMap String DenseTensor := {}<br>  let env := (((((e0.insert "X" (tensorOf [1] [1.0])).insert "Y" (tensorOf [1] [2.0])).insert "W_G"<br>      (tensorOf [1,1] [1.0])).insert "U" (tensorOf [1,1] [1.0])).insert "W_H"<br>      (tensorOf [1,1] [1.0])).insert "V" (tensorOf [1,1] [1.0])<br>  match TLProgram.eval (tlprog!{<br>    iter l = 3<br>    G[j, 0]    := X[j]<br>    G[j, l +1] := relu(G[j, l] · W_G[j, k] + H[j, l] · U[j, k])<br>    H[j, 0]    := Y[j]<br>    H[j, l +1] := relu(H[j, l] · W_H[j, k] + G[j, l] · V[j, k])<br>  }) env with<br>  | .error e => throwError s!"scan: {e}"<br>  | .ok report => match report.env["G"]?, report.env["H"]? with<br>    | some G, some H =><br>        unless DenseTensor.approxEq G (tensorOf [1,3] [1,3,6]) do<br>          throwError s!"scan G wrong: {repr G.data}"<br>        unless DenseTensor.approxEq H (tensorOf [1,3] [2,3,6]) do<br>          throwError s!"scan H wrong: {repr H.data}"<br>    | _, _ => throwError "scan: no G/H"</code></pre> |
| Inputs | `X = [1]`, `Y = [2]`, and `W_G = U = W_H = V = [[1]]`; the exact source declarations are included in the command above. |
| Adopted assertion confirmed | `test/Eval/EvalExamplesTest.lean` exited 0, confirming example 5's exact inline assertions `G = [1, 3, 6]` and `H = [2, 3, 6]`. The adopted command emits no values on success; these are not seed-authored outputs. |
| Structural facts | Coupled persistent states `G` and `H` each have a base and nonlinear recurrence; each recurrence reads both pre-step states. |

The seed runs `lake env lean test/Eval/EvalExamplesTest.lean`, so original example 5 above—not a
transcription—still confirms the recorded `G = [1, 3, 6]`, `H = [2, 3, 6]`.

### Decisions not fixed by the brief

- Fixture 1 uses two features, `X = [-1, 2]`, `K = [-2, 3]`, and three history positions.
- Fixture 2 uses unmasked `normalize`, two local values `[1, 3]`, and two iteration axes of extent 3.
- Fixture 4 uses `X = [-2, 3]`, a linear multiplier `A = [2, -1]`, and extent 3.
- Fixture 5 uses scalar state, ReLU scratch `T`, linear scratch `U`, and extent 3.
- Fresh UIDs are local to the four authored fixtures. None of the six fixtures uses a mask,
  predicate, scatter, max/min, or anything other than `f64`.

### Direct seed output

Command, from `leanncd/`:

```bash
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/nonlinear_scan_admission/OracleFixtureSeed.lean
```

Raw stdout, verbatim:

```text
FIXTURE 1: S shape [2, 3] = #[-1.000000, 2.000000, 0.000000, 2.000000, 6.000000, 18.000000]
FIXTURE 2: S shape [3, 2, 3] = #[1.000000, 0.000000, 0.000000, 3.000000, 0.000000, 0.000000, 0.000000, 0.250000, 0.000000, 0.000000, 0.750000,
  0.000000, 0.000000, 0.000000, 0.250000, 0.000000, 0.000000, 0.750000]
FIXTURE 3 ADOPTED: SOURCE ASSERTIONS PASSED (test/Eval/ScanTest.lean exited 0; its inline ReLU-scan command asserts S = [1, 0])
FIXTURE 4: S shape [2, 3] = #[0.000000, 0.000000, 0.000000, 3.000000, -3.000000, 3.000000]
FIXTURE 5: S shape [3] = #[1.000000, 6.000000, 0.000000]
FIXTURE 6 ADOPTED: SOURCE ASSERTIONS PASSED (test/Eval/EvalExamplesTest.lean exited 0; its inline example 5 command asserts G = [1, 3, 6] and H = [2, 3, 6])
```

### Final gates

```bash
"$HOME/.elan/bin/lake" build Tests
```

```text
Build completed successfully (8657 jobs).
```

```bash
"$HOME/.elan/bin/lake" build LeanNCD
```

```text
Build completed successfully (8543 jobs).
```

## Oracle `.freeNorm` extension

### Complete `ScanUnroll.lean` diff

```diff
diff --git a/leanncd/test/Eval/PropertyOracle/ScanUnroll.lean b/leanncd/test/Eval/PropertyOracle/ScanUnroll.lean
index fddfe6b..077a79d 100644
--- a/leanncd/test/Eval/PropertyOracle/ScanUnroll.lean
+++ b/leanncd/test/Eval/PropertyOracle/ScanUnroll.lean
@@ -165,0 +166 @@ geometry is not the admitted rectangular all-axis `+1` form"
+    | some (LHSSlot.freeNorm a) => pure (LHSSlot.freeNorm a)
@@ -257,0 +259 @@ private def baseFreeSlots (st : StateGeom) (s : Stmt) : Except String (List LHSS
+    | some (LHSSlot.freeNorm a) => pure (LHSSlot.freeNorm a)
```

### Before

```text
LEGACY: S shape [3, 2, 3] = #[1.000000, 0.000000, 0.000000, 3.000000, 0.000000, 0.000000, 0.000000, 0.250000, 0.000000, 0.000000, 0.750000,
  0.000000, 0.000000, 0.000000, 0.250000, 0.000000, 0.000000, 0.750000]
INDEPENDENT ERROR: S: dimension 1 is neither advancing nor a plain free axis (LeanNCD.LHSSlot.freeNorm { name := "i", uid := 202, kind := LeanNCD.AxisKind.real }) — outside the oracle's fragment
```

### After

```text
LEGACY: S shape [3, 2, 3] = #[1.000000, 0.000000, 0.000000, 3.000000, 0.000000, 0.000000, 0.000000, 0.250000, 0.000000, 0.000000, 0.750000,
  0.000000, 0.000000, 0.000000, 0.250000, 0.000000, 0.000000, 0.750000]
INDEPENDENT: S shape [3, 2, 3] = #[1.000000, 0.000000, 0.000000, 3.000000, 0.000000, 0.000000, 0.000000, 0.250000, 0.000000, 0.000000, 0.750000,
  0.000000, 0.000000, 0.000000, 0.250000, 0.000000, 0.000000, 0.750000]
```

The legacy and independent results agree.

### Gate job counts

```text
Build completed successfully (8505 jobs).
Build completed successfully (8657 jobs).
Build completed successfully (8543 jobs).
```

### Import audit

`ScanUnroll.lean`'s import list is unchanged:

```lean
import Eval.PropertyOracle.Compare
import Eval.PropertyOracle.ScanGen
```

### Decisions

No decisions beyond the brief were required.

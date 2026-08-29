import LeanNCD.Eval.Plan.Adapter
import LeanNCD.Eval.Entry
import Eval.PropertyOracle.Gen
import Eval.PropertyOracle.Compare
import Eval.PropertyOracle.ScanGen
import Eval.PropertyOracle.ScanUnroll
import Eval.Plan.ScanCompileTest
import Eval.Plan.AdapterTest

/-!
# Wave C C4 — differential testing against the legacy evaluator

The empirical core of C4: `prepareEvalPlan`/`runPreparedDense` against `evalScheduled`, over every
`PropertyOracle.enumPrograms` entry, plus an alpha-renaming law and test-the-tester mutations.
Capability-row accept/reject coverage, deterministic-slot/term-basis fixtures, zero-coefficient
contraction, repeated-assignment, `requiredInputs`-order independence, and packing/unpacking edge
cases are already covered by `CompileTest.lean` and `AdapterTest.lean` — this file does not
re-derive them.

Wave F F4 Task 4 extends the same treatment to SOURCE SCANS at the end of this file:
`ScanCompileTest.lean`'s twelve acceptance fixtures assert the STRUCTURE the compiler residualized;
the section below asserts what that structure DOES — that each one executes through
`prepareEvalPlan`/`runPreparedDense` to a result bit-identical to `evalScheduled`, and that the
curated `enumScanCases` generator splits exactly 9 accepted / 4 `unsupportedNonlin` /
4 `unsupportedAgg` with every accepted case matching the legacy evaluator.
-/

namespace LeanNCD.Eval.Plan.DifferentialTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.PropertyOracle Std

-- ── Alpha-renaming law (§5.4): `PlanBindings` can be replaced for an alpha-renamed source
-- program without changing the indexed computation — verified here, not assumed. ──

private def origAlphaProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := X[i]
}

private def renamedAlphaProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y2[i] := X2[i]
}

private def alphaInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[2], #[7.0, 9.0]⟩

private def alphaInputs2 : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X2" ⟨[2], #[7.0, 9.0]⟩

run_cmd do
  match origAlphaProg.compileToScheduled.run 0, renamedAlphaProg.compileToScheduled.run 0 with
  | .error e _, _ => throwError s!"origAlphaProg compile failed: {repr e}"
  | _, .error e _ => throwError s!"renamedAlphaProg compile failed: {repr e}"
  | .ok sched1 _, .ok sched2 _ =>
      match prepareEvalPlan sched1 (InputSignature.ofDenseInputs alphaInputs),
            prepareEvalPlan sched2 (InputSignature.ofDenseInputs alphaInputs2) with
      | .error _, _ => throwError "origAlphaProg failed to prepare"
      | _, .error _ => throwError "renamedAlphaProg failed to prepare"
      | .ok p1, .ok p2 =>
          unless p1.plan.raw == p2.plan.raw do
            throwError s!"alpha-renaming CHANGED the checked semantic graph: \
{repr p1.plan.raw} vs {repr p2.plan.raw}"
          -- `PlanBindings` has no derived `BEq` (`RequiredBindings` has none — same
          -- private-constructor precedent as `PreparedPlan` itself): compare through
          -- `.requiredInputs.bindings`/`.materializedNames` instead of whole-struct equality.
          unless p1.bindings.requiredInputs.bindings != p2.bindings.requiredInputs.bindings ||
                 p1.bindings.materializedNames != p2.bindings.materializedNames do
            throwError "alpha-renaming did NOT change bindings — bindings should be name-keyed"

-- ── The `enumPrograms` differential sweep ──

/-- Exact environment equality: same key set, `denseEq`-equal (`Compare.lean`) on every key. -/
private def envEq (e1 e2 : HashMap String DenseTensor) : Bool :=
  let ks1 := e1.toList.map Prod.fst
  let ks2 := e2.toList.map Prod.fst
  ks1.length == ks2.length && ks1.all (fun k => ks2.contains k) &&
    ks1.all (fun k => match e1[k]?, e2[k]? with
      | some a, some b => denseEq a b
      | _, _ => false)

private def capabilityCategory : CapabilityError → String
  | .scanNode _ => "scanNode"
  | .scatterOrAffineLhs _ => "scatterOrAffineLhs"
  | .unsupportedLhsSlot _ => "unsupportedLhsSlot"
  | .unsupportedNonlin _ => "unsupportedNonlin"
  | .maskOrPredicate _ => "maskOrPredicate"
  | .unaryFactor _ => "unaryFactor"
  | .unsupportedAgg _ => "unsupportedAgg"
  | .booleanOutput _ => "booleanOutput"
  | .unsupportedDtype _ => "unsupportedDtype"
  | .dynamicShape _ => "dynamicShape"
  | .recurrenceOrCallback _ => "recurrenceOrCallback"
  | .noAdvancingAxis _ => "noAdvancingAxis"

private inductive SweepOutcome
  | accepted
  | rejected (category : String)

/-- Check one `enumPrograms` entry. Rejected entries only need to be CONSISTENTLY rejected (both
    `capabilityPreflight` AND `prepareEvalPlan`, with a `.capability`-tagged failure) — never
    compared against `evalScheduled`, since they are legitimately outside Wave C's fragment.
    Accepted entries are compared bit-for-bit against `evalScheduled`. Any inconsistency or
    disagreement is a real bug and aborts the whole sweep with a diagnostic message. -/
private def checkEntry (p : TLProgram) (env : HashMap String DenseTensor) :
    Except String SweepOutcome := do
  let sched ← match p.compileToScheduled.run 0 with
    | .ok sched _ => pure sched
    | .error e _ => throw s!"generator produced a program that fails to compile: {repr e}"
  let sig := InputSignature.ofDenseInputs env
  match capabilityPreflight sched with
  | .error capErr =>
      match prepareEvalPlan sched sig with
      | .ok _ =>
          throw s!"INCONSISTENCY: capabilityPreflight rejected ({repr capErr}) but \
prepareEvalPlan accepted the same schedule.\nprogram: {repr p}"
      | .error pf =>
          match pf.cause with
          | .capability _ => pure (SweepOutcome.rejected (capabilityCategory capErr))
          | _ =>
              throw s!"INCONSISTENCY: prepareEvalPlan rejected a capability-rejected schedule \
for a NON-capability reason.\nprogram: {repr p}"
  | .ok () =>
      match prepareEvalPlan sched sig with
      | .error _ =>
          throw s!"prepareEvalPlan rejected a program capabilityPreflight accepted.\nprogram: {repr p}"
      | .ok prepared =>
          match runPreparedDense prepared env, evalScheduled sched env with
          | .error e, _ =>
              throw s!"runPreparedDense failed on an accepted program (warnings={e.warnings.length}).\nprogram: {repr p}"
          | _, .error e =>
              throw s!"evalScheduled failed on a capabilityPreflight-accepted program: \
{e.error}.\nprogram: {repr p}"
          | .ok planReport, .ok refReport =>
              let envOk := envEq planReport.env refReport.env
              -- `EvalWarning` derives `DecidableEq` only (no `BEq`) — compare via `List`'s derived
              -- `DecidableEq` (order matters: warnings are meant to preserve emission order, not be
              -- compared as a set).
              let warningsOk := decide (planReport.warnings = refReport.warnings)
              if envOk && warningsOk then
                pure SweepOutcome.accepted
              else if !envOk then
                throw s!"DISAGREEMENT (env) between runPreparedDense and evalScheduled.\n\
program: {repr p}\ninput env: {repr env}\nplan env: {repr planReport.env.toList}\n\
reference env: {repr refReport.env.toList}"
              else
                throw s!"DISAGREEMENT (warnings) between runPreparedDense and evalScheduled.\n\
program: {repr p}\ninput env: {repr env}\nplan warnings: {planReport.warnings.map toString}\n\
reference warnings: {refReport.warnings.map toString}"

/-- Fold the whole corpus, accumulating (total, accepted, per-category rejection counts).
    `foldlM` over `Except String _` short-circuits on the first `checkEntry` failure — a genuine
    inconsistency or disagreement stops the sweep immediately rather than continuing past it. -/
private def sweep : Except String (Nat × Nat × HashMap String Nat) :=
  enumPrograms.foldlM (fun (acc : Nat × Nat × HashMap String Nat) (pe : TLProgram × HashMap String DenseTensor) => do
      let (total, accepted, rejCounts) := acc
      match ← checkEntry pe.1 pe.2 with
      | .accepted => pure (total + 1, accepted + 1, rejCounts)
      | .rejected cat => pure (total + 1, accepted, rejCounts.insert cat (rejCounts.getD cat 0 + 1)))
    (0, 0, ({} : HashMap String Nat))

run_cmd do
  match sweep with
  | .error msg => throwError s!"DIFFERENTIAL SWEEP FAILED:\n{msg}"
  | .ok (total, accepted, rejCounts) =>
      dbg_trace s!"DifferentialTest sweep: total={total} accepted={accepted} \
rejected={total - accepted} categories={rejCounts.toList}"
      pure ()

-- Pin the REAL observed counts (confirmed by an actual run, not estimated) so a future regression
-- that silently changes the fragment's accept/reject boundary — or `enumPrograms`'s own size — is
-- caught rather than silently re-baselined. Every `enumPrograms` entry today is inside Wave C's
-- scan-free fragment (no scatter/scan/predicate/nonlin/agg construct anywhere in `Gen.lean`'s
-- generator), so `rejected == 0` is the real, not merely expected, outcome; the day a future
-- `Gen.lean` change adds an out-of-fragment construct, this guard fails loudly instead of silently
-- starting to skip differential comparison on the new entries.
#guard match sweep with
  | .ok (total, accepted, rejCounts) => total == 3832 && accepted == 3832 && rejCounts.isEmpty
  | .error _ => false

-- ── Test-the-tester mutations ──

private def envOf (p : TLProgram) (env : HashMap String DenseTensor) :
    Except String (HashMap String DenseTensor) := do
  let sched ← match p.compileToScheduled.run 0 with
    | .ok s _ => pure s
    | .error e _ => throw s!"compile failed: {repr e}"
  match evalScheduled sched env with
  | .ok r => pure r.env
  | .error e => throw s!"eval failed: {e.error}"

private def planAgrees (p : TLProgram) (env : HashMap String DenseTensor) : Except String Unit := do
  match checkEntry p env with
  | .ok .accepted => pure ()
  | .ok (.rejected cat) => throw s!"expected an accepted case, got rejected ({cat})"
  | .error e => throw e

-- ── Rank-2 output coverage: every `enumPrograms` entry and every hand-built value-comparison
-- fixture above writes a rank-1 output (`Y[i] := ...`, one `.free` LHS slot). The multi-retained-
-- axis surface — `outputShape` in `retainedUids` order, `outputPos := Array.range`, how
-- `basisUids`'s retained prefix lines up with `runDenseAssign`'s row-major coordinate enumeration —
-- is otherwise untested at the value level. `Y[i, j] := A[i] · B[j]` (outer product, both `i` and
-- `j` retained, no contraction) exercises exactly that surface. ──

private def rank2Prog : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  Y[i, j] := A[i] · B[j]
}

private def rank2Inputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" ⟨[2], #[1.0, 2.0]⟩).insert
    "B" ⟨[3], #[10.0, 20.0, 30.0]⟩

run_cmd do
  match planAgrees rank2Prog rank2Inputs with
  | .error e => throwError s!"rank-2 output case: {e}"
  | .ok () => pure ()

-- ── Multiple factors and ordered reductions: `CompileTest.lean`'s `multiReductionSched` fixture
-- checks the STRUCTURAL basis/reduction ordering (`reductionPos == #[1, 2]`, per-factor coeff
-- rows) but never actually RUNS the plan. `enumPrograms` never contracts more than one axis (its
-- generator caps every term at 2 factors, `Gen.lean` confirmed), so a THREE-factor term
-- contracting TWO axes jointly (`Y[i] := A[i,j]·B[j,k]·C[k]`, summing over both `j` and `k`) is
-- otherwise unexercised at the value level anywhere in this suite. Cross-checked against
-- `evalScheduled` via `planAgrees`, same belt-and-suspenders pattern as `rank2Prog` above. ──

private def multiReductionProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  axis k : ℕ = 2
  Y[i] := A[i, j] · B[j, k] · C[k]
}

private def multiReductionProgInputs : HashMap String DenseTensor :=
  ((({} : HashMap String DenseTensor).insert "A" ⟨[2, 2], #[1.0, 2.0, 3.0, 4.0]⟩).insert
    "B" ⟨[2, 2], #[1.0, 0.0, 0.0, 1.0]⟩).insert "C" ⟨[2], #[1.0, 1.0]⟩

run_cmd do
  match planAgrees multiReductionProg multiReductionProgInputs with
  | .error e => throwError s!"multi-factor ordered-reduction case: {e}"
  | .ok () => pure ()

-- ── Repeated-assignment executing coverage: `CompileTest.lean`'s `repeatSched` fixture
-- (`Y[i]:=A[i]; Y[i]:=B[i]; Z[i]:=Y[i]`) is checked STRUCTURALLY there (`materializedNames ==
-- #["Y","Y","Z"]`, two distinct slots for the two `Y` entries) but never actually RUN.
-- `PlanBindings.materializedNames`'s deliberate non-deduplication design and `unpack`'s "later
-- insertion wins" behavior have zero executing test behind them without this: a regression in
-- `unpack`'s fold direction (e.g. `foldr` instead of `foldl`, or an accidental `.reverse`) would
-- silently make a reassigned name return its FIRST write instead of its last, and nothing else in
-- this slice would catch it. Runs the equivalent source program through the full
-- `prepareEvalPlan` → `runPreparedDense` pipeline, asserts the explicit expected value (last write
-- wins), AND cross-checks against `evalScheduled` via `planAgrees` — belt and suspenders. ──

private def repeatProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Y[i] := B[i]
  Z[i] := Y[i]
}

private def repeatProgInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" ⟨[2], #[1.0, 2.0]⟩).insert
    "B" ⟨[2], #[100.0, 200.0]⟩

run_cmd do
  match planAgrees repeatProg repeatProgInputs with
  | .error e => throwError s!"repeated-assignment case: {e}"
  | .ok () => pure ()
  match repeatProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"repeatProg compile failed: {repr e}"
  | .ok sched _ =>
      match prepareEvalPlan sched (InputSignature.ofDenseInputs repeatProgInputs) with
      | .error _ => throwError "repeatProg prepare failed (unexpected — planAgrees already accepted it)"
      | .ok prepared =>
          match runPreparedDense prepared repeatProgInputs with
          | .error e => throwError s!"repeatProg run failed (warnings={e.warnings.length})"
          | .ok report =>
              match report.env["Y"]?, report.env["Z"]? with
              | some y, some z =>
                  unless denseEq y ⟨[2], #[100.0, 200.0]⟩ do
                    throwError s!"Y did not take the LAST write's value: {repr y.data}"
                  unless denseEq z ⟨[2], #[100.0, 200.0]⟩ do
                    throwError s!"Z did not read the LAST write of Y: {repr z.data}"
              | _, _ => throwError "Y or Z missing from repeated-assignment plan env"

/-- Confirm mutating `original` into `mutated` actually changes `outputName`'s value relative to
    `original`'s OWN `evalScheduled` result — a mutation that doesn't break agreement is worse than
    no mutation test at all. -/
private def mutationHasTeeth (original mutated : TLProgram) (env : HashMap String DenseTensor)
    (outputName : String) : Except String Unit := do
  let origEnv ← envOf original env
  let mutEnv ← envOf mutated env
  match origEnv[outputName]?, mutEnv[outputName]? with
  | some a, some b =>
      if denseEq a b then
        throw s!"mutation did NOT break agreement (both = {repr a.data}) — no teeth"
      else pure ()
  | none, _ => throw s!"{outputName} missing from original's env"
  | _, none => throw s!"{outputName} missing from mutated's env"

-- (a) change one coefficient in an index expression: `A[i+1]` (coeff 1 on `i`) vs `A[2*i+1]`
-- (coeff 2). Original stays in-range for every `i`; the mutated coefficient pushes the last read
-- out of range (zero-padded), so the two must disagree.
private def coeffOrigProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[i + 1]
}

private def coeffMutProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[2 * i + 1]
}

private def coeffInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "A" ⟨[4], #[10.0, 20.0, 30.0, 40.0]⟩

run_cmd do
  match planAgrees coeffOrigProg coeffInputs with
  | .error e => throwError s!"mutation (a) original case: {e}"
  | .ok () => pure ()
  match mutationHasTeeth coeffOrigProg coeffMutProg coeffInputs "Y" with
  | .error e => throwError s!"mutation (a) (coefficient change) has no teeth: {e}"
  | .ok () => pure ()

-- (b) drop a term from a multi-term sum: `Y[i] := A[i] + B[i]` vs `Y[i] := A[i]`.
private def dropOrigProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i] + B[i]
}

private def dropMutProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
}

private def dropInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" ⟨[2], #[1.0, 2.0]⟩).insert
    "B" ⟨[2], #[10.0, 20.0]⟩

run_cmd do
  match planAgrees dropOrigProg dropInputs with
  | .error e => throwError s!"mutation (b) original case: {e}"
  | .ok () => pure ()
  match mutationHasTeeth dropOrigProg dropMutProg dropInputs "Y" with
  | .error e => throwError s!"mutation (b) (dropped term) has no teeth: {e}"
  | .ok () => pure ()

-- (c) reorder a Float-sensitive fold: `Y[i] := P[i] + Q[i] + R[i]` (three single-factor terms,
-- folded strictly in array order under `reduceId := 0.0`) with `P=1e16, Q=1.0, R=1.0` vs the
-- fully-reversed term order `R[i] + Q[i] + P[i]`. `((0+1e16)+1.0)+1.0` rounds `1e16+1.0` back to
-- `1e16` at this magnitude (binary64 ULP 2, same phenomenon C2/C3's fold-order fixtures already
-- confirmed), so the forward order yields `1e16` exactly; the reversed order accumulates
-- `((0+1.0)+1.0)+1e16 = 2.0 + 1e16`, and `2.0` IS exactly one ULP at this magnitude, so it adds
-- without rounding loss — a genuinely different Float bit pattern, confirmed by a real run, not
-- hand-derivation alone.
private def foldOrigProg : TLProgram := tlprog!{
  axis i : ℕ = 1
  Y[i] := P[i] + Q[i] + R[i]
}

private def foldMutProg : TLProgram := tlprog!{
  axis i : ℕ = 1
  Y[i] := R[i] + Q[i] + P[i]
}

private def foldInputs : HashMap String DenseTensor :=
  ((({} : HashMap String DenseTensor).insert "P" ⟨[1], #[1e16]⟩).insert
    "Q" ⟨[1], #[1.0]⟩).insert "R" ⟨[1], #[1.0]⟩

run_cmd do
  match planAgrees foldOrigProg foldInputs with
  | .error e => throwError s!"mutation (c) original case: {e}"
  | .ok () => pure ()
  match mutationHasTeeth foldOrigProg foldMutProg foldInputs "Y" with
  | .error e => throwError s!"mutation (c) (fold reorder) has no teeth: {e}"
  | .ok () => pure ()

/-! ## Wave F F4 Task 4 — source scans: named-boundary execution and legacy parity

`ScanCompileTest.lean` pins WHAT the compiler residualizes (whole `RawScanPlan` values, write maps,
affine rows, capture slots). This section pins what that residualization COMPUTES: every admitted
fixture there is executed through the public named API and compared against `evalScheduled`.

Scope note (proposal §10, Law 1). Parity is claimed only for "the source fragment whose checked
Jacobi semantics is observationally equal to the legacy worker". The legacy scan worker
(`LeanNCD/Eval/Scan.lean`) is known nonconforming in two ways F0 pinned: it applies Gauss-Seidel
rather than Jacobi update (a later `recur` statement observes an earlier sibling's just-written
value), and it silently applies last-write-wins where the checked worker rejects colliding
multi-base-writes. Neither is reachable from any fixture below — verified, not assumed:

* Gauss-Seidel is only observable when a later recurrence statement reads a STATE at a coordinate an
  earlier sibling already wrote this step. The multi-statement recurrences here
  (`ScanCompileTest.coupledSched`, the generator's `template3`) all write at the ADVANCED coordinate
  and read at the current one, so no sibling read can see a sibling write. `scratchSched`'s later
  statement does read what its earlier sibling produced, but that name is block-local SCRATCH, which
  both workers deliberately make visible to later statements in the same block — not state.
* `multiBaseSched`'s two base writes are disjoint by construction (`r` pinned to different
  literals), so last-write-wins never arbitrates anything.

All twenty-one scan programs exercised here (twelve hand-written, nine generated) agree with
`evalScheduled` exactly, so no divergence needed classifying. A future fixture that DID diverge would
fail loudly here rather than being absorbed. -/

/-- Names a scan's recurrence list produces that are NOT persistent state — block-local scratch.
    Derived the same way `compileScan` classifies (base destinations are the states; a recurrence-
    only destination is scratch), so this is the set that must never reach the named boundary. -/
private def scanScratchNames (sched : ScheduledProgram) : List String :=
  sched.stmts.flatMap (fun
    | .scan _ _ base recur _ =>
        let stateNames := (base.map Stmt.lhsName).eraseDups
        ((recur.map Stmt.lhsName).eraseDups).filter (fun nm => !stateNames.contains nm)
    | _ => [])

/-- The task's execution matrix for one admitted scan fixture:

    1. compile with `prepareEvalPlan` (and confirm a `PlanStep.scan` was actually emitted — an
       execution assertion that silently stopped covering scans would otherwise still pass);
    2. execute with `runPreparedDense`;
    3. execute the same `ScheduledProgram` with `evalScheduled`;
    4. compare EVERY materialized persistent state one by one, then the whole environment (the
       per-name loop names the offender; the whole-environment check additionally catches an extra
       or missing key that a per-name loop structurally cannot see);
    5. verify every named input the plan does not overwrite is returned unchanged;
    6. verify every block-local scratch name is absent from the unpacked environment AND from
       `materializedNames` — with `expectedScratch` pinned by the caller, so a fixture that stopped
       having scratch at all cannot make this check pass vacuously;
    7. compare warnings as LISTS — order and payload, not count;
    8. (F4 Task 5) run the THIRD leg — `PropertyOracle.independentRun`'s mechanically generated
       scan-free unrolling, evaluated by the ordinary assignment evaluator with no scan construct
       anywhere — and compare every materialized state against the compiled plan, plus scratch
       privacy on that leg too.

    Points 1–7 compare two implementations that share the source language's front end; point 8 is
    what makes this a genuine differential rather than a consistency check. Warnings are compared
    only between legs 1 and 2: the unrolling replaces every scan-axis index with a literal, so which
    reads are STATICALLY out of extent legitimately changes, while the VALUES may not. -/
private def scanParityCheck (name : String) (sched : ScheduledProgram)
    (inputs : HashMap String DenseTensor) (expectedScratch : List String) :
    Except String Unit := do
  -- (6a) the scratch set this fixture is asserted to have.
  let scratch := scanScratchNames sched
  unless scratch == expectedScratch do
    throw s!"{name}: scratch names changed: got {scratch}, expected {expectedScratch}"
  -- (1) compile.
  let prepared ← match prepareEvalPlan sched (InputSignature.ofDenseInputs inputs) with
    | .ok p => pure p
    | .error f => throw s!"{name}: prepareEvalPlan rejected an admitted scan fixture: \
{ScanCompileTest.render f.cause}"
  unless prepared.plan.raw.steps.any (fun s => match s with
      | .scan _ => true | .assign _ | .pointwise _ | .axiswise _ => false) do
    throw s!"{name}: the compiled plan contains no scan step — this fixture no longer exercises \
F4's source scan compiler"
  -- (6b) scratch never becomes a published name. Checked BEFORE the run so a leak is reported as
  -- the privacy failure it is, rather than downstream as "the legacy env is missing a key".
  for nm in scratch do
    if prepared.bindings.materializedNames.any (·.name == nm) then
      throw s!"{name}: block-local scratch {nm} became a materialized name"
  -- (2) execute through the public named API.
  let planReport ← match runPreparedDense prepared inputs with
    | .ok r => pure r
    | .error e => throw s!"{name}: runPreparedDense failed on an admitted fixture \
(warnings={e.warnings.length})"
  -- (6c) …and never reaches the unpacked environment. `unpack` starts from the caller's own `env`,
  -- so a leak shows up as an EXTRA key — which asserting "the expected states are present" could
  -- never detect. Asserted against the legacy boundary too: both must keep it private.
  for nm in scratch do
    if (planReport.env[nm]?).isSome then
      throw s!"{name}: block-local scratch {nm} leaked into the unpacked environment"
  -- (3) execute the same schedule with the legacy evaluator.
  let refReport ← match evalScheduled sched inputs with
    | .ok r => pure r
    | .error e => throw s!"{name}: evalScheduled failed on an admitted fixture: {e.error}"
  for nm in scratch do
    if (refReport.env[nm]?).isSome then
      throw s!"{name}: the LEGACY evaluator published scratch {nm} — the two boundaries disagree \
about privacy, which this parity check would otherwise report only as an env mismatch"
  -- (4) every materialized persistent state, compared exactly and individually.
  if prepared.bindings.materializedNames.isEmpty then
    throw s!"{name}: no materialized names — nothing for the parity check to compare"
  for b in prepared.bindings.materializedNames do
    match planReport.env[b.name]?, refReport.env[b.name]? with
    | some a, some c =>
        unless denseEq a c do
          throw s!"{name}: materialized state {b.name} diverges from the legacy evaluator: \
plan={repr a.shape}/{repr a.data} ref={repr c.shape}/{repr c.data}"
    | none, _ => throw s!"{name}: materialized name {b.name} is absent from the unpacked env"
    | _, none => throw s!"{name}: materialized name {b.name} is absent from the legacy env"
  -- (4b) whole-environment equality: same key set, `denseEq` on every key.
  unless envEq planReport.env refReport.env do
    throw s!"{name}: environment mismatch.\nplan env: {repr planReport.env.toList}\n\
reference env: {repr refReport.env.toList}"
  -- (5) named inputs the plan does not itself overwrite come back untouched.
  for (nm, t) in inputs.toList do
    unless prepared.bindings.materializedNames.any (·.name == nm) do
      match planReport.env[nm]? with
      | some t' =>
          unless denseEq t t' do
            throw s!"{name}: input {nm} was modified by the run: {repr t'.data}"
      | none => throw s!"{name}: input {nm} disappeared from the unpacked env"
  -- (7) warnings compared as lists: order AND payload.
  unless decide (planReport.warnings = refReport.warnings) do
    throw s!"{name}: warnings differ.\nplan: {planReport.warnings.map toString}\n\
reference: {refReport.warnings.map toString}"
  -- (8) the third leg: an independently derived scan-free unrolling.
  let indepEnv ← match PropertyOracle.independentRun sched inputs with
    | .ok e    => pure e
    | .error m => throw s!"{name}: the independent scan-free unrolling failed: {m}"
  for b in prepared.bindings.materializedNames do
    match planReport.env[b.name]?, indepEnv[b.name]? with
    | some a, some c =>
        unless denseEq a c do
          throw s!"{name}: THREE-WAY DIFFERENTIAL FAILURE — materialized state {b.name} disagrees \
with the independent scan-free unrolling.\nplan={repr a.shape}/{repr a.data}\n\
unrolled={repr c.shape}/{repr c.data}\nThis is a semantic finding, not an oracle to retune: see \
the plan's §12.2 stop condition."
    | none, _ => throw s!"{name}: materialized name {b.name} is absent from the unpacked env"
    | _, none => throw s!"{name}: the independent unrolling published no {b.name}"
  -- scratch stays private on the third leg too: leaf names live inside the per-scan sub-evaluation
  -- and the reconstruction only republishes persistent states.
  for nm in scratch do
    if (indepEnv[nm]?).isSome then
      throw s!"{name}: block-local scratch {nm} escaped the independent unrolling"

/-- Every acceptance fixture `ScanCompileTest.lean` asserts structurally, run through the execution
    matrix. The list is exhaustive over that file's Part 1 (A, B, C, D/E, F, G, H, I/J, K/L —
    nine `ScheduledProgram`s covering its twelve lettered shapes); `G` deliberately reuses `F`'s
    input map, exactly as the structural file does. -/
private def scanFixtures :
    List (String × ScheduledProgram × HashMap String DenseTensor × List String) :=
  [ ("A/selfRecur", ScanCompileTest.selfRecurSched, ScanCompileTest.selfRecurInputs, [])
  , ("B/coupled", ScanCompileTest.coupledSched, ScanCompileTest.coupledInputs, [])
  , ("C/scratch", ScanCompileTest.scratchSched, ScanCompileTest.scratchInputs, ["T"])
  , ("D-E/contract", ScanCompileTest.contractSched, ScanCompileTest.contractInputs, [])
  , ("F/deepHistory", ScanCompileTest.deepHistorySched, ScanCompileTest.deepHistoryInputs, [])
  , ("G/extentOne", ScanCompileTest.extentOneSched, ScanCompileTest.deepHistoryInputs, [])
  , ("H/axisPos", ScanCompileTest.axisPosSched, ScanCompileTest.axisPosInputs, [])
  , ("I-J/multiBase", ScanCompileTest.multiBaseSched, ScanCompileTest.multiBaseInputs, [])
  , ("K-L/twoScans", ScanCompileTest.twoScanSched, ScanCompileTest.twoScanInputs, [])
    -- Every fixture above is warning-free, which would leave point 7 vacuous across the whole
    -- matrix. `AdapterTest.scanWarnSched` reads two different externals past their extents from
    -- inside the recurrence, so it carries TWO `paddedAccess` warnings and the comparison
    -- discriminates order as well as payload. (`AdapterTest.lean` Check 15 pins that it really
    -- carries exactly two, so this reuse cannot go quietly vacuous either.)
  , ("M/scanWarnings", AdapterTest.scanWarnSched, AdapterTest.scanWarnInputs, []) ]

private def scanFixtureChecks : List (Except String Unit) :=
  scanFixtures.map (fun (nm, sched, inputs, scratch) => scanParityCheck nm sched inputs scratch)

run_cmd do
  for c in scanFixtureChecks do
    match c with
    | .ok () => pure ()
    | .error m => throwError s!"SCAN PARITY FAILED:\n{m}"

/-! ### Required feature coverage of the three-way gate

Plan Task 5: "keep exact corpus counts and ensure every required feature family has an accepted
fixture. Corpus count alone is not sufficient coverage." Each row below is derived STRUCTURALLY
from the gated schedules, never asserted by fixture name, so a fixture that quietly stopped
exhibiting its feature thins the gate loudly instead of silently. -/

private def scanNodesOf (s : ScheduledProgram) : List (List AxisSpec × List Stmt × List Stmt) :=
  s.stmts.filterMap (fun
    | .scan _ axes base recur _ => some (axes, base, recur)
    | _ => none)

/-- The axes a statement's reads mention that are neither on its LHS nor scan-context axes: the
    per-term contracted axes. -/
private def contractedAxes (axes : List AxisSpec) (s : Stmt) : List UID :=
  let lhs := s.slots.filterMap LHSSlot.axisUID?
  ((s.rhsReads.flatMap (fun e => (idxAffineForm e).2.map Prod.snd)).eraseDups).filter
    (fun u => !lhs.contains u && !axes.any (fun a => a.uid == u))

private def scanFeatures : List (String × (ScheduledProgram → Bool)) :=
  [ -- a state read biased strictly backwards: deep constant look-back, and the only shape that
    -- forces zero padding at the start of a history
    ("deep look-back and zero padding", fun s => (scanNodesOf s).any (fun (_, base, recur) =>
        let states := (base.map Stmt.lhsName).eraseDups
        recur.any (fun r => r.readFactors.any (fun (nm, es) =>
          states.contains nm && es.any (fun e => (idxAffineForm e).1 < 0)))))
  , ("coupled states", fun s => (scanNodesOf s).any (fun (_, base, _) =>
        ((base.map Stmt.lhsName).eraseDups).length ≥ 2))
  , ("block-local scratch", fun s => (scanNodesOf s).any (fun (_, base, recur) =>
        let states := (base.map Stmt.lhsName).eraseDups
        ((recur.map Stmt.lhsName).eraseDups).any (fun nm => !states.contains nm)))
  , ("external reads inside a recurrence", fun s => (scanNodesOf s).any (fun (_, base, recur) =>
        let produced := ((base ++ recur).map Stmt.lhsName).eraseDups
        recur.any (fun r => r.readFactors.any (fun (nm, _) => !produced.contains nm))))
  , ("contraction inside a recurrence", fun s => (scanNodesOf s).any (fun (axes, _, recur) =>
        recur.any (fun r => !(contractedAxes axes r).isEmpty)))
  , ("extent one", fun s => (scanNodesOf s).any (fun (axes, _, _) =>
        s.decls.any (fun d => match d with
          | .iter a 1 => axes.any (fun x => x.uid == a.uid)
          | _ => false)))
  , ("more than one scan axis", fun s => (scanNodesOf s).any (fun (axes, _, _) => axes.length ≥ 2))
  , ("several base writes for one state", fun s => (scanNodesOf s).any (fun (_, base, _) =>
        (base.map Stmt.lhsName).length != ((base.map Stmt.lhsName).eraseDups).length))
  , ("a non-trailing advancing dimension", fun s => (scanNodesOf s).any (fun (axes, _, recur) =>
        recur.any (fun r => (r.slots.zipIdx).any (fun (sl, i) => match sl with
          | .iterNext a => axes.any (fun x => x.uid == a.uid) && i + 1 != r.slots.length
          | _ => false))))
  , ("more than one scan in a schedule", fun s => (scanNodesOf s).length ≥ 2)
  , ("a plain statement consuming a published history", fun s =>
        !(scanNodesOf s).isEmpty && s.stmts.any (fun st => match st with
          | .plain _ => true
          | _ => false)) ]

run_cmd do
  for (feature, holds) in scanFeatures do
    unless scanFixtures.any (fun (_, sched, _, _) => holds sched) do
      throwError s!"THREE-WAY GATE COVERAGE GAP: no gated scan fixture exhibits \"{feature}\" \
any more — the corpus count alone does not keep this gate honest"

-- ── Alpha-renaming across the whole scan surface ──
-- `origAlphaProg`/`renamedAlphaProg` above rename a scan-FREE program's tensors. This pair renames
-- everything a scan node carries — the scan's representative name (`S` → `Sigma`), its persistent
-- state, its block-local scratch (`T` → `Tmp`), and both externals — while keeping every axis UID
-- and every input VALUE identical to `ScanCompileTest.scratchSched`. The checked semantic graph
-- must be literally the same value (names live only in `PlanBindings`), and the two runs must
-- produce the same tensors under the renaming.

private def alphaScanAxis : AxisSpec := ⟨"m", 21, .nat⟩   -- same UID as `ScanCompileTest.axM`

private def renamedScanSched : ScheduledProgram :=
  { decls := [.iter alphaScanAxis 3]
  , stmts := [.scan "Sigma" [alphaScanAxis]
      [ .assign "Sigma" [.iterAt alphaScanAxis 0]
          { body := { terms := [{ factors := [.read "Init" []] }] }, nonlin := .identity } ]
      [ .assign "Tmp" []
          { body := { terms := [{ factors :=
              [.read "Sigma" [.axis alphaScanAxis], .read "Kern" [.axis alphaScanAxis]] }] }
          , nonlin := .identity }
      , .assign "Sigma" [.iterNext alphaScanAxis]
          { body := { terms := [{ factors := [.read "Tmp" []] }] }, nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "Init" (insert "Kern" (∅ : Finset String))
  , explicitSizes := (({} : HashMap UID Nat).insert alphaScanAxis.uid 3) }

private def renamedScanInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "Init" ⟨[], #[1.0]⟩).insert
    "Kern" ⟨[3], #[2.0, 3.0, 4.0]⟩

run_cmd do
  match scanParityCheck "alpha/renamedScan" renamedScanSched renamedScanInputs ["Tmp"] with
  | .error m => throwError s!"alpha-renamed scan failed its own parity check:\n{m}"
  | .ok () => pure ()
  match prepareEvalPlan ScanCompileTest.scratchSched
          (InputSignature.ofDenseInputs ScanCompileTest.scratchInputs),
        prepareEvalPlan renamedScanSched (InputSignature.ofDenseInputs renamedScanInputs) with
  | .error _, _ => throwError "alpha: the original scan fixture failed to prepare"
  | _, .error _ => throwError "alpha: the renamed scan fixture failed to prepare"
  | .ok p1, .ok p2 =>
      unless p1.plan.raw == p2.plan.raw do
        throwError s!"alpha-renaming CHANGED a scan's checked semantic graph:\n\
{repr p1.plan.raw}\nvs\n{repr p2.plan.raw}"
      unless p1.bindings.requiredInputs.bindings != p2.bindings.requiredInputs.bindings &&
             p1.bindings.materializedNames != p2.bindings.materializedNames do
        throwError "alpha: renaming did NOT change the scan's bindings — they should be name-keyed"
      -- the renaming is a bijection on the boundary: same slots, renamed names.
      unless p1.bindings.requiredInputs.bindings.map (·.slot) ==
             p2.bindings.requiredInputs.bindings.map (·.slot) &&
             p1.bindings.materializedNames.map (·.slot) ==
             p2.bindings.materializedNames.map (·.slot) do
        throwError "alpha: renaming moved a scan's boundary SLOTS, not just its names"
      -- and the two runs agree tensor-for-tensor under the renaming.
      match runPreparedDense p1 ScanCompileTest.scratchInputs,
            runPreparedDense p2 renamedScanInputs with
      | .ok r1, .ok r2 =>
          match r1.env["S"]?, r2.env["Sigma"]? with
          | some a, some b =>
              unless denseEq a b do
                throwError s!"alpha: renamed state differs: {repr a.data} vs {repr b.data}"
          | _, _ => throwError "alpha: a renamed state is missing from its unpacked env"
      | _, _ => throwError "alpha: one of the two renamed runs failed"

-- ── Two axes sharing a NAME but not a UID ──
-- Axis identity is by UID everywhere in this codebase; a scan makes that load-bearing twice over
-- (context membership and causality are both UID-keyed). This fixture scans over an axis literally
-- named "l" while a DIFFERENT axis also named "l" is a free output dimension of the same state, so
-- any name-based axis comparison would either treat the free axis as a context axis (and reject the
-- program) or mis-place `advancingDims`. Cross-checked against `evalScheduled`, which resolves
-- axes by UID too.

private def sameNameIter : AxisSpec := ⟨"l", 3101, .nat⟩
private def sameNameFree : AxisSpec := ⟨"l", 3102, .nat⟩

private def sameAxisNameSched : ScheduledProgram :=
  { decls := [.iter sameNameIter 3, .axis sameNameFree (some 2)]
  , stmts := [.scan "S" [sameNameIter]
      [ .assign "S" [.free sameNameFree, .iterAt sameNameIter 0]
          { body := { terms := [{ factors := [.read "S0" [.axis sameNameFree]] }] }
          , nonlin := .identity } ]
      [ .assign "S" [.free sameNameFree, .iterNext sameNameIter]
          { body := { terms :=
              [ { factors := [.read "S" [.axis sameNameFree, .axis sameNameIter]] }
              , { factors := [.read "W" [.axis sameNameFree]] } ] }
          , nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "S0" (insert "W" (∅ : Finset String))
  , explicitSizes :=
      ((({} : HashMap UID Nat).insert sameNameIter.uid 3).insert sameNameFree.uid 2) }

private def sameAxisNameInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "S0" ⟨[2], #[1.0, 2.0]⟩).insert
    "W" ⟨[2], #[10.0, 20.0]⟩

run_cmd do
  match scanParityCheck "sameAxisName" sameAxisNameSched sameAxisNameInputs [] with
  | .error m => throwError s!"same-axis-name scan case: {m}"
  | .ok () => pure ()
  match prepareEvalPlan sameAxisNameSched (InputSignature.ofDenseInputs sameAxisNameInputs) with
  | .error _ => throwError "sameAxisName: prepare failed (already reported above)"
  | .ok p =>
      match (p.plan.raw.steps[0]? : Option PlanStep) with
      | some (.scan s) =>
          -- the UID-distinct free axis is dimension 0 and is NOT advancing; only the iter axis is.
          unless s.states.map (·.advancingDims) == #[#[1]] do
            throwError s!"sameAxisName: advancingDims resolved by NAME, not UID: \
{repr (s.states.map (·.advancingDims))}"
          unless s.historyExtents == #[3] do
            throwError s!"sameAxisName: the free same-named axis leaked into the context: \
{repr s.historyExtents}"
      | _ => throwError "sameAxisName: step 0 is not a scan"

-- ── The generated-corpus gate ──
-- `enumScanCases` (`test/Eval/PropertyOracle/ScanGen.lean`) is a curated six-template family:
-- template 2 (×4) applies `.pointwise .relu` inside the recurrence and template 5 (×4) uses
-- `.max`/`.min` aggregation — both outside F4's admitted fragment — while the remaining nine are
-- admitted. The split below is pinned by exact count AND by which capability constructor each
-- rejection produces, so a regression that widened or narrowed the fragment cannot be absorbed by
-- the accepted cases silently getting fewer.

private inductive ScanCaseOutcome
  | accepted
  | rejectedNonlin
  | rejectedAgg

/-- One generated case. A rejected case is rejected at COMPILE time, so no `PreparedPlan` exists and
    `runDensePlan` is unreachable for it by construction — the `.ok` arm below is the only path that
    can reach execution at all, and it is the arm that demands full parity. -/
private def checkScanCase (i : Nat) (c : LeanNCD.PropertyOracle.ScanCase) :
    Except String ScanCaseOutcome := do
  let sched ← match c.prog.compileToScheduled.run 0 with
    | .ok s _ => pure s
    | .error e _ => throw s!"scan case {i}: the generator produced a program that fails to \
compile: {repr e}"
  match prepareEvalPlan sched (InputSignature.ofDenseInputs c.inputs) with
  | .error f =>
      match f.cause with
      | .capability (.unsupportedNonlin _) => pure .rejectedNonlin
      | .capability (.unsupportedAgg _) => pure .rejectedAgg
      | cause =>
          throw s!"scan case {i}: rejected for an unexpected reason: {ScanCompileTest.render cause}"
  | .ok _ =>
      -- No template in `ScanGen.lean` writes a recurrence-only name, so every generated case has an
      -- empty scratch set; asserting `[]` (rather than deriving it) keeps point 6 honest here too.
      match scanParityCheck s!"scan case {i}" sched c.inputs [] with
      | .ok () => pure .accepted
      | .error m => throw m

/-- (total, accepted, `unsupportedNonlin`, `unsupportedAgg`) over the whole curated corpus.
    `foldlM` short-circuits: the first parity disagreement or unexpected rejection aborts. -/
private def scanCorpusSplit : Except String (Nat × Nat × Nat × Nat) :=
  (LeanNCD.PropertyOracle.enumScanCases.zipIdx).foldlM
    (fun (acc : Nat × Nat × Nat × Nat) (ci : LeanNCD.PropertyOracle.ScanCase × Nat) => do
      let (total, accepted, nonlin, agg) := acc
      match ← checkScanCase ci.2 ci.1 with
      | .accepted => pure (total + 1, accepted + 1, nonlin, agg)
      | .rejectedNonlin => pure (total + 1, accepted, nonlin + 1, agg)
      | .rejectedAgg => pure (total + 1, accepted, nonlin, agg + 1))
    (0, 0, 0, 0)

-- The counts pinned by F4's plan §0, independently re-derived from `ScanGen.lean`'s six templates:
-- 4×template1 + 4×template2 + 2×template3 + 2×template4 + 4×template5 + 1×template6 = 17, of which
-- template 5's four are `unsupportedAgg`, leaving 13 admitted. Thread 4 Task 4 admitted nonlinear
-- scan sources, so template 2's four ReLU-scan cases moved from `unsupportedNonlin` to `accepted`
-- (9→13; nonlin 4→0). The sweep short-circuits on the first parity disagreement, so `accepted=13`
-- also asserts those four now match `evalScheduled` byte-for-byte. Per the plan's stop condition, an
-- accepted case that stops compiling — or stops matching `evalScheduled` — is a contract defect to
-- REPORT, not a number to re-baseline here.
run_cmd do
  match scanCorpusSplit with
  | .error msg => throwError s!"SCAN CORPUS GATE FAILED:\n{msg}"
  | .ok (total, accepted, nonlin, agg) =>
      dbg_trace s!"DifferentialTest scan corpus: total={total} accepted={accepted} \
unsupportedNonlin={nonlin} unsupportedAgg={agg}"
      unless total == 17 && accepted == 13 && nonlin == 0 && agg == 4 do
        throwError s!"scan corpus split counts changed: total={total} accepted={accepted} \
nonlin={nonlin} agg={agg}"

/-! ## Thread 4 (nonlinearity) Task 5 — top-level nonlin differential fixtures

`NonlinCompileTest.lean`'s Section 2 confirms the compiled Dense path produces the right tensor for
one real top-level program per nonlin function (`relu`, `sigmoid`, `tanh`, `gelu`, `leakyrelu`,
`normalize`, `softmax`, `l2normalize`), but only against a hand-computed literal — it never runs the
same program through the independent legacy evaluator (`evalScheduled`). This section reuses those
exact eight donor programs/tensors/expected-values VERBATIM (no re-derivation) and adds the missing
leg: `planAgrees` (already defined above) supplies the `checkEntry`-style differential comparison —
`envEq`/warnings equality, exact (`denseEq`), between `runPreparedDense` and `evalScheduled` — while
the sanity check below against Task 3's own literal stays a tolerant `DenseTensor.approxEq`, exactly
Task 3's own convention. The exact `envEq` leg is what actually proves bit-for-bit legacy agreement;
the literal sanity check merely confirms this section is still looking at the fixture Task 3 named. -/

/-- Local tensor-literal helper, mirroring `NonlinCompileTest.lean`'s own `tl` (not imported from
    there — this file avoids importing the sibling test file, following its own self-contained
    convention). -/
private def tl (shape : List Nat) (xs : List Float) : DenseTensor := ⟨shape, xs.toArray⟩

private def nonlinFixtures :
    List (String × TLProgram × HashMap String DenseTensor × String × DenseTensor) :=
  [ ("relu", tlprog!{ H[i] := relu(W[i, j] · x[j]) },
      HashMap.ofList [("W", tl [2,2] [1,-1,-2,1]), ("x", tl [2] [1,1])],
      "H", tl [2] [0,0])
  , ("sigmoid", tlprog!{ H[i] := sigmoid(W[i, j] · x[j]) },
      HashMap.ofList [("W", tl [2,2] [1,0,0,1]), ("x", tl [2] [-2,2])],
      "H", tl [2] [0.11920292202211755, 0.8807970779778823])
  , ("tanh", tlprog!{ H[i] := tanh(W[i, j] · x[j]) },
      HashMap.ofList [("W", tl [2,2] [1,0,0,1]), ("x", tl [2] [-2,2])],
      "H", tl [2] [-0.9640275800758169, 0.9640275800758169])
  , ("gelu", tlprog!{ H[i] := gelu(W[i, j] · x[j]) },
      HashMap.ofList [("W", tl [2,2] [1,0,0,1]), ("x", tl [2] [-2,2])],
      "H", tl [2] [-0.045402305912, 1.954597694088])
  , ("leakyrelu", tlprog!{ H[i] := leakyrelu(W[i, j] · x[j]) },
      HashMap.ofList [("W", tl [2,2] [1,0,0,1]), ("x", tl [2] [-2,2])],
      "H", tl [2] [-0.02, 2])
  , ("normalize", tlprog!{ Y[q, s.] := normalize(A[q, s]) },
      HashMap.ofList [("A", tl [2,2] [1,3,2,2])],
      "Y", tl [2,2] [0.25,0.75,0.5,0.5])
  , ("softmax", tlprog!{ Y[q, s.] := softmax(A[q, s]) },
      HashMap.ofList [("A", tl [2,2] [0, 0, 0, Float.log 3])],
      "Y", tl [2,2] [0.5,0.5,0.25,0.75])
  , ("l2normalize", tlprog!{
        Z1n[i, d.] := l2normalize(Z1[i, d])
        Z2n[j, d.] := l2normalize(Z2[j, d])
        S[i, j] := Z1n[i, d] · Z2n[j, d]
      },
      HashMap.ofList [("Z1", tl [1,2] [3,4]), ("Z2", tl [1,2] [1,0])],
      "S", tl [1,1] [0.6]) ]

/-- One donor fixture's full check: (1) the differential leg — `planAgrees` runs the identical
    program/inputs through both `prepareEvalPlan`+`runPreparedDense` and `evalScheduled` and demands
    exact (`envEq`) agreement, precisely `checkEntry`'s own contract; (2) a sanity cross-check that
    the plan's own named output still matches Task 3's literal expected value, so this section
    cannot silently drift onto a different computation than the one Task 3 named. -/
private def checkNonlinFixture (name : String) (p : TLProgram) (inputs : HashMap String DenseTensor)
    (key : String) (expected : DenseTensor) : Except String Unit := do
  match planAgrees p inputs with
  | .error e => throw s!"{name}: differential leg failed: {e}"
  | .ok () => pure ()
  let sched ← match p.compileToScheduled.run 0 with
    | .ok s _ => pure s
    | .error e _ => throw s!"{name}: compile failed: {repr e}"
  let prepared ← match prepareEvalPlan sched (InputSignature.ofDenseInputs inputs) with
    | .ok pp => pure pp
    | .error _ => throw s!"{name}: prepareEvalPlan failed (already accepted by the differential leg)"
  let planReport ← match runPreparedDense prepared inputs with
    | .ok r => pure r
    | .error e => throw s!"{name}: runPreparedDense failed (warnings={e.warnings.length})"
  match planReport.env[key]? with
  | none => throw s!"{name}: {key} missing from the compiled plan's output"
  | some t =>
      unless DenseTensor.approxEq t expected do
        throw s!"{name}: compiled plan's {key} disagrees with Task 3's expected value: \
got {repr t.data}, expected {repr expected.data}"

run_cmd do
  for (name, p, inputs, key, expected) in nonlinFixtures do
    match checkNonlinFixture name p inputs key expected with
    | .ok () => pure ()
    | .error m => throwError s!"THREAD 4 TASK 5 NONLIN DIFFERENTIAL FAILED:\n{m}"

end LeanNCD.Eval.Plan.DifferentialTest

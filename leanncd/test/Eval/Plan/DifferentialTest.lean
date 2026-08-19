import LeanNCD.Eval.Plan.Adapter
import LeanNCD.Eval.Entry
import Eval.PropertyOracle.Gen
import Eval.PropertyOracle.Compare

/-!
# Wave C C4 — differential testing against the legacy evaluator

The empirical core of C4: `prepareEvalPlan`/`runPreparedDense` against `evalScheduled`, over every
`PropertyOracle.enumPrograms` entry, plus an alpha-renaming law and test-the-tester mutations.
Capability-row accept/reject coverage, deterministic-slot/term-basis fixtures, zero-coefficient
contraction, repeated-assignment, `requiredInputs`-order independence, and packing/unpacking edge
cases are already covered by `CompileTest.lean` and `AdapterTest.lean` — this file does not
re-derive them.
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

end LeanNCD.Eval.Plan.DifferentialTest

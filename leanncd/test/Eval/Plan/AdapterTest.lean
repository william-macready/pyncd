import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter

/-!
# Wave C runtime-adaptation tests (C4)

Hand-built fixtures only — the `PropertyOracle.enumPrograms` differential matrix is Task 4, not
this task. Covers the full `pack`/`unpack`/`runPreparedDense` round trip cross-checked against the
legacy evaluator, every `InputBindingError` constructor, and warning preservation on success and on
a later binding failure.
-/

namespace LeanNCD.Eval.Plan.AdapterTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

private def expectTensor (t : Option DenseTensor) (shape : List Nat) (data : Array Float) : Bool :=
  t.map (fun d => d.shape == shape && d.data == data) |>.getD false

-- Example 1: contraction, reused from Task 2's own worked example (`Y[i] := A[i]·B[j]`
-- contracted over `j`). Baseline verified against the real evaluator: A=[10,100], B=[1,2,3],
-- ΣB=6 ⇒ Y = A·6 = [60, 600].
private def zeroCoeffProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  Y[i] := A[i] · B[j]
}

private def zeroCoeffInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" ⟨[2], #[10.0, 100.0]⟩).insert
    "B" ⟨[3], #[1.0, 2.0, 3.0]⟩

private def undersizedDataInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" ⟨[2], #[10.0]⟩).insert
    "B" ⟨[3], #[1.0, 2.0, 3.0]⟩

-- Example 2: two same-shape, different-value inputs playing ASYMMETRIC roles (`A` retained on the
-- output axis `i`, `B` contracted over `j`) — `+`/`·` over identically-indexed same-shape reads
-- would be commutative and so would NOT actually discriminate a positional slot-swap bug from a
-- correct by-name resolution (confirmed by mutation testing below: an `A[i]+B[i]` version of this
-- fixture did NOT fail under a deliberately-broken positional `pack`, because addition is
-- commutative). Contraction breaks the symmetry: swapping which VALUES are bound to slots 0/1
-- changes the result to `B[i]·ΣA` instead of `A[i]·ΣB`, which differ whenever `A ≠ B` — real
-- teeth. Baseline verified against the real evaluator: A=[10,100], B=[1,2], ΣB=3 ⇒ W = A·3 =
-- [30, 300] (the swapped-slot alternative would be B·ΣA = B·110 = [110, 220] — confirmed
-- different, by hand-substitution of the same verified arithmetic).
private def swapProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  W[i] := A[i] · B[j]
}

private def swapInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" ⟨[2], #[10.0, 100.0]⟩).insert "B" ⟨[2], #[1.0, 2.0]⟩

-- Example 3: an undersized read (`X` shape [6], reads up to index 8) — triggers a real
-- `paddedAccess` `EvalWarning`, so the "warnings preserved through pack/run" checks below have a
-- genuinely non-empty list to preserve, not a vacuously-passing empty one.
private def warnProg : TLProgram := tlprog!{
  axis i : ℕ = 4
  axis j : ℕ = 3
  Y[i, j] := X[2 * i + j]
}

private def warnInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[6], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]⟩

/-- Manual renderer for `PlanCompileCause` (used only for test-failure messages): the type
    deliberately has no `Repr`/`ToString` (`ShapeError` — nested via `.shape` — has neither), so a
    diagnosable message has to dispatch per-constructor to whichever rendering each nested cause
    DOES support (`Repr` for `CapabilityError`/`InputSignatureError`/`PlanError`, `ToString` for
    `ShapeError`). -/
private def renderCompileCause : PlanCompileCause → String
  | .inputSignature c => s!"inputSignature: {repr c}"
  | .capability c     => s!"capability: {repr c}"
  | .shape c          => s!"shape: {c}"
  | .invalidPlan c     => s!"invalidPlan: {repr c}"

-- ── Checks 1–4: full adapter round-trip (cross-checked against the legacy evaluator), an unpack
-- preserving an unrelated extra input, a missing-env-binding failure, and a shape-mismatch
-- failure — all against the `zeroCoeffProg` contraction example. ──

run_cmd do
  match zeroCoeffProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"zeroCoeff compile failed: {repr e}"
  | .ok sched _ =>
    match prepareEvalPlan sched (InputSignature.ofDenseInputs zeroCoeffInputs) with
    | .error f => throwError s!"zeroCoeff prepare failed: {renderCompileCause f.cause}"
    | .ok prepared =>
      -- Check 1: round-trip, cross-checked against the legacy evaluator.
      match runPreparedDense prepared zeroCoeffInputs with
      | .error e => throwError s!"round-trip run failed: {repr e.cause}"
      | .ok report =>
          unless expectTensor report.env["Y"]? [2] #[60.0, 600.0] do
            throwError s!"round-trip Y mismatch: {repr (report.env["Y"]?)}"
          match TLProgram.eval zeroCoeffProg zeroCoeffInputs with
          | .error e2 => throwError s!"legacy evaluator failed: {e2}"
          | .ok legacy =>
              unless expectTensor legacy.env["Y"]? [2] #[60.0, 600.0] do
                throwError "legacy evaluator itself diverged from the verified baseline"
          unless expectTensor report.env["A"]? [2] #[10.0, 100.0] do
            throwError s!"round-trip did not preserve input A: {repr (report.env["A"]?)}"
          unless expectTensor report.env["B"]? [3] #[1.0, 2.0, 3.0] do
            throwError s!"round-trip did not preserve input B: {repr (report.env["B"]?)}"
      -- Check 2: unpack preserves an unrelated extra input the plan never reads.
      match runPreparedDense prepared (zeroCoeffInputs.insert "Unused" ⟨[1], #[42.0]⟩) with
      | .error e => throwError s!"extra-input run failed: {repr e.cause}"
      | .ok report2 =>
          unless expectTensor report2.env["Unused"]? [1] #[42.0] do
            throwError s!"extra unused input was not preserved: {repr (report2.env["Unused"]?)}"
          unless expectTensor report2.env["Y"]? [2] #[60.0, 600.0] do
            throwError s!"extra input incorrectly affected Y: {repr (report2.env["Y"]?)}"
      -- Check 3: `pack` fails loudly when `env` is missing a required name.
      match pack prepared (({} : HashMap String DenseTensor).insert "A" ⟨[2], #[10.0, 100.0]⟩) with
      | .ok _ => throwError "expected pack to fail on a missing required binding"
      | .error (.missingEnvBinding nm) =>
          unless nm == "B" do throwError s!"wrong missing name reported: {nm}"
      | .error e => throwError s!"wrong error kind for a missing env entry: {repr e}"
      -- Check 4: `pack` fails loudly on a shape mismatch against the prepared signature.
      match pack prepared
          ((({} : HashMap String DenseTensor).insert "A" ⟨[3], #[1.0, 2.0, 3.0]⟩).insert
            "B" ⟨[3], #[1.0, 2.0, 3.0]⟩) with
      | .ok _ => throwError "expected pack to fail on a shape mismatch"
      | .error (.shapeMismatch nm _ expected actual) =>
          unless nm == "A" && expected == #[2] && actual == [3] do
            throwError s!"wrong shapeMismatch payload: name={nm} expected={repr expected} actual={repr actual}"
      | .error e => throwError s!"wrong error kind for a shape mismatch: {repr e}"
      -- Check 10: `pack` fails loudly when a required input's declared shape matches but its
      -- data array is undersized. Distinct from Check 4 (`shapeMismatch`): here `.shape` itself
      -- agrees with the signature, but `.data.size` doesn't match the shape's element product.
      match pack prepared undersizedDataInputs with
      | .ok _ => throwError "expected pack to fail on a storage mismatch"
      | .error (.storageMismatch nm slot shape dataSize) =>
          unless nm == "A" && slot == 0 && shape == [2] && dataSize == 1 do
            throwError s!"wrong storageMismatch payload: name={nm} slot={slot} shape={repr shape} dataSize={dataSize}"
      | .error e => throwError s!"wrong error kind for a storage mismatch: {repr e}"

-- ── Checks 5–8: reordering `requiredInputs`, a genuine duplicate slot binding, an extra binding
-- naming a slot the plan doesn't need, and a structurally-missing required binding — all against
-- the `swapProg` example (two same-shape, different-value inputs in asymmetric roles). ──

run_cmd do
  match swapProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"swap compile failed: {repr e}"
  | .ok sched _ =>
    match prepareEvalPlan sched (InputSignature.ofDenseInputs swapInputs) with
    | .error f => throwError s!"swap prepare failed: {renderCompileCause f.cause}"
    | .ok prepared =>
      unless prepared.bindings.requiredInputs.size == 2 do
        throwError s!"expected exactly two required inputs, got {prepared.bindings.requiredInputs.size}"
      -- Check 5: reordering `requiredInputs` does not change which value lands in which slot.
      -- MUTATION-VERIFIED: a deliberately-broken `pack`, patched to resolve `requiredInputs[i]` by
      -- ARRAY POSITION `i` against `raw.inputSlots[i]` instead of by each binding's own `.slot`
      -- field, was run against this whole file. It passed every OTHER check here unchanged, but
      -- failed EXACTLY this one — producing W = [110.0, 220.0] (the swapped-slot value predicted
      -- above) instead of the correct [30.0, 300.0]. Restored before this fixture shipped. (An
      -- earlier `A[i]+B[i]` version of this fixture did NOT catch the same broken `pack`, because
      -- addition is commutative — that's why `swapProg` uses contraction instead.)
      let reordered : PreparedPlan :=
        { prepared with
            bindings := { prepared.bindings with
                            requiredInputs := prepared.bindings.requiredInputs.reverse } }
      unless prepared.bindings.requiredInputs != reordered.bindings.requiredInputs do
        throwError "reversal of a two-element array should differ from the original — fixture is broken"
      match runPreparedDense reordered swapInputs with
      | .error e => throwError s!"reordered-bindings run failed: {repr e.cause}"
      | .ok report =>
          unless expectTensor report.env["W"]? [2] #[30.0, 300.0] do
            throwError s!"reordered requiredInputs produced a wrong slotting: {repr (report.env["W"]?)}"
      -- Check 6: a genuine duplicate slot binding fails loudly.
      let dup : PreparedPlan :=
        { prepared with
            bindings := { prepared.bindings with
                            requiredInputs := prepared.bindings.requiredInputs.push { name := "A2", slot := 0 } } }
      match pack dup swapInputs with
      | .ok _ => throwError "expected pack to fail on a duplicate slot binding"
      | .error (.duplicateRequiredBinding slot first second) =>
          unless slot == 0 && first == "A" && second == "A2" do
            throwError s!"wrong duplicateRequiredBinding payload: slot={slot} first={first} second={second}"
      | .error e => throwError s!"wrong error kind for a duplicate binding: {repr e}"
      -- Check 7: an extra binding naming a slot the plan doesn't need fails loudly.
      let wSlot := (prepared.bindings.materializedNames[0]!).slot
      let extra : PreparedPlan :=
        { prepared with
            bindings := { prepared.bindings with
                            requiredInputs := prepared.bindings.requiredInputs.push { name := "W", slot := wSlot } } }
      match pack extra swapInputs with
      | .ok _ => throwError "expected pack to fail on an extra (not-needed) slot binding"
      | .error (.extraRequiredBinding slot nm) =>
          unless slot == wSlot && nm == "W" do
            throwError s!"wrong extraRequiredBinding payload: slot={slot} name={nm}"
      | .error e => throwError s!"wrong error kind for an extra binding: {repr e}"
      -- Check 8: a missing required-input slot (structurally absent), distinct from a name
      -- absent from `env` (Check 3).
      let missingStructural : PreparedPlan :=
        { prepared with
            bindings := { prepared.bindings with
                            requiredInputs := #[prepared.bindings.requiredInputs[0]!] } }
      match pack missingStructural swapInputs with
      | .ok _ => throwError "expected pack to fail on a structurally-missing required binding"
      | .error (.missingRequiredBinding slot) =>
          unless slot == 1 do throwError s!"wrong missingRequiredBinding slot: {slot}"
      | .error e => throwError s!"wrong error kind for a structurally-missing binding: {repr e}"

-- ── Check 9: preparation warnings survive both a successful run and a later binding failure ──
-- (real teeth: `warnProg` genuinely produces a non-empty warning list, verified against the
-- legacy evaluator producing the SAME warning on the SAME inputs, not an empty list that would
-- pass this check vacuously.)

run_cmd do
  match warnProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"warn compile failed: {repr e}"
  | .ok sched _ =>
    match prepareEvalPlan sched (InputSignature.ofDenseInputs warnInputs) with
    | .error f => throwError s!"warn prepare failed: {renderCompileCause f.cause}"
    | .ok prepared =>
      if prepared.warnings.isEmpty then
        throwError "fixture is broken: expected prepareEvalPlan to record a non-empty warning list"
      else pure ()
      match TLProgram.eval warnProg warnInputs with
      | .error e => throwError s!"legacy evaluator failed unexpectedly: {e}"
      | .ok legacyReport =>
          unless legacyReport.warnings == prepared.warnings do
            throwError s!"prepared warnings diverge from the legacy evaluator's: \
{prepared.warnings} vs {legacyReport.warnings}"
      -- success path: warnings preserved into the successful `EvalReport`.
      match runPreparedDense prepared warnInputs with
      | .error e => throwError s!"warn-fixture run unexpectedly failed: {repr e.cause}"
      | .ok report =>
          unless report.warnings == prepared.warnings do
            throwError s!"success-path warnings dropped/changed: {report.warnings}"
      -- failure path: warnings still preserved when `pack` itself fails.
      match runPreparedDense prepared (({} : HashMap String DenseTensor)) with
      | .ok _ => throwError "expected a binding failure against an empty env"
      | .error failure =>
          unless failure.warnings == prepared.warnings do
            throwError s!"binding-failure warnings dropped/changed: {failure.warnings}"
          match failure.cause with
          | .binding (.missingEnvBinding nm) => unless nm == "X" do throwError s!"wrong missing name: {nm}"
          | c => throwError s!"expected a binding failure, got: {repr c}"

-- PlanRunCause.execution: unreachable through the full runPreparedDense pipeline — pack's own
-- validation (Adapter.lean) and runDenseAssign's self-consistent output construction (Dense.lean)
-- together rule out every PositionalInputError constructor once pack has already succeeded.
-- Named directly instead, same pattern as PlanError.numericModeNotAdmitted (C3).
#guard (PlanRunCause.execution (.arityMismatch 2 3)) == PlanRunCause.execution (.arityMismatch 2 3)

end LeanNCD.Eval.Plan.AdapterTest

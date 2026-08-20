import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter
import Eval.Plan.ScanCompileTest

/-!
# Wave C runtime-adaptation tests (C4)

Hand-built fixtures only — the `PropertyOracle.enumPrograms` differential matrix is Task 4, not
this task. Covers the full `pack`/`unpack`/`runPreparedDense` round trip cross-checked against the
legacy evaluator, every `InputBindingError` constructor, every `BindingsError` constructor at the
`checkBindings` construction boundary (Task 3), and warning preservation on success and on a later
binding failure.

Wave F F4 Task 4 adds the SCAN half of the same boundary at the end of the file (Checks 11–16):
the adapter is generic over `PreparedPlan`, so a compiled scan step needs no adapter code of its
own — these fixtures are what turns that claim from a design assertion into a tested one. Legacy
parity for scans lives in `DifferentialTest.lean`; this file covers the boundary FAILURES (a missing
input at a scan capture, shape and storage mismatches there) and warning preservation.
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
  | .scan c            => s!"scan: {repr c}"
  | .invalidPlan c     => s!"invalidPlan: {repr c}"
  | .bindings c        => s!"bindings: {repr c}"

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
      -- Check 4b: `pack` fails loudly when a required input's declared shape matches but its
      -- data array is undersized. Distinct from Check 4 (`shapeMismatch`): here `.shape` itself
      -- agrees with the signature, but `.data.size` doesn't match the shape's element product.
      match pack prepared undersizedDataInputs with
      | .ok _ => throwError "expected pack to fail on a storage mismatch"
      | .error (.storageMismatch nm slot shape dataSize) =>
          unless nm == "A" && slot == 0 && shape == [2] && dataSize == 1 do
            throwError s!"wrong storageMismatch payload: name={nm} slot={slot} shape={repr shape} dataSize={dataSize}"
      | .error e => throwError s!"wrong error kind for a storage mismatch: {repr e}"

-- ── Checks 5–9: reordering `requiredInputs` (Check 5, kept exactly as designed — proves the
-- `Perm` choice over positional equality), and `checkBindings`-boundary rejections for a genuine
-- duplicate slot binding, an extra binding naming a slot the plan doesn't need, a
-- structurally-missing required binding, and a duplicated source name across two different slots
-- (Checks 6–9) — all against the `swapProg` example (two same-shape, different-value inputs in
-- asymmetric roles). `RequiredBindings`' private constructor means Checks 6–9 can no longer be
-- expressed via `{ prepared.bindings with requiredInputs := ... }` struct-update on a malformed
-- array (that malformed state is now unconstructable outside `Prepared.lean`) — they instead call
-- `checkBindings` directly with a raw, malformed `Array SlotBinding`, confirming the typed
-- rejection fires with the right `BindingsError` constructor and payload. ──

run_cmd do
  match swapProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"swap compile failed: {repr e}"
  | .ok sched _ =>
    match prepareEvalPlan sched (InputSignature.ofDenseInputs swapInputs) with
    | .error f => throwError s!"swap prepare failed: {renderCompileCause f.cause}"
    | .ok prepared =>
      let rb := prepared.bindings.requiredInputs
      unless rb.bindings.size == 2 do
        throwError s!"expected exactly two required inputs, got {rb.bindings.size}"
      -- Check 5: reordering `requiredInputs` does not change which value lands in which slot.
      -- MUTATION-VERIFIED: a deliberately-broken `pack`, patched to resolve `requiredInputs[i]` by
      -- ARRAY POSITION `i` against `raw.inputSlots[i]` instead of by each binding's own `.slot`
      -- field, was run against this whole file. It passed every OTHER check here unchanged, but
      -- failed EXACTLY this one — producing W = [110.0, 220.0] (the swapped-slot value predicted
      -- above) instead of the correct [30.0, 300.0]. Restored before this fixture shipped. (An
      -- earlier `A[i]+B[i]` version of this fixture did NOT catch the same broken `pack`, because
      -- addition is commutative — that's why `swapProg` uses contraction instead.) The reversed
      -- array is obtained via `checkBindings` itself (the only public way to build a
      -- `RequiredBindings`), not via struct-update — reversal stays a legal `Perm` of `inputSlots`.
      match checkBindings rb.inputSlots rb.bindings.reverse with
      | .error e => throwError s!"expected reversed bindings to still check out: {repr e}"
      | .ok reorderedRB =>
          unless rb.bindings != reorderedRB.bindings do
            throwError "reversal of a two-element array should differ from the original — fixture is broken"
          let reordered : PreparedPlan :=
            { prepared with bindings := { prepared.bindings with requiredInputs := reorderedRB } }
          match runPreparedDense reordered swapInputs with
          | .error e => throwError s!"reordered-bindings run failed: {repr e.cause}"
          | .ok report =>
              unless expectTensor report.env["W"]? [2] #[30.0, 300.0] do
                throwError s!"reordered requiredInputs produced a wrong slotting: {repr (report.env["W"]?)}"
      -- Sanity check on the well-formed fixture the four malformed variants below are derived
      -- from — confirms it still succeeds (Checks 6–9 mutate exactly one aspect of it each).
      match checkBindings rb.inputSlots rb.bindings with
      | .error e => throwError s!"expected well-formed bindings to succeed: {repr e}"
      | .ok _ => pure ()
      let slotA := (rb.bindings[0]!).slot
      let slotB := (rb.bindings[1]!).slot
      -- Check 6: a genuine duplicate slot binding (two entries naming the same slot, so the other
      -- required slot goes unbound) breaks the slot permutation — rejected as `.notAPermutation`.
      let dupSlotBindings : Array SlotBinding :=
        #[{ name := "A", slot := slotA }, { name := "A2", slot := slotA }]
      match checkBindings rb.inputSlots dupSlotBindings with
      | .ok rb2 => throwError s!"expected a duplicate slot binding to be rejected, got {repr rb2}"
      | .error (.notAPermutation expected observed) =>
          unless expected == rb.inputSlots && observed == dupSlotBindings.map (·.slot) do
            throwError
              s!"wrong notAPermutation payload for a duplicate slot: expected={repr expected} observed={repr observed}"
      | .error e => throwError s!"wrong error kind for a duplicate slot binding: {repr e}"
      -- Check 7: an extra binding naming a slot the plan doesn't need also breaks the slot
      -- permutation (the observed multiset no longer matches `inputSlots`) — `.notAPermutation`.
      let wSlot := (prepared.bindings.materializedNames[0]!).slot
      let extraBindings : Array SlotBinding := rb.bindings.push { name := "W", slot := wSlot }
      match checkBindings rb.inputSlots extraBindings with
      | .ok rb2 => throwError s!"expected an extra slot binding to be rejected, got {repr rb2}"
      | .error (.notAPermutation expected observed) =>
          unless expected == rb.inputSlots && observed == extraBindings.map (·.slot) do
            throwError
              s!"wrong notAPermutation payload for an extra binding: expected={repr expected} observed={repr observed}"
      | .error e => throwError s!"wrong error kind for an extra binding: {repr e}"
      -- Check 8: a structurally-missing required binding (fewer bindings than input slots),
      -- distinct from a name absent from `env` (Check 3) — also `.notAPermutation`.
      let missingBindings : Array SlotBinding := #[rb.bindings[0]!]
      match checkBindings rb.inputSlots missingBindings with
      | .ok rb2 => throwError s!"expected a missing binding to be rejected, got {repr rb2}"
      | .error (.notAPermutation expected observed) =>
          unless expected == rb.inputSlots && observed == missingBindings.map (·.slot) do
            throwError
              s!"wrong notAPermutation payload for a missing binding: expected={repr expected} observed={repr observed}"
      | .error e => throwError s!"wrong error kind for a missing binding: {repr e}"
      -- Check 9: a duplicate NAME across two different slots is a genuinely separate
      -- malformation from Checks 6–8 — the slot permutation is perfectly fine (both `slotA` and
      -- `slotB` appear exactly once), but the same source name is bound to two different slots.
      -- Not covered by the old `pack`-level duplicate check at all: that one only ever caught the
      -- same SLOT bound to two names, never the same NAME bound to two slots.
      let dupNameBindings : Array SlotBinding :=
        #[{ name := "A", slot := slotA }, { name := "A", slot := slotB }]
      match checkBindings rb.inputSlots dupNameBindings with
      | .ok rb2 => throwError s!"expected a duplicate name binding to be rejected, got {repr rb2}"
      | .error (.duplicateName nm) => unless nm == "A" do throwError s!"wrong duplicateName payload: {nm}"
      | .error e => throwError s!"wrong error kind for a duplicate name binding: {repr e}"

-- ── Check 10: preparation warnings survive both a successful run and a later binding failure ──
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

-- ── Wave F F4 Task 4: the same boundary with a compiled SCAN step behind it ──
--
-- `Adapter.lean` is generic over `PreparedPlan`: `pack` resolves inputs by name through
-- `PlanBindings.requiredInputs` and `unpack` re-inserts every `materializedNames` entry, neither of
-- which inspects `PlanStep`. A scan therefore needs no adapter-specific code — but that is a claim
-- about the boundary, and these checks are what test it. The fixtures are reused directly from
-- `ScanCompileTest.lean` (its `scratchSched` is the one carrying every boundary population at once:
-- a base capture `S0`, a step capture `K`, block-local scratch `T`, and a persistent state `S`), so
-- a change to the compiler's residualization is felt here too instead of drifting against a private
-- copy.

private def scanEnvPlus (extra : String) (t : DenseTensor) : HashMap String DenseTensor :=
  ScanCompileTest.scratchInputs.insert extra t

-- Check 11: full named round trip through a scan — cross-checked against the legacy evaluator,
-- with an unrelated extra input preserved and block-local scratch kept private. The scratch check
-- asserts `T` is ABSENT from the unpacked environment (not merely that `S` is present): `unpack`
-- starts from the caller's own `env`, so a leak would show up as an extra key, which "the expected
-- states are present" could never detect.
run_cmd do
  match prepareEvalPlan ScanCompileTest.scratchSched
      (InputSignature.ofDenseInputs ScanCompileTest.scratchInputs) with
  | .error f => throwError s!"scan prepare failed: {renderCompileCause f.cause}"
  | .ok prepared =>
      unless prepared.bindings.materializedNames == #[{ name := "S", slot := 2 }] do
        throwError s!"scan materializedNames drifted: {repr prepared.bindings.materializedNames}"
      match runPreparedDense prepared (scanEnvPlus "Unrelated" ⟨[1], #[42.0]⟩) with
      | .error e => throwError s!"scan round-trip run failed: {repr e.cause}"
      | .ok report =>
          -- the state history, against the legacy evaluator's own answer for the same schedule.
          match evalScheduled ScanCompileTest.scratchSched ScanCompileTest.scratchInputs with
          | .error e => throwError s!"legacy evaluator failed on the scan fixture: {e.error}"
          | .ok legacy =>
              match report.env["S"]?, legacy.env["S"]? with
              | some a, some b =>
                  unless a.shape == b.shape && a.data == b.data do
                    throwError s!"scan state S diverges from the legacy evaluator: \
{repr a.data} vs {repr b.data}"
              | _, _ => throwError "scan state S missing from one of the two environments"
          -- block-local scratch never crosses the named boundary.
          if (report.env["T"]?).isSome then
            throwError s!"block-local scratch T leaked into the unpacked env: {repr (report.env["T"]?)}"
          -- an input the plan reads is returned untouched; an input it never reads survives too.
          unless expectTensor report.env["K"]? [3] #[2.0, 3.0, 4.0] do
            throwError s!"scan run did not preserve input K: {repr (report.env["K"]?)}"
          unless expectTensor report.env["Unrelated"]? [1] #[42.0] do
            throwError s!"scan run dropped an unrelated extra input: {repr (report.env["Unrelated"]?)}"

-- Check 12: a name missing at a scan CAPTURE fails loud in `pack`, naming the capture. Both
-- populations are covered: `S0` is captured by the BASE block, `K` by the STEP block — two
-- different `ScanCapture` sources that nonetheless resolve through the same outer `inputSlots`.
run_cmd do
  match prepareEvalPlan ScanCompileTest.scratchSched
      (InputSignature.ofDenseInputs ScanCompileTest.scratchInputs) with
  | .error f => throwError s!"scan prepare failed: {renderCompileCause f.cause}"
  | .ok prepared =>
      match pack prepared (({} : HashMap String DenseTensor).insert "K" ⟨[3], #[2.0, 3.0, 4.0]⟩) with
      | .ok _ => throwError "expected pack to fail on a missing base-block capture"
      | .error (.missingEnvBinding nm) =>
          unless nm == "S0" do throwError s!"wrong missing base-capture name: {nm}"
      | .error e => throwError s!"wrong error kind for a missing base capture: {repr e}"
      match pack prepared (({} : HashMap String DenseTensor).insert "S0" ⟨[], #[1.0]⟩) with
      | .ok _ => throwError "expected pack to fail on a missing step-block capture"
      | .error (.missingEnvBinding nm) =>
          unless nm == "K" do throwError s!"wrong missing step-capture name: {nm}"
      | .error e => throwError s!"wrong error kind for a missing step capture: {repr e}"
      -- Check 13: shape mismatch at a scan capture — `K` declared [3] by the prepared signature.
      match pack prepared (ScanCompileTest.scratchInputs.insert "K" ⟨[4], #[1.0, 2.0, 3.0, 4.0]⟩) with
      | .ok _ => throwError "expected pack to fail on a scan capture's shape mismatch"
      | .error (.shapeMismatch nm slot expected actual) =>
          unless nm == "K" && slot == 1 && expected == #[3] && actual == [4] do
            throwError s!"wrong shapeMismatch payload at a scan capture: name={nm} slot={slot} \
expected={repr expected} actual={repr actual}"
      | .error e => throwError s!"wrong error kind for a scan capture shape mismatch: {repr e}"
      -- Check 14: storage mismatch at a scan capture — declared shape agrees, data array does not.
      match pack prepared (ScanCompileTest.scratchInputs.insert "K" ⟨[3], #[1.0, 2.0]⟩) with
      | .ok _ => throwError "expected pack to fail on a scan capture's storage mismatch"
      | .error (.storageMismatch nm slot shape dataSize) =>
          unless nm == "K" && slot == 1 && shape == [3] && dataSize == 2 do
            throwError s!"wrong storageMismatch payload at a scan capture: name={nm} slot={slot} \
shape={repr shape} dataSize={dataSize}"
      | .error e => throwError s!"wrong error kind for a scan capture storage mismatch: {repr e}"

-- Check 15: warnings through a scan. TWO distinct `paddedAccess` warnings (two different externals
-- read past their extents from inside the recurrence) so the comparison below discriminates ORDER
-- as well as payload — a one-warning fixture would pass under any permutation. Cross-checked
-- against the legacy evaluator producing the same list on the same inputs.

def axWarn : AxisSpec := ⟨"l", 3201, .nat⟩

/-- Public (unlike this file's other fixtures) because `DifferentialTest.lean`'s scan parity matrix
    reuses it: every scan fixture in `ScanCompileTest.lean` is warning-free, so without this one the
    matrix's warning comparison would pass vacuously there. -/
def scanWarnSched : ScheduledProgram :=
  { decls := [.iter axWarn 3]
  , stmts := [.scan "S" [axWarn]
      [ .assign "S" [.iterAt axWarn 0]
          { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity } ]
      [ .assign "S" [.iterNext axWarn]
          { body := { terms := [ { factors := [.read "S" [.axis axWarn]] }
                               , { factors := [.read "X" [.scale 2 axWarn]] }
                               , { factors := [.read "V" [.scale 3 axWarn]] } ] }
          , nonlin := .identity } ]
      false ]
  , env := {}
  , extNames := insert "S0" (insert "X" (insert "V" (∅ : Finset String)))
  , explicitSizes := (({} : HashMap UID Nat).insert axWarn.uid 3) }

def scanWarnInputs : HashMap String DenseTensor :=
  ((({} : HashMap String DenseTensor).insert "S0" ⟨[], #[1.0]⟩).insert
    "X" ⟨[3], #[1.0, 2.0, 3.0]⟩).insert "V" ⟨[4], #[5.0, 6.0, 7.0, 8.0]⟩

run_cmd do
  match prepareEvalPlan scanWarnSched (InputSignature.ofDenseInputs scanWarnInputs) with
  | .error f => throwError s!"scan-warning prepare failed: {renderCompileCause f.cause}"
  | .ok prepared =>
      unless prepared.warnings.length == 2 do
        throwError s!"fixture is broken: expected exactly two preparation warnings, got \
{prepared.warnings.map toString}"
      match evalScheduled scanWarnSched scanWarnInputs with
      | .error e => throwError s!"legacy evaluator failed on the scan-warning fixture: {e.error}"
      | .ok legacy =>
          unless legacy.warnings == prepared.warnings do
            throwError s!"prepared warnings diverge from the legacy evaluator's:\n\
{prepared.warnings.map toString}\nvs\n{legacy.warnings.map toString}"
      -- success path: the same list, in the same order, with the same payloads.
      match runPreparedDense prepared scanWarnInputs with
      | .error e => throwError s!"scan-warning run unexpectedly failed: {repr e.cause}"
      | .ok report =>
          unless report.warnings == prepared.warnings do
            throwError s!"success-path scan warnings dropped/reordered: {report.warnings.map toString}"
      -- binding-failure path: warnings survive a `pack` failure unchanged.
      match runPreparedDense prepared (({} : HashMap String DenseTensor)) with
      | .ok _ => throwError "expected a binding failure against an empty env"
      | .error failure =>
          unless failure.warnings == prepared.warnings do
            throwError s!"binding-failure scan warnings dropped/reordered: \
{failure.warnings.map toString}"
          match failure.cause with
          | .binding (.missingEnvBinding nm) =>
              unless nm == "S0" do throwError s!"wrong missing name: {nm}"
          | c => throwError s!"expected a binding failure, got: {repr c}"

-- Check 16: `PlanRunCause.execution` stays unreachable once a scan step is in the plan, so
-- "warnings preserved on execution failure" has no natural trigger to test against. This is a
-- property of the code, re-verified for F4 rather than inherited: `pack` (Adapter.lean) validates
-- presence, shape, and storage of every `raw.inputSlots` entry against `raw.tensorSigs` using the
-- SAME two predicates `runDensePlan` (EvalPlan.lean) re-applies, and returns exactly
-- `raw.inputSlots.size` tensors in that order, so its arity, shape and storage arms are all dead
-- once `pack` returned `.ok`; `runDenseScan` (Scan.lean) then throws only from arms its own doc
-- comments mark unreachable-because-checked (`checkCaptures` guarantees every block input has a
-- capture, and the step context comes from `mixedRadixUnrank` over the checked `stepExtents`).
-- Pinned two ways: the constructor is named directly (same pattern as the C3/C4 precedent above),
-- and the four structurally distinct scan shapes below assert positively that `pack` succeeding
-- implies `runDensePlan` succeeding — which is exactly the statement that makes the branch dead.
-- If a future change ever DOES make it reachable, this loop fails and says so, rather than the
-- comment above silently going stale.
run_cmd do
  for (name, sched, inputs) in
      [ ("scratch", ScanCompileTest.scratchSched, ScanCompileTest.scratchInputs)
      , ("coupled", ScanCompileTest.coupledSched, ScanCompileTest.coupledInputs)
      , ("multiBase", ScanCompileTest.multiBaseSched, ScanCompileTest.multiBaseInputs)
      , ("twoScans", ScanCompileTest.twoScanSched, ScanCompileTest.twoScanInputs) ] do
    match prepareEvalPlan sched (InputSignature.ofDenseInputs inputs) with
    | .error f => throwError s!"{name}: prepare failed: {renderCompileCause f.cause}"
    | .ok prepared =>
        match pack prepared inputs with
        | .error e => throwError s!"{name}: pack unexpectedly failed: {repr e}"
        | .ok packed =>
            match runDensePlan prepared.plan packed with
            | .error e =>
                throwError s!"{name}: runDensePlan failed after a successful pack — \
PlanRunCause.execution is NOT unreachable and Check 16's reasoning is stale: {repr e}"
            | .ok _ => pure ()

end LeanNCD.Eval.Plan.AdapterTest

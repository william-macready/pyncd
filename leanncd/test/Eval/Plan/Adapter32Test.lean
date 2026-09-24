import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter32
import Eval.Plan.CompileTest   -- fixture 10 reuses its `.float64` identity plan as the wrong-carrier donor

/-!
# The named binary32 boundary (f32 slice, Task 4)

Fixtures 3–10 and 12 of Task 4: the `pack32`/`unpack32`/`runPreparedDense32` round trip, its
failure boundaries, and the three `.float32` storage-kind doors. Fixtures 1, 2, 13, 14 and 15 (the
declaration-aware binary32 SIGNATURE constructor) live in `SignatureTest.lean`; fixture 11 (the
`EvalReport` compatibility shim) lives in `AdapterTest.lean` beside the Float adapter it belongs to.

Each program here is a `tlprog!` clone of an existing binary64 donor with its real declarations
changed to `tensor f32` and its inputs re-expressed as native `Float32` buffers, so a difference in
outcome is attributable to the carrier and to nothing else. The donors are named per fixture below.

**Every value expectation is an exact IEEE-754 binary32 BIT PATTERN, compared through
`Float32.toBits`**, for the reason `KernelDense32Test.lean` states at length: `BEq Float32` is IEEE
comparison, which identifies `+0` with `-0` and makes every NaN unequal to itself, so it is not
propositional equality and is never used to assert a value here.
-/

namespace LeanNCD.Eval.Plan.Adapter32Test
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

/-- The exact bits of a named binary32 result, or `none` if the name is absent. -/
private def bitsOf (env : NamedDenseEnv32) (nm : String) : Option (Array UInt32) :=
  (env[nm]?).map (fun t => t.data.map Float32.toBits)

/-- Shape and exact bits together, so a fixture cannot be satisfied by the right numbers under the
    wrong shape. -/
private def expect32 (env : NamedDenseEnv32) (nm : String) (shape : List Nat)
    (bits : Array UInt32) : Bool :=
  (env[nm]?).map (fun t => t.shape == shape && t.data.map Float32.toBits == bits) |>.getD false

/-- Manual renderer for `PlanCompileCause` (test-failure messages only): the type deliberately has
    no `Repr`/`ToString` (`ShapeError`, nested via `.shape`, has neither), so a diagnosable message
    has to dispatch per-constructor to whichever rendering each nested cause DOES support. Same
    shape as `AdapterTest`'s own `renderCompileCause`, which is `private` to that module. -/
private def renderCompileCause : PlanCompileCause → String
  | .inputSignature c => s!"inputSignature: {repr c}"
  | .capability c     => s!"capability: {repr c}"
  | .shape c          => s!"shape: {c}"
  | .scan c           => s!"scan: {repr c}"
  | .invalidPlan c    => s!"invalidPlan: {repr c}"
  | .bindings c       => s!"bindings: {repr c}"
  | .nonlin c         => s!"nonlin: {repr c}"
  | .sourceInvariant c => s!"sourceInvariant: {repr c}"

/-- Compile a source program and prepare it through the declaration-aware BINARY32 signature
    constructor — the whole public entry path a caller of this boundary takes. Every fixture below
    goes through this one helper, so no fixture can accidentally prepare its plan a different way. -/
private def prepare32 (p : TLProgram) (inputs : NamedDenseEnv32) : Except String PreparedPlan := do
  let sched ← match p.compileToScheduled.run 0 with
    | .ok s _ => .ok s
    | .error e _ => .error s!"compile failed: {repr e}"
  let sig ← match InputSignature.ofDenseInputs32ForDecls sched.decls inputs with
    | .ok s => .ok s
    | .error e => .error s!"declaration-aware binary32 signature rejected sched.decls: {repr e}"
  match prepareEvalPlan sched sig with
  | .ok prepared => .ok prepared
  | .error f => .error s!"prepare failed: {renderCompileCause f.cause}"

/-- The ordered materialized `(name, dtype)` pairs, in `materializedNames` order, repeats included. -/
private def matDtypes (p : PreparedPlan) : Except String (Array (String × ScalarDType)) :=
  match p.materializedSignatures with
  | .ok ss => .ok (ss.map (fun e => (e.1, e.2.dtype)))
  | .error e => .error s!"materializedSignatures failed: {repr e}"

/-! ## Fixture 3: the named contraction round trip

`AdapterTest.zeroCoeffProg`/`zeroCoeffInputs` (`Y[i] := A[i] · B[j]`, A = [10, 100], B = [1, 2, 3],
ΣB = 6 ⇒ Y = [60, 600]) with `A`, `B` and `Y` declared `tensor f32` and native binary32 inputs.

The asymmetric contraction is the donor's own choice and is retained deliberately: `A` is retained
on the output axis while `B` is contracted, so a positional slot swap would produce `B[i] · ΣA`
rather than `A[i] · ΣB`, which a commutative `A[i] + B[i]` fixture could not discriminate (the donor
fixture's comment records that this was established by mutation testing, not assumed). -/

def f32ContractProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  tensor f32 A(i), B(j), Y(i)
  Y[i] := A[i] · B[j]
}

def f32ContractInputs : NamedDenseEnv32 :=
  (({} : NamedDenseEnv32).insert "A" ⟨[2], #[(10.0 : Float32), 100.0]⟩).insert
    "B" ⟨[3], #[(1.0 : Float32), 2.0, 3.0]⟩

run_cmd do
  let prepared ← match prepare32 f32ContractProg f32ContractInputs with
    | .ok p => pure p
    | .error e => throwError s!"f32 contraction: {e}"
  -- The plan really is binary32 evidence, so nothing below is the Float path in disguise.
  unless prepared.plan.storageKind == LeanNCD.StorageKind.float32 do
    throwError s!"f32 contraction: storage kind is {repr prepared.plan.storageKind}, not float32"
  match runPreparedDense32 prepared f32ContractInputs with
  | .error e => throwError s!"f32 contraction run failed: {repr e.cause}"
  | .ok report =>
      -- `60` and `600` as exact binary32 bit patterns.
      unless expect32 report.env "Y" [2] #[1114636288, 1142292480] do
        throwError s!"f32 contraction Y wrong: {repr (bitsOf report.env "Y")}"
      -- The ORIGINAL named inputs survive the round trip bit for bit: `unpack32` starts from the
      -- caller's own environment, exactly as `unpack` does.
      unless expect32 report.env "A" [2] #[1092616192, 1120403456] do
        throwError s!"f32 contraction did not preserve input A: {repr (bitsOf report.env "A")}"
      unless expect32 report.env "B" [3] #[1065353216, 1073741824, 1077936128] do
        throwError s!"f32 contraction did not preserve input B: {repr (bitsOf report.env "B")}"
  -- ... and the materialized signature the prepared accessor publishes is `f32`, not `f64`.
  match matDtypes prepared with
  | .error e => throwError s!"f32 contraction: {e}"
  | .ok pairs =>
      unless pairs == #[("Y", ScalarDType.f32)] do
        throwError s!"f32 contraction materialized signatures wrong: {repr pairs}"

/-! ## Fixture 4: repeated assignment, homogeneous f32

`CompileTest.repeatSched`'s shape (`Y[i] := A[i]; Y[i] := B[i]; Z[i] := Y[i]`) in source spelling
with binary32 declarations. `materializedNames` is NOT deduplicated — two `Y` entries, one per
write, then `Z`, in schedule order — and `unpack32` inserts them IN THAT ORDER, so the LAST write is
what survives under the repeated name. A deduplicating or reversed publication would leave `Y` at
`A`'s value instead of `B`'s, which is why the two inputs carry visibly different values. -/

def f32RepeatProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  tensor f32 A(i), B(i), Y(i), Z(i)
  Y[i] := A[i]
  Y[i] := B[i]
  Z[i] := Y[i]
}

def f32RepeatInputs : NamedDenseEnv32 :=
  (({} : NamedDenseEnv32).insert "A" ⟨[2], #[(1.0 : Float32), 2.0]⟩).insert
    "B" ⟨[2], #[(100.0 : Float32), 200.0]⟩

run_cmd do
  let prepared ← match prepare32 f32RepeatProg f32RepeatInputs with
    | .ok p => pure p
    | .error e => throwError s!"f32 repeat: {e}"
  unless prepared.bindings.materializedNames.map (·.name) == #["Y", "Y", "Z"] do
    throwError s!"f32 repeat materializedNames drifted: \
{repr (prepared.bindings.materializedNames.map (·.name))}"
  -- The two `Y` entries name DISTINCT slots, so "last write wins" is a real ordering claim about
  -- publication rather than a statement about one slot written twice.
  let ySlots := (prepared.bindings.materializedNames.filter (·.name == "Y")).map (·.slot)
  unless ySlots.size == 2 && ySlots[0]! != ySlots[1]! do
    throwError s!"f32 repeat: expected two distinct Y slots, got {repr ySlots}"
  match runPreparedDense32 prepared f32RepeatInputs with
  | .error e => throwError s!"f32 repeat run failed: {repr e.cause}"
  | .ok report =>
      -- `100` and `200` as exact binary32 bits — `B`'s values, not `A`'s (`1`/`2` would be
      -- `#[1065353216, 1073741824]`).
      unless expect32 report.env "Y" [2] #[1120403456, 1128792064] do
        throwError s!"f32 repeat: Y did not take the LAST write's value: \
{repr (bitsOf report.env "Y")}"
      unless expect32 report.env "Z" [2] #[1120403456, 1128792064] do
        throwError s!"f32 repeat: Z did not read the LAST write of Y: \
{repr (bitsOf report.env "Z")}"
  match matDtypes prepared with
  | .error e => throwError s!"f32 repeat: {e}"
  | .ok pairs =>
      unless pairs == #[("Y", ScalarDType.f32), ("Y", ScalarDType.f32), ("Z", ScalarDType.f32)] do
        throwError s!"f32 repeat materialized signatures wrong: {repr pairs}"

/-! ## Fixture 5: a malformed binary32 input buffer is rejected BEFORE execution

`AdapterTest`'s `undersizedDataInputs` shape at this boundary: `A`'s declared shape `[2]` agrees
with the prepared signature, but its native buffer holds ONE element. `pack32` reports
`storageMismatch` naming the input, its slot, its shape and its actual size — the worker is never
reached, so the failure is diagnosable in the caller's own vocabulary. -/

def f32UndersizedInputs : NamedDenseEnv32 :=
  (({} : NamedDenseEnv32).insert "A" ⟨[2], #[(10.0 : Float32)]⟩).insert
    "B" ⟨[3], #[(1.0 : Float32), 2.0, 3.0]⟩

run_cmd do
  let prepared ← match prepare32 f32ContractProg f32ContractInputs with
    | .ok p => pure p
    | .error e => throwError s!"f32 undersized: {e}"
  match pack32 prepared f32UndersizedInputs with
  | .ok _ => throwError "expected pack32 to fail on an undersized binary32 buffer"
  | .error (.storageMismatch nm slot shape dataSize) =>
      unless nm == "A" && slot == 0 && shape == [2] && dataSize == 1 do
        throwError s!"wrong storageMismatch payload: name={nm} slot={slot} shape={repr shape} \
dataSize={dataSize}"
  | .error e => throwError s!"wrong error kind for an undersized binary32 buffer: {repr e}"
  -- The same environment through the composite runner reports the same cause, tagged `.binding`.
  match runPreparedDense32 prepared f32UndersizedInputs with
  | .ok _ => throwError "expected runPreparedDense32 to fail on an undersized binary32 buffer"
  | .error f =>
      unless f.cause == .binding (.storageMismatch "A" 0 [2] 1) do
        throwError s!"wrong composite cause for an undersized binary32 buffer: {repr f.cause}"

/-! ## Fixture 6: the result store's arity is the PLAN's, not the caller's

`AdapterTest`'s wrong-result-arity fixture against `unpack32`. The store handed over is the plan's
own result with ONE EXTRA, validly shaped slot appended — so every materialized binding is still in
range and the rejection cannot be a disguised `slotOutOfRange`. Removing `unpackBodyOf`'s arity
guard turns this fixture into a success, which is what makes the guard observable here. -/

run_cmd do
  let prepared ← match prepare32 f32ContractProg f32ContractInputs with
    | .ok p => pure p
    | .error e => throwError s!"f32 arity: {e}"
  let packed ← match pack32 prepared f32ContractInputs with
    | .ok a => pure a
    | .error e => throwError s!"f32 arity: pack32 unexpectedly failed: {repr e}"
  let result ← match runDensePlan32 prepared.plan packed with
    | .ok r => pure r
    | .error e => throwError s!"f32 arity: runDensePlan32 unexpectedly failed: {repr e}"
  unless result.size == 3 do
    throwError s!"fixture drifted: expected a 3-slot store, got {result.size}"
  -- The plan's own store round-trips (the valid sibling, so the rejection below is about arity).
  match unpack32 prepared f32ContractInputs result with
  | .error c => throwError s!"f32 arity: the plan's own store was rejected: {repr c}"
  | .ok env =>
      unless expect32 env "Y" [2] #[1114636288, 1142292480] do
        throwError s!"f32 arity: exact-size unpack32 lost Y: {repr (bitsOf env "Y")}"
  -- One extra VALIDLY SHAPED slot: legal against the store, illegal against the 3-slot checked plan.
  let oversized := result.push ⟨[2], #[(1.0 : Float32), 2.0]⟩
  match unpack32 prepared f32ContractInputs oversized with
  | .ok env =>
      throwError s!"an oversized store was accepted by unpack32: {repr (bitsOf env "Y")}"
  | .error c =>
      unless c == .resultStore (.storeArityMismatch 3 4) do
        throwError s!"unpack32: wrong error for an oversized store: {repr c}"

/-! ## Fixture 7: preparation warnings through the binary32 boundary

`AdapterTest.warnProg`/`warnInputs` (`Y[i, j] := X[2 * i + j]`, `X` shape `[6]` read up to index 8)
with binary32 declarations and a native binary32 buffer. The warning list is genuinely NON-EMPTY —
cross-checked against the legacy evaluator producing the SAME list on the same binary64 values, so
this is not a vacuously-passing empty comparison — and must arrive unchanged in the successful
`EvalReport32` AND on the reachable `missingEnvBinding "X"` failure against an empty environment.

No `PlanRunCause.execution` fixture is claimed here: `AdapterTest`'s Check 16 (corrected, f32 slice
Task 2 — see its own doc comment) establishes only that `pack`/`pack32` rule out every *shape/arity/
storage* cause before the worker runs, which `pack32`/`runDensePlan32` reproduce exactly; a RUNTIME
domain violation inside the worker (an inline unary factor's `log`/`sqrt`/`recip`) is a different
matter and genuinely reaches `.execution` in both carriers — Fixture 2.11 below pins the binary32
half of that reachability, its `AdapterTest` twin the binary64 half. -/

def f32WarnProg : TLProgram := tlprog!{
  axis i : ℕ = 4
  axis j : ℕ = 3
  tensor f32 X(i), Y(i, j)
  Y[i, j] := X[2 * i + j]
}

def f32WarnInputs : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "X" ⟨[6], #[(1.0 : Float32), 2.0, 3.0, 4.0, 5.0, 6.0]⟩

/-- The same program in the untyped (binary64) spelling, with the same values — the legacy
    evaluator's own input, used only to cross-check that the warning list below is real. -/
def warnProgF64 : TLProgram := tlprog!{
  axis i : ℕ = 4
  axis j : ℕ = 3
  Y[i, j] := X[2 * i + j]
}

def warnInputsF64 : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "X" ⟨[6], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]⟩

run_cmd do
  let prepared ← match prepare32 f32WarnProg f32WarnInputs with
    | .ok p => pure p
    | .error e => throwError s!"f32 warn: {e}"
  if prepared.warnings.isEmpty then
    throwError "fixture is broken: expected prepareEvalPlan to record a non-empty warning list"
  else pure ()
  match TLProgram.eval warnProgF64 warnInputsF64 with
  | .error e => throwError s!"legacy evaluator failed unexpectedly: {e}"
  | .ok legacy =>
      unless legacy.warnings == prepared.warnings do
        throwError s!"binary32 prepared warnings diverge from the legacy evaluator's: \
{prepared.warnings.map toString} vs {legacy.warnings.map toString}"
  -- success path: the identical list arrives in `EvalReport32`.
  match runPreparedDense32 prepared f32WarnInputs with
  | .error e => throwError s!"f32 warn run unexpectedly failed: {repr e.cause}"
  | .ok report =>
      unless report.warnings == prepared.warnings do
        throwError s!"binary32 success-path warnings dropped/changed: \
{report.warnings.map toString}"
      -- The zero-padded tail is real output, not an artifact: indices 6..8 pad to `+0`.
      unless expect32 report.env "Y" [4, 3]
          #[ 1065353216, 1073741824, 1077936128, 1077936128, 1082130432, 1084227584
           , 1084227584, 1086324736, 0, 0, 0, 0 ] do
        throwError s!"f32 warn Y wrong: {repr (bitsOf report.env "Y")}"
  -- failure path: the SAME nonempty list survives a reachable binding failure.
  match runPreparedDense32 prepared ({} : NamedDenseEnv32) with
  | .ok _ => throwError "expected a binding failure against an empty binary32 environment"
  | .error failure =>
      unless failure.warnings == prepared.warnings do
        throwError s!"binary32 binding-failure warnings dropped/changed: \
{failure.warnings.map toString}"
      unless failure.cause == .binding (.missingEnvBinding "X") do
        throwError s!"expected a missing-binding failure naming X, got: {repr failure.cause}"

/-! ## Fixture 8: the reduction that distinguishes the carriers

`CompileTest.contractSched`'s preparation-valid shape with its `A[i]` factor and its free output
axis removed, leaving `B[j]` as the sole factor over the pinned extent-three reduction and a SCALAR
destination `Y`. The inputs are `[2²⁴, 1, −2²⁴]`.

Left-to-right in binary32: `2²⁴ + 1` is not representable and rounds back to `2²⁴`, so the third
term cancels it exactly and `Y = +0` (bits `0`). In binary64 the same fold gives `2²⁴ + 1 = 16777217`
and `Y = 1`. The binary64 half below runs the SAME transformed program in its ordinary-tensor
spelling through `runPreparedDense`, so the contrast is measured rather than asserted — this is the
fixture that a widen-to-binary64-then-narrow execution leg cannot pass. -/

def f32ReductionProg : TLProgram := tlprog!{
  axis j : ℕ = 3
  tensor f32 B(j), Y()
  Y[] := B[j]
}

def f32ReductionInputs : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "B" ⟨[3], #[(16777216.0 : Float32), 1.0, -16777216.0]⟩

/-- The same program, ordinary (binary64) declarations and the same three values. -/
def f64ReductionProg : TLProgram := tlprog!{
  axis j : ℕ = 3
  tensor B(j), Y()
  Y[] := B[j]
}

def f64ReductionInputs : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "B" ⟨[3], #[16777216.0, 1.0, -16777216.0]⟩

run_cmd do
  let prepared ← match prepare32 f32ReductionProg f32ReductionInputs with
    | .ok p => pure p
    | .error e => throwError s!"f32 reduction: {e}"
  match runPreparedDense32 prepared f32ReductionInputs with
  | .error e => throwError s!"f32 reduction run failed: {repr e.cause}"
  | .ok report =>
      unless expect32 report.env "Y" [] #[0] do
        throwError s!"f32 reduction: expected binary32 Y = +0 (bits 0), got \
{repr (bitsOf report.env "Y")}"
  -- The binary64 contrast, through the Float named runner, over the same three values.
  match f64ReductionProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"f64 reduction compile failed: {repr e}"
  | .ok sched _ =>
      let sig ← match InputSignature.ofDenseInputsForDecls sched.decls f64ReductionInputs with
        | .ok s => pure s
        | .error e => throwError s!"f64 reduction signature rejected sched.decls: {repr e}"
      match prepareEvalPlan sched sig with
      | .error _ => throwError "f64 reduction prepare failed"
      | .ok preparedF64 =>
          unless preparedF64.plan.storageKind == LeanNCD.StorageKind.float64 do
            throwError "f64 reduction control is not a binary64 plan — fixture is broken"
          match runPreparedDense preparedF64 f64ReductionInputs with
          | .error e => throwError s!"f64 reduction run failed: {repr e.cause}"
          | .ok report64 =>
              match report64.env["Y"]? with
              | some y =>
                  unless y.shape == [] && y.data.map Float.toBits == #[0x3ff0000000000000] do
                    throwError s!"f64 reduction: expected binary64 Y = 1, got \
{repr (y.data.map Float.toBits)}"
              | none => throwError "f64 reduction: Y missing from the binary64 environment"

/-! ## Fixture 9: max/min aggregation through the binary32 destination algebra

`DifferentialTest`'s `maxPlainProg`/`minPlainProg`/`plainAggInputs` rebuilt from their source shapes
(those donors are `private` and cannot be referenced across modules): `Y[i] := maxreduce(A[i, j])`
and its `minreduce` sibling over `A = [[3, 1], [1, 5]]`, with `tensor f32` declarations.

The values are the donors' own, chosen so `max`/`min` and `sum` DISAGREE: row sums are `[4, 6]`,
row maxima `[3, 5]`, row minima `[1, 1]`. `Compile.lean`'s `algebraForDest` `.f32` arm became
REACHABLE only when Task 2 admitted f32 evidence, and it is the single point where a homogeneous-f32
schedule's real algebra is chosen; hardcoding a sum algebra there would produce `[4, 6]` here
instead. That is the regression the donor's own comment names, now live at a new call site. -/

def f32MaxProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  tensor f32 A(i, j), Y(i)
  Y[i] := maxreduce(A[i, j])
}

def f32MinProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  tensor f32 A(i, j), Y(i)
  Y[i] := minreduce(A[i, j])
}

def f32AggInputs : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "A" ⟨[2, 2], #[(3.0 : Float32), 1.0, 1.0, 5.0]⟩

run_cmd do
  for (nm, prog, expected) in
      [ ("max", f32MaxProg, #[(1077936128 : UInt32), 1084227584])   -- [3, 5]
      , ("min", f32MinProg, #[(1065353216 : UInt32), 1065353216]) ] do   -- [1, 1]
    let prepared ← match prepare32 prog f32AggInputs with
      | .ok p => pure p
      | .error e => throwError s!"f32 {nm}: {e}"
    unless prepared.plan.storageKind == LeanNCD.StorageKind.float32 do
      throwError s!"f32 {nm}: storage kind is {repr prepared.plan.storageKind}, not float32"
    match runPreparedDense32 prepared f32AggInputs with
    | .error e => throwError s!"f32 {nm} run failed: {repr e.cause}"
    | .ok report =>
        unless expect32 report.env "Y" [2] expected do
          throwError s!"f32 {nm}: expected {repr expected} (the sum would be \
#[1082130432, 1086324736]), got {repr (bitsOf report.env "Y")}"
    match matDtypes prepared with
    | .error e => throwError s!"f32 {nm}: {e}"
    | .ok pairs =>
        unless pairs == #[("Y", ScalarDType.f32)] do
          throwError s!"f32 {nm} materialized signatures wrong: {repr pairs}"

/-! ## Fixture 10: the three binary32 storage-kind doors fire FIRST

The mirror of Task 2's fixtures 20 and 21 at the new boundary. `CompileTest.identitySched`'s prepared
plan is genuinely `.float64` and genuinely well-formed (`prepareEvalPlan` built it, so its bindings
sidecar passes `checkPreparedBindings` and cannot be what any rejection below is attributable to).

Each entry is additionally handed input that is invalid in that entry's OWN pre-existing terms, so
these are ORDER claims and not existence claims:

  * `pack32` gets a shape-conforming, storage-malformed buffer — `packBodyOf`'s storage check would
    otherwise report `storageMismatch`;
  * `unpack32` gets an empty result store against a two-slot plan — `unpackBodyOf`'s arity check
    would otherwise report `storeArityMismatch 2 0`;
  * `runPreparedDense32` gets a perfectly well-shaped native binary32 environment, and must fail at
    its OWN adapter tier (`PlanRunCause.storageKindMismatch` directly) rather than inheriting
    `packBodyOf`'s nested `.binding (.storageKindMismatch …)`. -/

def f64Prepared : Option PreparedPlan :=
  (prepareEvalPlan CompileTest.identitySched CompileTest.identitySig).toOption

-- The donor really is a well-formed BINARY64 plan, so nothing below is a disguised bindings failure.
#guard f64Prepared.map (·.plan.storageKind) == some LeanNCD.StorageKind.float64
#guard (match f64Prepared with
  | some p => (checkPreparedBindings p).toOption.isSome
  | none => false)
#guard f64Prepared.map (·.plan.raw.tensorSigs.size) == some 2

/-- A well-shaped native binary32 environment for that plan: `X : [3]`, three elements. Used as-is
    by the `runPreparedDense32` half; the `pack32` half malforms its storage. -/
def wellShaped32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "X" ⟨[3], #[(1.0 : Float32), 2.0, 3.0]⟩

/-- The same name with a shape-conforming header but only ONE stored element. -/
def badStorage32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "X" ⟨[3], #[(1.0 : Float32)]⟩

def pack32Err (p : Option PreparedPlan) (env : NamedDenseEnv32) : Option InputBindingError :=
  match p with
  | none => none
  | some p => match pack32 p env with
              | .error e => some e
              | .ok _ => none

def unpack32Err (p : Option PreparedPlan) (result : Array DenseTensor32) : Option PlanRunCause :=
  match p with
  | none => none
  | some p => match unpack32 p wellShaped32 result with
              | .error e => some e
              | .ok _ => none

def run32Err (p : Option PreparedPlan) (env : NamedDenseEnv32) : Option PlanRunCause :=
  match p with
  | none => none
  | some p => match runPreparedDense32 p env with
              | .error f => some f.cause
              | .ok _ => none

-- Fixture 10a: `pack32` reports the storage KIND, not the storage SIZE.
#guard pack32Err f64Prepared badStorage32 == some (.storageKindMismatch .float32 .float64)

-- Fixture 10b: `unpack32` reports the storage KIND, not `storeArityMismatch 2 0`.
#guard unpack32Err f64Prepared #[] == some (.storageKindMismatch .float32 .float64)

-- Fixture 10c: `runPreparedDense32` fails at its own adapter tier, with a well-shaped environment —
-- `PlanRunCause.storageKindMismatch` directly, NOT `.binding (.storageKindMismatch …)` from
-- `packBodyOf` and not `.execution (…)` from `runDensePlan32`.
#guard run32Err f64Prepared wellShaped32 == some (.storageKindMismatch .float32 .float64)

-- Fixture 10 control: preparation warnings survive this failure path exactly as they do every other
-- one. This plan carries none, so the observable claim is that the field is `plan.warnings` verbatim
-- rather than a re-derived or dropped list.
#guard (match f64Prepared with
  | some p => (match runPreparedDense32 p wellShaped32 with
               | .error f => f.warnings == p.warnings
               | .ok _ => false)
  | none => false)

/-! ### Fixture 10d: the composite guard also precedes `checkPreparedBindings`

10a–10c race the guard against `packBodyOf`'s storage check, `unpackBodyOf`'s arity check, and
`packBodyOf`'s own nested guard. All three donors have VALID bindings
(`#guard (checkPreparedBindings p).toOption.isSome` above), so none of them can see a guard
relocated to run AFTER `checkPreparedBindings` — `runPreparedDenseOf`'s very next step. This
sub-case closes that: the SAME `.float64` plan with a deliberately out-of-range materialized slot,
so `checkPreparedBindings` genuinely fails on it, and `runPreparedDense32` must still report its own
adapter-tier storage kind rather than the bindings diagnostic.

(`PreparedPlan`/`PlanBindings` have public constructors — `AdapterTest`'s Check 18 builds malformed
ones the same way by struct update — so this state is constructible even though `prepareEvalPlan`
cannot emit it.) -/

def f64PreparedBadBindings : Option PreparedPlan :=
  f64Prepared.map (fun p =>
    { p with bindings := { p.bindings with
        materializedNames := #[{ name := "Y", slot := 99 }] } })

-- The bindings really ARE invalid, and `checkPreparedBindings` really does reject them — otherwise
-- the assertion below would be vacuous. The two-slot plan makes `slotOutOfRange 99 2` exact.
#guard (match f64PreparedBadBindings with
  | some p => (match checkPreparedBindings p with
               | .error e => e == .materializedSlot (.slotOutOfRange 99 2)
               | .ok _ => false)
  | none => false)

-- Control: the BINARY64 runner — whose own guard admits this `.float64` plan — reaches
-- `checkPreparedBindings` and reports exactly that, so the bindings error is a reachable,
-- observable alternative and not a hypothetical one.
#guard (match f64PreparedBadBindings with
  | some p => (match runPreparedDense p CompileTest.identityInputs with
               | .error f => f.cause == .binding (.invalidPreparedBindings
                   (.materializedSlot (.slotOutOfRange 99 2)))
               | .ok _ => false)
  | none => false)

-- The claim: `runPreparedDense32` reports the STORAGE KIND, not the bindings error. A guard placed
-- after the `checkPreparedBindings` call would report `.binding (.invalidPreparedBindings …)` here.
-- Written as `run_cmd` rather than `#guard` so a violation NAMES the cause it saw instead — the
-- point of this sub-case is which of two specific diagnostics arrives, and "Expression" would not
-- distinguish them.
run_cmd do
  match run32Err f64PreparedBadBindings wellShaped32 with
  | some (.storageKindMismatch .float32 .float64) => pure ()
  | other =>
      throwError s!"fixture 10d: runPreparedDense32's own guard did not precede \
checkPreparedBindings — expected storageKindMismatch .float32 .float64, got {repr other}"

/-! ## Fixture 12: a Boolean tensor rides the binary32 carrier, uncoerced

Fixture 3's shape with one `predicate` input and one `tensor f32` input, BOTH presented as native
`Float32` buffers holding deliberately NON-BINARY values: `0.25` (bits `1048576000`) for the
predicate and `0.75` (bits `1061158912`) for the real tensor.

Three separate claims:

  * the declaration-aware binary32 constructor and the whole `pack32`/`runPreparedDense32`/`unpack32`
    path ACCEPT the `bool` signature — a `predicate` declaration is precision-neutral
    (`storageConstraintOfDecl`), so a Boolean name shares whichever real carrier the graph selects;
  * the exact bits survive with NO truth-value coercion, on input and on output alike. This is the
    documented Boolean semantics (`admittedAlgebraBool` is Float `min`/`max` over the carrier's own
    zero/one, and `Check.lean` states outright that runtime values are not restricted to `0`/`1`), so
    a `0.25` that came back as `1.0` would be a coercion this layer never had licence to perform;
  * the published signatures are `bool` for the predicate destination and `f32` for the real one, in
    `materializedNames` order. -/

def f32BoolProg : TLProgram := tlprog!{
  axis i : ℕ = 1
  tensor f32 A(i), Y(i)
  predicate P(i), Q(i)
  Q[i] := P[i]
  Y[i] := A[i]
}

def f32BoolInputs : NamedDenseEnv32 :=
  (({} : NamedDenseEnv32).insert "P" ⟨[1], #[Float32.ofBits 1048576000]⟩).insert
    "A" ⟨[1], #[Float32.ofBits 1061158912]⟩

run_cmd do
  let prepared ← match prepare32 f32BoolProg f32BoolInputs with
    | .ok p => pure p
    | .error e => throwError s!"f32 bool: {e}"
  unless prepared.plan.storageKind == LeanNCD.StorageKind.float32 do
    throwError s!"f32 bool: storage kind is {repr prepared.plan.storageKind}, not float32"
  -- The INPUT signature table really does carry a `bool` entry beside an `f32` one, which is the
  -- combination `deriveStorageKind` must treat as homogeneous rather than mixed.
  let inputDtypes := prepared.plan.raw.tensorSigs.map (·.dtype)
  unless inputDtypes.any (· == ScalarDType.bool) && inputDtypes.any (· == ScalarDType.f32) do
    throwError s!"f32 bool: expected both bool and f32 signatures, got {repr inputDtypes}"
  -- `pack32` accepts the bool-signature input slot.
  match pack32 prepared f32BoolInputs with
  | .error e => throwError s!"f32 bool: pack32 rejected the bool signature: {repr e}"
  | .ok _ => pure ()
  match runPreparedDense32 prepared f32BoolInputs with
  | .error e => throwError s!"f32 bool run failed: {repr e.cause}"
  | .ok report =>
      -- inputs preserved bit for bit, `0.25` still `0.25`.
      unless expect32 report.env "P" [1] #[1048576000] do
        throwError s!"f32 bool: predicate input P was coerced: {repr (bitsOf report.env "P")}"
      unless expect32 report.env "A" [1] #[1061158912] do
        throwError s!"f32 bool: real input A was altered: {repr (bitsOf report.env "A")}"
      -- and the Boolean DESTINATION carries the same non-binary value through, uncoerced.
      unless expect32 report.env "Q" [1] #[1048576000] do
        throwError s!"f32 bool: Boolean destination Q was coerced to a truth value: \
{repr (bitsOf report.env "Q")}"
      unless expect32 report.env "Y" [1] #[1061158912] do
        throwError s!"f32 bool: real destination Y wrong: {repr (bitsOf report.env "Y")}"
  match matDtypes prepared with
  | .error e => throwError s!"f32 bool: {e}"
  | .ok pairs =>
      unless pairs == #[("Q", ScalarDType.bool), ("Y", ScalarDType.f32)] do
        throwError s!"f32 bool materialized signatures wrong: {repr pairs}"

/-! ## Fixture 2.10 (f32 slice, Task 2): end-to-end witness (PLATFORM-DEPENDENT)

`DifferentialTest`'s `expOobProg` shape (`E[i] := exp(A[i + 1])`, `axis i : ℕ = 3`) as an f32
`tlprog!`, through the FULL named adapter pipeline (`prepare32`/`runPreparedDense32`), over
`Nonlin32Test`'s own platform witness lanes for `exp` at `A[1]`/`A[2]` (conflict-scan note C5: the
same lane list, not a hand-typed copy) — `A[3]` is out of range, so `E[2] = exp(+0) = 1` regardless
of platform. The assertion is RELATIONAL (the native `Float32.exp` applied directly to each input,
never a hardcoded bit pattern), and the precondition is the same one `Nonlin32Test.witness`
enforces: at least one lane must separate that native result from binary64-then-narrow, checked here
against the SAME three values through the ordinary binary64 named runner (`runPreparedDense`), or
this fixture could not tell the two apart. -/

def f32ExpOobProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  tensor f32 A(i), E(i)
  E[i] := exp(A[i + 1])
}

def f32ExpOobInputs : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "A"
    ⟨[3], #[Float32.ofBits 0, Float32.ofBits 1048801280, Float32.ofBits 1049583616]⟩

/-- The binary64 twin, same source values widened — used only to compute this fixture's
    narrowed-contrast precondition. `AdapterTest` has no `TLProgram`-to-`PreparedPlan` helper of its
    own either, so this follows its `warnProg` fixtures' inline `compileToScheduled`/`prepareEvalPlan`
    pattern rather than adding one. -/
def expOobProgF64 : TLProgram := tlprog!{
  axis i : ℕ = 3
  E[i] := exp(A[i + 1])
}

def expOobInputsF64 : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "A"
    ⟨[3], #[(0 : Float), (Float32.ofBits 1048801280).toFloat, (Float32.ofBits 1049583616).toFloat]⟩

run_cmd do
  let prepared ← match prepare32 f32ExpOobProg f32ExpOobInputs with
    | .ok p => pure p
    | .error e => throwError s!"f32 exp-oob: {e}"
  match runPreparedDense32 prepared f32ExpOobInputs with
  | .error e => throwError s!"f32 exp-oob run failed: {repr e.cause}"
  | .ok report =>
    match report.env["E"]? with
    | none => throwError "f32 exp-oob: E missing from result env"
    | some e32 =>
      let native : Array UInt32 :=
        #[ Float32.exp (Float32.ofBits 1048801280), Float32.exp (Float32.ofBits 1049583616)
         , Float32.exp (Float32.ofBits 0) ].map Float32.toBits
      unless e32.data.map Float32.toBits == native do
        throwError s!"f32 exp-oob: E is not the native binary32 exp applied directly: \
{repr (e32.data.map Float32.toBits)} vs {repr native}"
      -- the materialized dtype is `.f32`.
      match matDtypes prepared with
      | .error e => throwError s!"f32 exp-oob: {e}"
      | .ok pairs =>
          unless pairs == #[("E", ScalarDType.f32)] do
            throwError s!"f32 exp-oob materialized signatures wrong: {repr pairs}"
      -- Precondition: the binary64 twin, same values, through `runPreparedDense`, narrowed once —
      -- must disagree with the native result above in at least one lane.
      match expOobProgF64.compileToScheduled.run 0 with
      | .error e _ => throwError s!"f32 exp-oob: binary64 twin compile failed: {repr e}"
      | .ok sched _ =>
        match prepareEvalPlan sched (InputSignature.ofDenseInputs expOobInputsF64) with
        | .error f =>
            throwError s!"f32 exp-oob: binary64 twin prepare failed: {renderCompileCause f.cause}"
        | .ok prepared64 =>
          match runPreparedDense prepared64 expOobInputsF64 with
          | .error e => throwError s!"f32 exp-oob: binary64 twin run failed: {repr e.cause}"
          | .ok report64 =>
            match report64.env["E"]? with
            | none => throwError "f32 exp-oob: binary64 twin E missing"
            | some e64 =>
                let narrowed := e64.data.map (fun x => x.toFloat32.toBits)
                unless (List.range 3).any (fun i => native[i]! != narrowed[i]!) do
                  throwError s!"f32 exp-oob: no lane separates native binary32 exp from \
binary64-then-narrow on this platform's libm; choose new witness lanes (the fixture would \
otherwise pin nothing)"

/-! ## Fixture 2.11 (f32 slice, Task 2): end-to-end domain error, binary32 half

Fixture 2.10's donor with `log` in place of `exp` and `A = [1, 2, 4]` — every VALID lane is in
domain, so the failure is purely about the PADDED lane (`A[3]`, out of range, zero-pads to `+0`, and
`log(+0)` is a genuine domain violation). This is the first fixture anywhere to pin warnings on an
`.execution` failure: `AdapterTest`'s binary64 twin pins the same shape on the other carrier. -/

def f32LogDomainProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  tensor f32 A(i), E(i)
  E[i] := log(A[i + 1])
}

def f32LogDomainInputs : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "A" ⟨[3], #[(1.0 : Float32), 2.0, 4.0]⟩

run_cmd do
  let prepared ← match prepare32 f32LogDomainProg f32LogDomainInputs with
    | .ok p => pure p
    | .error e => throwError s!"f32 log-domain: {e}"
  -- The fixture's own teeth: a genuinely non-empty, single-entry warning list to preserve, not a
  -- vacuously-passing empty one.
  unless prepared.warnings.length == 1 do
    throwError s!"fixture is broken: expected exactly one preparation warning, got: \
{prepared.warnings.map toString}"
  match runPreparedDense32 prepared f32LogDomainInputs with
  | .ok _ => throwError "expected a binary32 domain-error failure"
  | .error failure =>
      unless failure.cause == .execution (.unaryDomain32 .log 0 0) do
        throwError s!"f32 log-domain: wrong cause: {repr failure.cause}"
      unless failure.warnings == prepared.warnings do
        throwError s!"f32 log-domain: warnings dropped/changed on an execution failure: \
{failure.warnings.map toString}"

end LeanNCD.Eval.Plan.Adapter32Test

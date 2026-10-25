import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter32
import Eval.Plan.ScanCompileTest   -- `scratchSched`: the donor for block-local scan scratch

/-!
# Additive collection through the CHECKED plan (slice 1, P2a)

`Eval/CollectEvalTest.lean` pins the multi-writer collection on the reference evaluator. This module
pins the same programs through `prepareEvalPlan` / `runPreparedDense` / `runPreparedDense32`:

* **Hiding (decision note §C.8).** The private per-writer tensors `Y#k` are published by the raw plan
  but are not persistent outputs: `materializedNames`, `materializedSignatures` and the
  `unpack`/`unpack32` result contain only public names, and the checked plan's reported environment
  equals the reference's.
* **B3 (decision note B3).** A supplied input that names a tensor the program defines is refused by
  `runPreparedDense`/`runPreparedDense32`/`unpack`/`unpack32` with
  `InputBindingError.inputIsDefined`, naming the same tensor the reference names as
  `EvalError.inputIsDefined`.

f32 is the DEFAULT dtype: plain `tensor` and undeclared names are binary32, `tensor f64` is the
explicit binary64 spelling, and the reference evaluator refuses f32 outright. So every fixture exists
twice: a binary64 version (declared `tensor f64` through `TLProgram.explicitF64`, compared
bit-for-bit with `evalScheduled`) and a binary32 version through `Adapter32`/`Dense32` (declared
`tensor f32`, and UNDECLARED, i.e. the default), whose expected bit patterns are observed from real
runs and never narrowed from binary64.
-/

namespace LeanNCD.Eval.Plan.CollectPlanTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

/-! ## Helpers -/

private def keysOf {α : Type} (env : HashMap String α) : List String :=
  (env.toList.map (·.1)).toArray.qsort (· < ·) |>.toList

private def sched64 (p : TLProgram) : Option ScheduledProgram :=
  match p.explicitF64.compileToScheduled.run 0 with
  | .ok s _ => some s
  | .error _ _ => none

private def sched32 (p : TLProgram) : Option ScheduledProgram :=
  match p.compileToScheduled.run 0 with
  | .ok s _ => some s
  | .error _ _ => none

private def prepared64 (p : TLProgram) (inputs : NamedDenseEnv) : Option PreparedPlan :=
  (sched64 p).bind fun s => (prepareEvalPlan s (InputSignature.ofDenseInputs inputs)).toOption

private def prepared32 (p : TLProgram) (inputs : NamedDenseEnv32) : Option PreparedPlan :=
  (sched32 p).bind fun s =>
    (InputSignature.ofDenseInputs32ForDecls s.decls inputs).toOption.bind fun sig =>
      (prepareEvalPlan s sig).toOption

private def plan64 (p : TLProgram) (inputs : NamedDenseEnv) : Option NamedDenseEnv :=
  (prepared64 p inputs).bind fun pp => (runPreparedDense pp inputs).toOption.map (·.env)

private def ref64 (p : TLProgram) (inputs : NamedDenseEnv) : Option NamedDenseEnv :=
  (sched64 p).bind fun s => (evalScheduled s inputs).toOption.map (·.env)

private def plan32 (p : TLProgram) (inputs : NamedDenseEnv32) : Option NamedDenseEnv32 :=
  (prepared32 p inputs).bind fun pp => (runPreparedDense32 pp inputs).toOption.map (·.env)

private def bits64 (env : Option NamedDenseEnv) (nm : String) : Option (Array UInt64) :=
  env.bind fun e => (e[nm]?).map fun t => t.data.map Float.toBits

private def bits32 (env : Option NamedDenseEnv32) (nm : String) : Option (Array UInt32) :=
  env.bind fun e => (e[nm]?).map fun t => t.data.map Float32.toBits

private def mk64 (xs : List (String × List Nat × Array Float)) : NamedDenseEnv :=
  xs.foldl (fun m (nm, sh, d) => m.insert nm ⟨sh, d⟩) {}

private def mk32 (xs : List (String × List Nat × Array Float32)) : NamedDenseEnv32 :=
  xs.foldl (fun m (nm, sh, d) => m.insert nm ⟨sh, d⟩) {}

private def f64bits (xs : Array Float) : Option (Array UInt64) := some (xs.map Float.toBits)
private def f32bits (xs : Array Float32) : Option (Array UInt32) := some (xs.map Float32.toBits)

private def matNames (p : Option PreparedPlan) : Option (Array String) :=
  p.map fun pp => pp.bindings.materializedNames.map (·.name)

/-! ## T1: hiding

### H1 (donor: `CollectEvalTest` V1, `Y:=A; Y:=B`)

Two writers of `Y`. Checked plan: `materializedNames = [Y]`, two hidden slots, env keys exactly
`[A, B, Y]`, `Y = A + B`. Accept-neighbour: H1s, the single-writer program, same keys, `Y = A`. -/

def h1 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Y[i] := B[i]
}
def h1s : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
}
private def h1In : NamedDenseEnv := mk64 [("A", [2], #[5.0, 9.0]), ("B", [2], #[2.0, 4.0])]

-- binary64 (explicitF64): plan and reference agree on keys and values.
#guard keysOf <$> plan64 h1 h1In == some ["A", "B", "Y"]
#guard bits64 (plan64 h1 h1In) "Y" == f64bits #[7.0, 13.0]
#guard (keysOf <$> plan64 h1 h1In) == (keysOf <$> ref64 h1 h1In)
#guard bits64 (plan64 h1 h1In) "Y" == bits64 (ref64 h1 h1In) "Y"
#guard matNames (prepared64 h1 h1In) == some #["Y"]
#guard (prepared64 h1 h1In).map (·.bindings.privateSlots.size) == some 2
-- accept-neighbour: one writer, same inventory, no hidden slot.
#guard keysOf <$> plan64 h1s h1In == some ["A", "B", "Y"]
#guard bits64 (plan64 h1s h1In) "Y" == f64bits #[5.0, 9.0]
#guard (prepared64 h1s h1In).map (·.bindings.privateSlots) == some #[]

/-- `h1` with `Y` declared `tensor f32` (the clone path) and with `Y` undeclared (the default). -/
def h1f32 : TLProgram := tlprog!{
  axis i : ℕ = 2
  tensor f32 A(i), B(i), Y(i)
  Y[i] := A[i]
  Y[i] := B[i]
}
private def h1In32 : NamedDenseEnv32 :=
  mk32 [("A", [2], #[5.0, 9.0]), ("B", [2], #[2.0, 4.0])]

-- binary32, declared: private names absent, one public Y, two hidden slots.
#guard keysOf <$> plan32 h1f32 h1In32 == some ["A", "B", "Y"]
#guard bits32 (plan32 h1f32 h1In32) "Y" == f32bits #[7.0, 13.0]
#guard matNames (prepared32 h1f32 h1In32) == some #["Y"]
#guard (prepared32 h1f32 h1In32).map (·.bindings.privateSlots.size) == some 2
-- binary32, undeclared (default f32): same.
#guard keysOf <$> plan32 h1 h1In32 == some ["A", "B", "Y"]
#guard bits32 (plan32 h1 h1In32) "Y" == f32bits #[7.0, 13.0]
#guard matNames (prepared32 h1 h1In32) == some #["Y"]
-- accept-neighbour (binary32): the single-writer program.
#guard keysOf <$> plan32 h1s h1In32 == some ["A", "B", "Y"]
#guard (prepared32 h1s h1In32).map (·.bindings.privateSlots) == some #[]

/-- The materialized SIGNATURE table lists only public names, in both precisions. -/
private def matDtypes (p : Option PreparedPlan) : Option (Array (String × ScalarDType)) :=
  p.bind fun pp => match pp.materializedSignatures with
    | .ok a => some (a.map fun e => (e.1, e.2.dtype))
    | .error _ => none
#guard matDtypes (prepared64 h1 h1In) == some #[("Y", .f64)]
#guard matDtypes (prepared32 h1f32 h1In32) == some #[("Y", .f32)]

/-- `unpack32` itself, fed the worker's positional result: private names are absent from its output. -/
private def unpack32Keys (p : TLProgram) (inputs : NamedDenseEnv32) : Option (List String) := do
  let pp ← prepared32 p inputs
  let packed ← (pack32 pp inputs).toOption
  let result ← (runDensePlan32 pp.plan packed).toOption
  let env ← (unpack32 pp inputs result).toOption
  return keysOf env
#guard unpack32Keys h1f32 h1In32 == some ["A", "B", "Y"]
#guard unpack32Keys h1 h1In32 == some ["A", "B", "Y"]

/-! ### H2 (donor: `CollectEvalTest` V5, non-integral three writers, order)

`Y := A; Y := B; Y := W` with `A = 0.1`, `B = 0.3`, `W = 0.4` on a one-element axis. The collector
folds the writers in SOURCE order, so the result is `(A + B) + W` and the reversed program gives
`(W + B) + A`. The three values were chosen so that the two orders differ in BOTH precisions. The
binary64 expected bits come from the reference evaluator on the same program; the binary32 bits are
observed from the checked plan (`Dense32`) and are not a narrowed binary64 result. -/

def h2 : TLProgram := tlprog!{
  axis i : ℕ = 1
  Y[i] := A[i]
  Y[i] := B[i]
  Y[i] := W[i]
}
def h2r : TLProgram := tlprog!{
  axis i : ℕ = 1
  Y[i] := W[i]
  Y[i] := B[i]
  Y[i] := A[i]
}
/-- `h2` with every name declared `tensor f32` (the clone path), beside the undeclared default. -/
def h2f32 : TLProgram := tlprog!{
  axis i : ℕ = 1
  tensor f32 A(i), B(i), W(i), Y(i)
  Y[i] := A[i]
  Y[i] := B[i]
  Y[i] := W[i]
}
private def h2In : NamedDenseEnv :=
  mk64 [("A", [1], #[0.1]), ("B", [1], #[0.3]), ("W", [1], #[0.4])]
private def h2In32 : NamedDenseEnv32 :=
  mk32 [("A", [1], #[0.1]), ("B", [1], #[0.3]), ("W", [1], #[0.4])]

#guard bits64 (plan64 h2 h2In) "Y" == bits64 (ref64 h2 h2In) "Y"
#guard bits64 (plan64 h2r h2In) "Y" == bits64 (ref64 h2r h2In) "Y"
#guard bits64 (plan64 h2 h2In) "Y" != bits64 (plan64 h2r h2In) "Y"
#guard bits64 (plan64 h2 h2In) "Y" == f64bits #[(0.1 + 0.3) + 0.4]
#guard bits32 (plan32 h2 h2In32) "Y" != bits32 (plan32 h2r h2In32) "Y"
-- Observed bit patterns (real runs): schedule order folds left, so reversing the writers changes the
-- last bit in both precisions. The f32 default (undeclared) schedule and the declared one agree.
#guard bits64 (plan64 h2 h2In) "Y" == some #[4605380978949069210]
#guard bits64 (plan64 h2r h2In) "Y" == some #[4605380978949069209]
#guard bits32 (plan32 h2 h2In32) "Y" == some #[1061997773]
#guard bits32 (plan32 h2r h2In32) "Y" == some #[1061997774]
#guard bits32 (plan32 h2f32 h2In32) "Y" == some #[1061997773]

/-! ### H3 (donor: `CollectEvalTest` V4, predicate OR)

`predicate R(i); R := A; R := B`. The collector of a predicate `R` is an OR (`Combine.bool` through
`R`'s own declaration), not a sum and not a count. Binary64 compares with the reference; the binary32
version runs on an f32 schedule (`A`, `B` undeclared, i.e. the default dtype) where the predicate is
storage-neutral and its private clones are predicates too. Accept-neighbour: the single writer. -/

def h3 : TLProgram := tlprog!{
  axis i : ℕ = 2
  predicate R(i)
  R[i] := A[i]
  R[i] := B[i]
}
def h3s : TLProgram := tlprog!{
  axis i : ℕ = 2
  predicate R(i)
  R[i] := A[i]
}
private def h3In : NamedDenseEnv := mk64 [("A", [2], #[1.0, 0.0]), ("B", [2], #[1.0, 1.0])]
private def h3In32 : NamedDenseEnv32 := mk32 [("A", [2], #[1.0, 0.0]), ("B", [2], #[1.0, 1.0])]

#guard bits64 (plan64 h3 h3In) "R" == bits64 (ref64 h3 h3In) "R"
#guard bits64 (plan64 h3 h3In) "R" == f64bits #[1.0, 1.0]
#guard keysOf <$> plan64 h3 h3In == some ["A", "B", "R"]
#guard matDtypes (prepared64 h3 h3In) == some #[("R", .bool)]
#guard bits64 (plan64 h3s h3In) "R" == f64bits #[1.0, 0.0]
#guard bits32 (plan32 h3 h3In32) "R" == f32bits #[1.0, 1.0]
#guard keysOf <$> plan32 h3 h3In32 == some ["A", "B", "R"]
#guard matDtypes (prepared32 h3 h3In32) == some #[("R", .bool)]
#guard bits32 (plan32 h3s h3In32) "R" == f32bits #[1.0, 0.0]

/-! ### H4: no `mixedStorageKinds` from `T#k`

`tensor f64 Y(i)` / `tensor f32 Y(i)` with two writers: the private clones `Y#1`, `Y#2` carry `Y`'s
element type, so the schedule stays homogeneous and PREPARES. A clone left undeclared would default
to f32 and make the f64 schedule mixed (rejected `unsupportedDtype ... mixed f32/f64`), which is what
the f64 version below discriminates; the f32 version holds for the default-f32 reason either way, so
its discriminating mutation changes the clone's element type instead. -/

def h4f64 : TLProgram := tlprog!{
  axis i : ℕ = 2
  tensor f64 A(i), B(i), Y(i)
  Y[i] := A[i]
  Y[i] := B[i]
}
#guard (prepared64 h4f64 h1In).isSome
#guard bits64 (plan64 h4f64 h1In) "Y" == f64bits #[7.0, 13.0]
#guard (prepared32 h1f32 h1In32).isSome

/-! ## T2: B3 on the checked side

A supplied input naming a tensor the program defines is refused by BOTH backends with the same name:
the reference as `EvalError.inputIsDefined`, the checked plan as `InputBindingError.inputIsDefined`
(through `runPreparedDense`/`runPreparedDense32`, wrapped `.binding`, and through a direct
`unpack`/`unpack32`, wrapped `.binding` into `PlanRunCause`). The first defined name in the
schedule's write order is reported by both, including the private `Y#k`. Block-local scan scratch
counts as defined too (`ScanStmt.writes`). Unrelated extra inputs still pass through unchanged. -/

/-- The name the reference refuses, if it refuses with `inputIsDefined`. -/
private def refDefined (s : ScheduledProgram) (supplied : NamedDenseEnv) : Option String :=
  match evalScheduled s supplied with
  | .error { error := .inputIsDefined nm, .. } => some nm
  | _ => none

private def prepS64 (s : ScheduledProgram) (clean : NamedDenseEnv) : Option PreparedPlan :=
  (prepareEvalPlan s (InputSignature.ofDenseInputs clean)).toOption

private def prepS32 (s : ScheduledProgram) (clean : NamedDenseEnv32) : Option PreparedPlan :=
  (InputSignature.ofDenseInputs32ForDecls s.decls clean).toOption.bind fun sig =>
    (prepareEvalPlan s sig).toOption

/-- The name the checked plan refuses through `runPreparedDense`. -/
private def runDefined64 (pp : PreparedPlan) (supplied : NamedDenseEnv) : Option String :=
  match runPreparedDense pp supplied with
  | .error { cause := .binding (.inputIsDefined nm), .. } => some nm
  | _ => none

/-- ... and through a direct `unpack` (any positional store: the check precedes the arity check). -/
private def unpackDefined64 (pp : PreparedPlan) (supplied : NamedDenseEnv) : Option String :=
  match unpack pp supplied #[] with
  | .error (.binding (.inputIsDefined nm)) => some nm
  | _ => none

/-- ... and through a direct `pack` (the pack door is guarded on its own: through the runner the
    unpack door would report the same cause, so only a direct call pins this guard). -/
private def packDefined64 (pp : PreparedPlan) (supplied : NamedDenseEnv) : Option String :=
  match pack pp supplied with
  | .error (.inputIsDefined nm) => some nm
  | _ => none

private def packDefined32 (pp : PreparedPlan) (supplied : NamedDenseEnv32) : Option String :=
  match pack32 pp supplied with
  | .error (.inputIsDefined nm) => some nm
  | _ => none

private def runDefined32 (pp : PreparedPlan) (supplied : NamedDenseEnv32) : Option String :=
  match runPreparedDense32 pp supplied with
  | .error { cause := .binding (.inputIsDefined nm), .. } => some nm
  | _ => none

private def unpackDefined32 (pp : PreparedPlan) (supplied : NamedDenseEnv32) : Option String :=
  match unpack32 pp supplied #[] with
  | .error (.binding (.inputIsDefined nm)) => some nm
  | _ => none

/-- The four binary64 observers of one (program, supplied-environment) pair, as a tuple:
    reference, `runPreparedDense`, `unpack`, `pack`. -/
private def verdict64 (s : ScheduledProgram) (clean supplied : NamedDenseEnv) :
    Option (Option String × Option String × Option String × Option String) :=
  (prepS64 s clean).map fun pp =>
    (refDefined s supplied, runDefined64 pp supplied, unpackDefined64 pp supplied, packDefined64 pp supplied)

/-- The three binary32 observers: `runPreparedDense32`, `unpack32`, `pack32`. -/
private def verdict32 (s : ScheduledProgram) (clean supplied : NamedDenseEnv32) :
    Option (Option String × Option String × Option String) :=
  (prepS32 s clean).map fun pp =>
    (runDefined32 pp supplied, unpackDefined32 pp supplied, packDefined32 pp supplied)

private def s1 : Option ScheduledProgram := sched64 h1s    -- `Y := A`, single writer
private def s1m : Option ScheduledProgram := sched64 h1   -- `Y := A; Y := B`, two writers
private def s1_32 : Option ScheduledProgram := sched32 h1s
private def s1m_32 : Option ScheduledProgram := sched32 h1

private def yIn : NamedDenseEnv := h1In.insert "Y" ⟨[2], #[7.0, 7.0]⟩
private def y1In : NamedDenseEnv := h1In.insert "Y#1" ⟨[2], #[7.0, 7.0]⟩
private def yy1In : NamedDenseEnv := yIn.insert "Y#1" ⟨[2], #[7.0, 7.0]⟩
private def yIn32 : NamedDenseEnv32 := h1In32.insert "Y" ⟨[2], #[7.0, 7.0]⟩
private def y1In32 : NamedDenseEnv32 := h1In32.insert "Y#1" ⟨[2], #[7.0, 7.0]⟩
private def yy1In32 : NamedDenseEnv32 := yIn32.insert "Y#1" ⟨[2], #[7.0, 7.0]⟩

-- B3.1 (donor: `CollectEvalTest` J5): single writer, supplied `Y`; all three observers name `Y`.
#guard s1.bind (verdict64 · h1In yIn) == some (some "Y", some "Y", some "Y", some "Y")
-- B3.1 accept-neighbour: the same program without the supplied `Y`, and with an unrelated extra input.
#guard s1.bind (verdict64 · h1In h1In) == some (none, none, none, none)
#guard s1.bind (verdict64 · h1In (h1In.insert "Unused" ⟨[1], #[7.0]⟩)) == some (none, none, none, none)
-- B3.1 f32 (undeclared = default f32, and declared f32): the checked plan names `Y` too.
#guard s1_32.bind (verdict32 · h1In32 yIn32) == some (some "Y", some "Y", some "Y")
#guard s1_32.bind (verdict32 · h1In32 h1In32) == some (none, none, none)
#guard s1_32.bind (verdict32 · h1In32 (h1In32.insert "Unused" ⟨[1], #[7.0]⟩)) == some (none, none, none)
#guard (sched32 h1f32).bind (verdict32 · h1In32 yIn32) == some (some "Y", some "Y", some "Y")

-- B3.2 (clone B3.1, two writers): a supplied `Y#1` is refused by name; with `Y` also supplied the FIRST
-- defined name in write order wins, on every observer.
#guard s1m.bind (verdict64 · h1In yIn) == some (some "Y", some "Y", some "Y", some "Y")
#guard s1m.bind (verdict64 · h1In y1In) == some (some "Y#1", some "Y#1", some "Y#1", some "Y#1")
#guard s1m.bind (verdict64 · h1In yy1In) == some (some "Y#1", some "Y#1", some "Y#1", some "Y#1")
#guard s1m.bind (verdict64 · h1In h1In) == some (none, none, none, none)
#guard s1m_32.bind (verdict32 · h1In32 yIn32) == some (some "Y", some "Y", some "Y")
#guard s1m_32.bind (verdict32 · h1In32 y1In32) == some (some "Y#1", some "Y#1", some "Y#1")
#guard s1m_32.bind (verdict32 · h1In32 yy1In32) == some (some "Y#1", some "Y#1", some "Y#1")
#guard s1m_32.bind (verdict32 · h1In32 h1In32) == some (none, none, none)

-- B3.3 (donor: `ScanCompileTest.scratchSched`): block-local scan scratch `T` counts as defined on both
-- backends, although it is not a persistent output.
private def scratchS64 : ScheduledProgram :=
  Eval.Plan.ScanCompileTest.explicitF64Sched Eval.Plan.ScanCompileTest.scratchSched
private def scratchIn : NamedDenseEnv := Eval.Plan.ScanCompileTest.scratchInputs
private def scratchIn32 : NamedDenseEnv32 :=
  mk32 [("S0", [], #[1.0]), ("K", [3], #[2.0, 3.0, 4.0])]
#guard verdict64 scratchS64 scratchIn (scratchIn.insert "T" ⟨[], #[9.0]⟩) ==
  some (some "T", some "T", some "T", some "T")
#guard verdict64 scratchS64 scratchIn scratchIn == some (none, none, none, none)
#guard verdict32 Eval.Plan.ScanCompileTest.scratchSched scratchIn32
    (scratchIn32.insert "T" ⟨[], #[9.0]⟩) == some (some "T", some "T", some "T")
#guard verdict32 Eval.Plan.ScanCompileTest.scratchSched scratchIn32 scratchIn32 == some (none, none, none)

/-! ## B3 prepare-time half: a SIGNATURE entry naming a defined tensor

`prepareEvalPlan` refuses with `InputSignatureError.definedName`, over the SAME defined-name set as
the run-time refusals above (the collected schedule's writes: public outputs, private `T#k`
clones, scan scratch), BEFORE the required-input checks, reporting the first offender in write
order. `prepOutcome` tags the verdict so `definedName` is told apart from `missingSignature`. -/

private def prepOutcome (r : Except PlanCompileFailure PreparedPlan) : String :=
  match r with
  | .ok _ => "ok"
  | .error e =>
      match e.cause with
      | .inputSignature (.definedName n) => s!"defined:{n}"
      | .inputSignature (.missingSignature n) => s!"missing:{n}"
      | _ => "other"

private def out64 (s : ScheduledProgram) (env : NamedDenseEnv) : String :=
  prepOutcome (prepareEvalPlan s (InputSignature.ofDenseInputs env))

private def out32 (s : ScheduledProgram) (env : NamedDenseEnv32) : String :=
  match InputSignature.ofDenseInputs32ForDecls s.decls env with
  | .ok sig => prepOutcome (prepareEvalPlan s sig)
  | .error _ => "sigbuild"

-- Fixture 3 (private clone): `h1` has two writers of `Y`, so `Y#1` is a private clone. Naming it in the
-- signature is refused by name; accept-neighbour: h1's own (clean) signature.
#guard s1m.map (out64 · y1In) == some "defined:Y#1"
#guard s1m.map (out64 · h1In) == some "ok"
#guard s1m_32.map (out32 · y1In32) == some "defined:Y#1"
#guard s1m_32.map (out32 · h1In32) == some "ok"
-- The public output beside the clone: the FIRST defined name in write order (`Y#1`, as at run time).
#guard s1m.map (out64 · yy1In) == some "defined:Y#1"
#guard s1m_32.map (out32 · yy1In32) == some "defined:Y#1"
-- Single writer (no clone): the public output alone is refused; accept-neighbour as above.
#guard s1.map (out64 · yIn) == some "defined:Y"
#guard s1.map (out64 · h1In) == some "ok"

-- Fixture 4 (scan scratch): `T` is written only inside the scan body, never a persistent output.
#guard out64 scratchS64 (scratchIn.insert "T" ⟨[], #[9.0]⟩) == "defined:T"
#guard out64 scratchS64 scratchIn == "ok"
#guard out32 Eval.Plan.ScanCompileTest.scratchSched (scratchIn32.insert "T" ⟨[], #[9.0]⟩) == "defined:T"
#guard out32 Eval.Plan.ScanCompileTest.scratchSched scratchIn32 == "ok"

/-! ## Declared-f32 variants (review T5-F4)

`h3d32`: H3's predicate OR on a schedule whose surrounding real tensors are declared `tensor f32`
(the predicate itself is storage-neutral). The overlapping inputs separate OR (`[1,1]`) from a count
(`[2,1]`). Accept-neighbour: the single writer. `b32d32`: B3.2 on the declared-f32 CLONE path, i.e.
a supplied private `Y#1` (and `Y#1` beside `Y`) refused by name, with the clean-input accept-neighbour. -/

def h3d32 : TLProgram := tlprog!{
  axis i : ℕ = 2
  tensor f32 A(i), B(i)
  predicate R(i)
  R[i] := A[i]
  R[i] := B[i]
}
def h3d32s : TLProgram := tlprog!{
  axis i : ℕ = 2
  tensor f32 A(i), B(i)
  predicate R(i)
  R[i] := A[i]
}
#guard bits32 (plan32 h3d32 h3In32) "R" == f32bits #[1.0, 1.0]
#guard keysOf <$> plan32 h3d32 h3In32 == some ["A", "B", "R"]
#guard matDtypes (prepared32 h3d32 h3In32) == some #[("R", .bool)]
#guard bits32 (plan32 h3d32s h3In32) "R" == f32bits #[1.0, 0.0]

#guard (sched32 h1f32).bind (verdict32 · h1In32 y1In32) == some (some "Y#1", some "Y#1", some "Y#1")
#guard (sched32 h1f32).bind (verdict32 · h1In32 yy1In32) == some (some "Y#1", some "Y#1", some "Y#1")
#guard (sched32 h1f32).bind (verdict32 · h1In32 h1In32) == some (none, none, none)

/-! ## Mixed-storage diagnostic names the public tensor (final review B-F2)

f64 inputs with `Y` left undeclared (f32 by default) make the schedule mixed f32/f64. Step 0b's
first conflicting used name is then the private clone `Y#1`; the error must name `Y`, as the
reference evaluator's f32 refusal does (`collectorOwner`). Accept-neighbour: every tensor declared
`f64` prepares. A declared `tensor f32 Y(i)` beside f64 inputs is the same mixed schedule. -/

/-- The `unsupportedDtype` text `prepareEvalPlan` reports (checked), if it refuses that way. -/
private def prepDtypeErr (s : ScheduledProgram) (inputs : NamedDenseEnv) : Option String :=
  match prepareEvalPlan s (InputSignature.ofDenseInputs inputs) with
  | .error { cause := .capability (.unsupportedDtype m), .. } => some m
  | _ => none

def mixedUndeclY : TLProgram := tlprog!{
  axis i : ℕ = 2
  tensor f64 A(i), B(i)
  Y[i] := A[i]
  Y[i] := B[i]
}
def mixedDeclF32Y : TLProgram := tlprog!{
  axis i : ℕ = 2
  tensor f64 A(i), B(i)
  tensor f32 Y(i)
  Y[i] := A[i]
  Y[i] := B[i]
}
#guard (sched32 mixedUndeclY).bind (prepDtypeErr · h1In) == some "Y: mixed f32/f64 storage in one schedule"
#guard (sched32 mixedDeclF32Y).bind (prepDtypeErr · h1In) == some "Y: mixed f32/f64 storage in one schedule"
#guard (sched32 h4f64).bind (prepDtypeErr · h1In) == none
#guard ((sched32 h4f64).bind fun s => (prepareEvalPlan s (InputSignature.ofDenseInputs h1In)).toOption).isSome

/-! ## S3b-ii T2: tropical (all-max / all-min) multi-writer collection

A tensor written only by `maxreduce` (resp. `minreduce`) statements collects with max (min), not
sum, through the reference evaluator, the checked plan on binary64 and the checked plan on binary32.
The data is chosen so that the wrong collector (sum) and the wrong `0` pad each change the result:
the max groups hold NEGATIVE values (a sum is more negative, a `0` pad beats every cell), the min
groups POSITIVE ones. A sort-neutral copy writer (`Y[i] := A[i + 1]`, sum-annotated) beside a
non-neutral writer abstains and is evaluated in the group's sort, so its out-of-range read (`i = 2`
of a 3-element `A`) pads `-inf` (max) / `+inf` (min), not `0`. Every expected value was observed from
a run, binary32 bits included. -/

private def pinf : Float := 1.0 / 0.0
private def pinf32 : Float32 := 1.0 / 0.0

def tmax : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := maxreduce(A[i, j])
  Y[i] := maxreduce(B[i, j])
}
def tmin : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := minreduce(A[i, j])
  Y[i] := minreduce(B[i, j])
}
def tmax32 : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  tensor f32 A(i, j), B(i, j), Y(i)
  Y[i] := maxreduce(A[i, j])
  Y[i] := maxreduce(B[i, j])
}
private def tmaxIn : NamedDenseEnv :=
  mk64 [("A", [2, 2], #[-5.0, -2.0, -7.0, -4.0]), ("B", [2, 2], #[-9.0, -6.0, -3.0, -8.0])]
private def tmaxIn32 : NamedDenseEnv32 :=
  mk32 [("A", [2, 2], #[-5.0, -2.0, -7.0, -4.0]), ("B", [2, 2], #[-9.0, -6.0, -3.0, -8.0])]
private def tminIn : NamedDenseEnv :=
  mk64 [("A", [2, 2], #[5.0, 2.0, 7.0, 4.0]), ("B", [2, 2], #[9.0, 6.0, 3.0, 8.0])]
private def tminIn32 : NamedDenseEnv32 :=
  mk32 [("A", [2, 2], #[5.0, 2.0, 7.0, 4.0]), ("B", [2, 2], #[9.0, 6.0, 3.0, 8.0])]

-- max group: Y = [max(-2,-6), max(-4,-3)] = [-2, -3]  (sum collector: [-8, -7])
#guard bits64 (ref64 tmax tmaxIn) "Y" == f64bits #[-2.0, -3.0]
#guard bits64 (plan64 tmax tmaxIn) "Y" == f64bits #[-2.0, -3.0]
#guard bits32 (plan32 tmax tmaxIn32) "Y" == f32bits #[-2.0, -3.0]
#guard bits32 (plan32 tmax32 tmaxIn32) "Y" == f32bits #[-2.0, -3.0]
-- min group: Y = [min(2,6), min(4,3)] = [2, 3]  (sum collector: [8, 7])
#guard bits64 (ref64 tmin tminIn) "Y" == f64bits #[2.0, 3.0]
#guard bits64 (plan64 tmin tminIn) "Y" == f64bits #[2.0, 3.0]
#guard bits32 (plan32 tmin tminIn32) "Y" == f32bits #[2.0, 3.0]
-- the private clones stay hidden and the public inventory is unchanged
#guard keysOf <$> plan64 tmax tmaxIn == some ["A", "B", "Y"]
#guard keysOf <$> plan32 tmax32 tmaxIn32 == some ["A", "B", "Y"]

/-- Neutral copy beside a non-neutral writer, both orders: the copy abstains (its `sum` annotation
    does not make the group real) and is rewritten to the group's sort. -/
def tpadMax : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := maxreduce(B[i, j])
  Y[i] := A[i + 1]
}
def tpadMaxR : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[i + 1]
  Y[i] := maxreduce(B[i, j])
}
def tpadMin : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := minreduce(B[i, j])
  Y[i] := A[i + 1]
}
private def tpadMaxIn : NamedDenseEnv :=
  mk64 [("A", [3], #[-10.0, -1.0, -8.0]), ("B", [3, 2], #[-5.0, -2.0, -7.0, -4.0, -9.0, -6.0])]
private def tpadMaxIn32 : NamedDenseEnv32 :=
  mk32 [("A", [3], #[-10.0, -1.0, -8.0]), ("B", [3, 2], #[-5.0, -2.0, -7.0, -4.0, -9.0, -6.0])]
private def tpadMinIn : NamedDenseEnv :=
  mk64 [("A", [3], #[10.0, 1.0, 8.0]), ("B", [3, 2], #[5.0, 2.0, 7.0, 4.0, 9.0, 6.0])]
private def tpadMinIn32 : NamedDenseEnv32 :=
  mk32 [("A", [3], #[10.0, 1.0, 8.0]), ("B", [3, 2], #[5.0, 2.0, 7.0, 4.0, 9.0, 6.0])]

-- max: Y = [max(-2, A[1]=-1), max(-4, A[2]=-8), max(-6, pad)] = [-1, -4, -6] (a 0 pad gives 0 last)
#guard bits64 (ref64 tpadMax tpadMaxIn) "Y" == f64bits #[-1.0, -4.0, -6.0]
#guard bits64 (plan64 tpadMax tpadMaxIn) "Y" == f64bits #[-1.0, -4.0, -6.0]
#guard bits32 (plan32 tpadMax tpadMaxIn32) "Y" == f32bits #[-1.0, -4.0, -6.0]
#guard bits64 (ref64 tpadMaxR tpadMaxIn) "Y" == f64bits #[-1.0, -4.0, -6.0]
#guard bits64 (plan64 tpadMaxR tpadMaxIn) "Y" == f64bits #[-1.0, -4.0, -6.0]
#guard bits32 (plan32 tpadMaxR tpadMaxIn32) "Y" == f32bits #[-1.0, -4.0, -6.0]
-- min: Y = [min(2, 1), min(4, 8), min(6, pad)] = [1, 4, 6] (a 0 pad gives 0 last)
#guard bits64 (ref64 tpadMin tpadMinIn) "Y" == f64bits #[1.0, 4.0, 6.0]
#guard bits64 (plan64 tpadMin tpadMinIn) "Y" == f64bits #[1.0, 4.0, 6.0]
#guard bits32 (plan32 tpadMin tpadMinIn32) "Y" == f32bits #[1.0, 4.0, 6.0]

/-- All-neutral group: the `maxreduce` copy votes `max`, the sum copy abstains and is rewritten, so
    the cell no writer reads is `0_K` itself: `-inf` (max) / `+inf` (min), observable directly. -/
def tinfMax : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := maxreduce(A[i + 1])
  Y[i] := B[i + 1]
}
def tinfMin : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := minreduce(A[i + 1])
  Y[i] := B[i + 1]
}
private def tinfIn : NamedDenseEnv :=
  mk64 [("A", [3], #[-10.0, -1.0, -8.0]), ("B", [3], #[-20.0, -30.0, -40.0])]
private def tinfIn32 : NamedDenseEnv32 :=
  mk32 [("A", [3], #[-10.0, -1.0, -8.0]), ("B", [3], #[-20.0, -30.0, -40.0])]
private def tinfMinIn : NamedDenseEnv :=
  mk64 [("A", [3], #[10.0, 1.0, 8.0]), ("B", [3], #[20.0, 30.0, 40.0])]
private def tinfMinIn32 : NamedDenseEnv32 :=
  mk32 [("A", [3], #[10.0, 1.0, 8.0]), ("B", [3], #[20.0, 30.0, 40.0])]
-- max: [max(-1,-30), max(-8,-40), -inf]; min: [min(1,30), min(8,40), +inf]
#guard bits64 (ref64 tinfMax tinfIn) "Y" == f64bits #[-1.0, -8.0, -pinf]
#guard bits64 (plan64 tinfMax tinfIn) "Y" == f64bits #[-1.0, -8.0, -pinf]
#guard bits32 (plan32 tinfMax tinfIn32) "Y" == f32bits #[-1.0, -8.0, -pinf32]
#guard bits64 (ref64 tinfMin tinfMinIn) "Y" == f64bits #[1.0, 8.0, pinf]
#guard bits64 (plan64 tinfMin tinfMinIn) "Y" == f64bits #[1.0, 8.0, pinf]
#guard bits32 (plan32 tinfMin tinfMinIn32) "Y" == f32bits #[1.0, 8.0, pinf32]

/-- The Bellman shape: a sum-annotated NEUTRAL copy beside a `maxreduce` (resp. `minreduce`) writer
    abstains and collects with max (min). Sum would give `[-3, -13]` (resp. `[6, 13]`). -/
def tcopyMax : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := maxreduce(B[i, j])
  Y[i] := A[i]
}
def tcopyMin : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := minreduce(B[i, j])
  Y[i] := A[i]
}
private def tcopyMaxIn : NamedDenseEnv :=
  mk64 [("A", [2], #[-1.0, -9.0]), ("B", [2, 2], #[-5.0, -2.0, -7.0, -4.0])]
private def tcopyMaxIn32 : NamedDenseEnv32 :=
  mk32 [("A", [2], #[-1.0, -9.0]), ("B", [2, 2], #[-5.0, -2.0, -7.0, -4.0])]
private def tcopyMinIn : NamedDenseEnv :=
  mk64 [("A", [2], #[1.0, 9.0]), ("B", [2, 2], #[5.0, 2.0, 7.0, 4.0])]
private def tcopyMinIn32 : NamedDenseEnv32 :=
  mk32 [("A", [2], #[1.0, 9.0]), ("B", [2, 2], #[5.0, 2.0, 7.0, 4.0])]
#guard bits64 (ref64 tcopyMax tcopyMaxIn) "Y" == f64bits #[-1.0, -4.0]
#guard bits64 (plan64 tcopyMax tcopyMaxIn) "Y" == f64bits #[-1.0, -4.0]
#guard bits32 (plan32 tcopyMax tcopyMaxIn32) "Y" == f32bits #[-1.0, -4.0]
#guard bits64 (ref64 tcopyMin tcopyMinIn) "Y" == f64bits #[1.0, 4.0]
#guard bits64 (plan64 tcopyMin tcopyMinIn) "Y" == f64bits #[1.0, 4.0]
#guard bits32 (plan32 tcopyMin tcopyMinIn32) "Y" == f32bits #[1.0, 4.0]


/-! ## S3b-ii T4: the Bellman target programs and their neighbours

Value iteration (max-plus) and shortest paths (min-plus) written as SEPARATE statements of one
tensor, the form the user wants: a `maxreduce`/`minreduce` writer plus a terminal / source-init writer,
which is either a `maxreduce` of the terminal vector or a bare sum-annotated COPY of it (the copy
abstains and collects in the group's sort). Each program is compared on the reference evaluator, the
checked plan on binary64 and the checked plan on binary32; every expected value was observed from a
run and equals the hand value of the audit (P1 `[5,3]`, P2 `[22,100]`, P3 `[2,1]`). The one-statement
forms (P5) give the same values, which pins that the multi-writer and single-statement spellings
agree. Undeclared tensors are the default `f32` on the binary32 leg; `belP1d` declares them. -/

private def ninf : Float := -(1.0 / 0.0)
private def ninf32 : Float32 := -(1.0 / 0.0)

private def dat64 (env : Option NamedDenseEnv) (nm : String) : Option (Array Float) :=
  env.bind fun e => (e[nm]?).map (·.data)
private def dat32 (env : Option NamedDenseEnv32) (nm : String) : Option (Array Float32) :=
  env.bind fun e => (e[nm]?).map (·.data)

/-- the three backends' values of `nm` -/
private def obs (p : TLProgram) (i : NamedDenseEnv) (i32 : NamedDenseEnv32) (nm : String) :
    Option (Array Float) × Option (Array Float) × Option (Array Float32) :=
  (dat64 (ref64 p i) nm, dat64 (plan64 p i) nm, dat32 (plan32 p i32) nm)

private def compErr (p : TLProgram) : Option CompileError :=
  match p.compileToScheduled.run 0 with | .error e _ => some e | .ok _ _ => none
private def refErr64 (p : TLProgram) (i : NamedDenseEnv) : Option CompileError :=
  (sched64 p).bind fun s => match evalScheduled s i with
    | .error f => (match f.error with | .compile c => some c | _ => none) | .ok _ => none
private def srcErr : Option PlanCompileCause → Option CompileError
  | some (.sourceInvariant c) => some c | _ => none
private def planCause64 (p : TLProgram) (i : NamedDenseEnv) : Option PlanCompileCause :=
  (sched64 p).bind fun s => match prepareEvalPlan s (InputSignature.ofDenseInputs i) with
    | .error f => some f.cause | .ok _ => none
private def planCause32 (p : TLProgram) (i : NamedDenseEnv32) : Option PlanCompileCause :=
  (sched32 p).bind fun s => (InputSignature.ofDenseInputs32ForDecls s.decls i).toOption.bind fun sig =>
    match prepareEvalPlan s sig with | .error f => some f.cause | .ok _ => none

def belP1 : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  Vn[s] := maxreduce(Q[s, a])
  Vn[s] := maxreduce(Term[s])
}
def belP1c : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  Vn[s] := maxreduce(Q[s, a])
  Vn[s] := Term[s]
}
def belP5 : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  Vn[s] := maxreduce(Q[s, a] + Term[s])
}
def belP1d : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  tensor f32 Q(s, a), Term(s), Vn(s)
  Vn[s] := maxreduce(Q[s, a])
  Vn[s] := Term[s]
}
def belP2 : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  axis t : ℕ = 2
  Vn[s] := maxreduce(R[s, a] · Tr[s, a, t] · V[t])
  Vn[s] := maxreduce(Term[s])
}
def belP2c : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  axis t : ℕ = 2
  Vn[s] := maxreduce(R[s, a] · Tr[s, a, t] · V[t])
  Vn[s] := Term[s]
}
def belP3 : TLProgram := tlprog!{
  axis u : ℕ = 2
  axis v : ℕ = 2
  D[v] := minreduce(W[u, v] · D0[u])
  D[v] := minreduce(S[v])
}
def belP3c : TLProgram := tlprog!{
  axis u : ℕ = 2
  axis v : ℕ = 2
  D[v] := minreduce(W[u, v] · D0[u])
  D[v] := S[v]
}
def belP5m : TLProgram := tlprog!{
  axis u : ℕ = 2
  axis v : ℕ = 2
  D[v] := minreduce(W[u, v] · D0[u] + S[v])
}
private def belIn : NamedDenseEnv :=
  mk64 [("Q", [2, 2], #[1.0, 5.0, 2.0, 3.0]), ("Term", [2], #[4.0, 1.0])]
private def belIn32 : NamedDenseEnv32 :=
  mk32 [("Q", [2, 2], #[1.0, 5.0, 2.0, 3.0]), ("Term", [2], #[4.0, 1.0])]
private def bel2In : NamedDenseEnv :=
  mk64 [("R", [2, 2], #[1.0, 2.0, 0.0, 3.0]), ("V", [2], #[10.0, 20.0]), ("Term", [2], #[5.0, 100.0]),
        ("Tr", [2, 2, 2], #[0.0, ninf, ninf, 0.0, 0.0, ninf, ninf, 0.0])]
private def bel2In32 : NamedDenseEnv32 :=
  mk32 [("R", [2, 2], #[1.0, 2.0, 0.0, 3.0]), ("V", [2], #[10.0, 20.0]), ("Term", [2], #[5.0, 100.0]),
        ("Tr", [2, 2, 2], #[0.0, ninf32, ninf32, 0.0, 0.0, ninf32, ninf32, 0.0])]
private def bel3In : NamedDenseEnv :=
  mk64 [("W", [2, 2], #[0.0, 4.0, 1.0, 0.0]), ("D0", [2], #[3.0, 1.0]), ("S", [2], #[2.0, 9.0])]
private def bel3In32 : NamedDenseEnv32 :=
  mk32 [("W", [2, 2], #[0.0, 4.0, 1.0, 0.0]), ("D0", [2], #[3.0, 1.0]), ("S", [2], #[2.0, 9.0])]


def nbMM : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := maxreduce(A[i, j])
  Y[i] := minreduce(B[i, j])
}
def nbMMr : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := minreduce(A[i, j])
  Y[i] := maxreduce(B[i, j])
}
def nbSM : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i, j]
  Y[i] := maxreduce(B[i, j])
}
def nbMS : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := maxreduce(B[i, j])
  Y[i] := A[i, j]
}
def nbScat : TLProgram := tlprog!{
  axis i : ℕ = 2
  S[2*i] := maxreduce(X[i])
  S[2*i + 1] := maxreduce(Y[i])
}
def nbScan : TLProgram := tlprog!{
  iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := maxreduce(S[j, l] · A[j, k])
  S[j, l] := maxreduce(Y[j, l])
}
def rdBool : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  predicate B(s)
  Vn[s] := maxreduce(Q[s, a])
  Vn[s] := Term[s]
  B[s] := Vn[s]
}
def rdMin : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  Vn[s] := maxreduce(Q[s, a])
  Vn[s] := Term[s]
  Z[s] := minreduce(Vn[s])
}
def rdMax : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  Vn[s] := maxreduce(Q[s, a])
  Vn[s] := Term[s]
  Z[s] := maxreduce(Vn[s])
}
def rdReal : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  Vn[s] := maxreduce(Q[s, a])
  Tot[] := Vn[s]
  Vn[s] := Term[s]
}
private def abIn : NamedDenseEnv :=
  mk64 [("A", [2, 2], #[1.0, 2.0, 3.0, 4.0]), ("B", [2, 2], #[5.0, 6.0, 7.0, 8.0])]
private def rdIn : NamedDenseEnv :=
  mk64 [("Q", [2, 2], #[1.0, 5.0, 2.0, 3.0]), ("Term", [2], #[9.0, 1.0])]
private def rdIn32 : NamedDenseEnv32 :=
  mk32 [("Q", [2, 2], #[1.0, 5.0, 2.0, 3.0]), ("Term", [2], #[9.0, 1.0])]


/-- All three backends hold exactly `xs` (binary64 expectation) / `xs32` (binary32, observed) in `nm`. -/
private def agree (p : TLProgram) (i : NamedDenseEnv) (i32 : NamedDenseEnv32) (nm : String)
    (xs : Array Float) (xs32 : Array Float32) : Bool :=
  bits64 (ref64 p i) nm == f64bits xs && bits64 (plan64 p i) nm == f64bits xs &&
    bits32 (plan32 p i32) nm == f32bits xs32

-- P1: continuing value beside a terminal value; Vn = [max(5,4), max(3,1)]. Sum would give [9, 4].
#guard agree belP1 belIn belIn32 "Vn" #[5.0, 3.0] #[5.0, 3.0]
-- P1' (the form the user wants): the terminal value is a bare copy. Same values.
#guard agree belP1c belIn belIn32 "Vn" #[5.0, 3.0] #[5.0, 3.0]
-- P1' with the tensors DECLARED f32 (binary32 leg only; the binary64 legs refuse mixed storage).
#guard bits32 (plan32 belP1d belIn32) "Vn" == f32bits #[5.0, 3.0]
-- P5: the single-statement equivalent agrees with the multi-writer form.
#guard agree belP5 belIn belIn32 "Vn" #[5.0, 3.0] #[5.0, 3.0]
-- the private clones stay hidden
#guard keysOf <$> plan64 belP1c belIn == some ["Q", "Term", "Vn"]
-- P2: deterministic transition, `-inf` is `0_K` in `Tr`. Vn = [max(1+10, 2+20, 5), max(0+10, 3+20, 100)].
#guard agree belP2 bel2In bel2In32 "Vn" #[22.0, 100.0] #[22.0, 100.0]
#guard agree belP2c bel2In bel2In32 "Vn" #[22.0, 100.0] #[22.0, 100.0]
-- P3: shortest paths with source init. D = [min(0+3, 1+1, 2), min(4+3, 0+1, 9)].
#guard agree belP3 bel3In bel3In32 "D" #[2.0, 1.0] #[2.0, 1.0]
#guard agree belP3c bel3In bel3In32 "D" #[2.0, 1.0] #[2.0, 1.0]
#guard agree belP5m bel3In bel3In32 "D" #[2.0, 1.0] #[2.0, 1.0]

private def scanBase : TLProgram := tlprog!{
  iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := maxreduce(S[j, l] · A[j, k])
}
private def axJ : AxisSpec := { name := "j", uid := 1, kind := .nat }
private def axL : AxisSpec := { name := "l", uid := 2, kind := .nat }
private def scanPlusMax : Option ScheduledProgram :=
  (sched64 scanBase).map fun sp =>
    { sp with stmts := sp.stmts ++ [.plain (.assign "S" [.free axJ, .free axL]
      { body := ⟨[⟨[.read "Y" [.axis axJ, .axis axL]]⟩]⟩, nonlin := .identity, agg := .max })] }

def belP1p : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  Vn[s] := maxreduce(Q[s, a])
  Vn[s] := Term[s + 1]
}
def belP3p : TLProgram := tlprog!{
  axis u : ℕ = 2
  axis v : ℕ = 2
  D[v] := minreduce(W[u, v] · D0[u])
  D[v] := S[v + 1]
}
private def belPIn : NamedDenseEnv :=
  mk64 [("Q", [2, 2], #[-5.0, -2.0, -7.0, -4.0]), ("Term", [2], #[-10.0, -20.0])]
private def belPIn32 : NamedDenseEnv32 :=
  mk32 [("Q", [2, 2], #[-5.0, -2.0, -7.0, -4.0]), ("Term", [2], #[-10.0, -20.0])]

-- P1'/P3' with a SHIFTED terminal copy: the copy's out-of-range read (`s = 1`) pads the group's
-- `0_K`, not `0`. Negative values make a `0` pad visible: Vn = [max(-2, Term[1] = -20), max(-4, pad)]
-- = [-2, -4] (a `0` pad would give [-2, 0]); min twin D = [min(2, S[1] = 9), min(1, pad)] = [2, 1]
-- (a `0` pad would give [2, 0]).
#guard agree belP1p belPIn belPIn32 "Vn" #[-2.0, -4.0] #[-2.0, -4.0]
#guard agree belP3p bel3In bel3In32 "D" #[2.0, 1.0] #[2.0, 1.0]

/-! Refusals that stay, observed on all three backends (the refusal is raised by collection, so the
schedule itself compiles). -/

private def abIn32 : NamedDenseEnv32 :=
  mk32 [("A", [2, 2], #[1.0, 2.0, 3.0, 4.0]), ("B", [2, 2], #[5.0, 6.0, 7.0, 8.0])]
private def refusedBy (p : TLProgram) (i : NamedDenseEnv) (i32 : NamedDenseEnv32) (c : CompileError) :
    Bool :=
  refErr64 p i == some c && srcErr (planCause64 p i) == some c && srcErr (planCause32 p i32) == some c

-- max + min (non-neutral writers), both orders
#guard refusedBy nbMM abIn abIn32 (.multiWriterAlgebra "Y")
#guard refusedBy nbMMr abIn abIn32 (.multiWriterAlgebra "Y")
-- sum + max with a NON-neutral sum writer (it contracts `j`), both orders
#guard refusedBy nbSM abIn abIn32 (.multiWriterAlgebra "Y")
#guard refusedBy nbMS abIn abIn32 (.multiWriterAlgebra "Y")
-- two affine scatter writers, even max-annotated
#guard refusedBy nbScat abIn abIn32 (.multiWriterScatter "S")
-- a scan node of `S` plus a max-annotated plain writer of `S` (hand-built: the surface cannot
-- spell it, `nbScan` fails earlier with `scanProjectionUnsupported`)
#guard (scanPlusMax.bind fun sp => match evalScheduled sp {} with
    | .error f => (match f.error with | .compile c => some c | _ => none) | .ok _ => none) ==
  some (.multiWriterScan "S")
#guard (scanPlusMax.bind fun sp =>
    srcErr (match prepareEvalPlan sp (InputSignature.ofDenseInputs {}) with
      | .error f => some f.cause | .ok _ => none)) == some (.multiWriterScan "S")
#guard (compErr nbScan) == some (.scanProjectionUnsupported "S")

/-! Readers of a collected max-plus `Vn`: a bool reader and a min-plus reader are refused with
`sortCastUnsupported` (the agreed sort is the tensor's sort), a max-plus reader and a real reader
are accepted. The real reader sits BETWEEN the two writers in source, so it sees the collected
`Vn = [max(5,9), max(3,1)] = [9, 3]` (writer 1 alone would give `[5, 3]`, a sum 8), `Tot = 12`. -/

#guard refusedBy rdBool rdIn rdIn32 (.sortCastUnsupported "B" "Vn")
#guard refusedBy rdMin rdIn rdIn32 (.sortCastUnsupported "Z" "Vn")
#guard agree rdMax rdIn rdIn32 "Z" #[9.0, 3.0] #[9.0, 3.0]
#guard agree rdReal rdIn rdIn32 "Tot" #[12.0] #[12.0]
#guard agree rdReal rdIn rdIn32 "Vn" #[9.0, 3.0] #[9.0, 3.0]


/-! ## S3b-ii review follow-up: abstaining-copy casts, vote-rule neighbours, NaN, signed zero, `route`

Every expected value was observed from a run (reference, binary64 plan, binary32 plan) before it was
pinned; the predicate programs use the `ForDecls` signature (a predicate input is typed by its
declaration), so their binary64 plan leg is `plan64p`. -/

private def plan64p (p : TLProgram) (inputs : NamedDenseEnv) : Option NamedDenseEnv :=
  (sched64 p).bind fun s =>
    (InputSignature.ofDenseInputsForDecls s.decls inputs).toOption.bind fun sig =>
      (prepareEvalPlan s sig).toOption.bind fun pp => (runPreparedDense pp inputs).toOption.map (·.env)

/-- Reference, binary64 plan (predicate-aware signature) and binary32 plan hold exactly these BITS. -/
private def agreeP (p : TLProgram) (i : NamedDenseEnv) (i32 : NamedDenseEnv32) (nm : String)
    (xs : Array Float) (xs32 : Array Float32) : Bool :=
  bits64 (ref64 p i) nm == f64bits xs && bits64 (plan64p p i) nm == f64bits xs &&
    bits32 (plan32 p i32) nm == f32bits xs32

private def nanEqA (a b : Array Float) : Bool :=
  a.size == b.size && (a.zip b).all fun (x, y) => (x.isNaN && y.isNaN) || x == y

/-- NaN-aware: all three backends hold `xs` (a NaN cell matches any NaN). -/
private def agreeNaN (p : TLProgram) (i : NamedDenseEnv) (i32 : NamedDenseEnv32) (nm : String)
    (xs : Array Float) : Bool :=
  (dat64 (ref64 p i) nm).map (nanEqA · xs) == some true &&
  (dat64 (plan64 p i) nm).map (nanEqA · xs) == some true &&
  (dat32 (plan32 p i32) nm).map (fun a => nanEqA (a.map Float32.toFloat) xs) == some true

/-! ### Abstaining copy of a PREDICATE beside a tropical writer (review rej F1)

`Vn[s] := maxreduce(Q[s, a]); Vn[s] := Reach[s]` with `predicate Reach`. The copy is neutral, so it
abstains and is rewritten to the group's sort; that rewrite changes its BOOL CAST, not only its pad:
the copy reads true/false as `0` / `-inf` (max-plus cast), where the same statement alone (the
neighbour `cpAlone`, a real `Vn`) reads `1` / `0`. With `Q = [[-5,-2],[-7,-4]]`, `Reach = [1, 0]`:
`Vn = [max(-2, 0), max(-4, -inf)] = [0, -4]`; the real cast would give `[max(-2,1), max(-4,0)] = [1, 0]`.
The min twin (`Q = [[5,2],[7,4]]`) gives `[min(2,0), min(4,+inf)] = [0, 4]` (real cast: `[1, 0]`).
A `minreduce(Reach[s])` copy beside a `maxreduce` writer is rewritten to MAX too: the user wrote min
(false -> `+inf`) and gets max (false -> `-inf`), so `Vn = [0, -4]`. Design section 4's claim that the
annotation "cannot change values, only the pad" is therefore false for a bool source. -/

def cpMax : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  predicate Reach(s)
  Vn[s] := maxreduce(Q[s, a])
  Vn[s] := Reach[s]
}
def cpMin : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  predicate Reach(s)
  Vn[s] := minreduce(Q[s, a])
  Vn[s] := Reach[s]
}
def cpMinOnMax : TLProgram := tlprog!{
  axis s : ℕ = 2
  axis a : ℕ = 2
  predicate Reach(s)
  Vn[s] := maxreduce(Q[s, a])
  Vn[s] := minreduce(Reach[s])
}
def cpAlone : TLProgram := tlprog!{
  axis s : ℕ = 2
  predicate Reach(s)
  Vn[s] := Reach[s]
}
private def cpMaxIn : NamedDenseEnv :=
  mk64 [("Q", [2, 2], #[-5.0, -2.0, -7.0, -4.0]), ("Reach", [2], #[1.0, 0.0])]
private def cpMaxIn32 : NamedDenseEnv32 :=
  mk32 [("Q", [2, 2], #[-5.0, -2.0, -7.0, -4.0]), ("Reach", [2], #[1.0, 0.0])]
private def cpMinIn : NamedDenseEnv :=
  mk64 [("Q", [2, 2], #[5.0, 2.0, 7.0, 4.0]), ("Reach", [2], #[1.0, 0.0])]
private def cpMinIn32 : NamedDenseEnv32 :=
  mk32 [("Q", [2, 2], #[5.0, 2.0, 7.0, 4.0]), ("Reach", [2], #[1.0, 0.0])]
private def cpAloneIn : NamedDenseEnv := mk64 [("Reach", [2], #[1.0, 0.0])]
private def cpAloneIn32 : NamedDenseEnv32 := mk32 [("Reach", [2], #[1.0, 0.0])]

#guard agreeP cpMax cpMaxIn cpMaxIn32 "Vn" #[0.0, -4.0] #[0.0, -4.0]
#guard agreeP cpMin cpMinIn cpMinIn32 "Vn" #[0.0, 4.0] #[0.0, 4.0]
#guard agreeP cpMinOnMax cpMaxIn cpMaxIn32 "Vn" #[0.0, -4.0] #[0.0, -4.0]
-- accept-neighbour: the same copy alone keeps the real cast (1 / 0)
#guard agreeP cpAlone cpAloneIn cpAloneIn32 "Vn" #[1.0, 0.0] #[1.0, 0.0]

/-! ### Vote rule: a neutral tropical copy beside a NON-neutral SUM writer is absorbed (rej F4a, sem F3)

`Y[i] := A[i, j]` (non-neutral: contracts `j`) beside `Y[i] := maxreduce(B[i + 1])` (neutral). The
tropical copy ABSTAINS, the group is real, and the copy is rewritten to `sum`: its `maxreduce`
annotation is dropped and its out-of-range read pads the REAL `0`. Accepted (it was
`multiWriterAlgebra` before the slice) and run as SUM on all three backends:
`Y = [3 + B[1], 7 + B[2], 11 + 0] = [2, -1, 11]` (`A = [[1,2],[3,4],[5,6]]`, `B = [-10,-1,-8]`); a max
collector would not give these values and a `-inf` pad would give `-inf` in the last cell.
Both orders and the min twin; neighbour `vrSumOnly` (the sum-annotated copy) gives the same values. -/

def vrSumMax : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[i, j]
  Y[i] := maxreduce(B[i + 1])
}
def vrSumMaxR : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := maxreduce(B[i + 1])
  Y[i] := A[i, j]
}
def vrSumMin : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[i, j]
  Y[i] := minreduce(B[i + 1])
}
def vrSumOnly : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[i, j]
  Y[i] := B[i + 1]
}
private def vrIn : NamedDenseEnv :=
  mk64 [("A", [3, 2], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]), ("B", [3], #[-10.0, -1.0, -8.0])]
private def vrIn32 : NamedDenseEnv32 :=
  mk32 [("A", [3, 2], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]), ("B", [3], #[-10.0, -1.0, -8.0])]
#guard agree vrSumMax vrIn vrIn32 "Y" #[2.0, -1.0, 11.0] #[2.0, -1.0, 11.0]
#guard agree vrSumMaxR vrIn vrIn32 "Y" #[2.0, -1.0, 11.0] #[2.0, -1.0, 11.0]
#guard agree vrSumMin vrIn vrIn32 "Y" #[2.0, -1.0, 11.0] #[2.0, -1.0, 11.0]
#guard agree vrSumOnly vrIn vrIn32 "Y" #[2.0, -1.0, 11.0] #[2.0, -1.0, 11.0]

/-! ### Vote rule: a relu or Iverson-only copy beside a `maxreduce` writer is REFUSED (rej F4b)

A non-identity nonlinearity (`relu`) and an Iverson-only body (`f.read? = none`) are non-neutral, so
the copy votes real against the max writer: `multiWriterAlgebra "Y"` on the reference and both plan
precisions (the schedule itself compiles). Accept-neighbours: the same copies beside a NON-neutral SUM
writer (real group): `relu(A) + sum_j B = [0 + -7, 3 + -11] = [-7, -8]`, `[i <= 0] + sum_j B = [1 + -7,
0 + -11] = [-6, -11]`. -/

def vrRelu : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := relu(A[i])
  Y[i] := maxreduce(B[i, j])
}
def vrReluSum : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := relu(A[i])
  Y[i] := B[i, j]
}
def vrIv : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := [i ≤ 0]
  Y[i] := maxreduce(B[i, j])
}
def vrIvSum : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := [i ≤ 0]
  Y[i] := B[i, j]
}
private def vrBIn : NamedDenseEnv :=
  mk64 [("A", [2], #[-1.0, 3.0]), ("B", [2, 2], #[-5.0, -2.0, -7.0, -4.0])]
private def vrBIn32 : NamedDenseEnv32 :=
  mk32 [("A", [2], #[-1.0, 3.0]), ("B", [2, 2], #[-5.0, -2.0, -7.0, -4.0])]
#guard refusedBy vrRelu vrBIn vrBIn32 (.multiWriterAlgebra "Y")
#guard refusedBy vrIv vrBIn vrBIn32 (.multiWriterAlgebra "Y")
#guard agree vrReluSum vrBIn vrBIn32 "Y" #[-7.0, -8.0] #[-7.0, -8.0]
#guard agree vrIvSum vrBIn vrBIn32 "Y" #[-6.0, -11.0] #[-6.0, -11.0]

/-! ### NaN and signed zero through the tropical collector (sem F5, rej F8)

The collector is an ordinary multi-term statement, so NaN propagates through `max` and `min` exactly
as in the per-writer fold, on all three backends: with `A = [[NaN,1],[2,3]]`, `B = 0`, max gives
`[NaN, 3]` and min `[NaN, 0]`, in either writer position. Signed zero: `max`/`min` of `-0.0` and `+0.0`
in either order gives `+0.0` on all three backends (bits pinned); the all-`-0.0` input is the neighbour. -/

private def nanF : Float := 0.0 / 0.0
private def nanF32 : Float32 := 0.0 / 0.0
private def nanIn : NamedDenseEnv :=
  mk64 [("A", [2, 2], #[nanF, 1.0, 2.0, 3.0]), ("B", [2, 2], #[0.0, 0.0, 0.0, 0.0])]
private def nanIn32 : NamedDenseEnv32 :=
  mk32 [("A", [2, 2], #[nanF32, 1.0, 2.0, 3.0]), ("B", [2, 2], #[0.0, 0.0, 0.0, 0.0])]
private def nanSwapIn : NamedDenseEnv :=
  mk64 [("B", [2, 2], #[nanF, 1.0, 2.0, 3.0]), ("A", [2, 2], #[0.0, 0.0, 0.0, 0.0])]
private def nanSwapIn32 : NamedDenseEnv32 :=
  mk32 [("B", [2, 2], #[nanF32, 1.0, 2.0, 3.0]), ("A", [2, 2], #[0.0, 0.0, 0.0, 0.0])]
#guard agreeNaN tmax nanIn nanIn32 "Y" #[nanF, 3.0]
#guard agreeNaN tmin nanIn nanIn32 "Y" #[nanF, 0.0]
#guard agreeNaN tmax nanSwapIn nanSwapIn32 "Y" #[nanF, 3.0]
-- accept-neighbour: the same program without a NaN is ordinary
#guard agreeNaN tmax (nanIn.insert "A" ⟨[2, 2], #[-1.0, 1.0, 2.0, 3.0]⟩)
  (nanIn32.insert "A" ⟨[2, 2], #[-1.0, 1.0, 2.0, 3.0]⟩) "Y" #[1.0, 3.0]

private def zIn : NamedDenseEnv :=
  mk64 [("A", [2, 2], #[-0.0, -0.0, 0.0, 0.0]), ("B", [2, 2], #[0.0, 0.0, -0.0, -0.0])]
private def zIn32 : NamedDenseEnv32 :=
  mk32 [("A", [2, 2], #[-0.0, -0.0, 0.0, 0.0]), ("B", [2, 2], #[0.0, 0.0, -0.0, -0.0])]
private def nzIn : NamedDenseEnv :=
  mk64 [("A", [2, 2], #[-0.0, -0.0, -0.0, -0.0]), ("B", [2, 2], #[-0.0, -0.0, -0.0, -0.0])]
private def nzIn32 : NamedDenseEnv32 :=
  mk32 [("A", [2, 2], #[-0.0, -0.0, -0.0, -0.0]), ("B", [2, 2], #[-0.0, -0.0, -0.0, -0.0])]
#guard bits64 (ref64 tmax zIn) "Y" == f64bits #[0.0, 0.0]
#guard bits64 (plan64 tmax zIn) "Y" == f64bits #[0.0, 0.0]
#guard bits32 (plan32 tmax zIn32) "Y" == f32bits #[0.0, 0.0]
#guard bits64 (ref64 tmin zIn) "Y" == f64bits #[0.0, 0.0]
#guard bits64 (plan64 tmin zIn) "Y" == f64bits #[0.0, 0.0]
#guard bits32 (plan32 tmin zIn32) "Y" == f32bits #[0.0, 0.0]
-- neighbour: an all-`-0.0` input also gives `+0.0` (bits 0) on all three backends, so the collector
-- does not preserve a negative zero (observed; the sign of a zero result is not specified).
#guard bits64 (ref64 tmax nzIn) "Y" == f64bits #[0.0, 0.0]
#guard bits64 (plan64 tmax nzIn) "Y" == f64bits #[0.0, 0.0]
#guard bits32 (plan32 tmax nzIn32) "Y" == f32bits #[0.0, 0.0]
#guard bits64 (ref64 tmin nzIn) "Y" == f64bits #[0.0, 0.0]
#guard bits64 (plan64 tmin nzIn) "Y" == f64bits #[0.0, 0.0]
#guard bits32 (plan32 tmin nzIn32) "Y" == f32bits #[0.0, 0.0]

/-! ### `route` on a tropical multi-writer program (rej F5): OBSERVED, not endorsed

`route` (the `compile` entry) runs `desugarMultiWriters` but never `checkSortCasts`. Observed: the
two-writer max (min) program routes to two private writer steps and a `maxreduce` (`minreduce`)
collector reading both; a bool reader of a collected max-plus tensor (`rdBool`), which BOTH evaluation
entries refuse with `sortCastUnsupported`, routes WITHOUT complaint (a `contract` step reads the
collector), and so does the min-plus reader `rdMin`. -/

private def routedOps (p : TLProgram) : Option (List BrOp × List (List Wire)) :=
  match p.compile.run 0 with
  | .ok tc _ => some (tc.steps.map (·.op), tc.routing)
  | .error _ _ => none
#guard routedOps tmax == some ([.maxreduce, .maxreduce, .maxreduce],
  [[.external 0], [.external 1], [.internal 0 0, .internal 1 0]])
#guard routedOps tmin == some ([.minreduce, .minreduce, .minreduce],
  [[.external 0], [.external 1], [.internal 0 0, .internal 1 0]])
#guard routedOps rdBool == some ([.maxreduce, .maxreduce, .maxreduce, .contract],
  [[.external 0], [.external 1], [.internal 0 0, .internal 1 0], [.internal 2 0]])
#guard routedOps rdMin == some ([.maxreduce, .maxreduce, .maxreduce, .minreduce],
  [[.external 0], [.external 1], [.internal 0 0, .internal 1 0], [.internal 2 0]])

end LeanNCD.Eval.Plan.CollectPlanTest

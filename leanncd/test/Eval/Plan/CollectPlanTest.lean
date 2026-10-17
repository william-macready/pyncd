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
-- Observed bit patterns (real runs): source order folds left, so reversing the writers changes the
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
private def h3In : NamedDenseEnv := mk64 [("A", [2], #[1.0, 0.0]), ("B", [2], #[0.0, 1.0])]
private def h3In32 : NamedDenseEnv32 := mk32 [("A", [2], #[1.0, 0.0]), ("B", [2], #[0.0, 1.0])]

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

end LeanNCD.Eval.Plan.CollectPlanTest

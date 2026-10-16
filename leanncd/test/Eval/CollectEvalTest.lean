import Eval.ExplicitF64
import LeanNCD.Eval.Entry

/-!
# Additive collection through the reference evaluator (slice 1)

A tensor with several writers is the sum (predicate: OR) of the writers' values, not the last
write. Each fixture pins a value observed through `TLProgram.eval` on an `explicitF64` program,
compared bit-for-bit (`Float.toBits`). Rejections are compared by their rendered text. Structural
facts of the desugar itself are in `test/DSL/Pipeline/CollectTest.lean`.
-/

namespace LeanNCD.Eval.CollectEvalTest
open LeanNCD LeanNCD.Eval Std

private def tz (shape : List Nat) (d : List Float) : DenseTensor := ⟨shape, d.toArray⟩
private def inp (l : List (String × DenseTensor)) : HashMap String DenseTensor :=
  l.foldl (fun m (k, v) => m.insert k v) {}

/-- The bits of tensor `nm` after evaluating `p.explicitF64`, or `none` on failure/absence. -/
private def bitsOf (p : TLProgram) (i : HashMap String DenseTensor) (nm : String) :
    Option (List UInt64) :=
  match TLProgram.eval p.explicitF64 i with
  | .ok r => r.env[nm]?.map (·.data.toList.map Float.toBits)
  | .error _ => none

private def keysOf (p : TLProgram) (i : HashMap String DenseTensor) : Option (List String) :=
  match TLProgram.eval p.explicitF64 i with
  | .ok r => some ((r.env.toList.map (·.1)).mergeSort (· ≤ ·))
  | .error _ => none

private def errOf (p : TLProgram) (i : HashMap String DenseTensor) : Option String :=
  match TLProgram.eval p.explicitF64 i with
  | .ok _ => none
  | .error e => some (toString e.error)

private def bits (xs : List Float) : List UInt64 := xs.map Float.toBits

/-! ## Values -/

-- V1 (donor: F14 `multiDefinition`, SourceDifferentialPolicyTest; spec value [7,13]).
def v1 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Y[i] := B[i]
}
private def v1In := inp [("A", tz [2] [5, 9]), ("B", tz [2] [2, 4])]
#guard bitsOf v1 v1In "Y" == some (bits [7, 13])
-- Private names are hidden from the reported environment.
#guard keysOf v1 v1In == some ["A", "B", "Y"]

-- V2 (donor: F15 `duplicateDefinition`; clone v1, append `Y := A`; spec value [12,22]).
def v2 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Y[i] := B[i]
  Y[i] := A[i]
}
#guard bitsOf v2 v1In "Y" == some (bits [12, 22])

-- V3 duplicate statement gives 2X (spec §9.1). Clone v1, both writers read X.
def v3 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := X[i]
  Y[i] := X[i]
}
#guard bitsOf v3 (inp [("X", tz [2] [1.5, 2.5])]) "Y" == some (bits [3, 5])

-- V4 predicate multi-writer collects by ∃ (OR), not by counting: A=[1,0], B=[1,1] gives [1,1]
-- (a count would give [2,1]). Clone v1, declare Y `predicate`.
def v4 : TLProgram := tlprog!{
  axis i : ℕ = 2
  predicate R(i)
  R[i] := A[i]
  R[i] := B[i]
}
#guard bitsOf v4 (inp [("A", tz [2] [1, 0]), ("B", tz [2] [1, 1])]) "R" == some (bits [1, 1])
-- The decision-note probe inputs A=[1,0], B=[0,1] (old overwrite: [0,1]).
#guard bitsOf v4 (inp [("A", tz [2] [1, 0]), ("B", tz [2] [0, 1])]) "R" == some (bits [1, 1])

-- V5 writers are collected in SOURCE order: (0.1+0.2)+0.3 = 0x3FE3333333333334, while the
-- reversed program (V5r) gives (0.3+0.2)+0.1 = 0x3FE3333333333333. Non-integral on purpose.
def v5 : TLProgram := tlprog!{
  axis i : ℕ = 1
  Y[i] := A[i]
  Y[i] := B[i]
  Y[i] := C[i]
}
def v5r : TLProgram := tlprog!{
  axis i : ℕ = 1
  Y[i] := C[i]
  Y[i] := B[i]
  Y[i] := A[i]
}
private def v5In := inp [("A", tz [1] [0.1]), ("B", tz [1] [0.2]), ("C", tz [1] [0.3])]
#guard bitsOf v5 v5In "Y" == some [4603579539098121012]
#guard bitsOf v5r v5In "Y" == some [4603579539098121011]

-- V6 a reader between two writers sees BOTH (decision note §C.2 probe; old: U = A).
def v6 : TLProgram := tlprog!{
  axis i : ℕ = 2
  T[i] := A[i]
  U[i] := T[i]
  T[i] := B[i]
}
private def v6In := inp [("A", tz [2] [1, 2]), ("B", tz [2] [10, 20])]
#guard bitsOf v6 v6In "U" == some (bits [11, 22])
#guard bitsOf v6 v6In "T" == some (bits [11, 22])

-- V7 each writer keeps its own nonlinearity; the collector is the identity (spec §15.3):
-- relu(A)+relu(B) = [3,2], not relu(A+B) = [2,0].
def v7 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := relu(A[i])
  Y[i] := relu(B[i])
}
#guard bitsOf v7 (inp [("A", tz [2] [-1, 2]), ("B", tz [2] [3, -4])]) "Y" == some (bits [3, 2])

-- V8 single-writer accept-neighbour of v1: unchanged, nothing hidden.
def v8 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
}
#guard bitsOf v8 v1In "Y" == some (bits [5, 9])
#guard keysOf v8 v1In == some ["A", "B", "Y"]

/-! ## Rejections -/

-- J1 a writer reading its own multi-writer destination is cyclic (old: T = A·B, overwrite chain).
def j1 : TLProgram := tlprog!{
  axis i : ℕ = 2
  T[i] := A[i]
  T[i] := T[i] · B[i]
}
#guard errOf j1 v6In == some "compile failed: LeanNCD.CompileError.cyclicDataflow \"schedule: cyclic dataflow\""

-- J2 assign writers on different axes (old: silently truncated). Clone v1, writer 2 on j.
def j2 : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  Y[i] := A[i]
  Y[j] := B[j]
}
#guard errOf j2 (inp [("A", tz [2] [1, 2]), ("B", tz [3] [10, 20, 30])]) ==
  some "compile failed: LeanNCD.CompileError.writerShapeMismatch \"Y\" 2 0"

-- J3 scatter multi-writer (old: S = [0,10,0,20], X lost).
def j3 : TLProgram := tlprog!{
  axis i : ℕ = 2
  S[2*i] := X[i]
  S[2*i + 1] := Y[i]
}
#guard errOf j3 (inp [("X", tz [2] [1, 2]), ("Y", tz [2] [10, 20])]) ==
  some "compile failed: LeanNCD.CompileError.multiWriterScatter \"S\""

-- J4 max-annotated multi-writer (slice 1 admits only sum).
def j4 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := maxreduce(A[i, j])
  Y[i] := maxreduce(B[i, j])
}
#guard errOf j4 (inp [("A", tz [2, 2] [1, 2, 3, 4]), ("B", tz [2, 2] [5, 6, 7, 8])]) ==
  some "compile failed: LeanNCD.CompileError.multiWriterAlgebra \"Y\""

-- J5 a supplied input naming a defined tensor (decision note B3; old: silently replaced).
#guard errOf v8 (inp [("A", tz [2] [1, 2]), ("Y", tz [2] [7, 7])]) ==
  some "evalScheduled: supplied input Y names a tensor the program defines"
-- J5b accept-neighbour: an unrelated extra input passes through unchanged.
#guard bitsOf v8 (inp [("A", tz [2] [1, 2]), ("Unused", tz [1] [7])]) "Unused" == some (bits [7])

end LeanNCD.Eval.CollectEvalTest

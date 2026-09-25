import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter32

/-!
# F32-D Task 3: an independent binary32 scatter oracle

There is no legacy oracle for binary32 (the reference evaluator refuses every f32 program), so each
case below checks a binary32 SCATTER program against a result assembled from two pieces that share
no code with the scatter path:

1. the scatter's RHS evaluated as an ordinary binary32 ASSIGNMENT (`twin`, free LHS over the same
   source axes) through the F32-A path — `prepareEvalPlan`'s plain branch, `checkAssignF32`,
   `runDenseAssign32` — which never touches `ScatterPlan`, `checkScatterF32`, `runDenseScatter32`,
   Step D's scatter branch, or `scatterFillOrFail`;
2. a placement written HERE from the source LHS text (`place`), with its own row-major helpers — not
   `outCoeffs`/`outBias`, not `applyAffine`/`flatIndex` — into a `destShape` taken from the
   REFERENCE-measured binary64 extents (`ScatterDenseTest` fixtures 1, 2, 4; `DifferentialTest`
   SA1-SA3), with every other cell `+0` (bits `0`).

Placement copies values under `.rejectCollisions`, so these two must agree bit for bit. Each case
also pins its observed bits, and the two carrier-discriminating cases (O1, O5) require at least one
lane where binary64-then-narrow differs from the native result.

What this cannot catch, by construction: a defect in the traversal both legs share
(`denseValueAtWith`, `float32Ops`, `residualizeAssignment`); the destination-extent convention (the
oracle takes `destShape` as given); collision and out-of-range behaviour (every case is
collision-free and in range, which is all surface syntax can express); and any non-zero or tropical
`fill` (source syntax admits only sum-product fill `0`).
-/

namespace LeanNCD.Eval.Plan.Scatter32OracleTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

/-- Compile and prepare through the declaration-aware binary32 signature constructor. -/
def compile32 (p : TLProgram) (inputs : NamedDenseEnv32) : Except String PreparedPlan := do
  let sched ← match p.compileToScheduled.run 0 with
    | .ok s _ => .ok s
    | .error e _ => .error s!"compile failed: {repr e}"
  let sig ← match InputSignature.ofDenseInputs32ForDecls sched.decls inputs with
    | .ok s => .ok s
    | .error e => .error s!"binary32 signature rejected: {repr e}"
  match prepareEvalPlan sched sig with
  | .ok prepared => .ok prepared
  | .error _ => .error "prepare failed"

/-- Run a binary32 program by name and return one named result. -/
def run32 (p : TLProgram) (inputs : NamedDenseEnv32) (nm : String) :
    Except String (PreparedPlan × DenseTensor32) := do
  let prepared ← compile32 p inputs
  match runPreparedDense32 prepared inputs with
  | .error e => .error s!"run failed: {repr e.cause}"
  | .ok report => match report.env[nm]? with
    | some t => .ok (prepared, t)
    | none => .error s!"{nm} missing from the result environment"

/-- Row-major coordinates of `shape` — this file's own, not `Coordinates.allCoords`. -/
def coordsOf : List Nat → List (List Nat)
  | [] => [[]]
  | n :: rest => (List.range n).flatMap (fun i => (coordsOf rest).map (i :: ·))

/-- Row-major offset of `c` in `shape`, or `none` if any component is out of range. -/
def offsetOf (shape c : List Nat) : Option Nat :=
  if c.length == shape.length && (c.zip shape).all (fun (x, n) => x < n) then
    some ((c.zip shape).foldl (fun acc (x, n) => acc * n + x) 0)
  else none

/-- Place a source-shaped binary32 tensor into `destShape` through `place`, `+0` elsewhere.
    Fails on a collision or an out-of-range placement (no case here may produce either). -/
def placeInto (src : DenseTensor32) (destShape : List Nat) (place : List Nat → List Nat) :
    Except String (Array UInt32) := do
  let mut out : Array UInt32 := Array.replicate (destShape.foldl (· * ·) 1) 0
  let mut written : Array Bool := Array.replicate out.size false
  for (sc, k) in (coordsOf src.shape).zipIdx do
    match offsetOf destShape (place sc) with
    | none => throw s!"oracle: {sc} places out of range"
    | some o =>
        if written[o]! then throw s!"oracle: collision at {place sc}"
        written := written.set! o true
        out := out.set! o (src.data[k]!).toBits
  return out

structure OracleCase where
  name : String
  scatterProg : TLProgram
  outName : String
  twinProg : TLProgram
  twinName : String
  destShape : List Nat
  place : List Nat → List Nat
  inputs : NamedDenseEnv32
  observed : Array UInt32
  /-- For a carrier-discriminating case: the same program with ordinary (binary64) declarations
      and its inputs widened, run through `runPreparedDense`. -/
  contrast64 : Option (TLProgram × HashMap String DenseTensor) := none

def run64 (p : TLProgram) (inputs : HashMap String DenseTensor) (nm : String) :
    Except String (Array Float) := do
  let sched ← match p.compileToScheduled.run 0 with
    | .ok s _ => .ok s
    | .error e _ => .error s!"compile failed: {repr e}"
  let sig ← match InputSignature.ofDenseInputsForDecls sched.decls inputs with
    | .ok s => .ok s
    | .error e => .error s!"binary64 signature rejected: {repr e}"
  let prepared ← match prepareEvalPlan sched sig with
    | .ok p => .ok p
    | .error _ => .error "binary64 prepare failed"
  match runPreparedDense prepared inputs with
  | .error e => .error s!"binary64 run failed: {repr e.cause}"
  | .ok report => match report.env[nm]? with
    | some t => .ok t.data
    | none => .error s!"{nm} missing from the binary64 environment"

def checkCase (c : OracleCase) : Except String Unit := do
  let (prepared, out) ← (run32 c.scatterProg c.inputs c.outName).mapError (s!"{c.name}: " ++ ·)
  unless prepared.plan.storageKind == .float32 do throw s!"{c.name}: not a binary32 plan"
  unless prepared.plan.raw.steps.any (fun | .scatter _ => true | _ => false) do
    throw s!"{c.name}: compiled without a scatter step"
  let (_, twin) ← (run32 c.twinProg c.inputs c.twinName).mapError (s!"{c.name} twin: " ++ ·)
  let expected ← placeInto twin c.destShape c.place
  let got := out.data.map Float32.toBits
  unless out.shape == c.destShape && got == expected do
    throw s!"{c.name}: scatter {out.shape}/{got} ≠ oracle {c.destShape}/{expected}"
  unless got == c.observed do throw s!"{c.name}: observed bits changed: {got}"
  match c.contrast64 with
  | none => pure ()
  | some (p64, in64) =>
      let wide ← (run64 p64 in64 c.outName).mapError (s!"{c.name} contrast: " ++ ·)
      let narrowed := wide.map (fun x => x.toFloat32.toBits)
      unless narrowed.size == got.size && (narrowed.zip got).any (fun (a, b) => a != b) do
        throw s!"{c.name}: no lane separates native binary32 from binary64-then-narrow"

def env32 (xs : List (String × List Nat × List Float32)) : NamedDenseEnv32 :=
  HashMap.ofList (xs.map (fun (n, s, v) => (n, ⟨s, v.toArray⟩)))

def env64 (xs : List (String × List Nat × List Float32)) : HashMap String DenseTensor :=
  HashMap.ofList (xs.map (fun (n, s, v) => (n, ⟨s, v.toArray.map Float32.toFloat⟩)))

/-- O1 values: lane 0 is `sqrt(2^48) + 1 - 2^24`, `+0` natively and `1` in binary64. -/
def o1Vals : List (String × List Nat × List Float32) :=
  [("A", [3], [281474976710656.0, 4.0, 9.0]), ("B", [3], [1.0, 1.0, 1.0]),
   ("Z", [3], [-16777216.0, 0.5, 0.25])]

/-- O5 values: `W = A·A` rounds `4097² = 16785409` to `16785408` natively; `+ 1` stays there
    (ties-to-even), while binary64 reaches `16785410`, which narrows exactly. -/
def o5Vals : List (String × List Nat × List Float32) :=
  [("A", [3], [4097.0, 3.0, 0.5]), ("B", [3], [1.0, 1.0, 1.0])]

def oracleCases : List OracleCase :=
  [ { name := "O1 strided, unary, carrier-discriminating"
    , scatterProg := tlprog!{
        axis i : ℕ = 3
        tensor f32 A(i), B(i), Z(i), Out(i)
        Out[2*i] := sqrt(A[i]) + B[i] + Z[i] }
    , outName := "Out"
    , twinProg := tlprog!{
        axis i : ℕ = 3
        tensor f32 A(i), B(i), Z(i), Src(i)
        Src[i] := sqrt(A[i]) + B[i] + Z[i] }
    , twinName := "Src", destShape := [6], place := fun c => c.map (2 * ·)
    , inputs := env32 o1Vals
    , observed := #[0, 0, 1080033280, 0, 1082654720, 0]
    , contrast64 := some (tlprog!{
        axis i : ℕ = 3
        tensor A(i), B(i), Z(i), Out(i)
        Out[2*i] := sqrt(A[i]) + B[i] + Z[i] }, env64 o1Vals) }
  , { name := "O2 shifted stride (placement bias)"
    , scatterProg := tlprog!{
        axis i : ℕ = 3
        tensor f32 A(i), B(i), Out(i)
        Out[2*i + 1] := A[i] · B[i] }
    , outName := "Out"
    , twinProg := tlprog!{
        axis i : ℕ = 3
        tensor f32 A(i), B(i), Src(i)
        Src[i] := A[i] · B[i] }
    , twinName := "Src", destShape := [6], place := fun c => c.map (2 * · + 1)
    , inputs := env32 [("A", [3], [4097.0, 3.0, 0.1]), ("B", [3], [4097.0, 0.1, 3.0])]
    , observed := #[0, 1266683904, 0, 1050253722, 0, 1050253722] }
  , { name := "O3 diagonal"
    , scatterProg := tlprog!{
        axis i : ℕ = 3
        tensor f32 A(i), B(i), Y(i, i)
        Y[i, i] := A[i] + B[i] }
    , outName := "Y"
    , twinProg := tlprog!{
        axis i : ℕ = 3
        tensor f32 A(i), B(i), Src(i)
        Src[i] := A[i] + B[i] }
    , twinName := "Src", destShape := [3, 3], place := fun c => c ++ c
    , inputs := env32 [("A", [3], [16777216.0, 0.1, 1.0]), ("B", [3], [1.0, 0.2, 2.0])]
    , observed := #[1266679808, 0, 0, 0, 1050253722, 0, 0, 0, 1077936128] }
  , { name := "O4 two-dimensional stride"
    , scatterProg := tlprog!{
        axis i : ℕ = 2
        axis j : ℕ = 3
        tensor f32 X(i, j), Out(i, j)
        Out[2*i, 2*j] := X[i, j] }
    , outName := "Out"
    , twinProg := tlprog!{
        axis i : ℕ = 2
        axis j : ℕ = 3
        tensor f32 X(i, j), Src(i, j)
        Src[i, j] := X[i, j] }
    , twinName := "Src", destShape := [4, 6], place := fun c => c.map (2 * ·)
    , inputs := env32 [("X", [2, 3], [1.0, 2.0, 3.0, 4.0, 5.0, 6.0])]
    , observed := #[1065353216, 0, 1073741824, 0, 1077936128, 0, 0, 0, 0, 0, 0, 0,
                    1082130432, 0, 1084227584, 0, 1086324736, 0, 0, 0, 0, 0, 0, 0] }
  , { name := "O5 assignment then scatter, carrier-discriminating"
    , scatterProg := tlprog!{
        axis i : ℕ = 3
        tensor f32 A(i), B(i), W(i), Out(i)
        W[i] := A[i] · A[i]
        Out[2*i] := W[i] + B[i] }
    , outName := "Out"
    , twinProg := tlprog!{
        axis i : ℕ = 3
        tensor f32 A(i), B(i), W(i), Src(i)
        W[i] := A[i] · A[i]
        Src[i] := W[i] + B[i] }
    , twinName := "Src", destShape := [6], place := fun c => c.map (2 * ·)
    , inputs := env32 o5Vals
    , observed := #[1266683904, 0, 1092616192, 0, 1067450368, 0]
    , contrast64 := some (tlprog!{
        axis i : ℕ = 3
        tensor A(i), B(i), W(i), Out(i)
        W[i] := A[i] · A[i]
        Out[2*i] := W[i] + B[i] }, env64 o5Vals) } ]

#guard oracleCases.length == 5

run_cmd do
  for c in oracleCases do
    match checkCase c with
    | .ok () => pure ()
    | .error m => throwError s!"BINARY32 SCATTER ORACLE FAILED: {m}"

end LeanNCD.Eval.Plan.Scatter32OracleTest

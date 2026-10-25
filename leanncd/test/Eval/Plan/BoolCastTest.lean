import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Compile
import LeanNCD.Eval.Plan.Adapter
import LeanNCD.Eval.Plan.Adapter32
import Eval.ExplicitF64

/-!
# S3b T5 — the bool -> tropical READ CAST, in both backends

Design §3: a BARE read of a `predicate` tensor in a max-plus / min-plus statement reads false as
`0_K` of the statement (`-inf` / `+inf`) and true as `1_K` (`0.0`); a read under a `unaryFn` takes
real 0/1 and is not cast; every other read (bool -> real, real -> tropical) is the identity.

Every program below runs three ways — the reference `TLProgram.eval`, the checked plan in binary64
(`runPreparedDense`) and the checked plan in binary32 (`runPreparedDense32`) — and all three must
equal the hand-computed value. Data is chosen so the OLD identity cast (`edge + X`, i.e. false read
as `0` instead of `-inf`) gives a DIFFERENT answer; each max-plus fixture has a min-plus duality twin
from negated data. Donors: `GnnScatterTest` GN4 (the program), `ScatterCompileTest` S11/S12 (scatter
parity), `Scatter32OracleTest` (the binary32 run), `ScatterDenseTest` fixture 8 (raw-plan shapes).
-/

namespace LeanNCD.Eval.Plan.BoolCastTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.Eval.ExplicitF64 Std

def negInf : Float := -1.0 / 0.0
def posInf : Float := 1.0 / 0.0

/-- Named inputs: name, shape, row-major data. -/
abbrev Ins := List (String × List Nat × List Float)

def env64 (xs : Ins) : HashMap String DenseTensor :=
  HashMap.ofList (xs.map (fun (n, s, v) => (n, ⟨s, v.toArray⟩)))

def env32 (xs : Ins) : NamedDenseEnv32 :=
  HashMap.ofList (xs.map (fun (n, s, v) => (n, ⟨s, v.toArray.map Float.toFloat32⟩)))

def refOut (p : TLProgram) (xs : Ins) (nm : String) : Except String (List Float) :=
  match TLProgram.eval p.explicitF64 (env64 xs) with
  | .error e => .error s!"reference: {e}"
  | .ok r => match r.env[nm]? with
    | some t => .ok t.data.toList
    | none => .error s!"reference: {nm} missing"

def planOut64 (p : TLProgram) (xs : Ins) (nm : String) : Except String (List Float) := do
  let sched ← match p.explicitF64.compileToScheduled.run 0 with
    | .ok s _ => .ok s
    | .error e _ => .error s!"compile: {repr e}"
  let sig ← match InputSignature.ofDenseInputsForDecls sched.decls (env64 xs) with
    | .ok s => .ok s
    | .error e => .error s!"signature64: {repr e}"
  let prepared ← match prepareEvalPlan sched sig with
    | .ok q => .ok q
    | .error _ => .error "prepare64 failed"
  match runPreparedDense prepared (env64 xs) with
  | .error e => .error s!"run64: {repr e.cause}"
  | .ok r => match r.env[nm]? with
    | some t => .ok t.data.toList
    | none => .error s!"plan64: {nm} missing"

/-- The binary32 plan on the program as written (undeclared names are `f32`, `predicate` stays bool). -/
def planOut32 (p : TLProgram) (xs : Ins) (nm : String) : Except String (List Float) := do
  let sched ← match p.compileToScheduled.run 0 with
    | .ok s _ => .ok s
    | .error e _ => .error s!"compile32: {repr e}"
  let sig ← match InputSignature.ofDenseInputs32ForDecls sched.decls (env32 xs) with
    | .ok s => .ok s
    | .error e => .error s!"signature32: {repr e}"
  let prepared ← match prepareEvalPlan sched sig with
    | .ok q => .ok q
    | .error _ => .error "prepare32 failed"
  match runPreparedDense32 prepared (env32 xs) with
  | .error e => .error s!"run32: {repr e.cause}"
  | .ok r => match r.env[nm]? with
    | some t => .ok (t.data.toList.map Float32.toFloat)
    | none => .error s!"plan32: {nm} missing"

/-- Reference, binary64 plan and binary32 plan all equal `expected`, comparing cells with `eq`. -/
def agreeWith (eq : Float → Float → Bool) (label : String) (p : TLProgram) (xs : Ins) (nm : String)
    (expected : List Float) : Except String Unit := do
  let same : List Float → Bool := fun v =>
    v.length == expected.length && (v.zip expected).all (fun (a, b) => eq a b)
  let r ← refOut p xs nm
  let a ← planOut64 p xs nm
  let b ← planOut32 p xs nm
  unless same r do throw s!"{label}: reference {r} ≠ {expected}"
  unless same a do throw s!"{label}: plan f64 {a} ≠ {expected}"
  unless same b do throw s!"{label}: plan f32 {b} ≠ {expected}"

/-- Reference, binary64 plan and binary32 plan all equal `expected`. -/
def agree (label : String) (p : TLProgram) (xs : Ins) (nm : String) (expected : List Float) :
    Except String Unit :=
  agreeWith (· == ·) label p xs nm expected

def assertAgree (label : String) (p : TLProgram) (xs : Ins) (nm : String) (expected : List Float) :
    Lean.Elab.Command.CommandElabM Unit :=
  match agree label p xs nm expected with
  | .ok () => pure ()
  | .error e => throwError e

/-! ## (a) a predicate read BARE in a max-plus / min-plus statement (GN4's program, negative data)

`edge = [[1,1],[0,1]]`, max-plus, `X = [[-1,-2],[-3,-4]]`. Cast: row 0 is `max(X0, X1) = [-1,-2]`,
row 1 is `X1 = [-3,-4]` (the false edge is `-inf`). The old identity cast gives `[[0,-1],[-1,-2]]`.
Min-plus twin (negated data): `[[1,2],[3,4]]`; identity would give `[[2,3],[1,2]]`. -/
def bareMax : TLProgram := tlprog!{
  predicate edge(i, j)
  H[i, f] := maxreduce(edge[i, j] · X[j, f]) }
def bareMin : TLProgram := tlprog!{
  predicate edge(i, j)
  H[i, f] := minreduce(edge[i, j] · X[j, f]) }

run_cmd do
  assertAgree "a1 max" bareMax
    [("edge", [2, 2], [1, 1, 0, 1]), ("X", [2, 2], [-1, -2, -3, -4])] "H" [-1, -2, -3, -4]
  assertAgree "a2 min" bareMin
    [("edge", [2, 2], [1, 1, 0, 1]), ("X", [2, 2], [1, 2, 3, 4])] "H" [1, 2, 3, 4]

/-! ## (f) an all-false predicate row is an EMPTY effective reduction: `-inf` / `+inf`

`edge = [[0,0],[1,0]]`: row 0 has no true edge. Max-plus, `X = [[-1,-2],[-3,-4]]`: row 0 is `-inf`,
row 1 is `X0 = [-1,-2]` (the identity cast would make row 0 `max(X0,X1) = [-1,-2]`). -/
run_cmd do
  assertAgree "f1 max all-false row" bareMax
    [("edge", [2, 2], [0, 0, 1, 0]), ("X", [2, 2], [-1, -2, -3, -4])] "H" [negInf, negInf, -1, -2]
  assertAgree "f2 min all-false row" bareMin
    [("edge", [2, 2], [0, 0, 1, 0]), ("X", [2, 2], [1, 2, 3, 4])] "H" [posInf, posInf, 1, 2]

/-! ## (b) the same read UNDER a `unaryFn` takes REAL input: bool 0/1, no cast

`sqrt(edge[i,j]) · X[j]` (`sqrt 0 = 0`, `sqrt 1 = 1`), `edge = [[1,1],[0,1]]`, `X = [-1,-3]`,
max-plus: row 0 `max(1-1, 1-3) = 0`, row 1 `max(0-1, 1-3) = -1`. A cast applied under the unary would
feed `sqrt(-inf)` (a domain error) instead of `sqrt(0) = 0`. Min-plus twin: `X = [1,3]`: `[2, 1]`. -/
def unaryMax : TLProgram := tlprog!{
  predicate edge(i, j)
  H[i] := maxreduce(sqrt(edge[i, j]) · X[j]) }
def unaryMin : TLProgram := tlprog!{
  predicate edge(i, j)
  H[i] := minreduce(sqrt(edge[i, j]) · X[j]) }

run_cmd do
  assertAgree "b1 unary max" unaryMax
    [("edge", [2, 2], [1, 1, 0, 1]), ("X", [2], [-1, -3])] "H" [0, -1]
  assertAgree "b2 unary min" unaryMin
    [("edge", [2, 2], [1, 1, 0, 1]), ("X", [2], [1, 3])] "H" [2, 1]

/-! ## (c) neighbours: bool -> real and real -> tropical are the identity (real -> bool is NOT: see (j))

bool -> real sum, `X = [[-1,-2],[-3,-4]]`: `H = [[-4,-6],[-3,-4]]` (a cast would be a bug here).
real -> max-plus: `A = [[1,1],[0,1]]` is added, not cast: `[[0,-1],[-1,-2]]`; min-plus twin on
`X = [[1,2],[3,4]]`: `[[2,3],[1,2]]`. -/
def boolReal : TLProgram := tlprog!{
  predicate edge(i, j)
  H[i, f] := edge[i, j] · X[j, f] }
def realMax : TLProgram := tlprog!{ H[i, f] := maxreduce(A[i, j] · X[j, f]) }
def realMin : TLProgram := tlprog!{ H[i, f] := minreduce(A[i, j] · X[j, f]) }

run_cmd do
  assertAgree "c1 bool->real" boolReal
    [("edge", [2, 2], [1, 1, 0, 1]), ("X", [2, 2], [-1, -2, -3, -4])] "H" [-4, -6, -3, -4]
  assertAgree "c2 real->max" realMax
    [("A", [2, 2], [1, 1, 0, 1]), ("X", [2, 2], [-1, -2, -3, -4])] "H" [0, -1, -1, -2]
  assertAgree "c3 real->min" realMin
    [("A", [2, 2], [1, 1, 0, 1]), ("X", [2, 2], [1, 2, 3, 4])] "H" [2, 3, 1, 2]

/-! ## the out-of-bounds pad is NOT cast

`H[i] := maxreduce(edge[i+1] · X[i])`, `edge = [1,0,1]`, `X = [-1,-2,-3]` (`i : 3`): `edge[1] = 0`
(false: `-inf`), `edge[2] = 1` (true: `-2 + 0`), `edge[3]` out of bounds (pad `-inf`). So
`[-inf, -2, -inf]`; a cast of the pad (`-inf` read as true) would give `-3` in the last cell.
Min-plus twin: `X = [1,2,3]`: `[+inf, 2, +inf]`. -/
def oobMax : TLProgram := tlprog!{
  axis i : ℕ = 3
  predicate edge(m)
  H[i] := maxreduce(edge[i + 1] · X[i]) }
def oobMin : TLProgram := tlprog!{
  axis i : ℕ = 3
  predicate edge(m)
  H[i] := minreduce(edge[i + 1] · X[i]) }

run_cmd do
  assertAgree "g1 oob max" oobMax
    [("edge", [3], [1, 0, 1]), ("X", [3], [-1, -2, -3])] "H" [negInf, -2, negInf]
  assertAgree "g2 oob min" oobMin
    [("edge", [3], [1, 0, 1]), ("X", [3], [1, 2, 3])] "H" [posInf, 2, posInf]

/-! ## (d) a tropical SCATTER compute half and a tropical SCAN (base and step) read a predicate

Scatter: `Out[2*i] := maxreduce(edge[i, j] · X[j])`, `edge = [[1,1],[0,1],[0,0]]`, `X = [-1,-3]`:
`[-1, -inf, -3, -inf, -inf, -inf]` (identity cast: cell 0 would be `0`). Min-plus twin `X = [1,3]`.

Scan: base `S[j,0] := maxreduce(B[j,k] · Z[k])` (the scan BASE caller) and step
`S[j,t+1] := maxreduce(S[j,t] · E[j,t,k])` (the scan STEP caller), `B = [[1,1],[0,1]]`,
`Z = [-2,-5]`: `S[:,0] = [-2,-5]`; `E[0,0] = [1,0]` gives `S[0,1] = -2`, `E[0,1] = [0,0]` gives
`S[0,2] = -inf`; `E[1,0] = [0,1]`, `E[1,1] = [1,1]` give `S[1,1] = S[1,2] = -5`. Min-plus twin
`Z = [2,5]`: `[[2,2,+inf],[5,5,5]]`. -/
def scatterMax : TLProgram := tlprog!{
  predicate edge(i, j)
  Out[2*i] := maxreduce(edge[i, j] · X[j]) }
def scatterMin : TLProgram := tlprog!{
  predicate edge(i, j)
  Out[2*i] := minreduce(edge[i, j] · X[j]) }
def scanMax : TLProgram := tlprog!{
  iter t = 3
  predicate B(j, k)
  predicate E(j, t, k)
  S[j, 0] := maxreduce(B[j, k] · Z[k])
  S[j, t + 1] := maxreduce(S[j, t] · E[j, t, k]) }
def scanMin : TLProgram := tlprog!{
  iter t = 3
  predicate B(j, k)
  predicate E(j, t, k)
  S[j, 0] := minreduce(B[j, k] · Z[k])
  S[j, t + 1] := minreduce(S[j, t] · E[j, t, k]) }

def scanE : List Float := [1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0]

run_cmd do
  assertAgree "d1 scatter max" scatterMax
    [("edge", [3, 2], [1, 1, 0, 1, 0, 0]), ("X", [2], [-1, -3])] "Out"
    [-1, negInf, -3, negInf, negInf, negInf]
  assertAgree "d2 scatter min" scatterMin
    [("edge", [3, 2], [1, 1, 0, 1, 0, 0]), ("X", [2], [1, 3])] "Out"
    [1, posInf, 3, posInf, posInf, posInf]
  assertAgree "d3 scan max" scanMax
    [("B", [2, 2], [1, 1, 0, 1]), ("E", [2, 3, 2], scanE), ("Z", [2], [-2, -5])] "S"
    [-2, -2, negInf, -5, -5, -5]
  assertAgree "d4 scan min" scanMin
    [("B", [2, 2], [1, 1, 0, 1]), ("E", [2, 3, 2], scanE), ("Z", [2], [2, 5])] "S"
    [2, 2, posInf, 5, 5, 5]

/-! ## (e) a RAW plan carrying the cast: accepted on a bool source under a tropical algebra,
rejected (`castNotAdmitted term factor`) on a non-bool source, a real algebra, or a unary read -/

def castRead (cast : Bool) (unary : Option UnaryOp := none) : ReadPlan :=
  { sourceSlot := 0, map := AffineMap.mk #[#[1]] #[0], sourceShape := #[3]
  , oobPolicy := .zeroPad, unary := unary, boolToTropical := cast }

def castPlan (alg : ContractionAlgebra) (r : ReadPlan) : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read r] }]
  , algebra := alg }

def boolSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .bool }, { shape := #[3], dtype := .f64 } ]
def realSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 } ]

def accepted (sigs : Array TensorSignature) (a : AssignPlan) : Bool :=
  match checkAssign sigs a with | .ok _ => true | .error _ => false

def rejectedCast (sigs : Array TensorSignature) (a : AssignPlan) : Bool :=
  match checkAssign sigs a with | .error (.castNotAdmitted 0 0) => true | _ => false

-- accept: cast on a bool source, max-plus and min-plus
#guard accepted boolSigs (castPlan admittedAlgebraMax (castRead true))
#guard accepted boolSigs (castPlan admittedAlgebraMin (castRead true))
-- accept neighbours: no cast (any source, any algebra)
#guard accepted boolSigs (castPlan admittedAlgebra (castRead false))
#guard accepted realSigs (castPlan admittedAlgebraMax (castRead false))
-- reject: cast on a non-bool source
#guard rejectedCast realSigs (castPlan admittedAlgebraMax (castRead true))
-- reject: cast under the real algebra (a bool source, but the statement is not tropical)
#guard rejectedCast boolSigs (castPlan admittedAlgebra (castRead true))
-- reject: cast on a unary read (the unary takes real input)
#guard rejectedCast boolSigs (castPlan admittedAlgebraMax (castRead true (some .exp)))

-- S3b-ii T3b (D1): the real -> bool cast flag `realToBool`, admitted ONLY on a bare read of a non-bool
-- source under the bool algebra. Same guard shape as the tropical flag above.
def rtbRead (cast : Bool) (unary : Option UnaryOp := none) : ReadPlan :=
  { sourceSlot := 0, map := AffineMap.mk #[#[1]] #[0], sourceShape := #[3]
  , oobPolicy := .zeroPad, unary := unary, realToBool := cast }
-- (the bool algebra needs a `.bool` DESTINATION slot, so these use their own signature tables)
def rtbRealSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .bool } ]
def rtbRealSigs32 : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f32 }, { shape := #[3], dtype := .bool } ]
def rtbBoolSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .bool }, { shape := #[3], dtype := .bool } ]
-- accept: the flag on a real (f64) source under the bool algebra (and the f32 checker on an f32 source)
#guard accepted rtbRealSigs (castPlan admittedAlgebraBool (rtbRead true))
#guard (match checkAssignF32 rtbRealSigs32 (castPlan admittedAlgebraBool (rtbRead true)) with
        | .ok _ => true | _ => false)
-- accept neighbours: no flag (any source) under the bool algebra
#guard accepted rtbRealSigs (castPlan admittedAlgebraBool (rtbRead false))
#guard accepted rtbBoolSigs (castPlan admittedAlgebraBool (rtbRead false))
-- reject: flag on a BOOL source (bool -> bool is the identity)
#guard rejectedCast rtbBoolSigs (castPlan admittedAlgebraBool (rtbRead true))
-- reject: flag under the real algebra, and under a tropical one
#guard rejectedCast realSigs (castPlan admittedAlgebra (rtbRead true))
#guard rejectedCast realSigs (castPlan admittedAlgebraMax (rtbRead true))
-- reject: flag on a unary read (the unary takes real input)
#guard rejectedCast rtbRealSigs (castPlan admittedAlgebraBool (rtbRead true (some .exp)))

/-! ## S3b T6 — a scan state starts at `0_K` of the STATE's sort; a sort-neutral writer of the state
(one bare read, no contracted axis) is evaluated in that sort

The state's sort comes from the scan's own non-neutral statements (`scanStateAlgebra`). Every
program runs in the reference, the binary64 plan and the binary32 plan (`assertAgree`).
(a) RC10 shape (donor `RecurrenceTest` RC10): the unwritten cell `G[0,1]` holds `-inf` (max-plus)
    or `+inf` (min-plus twin); (b) a SUM scan's unwritten cell stays `0`;
(c) a neutral BASE with an out-of-bounds bare read `X0[j+1]` pads with the state's `0_K`: the old
    code evaluated that base as a real `sum` statement and padded `0` (`axis j : ℕ = 3` gives the
    shift an extent); (d) a neutral base bare-reading a PREDICATE tensor is cast bool -> tropical
    (false `-inf`/`+inf`, true `0`), where the old base read the raw 0/1; (f) the compiled plan
    states the sort (`StateSlot.initValue`). (e) a tropical SCRATCH cannot be written in the surface
    (`scanProjectionUnsupported`): its raw-schedule fixture is in `ScanCompileTest`. Min-plus twins
    come from negated data. -/
def stateMax : TLProgram := tlprog!{
  iter r = 2, c = 2
  G[r, 0] := Z[r]
  G[r + 1, c + 1] := maxreduce(G[r, c] · W[r, c, k]) }
def stateMin : TLProgram := tlprog!{
  iter r = 2, c = 2
  G[r, 0] := Z[r]
  G[r + 1, c + 1] := minreduce(G[r, c] · W[r, c, k]) }
def stateSum : TLProgram := tlprog!{
  iter r = 2, c = 2
  G[r, 0] := Z[r]
  G[r + 1, c + 1] := G[r, c] · W[r, c, k] }
def neutralOobMax : TLProgram := tlprog!{
  axis j : ℕ = 3
  iter t = 2
  S[j, 0] := X0[j + 1]
  S[j, t + 1] := maxreduce(S[j, t] · E[j, t, k]) }
def neutralOobMin : TLProgram := tlprog!{
  axis j : ℕ = 3
  iter t = 2
  S[j, 0] := X0[j + 1]
  S[j, t + 1] := minreduce(S[j, t] · E[j, t, k]) }
def neutralPredMax : TLProgram := tlprog!{
  iter t = 2
  predicate P(j)
  S[j, 0] := P[j]
  S[j, t + 1] := maxreduce(S[j, t] · E[j, t, k]) }
def neutralPredMin : TLProgram := tlprog!{
  iter t = 2
  predicate P(j)
  S[j, 0] := P[j]
  S[j, t + 1] := minreduce(S[j, t] · E[j, t, k]) }

def wPos : List Float := [1, 3, 0, 0, 0, 0, 0, 0]
def wNeg : List Float := [-1, -3, 0, 0, 0, 0, 0, 0]
def eZero : List Float := [0, 0, 0, 0, 0, 0]

run_cmd do
  assertAgree "T6-a1 state max-plus" stateMax
    [("Z", [2], [2, 5]), ("W", [2, 2, 2], wPos)] "G" [2, negInf, 5, 5]
  assertAgree "T6-a2 state min-plus" stateMin
    [("Z", [2], [-2, -5]), ("W", [2, 2, 2], wNeg)] "G" [-2, posInf, -5, -5]
  assertAgree "T6-b sum state keeps 0" stateSum
    [("Z", [2], [2, 5]), ("W", [2, 2, 2], wPos)] "G" [2, 0, 5, 8]
  assertAgree "T6-c1 neutral oob max" neutralOobMax
    [("X0", [3], [-1, -2, -3]), ("E", [3, 2, 1], eZero)] "S"
    [-2, -2, -3, -3, negInf, negInf]
  assertAgree "T6-c2 neutral oob min" neutralOobMin
    [("X0", [3], [1, 2, 3]), ("E", [3, 2, 1], eZero)] "S"
    [2, 2, 3, 3, posInf, posInf]
  assertAgree "T6-d1 neutral predicate max" neutralPredMax
    [("P", [3], [1, 0, 1]), ("E", [3, 2, 1], eZero)] "S" [0, 0, negInf, negInf, 0, 0]
  assertAgree "T6-d2 neutral predicate min" neutralPredMin
    [("P", [3], [1, 0, 1]), ("E", [3, 2, 1], eZero)] "S" [0, 0, posInf, posInf, 0, 0]

/-- The `initValue` of every state of every scan step of the binary64 checked plan. -/
def scanInits (p : TLProgram) (xs : Ins) : Except String (List (Array StateInit)) := do
  let sched ← match p.explicitF64.compileToScheduled.run 0 with
    | .ok s _ => .ok s
    | .error e _ => .error s!"compile: {repr e}"
  let sig ← match InputSignature.ofDenseInputsForDecls sched.decls (env64 xs) with
    | .ok s => .ok s
    | .error e => .error s!"signature64: {repr e}"
  let prepared ← match prepareEvalPlan sched sig with
    | .ok q => .ok q
    | .error _ => .error "prepare64 failed"
  pure (prepared.plan.raw.steps.toList.filterMap (fun st => match st with
    | .scan s => some (s.states.map (·.initValue))
    | _ => none))

def assertInits (label : String) (p : TLProgram) (xs : Ins) (expected : List (Array StateInit)) :
    Lean.Elab.Command.CommandElabM Unit :=
  match scanInits p xs with
  | .error e => throwError s!"{label}: {e}"
  | .ok got => unless got == expected do throwError s!"{label}: inits {repr got} ≠ {repr expected}"

-- The compiled plan states the sort: max-plus `negInf`, min-plus `posInf`, real/scratch-only `zero`.
run_cmd do
  let zw := [("Z", [2], [2, 5]), ("W", [2, 2, 2], wPos)]
  assertInits "T6-f1 max-plus init" stateMax zw [#[.negInf]]
  assertInits "T6-f2 min-plus init" stateMin zw [#[.posInf]]
  assertInits "T6-f3 sum init" stateSum zw [#[.zero]]

/-! ## S3b follow-up (h): a tropical scan step reads a BOOL STATE

Every fixture above reads a predicate that is an EXTERNAL input. Here the scan has two states: the
predicate state `P` (bool recurrence `P[j,t+1] := P[j,t] + Q[j]`, base `P[j,0] := Pi[j]`) and a
second state `S` whose step bare-reads `P[j,t]`. The reference casts through `isPredicateDest` on
the state NAME; the plan casts through the capture slot's dtype (`isBoolSlot` on the state capture).
`Pi = [1,0]`, `Q = [0,1]`: `P = [[1,1,1],[0,1,1]]`. Max-plus `S[j,t+1] := maxreduce(S[j,t] · P[j,t])`,
`Z = [-2,-5]`: row 0 reads true (`0`), stays `-2`; row 1 reads false at `t = 0` (`-inf`), so `S[1,1]`
and (`-inf + 0`) `S[1,2]` are `-inf`. The identity read would give `[-2,-1,0,-5,-4,-3]`. Min-plus twin
(`Z = [2,5]`): `[2,2,2,5,+inf,+inf]`. Accept neighbour: a REAL step `S[j,t+1] := S[j,t] + P[j,t]`
reads the same bool state as the plain 0/1: `[2,3,4,5,5,6]`. A structural fixture pins that the
checked plan really does read a bool state, with the cast set exactly on the tropical read (`P`'s own
recurrence is a bool statement and reads its state un-cast). -/
def boolStateMax : TLProgram := tlprog!{
  iter t = 3
  predicate P(j, t)
  P[j, 0] := Pi[j]
  P[j, t + 1] := P[j, t] + Q[j]
  S[j, 0] := Z[j]
  S[j, t + 1] := maxreduce(S[j, t] · P[j, t]) }
def boolStateMin : TLProgram := tlprog!{
  iter t = 3
  predicate P(j, t)
  P[j, 0] := Pi[j]
  P[j, t + 1] := P[j, t] + Q[j]
  S[j, 0] := Z[j]
  S[j, t + 1] := minreduce(S[j, t] · P[j, t]) }
def boolStateReal : TLProgram := tlprog!{
  iter t = 3
  predicate P(j, t)
  P[j, 0] := Pi[j]
  P[j, t + 1] := P[j, t] + Q[j]
  S[j, 0] := Z[j]
  S[j, t + 1] := S[j, t] + P[j, t] }

def hIns (z : List Float) : Ins := [("Pi", [2], [1, 0]), ("Q", [2], [0, 1]), ("Z", [2], z)]

/-- For each factor of the binary64 checked plan's scan step blocks that reads a captured BOOL
    state, its `boolToTropical` flag. -/
def boolStateReadCasts (p : TLProgram) (xs : Ins) : Except String (List Bool) := do
  let sched ← match p.explicitF64.compileToScheduled.run 0 with
    | .ok s _ => .ok s
    | .error e _ => .error s!"compile: {repr e}"
  let sig ← match InputSignature.ofDenseInputsForDecls sched.decls (env64 xs) with
    | .ok s => .ok s
    | .error e => .error s!"signature64: {repr e}"
  let prepared ← match prepareEvalPlan sched sig with
    | .ok q => .ok q
    | .error _ => .error "prepare64 failed"
  let sigs := prepared.plan.raw.tensorSigs
  pure (prepared.plan.raw.steps.toList.flatMap (fun st => match st with
    | .scan s =>
        let boolInputs := s.stepCaptures.toList.filterMap (fun c => match c.source with
          | .state si =>
              if (sigs.getD (s.states.getD si default).destSlot { shape := #[], dtype := .f64 }).dtype
                  == .bool then some c.inputSlot else none
          | .external _ => none)
        s.stepBlock.steps.toList.flatMap (fun b => match b with
          | .assign a => a.terms.toList.flatMap (fun t => t.factors.toList.filterMap (fun f =>
              match f with
              | .read r => if boolInputs.contains r.sourceSlot then some r.boolToTropical else none
              | _ => none))
          | _ => [])
    | _ => []))

def assertCasts (label : String) (p : TLProgram) (xs : Ins) (expected : List Bool) :
    Lean.Elab.Command.CommandElabM Unit :=
  match boolStateReadCasts p xs with
  | .error e => throwError s!"{label}: {e}"
  | .ok got => unless got == expected do throwError s!"{label}: casts {got} ≠ {expected}"

run_cmd do
  assertAgree "h1 bool state max" boolStateMax (hIns [-2, -5]) "S"
    [-2, -2, -2, -5, negInf, negInf]
  assertAgree "h2 bool state min" boolStateMin (hIns [2, 5]) "S"
    [2, 2, 2, 5, posInf, posInf]
  assertAgree "h3 bool state real neighbour" boolStateReal (hIns [2, 5]) "S" [2, 3, 4, 5, 5, 6]
  -- `P`'s own recurrence reads its bool state un-cast (a bool statement); only `S`'s step casts
  assertCasts "h1 cast flag" boolStateMax (hIns [-2, -5]) [false, true]
  assertCasts "h2 cast flag" boolStateMin (hIns [2, 5]) [false, true]
  assertCasts "h3 cast flag" boolStateReal (hIns [2, 5]) [false, false]

/-! ## S3b follow-up (i): a NaN stored in a PREDICATE tensor, read through the bool -> tropical cast

CURRENT CONVENTION, pinned and not endorsed as final (the intent is that truth is `!= 0`): a stored
NaN is not `0`, so it reads as TRUE in a tropical statement, i.e. `1_K = 0.0` — and the NaN
disappears. Every other reader keeps it: a bool -> real statement multiplies it through, a
real -> tropical read (not cast) adds it and the NaN-propagating `max`/`min` carries it, and a bool
statement keeps it too. `edge = [[NaN,1],[0,1]]`, so the cast programs equal `a1`/`a2` on `[[1,1],[0,1]]`
(a NaN read as FALSE would give row 0 `[-3,-4]` / `[3,4]`). Cells compare NaN-aware (`both NaN`). -/
def nan : Float := 0.0 / 0.0
def nanEq (a b : Float) : Bool := (a.isNaN && b.isNaN) || a == b

def assertAgreeNaN (label : String) (p : TLProgram) (xs : Ins) (nm : String)
    (expected : List Float) : Lean.Elab.Command.CommandElabM Unit :=
  match agreeWith nanEq label p xs nm expected with
  | .ok () => pure ()
  | .error e => throwError e

/-- A program with no `f32` tensor runs the plan in binary64 only (the binary32 entry refuses it with
    `storageKindMismatch`), so the bool-statement neighbour compares the reference and binary64 plan. -/
def agreeNaN64 (label : String) (p : TLProgram) (xs : Ins) (nm : String) (expected : List Float) :
    Lean.Elab.Command.CommandElabM Unit :=
  match (do
    let r ← refOut p xs nm
    let a ← planOut64 p xs nm
    let same : List Float → Bool := fun v =>
      v.length == expected.length && (v.zip expected).all (fun (x, y) => nanEq x y)
    unless same r do throw s!"{label}: reference {r} ≠ {expected}"
    unless same a do throw s!"{label}: plan f64 {a} ≠ {expected}" : Except String Unit) with
  | .ok () => pure ()
  | .error e => throwError e

def boolStmt : TLProgram := tlprog!{
  predicate edge(i, j)
  predicate M(i)
  M[i] := edge[i, j] }

run_cmd do
  let edgeNaN : List Float := [nan, 1, 0, 1]
  assertAgreeNaN "i1 NaN predicate max" bareMax
    [("edge", [2, 2], edgeNaN), ("X", [2, 2], [-1, -2, -3, -4])] "H" [-1, -2, -3, -4]
  assertAgreeNaN "i2 NaN predicate min" bareMin
    [("edge", [2, 2], edgeNaN), ("X", [2, 2], [1, 2, 3, 4])] "H" [1, 2, 3, 4]
  assertAgreeNaN "i3 NaN kept by bool->real" boolReal
    [("edge", [2, 2], edgeNaN), ("X", [2, 2], [-1, -2, -3, -4])] "H" [nan, nan, -3, -4]
  assertAgreeNaN "i4 NaN kept by real->max (no cast)" realMax
    [("A", [2, 2], edgeNaN), ("X", [2, 2], [-1, -2, -3, -4])] "H" [nan, nan, -1, -2]
  assertAgreeNaN "i5 NaN kept by real->min (no cast)" realMin
    [("A", [2, 2], edgeNaN), ("X", [2, 2], [1, 2, 3, 4])] "H" [nan, nan, 1, 2]
  agreeNaN64 "i6 NaN kept by a bool statement" boolStmt
    [("edge", [2, 2], edgeNaN)] "M" [nan, 1]

/-! ## S3b-ii T3b (j): a `real -> bool` read COERCES (D1): a predicate statement's bare read of a
non-predicate source sees truth `stored != 0`, as 1 / 0, on reference, binary64 plan and binary32 plan

`X = {0.25, 0.75, 0, NaN, -2}` (NaN reads TRUE, the same convention as (i): pinned, not endorsed) into a
predicate `P` gives `{1, 1, 0, 1, 1}`; the identity read (the pre-D1 behaviour) gives `{0.25, 0.75, 0,
NaN, 0}` (the Boolean accumulator's `max(0, min(1, v))`). One fixture per plan CALLER of
`residualizeAssignment` that can carry a predicate destination: top-level plain assign, scan BASE and scan
STEP. The fourth caller, a scatter compute half, can never see one: `capabilityPreflight` rejects a
predicate scatter destination (`predicateScatterDest`), so its flag is structurally always false.
Neighbours: a bool source is unchanged (identity, NaN kept), a unary-function read is not coerced, the
out-of-range pad is not coerced. -/
def rtbTop : TLProgram := tlprog!{
  predicate P(i)
  P[i] := X[i] }
def rtbBoolSrc : TLProgram := tlprog!{
  predicate Q(i)
  predicate P(i)
  P[i] := Q[i] }
def rtbUnary : TLProgram := tlprog!{
  predicate P(i)
  P[i] := sqrt(X[i]) }
def rtbOob : TLProgram := tlprog!{
  axis i : ℕ = 3
  predicate P(i)
  P[i] := X[i + 1] }
def rtbScanBase : TLProgram := tlprog!{
  iter t = 3
  predicate S(j, t)
  S[j, 0] := X[j]
  S[j, t + 1] := S[j, t] }
def rtbScanStep : TLProgram := tlprog!{
  iter t = 3
  predicate S(j, t)
  predicate B(j)
  S[j, 0] := B[j]
  S[j, t + 1] := S[j, t] · Y[j] }

def rtbReal : List Float := [0.25, 0.75, 0, nan, -2]

run_cmd do
  assertAgree "j1 top-level real->bool" rtbTop [("X", [5], rtbReal)] "P" [1, 1, 0, 1, 1]
  assertAgree "j2 binary source unchanged" rtbTop [("X", [5], [1, 0, 1, 1, 0])] "P" [1, 0, 1, 1, 0]
  agreeNaN64 "j3 bool source unchanged (identity, NaN kept)" rtbBoolSrc [("Q", [5], rtbReal)] "P"
    [0.25, 0.75, 0, nan, 0]
  assertAgree "j4 unary read not coerced" rtbUnary [("X", [2], [0.25, 4])] "P" [0.5, 1]
  assertAgree "j5 pad not coerced" rtbOob [("X", [3], [0.25, 0, -2])] "P" [0, 1, 0]
  assertAgree "j6 scan base" rtbScanBase [("X", [5], rtbReal)] "S"
    [1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1]
  assertAgree "j7 scan step" rtbScanStep
    [("B", [5], [1, 1, 1, 1, 1]), ("Y", [5], rtbReal)] "S"
    [1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1]

end LeanNCD.Eval.Plan.BoolCastTest

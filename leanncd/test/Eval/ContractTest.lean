import Eval.ExplicitF64
import LeanNCD.Eval.Contract
import LeanNCD.Eval.SizeInfer   -- `inferAxisSizes`, used directly below (was transitive via `Eval.Shape`)
namespace LeanNCD.Eval
open Std
private def ax (nm : String) (u : Nat) : AxisSpec := { name := nm, uid := u, kind := .real }
private def tensorOf (shape : List Nat) (xs : List Float) : DenseTensor := ⟨shape, xs.toArray⟩

-- W (2×3) · X (3×2) = known 2×2 product.
-- W = [[1,2,3],[4,5,6]], X = [[1,0],[0,1],[1,1]]  ⇒  W·X = [[4,5],[10,11]]
run_cmd do
  let i := ax "i" 1; let k := ax "k" 2; let j := ax "j" 3
  let W := tensorOf [2,3] [1,2,3, 4,5,6]
  let X := tensorOf [3,2] [1,0, 0,1, 1,1]
  let env : HashMap String DenseTensor := (({} : HashMap String DenseTensor).insert "W" W).insert "X" X
  let mm : Stmt := .assign "Y" [.free i, .free j]
    { body := { terms := [{ factors := [.read "W" [.axis i, .axis k], .read "X" [.axis k, .axis j]] }] }, nonlin := .identity }
  match inferAxisSizes {} env [mm] with
  | .error e => throwError (toString e)
  | .ok (sizes, _) =>
    match evalAssign env sizes "Y" [.free i, .free j] { body := { terms := [{ factors := [.read "W" [.axis i, .axis k], .read "X" [.axis k, .axis j]] }] }, nonlin := .identity } with
    | .error e => throwError (toString e)
    | .ok (_, Y) =>
        let expected := tensorOf [2,2] [4,5, 10,11]
        unless DenseTensor.approxEq Y expected do throwError s!"matmul wrong: {repr Y.data}"

-- elementwise sum of two terms: Z[i] := A[i] + B[i]  (A=[1,2,3], B=[10,20,30]) ⇒ [11,22,33]
run_cmd do
  let i := ax "i" 1
  let A := tensorOf [3] [1,2,3]; let B := tensorOf [3] [10,20,30]
  let env : HashMap String DenseTensor := (({} : HashMap String DenseTensor).insert "A" A).insert "B" B
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "A" [.axis i]] }, { factors := [.read "B" [.axis i]] }] }, nonlin := .identity }
  match inferAxisSizes {} env [.assign "Z" [.free i] rhs] with
  | .error e => throwError (toString e)
  | .ok (sizes, _) => match evalAssign env sizes "Z" [.free i] rhs with
    | .error e => throwError (toString e)
    | .ok (_, Z) => unless DenseTensor.approxEq Z (tensorOf [3] [11,22,33]) do throwError "sum wrong"

-- missing input tensor ⇒ .error (not silent 0)
run_cmd do
  let i := ax "i" 1
  let A := tensorOf [3] [1,2,3]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "A" A
  let sizes : HashMap UID Nat := ({} : HashMap UID Nat).insert 1 3
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "MISSING" [.axis i]] }] }, nonlin := .identity }
  match evalAssign env sizes "Q" [.free i] rhs with
  | .error _ => pure ()
  | .ok _ => throwError "expected error for missing input tensor"

-- Masked aggregation: Result[] := F[t,i]·F[t,j]·edge[i,j], all axes contracted ⇒ scalar.
-- F : [1,2] (t=1, i/j=2): F = [[1, 1]] (so F[0,0]=1, F[0,1]=1). edge : [2,2] = [[1,0],[0,1]] (identity).
-- ℝ reading: Σ_{t,i,j} F[t,i]·F[t,j]·edge[i,j] = (i=j terms) F[0,0]²·1 + F[0,1]²·1 = 1 + 1 = 2.
run_cmd do
  let t := ax "t" 1; let i := ax "i" 2; let j := ax "j" 3
  let F := tensorOf [1,2] [1, 1]
  let edge := tensorOf [2,2] [1,0, 0,1]
  let env : HashMap String DenseTensor := (({} : HashMap String DenseTensor).insert "F" F).insert "edge" edge
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "F" [.axis t, .axis i], .read "F" [.axis t, .axis j], .read "edge" [.axis i, .axis j]] }] }, nonlin := .identity }
  match inferAxisSizes {} env [.assign "Result" [] rhs] with
  | .error e => throwError (toString e)
  | .ok (sizes, _) =>
    -- ℝ (tensor) reading ⇒ scalar 2.0
    match evalAssignDtypedF64 [.typedTensor .f64 "Result" []] env sizes "Result" [] rhs with
    | .error e => throwError (toString e)
    | .ok (_, R) => unless DenseTensor.approxEq R (tensorOf [] [2.0]) do throwError s!"ℝ agg wrong: {repr R.data}"
    -- Boolean (predicate) reading ⇒ ∃ t,i,j with all-1 ⇒ 1.0 (there is such a term)
    match evalAssignDtypedF64 [.predicate "Result" []] env sizes "Result" [] rhs with
    | .error e => throwError (toString e)
    | .ok (_, R) => unless DenseTensor.approxEq R (tensorOf [] [1.0]) do throwError s!"Bool agg wrong: {repr R.data}"
    -- Task 4.1 fixture 5: an EARLIER `.axis` declaration whose axis name is also `Result` must not
    -- hide the later `predicate Result`. `combineFor` scans tensor-bearing declarations only, so
    -- this still selects the Boolean algebra (1.0); a scan over ALL declarations would find the
    -- axis first and silently fall back to real sum-product (2.0).
    match evalAssignDtypedF64
        [.axis { name := "Result", uid := 99, kind := .real } none, .predicate "Result" []]
        env sizes "Result" [] rhs with
    | .error e => throwError (toString e)
    | .ok (_, R) => unless DenseTensor.approxEq R (tensorOf [] [1.0]) do
        throwError s!"axis-shadowed Bool agg wrong: {repr R.data} (an axis decl hid the predicate)"

/-! ### f32 Task 1, fixtures 8-10: the direct assignment entries refuse f32 operands

Fixtures 8 and 9 reuse the masked-aggregation fixture above verbatim — same `Result` destination,
same `F`/`edge` reads, same environment, sizes, slots, and RHS — varying only the declarations (and,
in fixture 9, deleting `F` from the environment). -/

run_cmd do
  let t := ax "t" 1; let i := ax "i" 2; let j := ax "j" 3
  let F := tensorOf [1,2] [1, 1]
  let edge := tensorOf [2,2] [1,0, 0,1]
  let env : HashMap String DenseTensor := (({} : HashMap String DenseTensor).insert "F" F).insert "edge" edge
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "F" [.axis t, .axis i], .read "F" [.axis t, .axis j], .read "edge" [.axis i, .axis j]] }] }, nonlin := .identity }
  let seed : HashMap UID Int := {}
  match inferAxisSizes {} env [.assign "Result" [] rhs] with
  | .error e => throwError (toString e)
  | .ok (sizes, _) => do
    -- Fixture 8: only the DESTINATION is f32. The deepest entry refuses it, naming `Result`.
    match evalAssignDtypedSeededF64 [.typedTensor .f32 "Result" []] env sizes seed "Result" [] rhs with
    | Except.error (.unsupportedDtype "Result") => pure ()
    | Except.error e => throwError s!"fixture 8 (seeded): wrong error {e}"
    | Except.ok _ => throwError "fixture 8 (seeded): an f32 destination was evaluated as Float"
    -- and the unseeded wrapper inherits exactly that rejection.
    match evalAssignDtypedF64 [.typedTensor .f32 "Result" []] env sizes "Result" [] rhs with
    | Except.error (.unsupportedDtype "Result") => pure ()
    | Except.error e => throwError s!"fixture 8 (unseeded): wrong error {e}"
    | Except.ok _ => throwError "fixture 8 (unseeded): an f32 destination was evaluated as Float"
    -- Fixture 8, dual-invalid subcase: `Result` is ALSO declared tensor-bearing twice. The shared
    -- declaration builder runs first, so the malformed declaration list is what is reported — proof
    -- that this entry reuses `buildDeclEnv` rather than scanning `decls` itself.
    match evalAssignDtypedSeededF64 [.typedTensor .f32 "Result" [], .typedTensor .f64 "Result" []]
        env sizes seed "Result" [] rhs with
    | Except.error (.compile (.duplicateTensorDecl "Result")) => pure ()
    | Except.error e => throwError s!"fixture 8 (dual-invalid): wrong error {e}"
    | Except.ok _ => throwError "fixture 8 (dual-invalid): a duplicate declaration was accepted"

-- Fixture 9: the same donor with `Result` back to f64 and the READ SOURCE `F` f32, while `F` is
-- simultaneously absent from the environment. The dtype refusal precedes `evalAssignSeeded`'s
-- missing-input check, and it names `F`, not the destination. Its own `run_cmd` so it reports
-- independently of fixture 8 rather than being short-circuited by it.
run_cmd do
  let t := ax "t" 1; let i := ax "i" 2; let j := ax "j" 3
  let F := tensorOf [1,2] [1, 1]
  let edge := tensorOf [2,2] [1,0, 0,1]
  let env : HashMap String DenseTensor := (({} : HashMap String DenseTensor).insert "F" F).insert "edge" edge
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "F" [.axis t, .axis i], .read "F" [.axis t, .axis j], .read "edge" [.axis i, .axis j]] }] }, nonlin := .identity }
  let seed : HashMap UID Int := {}
  match inferAxisSizes {} env [.assign "Result" [] rhs] with
  | .error e => throwError (toString e)
  | .ok (sizes, _) => do
    let envNoF : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "edge" edge
    let decls9 : List Decl := [.typedTensor .f64 "Result" [], .typedTensor .f32 "F" [t, i]]
    match evalAssignDtypedSeededF64 decls9 envNoF sizes seed "Result" [] rhs with
    | Except.error (.unsupportedDtype "F") => pure ()
    | Except.error e => throwError s!"fixture 9 (seeded): wrong error {e}"
    | Except.ok _ => throwError "fixture 9 (seeded): an f32 read source was gathered as Float"
    match evalAssignDtypedF64 decls9 envNoF sizes "Result" [] rhs with
    | Except.error (.unsupportedDtype "F") => pure ()
    | Except.error e => throwError s!"fixture 9 (unseeded): wrong error {e}"
    | Except.ok _ => throwError "fixture 9 (unseeded): an f32 read source was gathered as Float"

-- Fixture 10: the accepted identity assignment `Y[i] := A[i]`, with the destination AND every read
-- source f32 — a HOMOGENEOUS f32 assignment, in which no two operands disagree. A guard that
-- rejected only mixed modes would accept and silently execute this in binary64; the refusal names
-- the destination `Y`.
run_cmd do
  let i := ax "i" 1
  let A := tensorOf [3] [1, 2, 3]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "A" A
  let sizes : HashMap UID Nat := ({} : HashMap UID Nat).insert 1 3
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "A" [.axis i]] }] }, nonlin := .identity }
  let decls : List Decl := [.typedTensor .f32 "Y" [i], .typedTensor .f32 "A" [i]]
  let seed : HashMap UID Int := {}
  match evalAssignDtypedSeededF64 decls env sizes seed "Y" [LHSSlot.free i] rhs with
  | Except.error (.unsupportedDtype "Y") => pure ()
  | Except.error e => throwError s!"fixture 10 (seeded): wrong error {e}"
  | Except.ok _ => throwError "fixture 10 (seeded): a homogeneous f32 assignment was accepted"
  match evalAssignDtypedF64 decls env sizes "Y" [LHSSlot.free i] rhs with
  | Except.error (.unsupportedDtype "Y") => pure ()
  | Except.error e => throwError s!"fixture 10 (unseeded): wrong error {e}"
  | Except.ok _ => throwError "fixture 10 (unseeded): a homogeneous f32 assignment was accepted"

-- 4b: a term with an EMPTY factor list must fold to the Combine's `unit1`, not a hard-coded 1.0.
-- Use a synthetic min-plus-style Combine (mul = add, combine = min) to make the difference
-- observable: if the product fold still started from a literal 1.0, this would wrongly give
-- combine(unit0, 1.0) = min(+inf, 1.0) = 1.0 instead of the correct min(+inf, 0.0) = 0.0.
run_cmd do
  let minPlus : Combine := { mul := (· + ·), combine := Min.min, unit0 := 1.0 / 0.0, unit1 := 0.0 }
  let env : HashMap String DenseTensor := {}
  let rhs : RHSExpr := { body := { terms := [{ factors := [] }] }, nonlin := .identity }
  match evalAssignWith minPlus.mul minPlus.combine minPlus.unit0 minPlus.unit1 env {} "Z" [] rhs with
  | .error e => throwError s!"4b empty-product: unexpected error {e}"
  | .ok (_, Z) => unless DenseTensor.approxEq Z (tensorOf [] [0.0]) do
      throwError s!"4b empty-product: got {repr Z.data}, want [0.0] (unit1 not threaded through)"

-- 4a: an out-of-range seed coordinate must be rejected.
-- (mul/combine bound to explicitly-typed `let`s, and LHSSlot/Except spelled out rather than
-- dot notation — passing `(· * ·)`/`(· + ·)` inline stalls expected-type propagation for the
-- `slots` argument, breaking plain `.iterAt`/`.free`/`.error`/`.ok`; caught while executing Task 1.)
run_cmd do
  let k := ax "k" 2
  let X := tensorOf [2] [1, 2]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes : HashMap UID Nat := ({} : HashMap UID Nat).insert 2 2
  let seed : HashMap UID Int := ({} : HashMap UID Int).insert 2 5   -- 5 ∉ [0, 2)
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis k]] }] }, nonlin := .identity }
  let mul : Float → Float → Float := (· * ·)
  let combine : Float → Float → Float := (· + ·)
  match evalAssignSeeded mul combine 0.0 1.0 env sizes seed "Y" [LHSSlot.iterAt k 0] rhs with
  | Except.error (.invalidSeed "Y" 2 5 2) => pure ()
  | Except.error e => throwError s!"4a: wrong error for out-of-range seed: {e}"
  | Except.ok _    => throwError "4a: expected rejection of out-of-range seed coordinate 5 ∉ [0, 2)"

-- 4a: empty seed gives the same result as the unseeded wrapper (evalAssignWith IS
-- evalAssignSeeded with seed = {} — this is the definitional check for the unification).
run_cmd do
  let i := ax "i" 1
  let A := tensorOf [3] [1, 2, 3]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "A" A
  let sizes : HashMap UID Nat := ({} : HashMap UID Nat).insert 1 3
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "A" [.axis i]] }] }, nonlin := .identity }
  let mul : Float → Float → Float := (· * ·)
  let combine : Float → Float → Float := (· + ·)
  match evalAssignWith mul combine 0.0 1.0 env sizes "Y" [LHSSlot.free i] rhs,
        evalAssignSeeded mul combine 0.0 1.0 env sizes {} "Y" [LHSSlot.free i] rhs with
  | Except.ok (_, a), Except.ok (_, b) => unless DenseTensor.approxEq a b do
      throwError s!"4a: evalAssignWith {repr a.data} ≠ evalAssignSeeded-with-empty-seed {repr b.data}"
  | _, _ => throwError "4a: one of the two calls errored unexpectedly"

-- S3b-i task T1: `Combine.max`/`Combine.min` are the semirings max-plus `(+, max, −∞, 0)` and min-plus
-- `(+, min, +∞, 0)`, and every `Combine`'s ⊕/⊗ on binary64 is NaN-propagating where it is max/min.

-- ⊗ is `+` with identity `0.0` (before S3b-i it was `*` with identity `1.0`); ⊕ identity is `∓∞`.
#guard Combine.max.mul 2.0 3.0 == 5.0 && Combine.max.unit1 == 0.0 && Combine.max.unit0 == -1.0 / 0.0
#guard Combine.min.mul 2.0 3.0 == 5.0 && Combine.min.unit1 == 0.0 && Combine.min.unit0 == 1.0 / 0.0
-- Accept-neighbour: the real semiring keeps `*` / `+` with `1.0` / `0.0`.
#guard Combine.real.mul 2.0 3.0 == 6.0 && Combine.real.unit1 == 1.0 && Combine.real.unit0 == 0.0
-- Accept-neighbour: non-NaN max/min behave as before.
#guard Combine.max.combine 1.0 2.0 == 2.0 && Combine.max.combine 2.0 1.0 == 2.0
#guard Combine.min.combine 1.0 2.0 == 1.0 && Combine.min.combine 2.0 1.0 == 1.0

-- Negation duality: `min-plus(x) = −max-plus(−x)`, for ⊗ and ⊕ and the identities.
#guard Combine.min.mul 2.0 3.0 == -(Combine.max.mul (-2.0) (-3.0))
#guard Combine.min.combine 1.0 2.0 == -(Combine.max.combine (-1.0) (-2.0))
#guard Combine.min.unit0 == -Combine.max.unit0

private def nanF : Float := 0.0 / 0.0

-- NaN propagation: a NaN in EITHER argument position is the result, for the tropical ⊕ and both
-- Boolean operations (`min` for ∧, `max` for ∃). Lean's `Max.max` drops a NaN second operand and
-- `Min.min` a NaN first operand, so each position catches one of the unfixed operators.
#guard (Combine.max.combine nanF 1.0).isNaN && (Combine.max.combine 1.0 nanF).isNaN
#guard (Combine.min.combine nanF 1.0).isNaN && (Combine.min.combine 1.0 nanF).isNaN
#guard (Combine.bool.mul nanF 1.0).isNaN && (Combine.bool.mul 1.0 nanF).isNaN
#guard (Combine.bool.combine nanF 1.0).isNaN && (Combine.bool.combine 1.0 nanF).isNaN
-- The shared helpers directly, binary64 and binary32.
#guard (maxNaN nanF 1.0).isNaN && (maxNaN 1.0 nanF).isNaN && (minNaN nanF 1.0).isNaN && (minNaN 1.0 nanF).isNaN
#guard (maxNaN32 (Float32.ofBits 0x7fc00000) (Float32.ofBits 0x3f800000)).isNaN
#guard (maxNaN32 (Float32.ofBits 0x3f800000) (Float32.ofBits 0x7fc00000)).isNaN
#guard (minNaN32 (Float32.ofBits 0x7fc00000) (Float32.ofBits 0x3f800000)).isNaN
#guard (minNaN32 (Float32.ofBits 0x3f800000) (Float32.ofBits 0x7fc00000)).isNaN
-- Accept-neighbour (binary32): non-NaN operands behave as `max`/`min`.
#guard maxNaN32 (Float32.ofBits 0x3f800000) (Float32.ofBits 0x40000000) == Float32.ofBits 0x40000000
#guard minNaN32 (Float32.ofBits 0x3f800000) (Float32.ofBits 0x40000000) == Float32.ofBits 0x3f800000

-- S3b T2 (reference; regression pins, the folds are seeded with the `Combine` identities): the empty
-- product is `1_K` (tropical: 0.0), the empty sum and a zero-extent reduction are `0_K` (−∞ / +∞).
-- Each case runs under max-plus, min-plus (duality twin) and real (accept-neighbour).
private def negInfC : Float := -1.0 / 0.0
private def posInfC : Float := 1.0 / 0.0
private def refRows (c : Combine) (rhs : RHSExpr) : Option (Array Float) :=
  let i := ax "i" 1; let k := ax "k" 2
  let X : DenseTensor := ⟨[3, 0], #[]⟩
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let sizes : HashMap UID Nat := (({} : HashMap UID Nat).insert 1 3).insert 2 0
  match evalAssignWith c.mul c.combine c.unit0 c.unit1 env sizes "Y" [.free i] rhs with
  | .ok (_, Y) => some Y.data
  | .error _ => none
private def emptyProdRhs : RHSExpr := { body := { terms := [{ factors := [] }] }, nonlin := .identity }
private def emptySumRhs : RHSExpr := { body := { terms := [] }, nonlin := .identity }
private def zeroExtRhs : RHSExpr :=
  { body := { terms := [{ factors := [.read "X" [.axis (ax "i" 1), .axis (ax "k" 2)]] }] }, nonlin := .identity }
#guard refRows Combine.max emptyProdRhs == some #[0.0, 0.0, 0.0]
#guard refRows Combine.min emptyProdRhs == some #[0.0, 0.0, 0.0]
#guard refRows Combine.real emptyProdRhs == some #[1.0, 1.0, 1.0]
#guard refRows Combine.max emptySumRhs == some #[negInfC, negInfC, negInfC]
#guard refRows Combine.min emptySumRhs == some #[posInfC, posInfC, posInfC]
#guard refRows Combine.real emptySumRhs == some #[0.0, 0.0, 0.0]
#guard refRows Combine.max zeroExtRhs == some #[negInfC, negInfC, negInfC]
#guard refRows Combine.min zeroExtRhs == some #[posInfC, posInfC, posInfC]
#guard refRows Combine.real zeroExtRhs == some #[0.0, 0.0, 0.0]

-- S3b-ii T3a (D1, reference side): a `real -> bool` READ COERCES. A `predicate` destination reading
-- a non-predicate (real) tensor with a BARE read sees truth = (stored != 0), mapped to 1.0 / 0.0 —
-- the same rule as the bool -> tropical cast (`boolReadCast`). NaN `!= 0`, so it reads TRUE: this is
-- the existing convention, PINNED here, not endorsed. (The plan layer follows in T3b.)
private def d1Same (a b : Array Float) : Bool :=
  a.size == b.size && (a.zip b).all fun (x, y) => x == y || (x.isNaN && y.isNaN)
private def d1Nan : Float := 0.0 / 0.0
private def d1Real : DenseTensor := tensorOf [5] [0.25, 0.75, 0, d1Nan, -2]
private def d1Rhs (f : Factor) : RHSExpr := { body := { terms := [{ factors := [f] }] }, nonlin := .identity }
private def d1Run (decls : List Decl) (x : DenseTensor) (n : Nat) (slots : List LHSSlot) (f : Factor) :
    Except EvalError DenseTensor :=
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" x
  let sizes : HashMap UID Nat := ({} : HashMap UID Nat).insert 1 n
  (evalPlainF64 decls env sizes (.assign "R" slots (d1Rhs f))).map (·.2)

-- real source {0.25, 0.75, 0, NaN, -2} read by a bare predicate statement ⇒ {1, 1, 0, 1, 1}
run_cmd do
  match d1Run [.predicate "R" []] d1Real 5 [.free (ax "i" 1)] (.read "X" [.axis (ax "i" 1)]) with
  | .error e => throwError s!"D1 real->bool bare read: {e}"
  | .ok R => unless d1Same R.data #[1, 1, 0, 1, 1] do throwError s!"D1 real->bool coerce: {repr R.data}"

-- the SAME program with a BOOL source is unchanged: the predicate source is read as stored (the
-- statement is `max(0, min(1, v))`, so a stored 0.25 stays 0.25, NaN stays NaN and -2 floors at 0:
-- the Boolean accumulator's own arithmetic, no coerce on bool -> bool).
run_cmd do
  match d1Run [.predicate "R" [], .predicate "X" []] d1Real 5 [.free (ax "i" 1)]
      (.read "X" [.axis (ax "i" 1)]) with
  | .error e => throwError s!"D1 bool->bool unchanged: {e}"
  | .ok R => unless d1Same R.data #[0.25, 0.75, 0, d1Nan, 0] do
      throwError s!"D1 bool->bool must stay uncoerced: {repr R.data}"

-- binary-valued real source: unchanged ({0,1} is its own truth image)
run_cmd do
  match d1Run [.predicate "R" []] (tensorOf [5] [1, 0, 1, 1, 0]) 5 [.free (ax "i" 1)]
      (.read "X" [.axis (ax "i" 1)]) with
  | .error e => throwError s!"D1 binary: {e}"
  | .ok R => unless d1Same R.data #[1, 0, 1, 1, 0] do throwError s!"D1 binary: {repr R.data}"

-- a CONTRACTED axis: `R[] := X[k]` is an ∃ over the coerced bare reads: X = [0.25, 0, 0, 0, 0]
-- ⇒ 1 (uncoerced it would be 0.25).
run_cmd do
  match d1Run [.predicate "R" []] (tensorOf [5] [0.25, 0, 0, 0, 0]) 5 [] (.read "X" [.axis (ax "i" 1)]) with
  | .error e => throwError s!"D1 contracted: {e}"
  | .ok R => unless d1Same R.data #[1] do throwError s!"D1 contracted: {repr R.data}"

-- a UNARY-FUNCTION read is NOT coerced (the primitive takes real input; the cast is bare reads
-- only, exactly as for the bool -> tropical cast): R[i] := sqrt(X[i]), X = [0.25, 4] ⇒ the Boolean
-- ∧ with 1 gives min(1, 0.5) = 0.5 and min(1, 2) = 1 (a coerced read would give sqrt(1) = 1 twice).
run_cmd do
  match d1Run [.predicate "R" []] (tensorOf [2] [0.25, 4]) 2 [.free (ax "i" 1)]
      (.unaryFn .sqrt "X" [.axis (ax "i" 1)]) with
  | .error e => throwError s!"D1 unary: {e}"
  | .ok R => unless d1Same R.data #[0.5, 1] do throwError s!"D1 unary read must not coerce: {repr R.data}"

-- the OUT-OF-RANGE PAD is not coerced: R[i] := X[i+1], X = [0.25, 0.75] ⇒ [1, 0] (the pad is the
-- Boolean 0_K = 0.0; for a Boolean statement the coerce could not change it, so this pins the shape).
run_cmd do
  match d1Run [.predicate "R" []] (tensorOf [2] [0.25, 0.75]) 2 [.free (ax "i" 1)]
      (.read "X" [.shift (ax "i" 1) 1]) with
  | .error e => throwError s!"D1 pad: {e}"
  | .ok R => unless d1Same R.data #[1, 0] do throwError s!"D1 pad: {repr R.data}"

-- a tropical (`agg = .max`) statement into a predicate-named destination is NOT a Boolean
-- statement (`combineFor`: agg first): its real source reads stay the identity.
run_cmd do
  let i := ax "i" 1
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := .identity, agg := .max }
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" (tensorOf [2] [0.25, 0.75])
  match evalPlainF64 [.predicate "R" []] env (({} : HashMap UID Nat).insert 1 2) (.assign "R" [] rhs) with
  | .error e => throwError s!"D1 max agg: {e}"
  | .ok (_, R) => unless d1Same R.data #[0.75] do throwError s!"D1 max agg identity: {repr R.data}"


end LeanNCD.Eval

import LeanNCD.Eval.Tensor
import LeanNCD.Eval.Error
import LeanNCD.DSL.Ast
namespace LeanNCD.Eval
open Std

/-- Evaluate an index expression at a coordinate assignment → an integer coordinate. -/
def evalIdx (coord : HashMap UID Int) : IdxExpr → Int
  | .axis a      => (coord[a.uid]?).getD 0
  | .const n     => n
  | .scale c a   => c * (coord[a.uid]?).getD 0
  | .shift a n   => (coord[a.uid]?).getD 0 + n
  | .affine n xs => xs.foldl (fun acc (c, a) => acc + c * (coord[a.uid]?).getD 0) n

/-- Evaluate predicate arithmetic (PredArith) at a coordinate → Int. -/
def evalPred (coord : HashMap UID Int) : PredArith → Int
  | .embed e => evalIdx coord e
  | .mul a b => evalPred coord a * evalPred coord b
  | .iabs a  => ((evalPred coord a).natAbs : Int)        -- |·| ; natAbs : Nat, cast back to Int

/-- Evaluate a Boolean/mask predicate at a coordinate → Bool.
    NB: `.ieq` is the modular/wrapping equality of the DSL; here we approximate it with
    structural Int equality (`==`), which coincides whenever no wraparound occurs. -/
def evalBool (coord : HashMap UID Int) : BoolExpr → Bool
  | .rel op a b =>
      let x := evalPred coord a
      let y := evalPred coord b
      match op with
      | .lt => x < y
      | .le => x ≤ y
      | .eq => x = y
      | .ne => x ≠ y
      | .ge => x ≥ y
      | .gt => x > y
  | .and a b => evalBool coord a && evalBool coord b
  | .or  a b => evalBool coord a || evalBool coord b
  | .not a   => ! evalBool coord a
  | .ieq a b => evalPred coord a == evalPred coord b

/-- Read a tensor at a coordinate: bounds-checked; an out-of-range coordinate yields `pad`. Shared by
    `gather`'s `.read` and `.unaryFn` cases — a `.unaryFn` factor reads identically to a plain
    `.read` (with its own `pad`, see `gather`), then applies its function to the resulting value. -/
def gatherRead (env : HashMap String DenseTensor) (coord : HashMap UID Int) (pad : Float)
    (nm : String) (es : List IdxExpr) (cast : Float → Float := fun v => v) : Except EvalError Float :=
  match env[nm]? with
  | none => .error (.unknownTensor .gather nm)
  | some t =>
      let srcZ : List Int := es.map (evalIdx coord)
      -- bounds check against t.shape; out-of-range ⇒ pad (never cast)
      if (srcZ.zip t.shape).any (fun (z, d) => z < 0 || z ≥ (d : Int)) then
        .ok pad
      else
        .ok (cast (t.get! (srcZ.map Int.toNat)))

/-- Apply a unary transcendental function to a gathered value. `log`/`sqrt`/`recip` fail loud on
    a domain violation (consistent with this evaluator's fail-loud conventions elsewhere —
    unsized axes, unknown tensors, causality violations); `exp`/`sin`/`cos` are total, no domain
    check needed. `recip` (the friendly `/` operator's desugared form) fails on exactly zero
    rather than propagating `inf`. `ctx` is the deterministic tensor/coordinate the failing value
    was gathered from — carried on `EvalError.unaryDomain` for future/typed inspection, but NOT
    part of the initial rendered message (see `Error.lean`'s `EvalContext` doc). -/
def applyUnaryFn (ctx : EvalContext) : UnaryOp → Float → Except EvalError Float
  | op, v => (op.applyChecked v).mapError (fun dop => .unaryDomain dop v ctx)


/-- Gather one factor's value at a coordinate, from the input tensors, for a statement whose
    semiring has additive identity `zero` (0_K) and multiplicative identity `one` (1_K).
    `.read nm es`: map each `eᵢ` to its source coord via `evalIdx`; out-of-range (any coord < 0
    or ≥ dim) pads with `zero` (0_K of the statement's sort: real 0.0, bool 0.0, max-plus -inf,
    min-plus +inf). `.iverson b`: `one` if the predicate holds else `zero`. `.unaryFn op nm es`:
    reads like `.read nm es` BUT an out-of-range read pads with the real 0.0 (the primitive takes
    real input, so `f(0.0)` is what an out-of-range read contributes), then applies `op` to the
    resulting value; the result is taken as-is.

    `castOf nm` is the statement's SOURCE READ CAST (S3b design §3): applied to the value of a BARE
    in-bounds read of `nm` (the bool -> tropical cast: a Boolean source read by a tropical statement
    is `0_K`/`1_K` of that statement, not the raw 0/1). It is NOT applied to the out-of-range pad
    (already `zero`) nor under a `.unaryFn` (the primitive takes real input). -/
def gatherCast (zero one : Float) (castOf : String → Float → Float)
    (env : HashMap String DenseTensor) (coord : HashMap UID Int) :
    Factor → Except EvalError Float
  | .iverson b => .ok (if evalBool coord b then one else zero)
  | .read nm es => gatherRead env coord zero nm es (castOf nm)
  | .unaryFn op nm es =>
      let ctx : EvalContext := { tensor := nm, coord := es.map (evalIdx coord) }
      (gatherRead env coord 0.0 nm es).bind (applyUnaryFn ctx op)

/-- `gatherCast` with no source cast: the real and Boolean statements' gather. -/
def gather (zero one : Float) (env : HashMap String DenseTensor) (coord : HashMap UID Int) :
    Factor → Except EvalError Float :=
  gatherCast zero one (fun _ v => v) env coord

end LeanNCD.Eval

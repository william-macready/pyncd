import Std.Data.HashMap

/-!
# Wave C plan-layer static vocabulary (C1)

`ScalarDType`/`TensorSignature`/`InputSignature` are plan compilation's *specialization input* —
concrete shape and dtype metadata, no tensor values. See `papers/wave_c_evalplan_proposal.md`
§5.1 and Appendix A.5. This file introduces no error type: C1 has no producer for one (see
`Eval/Plan/Signature.lean`'s module doc for why `InputSignatureError` belongs to C4 instead).
-/

namespace LeanNCD.Eval.Plan
open Std

/-- Closed concrete-storage dtype vocabulary. Only `f64` is admitted by Wave C; `f32`/`bool` are
    reserved tags for later plan capabilities with no producer or consumer yet. -/
inductive ScalarDType
  | f64 | f32 | bool
  deriving DecidableEq, BEq, Repr

/-- A concrete tensor shape and scalar dtype, without element values. `shape` is `Array Nat`
    (not `List Nat`, unlike `DenseTensor.shape`) — this is Plan-layer semantic IR, which uses
    `Array` throughout (it will sit inside `RawEvalPlan.tensorSigs : Array TensorSignature` in a
    later slice); the shape-inference core this feeds still speaks `List Nat` internally, and the
    boundary conversion happens once, in `Signature.lean`. -/
structure TensorSignature where
  shape : Array Nat
  dtype : ScalarDType
  deriving DecidableEq, BEq, Repr

/-- Source-name-keyed specialization input: maps required external tensor names to their concrete
    signatures. Named because it is consumed at the source-facing boundary; the checked semantic
    plan (a later slice) is positional and does not retain these names. -/
structure InputSignature where
  tensors : HashMap String TensorSignature

end LeanNCD.Eval.Plan

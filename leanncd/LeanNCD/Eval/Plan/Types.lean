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

/-- Index into a plan's `tensorSigs` table and the worker's parallel tensor store. -/
abbrev TensorSlot := Nat

/-- Cross-backend numeric convention. Wave C has exactly one: ordered sum-product over binary64,
    with source-declared fold order preserved (proposal §8.4). -/
inductive NumericMode
  | reference64SumProduct
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Out-of-range read policy. Wave C has exactly one. -/
inductive OutOfBoundsPolicy
  | zeroPad
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A scalar literal in dtype-preserving canonical form. `f64` stores `Float.toBits`, never a
    `Float`: `Float.toBits 0.0 ≠ Float.toBits (-0.0)` whereas `(0.0 : Float) == (-0.0 : Float)`
    is `true`, so bits distinguish signed zero and preserve NaN payloads. Verified by `#eval`.

    As with `ScalarDType`, only `.f64` is admitted by Wave C: `admittedAlgebra` (`Check.lean`) is
    the sole `ContractionAlgebra` `checkAssign` accepts (its `algebraNotAdmitted` guard forces
    `a.algebra == admittedAlgebra` exactly), and both of its constants (`factorId`, `reduceId`) are
    `.f64 _`. `.f32`/`.bool` are reserved tags — like `ScalarDType.f32`/`.bool` — with no producer
    or consumer yet; neither can ever appear inside a checked plan's `ContractionAlgebra`. -/
inductive ScalarConst
  | f64  (bits : UInt64)
  | f32  (bits : UInt32)
  | bool (value : Bool)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Closed binary scalar operations. Exactly the ones Wave C's checker and worker implement —
    `min`/`max`/`logicalAnd`/`logicalOr` are absent by design, not oversight: max/min aggregation
    and predicate outputs are rejected at the source boundary (proposal §3.2), so nothing could
    construct them and no worker implements their semantics. Adding a constructor here is itself
    a semantic-version change (§9.2). -/
inductive ScalarBinOp
  | add | mul
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The operation and identity used within a factor product and across reductions/terms.
    `reduceOp`/`reduceId` intentionally serve BOTH the reduction over a term's contracted
    coordinates and the fold combining completed terms — mirroring the reference evaluator's
    `Combine.combine`/`unit0`, so the format cannot silently permit different operations at the
    two layers (proposal §8.1). -/
structure ContractionAlgebra where
  factorOp : ScalarBinOp
  factorId : ScalarConst
  reduceOp : ScalarBinOp
  reduceId : ScalarConst
  deriving DecidableEq, BEq, Repr, Inhabited

end LeanNCD.Eval.Plan

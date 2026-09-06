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

/-- Closed concrete-storage dtype vocabulary. `f64` and `bool` are admitted by the checked plan
    layer — `bool` as a *semantic algebra/signature tag over the same Float-backed storage*, not a
    native carrier (`admittedAlgebraBool`, `Check.lean`). `f32` remains a reserved tag with no
    producer or consumer. -/
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

/-- Out-of-range read policy. Wave C has exactly one. -/
inductive OutOfBoundsPolicy
  | zeroPad
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A scalar literal in dtype-preserving canonical form. `f64` stores `Float.toBits`, never a
    `Float`: `Float.toBits 0.0 ≠ Float.toBits (-0.0)` whereas `(0.0 : Float) == (-0.0 : Float)`
    is `true`, so bits distinguish signed zero and preserve NaN payloads. Verified by `#eval`.

    As with `ScalarDType`, `.f64` and `.bool` are admitted: `checkAssign`'s `algebraNotAdmitted`
    guard forces `a.algebra ∈ admittedAlgebrasFor destDtype` (`Check.lean`) — a real destination
    selects the real sum-product plus the two tropical semirings `AggOp.max`/`.min` select, all of
    whose constants (`factorId`, `reduceId`) are `.f64 _`, and a predicate destination selects
    `admittedAlgebraBool`, whose constants are `.bool true`/`.bool false` (decoded to `1.0`/`0.0` by
    `Dense.constFloat`). `.f32` remains a reserved tag — like `ScalarDType.f32` — with no producer or
    consumer; it can never appear inside a checked plan's `ContractionAlgebra`. -/
inductive ScalarConst
  | f64  (bits : UInt64)
  | f32  (bits : UInt32)
  | bool (value : Bool)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Closed binary scalar operations. `min`/`max` back the tropical-semiring reductions that
    `AggOp.max`/`.min` select (`admittedAlgebraMax`/`admittedAlgebraMin` in `Check.lean`) AND the
    Boolean conjunction/disjunction a predicate destination compiles to (`admittedAlgebraBool`);
    `add`/`mul` back Wave C's real sum-product. `logicalAnd`/`logicalOr` remain absent by design —
    Boolean semantics is exactly Float `min`/`max` over `1.0`/`0.0`, per the reference `Combine.bool`,
    so a dedicated pair of constructors would duplicate an existing semantics rather than add one.
    Adding a constructor here is itself a semantic-version change (§9.2): `min`/`max` were added by
    the max/min-aggregation thread. -/
inductive ScalarBinOp
  | add | mul | min | max
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

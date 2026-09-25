import LeanNCD.Eval.Tensor
import LeanNCD.Eval.Error
import LeanNCD.Eval.Gather
import LeanNCD.Eval.Slots
namespace LeanNCD.Eval
open Std

/-- One carrier's scalar runtime for the nonlinearity formulas: every scalar operation and
    constant the eight functions of this module use, and nothing else. Private data passed to a
    formula, not a typeclass (the same shape as `Plan/Dense.lean`'s `ScalarKernelOps`): each formula
    below is written ONCE over this record and instantiated for exactly two carriers, binary64
    (`floatNonlinOps`) and native binary32 (`float32NonlinOps`). -/
private structure NonlinScalarOps (α : Type) where
  zero : α
  one : α
  half : α
  three : α
  geluScale : α
  geluCubic : α
  leakSlope : α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  neg : α → α
  max : α → α → α
  le : α → α → Bool
  beq : α → α → Bool
  exp : α → α
  tanh : α → α
  sqrt : α → α
  pow : α → α → α

/-- Binary64: every constant is the literal the pre-F32-B `Float` formulas spelled, so the Float
    instantiation is that behavior verbatim (the `3` is the `OfNat Float 3` that `x^3` elaborated
    to). -/
private def floatNonlinOps : NonlinScalarOps Float :=
  { zero := 0.0, one := 1.0, half := 0.5, three := 3
  , geluScale := 0.7978845608028654, geluCubic := 0.044715, leakSlope := 0.01
  , add := fun a b => a + b, sub := fun a b => a - b, mul := fun a b => a * b
  , div := fun a b => a / b, neg := fun a => -a, max := fun a b => max a b
  , le := fun a b => decide (a ≤ b), beq := fun a b => a == b
  , exp := Float.exp, tanh := Float.tanh, sqrt := Float.sqrt, pow := fun a b => a ^ b }

/-- Binary32: every constant is an exact bit pattern, and every operation is a native `Float32`
    primitive (`expf`/`tanhf`/`sqrtf`/`powf` for the four transcendentals). Nothing here widens to
    `Float` and narrows back: that would compute a different function (`papers/f32b_evalplan.md` §2.6). -/
private def float32NonlinOps : NonlinScalarOps Float32 :=
  { zero := Float32.ofBits 0x00000000, one := Float32.ofBits 0x3f800000
  , half := Float32.ofBits 0x3f000000, three := Float32.ofBits 0x40400000
  , geluScale := Float32.ofBits 0x3f4c422a, geluCubic := Float32.ofBits 0x3d372713
  , leakSlope := Float32.ofBits 0x3c23d70a
  , add := fun a b => a + b, sub := fun a b => a - b, mul := fun a b => a * b
  , div := fun a b => a / b, neg := fun a => -a, max := fun a b => max a b
  , le := fun a b => decide (a ≤ b), beq := fun a b => a == b
  , exp := Float32.exp, tanh := Float32.tanh, sqrt := Float32.sqrt, pow := Float32.pow }

section
variable {α : Type}

/-- The five pointwise formulas, each written ONCE over the carrier record. The operation tree and
    association of each arm are exactly the pre-F32-B `Float` bodies of `reluT`/`sigmoidT`/`tanhT`/
    `geluT`/`leakyReluT`. `relu` is `max 0 x`, and Lean's `maxOfLe` returns `x` exactly when
    `0 ≤ x`, so `relu(-0) = -0` and `relu(NaN) = +0` in both carriers. -/
private def pointwiseWith (o : NonlinScalarOps α) : PointwiseFn → α → α
  | .relu      => fun x => o.max o.zero x
  | .sigmoid   => fun x => o.div o.one (o.add o.one (o.exp (o.neg x)))
  | .tanh      => fun x => o.tanh x
  | .gelu      => fun x => o.mul (o.mul o.half x) (o.add o.one (o.tanh (o.mul o.geluScale
                    (o.add x (o.mul o.geluCubic (o.pow x o.three))))))
  | .leakyrelu => fun x => if o.le o.zero x then x else o.mul o.leakSlope x

/-- softmax over one row of `(value, masked?)` entries. Masked entries are excluded (treated as
    -∞ ⇒ exp 0), and — critically — excluded from the row MAXIMUM too; `y = exp(x - rowMax) /
    Σ exp(x - rowMax)` over unmasked entries, the sum folded left to right. An all-masked row
    normalizes to zeros (never a uniform row). -/
private def softmaxRowWith (o : NonlinScalarOps α) (entries : List (α × Bool)) : List α :=
  let unmasked := entries.filterMap (fun (x, m) => if m then none else some x)
  let m := match unmasked with
    | []      => o.zero
    | x :: xs => xs.foldl (fun a b => o.max a b) x
  let es := entries.map (fun (x, masked) => if masked then o.zero else o.exp (o.sub x m))
  let s := es.foldl o.add o.zero
  (entries.zip es).map (fun ((_, masked), e) =>
    if masked || o.beq s o.zero then o.zero else o.div e s)

/-- normalize over one row: `y = x / Σ x` over unmasked entries, the sum folded left to right; a
    zero-sum row normalizes to zeros. -/
private def normalizeRowWith (o : NonlinScalarOps α) (entries : List (α × Bool)) : List α :=
  let s := entries.foldl (fun a (x, masked) => if masked then a else o.add a x) o.zero
  entries.map (fun (x, masked) => if masked || o.beq s o.zero then o.zero else o.div x s)

/-- L2-normalize over one row: `y = x / √(Σ x²)` over unmasked entries. An all-zero row
    (‖x‖₂ = 0) normalizes to zero, matching `normalizeRowWith`'s convention (not a domain error —
    see SC8's precedent for softmax). -/
private def l2normalizeRowWith (o : NonlinScalarOps α) (entries : List (α × Bool)) : List α :=
  let s := o.sqrt (entries.foldl
    (fun a (x, masked) => if masked then a else o.add a (o.mul x x)) o.zero)
  entries.map (fun (x, masked) => if masked || o.beq s o.zero then o.zero else o.div x s)

/-- The row formula an `AxiswiseFn` denotes, over the carrier record. -/
private def axiswiseRowWith (o : NonlinScalarOps α) : AxiswiseFn → List (α × Bool) → List α
  | .softmax     => softmaxRowWith o
  | .normalize   => normalizeRowWith o
  | .l2normalize => l2normalizeRowWith o

end

/-- relu: elementwise max(0, x). -/
def reluT (t : DenseTensor) : DenseTensor :=
  ⟨t.shape, t.data.map (pointwiseWith floatNonlinOps .relu)⟩

/-- sigmoid: elementwise 1/(1+e^-x). -/
def sigmoidT (t : DenseTensor) : DenseTensor :=
  ⟨t.shape, t.data.map (pointwiseWith floatNonlinOps .sigmoid)⟩

/-- tanh: elementwise hyperbolic tangent. -/
def tanhT (t : DenseTensor) : DenseTensor :=
  ⟨t.shape, t.data.map (pointwiseWith floatNonlinOps .tanh)⟩

/-- gelu (tanh approximation): `0.5·x·(1 + tanh(√(2/π)·(x + 0.044715·x³)))`. The exact
    erf-based form isn't available (no `Float.erf` in this toolchain); this is the standard
    approximation used by BERT/GPT-2-style implementations. -/
def geluT (t : DenseTensor) : DenseTensor :=
  ⟨t.shape, t.data.map (pointwiseWith floatNonlinOps .gelu)⟩

/-- leaky relu: elementwise `x` if `x ≥ 0` else `0.01·x` (fixed negative slope). -/
def leakyReluT (t : DenseTensor) : DenseTensor :=
  ⟨t.shape, t.data.map (pointwiseWith floatNonlinOps .leakyrelu)⟩

/-- Build the `coord : HashMap UID Int` for a full multi-index `c`, pairing each axis position's
    UID with its coordinate value (so `evalBool` can see the coordinate for masking). -/
private def coordMap (axisUids : List UID) (c : List Nat) : HashMap UID Int :=
  (axisUids.zip c).foldl (fun m (u, v) => m.insert u (v : Int)) ({} : HashMap UID Int)

/-- Group the tensor's coordinates into "rows" along `axisPos`: each row is the list of full
    coordinates that agree on all axes except `axisPos` (varying that axis 0..dim-1). Returns a
    list of rows, each a list of `(coord, flatIdx)`. -/
private def rowsAlong (axisPos : Nat) (shape : List Nat) : List (List (List Nat × Nat)) :=
  let coords := DenseTensor.allCoords shape
  -- row key = coord with position `axisPos` removed.
  let keyed := coords.map (fun c => (c.eraseIdx axisPos, c, DenseTensor.flatIdx shape c))
  -- group by key, preserving first-seen order of keys.
  let keys := (keyed.map (·.1)).foldl
    (fun acc k => if acc.contains k then acc else acc ++ [k]) []
  keys.map (fun k =>
    (keyed.filter (fun e => e.1 == k)).map (fun e => (e.2.1, e.2.2)))

/-- Apply a per-row normalization `f` (given the list of (value, masked?) entries it returns the
    list of output values, in the same order) along `axisPos`, with an `included?` predicate over the
    FULL coordinate. `included? c = true` keeps entry `c`; `false` masks it. This is the single row
    engine every nonlinearity backend and both carriers share: the SOURCE wrapper
    (`AxiswiseFn.apply`) builds `included?` from a source `BoolExpr` + axis UIDs; the CHECKED
    adapter (`Plan/Nonlin.lean`'s `runDenseAxiswise`) builds it from a UID-free `PosBoolExpr`. The
    carrier record `o` supplies only the unreachable `getD` default (its own zero). -/
private def perRowCoreWith {α : Type} (o : NonlinScalarOps α) (axisPos : Nat)
    (included? : List Nat → Bool) (f : List (α × Bool) → List α) (t : DenseTensorOf α) :
    DenseTensorOf α :=
  let rows := rowsAlong axisPos t.shape
  rows.foldl (fun acc row =>
    let entries : List (α × Bool) := row.map (fun (c, fi) =>
      let x := acc.data.getD fi o.zero
      (x, ! included? c))
    let ys := f entries
    -- write outputs back at each flatIdx.
    ((row.zip ys).foldl (fun (cur : DenseTensorOf α) ((_, fi), y) =>
      ⟨cur.shape, cur.data.set! fi y⟩) acc))
    t

/-- softmax along `axisPos`, with an `included?` coordinate predicate. For each row: masked entries
    (`included? c = false`) are excluded (treated as -∞ ⇒ exp 0), and — critically — excluded from
    the row MAXIMUM too; `y = exp(x - rowMax) / Σ exp(x - rowMax)` over unmasked entries. An
    all-masked row normalizes to zeros (never a uniform row). -/
def softmaxT (axisPos : Nat) (included? : List Nat → Bool)
    (t : DenseTensor) : DenseTensor :=
  perRowCoreWith floatNonlinOps axisPos included? (softmaxRowWith floatNonlinOps) t

/-- normalize along `axisPos` (+ `included?`): y = x / Σ x over unmasked entries in the row. -/
def normalizeT (axisPos : Nat) (included? : List Nat → Bool)
    (t : DenseTensor) : DenseTensor :=
  perRowCoreWith floatNonlinOps axisPos included? (normalizeRowWith floatNonlinOps) t

/-- L2-normalize along `axisPos` (+ `included?`): y = x / ‖x‖₂ = x / √(Σ x²) over unmasked
    entries in the row. An all-zero row (‖x‖₂ = 0) normalizes to zero, matching `normalizeT`'s
    convention (not a domain error — see SC8's precedent for softmax). -/
def l2normalizeT (axisPos : Nat) (included? : List Nat → Bool)
    (t : DenseTensor) : DenseTensor :=
  perRowCoreWith floatNonlinOps axisPos included? (l2normalizeRowWith floatNonlinOps) t

/-- The elementwise tensor map a `PointwiseFn` denotes — owned by the enum, so a new pointwise
    function has exactly one place to be interpreted (and no axis/mask to forget): one
    `pointwiseWith` arm, shared with the binary32 sibling `PointwiseFn.apply32`. -/
def _root_.LeanNCD.PointwiseFn.apply (pf : PointwiseFn) (t : DenseTensor) : DenseTensor :=
  ⟨t.shape, t.data.map (pointwiseWith floatNonlinOps pf)⟩

/-- The native binary32 elementwise map a `PointwiseFn` denotes: the same `pointwiseWith` formula
    as `PointwiseFn.apply`, instantiated with `Float32` primitives and exact binary32 constants. -/
def _root_.LeanNCD.PointwiseFn.apply32 (pf : PointwiseFn) (t : DenseTensor32) : DenseTensor32 :=
  ⟨t.shape, t.data.map (pointwiseWith float32NonlinOps pf)⟩

/-- The axiswise reduction a `AxiswiseFn` denotes, dispatched over its ONE `included?`-parametric
    softmax/normalize/L2 implementation. Both the source `AxiswiseFn.apply` and the checked
    `runDenseAxiswise` funnel through here, so there is exactly one implementation of each function
    regardless of which backend supplies the inclusion predicate — and the binary32 sibling
    `AxiswiseFn.applyCore32` shares the same row formulas and row engine. -/
def _root_.LeanNCD.AxiswiseFn.applyCore (fn : AxiswiseFn) (axisPos : Nat)
    (included? : List Nat → Bool) (t : DenseTensor) : DenseTensor :=
  perRowCoreWith floatNonlinOps axisPos included? (axiswiseRowWith floatNonlinOps fn) t

/-- The native binary32 axiswise entry: the same row engine, row formulas, and `included?`
    contract as `AxiswiseFn.applyCore`, instantiated with `Float32` primitives. There is
    deliberately no `AxiswiseFn.apply32` source-mask wrapper: the legacy evaluator never executes
    binary32. -/
def _root_.LeanNCD.AxiswiseFn.applyCore32 (fn : AxiswiseFn) (axisPos : Nat)
    (included? : List Nat → Bool) (t : DenseTensor32) : DenseTensor32 :=
  perRowCoreWith float32NonlinOps axisPos included? (axiswiseRowWith float32NonlinOps fn) t

/-- The SOURCE axiswise wrapper: build the full-coordinate `included?` predicate from a source
    `BoolExpr` mask (`evalBool` over the `axisUids → Int` coordinate map) and hand it to `applyCore`.
    A `none` mask includes every coordinate, so an unmasked reduction is byte-for-byte the pre-mask
    behavior. Owned by the enum, symmetric with `PointwiseFn.apply`. -/
def _root_.LeanNCD.AxiswiseFn.apply (fn : AxiswiseFn) (axisPos : Nat) (axisUids : List UID)
    (mask? : Option BoolExpr) (t : DenseTensor) : DenseTensor :=
  fn.applyCore axisPos (fun c => match mask? with
    | none => true
    | some b => evalBool (coordMap axisUids c) b) t

/-- A nonlinearity together with everything statically resolved against one statement's own
    output slots: which axis position (if any) is the marked reduction axis, checked exactly
    once. Both `evalPlain` and `evalStmtSliceSeeded` consume this instead of each independently
    searching `slots` for a `·`-marked axis. -/
inductive ResolvedNonlin
  | identity
  | pointwise : PointwiseFn → ResolvedNonlin
  | axiswise  : AxiswiseFn → Option BoolExpr → Nat → ResolvedNonlin

/-- Resolve a statement's `Nonlin` against its own output slots. `identity`/`pointwise` need no
    axis and always succeed. `axiswise` needs exactly one `·`-marked output slot among
    `axisUids`; its position there is computed once here rather than at every evaluation call. -/
def resolveNonlin (nl : Nonlin) (slots : List LHSSlot) (axisUids : List UID) :
    Except EvalError ResolvedNonlin :=
  match nl with
  | .identity      => pure .identity
  | .pointwise pf  => pure (.pointwise pf)
  | .axiswise fn m => match normAxisUidOf slots with
      | some nu => match axisUids.findIdx? (· == nu) with
          | some p => pure (.axiswise fn m p)
          | none   => throw (.invalidNormAxis .notAmongOutputAxes)
      | none    => throw (.invalidNormAxis .notMarked)

/-- Dispatch: apply a resolved Nonlin. `axisUids` is only consumed by `AxiswiseFn.apply` to build
    the `included?` coordinate map from the source mask; `softmaxT`/`normalizeT`/`l2normalizeT`
    themselves take that `included?` predicate directly. The axis *position* itself already lives
    in `rn` for the `.axiswise` case, resolved once by `resolveNonlin` rather than re-derived
    here. -/
def applyNonlin (rn : ResolvedNonlin) (axisUids : List UID) (t : DenseTensor) : DenseTensor :=
  match rn with
  | .identity        => t
  | .pointwise pf    => pf.apply t
  | .axiswise fn m p => fn.apply p axisUids m t

end LeanNCD.Eval

import LeanNCD.Eval.Tensor
import LeanNCD.Eval.Error
import LeanNCD.Eval.Gather
import LeanNCD.Eval.Slots
namespace LeanNCD.Eval
open Std

/-- relu: elementwise max(0, x). -/
def reluT (t : DenseTensor) : DenseTensor := ⟨t.shape, t.data.map (fun x => max 0.0 x)⟩

/-- sigmoid: elementwise 1/(1+e^-x). -/
def sigmoidT (t : DenseTensor) : DenseTensor :=
  ⟨t.shape, t.data.map (fun x => 1.0 / (1.0 + Float.exp (-x)))⟩

/-- tanh: elementwise hyperbolic tangent. -/
def tanhT (t : DenseTensor) : DenseTensor := ⟨t.shape, t.data.map Float.tanh⟩

/-- gelu (tanh approximation): `0.5·x·(1 + tanh(√(2/π)·(x + 0.044715·x³)))`. The exact
    erf-based form isn't available (no `Float.erf` in this toolchain); this is the standard
    approximation used by BERT/GPT-2-style implementations. -/
def geluT (t : DenseTensor) : DenseTensor :=
  ⟨t.shape, t.data.map (fun x =>
    0.5 * x * (1.0 + Float.tanh (0.7978845608028654 * (x + 0.044715 * x^3))))⟩

/-- leaky relu: elementwise `x` if `x ≥ 0` else `0.01·x` (fixed negative slope). -/
def leakyReluT (t : DenseTensor) : DenseTensor :=
  ⟨t.shape, t.data.map (fun x => if x ≥ 0.0 then x else 0.01 * x)⟩

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
    list of output values, in the same order) along `axisPos`. `included` sees each entry's full
    tensor coordinate. -/
private def perRowIncluded (axisPos : Nat) (included : List Nat → Bool)
    (f : List (Float × Bool) → List Float) (t : DenseTensor) : DenseTensor :=
  let rows := rowsAlong axisPos t.shape
  rows.foldl (fun acc row =>
    let entries : List (Float × Bool) := row.map (fun (c, fi) =>
      let x := acc.data.getD fi 0.0
      let masked := !included c
      (x, masked))
    let ys := f entries
    -- write outputs back at each flatIdx.
    ((row.zip ys).foldl (fun (cur : DenseTensor) ((_, fi), y) => ⟨cur.shape, cur.data.set! fi y⟩) acc))
    t

/-- The single callback-based implementation of axiswise nonlinear math. The callback returns
    whether an entry is included and receives that entry's full tensor coordinate. -/
def _root_.LeanNCD.AxiswiseFn.applyIncluded (fn : AxiswiseFn) (axisPos : Nat)
    (included : List Nat → Bool) (t : DenseTensor) : DenseTensor :=
  match fn with
  | .softmax =>
      perRowIncluded axisPos included (fun entries =>
        let unmasked := entries.filterMap (fun (x, m) => if m then none else some x)
        let m := match unmasked with
          | []      => 0.0
          | x :: xs => xs.foldl (fun a b => max a b) x
        let es := entries.map (fun (x, masked) => if masked then 0.0 else Float.exp (x - m))
        let s := es.foldl (· + ·) 0.0
        (entries.zip es).map (fun ((_, masked), e) =>
          if masked || s == 0.0 then 0.0 else e / s)) t
  | .normalize =>
      perRowIncluded axisPos included (fun entries =>
        let s := entries.foldl (fun a (x, masked) => if masked then a else a + x) 0.0
        entries.map (fun (x, masked) =>
          if masked || s == 0.0 then 0.0 else x / s)) t
  | .l2normalize =>
      perRowIncluded axisPos included (fun entries =>
        let s := Float.sqrt
          (entries.foldl (fun a (x, masked) => if masked then a else a + x*x) 0.0)
        entries.map (fun (x, masked) =>
          if masked || s == 0.0 then 0.0 else x / s)) t

private def sourceIncluded (axisUids : List UID) (mask? : Option BoolExpr) (c : List Nat) : Bool :=
  match mask? with
  | none => true
  | some b => evalBool (coordMap axisUids c) b

/-- softmax along `axisPos`, with an optional mask. For each row: masked entries are excluded
    (treated as -∞ ⇒ exp 0); `y = exp(x - rowMax) / Σ exp(x - rowMax)` over unmasked entries.
    The `mask?`/`axisUids` let `evalBool` see the coordinate (axis-UID → Int) for masking. -/
def softmaxT (axisPos : Nat) (axisUids : List UID) (mask? : Option BoolExpr)
    (t : DenseTensor) : DenseTensor :=
  AxiswiseFn.softmax.applyIncluded axisPos (sourceIncluded axisUids mask?) t

/-- normalize along `axisPos` (+ optional mask): y = x / Σ x over unmasked entries in the row. -/
def normalizeT (axisPos : Nat) (axisUids : List UID) (mask? : Option BoolExpr)
    (t : DenseTensor) : DenseTensor :=
  AxiswiseFn.normalize.applyIncluded axisPos (sourceIncluded axisUids mask?) t

/-- L2-normalize along `axisPos` (+ optional mask): y = x / ‖x‖₂ = x / √(Σ x²) over unmasked
    entries in the row. An all-zero row (‖x‖₂ = 0) normalizes to zero, matching `normalizeT`'s
    convention (not a domain error — see SC8's precedent for softmax). -/
def l2normalizeT (axisPos : Nat) (axisUids : List UID) (mask? : Option BoolExpr)
    (t : DenseTensor) : DenseTensor :=
  AxiswiseFn.l2normalize.applyIncluded axisPos (sourceIncluded axisUids mask?) t

/-- The elementwise tensor map a `PointwiseFn` denotes — owned by the enum, so a new pointwise
    function has exactly one place to be interpreted (and no axis/mask to forget). -/
def _root_.LeanNCD.PointwiseFn.apply : PointwiseFn → DenseTensor → DenseTensor
  | .relu => reluT | .sigmoid => sigmoidT | .tanh => tanhT | .gelu => geluT
  | .leakyrelu => leakyReluT

/-- The axiswise reduction a `AxiswiseFn` denotes — owned by the enum, symmetric with
    `PointwiseFn.apply` above. -/
def _root_.LeanNCD.AxiswiseFn.apply (fn : AxiswiseFn) (axisPos : Nat) (axisUids : List UID)
    (mask? : Option BoolExpr) (t : DenseTensor) : DenseTensor :=
  match fn with
  | .softmax     => softmaxT axisPos axisUids mask? t
  | .normalize   => normalizeT axisPos axisUids mask? t
  | .l2normalize => l2normalizeT axisPos axisUids mask? t

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

/-- Dispatch: apply a resolved Nonlin. `axisUids` is still needed by `softmaxT`/`normalizeT`/
    `l2normalizeT` for their coordinate/mask math; the axis *position* itself already lives in
    `rn` for the `.axiswise` case, resolved once by `resolveNonlin` rather than re-derived here. -/
def applyNonlin (rn : ResolvedNonlin) (axisUids : List UID) (t : DenseTensor) : DenseTensor :=
  match rn with
  | .identity        => t
  | .pointwise pf    => pf.apply t
  | .axiswise fn m p => fn.apply p axisUids m t

end LeanNCD.Eval

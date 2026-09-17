namespace LeanNCD.Eval

-- Deliberately does NOT import `Error.lean`: `DenseTensorOf` is pure runtime data (shape + a flat
-- carrier buffer), independent of how any worker that reads/writes it reports failure. Before 4h
-- this file also defined `abbrev EvalError := String`, which made every Eval/ module depend on
-- `Tensor.lean` just to name its own error type — that's gone now, and each worker instead
-- imports `LeanNCD.Eval.Error` explicitly for `EvalError`.

/-- A dense row-major tensor over one scalar carrier `α`. Invariant:
    `data.size = (shape.foldl (·*·) 1)`.

    Only the carrier SHELL is generic (f32 slice, Task 3): the shape/storage pair is the one piece
    of this layer that genuinely has nothing carrier-specific in it, so parameterizing it is what
    lets a binary32 worker reuse the row-major coordinate and affine primitives verbatim instead of
    copying them. Everything with real arithmetic in it — the helpers below, the folds, the constant
    decoders — stays carrier-specific by design (see `Eval/Plan/Dense.lean`'s `ScalarKernelOps`). -/
structure DenseTensorOf (α : Type) where
  shape : List Nat
  data  : Array α
  deriving Repr, Inhabited

/-- The binary64 carrier: the original `DenseTensor`, unchanged in meaning and in field names. -/
abbrev DenseTensor := DenseTensorOf Float

/-- The binary32 carrier. A native `Array Float32` buffer — NOT `Array Float` relabelled — so the
    binary32 worker (`Eval/Plan/Dense32.lean`, `runDenseAssignAt32`) rounds at every primitive
    operation rather than once at the end. -/
abbrev DenseTensor32 := DenseTensorOf Float32

/-! ### `DenseTensor`'s old generated names

Changing a structure into an alias does NOT synthesize the alias's old `mk`/field projections, and
a bare `abbrev` of a generic projection is not usable through legacy field notation (verified by a
compiled Lean 4.30 probe while this slice was being planned). So all three are preserved explicitly:
`mk` as an abbreviation, and the two projections as definitions whose `self` parameter is typed with
the legacy alias. Every pre-existing direct user — `KernelDenseTest`, `GraphDenseTest`,
`NonlinDenseTest`, `Portfolio.ScatterNonlinRejectTest` — therefore compiles unmigrated, which is
what `Eval.TensorTest`'s fixture 15 pins. -/

/-- Compatibility: the binary64 carrier's old generated constructor. -/
abbrev DenseTensor.mk (shape : List Nat) (data : Array Float) : DenseTensor :=
  DenseTensorOf.mk shape data

/-- Compatibility: the binary64 carrier's old generated `shape` projection. -/
def DenseTensor.shape (self : DenseTensor) : List Nat := DenseTensorOf.shape self

/-- Compatibility: the binary64 carrier's old generated `data` projection. -/
def DenseTensor.data (self : DenseTensor) : Array Float := DenseTensorOf.data self

namespace DenseTensor

/-- number of elements of a shape. -/
def sizeOf (shape : List Nat) : Nat := shape.foldl (· * ·) 1

/-- all-zeros tensor of a shape. -/
def zeros (shape : List Nat) : DenseTensor := ⟨shape, Array.replicate (sizeOf shape) 0.0⟩

/-- row-major strides: strides[k] = product of dims AFTER position k.
    e.g. shape [2,3,4] ⇒ [12,4,1]. -/
def strides (shape : List Nat) : List Nat :=
  (shape.foldr (fun d (acc : Nat × List Nat) => (acc.1 * d, acc.1 :: acc.2)) (1, [])).2

/-- flat index of a multi-index `coord` (must have the same length as `shape`). -/
def flatIdx (shape coord : List Nat) : Nat :=
  ((strides shape).zip coord).foldl (fun a (s, c) => a + s * c) 0

/-- read element at `coord` (out-of-range defaults to `0.0`; `Array.get!` is gone in v4.30). -/
def get! (t : DenseTensor) (coord : List Nat) : Float := t.data.getD (flatIdx t.shape coord) 0.0

/-- write element at `coord`. -/
def set! (t : DenseTensor) (coord : List Nat) (v : Float) : DenseTensor :=
  ⟨t.shape, t.data.set! (flatIdx t.shape coord) v⟩

/-- enumerate every multi-index of a shape, row-major order (reused by ofFn + later tasks). -/
partial def allCoords (shape : List Nat) : List (List Nat) :=
  match shape with
  | []      => [[]]
  | d :: ds =>
      let rest := allCoords ds
      (List.range d).flatMap (fun i => rest.map (fun c => i :: c))

/-- build a tensor from a coordinate → value function (row-major). -/
def ofFn (shape : List Nat) (f : List Nat → Float) : DenseTensor :=
  ⟨shape, ((allCoords shape).map f).toArray⟩

/-- elementwise approximate equality (tolerance) — for tests; Float isn't exactly comparable. -/
def approxEq (a b : DenseTensor) (ε : Float := 1e-6) : Bool :=
  a.shape == b.shape && a.data.size == b.data.size &&
    (a.data.zip b.data).all (fun (x, y) => Float.abs (x - y) < ε)

end DenseTensor
end LeanNCD.Eval

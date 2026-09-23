import LeanNCD.Eval.Tensor
import LeanNCD.Eval.Plan.Check
import LeanNCD.Eval.Plan.Coordinates

/-!
# Wave C Dense interpretation of one checked operation (C2)

The pullback-product-pushforward semantics of proposal §8, over positional `DenseTensor` storage.
Independent of the legacy evaluator by construction — this module imports neither `Gather` nor
`Contract`, builds no `HashMap UID Int`, and knows no source names — so the two implementations can
serve as each other's oracle in C4's differential matrix. Row-major coordinate enumeration, affine
application, flattening, and the per-dimension bounds predicate live in `Coordinates.lean`.
-/

namespace LeanNCD.Eval.Plan
open LeanNCD.Eval

/-! ## The scalar kernel seam (f32 slice, Task 3)

Everything ABOVE the scalar level is carrier-independent integer/Boolean work and is SHARED verbatim
from `Coordinates.lean`: row-major coordinate enumeration (`allCoords`), affine application
(`applyAffine`), flattening (`flatIndex`), the per-dimension bounds predicate (`inBoundsPerDim`), and
the positional predicate evaluator (`evalPosBool`). Everything AT the scalar level is not, and
deliberately so: a binary32 program must round independently at EVERY primitive operation, so its
arithmetic, its constant decoders, and its exact zero/one are native `Float32` — never a binary64
computation with a cast at the end, which gives a different answer (`[16777216, 1, -16777216]` folds
to `+0` natively and to `1` if accumulated in binary64).

`ScalarKernelOps α` is that seam. It is **private data passed to a worker**, not a global typeclass
and not a public interface: every public door in this module takes CHECKED evidence, so no caller can
pair an arbitrary `AssignPlan` with arbitrary scalar operations.

It is also deliberately FALLIBLE rather than total. `binOp` SELECTS an implementation of one
`ScalarBinOp` and may refuse — a total `ScalarBinOp → α → α → α` would force a future complex carrier
to invent `min`/`max` semantics it does not have. `decodeConst` may refuse a constant tagged for the
other real carrier instead of silently converting it. `applyUnary` may refuse inline unary math
outright, which is exactly what the `Float32` instantiation does.
-/

/-- One carrier's scalar runtime: the complete set of scalar-level operations the assignment
    traversal below needs, and nothing else. -/
private structure ScalarKernelOps (α : Type) where
  /-- Decode one checked plan constant (an algebra identity, or a scatter `fill`) into this
      carrier's own exact value. A constant tagged for the OTHER real carrier is refused, never
      converted — that conversion is precisely the silent precision substitution this slice exists
      to prevent. -/
  decodeConst : ScalarConst → Except PositionalInputError α
  /-- This carrier's exact zero: the out-of-bounds zero-pad value, and an Iverson `false`. -/
  zero : α
  /-- This carrier's exact one: an Iverson `true`. -/
  one : α
  /-- This carrier's implementation of one binary operation, or a refusal for one it has no
      semantics for. -/
  binOp : ScalarBinOp → Except PositionalInputError (α → α → α)
  /-- Apply one inline unary read operation to a value gathered from `slot`, or refuse it. -/
  applyUnary : LeanNCD.UnaryOp → α → TensorSlot → Except PositionalInputError α

/-- The BINARY64 scalar runtime: Wave C's original semantics, unchanged, now behind the seam.

    `.bool` is a semantic tag over the same Float storage, so `true`/`false` decode to the reference
    evaluator's Boolean identities `1.0`/`0.0` (`Combine.bool`'s `unit0`/`unit1`) — no separate
    Boolean carrier, no coercion of gathered values.

    The `.f32` arm is the one behavioral change: it was a silent `0.0` catch-all and is now a
    fail-loud `storageKindMismatch`. It stays unreachable through this worker for the reasons it
    always was — `checkAssign` rejects an `f32` destination and every `f32` read (`dtypeAdmitted`),
    and `runDenseAssignAt` below refuses non-`.float64` evidence before a constant is decoded — but
    "unreachable" is now enforced by the decoder itself rather than by silently answering zero.

    Inline unary math delegates to the shared `UnaryOp.applyChecked` (`Eval/Error.lean`), the same
    oracle the reference `applyUnaryFn` wraps, and keeps its `UInt64` `unaryDomain` payload. -/
private def floatOps : ScalarKernelOps Float :=
  { decodeConst := fun c => match c with
      | .f64 bits => .ok (Float.ofBits bits)
      | .bool true => .ok 1.0
      | .bool false => .ok 0.0
      | .f32 _ => .error (.storageKindMismatch .float64 .float32)
  , zero := 0.0
  , one := 1.0
  , binOp := fun op => match op with
      | .add => .ok (fun a b => a + b)
      | .mul => .ok (fun a b => a * b)
      | .min => .ok (fun a b => Min.min a b)
      | .max => .ok (fun a b => Max.max a b)
  , applyUnary := fun op x slot =>
      (op.applyChecked x).mapError (fun dop => .unaryDomain dop (Float.toBits x) slot) }

/-- The BINARY32 scalar runtime: native `Float32` throughout, with every value written as an exact
    bit pattern rather than a decimal literal so the identities are auditable against IEEE-754
    directly (`0x3f800000` is `1`, `0x00000000` is `+0`).

    `.bool` decodes to THIS carrier's exact zero/one, not to a `Float` that is then converted: a
    Boolean destination or source inside a binary32 graph lives in the same `Array Float32` store as
    the graph's real tensors, and Boolean-tagged runtime values keep literal `min`/`max` behavior
    exactly as they do in binary64 (they are not coerced to exact zero/one).

    `applyUnary` refuses UNCONDITIONALLY. Native binary32 `log`/`exp`/`sqrt`/`recip` are slice
    F32-B, and routing an f32 read through the binary64 helper would be false f32. The branch is
    unreachable for any checked evidence this worker can be handed — `checkAssignF32` rejects an
    inline unary read in a binary32 graph (`PlanError.unaryNotAdmittedForDtype`) — so this is a
    fail-loud floor under that checker clause, not a live rejection path. -/
private def float32Ops : ScalarKernelOps Float32 :=
  { decodeConst := fun c => match c with
      | .f32 bits => .ok (Float32.ofBits bits)
      | .bool true => .ok (Float32.ofBits 0x3f800000)
      | .bool false => .ok (Float32.ofBits 0x00000000)
      | .f64 _ => .error (.storageKindMismatch .float32 .float64)
  , zero := Float32.ofBits 0x00000000
  , one := Float32.ofBits 0x3f800000
  , binOp := fun op => match op with
      | .add => .ok (fun a b => a + b)
      | .mul => .ok (fun a b => a * b)
      | .min => .ok (fun a b => Min.min a b)
      | .max => .ok (fun a b => Max.max a b)
  , applyUnary := fun op _ slot => .error (.unaryNotAdmittedForStorage .float32 op slot) }

/-- Gather one factor. Every source dimension is range-tested BEFORE flattening (`inBoundsPerDim`,
    `Coordinates.lean`): testing the flat offset instead can alias distinct invalid coordinates onto
    a valid address (proposal §8.3). A `unary` function is applied to the gathered value AFTER the
    out-of-bounds zero-pad (so an out-of-bounds read contributes `f(0)`, matching the reference
    `gather`), and can fail loud — on a binary64 domain violation (`log`/`sqrt`/`recip`) or, for a
    carrier with no unary implementation at all, on the operation itself.

    The zero-pad is the CARRIER's own exact zero (`ops.zero`), never the algebra's reduction
    identity: a padded read is a FACTOR value flowing through `factorOp`, which is what makes a
    padded `0` beat an all-negative column under a tropical max reduction. -/
private def gatherFactorWith {α : Type} (ops : ScalarKernelOps α) (store : Array (DenseTensorOf α))
    (f : ReadPlan) (iter : List Int) : Except PositionalInputError α :=
  let base : α :=
    match store[f.sourceSlot]? with
    | none => ops.zero
    | some t =>
        let src := applyAffine f.map iter
        let shape := f.sourceShape.toList
        if inBoundsPerDim shape src then (t.data[flatIndex shape (src.map Int.toNat)]?).getD ops.zero
        else ops.zero
  match f.unary with
  | none => .ok base
  | some op => ops.applyUnary op base f.sourceSlot

/-- The ONE left-associated scalar fold behind all three of architecture doc §2.2's fold equations —
    a term's factor product, a term's reduction over its contracted coordinates, and the combination
    of completed terms. The three differ ONLY in which operation/identity pair the checked algebra
    supplies and in which list they consume, so they are three CALL SITES (see `denseValueAtWith`,
    where each is named at its use) rather than three identical functions.

    `op` and `seed` are pre-selected and pre-decoded by the caller, which is why this is total while
    the kernel seam is fallible: selection can fail, application cannot. Left-associated in the given
    order is the whole semantic content — floating-point addition and multiplication are not
    associative, and the fixtures pin the declared order at every one of the three sites. -/
private def foldScalars {α : Type} (op : α → α → α) (seed : α) (xs : List α) : α :=
  xs.foldl op seed

example {α : Type} (op : α → α → α) (seed : α) : foldScalars op seed [] = seed := rfl

example {α : Type} (op : α → α → α) (seed : α) (xs : List α) (x : α) :
    foldScalars op seed (xs ++ [x]) = op (foldScalars op seed xs) x := by
  simp [foldScalars, List.foldl_append]

/-- Validate the positional store against the shapes `checkAssign` already validated. Runtime
    values are a separate trust boundary from plan structure, so this is a value check, not a
    re-validation of the plan.

    Takes a raw `AssignPlan`, matching `validateContext` beside it: both read plan FIELDS only and
    neither consults the checked wrapper, so the `Checked` guarantee belongs at the public API
    boundary, not on a private helper. `runDenseScatter` validates a scatter's compute half — a raw
    `AssignPlan` reached through `CheckedScatterPlan`, which deliberately stores no
    `CheckedAssignPlan` for it — through this same function rather than a second copy. -/
private def validateStore {α : Type} (a : AssignPlan) (store : Array (DenseTensorOf α)) :
    Except PositionalInputError Unit := do
  for t in a.terms do
    for (_, f) in t.readFactorsIndexed do
      match store[f.sourceSlot]? with
      | none => throw (.missingSlot f.sourceSlot store.size)
      | some d =>
          unless d.shape == f.sourceShape.toList do
            throw (.shapeMismatch f.sourceSlot f.sourceShape d.shape)
          unless d.data.size == f.sourceShape.toList.foldl (· * ·) 1 do
            throw (.storageMismatch f.sourceSlot d.shape d.data.size)

/-- Validate a runtime context coordinate against the checked context shape: same rank, and every
    component in range. A separate check from `checkAssign`'s structural work — `ctx` is a runtime
    value supplied per call, not plan data (proposal §7.1). -/
private def validateContext (a : AssignPlan) (ctx : List Int) : Except PositionalInputError Unit :=
  let inRange := (ctx.zip a.contextShape.toList).all (fun (v, d) => 0 ≤ v && v < (d : Int))
  if ctx.length == a.contextShape.size && inRange then pure ()
  else throw (.contextShapeMismatch a.contextShape ctx)

/-- ONE output coordinate's value under a raw `AssignPlan`, at a fixed context coordinate, over ANY
    carrier's scalar runtime. Fold order is source-declared and preserved exactly: factors first,
    then that term's reduction coordinates, then completed terms in term-array order — matching
    architecture doc §2.2's three fold equations one-for-one, each named at its `foldScalars` call
    below. The inner reduction fold and the outer term fold are NOT flattened — `Y[i] := A[i] +
    P[i,j]` must add `A[i]` once, not once per `j` (proposal §8.2). `ctx` is bound at every term's
    `contextPos` positions and held fixed here — it does not get enumerated like
    `outputPos`/`reductionPos` do.

    The four scalar facts the algebra names — both operations and both identities — are selected and
    decoded ONCE, at the top, before any coordinate is enumerated. That is where the kernel seam's
    fallibility is discharged, which is what lets the three folds themselves be total.

    Carrier-generic but NOT public, and no public entry exposes it: every door below takes CHECKED
    evidence, whose recorded storage kind is what selects the ops record. A raw-`AssignPlan`-plus-
    arbitrary-scalar-ops entry would be exactly the unguarded door this slice exists to prevent.

    Takes a raw `AssignPlan` and not a `CheckedAssignPlan` for the reason `validateStore` above does:
    the body reads plan fields only, so the checked wrapper's guarantee lives at the public API
    boundary rather than on this helper, and every caller is already past that boundary.
    `runDenseAssignAt`/`runDenseAssignAt32` enumerate `outputShape` and map this over it (the
    output-driven case); `runDenseScatter` enumerates the same array as its SOURCE domain and places
    each value through a separate map, reaching the compute half through `CheckedScatterPlan`, which
    deliberately stores no `CheckedAssignPlan` for it. Shared rather than duplicated so no two
    workers — and now no two CARRIERS — can drift in fold order, zero-pad behavior, or predicate
    handling. -/
private def denseValueAtWith {α : Type} (ops : ScalarKernelOps α) (a : AssignPlan) (ctx : List Int)
    (store : Array (DenseTensorOf α)) (oc : List Int) : Except PositionalInputError α := do
  let alg := a.algebra
  let factorOp ← ops.binOp alg.factorOp
  let reduceOp ← ops.binOp alg.reduceOp
  let factorId ← ops.decodeConst alg.factorId
  let reduceId ← ops.decodeConst alg.reduceId
  let termAccs ← a.terms.toList.mapM (fun t => do
    let redShape := t.reductionPos.toList.filterMap (fun p => t.iterationShape[p]?)
    let prods ← (allCoords redShape).mapM (fun rc => do
      let iter : Array Int := Id.run do
        let mut iter : Array Int := Array.replicate t.iterationShape.size 0
        for (p, v) in t.contextPos.toList.zip ctx do iter := iter.set! p v
        for (p, v) in t.outputPos.toList.zip oc do iter := iter.set! p v
        for (p, v) in t.reductionPos.toList.zip rc do iter := iter.set! p v
        return iter
      let factorVals ← t.factors.toList.mapM (fun f => match f with
        | .read r => gatherFactorWith ops store r iter.toList
        | .iverson b =>
            (evalPosBool iter.toList b
              |>.mapError (fun e => match e with
                | .affineWidthMismatch exp act => PositionalInputError.predicateWidthMismatch exp act)).map
              (fun v => if v then ops.one else ops.zero))
      -- §2.2 fold 1: this term's FACTORS, left to right in stored order, seeded with `factorId`.
      return foldScalars factorOp factorId factorVals)
    -- §2.2 fold 2: this term's REDUCTION coordinates, left to right in row-major order, seeded with
    -- `reduceId`. Each value is that coordinate's factor product, not a raw factor value.
    return foldScalars reduceOp reduceId prods)
  -- §2.2 fold 3: the completed TERMS, left to right in term-array order. Uses `reduceOp`/`reduceId`
  -- again, not a coincidence: `ContractionAlgebra`'s own doc comment (`Types.lean`) states that term
  -- combination and reduction intentionally share one op/identity pair, mirroring the reference
  -- evaluator's `Combine.combine`/`unit0`.
  return foldScalars reduceOp reduceId termAccs

/-- The BINARY64 specialization of `denseValueAtWith`, and the only one `runDenseScatter` uses. -/
private def denseValueAt (a : AssignPlan) (ctx : List Int) (store : Array DenseTensor)
    (oc : List Int) : Except PositionalInputError Float :=
  denseValueAtWith floatOps a ctx store oc

/-- Execute one checked operation at a fixed context coordinate: `denseValueAt` at every output
    coordinate, in row-major order, into a tensor of the plan's own `outputShape`.

    **The storage-kind guard is first, before the context and store checks.** This is the deepest
    public binary64 assignment door, and it is where checked binary32 evidence must stop: this
    worker's store is `Array Float` and its scalar runtime is `floatOps`, so executing `.float32`
    evidence here would answer a binary32 question in binary64 with no diagnostic anywhere. Guarding
    `runDenseAssign` alone would be insufficient — that is a wrapper, and `runDenseBlock`
    (`Block.lean`) calls THIS entry directly. -/
def runDenseAssignAt (c : CheckedAssignPlan) (ctx : List Int) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  unless c.storageKind == .float64 do
    throw (.storageKindMismatch .float64 c.storageKind)
  validateContext c.plan ctx
  validateStore c.plan store
  let a := c.plan
  let out ← (allCoords a.outputShape.toList).mapM (denseValueAt a ctx store)
  return { shape := a.outputShape.toList, data := out.toArray }


/-- The empty-context wrapper every existing (scan-free) call site uses. -/
def runDenseAssign (c : CheckedAssignPlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor :=
  runDenseAssignAt c [] store

/-! ## The native binary32 local worker (f32 slice, Task 3)

The mirror image of the two entries above, over `float32Ops` and an `Array DenseTensor32` store.
Structurally identical — same guard, same context/store validation, same row-major output
enumeration, same shared traversal — because everything that is NOT scalar arithmetic is genuinely
carrier-independent; the whole of the difference is which `ScalarKernelOps` record is handed to
`denseValueAtWith`, and that record is where every binary32 fact lives.

There is deliberately no third, generic public entry taking a raw `AssignPlan` plus an ops record:
that would be an unchecked execution door, and the storage-kind guards below would have nothing to
guard.
-/

/-- Execute one checked BINARY32 operation at a fixed context coordinate. Native `Float32`
    throughout: the store's buffers are `Array Float32`, the zero-pad is native `+0`, an Iverson
    predicate becomes native one/zero, and every factor/reduction/term fold step is a native
    binary32 operation that rounds on its own. Nothing widens to `Float` anywhere on this path.

    **The storage-kind guard is first, before the context and store checks** — the exact mirror of
    `runDenseAssignAt`'s, and load-bearing for the same reason in the other direction: binary64
    evidence executed here would answer a binary64 question in binary32, silently losing 29 bits of
    significand. Guarding `runDenseAssign32` alone would be insufficient, since a direct caller can
    invoke this entry (and `Adapter32.lean` will, in Task 4). -/
def runDenseAssignAt32 (c : CheckedAssignPlan) (ctx : List Int) (store : Array DenseTensor32) :
    Except PositionalInputError DenseTensor32 := do
  unless c.storageKind == .float32 do
    throw (.storageKindMismatch .float32 c.storageKind)
  validateContext c.plan ctx
  validateStore c.plan store
  let a := c.plan
  let out ← (allCoords a.outputShape.toList).mapM (denseValueAtWith float32Ops a ctx store)
  return { shape := a.outputShape.toList, data := out.toArray }

/-- The empty-context wrapper, the binary32 sibling of `runDenseAssign`. Inherits the guard above
    rather than repeating it. -/
def runDenseAssign32 (c : CheckedAssignPlan) (store : Array DenseTensor32) :
    Except PositionalInputError DenseTensor32 :=
  runDenseAssignAt32 c [] store

/-! ## The dense scatter worker (S-A Task 4)

`runDensePlan`'s `.scatter` arm (`EvalPlan.lean`) calls `runDenseScatter` and writes its result to
`c.plan.compute.destinationSlot` — the scatter's only destination slot (S-A Task 2 wired this). It
reaches this worker with a `CheckedScatterPlan`, never the compute half's `CheckedAssignPlan`, which
is the point of `CheckedScatterPlan` storing no such evidence. A scatter step is still unreachable
from source syntax; that is Task 5.
-/

/-- Execute one checked scatter over a positional store. SOURCE-driven, which is the whole structural
    difference from `runDenseAssignAt`: that worker enumerates its DESTINATION and pulls one value per
    destination cell, while this one enumerates `compute.outputShape` — the source iteration domain —
    evaluates the compute half there through the shared `denseValueAt`, and PUSHES the value to
    `outCoeffs · sourceCoordinate + outBias`. Unwritten destination cells keep `fill`.

    Reproduces `Eval/Scatter.lean`'s `evalScatter` equation for equation **for the real sum-product
    algebra**, because differential parity against that evaluator is this feature's correctness gate
    (plan §2.1) — including the two places where matching it means NOT improving it:

    * **An out-of-range destination coordinate is skipped silently.** The reference tests its placed
      coordinate against the output shape and simply does not write when it fails, with no
      diagnostic. `checkScatter`'s docstring names this as the one case-audit cell it leaves to this
      worker, and rejecting it here — statically or at runtime — would refuse programs the reference
      accepts. The test is `inBoundsPerDim` (`Coordinates.lean`), the same per-dimension predicate
      `gatherFactorWith` uses on the read side, and it runs BEFORE `flatIndex`: a flat-offset test
      can alias distinct invalid coordinates onto a valid address (proposal §8.3). So `Int.toNat` on
      the destination coordinate is never lossy here — every component is already known
      non-negative.
    * **The `.toNat` extent degeneracies reach this worker as an empty destination, not as an
      error.** A zero or negative placement coefficient makes `LHSSlot.outExtent` clamp that
      dimension's extent to `0` (`ScatterCheckTest` pins both), and `checkScatter` admits the plan
      because `destShape` does equal `outExtent`'s answer. Here that means `inBoundsPerDim` is false
      at every source coordinate, so every write is skipped by the rule above and the result is the
      empty tensor the reference produces. Nothing special-cases it.

    **A TROPICAL-algebra scatter's unwritten cells diverge from the reference BY DESIGN, and that
    divergence is permanent.** The scoping of the parity claim above is load-bearing, not hedging:
    the reference's `ScatterOpts.fill` is an `Int` (`DSL/Ast.lean`) which `evalScatter` widens with
    `Float.ofInt`, so the reference layer cannot express `±∞` at all and fills every unwritten cell
    with an integer-valued Float — `0.0` in practice, its default. `checkScatter` meanwhile forces
    `fill == compute.algebra.reduceId`, which for `admittedAlgebraMax`/`Min` IS `∓∞`, and the checked
    plan's `fill : ScalarConst` can carry it. So on a max/min scatter the two implementations
    provably disagree on every unwritten cell, and this worker is the correct one: filling with `0.0`
    under max-product would let a spurious zero win the reduction over an all-negative cell, the
    exact incoherence `PlanError.scatterFillNotIdentity` exists to reject. `ScatterDenseTest`'s
    tropical-`fill` fixture pins the checked-layer value and records the divergence; a differential
    corpus must therefore not treat a tropical scatter as a parity-checked entry without special
    casing the unwritten cells.

    `writtenBy` maps a destination flat index to the FIRST source coordinate that wrote there, and
    exists only to name both halves of a conflict in `scatterCollision` — the reference's own reason
    for carrying it. `.rejectCollisions` is the only policy `checkScatter` admits, so the four arms
    beside it are unreachable for any `CheckedScatterPlan`; they are written to the reference's own
    equations (not to each other) so that admitting one later is a checker change alone. -/
def runDenseScatter (c : CheckedScatterPlan) (store : Array DenseTensor) :
    Except PositionalInputError DenseTensor := do
  let s := c.plan
  let a := s.compute
  -- A scatter is admitted only as a top-level step, so its compute half runs at the empty context —
  -- the same coordinate `runDenseAssign` supplies. Validated rather than assumed: `checkScatter`
  -- deliberately does not check `compute.contextShape` (`checkPlan`'s `contextCheck` owns that), so
  -- a non-empty one must fail loud here instead of silently binding no context position.
  validateContext a []
  validateStore a store
  let destShape := s.destShape.toList
  -- The placement map's fields already ARE `AffineMap`'s, row per destination dimension and width per
  -- source position, so `applyAffine` applies as-is — no second affine evaluator.
  let placement : AffineMap := { coeffs := s.outCoeffs, bias := s.outBias }
  let fill ← floatOps.decodeConst s.fill
  let mut data : Array Float := Array.replicate (destShape.foldl (· * ·) 1) fill
  let mut writtenBy : Std.HashMap Nat (List Nat) := {}
  for sc in allCoords a.outputShape.toList do
    let val ← denseValueAt a [] store sc
    let dc := applyAffine placement sc
    if inBoundsPerDim destShape dc then
      let oc := dc.map Int.toNat
      let fi := flatIndex destShape oc
      let prev := data.getD fi fill
      match s.reduce with
      | .rejectCollisions =>
          match writtenBy[fi]? with
          | some firstSrc => throw (.scatterCollision oc firstSrc (sc.map Int.toNat))
          | none =>
              writtenBy := writtenBy.insert fi (sc.map Int.toNat)
              data := data.set! fi val
      | .overwrite => data := data.set! fi val
      | .sum => data := data.set! fi (prev + val)
      | .max => data := data.set! fi (Max.max prev val)
      | .min => data := data.set! fi (Min.min prev val)
  return { shape := destShape, data := data }

-- `runDensePlan` used to live here (C3), but now that a checked outer graph can contain a `.scan`
-- node (whose worker is `runDenseScan`, `Scan.lean`), it relocated to `EvalPlan.lean` — the only
-- module that can see both this file's `runDenseAssign` and `Scan.lean`'s `runDenseScan` without a
-- circular import. See `EvalPlan.lean`.

end LeanNCD.Eval.Plan

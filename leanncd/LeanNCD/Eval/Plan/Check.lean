import LeanNCD.Eval.Plan.Error
import LeanNCD.Eval.Plan.Graph

/-!
# Wave C local checked construction (C2)

`checkAssign` is the only way to obtain a `CheckedAssignPlan`. Its constructor is `private mk ::`
— NOT a bare `structure … where private`, which compiles but leaves the anonymous constructor
public and silently defeats the boundary. Field projections remain public under `private mk ::`
(construction is blocked, reading is not), which is the intended design: build only through the
checker, read freely.

Graph availability and production order are deliberately NOT checked here — they are not local
properties. `checkPlan` (C3) adds them.
-/

namespace LeanNCD.Eval.Plan

/-- Evidence that one `AssignPlan` satisfies every local invariant. -/
structure CheckedAssignPlan where private mk ::
  raw : AssignPlan
  deriving Repr

/-- Trusted accessor for the validated payload. -/
def CheckedAssignPlan.plan (c : CheckedAssignPlan) : AssignPlan := c.raw

/-- Wave C admits exactly one algebra: real sum-product with binary64 identities. -/
def admittedAlgebra : ContractionAlgebra :=
  { factorOp := .mul, factorId := .f64 (Float.toBits 1.0)
  , reduceOp := .add, reduceId := .f64 (Float.toBits 0.0) }

/-- Tropical max-product `(×, max, −∞)` — the algebra `AggOp.max` compiles to. Identity `−∞` so an
    all-negative reduction still returns its greatest element (a `0` identity would spuriously win).
    Mirrors the reference `Combine.max`. -/
def admittedAlgebraMax : ContractionAlgebra :=
  { factorOp := .mul, factorId := .f64 (Float.toBits 1.0)
  , reduceOp := .max, reduceId := .f64 (Float.toBits (-1.0 / 0.0)) }

/-- Tropical min-product `(×, min, +∞)` — the algebra `AggOp.min` compiles to. Identity `+∞` so an
    all-positive reduction still returns its least element. Mirrors the reference `Combine.min`. -/
def admittedAlgebraMin : ContractionAlgebra :=
  { factorOp := .mul, factorId := .f64 (Float.toBits 1.0)
  , reduceOp := .min, reduceId := .f64 (Float.toBits (1.0 / 0.0)) }

/-- Boolean conjunction/disjunction `(min, max)` with identities `true`/`false` — the algebra a
    predicate destination compiles to. `min` with identity `true` conjoins a term's factors; `max`
    with identity `false` disjoins both a term's contracted coordinates and the completed terms,
    mirroring the reference `Combine.bool` exactly.

    `.bool` here is a SEMANTIC tag over Float-backed storage, not a native carrier: `Dense.constFloat`
    decodes `.bool true` to `1.0` and `.bool false` to `0.0`, and `applyOp` runs the same Float
    `min`/`max` the reference evaluator does. Runtime values are therefore NOT restricted to `0.0`/
    `1.0`; a non-binary Float retains literal `min`/`max` behavior rather than being coerced or
    rejected. The out-of-bounds `zeroPad` policy needs no Boolean special case: a padded read is a
    factor value of `0.0` = false, which is exactly what `min` should propagate. -/
def admittedAlgebraBool : ContractionAlgebra :=
  { factorOp := .min, factorId := .bool true
  , reduceOp := .max, reduceId := .bool false }

/-- The algebras `checkAssign` admits for an `f64` destination: real sum-product plus the two
    tropical semirings that `AggOp.max`/`.min` select. The out-of-bounds `zeroPad` policy still pads
    reads with `0` in all three — a padded read is a factor value flowing through `factorOp` (mul),
    never the reduction identity — so only `reduceOp`/`reduceId` differ between them. -/
def admittedAlgebras : List ContractionAlgebra :=
  [admittedAlgebra, admittedAlgebraMax, admittedAlgebraMin]

/-- Algebra admission is DESTINATION-SPECIFIC: the destination dtype selects the algebra, and no
    other dtype's algebras are admitted alongside it. A real destination may not carry the Boolean
    algebra and a predicate destination may not carry real sum-product or a tropical semiring —
    either would silently give a destination semantics its declared dtype does not name. `f32` admits
    nothing; it is already rejected by the earlier `dtypeNotAdmitted` destination guard, and this
    empty list keeps that fact local to the table rather than relying on the guard's order. -/
def admittedAlgebrasFor : ScalarDType → List ContractionAlgebra
  | .f64  => admittedAlgebras
  | .bool => [admittedAlgebraBool]
  | .f32  => []

/-- The extents this term projects onto the output, in `outputPos` order. -/
def TermPlan.outputProjection (t : TermPlan) : Array Nat :=
  t.outputPos.filterMap (fun p => t.iterationShape[p]?)

/-- The extents this term projects onto the surrounding context, in `contextPos` order. -/
def TermPlan.contextProjection (t : TermPlan) : Array Nat :=
  t.contextPos.filterMap (fun p => t.iterationShape[p]?)

/-- `contextPos ++ outputPos ++ reductionPos` must be a disjoint partition of every iteration-basis
    position.
    Checked by sorting the concatenation and comparing against `List.range`, which catches
    duplicates, omissions, and out-of-range positions in one comparison. -/
def TermPlan.positionsPartition (t : TermPlan) : Bool :=
  let all := (t.contextPos ++ t.outputPos ++ t.reductionPos).toList
  all.length == t.iterationShape.size && all.mergeSort (· ≤ ·) == List.range t.iterationShape.size

def constMatchesDtype : ScalarDType → ScalarConst → Bool
  | .f64,  .f64 _  => true
  | .f32,  .f32 _  => true
  | .bool, .bool _ => true
  | _, _ => false

/-- The storage dtypes a checked assignment may name, at a destination or at a read: `f64` and the
    Float-backed Boolean tag. `f32` remains rejected — no worker implements binary32 rounding, so
    admitting the tag would silently execute it as binary64. -/
def dtypeAdmitted : ScalarDType → Bool
  | .f64 | .bool => true
  | .f32 => false

/-- Validate one operation against the positional signature table.

    `destSigShape?` is the shape the DESTINATION SIGNATURE must carry. `none` — every existing
    caller — means "the plan's own `outputShape`", which is the original clause verbatim: for an
    assignment the iteration domain it writes over and the extent of the tensor it writes into are
    the same array, and the error payload is unchanged (`destinationShapeMismatch a.outputShape
    destSig.shape`).

    A scatter is exactly the case that separates those two, which is why the clause is a parameter
    rather than a constant. `checkScatter` passes `some s.destShape`: a scatter's registered
    destination signature carries the DESTINATION extent, while `s.compute.outputShape` is the
    SOURCE iteration domain — comparing the signature against the latter would reject every strided
    write (`#[6]` against `#[3]` for `Out[2*i] := X[i]`, `i : 3`). Everything else here is checked
    for a scatter's compute half unchanged: the destination dtype still selects the algebra, and the
    term/factor loop still pins each term's `outputProjection` to `compute.outputShape`, which is the
    right obligation on the source side. -/
def checkAssign (sigs : Array TensorSignature) (a : AssignPlan)
    (destSigShape? : Option (Array Nat) := none) :
    Except PlanError CheckedAssignPlan := do
  let destSig ← match sigs[a.destinationSlot]? with
    | some s => pure s
    | none => throw (.slotOutOfRange a.destinationSlot sigs.size)
  unless dtypeAdmitted destSig.dtype do
    throw (.dtypeNotAdmitted a.destinationSlot destSig.dtype)
  let expectedDestShape := destSigShape?.getD a.outputShape
  unless destSig.shape == expectedDestShape do
    throw (.destinationShapeMismatch expectedDestShape destSig.shape)
  unless (admittedAlgebrasFor destSig.dtype).contains a.algebra do
    throw (.algebraNotAdmitted a.algebra)
  unless constMatchesDtype destSig.dtype a.algebra.factorId do
    throw (.constDtypeMismatch destSig.dtype a.algebra.factorId)
  unless constMatchesDtype destSig.dtype a.algebra.reduceId do
    throw (.constDtypeMismatch destSig.dtype a.algebra.reduceId)
  for h : ti in [0 : a.terms.size] do
    let t := a.terms[ti]
    unless t.positionsPartition do throw (.positionsNotPartition ti)
    unless t.outputProjection == a.outputShape do
      throw (.outputProjectionMismatch ti t.outputProjection a.outputShape)
    unless t.contextProjection == a.contextShape do
      throw (.contextProjectionMismatch ti t.contextProjection a.contextShape)
    for h2 : fi in [0 : t.factors.size] do
      match t.factors[fi] with
      | .iverson b =>
          -- A positional Iverson predicate: no source slot, no affine read. Each Boolean-leaf
          -- coefficient row must span exactly the term's iteration basis; a width failure reuses the
          -- same `affineWidthMismatch ti fi` locator a read affine row throws, `fi` kept at the
          -- all-factor index.
          for w in b.affineWidths do
            unless w == t.iterationShape.size do
              throw (.affineWidthMismatch ti fi t.iterationShape.size w)
      | .read f =>
        let srcSig ← match sigs[f.sourceSlot]? with
          | some s => pure s
          | none => throw (.slotOutOfRange f.sourceSlot sigs.size)
        -- A source dtype does not have to equal the destination's: the DESTINATION selects the
        -- algebra, and gathering is dtype-blind (`Dense.gatherFactor` reads the same `Array Float`
        -- either way, applies no truth check, and performs no conversion). So an `f64` source may
        -- feed a predicate destination and a `bool` source may feed a real one; only `f32` — which
        -- no worker implements — is rejected. `PlanError.dtypeMismatch` is deliberately no longer
        -- produced here (see `KernelCheckTest`); nonlinearity checking keeps its own separate
        -- dtype-equality error, `NonlinPlanError.dtypeMismatch`.
        unless dtypeAdmitted srcSig.dtype do throw (.dtypeNotAdmitted f.sourceSlot srcSig.dtype)
        unless f.sourceShape == srcSig.shape do
          throw (.sourceShapeMismatch ti fi f.sourceShape srcSig.shape)
        unless f.oobPolicy == .zeroPad do throw (.policyNotAdmitted f.oobPolicy)
        unless f.map.coeffs.size == f.sourceShape.size && f.map.bias.size == f.sourceShape.size do
          throw (.affineRankMismatch ti fi f.sourceShape.size f.map.coeffs.size)
        for row in f.map.coeffs do
          unless row.size == t.iterationShape.size do
            throw (.affineWidthMismatch ti fi t.iterationShape.size row.size)
  return CheckedAssignPlan.mk a

/-! ## The scatter checker (S-A Task 3)

`checkScatter` is free-standing: `checkPlan` still rejects every scatter step with
`.scatterNotChecked` (`EvalPlan.lean`), because admitting one needs both this checker AND a checked
scatter evidence arm plus a dense worker. Wiring is a later task; this is the validator it will call.
-/

/-- Evidence that one `ScatterPlan` satisfies every local invariant. Same `private mk ::` boundary
    as `CheckedAssignPlan`: `checkScatter` is the only way to obtain one, projections stay public.

    Deliberately stores ONLY the raw plan — not the `CheckedAssignPlan` `checkAssign` returned for
    the compute half. A scatter's worker is source-driven and must not be able to hand that evidence
    to `runDenseAssign`: doing so publishes the SOURCE-shaped compute result under the destination's
    name, which is the exact silent-wrong-answer failure the rejected "widen `AssignPlan`" design was
    measured to produce. -/
structure CheckedScatterPlan where private mk ::
  raw : ScatterPlan
  deriving Repr

/-- Trusted accessor for the validated payload. -/
def CheckedScatterPlan.plan (c : CheckedScatterPlan) : ScatterPlan := c.raw

/-- The `LHSSlot` one destination dimension of a scatter's placement map denotes, over a synthetic
    positional axis basis: basis axis `k` is source-iteration position `k`, minted as an `AxisSpec`
    whose `uid` IS that position. The uids are private to this derivation — `scatterDestExtent`
    builds the matching sizing lookup alongside them — so they cannot collide with a program's own.

    Always `outExtent`'s `.affine` arm, never its `.const` arm, and that is a fact about which slot
    forms can reach a `ScatterPlan` rather than a convenience. `outExtent`'s `.axis`/`.scale`/
    `.shift`/`.affine` arms are all the same `bias + Σ coeff · size` sum this reconstruction
    reproduces; `.const` (extent `n + 1`) is reachable only from `LHSSlot.iterAt`, which is what
    `elabTLLHSSlot` (`DSL/Elab.lean`) turns a bare numeral LHS slot into — a scan base case — and
    `checkScatterNoScan` (`DSL/Pipeline/Structural.lean`) rejects a scatter-shaped LHS carrying any
    iteration slot. So an all-zero placement row keeps the documented `.toNat` degeneracy of the
    zero-coefficient slot it comes from (`Out[0*i]` has extent `0`), rather than being re-read as a
    constant coordinate with extent `bias + 1`. -/
def scatterPlacementSlot (row : Array Int) (bias : Int) : LHSSlot :=
  .affine (.affine bias
    (row.toList.zipIdx.map (fun (c, k) => (c, { name := "", uid := k, kind := .nat }))))

/-- The destination extent one placement row implies, BY CALLING `LHSSlot.outExtent` — the one home
    of the `scale * n + offset` convention (`DSL/Ast.lean`). This restates no arithmetic of its own,
    and in particular not the memory-sufficient bound `scale * (n - 1) + offset + 1`, which is
    measured to disagree with the convention by exactly `scale - 1`; a second extent formula has
    already shipped a soundness bug in this repo once. `srcShape` is the source iteration domain
    (`compute.outputShape`), indexed by position to match `scatterPlacementSlot`'s synthetic uids. -/
def scatterDestExtent (srcShape : Array Nat) (row : Array Int) (bias : Int) : Option Nat :=
  (scatterPlacementSlot row bias).outExtent (fun u => srcShape[u]?)

/-- Validate one raw `ScatterPlan` against the positional signature table.

    Clause order: the compute half through the shared `checkAssign` core, then the two scalar
    coherence clauses (`fill`, `reduce`), then the placement map's rank and its per-dimension width
    and extent — global facts before the loop, the same shape `checkAssign` itself uses.

    The compute half is checked with `destSigShape? := some s.destShape`, which is the whole point of
    that parameter: the registered destination signature must carry the DESTINATION extent, while
    `s.compute.outputShape` is the SOURCE iteration domain. Every other `checkAssign` clause applies
    to a scatter's compute half unchanged (the destination dtype selects the algebra; each term's
    `outputProjection` pins to the source domain).

    `fill`'s dtype needs no separate check: the algebra-admission clause inside `checkAssign` already
    forces `compute.algebra` into the destination dtype's own row of `admittedAlgebrasFor`, whose
    every member carries that dtype's constants, so `fill == compute.algebra.reduceId` makes the
    fill's dtype track the destination's transitively. Writing a second `constMatchesDtype` check
    here would be a second, weaker copy of that guard. `ScalarConst.f32` is unreachable in a checked
    plan for the same reason.

    `s.compute.contextShape` is NOT checked here: a scatter is admitted only as a top-level step, and
    `checkPlan`'s own `contextCheck` arm already discharges that obligation on the nested plan's
    field.

    **Placement RANGE is not checked here either, deliberately, and it is the one case-audit cell
    this checker leaves to the worker.** Nothing above rejects a placement map that sends some source
    coordinate outside `[0, destShape[d])` — a negative coefficient or bias is admitted as long as
    `destShape` equals `outExtent`'s answer for it, which for `#[-1]` over a rank-3 source domain is
    the empty destination `#[0]`, accepted with three source values and nowhere to put them. That is
    not an oversight to close statically: the reference evaluator `Eval/Scatter.lean` **skips an
    out-of-range output coordinate silently**, the checked layer's obligation is to REPRODUCE that
    (differential parity against the reference is the gate for this feature), and a static rejection
    here would refuse plans the reference accepts. So the owner is the dense scatter worker, where the
    per-coordinate skip belongs and where parity is measured — not this function. Mitigating fact
    while that worker is unwritten: the shape is unreachable from surface syntax, since
    `elabTLLHSSlot` (`DSL/Elab.lean`) parses only non-negative numeral coefficients and biases in an
    affine LHS slot, so only a programmatic `ScatterPlan` can express it. -/
def checkScatter (sigs : Array TensorSignature) (s : ScatterPlan) :
    Except PlanError CheckedScatterPlan := do
  let _ ← checkAssign sigs s.compute (some s.destShape)
  unless s.fill == s.compute.algebra.reduceId do
    throw (.scatterFillNotIdentity s.fill s.compute.algebra.reduceId)
  match s.reduce with
  | .rejectCollisions => pure ()
  | .overwrite | .sum | .max | .min => throw (.scatterReduceNotAdmitted s.reduce)
  unless s.outCoeffs.size == s.destShape.size && s.outBias.size == s.destShape.size do
    throw (.scatterPlacementRankMismatch s.destShape.size s.outCoeffs.size s.outBias.size)
  let srcRank := s.compute.outputShape.size
  -- Zipped rather than indexed so each destination dimension's row, bias, and declared extent are
  -- in hand together; the rank clause above makes the zip lossless.
  for ((row, bias, declared), d) in
      (s.outCoeffs.toList.zip (s.outBias.toList.zip s.destShape.toList)).zipIdx do
    unless row.size == srcRank do
      throw (.scatterPlacementWidthMismatch d srcRank row.size)
    match scatterDestExtent s.compute.outputShape row bias with
    | none => throw (.scatterDestExtentUnknown d)
    | some derived =>
        unless declared == derived do
          throw (.scatterDestExtentMismatch d declared derived)
  return CheckedScatterPlan.mk s

-- `CheckedEvalPlan`/`checkPlan` used to live here (C3), but now that the outer graph can contain a
-- `.scan` step, both relocated to `EvalPlan.lean` — the only module that can see both the local
-- checker here and `Scan.lean`'s `checkScanPlan` without a circular import. See `EvalPlan.lean`.

end LeanNCD.Eval.Plan

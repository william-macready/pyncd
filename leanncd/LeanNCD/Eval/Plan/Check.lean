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

/-- Evidence that one `AssignPlan` satisfies every local invariant, TOGETHER WITH the storage kind
    it was validated for.

    `storageKind` is set only by `checkAssign` (`.float64`) and `checkAssignF32` (`.float32`); the
    constructor stays `private mk ::`, so no caller can relabel evidence. It is stored rather than
    re-derived because re-derivation needs the signature table, which the workers do not all carry:
    the point of the field is that handing binary32 evidence to the binary64 worker is a
    fail-loud `PositionalInputError.storageKindMismatch` at that worker's own door
    (`runDenseAssignAt`, `Dense.lean`), not a silent binary64 execution of a binary32 question. -/
structure CheckedAssignPlan where private mk ::
  raw : AssignPlan
  storageKind : LeanNCD.StorageKind
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

    `.bool` here is a SEMANTIC tag over whichever real carrier the graph's storage kind selects, not
    a native carrier of its own — both graphs' tables (`admittedAlgebrasFor`,
    `admittedAlgebrasForF32`) use this one algebra for a `bool` destination. Each carrier's private
    scalar runtime (`floatOps`/`float32Ops`, `Dense.lean`) decodes `.bool true`/`.bool false` to its
    own exact one/zero and runs its own `min`/`max` over them. Runtime values are therefore NOT
    restricted to `0`/`1`; a non-binary value retains literal `min`/`max` behavior rather than being
    coerced or rejected. The out-of-bounds `zeroPad` policy needs no Boolean special case: a padded
    read is a factor value of `0.0` = false, which is exactly what `min` should propagate. -/
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
    either would silently give a destination semantics its declared dtype does not name.

    This is the FLOAT64 graph's table, consulted only by `checkAssign`. Its `f32` row stays empty:
    an `f32` destination in a binary64 graph is already rejected by the earlier `dtypeNotAdmitted`
    destination guard, and the empty row keeps that fact local to the table rather than relying on
    the guard's order. The binary32 graph has its own table, `admittedAlgebrasForF32` below — the
    two are separate rather than merged because algebra admission is about which CARRIER's constants
    a destination may denote, and a `.f64`-identity algebra under an `f32` destination is exactly
    the silent precision substitution this slice exists to prevent. -/
def admittedAlgebrasFor : ScalarDType → List ContractionAlgebra
  | .f64  => admittedAlgebras
  | .bool => [admittedAlgebraBool]
  | .f32  => []

/-! ## The binary32 algebras (f32 slice, Task 2)

The `f32` counterparts of the three real algebras above. Every identity is a `ScalarConst.f32`
bit pattern, never a `.f64` one: `constMatchesDtype` is the final defense against a cross-tag
identity reaching a worker, and a `.f64` identity under an `f32` destination would be decoded by a
binary64 `Float.ofBits` in a binary32 fold. -/

/-- Real binary32 sum-product `(×, +, 0)`. `factorId` is `0x3f800000` = binary32 `1.0`;
    `reduceId` is `0x00000000` = binary32 `+0.0`. -/
def admittedAlgebraF32 : ContractionAlgebra :=
  { factorOp := .mul, factorId := .f32 0x3f800000
  , reduceOp := .add, reduceId := .f32 0x00000000 }

/-- Tropical binary32 max-product `(×, max, −∞)`. `reduceId` is `0xff800000` = binary32 `−∞`, so an
    all-negative reduction still returns its greatest element. Mirrors `admittedAlgebraMax`. -/
def admittedAlgebraF32Max : ContractionAlgebra :=
  { factorOp := .mul, factorId := .f32 0x3f800000
  , reduceOp := .max, reduceId := .f32 0xff800000 }

/-- Tropical binary32 min-product `(×, min, +∞)`. `reduceId` is `0x7f800000` = binary32 `+∞`.
    Mirrors `admittedAlgebraMin`. -/
def admittedAlgebraF32Min : ContractionAlgebra :=
  { factorOp := .mul, factorId := .f32 0x3f800000
  , reduceOp := .min, reduceId := .f32 0x7f800000 }

/-- The binary32 counterpart of `admittedAlgebras`. -/
def admittedAlgebrasF32 : List ContractionAlgebra :=
  [admittedAlgebraF32, admittedAlgebraF32Max, admittedAlgebraF32Min]

/-- The FLOAT32 graph's destination-specific algebra table, consulted only by `checkAssignF32`.
    A `bool` destination keeps `admittedAlgebraBool` verbatim — a Boolean tensor is an algebra tag
    over whichever real carrier the graph selected, so its `.bool` identities are decoded to the
    selected carrier's own exact zero/one by that carrier's scalar runtime, not converted. The
    `.f64` row is empty for the mirror-image reason `admittedAlgebrasFor`'s `.f32` row is: an `f64`
    destination in a binary32 graph is already rejected by `checkAssignF32`'s destination guard. -/
def admittedAlgebrasForF32 : ScalarDType → List ContractionAlgebra
  | .f32  => admittedAlgebrasF32
  | .bool => [admittedAlgebraBool]
  | .f64  => []

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

/-- The storage dtypes a FLOAT64 checked assignment may name, at a destination or at a read: `f64`
    and the Float-backed Boolean tag. `f32` stays rejected HERE, permanently: this predicate is the
    binary64 checker's own admission rule, and admitting the tag would hand binary32 data to the
    `Array Float` worker. The binary32 graph is not a relaxation of this predicate — it has its own
    checker (`checkAssignF32` below) with its own admission rule (`dtypeAdmittedF32`), its own
    algebra table, and its own storage-kind evidence, so no global relaxation of `dtypeAdmitted` is
    needed or allowed. `checkScanPlan` (`Scan.lean`) and `checkPointwise`/`checkAxiswise`
    (`Nonlin.lean`) share this predicate and stay Float-backed for the same reason. -/
def dtypeAdmitted : ScalarDType → Bool
  | .f64 | .bool => true
  | .f32 => false

/-- The storage dtypes a FLOAT32 checked assignment may name at its DESTINATION: `f32` and the
    Boolean tag (an algebra tag over the graph's selected real carrier, here `Float32`). The
    mirror image of `dtypeAdmitted`. The SOURCE rule is not this predicate — see
    `checkAssignCore`'s source clause, which reports an `f64` source as
    `PlanError.dtypeMismatch .f32 .f64` rather than as a bare `dtypeNotAdmitted`, because in a
    binary32 graph an `f64` read is a precision disagreement with a known other side, not an
    unimplementable tag. -/
def dtypeAdmittedF32 : ScalarDType → Bool
  | .f32 | .bool => true
  | .f64 => false

/-! ## Graph-level storage-kind derivation

Kept strictly SEPARATE from per-dtype operation capability (`admittedAlgebrasFor*`,
`dtypeAdmitted*`): "which carrier does this whole table live in" and "which operations does this
dtype support" are different questions, and a future complex dtype must be able to share the
generic tensor plumbing below while still rejecting operations such as min/max that have no
declared complex semantics. -/

/-- The storage constraint one signature dtype places on a table, or `none` if it places none.
    The plan-layer sibling of `LeanNCD.storageConstraintOfDecl` (`DSL/Ast.lean`), over the
    signature vocabulary rather than the declaration vocabulary:

    * `.f64 → some .float64`, `.f32 → some .float32` — a real dtype SELECTS the carrier;
    * `.bool → none` — a Boolean signature INHERITS the carrier the real signatures select, exactly
      as a `predicate` declaration is precision-neutral at the source layer. Mapping `bool` to a
      fixed `.float64` here would make every `[f32, bool]` graph mixed, which is precisely the
      combination this slice admits. -/
def storageConstraintOfDtype : ScalarDType → Option LeanNCD.StorageKind
  | .f64  => some .float64
  | .f32  => some .float32
  | .bool => none

/-- The single storage kind a complete signature table commits to, or the FIRST slot whose real
    dtype disagrees with the kind an earlier slot established.

    Scans slots in table order; the first real (non-`bool`) signature establishes the kind, and the
    scan STOPS at the first slot that disagrees, so a table with several conflicts reports the
    earliest one. An empty or bool-only table defaults to `.float64`, preserving the behavior of
    every graph that existed before this slice. `[f64, bool]` is `.float64` and `[f32, bool]` is
    `.float32`, because `bool` contributes no constraint at all. -/
def deriveStorageKind (sigs : Array TensorSignature) :
    Except PlanError LeanNCD.StorageKind := do
  let mut established : Option (LeanNCD.StorageKind × ScalarDType) := none
  for h : i in [0 : sigs.size] do
    match storageConstraintOfDtype sigs[i].dtype with
    | none => pure ()
    | some k =>
        match established with
        | none => established := some (k, sigs[i].dtype)
        | some (k0, dt0) =>
            unless k0 == k do throw (.mixedStorageKinds i dt0 sigs[i].dtype)
  return (established.map (·.1)).getD .float64

/-- Validate one operation against the positional signature table, for one storage kind.

    THE one assignment checker: `checkAssign` (binary64) and `checkAssignF32` (binary32) are both
    thin applications of it, so the shape, partition, affine, policy, and all-factor-index clauses
    exist once and cannot drift between carriers. `kind` is the ONLY parameter that varies the
    policy, and it varies it at exactly four clauses — destination dtype admission, algebra table,
    source dtype rule, and inline-unary admission — each marked below. It is also what the returned
    evidence records, so a worker can refuse evidence built for the other carrier.

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
private def checkAssignCore (kind : LeanNCD.StorageKind) (sigs : Array TensorSignature)
    (a : AssignPlan) (destSigShape? : Option (Array Nat)) :
    Except PlanError CheckedAssignPlan := do
  let destSig ← match sigs[a.destinationSlot]? with
    | some s => pure s
    | none => throw (.slotOutOfRange a.destinationSlot sigs.size)
  unless (match kind with
          | .float64 => dtypeAdmitted destSig.dtype
          | .float32 => dtypeAdmittedF32 destSig.dtype) do
    throw (.dtypeNotAdmitted a.destinationSlot destSig.dtype)
  let expectedDestShape := destSigShape?.getD a.outputShape
  unless destSig.shape == expectedDestShape do
    throw (.destinationShapeMismatch expectedDestShape destSig.shape)
  let algebras := match kind with
    | .float64 => admittedAlgebrasFor destSig.dtype
    | .float32 => admittedAlgebrasForF32 destSig.dtype
  unless algebras.contains a.algebra do
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
        -- algebra, and gathering is dtype-blind (a carrier's gather reads the same store either
        -- way, applies no truth check, and performs no conversion). So within one storage kind an
        -- `f64` source may feed a predicate destination and a `bool` source may feed a real one.
        -- What a source may NOT do is name the OTHER real carrier:
        --   * in a `.float64` graph an `f32` source is `dtypeNotAdmitted` — the binary64 checker's
        --     own admission rule, unchanged;
        --   * in a `.float32` graph an `f64` source is `dtypeMismatch .f32 .f64` — the graph's real
        --     carrier against this read's, which is a precision DISAGREEMENT between two known
        --     sides rather than an unimplementable tag, and is the one producer of that constructor
        --     (it was producer-less between Task 4.2 and this slice; nonlinearity checking keeps its
        --     own separate `NonlinPlanError.dtypeMismatch`).
        match kind with
        | .float64 =>
            unless dtypeAdmitted srcSig.dtype do
              throw (.dtypeNotAdmitted f.sourceSlot srcSig.dtype)
        | .float32 =>
            unless dtypeAdmittedF32 srcSig.dtype do
              throw (.dtypeMismatch .f32 srcSig.dtype)
        unless f.sourceShape == srcSig.shape do
          throw (.sourceShapeMismatch ti fi f.sourceShape srcSig.shape)
        unless f.oobPolicy == .zeroPad do throw (.policyNotAdmitted f.oobPolicy)
        unless f.map.coeffs.size == f.sourceShape.size && f.map.bias.size == f.sourceShape.size do
          throw (.affineRankMismatch ti fi f.sourceShape.size f.map.coeffs.size)
        for row in f.map.coeffs do
          unless row.size == t.iterationShape.size do
            throw (.affineWidthMismatch ti fi t.iterationShape.size row.size)
        -- Inline unary math is admitted in a `.float64` graph (the Float worker delegates to
        -- `UnaryOp.applyChecked`) and rejected in a `.float32` one: native binary32 `log`/`exp`/
        -- `sqrt`/`recip` are slice F32-B, and routing an f32 read through the binary64 helper would
        -- be false f32. Located at the ORIGINAL all-factor index `fi`, like every other per-factor
        -- locator here, and last among this factor's clauses so the pre-existing shape/policy/affine
        -- diagnostics keep strict priority over it.
        match kind with
        | .float64 => pure ()
        | .float32 =>
            unless f.unary.isNone do
              throw (.unaryNotAdmittedForDtype ti fi .f32)
  return CheckedAssignPlan.mk a kind

/-- The FLOAT64 public checker: the original Wave C policy, unchanged in every clause, now naming
    its storage kind explicitly on the evidence it returns. Still rejects `f32` at the destination
    and at every read (`dtypeAdmitted`), so the legacy entry was not widened by this slice. -/
def checkAssign (sigs : Array TensorSignature) (a : AssignPlan)
    (destSigShape? : Option (Array Nat) := none) :
    Except PlanError CheckedAssignPlan :=
  checkAssignCore .float64 sigs a destSigShape?

/-- The FLOAT32 public checker, through the same private core: identical shape, partition, affine,
    policy, and all-factor-index clauses, differing only where the carrier genuinely differs — the
    admitted destination/source dtypes, the algebra table, and the inline-unary rejection. It is a
    sibling of `checkAssign`, never a relaxation of it: the two produce evidence carrying DIFFERENT
    storage kinds, and every worker and adapter door checks that kind before touching a buffer.

    `destSigShape?` is retained for signature parity with `checkAssign`; this slice's only caller
    (`checkPlan`, `EvalPlan.lean`) passes `none`, since a binary32 scatter — the one construct that
    needs it — is deferred to slice F32-D. -/
def checkAssignF32 (sigs : Array TensorSignature) (a : AssignPlan)
    (destSigShape? : Option (Array Nat) := none) :
    Except PlanError CheckedAssignPlan :=
  checkAssignCore .float32 sigs a destSigShape?

/-! ## The scatter checker (S-A Task 3)

`checkPlan`'s `.scatter` local check (`EvalPlan.lean`) calls `checkScatter` and publishes its
`CheckedScatterPlan` as `CheckedPlanStepEvidence.scatter` (S-A Task 2 wired this; the transient
unconditional rejection that stood in its place between Tasks 3 and 2 is gone). A `checkScatter`
failure surfaces as `PlanStepError.assign (.nodeError ni e)`, like `checkAssign`'s — that
constructor names the error's SHAPE (a plain `PlanError`, which is what this function returns), not
the step's kind. A scatter step is still unreachable from source syntax; that is Task 5.
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

    Always `outExtent`'s affine calculation, never its `.const` arm: this function constructs an
    `.affine` expression even when the row is all zero. Thus an all-zero placement row keeps the
    documented `.toNat` degeneracy of the zero-coefficient slot it comes from (`Out[0*i]` has extent
    `0`), rather than being re-read as a constant coordinate with extent `bias + 1`. -/
def scatterPlacementSlot (row : Array Int) (bias : Int) : LHSSlot :=
  .affine (.affine bias
    (row.toList.zipIdx.map (fun (c, k) => (c, { name := "", uid := k, kind := .nat }))))

/-- The destination extent one placement row implies, BY CALLING `LHSSlot.outExtent` — the one home
    of the normalized stride-aligned convention and its legacy fallbacks (`DSL/Ast.lean`). This
    restates no arithmetic of its own; a second extent formula has already shipped a soundness bug
    in this repo once. `srcShape` is the source iteration domain (`compute.outputShape`), indexed by
    position to match `scatterPlacementSlot`'s synthetic uids. -/
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

import LeanNCD.Eval.Gather
import LeanNCD.Eval.Error
import LeanNCD.DSL.TraverseAxes
namespace LeanNCD.Eval
open Std

-- E1 migration sub-project 2: the five `*AxisUIDs` collectors below are `ConstL (List UID)`
-- instantiations of the production `NodeName.traverseAxes` machinery
-- (`LeanNCD/DSL/TraverseAxes.lean`), the UID-direction analogue of sub-project 1's `specs*`
-- migration. `freeAxisUIDs` is deliberately NOT migrated (see its comment).

/-- All axis-UIDs referenced by an index expression.
    The `ConstL (List UID)` instantiation of `IdxExpr.traverseAxes`. -/
def idxAxisUIDs (e : IdxExpr) : List UID :=
  (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run

/-- All axis-UIDs referenced by predicate arithmetic.
    The `ConstL (List UID)` instantiation of `PredArith.traverseAxes`. -/
def predAxisUIDs (e : PredArith) : List UID :=
  (PredArith.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run

/-- All axis-UIDs referenced by a Boolean/mask predicate.
    The `ConstL (List UID)` instantiation of `BoolExpr.traverseAxes`. -/
def boolAxisUIDs (e : BoolExpr) : List UID :=
  (BoolExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run

/-- The free axes (LHS) of an assign, as UID list (affine slots contribute none). -/
-- Deliberately NOT migrated to `traverseAxes` (unlike the other collectors in this block):
-- `LHSSlot.axisUID?` returns `none` for `.affine` slots, so `freeAxisUIDs` collects a *subset* — the
-- free (non-affine) axes only — not every axis. `LHSSlot.traverseAxes` visits every axis
-- (including the affine slot's `IdxExpr`), so this is not a `traverseAxes` instantiation and the
-- spike proves no equivalence for it. Migrating it would silently change its meaning.
def freeAxisUIDs (slots : List LHSSlot) : List UID := slots.filterMap (·.axisUID?)

/-- Every axis-UID appearing in one product term's reads/masks. This is the per-term
    contraction scope: a `+`-joined RHS sums each term over only the axes *that term*
    mentions, not the union of axes across the whole equation (see `evalAssignWith`).
    The `ConstL (List UID)` instantiation of `ProdTerm.traverseAxes`. -/
def termAxisUIDs (t : ProdTerm) : List UID :=
  (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) t).run

/-- Every axis-UID appearing anywhere in the RHS reads/masks (union across all terms).
    Used for size inference / shape solving, where the full axis set is wanted — NOT for
    contraction scoping, which must stay per-term (`termAxisUIDs`). -/
-- The `ConstL (List UID)` instantiation of `RHSExpr.traverseAxesNoMask`.
-- IMPORTANT — `traverseAxesNoMask`, NOT `traverseAxesWithMask`: `readAxisUIDs` deliberately
-- EXCLUDES the nonlin-mask axes (the documented `specsRHS`-includes-vs-`readAxisUIDs`-excludes
-- asymmetry). `traverseAxesNoMask` never visits `r.nonlin`. A future edit to `WithMask` here
-- would silently pull nonlin-mask UIDs into shape inference and corrupt it — do not change it.
def readAxisUIDs (rhs : RHSExpr) : List UID :=
  (RHSExpr.traverseAxesNoMask (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) rhs).run

/-- Every read tensor name appearing in the RHS. -/
def readNames (rhs : RHSExpr) : List String := rhs.readFactors.map (·.1)

/-- The cartesian product of `[0..d-1]` ranges (one per dimension). Reuses `allCoords`. -/
def cartesian (dims : List Nat) : List (List Nat) := DenseTensor.allCoords dims

/-- Evaluate an assign to its output tensor, seeded or not. A `seed : HashMap UID Int` pins
    axis-UIDs to fixed values (e.g. a scan's iteration axis, pinned to the current slice `l`);
    seeded UIDs are excluded from BOTH the free (output) axes and the contracted axes, and every
    per-output coord is seeded with these fixed values. `evalAssignWith` (below) is this function
    called with an empty seed — unseeded assignment IS seeded assignment with no pins, literally,
    not a separately maintained implementation.

    `mul` combines factors within a product term (empty product = `unit1`); `combine` folds
    contributions onto the accumulator starting from `unit0`. Default is the ℝ contraction
    `(*, +, 0, 1)`.

    Each product term is contracted **independently**, over only the axes that term itself
    mentions (`termAxisUIDs`), then its result is folded into the output accumulator via
    `combine`. This is standard per-term (Einstein) summation scoping: a `k`-less term like
    `a[i]` in `Y[i] := a[i] + W[i,k]·v[k]` must never be summed over `k` at all, since it has
    no `k`-dependence. Scoping contraction at the whole-equation level instead (one shared
    axis set for every term) would force `a[i]` through a `k`-indexed loop it doesn't need,
    adding it in `|k|` times instead of once.

    Fails loud (returns `.error`, never a wrong or empty-shaped tensor) if: a non-seeded free
    output axis has no inferable size; a seeded axis has no declared size, or its seed coordinate
    is out of range; or a per-term contracted axis has no inferable size (previously defaulted to
    extent one — Wave-B corroborating example #2, `papers/copilot_code_analysis.md`).

    All `.read`/`.unaryFn` tensor names are validated against `env` up front. A `gather` error
    during accumulation is now genuinely reachable — a `.unaryFn` domain violation (e.g.
    `log` of a non-positive value) — and propagates as a hard `.error`, per this evaluator's
    fail-loud convention; it is never treated as an out-of-range pad (out-of-range reads return
    `.ok pad` directly from `gather`, they never reach the `.error` branch at all). -/
def evalAssignSeeded (mul : Float → Float → Float) (combine : Float → Float → Float)
    (unit0 : Float) (unit1 : Float)
    (env : HashMap String DenseTensor) (sizes : HashMap UID Nat)
    (seed : HashMap UID Int) (nm : String) (slots : List LHSSlot) (rhs : RHSExpr)
    (castOf : String → Float → Float := fun _ v => v) :
    Except EvalError (String × DenseTensor) := do
  for rn in (readNames rhs).eraseDups do
    if !(env.contains rn) then
      throw (.unknownTensor .assign rn)
  -- free axes = LHS slot axes minus the seeded UIDs (and minus affine slots, which contribute none)
  let freesAll := freeAxisUIDs slots
  let frees := freesAll.filter (fun u => ! seed.contains u)
  -- fail loud: a non-seeded free output axis with no inferred size would silently yield a
  -- 0-extent tensor (Wave-B corroborating example #1).
  for u in frees do
    if (sizes[u]?).isNone then
      throw (.shape (.unsizedAxis u (.assignOutput nm)))
  -- fail loud: a seeded axis needs a declared size to check its seed coordinate is in range.
  for u in seed.keys do
    match sizes[u]? with
    | none   => throw (.shape (.unsizedAxis u (.assignSeeded nm)))
    | some n =>
        let v := (seed[u]?).getD 0
        if v < 0 || v >= Int.ofNat n then
          throw (.invalidSeed nm u v n)
  -- output shape: each non-seeded free slot's size, in slot order
  let outShape := slots.filterMap (fun sl => match sl.axisUID? with
    | some u => if seed.contains u then none else some ((sizes[u]?).getD 0)
    | none   => none)
  let data ← (DenseTensor.allCoords outShape).mapM (fun fcoord => do
      let baseCoord : HashMap UID Int :=
        (frees.zip fcoord).foldl (fun m (u, v) => m.insert u (Int.ofNat v)) seed
      let mut acc := unit0
      for t in rhs.body.terms do
        -- per-term contraction scoping, same rationale as above.
        let termContr := (termAxisUIDs t).eraseDups.filter (fun u => ! frees.contains u && ! seed.contains u)
        -- fail loud: a contracted axis with no inferable size used to silently contract at
        -- extent one (Wave-B corroborating example #2) instead of rejecting the malformed context.
        let termSizes ← termContr.mapM (fun u => match sizes[u]? with
          | some n => pure n
          | none   => throw (.shape (.unsizedAxis u (.assignContracted nm))))
        let mut termAcc := unit0
        for cc in cartesian termSizes do
          let coord := (termContr.zip cc).foldl (fun m (u, v) => m.insert u (Int.ofNat v)) baseCoord
          let mut prod := unit1
          for f in t.factors do
            match gatherCast unit0 unit1 castOf env coord f with
            | .ok v   => prod := mul prod v
            | .error e => throw e
          termAcc := combine termAcc prod
        acc := combine acc termAcc
      pure acc)
  return (nm, ⟨outShape, data.toArray⟩)

/-- Unseeded assignment: `evalAssignSeeded` with an empty seed, literally — not a separate
    implementation. -/
def evalAssignWith (mul : Float → Float → Float) (combine : Float → Float → Float)
    (unit0 : Float) (unit1 : Float)
    (env : HashMap String DenseTensor) (sizes : HashMap UID Nat)
    (nm : String) (slots : List LHSSlot) (rhs : RHSExpr) : Except EvalError (String × DenseTensor) :=
  evalAssignSeeded mul combine unit0 unit1 env sizes {} nm slots rhs

/-- The default tensor (ℝ) contraction: multiply factors, then sum contributions. -/
def evalAssign := evalAssignWith (· * ·) (· + ·) 0.0 1.0

/-- The contraction "semiring" to use for an output, selected by its declared dtype. -/
structure Combine where
  mul     : Float → Float → Float
  combine : Float → Float → Float
  unit0   : Float
  unit1   : Float

/-- The ℝ contraction `(×, Σ)`: multiply factors, then sum. -/
def Combine.real : Combine := ⟨(· * ·), (· + ·), 0.0, 1.0⟩

/-- The Boolean contraction `(∧, ∃)` on 0/1 Floats: `min` factors (∧), `max` terms (∃). Both are the
    NaN-propagating `minNaN`/`maxNaN` (identical to `min`/`max` on 0/1 values; they differ only on a
    non-binary NaN input). -/
def Combine.bool : Combine := ⟨minNaN, maxNaN, 0.0, 1.0⟩

/-- The shared shape of the two tropical semirings: ⊗ = `+` with identity `1_K = 0.0`, ⊕ = `op`
    (NaN-propagating `max`/`min`) with identity `0_K = zero` (`−∞` for max-plus, `+∞` for min-plus).
    `Combine.max` and `Combine.min` instantiate it once each, so the two directions share code and
    differ only in `(op, zero)`. -/
def Combine.tropical (op : Float → Float → Float) (zero : Float) : Combine :=
  ⟨(· + ·), op, zero, 0.0⟩

/-- Max-plus `(+, max, −∞, 0)`: ADD factors within a term, then take the NaN-propagating max across
    terms and contracted axes. `unit0 = −∞` (`0_K`) so all-negative inputs reduce correctly;
    `unit1 = 0` is the empty product. -/
def Combine.max : Combine := Combine.tropical maxNaN (-1.0 / 0.0)

/-- Min-plus `(+, min, +∞, 0)`: ADD factors within a term, then take the NaN-propagating min across
    terms and contracted axes. `unit0 = +∞` (`0_K`) so all-positive inputs reduce correctly. -/
def Combine.min : Combine := Combine.tropical minNaN (1.0 / 0.0)

/-- Whether `nm`'s declaration is a `predicate`, i.e. its values are Boolean {0,1}. Searches
    TENSOR-BEARING declarations only (everything but `.axis`/`.iter`: `.tensor`, `.typedTensor`,
    `.linear`, `.typedLinear`, `.predicate`), taking the first match.
    `.axis`/`.iter` declarations name an axis, not a tensor, and are excluded from `DeclEnv`
    (`resolveDecls`) — including them here let an earlier `axis Result` hide a later
    `predicate Result` and silently select real sum-product for a Boolean output. -/
def isPredicateDest (decls : List Decl) (nm : String) : Bool :=
  match decls.find? (fun d => match d with
      | .axis _ _ | .iter _ _ => false
      | _                     => d.name == nm) with
  | some (.predicate _ _) => true
  | _                     => false

/-- Pick the `Combine` for an output given its decl and the RHS aggregation op.
    Priority: `agg = .max` ⇒ tropical max; `agg = .min` ⇒ tropical min; `predicate` ⇒ bool; else real.
    The `.sum` arm's predicate lookup is `isPredicateDest`. -/
def combineFor (decls : List Decl) (nm : String) (agg : AggOp) : Combine :=
  match agg with
  | .max => Combine.max
  | .min => Combine.min
  | .sum => if isPredicateDest decls nm then Combine.bool else Combine.real

/-- The per-source READ CAST of a statement, as a per-source-name map for `gatherCast` (applied to
    BARE in-bounds reads only: never a unary-function read, never the out-of-range pad).
    `nm` is the statement's DESTINATION; `c`/`agg` its `Combine`/aggregation.
    * Tropical statement (`agg` ≠ `.sum`; S3b design §3), the bool -> tropical cast: a bare read of
      a `predicate`-declared tensor reads a stored false (`0`) as `c.unit0` (0_K: `-inf`/`+inf`) and
      a stored true (anything else) as `c.unit1` (1_K: `0.0`).
    * Boolean statement (`agg = .sum` into a `predicate` destination; S3b-ii D1), the real -> bool
      cast: a bare read of a NON-`predicate` tensor reads `v != 0` as `c.unit1` (`1.0`) else
      `c.unit0` (`0.0`) — the same truth rule as the bool -> tropical cast (NaN is `!= 0`, so it
      reads true: pinned, not endorsed).
    Every other read, and every real statement, is the identity, so real statements stay
    bit-identical and a bool -> bool read is unchanged. -/
def boolReadCast (decls : List Decl) (nm : String) (c : Combine) (agg : AggOp) :
    String → Float → Float :=
  match agg with
  | .sum => fun src v =>
      if isPredicateDest decls nm && !isPredicateDest decls src then
        (if v != 0.0 then c.unit1 else c.unit0)
      else v
  | .max | .min => fun src v =>
      if isPredicateDest decls src then (if v != 0.0 then c.unit1 else c.unit0) else v

/-! ## The storage boundary of the reference evaluator

Every worker in `Eval/` computes in `Float` (IEEE-754 binary64): `Combine`'s four fields, the
`evalAssignSeeded` accumulator, `DenseTensor.data`. A tensor a declaration explicitly commits to
`f32` therefore cannot be evaluated at its declared precision here, and running it as `Float` would
silently answer a different question than the source asks — so every public entry refuses it
outright, BEFORE its own algebra selection, gathering, shape, scan-structure, or nonlinearity work.

This is the per-NAME rule the DIRECT entries use. The schedule-wide sibling
(`scheduleFloat32Name?`, `DSL/Pipeline/ScheduledValidation.lean`) is what `evalScheduled` uses;
neither classifies declarations itself — both go through `storageConstraintOfName?`
(`DSL/Ast.lean`). -/

/-- The tensor names one statement commits to a storage kind, in rejection-reporting order: the
    DESTINATION first, then its read sources in RHS traversal order. The destination is first
    because it is what the statement's algebra and output tensor are built for; a mixed statement
    is named by its destination, not by whichever source happens to be read first. -/
def stmtStorageNames (s : Stmt) : List String := s.lhsName :: s.readFactors.map (·.1)

/-- Refuse a statement/schedule whose declarations commit any of `names` to `.float32`.

    `buildDeclEnv` (`DSL/Ast.lean`) runs FIRST, over `decls` as presented: a name declared
    tensor-bearing twice makes "which declaration is `Y`" ambiguous, so the storage question is not
    even well-defined until the environment is — and that is the SAME shared, duplicate-rejecting
    builder `resolveDecls` and `prepareEvalPlan`'s Step 0 apply, reported through the existing
    `EvalError.compile` constructor, not a second private scan.

    Rejection is per-OPERAND, not per-disagreement: a homogeneously-f32 statement is refused just
    as a mixed one is, because binary64 execution is wrong for both. -/
def rejectUnsupportedStorage (decls : List Decl) (names : List String) :
    Except EvalError Unit := do
  let env : DeclEnv ← match buildDeclEnv decls with
    | .ok e    => pure e
    | .error e => throw (.compile e)
  for nm in names do
    if storageConstraintOfName? env nm == some .float32 then
      throw (.unsupportedDtype nm)

/-- dtype-aware assign, seeded or not: choose the `Combine` from the decls and `rhs.agg`, then
    evaluate. Shared by `evalPlain` (via `evalAssignDtyped`, its empty-seed wrapper) AND
    `Scan.evalStmtSliceSeeded` — before Wave B (4c), the scan path matched `rhs.agg` manually and
    could never select `Combine.bool` for a predicate state, since it never saw `decls` at all.
    `agg = .max` ⇒ max-plus `(+, max, −∞)`; `agg = .min` ⇒ min-plus `(+, min, +∞)`;
    `predicate` ⇒ Boolean `(∧, ∃)`;
    else ℝ `(×, Σ, 0)`.

    This is the DEEPEST public assignment entry, so the storage refusal
    (`rejectUnsupportedStorage`) is installed here — before algebra selection and before
    `evalAssignSeeded` validates reads against `env` or gathers anything. `evalAssignDtyped` (the
    empty-seed wrapper), `Eval.evalPlain`'s assignment arm, and `Scan.evalStmtSliceSeeded`'s
    assignment arm all inherit it; the scan/scatter paths that do NOT route through here get their
    own entry guard. -/
def evalAssignDtypedSeeded (decls : List Decl)
    (env : HashMap String DenseTensor) (sizes : HashMap UID Nat)
    (seed : HashMap UID Int) (nm : String) (slots : List LHSSlot) (rhs : RHSExpr) :
    Except EvalError (String × DenseTensor) := do
  rejectUnsupportedStorage decls (nm :: readNames rhs)
  let c := combineFor decls nm rhs.agg
  evalAssignSeeded c.mul c.combine c.unit0 c.unit1 env sizes seed nm slots rhs
    (boolReadCast decls nm c rhs.agg)

/-- Unseeded dtype-aware assign: `evalAssignDtypedSeeded` with an empty seed. -/
def evalAssignDtyped (decls : List Decl)
    (env : HashMap String DenseTensor) (sizes : HashMap UID Nat)
    (nm : String) (slots : List LHSSlot) (rhs : RHSExpr) :
    Except EvalError (String × DenseTensor) :=
  evalAssignDtypedSeeded decls env sizes {} nm slots rhs

end LeanNCD.Eval

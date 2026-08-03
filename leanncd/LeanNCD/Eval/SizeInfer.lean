import LeanNCD.DSL.Ast
import LeanNCD.Eval.Tensor
import LeanNCD.Eval.Error
import LeanNCD.Eval.SizeSolve
import Std.Data.HashMap

namespace LeanNCD.Eval
open Std

-- `idxAffineForm` (the shared affine-lowering primitive) lives in `DSL/Ast.lean`; the unqualified
-- name below resolves to `LeanNCD.idxAffineForm` (M2 dedup, §6.2).
--
-- Owns the concrete, shape-driven half of axis-size inference: turning statements' actual read
-- positions (against known input/scatter-output shapes) into `SizeSolve.SizeConstraint`s, driving
-- the solve-and-repropagate fixpoint (`inferAxisSizes`), and reporting the two failure modes that
-- are about *which* axes are unsized rather than the arithmetic of solving for them (a bare-axis
-- conflict, and Issue D's purely-negatively-constrained axis). `SizeSolve.lean` is the layer below
-- (pure constraint algebra, no notion of a "read position" or a `Stmt`); this module is the sole
-- caller of everything `SizeSolve` exposes.

/-- One affine read position: a read `name[e]` against a known dimension `d`, with `e` already
    lowered to `const + Σ coeffs`. Private: purely this module's intermediate representation
    between "walk the statements" and "hand `SizeSolve` a constraint" — nothing outside
    `inferAxisSizes` needs to see it. -/
private structure AffinePosition where
  coeffs : List (Int × UID)
  const : Int
  dim : Nat
  source : String

/-- Build the affine positions for one tensor's read factors against a known shape, tagging each
    position's diagnostic `source` with `nm[e]` plus a `suffix` (empty for an ordinary input read,
    `" (scatter-out)"` for a read of a scatter-produced shape). `inferAxisSizes` collected these
    two position families via two separately-written, otherwise-identical `flatMap` blocks before
    this split; consolidating them here keeps the diagnostic source text
    (`{nm}[{repr e}]` / `{nm}[{repr e}] (scatter-out)`) byte-identical to before the move — the
    `suffix` argument is exactly the string each original block's `source :=` line appended. -/
private def affinePositionsOf (suffix : String) (nm : String) (es : List IdxExpr) (shape : List Nat) :
    List AffinePosition :=
  (es.zip shape).map (fun (e, d) =>
    let (const, coeffs) := idxAffineForm e
    { coeffs := SizeSolve.normalizeCoeffs coeffs, const, dim := d,
      source := s!"{nm}[{repr e}]{suffix}" })

/-- Merge one solver-produced size into the running `sizes` map, failing loud on a conflict with an
    already-known size for the same UID (the same "axis size conflict" wording `inferAxisSizes`
    uses for its own bare-axis check below — this is the solver-output-merging counterpart of that
    check, not a duplicate of it: one validates a single read against one already-known size, this
    one validates the solver's simultaneous solution for possibly-many UIDs against the state
    those UIDs already had before this solve round). Private: only the fixpoint loop calls it. -/
private def insertSolvedSize (sizes : HashMap UID Nat) (u : UID) (sz : Nat) :
    Except EvalError (HashMap UID Nat) :=
  match sizes[u]? with
  | some d' =>
      if d' == sz then
        return sizes
      else
        throw (.shape (.sizeConflict u d' sz))
  | none => return sizes.insert u sz

/-- Output shapes of the scatter stmts whose source axes are all sized, keyed by output name. Lets
    downstream reads of a scatter-produced tensor size their own axes (B3 — the eval read-path for
    scatter outputs, e.g. an upsampling decoder feeding a subsequent layer). -/
def scatterOutputShapes (sizes : HashMap UID Nat) (stmts : List Stmt) : HashMap String (List Nat) :=
  stmts.foldl (fun m s => match s with
    | .scatter nm slots _ _ =>
        match slots.mapM (fun sl => sl.outExtent (fun u => sizes[u]?)) with
        | some dims => m.insert nm dims
        | none      => m
    | _ => m) {}

/-- Sorted-unique `EvalWarning` list insertion, keyed by each warning's rendered text — mirrors
    `SizeSolve.insertStringSortedUnique`'s ordering/dedup logic exactly, so `inferAxisSizes`'s
    warning list is ordered identically to before 4h (when warnings were raw pre-rendered
    strings) even though the list now holds typed `EvalWarning` values. Keying by `toString`
    rather than duplicating a second renderer keeps `EvalWarning.render` the sole place warning
    text is produced. -/
private def insertWarningSortedUnique (acc : List EvalWarning) (w : EvalWarning) : List EvalWarning :=
  match acc with
  | [] => [w]
  | x :: xs =>
      let ws := toString w
      let xs' := toString x
      if ws == xs' then
        acc
      else if ws < xs' then
        w :: acc
      else
        x :: insertWarningSortedUnique xs w

/-- Infer axis-UID → concrete size from the input tensors + read positions.
    For a read `name[e₁,…,eₘ]` whose input `env[name]` has shape `[d₁,…,dₘ]`, each `eᵢ`
    is treated as the integer-affine map `c0 + Σ cₖ·aₖ`. A bare `.axis a` (the common case)
    binds `a.uid ↦ dᵢ`. For a richer affine position with one or more unknown axes, we build
    the upper-envelope constraint `Σ max(cₖ,0)·sizeₖ = d - c0 + Σ max(cₖ,0) - 1` and pass all
    remaining unknowns to an exact RREF solver over ℚ. Non-integral RREF solutions are floored
    and verified against all original constraints as inequalities (padded semantics: the maximal
    valid index need not sit exactly at `d-1`). This is the unified floor-then-verify convention.
    Conflicting sizes for one UID ⇒ error. We iterate to a fixpoint so inference order
    (e.g. a kernel axis sizing before the dotted output axis) does not matter.
    `seed` pre-binds axes pinned by `axis … = n` or `iter … = n` decls; inference treats them as already
    known (and a later read implying a different size conflicts, as for any bound UID).

    **Known gap (Issue H)**: when ALL axes in a multi-term read are already sized (fully-known
    position), the max-index `c0 + Σ max(cₖ,0)·(sizeₖ-1)` may exceed `dim-1`. Under padded
    semantics this is valid (out-of-range reads return 0) but is often surprising. A non-fatal
    warning is emitted for such positions; the second component of a successful return pair
    collects all such warnings, while `EvalFailure.warnings` preserves them if a later inference
    step fails. Only bare-axis positions (`name[a]`) receive a hard conflict check. -/
def inferAxisSizes (seed : HashMap UID Nat) (env : HashMap String DenseTensor)
    (stmts : List Stmt) : Except EvalFailure (HashMap UID Nat × List EvalWarning) := do
  -- collect every (affine-form, dim) read position once
  let positions : List AffinePosition := stmts.flatMap (fun s =>
    (Stmt.readFactors s).flatMap (fun (nm, es) =>
      match env[nm]? with
      | none   => []
      | some t => affinePositionsOf "" nm es t.shape))
  let mut sizes : HashMap UID Nat := seed
  let mut warns : List EvalWarning := []
  -- fixpoint: build upper-envelope constraints for all unknown positions, solve jointly,
  -- then loop until no new sizes are learned. Each iteration also derives scatter OUTPUT shapes
  -- from the sizes learned so far (B3) and adds read positions for downstream reads of those
  -- outputs — so e.g. an upsample's scatter output can size a subsequent layer's read axes. The
  -- extra `stmts.length` iterations let sizes flow through scatter-produce → read phases.
  for _ in List.range (positions.length + stmts.length + 1) do
    let producedShapes := scatterOutputShapes sizes stmts
    let scatterPositions : List AffinePosition := stmts.flatMap (fun s =>
      (Stmt.readFactors s).flatMap (fun (nm, es) =>
        match producedShapes[nm]? with
        | none       => []
        | some shape => affinePositionsOf " (scatter-out)" nm es shape))
    let mut deferred : List SizeConstraint := []
    for pos in positions ++ scatterPositions do
      let maxCoeffs := SizeSolve.upperEnvelopeCoeffs pos.coeffs
      let unknown := maxCoeffs.filter (fun (_, u) => ! (sizes.contains u))
      match unknown with
      | [] =>
          match pos.const, pos.coeffs with
          | 0, [(1, u)] =>
              -- bare single-axis: hard conflict check
              match sizes[u]? with
              | some d' =>
                  if d' != pos.dim then
                    throw { error := .shape (.sizeConflict u d' pos.dim), warnings := warns }
              | none => pure ()
          | _, _ =>
              -- Issue H: fully-known multi-term (or negative-only) read.
              -- Under padded semantics this is valid, but warn if max-index ≥ dim.
              let maxIdx : Int := pos.const + maxCoeffs.foldl
                (fun acc (coef, u) => acc + coef * (Int.ofNat ((sizes[u]?).getD 0) - 1)) 0
              if maxIdx >= Int.ofNat pos.dim then
                warns := insertWarningSortedUnique warns (.paddedAccess pos.source maxIdx pos.dim)
      | _ =>
          deferred := deferred ++
            [SizeSolve.mkConstraint maxCoeffs pos.const pos.dim pos.source]
    let remaining :=
      (deferred.map (SizeSolve.substituteKnownSizes sizes)).filter (fun c => !c.coeffs.isEmpty)
    if remaining.isEmpty then
      break
    let solved ← match SizeSolve.solveSizeConstraints remaining with
      | .ok solved => .ok solved
      | .error error => .error { error, warnings := warns }
    let mut solverChanged := false
    for (u, sz) in solved.toList do
      let next ← match insertSolvedSize sizes u sz with
        | .ok next => .ok next
        | .error error => .error { error, warnings := warns }
      if !(sizes.contains u) then
        solverChanged := true
      sizes := next
    unless solverChanged do break
  -- Issue D: axes that appear in reads but only with non-positive upper-envelope
  -- coefficients are invisible to the solver. Detect and fail loud.
  let uidMaxCoeff : HashMap UID Int := positions.foldl (fun acc pos =>
    pos.coeffs.foldl (fun acc' (coef, u) =>
      acc'.insert u (max coef ((acc'[u]?).getD coef))) acc) {}
  let negUids := uidMaxCoeff.toList.foldl
    (fun acc (u, c) =>
      if c <= 0 && !sizes.contains u then SizeSolve.insertUIDSorted acc u else acc) []
  if let u :: _ := negUids then
    let srcs := positions.filterMap (fun pos =>
      if pos.coeffs.any (fun (_, v) => v == u) then some pos.source else none)
    throw { error := .shape (.negativeOnlyAxis u srcs), warnings := warns }
  return (sizes, warns)

end LeanNCD.Eval

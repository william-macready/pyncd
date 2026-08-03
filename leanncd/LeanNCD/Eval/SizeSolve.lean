import LeanNCD.Exec.Uid
import LeanNCD.Eval.Error
import Std.Data.HashMap

namespace LeanNCD.Eval
open Std

-- Owns the pure affine-constraint solver: a `SizeConstraint` is one linear inequality over axis
-- UIDs (an upper-envelope translation of a single affine read position — see `SizeInfer.lean` for
-- where those positions come from), and `solveSizeConstraints` reduces a whole batch to concrete
-- UID sizes via RREF over `ℚ`. This module knows nothing about statements, tensors-by-name, or the
-- inference fixpoint that drives it; `SizeInfer.lean` is the sole caller of everything exposed
-- here. Keeping this file's public surface small (constraint construction/substitution + the
-- solver entry point) rather than exporting RREF internals means the exact-rational row-reduction
-- mechanics can be touched independently of anything outside this file. As of 4h, `SolveFailureKind`
-- and `SolveDiagnostic` (and their renderer/remediation helpers) live in `Error.lean` instead of
-- here: this file only ever CONSTRUCTS a `SolveDiagnostic` at each of its four failure points and
-- immediately wraps/throws it as `EvalError.shape (.solveFailure _)` — it never renders one, so
-- the type's public home is the module that owns rendering, not the module that owns solving.

/-- One linear constraint over unsized axis UIDs: `Σ coeffs[i].1 · size(coeffs[i].2) ≤ rhs`,
    carrying a `source` label (e.g. `"X[i+j]"`) for diagnostics. Built from an affine read
    position's upper-envelope coefficients by `mkConstraint`; solved jointly by
    `solveSizeConstraints`. -/
structure SizeConstraint where
  coeffs : List (Int × UID)
  rhs : Int
  source : String

namespace SizeSolve

/-- One row of the RREF matrix over `ℚ`: `Σ coeffs[i]·var[i] = rhs`, carrying the set of original
    constraint `source`s that were combined (by elimination or row-merging) to produce it, so a
    failure at this row can still cite every contributing read position. Private: pure pivoting
    scratch space, never inspected outside the solver loop. -/
private structure RatRow where
  coeffs : Array Rat
  rhs : Rat
  sources : List String := []
  deriving Inhabited

/-- Sorted-unique string list insertion. Exposed (not `private`): `SizeInfer.inferAxisSizes` reuses
    this exact ordering primitive to build its deterministic padded-access warning list, so the
    warning order doesn't depend on statement traversal order any more than the solver's own
    `mlHints`/`sourceRefs` lists do. -/
def insertStringSortedUnique (acc : List String) (s : String) : List String :=
  match acc with
  | [] => [s]
  | x :: xs =>
      if s == x then
        acc
      else if s < x then
        s :: acc
      else
        x :: insertStringSortedUnique xs s

private def mlHintsOfConstraints (constraints : List SizeConstraint) : List String :=
  let hints0 : List String := []
  let hints1 := if constraints.length ≥ 2 then
      insertStringSortedUnique hints0 "ml-hint: coupled affine constraints"
    else
      hints0
  let hints2 := if constraints.any (fun c => c.coeffs.length ≥ 2) then
      insertStringSortedUnique hints1 "ml-hint: multi-axis window constraint"
    else
      hints1
  if constraints.any (fun c => c.coeffs.any (fun (coef, _) => coef.natAbs > 1)) then
    insertStringSortedUnique hints2 "ml-hint: stride/dilation-like coefficients"
  else
    hints2

private def mergeStringLists (xs ys : List String) : List String :=
  ys.foldl insertStringSortedUnique xs

private def uidConstraintCount (constraints : List SizeConstraint) (u : UID) : Nat :=
  constraints.foldl (fun acc c => if c.coeffs.any (fun (_, v) => v == u) then acc + 1 else acc) 0

private def uidConstraintSources (constraints : List SizeConstraint) (u : UID) : List String :=
  constraints.foldl
    (fun acc c => if c.coeffs.any (fun (_, v) => v == u) then insertStringSortedUnique acc c.source else acc)
    []

private def renderUnderdeterminedDetail (constraints : List SizeConstraint) (freeUids : List UID)
    (rank vars : Nat) : String :=
  let uidParts := freeUids.map
    (fun u => s!"uid {u}: in {uidConstraintCount constraints u} equation(s), sources={uidConstraintSources constraints u}")
  s!"rank={rank}, vars={vars}, {uidParts}"

private def addCoeff (acc : List (Int × UID)) (coef : Int) (u : UID) : List (Int × UID) :=
  match acc with
  | [] => if coef == 0 then [] else [(coef, u)]
  | (c, v) :: rest =>
      if v == u then
        let c' := c + coef
        if c' == 0 then rest else (c', v) :: rest
      else
        (c, v) :: addCoeff rest coef u

private def insertCoeffSorted (acc : List (Int × UID)) (entry : Int × UID) : List (Int × UID) :=
  match acc with
  | [] => [entry]
  | hd :: tl =>
      if entry.2 < hd.2 then
        entry :: acc
      else
        hd :: insertCoeffSorted tl entry

private def sortCoeffs (coeffs : List (Int × UID)) : List (Int × UID) :=
  coeffs.foldl (fun acc entry => insertCoeffSorted acc entry) []

/-- Fold duplicate-UID coefficients together (dropping any that cancel to zero) and re-sort by
    UID. Exposed: `SizeInfer` calls this both when building each `AffinePosition`'s `coeffs` (so
    positions are already canonical before they reach the solver) and, via `upperEnvelopeCoeffs`,
    when computing the upper-envelope subset. -/
def normalizeCoeffs (coeffs : List (Int × UID)) : List (Int × UID) :=
  sortCoeffs (coeffs.foldl (fun acc (coef, u) => addCoeff acc coef u) [])

/-- The "upper envelope" of an affine position: only the positive-coefficient terms, since a
    negative-coefficient axis can only ever pull the max index down (raising that axis's size
    never risks pushing the read out of range) and so does not participate in the size-bounding
    inequality. Exposed: `SizeInfer.inferAxisSizes` calls this directly to decide, per read
    position, which axes are actually still unknown after excluding negative-only coefficients
    (Issue D's "purely negatively constrained" axes are the ones that never show up here). -/
def upperEnvelopeCoeffs (coeffs : List (Int × UID)) : List (Int × UID) :=
  normalizeCoeffs (coeffs.filterMap (fun (coef, u) => if coef > 0 then some (coef, u) else none))

/-- Reduce a constraint's coefficients to lowest terms (divide through by their gcd with `rhs`)
    and fix its sign (leading coefficient, or `rhs` if the constraint has no coefficients, must be
    non-negative) so that two constraints derived from equivalent affine reads compare equal by
    structure — this is what lets `sortConstraints`/`insertConstraintSorted` deduplicate-by-key and
    the RREF row-merge (`findEquivalentRow?`) recognize identical rows. Private: an internal
    normal-form step of constraint construction, not itself something `SizeInfer` needs to call —
    every constraint it builds (via `mkConstraint`) or substitutes (via `substituteKnownSizes`) is
    already canonicalized by those two exposed entry points. -/
private def canonicalizeConstraint (constraint : SizeConstraint) : SizeConstraint :=
  let coeffs0 := normalizeCoeffs constraint.coeffs
  let g := coeffs0.foldl (fun acc (coef, _) => Nat.gcd acc coef.natAbs) constraint.rhs.natAbs
  let g := if g == 0 then 1 else g
  let div := Int.ofNat g
  let coeffs1 := if g == 1 then coeffs0 else coeffs0.map (fun (coef, u) => (coef / div, u))
  let rhs1 := if g == 1 then constraint.rhs else constraint.rhs / div
  let lead : Int := match coeffs1.find? (fun (coef, _) => coef != 0) with
    | some (coef, _) => coef
    | none => rhs1
  let negLead := match lead with
    | Int.negSucc _ => true
    | _ => false
  let (coeffs2, rhs2) := if negLead then
      (coeffs1.map (fun (coef, u) => (-coef, u)), -rhs1)
    else
      (coeffs1, rhs1)
  { constraint with coeffs := sortCoeffs coeffs2, rhs := rhs2 }

/-- Build the canonical `SizeConstraint` for one affine read position — "the maximal valid index
    `const + Σ coef·(size-1)` must be `≤ dim-1`" rearranges to `Σ coef·size ≤ dim - const + Σ coef
    - 1`, which this canonicalizes. Exposed (not `private`): this is the constraint-construction
    step `SizeInfer.inferAxisSizes` calls once per still-unsized read position, after it has
    already filtered `coeffs` down to the upper-envelope subset via `upperEnvelopeCoeffs`. It takes
    the position's raw fields rather than `SizeInfer`'s `AffinePosition` structure itself, so this
    module (which `SizeInfer` imports) never needs to import `SizeInfer` back to name that type. -/
def mkConstraint (coeffs : List (Int × UID)) (const : Int) (dim : Nat) (source : String) : SizeConstraint :=
  let rhs := Int.ofNat dim - const + coeffs.foldl (fun acc (coef, _) => acc + coef) 0 - 1
  canonicalizeConstraint { coeffs, rhs, source }

/-- Eliminate every already-known UID from a constraint, folding its contribution into `rhs` and
    re-canonicalizing. Exposed (not `private`): `SizeInfer.inferAxisSizes`'s fixpoint calls this
    directly on each deferred constraint every iteration, since a UID solved in an earlier
    iteration (or seeded up front) must stop appearing as a solver variable in later ones — the
    solver's own `sortedVarsOfConstraints` only sees genuinely-still-unknown UIDs this way. -/
def substituteKnownSizes (sizes : HashMap UID Nat) (constraint : SizeConstraint) : SizeConstraint :=
  let (rhs, coeffsRev) := constraint.coeffs.foldl
    (fun (state : Int × List (Int × UID)) (coef, u) =>
      match sizes[u]? with
      | some sz => (state.1 - coef * Int.ofNat sz, state.2)
      | none    => (state.1, (coef, u) :: state.2))
    (constraint.rhs, [])
  canonicalizeConstraint { constraint with rhs, coeffs := normalizeCoeffs coeffsRev.reverse }

private def ratOfInt (n : Int) : Rat := Rat.normalize n

private def ratRowScale (factor : Rat) (row : RatRow) : RatRow :=
  { coeffs := row.coeffs.map (fun q => factor * q), rhs := factor * row.rhs, sources := row.sources }

private def ratRowSub (row pivot : RatRow) (factor : Rat) : RatRow :=
  let coeffs := Id.run do
    if row.coeffs.size ≠ pivot.coeffs.size then
      panic! s!"ratRowSub: row/pivot size mismatch ({row.coeffs.size} ≠ {pivot.coeffs.size})"
    let mut out := Array.mkEmpty row.coeffs.size
    for i in List.range row.coeffs.size do
      out := out.push (row.coeffs[i]! - factor * pivot.coeffs[i]!)
    return out
  { coeffs, rhs := row.rhs - factor * pivot.rhs, sources := mergeStringLists row.sources pivot.sources }

private def swapRows (rows : Array RatRow) (i j : Nat) : Array RatRow :=
  if i == j then
    rows
  else
    let ri := rows[i]!
    let rj := rows[j]!
    (rows.set! i rj).set! j ri

private def findPivotRow? (rows : Array RatRow) (start col : Nat) : Option Nat :=
  (List.range rows.size).drop start |>.find? (fun i => rows[i]!.coeffs[col]! != 0)

private def rowIsZero (row : RatRow) : Bool :=
  row.coeffs.all (fun q => q == 0)

private def sameEquation (a b : RatRow) : Bool :=
  a.rhs == b.rhs && a.coeffs == b.coeffs

private def findEquivalentRow? (rows : Array RatRow) (target : RatRow) : Option Nat :=
  (List.range rows.size).find? (fun i => sameEquation rows[i]! target)

/-- Sorted-unique UID list insertion. Exposed (not `private`): `SizeInfer.inferAxisSizes` reuses
    this exact ordering primitive for Issue D's "purely negatively constrained axis" list, so that
    diagnostic's UID ordering is deterministic for the same reason `sortedVarsOfConstraints`
    below needs it to be. -/
def insertUIDSorted (acc : List UID) (u : UID) : List UID :=
  match acc with
  | [] => [u]
  | x :: xs =>
      if u == x then
        acc
      else if u < x then
        u :: acc
      else
        x :: insertUIDSorted xs u

private def sortedVarsOfConstraints (constraints : List SizeConstraint) : List UID :=
  constraints.foldl
    (fun acc constraint =>
      constraint.coeffs.foldl (fun acc' (_, u) => insertUIDSorted acc' u) acc)
    []

private def insertConstraintSorted (acc : List SizeConstraint) (constraint : SizeConstraint) : List SizeConstraint :=
  let key := s!"{constraint.source}|{constraint.rhs}|{repr constraint.coeffs}"
  match acc with
  | [] => [constraint]
  | hd :: tl =>
      let keyH := s!"{hd.source}|{hd.rhs}|{repr hd.coeffs}"
      if key < keyH then
        constraint :: acc
      else
        hd :: insertConstraintSorted tl constraint

private def sortConstraints (constraints : List SizeConstraint) : List SizeConstraint :=
  constraints.foldl (fun acc c => insertConstraintSorted acc c) []

/-- Solve a batch of upper-envelope size constraints to concrete UID sizes via exact-rational
    RREF, then floor-and-verify (padded/stride semantics: a non-divisible RREF solution is floored
    down and re-checked as an inequality against every original constraint, since the maximal
    valid index need not land exactly at `dim-1`). The sole solver entry point `SizeInfer` calls;
    the row-reduction machinery behind this deliberately small namespaced seam stays private. -/
def solveSizeConstraints (constraints : List SizeConstraint) :
    Except EvalError (HashMap UID Nat) := do
  let constraints := sortConstraints (constraints.map canonicalizeConstraint)
  let mlHints := mlHintsOfConstraints constraints
  let vars := sortedVarsOfConstraints constraints
  if vars.isEmpty then
    return {}
  let varIndex := Id.run do
    let mut idx : HashMap UID Nat := {}
    for i in List.range vars.length do
      idx := idx.insert vars[i]! i
    return idx
  let rows := Id.run do
    let mut out := Array.mkEmpty constraints.length
    for constraint in constraints do
      let mut coeffs := Array.replicate vars.length (0 : Rat)
      for (coef, u) in constraint.coeffs do
        let i := (varIndex[u]?).get!
        coeffs := coeffs.set! i (coeffs[i]! + ratOfInt coef)
      let row : RatRow := { coeffs, rhs := ratOfInt constraint.rhs, sources := [constraint.source] }
      match findEquivalentRow? out row with
      | some i =>
          let merged := { row with sources := mergeStringLists out[i]!.sources row.sources }
          out := out.set! i merged
      | none =>
          out := out.push row
    return out
  let mut matrix := rows
  let mut pivotRow := 0
  let mut pivots : Array (Nat × Nat) := #[]
  for col in List.range vars.length do
    if pivotRow < matrix.size then
      match findPivotRow? matrix pivotRow col with
      | none => pure ()
      | some found =>
          matrix := swapRows matrix pivotRow found
          let pivot := matrix[pivotRow]!
          let lead := pivot.coeffs[col]!
          let pivot := ratRowScale ((1 : Rat) / lead) pivot
          matrix := matrix.set! pivotRow pivot
          for row in List.range matrix.size do
            if row != pivotRow then
              let coeff := matrix[row]!.coeffs[col]!
              if coeff != 0 then
                matrix := matrix.set! row (ratRowSub matrix[row]! pivot coeff)
          pivots := pivots.push (pivotRow, col)
          pivotRow := pivotRow + 1
  for row in matrix do
    if rowIsZero row && row.rhs != 0 then
      throw (.shape (.solveFailure
        { kind := .inconsistent
        , detail? := some s!"reduced witness: 0 = {row.rhs}"
        , sourceRefs := row.sources
        , mlHints }))
  let pivotColSet := pivots.foldl (fun acc (_, col) => acc.insert col) ({} : HashSet Nat)
  let freeCols := (List.range vars.length).filter (fun i => !(pivotColSet.contains i))
  if !freeCols.isEmpty then
    let freeUids := freeCols.map (fun i => vars[i]!)
    let refs := freeUids.foldl (fun acc u => mergeStringLists acc (uidConstraintSources constraints u)) []
    throw (.shape (.solveFailure
      { kind := .underdetermined
      , unconstrained := freeUids
      , detail? := some (renderUnderdeterminedDetail constraints freeUids pivots.size vars.length)
      , sourceRefs := refs
      , mlHints }))
  -- Phase 1: floor all RREF solutions (padded semantics: non-divisible cases floor down)
  let mut solved : HashMap UID Nat := {}
  for (rowIdx, col) in pivots do
    let value := matrix[rowIdx]!.rhs
    let flooredNum : Int := Rat.num value / Int.ofNat (Rat.den value)
    if flooredNum <= 0 then
      let hints := insertStringSortedUnique mlHints "ml-hint: offset/window yields non-positive extent"
      throw (.shape (.solveFailure
        { kind := .nonPositive
        , offendingUid? := some vars[col]!
        , detail? := some s!"value={value}, reduced row={rowIdx}, col={col}"
        , sourceRefs := matrix[rowIdx]!.sources
        , mlHints := hints }))
    solved := solved.insert vars[col]! flooredNum.toNat
  -- Phase 2: verify floored solution satisfies all original constraints as inequalities
  for constraint in constraints do
    let lhs := constraint.coeffs.foldl
      (fun acc (coef, u) => acc + coef * Int.ofNat ((solved[u]?).get!)) 0
    if lhs > constraint.rhs then
      let hints := insertStringSortedUnique mlHints "ml-hint: output extent divisibility mismatch"
      throw (.shape (.solveFailure
        { kind := .nonIntegral
        , detail? := some s!"floored solution violates constraint: {lhs} > {constraint.rhs} ({constraint.source})"
        , sourceRefs := [constraint.source]
        , mlHints := hints }))
  return solved

end SizeSolve
end LeanNCD.Eval

import LeanNCD.DSL.Pipeline.Collect
import LeanNCD.Eval.Error

namespace LeanNCD.Eval

/-- Shape rule for newly enabled groups, after ordinary size inference. A boxed group (declared
    destination, every axis pinned) requires each writer's extent to fit the box; every other group
    keeps strict equality. Dimension indices are zero-based; writer indices are one-based schedule
    order. -/
def checkCollectorShapes (obligations : List CollectorShapeObligation)
    (sizes : Std.HashMap UID Nat) : Except ShapeError Unit := do
  for g in obligations do
    let expected ← g.basis.mapM fun sl =>
      match sl.outExtent (fun u => sizes[u]?) with
      | some n => pure n
      | none => throw (.unsizedScatterOutput sl)
    for (slots, k) in g.writers.zipIdx 1 do
      for (sl, dim) in slots.zipIdx do
        let actual ← match sl.outExtent (fun u => sizes[u]?) with
          | some n => pure n
          | none => throw (.unsizedScatterOutput sl)
        let want := expected[dim]?.getD 0
        if g.boxed then
          unless actual ≤ want do
            throw (.writerExtentExceedsBox g.name k dim want actual)
        else
          unless want == actual do
            throw (.writerExtentMismatch g.name k dim want actual)

/-- Private scratch names of boxed groups. Their scatter outputs may be shorter than the box. -/
def boxedScratchNames (obligations : List CollectorShapeObligation) : List String :=
  obligations.flatMap fun g =>
    if g.boxed then (List.range g.writers.length).map (collectorName g.name ∘ (· + 1)) else []

/-- Size inference sees a boxed group's scatter scratches as assignments, so a collector's bare read
    of a short scratch cannot raise the scatter-output `sizeConflict`. Their right-hand reads still
    size axes, as for scan-local scatters. -/
def sizingView (padded : List String) : Stmt → Stmt
  | .scatter nm slots rhs => if padded.contains nm then .assign nm slots rhs else .scatter nm slots rhs
  | s => s

end LeanNCD.Eval

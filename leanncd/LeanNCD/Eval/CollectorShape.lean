import LeanNCD.DSL.Pipeline.Collect
import LeanNCD.Eval.Error

namespace LeanNCD.Eval

/-- Strict S3 equality for newly enabled groups, after ordinary size inference.
    Dimension indices are zero-based; writer indices are one-based schedule order. -/
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
        unless want == actual do
          throw (.writerExtentMismatch g.name k dim want actual)

end LeanNCD.Eval

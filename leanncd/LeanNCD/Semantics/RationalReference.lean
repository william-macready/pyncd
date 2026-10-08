import LeanNCD.Semantics.ReferenceExecutor

namespace LeanNCD.Semantics.RationalReference

abbrev Carrier (_ : Unit) := ℚ

def ops : (s : Unit) → ScalarOps (Carrier s) :=
  fun _ => ⟨0, 1, (· + ·), (· * ·)⟩

/- This closed registry is the supported primitive profile. There is no
   translation of arbitrary backend operations or unsupported-op fallback. -/
inductive Primitive
  | reciprocal
  | square
  deriving DecidableEq, Repr

@[reducible] def registry : Registry Carrier where
  Op := Primitive
  arity := fun _ => 1
  input := fun _ _ => .scalar ()
  output := fun _ => .scalar ()
  domain
    | .reciprocal => fun xs => decide (xs 0 ≠ 0)
    | .square => fun _ => true
  meaning
    | .reciprocal => fun xs _ => (xs 0)⁻¹
    | .square => fun xs _ => (xs 0) * (xs 0)

end LeanNCD.Semantics.RationalReference

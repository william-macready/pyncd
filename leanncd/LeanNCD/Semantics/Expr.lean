import LeanNCD.Semantics.Types

namespace LeanNCD.Semantics

inductive Bin
  | add | mul

def ScalarOps.combine (ops : ScalarOps K) : Bin → K → K → K
  | .add => ops.add
  | .mul => ops.mul

/- Typed valuation spaces are not named syntax. Restrict Γ to a guard-admitted
   subtype before constructing reads; binders extend that space by products. -/
inductive Expr (K : S → Type) (σ : Declarations S) (r : Registry K) :
    Type → Ty S → Type 1
  | lit {Γ s} : K s → Expr K σ r Γ (.scalar s)
  | read {Γ} (t : σ.Tensor) :
      AdmittedRead (K (σ.signature t).sort) (σ.signature t).axes Γ →
      Expr K σ r Γ (.scalar (σ.signature t).sort)
  | iverson {Γ s} : (Γ → Bool) → Expr K σ r Γ (.scalar s)
  | binary {Γ s} : Bin → Expr K σ r Γ (.scalar s) →
      Expr K σ r Γ (.scalar s) → Expr K σ r Γ (.scalar s)
  | reduce {Γ s} (n : Nat) : Expr K σ r (Γ × Fin n) (.scalar s) →
      Expr K σ r Γ (.scalar s)
  | tab {Γ s} (sh : ArrayShape) (layout : Layout sh.axes) :
      Expr K σ r (Γ × Coord sh.axes) (.scalar s) → Expr K σ r Γ (.array s sh)
  | at {Γ s sh} : Expr K σ r Γ (.array s sh) →
      (Γ → Coord sh.axes) → Expr K σ r Γ (.scalar s)
  | prim {Γ} (f : r.Op) : ((i : Fin (r.arity f)) → Expr K σ r Γ (r.input f i)) →
      Expr K σ r Γ (r.output f)

end LeanNCD.Semantics

import LeanNCD.Semantics.Expr

namespace LeanNCD.Semantics

variable {S : Type} {K : S → Type} {σ : Declarations S} {r : Registry K}

def sequence : {n : Nat} → {A : Fin n → Type} →
    ((i : Fin n) → Option (A i)) → Option ((i : Fin n) → A i)
  | 0, _, _ => some (fun i => nomatch i)
  | _ + 1, _, f => do
      let x ← f 0
      let xs ← sequence (fun i => f i.succ)
      pure (Fin.cases x xs)

def foldValues {V : Type} (ops : ScalarOps V) : List (Option V) → Option V
  | [] => some ops.zero
  | x :: xs => do
      let a ← x
      let b ← foldValues ops xs
      pure (ops.add a b)

def footprint : {Γ : Type} → {τ : Ty S} → Expr K σ r Γ τ → Γ → List (Address σ)
  | _, _, .lit _, _ => []
  | _, _, .read t access, γ =>
      match access.resolved γ with
      | .at p => [⟨t, p⟩]
      | .const _ => []
  | _, _, .iverson _, _ => []
  | _, _, .binary _ l e, γ => footprint l γ ++ footprint e γ
  | _, _, .reduce n body, γ =>
      (List.finRange n).flatMap (fun i => footprint body (γ, i))
  | _, _, .tab _ layout body, γ =>
      (List.finRange layout.count).flatMap
        (fun i => footprint body (γ, layout.enumerate i))
  | _, _, .at e _, γ => footprint e γ
  | _, _, .prim f args, γ =>
      (List.finRange (r.arity f)).flatMap (fun i => footprint (args i) γ)

def evalWith (ops : (s : S) → ScalarOps (K s))
    (store : PartialStore K σ) :
    {Γ : Type} → {τ : Ty S} → Expr K σ r Γ τ → Γ → Option (Value K τ)
  | _, _, .lit x, _ => some x
  | _, _, .read t access, γ =>
      match access.resolved γ with
      | .at p => store ⟨t, p⟩
      | .const c => some c
  | _, _, .iverson q, γ => some (if q γ then (ops _).one else (ops _).zero)
  | _, _, .binary b l e, γ => do
      let x ← evalWith ops store l γ
      let y ← evalWith ops store e γ
      pure ((ops _).combine b x y)
  | _, _, .reduce n body, γ =>
      foldValues (ops _) ((List.finRange n).map (fun i => evalWith ops store body (γ, i)))
  | _, _, .tab _ layout body, γ => do
      let xs ← sequence (fun i => evalWith ops store body (γ, layout.enumerate i))
      pure (fun p => xs (layout.enumerate.symm p))
  | _, _, .at e index, γ => do
      let xs ← evalWith ops store e γ
      pure (xs (index γ))
  | _, _, .prim f args, γ => do
      let xs ← sequence (fun i => evalWith ops store (args i) γ)
      r.apply f xs

def interpret (ops : (s : S) → ScalarOps (K s)) (store : Store K σ)
    (e : Expr K σ r Γ τ) (γ : Γ) : Option (Value K τ) :=
  evalWith ops (fun a => some (store a)) e γ

end LeanNCD.Semantics

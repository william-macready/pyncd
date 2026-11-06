import IndexedComponentTransport

namespace IndexedComponentTransport
open LeanNCD.Semantics

def transport (f : Embedding src dst) :
    {Γ Δ : Type} → {τ : Ty Unit} → (Δ → Γ) → Expr K src R Γ τ → Expr K dst R Δ τ
  | _, _, _, _, .lit x => .lit x
  | _, _, _, h, .read t a => .read (f.tensor t) ((f.domain t).read h a)
  | _, _, _, h, .iverson q => .iverson (q ∘ h)
  | _, _, _, h, .binary b l r => .binary b (transport f h l) (transport f h r)
  | _, _, _, h, .reduce n body =>
      .reduce n (transport f (fun γ => (h γ.1, γ.2)) body)
  | _, _, _, h, .tab sh layout body =>
      .tab sh layout (transport f (fun γ => (h γ.1, γ.2)) body)
  | _, _, _, h, .at e index => .at (transport f h e) (index ∘ h)
  | _, _, _, h, .prim op args => .prim op (fun i => transport f h (args i))

theorem footprint_transport (f : Embedding src dst) (e : Expr K src R Γ τ)
    (h : Δ → Γ) (γ : Δ) :
    footprint (transport f h e) γ = (footprint e (h γ)).map f.address := by
  induction e generalizing Δ with
  | lit x => rfl
  | read t a =>
      cases hr : a.resolved (h γ) <;>
        simp [transport, footprint, Domain.read, mapResolved, Embedding.address, hr]
  | iverson q => rfl
  | binary b l r il ir => simp [transport, footprint, il, ir]
  | reduce n body ih =>
      simp only [transport, footprint, List.map_flatMap]
      congr 1
      funext i
      exact ih _ _
  | tab sh layout body ih =>
      simp only [transport, footprint, List.map_flatMap]
      congr 1
      funext i
      exact ih _ _
  | «at» e index ih => exact ih h γ
  | prim op args ih =>
      simp only [transport, footprint, List.map_flatMap]
      congr 1
      funext i
      exact ih i h γ

end IndexedComponentTransport

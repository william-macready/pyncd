import IndexedComponentTransportExpr

namespace IndexedComponentTransport
open LeanNCD.Semantics

theorem evalWith_transport (f : Embedding src dst) (s : PartialStore K dst)
    (e : Expr K src R Γ τ) (h : Δ → Γ) (γ : Δ) :
    evalWith RationalReference.ops s (transport f h e) γ =
      evalWith RationalReference.ops (f.pull s) e (h γ) := by
  induction e generalizing Δ with
  | lit x => rfl
  | read t a =>
      cases hr : a.resolved (h γ) <;>
        simp [transport, evalWith, Domain.read, mapResolved, Embedding.pull,
          Embedding.address, hr]
  | iverson q => rfl
  | binary b l r il ir => simp only [transport, evalWith, il h γ, ir h γ]
  | reduce n body ih =>
      simp only [transport, evalWith]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih _ _
  | tab sh layout body ih =>
      have hb : (fun i => evalWith RationalReference.ops s
          (transport f (fun γ => (h γ.1, γ.2)) body) (γ, layout.enumerate i)) =
          (fun i => evalWith RationalReference.ops (f.pull s) body (h γ, layout.enumerate i)) := by
        funext i
        exact ih _ _
      simp only [transport, evalWith, hb]
  | «at» e index ih => simp only [transport, evalWith, ih h γ, Function.comp_apply]
  | prim op args ih =>
      have hb : (fun i => evalWith RationalReference.ops s (transport f h (args i)) γ) =
          (fun i => evalWith RationalReference.ops (f.pull s) (args i) (h γ)) := by
        funext i
        exact ih i h γ
      simp only [transport, evalWith, hb]

theorem checkReads_map (f : Embedding src dst) (s : PartialStore K dst)
    (as : List (Address src)) :
    checkReads s (as.map f.address) = checkReads (f.pull s) as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, checkReads, Embedding.pull, ih]

theorem evalReady_transport (f : Embedding src dst) (s : PartialStore K dst)
    (e : Expr K src R Γ τ) (h : Δ → Γ) (γ : Δ) :
    evalReady RationalReference.ops s (transport f h e) γ =
      evalReady RationalReference.ops (f.pull s) e (h γ) := by
  simp only [evalReady, footprint_transport, checkReads_map, evalWith_transport]

theorem interpret_transport (f : Embedding src dst) (s : Store K dst)
    (e : Expr K src R Γ τ) (h : Δ → Γ) (γ : Δ) :
    interpret RationalReference.ops s (transport f h e) γ =
      interpret RationalReference.ops (f.pullComplete s) e (h γ) :=
  evalWith_transport f (fun a => some (s a)) e h γ

theorem evalWith_id (s : PartialStore K src) (e : Expr K src R Γ τ) (γ : Γ) :
    evalWith RationalReference.ops s (transport (Embedding.id src) id e) γ =
      evalWith RationalReference.ops s e γ := evalWith_transport _ _ _ _ _

theorem evalWith_comp (f : Embedding src mid) (g : Embedding mid dst)
    (s : PartialStore K dst) (e : Expr K src R Γ τ) (h : Δ → Γ) (k : Θ → Δ) (γ : Θ) :
    evalWith RationalReference.ops s (transport g k (transport f h e)) γ =
      evalWith RationalReference.ops s (transport (f.comp g) (h ∘ k) e) γ := by
  simp only [evalWith_transport, Embedding.pull_comp, Function.comp_apply]

theorem footprint_id (e : Expr K src R Γ τ) (γ : Γ) :
    footprint (transport (Embedding.id src) id e) γ = footprint e γ := by
  have ha : (Embedding.id src).address = id := by funext a; rfl
  rw [footprint_transport, ha]
  exact List.map_id _

theorem footprint_comp (f : Embedding src mid) (g : Embedding mid dst)
    (e : Expr K src R Γ τ) (h : Δ → Γ) (k : Θ → Δ) (γ : Θ) :
    footprint (transport g k (transport f h e)) γ =
      footprint (transport (f.comp g) (h ∘ k) e) γ := by
  simp only [footprint_transport, List.map_map, Embedding.address_comp, Function.comp_apply]
  rfl

#print axioms evalWith_transport
#print axioms footprint_transport
#print axioms evalReady_transport

end IndexedComponentTransport

import LeanNCD.Semantics.Plan.ScanHistory.Plan
import LeanNCD.Semantics.Completeness

namespace LeanNCD.Semantics.Program.Plan.ScanHistory

variable {V : Type} {d N : Nat} {r : Registry (Carrier V)}

def inputX {f : RegisteredF r d} (η : (program f N).Input) : State V d :=
  fun i => (η.val .X).get (η.property .X) (stateCoord i)

def inputZ {f : RegisteredF r d} (η : (program f N).Input) : State V d :=
  fun i => (η.val .Z).get (η.property .Z) (stateCoord i)

theorem input_reconstruct (f : RegisteredF r d) (N : Nat)
    (η : (program f N).Input) :
    η = input f N (inputX η) (inputZ η) := by
  apply Subtype.ext
  funext t
  cases t with
  | X =>
      change η.val .X = some (fun c : Coord (stateShape d).axes => inputX η c.1)
      calc
        η.val .X = some ((η.val .X).get (η.property .X)) := (Option.some_get _).symm
        _ = _ := by congr 1
  | Z =>
      change η.val .Z = some (fun c : Coord (stateShape d).axes => inputZ η c.1)
      calc
        η.val .Z = some ((η.val .Z).get (η.property .Z)) := (Option.some_get _).symm
        _ = _ := by congr 1
  | H =>
      have presence := η.property .H
      cases hh : η.val .H with
      | none => rfl
      | some h => simp [hh, isInput] at presence

theorem evalWith_cast_some {S : Type} {K : S → Type} {σ : Declarations S}
    {r : Registry K} {Γ : Type} {τ τ' : Ty S}
    (ops : (s : S) → ScalarOps (K s)) (p : PartialStore K σ)
    (h : τ = τ') (e : Expr K σ r Γ τ) (γ : Γ) (v : Value K τ)
    (he : evalWith ops p e γ = some v) :
    evalWith ops p (cast (congrArg (Expr K σ r Γ) h) e) γ =
      some (cast (congrArg (Value K) h) v) := by
  cases h
  exact he

theorem arrayExpr_output (f : RegisteredF r d) (x : State V d) :
    cast (congrArg (Value (Carrier V)) f.output_eq)
      (r.meaning f.op (f.arguments x) (f.total (f.arguments x))) =
        (fun p : Coord (stateShape d).axes => f.transition x p.1) := by
  funext ⟨i, u⟩
  cases u
  rfl

theorem arrayExpr_eval {Γ : Type} {σ : Declarations Unit}
    (f : RegisteredF r d) (ops : (s : Unit) → ScalarOps (Carrier V s))
    (p : PartialStore (Carrier V) σ)
    (arg : Expr (Carrier V) σ r Γ (stateTy d)) (γ : Γ) (x : State V d)
    (harg : evalWith ops p arg γ =
      some (fun c : Coord (stateShape d).axes => x c.1)) :
    evalWith ops p (f.arrayExpr arg) γ =
      some (fun c : Coord (stateShape d).axes => f.transition x c.1) := by
  have hargs (j : Fin (r.arity f.op)) :
      evalWith ops p
        (cast (congrArg (Expr (Carrier V) σ r Γ) (f.input_eq j).symm) arg) γ =
          some (f.arguments x j) :=
    evalWith_cast_some ops p (f.input_eq j).symm arg γ _ harg
  have hs := sequence_complete _ (f.arguments x) hargs
  have hp :
      evalWith ops p
        (.prim f.op (fun j =>
          cast (congrArg (Expr (Carrier V) σ r Γ) (f.input_eq j).symm) arg)) γ =
        some (r.meaning f.op (f.arguments x) (f.total (f.arguments x))) := by
    simp only [evalWith, hs]
    exact (registry_apply_some_iff _ _ _).mpr ⟨f.total _, rfl⟩
  rw [← arrayExpr_output f x]
  exact evalWith_cast_some ops p f.output_eq _ γ _ hp

theorem priorSlice_eval {Γ : Type}
    (ops : (s : Unit) → ScalarOps (Carrier V s))
    (p : PartialStore (Carrier V) (declarations d N))
    (l : Γ → Fin (N + 1)) (γ : Γ) (slice : State V d)
    (hpresent : ∀ j, p (historyAddress d N j (l γ)) = some (slice j)) :
    evalWith ops p (priorSlice (r := r) l) γ =
      some (fun c : Coord (stateShape d).axes => slice c.1) := by
  apply (tab_complete ops p (stateShape d) (stateLayout d) _ γ _).mpr
  intro c
  exact hpresent c.1

theorem recurrenceBody_eval {Γ : Type} (f : RegisteredF r d)
    (ops : (s : Unit) → ScalarOps (Carrier V s))
    (p : PartialStore (Carrier V) (declarations d N))
    (i : Γ → Fin d) (l : Γ → Fin (N + 1)) (γ : Γ) (slice : State V d)
    (hpresent : ∀ j, p (historyAddress d N j (l γ)) = some (slice j)) :
    evalWith ops p (recurrenceBody f i l) γ = some (f.transition slice (i γ)) := by
  have harray := arrayExpr_eval f ops p (priorSlice l) γ slice
    (priorSlice_eval ops p l γ slice hpresent)
  exact (at_some_iff ops p (stateShape d) _ _ γ _).mpr ⟨_, harray, rfl⟩

theorem priorSlice_interpret {Γ : Type}
    (ops : (s : Unit) → ScalarOps (Carrier V s))
    (ρ : Store (Carrier V) (declarations d N))
    (l : Γ → Fin (N + 1)) (γ : Γ) :
    interpret ops ρ (priorSlice (d := d) (r := r) l) γ =
      some (fun c : Coord (stateShape d).axes =>
        ρ (historyAddress d N c.1 (l γ))) :=
  priorSlice_eval ops (fun a => some (ρ a)) l γ
    (fun j => ρ (historyAddress d N j (l γ))) (fun _ => rfl)

theorem recurrenceBody_interpret {Γ : Type} (f : RegisteredF r d)
    (ops : (s : Unit) → ScalarOps (Carrier V s))
    (ρ : Store (Carrier V) (declarations d N))
    (i : Γ → Fin d) (l : Γ → Fin (N + 1)) (γ : Γ) :
    interpret ops ρ (recurrenceBody f i l) γ =
      some (f.transition (fun j => ρ (historyAddress d N j (l γ))) (i γ)) :=
  recurrenceBody_eval f ops (fun a => some (ρ a)) i l γ
    (fun j => ρ (historyAddress d N j (l γ))) (fun _ => rfl)

#print axioms input_reconstruct
#print axioms evalWith_cast_some
#print axioms arrayExpr_output
#print axioms arrayExpr_eval
#print axioms priorSlice_eval
#print axioms recurrenceBody_eval
#print axioms priorSlice_interpret
#print axioms recurrenceBody_interpret

end LeanNCD.Semantics.Program.Plan.ScanHistory

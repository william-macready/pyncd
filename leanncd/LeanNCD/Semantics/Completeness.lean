import LeanNCD.Semantics.Readiness
import Mathlib.Algebra.BigOperators.Fin

namespace LeanNCD.Semantics

variable {S : Type} {K : S → Type} {σ : Declarations S} {r : Registry K}
  {Γ : Type} {s : S}

theorem sequence_sound {n : Nat} {A : Fin n → Type}
    (f : (i : Fin n) → Option (A i)) (v : (i : Fin n) → A i)
    (h : sequence f = some v) : ∀ i, f i = some (v i) := by
  induction n with
  | zero => exact fun i => Fin.elim0 i
  | succ n ih =>
      cases h0 : f 0 with
      | none => simp [sequence, h0] at h
      | some x =>
          cases ht : sequence (fun i => f i.succ) with
          | none => simp [sequence, h0, ht] at h
          | some xs =>
              have hv : Fin.cases x xs = v := by simpa [sequence, h0, ht] using h
              subst v
              intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · exact h0
              · exact ih _ _ ht j

theorem sequence_complete {n : Nat} {A : Fin n → Type}
    (f : (i : Fin n) → Option (A i)) (v : (i : Fin n) → A i)
    (h : ∀ i, f i = some (v i)) : sequence f = some v := by
  induction n with
  | zero =>
      change some (fun i => nomatch i) = some v
      apply congrArg some
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      have ht := ih (fun i => f i.succ) (fun i => v i.succ) (fun i => h i.succ)
      simp only [sequence, h 0, ht]
      change some (Fin.cases (v 0) (fun i => v i.succ)) = some v
      apply congrArg some
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

theorem sequence_some_iff {n : Nat} {A : Fin n → Type}
    (f : (i : Fin n) → Option (A i)) (v : (i : Fin n) → A i) :
    sequence f = some v ↔ ∀ i, f i = some (v i) :=
  ⟨sequence_sound f v, sequence_complete f v⟩

theorem tab_complete (ops : (s : S) → ScalarOps (K s))
    (p : PartialStore K σ) (sh : ArrayShape) (layout : Layout sh.axes)
    (body : Expr K σ r (Γ × Coord sh.axes) (.scalar s)) (γ : Γ)
    (v : Coord sh.axes → K s) :
    evalWith ops p (.tab sh layout body) γ = some v ↔
      ∀ c, evalWith ops p body (γ, c) = some (v c) := by
  constructor
  · intro h
    cases ht : sequence (fun i => evalWith ops p body (γ, layout.enumerate i)) with
    | none => simp [evalWith, ht] at h
    | some xs =>
        have hv : (fun c => xs (layout.enumerate.symm c)) = v := by
          simpa [evalWith, ht] using h
        subst v
        intro c
        simpa using sequence_sound _ xs ht (layout.enumerate.symm c)
  · intro h
    have ht := sequence_complete
      (fun i => evalWith ops p body (γ, layout.enumerate i))
      (fun i => v (layout.enumerate i)) (fun i => h _)
    simp [evalWith, ht]

theorem foldValues_defined_iff {V : Type} (ops : ScalarOps V)
    (xs : List (Option V)) :
    (foldValues ops xs).isSome = true ↔ ∀ x ∈ xs, x.isSome = true := by
  induction xs with
  | nil => simp [foldValues]
  | cons x xs ih =>
      cases x <;> cases hf : foldValues ops xs <;> simp_all [foldValues]

theorem reduce_defined_iff (ops : (s : S) → ScalarOps (K s))
    (p : PartialStore K σ) (n : Nat)
    (body : Expr K σ r (Γ × Fin n) (.scalar s)) (γ : Γ) :
    (evalWith ops p (.reduce n body) γ).isSome = true ↔
      ∀ i, (evalWith ops p body (γ, i)).isSome = true := by
  simp [evalWith, foldValues_defined_iff]

theorem reduce_empty (ops : (s : S) → ScalarOps (K s))
    (p : PartialStore K σ)
    (body : Expr K σ r (Γ × Fin 0) (.scalar s)) (γ : Γ) :
    evalWith ops p (.reduce 0 body) γ = some (ops s).zero := by
  simp [evalWith, foldValues]

theorem foldValues_some_map_sum {V : Type} [AddCommMonoid V]
    (ops : ScalarOps V) (zero : ops.zero = 0) (add : ops.add = (· + ·))
    (xs : List V) :
    foldValues ops (xs.map some) = some xs.sum := by
  induction xs with
  | nil => simp [foldValues, zero]
  | cons x xs ih => simp [foldValues, ih, add]

/- Only the selected sort needs additive laws; ordered native-float folds
   and read stability require no algebraic instance. -/
theorem reduce_sum [AddCommMonoid (K s)]
    (ops : (s : S) → ScalarOps (K s)) (p : PartialStore K σ)
    (zero : (ops s).zero = 0) (add : (ops s).add = (· + ·))
    (n : Nat) (body : Expr K σ r (Γ × Fin n) (.scalar s)) (γ : Γ)
    (v : Fin n → K s) (body_values : ∀ i, evalWith ops p body (γ, i) = some (v i)) :
    evalWith ops p (.reduce n body) γ = some (∑ i, v i) := by
  calc
    evalWith ops p (.reduce n body) γ =
        foldValues (ops s) ((List.finRange n).map (fun i => some (v i))) := by
      simp only [evalWith, body_values]
    _ = some (((List.finRange n).map v).sum) := by
      simpa only [List.map_map] using
        foldValues_some_map_sum (ops s) zero add ((List.finRange n).map v)
    _ = some (∑ i, v i) := by rw [Fin.sum_univ_def]

theorem interpret_reduce_sum [AddCommMonoid (K s)]
    (ops : (s : S) → ScalarOps (K s)) (ρ : Store K σ)
    (zero : (ops s).zero = 0) (add : (ops s).add = (· + ·))
    (n : Nat) (body : Expr K σ r (Γ × Fin n) (.scalar s)) (γ : Γ)
    (v : Fin n → K s) (body_values : ∀ i, interpret ops ρ body (γ, i) = some (v i)) :
    interpret ops ρ (.reduce n body) γ = some (∑ i, v i) :=
  reduce_sum ops (fun a => some (ρ a)) zero add n body γ v body_values

theorem at_some_iff (ops : (s : S) → ScalarOps (K s))
    (p : PartialStore K σ) (sh : ArrayShape)
    (e : Expr K σ r Γ (.array s sh)) (index : Γ → Coord sh.axes)
    (γ : Γ) (v : K s) :
    evalWith ops p (.at e index) γ = some v ↔
      ∃ xs, evalWith ops p e γ = some xs ∧ xs (index γ) = v := by
  constructor
  · intro h
    cases he : evalWith ops p e γ with
    | none => simp [evalWith, he] at h
    | some xs => exact ⟨xs, rfl, by simpa [evalWith, he] using h⟩
  · rintro ⟨xs, he, hv⟩
    simp [evalWith, he, hv]

theorem registry_apply_some_iff (f : r.Op)
    (xs : (i : Fin (r.arity f)) → Value K (r.input f i))
    (v : Value K (r.output f)) :
    r.apply f xs = some v ↔
      ∃ h : r.domain f xs = true, r.meaning f xs h = v := by
  by_cases h : r.domain f xs = true <;> simp [Registry.apply, h]

theorem prim_some_iff (ops : (s : S) → ScalarOps (K s))
    (p : PartialStore K σ) (f : r.Op)
    (args : (i : Fin (r.arity f)) → Expr K σ r Γ (r.input f i))
    (γ : Γ) (v : Value K (r.output f)) :
    evalWith ops p (.prim f args) γ = some v ↔
      ∃ xs : (i : Fin (r.arity f)) → Value K (r.input f i),
        (∀ i, evalWith ops p (args i) γ = some (xs i)) ∧
          ∃ h : r.domain f xs = true, r.meaning f xs h = v := by
  constructor
  · intro h
    cases hs : sequence (fun i => evalWith ops p (args i) γ) with
    | none => simp [evalWith, hs] at h
    | some xs =>
        exact ⟨xs, sequence_sound _ xs hs,
          (registry_apply_some_iff f xs v).mp (by simpa [evalWith, hs] using h)⟩
  · rintro ⟨xs, hargs, hmeaning⟩
    have hs := sequence_complete (fun i => evalWith ops p (args i) γ) xs hargs
    simpa [evalWith, hs] using (registry_apply_some_iff f xs v).mpr hmeaning

/- The default supplies a mathematical extension, not an evaluator fallback. -/
theorem ready_complete_extension (ops : (s : S) → ScalarOps (K s))
    {τ : Ty S} (p : PartialStore K σ) (e : Expr K σ r Γ τ) (γ : Γ)
    (ready : Ready p e γ) :
    ∃ ρ : Store K σ,
      (∀ a x, p a = some x → ρ a = x) ∧
        ∀ a ∈ footprint e γ, p a = some (ρ a) := by
  let ρ : Store K σ := fun a => (p a).getD (ops (σ.signature a.1).sort).zero
  refine ⟨ρ, ?_, ?_⟩
  · intro a x hx
    simp [ρ, hx]
  · intro a ha
    cases hp : p a with
    | none =>
        have h := ready a ha
        simp [hp] at h
    | some x => simp [ρ, hp]

#print axioms sequence_some_iff
#print axioms tab_complete
#print axioms foldValues_defined_iff
#print axioms reduce_defined_iff
#print axioms reduce_empty
#print axioms foldValues_some_map_sum
#print axioms reduce_sum
#print axioms interpret_reduce_sum
#print axioms at_some_iff
#print axioms registry_apply_some_iff
#print axioms prim_some_iff
#print axioms ready_complete_extension

end LeanNCD.Semantics

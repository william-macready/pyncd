import IndexedComponentCompositionMatch
import LeanNCD.Semantics.Models

namespace IndexedComponentComposition

open LeanNCD.Semantics
open IndexedComponentTransport

variable {σA σB : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB)
variable (wire : Boundary A B)

theorem outcome_upstream (ρ : Store K (declarations A B))
    (t : A.program.Defined) (o : A.program.Occurrence t) :
    (program A B wire).outcome RationalReference.ops ρ
      (upstreamDefined A B wire t) o =
    A.program.outcome RationalReference.ops ((upstream A B).pullComplete ρ) t o := by
  unfold Program.outcome
  rw [upstream_body]
  exact interpret_transport _ _ _ id _

theorem outcome_downstream (ρ : Store K (declarations A B))
    (t : B.program.Defined) (o : B.program.Occurrence t) :
    (program A B wire).outcome RationalReference.ops ρ
      (downstreamDefined A B wire t) o =
    B.program.outcome RationalReference.ops ((downstream A B wire).pullComplete ρ) t o := by
  unfold Program.outcome
  rw [downstream_body]
  exact interpret_transport _ _ _ id _

theorem admEnv_components (ρ : Store K (declarations A B)) :
    (program A B wire).AdmEnv RationalReference.ops ρ ↔
      A.program.AdmEnv RationalReference.ops ((upstream A B).pullComplete ρ) ∧
      B.program.AdmEnv RationalReference.ops ((downstream A B wire).pullComplete ρ) := by
  constructor
  · intro h
    constructor
    · intro t o
      rw [← outcome_upstream A B wire ρ t o]
      exact h _ _
    · intro t o
      rw [← outcome_downstream A B wire ρ t o]
      exact h _ _
  · rintro ⟨ha, hb⟩ ⟨t, ht⟩ o
    cases t with
    | inl t =>
      exact (outcome_upstream A B wire ρ ⟨t, ht⟩ o) ▸ ha ⟨t, ht⟩ o
    | inr t =>
      exact (outcome_downstream A B wire ρ t o) ▸ hb t o

theorem collect_upstream (ρ : Store K (declarations A B))
    (h : (program A B wire).AdmEnv RationalReference.ops ρ)
    (ha : A.program.AdmEnv RationalReference.ops ((upstream A B).pullComplete ρ))
    (t : A.program.Defined) (p : Coord (σA.signature t.val).axes) :
    (program A B wire).collect RationalReference.ops ρ h
      (upstreamDefined A B wire t) p =
      A.program.collect RationalReference.ops ((upstream A B).pullComplete ρ) ha t p := by
  unfold Program.collect pushforward
  apply Finset.sum_congr rfl
  intro o _
  congr 1
  unfold Program.contribution
  simp only [outcome_upstream A B wire ρ t o]

theorem collect_downstream (ρ : Store K (declarations A B))
    (h : (program A B wire).AdmEnv RationalReference.ops ρ)
    (hb : B.program.AdmEnv RationalReference.ops ((downstream A B wire).pullComplete ρ))
    (t : B.program.Defined) (p : Coord (σB.signature t.val).axes) :
    (program A B wire).collect RationalReference.ops ρ h
      (downstreamDefined A B wire t) p =
      B.program.collect RationalReference.ops ((downstream A B wire).pullComplete ρ) hb t p := by
  unfold Program.collect pushforward
  apply Finset.sum_congr rfl
  intro o _
  congr 1
  unfold Program.contribution
  simp only [outcome_downstream A B wire ρ t o]

theorem equations_components (ρ : Store K (declarations A B))
    (h : (program A B wire).AdmEnv RationalReference.ops ρ)
    (ha : A.program.AdmEnv RationalReference.ops ((upstream A B).pullComplete ρ))
    (hb : B.program.AdmEnv RationalReference.ops ((downstream A B wire).pullComplete ρ)) :
    (∀ t p, ρ ⟨t.val, p⟩ =
      (program A B wire).collect RationalReference.ops ρ h t p) ↔
    (∀ t p, (upstream A B).pullComplete ρ ⟨t.val, p⟩ =
      A.program.collect RationalReference.ops ((upstream A B).pullComplete ρ) ha t p) ∧
    (∀ t p, (downstream A B wire).pullComplete ρ ⟨t.val, p⟩ =
      B.program.collect RationalReference.ops ((downstream A B wire).pullComplete ρ) hb t p) := by
  constructor
  · intro equations
    constructor
    · intro t p
      have eq := equations (upstreamDefined A B wire t) p
      rw [collect_upstream A B wire ρ h ha t p] at eq
      exact eq
    · intro t p
      change ρ ((downstream A B wire).address ⟨t.val, p⟩) = _
      rw [downstream_defined_address, ← collect_downstream A B wire ρ h hb t p]
      exact equations (downstreamDefined A B wire t) p
  · rintro ⟨ea, eb⟩ ⟨t, ht⟩ p
    cases t with
    | inl t =>
      change ρ ⟨.inl t, p⟩ = (program A B wire).collect RationalReference.ops ρ h
        (upstreamDefined A B wire ⟨t, ht⟩) p
      rw [collect_upstream A B wire ρ h ha ⟨t, ht⟩ p]
      exact ea ⟨t, ht⟩ p
    | inr t =>
      change ρ ⟨.inr t, p⟩ = (program A B wire).collect RationalReference.ops ρ h
        (downstreamDefined A B wire t) p
      rw [collect_downstream A B wire ρ h hb t p]
      have eq := eb t p
      change ρ ((downstream A B wire).address ⟨t.val, p⟩) = _ at eq
      rw [downstream_defined_address A B wire t p] at eq
      exact eq

end IndexedComponentComposition

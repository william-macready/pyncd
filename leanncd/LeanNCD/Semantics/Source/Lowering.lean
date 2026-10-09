import LeanNCD.Semantics.Source.Context
import Mathlib.Data.List.FinRange

namespace LeanNCD.Semantics.Source

instance coordFinite : (sh : Shape) → Fintype (Coord sh)
  | [] => inferInstance
  | _ :: sh => letI := coordFinite sh; inferInstance

instance coordEq (sh : Shape) : DecidableEq (Coord sh) := coordDecidableEq sh

variable {K : Type} [Semiring K] {σ : Declarations Unit}
  {r : Registry (fun _ : Unit => K)}

def semiringOps : (s : Unit) → ScalarOps K := fun _ => ⟨0, 1, (· + ·), (· * ·)⟩

structure Read (ctx : Shape) (σ : Declarations Unit) where
  tensor : σ.Tensor
  slots : Slots ctx (σ.signature tensor).axes

def readExpr (read : Read ctx σ) (env : Γ → Coord ctx) :
    Expr (fun _ => K) σ r Γ (.scalar ()) :=
  .read read.tensor
    ⟨strictPolicy _, fun γ => Coord.raw (read.slots.project (env γ)),
      fun γ => .at (read.slots.project (env γ)), fun _ => (strictPolicy _).inBounds _⟩

def product (reads : List (Read ctx σ)) (env : Γ → Coord ctx) :
    Expr (fun _ => K) σ r Γ (.scalar ()) :=
  match reads with
  | [] => .lit 1
  | read :: reads => .binary .mul (readExpr read env) (product reads env)

def operandProduct (ρ : Store (fun _ => K) σ) (reads : List (Read ctx σ))
    (v : Coord ctx) : K :=
  (reads.map (fun read => ρ ⟨read.tensor, read.slots.project v⟩)).prod

theorem interpret_product (ρ : Store (fun _ => K) σ) (reads : List (Read ctx σ))
    (env : Γ → Coord ctx) (γ : Γ) :
    interpret semiringOps ρ (product (r := r) reads env) γ =
      some (operandProduct ρ reads (env γ)) := by
  induction reads with
  | nil => rfl
  | cons read reads ih =>
    unfold interpret at ih
    simp [product, readExpr, interpret, evalWith, ScalarOps.combine,
      semiringOps, operandProduct, ih]

def contract (bound : Shape) (reads : List (Read ctx σ))
    (env : Γ → Coord bound → Coord ctx) : Expr (fun _ => K) σ r Γ (.scalar ()) :=
  match bound with
  | [] => product reads (fun γ => env γ ())
  | a :: rest =>
    .reduce a.extent (contract rest reads (fun γ p => env γ.1 (γ.2, p)))

theorem fold_some (xs : List K) :
    foldValues (semiringOps ()) (xs.map some) = some xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, foldValues, ih]
    rfl

theorem interpret_contract (ρ : Store (fun _ => K) σ) (bound : Shape)
    (reads : List (Read ctx σ)) (env : Γ → Coord bound → Coord ctx) (γ : Γ) :
    interpret semiringOps ρ (contract (r := r) bound reads env) γ =
      some (∑ p : Coord bound, operandProduct ρ reads (env γ p)) := by
  induction bound generalizing Γ with
  | nil => simpa [contract] using interpret_product (r := r) ρ reads (fun γ => env γ ()) γ
  | cons a rest ih =>
    simp only [contract, interpret, evalWith]
    change foldValues (semiringOps ())
      ((List.finRange a.extent).map (fun i =>
        interpret semiringOps ρ
          (contract rest reads (fun γ p => env γ.1 (γ.2, p))) (γ, i))) = _
    simp_rw [ih]
    have h := fold_some ((List.finRange a.extent).map (fun i =>
      ∑ x, operandProduct ρ reads (env γ (i, x))))
    simp only [List.map_map, Function.comp_def] at h
    rw [h]
    congr 1
    simpa [List.finRange, List.sum_ofFn] using
      (Fintype.sum_prod_type (fun p : Fin a.extent × Coord rest =>
        operandProduct ρ reads (env γ p))).symm

theorem interpret_contract_reindex (ρ : Store (fun _ => K) σ)
    (bound reordered : Shape) (e : Coord reordered ≃ Coord bound)
    (reads : List (Read ctx σ)) (env : Γ → Coord bound → Coord ctx) (γ : Γ) :
    interpret semiringOps ρ
      (contract (r := r) reordered reads (fun γ p => env γ (e p))) γ =
      interpret semiringOps ρ (contract (r := r) bound reads env) γ := by
  rw [interpret_contract, interpret_contract]
  congr 1
  exact Equiv.sum_comp e (fun p => operandProduct ρ reads (env γ p))

end LeanNCD.Semantics.Source

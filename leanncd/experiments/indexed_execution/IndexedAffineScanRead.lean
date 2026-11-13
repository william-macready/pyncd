import LeanNCD.Eval.Plan.Coordinates
import LeanNCD.Semantics.Source.Context
import LeanNCD.Semantics.Interpret

namespace IndexedExecutionExperiment.AffineScan

open LeanNCD.Semantics
open LeanNCD.Eval.Plan

/-- Structural evidence about the existing table, not a second affine representation. -/
structure ReadTable (sh : Shape) (width : Nat) where
  read : ReadPlan
  shape_eq : read.sourceShape.toList = sh.map Axis.extent
  coeff_rank : read.map.coeffs.size = sh.length
  bias_rank : read.map.bias.size = sh.length
  widths : ∀ row ∈ read.map.coeffs, row.size = width
  unary_none : read.unary = none
  no_bool_cast : read.boolToTropical = false
  no_real_cast : read.realToBool = false

def decodeRaw : (sh : Shape) → RawCoord sh → Option (Coord sh)
  | [], _ => some ()
  | a :: sh, raw =>
      if h : 0 ≤ raw 0 ∧ raw 0 < (a.extent : Int) then
        (decodeRaw sh (fun i => raw i.succ)).map
          (fun p => (⟨(raw 0).toNat, by omega⟩, p))
      else none

theorem decodeRaw_raw (sh : Shape) (p : Coord sh) :
    decodeRaw sh (Coord.raw p) = some p := by
  induction sh with
  | nil => cases p; rfl
  | cons a sh ih =>
      rcases p with ⟨i, p⟩
      simp [decodeRaw, Coord.raw, ih p]

theorem decodeRaw_sound (sh : Shape) (raw : RawCoord sh) (q : Coord sh)
    (inside : decodeRaw sh raw = some q) : Coord.raw q = raw := by
  induction sh with
  | nil => funext j; exact Fin.elim0 j
  | cons a sh ih =>
      simp only [decodeRaw] at inside
      split at inside
      · rename_i bound
        rcases Option.map_eq_some_iff.mp inside with ⟨tail, hd, he⟩
        cases he
        funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · dsimp [Coord.raw]
          omega
        · exact congrFun (ih _ tail hd) k
      · contradiction

def paddedResolve {K : Type} (zero : K) (sh : Shape) (raw : RawCoord sh) :
    Resolved K (Coord sh) :=
  match decodeRaw sh raw with
  | some p => .at p
  | none => .const zero

def zeroPolicy {K : Type} (zero : K) (sh : Shape) : ReadPolicy K sh where
  resolve := fun raw => (paddedResolve zero sh raw).outcome
  inBounds := by intro p; simp [paddedResolve, decodeRaw_raw, Resolved.outcome]

def ReadTable.raw (table : ReadTable sh width) (iter : List Int) : RawCoord sh :=
  fun i => (applyAffine table.read.map iter).getD i.val 0

theorem ReadTable.coordinate (table : ReadTable sh width) (iter : List Int)
    (i : Fin sh.length) :
    table.raw iter i = (applyAffine table.read.map iter).getD i.val 0 := rfl

theorem ReadTable.rank (table : ReadTable sh width) (iter : List Int) :
    (applyAffine table.read.map iter).length = sh.length := by
  simp [applyAffine, table.coeff_rank, table.bias_rank]

def ReadTable.admitted {K Γ : Type} (table : ReadTable sh width)
    (zero : K) (iter : Γ → List Int) : AdmittedRead K sh Γ where
  policy := zeroPolicy zero sh
  raw := fun γ => table.raw (iter γ)
  resolved := fun γ => paddedResolve zero sh (table.raw (iter γ))
  admission := fun _ => rfl

theorem ReadTable.padded {K Γ : Type} (table : ReadTable sh width)
    (zero : K) (iter : Γ → List Int) (γ : Γ)
    (out : decodeRaw sh (table.raw (iter γ)) = none) :
    (table.admitted zero iter).resolved γ = .const zero := by
  simp [admitted, paddedResolve, out]

theorem ReadTable.inBounds {K Γ : Type} (table : ReadTable sh width)
    (zero : K) (iter : Γ → List Int) (γ : Γ) (p : Coord sh)
    (inside : decodeRaw sh (table.raw (iter γ)) = some p) :
    (table.admitted zero iter).resolved γ = .at p := by
  simp [admitted, paddedResolve, inside]

end IndexedExecutionExperiment.AffineScan

import LeanNCD.Exec.Uid
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace LeanNCD.Semantics

structure Axis where
  uid : UID
  extent : Nat
  deriving DecidableEq, Repr

abbrev Shape := List Axis

@[reducible] def Coord : Shape → Type
  | [] => Unit
  | a :: sh => Fin a.extent × Coord sh

def RawCoord (sh : Shape) := Fin sh.length → Int

def Coord.raw : {sh : Shape} → Coord sh → RawCoord sh
  | [], _ => Fin.elim0
  | _ :: _, (i, p) => Fin.cases (Int.ofNat i.val) (Coord.raw p)

structure Layout (sh : Shape) where
  count : Nat
  enumerate : Fin count ≃ Coord sh

def canonicalLayout : (sh : Shape) → Layout sh
  | [] => ⟨1, { toFun := fun _ => (), invFun := fun _ => 0
                left_inv := fun i => Subsingleton.elim _ _
                right_inv := fun i => by cases i; rfl }⟩
  | a :: sh =>
      let tail := canonicalLayout sh
      ⟨a.extent * tail.count,
        finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) tail.enumerate)⟩

structure ArrayShape where
  axes : Shape
  nonempty : axes ≠ []

inductive Ty (S : Type)
  | scalar : S → Ty S
  | array : S → ArrayShape → Ty S

@[reducible] def Value (K : S → Type) : Ty S → Type
  | .scalar s => K s
  | .array s sh => Coord sh.axes → K s

structure ScalarOps (K : Type) where
  zero : K
  one : K
  add : K → K → K
  mul : K → K → K

structure Signature (S : Type) where
  sort : S
  axes : Shape

structure Declarations (S : Type) where
  Tensor : Type
  uid : Tensor → UID
  unique : Function.Injective uid
  signature : Tensor → Signature S

abbrev Address (σ : Declarations S) := (t : σ.Tensor) × Coord (σ.signature t).axes
abbrev Cell (K : S → Type) (σ : Declarations S) (a : Address σ) := K (σ.signature a.1).sort
abbrev Store (K : S → Type) (σ : Declarations S) := (a : Address σ) → Cell K σ a
abbrev PartialStore (K : S → Type) (σ : Declarations S) :=
  (a : Address σ) → Option (Cell K σ a)

inductive ReadOutcome (K C : Type)
  | at : C → ReadOutcome K C
  | const : K → ReadOutcome K C
  | reject : ReadOutcome K C

inductive Resolved (K C : Type)
  | at : C → Resolved K C
  | const : K → Resolved K C

def Resolved.outcome : Resolved K C → ReadOutcome K C
  | .at p => .at p
  | .const c => .const c

structure ReadPolicy (K : Type) (sh : Shape) where
  resolve : RawCoord sh → ReadOutcome K (Coord sh)
  inBounds : ∀ p, resolve (Coord.raw p) = .at p

structure AdmittedRead (K : Type) (sh : Shape) (Γ : Type) where
  policy : ReadPolicy K sh
  raw : Γ → RawCoord sh
  resolved : Γ → Resolved K (Coord sh)
  admission : ∀ γ, policy.resolve (raw γ) = (resolved γ).outcome

structure Registry (K : S → Type) where
  Op : Type
  arity : Op → Nat
  input : (f : Op) → Fin (arity f) → Ty S
  output : Op → Ty S
  domain : (f : Op) → ((i : Fin (arity f)) → Value K (input f i)) → Bool
  meaning : (f : Op) → (xs : (i : Fin (arity f)) → Value K (input f i)) →
    domain f xs = true → Value K (output f)

def Registry.apply (r : Registry K) (f : r.Op)
    (xs : (i : Fin (r.arity f)) → Value K (r.input f i)) : Option (Value K (r.output f)) :=
  if h : r.domain f xs = true then some (r.meaning f xs h) else none

end LeanNCD.Semantics

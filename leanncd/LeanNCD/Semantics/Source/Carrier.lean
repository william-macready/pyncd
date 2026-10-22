import LeanNCD.DSL.Ast
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Algebra.Order.Ring.Rat

/-! S2b: scalar carriers for the exact Source oracle.

The oracle's `+`, `*`, `0`, `1` come from `[Semiring K]`, the same instance the core leg
(`AdmittedSource.program`, `semiringOps`) uses, so the two legs cannot disagree on the algebra. A
carrier record adds only what the semiring does not know: which source aggregation it interprets
and how a finite rational input value embeds. -/

namespace LeanNCD.Semantics.Source.Oracle

open Tropical

/-- S2b: the one shared observation value: a finite rational or a signed infinity. Every
carrier maps into it (`Carrier.observe`); the profile and production comparison read only this. -/
inductive ExtVal
  | fin (q : ℚ)
  | negInf
  | posInf
  deriving DecidableEq

/-- Finite values print exactly as `ℚ` does, so a real rendering is byte-identical. -/
instance : Repr ExtVal where
  reprPrec
    | .fin q, p => reprPrec q p
    | .negInf, _ => "-inf"
    | .posInf, _ => "+inf"

/-- What the oracle needs from a scalar carrier beyond `[Semiring K]`. -/
structure Carrier (K : Type) where
  /-- Selection key: does this carrier interpret a program whose statements all aggregate with
  `agg` into destinations of element type `ty`? Read ONLY by `selectCarrier`: `runWith` never
  consults it, so any carrier can be run over any program, and `admitSourceSorted` is what ties a
  program to its carrier. The element type is part of the key because `agg` alone cannot separate a
  fourth carrier. -/
  admits : AggOp → TensorElementType → Bool
  /-- Embedding of a finite rational input value. -/
  ofRat : ℚ → K
  /-- The shared observation of a carrier value. -/
  observe : K → ExtVal

def Carrier.real : Carrier ℚ := ⟨fun a _ => a == .sum, id, .fin⟩

/-- Min-plus: `+` is `min`, `*` is `+`, `0` is `+∞`, `1` is `0`. -/
def MinPlus := Tropical (WithTop ℚ)

instance : CommSemiring MinPlus := inferInstanceAs (CommSemiring (Tropical (WithTop ℚ)))
instance : DecidableEq MinPlus := inferInstanceAs (DecidableEq (Tropical (WithTop ℚ)))
instance : Repr MinPlus where
  reprPrec x _ := match untrop (show Tropical (WithTop ℚ) from x) with
    | ⊤ => "+inf"
    | (q : ℚ) => repr q

def Carrier.minPlus : Carrier MinPlus :=
  ⟨fun a _ => a == .min, fun q => trop (q : WithTop ℚ),
    fun x => match untrop (show Tropical (WithTop ℚ) from x) with
      | ⊤ => .posInf
      | (q : ℚ) => .fin q⟩

/-- Mathlib's tropical semiring needs `LinearOrderedAddCommMonoidWithTop`; the order dual of
`WithBot ℚ` has every piece except the two absorbing/cancellation fields supplied here. Both fields
are proved (the second uses `WithBot.add_left_cancel`, i.e. ℚ is add-cancellative). This is a global,
unscoped instance on a Mathlib type; it is kept here because only `MaxPlus` needs it. -/
instance : LinearOrderedAddCommMonoidWithTop (WithBot ℚ)ᵒᵈ where
  top_add' x := WithBot.bot_add (OrderDual.ofDual x)
  isAddLeftRegular_of_ne_top {x} hx := by
    intro a b h
    exact WithBot.add_left_cancel (show OrderDual.ofDual x ≠ ⊥ from hx) h

/-- Max-plus: `+` is `max`, `*` is `+`, `0` is `-∞`, `1` is `0`. -/
def MaxPlus := Tropical (WithBot ℚ)ᵒᵈ

instance : CommSemiring MaxPlus := inferInstanceAs (CommSemiring (Tropical (WithBot ℚ)ᵒᵈ))
instance : DecidableEq MaxPlus := inferInstanceAs (DecidableEq (Tropical (WithBot ℚ)ᵒᵈ))
instance : Repr MaxPlus where
  reprPrec x _ := match OrderDual.ofDual (untrop (show Tropical (WithBot ℚ)ᵒᵈ from x)) with
    | ⊥ => "-inf"
    | (q : ℚ) => repr q

def Carrier.maxPlus : Carrier MaxPlus :=
  ⟨fun a _ => a == .max, fun q => trop (OrderDual.toDual (q : WithBot ℚ)),
    fun x => match OrderDual.ofDual (untrop (show Tropical (WithBot ℚ)ᵒᵈ from x)) with
      | ⊥ => .negInf
      | (q : ℚ) => .fin q⟩

/-- S2b: a carrier packaged with the instances every leg needs, so a selection result can be
passed around without fixing `K` in a type. -/
structure Sorted where
  K : Type
  [semiring : Semiring K]
  [decEq : DecidableEq K]
  [repr : Repr K]
  carrier : Carrier K
  /-- Display name for diagnostics. -/
  name : String

attribute [instance] Sorted.semiring Sorted.decEq Sorted.repr

/-- The selection table. First match wins; a fourth carrier is one more entry (callers may pass
an extended table), never an edit to the oracle. -/
def standardCarriers : List Sorted :=
  [⟨ℚ, Carrier.real, "real"⟩, ⟨MaxPlus, Carrier.maxPlus, "maxPlus"⟩,
    ⟨MinPlus, Carrier.minPlus, "minPlus"⟩]

/-- Why selection failed. -/
inductive SelectionError
  /-- Statements aggregate with different operations (a cross-sort program, out of S2b). -/
  | mixedSorts (aggs : List AggOp)
  /-- No carrier in the table admits this key. -/
  | noCarrier (agg : AggOp) (ty : TensorElementType)
  /-- Destinations of one program have different element types. -/
  | mixedElementTypes (tys : List TensorElementType)
  deriving DecidableEq, Repr

/-- Single-sort selection from per-statement `(agg, destination element type)` keys. An empty
program selects the first entry that admits `(sum, f64)`: `real` in `standardCarriers`, `noCarrier`
for a custom table without such an entry. -/
def selectCarrier (keys : List (AggOp × TensorElementType))
    (table : List Sorted := standardCarriers) : Except SelectionError Sorted :=
  let pick (agg : AggOp) (ty : TensorElementType) : Except SelectionError Sorted :=
    match table.find? (·.carrier.admits agg ty) with
    | some c => .ok c
    | none => .error (.noCarrier agg ty)
  match (keys.map (·.1)).eraseDups, (keys.map (·.2)).eraseDups with
  | [], _ => pick .sum .f64
  | [a], [t] => pick a t
  | [_], ts => .error (.mixedElementTypes ts)
  | as, _ => .error (.mixedSorts as)

end LeanNCD.Semantics.Source.Oracle

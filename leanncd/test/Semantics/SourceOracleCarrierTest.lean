import Semantics.SourceProgramFixtures
import LeanNCD.Semantics.Source.Observation

/-! S2b: the exact oracle evaluated over non-real carriers.

The programs below are `agg = sum` source (the unsorted admission entries refuse `max`/`min`); the
point here is that `Oracle.runWith` evaluates the SAME admitted program under a different semiring
with no change to the oracle's evaluation code.

Inputs: `X[a] = [1, 2, 3, 4]` (declaration 3), `W[b] = [1, 10, 100]` (declaration 4); `|a| = 4`,
`|b| = 3`; `Y` is declaration 5. -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceProgramFixtures

namespace SourceOracleCarrierTest

open Oracle

private def a : AxisSpec := ⟨"a", 7, .real⟩
private def b : AxisSpec := ⟨"b", 8, .real⟩
private def k : AxisSpec := ⟨"k", 9, .real⟩

private def rhs (terms : List (List Factor)) : RHSExpr :=
  ⟨⟨terms.map ProdTerm.mk⟩, .identity, .sum⟩

private def snap (kExtent : Nat) (yAxes : List AxisSpec) (stmts : List Stmt) : SourceSnapshot :=
  let extent (ax : AxisSpec) : Nat :=
    if ax.uid = 7 then 4 else if ax.uid = 8 then 3 else kExtent
  { resolved := {
      decls := [.axis a (some 4), .axis b (some 3), .axis k (some kExtent),
        .typedTensor .f64 "X" [a], .typedTensor .f64 "W" [b], .typedTensor .f64 "Y" yAxes]
      stmts := stmts
      env := {}, extNames := ∅ }
    specs := [⟨3, .input, [4]⟩, ⟨4, .input, [3]⟩, ⟨5, .output, yAxes.map extent⟩]
    inputs := [⟨3, [4], [1, 2, 3, 4]⟩, ⟨4, [3], [1, 10, 100]⟩] }

/-- `Y` values of the oracle run over carrier `C`, or `none` on any refusal. -/
private def yWith {K : Type} [Semiring K] (C : Carrier K) (s : SourceSnapshot) : Option (List K) :=
  match admitSourceAffine s with
  | .error _ => none
  | .ok admitted => match runWith C admitted (some [5]) with
    | .error _ => none
    | .ok r => (r.tensors.find? (·.declaration == 5)).map (·.values)

/-- `Y[a] := X[a] * W[b]`: a reduction over `b` of a two-factor product. -/
private def contraction : SourceSnapshot :=
  snap 7 [a] [.assign "Y" [.free a] (rhs [[.read "X" [.axis a], .read "W" [.axis b]]])]

/-- `Y[2*a] := X[a]`, `|k| = 7`: odd cells are empty fibers (the empty reduction). -/
private def strided : SourceSnapshot :=
  snap 7 [k] [.assign "Y" [.affine (.scale 2 a)] (rhs [[.read "X" [.axis a]]])]

/-! Real instance (hand: X[a] * 111). `run` is `runWith Carrier.real`; the existing oracle
fixtures (`SourceOracleTest`, `SourceOracleAffineTest`, ...) are the unchanged-behaviour check. -/
#guard yWith Carrier.real contraction == some [111, 222, 333, 444]
#guard yWith Carrier.real strided == some [1, 0, 2, 0, 3, 0, 4]

/-! Max-plus. Hand: X[a] + max W = X[a] + 100; strided odd cells are `-inf` (= `0`). -/
private def mx := Carrier.maxPlus.ofRat
#guard yWith Carrier.maxPlus contraction == some [mx 101, mx 102, mx 103, mx 104]
#guard yWith Carrier.maxPlus strided == some [mx 1, 0, mx 2, 0, mx 3, 0, mx 4]

/-! Min-plus. Hand: X[a] + min W = X[a] + 1; strided odd cells are `+inf` (= `0`). -/
private def mn := Carrier.minPlus.ofRat
#guard yWith Carrier.minPlus contraction == some [mn 2, mn 3, mn 4, mn 5]
#guard yWith Carrier.minPlus strided == some [mn 1, 0, mn 2, 0, mn 3, 0, mn 4]

/-- info: some [101, 102, 103, 104] -/
#guard_msgs in #eval yWith Carrier.maxPlus contraction
/-- info: some [1, -inf, 2, -inf, 3, -inf, 4] -/
#guard_msgs in #eval yWith Carrier.maxPlus strided
/-- info: some [1, +inf, 2, +inf, 3, +inf, 4] -/
#guard_msgs in #eval yWith Carrier.minPlus strided

/-! Extensibility check: a fourth carrier, the Boolean (or, and) semiring, defined HERE only
(test file), with hand-proved laws. Nothing in `Oracle.lean` or `Carrier.lean` changes. -/

/-- `true` iff some term is nonzero; `Bool`'s own Mathlib ring is XOR, hence a fresh type. -/
structure OrAnd where
  val : Bool
  deriving DecidableEq, Repr

instance : Zero OrAnd := ⟨⟨false⟩⟩
instance : One OrAnd := ⟨⟨true⟩⟩
instance : Add OrAnd := ⟨fun x y => ⟨x.val || y.val⟩⟩
instance : Mul OrAnd := ⟨fun x y => ⟨x.val && y.val⟩⟩

instance : CommSemiring OrAnd where
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  add_assoc := by rintro ⟨_|_⟩ ⟨_|_⟩ ⟨_|_⟩ <;> rfl
  zero_add := by rintro ⟨_|_⟩ <;> rfl
  add_zero := by rintro ⟨_|_⟩ <;> rfl
  add_comm := by rintro ⟨_|_⟩ ⟨_|_⟩ <;> rfl
  mul_assoc := by rintro ⟨_|_⟩ ⟨_|_⟩ ⟨_|_⟩ <;> rfl
  one_mul := by rintro ⟨_|_⟩ <;> rfl
  mul_one := by rintro ⟨_|_⟩ <;> rfl
  zero_mul := by rintro ⟨_|_⟩ <;> rfl
  mul_zero := by rintro ⟨_|_⟩ <;> rfl
  left_distrib := by rintro ⟨_|_⟩ ⟨_|_⟩ ⟨_|_⟩ <;> rfl
  right_distrib := by rintro ⟨_|_⟩ ⟨_|_⟩ ⟨_|_⟩ <;> rfl
  mul_comm := by rintro ⟨_|_⟩ ⟨_|_⟩ <;> rfl

/-- Keyed on `(max, f32)`: the element type, not the aggregation, separates it from max-plus. -/
private def Carrier.orAnd : Carrier OrAnd :=
  ⟨fun a ty => a == .max && ty == .f32, fun q => ⟨q != 0⟩,
    fun b => if b.val then .fin 1 else .fin 0⟩

/-! Hand: every `Y[a]` has a nonzero product; strided odd cells are empty, hence `false`. -/
#guard yWith Carrier.orAnd contraction == some [⟨true⟩, ⟨true⟩, ⟨true⟩, ⟨true⟩]
#guard yWith Carrier.orAnd strided ==
  some [⟨true⟩, ⟨false⟩, ⟨true⟩, ⟨false⟩, ⟨true⟩, ⟨false⟩, ⟨true⟩]

/-! S2b: selection-table extension. The toy is one more table entry keyed on `(max, f32)`; the
element type separates it from max-plus. No edit to `Carrier.lean`'s table or the oracle. -/
private def withToy : List Sorted := ⟨OrAnd, Carrier.orAnd, "orAnd"⟩ :: standardCarriers
private def pickName (keys : List (AggOp × TensorElementType)) (table : List Sorted) : String :=
  match selectCarrier keys table with
  | .ok S => S.name
  | .error e => toString (repr e)
#guard pickName [(.max, .f32)] withToy == "orAnd"
#guard pickName [(.max, .f64)] withToy == "maxPlus"
#guard pickName [(.max, .f32)] standardCarriers == "maxPlus"
#guard pickName [(.sum, .f64), (.min, .f64)] withToy ==
  toString (repr (SelectionError.mixedSorts [.sum, .min]))

/-! Audit rows (plan section 3, rows 3-5): the refusal and empty cases of `selectCarrier` that no
row above reaches. `mixedElementTypes` is a refusal on the sorted entry only; `noCarrier` needs a
custom table; an empty program is real. -/
#guard pickName [(.sum, .f64), (.sum, .f32)] standardCarriers ==
  toString (repr (SelectionError.mixedElementTypes [.f64, .f32]))
#guard pickName [(.sum, .f64)] [] == toString (repr (SelectionError.noCarrier .sum .f64))
#guard pickName [] standardCarriers == "real"

/-! Closing the T1 review gaps (parked findings F1-F3): `minPlus` and `real` selection, the `observe`
field of each carrier (nothing else in this file calls it), and the toy's `ofRat`, `observe` and
algebra, which the all-nonzero rows above cannot tell from a constant. -/
#guard pickName [(.min, .f64)] standardCarriers == "minPlus"
#guard pickName [(.sum, .f64)] standardCarriers == "real"
#guard Carrier.real.observe (3 / 2) == .fin (3 / 2)
#guard Carrier.maxPlus.observe (0 : MaxPlus) == .negInf
#guard Carrier.maxPlus.observe (1 : MaxPlus) == .fin 0
#guard Carrier.maxPlus.observe (Carrier.maxPlus.ofRat 5) == .fin 5
#guard Carrier.minPlus.observe (0 : MinPlus) == .posInf
#guard Carrier.minPlus.observe (1 : MinPlus) == .fin 0
#guard Carrier.minPlus.observe (Carrier.minPlus.ofRat 5) == .fin 5
#guard (Carrier.orAnd.ofRat 0).val == false
#guard (Carrier.orAnd.ofRat 3).val == true
#guard Carrier.orAnd.observe ⟨true⟩ == .fin 1
#guard Carrier.orAnd.observe ⟨false⟩ == .fin 0
#guard ((0 : OrAnd) + 1).val == true
#guard ((1 : OrAnd) * 0).val == false

/-! The toy carrier through the CORE leg (`runSourceAt`, `Registry.none`), selected by the extended
table. The destination `Y` is f32 and the aggregation `max`, so `withToy` picks `orAnd` (standard
tables would pick max-plus). Same hand values as the oracle rows above, read through the toy's own
`observe` (`true` is `fin 1`, `false` is `fin 0`). The third row zeroes two inputs, which only a
toy `ofRat` that really maps `0` to `false` can reproduce (the all-nonzero rows cannot tell it from
a constant). -/
private def toyCoreSnap (s : SourceSnapshot) : SourceSnapshot :=
  { s with resolved := { s.resolved with
      decls := s.resolved.decls.map fun
        | .typedTensor _ "Y" ax => .typedTensor .f32 "Y" ax
        | d => d
      stmts := s.resolved.stmts.map fun
        | .assign n sl r => .assign n sl { r with agg := .max }
        | st => st } }

private def toyCore (s : SourceSnapshot) : String :=
  match admitSourceSorted (toyCoreSnap s) withToy with
  | .error d => s!"refused {repr d.cause}"
  | .ok (source, S) =>
    match runSourceAt S.carrier source (Registry.none S.K) with
    | .error t => s!"input presence {t.val}"
    | .ok result => match result.result.outcome with
      | .complete c _ =>
        S.name ++ " " ++ toString (repr (((Debug.observeTensorsAt source (Registry.none S.K)
          S.carrier.observe c).find? (·.declaration == 5)).map (·.values)))
      | _ => "core leg incomplete"

#guard toyCore contraction == "orAnd some [some 1, some 1, some 1, some 1]"
#guard toyCore strided == "orAnd some [some 1, some 0, some 1, some 0, some 1, some 0, some 1]"
#guard toyCore { contraction with inputs := [⟨3, [4], [0, 2, 0, 4]⟩, ⟨4, [3], [1, 10, 100]⟩] } ==
  "orAnd some [some 0, some 1, some 0, some 1]"

end SourceOracleCarrierTest

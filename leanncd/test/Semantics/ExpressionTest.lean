import LeanNCD.Semantics

namespace LeanNCD.Semantics.Fixtures

inductive ScalarSort
  | rational | flag
  deriving DecidableEq

@[reducible] def Carrier : ScalarSort → Type
  | .rational => ℚ
  | .flag => Bool

def ops : (s : ScalarSort) → ScalarOps (Carrier s)
  | .rational => ⟨0, 1, (· + ·), (· * ·)⟩
  | .flag => ⟨false, true, (· || ·), (· && ·)⟩

@[reducible] def vectorShape : ArrayShape := ⟨[⟨41, 3⟩], by decide⟩
@[reducible] def emptyShape : ArrayShape := ⟨[⟨42, 0⟩], by decide⟩
@[reducible] def declarations : Declarations ScalarSort :=
  ⟨Unit, fun _ => 7, fun a b _ => by cases a; cases b; rfl,
    fun _ => ⟨.rational, vectorShape.axes⟩⟩

inductive Op
  | recip | nullary | mixed | rejectEmpty | identityArray

@[reducible] def registry : Registry Carrier where
  Op := Op
  arity
    | .recip | .rejectEmpty | .identityArray => 1
    | .nullary => 0
    | .mixed => 2
  input
    | .recip => fun _ => .scalar .rational
    | .nullary => Fin.elim0
    | .mixed => Fin.cases (.scalar .rational) (fun _ => .scalar .flag)
    | .rejectEmpty => fun _ => .array .rational emptyShape
    | .identityArray => fun _ => .array .rational vectorShape
  output
    | .identityArray => .array .rational vectorShape
    | _ => .scalar .rational
  domain
    | .recip => fun xs => decide (xs 0 ≠ 0)
    | .rejectEmpty => fun _ => false
    | _ => fun _ => true
  meaning
    | .recip => fun xs _ => (xs 0)⁻¹
    | .nullary => fun _ _ => 13
    | .mixed => fun xs _ => by
        have a : ℚ := by simpa using xs 0
        have b : Bool := by simpa using xs 1
        exact if b then a + 10 else a
    | .rejectEmpty => fun _ _ => 99
    | .identityArray => fun xs _ => xs 0

abbrev E (Γ : Type) (τ : Ty ScalarSort) := Expr Carrier declarations registry Γ τ
abbrev Scalar (Γ : Type) := E Γ (.scalar .rational)

def strictPolicy : ReadPolicy ℚ vectorShape.axes where
  resolve raw := if h : 0 ≤ raw 0 ∧ raw 0 < 3 then
    .at (⟨(raw 0).toNat, by change (raw 0).toNat < 3; omega⟩, ()) else .reject
  inBounds p := by
    rcases p with ⟨i, u⟩
    cases u
    simp [Coord.raw, vectorShape]

def constantPolicy : ReadPolicy ℚ vectorShape.axes where
  resolve raw := if h : 0 ≤ raw 0 ∧ raw 0 < 3 then
    .at (⟨(raw 0).toNat, by change (raw 0).toNat < 3; omega⟩, ()) else .const 9
  inBounds p := by
    rcases p with ⟨i, u⟩
    cases u
    simp [Coord.raw, vectorShape]

def wrapPolicy : ReadPolicy ℚ vectorShape.axes where
  resolve raw := .at (⟨(raw 0 % 3).toNat, by change (raw 0 % 3).toNat < 3; omega⟩, ())
  inBounds p := by
    rcases p with ⟨i, u⟩
    cases u
    simp [Coord.raw, vectorShape, Int.emod_eq_of_lt, i.isLt]

def point (i : Fin 3) : Coord vectorShape.axes := (i, ())

def direct {Γ : Type} (index : Γ → Fin 3) : Scalar Γ :=
  .read () ⟨strictPolicy, fun γ => Coord.raw (point (index γ)),
    fun γ => .at (point (index γ)), fun _ => strictPolicy.inBounds _⟩

def constRead : Scalar Unit :=
  .read () ⟨constantPolicy, fun _ _ => -1, fun _ => .const 9, by intro _; rfl⟩
def remapRead : Scalar Unit :=
  .read () ⟨wrapPolicy, fun _ _ => -1, fun _ => .at (point 2), by intro _; rfl⟩
def store : Store Carrier declarations := fun a => [2, 5, 7].get a.2.1
def partialStore : PartialStore Carrier declarations := fun a =>
  if a.2.1.val = 0 then some 2 else none

def bad {Γ : Type} : Scalar Γ := .prim (r := registry) Op.recip (fun _ => .lit 0)
def zeroStrict : Scalar Unit := .binary .mul (.lit 0) bad
def emptyReduction : Scalar Unit := .reduce 0 bad
def emptyTab : E Unit (.array .rational emptyShape) :=
  .tab emptyShape (canonicalLayout _) bad
def outsideEmpty : Scalar Unit := .prim (r := registry) Op.rejectEmpty (fun _ => emptyTab)
def nullary : Scalar Unit := .prim (r := registry) Op.nullary (fun i => nomatch i)
def heterogeneous : Scalar Unit := .prim (r := registry) Op.mixed (by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .lit 4
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact .lit true)
def strictArgument : Scalar Unit := .prim (r := registry) Op.mixed (by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact bad
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact .lit false)
def tabulated : E Unit (.array .rational vectorShape) :=
  .tab vectorShape (canonicalLayout _)
    (.binary .add (direct (fun γ => γ.2.1)) (.lit 1))
def selected : Scalar Unit := .at tabulated (fun _ => point 1)
def nonselectedUndefined : Scalar Unit :=
  .at (.tab vectorShape (canonicalLayout _)
    (.prim (r := registry) Op.recip (fun _ => .iverson (fun γ => γ.2.1.val == 0))))
    (fun _ => point 0)
def arrayPrimitive : Scalar Unit :=
  .at (.prim (r := registry) Op.identityArray (fun _ => tabulated)) (fun _ => point 2)

def nested : Scalar Unit :=
  .reduce 2 (.reduce 3
    (.binary .mul (direct (fun γ => γ.2))
      (.binary .add (.iverson (fun γ => γ.1.2.val == 1)) (.lit 1))))
def nestedSwapped : Scalar Unit :=
  .reduce 2 (.reduce 3
    (.binary .mul (direct (fun γ => ⟨γ.1.2.val, by omega⟩))
      (.binary .add (.iverson (fun γ => γ.2.val == 1)) (.lit 1))))

def scalarObservation (e : Scalar Unit) := interpret ops store e ()
def readyObservation (e : Scalar Unit) : String :=
  match evalReady ops partialStore e () with
  | .notReady => "notReady"
  | .evaluated none => "undefined"
  | .evaluated (some x) => toString x

#guard scalarObservation (direct (fun _ => 1)) == some 5
#guard scalarObservation constRead == some 9
#guard scalarObservation remapRead == some 7
#guard (footprint constRead ()).isEmpty
#guard (footprint remapRead ()).map (fun a => a.2.1.val) == [2]
#guard readyObservation remapRead == "notReady"
#guard readyObservation (direct (fun _ => 0)) == "2"
#guard scalarObservation zeroStrict == none
#guard readyObservation zeroStrict == "undefined"
#guard scalarObservation emptyReduction == some 0
#guard (interpret ops store emptyTab ()).isSome
#guard (footprint emptyTab ()).isEmpty
#guard scalarObservation outsideEmpty == none
#guard scalarObservation nullary == some 13
#guard scalarObservation heterogeneous == some 14
#guard scalarObservation strictArgument == none
#guard scalarObservation selected == some 6
#guard scalarObservation arrayPrimitive == some 8
#guard scalarObservation nonselectedUndefined == none
#guard readyObservation selected == "notReady"
#guard (footprint tabulated ()).map (fun a => a.2.1.val) == [0, 1, 2]
#guard scalarObservation nested == some 42
#guard scalarObservation nestedSwapped == some 28

#eval [scalarObservation constRead, scalarObservation remapRead,
  scalarObservation zeroStrict, scalarObservation emptyReduction,
  scalarObservation outsideEmpty, scalarObservation nullary,
  scalarObservation heterogeneous, scalarObservation selected,
  scalarObservation nonselectedUndefined, scalarObservation nested,
  scalarObservation nestedSwapped]
#eval [readyObservation remapRead, readyObservation zeroStrict, readyObservation selected]

end LeanNCD.Semantics.Fixtures

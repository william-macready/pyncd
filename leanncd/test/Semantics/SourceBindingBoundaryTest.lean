import LeanNCD.Semantics.Source

namespace LeanNCD.Semantics.Source.BindingBoundaryFixtures

def matrixContext : Context := ⟨[⟨10, 2⟩, ⟨11, 2⟩], by decide⟩
def renamedContext : Context := ⟨[⟨19, 2⟩, ⟨23, 2⟩], by decide⟩

def matrixValuation : UIDVal matrixContext :=
  (uidCoordEquiv matrixContext).symm (⟨1, by decide⟩, ⟨0, by decide⟩, ())

def renamedValuation : UIDVal renamedContext :=
  (uidCoordEquiv renamedContext).symm (⟨1, by decide⟩, ⟨0, by decide⟩, ())

private def values (c : Context) (v : UIDVal c) : List Nat :=
  (List.finRange c.axes.length).map (fun i => (uidPositionalEquiv c v i).val)

private def mappedUIDs (m : IndexMap src dst) : List UID :=
  (List.finRange src.axes.length).map (fun i => (m.map (src.uidEquiv i)).val)

-- Donor M's matrixStore makes the two equal-domain UID assignments distinguishable.
def matrixValue (v : UIDVal matrixContext) : Nat :=
  let p := uidCoordEquiv matrixContext v
  1 + 10 * p.1.val + p.2.1.val

def repeatedSlots : Slots matrixContext.axes [⟨10, 2⟩, ⟨10, 2⟩] :=
  .cons .here (.cons .here .nil)

def v7 : Except Diagnostic (List (String × List Nat)) := do
  let swap ← resolveIndexMap matrixContext matrixContext
    (fun u => if u = 10 then 11 else 10)
  let rename ← resolveIndexMap matrixContext renamedContext
    (fun u => if u = 10 then 19 else 23)
  let repeated ← resolveIndexMap matrixContext matrixContext (fun _ => 11)
  let pulled := indexPullback swap matrixValuation
  let slots := repeatedSlots.project (uidCoordEquiv matrixContext pulled)
  pure [
    ("source-uids", matrixContext.axes.map Axis.uid),
    ("target-uids", mappedUIDs swap),
    ("before", values matrixContext matrixValuation),
    ("pulled", values matrixContext pulled),
    ("matrix-before-after", [matrixValue matrixValuation, matrixValue pulled]),
    ("composed-uids", mappedUIDs (swap.comp rename)),
    ("composed", values matrixContext (indexPullback (swap.comp rename) renamedValuation)),
    ("sequential", values matrixContext (indexPullback swap
      (indexPullback rename renamedValuation))),
    ("repeated-uids", mappedUIDs repeated),
    ("repeated-pullback", values matrixContext (indexPullback repeated matrixValuation)),
    ("repeated-slots", [slots.1.val, slots.2.1.val])]

#guard v7 = .ok [
  ("source-uids", [10, 11]),
  ("target-uids", [11, 10]),
  ("before", [1, 0]),
  ("pulled", [0, 1]),
  ("matrix-before-after", [11, 2]),
  ("composed-uids", [23, 19]),
  ("composed", [0, 1]),
  ("sequential", [0, 1]),
  ("repeated-uids", [11, 11]),
  ("repeated-pullback", [0, 0]),
  ("repeated-slots", [0, 0])]

#eval v7

theorem v7_lookup (m : IndexMap matrixContext matrixContext) (u : matrixContext.Key) :
    (indexPullback m matrixValuation u).val = (matrixValuation (m.map u)).val :=
  indexPullback_lookup m matrixValuation u

theorem v7_comp (m : IndexMap matrixContext matrixContext)
    (n : IndexMap matrixContext renamedContext) :
    indexPullback (m.comp n) renamedValuation =
      indexPullback m (indexPullback n renamedValuation) :=
  indexPullback_comp m n renamedValuation

theorem v7_repeated (m : IndexMap matrixContext matrixContext)
    (u w : matrixContext.Key) (h : m.map u = m.map w) :
    (indexPullback m matrixValuation u).val = (indexPullback m matrixValuation w).val :=
  indexPullback_repeated m matrixValuation u w h

-- Donors S/E: rank zero is a singleton; the matrix tail with extent zero is empty.
def emptyContext : Context := ⟨[], by decide⟩
def zeroContext : Context := ⟨[⟨10, 2⟩, ⟨12, 0⟩], by decide⟩

def emptyValuation : UIDVal emptyContext := (uidCoordEquiv emptyContext).symm ()

private def enumeratedValues (c : Context) : List (List Nat) :=
  (List.finRange (canonicalLayout c.axes).count).map (fun i =>
    values c ((uidCoordEquiv c).symm ((canonicalLayout c.axes).enumerate i)))

def v8 : Nat × Nat × List (List Nat) × List (List Nat) :=
  ((canonicalLayout emptyContext.axes).count, (canonicalLayout zeroContext.axes).count,
    enumeratedValues emptyContext, enumeratedValues zeroContext)

#guard v8 = (1, 0, [[]], [])
#eval v8

theorem v8_empty_roundtrip : uidCoordEquiv emptyContext emptyValuation = () :=
  uidCoordEquiv_right emptyContext ()

theorem v8_empty_uid_unique (v : UIDVal emptyContext) : v = emptyValuation := by
  funext u
  have h := u.property
  simp [emptyContext] at h

theorem v8_empty_coord_unique (p : Coord emptyContext.axes) : p = () := by
  cases p
  rfl

theorem v8_empty_uid_exactly_one : ∃! _v : UIDVal emptyContext, True :=
  ⟨emptyValuation, trivial, fun v _ => v8_empty_uid_unique v⟩

theorem v8_empty_coord_exactly_one : ∃! _p : Coord emptyContext.axes, True :=
  ⟨(), trivial, fun p _ => v8_empty_coord_unique p⟩

theorem v8_zero_uid_none : ¬ Nonempty (UIDVal zeroContext) := by
  rintro ⟨v⟩
  have impossible : Fin 0 := v.lookupRef (.there .here)
  exact Fin.elim0 impossible

theorem v8_zero_coord_none : ¬ Nonempty (Coord zeroContext.axes) := by
  rintro ⟨p⟩
  exact Fin.elim0 p.2.1

theorem v8_empty_left (v : UIDVal emptyContext) :
    (uidCoordEquiv emptyContext).symm (uidCoordEquiv emptyContext v) = v :=
  uidCoordEquiv_left emptyContext v

theorem v8_empty_right (p : Coord emptyContext.axes) :
    uidCoordEquiv emptyContext ((uidCoordEquiv emptyContext).symm p) = p :=
  uidCoordEquiv_right emptyContext p

theorem v8_zero_left (v : UIDVal zeroContext) :
    (uidCoordEquiv zeroContext).symm (uidCoordEquiv zeroContext v) = v :=
  uidCoordEquiv_left zeroContext v

theorem v8_zero_right (p : Coord zeroContext.axes) :
    uidCoordEquiv zeroContext ((uidCoordEquiv zeroContext).symm p) = p :=
  uidCoordEquiv_right zeroContext p

#print axioms v7_lookup
#print axioms v7_comp
#print axioms v7_repeated
#print axioms v8_empty_roundtrip
#print axioms v8_empty_uid_exactly_one
#print axioms v8_empty_coord_exactly_one
#print axioms v8_zero_uid_none
#print axioms v8_zero_coord_none
#print axioms v8_empty_left
#print axioms v8_empty_right
#print axioms v8_zero_left
#print axioms v8_zero_right

end LeanNCD.Semantics.Source.BindingBoundaryFixtures

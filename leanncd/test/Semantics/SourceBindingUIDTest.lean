import LeanNCD.Semantics.Source

namespace LeanNCD.Semantics.Source.BindingUIDFixtures

@[reducible] def i : Axis := ⟨10, 2⟩
@[reducible] def j : Axis := ⟨11, 2⟩

def sameName : List UData := [⟨10, some "i"⟩, ⟨11, some "i"⟩]

def sameExtent : Context := ⟨[i, j], by decide⟩

def skewedAssignment : UIDVal sameExtent := fun u =>
  if h : u.val = 10 then
    ⟨1, by
      rw [sameExtent.domain_of_mem u i (by decide) h.symm]
      decide⟩
  else
    ⟨0, by
      have hu : u.val = 11 := by
        have hm := u.property
        simp [sameExtent, i, j] at hm
        exact hm.resolve_left h
      rw [sameExtent.domain_of_mem u j (by decide) hu.symm]
      decide⟩

def firstRef : Ref sameExtent.axes 2 := .here
def secondRef : Ref sameExtent.axes 2 := .there .here

def slotValues (c : Context) (sh : Shape) (uids : List UID) (v : UIDVal c) :
    Except Diagnostic (Coord sh) := do
  let slots ← resolveSlots c.axes sh uids
  pure (slots.project (uidCoordEquiv c v))

def matrixStore (p : Coord [i, j]) : Nat :=
  1 + 10 * p.1.val + p.2.1.val

def matrixRead (uids : List UID) : Except Diagnostic Nat := do
  pure (matrixStore (← slotValues sameExtent [i, j] uids skewedAssignment))

namespace V1

#guard sameName.map UData.name = [some "i", some "i"]
#guard sameName.map UData.uid = [10, 11]
#guard i.extent = j.extent
#guard i.uid ≠ j.uid

def directUIDValues : Nat × Nat :=
  ((skewedAssignment ⟨10, by decide⟩).val,
    (skewedAssignment ⟨11, by decide⟩).val)

def referenceValues : Nat × Nat :=
  ((skewedAssignment.lookupRef firstRef).val,
    (skewedAssignment.lookupRef secondRef).val)

def distinctSlots := slotValues sameExtent [i, j] [10, 11] skewedAssignment
def reversedSlots := slotValues sameExtent [i, j] [11, 10] skewedAssignment
def distinctRead := matrixRead [10, 11]
def reversedRead := matrixRead [11, 10]

#guard directUIDValues = (1, 0)
#guard referenceValues = (1, 0)
#guard referenceValues.1 ≠ referenceValues.2
#guard distinctSlots = .ok (1, 0, ())
#guard reversedSlots = .ok (0, 1, ())
#guard distinctRead = .ok 11
#guard reversedRead = .ok 2
#guard distinctRead ≠ matrixRead [10, 10]
#guard distinctRead ≠ matrixRead [11, 11]

theorem first_lookup :
    firstRef.get (uidCoordEquiv sameExtent skewedAssignment) =
      skewedAssignment.lookupRef firstRef :=
  Ref.get_uidCoordEquiv sameExtent firstRef skewedAssignment

theorem second_lookup :
    secondRef.get (uidCoordEquiv sameExtent skewedAssignment) =
      skewedAssignment.lookupRef secondRef :=
  Ref.get_uidCoordEquiv sameExtent secondRef skewedAssignment

#eval ("V1 UID/reference values and matrix reads",
  directUIDValues, referenceValues, distinctRead, reversedRead)

end V1

namespace V2

def repeatedFirst := slotValues sameExtent [i, j] [10, 10] skewedAssignment
def repeatedSecond := slotValues sameExtent [i, j] [11, 11] skewedAssignment
def diagonalFirst := matrixRead [10, 10]
def diagonalSecond := matrixRead [11, 11]

#guard repeatedFirst = .ok (1, 1, ())
#guard repeatedSecond = .ok (0, 0, ())
#guard diagonalFirst = .ok 12
#guard diagonalSecond = .ok 1

theorem shared_assignment (v : UIDVal sameExtent)
    (r s : Ref sameExtent.axes 2) (h : r.uid = s.uid) :
    (v.lookupRef r).val = (v.lookupRef s).val :=
  Ref.sameUID_lookup sameExtent r s v h

#eval ("V2 repeated UID matrix reads", diagonalFirst, diagonalSecond)

end V2

namespace V3

def original : Context := ⟨[⟨7, 2⟩, ⟨3, 4⟩], by decide⟩
def permutation : original.axes.Perm [⟨3, 4⟩, ⟨7, 2⟩] := List.Perm.swap ..
def reversed : Context := original.reenumerate _ permutation
def transport : UIDTransport original reversed := original.reenumerateTransport _ permutation

def coordinate : Coord original.axes := (1, 2, ())
def reversedCoordinate : Coord reversed.axes := (2, 1, ())
def valuation : UIDVal original := (uidCoordEquiv original).symm coordinate
def transported : UIDVal reversed := transport.valuationEquiv valuation
def independentReversed : UIDVal reversed :=
  (uidCoordEquiv reversed).symm reversedCoordinate

def originalUIDValues : Nat × Nat :=
  ((valuation ⟨7, by decide⟩).val, (valuation ⟨3, by decide⟩).val)
def reversedUIDValues : Nat × Nat :=
  ((transported ⟨7, by decide⟩).val, (transported ⟨3, by decide⟩).val)
def transportedValues : Nat × Nat :=
  let p := uidCoordEquiv reversed transported
  (p.1.val, p.2.1.val)
def inverseTransportValues : Nat × Nat :=
  let p := uidCoordEquiv original (transport.valuationEquiv.symm independentReversed)
  (p.1.val, p.2.1.val)

#guard original.axes.map Axis.extent = [2, 4]
#guard reversed.axes.map Axis.extent = [4, 2]
#guard originalUIDValues = (1, 2)
#guard reversedUIDValues = (1, 2)
#guard transportedValues = (2, 1)
#guard inverseTransportValues = (1, 2)
#guard @Eq (Fin 2 × Fin 4 × Unit) (uidCoordEquiv original valuation) coordinate
#guard @Eq (Fin 4 × Fin 2 × Unit) (uidCoordEquiv reversed transported) reversedCoordinate
#guard (valuation.lookupRef (Ref.there Ref.here)).val = 2
#guard (transported.lookupRef Ref.here).val = 2
#guard (transported.lookupRef (Ref.there Ref.here)).val = 1

theorem original_coord_left (v : UIDVal original) :
    (uidCoordEquiv original).symm (uidCoordEquiv original v) = v :=
  uidCoordEquiv_left original v

theorem original_coord_right (p : Coord original.axes) :
    uidCoordEquiv original ((uidCoordEquiv original).symm p) = p :=
  uidCoordEquiv_right original p

theorem reversed_coord_left (v : UIDVal reversed) :
    (uidCoordEquiv reversed).symm (uidCoordEquiv reversed v) = v :=
  uidCoordEquiv_left reversed v

theorem reversed_coord_right (p : Coord reversed.axes) :
    uidCoordEquiv reversed ((uidCoordEquiv reversed).symm p) = p :=
  uidCoordEquiv_right reversed p

theorem transport_left (v : UIDVal original) :
    transport.valuationEquiv.symm (transport.valuationEquiv v) = v :=
  transport.valuationEquiv.symm_apply_apply v

theorem transport_right (v : UIDVal reversed) :
    transport.valuationEquiv (transport.valuationEquiv.symm v) = v :=
  transport.valuationEquiv.apply_symm_apply v

#eval ("V3 UID values, forward and inverse Coord transport",
  originalUIDValues, reversedUIDValues, transportedValues, inverseTransportValues)

end V3

#print axioms V1.first_lookup
#print axioms V1.second_lookup
#print axioms V2.shared_assignment
#print axioms V3.original_coord_left
#print axioms V3.original_coord_right
#print axioms V3.reversed_coord_left
#print axioms V3.reversed_coord_right
#print axioms V3.transport_left
#print axioms V3.transport_right
#print axioms Context.reenumerateTransport

end LeanNCD.Semantics.Source.BindingUIDFixtures

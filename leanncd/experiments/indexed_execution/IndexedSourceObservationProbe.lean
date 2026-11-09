import IndexedSourceWire
import IndexedWitnessObservationProbe

namespace IndexedSourceObservationProbe
open IndexedSource IndexedWitness LeanNCD.Semantics

def boundaryCopy {X Y : Object} (a : Wire X Y) : X.interface.Env ≃ Y.interface.Env :=
  (Equiv.piCongrLeft' (fun t : X.interface.Tensor =>
    Coord (X.interface.signature t).axes → ℚ) a.ports.symm).trans
    (Equiv.piCongrRight (fun t =>
      Equiv.arrowCongr (a.domain t).coord.symm (Equiv.refl ℚ)))

def inputCopy {X Y : Object} (a : Wire X Y) : X.interface.Env ≃ Y.interface.Env :=
  (Equiv.piCongrLeft' (fun t : X.interface.Tensor =>
    Coord (X.interface.signature t).axes → ℚ) a.ports.symm).trans
    (Equiv.piCongrRight (fun t =>
      Equiv.arrowCongr (a.domain t).coord.symm (Equiv.refl ℚ)))

def outputCopy {X Y : Object} (a : Wire X Y) : X.interface.Env ≃ Y.interface.Env :=
  (Equiv.piCongrLeft' (fun t : X.interface.Tensor =>
    Coord (X.interface.signature t).axes → ℚ) a.ports.symm).trans
    (Equiv.piCongrRight (fun t =>
      Equiv.arrowCongr (a.domain t).coord.symm (Equiv.refl ℚ)))

def inverseCopy {X Y : Object} (a : Wire X Y) : Y.interface.Env ≃ X.interface.Env :=
  (boundaryCopy a).symm

end IndexedSourceObservationProbe

import IndexedSourceObservationProbe
import Semantics.AxiomAudit

namespace IndexedSourceObservationParity
open IndexedSource IndexedSourceObservationProbe
theorem boundary {X Y : Object} (a : Wire X Y) : boundaryCopy a = a.env := rfl
theorem input {X Y : Object} (a : Wire X Y) : inputCopy a = a.env := rfl
theorem output {X Y : Object} (a : Wire X Y) : outputCopy a = a.env := rfl
theorem inverse {X Y : Object} (a : Wire X Y) : inverseCopy a = a.inverse.env :=
  (Wire.env_inverse a).symm
#audit_axioms IndexedSourceObservationParity
end IndexedSourceObservationParity

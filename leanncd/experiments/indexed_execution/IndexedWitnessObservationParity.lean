import IndexedWitnessObservationProbe
import Semantics.AxiomAudit

-- Baseline generic parity ONLY. Mutated observations must never import this module.
namespace IndexedWitnessObservationParity

open LeanNCD.Semantics IndexedComponentComposition IndexedWitness
open IndexedWitnessObservationProbe

variable {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]

omit [DecidableEq σ.Tensor] in
theorem roleInterface_parity (role : σ.Tensor → Bool) :
    roleInterfaceCopy role = roleInterface role := rfl

theorem envInput_parity (A : MatchedComponent σ) (x : (inputInterface A).Env) :
    envInputCopy A x = envInput A x := rfl

theorem componentSpan_parity (A : MatchedComponent σ) :
    componentSpanCopy A = componentSpan A := rfl

variable {σA σB : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB) (wire : Boundary A B)

theorem boundaryEnvEquiv_parity :
    boundaryEnvEquivCopy A B wire = boundaryEnvEquiv A B wire := rfl

theorem compositeInputEquiv_parity :
    compositeInputEquivCopy A B wire = compositeInputEquiv A B wire := rfl

theorem compositeOutputEquiv_parity :
    compositeOutputEquivCopy A B wire = compositeOutputEquiv A B wire := rfl

theorem toWired_parity (w : (componentSpan (compose A B wire)).W) :
    toWiredCopy A B wire w = toWired A B wire w := rfl

#audit_axioms IndexedWitnessObservationParity

end IndexedWitnessObservationParity

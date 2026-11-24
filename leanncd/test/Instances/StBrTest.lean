import Mathlib
import LeanNCD.Instances.StBr
import LeanNCD.Props.Generic

namespace LeanNCD
open CategoryTheory

-- TEST: the flagship instance resolves (noncomputable, since `St` builds over the noncomputable `Coeff`).
noncomputable example : DGradedColoredPROP StObj BrObj := inferInstance

-- TEST: a generic §9 proposition specializes to the instance (the inheritance payoff).
#check (lift_functorial (D := StObj) (C := BrObj))

end LeanNCD

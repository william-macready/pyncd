import LeanNCD.Eval.Entry
import LeanNCD.DSL.Compile
import LeanNCD.Eval.Plan.Adapter32
import EvalPlanCodegen

/-!
# A scan block assignment with an Iverson factor: the gate admits it, the emitter refuses it

`checkJaxScanSupport` (the production support gate) does not look at predicate factors, so a scan whose
base or step assignment carries an Iverson factor `[j ≤ 1]` passes it; the JAX bridge has no lowering
for a predicate, so `renderScanNode` refuses with the located `JaxCodegenError.iversonFactor`. The
neighbour without the predicate is accepted by both. Locators are the scan's outer step index
(`nodeIndex`), then the term and factor index inside the offending block assignment, as observed.
-/

namespace ScanIversonRefusalTest

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std
open JaxBridge

def inputs : HashMap String DenseTensor :=
  HashMap.ofList [("X", ⟨[2], #[1.0, 2.0]⟩)]

/-- Step assignment with an Iverson factor. -/
def iverStep : TLProgram := tlprog!{
  iter l = 3
  tensor f64 X(j), S(j, l)
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l] · [j ≤ 1]
}

/-- Base assignment with an Iverson factor. -/
def iverBase : TLProgram := tlprog!{
  iter l = 3
  tensor f64 X(j), S(j, l)
  S[j, 0]    := X[j] · [j ≤ 1]
  S[j, l +1] := S[j, l]
}

/-- The neighbour: the same scan with no predicate. -/
def noIver : TLProgram := tlprog!{
  iter l = 3
  tensor f64 X(j), S(j, l)
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l]
}

/-- The plan's scan node and its outer step index. -/
def scanOf (p : TLProgram) : Option (Nat × CheckedScanPlan) :=
  match p.compileToScheduled.run 0 with
  | .error _ _ => none
  | .ok s _ =>
    match prepareEvalPlan s (InputSignature.ofDenseInputs inputs) with
    | .error _ => none
    | .ok pp => pp.plan.checkedNodes.toList.zipIdx.findSome? fun (n, i) =>
        match n with | .scan c => some (i, c) | _ => none

/-- The production support gate admits the scan. -/
def gateAdmits (p : TLProgram) : Bool :=
  match scanOf p with
  | some (i, c) => (checkJaxScanSupport i c).toOption.isSome
  | none => false

/-- The emitter's verdict on the scan node: `ok loc` for an `iversonFactor` refusal at `loc`, an `error`
    tag if it renders or refuses for another reason, `none` if there is no scan node. -/
def emitter (p : TLProgram) : Option (Except String (Nat × Nat × Nat)) :=
  match scanOf p with
  | none => none
  | some (i, c) =>
    match renderScanNode i c with
    | .ok _ => some (.error "rendered")
    | .error (.iversonFactor n t f) => some (.ok (n, t, f))
    | .error _ => some (.error "other refusal")

#guard gateAdmits iverStep
#guard gateAdmits iverBase
#guard gateAdmits noIver
#guard emitter iverStep == some (.ok (0, 0, 1))
#guard emitter iverBase == some (.ok (0, 0, 1))
#guard emitter noIver == some (.error "rendered")

end ScanIversonRefusalTest

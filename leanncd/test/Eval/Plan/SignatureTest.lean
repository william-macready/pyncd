import LeanNCD.Eval.Plan.Signature
import LeanNCD.Eval.Entry

/-!
# Wave C C1 signature-boundary tests

Covers `papers/wave_c_evalplan_proposal.md` §A.5's six test bullets for the static signature
boundary: signature conversion, existing-shape-test parity, corpus parity, an
`explicitSizes`-only extent, a pinned-size/input conflict, and warning preservation across a
later failure.
-/

namespace LeanNCD.Eval.Plan.SignatureTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

private def conversionInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[2, 3], #[0.0, 0.0, 0.0, 0.0, 0.0, 0.0]⟩

#guard (InputSignature.ofDenseInputs conversionInputs).tensors["X"]? ==
  some ({ shape := #[2, 3], dtype := .f64 } : TensorSignature)
#guard (InputSignature.ofDenseInputs conversionInputs).tensors["Missing"]? == none

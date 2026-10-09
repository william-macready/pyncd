import LeanNCD.Semantics.Source.Differential
import Semantics.SourceProgramFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceAdmissionFixtures

namespace SourceDiagnosticFixtures

def vectorSnapshot : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .axis k (some 3), .axis e (some 0),
      .typedTensor .f64 "A" [i, k], .typedTensor .f64 "B" [i],
      .typedTensor .f64 "Y" [i], .typedTensor .f64 "Empty" [e],
      .typedTensor .f64 "Diagonal" [i, i]],
    stmts, {}, ∅⟩, specs, inputs⟩

def scalarSnapshot : SourceSnapshot :=
  ⟨⟨[.typedTensor .f64 "A" [], .typedTensor .f64 "Y" []],
    [.assign "Y" [] (rhs [[.read "A" []]])], {}, ∅⟩,
    [⟨0, .input, []⟩, ⟨1, .output, []⟩], [⟨0, [], [3]⟩]⟩

end SourceDiagnosticFixtures

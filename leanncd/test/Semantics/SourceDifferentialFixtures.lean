import LeanNCD.Semantics.Source.Differential
import LeanNCD.Semantics.Source.Permutation
import Semantics.SourceProgramFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceAdmissionFixtures

namespace SourceDifferentialFixtures

def j : AxisSpec := ⟨"j", 19, .nat⟩

def matmul : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .axis j (some 2), .axis k (some 3),
      .typedTensor .f64 "W" [i, k], .typedTensor .f64 "X" [k, j],
      .typedTensor .f64 "Y" [i, j]],
    [.assign "Y" [.free i, .free j]
      (rhs [[.read "W" [.axis i, .axis k], .read "X" [.axis k, .axis j]]])],
    {}, ∅⟩,
    [⟨3, .input, [2, 3]⟩, ⟨4, .input, [3, 2]⟩, ⟨5, .output, [2, 2]⟩],
    [⟨3, [2, 3], [1, 2, 3, 4, 5, 6]⟩, ⟨4, [3, 2], [1, 0, 0, 1, 1, 1]⟩]⟩

def biasSnapshot : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .axis k (some 3),
      .typedTensor .f64 "W" [i, k], .typedTensor .f64 "X" [k],
      .typedTensor .f64 "B" [i], .typedTensor .f64 "Y" [i]],
    [.assign "Y" [.free i]
      (rhs [[.read "W" [.axis i, .axis k], .read "X" [.axis k]], [.read "B" [.axis i]]])],
    {}, ∅⟩,
    [⟨2, .input, [2, 3]⟩, ⟨3, .input, [3]⟩, ⟨4, .input, [2]⟩, ⟨5, .output, [2]⟩],
    [⟨2, [2, 3], [1, 2, 3, 4, 5, 6]⟩, ⟨3, [3], [1, 1, 1]⟩, ⟨4, [2], [7, 9]⟩]⟩

def diagonalRead : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .typedTensor .f64 "A" [i, i], .typedTensor .f64 "Y" []],
    [.assign "Y" [] (rhs [[.read "A" [.axis i, .axis i]]])], {}, ∅⟩,
    [⟨1, .input, [2, 2]⟩, ⟨2, .output, []⟩], [⟨1, [2, 2], [2, 3, 5, 11]⟩]⟩

def diagonalWrite : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .typedTensor .f64 "A" [i], .typedTensor .f64 "Y" [i, i]],
    [.assign "Y" [.free i, .free i] (rhs [[.read "A" [.axis i]]])], {}, ∅⟩,
    [⟨1, .input, [2]⟩, ⟨2, .output, [2, 2]⟩], [⟨1, [2], [5, 9]⟩]⟩

def emptyContraction : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .axis k (some 0),
      .typedTensor .f64 "A" [i, k], .typedTensor .f64 "Y" [i]],
    [.assign "Y" [.free i] (rhs [[.read "A" [.axis i, .axis k]]])], {}, ∅⟩,
    [⟨2, .input, [2, 0]⟩, ⟨3, .output, [2]⟩], [⟨2, [2, 0], []⟩]⟩

def scalar : SourceSnapshot :=
  ⟨⟨[.typedTensor .f64 "A" [], .typedTensor .f64 "B" [], .typedTensor .f64 "Y" []],
    [.assign "Y" [] (rhs [[.read "A" [], .read "B" []]])], {}, ∅⟩,
    [⟨0, .input, []⟩, ⟨1, .input, []⟩, ⟨2, .output, []⟩],
    [⟨0, [], [3]⟩, ⟨1, [], [7]⟩]⟩

end SourceDifferentialFixtures

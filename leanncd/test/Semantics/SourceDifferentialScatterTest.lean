import Semantics.SourceDifferentialFixtures
import Semantics.SourceDiagnosticFixtures

/-! S2a P3: the four-leg differential on affine write slots and scatters.

Inputs: `X[a] = [1, 2, 3, 4]` (declaration 3), `W[b] = [1, 10, 100]` (declaration 4); `|a| = 4`,
`|b| = 3`; `Y` is declaration 5 over `k` with the declared extent `|k|` (the oracle's shape);
production derives its own shape from the write forms. Fixtures are appended at the END of the
file only. -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Source.Debug
open LeanNCD.Semantics.Source.NativeLegs
open LeanNCD.Semantics.Source.Differential
open LeanNCD.Semantics.Source.NumericalProfile

namespace SourceDifferentialScatterTest

private def a : AxisSpec := ⟨"a", 7, .real⟩
private def b : AxisSpec := ⟨"b", 8, .real⟩
private def k : AxisSpec := ⟨"k", 9, .real⟩

private def rhs (terms : List (List Factor)) : RHSExpr :=
  ⟨⟨terms.map ProdTerm.mk⟩, .identity, .sum⟩

private def readX : RHSExpr := rhs [[.read "X" [.axis a]]]
private def readW : RHSExpr := rhs [[.read "W" [.axis b]]]
private def readXW : RHSExpr := rhs [[.read "X" [.axis a], .read "W" [.axis b]]]

private def snap (kExtent : Nat) (yAxes : List AxisSpec) (stmts : List Stmt) : SourceSnapshot :=
  let extent (ax : AxisSpec) : Nat :=
    if ax.uid = 7 then 4 else if ax.uid = 8 then 3 else kExtent
  { resolved := {
      decls := [.axis a (some 4), .axis b (some 3), .axis k (some kExtent),
        .typedTensor .f64 "X" [a], .typedTensor .f64 "W" [b], .typedTensor .f64 "Y" yAxes]
      stmts := stmts
      env := {}, extNames := ∅ }
    specs := [⟨3, .input, [4]⟩, ⟨4, .input, [3]⟩, ⟨5, .output, yAxes.map extent⟩]
    inputs := [⟨3, [4], [1, 2, 3, 4]⟩, ⟨4, [3], [1, 10, 100]⟩] }

private def bits (o : NativeObservation) : String :=
  match o.outputs with
  | .error issues => s!"binding issues {repr issues}"
  | .ok bs => s!"{bs.map fun x => (x.metadata.name, x.shape, x.bits.toList.map (toString ∘ Float.ofBits))}"

/-- Compact per-leg report used to record the observed table. -/
def observe (s : SourceSnapshot) : String :=
  match compareSource s (some [5]) with
  | .error e => s!"ERROR {renderExecutionError e}"
  | .ok run =>
    let oracle := match run.oracle with
      | .error u => s!"unavailable {repr u}"
      | .ok r =>
        let ys := r.tensors.filter (fun (t : Oracle.Tensor) => t.declaration == 5)
        s!"{ys.map fun (t : Oracle.Tensor) => (t.name, t.shape, t.values)}"
    let legacy := match run.native with
      | .error d => s!"admission {repr d.cause}"
      | .ok n => match n.legacy with
        | .unavailable r => s!"unavailable {repr r}"
        | .failure e => s!"failure phase={repr e.phase} cause={e.original.error}"
        | .observed o => s!"value {bits o}"
    let checked := match run.native with
      | .error _ => "-"
      | .ok n => match n.checked with
        | .unavailable r => s!"unavailable {repr r}"
        | .sourceCompilation e => s!"sourceCompilation {repr e.cause}"
        | .preparation e => s!"preparation {((renderChecked (.preparation e)).splitOn "\n").head!}"
        | .runtime e => s!"runtime {repr e.original.cause}"
        | .observed o _ => s!"value {bits o}"
    s!"class={repr run.classification}\n  oracle={oracle}\n  legacy={legacy}\n  checked={checked}"

private def conv : SourceSnapshot :=
  snap 6 [k] [.assign "Y" [.affine (.affine 0 [(1, a), (1, b)])] readXW]

#eval observe (snap 8 [k] [.assign "Y" [.affine (.scale 2 a)] readX])
#eval observe (snap 6 [k] [.assign "Y" [.affine (.shift a 2)] readX])
#eval observe (snap 6 [k] [.assign "Y" [.affine (.scale 2 a)] readX])

end SourceDifferentialScatterTest

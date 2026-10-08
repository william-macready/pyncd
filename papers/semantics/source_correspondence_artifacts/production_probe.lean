import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter

namespace SourceProductionProbe
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

private def mkAxis (name : String) (uid : Nat) : AxisSpec :=
  { name, uid, kind := .nat }

private def dense (shape : List Nat) (data : Array Float) : DenseTensor :=
  ⟨shape, data⟩

private def rhs (terms : List (List Factor)) : RHSExpr :=
  { body := ⟨terms.map ProdTerm.mk⟩, nonlin := .identity }

private def renderCause : PlanCompileCause → String
  | .inputSignature c => s!"inputSignature: {repr c}"
  | .capability c => s!"capability: {repr c}"
  | .shape c => s!"shape: {c}"
  | .scan c => s!"scan: {repr c}"
  | .invalidPlan c => s!"invalidPlan: {repr c}"
  | .bindings c => s!"bindings: {repr c}"
  | .nonlin c => s!"nonlin: {repr c}"
  | .sourceInvariant c => s!"sourceInvariant: {repr c}"

private def summarize (report : EvalReport) : String :=
  let outputs := report.env.toList.mergeSort (fun a b => a.1 ≤ b.1)
  s!"{outputs.map (fun (n, t) => (n, t.shape, t.data.toList))}; warnings={report.warnings.map toString}"

private def legacy (p : TLProgram) (inputs : HashMap String DenseTensor) : String :=
  match LeanNCD.Eval.TLProgram.eval p inputs with
  | .ok report => s!"ok {summarize report}"
  | .error e => s!"error {e.error}; warnings={e.warnings.map toString}"

private def checked (p : TLProgram) (inputs : HashMap String DenseTensor) : String :=
  match p.compileToScheduled |>.run 0 with
  | .error e _ => s!"compile: {repr e}"
  | .ok sched _ =>
    match prepareEvalPlan sched (InputSignature.ofDenseInputs inputs) with
    | .error e => s!"prepare: {renderCause e.cause}"
    | .ok plan =>
      match runPreparedDense plan inputs with
      | .error e => s!"run: {repr e.cause}"
      | .ok report => s!"ok {summarize report}"

private def compare (label : String) (p : TLProgram)
    (inputs : HashMap String DenseTensor) : String :=
  s!"{label}\n legacy: {legacy p inputs}\n checked: {checked p inputs}"

private def i := mkAxis "i" 10
private def j := mkAxis "j" 11
private def k := mkAxis "k" 12

#eval compare "matmul"
  { decls := [.axis i (some 2), .axis j (some 2), .axis k (some 3),
      .typedTensor .f64 "W" [i, k], .typedTensor .f64 "X" [k, j],
      .typedTensor .f64 "Y" [i, j]]
    stmts := [.assign "Y" [.free i, .free j]
      (rhs [[.read "W" [.axis i, .axis k], .read "X" [.axis k, .axis j]]])] }
  ((({} : HashMap String DenseTensor).insert "W"
    (dense [2, 3] #[1, 2, 3, 4, 5, 6])).insert "X" (dense [3, 2] #[1, 0, 0, 1, 1, 1]))

#eval compare "term-local-bias"
  { decls := [.axis i (some 2), .axis k (some 3),
      .typedTensor .f64 "W" [i, k], .typedTensor .f64 "X" [k],
      .typedTensor .f64 "B" [i], .typedTensor .f64 "Y" [i]]
    stmts := [.assign "Y" [.free i]
      (rhs [[.read "W" [.axis i, .axis k], .read "X" [.axis k]],
        [.read "B" [.axis i]]])] }
  (((({} : HashMap String DenseTensor).insert "W"
    (dense [2, 3] #[1, 2, 3, 4, 5, 6])).insert "X"
    (dense [3] #[1, 1, 1])).insert "B" (dense [2] #[7, 9]))

#eval compare "diagonal-read"
  { decls := [.axis i (some 2), .typedTensor .f64 "A" [i, i],
      .typedTensor .f64 "Y" []]
    stmts := [.assign "Y" [] (rhs [[.read "A" [.axis i, .axis i]]])] }
  (({} : HashMap String DenseTensor).insert "A" (dense [2, 2] #[2, 3, 5, 11]))

#eval compare "diagonal-write"
  { decls := [.axis i (some 2), .typedTensor .f64 "A" [i],
      .typedTensor .f64 "Y" [i, i]]
    stmts := [.assign "Y" [.free i, .free i] (rhs [[.read "A" [.axis i]]])] }
  (({} : HashMap String DenseTensor).insert "A" (dense [2] #[5, 9]))

#eval compare "empty-contraction"
  { decls := [.axis i (some 2), .axis k (some 0),
      .typedTensor .f64 "A" [i, k], .typedTensor .f64 "Y" [i]]
    stmts := [.assign "Y" [.free i] (rhs [[.read "A" [.axis i, .axis k]]])] }
  (({} : HashMap String DenseTensor).insert "A" (dense [2, 0] #[]))

#eval compare "scalar"
  { decls := [.typedTensor .f64 "A" [], .typedTensor .f64 "B" [],
      .typedTensor .f64 "Y" []]
    stmts := [.assign "Y" [] (rhs [[.read "A" [], .read "B" []]])] }
  ((({} : HashMap String DenseTensor).insert "A" (dense [] #[3])).insert
    "B" (dense [] #[7]))

#eval compare "within-statement-duplicates"
  { decls := [.axis i (some 2), .typedTensor .f64 "A" [i],
      .typedTensor .f64 "Y" [i]]
    stmts := [.assign "Y" [.free i]
      (rhs [[.read "A" [.axis i]], [.read "A" [.axis i]]])] }
  (({} : HashMap String DenseTensor).insert "A" (dense [2] #[5, 9]))

#eval compare "cross-statement-known-contract"
  { decls := [.axis i (some 2), .typedTensor .f64 "A" [i],
      .typedTensor .f64 "B" [i], .typedTensor .f64 "Y" [i]]
    stmts := [.assign "Y" [.free i] (rhs [[.read "A" [.axis i]]]),
      .assign "Y" [.free i] (rhs [[.read "B" [.axis i]]])] }
  ((({} : HashMap String DenseTensor).insert "A" (dense [2] #[5, 9])).insert
    "B" (dense [2] #[2, 4]))

#eval compare "default-dtype-outside-f64-profile"
  { decls := [.axis i (some 2), .tensor "A" [i], .tensor "Y" [i]]
    stmts := [.assign "Y" [.free i] (rhs [[.read "A" [.axis i]]])] }
  (({} : HashMap String DenseTensor).insert "A" (dense [2] #[5, 9]))

end SourceProductionProbe

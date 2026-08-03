import LeanNCD.Eval.Entry

/-!
# Evaluator entry/report boundary

These checks pin the Wave-E boundary rather than numeric semantics already covered elsewhere:
`evalScheduled` consumes a compiled schedule without owning compilation, and `TLProgram.eval`
preserves warnings in both `EvalReport` and `EvalFailure`.
-/

namespace LeanNCD.Eval
open Std

private def paddedProgram : TLProgram := tlprog!{
  axis i : ℕ = 4
  axis j : ℕ = 3
  Y[i, j] := X[2 * i + j]
}

private def paddedInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" (DenseTensor.zeros [6])

private def paddedDomainProgram : TLProgram := tlprog!{
  axis i : ℕ = 4
  axis j : ℕ = 3
  Y[i, j] := log(X[2 * i + j])
}

private def paddedConflictProgram : TLProgram := tlprog!{
  axis i : ℕ = 4
  axis j : ℕ = 3
  axis k : ℕ = 2
  Y[i, j, k] := X[2 * i + j] · A[k]
}

/-- Check the complete structured padded-access payload rather than merely its rendered prefix. -/
private def isExpectedPadding : List EvalWarning → Bool
  | [.paddedAccess source 8 6] => source.startsWith "X["
  | _ => false

-- The warning first produced by `inferAxisSizes` reaches the compiler-independent worker report.
run_cmd do
  match paddedProgram.compileToScheduled.run 0 with
  | .error e _ => throwError s!"report worker setup did not compile: {repr e}"
  | .ok sched _ =>
      match evalScheduled sched paddedInputs with
      | .error e => throwError s!"scheduled report evaluation failed: {e}"
      | .ok report =>
          unless isExpectedPadding report.warnings do
            throwError s!"scheduled report lost warning payload: {report.warnings.map toString}"
          unless report.env["Y"]?.map (·.shape) == some [4, 3] do
            throwError "scheduled report did not preserve the full output environment"

-- The source entry returns the same structured warning and full environment.
run_cmd do
  match TLProgram.eval paddedProgram paddedInputs with
  | .error e => throwError s!"source report evaluation failed: {e}"
  | .ok report =>
      unless isExpectedPadding report.warnings do
        throwError s!"source report lost warning payload: {report.warnings.map toString}"
      unless report.warnings.any (fun w => (toString w).contains "padded-access warning") do
        throwError "warning renderer no longer preserves its compatibility text"
      unless report.env["Y"]?.map (·.shape) == some [4, 3] do
        throwError "source report did not preserve the evaluated environment"

-- Warning-free evaluation reports an empty list rather than printing or fabricating diagnostics.
run_cmd do
  let env : HashMap String DenseTensor :=
    ({} : HashMap String DenseTensor).insert "X" (DenseTensor.zeros [2])
  match TLProgram.eval (tlprog!{ Y[i] := X[i] }) env with
  | .error e => throwError s!"warning-free report evaluation failed: {e}"
  | .ok report =>
      unless report.warnings.isEmpty do
        throwError s!"warning-free evaluation returned {report.warnings.map toString}"

-- A later fatal worker error must not erase warnings already discovered during shape inference.
-- This program has the same padded affine read as above, then fails immediately because X[0] = 0
-- is outside log's domain.
run_cmd do
  match TLProgram.eval paddedDomainProgram paddedInputs with
  | .error failure =>
      match failure.error with
      | .unaryDomain .log value context =>
          unless value == 0.0 do
            throwError s!"expected log(0) domain failure, got value {value}"
          unless context.tensor == "X" && context.coord == [0] do
            throwError s!"domain failure lost its source context: {context.tensor} {context.coord}"
          unless isExpectedPadding failure.warnings do
            throwError s!"fatal evaluation lost prior warnings: {failure.warnings.map toString}"
      | error => throwError s!"expected log domain failure after warning, got: {error}"
  | .ok _ => throwError "expected padded-domain program to fail"

-- Inference can itself fail after an earlier position emitted a warning. The X position warns
-- first; the later bare A[k] position conflicts with explicit k=2 versus A's dimension 3.
run_cmd do
  let inputs := paddedInputs.insert "A" (DenseTensor.zeros [3])
  match TLProgram.eval paddedConflictProgram inputs with
  | .error failure =>
      match failure.error with
      | .shape (.sizeConflict _uid 2 3) =>
          unless isExpectedPadding failure.warnings do
            throwError s!"shape inference failure lost prior warnings: {failure.warnings.map toString}"
      | error => throwError s!"expected size conflict after warning, got: {error}"
  | .ok _ => throwError "expected padded-conflict program to fail during shape inference"

-- Source compilation failures remain typed causes at the entry boundary.
run_cmd do
  match TLProgram.eval (tlprog!{
    tensor X(j)
    G[j, 0] := X[j]
    G[j, l + 1] := G[j, l]
  }) ({} : HashMap String DenseTensor) with
  | .error { error := .compile (.scanAxisNotIter "l"), warnings := [] } => pure ()
  | .error failure => throwError s!"compile cause was changed or flattened: {failure}"
  | .ok _ => throwError "expected source entry to preserve scanAxisNotIter"

-- Worker failures likewise retain their nested shape cause through the source entry.
run_cmd do
  let env : HashMap String DenseTensor :=
    (({} : HashMap String DenseTensor).insert "A" (DenseTensor.zeros [3])).insert "B"
      (DenseTensor.zeros [2])
  match TLProgram.eval (tlprog!{ s[] := A[i] · B[i] }) env with
  | .error { error := .shape (.solveFailure diagnostic), warnings } =>
      unless warnings.isEmpty do
        throwError s!"shape inference failure unexpectedly carried warnings: {warnings.map toString}"
      unless decide (diagnostic.kind = .inconsistent) do
        throwError s!"expected inconsistent shape diagnostic, got: {renderSolveDiagnostic diagnostic}"
  | .error failure => throwError s!"shape cause was changed or flattened: {failure}"
  | .ok _ => throwError "expected source entry to preserve the shape failure"

end LeanNCD.Eval

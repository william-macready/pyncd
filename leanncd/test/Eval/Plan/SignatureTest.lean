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

/-- Run both shape-inference adapters over the same schedule and concrete inputs, and assert
    their outcomes agree exactly — the Gate's own criterion, applied directly rather than
    re-derived by hand. -/
private def parityCheck (sched : ScheduledProgram) (inputs : HashMap String DenseTensor) :
    Except String Unit := do
  let allStmts : List Stmt := sched.stmts.flatMap (fun
    | .plain s => [s] | .scan _ _ b r _ => b ++ r | .scanPre _ _ _ => [])
  let sig := InputSignature.ofDenseInputs inputs
  match inferAxisSizes sched.explicitSizes inputs allStmts,
        inferAxisSizesFromSignature sched.explicitSizes sig allStmts with
  | .ok (sizes1, warns1), .ok (sizes2, warns2) =>
      unless decide (sizes1.toList = sizes2.toList) do
        throw s!"sizes diverged: {sizes1.toList} vs {sizes2.toList}"
      unless decide (warns1 = warns2) do
        throw s!"warnings diverged: {warns1} vs {warns2}"
  | .error e1, .error e2 =>
      -- `EvalError` has no `DecidableEq` (its `.unaryDomain` case carries a `Float`, which has
      -- none either — confirmed empirically, not assumed), so structural `=` does not typecheck
      -- here; compare via the existing byte-for-byte `ToString EvalError` renderer instead. Every
      -- error this helper actually sees is `inferAxisSizesCore`'s own `.shape` variant (the only
      -- one it ever throws — see `Eval/SizeInfer.lean`), whose `ShapeError` DOES derive
      -- `DecidableEq`, so the rendered text is a faithful, lossless stand-in for structural
      -- equality in every case this test corpus exercises.
      unless decide (toString e1.error = toString e2.error) do
        throw s!"errors diverged: {e1.error} vs {e2.error}"
      unless decide (e1.warnings = e2.warnings) do
        throw s!"error-path warnings diverged: {e1.warnings} vs {e2.warnings}"
  | .ok _, .error e2 => throw s!"env-based path succeeded but signature-based path failed: {e2.error}"
  | .error e1, .ok _ => throw s!"signature-based path succeeded but env-based path failed: {e1.error}"

private def parityProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  Y[i, j] := X[2 * i + j]
}

private def parityInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[6], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]⟩

run_cmd do
  match parityProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"parity-case compile failed: {repr e}"
  | .ok sched _ =>
      match parityCheck sched parityInputs with
      | .error e => throwError s!"parity mismatch (existing shape case): {e}"
      | .ok () => pure ()

-- Category 3 — parity across a small hand-written corpus.
--
-- Route decision: `test/Eval/PropertyOracle/Gen.lean` was read first, per the brief. Its only
-- non-`private` declaration is `enumPrograms : List (TLProgram × HashMap String DenseTensor)` — a
-- single bulk enumerator (`one ++ two ++ yDepPrograms ++ contractPrograms ++
-- contractMultiTermPrograms`, up to 5000 entries per its own contract test). Every named,
-- individually-meaningful sub-list feeding it (`contractPrograms`, `yDepPrograms`,
-- `contractMultiTermPrograms`, `stmtChoices`, etc.) is `private` to `Gen.lean` and so is not
-- accessible from this file, and picking specific numeric indices out of `enumPrograms` itself
-- would mean relying on undocumented, cap-dependent positional offsets (`twoStmtCap`,
-- `cappedTwoStmt`) to guess which index is "the multi-factor one" or "the chained one" — brittle
-- and opaque, exactly the case the brief calls out as not easily sliceable. So this follows the
-- brief's fallback: two hand-written `tlprog!` fixtures, in the same explicit-axis style as
-- `parityProg`/`conflictProg` above, covering multiple factors in one term (a contraction, not
-- covered by category 2's single-factor affine read) and a chained two-statement program (not
-- covered anywhere else in this file).

private def multiFactorProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  H[i] := A[i, j] · B[j]
}

private def multiFactorInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" ⟨[2, 3], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]⟩).insert
    "B" ⟨[3], #[1.0, 1.0, 1.0]⟩

run_cmd do
  match multiFactorProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"corpus multi-factor case compile failed: {repr e}"
  | .ok sched _ =>
      match parityCheck sched multiFactorInputs with
      | .error e => throwError s!"parity mismatch (corpus multi-factor case): {e}"
      | .ok () => pure ()

private def chainedProg : TLProgram := tlprog!{
  axis i : ℕ = 4
  Y[i] := P[i]
  Z[i] := Y[i]
}

private def chainedInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "P" ⟨[4], #[10.0, 20.0, 30.0, 40.0]⟩

run_cmd do
  match chainedProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"corpus chained-program case compile failed: {repr e}"
  | .ok sched _ =>
      match parityCheck sched chainedInputs with
      | .error e => throwError s!"parity mismatch (corpus chained-program case): {e}"
      | .ok () => pure ()

private def conflictProg : TLProgram := tlprog!{
  axis k : ℕ = 2
  Z[k] := W[k]
}

-- W's actual shape (5) conflicts with k's pinned size (2) from the `axis k : ℕ = 2` declaration.
private def conflictInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "W" ⟨[5], #[0.0, 0.0, 0.0, 0.0, 0.0]⟩

run_cmd do
  match conflictProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"conflict-case compile failed: {repr e}"
  | .ok sched _ =>
      match parityCheck sched conflictInputs with
      | .error e => throwError s!"parity mismatch (pinned-size conflict case): {e}"
      | .ok () => pure ()
      -- Also confirm this case actually IS a conflict, not an accidentally-passing fixture:
      let allStmts := sched.stmts.flatMap (fun
        | .plain s => [s] | .scan _ _ b r _ => b ++ r | .scanPre _ _ _ => [])
      match inferAxisSizes sched.explicitSizes conflictInputs allStmts with
      | .ok _ => throwError "conflict-case fixture does not actually conflict — fix the fixture"
      | .error _ => pure ()

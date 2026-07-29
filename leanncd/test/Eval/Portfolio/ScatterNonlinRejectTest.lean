import Eval.Portfolio.Harness
/-!
# Spike-3 Stage 0 — reject non-identity scatter

Regression tests for the silent-erasure bug: `splitStmt` passed `.scatter` through unchanged
and `evalScatter` evaluated `rhs.body` but never applied `rhs.nonlin`, so e.g.
`Out[2*i] := relu(X[i])` used to compile AND evaluate with the `relu` silently dropped. Chosen
policy (Spike-3 Stage-0, SHORT-TERM — see `checkScatterNonlin` in
`DSL/Pipeline/Structural.lean`): `scatter + identity` accepted, `scatter + non-identity`
rejected during validation.

* RSN1 — a scatter LHS with a `relu` RHS is REJECTED at compile time with the specific
  `CompileError.unsupportedNonlinScatter` constructor (not merely "is an error").
* RSN2 — an identity-nonlin scatter still compiles and evaluates correctly (the existing
  upsample pattern from `Eval.ScatterTest`/`Eval.Portfolio.GnnScatterTest`'s SC1).
* RSN3 — the defensive `evalScatter` check (belt-and-suspenders for programmatic callers that
  build the AST directly, bypassing the surface compiler's validation) also rejects a
  non-identity-nonlin scatter, pinned to the specific defensive-check error message (not merely
  "is an error" — `EvalError` is a plain `String` and `evalScatter` has other `throw` sites, e.g.
  unknown tensor name or unsized source axis, so a bare "is an error" check wouldn't pin down
  *which* check fired).
* RSN4 — a *diagonal* LHS (`Y[i, i]`, a repeated `.free` axis UID — the other
  `slotsBecomeScatter` trigger besides an `.affine` slot) with a `relu` RHS is REJECTED at
  compile time with the same `unsupportedNonlinScatter` constructor.
-/
namespace LeanNCD.Eval
open Std

-- RSN1  a scatter LHS with a relu RHS ⇒ CompileError.unsupportedNonlinScatter, NOT a value.
run_cmd do
  match TLProgram.compile (tlprog!{ Out[2 * i] := relu(X[i]) }) |>.run 0 with
  | .error (.unsupportedNonlinScatter "Out") _ => pure ()
  | .error e _ => throwError s!"RSN1: wrong CompileError: {repr e}"
  | .ok _ _    => throwError "RSN1: expected unsupportedNonlinScatter, compile succeeded"

-- RSN2  an identity-nonlin scatter still compiles/evaluates fine (2× upsample; X at even coords,
--   0 elsewhere — same shape as the SC1 pattern in GnnScatterTest).
run_cmd (assertEval "RSN2 identity-scatter-still-works"
  (tlprog!{ tensor Out(i, j)
            Out[2 * i, 2 * j] := X[i, j] })
  (HashMap.ofList [("X", tl [2,2] [1,2, 3,4])])
  "Out" (tl [4,4] [1,0,2,0, 0,0,0,0, 3,0,4,0, 0,0,0,0]))

-- RSN3  defensive check: `evalScatter` itself rejects a non-identity nonlin (programmatic AST
--   construction bypassing the surface compiler / validation).
run_cmd do
  let i : AxisSpec := { name := "i", uid := 1, kind := .real none }
  let X := DenseTensor.mk [2] #[1.0, 2.0]
  let env : HashMap String DenseTensor := ({} : HashMap String DenseTensor).insert "X" X
  let slots : List LHSSlot := [.affine (.scale 2 i)]
  let rhs : RHSExpr := { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := .relu }
  let sizes := ({} : HashMap UID Nat).insert 1 2
  match evalScatter env sizes "Out" slots rhs { fill := 0, reduce := none } [4] with
  | .error e =>
      unless (e.splitOn "non-identity nonlinearity on scatter").length > 1 do
        throwError s!"RSN3: wrong error message: {e}"
  | .ok _    => throwError "RSN3: expected evalScatter to reject a non-identity nonlin scatter"

-- RSN4  diagonal-LHS trigger: `Y[i, i]` repeats the free axis `i`, so `slotsBecomeScatter` fires
--   via the repeated-freeUID disjunct (no `.affine` slot at all — confirmed by construction: a
--   bare axis variable on the LHS elaborates to `.free`, only an arithmetic index like `2*i`
--   elaborates to `.affine`; see `LHSSlot` cases in `DSL/Ast.lean`). Non-identity nonlin ⇒ same
--   `unsupportedNonlinScatter` rejection as the affine case (RSN1).
run_cmd do
  match TLProgram.compile (tlprog!{ Y[i, i] := relu(X[i]) }) |>.run 0 with
  | .error (.unsupportedNonlinScatter "Y") _ => pure ()
  | .error e _ => throwError s!"RSN4: wrong CompileError: {repr e}"
  | .ok _ _    => throwError "RSN4: expected unsupportedNonlinScatter, compile succeeded"

end LeanNCD.Eval

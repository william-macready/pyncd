import Eval.Portfolio.Harness
/-!
# Portfolio §13 — Adversarial reject tests

Programs the DSL should refuse. Three sub-kinds:

* **compile-error** — caught via `TLProgram.compile … |>.run 0` (specific `CompileError`).
* **eval-error** — surfaced through `TLProgram.eval` (`assertEvalError`).
* **parse-error** — fail during elaboration of `tlprog!`; these CANNOT be automated (a hard
  parse error fails the build, and `#guard_msgs` does not validate parse-time errors), so they
  are documented as comments below.

Probed against HEAD (2026-07-04); RJ6 re-probed 2026-07-30. Note: the draft's RJ9
(purely-negative index) does **not** actually reject — it returns output — so it is not authored
here; see the note at the end.  **RJ6 now REJECTS** (it previously did not; see RJ6 below).
-/
namespace LeanNCD.Eval
open Std

-- RJ3  predicate output + non-sum aggregation ⇒ CompileError.predicateAgg
run_cmd do
  match TLProgram.compile (tlprog!{ predicate P(i)
                                    P[i] := maxreduce(E[i, j]) }) |>.run 0 with
  | .error (.predicateAgg "P") _ => pure ()
  | .error e _ => throwError s!"RJ3: wrong CompileError: {repr e}"
  | .ok _ _    => throwError "RJ3: expected predicateAgg, compile succeeded"

-- RJ4  softmax with no `·`-marked reduction axis ⇒ eval error
-- RJ6  a scan whose iteration axis is never sized IS rejected — but read the mechanism carefully,
--       because it is NOT the one the 2026-07-26 code analysis reported.
--
--       Probed 2026-07-30: `compileToScheduled` on this program yields
--         SCAN G axes=[] uids=[] base=1 recur=1 aff=true
--       i.e. `finalizeScans` emits a `.scan` node with an EMPTY iteration-axis list, so the
--       pre-existing `axes.isEmpty` guard in `evalScan` is what rejects it.  The separate
--       unsized-extent check added to `evalScan` the same day (an unspecified extent is not an
--       extent of 0) is correct hardening but is UNREACHABLE for this program — it needs a scan
--       that has axes yet lacks a size for one.  This assertion therefore pins the `axes.isEmpty`
--       path; the sizing check is currently unguarded by any test.
--
--       TWO OPEN PUZZLES (do not treat #5 as closed):
--        (a) Why does `finalizeScans` build a `.scan` with `axes = []` at all?  A scan with no
--            iteration axis looks like it should be unrepresentable, and the guard is masking it.
--        (b) `#eval!`-ing `TLProgram.eval` on this program still emitted
--            `Error: index out of bounds` from `lean_array_set_panic` (reproduced 2026-07-30).
--            `compileToScheduled` alone does NOT panic, so the unchecked `Array.set!` is somewhere
--            in the eval path — `Shape.lean:431,472`'s own `getD 0` are the prime suspects.  A
--            panic that does not become an `EvalError` is a defect under any sizing policy.
run_cmd (assertEvalError "RJ6 unsized-scan-axis (via the axes.isEmpty guard — see note)"
  (tlprog!{ tensor X(j)
            G[j, 0]     := X[j]
            G[j, l + 1] := G[j, l] })
  (HashMap.ofList [("X", tl [2] [1, 2])])
  "no iteration axis")

run_cmd (assertEvalError "RJ4 softmax-no-axis"
  (tlprog!{ A[q, s] := softmax(Q[q, d] · K[s, d]) })
  (HashMap.ofList [("Q", tl [2,2] [1,0,0,1]), ("K", tl [2,2] [1,0,0,1])])
  "no output axis is marked")

-- RJ7  an axis unified to two different sizes ⇒ eval size-inconsistency error
run_cmd (assertEvalError "RJ7 size-conflict"
  (tlprog!{ s[] := A[i] · B[i] })
  (HashMap.ofList [("A", tl [3] [1,2,3]), ("B", tl [2] [1,1])])
  "inconsistent")

-- SS4 / RC4  a scan step reading an external at the advancing index l+1 ⇒ causalityViolation
run_cmd do
  match TLProgram.compile (tlprog!{ axis l : ℕ = 3
                                    S[j, 0]    := X[j, 0]
                                    S[j, l +1] := S[j, l] + X[j, l + 1] }) |>.run 0 with
  | .error (.causalityViolation "S") _ => pure ()
  | .error e _ => throwError s!"SS4: wrong CompileError: {repr e}"
  | .ok _ _    => throwError "SS4: expected causalityViolation, compile succeeded"

-- UF1  unknown tensor referenced ONLY via a `.unaryFn` factor (`log(Missing[i])`) ⇒ the same
--   up-front "unknown tensor" eval error as a plain `.read` would give — regression test for
--   `readNames` treating `.unaryFn` exactly like `.read` (§19 test_portfolio discussion).
run_cmd (assertEvalError "UF1 unaryFn-unknown-tensor"
  (tlprog!{ L[] := log(Missing[i]) })
  (HashMap.ofList [("dummy", tl [2] [1,1])])
  "unknown tensor")

-- UF2  a look-ahead scan read HIDDEN inside `log(...)` must still trip the causality guard —
--   regression test for `Stmt.rhsReads` treating `.unaryFn` exactly like `.read` (the guard
--   is computed from index expressions, not raw factor reads, so a careless implementation
--   could let this slip through).
run_cmd do
  match TLProgram.compile (tlprog!{ axis l : ℕ = 3
                                    S[j, 0]    := X[j, 0]
                                    S[j, l +1] := S[j, l] + log(X[j, l + 1]) }) |>.run 0 with
  | .error (.causalityViolation "S") _ => pure ()
  | .error e _ => throwError s!"UF2: wrong CompileError: {repr e}"
  | .ok _ _    => throwError "UF2: expected causalityViolation, compile succeeded"

-- UF3  domain violation: log of a non-positive value fails loud (not a silent NaN/-inf), per
--   this evaluator's fail-loud convention.
run_cmd (assertEvalError "UF3 log-domain-violation"
  (tlprog!{ L[] := log(P[i]) })
  (HashMap.ofList [("P", tl [2] [1, -1])])
  "log domain error")

-- UF4  division by zero (the friendly `/` operator, KG-div) fails loud rather than propagating
--   `inf`. `/` desugars to `Factor.unaryFn .recip`, so this exercises the same domain-check
--   convention as UF3.
run_cmd (assertEvalError "UF4 div-domain-violation"
  (tlprog!{ Y[i] := X[i] / Z[i] })
  (HashMap.ofList [("X", tl [2] [1,2]), ("Z", tl [2] [1,0])])
  "div domain error")

-- UF5  a per-step scan read-out written INSIDE the scan block ⇒ scanProjectionUnsupported.
--   `y[j,l] := C[j,k]·h[k,l]` has no base case and its own LHS references the scan axis `l` —
--   ambiguous between "track this across every step" (not materialized here) and "same-step
--   scratch" (never references `l` on its own LHS). Rejected rather than silently dropped; the
--   fully general workaround is SS2 (`GenerativeTest.lean`) — write it standalone, after the
--   scan, reading the materialized state.
run_cmd do
  match TLProgram.compile (tlprog!{ axis l : ℕ = 3
                                    h[j, 0]    := h0[j]
                                    h[j, l +1] := A[j, k] · h[k, l] + B[j] · u[l]
                                    y[j, l]    := C[j, k] · h[k, l] }) |>.run 0 with
  | .error (.scanProjectionUnsupported "y") _ => pure ()
  | .error e _ => throwError s!"UF5: wrong CompileError: {repr e}"
  | .ok _ _    => throwError "UF5: expected scanProjectionUnsupported, compile succeeded"

/-
Parse-level rejects (fail during elaboration of `tlprog!`; not automatable — kept as documentation):

  RJ1  symbolic-coefficient stride:   Y[i] := W[p] · X[s * j]
       → `unexpected token '*'; expected ']'`  (IdxExpr has no symbolic-coeff strides)

  RJ2  floor-division by a variable inside an INDEX expression:   Y[i] := X[i / j]
       → `unexpected token '/'; expected ']'`  (`/` is not wired into `tl_idx_expr` grammar at
       all — this is unrelated to the friendly `/` DIVISION operator added for KG-div, UF4,
       which lives in `tl_prod_term` — a different syntax category — and only divides one
       tensor's value by another's, never an index)

  RJ5  over-indexed read of an undeclared intermediate — rejected by Task-A guard.

  RJ8  softmax norm axis not among outputs — not constructible via surface syntax (marking a
       slot always places it on the LHS).

  RJ10 scatter with an unsized output axis — `scatterOutShape` fails loud; needs an upstream
       sizing gap that surface syntax does not readily produce.

Dropped from the draft (do NOT reject — return output instead):
  RJ9  Y[i] := X[i - 5] with a short input               → evaluates (zero-padded), no Issue-D error.

REVERSED 2026-07-30 — RJ6 now rejects:
  RJ6  scan with no `axis l` pin and no input fixing `l`.  This entry previously read "do NOT
       reject — evaluates (0-step / defaulted)".  That was decided WITHOUT knowing the path
       panics: `evalScan`'s `(sizes[u]?).getD 0` conflated "unsized" with "extent 0", which drove
       an unchecked `Array.set!` in the base-slice write, so the program below emitted
       `Error: index out of bounds` from `lean_array_set_panic` rather than returning anything.
       Reproduced 2026-07-30.  An unspecified extent is not an extent of zero, so `evalScan` now
       fails loud and names the axis.  Automated as RJ6 above.
-/

end LeanNCD.Eval

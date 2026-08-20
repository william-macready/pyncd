import Eval.PropertyOracle.ScanUnroll

/-!
# Scan-unrolling oracle runner (E6; generalized for Wave F F4, Task 5)

`checkScanLaw`/`runAllScans` state the SCAN-UNROLL law over the curated generator: evaluating a
scan program and evaluating its mechanically unrolled, scan-free companion must publish the same
complete state histories.

Two things changed in F4 relative to the E6 original:

* the companion is built by `ScanUnroll.independentRun`, which handles arbitrary advancing-dimension
  positions, deep affine history reads, multi-axis grids, several base writes per state and
  block-local scratch — the four deficiencies plan §4.8 lists — instead of the old immediate-
  predecessor/trailing-axis/one-2×2-template pair; and
* the comparison reassembles histories with `DenseTensor.ofFn` from per-coordinate leaves instead of
  slicing the scan's own output with the inverse of a scan-worker write helper.

This file is the TWO-way leg (legacy evaluator versus independent unrolling) and runs over the whole
17-case corpus, including the eight cases F4 rejects as capability failures but which the legacy
evaluator still executes. The THREE-way gate (compiled checked plan, legacy, independent) lives in
`test/Eval/Plan/DifferentialTest.lean`, where the compiler is in scope.

Scope note: the independent unrolling implements the CHECKED (Jacobi, immutable-pre-step) reading —
a state read inside step `u` always resolves to the pre-step snapshot. The legacy worker is
Gauss-Seidel. No case here can tell them apart (every recurrence writes at the advanced coordinate
and reads at the current one), so a future disagreement is a real semantic finding to report, not
an oracle bug to tune away.
-/
namespace LeanNCD.PropertyOracle
open LeanNCD LeanNCD.Eval Std

/-- Compare two environments on the given names. `none` if they agree. -/
def statesAgree (what : String) (names : List String)
    (a b : HashMap String DenseTensor) : Option String :=
  names.findSome? (fun nm =>
    match a[nm]?, b[nm]? with
    | some x, some y =>
        if denseEq x y then none
        else some s!"{what}: state {nm} differs — \
left={repr x.shape}/{repr x.data} right={repr y.shape}/{repr y.data}"
    | none, _ => some s!"{what}: the left environment has no {nm}"
    | _, none => some s!"{what}: the right environment has no {nm}")

/-- The scan-unrolling law on one generated case: `none` if the legacy evaluator and the
    independent scan-free unrolling publish identical histories, else a counterexample message. -/
def checkScanLaw (c : ScanCase) : Option String :=
  match schedOfCase c with
  | .error m => some m
  | .ok sched =>
      let names := scannedStateNames sched
      if names.isEmpty then some "generated case publishes no scan state at all" else
      match evalScheduled sched c.inputs, independentRun sched c.inputs with
      | .error e, _ => some s!"the legacy evaluator rejected a generated case: {e.error}"
      | _, .error m => some s!"the independent unrolling failed: {m}"
      | .ok legacy, .ok indep => statesAgree "SCAN-UNROLL law violated" names legacy.env indep

/-- Run the law over the whole generator; `none` if all pass, else the first failure message. -/
def runAllScans : Option String :=
  enumScanCases.findSome? checkScanLaw

-- TEST-THE-TESTER (a): every generated case passes, and the corpus is the size it claims to be.
#guard enumScanCases.length == 17
#guard runAllScans.isNone

-- TEST-THE-TESTER (b): the corpus really exercises what this leg claims. Derived structurally from
-- the compiled schedules, not asserted by name, so a template that quietly stopped having the
-- feature cannot keep the guard green.
private def compiledScans : List ScheduledProgram :=
  enumScanCases.filterMap (fun c => (schedOfCase c).toOption)
#guard compiledScans.length == 17
-- more than one scan axis
#guard compiledScans.any (fun s => s.stmts.any (fun
  | .scan _ axes _ _ _ => axes.length ≥ 2
  | _ => false))
-- coupled states (two persistent states in one node)
#guard compiledScans.any (fun s => s.stmts.any (fun
  | .scan _ _ base _ _ => ((base.map Stmt.lhsName).eraseDups).length ≥ 2
  | _ => false))
-- a base write that leaves an advancing axis FREE (the §5.1 boundary face, which is what makes the
-- base region an enumeration rather than a single coordinate)
#guard compiledScans.any (fun s => s.stmts.any (fun
  | .scan _ axes base _ _ =>
      base.any (fun b => b.slots.any (fun sl => match sl with
        | .free a => axes.any (fun x => x.uid == a.uid)
        | _ => false))
  | _ => false))
-- a non-identity nonlinearity and a tropical aggregation carried through the unrolling
#guard compiledScans.any (fun s => s.stmts.any (fun
  | .scan _ _ _ recur _ => recur.any (fun r => r.nonlinOf != Nonlin.identity)
  | _ => false))
#guard compiledScans.any (fun s => s.stmts.any (fun
  | .scan _ _ _ recur _ => recur.any (fun r => match r with
      | .assign _ _ rhs => rhs.agg == .max || rhs.agg == .min
      | _ => false)
  | _ => false))

-- `advScratch` (`ScanUnroll.lean`'s `ScanGeom` field, the `%nl` shape `splitNonlins` manufactures
-- for a nonlinear recurrence) is populated only by the `relu`-template generated cases; assert that
-- at least one still does, so a future template change that silently drops those cases is caught
-- here instead of by a later audit.
private def analyzedScans : List ScanGeom :=
  enumScanCases.filterMap (fun c => match schedOfCase c with
    | .error _ => none
    | .ok sched => match sched.stmts.find? (fun s => match s with | .scan .. => true | _ => false) with
        | none => none
        | some sc => (analyzeScan sched.explicitSizes sc).toOption)
-- at least one generated case actually populates advScratch (the recurrence-only nonlinear-carry
-- destination `splitNonlins` manufactures) — previously implicit in which templates happen to exist.
#guard analyzedScans.any (fun g => !g.advScratch.isEmpty)

/-! ## TEST-THE-TESTER (c): the oracle has teeth

A deliberately wrong unrolling must be caught. The mutations below are applied to the LEAF program,
which is the surface every oracle mutation in the F4 completion record perturbs, and each is checked
to produce a genuine value disagreement rather than a missing key. -/

private def t1sched : Except String ScheduledProgram := schedOfCase (template1 3 false)

/-- Evaluate a corrupted leaf program for the one-axis template and reconstruct its history. -/
private def corruptedT1 (f : List Stmt → List Stmt) : Except String DenseTensor := do
  let sched ← t1sched
  let sc ← match sched.stmts.find? (fun s => match s with | .scan .. => true | _ => false) with
    | some sc => pure sc
    | none    => .error "template1 did not compile to a scan node"
  let un ← unrollScanNode sched.explicitSizes sc
  let un' := { un with stmts := f un.stmts }
  let leafEnv ← match evalScheduled
      { sched with stmts := un'.stmts.map ScanStmt.plain } (template1 3 false).inputs with
    | .ok r    => pure r.env
    | .error e => .error s!"corrupted leaf program failed: {e.error}"
  match un'.geom.states with
  | [st] => reconstructHistory un' st leafEnv
  | _    => .error "template1 should have exactly one state"

private def t1Reference : Option DenseTensor :=
  match t1sched with
  | .error _ => none
  | .ok sched => (independentRun sched (template1 3 false).inputs).toOption.bind (·["S"]?)

-- the uncorrupted reconstruction is the hand-derived history…
#guard match t1Reference with
  | some s => denseEq s ⟨[2, 3], #[1.0, 2.0, 4.0, 2.0, 6.0, 18.0]⟩
  | none   => false

-- …and dropping the last step's terms is caught as a VALUE difference, not a missing key.
#guard match corruptedT1 (fun ss => ss.map (fun s => match s with
    | .assign nm slots rhs =>
        if nm == stateLeafName "S" [2] then .assign nm slots { rhs with body := { terms := [] } }
        else .assign nm slots rhs
    | other => other)), t1Reference with
  | .ok bad, some good => !denseEq bad good
  | _, _ => false

-- Deleting a base leaf entirely is caught by the completeness check, which is what keeps the
-- `ofFn` zero default from absorbing a lost or misplaced leaf.
#guard match corruptedT1 (fun ss => ss.filter (fun s => s.lhsName != stateLeafName "S" [0])) with
  | .error _ => true
  | .ok _    => false

end LeanNCD.PropertyOracle

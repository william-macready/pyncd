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
      match evalScheduledF64 sched c.inputs, independentRun sched c.inputs with
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

-- Task 4 S-B corpus: every fixture must retain a source scatter inside its scan, and at least one
-- unrolled leaf program must retain a top-level scatter after scan elimination.
#guard scanScatterOracleCases.length == 5
#guard scanScatterOracleCases.all (fun c => c.sched.stmts.any (fun
  | .scan _ _ base recur _ => (base ++ recur).any (fun
      | .scatter .. => true
      | _ => false)
  | _ => false))
#guard scanScatterOracleCases.any (fun c =>
  match c.sched.stmts with
  | [sc] => match sc with
      | .scan .. =>
          match unrollScanNode c.sched.explicitSizes c.sched.decls sc with
          | .ok un => un.stmts.any (fun s => match s with | .scatter .. => true | _ => false)
          | .error _ => false
      | _ => false
  | _ => false)

/-- The five hand-built S-B isolation cases also compare the legacy scan evaluator with the
    independent oracle directly. Task 7's seven source-generated cases add the checked-plan leg in
    `DifferentialTest`; this smaller corpus remains pinned separately so its Task 4 assertions do not
    get silently replaced. -/
private def checkScanScatterLaw (c : ScanScatterOracleCase) : Option String :=
  match evalScheduledF64 c.sched c.inputs, independentRun c.sched c.inputs with
  | .error e, _ => some s!"{c.label}: legacy evaluator failed: {e.error}"
  | _, .error m => some s!"{c.label}: independent oracle failed: {m}"
  | .ok legacy, .ok indep =>
      match statesAgree s!"{c.label}: legacy versus independent oracle" ["S"] legacy.env indep with
      | some m => some m
      | none =>
          match legacy.env["S"]?, indep["S"]? with
          | some a, some b =>
              if denseEq a c.expected && denseEq b c.expected then none
              else some s!"{c.label}: a reference leg disagrees with the explicit expected state"
          | _, _ => some s!"{c.label}: a reference leg omitted state S"

#guard (scanScatterOracleCases.findSome? checkScanScatterLaw).isNone

-- `advScratch` (`ScanUnroll.lean`'s `ScanGeom` field) used to be populated by the `%nl` shape
-- `splitNonlins` manufactured for a nonlinear recurrence, in every `relu`-template generated case.
-- The logical-schedule flip (`papers/nonlinearity_split_pair_direct_lowering.md` §2.1) removed
-- `splitNonlins` from `compileToScheduled`, so `schedOfCase` no longer produces that shape at all —
-- assert the new reality (zero, not "at least one") so a future change that reintroduces
-- schedule-level splitting is caught here instead of by a later audit.
private def analyzedScans : List ScanGeom :=
  enumScanCases.filterMap (fun c => match schedOfCase c with
    | .error _ => none
    | .ok sched => match sched.stmts.find? (fun s => match s with | .scan .. => true | _ => false) with
        | none => none
        | some sc => (analyzeScan sched.explicitSizes sched.decls sc).toOption)
#guard analyzedScans.length == 17
#guard analyzedScans.all (fun g => g.advScratch.isEmpty)
#guard analyzedScans.all (fun g => g.scratch.isEmpty)

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
  let un ← unrollScanNode sched.explicitSizes sched.decls sc
  let un' := { un with stmts := f un.stmts }
  let leafSizes := un'.sizes.foldl (fun m (u, n) => m.insert u n) sched.explicitSizes
  let leafEnv ← match evalScheduled
      { sched with stmts := un'.stmts.map ScanStmt.plain
                   , decls := LeanNCD.Eval.ExplicitF64.explicitF64Decls
                       (sched.decls ++ un'.axisDecls ++ un'.decls) un'.stmts
                   , explicitSizes := leafSizes } (template1 3 false).inputs with
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

-- Deleting a base leaf entirely is not absorbed as a zero default. OBSERVED: the failure that fires
-- first is NOT `reconstructHistory`'s completeness check but the leaf evaluator's own
-- missing-input refusal (leaf `S_1` reads the deleted leaf, which is then an unknown tensor). The
-- guard pins that exact text, so it cannot be satisfied by an unrelated refusal (e.g. an
-- `unsupportedDtype` after the default storage flips to binary32).
#guard match corruptedT1 (fun ss => ss.filter (fun s => s.lhsName != stateLeafName "S" [0])) with
  | .error m => m == s!"corrupted leaf program failed: evalAssign: unknown tensor {stateLeafName "S" [0]}"
  | .ok _    => false

-- S3b T8: the SAME law on the tropical grid shapes with an UNWRITTEN state cell (`G[0,1]`, written by
-- neither the base nor the step). The legacy evaluator starts a tropical state at `0_K` of its sort
-- (-inf under max, +inf under min); the independent unrolling must therefore fill unreached
-- coordinates with the state's own `0_K` and merge base contributions with the state's own `⊕`.
-- The unrolling derives that sort from the statements' annotations (`ScanUnroll.localStateAgg`), not
-- from production's `scanStateAlgebra`, so agreement is not circular.
#guard tropicalUnwrittenScanCases.length == 2
#guard (tropicalUnwrittenScanCases.findSome? checkScanLaw).isNone
-- TEST-THE-TESTER: the shape really has an unwritten cell that only the state's `0_K` can fill
-- (a real-zero leaf gave `[2, 0, 5, 5]` / `[-2, 0, -5, -5]` here before the fix).
#guard (tropicalUnwrittenScanCases.map (fun c => match schedOfCase c with
  | .ok s => (evalScheduledF64 s c.inputs).toOption.bind (fun r => r.env["G"]?) |>.map (·.data)
  | .error _ => none)) ==
  [some #[2.0, -1.0 / 0.0, 5.0, 5.0], some #[-2.0, 1.0 / 0.0, -5.0, -5.0]]

-- S3b follow-up: the oracle's neutrality (`oracleNeutral`, stated from the plan's text in its own
-- shape) must agree with production's `Stmt.isSortNeutral`. The duality property and the unrolling
-- law both take the state's sort from `oracleNeutral`, so a defect in production's rule is only
-- visible if the two disagree somewhere: this is the place they are compared (the final-review M1
-- defect, a nonlinearity ignored by the production rule, was invisible for want of this check).
-- (1) over every statement of the scan corpora, program-level ones included;
private def corpusStmts : List Stmt :=
  (enumScanCases ++ tropicalUnwrittenScanCases).flatMap (fun c => c.base ++ c.recur ++ c.prog.stmts)
#guard corpusStmts.all (fun s => oracleNeutral s == s.isSortNeutral)
-- non-vacuity: the corpus holds both neutral statements (the bare-read bases) and non-neutral ones.
#guard corpusStmts.any oracleNeutral
#guard corpusStmts.any (fun s => !oracleNeutral s)
-- (2) over hand-built shapes the corpus lacks, each with the verdict the plan text dictates (pinned
-- literally here, so neither definition can drift together): one bare read with every axis on the
-- LHS is neutral; a contracted axis, a nonlinearity, a second factor, a second term, an Iverson
-- factor, or no factor at all is not. A scatter and a unary factor follow the
-- same rule.
private def nbJ : AxisSpec := ⟨"j", 9101, .real⟩
private def nbK : AxisSpec := ⟨"k", 9102, .real⟩
private def nbT : AxisSpec := ⟨"t", 9103, .nat⟩
private def nbStmt (ls : List LHSSlot) (terms : List (List Factor))
    (nl : Nonlin := .identity) (ag : AggOp := .sum) : Stmt :=
  .assign "S" ls { body := { terms := terms.map (fun fs => { factors := fs }) }, nonlin := nl, agg := ag }
private def nbScatter (fs : List Factor) : Stmt :=
  .scatter "S" [.affine (.scale 2 nbJ)] { body := { terms := [{ factors := fs }] }, nonlin := .identity }
private def nbRead (es : List IdxExpr) : Factor := .read "X" es
private def nbTruth : Factor := .iverson (.ieq (.embed (.const 0)) (.embed (.const 0)))
private def neutralShapes : List (Stmt × Bool) :=
  [ (nbStmt [.free nbJ, .iterAt nbT 0] [[nbRead [.axis nbJ]]], true)
  , (nbStmt [.free nbJ, .iterAt nbT 0] [[nbRead [.axis nbJ]]] .identity .max, true)
  , (nbStmt [.free nbJ, .iterAt nbT 0] [[nbRead [.shift nbJ 1]]], true)
  , (nbStmt [.free nbJ, .iterAt nbT 0] [[.unaryFn .exp "X" [.axis nbJ]]], true)
  , (nbStmt [.free nbJ, .iterAt nbT 0] [[nbRead []]], true)
  , (nbScatter [nbRead [.axis nbJ]], true)
  , (nbStmt [.free nbJ, .iterAt nbT 0] [[nbRead [.axis nbJ, .axis nbK]]], false)
  , (nbStmt [.free nbJ, .iterAt nbT 0] [[nbRead [.axis nbJ, .axis nbK]]] .identity .max, false)
  , (nbScatter [nbRead [.axis nbK]], false)
  , (nbStmt [.free nbJ, .iterAt nbT 0] [[nbRead [.axis nbJ]]] (.pointwise .relu), false)
  , (nbStmt [.free nbJ, .iterAt nbT 0] [[nbRead [.axis nbJ], nbRead [.axis nbJ]]], false)
  , (nbStmt [.free nbJ, .iterAt nbT 0] [[nbRead [.axis nbJ]], [nbRead [.axis nbJ]]], false)
  , (nbStmt [.free nbJ, .iterAt nbT 0] [[nbTruth]], false)
  , (nbStmt [.free nbJ, .iterAt nbT 0] [[]], false)
  , (nbStmt [.free nbJ, .iterAt nbT 0] [], false)
  -- an LHS slot over TWO axes writes one cell from many (j, k): those writes combine, so the
  -- statement is not neutral (it has its own sort), sum or max; a slot over ONE axis (scaled,
  -- shifted, constant offset) or one axis per slot places injectively and stays neutral.
  , (nbStmt [.affine (.affine 0 [(1, nbJ), (1, nbK)])] [[nbRead [.axis nbJ, .axis nbK]]], false)
  , (nbStmt [.affine (.affine 0 [(1, nbJ), (1, nbK)])] [[nbRead [.axis nbJ, .axis nbK]]] .identity .max, false)
  , (nbStmt [.affine (.affine 0 [(1, nbJ), (2, nbK)])] [[nbRead [.axis nbJ, .axis nbK]]], false)
  , (nbStmt [.affine (.affine 0 [(1, nbJ), (1, nbK)])] [[nbRead [.axis nbJ]]], false)
  , (nbStmt [.affine (.affine 1 [(2, nbJ)])] [[nbRead [.axis nbJ]]], true)
  , (nbStmt [.affine (.shift nbJ 1), .iterAt nbT 0] [[nbRead [.axis nbJ]]], true)
  , (nbStmt [.affine (.scale 2 nbJ), .affine (.const 3)] [[nbRead [.axis nbJ]]], true)
  , (nbStmt [.free nbJ, .free nbK] [[nbRead [.axis nbJ, .axis nbK]]], true)
  , (nbStmt [.free nbJ, .free nbK] [[nbRead [.axis nbJ, .axis nbK]]] .identity .max, true) ]
#guard neutralShapes.all (fun (s, expected) => oracleNeutral s == expected && s.isSortNeutral == expected)

-- S3b-ii T1 (D2): the state's sort rule, the part that depends on neutrality, is compared here too.
-- `localStateAgg` (a first-hit search in `ScanUnroll`, never calling the production vote helper) must
-- give the aggregation production's `scanStateAlgebra` selects, for every state of the scan corpora
-- and for hand-built states whose expected annotation is pinned LITERALLY (so the two cannot drift
-- together): an all-neutral state votes by its non-`sum` annotations; a state with a non-neutral
-- writer takes that writer's sort and the neutral writers abstain.
private def bareGeom (base recur : List Stmt) : ScanGeom :=
  { axes := [], ext := [], states := [], scratch := [], advScratch := [], base := base, recur := recur }
#guard (enumScanCases ++ tropicalUnwrittenScanCases).all (fun c =>
  (c.base ++ c.recur).all (fun s =>
    localStateAgg (bareGeom c.base c.recur) s.lhsName ==
      (scanStateAlgebra {} (c.base ++ c.recur) s.lhsName).stateAgg))
private def nbBase (ag : AggOp) : Stmt :=
  nbStmt [.free nbJ, .iterAt nbT 0] [[nbRead [.axis nbJ]]] .identity ag
private def nbStep (ag : AggOp) : Stmt :=
  nbStmt [.free nbJ, .iterNext nbT] [[nbRead [.axis nbJ]]] .identity ag
private def nbContracted (ag : AggOp) : Stmt :=
  nbStmt [.free nbJ, .iterNext nbT] [[nbRead [.axis nbJ, .axis nbK]]] .identity ag
private def stateVotes : List (List Stmt × List Stmt × AggOp) :=
  [ ([nbBase .max], [nbStep .max], .max)
  , ([nbBase .min], [nbStep .min], .min)
  , ([nbBase .sum], [nbStep .sum], .sum)
  , ([nbBase .sum], [nbStep .max], .max)
  , ([nbBase .min], [nbStep .sum], .min)
  , ([nbBase .max], [nbContracted .min], .min)
  , ([nbBase .min], [nbContracted .sum], .sum) ]
#guard stateVotes.all (fun (b, r, expected) =>
  localStateAgg (bareGeom b r) "S" == expected &&
  (scanStateAlgebra {} (b ++ r) "S").stateAgg == expected)

end LeanNCD.PropertyOracle

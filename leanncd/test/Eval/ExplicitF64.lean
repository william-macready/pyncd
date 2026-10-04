import LeanNCD.Eval.Entry
/-!
# Explicit-binary64 declarations for reference-evaluator tests

The reference evaluator (`TLProgram.eval`, `evalScheduled`, the direct `evalAssignDtyped*` /
`evalStmtSlice*` entries) is binary64-only: it refuses (`EvalError.unsupportedDtype`) any name
whose declaration commits it to `.float32` — and an UNDECLARED name commits to whatever the
pipeline's default storage is (`storageConstraintOfName?`). A test that wants to stay a binary64
regression gate therefore states binary64 EXPLICITLY for every name it leaves undeclared.

`explicitF64Decls decls stmts` appends a `tensor f64` declaration for each tensor name the
statements write or read (`stmtStorageNames`, the evaluator's own storage-name rule) that `decls`
does not already declare as a tensor-bearing name. It never rewrites an existing declaration: an
`f32`, `f64`, plain `tensor`/`linear`, or `predicate` declaration is left exactly as written, and
`axis`/`iter` declarations are untouched. (A plain `tensor`/`linear` takes the pipeline's default
storage; a binary64 gate re-spells it `tensor f64`/`linear f64` AT THE SOURCE, because after the
f32 default flip a plain declaration MEANS f32 and the helper must never turn it into f64.)
The added declaration's rank (and axes) come from the
name's use site — its first write's LHS slots, else its first read's index list — because the
pipeline rank-checks a declared name against `Decl.axisCount` (`checkReadRanksIn`); the axes'
identities otherwise carry no meaning (only `assignUIDs` reads them, by name, and they are names
the program already uses).

Three consequences to know:
* The added declarations change the ORDER in which `assignUIDs` first meets axis names, so the
  numeric UIDs it mints may change; which axes SHARE a UID cannot (UIDs are minted per distinct
  axis name).
* A name with no derivable axis (its use site has a position with no axis and the statements
  mention no axis anywhere, e.g. `Y[0] := X[0]`, or a name only a `recurMorphism` writes) stays
  UNDECLARED, so a later refusal stays loud rather than a wrong-rank declaration.
* The declared rank is the name's FIRST write's slot count and is then enforced on every access.
  A contrived undeclared name written twice with different slot counts, or a non-scatter LHS read at
  a rank other than its slot count, was accepted before and is rejected now. No test has such a
  program, so "semantics-neutral" holds for every program in the tests, not strictly for all
  programs.
-/
namespace LeanNCD.Eval.ExplicitF64
open LeanNCD

/-- The axes an index expression mentions (none for a constant). -/
private def idxAxes : IdxExpr → List AxisSpec
  | .axis a | .scale _ a | .shift a _ => [a]
  | .affine _ cs => cs.map (·.2)
  | .const _ => []

/-- The axes an LHS slot mentions. -/
private def slotAxes : LHSSlot → List AxisSpec
  | .free a | .freeNorm a | .iterAt a _ | .iterNext a => [a]
  | .affine e => idxAxes e

/-- One axis per position, taken from that position's own axes, else from any axis the same
    use site mentions, else from any axis the statements mention (a constant index such as
    `Y[0]` names no axis; only the COUNT is checked, so any program axis serves). `none` only if
    no axis exists at all (then the name is left undeclared, so a later refusal stays loud
    rather than a wrong-rank declaration). -/
private def positionAxes (fallback : Option AxisSpec) (perPos : List (List AxisSpec)) :
    Option (List AxisSpec) :=
  let any := perPos.flatten.head? <|> fallback
  perPos.mapM fun as => as.head? <|> any

/-- Every axis an LHS slot list or read index list of the statements mentions. -/
private def stmtAxes (stmts : List Stmt) : List AxisSpec :=
  stmts.flatMap fun s => s.slots.flatMap slotAxes ++
    s.readFactors.flatMap fun (_, es) => es.flatMap idxAxes

/-- The use-site axis list of `nm`: its first write's LHS slots, else its first read. -/
private def useSiteAxes (stmts : List Stmt) (nm : String) : Option (List AxisSpec) :=
  let write := stmts.findSome? fun s => match s with
    | .assign n ls _ | .scatter n ls _ _ => if n == nm then some (ls.map slotAxes) else none
    | .recurMorphism _ _ _ => none
  let read := (stmts.flatMap Stmt.readFactors).findSome? fun (n, es) =>
    if n == nm then some (es.map idxAxes) else none
  (write <|> read).bind (positionAxes (stmtAxes stmts).head?)

/-- `decls` plus a `tensor f64` declaration for every UNDECLARED storage name of `stmts`.
    If `decls` itself is malformed (`buildDeclEnv` rejects it), it is returned unchanged so the
    evaluator reports that error itself. -/
def explicitF64Decls (decls : List Decl) (stmts : List Stmt) : List Decl :=
  match buildDeclEnv decls with
  | .error _ => decls
  | .ok env =>
      let names := (stmts.flatMap stmtStorageNames).eraseDups.filter (!env.contains ·)
      decls ++ names.filterMap fun nm =>
        (useSiteAxes stmts nm).map (Decl.typedTensor .f64 nm)

/-- `p` with every undeclared tensor name declared `tensor f64` (`explicitF64Decls`). -/
def _root_.LeanNCD.TLProgram.explicitF64 (p : TLProgram) : TLProgram :=
  { p with decls := explicitF64Decls p.decls p.stmts }

/-! ### The direct reference-evaluator entries, with the same explicit-`f64` declarations

One wrapper per direct entry: each declares `f64` for exactly the statement(s) that entry's own
storage refusal inspects, then calls the entry unchanged. -/

/-- `evalPlain` with `explicitF64Decls decls [s]`. -/
def _root_.LeanNCD.Eval.evalPlainF64 (decls : List Decl) (env : Std.HashMap String DenseTensor)
    (sizes : Std.HashMap UID Nat) (s : Stmt) : Except EvalError (String × DenseTensor) :=
  evalPlain (explicitF64Decls decls [s]) env sizes s

/-- `evalStmtSliceSeeded` with `explicitF64Decls decls [s]`. -/
def _root_.LeanNCD.Eval.evalStmtSliceSeededF64 (decls : List Decl)
    (env : Std.HashMap String DenseTensor) (sizes : Std.HashMap UID Nat)
    (seed : Std.HashMap UID Int) (s : Stmt) : Except EvalError (String × DenseTensor) :=
  evalStmtSliceSeeded (explicitF64Decls decls [s]) env sizes seed s

/-- `evalScan` with `explicitF64Decls` over the scan node's own source statements. -/
def _root_.LeanNCD.Eval.evalScanF64 (decls : List Decl) (env : Std.HashMap String DenseTensor)
    (sizes : Std.HashMap UID Nat) (ss : ScanStmt) :
    Except EvalError (List (String × DenseTensor)) :=
  evalScan (explicitF64Decls decls ss.sourceStmts) env sizes ss

/-- `evalAssignDtypedSeeded` with `explicitF64Decls` over the assignment it evaluates. -/
def _root_.LeanNCD.Eval.evalAssignDtypedSeededF64 (decls : List Decl)
    (env : Std.HashMap String DenseTensor) (sizes : Std.HashMap UID Nat)
    (seed : Std.HashMap UID Int) (nm : String) (slots : List LHSSlot) (rhs : RHSExpr) :
    Except EvalError (String × DenseTensor) :=
  evalAssignDtypedSeeded (explicitF64Decls decls [.assign nm slots rhs]) env sizes seed nm slots rhs

/-- `evalAssignDtyped` with `explicitF64Decls` over the assignment it evaluates. -/
def _root_.LeanNCD.Eval.evalAssignDtypedF64 (decls : List Decl)
    (env : Std.HashMap String DenseTensor) (sizes : Std.HashMap UID Nat)
    (nm : String) (slots : List LHSSlot) (rhs : RHSExpr) :
    Except EvalError (String × DenseTensor) :=
  evalAssignDtyped (explicitF64Decls decls [.assign nm slots rhs]) env sizes nm slots rhs

/-- `evalScheduled` with `explicitF64Decls` over every source statement of the schedule. -/
def _root_.LeanNCD.Eval.evalScheduledF64 (sched : ScheduledProgram)
    (inputs : Std.HashMap String DenseTensor) : Except EvalFailure EvalReport :=
  evalScheduled { sched with
    decls := explicitF64Decls sched.decls (sched.stmts.flatMap ScanStmt.sourceStmts) } inputs

end LeanNCD.Eval.ExplicitF64

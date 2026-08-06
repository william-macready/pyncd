import LeanNCD.DSL.Ast
import LeanNCD.DSL.Pipeline.Types
import LeanNCD.Eval.Plan.Error

/-!
# Wave C source compiler: capability preflight (C4)

Ports C0's already-verified classification logic (`PlanContract.classify*`,
`test/Eval/Plan/ContractTest.lean`) from test-only `Classification`-valued classifiers into a real
production entry point that throws `CapabilityError`. No `PreparedPlan`, slot allocation, or shape
inference here — this file holds only capability preflight; Task 2 grows it.
-/

namespace LeanNCD.Eval.Plan

/-- Axis declarations (`.axis`, `.iter`) are structurally accepted regardless of use — rejection for
    `freeNorm`/scan usage happens at the `LHSSlot`/`ScanStmt` check below, not at the declaring
    axis. -/
def checkDecl : Decl → Except CapabilityError Unit
  | .tensor ..    => pure ()
  | .linear ..    => pure ()
  | .predicate n _ => throw (.booleanOutput n)
  | .axis ..      => pure ()
  | .iter ..      => pure ()

def checkLHSSlot (stmtName : String) : LHSSlot → Except CapabilityError Unit
  | .free _     => pure ()
  | .freeNorm a => throw (.unsupportedLhsSlot s!"{stmtName}: freeNorm {a.name}")
  | .iterAt a _ => throw (.unsupportedLhsSlot s!"{stmtName}: iterAt {a.name}")
  | .iterNext a => throw (.unsupportedLhsSlot s!"{stmtName}: iterNext {a.name}")
  | .affine _   => throw (.scatterOrAffineLhs s!"{stmtName}: affine LHS slot")

def checkFactor (stmtName : String) : Factor → Except CapabilityError Unit
  | .read ..       => pure ()
  | .iverson _     => throw (.maskOrPredicate s!"{stmtName}: iverson factor")
  | .unaryFn _ n _ => throw (.unaryFactor s!"{stmtName}: unary function on {n}")

def checkNonlin (stmtName : String) : Nonlin → Except CapabilityError Unit
  | .identity    => pure ()
  | .pointwise _ => throw (.unsupportedNonlin s!"{stmtName}: pointwise nonlinearity")
  | .axiswise .. => throw (.unsupportedNonlin s!"{stmtName}: axiswise nonlinearity")

def checkAggOp (stmtName : String) : AggOp → Except CapabilityError Unit
  | .sum => pure ()
  | .max => throw (.unsupportedAgg s!"{stmtName}: max aggregation")
  | .min => throw (.unsupportedAgg s!"{stmtName}: min aggregation")

/-- One `Stmt`'s capability check. Sub-construct order (LHS slots, then `agg`, then `nonlin`, then
    factors) mirrors C0's `classifyStmt` (`test/Eval/Plan/ContractTest.lean`) exactly — the first
    rejected sub-construct determines the reported category. `scatter`/`recurMorphism` are rejected
    outright, without inspecting their slots/payload, matching C0's `classifyStmt` too. -/
def checkStmt : Stmt → Except CapabilityError Unit
  | .assign nm slots rhs => do
      for s in slots do checkLHSSlot nm s
      checkAggOp nm rhs.agg
      checkNonlin nm rhs.nonlin
      for t in rhs.body.terms do
        for f in t.factors do checkFactor nm f
  | .scatter nm .. => throw (.scatterOrAffineLhs nm)
  | .recurMorphism nm .. => throw (.recurrenceOrCallback nm)

def checkScanStmt : ScanStmt → Except CapabilityError Unit
  | .plain s      => checkStmt s
  | .scan nm ..   => throw (.scanNode nm)
  | .scanPre nm .. => throw (.scanNode nm)

/-- Capability preflight over a whole `ScheduledProgram`: decls in order, then stmts in order, first
    failure wins. `unsupportedDtype`/`dynamicShape` are never thrown below — see `CapabilityError`'s
    doc comment for why they are structurally unreachable from this entry point specifically. -/
def capabilityPreflight (sched : ScheduledProgram) : Except CapabilityError Unit := do
  for d in sched.decls do checkDecl d
  for s in sched.stmts do checkScanStmt s

end LeanNCD.Eval.Plan

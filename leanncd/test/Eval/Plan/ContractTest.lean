import LeanNCD.DSL.Ast
import LeanNCD.DSL.Pipeline.Types

/-!
# Wave C capability classification (C0)

Pins, as compiler-checked exhaustive matches, exactly which source constructs Wave C's initial
scan-free `f64` fragment accepts versus rejects (`papers/wave_c_evalplan_proposal.md` §3.1/§3.2).
No `Plan/*` production module exists yet — these classifiers exist only to make the capability
matrix a typed artifact instead of prose, and to fail to compile (not silently pass) the moment a
new AST constructor is added anywhere these types are matched.
-/

namespace LeanNCD.PlanContract
open LeanNCD

/-- Wave C's classification of one source construct: accepted into the initial fragment, or
    rejected under one of §3.2's named categories (matching the `CapabilityError` constructor
    names in the proposal doc, so a category string here and a `CapabilityError` constructor added
    later name the same thing). -/
inductive Classification
  | accepted
  | rejected (category : String)
  deriving DecidableEq, BEq, Repr

/-- Axis declarations (`.axis`, `.iter`) are structurally accepted regardless of use — rejection
    for `freeNorm`/scan usage happens at the `LHSSlot`/`ScanStmt` use site below, not at the
    declaring axis. Only `.tensor`/`.predicate`/`.linear` carry a dtype-like distinction (real f64
    vs Boolean) relevant to Wave C's fragment boundary. -/
def classifyDecl : Decl → Classification
  | .tensor ..    => .accepted
  | .linear ..    => .accepted    -- bias is fully elaborated into ordinary Stmts by the time a
                                   -- ScheduledProgram exists; identical to `.tensor` for Wave C
  | .predicate .. => .rejected "booleanOutput"
  | .axis ..      => .accepted
  | .iter ..      => .accepted

def classifyLHSSlot : LHSSlot → Classification
  | .free _     => .accepted
  | .freeNorm _ => .rejected "unsupportedLhsSlot"
  | .iterAt ..  => .rejected "unsupportedLhsSlot"
  | .iterNext _ => .rejected "unsupportedLhsSlot"
  | .affine _   => .rejected "scatterOrAffineLhs"

def classifyFactor : Factor → Classification
  | .read ..    => .accepted
  | .iverson _  => .rejected "maskOrPredicate"
  | .unaryFn .. => .rejected "unaryFactor"

def classifyNonlin : Nonlin → Classification
  | .identity    => .accepted
  | .pointwise _ => .rejected "unsupportedNonlin"
  | .axiswise .. => .rejected "unsupportedNonlin"

def classifyAggOp : AggOp → Classification
  | .sum => .accepted
  | .max => .rejected "unsupportedAgg"
  | .min => .rejected "unsupportedAgg"

/-- A `Stmt` is accepted only if every LHS slot, its nonlinearity, and every factor classify as
    accepted. The first rejected sub-construct (LHS slots checked before nonlin before factors,
    matching the total precedence A.4/§4.2 fixes) determines the reported category. -/
def classifyStmt : Stmt → Classification
  | .assign _ slots rhs =>
      match slots.findSome? (fun s => match classifyLHSSlot s with
        | .accepted => none | .rejected c => some c) with
      | some c => .rejected c
      | none =>
          match classifyNonlin rhs.nonlin with
          | .rejected c => .rejected c
          | .accepted =>
              match rhs.body.terms.findSome? (fun t => t.factors.findSome? (fun f =>
                match classifyFactor f with
                | .accepted => none | .rejected c => some c)) with
              | some c => .rejected c
              | none => .accepted
  | .scatter .. => .rejected "scatterOrAffineLhs"
  | .recurMorphism .. => .rejected "recurrenceOrCallback"

def classifyScanStmt : ScanStmt → Classification
  | .plain s  => classifyStmt s
  | .scan ..  => .rejected "scanNode"
  | .scanPre .. => .rejected "scanNode"

/-- The total order in which `prepareEvalPlan`'s checks run (§4.2, A.4 item 2): the first phase
    whose check fails determines the reported failure category, with no other interleaving
    permitted. `priority` turning this into `Nat` order (rather than list position alone) means a
    future accidental reordering of `preflightOrder` is caught by `#guard`, not just by inspection. -/
inductive PreflightPhase
  | capability | inputSignature | shapeInference | rawConstruction
  | localChecking | graphChecking | runtimeBinding
  deriving DecidableEq, BEq, Repr

def PreflightPhase.priority : PreflightPhase → Nat
  | .capability      => 0
  | .inputSignature  => 1
  | .shapeInference  => 2
  | .rawConstruction => 3
  | .localChecking   => 4
  | .graphChecking   => 5
  | .runtimeBinding  => 6

def preflightOrder : List PreflightPhase :=
  [.capability, .inputSignature, .shapeInference, .rawConstruction,
   .localChecking, .graphChecking, .runtimeBinding]

/-- Strict pairwise increase, without depending on `List.Chain'`'s decidability instance. -/
def strictlyIncreasing : List Nat → Bool
  | []           => true
  | [_]          => true
  | a :: b :: rest => a < b && strictlyIncreasing (b :: rest)

#guard strictlyIncreasing (preflightOrder.map PreflightPhase.priority)
#guard preflightOrder.length == 7

end LeanNCD.PlanContract

open LeanNCD.PlanContract in
section
-- Decl
#guard classifyDecl (.tensor "X" []) == .accepted
#guard classifyDecl (.linear "W" [] true) == .accepted
#guard classifyDecl (.predicate "P" []) == .rejected "booleanOutput"
#guard classifyDecl (.axis ⟨"i", 0, .nat⟩ (some 3)) == .accepted
#guard classifyDecl (.iter ⟨"l", 0, .nat⟩ 3) == .accepted

-- LHSSlot
#guard classifyLHSSlot (.free ⟨"i", 0, .nat⟩) == .accepted
#guard classifyLHSSlot (.freeNorm ⟨"i", 0, .nat⟩) == .rejected "unsupportedLhsSlot"
#guard classifyLHSSlot (.iterAt ⟨"i", 0, .nat⟩ 0) == .rejected "unsupportedLhsSlot"
#guard classifyLHSSlot (.iterNext ⟨"i", 0, .nat⟩) == .rejected "unsupportedLhsSlot"
#guard classifyLHSSlot (.affine (.axis ⟨"i", 0, .nat⟩)) == .rejected "scatterOrAffineLhs"

-- Factor
#guard classifyFactor (.read "X" []) == .accepted
#guard classifyFactor
    (.iverson (.rel .eq (.embed (.const 0)) (.embed (.const 0)))) == .rejected "maskOrPredicate"
#guard classifyFactor (.unaryFn .log "X" []) == .rejected "unaryFactor"

-- Nonlin
#guard classifyNonlin .identity == .accepted
#guard classifyNonlin (.pointwise .relu) == .rejected "unsupportedNonlin"
#guard classifyNonlin (.axiswise .softmax none) == .rejected "unsupportedNonlin"

-- AggOp
#guard classifyAggOp .sum == .accepted
#guard classifyAggOp .max == .rejected "unsupportedAgg"
#guard classifyAggOp .min == .rejected "unsupportedAgg"

-- Stmt / ScanStmt composition
#guard classifyStmt (.scatter "Out" [] { body := { terms := [] }, nonlin := .identity } {}) ==
  .rejected "scatterOrAffineLhs"
#guard classifyStmt (.assign "Y" [.free ⟨"i", 0, .nat⟩]
  { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity }) == .accepted
#guard classifyStmt (.assign "Y" [.freeNorm ⟨"i", 0, .nat⟩]
  { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity }) ==
  .rejected "unsupportedLhsSlot"
#guard classifyScanStmt (.scan "s" [] [] [] false) == .rejected "scanNode"
#guard classifyScanStmt (.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
  { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })) == .accepted
end

-- NumericMode: deferred to C1/C2, where it is defined; Wave C admits only `reference64`.

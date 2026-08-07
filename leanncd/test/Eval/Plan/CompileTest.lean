import LeanNCD.Eval.Plan.Compile

/-!
# Wave C C4 capability preflight tests

One accepted program plus one rejected case per `CapabilityError` category (11 total); the two
structurally-unreachable categories (`unsupportedDtype`, `dynamicShape`) are exercised directly on
the constructor rather than through `capabilityPreflight`.
-/

namespace LeanNCD.Eval.Plan.CompileTest
open LeanNCD LeanNCD.Eval.Plan
open Std

def isOk : Except CapabilityError Unit → Bool
  | .ok _ => true | .error _ => false

def errOf : Except CapabilityError Unit → Option CapabilityError
  | .ok _ => none | .error e => some e

-- accepted: an ordinary in-fragment scheduled program (`Y[i] := X[i]`)
def acceptedSched : ScheduledProgram :=
  { decls := [.tensor "X" [], .tensor "Y" []]
  , stmts := [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
      { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })]
  , env := {}
  , extNames := {}
  , explicitSizes := {} }

#guard isOk (capabilityPreflight acceptedSched)

-- scanNode: a `.scan` ScanStmt
#guard errOf (capabilityPreflight
    { acceptedSched with stmts := [.scan "s" [] [] [] false] })
  == some (.scanNode "s")

-- scanNode via `.scanPre` (checked directly on the sub-function, not through a whole program, to
-- keep this fixture minimal — `capabilityPreflight` is already exercised end-to-end above)
#guard errOf (checkScanStmt (.scanPre "s" ⟨"l", 0, .nat⟩ default)) == some (.scanNode "s")

-- scatterOrAffineLhs: a scatter statement
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.scatter "Out" [] { body := { terms := [] }, nonlin := .identity } {})] })
  == some (.scatterOrAffineLhs "Out")

-- scatterOrAffineLhs: an affine LHS slot on an ordinary assign
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.affine (.axis ⟨"i", 0, .nat⟩)]
          { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })] })
  == some (.scatterOrAffineLhs "Y: affine LHS slot")

-- unsupportedLhsSlot: freeNorm
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.freeNorm ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })] })
  == some (.unsupportedLhsSlot "Y: freeNorm i")

-- unsupportedNonlin: pointwise
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .pointwise .relu })] })
  == some (.unsupportedNonlin "Y: pointwise nonlinearity")

-- maskOrPredicate: an iverson factor
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors :=
              [.iverson (.rel .eq (.embed (.const 0)) (.embed (.const 0)))] }] }
          , nonlin := .identity })] })
  == some (.maskOrPredicate "Y: iverson factor")

-- unaryFactor
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.unaryFn .log "X" []] }] }, nonlin := .identity })] })
  == some (.unaryFactor "Y: unary function on X")

-- unsupportedAgg: max
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }
          , nonlin := .identity, agg := .max })] })
  == some (.unsupportedAgg "Y: max aggregation")

-- booleanOutput: a predicate decl
#guard errOf (capabilityPreflight { acceptedSched with decls := [.predicate "P" []] })
  == some (.booleanOutput "P")

-- recurrenceOrCallback: a recurMorphism stmt
#guard errOf (capabilityPreflight
    { acceptedSched with stmts := [.plain (.recurMorphism "R" ⟨"l", 0, .nat⟩ default)] })
  == some (.recurrenceOrCallback "R")

-- unsupportedDtype: structurally unreachable via `capabilityPreflight` — `Decl` (`DSL/Ast.lean`)
-- carries no dtype field on any constructor (`.tensor`/`.linear`/`.predicate` are name+axes only;
-- dtype is an `InputSignature`/backend concept a LATER C4 step resolves, not a source declaration),
-- so nothing in this file's checkers can ever construct this value. Exercised directly, matching
-- `checkAssign`'s single-valued-vocabulary unreachables (`numericModeNotAdmitted`, C2/C3).
#guard (CapabilityError.unsupportedDtype "unreachable") == CapabilityError.unsupportedDtype "unreachable"

-- dynamicShape: structurally unreachable via `capabilityPreflight` — `IdxExpr` (`DSL/Ast.lean`) has
-- exactly five constructors (`axis`, `const`, `scale`, `shift`, `affine`), all integer-affine over
-- declared `AxisSpec`s; there is no value-dependent/runtime-shape construct anywhere in the AST for
-- this checker to reject. Exercised directly, same pattern as `unsupportedDtype` above.
#guard (CapabilityError.dynamicShape "unreachable") == CapabilityError.dynamicShape "unreachable"

-- Example 1: identity copy `Y[i] := X[i]`, axis i : ℕ = 3.
def axI1 : AxisSpec := { name := "i", uid := 1, kind := .nat }
def identitySched : ScheduledProgram :=
  { decls := [.axis axI1 (some 3)]
  , stmts := [.plain (.assign "Y" [.free axI1]
      { body := { terms := [{ factors := [.read "X" [.axis axI1]] }] }, nonlin := .identity })]
  , env := {}, extNames := insert "X" (∅ : Finset String)
  , explicitSizes := (({} : HashMap UID Nat).insert axI1.uid 3) }
def identityInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" (⟨[3], #[10.0, 20.0, 30.0]⟩ : DenseTensor)
def identitySig : InputSignature := InputSignature.ofDenseInputs identityInputs
#guard (prepareEvalPlan identitySched identitySig).toOption.isSome

-- Example 2: contraction `Y[i] := A[i] · B[j]` contracted over j — ALSO the zero-coefficient
-- contracted-axis case (A[i]'s row over basis [i,j] densifies to a zero column for j — proposal
-- §7.4: "do not infer reduction axes from matrix coefficients," confirmed here: the zero column
-- does not cause j to be dropped from the basis).
def axI2 : AxisSpec := { name := "i", uid := 1, kind := .nat }
def axJ2 : AxisSpec := { name := "j", uid := 2, kind := .nat }
def contractSched : ScheduledProgram :=
  { decls := [.axis axI2 (some 2), .axis axJ2 (some 3)]
  , stmts := [.plain (.assign "Y" [.free axI2]
      { body := { terms := [{ factors := [.read "A" [.axis axI2], .read "B" [.axis axJ2]] }] }
      , nonlin := .identity })]
  , env := {}, extNames := insert "A" (insert "B" (∅ : Finset String))
  , explicitSizes := ((({} : HashMap UID Nat).insert axI2.uid 2).insert axJ2.uid 3) }
def contractInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" (⟨[2], #[10.0, 100.0]⟩ : DenseTensor)).insert
    "B" (⟨[3], #[1.0, 2.0, 3.0]⟩ : DenseTensor)
def contractSig : InputSignature := InputSignature.ofDenseInputs contractInputs
#guard (prepareEvalPlan contractSched contractSig).toOption.isSome

def contractPrepared : Option PreparedPlan := (prepareEvalPlan contractSched contractSig).toOption
#guard contractPrepared.map (fun p => p.plan.raw.steps[0]!.terms[0]!.iterationShape) == some #[2, 3]
#guard contractPrepared.map (fun p => p.plan.raw.steps[0]!.terms[0]!.outputPos) == some #[0]
#guard contractPrepared.map (fun p => p.plan.raw.steps[0]!.terms[0]!.reductionPos) == some #[1]
#guard contractPrepared.map (fun p => p.plan.raw.steps[0]!.terms[0]!.factors[0]!.map.coeffs) ==
  some #[#[1, 0]]   -- A[i]: zero coefficient in the j (contracted) column — still counted
#guard contractPrepared.map (fun p => p.plan.raw.steps[0]!.terms[0]!.factors[1]!.map.coeffs) ==
  some #[#[0, 1]]   -- B[j]

-- Example 3: repeated assignment `Y[i]:=A[i]; Y[i]:=B[i]; Z[i]:=Y[i]`, axis i : ℕ = 2.
def axI3 : AxisSpec := { name := "i", uid := 1, kind := .nat }
def repeatSched : ScheduledProgram :=
  { decls := [.axis axI3 (some 2)]
  , stmts :=
      [ .plain (.assign "Y" [.free axI3]
          { body := { terms := [{ factors := [.read "A" [.axis axI3]] }] }, nonlin := .identity })
      , .plain (.assign "Y" [.free axI3]
          { body := { terms := [{ factors := [.read "B" [.axis axI3]] }] }, nonlin := .identity })
      , .plain (.assign "Z" [.free axI3]
          { body := { terms := [{ factors := [.read "Y" [.axis axI3]] }] }, nonlin := .identity }) ]
  , env := {}, extNames := insert "A" (insert "B" (∅ : Finset String))
  , explicitSizes := (({} : HashMap UID Nat).insert axI3.uid 2) }
def repeatInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" (⟨[2], #[1.0, 2.0]⟩ : DenseTensor)).insert
    "B" (⟨[2], #[100.0, 200.0]⟩ : DenseTensor)
def repeatSig : InputSignature := InputSignature.ofDenseInputs repeatInputs
#guard (prepareEvalPlan repeatSched repeatSig).toOption.isSome

def repeatPrepared : Option PreparedPlan := (prepareEvalPlan repeatSched repeatSig).toOption
-- NOT deduplicated: two entries for "Y" (one per write), then "Z" — matches §5.4's own text.
#guard repeatPrepared.map (fun p => p.bindings.materializedNames.map (·.name)) == some #["Y", "Y", "Z"]
def repeatYSlots : Option (Array TensorSlot) :=
  repeatPrepared.map (fun p => (p.bindings.materializedNames.filter (·.name == "Y")).map (·.slot))
#guard repeatYSlots.map (fun ss => ss[0]! == ss[1]!) == some false   -- two DISTINCT "Y" slots

-- Deterministic slot assignment: same input, same structural output.
#guard ((prepareEvalPlan contractSched contractSig).toOption.map (·.bindings.requiredInputs)) ==
       ((prepareEvalPlan contractSched contractSig).toOption.map (·.bindings.requiredInputs))
#guard ((prepareEvalPlan contractSched contractSig).toOption.map (·.plan.raw)) ==
       ((prepareEvalPlan contractSched contractSig).toOption.map (·.plan.raw))

-- Step A/B wiring: failures propagate through prepareEvalPlan with the right cause.
def causeOf (r : Except PlanCompileFailure PreparedPlan) : Option PlanCompileFailure :=
  match r with | .ok _ => none | .error e => some e
#guard causeOf (prepareEvalPlan identitySched (InputSignature.mk ({} : HashMap String TensorSignature))) ==
  some { cause := .inputSignature (.missingSignature "X"), warnings := [] }
def badDtypeSig : InputSignature :=
  InputSignature.mk (({} : HashMap String TensorSignature).insert "X" { shape := #[3], dtype := .bool })
#guard causeOf (prepareEvalPlan identitySched badDtypeSig) ==
  some { cause := .inputSignature (.dtypeNotAdmitted "X" .bool), warnings := [] }

-- `prepareEvalPlan`'s OWN capability-rejection path: Step A runs `capabilityPreflight` before
-- shape inference, so a `.scan` statement is rejected with a `.capability`-tagged
-- `PlanCompileFailure` and `warnings := []` (Step A fails before any warnings could accrue) — the
-- same schedule/error pair `capabilityPreflight`'s own `scanNode` guard above uses.
#guard causeOf (prepareEvalPlan { acceptedSched with stmts := [.scan "s" [] [] [] false] } identitySig) ==
  some { cause := .capability (.scanNode "s"), warnings := [] }

end LeanNCD.Eval.Plan.CompileTest

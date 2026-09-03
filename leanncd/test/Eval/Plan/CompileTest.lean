import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Compile

/-!
# Wave C C4 capability preflight tests

One baseline accepted program (`Y[i] := X[i]`) plus rejected cases for every remaining
`CapabilityError` category (9 top-level rejection categories now): 2 cases for `unsupportedLhsSlot`
(`iterAt`/`iterNext` — `.freeNorm` at top level is now ADMITTED, Thread 4, so it is no longer one of
these rejection cases; see the accepted fixture below instead), 2 for `unsupportedNonlin`
(pointwise/axiswise, now specifically SCAN-BLOCK cases — Thread 4 admits both at top level too), and
one each for the remaining categories. `unsupportedAgg` (max/min) is likewise no longer a rejection
category — the max/min-aggregation thread admits both (they compile to the tropical algebras), so its
two donor programs are now accepted-case fixtures below, not rejections. Plus three Thread-4
accepted-case fixtures pinning what preflight now admits at top level (`.freeNorm`, `.pointwise`,
unmasked `.axiswise`) that Wave C used to reject.
the two structurally-unreachable categories (`unsupportedDtype`, `dynamicShape`) are exercised
directly on the constructor rather than through `capabilityPreflight`. Also covers `prepareEvalPlan`
end-to-end on accepted programs — an identity copy, a zero-coefficient contraction, and a
repeated-assignment (no-dedup) case — every `PlanCompileCause` variant reached through the real
pipeline (`inputSignature`, `capability`, `shape`), and non-empty preparation warnings surviving a
later `shape` failure unchanged.
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

-- noAdvancingAxis: a `.scan` ScanStmt declaring no advancing axis. (Wave C rejected EVERY `.scan`
-- here with `scanNode`; F4 admits well-formed ones, so this fixture now pins the empty-axis
-- rejection specifically — see `Eval.Plan.ScanCompileTest` for the admitted cases.)
#guard errOf (capabilityPreflight
    { acceptedSched with stmts := [.scan "s" [] [] [] false] })
  == some (.noAdvancingAxis "s")

-- recurrenceOrCallback via `.scanPre` (checked directly on the sub-function, not through a whole
-- program, to keep this fixture minimal — `capabilityPreflight` is already exercised end-to-end
-- above). Reuses the constructor `Stmt.recurMorphism` already gets: a `.scanPre`'s payload IS a
-- pre-built step morphism (proposal §5.2 / plan §4.1), not a distinct capability.
#guard errOf (checkScanStmt (.scanPre "s" ⟨"l", 0, .nat⟩ default)) == some (.recurrenceOrCallback "s")

-- `scanNode` has no producer left in `Compile.lean` (F4 replaced both of its throw sites), but the
-- constructor is retained on `CapabilityError` — deleting a shipped closed-family constructor is
-- itself a semantic version change. Exercised directly, same pattern as `unsupportedDtype` below.
#guard (CapabilityError.scanNode "retained") == CapabilityError.scanNode "retained"

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

-- `.freeNorm` at top level (Thread 4): structurally ADMITTED now, unlike Wave C — `checkLHSSlot`
-- relaxes it to `pure ()`, same as `.free`. Whether this particular marker agrees with the
-- statement's own `Nonlin` (here `.identity`, so it does not) is NOT this preflight's concern —
-- that's `resolveNonlinAxis`'s compile-tier job (see `NonlinCompileTest.lean`'s
-- `unmarkedReductionAxis` fixture for the same program rejected one phase later).
#guard isOk (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.freeNorm ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })] })

-- unsupportedLhsSlot: iterAt
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.iterAt ⟨"i", 0, .nat⟩ 0]
          { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })] })
  == some (.unsupportedLhsSlot "Y: iterAt i")

-- unsupportedLhsSlot: iterNext
#guard errOf (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.iterNext ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })] })
  == some (.unsupportedLhsSlot "Y: iterNext i")

-- `.pointwise` at top level (Thread 4): structurally ADMITTED now — `checkNonlinTopLevel` (the
-- `.plain`-statement admission) accepts every `Nonlin`, unlike `checkNonlinScanBlock` below.
#guard isOk (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .pointwise .relu })] })

-- `.axiswise` (mask `none`) at top level (Thread 4): structurally ADMITTED now, same as pointwise
-- above. A masked `.axiswise` is likewise admitted at THIS tier; Slice 5.3 now lowers it through
-- `lowerMaskPredicate` (it is no longer a compile-tier rejection).
#guard isOk (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }
          , nonlin := .axiswise .softmax none })] })

-- scan-block `.pointwise`/`.axiswise` are now ADMITTED at preflight (Thread 4 Task 4), identically
-- to the top-level `.plain` cases above: `compileScan` compiles a nonlinear base/recurrence
-- statement into the same `.assign → .pointwise`/`.axiswise` block-step chain. A masked `.axiswise`
-- is likewise admitted here and (Slice 5.3) lowered via `lowerMaskPredicate`, not rejected.
#guard isOk (capabilityPreflight
    { acceptedSched with stmts :=
        [.scan "s" [⟨"l", 5, .nat⟩] [] [.assign "Y" [.iterNext ⟨"l", 5, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .pointwise .relu }]
          false] })

#guard isOk (capabilityPreflight
    { acceptedSched with stmts :=
        [.scan "s" [⟨"l", 5, .nat⟩] [] [.assign "Y" [.iterNext ⟨"l", 5, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }
          , nonlin := .axiswise .softmax none }]
          false] })

-- maskOrPredicate: an iverson factor is now ADMITTED (the predicate/mask parity thread lowers it to
-- a positional `PosBoolExpr` factor via `lowerFactorPredicate`) — preflight returns none, so this
-- donor program becomes an accepted-case fixture rather than a rejection, exactly like the
-- `unaryFactor` and max/min conversions above. Its executing/value coverage is the differential
-- fixtures in `DifferentialTest.lean` (pure-Iverson identity and the reduction-order cases).
#guard isOk (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors :=
              [.iverson (.rel .eq (.embed (.const 0)) (.embed (.const 0)))] }] }
          , nonlin := .identity })] })

-- unaryFactor: log/exp/… are now ADMITTED (they lower to a unary-carrying `ReadPlan` factor) —
-- preflight returns none, so this donor program becomes an accepted-case fixture rather than a
-- rejection.
#guard isOk (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.unaryFn .log "X" []] }] }, nonlin := .identity })] })

-- unsupportedAgg: max/min are now ADMITTED (they compile to the tropical algebras) — preflight
-- returns none, so these two donor programs become accepted-case fixtures rather than rejections.
#guard isOk (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }
          , nonlin := .identity, agg := .max })] })

#guard isOk (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.read "X" []] }] }
          , nonlin := .identity, agg := .min })] })

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
-- so nothing in this file's checkers can ever construct this value. Exercised directly, same
-- pattern as `dynamicShape` below.
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

/-- `PlanStep` field-access helper: every fixture in this file uses `nonlin := .identity` and no
    `.scan` node, so `prepareEvalPlan`'s Step D only ever emits `.assign` steps for them (the
    `.identity` branch's single-step, no-internal-slot path — Thread 4's Task 3 only chains a second
    `.pointwise`/`.axiswise` step for a nonlin-bearing statement, none of which appear here) — made
    explicit here (fails the assertion, since `AssignPlan` derives `Inhabited`) rather than silently
    defaulting or re-projecting a field that no longer exists directly on `PlanStep`. -/
def assignStep : PlanStep → AssignPlan
  | .assign a => a
  | .scan _ => panic! "unreachable: CompileTest fixtures are scan-free by construction"
  | .pointwise _ | .axiswise _ =>
      panic! "unreachable: CompileTest fixtures never compile to a nonlinearity step"

#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.iterationShape) == some #[2, 3]
#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.outputPos) == some #[0]
#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.reductionPos) == some #[1]
#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.contextPos) == some #[]
#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).contextShape) == some #[]
#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.factors[0]!.readOrDefault.map.coeffs) ==
  some #[#[1, 0]]   -- A[i]: zero coefficient in the j (contracted) column — still counted
#guard contractPrepared.map (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.factors[1]!.readOrDefault.map.coeffs) ==
  some #[#[0, 1]]   -- B[j]

-- Example 2b: multiple factors and ORDERED reductions `Y[i] := A[i,j]·B[j,k]·C[k]`, contracting
-- over TWO axes (j then k, in first-encountered order via `termAxisUIDs`) — Example 2 above never
-- exercises more than one contracted axis, and neither does `PropertyOracle.enumPrograms` (its
-- generator caps every term at 2 factors and never puts more than one contracted axis `j` into
-- play — confirmed by reading `Gen.lean` directly), so this is the only coverage anywhere in the
-- suite for reduction ORDER with more than one axis, and the only multi-dimensional-read (`A[i,j]`,
-- two idx-expr rows in one factor) coverage in this file.
def axI2b : AxisSpec := { name := "i", uid := 1, kind := .nat }
def axJ2b : AxisSpec := { name := "j", uid := 2, kind := .nat }
def axK2b : AxisSpec := { name := "k", uid := 3, kind := .nat }
def multiReductionSched : ScheduledProgram :=
  { decls := [.axis axI2b (some 2), .axis axJ2b (some 2), .axis axK2b (some 2)]
  , stmts := [.plain (.assign "Y" [.free axI2b]
      { body := { terms := [{ factors :=
          [ .read "A" [.axis axI2b, .axis axJ2b]
          , .read "B" [.axis axJ2b, .axis axK2b]
          , .read "C" [.axis axK2b] ] }] }
      , nonlin := .identity })]
  , env := {}, extNames := insert "A" (insert "B" (insert "C" (∅ : Finset String)))
  , explicitSizes :=
      (((({} : HashMap UID Nat).insert axI2b.uid 2).insert axJ2b.uid 2).insert axK2b.uid 2) }
def multiReductionInputs : HashMap String DenseTensor :=
  ((({} : HashMap String DenseTensor).insert "A" ⟨[2, 2], #[1.0, 2.0, 3.0, 4.0]⟩).insert
    "B" ⟨[2, 2], #[1.0, 0.0, 0.0, 1.0]⟩).insert "C" ⟨[2], #[1.0, 1.0]⟩
def multiReductionSig : InputSignature := InputSignature.ofDenseInputs multiReductionInputs
#guard (prepareEvalPlan multiReductionSched multiReductionSig).toOption.isSome

def multiReductionPrepared : Option PreparedPlan :=
  (prepareEvalPlan multiReductionSched multiReductionSig).toOption

#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.iterationShape) == some #[2, 2, 2]
#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.outputPos) == some #[0]
#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.reductionPos) == some #[1, 2]  -- j, then k
#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.contextPos) == some #[]
-- A[i,j]: one row per read dimension, over basis [i, j, k].
#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.factors[0]!.readOrDefault.map.coeffs) ==
  some #[#[1, 0, 0], #[0, 1, 0]]
-- B[j,k]
#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.factors[1]!.readOrDefault.map.coeffs) ==
  some #[#[0, 1, 0], #[0, 0, 1]]
-- C[k]
#guard multiReductionPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.factors[2]!.readOrDefault.map.coeffs) ==
  some #[#[0, 0, 1]]

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
-- `RequiredBindings` has no derived `BEq` (same established precedent as `PreparedPlan` itself, per
-- `Prepared.lean`'s own doc comment: private-constructor types compare through field projections,
-- not whole-struct equality), so compare through `.bindings` instead.
#guard ((prepareEvalPlan contractSched contractSig).toOption.map (·.bindings.requiredInputs.bindings)) ==
       ((prepareEvalPlan contractSched contractSig).toOption.map (·.bindings.requiredInputs.bindings))
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
-- shape inference, so an axis-less `.scan` statement is rejected with a `.capability`-tagged
-- `PlanCompileFailure` and `warnings := []` (Step A fails before any warnings could accrue) — the
-- same schedule/error pair `capabilityPreflight`'s own `noAdvancingAxis` guard above uses.
#guard causeOf (prepareEvalPlan { acceptedSched with stmts := [.scan "s" [] [] [] false] } identitySig) ==
  some { cause := .capability (.noAdvancingAxis "s"), warnings := [] }

-- `PlanCompileCause.shape` through `prepareEvalPlan`: axis `i` never appears in any read, so shape
-- inference succeeds vacuously (no read positions to fail on) but leaves `i` unsized;
-- `resolveSizeOrFail` then fails on it while resolving the statement's output shape.
def axUnsized : AxisSpec := { name := "i", uid := 1, kind := .nat }

def unsizedSched : ScheduledProgram :=
  { decls := [.axis axUnsized none]
  , stmts := [.plain (.assign "Y" [.free axUnsized]
      { body := { terms := [{ factors := [] }] }, nonlin := .identity })]
  , env := {}, extNames := (∅ : Finset String)
  , explicitSizes := {} }

def emptySig : InputSignature := InputSignature.mk ({} : HashMap String TensorSignature)

#guard causeOf (prepareEvalPlan unsizedSched emptySig) ==
  some { cause := .shape (.unsizedAxis 1 (.assignOutput "Y")), warnings := [] }

-- ── Task 4.1: direct-schedule source invariants and authoritative external-name derivation ──

/-- Fixture 7: `acceptedSched`'s shape, but `Y` is DECLARED a predicate and its statement violates
    BOTH predicate-output invariants (relu nonlinearity, max aggregation). Its LHS is the affine
    slot from the `scatterOrAffineLhs` donor above, and `X`'s required input signature is omitted.
    Source-invariant validation runs first, so the reported cause is `sourceInvariant
    predicateNonlin` — not the capability rejection its LHS would earn, not the missing signature,
    and not the `booleanOutput` its predicate declaration still earns at preflight. -/
def predicateSourceSched : ScheduledProgram :=
  { acceptedSched with
      decls := [.tensor "X" [], .predicate "Y" []]
    , stmts := [.plain (.assign "Y" [.affine (.axis ⟨"i", 0, .nat⟩)]
        { body := { terms := [{ factors := [.read "X" []] }] }
        , nonlin := .pointwise .relu, agg := .max })] }

#guard causeOf (prepareEvalPlan predicateSourceSched emptySig) ==
  some { cause := .sourceInvariant (.predicateNonlin "Y"), warnings := [] }

/-- Fixture 8: fixture 7 with identity nonlinearity restored and max aggregation retained ⇒
    `sourceInvariant predicateAgg`. Changing exactly one field distinguishes the two arms. -/
def predicateAggSched : ScheduledProgram :=
  { predicateSourceSched with
      stmts := [.plain (.assign "Y" [.affine (.axis ⟨"i", 0, .nat⟩)]
        { body := { terms := [{ factors := [.read "X" []] }] }
        , nonlin := .identity, agg := .max })] }

#guard causeOf (prepareEvalPlan predicateAggSched emptySig) ==
  some { cause := .sourceInvariant (.predicateAgg "Y"), warnings := [] }

/-- Fixture 9: `contractSched`'s two-input donor with both inputs given the SAME shape (so a
    slot-zero fallback could not be caught by shape checking) and `B` deliberately absent from the
    cached `sched.extNames`. Preparation derives external names from the statements themselves, so
    `A` and `B` still get distinct ordered bindings and `B[j]`'s read resolves to `B`'s own slot. -/
def sameShapeSched : ScheduledProgram :=
  { contractSched with
      extNames := insert "A" (∅ : Finset String)   -- `B` omitted from the cached set
    , explicitSizes := ((({} : HashMap UID Nat).insert axI2.uid 2).insert axJ2.uid 2) }
def sameShapeSig : InputSignature :=
  InputSignature.mk
    ((({} : HashMap String TensorSignature).insert "A" { shape := #[2], dtype := .f64 }).insert
      "B" { shape := #[2], dtype := .f64 })
def sameShapePrepared : Option PreparedPlan := (prepareEvalPlan sameShapeSched sameShapeSig).toOption

#guard sameShapePrepared.map (fun p => p.bindings.requiredInputs.bindings) ==
  some #[{ name := "A", slot := 0 }, { name := "B", slot := 1 }]
-- B[j] is the term's SECOND factor: it must read slot 1, not the slot-zero default.
#guard sameShapePrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.factors[1]!.readOrDefault.sourceSlot) ==
  some 1

/-- Fixture 9, repeated with one EXTRA cached external name that nothing reads: the derived names,
    ordered bindings, and resolved read slot are identical — an extra cached entry demands no
    signature and allocates no slot. -/
def extraCachedSched : ScheduledProgram :=
  { sameShapeSched with extNames := insert "A" (insert "NEVER_READ" (∅ : Finset String)) }
def extraCachedPrepared : Option PreparedPlan :=
  (prepareEvalPlan extraCachedSched sameShapeSig).toOption

#guard extraCachedPrepared.map (fun p => p.bindings.requiredInputs.bindings) ==
  some #[{ name := "A", slot := 0 }, { name := "B", slot := 1 }]
#guard extraCachedPrepared.map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.factors[1]!.readOrDefault.sourceSlot) ==
  some 1

/-- Manual renderer for `PlanCompileCause` (used only for test-failure messages): the type
    deliberately has no `Repr`/`ToString` (`ShapeError` — nested via `.shape` — has neither), so a
    diagnosable message has to dispatch per-constructor to whichever rendering each nested cause
    DOES support (`Repr` for `CapabilityError`/`InputSignatureError`/`PlanError`, `ToString` for
    `ShapeError`). -/
private def renderCompileCause : PlanCompileCause → String
  | .inputSignature c => s!"inputSignature: {repr c}"
  | .capability c     => s!"capability: {repr c}"
  | .shape c          => s!"shape: {c}"
  | .scan c            => s!"scan: {repr c}"
  | .invalidPlan c     => s!"invalidPlan: {repr c}"
  | .bindings c        => s!"bindings: {repr c}"
  | .nonlin c          => s!"nonlin: {repr c}"
  | .sourceInvariant c => s!"sourceInvariant: {repr c}"

-- non-empty `warnings` surviving into a real `prepareEvalPlan` failure: a second statement's
-- unsized-axis failure must not touch or clear warnings the first statement already accumulated.
private def warnProg : TLProgram := tlprog!{
  axis i : ℕ = 4
  axis j : ℕ = 3
  Y[i, j] := X[2 * i + j]
}
private def warnInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[6], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]⟩
def axUnsized2 : AxisSpec := { name := "k", uid := 1000, kind := .nat }

-- statement 1 alone, for cross-check that the combined program's warnings didn't change.
def warnBaselinePrepared : Option PreparedPlan := Id.run do
  match warnProg.compileToScheduled.run 0 with
  | .error _ _ => none
  | .ok sched _ => (prepareEvalPlan sched (InputSignature.ofDenseInputs warnInputs)).toOption

run_cmd do
  match warnProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"warnProg compile failed: {repr e}"
  | .ok sched _ =>
    let combined : ScheduledProgram :=
      { sched with
          decls := sched.decls ++ [.axis axUnsized2 none]
          stmts := sched.stmts ++ [.plain (.assign "Z" [.free axUnsized2]
            { body := { terms := [{ factors := [] }] }, nonlin := .identity })] }
    match causeOf (prepareEvalPlan combined (InputSignature.ofDenseInputs warnInputs)) with
    | none => throwError "expected prepareEvalPlan to fail on the combined program"
    | some f =>
        unless !f.warnings.isEmpty do
          throwError "expected non-empty warnings to survive into the Step D failure"
        unless f.cause == .shape (.unsizedAxis 1000 (.assignOutput "Z")) do
          throwError s!"wrong cause: {renderCompileCause f.cause}"
        match warnBaselinePrepared with
        | none => throwError "unreachable: baseline already confirmed some above"
        | some baseline =>
            unless f.warnings == baseline.warnings do
              throwError s!"combined warnings diverged from statement-1-alone: {f.warnings} vs {baseline.warnings}"

end LeanNCD.Eval.Plan.CompileTest

import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Compile
import LeanNCD.Eval.Plan.Adapter   -- `runPreparedDense`: the explicitSizes-authority fixture runs its plan

/-!
# Wave C C4 capability preflight tests

One baseline accepted program (`Y[i] := X[i]`) plus rejected cases for every remaining
`CapabilityError` category (8 top-level rejection categories now): 2 cases for `unsupportedLhsSlot`
(`iterAt`/`iterNext` — `.freeNorm` at top level is now ADMITTED, Thread 4, so it is no longer one of
these rejection cases; see the accepted fixture below instead), 2 for `unsupportedNonlin`
(pointwise/axiswise, now specifically SCAN-BLOCK cases — Thread 4 admits both at top level too), and
one each for the remaining categories. `unsupportedAgg` (max/min) is likewise no longer a rejection
category — the max/min-aggregation thread admits both (they compile to the tropical algebras), so its
two donor programs are now accepted-case fixtures below, not rejections. `booleanOutput` (Task 4.3) is
likewise no longer a rejection category — a `.predicate` declaration is now structurally admitted, so
its former rejection fixture becomes an accepted-case fixture below (immediately followed by a
donor confirming the NEXT statement is still checked, not skipped). Plus three Thread-4
accepted-case fixtures pinning what preflight now admits at top level (`.freeNorm`, `.pointwise`,
unmasked `.axiswise`) that Wave C used to reject.
the two structurally-unreachable categories (`unsupportedDtype`, `dynamicShape`) are exercised
directly on the constructor rather than through `capabilityPreflight`. Also covers `prepareEvalPlan`
end-to-end on accepted programs — an identity copy, a zero-coefficient contraction, and a
repeated-assignment (no-dedup) case — every `PlanCompileCause` variant reached through the real
pipeline (`inputSignature`, `capability`, `shape`), and non-empty preparation warnings surviving a
later `shape` failure unchanged. Task 4.3 adds declared-predicate-destination coverage: a required
input signature contradicting the source declaration (`inputSignature.dtypeMismatch`, both
directions), an external input's validated dtype carried into the checked plan rather than
hard-coded, and `PreparedPlan.materializedSignatures`'s repeated-name, per-slot dtype ordering.
The whole-branch review adds that accessor's failure side: `materializedSignatures` is
`Except PlanError`-valued, and two hand-built `PreparedPlan`s (a leading and a trailing slot
outside `plan.raw.tensorSigs`) pin the exact `slotOutOfRange` it must raise instead of
defaulting to a scalar `f64` signature.
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

-- booleanOutput (Task 4.3, fixture 10): a predicate decl is now structurally ADMITTED — changing
-- no field except the expected result from the pre-4.3 rejection above.
#guard isOk (capabilityPreflight { acceptedSched with decls := [.predicate "P" []] })

-- (Task 4.3, fixture 11): the SAME predicate decl, with the existing `scatterOrAffineLhs` scatter
-- donor appended as its one statement. Distinguishes "predicate admitted, the next statement in
-- source order is still checked" from a preflight that accidentally short-circuits after admitting
-- a predicate declaration and skips statement checking entirely.
#guard errOf (capabilityPreflight
    { acceptedSched with
        decls := [.predicate "P" []]
      , stmts := [.plain (.scatter "Out" [] { body := { terms := [] }, nonlin := .identity } {})] })
  == some (.scatterOrAffineLhs "Out")

-- `booleanOutput` has no producer left in this file (Task 4.3 replaced its one throw site), but the
-- constructor is retained on `CapabilityError` — deleting a shipped closed-family constructor is
-- itself a semantic version change, same discipline as `scanNode`/`unsupportedDtype`/`dynamicShape`.
#guard (CapabilityError.booleanOutput "retained") == CapabilityError.booleanOutput "retained"

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

-- Task 4.3, fixture 8: `repeatSched`'s shape with `Y` declared a predicate and `Z` left real —
-- `materializedSignatures` must show the destination-derived dtype in the SAME repeated-name,
-- per-slot order `materializedNames` already establishes (Task 4.1): two `bool` entries for `Y`
-- (one per write, since `checkPredicateOutput` re-validates BOTH writes independently), then one
-- `f64` entry for `Z`. This is the VALID repeated-name ordering sibling of the adversarial
-- out-of-range fixture below: both slots are in range, so the accessor succeeds and the array is
-- positionally aligned with `materializedNames`, repeats included.
-- (Round 4: the declaration is `.predicate "Y" [axI3]`, not `.predicate "Y" []`. `Y` is read
-- `Y[i]` by the third statement, so a zero-axis declaration is a rank contradiction the source
-- pipeline's `checkReadRanks` has always rejected — and which `prepareEvalPlan`'s Step 0 now
-- re-establishes for a direct schedule. The declared AXES were never what this fixture is about:
-- `dtypeOfDecl` reads the constructor, so the plan, its five slots, and the dtype ordering below
-- are unchanged.)
def repeatPredSched : ScheduledProgram :=
  { repeatSched with decls := repeatSched.decls ++ [.predicate "Y" [axI3]] }
#guard (prepareEvalPlan repeatPredSched repeatSig).toOption.isSome
def repeatPredPrepared : Option PreparedPlan := (prepareEvalPlan repeatPredSched repeatSig).toOption
/-- `materializedSignatures` under an `Option` — annotated so the `#guard` matches below can use
    dotted `.ok`/`.error` patterns (an un-annotated `Option.map` leaves the `Except` type a
    metavariable). -/
def matSigsOf (p : Option PreparedPlan) :
    Option (Except PreparedBindingsError (Array (String × TensorSignature))) :=
  p.map (·.materializedSignatures)

#guard match matSigsOf repeatPredPrepared with
  | some (.ok sigs) =>
      sigs.map (fun e => (e.1, e.2.dtype)) == #[("Y", .bool), ("Y", .bool), ("Z", .f64)]
  | _ => false

-- Whole-branch review finding 2: `materializedSignatures` is a PUBLIC accessor on a PUBLIC
-- structure, so a `PreparedPlan` whose `materializedNames` names a slot outside `plan.raw.tensorSigs`
-- is constructible by struct update (the same authority-substitution idiom `AdapterTest` Check 5
-- uses to reorder `requiredInputs`) — `prepareEvalPlan` is merely the only PRODUCER that cannot
-- emit one. Slot 99 against this plan's 5-entry signature table must be the located
-- `PlanError.slotOutOfRange 99 5`, not a fabricated scalar `f64` signature (which would misreport
-- `Y`'s declared-`bool` destination as real) and not a silently shortened array (which would break
-- the positional correspondence with `materializedNames` that the fixture above pins).
#guard repeatPredPrepared.map (fun p => p.plan.raw.tensorSigs.size) == some 5

def repeatPredBadSlot : Option PreparedPlan :=
  repeatPredPrepared.map (fun p =>
    { p with bindings := { p.bindings with
        materializedNames := #[{ name := "Y", slot := 99 }] } })

#guard match matSigsOf repeatPredBadSlot with
  | some (.error (.materializedSlot (.slotOutOfRange 99 5))) => true
  | _ => false

-- The out-of-range entry is rejected even when it TRAILS legal ones — the accessor's failure is not
-- "the first entry is bad", and a valid prefix does not license a partial array.
def repeatPredTrailingBadSlot : Option PreparedPlan :=
  repeatPredPrepared.map (fun p =>
    { p with bindings := { p.bindings with
        materializedNames := p.bindings.materializedNames.push { name := "Z", slot := 7 } } })

#guard match matSigsOf repeatPredTrailingBadSlot with
  | some (.error (.materializedSlot (.slotOutOfRange 7 5))) => true
  | _ => false

-- Exact publication is structural slot identity, not name authentication.  Omitting the middle
-- output is rejected even though the remaining slots are increasing; changing only names is valid.
def repeatPredMissingPublication : Option PreparedPlan :=
  repeatPredPrepared.map (fun p =>
    { p with bindings := { p.bindings with
        materializedNames := p.bindings.materializedNames.take 1 ++ p.bindings.materializedNames.drop 2 } })

#guard match repeatPredPrepared, repeatPredMissingPublication with
  | some valid, some malformed =>
      match checkPreparedBindings malformed with
      | .error (.publicationSlots expected actual) =>
          expected == valid.bindings.materializedNames.map (·.slot) &&
            actual == malformed.bindings.materializedNames.map (·.slot)
      | _ => false
  | _, _ => false

#guard match matSigsOf repeatPredMissingPublication with
  | some (.error (.publicationSlots _ _)) => true
  | _ => false

#guard repeatPredPrepared.map (fun p =>
  match checkPreparedBindings
      { p with bindings := { p.bindings with
          materializedNames := p.bindings.materializedNames.map fun b => { b with name := "renamed" } } } with
  | .ok _ => true
  | .error _ => false) == some true

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
-- (Task 4.3) `X` is undeclared in `identitySched` (no `.tensor`/`.predicate` decl at all), so its
-- expected dtype is `f64`; supplying `bool` is an ADMITTED dtype that disagrees with that
-- expectation, not an inadmissible one — `dtypeMismatch`, not `dtypeNotAdmitted`. Confirmed against
-- `dtypeOfDecl none = .f64`.
def badDtypeSig : InputSignature :=
  InputSignature.mk (({} : HashMap String TensorSignature).insert "X" { shape := #[3], dtype := .bool })
#guard causeOf (prepareEvalPlan identitySched badDtypeSig) ==
  some { cause := .inputSignature (.dtypeMismatch "X" .f64 .bool), warnings := [] }

-- `dtypeNotAdmitted` still has a real producer: a signature naming `f32` — inadmissible regardless
-- of what the (absent) declaration expects.
def f32Sig : InputSignature :=
  InputSignature.mk (({} : HashMap String TensorSignature).insert "X" { shape := #[3], dtype := .f32 })
#guard causeOf (prepareEvalPlan identitySched f32Sig) ==
  some { cause := .inputSignature (.dtypeNotAdmitted "X" .f32), warnings := [] }

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
    , stmts := [.plain (.assign "Y" []
        { body := { terms := [{ factors := [.read "X" []] }] }
        , nonlin := .pointwise .relu, agg := .max })] }

#guard causeOf (prepareEvalPlan predicateSourceSched emptySig) ==
  some { cause := .sourceInvariant (.predicateNonlin "Y"), warnings := [] }

/-- Fixture 8: fixture 7 with identity nonlinearity restored and max aggregation retained ⇒
    `sourceInvariant predicateAgg`. Changing exactly one field distinguishes the two arms. -/
def predicateAggSched : ScheduledProgram :=
  { predicateSourceSched with
      stmts := [.plain (.assign "Y" []
        { body := { terms := [{ factors := [.read "X" []] }] }
        , nonlin := .identity, agg := .max })] }

#guard causeOf (prepareEvalPlan predicateAggSched emptySig) ==
  some { cause := .sourceInvariant (.predicateAgg "Y"), warnings := [] }

/-- Fixture 9: `contractSched`'s two-input donor with both inputs given the SAME shape (so a
    slot-zero fallback could not be caught by shape checking) and `B` deliberately absent from the
    cached `sched.extNames`. Preparation derives external names from the statements themselves, so
    `A` and `B` still get distinct ordered bindings and `B[j]`'s read resolves to `B`'s own slot.

    `j`'s extent is equalized to 2 in the DECLARATIONS, not merely in the cached `explicitSizes` map:
    since the whole-branch review, `prepareEvalPlan` re-derives pinned sizes from `sched.decls`
    (`declaredAxisSizes`) instead of trusting that cached field, so a fixture that shrank `j` only in
    the cache would now be seeded with `contractSched`'s declared `j = 3` and fail its own signature.
    The cached map is left in place and honest — this fixture is about external NAMES, and its
    `explicitSizes`-authority sibling lives at the end of this file. -/
def sameShapeSched : ScheduledProgram :=
  { contractSched with
      decls := [.axis axI2 (some 2), .axis axJ2 (some 2)]
    , extNames := insert "A" (∅ : Finset String)   -- `B` omitted from the cached set
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

/-- Task 4.3, fixture 4: fixture 9's `sameShapeSched`, with `B` additionally declared a predicate —
    still absent from the cached `sched.extNames`, so the checked BASELINE below also confirms
    authoritative external-name derivation (not the cached, incomplete set) reaches
    declaration-aware Boolean validation. `A` stays undeclared (expects `f64`). -/
def declaredBSched : ScheduledProgram :=
  { sameShapeSched with decls := sameShapeSched.decls ++ [.predicate "B" [axJ2]] }
def declaredBCorrectSig : InputSignature :=
  InputSignature.mk
    ((({} : HashMap String TensorSignature).insert "A" { shape := #[2], dtype := .f64 }).insert
      "B" { shape := #[2], dtype := .bool })
#guard (prepareEvalPlan declaredBSched declaredBCorrectSig).toOption.isSome
def declaredBPrepared : Option PreparedPlan :=
  (prepareEvalPlan declaredBSched declaredBCorrectSig).toOption
-- The external half of "top-level destination dtype derivation": `B`'s own input slot carries the
-- VALIDATED `.bool` signature dtype through into the checked plan, rather than a hard-coded `f64`.
#guard declaredBPrepared.map (fun p =>
    (p.plan.raw.tensorSigs.getD
      ((p.bindings.requiredInputs.bindings.find? (·.name == "B")).map (·.slot) |>.getD 999)
      { shape := #[], dtype := .f64 }).dtype) ==
  some .bool

-- Variant 1: change only `B`'s explicit signature to `f64` (`B` is declared predicate ⇒ expects
-- `bool`) ⇒ `dtypeMismatch "B" .bool .f64`.
def declaredBWrongSigB : InputSignature :=
  InputSignature.mk
    ((({} : HashMap String TensorSignature).insert "A" { shape := #[2], dtype := .f64 }).insert
      "B" { shape := #[2], dtype := .f64 })
#guard causeOf (prepareEvalPlan declaredBSched declaredBWrongSigB) ==
  some { cause := .inputSignature (.dtypeMismatch "B" .bool .f64), warnings := [] }

-- Variant 2: change only `A`'s explicit signature to `bool` (`A` is undeclared ⇒ expects `f64`) ⇒
-- `dtypeMismatch "A" .f64 .bool`.
def declaredBWrongSigA : InputSignature :=
  InputSignature.mk
    ((({} : HashMap String TensorSignature).insert "A" { shape := #[2], dtype := .bool }).insert
      "B" { shape := #[2], dtype := .bool })
#guard causeOf (prepareEvalPlan declaredBSched declaredBWrongSigA) ==
  some { cause := .inputSignature (.dtypeMismatch "A" .f64 .bool), warnings := [] }

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

/-- Fixture 10 (per-task review finding): an OUT-OF-ORDER direct schedule — `Y[i] := A[i]·Z[j]`
    reads `Z`, which the statement AFTER it produces. Reads-minus-produced is order-insensitive, so
    `Z` was classified internal (no input slot, no signature demanded) while `resolveSource`'s `getD`
    resolved it to slot ZERO, aliasing `A` and computing a wrong answer with no diagnostic: the
    cached `extNames` is the honest `{A, B}` here, both inputs are the same shape, and every later
    phase passed. `prepareEvalPlan` Step 0 now re-establishes the statement ORDER invariant
    (`ScheduledProgram.stmts`: "producers precede consumers") with `schedule`'s own `isTopoOrdered`
    predicate and its own `cyclicDataflow` error, and rejects — it does not reorder. -/
def outOfOrderStmts : List ScanStmt :=
  [ .plain (.assign "Y" [.free axI2]
      { body := { terms := [{ factors := [.read "A" [.axis axI2], .read "Z" [.axis axJ2]] }] }
      , nonlin := .identity })
  , .plain (.assign "Z" [.free axJ2]
      { body := { terms := [{ factors := [.read "B" [.axis axJ2]] }] }, nonlin := .identity }) ]

def outOfOrderSched : ScheduledProgram :=
  { decls := [.axis axI2 (some 2), .axis axJ2 (some 2)]
  , stmts := outOfOrderStmts
  , env := {}, extNames := insert "A" (insert "B" (∅ : Finset String))
  , explicitSizes := ((({} : HashMap UID Nat).insert axI2.uid 2).insert axJ2.uid 2) }

#guard causeOf (prepareEvalPlan outOfOrderSched sameShapeSig) ==
  some { cause := .sourceInvariant
          (.cyclicDataflow "scheduled program: statements are not in producer-before-consumer order")
       , warnings := [] }

def topologyInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" ⟨[2], #[2.0, 3.0]⟩).insert
    "B" ⟨[2], #[5.0, 7.0]⟩ |>.insert "Z" ⟨[2], #[11.0, 13.0]⟩

-- The shared topology failure precedes input-signature lookup.
#guard causeOf (prepareEvalPlan outOfOrderSched emptySig) ==
  some { cause := .sourceInvariant
           (.cyclicDataflow "scheduled program: statements are not in producer-before-consumer order")
       , warnings := [] }

run_cmd do
  match evalScheduled outOfOrderSched topologyInputs with
  | .error failure =>
      match failure.error with
      | .compile (.cyclicDataflow
          "scheduled program: statements are not in producer-before-consumer order") =>
          unless failure.warnings == [] do
            throwError "out-of-order direct evaluation retained warnings"
      | _ => throwError s!"out-of-order direct evaluation reported: {failure.error}"
  | .ok _ => throwError "out-of-order direct evaluation was accepted"

/-- A plain assignment cannot satisfy its own read from the caller's input environment. The same
    dependency predicate rejects it at source scheduling and at both direct schedule boundaries. -/
def selfReadStmt : ScanStmt :=
  .plain (.assign "Y" [.free axI2]
    { body := { terms := [{ factors := [.read "Y" [.axis axI2]] }] }, nonlin := .identity })

def selfReadSched : ScheduledProgram :=
  { decls := [.axis axI2 (some 2), .tensor "Y" [axI2]]
  , stmts := [selfReadStmt]
  , env := {}, extNames := ∅
  , explicitSizes := (({} : HashMap UID Nat).insert axI2.uid 2) }

def selfReadInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "Y" ⟨[2], #[11.0, 13.0]⟩

#guard match (schedule
    { decls := selfReadSched.decls, stmts := [selfReadStmt], env := {}, extNames := ∅ }).run 0 with
  | .error (.cyclicDataflow "schedule: cyclic dataflow") _ => true
  | _ => false

#guard causeOf (prepareEvalPlan selfReadSched (InputSignature.ofDenseInputs selfReadInputs)) ==
  some { cause := .sourceInvariant
          (.cyclicDataflow "scheduled program: statements are not in producer-before-consumer order")
       , warnings := [] }

run_cmd do
  match evalScheduled selfReadSched selfReadInputs with
  | .error { error := .compile (.cyclicDataflow
      "scheduled program: statements are not in producer-before-consumer order"), warnings := [] } =>
      pure ()
  | .error failure => throwError s!"plain self-read direct evaluation reported: {failure.error}"
  | .ok _ => throwError "plain self-read consumed the caller-provided destination"

/-- Fixture 10's ORDERED twin — the identical two statements, producer first, which is what
    `schedule` would have emitted for this program. It must still compile, and `Z` must resolve to
    its own materialized slot (2), never to an input slot: rejecting fixture 10 is an order check,
    not a blanket rejection of programs whose statements read a locally produced tensor. External
    binding order is first-seen over the ORDERED statements, so `B` (read first) precedes `A`. -/
def orderedTwinSched : ScheduledProgram :=
  { outOfOrderSched with stmts := outOfOrderStmts.reverse }
def orderedTwinPrepared : Option PreparedPlan :=
  (prepareEvalPlan orderedTwinSched sameShapeSig).toOption

#guard orderedTwinPrepared.map (fun p => p.bindings.requiredInputs.bindings) ==
  some #[{ name := "B", slot := 0 }, { name := "A", slot := 1 }]
#guard orderedTwinPrepared.map
    (fun p => (assignStep p.plan.raw.steps[1]!).terms[0]!.factors.map (·.readOrDefault.sourceSlot)) ==
  some #[1, 2]

run_cmd do
  let prepared ← match prepareEvalPlan orderedTwinSched (InputSignature.ofDenseInputs topologyInputs) with
    | .ok p => pure p
    | .error _ => throwError "ordered topology sibling failed preparation"
  match evalScheduled orderedTwinSched topologyInputs, runPreparedDense prepared topologyInputs with
  | .ok direct, .ok dense =>
      match direct.env.get? "Y", dense.env.get? "Y" with
      | some directY, some denseY =>
          unless directY.shape == denseY.shape && directY.data == denseY.data do
            throwError "ordered topology sibling disagreed between direct and prepared Dense evaluation"
      | _, _ => throwError "ordered topology sibling did not publish Y"
  | .error e, _ => throwError s!"ordered topology direct evaluation failed: {e.error}"
  | _, .error e => throwError s!"ordered topology prepared Dense evaluation failed: {repr e.cause}"

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

-- ── Task 4 whole-branch review — `explicitSizes` is a cached pipeline product, not authority ──
--
-- `ScheduledProgram.explicitSizes` is what `schedule` derived from the declarations; on a
-- hand-built schedule nothing ties the two together. `prepareEvalPlan` used to seed shape inference
-- with that cached map directly, so `axis i : ℕ = 3` paired with a cached `i ↦ 4` allocated and
-- indexed every `i`-shaped tensor at 4 — silently, with no diagnostic, wherever no input shape
-- contradicts it. Step 0 now re-derives the map from `sched.decls` through the same
-- `declaredAxisSizes` rule `schedule` itself uses (the identical authority move Step 0 already made
-- for `sched.env` and `orderedExtNames` made for `sched.extNames`).
--
-- The attack needs an axis NO input shape can pin, or the disagreement would surface as an ordinary
-- `sizeConflict` instead of silently winning: `Y[i] := X[j]` contracts over `j` (pinned by `X`'s own
-- shape) and leaves `i` free on the LHS, where the declaration is its ONLY source of extent.
def axICache : AxisSpec := { name := "i", uid := 1, kind := .nat }
def axJCache : AxisSpec := { name := "j", uid := 2, kind := .nat }

def cacheSchedWith (cachedI : Nat) : ScheduledProgram :=
  { decls := [.axis axICache (some 3), .axis axJCache (some 2)]
  , stmts := [.plain (.assign "Y" [.free axICache]
      { body := { terms := [{ factors := [.read "X" [.axis axJCache]] }] }, nonlin := .identity })]
  , env := {}, extNames := insert "X" (∅ : Finset String)
  , explicitSizes := ((({} : HashMap UID Nat).insert axICache.uid cachedI).insert axJCache.uid 2) }

def cacheInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" (⟨[2], #[1.0, 10.0]⟩ : DenseTensor)
def cacheSig : InputSignature := InputSignature.ofDenseInputs cacheInputs

def cachePreparedWith (cachedI : Nat) : Option PreparedPlan :=
  (prepareEvalPlan (cacheSchedWith cachedI) cacheSig).toOption

-- The DECLARED extent (3) decides, whatever the cached map says — the lying cache (4) and the
-- honest one (3) produce byte-identical plans, iteration shape included.
#guard (cachePreparedWith 4).map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.iterationShape) == some #[3, 2]
#guard (cachePreparedWith 3).map
    (fun p => (assignStep p.plan.raw.steps[0]!).terms[0]!.iterationShape) == some #[3, 2]
#guard (cachePreparedWith 4).map (fun p => (assignStep p.plan.raw.steps[0]!).outputShape) == some #[3]
#guard (cachePreparedWith 3).map (fun p => (assignStep p.plan.raw.steps[0]!).outputShape) == some #[3]

-- …and the executed result is three elements of `ΣX = 11`, not four. Running it is what makes the
-- fixture about SEMANTICS rather than a metadata field: under the cached map the plan allocated a
-- four-element `Y`. The REFERENCE evaluator is required to agree element-for-element — it seeds
-- inference from the same re-derived map, so the fix cannot trade one silent wrong answer (both
-- backends at extent 4) for a silent disagreement (checked 3, reference 4).
run_cmd do
  match cachePreparedWith 4 with
  | none => throwError "explicitSizes attack fixture: prepareEvalPlan unexpectedly failed"
  | some prepared =>
      match runPreparedDense prepared cacheInputs with
      | .error e => throwError s!"explicitSizes attack fixture: run failed: {repr e.cause}"
      | .ok report =>
          match report.env.get? "Y" with
          | none => throwError "explicitSizes attack fixture: Y missing from the result"
          | some y =>
              unless y.shape == [3] && y.data == #[11.0, 11.0, 11.0] do
                throwError s!"explicitSizes attack fixture: Y is {repr y.shape} {repr y.data}"
      match evalScheduled (cacheSchedWith 4) cacheInputs with
      | .error f => throwError s!"explicitSizes attack fixture: evalScheduled failed: {f.error}"
      | .ok legacy =>
          match legacy.env.get? "Y" with
          | none => throwError "explicitSizes attack fixture: reference Y missing"
          | some y =>
              unless y.shape == [3] && y.data == #[11.0, 11.0, 11.0] do
                throwError s!"explicitSizes attack fixture: reference Y is {repr y.shape} {repr y.data}"

-- The sibling with an axis the cache pins and the declaration does NOT: `declaredAxisSizes` drops
-- the fabricated entry, so the axis falls to ordinary inference — which fails loud here rather than
-- honouring a size the source never declares.
def cacheUnsizedSched : ScheduledProgram :=
  { cacheSchedWith 4 with decls := [.axis axICache none, .axis axJCache (some 2)] }

#guard match causeOf (prepareEvalPlan cacheUnsizedSched cacheSig) with
  | some f => f.cause == .shape (.unsizedAxis axICache.uid (.assignOutput "Y"))
  | none => false

-- ── Task 4 whole-branch review — duplicate tensor-bearing declarations at the DIRECT evaluator ──
--
-- `Eval.combineFor` picks a statement's whole contraction algebra by scanning `decls` for the
-- destination's declaration and taking the FIRST tensor-bearing match, while a `DeclEnv` built from
-- the same list sees the LAST. On `[tensor Y, predicate Y]` that disagreement decides real-vs-Boolean
-- semantics silently. `resolveDecls` rules the list out in the source pipeline and `prepareEvalPlan`'s
-- Step 0 rules it out for the checked backend, but `evalScheduled` — a public boundary that accepts a
-- hand-built `ScheduledProgram` — used to evaluate it. It now re-runs the same `buildDeclEnv` first.
--
-- Both fixtures use `Y[i] := A[i] + B[i]` with `A = B = [1, 1]`, where the two readings genuinely
-- differ: real sum-product gives `2.0` per element, the Boolean `(∧, ∃)` reading gives `1.0`.
def axIDup : AxisSpec := { name := "i", uid := 1, kind := .nat }

def dupDeclStmts : List ScanStmt :=
  [ .plain (.assign "Y" [.free axIDup]
      { body := { terms := [ { factors := [.read "A" [.axis axIDup]] }
                           , { factors := [.read "B" [.axis axIDup]] } ] }
      , nonlin := .identity }) ]

def dupDeclInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" (⟨[2], #[1.0, 1.0]⟩ : DenseTensor)).insert
    "B" (⟨[2], #[1.0, 1.0]⟩ : DenseTensor)
def dupDeclSig : InputSignature := InputSignature.ofDenseInputs dupDeclInputs

/-- `Y` declared tensor-bearing TWICE (`tensor` then `predicate`) — the exact list `combineFor` and
    `DeclEnv` disagree about. -/
def dupDeclSched : ScheduledProgram :=
  { decls := [.axis axIDup (some 2), .tensor "Y" [axIDup], .predicate "Y" [axIDup]]
  , stmts := dupDeclStmts
  , env := {}, extNames := insert "A" (insert "B" (∅ : Finset String))
  , explicitSizes := (({} : HashMap UID Nat).insert axIDup.uid 2) }

/-- The VALID sibling: an `.axis` declaration sharing the predicate's NAME is a different namespace,
    so it is not a duplicate — and `combineFor`'s tensor-bearing-only scan still finds the predicate
    (Task 4.1's own fixture pins that at `evalAssignDtyped`, in `test/Eval/ContractTest.lean`; this
    one pins it through the whole `evalScheduled` boundary, past the new validation). -/
def axShadowSched : ScheduledProgram :=
  { dupDeclSched with
      decls := [ .axis axIDup (some 2)
               , .axis { name := "Y", uid := 77, kind := .real } none
               , .predicate "Y" [axIDup] ] }

run_cmd do
  -- reference path: the duplicate is rejected, with the source pipeline's own typed cause.
  match evalScheduled dupDeclSched dupDeclInputs with
  | .ok report =>
      throwError s!"evalScheduled accepted a doubly-declared tensor name: {repr (report.env.get? "Y")}"
  | .error failure =>
      match failure.error with
      | .compile (.duplicateTensorDecl nm) =>
          unless nm == "Y" do
            throwError s!"duplicate declaration named the wrong tensor: {nm}"
      | e => throwError s!"wrong reference cause for a duplicate declaration: {e}"
      unless failure.warnings == [] do
        throwError s!"duplicate-declaration failure carried warnings: {failure.warnings}"
  -- checked path: the SAME `CompileError`, nested in `sourceInvariant` — parity, not merely "both
  -- reject".
  match causeOf (prepareEvalPlan dupDeclSched dupDeclSig) with
  | none => throwError "prepareEvalPlan accepted a doubly-declared tensor name"
  | some f =>
      unless f.cause == .sourceInvariant (.duplicateTensorDecl "Y") do
        throwError s!"wrong checked cause for a duplicate declaration: {renderCompileCause f.cause}"
  -- the axis-shadow sibling is accepted by BOTH, and still reads as a predicate: `1.0`, not `2.0`.
  match evalScheduled axShadowSched dupDeclInputs with
  | .error failure => throwError s!"axis-shadow sibling rejected by evalScheduled: {failure.error}"
  | .ok report =>
      match report.env.get? "Y" with
      | none => throwError "axis-shadow sibling: Y missing from the result"
      | some y =>
          unless y.shape == [2] && y.data == #[1.0, 1.0] do
            throwError s!"axis-shadow sibling lost the Boolean reading: {repr y.data}"
  match causeOf (prepareEvalPlan axShadowSched dupDeclSig) with
  | none => pure ()
  | some f => throwError s!"axis-shadow sibling rejected by prepareEvalPlan: {renderCompileCause f.cause}"

-- ── Task 4 whole-branch review — predicate-output invariants at the DIRECT evaluator ──
--
-- A `predicate`-declared destination carries {0,1} values, so its statement may carry neither a
-- nonlinearity nor a non-`sum` aggregation. `checkDtypes` rules both out in the source pipeline and
-- `prepareEvalPlan`'s Step 0 rules them out for the checked backend — but `evalScheduled`, the other
-- boundary accepting a hand-built `ScheduledProgram`, used to EXECUTE them: `applyNonlin` mapped
-- `relu` over Boolean data, and `combineFor` selected the Boolean algebra from the DECLARATION while
-- the statement's `.max`/`.min` `agg` was silently ignored. Same schedule, typed rejection on one
-- backend and a silent answer on the other. Both entries now reach the rule through the SAME shared
-- traversal (`checkPredicateOutputs`, `Structural.lean`), so the fixtures below assert parity, not
-- merely "both reject".
--
-- The donor is the section above's: `Y[i] := A[i] + B[i]` with `A = B = [1, 1]`, where the readings
-- genuinely differ (real sum-product `2.0`, Boolean `(∧, ∃)` `1.0`), so the VALID siblings prove the
-- new validation did not cost the Boolean semantics it protects.

/-- The donor statement, parameterized by exactly the two fields the invariant constrains. -/
def predStmt (dest : String) (nl : Nonlin) (ag : AggOp) : ScanStmt :=
  .plain (.assign dest [.free axIDup]
    { body := { terms := [ { factors := [.read "A" [.axis axIDup]] }
                         , { factors := [.read "B" [.axis axIDup]] } ] }
    , nonlin := nl, agg := ag })

/-- `predicate Y(i)` plus the donor statement. `Y` is the only tensor-bearing declaration besides the
    two inputs, so `buildDeclEnv` succeeds and every rejection below is the per-statement rule's. -/
def predSchedWith (nl : Nonlin) (ag : AggOp) : ScheduledProgram :=
  { decls := [.axis axIDup (some 2), .tensor "A" [axIDup], .tensor "B" [axIDup]
             , .predicate "Y" [axIDup]]
  , stmts := [predStmt "Y" nl ag]
  , env := {}, extNames := insert "A" (insert "B" (∅ : Finset String))
  , explicitSizes := (({} : HashMap UID Nat).insert axIDup.uid 2) }

/-- Both backends reject `sched` with the SAME `CompileError`: the reference evaluator nests it in
    `EvalError.compile`, the checked backend in `PlanCompileCause.sourceInvariant`. Neither may carry
    warnings — both checks run before any warning can accrue. -/
def assertPredicateParity (label : String) (sched : ScheduledProgram) (expected : CompileError) :
    Lean.Elab.Command.CommandElabM Unit := do
  match evalScheduled sched dupDeclInputs with
  | .ok report => throwError s!"{label}: evalScheduled accepted it: {repr (report.env.get? "Y")}"
  | .error failure =>
      match failure.error with
      | .compile c =>
          unless c == expected do throwError s!"{label}: wrong reference CompileError: {repr c}"
      | e => throwError s!"{label}: wrong reference cause: {e}"
      unless failure.warnings == [] do
        throwError s!"{label}: reference failure carried warnings: {failure.warnings}"
  match causeOf (prepareEvalPlan sched dupDeclSig) with
  | none => throwError s!"{label}: prepareEvalPlan accepted it"
  | some f =>
      unless f.cause == .sourceInvariant expected do
        throwError s!"{label}: wrong checked cause: {renderCompileCause f.cause}"
      unless f.warnings == [] do
        throwError s!"{label}: checked failure carried warnings: {f.warnings}"

-- Each fixture is its OWN `run_cmd`: a batched block aborts at its first `throwError`, which would
-- let one regression mask every fixture after it in the same block.

-- A nonlinearity on a predicate destination: the `relu` case named in the finding.
run_cmd do
  assertPredicateParity "relu on a predicate output"
    (predSchedWith (.pointwise .relu) .sum) (.predicateNonlin "Y")

-- …and an axiswise one, so the rule is not read as "pointwise only".
run_cmd do
  assertPredicateParity "softmax on a predicate output"
    (predSchedWith (.axiswise .softmax none) .sum) (.predicateNonlin "Y")

-- A non-`sum` aggregation, both directions of the finding's `.max`/`.min`.
run_cmd do
  assertPredicateParity "max aggregation on a predicate output"
    (predSchedWith .identity .max) (.predicateAgg "Y")

run_cmd do
  assertPredicateParity "min aggregation on a predicate output"
    (predSchedWith .identity .min) (.predicateAgg "Y")

-- PRECEDENCE, within one statement: both invariants violated ⇒ nonlinearity is reported, on both
-- backends. Task 4.1's order, unchanged, because it is literally the same `checkPredicateOutput`.
run_cmd do
  assertPredicateParity "both invariants violated"
    (predSchedWith (.pointwise .relu) .max) (.predicateNonlin "Y")

-- PRECEDENCE, across phases: a duplicate tensor-bearing declaration AND a predicate violation in the
-- same schedule reports the DECLARATION failure. `buildDeclEnv` runs first for a reason — until it
-- succeeds, "which declaration is `Y`" is ambiguous, so the predicate obligation is not yet
-- well-defined.
def predDupSched : ScheduledProgram :=
  { predSchedWith (.pointwise .relu) .max with
      decls := [.axis axIDup (some 2), .tensor "A" [axIDup], .tensor "B" [axIDup]
               , .tensor "Y" [axIDup], .predicate "Y" [axIDup]] }

run_cmd do
  assertPredicateParity "duplicate declaration before predicate violation"
    predDupSched (.duplicateTensorDecl "Y")

-- PRECEDENCE, over size inference and execution: the violating statement reads `C`, which no input
-- supplies. Without the check this schedule fails somewhere in sizing/execution instead; with it,
-- the source invariant is reported first, on both backends.
def predUnreadableSched : ScheduledProgram :=
  { predSchedWith (.pointwise .relu) .sum with
      stmts := [.plain (.assign "Y" [.free axIDup]
        { body := { terms := [{ factors := [.read "C" [.axis axIDup]] }] }
        , nonlin := .pointwise .relu })] }

run_cmd do
  assertPredicateParity "predicate violation before sizing/execution"
    predUnreadableSched (.predicateNonlin "Y")

-- STATEMENT ORDER: two predicate destinations, the FIRST valid and the second violating ⇒ the second
-- is reported (the loop does not stop at the first statement), and with both violating ⇒ the FIRST is
-- reported (it does not run to the last one either). `Z`'s aggregation distinguishes the two.
def predTwoStmtSched (firstNl : Nonlin) : ScheduledProgram :=
  { predSchedWith .identity .sum with
      decls := [.axis axIDup (some 2), .tensor "A" [axIDup], .tensor "B" [axIDup]
               , .predicate "Y" [axIDup], .predicate "Z" [axIDup]]
    , stmts := [predStmt "Y" firstNl .sum, predStmt "Z" .identity .max] }

run_cmd do
  assertPredicateParity "second statement's violation is reached"
    (predTwoStmtSched .identity) (.predicateAgg "Z")

run_cmd do
  assertPredicateParity "first statement's violation wins"
    (predTwoStmtSched (.pointwise .relu)) (.predicateNonlin "Y")

-- The VALID plain sibling: identity nonlinearity, `sum` aggregation, predicate destination. Accepted
-- by both, and still the Boolean reading — `1.0`, not the real `2.0`.
run_cmd do
  match evalScheduled (predSchedWith .identity .sum) dupDeclInputs with
  | .error failure =>
      throwError s!"valid predicate sibling rejected by evalScheduled: {failure.error}"
  | .ok report =>
      match report.env.get? "Y" with
      | none => throwError "valid predicate sibling: Y missing from the result"
      | some y =>
          unless y.shape == [2] && y.data == #[1.0, 1.0] do
            throwError s!"valid predicate sibling lost the Boolean reading: {repr y.data}"
  match causeOf (prepareEvalPlan (predSchedWith .identity .sum) dupDeclSig) with
  | none => pure ()
  | some f => throwError s!"valid predicate sibling rejected by prepareEvalPlan: {renderCompileCause f.cause}"

-- …and the non-predicate control: the SAME statement fields on a `tensor`-declared destination are
-- unconstrained. `relu` of the real sum `2.0` is `2.0`, so the rule really is keyed on the
-- declaration and not on the nonlinearity alone.
def predRealDestSched : ScheduledProgram :=
  { predSchedWith (.pointwise .relu) .sum with
      decls := [.axis axIDup (some 2), .tensor "A" [axIDup], .tensor "B" [axIDup]
               , .tensor "Y" [axIDup]] }

run_cmd do
  match evalScheduled predRealDestSched dupDeclInputs with
  | .error failure => throwError s!"real-destination control rejected: {failure.error}"
  | .ok report =>
      match report.env.get? "Y" with
      | none => throwError "real-destination control: Y missing from the result"
      | some y =>
          unless y.shape == [2] && y.data == #[2.0, 2.0] do
            throwError s!"real-destination control: {repr y.data}"

-- ── The same invariant inside a `.scan` node (both halves of `base ++ recur`) ──
--
-- `checkPredicateOutputs` flattens a `.scan` into its base list followed by its recurrence list, so
-- both halves carry the obligation and their ORDER is fixed. The donor is a Boolean scan:
-- `predicate S(j, l)`, `S[j,0] := X[j]`, `S[j,l+1] := S[j,l] + A[j]` — where the readings again
-- differ, the real one growing (1, 2, 3) and the Boolean one saturating (1, 1, 1).
def axJScan : AxisSpec := { name := "j", uid := 11, kind := .nat }
def axLScan : AxisSpec := { name := "l", uid := 12, kind := .nat }

def scanBase (nl : Nonlin) (ag : AggOp) : Stmt :=
  .assign "S" [.free axJScan, .iterAt axLScan 0]
    { body := { terms := [{ factors := [.read "X" [.axis axJScan]] }] }, nonlin := nl, agg := ag }

def scanRecur (nl : Nonlin) (ag : AggOp) : Stmt :=
  .assign "S" [.free axJScan, .iterNext axLScan]
    { body := { terms := [ { factors := [.read "S" [.axis axJScan, .axis axLScan]] }
                         , { factors := [.read "A" [.axis axJScan]] } ] }
    , nonlin := nl, agg := ag }

def scanPredSchedWith (baseNl : Nonlin) (baseAg : AggOp) (recurNl : Nonlin) (recurAg : AggOp) :
    ScheduledProgram :=
  { decls := [.axis axJScan (some 1), .iter axLScan 3, .tensor "X" [axJScan]
             , .tensor "A" [axJScan], .predicate "S" [axJScan, axLScan]]
  , stmts := [.scan "S" [axLScan] [scanBase baseNl baseAg] [scanRecur recurNl recurAg] false]
  , env := {}, extNames := insert "X" (insert "A" (∅ : Finset String))
  , explicitSizes := ((({} : HashMap UID Nat).insert axJScan.uid 1).insert axLScan.uid 3) }

def scanPredInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" (⟨[1], #[1.0]⟩ : DenseTensor)).insert
    "A" (⟨[1], #[1.0]⟩ : DenseTensor)

def assertScanPredicateParity (label : String) (sched : ScheduledProgram) (expected : CompileError) :
    Lean.Elab.Command.CommandElabM Unit := do
  match evalScheduled sched scanPredInputs with
  | .ok report => throwError s!"{label}: evalScheduled accepted it: {repr (report.env.get? "S")}"
  | .error failure =>
      match failure.error with
      | .compile c =>
          unless c == expected do throwError s!"{label}: wrong reference CompileError: {repr c}"
      | e => throwError s!"{label}: wrong reference cause: {e}"
      unless failure.warnings == [] do
        throwError s!"{label}: reference failure carried warnings: {failure.warnings}"
  match causeOf (prepareEvalPlan sched (InputSignature.ofDenseInputs scanPredInputs)) with
  | none => throwError s!"{label}: prepareEvalPlan accepted it"
  | some f =>
      unless f.cause == .sourceInvariant expected do
        throwError s!"{label}: wrong checked cause: {renderCompileCause f.cause}"

-- base statement alone violating
run_cmd do
  assertScanPredicateParity "scan base: relu on a predicate state"
    (scanPredSchedWith (.pointwise .relu) .sum .identity .sum) (.predicateNonlin "S")

run_cmd do
  assertScanPredicateParity "scan base: max aggregation on a predicate state"
    (scanPredSchedWith .identity .max .identity .sum) (.predicateAgg "S")

-- recurrence statement alone violating — the base list is valid, so this is reached only because
-- the traversal continues past it.
run_cmd do
  assertScanPredicateParity "scan recurrence: relu on a predicate state"
    (scanPredSchedWith .identity .sum (.pointwise .relu) .sum) (.predicateNonlin "S")

run_cmd do
  assertScanPredicateParity "scan recurrence: min aggregation on a predicate state"
    (scanPredSchedWith .identity .sum .identity .min) (.predicateAgg "S")

-- ORDER within the node: base violates the AGGREGATION rule, recurrence the NONLINEARITY rule.
-- `base ++ recur` reports `predicateAgg`; a recurrence-first traversal would report
-- `predicateNonlin`, so this fixture pins the order and not merely the coverage.
run_cmd do
  assertScanPredicateParity "scan base is checked before the recurrence"
    (scanPredSchedWith .identity .max (.pointwise .relu) .sum) (.predicateAgg "S")

-- The VALID scan sibling: `evalScheduled` runs it to the saturating Boolean history `[1, 1, 1]` —
-- the real reading would be `[1, 2, 3]`. (The CHECKED backend is not asserted here: a Boolean scan's
-- acceptance is `compileScan`'s own question, and this fixture is about the reference evaluator's
-- new validation not costing a legal program. The rejection fixtures above already pin parity, and
-- they reach `sourceInvariant` before any scan compilation happens.)
run_cmd do
  match evalScheduled (scanPredSchedWith .identity .sum .identity .sum) scanPredInputs with
  | .error failure => throwError s!"valid Boolean scan sibling rejected: {failure.error}"
  | .ok report =>
      match report.env.get? "S" with
      | none => throwError "valid Boolean scan sibling: S missing from the result"
      | some s =>
          unless s.shape == [1, 3] && s.data == #[1.0, 1.0, 1.0] do
            throwError s!"valid Boolean scan sibling lost the Boolean reading: {repr s.shape} {repr s.data}"

-- ── Whole-branch review round 4 — READ ARITY at both direct-schedule entries ──
--
-- `checkReadRanks` (source pipeline, between `resolveDecls` and `checkDtypes`) rejects a read whose
-- index count contradicts its name's declaration, the other reads of the same external name, or its
-- producer's published rank. Neither `prepareEvalPlan`'s Step 0 nor `evalScheduled` re-established
-- it, so a `tensor X(i, j)` read as `X[i]` — `CompileError.rankMismatch` from source — compiled and
-- ran against a rank-1 input signature on both direct entries. Both now reach the rule through the
-- shared `checkScheduledReadRanks` (`Structural.lean`): the same rule AND the same
-- `.plain`/scan-`base ++ recur` traversal `checkPredicateOutputs` uses, with `extNames` re-derived
-- from the statements rather than read out of the cached field.
--
-- Fixtures assert PARITY (same `CompileError`, nested in each entry's own wrapper) plus the phase
-- order: declarations, then read ranks, then predicate invariants, then statement order — the source
-- pipeline's own `assignUIDs → resolveDecls → checkReadRanks → checkDtypes → … → schedule`.

def axIRank : AxisSpec := { name := "i", uid := 21, kind := .nat }
def axJRank : AxisSpec := { name := "j", uid := 22, kind := .nat }

def rankInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" (⟨[2], #[1.0, 1.0]⟩ : DenseTensor)).insert
    "A" (⟨[2], #[1.0, 1.0]⟩ : DenseTensor)

/-- Both direct entries reject `sched` with the SAME `CompileError`: the reference evaluator nests
    it in `EvalError.compile`, the checked backend in `PlanCompileCause.sourceInvariant`. Neither
    may carry warnings — read ranks are checked before anything that can warn. -/
def assertReadRankParity (label : String) (sched : ScheduledProgram) (expected : CompileError) :
    Lean.Elab.Command.CommandElabM Unit := do
  match evalScheduled sched rankInputs with
  | .ok report => throwError s!"{label}: evalScheduled accepted it: {repr (report.env.get? "Y")}"
  | .error failure =>
      match failure.error with
      | .compile c =>
          unless c == expected do throwError s!"{label}: wrong reference CompileError: {repr c}"
      | e => throwError s!"{label}: wrong reference cause: {e}"
      unless failure.warnings == [] do
        throwError s!"{label}: reference failure carried warnings: {failure.warnings}"
  match causeOf (prepareEvalPlan sched (InputSignature.ofDenseInputs rankInputs)) with
  | none => throwError s!"{label}: prepareEvalPlan accepted it"
  | some f =>
      unless f.cause == .sourceInvariant expected do
        throwError s!"{label}: wrong checked cause: {renderCompileCause f.cause}"
      unless f.warnings == [] do
        throwError s!"{label}: checked failure carried warnings: {f.warnings}"

/-- The donor: `Y[i] := X[…]`, with the read's index list the only thing that varies. -/
def rankSched (decls : List Decl) (readIdx : List IdxExpr) : ScheduledProgram :=
  { decls
  , stmts := [.plain (.assign "Y" [.free axIRank]
      { body := { terms := [{ factors := [.read "X" readIdx] }] }, nonlin := .identity })]
  , env := {}, extNames := insert "X" (∅ : Finset String)
  , explicitSizes := (({} : HashMap UID Nat).insert axIRank.uid 2) }

def rankDecls2 : List Decl :=
  [.axis axIRank (some 2), .axis axJRank (some 2), .tensor "X" [axIRank, axJRank]]

-- The finding's own program: `X` DECLARED rank 2, read with one index, and a rank-1 tensor supplied
-- for it. Source compilation rejects this outright; both direct entries used to accept it and
-- resolve the read against the rank-1 signature instead.
run_cmd do
  assertReadRankParity "declared rank 2, read with one index"
    (rankSched rankDecls2 [.axis axIRank]) (.rankMismatch "X" 2 1)

-- The other direction — a declared rank-1 name over-indexed — so the rule is not read as "too few
-- indices only".
run_cmd do
  assertReadRankParity "declared rank 1, read with two indices"
    (rankSched [.axis axIRank (some 2), .tensor "X" [axIRank]] [.axis axIRank, .axis axIRank])
    (.rankMismatch "X" 1 2)

/-- EXTERNAL name (no declaration at all): the first read site fixes the expected arity and every
    later read of the same name must agree. `X` is read `X[i]` then `X[i, i]` in the same
    statement. -/
def rankExtSched : ScheduledProgram :=
  { rankSched [.axis axIRank (some 2)] [.axis axIRank] with
      stmts := [.plain (.assign "Y" [.free axIRank]
        { body := { terms := [ { factors := [.read "X" [.axis axIRank]] }
                             , { factors := [.read "X" [.axis axIRank, .axis axIRank]] } ] }
        , nonlin := .identity })] }

run_cmd do
  assertReadRankParity "external name read at two arities" rankExtSched (.rankMismatch "X" 1 2)

/-- PRODUCED-but-undeclared intermediate: `T` is written at rank 1 and read at rank 2. Neither the
    declaration pass nor the external pass covers this name — only the producer-rank pass does. -/
def rankProducedSched : ScheduledProgram :=
  { rankSched [.axis axIRank (some 2)] [.axis axIRank] with
      stmts := [ .plain (.assign "T" [.free axIRank]
                   { body := { terms := [{ factors := [.read "X" [.axis axIRank]] }] }
                   , nonlin := .identity })
               , .plain (.assign "Y" [.free axIRank]
                   { body := { terms := [{ factors := [.read "T" [.axis axIRank, .axis axIRank]] }] }
                   , nonlin := .identity }) ] }

run_cmd do
  assertReadRankParity "produced-but-undeclared intermediate over-indexed"
    rankProducedSched (.rankMismatch "T" 1 2)

-- ── Phase ORDER, one fixture per neighbouring phase ──

-- Declarations first: a doubly-declared tensor name AND a rank violation ⇒ `duplicateTensorDecl`.
-- Until `buildDeclEnv` succeeds, "which declaration is `X`" — hence what rank a read of it must
-- have — is not even well-defined, which is exactly why `resolveDecls` precedes `checkReadRanks` in
-- the source pipeline.
run_cmd do
  assertReadRankParity "duplicate declaration before read rank"
    (rankSched (rankDecls2 ++ [.tensor "X" [axIRank]]) [.axis axIRank])
    (.duplicateTensorDecl "X")

/-- Read ranks before predicate invariants (`checkReadRanks` precedes `checkDtypes`): the statement
    violates both — a `predicate` destination carrying `relu`, and a rank-2 `X` read with one
    index. -/
def rankPredSched : ScheduledProgram :=
  { rankSched (rankDecls2 ++ [.predicate "Y" [axIRank]]) [.axis axIRank] with
      stmts := [.plain (.assign "Y" [.free axIRank]
        { body := { terms := [{ factors := [.read "X" [.axis axIRank]] }] }
        , nonlin := .pointwise .relu })] }

run_cmd do
  assertReadRankParity "read rank before predicate invariants" rankPredSched (.rankMismatch "X" 2 1)

/-- Read ranks before capability preflight (Step A) and signature validation (Step B): the statement
    ALSO has an affine (scatter) LHS, which preflight rejects as `scatterOrAffineLhs`. -/
def rankScatterSched : ScheduledProgram :=
  { rankSched rankDecls2 [.axis axIRank] with
      stmts := [.plain (.assign "Y" [.affine (.scale 2 axIRank)]
        { body := { terms := [{ factors := [.read "X" [.axis axIRank]] }] }
        , nonlin := .identity })] }

run_cmd do
  assertReadRankParity "read rank before capability preflight"
    rankScatterSched (.rankMismatch "X" 2 1)

/-- Read ranks before sizing and execution: the statement also reads `C`, which no input supplies
    (`missingSignature` on the checked backend, an execution failure on the reference one). -/
def rankUnreadableSched : ScheduledProgram :=
  { rankSched rankDecls2 [.axis axIRank] with
      stmts := [.plain (.assign "Y" [.free axIRank]
        { body := { terms := [ { factors := [.read "X" [.axis axIRank]] }
                             , { factors := [.read "C" [.axis axIRank]] } ] }
        , nonlin := .identity })] }

run_cmd do
  assertReadRankParity "read rank before sizing and execution"
    rankUnreadableSched (.rankMismatch "X" 2 1)

/-- Read ranks before the STATEMENT-ORDER invariant (`schedule`'s `isTopoOrdered`, re-established at
    Step 0 after both rules above): consumer before producer AND a rank violation. -/
def rankOutOfOrderSched : ScheduledProgram :=
  { rankProducedSched with
      decls := rankDecls2
    , stmts := rankProducedSched.stmts.reverse }

run_cmd do
  assertReadRankParity "read rank before statement order"
    rankOutOfOrderSched (.rankMismatch "X" 2 1)

-- The VALID sibling: the same donor with a correctly-ranked read. Accepted by both entries, and the
-- value is the real one — the new validation costs no legal program.
run_cmd do
  let valid := rankSched [.axis axIRank (some 2), .tensor "X" [axIRank]] [.axis axIRank]
  match evalScheduled valid rankInputs with
  | .error failure => throwError s!"valid read-rank sibling rejected by evalScheduled: {failure.error}"
  | .ok report =>
      match report.env.get? "Y" with
      | none => throwError "valid read-rank sibling: Y missing from the result"
      | some y =>
          unless y.shape == [2] && y.data == #[1.0, 1.0] do
            throwError s!"valid read-rank sibling: Y is {repr y.shape} {repr y.data}"
  match causeOf (prepareEvalPlan valid (InputSignature.ofDenseInputs rankInputs)) with
  | none => pure ()
  | some f =>
      throwError s!"valid read-rank sibling rejected by prepareEvalPlan: {renderCompileCause f.cause}"

-- ── Declared destination rank at all three source/direct boundaries ──

def destinationRankSched (decls : List Decl) (slots : List LHSSlot) (readIdx : List IdxExpr) :
    ScheduledProgram :=
  { decls
  , stmts := [.plain (.assign "Y" slots
      { body := { terms := [{ factors := [.read "X" readIdx] }] }, nonlin := .identity })]
  , env := {}, extNames := insert "X" ∅
  , explicitSizes := (({} : HashMap UID Nat).insert axIRank.uid 2).insert axJRank.uid 2 }

run_cmd do
  assertReadRankParity "declared destination under-rank"
    (destinationRankSched
      [.axis axIRank (some 2), .axis axJRank (some 2), .tensor "X" [axIRank], .tensor "Y" [axIRank, axJRank]]
      [.free axIRank] [.axis axIRank])
    (.rankMismatch "Y" 2 1)

run_cmd do
  assertReadRankParity "declared destination over-rank"
    (destinationRankSched
      [.axis axIRank (some 2), .axis axJRank (some 2), .tensor "X" [axIRank], .tensor "Y" [axIRank]]
      [.free axIRank, .free axJRank] [.axis axIRank])
    (.rankMismatch "Y" 1 2)

run_cmd do
  assertReadRankParity "read rank before declared destination rank"
    (destinationRankSched
      [.axis axIRank (some 2), .axis axJRank (some 2), .tensor "X" [axIRank, axJRank]
      , .tensor "Y" [axIRank, axJRank]]
      [.free axIRank] [.axis axIRank])
    (.rankMismatch "X" 2 1)

-- ── The same rule inside a `.scan` node (both halves of `base ++ recur`) ──
--
-- Donor: `tensor A(j)`, `S[j,0] := A[j]`, `S[j,l+1] := S[j,l] + A[j]`, over `axis j = 2`,
-- `iter l = 3`. Each half's read of `A` is what varies.

def axJRankScan : AxisSpec := { name := "j", uid := 23, kind := .nat }
def axLRankScan : AxisSpec := { name := "l", uid := 24, kind := .nat }

def rankScanBase (readIdx : List IdxExpr) : Stmt :=
  .assign "S" [.free axJRankScan, .iterAt axLRankScan 0]
    { body := { terms := [{ factors := [.read "A" readIdx] }] }, nonlin := .identity }

def rankScanRecur (readIdx : List IdxExpr) : Stmt :=
  .assign "S" [.free axJRankScan, .iterNext axLRankScan]
    { body := { terms := [ { factors := [.read "S" [.axis axJRankScan, .axis axLRankScan]] }
                         , { factors := [.read "A" readIdx] } ] }
    , nonlin := .identity }

def rankScanSched (baseIdx recurIdx : List IdxExpr) : ScheduledProgram :=
  { decls := [.axis axJRankScan (some 2), .iter axLRankScan 3, .tensor "A" [axJRankScan]
             , .tensor "S" [axJRankScan, axLRankScan]]
  , stmts := [.scan "S" [axLRankScan] [rankScanBase baseIdx] [rankScanRecur recurIdx] false]
  , env := {}, extNames := insert "A" (∅ : Finset String)
  , explicitSizes := ((({} : HashMap UID Nat).insert axJRankScan.uid 2).insert axLRankScan.uid 3) }

-- The scan BASE half.
run_cmd do
  assertReadRankParity "scan base: declared rank 1 read with two indices"
    (rankScanSched [.axis axJRankScan, .axis axJRankScan] [.axis axJRankScan])
    (.rankMismatch "A" 1 2)

-- The scan RECURRENCE half — reached only because the traversal continues past a valid base list.
run_cmd do
  assertReadRankParity "scan recurrence: declared rank 1 read with two indices"
    (rankScanSched [.axis axJRankScan] [.axis axJRankScan, .axis axJRankScan])
    (.rankMismatch "A" 1 2)

/-- ORDER within the node: the base over-indexes `A` (declared rank 1 ⇒ expected 1, actual 2) and
    the recurrence under-indexes `S` (declared rank 2 ⇒ expected 2, actual 1). `base ++ recur`
    reports the BASE's `A`; a recurrence-first traversal would report `S`. -/
def rankScanOrderSched : ScheduledProgram :=
  { rankScanSched [.axis axJRankScan, .axis axJRankScan] [.axis axJRankScan] with
      stmts := [.scan "S" [axLRankScan]
                  [rankScanBase [.axis axJRankScan, .axis axJRankScan]]
                  [.assign "S" [.free axJRankScan, .iterNext axLRankScan]
                     { body := { terms := [{ factors := [.read "S" [.axis axJRankScan]] }] }
                     , nonlin := .identity }] false] }

run_cmd do
  assertReadRankParity "scan base is checked before the recurrence" rankScanOrderSched
    (.rankMismatch "A" 1 2)

def rankScanDestinationSched (baseSlots recurSlots : List LHSSlot) : ScheduledProgram :=
  { rankScanSched [.axis axJRankScan] [.axis axJRankScan] with
      stmts := [.scan "S" [axLRankScan]
        [.assign "S" baseSlots
          { body := { terms := [{ factors := [.read "A" [.axis axJRankScan]] }] }, nonlin := .identity }]
        [.assign "S" recurSlots
          { body := { terms := [{ factors := [.read "S" [.axis axJRankScan, .axis axLRankScan]] }
                               , { factors := [.read "A" [.axis axJRankScan]] }] }
          , nonlin := .identity }]
        false] }

run_cmd do
  assertReadRankParity "scan base declared destination under-rank"
    (rankScanDestinationSched [.free axJRankScan] [.free axJRankScan, .iterNext axLRankScan])
    (.rankMismatch "S" 2 1)

run_cmd do
  assertReadRankParity "scan recurrence declared destination over-rank"
    (rankScanDestinationSched [.free axJRankScan, .iterAt axLRankScan 0]
      [.free axJRankScan, .iterNext axLRankScan, .free axJRankScan])
    (.rankMismatch "S" 2 3)

run_cmd do
  assertReadRankParity "scan base destination precedes recurrence destination"
    (rankScanDestinationSched [.free axJRankScan]
      [.free axJRankScan, .iterNext axLRankScan, .free axJRankScan])
    (.rankMismatch "S" 2 1)

-- The VALID scan sibling: both halves correctly ranked, so `evalScheduled` runs it to the real
-- history `[1, 2, 3]` per `j`.
run_cmd do
  match evalScheduled (rankScanSched [.axis axJRankScan] [.axis axJRankScan]) rankInputs with
  | .error failure => throwError s!"valid scan read-rank sibling rejected: {failure.error}"
  | .ok report =>
      match report.env.get? "S" with
      | none => throwError "valid scan read-rank sibling: S missing from the result"
      | some s =>
          unless s.shape == [2, 3] && s.data == #[1.0, 2.0, 3.0, 1.0, 2.0, 3.0] do
            throwError s!"valid scan read-rank sibling: S is {repr s.shape} {repr s.data}"

end LeanNCD.Eval.Plan.CompileTest

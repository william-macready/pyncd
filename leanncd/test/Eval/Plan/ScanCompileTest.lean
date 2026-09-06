import LeanNCD.Eval.Plan.Compile
import LeanNCD.Eval.Plan.Adapter
import LeanNCD.Eval.Eval

/-!
# Wave F F4 Task 3: source scan admission and residualization tests

`ScanTest.lean` builds `RawScanPlan`s by hand and asks `checkScanPlan`/`runDenseScan` about them.
This file goes the other way: it feeds `prepareEvalPlan` real `ScheduledProgram`s containing
`ScanStmt.scan` nodes and asserts the STRUCTURE of what the compiler residualized — outer tensor
signatures, persistent-state order, `advancingDims`, captures, block inputs/outputs, write maps, and
the affine coefficients and biases inside them. Execution-only assertions would not discriminate
between a correct residualization and several wrong ones that happen to agree numerically on one
input, so the acceptance fixtures assert whole `RawScanPlan` values or named sub-fields, not just
`.isOk`.

Four parts:

1. **Acceptance** — the twelve admitted source shapes, each asserted structurally.
2. **Typed rejection** — every `ScanCompileError` constructor plus the two `CapabilityError` ones
   F4 owns, each pinned to its exact value (not merely "fails").
3. **Precedence** — a program that violates two phases at once reports the EARLIER phase.
4. **Checker agreement** — every acceptance fixture's compiled scan is additionally re-run through
   `checkScanPlan` against the compiled outer signature table, so "the compiler accepted it" and
   "F3's checker accepts what the compiler produced" are two separate, both-asserted facts.
-/

namespace LeanNCD.Eval.Plan.ScanCompileTest
open LeanNCD LeanNCD.Eval.Plan
open Std

/-! ## Part 0: shared helpers -/

def causeOf : Except PlanCompileFailure PreparedPlan → Option PlanCompileCause
  | .ok _ => none | .error e => some e.cause

/-- Manual renderer for a failing fixture's diagnostic (`PlanCompileCause` has no `Repr` — see
    `EvalPlan.lean`), mirroring `CompileTest.lean`'s own `renderCompileCause`. -/
def render : PlanCompileCause → String
  | .inputSignature c => s!"inputSignature: {repr c}"
  | .capability c     => s!"capability: {repr c}"
  | .shape c          => s!"shape: {c}"
  | .scan c           => s!"scan: {repr c}"
  | .invalidPlan c    => s!"invalidPlan: {repr c}"
  | .bindings c       => s!"bindings: {repr c}"
  | .nonlin c         => s!"nonlin: {repr c}"
  | .sourceInvariant c => s!"sourceInvariant: {repr c}"

/-- The `i`-th outer step as a scan, or `none` if it is an assignment / absent. -/
def scanAt (p : PreparedPlan) (i : Nat) : Option RawScanPlan :=
  match p.plan.raw.steps[i]? with | some (.scan s) => some s | _ => none

def assignAt (p : PreparedPlan) (i : Nat) : Option AssignPlan :=
  match p.plan.raw.steps[i]? with | some (.assign a) => some a | _ => none

def prepared (sched : ScheduledProgram) (inputs : HashMap String DenseTensor) :
    Option PreparedPlan :=
  (prepareEvalPlan sched (InputSignature.ofDenseInputs inputs)).toOption

/-- Assert that a fixture compiles, and hand its `PreparedPlan` to `k`. Reports the real compile
    cause on failure rather than a bare `none`, which is what makes an unexpected rejection
    diagnosable instead of merely red. -/
def withPrepared (name : String) (sched : ScheduledProgram) (inputs : HashMap String DenseTensor)
    (k : PreparedPlan → Except String Unit) : Except String Unit :=
  match prepareEvalPlan sched (InputSignature.ofDenseInputs inputs) with
  | .error e => .error s!"{name}: expected acceptance, got {render e.cause}"
  | .ok p => k p

def expectEq [BEq α] [Repr α] (what : String) (actual expected : α) : Except String Unit :=
  if actual == expected then .ok () else
    .error s!"{what}: got {repr actual}, expected {repr expected}"

/-- Re-run one accepted fixture's compiled scan through F3's own checker, against the compiled outer
    signature table. `prepareEvalPlan` already routes every scan through `checkPlan` → `checkScanPlan`
    (a rejection there surfaces as `invalidPlan`), so this is a redundancy on purpose: it pins WHICH
    step was checked and turns a future regression that stops emitting scan steps at all — every
    `scanAt` returning `none`, every acceptance fixture still "passing" — into a failure. -/
def checkerAgrees (name : String) (p : PreparedPlan) (i : Nat) : Except String Unit :=
  match scanAt p i with
  | none => .error s!"{name}: step {i} is not a scan step"
  | some raw =>
      match checkScanPlan p.plan.raw.tensorSigs raw with
      | .ok _ => .ok ()
      | .error e => .error s!"{name}: checkScanPlan rejected the compiled scan: {repr e}"

/-! ## Part 1: acceptance fixtures

### A. One-axis self recurrence, asserted as a whole `RawScanPlan`

`iter l = 3`; `S[l@0] := S0`, `S[l+1] := S[l] + X[l]`. Deliberately the SAME recurrence
`ScanTest.lean`'s hand-built `linearScan` encodes, so the compiler's output can be read against a
raw fixture that F3 already verified independently — including the outer signature table
(`[S0 : scalar, X : [3], S : [3]]`) and `stateS.destSlot = 2`. -/

def axL : AxisSpec := ⟨"l", 1, .nat⟩

def selfRecurSched : ScheduledProgram :=
  { decls := [.iter axL 3]
  , stmts := [.scan "S" [axL]
      [ .assign "S" [.iterAt axL 0]
          { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity } ]
      [ .assign "S" [.iterNext axL]
          { body := { terms := [ { factors := [.read "S" [.axis axL]] }
                               , { factors := [.read "X" [.axis axL]] } ] }
          , nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "S0" (insert "X" (∅ : Finset String))
  , explicitSizes := (({} : HashMap UID Nat).insert axL.uid 3) }

def selfRecurInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "S0" ⟨[], #[5.0]⟩).insert "X" ⟨[3], #[1.0, 2.0, 3.0]⟩

/-- The complete expected residualization. Every field is hand-derived from the source above:
    * `states`: one state `S`, outer slot `2` (after the two externals), advancing dimension `0`.
    * base block: `S0` captured into local input `0`; the single base assignment writes local slot
      `1` with a scalar output and one factor whose affine map is `0 × 0` (a scalar read).
    * `baseWrites`: `S[0]` — one coefficient row of width `0` (no free output positions) and bias
      `0`, i.e. `classifyWriteRow`'s `.pinned 0`.
    * step block: context `#[2]` (`historyExtents - 1`); `S` captured as state `0` into local input
      `0`, `X` as external outer slot `1` into local input `1` — capture order is first-seen READ
      order, and `S[l]` is read before `X[l]`.
    * `stepWrites`: `S[l+1]` — a single `1` at CONTEXT position `0` with bias `1`, the canonical
      advancing row the compiler must construct itself. -/
def selfRecurExpected : RawScanPlan :=
  { states := #[{ destSlot := 2, advancingDims := #[0], materialization := .completeHistory }]
  , baseBlock :=
      { contextShape := #[]
      , tensorSigs := #[{ shape := #[], dtype := .f64 }, { shape := #[], dtype := .f64 }]
      , inputs := #[0]
      , steps := #[
          .assign
            { contextShape := #[], destinationSlot := 1, outputShape := #[]
            , terms := #[{ iterationShape := #[], contextPos := #[], outputPos := #[]
                         , reductionPos := #[]
                         , factors := #[.read { sourceSlot := 0, map := { coeffs := #[], bias := #[] }, sourceShape := #[], oobPolicy := .zeroPad }] }]
            , algebra := admittedAlgebra }]
      , outputs := #[1] }
  , baseCaptures := #[{ inputSlot := 0, source := .external 0 }]
  , baseWrites := #[{ outputSlot := 1, stateIndex := 0
                    , map := { coeffs := #[#[]], bias := #[0] } }]
  , stepBlock :=
      { contextShape := #[2]
      , tensorSigs := #[{ shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 }
                       , { shape := #[], dtype := .f64 }]
      , inputs := #[0, 1]
      , steps := #[
          .assign
            { contextShape := #[2], destinationSlot := 2, outputShape := #[]
            , terms := #[
                { iterationShape := #[2], contextPos := #[0], outputPos := #[], reductionPos := #[]
                , factors := #[.read { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[3], oobPolicy := .zeroPad }] }
              , { iterationShape := #[2], contextPos := #[0], outputPos := #[], reductionPos := #[]
                , factors := #[.read { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[3], oobPolicy := .zeroPad }] }]
            , algebra := admittedAlgebra }]
      , outputs := #[2] }
  , stepCaptures := #[{ inputSlot := 0, source := .state 0 }
                     , { inputSlot := 1, source := .external 1 }]
  , stepWrites := #[{ outputSlot := 2, stateIndex := 0
                    , map := { coeffs := #[#[1]], bias := #[1] } }]
  , historyExtents := #[3]
  , iterationOrder := .axisZeroFastest
  , boundaryPolicy := .zeroThenBaseOverlay
  , snapshotPolicy := .immutablePreStep }

def selfRecurCheck : Except String Unit :=
  withPrepared "A/selfRecur" selfRecurSched selfRecurInputs (fun p => do
    expectEq "A: outer tensorSigs" p.plan.raw.tensorSigs
      #[{ shape := #[], dtype := .f64 }, { shape := #[3], dtype := .f64 }
       , { shape := #[3], dtype := .f64 }]
    expectEq "A: outer inputSlots" p.plan.raw.inputSlots #[0, 1]
    expectEq "A: step count" p.plan.raw.steps.size 1
    expectEq "A: requiredInputs" (p.bindings.requiredInputs.bindings)
      #[{ name := "S0", slot := 0 }, { name := "X", slot := 1 }]
    expectEq "A: materializedNames" p.bindings.materializedNames #[{ name := "S", slot := 2 }]
    expectEq "A: whole RawScanPlan" (scanAt p 0) (some selfRecurExpected)
    checkerAgrees "A" p 0)

run_cmd match selfRecurCheck with | .ok _ => pure () | .error m => throwError m

/-! ### B. Coupled states, different advancing-dimension positions and orders

Two advancing axes `r`, `c` (context order `[r, c]`, extents `3`/`3`) and two coupled states whose
tensor dimensions disagree with the context order in DIFFERENT ways:

* `G[r, j, c]` — `advancingDims = #[0, 2]` (an interior non-advancing dimension);
* `H[c, r]`    — `advancingDims = #[1, 0]` (the context axes PERMUTED).

This is plan §4.3's illustrative case made real: the same context axis lands at different tensor
dimensions in different states, so context order can never be reused as state-dimension order. -/

def axR : AxisSpec := ⟨"r", 11, .nat⟩
def axC : AxisSpec := ⟨"c", 12, .nat⟩
def axJ : AxisSpec := ⟨"j", 13, .nat⟩

def coupledSched : ScheduledProgram :=
  { decls := [.iter axR 3, .iter axC 3, .axis axJ (some 2)]
  , stmts := [.scan "G" [axR, axC]
      [ .assign "G" [.iterAt axR 0, .free axJ, .iterAt axC 0]
          { body := { terms := [{ factors := [.read "G0" [.axis axJ]] }] }, nonlin := .identity }
      , .assign "H" [.iterAt axC 0, .iterAt axR 0]
          { body := { terms := [{ factors := [.read "H0" []] }] }, nonlin := .identity } ]
      [ .assign "G" [.iterNext axR, .free axJ, .iterNext axC]
          { body := { terms := [{ factors :=
              [.read "G" [.axis axR, .axis axJ, .axis axC], .read "W" [.axis axJ]] }] }
          , nonlin := .identity }
      , .assign "H" [.iterNext axC, .iterNext axR]
          { body := { terms := [ { factors := [.read "H" [.axis axC, .axis axR]] }
                               , { factors := [.read "G" [.axis axR, .axis axJ, .axis axC]] } ] }
          , nonlin := .identity } ]
      false ]
  , env := {}
  , extNames := insert "G0" (insert "H0" (insert "W" (∅ : Finset String)))
  , explicitSizes :=
      ((({} : HashMap UID Nat).insert axR.uid 3).insert axC.uid 3).insert axJ.uid 2 }

def coupledInputs : HashMap String DenseTensor :=
  ((({} : HashMap String DenseTensor).insert "G0" ⟨[2], #[1.0, 2.0]⟩).insert
    "H0" ⟨[], #[7.0]⟩).insert "W" ⟨[2], #[1.0, 1.0]⟩

def coupledCheck : Except String Unit :=
  withPrepared "B/coupled" coupledSched coupledInputs (fun p => do
    match scanAt p 0 with
    | none => .error "B: step 0 is not a scan"
    | some s => do
        -- persistent-state order is BASE-DESTINATION order (`G`, then `H`), not name order and not
        -- `ScanStmt.outputs` order.
        expectEq "B: materializedNames" p.bindings.materializedNames
          #[{ name := "G", slot := 3 }, { name := "H", slot := 4 }]
        expectEq "B: outer tensorSigs" p.plan.raw.tensorSigs
          #[{ shape := #[2], dtype := .f64 }        -- G0
          , { shape := #[], dtype := .f64 }         -- H0
          , { shape := #[2], dtype := .f64 }        -- W
          , { shape := #[3, 2, 3], dtype := .f64 }  -- G
          , { shape := #[3, 3], dtype := .f64 }]    -- H
        expectEq "B: state dest slots" (s.states.map (·.destSlot)) #[3, 4]
        -- the whole point: same context order, different dimension mappings, one of them permuted.
        expectEq "B: advancingDims" (s.states.map (·.advancingDims)) #[#[0, 2], #[1, 0]]
        expectEq "B: historyExtents" s.historyExtents #[3, 3]
        expectEq "B: step contextShape" s.stepBlock.contextShape #[2, 2]
        -- H's step write: `H[c+1, r+1]`, i.e. dimension 0 is driven by context position 1 (`c`) and
        -- dimension 1 by context position 0 (`r`) — each a single `1` at its OWN context column
        -- with bias 1, and the permutation visible directly in the coefficient rows.
        expectEq "B: H step write" (s.stepWrites.getD 1 default).map
          { coeffs := #[#[0, 1], #[1, 0]], bias := #[1, 1] }
        -- G's step write: `G[r+1, j, c+1]` — dimensions 0 and 2 are advancing rows at context
        -- columns 0 and 1 respectively (bias 1 each), while the interior free `j` row passes output
        -- position 0 through at column `numAxes + 0 = 2` with bias 0.
        expectEq "B: G step write" (s.stepWrites.getD 0 default).map
          { coeffs := #[#[1, 0, 0], #[0, 0, 1], #[0, 1, 0]], bias := #[1, 0, 1] }
        -- base writes: `G[0, j, 0]` (two pinned rows, one free) and `H[0, 0]` (fully pinned).
        expectEq "B: G base write" (s.baseWrites.getD 0 default).map
          { coeffs := #[#[0], #[1], #[0]], bias := #[0, 0, 0] }
        expectEq "B: H base write" (s.baseWrites.getD 1 default).map
          { coeffs := #[#[], #[]], bias := #[0, 0] }
        -- step captures: first-seen read order over the recurrence list is `G`, `W`, `H`.
        expectEq "B: step captures" s.stepCaptures
          #[{ inputSlot := 0, source := .state 0 }
          , { inputSlot := 1, source := .external 2 }
          , { inputSlot := 2, source := .state 1 }]
        expectEq "B: step block inputs" s.stepBlock.inputs #[0, 1, 2]
        expectEq "B: step block outputs" s.stepBlock.outputs #[3, 4]
        expectEq "B: base captures" s.baseCaptures
          #[{ inputSlot := 0, source := .external 0 }, { inputSlot := 1, source := .external 1 }]
        expectEq "B: base block outputs" s.baseBlock.outputs #[2, 3]
        checkerAgrees "B" p 0)

run_cmd match coupledCheck with | .ok _ => pure () | .error m => throwError m

/-! ### C. Scratch produced and consumed before a state result

`T` is written by the recurrence list but has no base statement, so it is block-local scratch: it
gets an ordinary block slot, is readable only by LATER statements, and never becomes an outer slot
or a materialized name. The state result `S` reads it. -/

def axM : AxisSpec := ⟨"m", 21, .nat⟩

def scratchSched : ScheduledProgram :=
  { decls := [.iter axM 3]
  , stmts := [.scan "S" [axM]
      [ .assign "S" [.iterAt axM 0]
          { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity } ]
      [ .assign "T"
          [] { body := { terms := [{ factors := [.read "S" [.axis axM], .read "K" [.axis axM]] }] }
             , nonlin := .identity }
      , .assign "S" [.iterNext axM]
          { body := { terms := [{ factors := [.read "T" []] }] }, nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "S0" (insert "K" (∅ : Finset String))
  , explicitSizes := (({} : HashMap UID Nat).insert axM.uid 3) }

def scratchInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "S0" ⟨[], #[1.0]⟩).insert "K" ⟨[3], #[2.0, 3.0, 4.0]⟩

def scratchCheck : Except String Unit :=
  withPrepared "C/scratch" scratchSched scratchInputs (fun p => do
    match scanAt p 0 with
    | none => .error "C: step 0 is not a scan"
    | some s => do
        -- scratch privacy: `T` is neither an outer signature nor a materialized name.
        expectEq "C: outer tensorSigs" p.plan.raw.tensorSigs
          #[{ shape := #[], dtype := .f64 }, { shape := #[3], dtype := .f64 }
           , { shape := #[3], dtype := .f64 }]
        expectEq "C: materializedNames" p.bindings.materializedNames #[{ name := "S", slot := 2 }]
        -- block slots: 0 = state capture `S`, 1 = external capture `K`, 2 = `T`, 3 = `S`'s result.
        expectEq "C: step captures" s.stepCaptures
          #[{ inputSlot := 0, source := .state 0 }, { inputSlot := 1, source := .external 1 }]
        expectEq "C: step assignment dests"
          (s.stepBlock.steps.filterMap BlockStep.assign? |>.map (·.destinationSlot))
          #[2, 3]
        -- only the state result is a block OUTPUT; `T` is produced but never leaves the block.
        expectEq "C: step block outputs" s.stepBlock.outputs #[3]
        -- and the result assignment reads `T` at its own local slot, not at a capture.
        expectEq "C: result reads scratch slot"
          (((s.stepBlock.steps.getD 1 default).assign?.getD default).terms.getD 0 default).factors
          #[.read { sourceSlot := 2, map := { coeffs := #[], bias := #[] }, sourceShape := #[], oobPolicy := .zeroPad }]
        checkerAgrees "C" p 0)

run_cmd match scratchCheck with | .ok _ => pure () | .error m => throwError m

/-- Task 4.4, fixture 3: `scratchSched` with its block-local scratch `T` declared a predicate while
    the persistent state `S` stays real — the paired negative case to fixture 1/2's Boolean STATE:
    a Boolean SCRATCH must ALSO derive its local block signature dtype from the declaration, not the
    former hardcoded `.f64` (`compileScan`'s step-assignment site, Task 4.4). `S`'s later recurrence
    assignment reads `T` unchanged (`S[m+1] := T[]`) — an `f64` destination reading a `bool` source
    is admitted (plan §1.2.2), so this does not additionally require `S` to become Boolean. -/
def scratchPredicateSched : ScheduledProgram :=
  { decls := [.iter axM 3, .predicate "T" []]
  , stmts := [.scan "S" [axM]
      [ .assign "S" [.iterAt axM 0]
          { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity } ]
      [ .assign "T"
          [] { body := { terms := [{ factors := [.read "S" [.axis axM], .read "K" [.axis axM]] }] }
             , nonlin := .identity }
      , .assign "S" [.iterNext axM]
          { body := { terms := [{ factors := [.read "T" []] }] }, nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "S0" (insert "K" (∅ : Finset String))
  , explicitSizes := (({} : HashMap UID Nat).insert axM.uid 3) }

def scratchPredicateInputs : HashMap String DenseTensor := scratchInputs

def scratchPredicateCheck : Except String Unit :=
  withPrepared "T4.4/scratchPredicate" scratchPredicateSched scratchPredicateInputs (fun p => do
    match scanAt p 0 with
    | none => .error "T4.4/scratchPredicate: step 0 is not a scan"
    | some s => do
        -- `S` (the persistent state) is unaffected: still `f64`, same outer table as `scratchSched`.
        expectEq "T4.4/scratchPredicate: outer tensorSigs" p.plan.raw.tensorSigs
          #[{ shape := #[], dtype := .f64 }, { shape := #[3], dtype := .f64 }
           , { shape := #[3], dtype := .f64 }]
        -- block slot 2 is `T`'s own (block-local, never published) result — now `bool`.
        expectEq "T4.4/scratchPredicate: scratch signature"
          (s.stepBlock.tensorSigs.getD 2 { shape := #[], dtype := .f64 }) { shape := #[], dtype := .bool }
        checkerAgrees "T4.4/scratchPredicate" p 0)

run_cmd match scratchPredicateCheck with | .ok _ => pure () | .error m => throwError m

/-! ### D/E. External current-coordinate reads and contractions inside a recurrence

`S[l+1] := Σ_k S[l] · M[k, l]` contracts over `k`, which is neither context nor output, while `M`
is read at the CURRENT iteration coordinate. The term basis is `context ++ output ++ reduction`, so
`k` lands at position 1 and `M[k, l]`'s two rows are `k` then `l`. -/

def axK : AxisSpec := ⟨"k", 31, .nat⟩

def contractSched : ScheduledProgram :=
  { decls := [.iter axL 4, .axis axK (some 2)]
  , stmts := [.scan "S" [axL]
      [ .assign "S" [.iterAt axL 0]
          { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity } ]
      [ .assign "S" [.iterNext axL]
          { body := { terms := [{ factors :=
              [.read "S" [.axis axL], .read "M" [.axis axK, .axis axL]] }] }
          , nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "S0" (insert "M" (∅ : Finset String))
  , explicitSizes := ((({} : HashMap UID Nat).insert axL.uid 4).insert axK.uid 2) }

def contractInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "S0" ⟨[], #[1.0]⟩).insert
    "M" ⟨[2, 4], #[1.0, 1.0, 1.0, 1.0, 2.0, 2.0, 2.0, 2.0]⟩

def contractCheck : Except String Unit :=
  withPrepared "D-E/contract" contractSched contractInputs (fun p => do
    match scanAt p 0 with
    | none => .error "D-E: step 0 is not a scan"
    | some s => do
        let t := ((s.stepBlock.steps.getD 0 default).assign?.getD default).terms.getD 0 default
        -- basis is `[l, k]`: context first, then this TERM's own contracted axis. `l` is the STEP
        -- extent (3 = 4 - 1), `k` its ordinary size.
        expectEq "D-E: iterationShape" t.iterationShape #[3, 2]
        expectEq "D-E: contextPos" t.contextPos #[0]
        expectEq "D-E: outputPos" t.outputPos #[]
        expectEq "D-E: reductionPos" t.reductionPos #[1]
        -- `S[l]`: one row (rank-1 state history), `1` on the context column.
        expectEq "D-E: state read map" (t.factors.getD 0 default).readOrDefault.map
          { coeffs := #[#[1, 0]], bias := #[0] }
        -- `M[k, l]`: read at the CURRENT coordinate — row 0 selects `k`, row 1 selects `l` with no
        -- bias — against `M`'s full declared shape, which is the history length, not the step count.
        expectEq "D-E: external read map" (t.factors.getD 1 default).readOrDefault.map
          { coeffs := #[#[0, 1], #[1, 0]], bias := #[0, 0] }
        expectEq "D-E: external read shape" (t.factors.getD 1 default).readOrDefault.sourceShape #[2, 4]
        checkerAgrees "D-E" p 0)

run_cmd match contractCheck with | .ok _ => pure () | .error m => throwError m

/-! ### F. Constant deep history with zero padding

`S[l+1] := S[l] + S[l-2]`. The look-back read has bias `-2`, which `causalAdvancingRow` admits
(non-positive bias); at `l < 2` it addresses a negative coordinate that `oobPolicy := .zeroPad`
resolves to `0`. Nothing about the deep read is special-cased in the compiler — it is the ordinary
affine lowering of `.shift l (-2)`. -/

def deepHistorySched : ScheduledProgram :=
  { decls := [.iter axL 4]
  , stmts := [.scan "S" [axL]
      [ .assign "S" [.iterAt axL 0]
          { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity } ]
      [ .assign "S" [.iterNext axL]
          { body := { terms := [ { factors := [.read "S" [.axis axL]] }
                               , { factors := [.read "S" [.shift axL (-2)]] } ] }
          , nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "S0" (∅ : Finset String)
  , explicitSizes := (({} : HashMap UID Nat).insert axL.uid 4) }

def deepHistoryInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "S0" ⟨[], #[1.0]⟩

def deepHistoryCheck : Except String Unit :=
  withPrepared "F/deepHistory" deepHistorySched deepHistoryInputs (fun p => do
    match scanAt p 0 with
    | none => .error "F: step 0 is not a scan"
    | some s => do
        let a := (s.stepBlock.steps.getD 0 default).assign?.getD default
        expectEq "F: immediate read" ((a.terms.getD 0 default).factors.getD 0 default).readOrDefault.map
          { coeffs := #[#[1]], bias := #[0] }
        expectEq "F: look-back read" ((a.terms.getD 1 default).factors.getD 0 default).readOrDefault.map
          { coeffs := #[#[1]], bias := #[-2] }
        expectEq "F: zero padding" ((a.terms.getD 1 default).factors.getD 0 default).readOrDefault.oobPolicy
          .zeroPad
        -- both reads share ONE state capture; a second capture of the same state would break the
        -- immutable-pre-step snapshot into two independently-bound inputs.
        expectEq "F: single state capture" s.stepCaptures
          #[{ inputSlot := 0, source := .state 0 }]
        checkerAgrees "F" p 0)

run_cmd match deepHistoryCheck with | .ok _ => pure () | .error m => throwError m

/-! ### G. Extent one

`iter l = 1`: the base block runs, the step block runs zero times. The compiler must still emit a
well-formed step block whose context shape is `#[0]` — `stepExtents = historyExtents - 1` — with
every term's iteration shape agreeing at the context position. -/

def extentOneSched : ScheduledProgram :=
  { decls := [.iter axL 1]
  , stmts := [.scan "S" [axL]
      [ .assign "S" [.iterAt axL 0]
          { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity } ]
      [ .assign "S" [.iterNext axL]
          { body := { terms := [{ factors := [.read "S" [.axis axL]] }] }, nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "S0" (∅ : Finset String)
  , explicitSizes := (({} : HashMap UID Nat).insert axL.uid 1) }

def extentOneCheck : Except String Unit :=
  withPrepared "G/extentOne" extentOneSched deepHistoryInputs (fun p => do
    match scanAt p 0 with
    | none => .error "G: step 0 is not a scan"
    | some s => do
        expectEq "G: historyExtents" s.historyExtents #[1]
        expectEq "G: step contextShape" s.stepBlock.contextShape #[0]
        expectEq "G: state shape" (p.plan.raw.tensorSigs.getD 1 { shape := #[9], dtype := .f64 })
          { shape := #[1], dtype := .f64 }
        expectEq "G: term iterationShape"
          (((s.stepBlock.steps.getD 0 default).assign?.getD default).terms.getD 0 default).iterationShape #[0]
        checkerAgrees "G" p 0)

run_cmd match extentOneCheck with | .ok _ => pure () | .error m => throwError m

/-! ### H. Arbitrary state-axis positions

`S[j, l]` puts the advancing axis at dimension `1`, behind a free axis. `advancingDims` must follow
the LHS, not the context list's position. -/

def axisPosSched : ScheduledProgram :=
  { decls := [.iter axL 3, .axis axJ (some 2)]
  , stmts := [.scan "S" [axL]
      [ .assign "S" [.free axJ, .iterAt axL 0]
          { body := { terms := [{ factors := [.read "S0" [.axis axJ]] }] }, nonlin := .identity } ]
      [ .assign "S" [.free axJ, .iterNext axL]
          { body := { terms := [{ factors := [.read "S" [.axis axJ, .axis axL]] }] }
          , nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "S0" (∅ : Finset String)
  , explicitSizes := ((({} : HashMap UID Nat).insert axL.uid 3).insert axJ.uid 2) }

def axisPosInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "S0" ⟨[2], #[1.0, 2.0]⟩

def axisPosCheck : Except String Unit :=
  withPrepared "H/axisPos" axisPosSched axisPosInputs (fun p => do
    match scanAt p 0 with
    | none => .error "H: step 0 is not a scan"
    | some s => do
        expectEq "H: advancingDims" (s.states.map (·.advancingDims)) #[#[1]]
        expectEq "H: state shape" (p.plan.raw.tensorSigs.getD 1 { shape := #[9], dtype := .f64 })
          { shape := #[2, 3], dtype := .f64 }
        -- base write `S[j, 0]`: row 0 passes free output position 0 through, row 1 is pinned to 0.
        expectEq "H: base write" (s.baseWrites.getD 0 default).map
          { coeffs := #[#[1], #[0]], bias := #[0, 0] }
        -- step write `S[j, l+1]`: row 0 is the free pass-through at column `numAxes + 0 = 1`,
        -- row 1 is the advancing row at context column 0 with bias 1.
        expectEq "H: step write" (s.stepWrites.getD 0 default).map
          { coeffs := #[#[0, 1], #[1, 0]], bias := #[0, 1] }
        -- causality is checked at the state's OWN advancing dimension (1), not at dimension 0.
        expectEq "H: state read map"
          ((((s.stepBlock.steps.getD 0 default).assign?.getD default).terms.getD 0 default).factors.getD 0 default).readOrDefault.map
          { coeffs := #[#[0, 1], #[1, 0]], bias := #[0, 0] }
        checkerAgrees "H" p 0)

run_cmd match axisPosCheck with | .ok _ => pure () | .error m => throwError m

/-! ### I/J. Duplicate pinned-UID bias substitution, and one state with multiple disjoint base writes

Two advancing axes `r`, `c`. `dp`'s boundary is a free-axis face at `r = 0` plus a fully-pinned
point override at `(r, c) = (1, 0)` — disjoint because `r` is pinned to different literals, and
boundary-touching because the point pins `c` (also advancing) to `0`. §5.1's admitted multi-write
form, exactly.

The point override's RHS is `X[1 + 2r + 4r]` with `r` pinned to `1`: the two `r` coefficients must
BOTH fold into the bias (`1 + 6·1 = 7`) and `r` must leave the residual basis entirely rather than
becoming a contracted axis — proposal §8.4's "a pinned axis is never accidentally contracted". -/

def multiBaseSched : ScheduledProgram :=
  { decls := [.iter axR 3, .iter axC 3]
  , stmts := [.scan "dp" [axR, axC]
      [ .assign "dp" [.iterAt axR 0, .free axC]
          { body := { terms := [{ factors := [.read "ROW" [.axis axC]] }] }, nonlin := .identity }
      , .assign "dp" [.iterAt axR 1, .iterAt axC 0]
          { body := { terms := [{ factors :=
              [.read "X" [.affine 1 [(2, axR), (4, axR)]]] }] }
          , nonlin := .identity } ]
      [ .assign "dp" [.iterNext axR, .iterNext axC]
          { body := { terms := [{ factors := [.read "dp" [.axis axR, .axis axC]] }] }
          , nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "ROW" (insert "X" (∅ : Finset String))
  , explicitSizes := ((({} : HashMap UID Nat).insert axR.uid 3).insert axC.uid 3) }

def multiBaseInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "ROW" ⟨[3], #[1.0, 2.0, 3.0]⟩).insert
    "X" ⟨[14], (Array.range 14).map (fun i => (i.toFloat))⟩

def multiBaseCheck : Except String Unit :=
  withPrepared "I-J/multiBase" multiBaseSched multiBaseInputs (fun p => do
    match scanAt p 0 with
    | none => .error "I-J: step 0 is not a scan"
    | some s => do
        expectEq "I-J: one state" (s.states.map (·.destSlot)) #[2]
        expectEq "I-J: advancingDims" (s.states.map (·.advancingDims)) #[#[0, 1]]
        -- TWO base writes for one state, both against state index 0.
        expectEq "I-J: base write count" s.baseWrites.size 2
        expectEq "I-J: base write states" (s.baseWrites.map (·.stateIndex)) #[0, 0]
        -- face `dp[0, c]`: row 0 pinned to 0, row 1 the free pass-through.
        expectEq "I-J: face write" (s.baseWrites.getD 0 default).map
          { coeffs := #[#[0], #[1]], bias := #[0, 0] }
        -- point `dp[1, 0]`: both rows pinned, no free positions, so both rows are width 0.
        expectEq "I-J: point write" (s.baseWrites.getD 1 default).map
          { coeffs := #[#[], #[]], bias := #[1, 0] }
        -- the pin substitution: `1 + 2r + 4r` at `r = 1` collapses to bias 7 over an EMPTY basis.
        let pointTerm := ((s.baseBlock.steps.getD 1 default).assign?.getD default).terms.getD 0 default
        expectEq "I-J: pinned basis is empty" pointTerm.iterationShape #[]
        expectEq "I-J: pinned axis is not contracted" pointTerm.reductionPos #[]
        expectEq "I-J: pinned bias accumulation" (pointTerm.factors.getD 0 default).readOrDefault.map
          { coeffs := #[#[]], bias := #[7] }
        -- the face write's own assignment keeps `c` as a real free output axis of extent 3.
        expectEq "I-J: face output shape"
          ((s.baseBlock.steps.getD 0 default).assign?.getD default).outputShape #[3]
        checkerAgrees "I-J" p 0)

run_cmd match multiBaseCheck with | .ok _ => pure () | .error m => throwError m

/-! ### K/L. More than one scan in an outer schedule, and a later plain statement consuming a history

Two independent scans followed by a plain assignment that reads BOTH complete histories. Exercises
outer-graph interleaving (`PlanStep.assign` after two `PlanStep.scan`s), per-scan slot allocation,
and the fact that a state history becomes an ordinary readable outer slot once published. -/

def axP : AxisSpec := ⟨"p", 41, .nat⟩

def twoScanSched : ScheduledProgram :=
  { decls := [.iter axL 3, .iter axP 3]
  , stmts :=
      [ .scan "A" [axL]
          [ .assign "A" [.iterAt axL 0]
              { body := { terms := [{ factors := [.read "A0" []] }] }, nonlin := .identity } ]
          [ .assign "A" [.iterNext axL]
              { body := { terms := [{ factors := [.read "A" [.axis axL]] }] }
              , nonlin := .identity } ]
          false
      , .scan "B" [axP]
          [ .assign "B" [.iterAt axP 0]
              { body := { terms := [{ factors := [.read "B0" []] }] }, nonlin := .identity } ]
          [ .assign "B" [.iterNext axP]
              { body := { terms := [{ factors := [.read "B" [.axis axP]] }] }
              , nonlin := .identity } ]
          false
      , .plain (.assign "Z" [.free axL]
          { body := { terms := [{ factors := [.read "A" [.axis axL], .read "B" [.axis axL]] }] }
          , nonlin := .identity }) ]
  , env := {}, extNames := insert "A0" (insert "B0" (∅ : Finset String))
  , explicitSizes := ((({} : HashMap UID Nat).insert axL.uid 3).insert axP.uid 3) }

def twoScanInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A0" ⟨[], #[1.0]⟩).insert "B0" ⟨[], #[2.0]⟩

def twoScanCheck : Except String Unit :=
  withPrepared "K-L/twoScans" twoScanSched twoScanInputs (fun p => do
    expectEq "K-L: step count" p.plan.raw.steps.size 3
    expectEq "K-L: outer tensorSigs" p.plan.raw.tensorSigs
      #[{ shape := #[], dtype := .f64 }      -- A0
      , { shape := #[], dtype := .f64 }      -- B0
      , { shape := #[3], dtype := .f64 }     -- A (scan 1's history)
      , { shape := #[3], dtype := .f64 }     -- B (scan 2's history)
      , { shape := #[3], dtype := .f64 }]    -- Z
    expectEq "K-L: materializedNames" p.bindings.materializedNames
      #[{ name := "A", slot := 2 }, { name := "B", slot := 3 }, { name := "Z", slot := 4 }]
    -- the second scan's state lands after the first scan's, with no slot reuse.
    match scanAt p 0, scanAt p 1 with
    | some s0, some s1 => do
        expectEq "K-L: scan 0 state slot" (s0.states.map (·.destSlot)) #[2]
        expectEq "K-L: scan 1 state slot" (s1.states.map (·.destSlot)) #[3]
    | _, _ => .error "K-L: steps 0 and 1 must both be scans"
    -- the later plain statement reads both histories as ordinary outer slots.
    match assignAt p 2 with
    | none => .error "K-L: step 2 is not an assignment"
    | some a =>
        expectEq "K-L: plain consumer sources"
          ((a.terms.getD 0 default).factors.map (·.readOrDefault.sourceSlot)) #[2, 3]
    checkerAgrees "K-L: scan 0" p 0
    checkerAgrees "K-L: scan 1" p 1)

run_cmd match twoScanCheck with | .ok _ => pure () | .error m => throwError m

/-! ## Part 2: typed rejection fixtures

Two shared playgrounds — a one-axis scan (`sc`, `iter l = 3`) and a two-axis one (`sc2`,
`iter r = 3`, `iter c = 3`) — whose base/recurrence lists each fixture overrides. Every assertion
pins the EXACT error value (phase tag, constructor, and every locator), so a fixture cannot pass by
failing for an unrelated reason or in an unrelated phase. -/

def axK2 : AxisSpec := ⟨"k2", 51, .nat⟩

def rejSched (base recur : List Stmt) : ScheduledProgram :=
  { decls := [.iter axL 3, .axis axJ (some 2), .axis axK2 (some 5)]
  , stmts := [.scan "sc" [axL] base recur false]
  , env := {}, extNames := insert "S0" (insert "X" (∅ : Finset String))
  , explicitSizes :=
      ((({} : HashMap UID Nat).insert axL.uid 3).insert axJ.uid 2).insert axK2.uid 5 }

def rejInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "S0" ⟨[], #[1.0]⟩).insert "X" ⟨[3], #[1.0, 2.0, 3.0]⟩

def rejSig : InputSignature := InputSignature.ofDenseInputs rejInputs

/-- Compile a one-axis playground program and return its failure cause (`none` if it was accepted).
    Most fixtures below expect a specific rejection cause, so `none` is a failure for them; the
    `badAgg … == none` fixtures are the exception — max/min aggregation is admitted, so acceptance
    (`none`) is exactly what they assert. -/
def rej (base recur : List Stmt) : Option PlanCompileCause :=
  causeOf (prepareEvalPlan (rejSched base recur) rejSig)

/-- `rej` plus an earlier scan that writes `NOPE` as block-local scratch. Such a write is not a
    publication, so a later scan read must fail the shared topology check rather than reach
    block-local resolution. -/
def rejScratchNope (base recur : List Stmt) : Option PlanCompileCause :=
  causeOf (prepareEvalPlan
    { rejSched base recur with
        stmts := [ .scan "pre" [axL]
                     [ .assign "P" [.iterAt axL 0]
                         { body := { terms := [{ factors := [.read "S0" []] }] }
                         , nonlin := .identity } ]
                     [ .assign "NOPE" []
                         { body := { terms := [{ factors := [.read "S0" []] }] }
                         , nonlin := .identity }
                     , .assign "P" [.iterNext axL]
                         { body := { terms := [{ factors := [.read "P" [.axis axL]] }] }
                         , nonlin := .identity } ]
                     false
                 , .scan "sc" [axL] base recur false ] }
    rejSig)

def okBase : Stmt := .assign "S" [.iterAt axL 0]
  { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }
def okRecur : Stmt := .assign "S" [.iterNext axL]
  { body := { terms := [{ factors := [.read "S" [.axis axL]] }] }, nonlin := .identity }

#guard rej [okBase] [okRecur] == none   -- the playground itself must compile

def rej2Sched (base recur : List Stmt) : ScheduledProgram :=
  { decls := [.iter axR 3, .iter axC 3]
  , stmts := [.scan "sc2" [axR, axC] base recur false]
  , env := {}, extNames := insert "ROW" (∅ : Finset String)
  , explicitSizes := ((({} : HashMap UID Nat).insert axR.uid 3).insert axC.uid 3) }

def rej2Sig : InputSignature := InputSignature.ofDenseInputs
  (({} : HashMap String DenseTensor).insert "ROW" ⟨[3], #[1.0, 2.0, 3.0]⟩)

def rej2 (base recur : List Stmt) : Option PlanCompileCause :=
  causeOf (prepareEvalPlan (rej2Sched base recur) rej2Sig)

def okBase2 : Stmt := .assign "dp" [.iterAt axR 0, .free axC]
  { body := { terms := [{ factors := [.read "ROW" [.axis axC]] }] }, nonlin := .identity }
def okRecur2 : Stmt := .assign "dp" [.iterNext axR, .iterNext axC]
  { body := { terms := [{ factors := [.read "dp" [.axis axR, .axis axC]] }] }
  , nonlin := .identity }

#guard rej2 [okBase2] [okRecur2] == none   -- the two-axis playground must compile too

/-! ### 2.1 `CapabilityError` — the two categories F4 owns -/

-- empty advancing-axis list
#guard causeOf (prepareEvalPlan
    { rejSched [okBase] [okRecur] with stmts := [.scan "sc" [] [okBase] [okRecur] false] } rejSig)
  == some (.capability (.noAdvancingAxis "sc"))

-- `.scanPre`: a pre-built step morphism payload, rejected as `recurrenceOrCallback`
#guard causeOf (prepareEvalPlan
    { rejSched [] [] with stmts := [.scanPre "sc" axL default] } rejSig)
  == some (.capability (.recurrenceOrCallback "sc"))

/-! ### 2.2 Unsupported assignment syntax inside base and recurrence blocks

Every category `checkScanBlockStmt` can reject, exercised on BOTH sides — the base list and the
recurrence list — since `checkScanStmt` walks `base ++ recur` and a rule applied to only one of them
would still pass a base-only or recur-only fixture. -/

def badAffineLhs (nm : String) : Stmt := .assign nm [.affine (.axis axL)]
  { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }
def badAgg (nm : String) (adv : LHSSlot) (op : AggOp) : Stmt := .assign nm [adv]
  { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity, agg := op }
def badIverson (nm : String) (adv : LHSSlot) : Stmt := .assign nm [adv]
  { body := { terms := [{ factors := [.iverson (.rel .eq (.embed (.const 0)) (.embed (.const 0)))] }] }
  , nonlin := .identity }
def badUnary (nm : String) (adv : LHSSlot) : Stmt := .assign nm [adv]
  { body := { terms := [{ factors := [.unaryFn .log "S0" []] }] }, nonlin := .identity }
def badScatter (nm : String) : Stmt :=
  .scatter nm [] { body := { terms := [] }, nonlin := .identity } {}
def badRecurMorphism (nm : String) : Stmt := .recurMorphism nm axL default

def pinL : LHSSlot := .iterAt axL 0
def nextL : LHSSlot := .iterNext axL

-- in the BASE list. `.freeNorm`, `.pointwise`, `.axiswise`, `.max`/`.min` aggregation, unary
-- factors, and now Iverson predicate factors are NO
-- LONGER preflight rejections: `compileScan` now admits and lowers the nonlinearities (Thread 4
-- Task 4), `.max`/`.min` compile to the tropical algebras (max/min-aggregation thread), unary
-- factors lower to unary-carrying `ReadPlan`s, and a source Iverson predicate lowers to a positional
-- `PosBoolExpr` factor (predicate/mask parity thread, via `lowerFactorPredicate`). Their
-- positive coverage is the accept-path fixtures (the `== none` `badAgg`/`badIverson` cases below,
-- plus `ScanTest.lean` and the `DifferentialTest.lean` scan-Iverson parity fixtures); the
-- marker-consistency and masked-axiswise negatives — which now surface at the
-- `resolveNonlinAxis` tier, not preflight — are Task 4's Task 2.
#guard rej [badAffineLhs "S"] [okRecur] == some (.capability (.scatterOrAffineLhs "S: affine LHS slot"))
#guard rej [badAgg "S" pinL .max] [okRecur] == none   -- max agg now admitted
#guard rej [badAgg "S" pinL .min] [okRecur] == none   -- min agg now admitted
#guard rej [badIverson "S" pinL] [okRecur] == none   -- iverson factor now admitted (base leg)
#guard rej [badUnary "S" pinL] [okRecur] == none   -- unary factor now admitted
#guard rej [badScatter "S"] [okRecur] == some (.capability (.scatterOrAffineLhs "S"))
#guard rej [badRecurMorphism "S"] [okRecur] == some (.capability (.recurrenceOrCallback "S"))

-- in the RECURRENCE list (`.freeNorm`/`.pointwise`/`.axiswise`, `.max`/`.min`, unary factors, and
-- Iverson predicate factors admitted — see note)
#guard rej [okBase] [badAffineLhs "S"] == some (.capability (.scatterOrAffineLhs "S: affine LHS slot"))
#guard rej [okBase] [badAgg "S" nextL .max] == none   -- max agg now admitted
#guard rej [okBase] [badAgg "S" nextL .min] == none   -- min agg now admitted
#guard rej [okBase] [badIverson "S" nextL] == none   -- iverson factor now admitted (recurrence leg)
#guard rej [okBase] [badUnary "S" nextL] == none   -- unary factor now admitted
#guard rej [okBase] [badScatter "S"] == some (.capability (.scatterOrAffineLhs "S"))
#guard rej [okBase] [badRecurMorphism "S"] == some (.capability (.recurrenceOrCallback "S"))

/-! ### 2.3 `ScanCompileError` — state/base/result pairing -/

-- no base statement at all: nothing can be persistent state.
#guard rej [] [okRecur] == some (.scan (.noPersistentState "sc"))

-- a base with no matching all-axis recurrence result.
#guard rej [okBase] [] == some (.scan (.orphanBaseState "sc" "S"))

-- an advancing result for a name no base statement writes.
#guard rej [okBase]
    [okRecur, .assign "T" [.iterNext axL]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }]
  == some (.scan (.orphanAdvancingResult "sc" "T" 1))

-- two advancing results for one state.
#guard rej [okBase] [okRecur, okRecur] == some (.scan (.duplicateStateResult "sc" "S" 0 1))

-- a recurrence statement writing a state name WITHOUT advancing it — this would silently shadow the
-- state's own immutable capture with block-local scratch, so it is rejected rather than reclassified.
#guard rej [okBase]
    [.assign "S" [.free axJ] { body := { terms := [{ factors := [.read "S0" []] }] }
                             , nonlin := .identity }]
  == some (.scan (.stateResultNotAdvancing "sc" "S" 0))

-- a result advancing only SOME of the context axes (the only non-canonical step-write geometry the
-- source language can express: every other shape is rejected earlier as `.iterAt` in a step block,
-- a duplicated axis, or a missing advancing axis).
#guard rej2 [okBase2] [.assign "dp" [.iterNext axR, .free axC]
    { body := { terms := [{ factors := [.read "dp" [.axis axR, .axis axC]] }] }
    , nonlin := .identity }]
  == some (.scan (.partialAdvancingResult "sc2" "dp" 0 1 2))

-- the same constructor's other direction: a result advancing an axis that is not scan context at
-- all, so `declared` (2) EXCEEDS the context width (1). Both directions break the canonical all-axis
-- `+1` geometry identically, which is why they share a constructor.
#guard rej [okBase] [.assign "S" [.iterNext axL, .iterNext axJ]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }]
  == some (.scan (.partialAdvancingResult "sc" "S" 0 2 1))

-- the degenerate sub-case: a result advancing the RIGHT NUMBER of axes (2, matching `numAxes = 2`)
-- but the WRONG SET (`{axR, axJ}` instead of `{axR, axC}`) — `declared` and `expected` agree as
-- counts, so only the set disagrees.
def partialSetSched : ScheduledProgram :=
  { decls := [.iter axR 3, .iter axC 3, .axis axJ (some 2)]
  , stmts := [.scan "sc2" [axR, axC]
      [okBase2]
      [.assign "dp" [.iterNext axR, .iterNext axJ]
        { body := { terms := [{ factors := [.read "dp" [.axis axR, .axis axC]] }] }
        , nonlin := .identity }] false]
  , env := {}, extNames := insert "ROW" (∅ : Finset String)
  , explicitSizes :=
      (((({} : HashMap UID Nat).insert axR.uid 3).insert axC.uid 3).insert axJ.uid 2) }

#guard causeOf (prepareEvalPlan partialSetSched rej2Sig)
  == some (.scan (.partialAdvancingResult "sc2" "dp" 0 2 2))

-- two producers for one scratch name.
def scratchT : Stmt := .assign "T" []
  { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }
#guard rej [okBase] [scratchT, scratchT, okRecur]
  == some (.scan (.duplicateScratchProducer "sc" "T" 0 1))

/-! ### 2.4 `ScanCompileError` — block dependency order -/

-- forward scratch read: statement 0 reads `T`, whose producer is statement 1.
#guard rej [okBase]
    [ .assign "U" [] { body := { terms := [{ factors := [.read "T" []] }] }, nonlin := .identity }
    , scratchT
    , okRecur ]
  == some (.scan (.blockReadNotAvailable "sc" false 0 "T" .forwardReference))

-- a base read of a name that is neither a state nor an available outer tensor. `NOPE` is PRODUCED
-- as block-local scratch by an EARLIER scan, so it is not an external input either: preparation
-- derives external names from the statements themselves (reads minus produced), so reaching this
-- rejection needs a genuinely unavailable name rather than one merely missing from the cached
-- `extNames`.
#guard rejScratchNope [.assign "S" [.iterAt axL 0]
      { body := { terms := [{ factors := [.read "NOPE" []] }] }, nonlin := .identity }] [okRecur]
  == some (.sourceInvariant
       (.cyclicDataflow "scheduled program: statements are not in producer-before-consumer order"))

-- a base block reading persistent state (proposal §8.4: initialization must not become a second,
-- implicit state machine).
#guard rej [okBase, .assign "S" [.iterAt axL 1]
      { body := { terms := [{ factors := [.read "S" [.axis axL]] }] }, nonlin := .identity }]
    [okRecur]
  == some (.scan (.stateReadInBaseBlock "sc" 1 "S"))

-- a scratch statement reading ITSELF: "available only after its producer" is strict, so a name is
-- not readable by the very statement that produces it (`producer < ri`, not `≤`).
#guard rej [okBase]
    [ .assign "T" [] { body := { terms := [{ factors := [.read "T" []] }] }, nonlin := .identity }
    , okRecur ]
  == some (.scan (.blockReadNotAvailable "sc" false 0 "T" .selfRead))

-- a step read of a name that is neither state, nor scratch, nor an available outer tensor (the
-- recurrence-side counterpart of the base-side fixture above — the two blocks resolve names through
-- separate code paths). Same earlier-scan-scratch construction, for the same reason.
#guard rejScratchNope [okBase]
    [ .assign "T" [] { body := { terms := [{ factors := [.read "NOPE" []] }] }
                     , nonlin := .identity }
    , okRecur ]
  == some (.sourceInvariant
       (.cyclicDataflow "scheduled program: statements are not in producer-before-consumer order"))

-- the FORWARD-reference outer shape the two fixtures above used to be built on — the scan reads
-- `NOPE`, and the plain statement producing it comes after. That is no longer a scan-block
-- resolution failure at all: `prepareEvalPlan`'s Step 0 rejects the statement ORDER first, with
-- `schedule`'s own topological predicate and error, before any statement is compiled.
def lateNopeSched : ScheduledProgram :=
  { rejSched [okBase] [okRecur] with
      stmts := [ .scan "sc" [axL]
                   [ .assign "S" [.iterAt axL 0]
                       { body := { terms := [{ factors := [.read "NOPE" []] }] }
                       , nonlin := .identity } ]
                   [okRecur] false
               , .plain (.assign "NOPE" []
                   { body := { terms := [{ factors := [.read "S0" []] }] }
                   , nonlin := .identity }) ] }

#guard causeOf (prepareEvalPlan lateNopeSched rejSig)
  == some (.sourceInvariant
       (.cyclicDataflow "scheduled program: statements are not in producer-before-consumer order"))

-- A recurrence-only destination is block-local scratch, not a scan publication. The shared
-- topology predicate must therefore reject a following plain read before either backend can treat
-- caller input under that name as its value. The scan itself remains valid: its recurrence reads
-- its own persistent state, and valid scan-internal self-dependencies stay eligible.
def scratchThenPlainReadSched : ScheduledProgram :=
  { rejSched [okBase] [okRecur] with
      stmts := [ .scan "pre" [axL]
                   [ .assign "P" [.iterAt axL 0]
                       { body := { terms := [{ factors := [.read "S0" []] }] }
                       , nonlin := .identity } ]
                   [ .assign "NOPE" []
                       { body := { terms := [{ factors := [.read "S0" []] }] }
                       , nonlin := .identity }
                   , .assign "P" [.iterNext axL]
                       { body := { terms := [{ factors := [.read "P" [.axis axL]] }] }
                       , nonlin := .identity } ]
                   false
               , .scan "sc" [axL] [okBase] [okRecur] false
               , .plain (.assign "Y" [.free axJ]
                   { body := { terms := [{ factors := [.read "NOPE" []] }] }
                   , nonlin := .identity }) ] }

#guard causeOf (prepareEvalPlan scratchThenPlainReadSched rejSig)
  == some (.sourceInvariant
       (.cyclicDataflow "scheduled program: statements are not in producer-before-consumer order"))

run_cmd do
  let inputs := rejInputs.insert "NOPE" ⟨[], #[37.0]⟩
  match evalScheduled scratchThenPlainReadSched inputs with
  | .error { error := .compile (.cyclicDataflow
      "scheduled program: statements are not in producer-before-consumer order"), warnings := [] } =>
      pure ()
  | .error failure => throwError s!"post-scan scratch read reported: {failure.error}"
  | .ok _ => throwError "post-scan scratch read consumed caller-provided scratch"

-- the same program with the plain statement reading the scan's published STATE `S` instead of its
-- private scratch: the guard rejects unpublished names, not locally produced ones, so this must
-- still compile and `Y` must read `S`'s own materialized outer slot rather than an input slot.
def statePlainReadSched : ScheduledProgram :=
  { scratchThenPlainReadSched with
      stmts := (scratchThenPlainReadSched.stmts.dropLast ++
        [ .plain (.assign "Y" [.free axL]
            { body := { terms := [{ factors := [.read "S" [.axis axL]] }] }
            , nonlin := .identity }) ]) }

#guard causeOf (prepareEvalPlan statePlainReadSched rejSig) == none
-- and it reads `S`'s materialized slot, not an input slot: `S0` is the only name this program reads
-- without producing, so it alone owns input slot 0; slot 1 is `pre`'s published state `P` and slot 2
-- is `sc`'s published state `S`. A slot-zero fallback would show up here as `#[0]`.
#guard (prepared statePlainReadSched rejInputs).bind (fun p => (assignAt p 2).map
    (fun a => (a.terms.getD 0 default).factors.map (·.readOrDefault.sourceSlot)))
  == some #[2]

/-! ### 2.5 `ScanCompileError` — context axes and per-state geometry -/

-- the same axis declared twice as scan context.
#guard causeOf (prepareEvalPlan
    { rejSched [] [] with
        stmts := [.scan "sc" [axL, axL] [okBase] [okRecur] false] } rejSig)
  == some (.scan (.duplicateContextAxis "sc" 0 axL.uid))

-- extent zero, discovered only after shape inference.
def zeroExtentSched : ScheduledProgram :=
  { decls := [.iter axL 0]
  , stmts := [.scan "sc" [axL] [okBase] [okRecur] false]
  , env := {}, extNames := insert "S0" (∅ : Finset String)
  , explicitSizes := (({} : HashMap UID Nat).insert axL.uid 0) }
#guard causeOf (prepareEvalPlan zeroExtentSched rejSig)
  == some (.scan (.scanAxisZeroExtent "sc" 0 axL.uid))

-- `.iterNext` in a base statement / `.iterAt` in a recurrence statement: both syntactically admitted
-- by preflight (which sees `base ++ recur` uniformly), both rejected here.
#guard rej [.assign "S" [.iterNext axL]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }] [okRecur]
  == some (.scan (.iterNextInBaseBlock "sc" "S" 0 axL.uid))
#guard rej [okBase] [.assign "S" [.iterAt axL 0]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }]
  == some (.scan (.iterAtInStepBlock "sc" "S" 0 axL.uid))

-- pinning an axis that is not scan context.
#guard rej [.assign "S" [.iterAt axL 0, .iterAt axJ 0]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }] [okRecur]
  == some (.scan (.pinnedAxisNotContext "sc" "S" 0 axJ.uid))

-- a scratch statement reusing a context axis as a free output axis (the loop coordinate is already
-- bound by the enclosing step, so this would put one UID in the basis twice).
#guard rej [okBase]
    [.assign "T" [.free axL] { body := { terms := [{ factors := [.read "X" [.axis axL]] }] }
                             , nonlin := .identity }, okRecur]
  == some (.scan (.contextAxisAsFreeOutput "sc" "T" 0 axL.uid))

-- one axis occupying two LHS positions, on each side: a base statement pinning and freeing the same
-- axis, and a result advancing the same axis twice (which would otherwise make `advancing.length`
-- agree with the context width while leaving a context axis unadvanced).
#guard rej [.assign "S" [.iterAt axL 0, .free axL]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }] [okRecur]
  == some (.scan (.duplicateAxisInLhs "sc" "S" true 0 axL.uid))
#guard rej [okBase] [.assign "S" [.iterNext axL, .iterNext axL]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }]
  == some (.scan (.duplicateAxisInLhs "sc" "S" false 0 axL.uid))

-- a base placement that never mentions the advancing axis.
#guard rej [.assign "S" [.free axJ, .free axK2]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }]
    [.assign "S" [.iterNext axL, .free axJ]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }]
  == some (.scan (.advancingAxisNotInLhs "sc" "S" true 0 axL.uid))

-- base and result disagreeing on the advancing axis's tensor dimension.
#guard rej [.assign "S" [.iterAt axL 0, .free axJ]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }]
    [.assign "S" [.free axJ, .iterNext axL]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }]
  == some (.scan (.inconsistentAdvancingDim "sc" "S" axL.uid 0 1))

-- base and result disagreeing on rank.
#guard rej [okBase]
    [.assign "S" [.iterNext axL, .free axJ]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }]
  == some (.scan (.inconsistentStateRank "sc" "S" false 0 1 2))

-- base and result agreeing on rank and advancing dimension but disagreeing on a free dimension's
-- extent (`j = 2` vs `k2 = 5` at dimension 1).
#guard rej [.assign "S" [.iterAt axL 0, .free axJ]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }]
    [.assign "S" [.iterNext axL, .free axK2]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }]
  == some (.scan (.inconsistentStateExtent "sc" "S" 1 2 5))

/-! ### 2.6 `ScanCompileError` — base write placement -/

-- interior-only: no advancing dimension pinned to `0`, so the write touches no boundary.
#guard rej [.assign "S" [.iterAt axL 1]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }] [okRecur]
  == some (.scan (.baseWriteNotAtBoundary "sc" "S" 0))

-- out of range above: `c = 5` on an extent-3 dimension (the write still touches the `r = 0`
-- boundary, so this is genuinely the range check firing, not the boundary check).
#guard rej2 [.assign "dp" [.iterAt axR 0, .iterAt axC 5]
      { body := { terms := [{ factors := [.read "ROW" [.axis axC]] }] }, nonlin := .identity }]
    [okRecur2]
  == some (.scan (.baseWritePinOutOfRange "sc2" "dp" 0 1 5 3))

-- out of range below: a negative pinned literal.
#guard rej2 [.assign "dp" [.iterAt axR 0, .iterAt axC (-1)]
      { body := { terms := [{ factors := [.read "ROW" [.axis axC]] }] }, nonlin := .identity }]
    [okRecur2]
  == some (.scan (.baseWritePinOutOfRange "sc2" "dp" 0 1 (-1) 3))

-- boundary contact is checked PER WRITE, not per state: a state whose FIRST write is a legitimate
-- boundary face still rejects a second, interior-only write — and the reported write index is `1`.
#guard rej2 [okBase2, .assign "dp" [.iterAt axR 1, .iterAt axC 1]
      { body := { terms := [{ factors := [.read "ROW" [.axis axC]] }] }, nonlin := .identity }]
    [okRecur2]
  == some (.scan (.baseWriteNotAtBoundary "sc2" "dp" 1))

-- two full free-axis faces: individually well-formed and boundary-touching, but never disjoint
-- (proposal §5.1's rejected row-0-plus-column-0 pair — rejected on REGIONS, not on values).
#guard rej2 [okBase2, .assign "dp" [.free axR, .iterAt axC 0]
      { body := { terms := [{ factors := [.read "ROW" [.axis axR]] }] }, nonlin := .identity }]
    [okRecur2]
  == some (.scan (.baseWritesOverlap "sc2" "dp" 0 1))

-- two fully-pinned point writes at the SAME coordinate: no dimension pins them apart, so they
-- collide even though neither leaves any axis free. (The face-plus-point acceptance fixture I/J
-- shows the same machinery admitting a genuinely disjoint pair.)
def pointBase (r c : Int) : Stmt := .assign "dp" [.iterAt axR r, .iterAt axC c]
  { body := { terms := [{ factors := [] }] }, nonlin := .identity }
#guard rej2 [pointBase 0 0, pointBase 0 0] [okRecur2]
  == some (.scan (.baseWritesOverlap "sc2" "dp" 0 1))
-- ... and the same pair pinned apart on `r` is accepted (both still touch the `c = 0` boundary).
#guard rej2 [pointBase 0 0, pointBase 1 0] [okRecur2] == none

/-! ### 2.7 `ScanCompileError` — step causality (proposal §7.4)

Four distinct violations of `causalAdvancingRow`'s single row shape: a positive bias (look-ahead), a
coefficient other than `1` (scaled), a `1` at the WRONG context column (cross-axis), and a `1` at an
output-slice column rather than a context column (slice-dependent). -/

-- look-ahead: `S[l + 1]`
#guard rej [okBase] [.assign "S" [.iterNext axL]
      { body := { terms := [{ factors := [.read "S" [.shift axL 1]] }] }, nonlin := .identity }]
  == some (.scan (.stateReadNotCausal "sc" "S" 0 0 0))

-- scaled: `S[2l]`
#guard rej [okBase] [.assign "S" [.iterNext axL]
      { body := { terms := [{ factors := [.read "S" [.scale 2 axL]] }] }, nonlin := .identity }]
  == some (.scan (.stateReadNotCausal "sc" "S" 0 0 0))

-- cross-axis: `dp[c, r]` reads dimension 0 (whose advancing axis is `r`, context position 0) at the
-- OTHER axis's context position.
#guard rej2 [okBase2] [.assign "dp" [.iterNext axR, .iterNext axC]
      { body := { terms := [{ factors := [.read "dp" [.axis axC, .axis axR]] }] }
      , nonlin := .identity }]
  == some (.scan (.stateReadNotCausal "sc2" "dp" 0 0 0))

-- slice-dependent: the advancing dimension is addressed by an OUTPUT-slice axis (`j`), not by the
-- scan context, so the read is not a bounded look-back at all.
#guard rej [.assign "S" [.free axJ, .iterAt axL 0]
      { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }]
    [.assign "S" [.free axJ, .iterNext axL]
      { body := { terms := [{ factors := [.read "S" [.axis axJ, .axis axJ]] }] }
      , nonlin := .identity }]
  == some (.scan (.stateReadNotCausal "sc" "S" 0 0 0))

-- loop-axis-ignoring constant read `S[0]`: the advancing row has NO nonzero coefficient at all, so
-- it is not a look-back on the loop axis and its value depends on when the read happens. This is
-- the Jacobi/Gauss-Seidel discriminator `ScanTest.lean` Part 4 pins at the checker; here it is
-- rejected one layer earlier, at the source.
#guard rej [okBase] [.assign "S" [.iterNext axL]
      { body := { terms := [{ factors := [.read "S" [.const 0]] }] }, nonlin := .identity }]
  == some (.scan (.stateReadNotCausal "sc" "S" 0 0 0))

-- causality binds every step-block statement, not only the ones producing state results: a SCRATCH
-- statement reading the state ahead is rejected with the scratch statement's own index.
#guard rej [okBase]
    [ .assign "T" [] { body := { terms := [{ factors := [.read "S" [.shift axL 1]] }] }
                     , nonlin := .identity }
    , okRecur ]
  == some (.scan (.stateReadNotCausal "sc" "S" 0 0 0))

-- the term/factor locators are real positions, not placeholders: the offending read below sits at
-- term 1, factor 1.
#guard rej [okBase] [.assign "S" [.iterNext axL]
      { body := { terms :=
          [ { factors := [.read "X" [.axis axL]] }
          , { factors := [.read "X" [.axis axL], .read "S" [.shift axL 1]] } ] }
      , nonlin := .identity }]
  == some (.scan (.stateReadNotCausal "sc" "S" 0 1 1))

-- Source causality factor locator (predicate/mask parity thread): the SAME term-1 shape as the
-- fixture above, but with an Iverson predicate factor inserted IMMEDIATELY BEFORE the noncausal
-- state read. `compileScan`'s Phase-5 causality loop skips the `.iverson` factor yet keeps the
-- ORIGINAL all-factor index, so the noncausal `S[l + 1]` read now sits at all-factor index `fi = 2`
-- (not the filtered-read index `1`). The reported locator must therefore be `… "S" 0 1 2`: this is
-- the fixture that first EXERCISES the locator invariant with a real source Iverson, and a filtered-
-- read reindexing of the loop would (wrongly) report `1` here. Without the inserted Iverson the read
-- index and factor index coincide (they do in the donor above), so only an Iverson-bearing term can
-- separate them.
#guard rej [okBase] [.assign "S" [.iterNext axL]
      { body := { terms :=
          [ { factors := [.read "X" [.axis axL]] }
          , { factors := [ .read "X" [.axis axL]
                         , .iverson (.rel .eq (.embed (.const 0)) (.embed (.const 0)))
                         , .read "S" [.shift axL 1] ] } ] }
      , nonlin := .identity }]
  == some (.scan (.stateReadNotCausal "sc" "S" 0 1 2))

/-! ## Part 3: precedence

The first failure in the phase order `capability → input signature → shape → scan specialization`
wins, regardless of how many later phases the same program would also fail. -/

-- Unsupported nested syntax (phase A) PLUS a missing input signature (phase B): capability wins.
def emptySig : InputSignature := InputSignature.mk ({} : HashMap String TensorSignature)
#guard causeOf (prepareEvalPlan
    (rejSched [okBase] [badAffineLhs "S"]) emptySig)
  == some (.capability (.scatterOrAffineLhs "S: affine LHS slot"))

-- Valid syntax, an unsized scan axis (phase C/geometry-sizing) AND an orphan base (phase D pairing):
-- the shape failure wins, and the pairing failure is never reported. `axis l` — deliberately not
-- `iter l = 3` — leaves `l` with no pinned size, and no read constrains it.
def shapeBeforePairingSched : ScheduledProgram :=
  { decls := [.axis axL none]
  , stmts := [.scan "sc" [axL] [okBase] [] false]
  , env := {}, extNames := insert "S0" (∅ : Finset String)
  , explicitSizes := {} }
#guard causeOf (prepareEvalPlan shapeBeforePairingSched rejSig)
  == some (.shape (.unsizedAxis axL.uid (.scanIteration "l")))
-- and the SAME program with `l` pinned does report the pairing failure, proving the fixture above
-- is really about precedence and not about the pairing check being absent.
#guard rej [okBase] [] == some (.scan (.orphanBaseState "sc" "S"))

/-! ## Part 4: Thread 4 Task 4 — nonlinear scan source admission (accept path)

`compileScan` now admits and lowers unmasked pointwise/axiswise base/recurrence statements into the
`.assign → .pointwise`/`.axiswise` block-step chain. These fixtures pin that the compiled checked-Plan
output equals the value the legacy evaluator produces — the six values re-observed in
`papers/implementation_seeds/nonlinearity_route_fragments/nonlinear_scan_admission/OracleFixtureSeed.lean`
(§0.4 of this slice's plan). The value-bearing fixtures (4, 2/5, 11) run the whole pipeline through
`runPreparedDense`; the structural fixtures (1, 3, 12, 13) pin acceptance and the materialized shape
for shapes whose legacy value is not one of the pinned numbers. -/

def t4rhs (name : String) (idxs : List IdxExpr) (nonlin := Nonlin.identity) : RHSExpr :=
  { body := { terms := [{ factors := [.read name idxs] }] }, nonlin }
def t4rhs2 (a : String) (ai : List IdxExpr) (b : String) (bi : List IdxExpr)
    (nonlin := Nonlin.identity) : RHSExpr :=
  { body := { terms := [{ factors := [.read a ai, .read b bi] }] }, nonlin }

/-- Compile a source scan, run it through the checked Plan path (`runPreparedDense`), and assert the
    materialized output tensor approx-equals `expected`. Reports the real compile/run cause on
    failure rather than a bare `none`. -/
def t4run (name : String) (sched : ScheduledProgram) (inputs : HashMap String DenseTensor)
    (outName : String) (expected : DenseTensor) : Except String Unit :=
  match prepareEvalPlan sched (InputSignature.ofDenseInputs inputs) with
  | .error e => .error s!"{name}: expected acceptance, got {render e.cause}"
  | .ok p =>
    match runPreparedDense p inputs with
    | .error f => .error s!"{name}: run failed: {repr f.cause}"
    | .ok report =>
      match report.env[outName]? with
      | none => .error s!"{name}: no materialized {outName}"
      | some tOut =>
          if DenseTensor.approxEq tOut expected then .ok ()
          else .error
            s!"{name}: got {repr tOut.shape}/{repr tOut.data}, expected {repr expected.shape}/{repr expected.data}"

/-- Compile a source scan, run it, and assert only the materialized output SHAPE (a structural
    acceptance check for shapes whose legacy value is not one of the pinned §0.4 numbers). -/
def t4shape (name : String) (sched : ScheduledProgram) (inputs : HashMap String DenseTensor)
    (outName : String) (expectedShape : List Nat) : Except String Unit :=
  match prepareEvalPlan sched (InputSignature.ofDenseInputs inputs) with
  | .error e => .error s!"{name}: expected acceptance, got {render e.cause}"
  | .ok p =>
    match runPreparedDense p inputs with
    | .error f => .error s!"{name}: run failed: {repr f.cause}"
    | .ok report =>
      match report.env[outName]? with
      | none => .error s!"{name}: no materialized {outName}"
      | some tOut =>
          if tOut.shape == expectedShape then .ok ()
          else .error s!"{name}: got shape {repr tOut.shape}, expected {repr expectedShape}"

/-- Source→checked DIFFERENTIAL for a scan: `t4run`'s checked-path value check PLUS the legacy
    reference evaluator (`evalScheduled`) on the same source `ScheduledProgram`, both asserted to
    approx-equal `expected`. Used by Slice 5.3's masked-scan fixtures so "the checked masked
    reduction" and "the reference masked reduction" are two separate, both-asserted facts. -/
def t4diff (name : String) (sched : ScheduledProgram) (inputs : HashMap String DenseTensor)
    (outName : String) (expected : DenseTensor) : Except String Unit :=
  match t4run name sched inputs outName expected with
  | .error m => .error m
  | .ok _ =>
    match evalScheduled sched inputs with
    | .error _ => .error s!"{name}: source (reference) eval failed"
    | .ok report =>
      match report.env[outName]? with
      | none => .error s!"{name}: source produced no {outName}"
      | some tOut =>
          if DenseTensor.approxEq tOut expected then .ok ()
          else .error
            s!"{name}: SOURCE got {repr tOut.shape}/{repr tOut.data}, expected {repr expected.data}"

/-! ### Fixture 4 — leading-axis pointwise scratch (value; = OracleFixtureSeed.fixture1)
`S[i,0]:=X[i]`; scratch `T[i]:=relu(S[i,l]·K[i])`; `S[i,l+1]:=T[i]`, `X=[-1,2]`, `K=[-2,3]`. -/
def p4i : AxisSpec := ⟨"i", 4141, .real⟩
def p4l : AxisSpec := ⟨"l", 4142, .nat⟩
def leadingPointwiseScratch : ScheduledProgram :=
  { decls := [.iter p4l 3]
  , stmts := [.scan "S" [p4l]
      [.assign "S" [.free p4i, .iterAt p4l 0] (t4rhs "X" [.axis p4i])]
      [ .assign "T" [.free p4i]
          (t4rhs2 "S" [.axis p4i, .axis p4l] "K" [.axis p4i] (.pointwise .relu))
      , .assign "S" [.free p4i, .iterNext p4l] (t4rhs "T" [.axis p4i]) ]
      false]
  , env := {}, extNames := {"X", "K"}
  , explicitSizes := ({} : HashMap UID Nat).insert p4l.uid 3 }
def leadingPointwiseScratchInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" ⟨[2], #[-1, 2]⟩).insert "K" ⟨[2], #[-2, 3]⟩
def leadingPointwiseScratchCheck : Except String Unit :=
  t4run "T4.4 leadingPointwiseScratch" leadingPointwiseScratch leadingPointwiseScratchInputs "S"
    ⟨[2, 3], #[-1, 2, 0, 2, 6, 18]⟩
run_cmd match leadingPointwiseScratchCheck with | .ok _ => pure () | .error m => throwError m

/-! ### Fixtures 2 and 5 — interleaved axiswise (value; = OracleFixtureSeed.fixture2)
`S[l+1, i., m+1] := normalize(S[l,i,m])` over two iteration axes; marker `.freeNorm i` at LHS index 1,
strictly between iteration slots 0 and 2. `X=[1,3]`, both extents 3. The marker's non-leading LHS
position makes this the retained-axis-mapping locator (Task 1 mutation 2). -/
def p2l : AxisSpec := ⟨"l", 4121, .nat⟩
def p2i : AxisSpec := ⟨"i", 4122, .real⟩
def p2m : AxisSpec := ⟨"m", 4123, .nat⟩
def interleavedAxiswise : ScheduledProgram :=
  { decls := [.iter p2l 3, .iter p2m 3]
  , stmts := [.scan "S" [p2l, p2m]
      [.assign "S" [.iterAt p2l 0, .free p2i, .iterAt p2m 0] (t4rhs "X" [.axis p2i])]
      [.assign "S" [.iterNext p2l, .freeNorm p2i, .iterNext p2m]
        (t4rhs "S" [.axis p2l, .axis p2i, .axis p2m] (.axiswise .normalize none))]
      false]
  , env := {}, extNames := {"X"}
  , explicitSizes := (({} : HashMap UID Nat).insert p2l.uid 3).insert p2m.uid 3 }
def interleavedAxiswiseInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[2], #[1, 3]⟩
def interleavedAxiswiseCheck : Except String Unit :=
  t4run "T4.2/5 interleavedAxiswise" interleavedAxiswise interleavedAxiswiseInputs "S"
    ⟨[3, 2, 3], #[1, 0, 0, 3, 0, 0, 0, 0.25, 0, 0, 0.75, 0, 0, 0, 0.25, 0, 0, 0.75]⟩
run_cmd match interleavedAxiswiseCheck with | .ok _ => pure () | .error m => throwError m

/-! ### Fixture 11 — pointwise nonlinear base, linear recurrence (value; = OracleFixtureSeed.fixture4)
base `S[i,0] := relu(X[i])`, recurrence `S[i,l+1] := S[i,l]·A[i]`, `X=[-2,3]`, `A=[2,-1]`. The base's
preactivation (`relu(X)`) and result differ on the negative input: this is the
preactivation-vs-result locator (Task 1 mutation 1). -/
def p11i : AxisSpec := ⟨"i", 4111, .real⟩
def p11l : AxisSpec := ⟨"l", 4112, .nat⟩
def nonlinearBase : ScheduledProgram :=
  { decls := [.iter p11l 3]
  , stmts := [.scan "S" [p11l]
      [.assign "S" [.free p11i, .iterAt p11l 0] (t4rhs "X" [.axis p11i] (.pointwise .relu))]
      [.assign "S" [.free p11i, .iterNext p11l]
        (t4rhs2 "S" [.axis p11i, .axis p11l] "A" [.axis p11i])]
      false]
  , env := {}, extNames := {"X", "A"}
  , explicitSizes := ({} : HashMap UID Nat).insert p11l.uid 3 }
def nonlinearBaseInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" ⟨[2], #[-2, 3]⟩).insert "A" ⟨[2], #[2, -1]⟩
def nonlinearBaseCheck : Except String Unit :=
  t4run "T4.11 nonlinearBase" nonlinearBase nonlinearBaseInputs "S" ⟨[2, 3], #[0, 0, 0, 3, -3, 3]⟩
run_cmd match nonlinearBaseCheck with | .ok _ => pure () | .error m => throwError m

/-! ### Fixture 1 — softmax recurrence, marker FIRST (local axis position 0; structural) -/
def p1l : AxisSpec := ⟨"l", 4101, .nat⟩
def p1j : AxisSpec := ⟨"j", 4102, .real⟩
def softmaxMarkerFirst : ScheduledProgram :=
  { decls := [.iter p1l 3]
  , stmts := [.scan "S" [p1l]
      [.assign "S" [.iterAt p1l 0, .free p1j] (t4rhs "X" [.axis p1j])]
      [.assign "S" [.iterNext p1l, .freeNorm p1j]
        (t4rhs "S" [.axis p1l, .axis p1j] (.axiswise .softmax none))]
      false]
  , env := {}, extNames := {"X"}
  , explicitSizes := ({} : HashMap UID Nat).insert p1l.uid 3 }
def softmaxMarkerFirstInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[2], #[1, 3]⟩
def softmaxMarkerFirstCheck : Except String Unit :=
  t4shape "T4.1 softmaxMarkerFirst" softmaxMarkerFirst softmaxMarkerFirstInputs "S" [3, 2]
run_cmd match softmaxMarkerFirstCheck with | .ok _ => pure () | .error m => throwError m

/-! ### Fixture 3 — normalize recurrence, marker LAST among several local axes (structural) -/
def p3l : AxisSpec := ⟨"l", 4131, .nat⟩
def p3a : AxisSpec := ⟨"a", 4132, .real⟩
def p3j : AxisSpec := ⟨"j", 4133, .real⟩
def normalizeMarkerLast : ScheduledProgram :=
  { decls := [.iter p3l 3]
  , stmts := [.scan "S" [p3l]
      [.assign "S" [.iterAt p3l 0, .free p3a, .free p3j] (t4rhs "X" [.axis p3a, .axis p3j])]
      [.assign "S" [.iterNext p3l, .free p3a, .freeNorm p3j]
        (t4rhs "S" [.axis p3l, .axis p3a, .axis p3j] (.axiswise .normalize none))]
      false]
  , env := {}, extNames := {"X"}
  , explicitSizes := ({} : HashMap UID Nat).insert p3l.uid 3 }
def normalizeMarkerLastInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[2, 2], #[1, 3, 2, 4]⟩
def normalizeMarkerLastCheck : Except String Unit :=
  t4shape "T4.3 normalizeMarkerLast" normalizeMarkerLast normalizeMarkerLastInputs "S" [3, 2, 2]
run_cmd match normalizeMarkerLastCheck with | .ok _ => pure () | .error m => throwError m

/-! ### Fixture 12 — nonlinear base over a 2-D free face plus point override (structural) -/
def p12i : AxisSpec := ⟨"i", 4151, .real⟩
def p12j : AxisSpec := ⟨"j", 4152, .real⟩
def p12l : AxisSpec := ⟨"l", 4153, .nat⟩
def nonlinearBaseFace : ScheduledProgram :=
  { decls := [.iter p12l 3]
  , stmts := [.scan "S" [p12l]
      [.assign "S" [.free p12i, .free p12j, .iterAt p12l 0]
        (t4rhs "X" [.axis p12i, .axis p12j] (.pointwise .relu))]
      [.assign "S" [.free p12i, .free p12j, .iterNext p12l]
        (t4rhs2 "S" [.axis p12i, .axis p12j, .axis p12l] "A" [.axis p12i])]
      false]
  , env := {}, extNames := {"X", "A"}
  , explicitSizes := ({} : HashMap UID Nat).insert p12l.uid 3 }
def nonlinearBaseFaceInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" ⟨[2, 2], #[-1, 2, 3, -4]⟩).insert "A" ⟨[2], #[1, 1]⟩
def nonlinearBaseFaceCheck : Except String Unit :=
  t4shape "T4.12 nonlinearBaseFace" nonlinearBaseFace nonlinearBaseFaceInputs "S" [2, 2, 3]
run_cmd match nonlinearBaseFaceCheck with | .ok _ => pure () | .error m => throwError m

/-! ### Fixture 13 — axiswise nonlinear base, linear recurrence (structural) -/
def p13i : AxisSpec := ⟨"i", 4161, .real⟩
def p13l : AxisSpec := ⟨"l", 4162, .nat⟩
def axiswiseBase : ScheduledProgram :=
  { decls := [.iter p13l 3]
  , stmts := [.scan "S" [p13l]
      [.assign "S" [.freeNorm p13i, .iterAt p13l 0] (t4rhs "X" [.axis p13i] (.axiswise .normalize none))]
      [.assign "S" [.free p13i, .iterNext p13l]
        (t4rhs2 "S" [.axis p13i, .axis p13l] "A" [.axis p13i])]
      false]
  , env := {}, extNames := {"X", "A"}
  , explicitSizes := ({} : HashMap UID Nat).insert p13l.uid 3 }
def axiswiseBaseInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" ⟨[2], #[1, 3]⟩).insert "A" ⟨[2], #[2, -1]⟩
def axiswiseBaseCheck : Except String Unit :=
  t4shape "T4.13 axiswiseBase" axiswiseBase axiswiseBaseInputs "S" [2, 3]
run_cmd match axiswiseBaseCheck with | .ok _ => pure () | .error m => throwError m

/-! ## Part 5: Thread 4 Task 4 — soundness matrix (publication/dependency + negative/write-safety)

Task 2 of the slice plan. The publication/dependency fixtures (6-10) pin that preactivations are
never published or state-written and that a nonlinear step's dependency wiring is correct; the
negative fixtures (14-19) pin that masked axiswise, an inconsistent `.freeNorm` marker, a `.freeNorm`
on a context axis, and a preactivation write source are all rejected at their named constructor. -/

/-- Compile a source scan and return its failure cause (`none` if accepted, itself a fixture failure
    for the negative cases). -/
def t4cause (sched : ScheduledProgram) (inputs : HashMap String DenseTensor) : Option PlanCompileCause :=
  causeOf (prepareEvalPlan sched (InputSignature.ofDenseInputs inputs))

/-! ### Fixture 6 — nonlinear scratch consumed by a later scratch (= OracleFixtureSeed.fixture5)
`T := relu(S[l]·A[l])`; `U := T·B[l]`; `S[l+1] := U`, `X=1`, `A=[2,-3,4]`, `B=[3,2,1]` ⇒ `S=[1,6,0]`.
Value plus the publication structural fact: only the state result is a block output; `T`/`U` are
internal (never materialized, never block outputs). -/
def p6l : AxisSpec := ⟨"l", 4601, .nat⟩
def scratchToScratchToState : ScheduledProgram :=
  { decls := [.iter p6l 3]
  , stmts := [.scan "S" [p6l]
      [.assign "S" [.iterAt p6l 0] (t4rhs "X" [])]
      [ .assign "T" [] (t4rhs2 "S" [.axis p6l] "A" [.axis p6l] (.pointwise .relu))
      , .assign "U" [] (t4rhs2 "T" [] "B" [.axis p6l])
      , .assign "S" [.iterNext p6l] (t4rhs "U" []) ]
      false]
  , env := {}, extNames := {"X", "A", "B"}
  , explicitSizes := ({} : HashMap UID Nat).insert p6l.uid 3 }
def scratchToScratchToStateInputs : HashMap String DenseTensor :=
  ((({} : HashMap String DenseTensor).insert "X" ⟨[], #[1]⟩).insert
    "A" ⟨[3], #[2, -3, 4]⟩).insert "B" ⟨[3], #[3, 2, 1]⟩
def fixture6Check : Except String Unit :=
  t4run "T4.6 scratchToScratchToState" scratchToScratchToState scratchToScratchToStateInputs "S"
    ⟨[3], #[1, 6, 0]⟩
run_cmd match fixture6Check with | .ok _ => pure () | .error m => throwError m
-- publication: `T`/`U` are neither materialized names nor step-block outputs; only `S`'s result is.
def fixture6Publication : Except String Unit :=
  withPrepared "T4.6 publication" scratchToScratchToState scratchToScratchToStateInputs (fun p => do
    match scanAt p 0 with
    | none => .error "T4.6: step 0 is not a scan"
    | some s => do
        expectEq "T4.6: materialized names" (p.bindings.materializedNames.map (·.name)) #["S"]
        expectEq "T4.6: step block output count" s.stepBlock.outputs.size 1)
run_cmd match fixture6Publication with | .ok _ => pure () | .error m => throwError m

/-! ### Fixture 7 — nonlinear scratch consumed by a state (clone fixture 6, drop the second scratch)
`T := relu(S[l]·A[l])`; `S[l+1] := T`, same inputs ⇒ `S=[1,2,0]`. -/
def p7l : AxisSpec := ⟨"l", 4701, .nat⟩
def scratchToState : ScheduledProgram :=
  { decls := [.iter p7l 3]
  , stmts := [.scan "S" [p7l]
      [.assign "S" [.iterAt p7l 0] (t4rhs "X" [])]
      [ .assign "T" [] (t4rhs2 "S" [.axis p7l] "A" [.axis p7l] (.pointwise .relu))
      , .assign "S" [.iterNext p7l] (t4rhs "T" []) ]
      false]
  , env := {}, extNames := {"X", "A"}
  , explicitSizes := ({} : HashMap UID Nat).insert p7l.uid 3 }
def scratchToStateInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" ⟨[], #[1]⟩).insert "A" ⟨[3], #[2, -3, 4]⟩
def fixture7Check : Except String Unit :=
  t4run "T4.7 scratchToState" scratchToState scratchToStateInputs "S" ⟨[3], #[1, 2, 0]⟩
run_cmd match fixture7Check with | .ok _ => pure () | .error m => throwError m

/-! ### Fixture 8 — persistent state's own nonlinear recurrence (base + recurrence writes)
`S[j,0]:=X[j]`; `S[j,l+1] := relu(S[j,l]·A[j])`, `X=[1]`, `A=[-1]`, extent 2 ⇒ `S=[1,0]`. -/
def p8j : AxisSpec := ⟨"j", 4811, .real⟩
def p8l : AxisSpec := ⟨"l", 4812, .nat⟩
def persistentNonlinRecur : ScheduledProgram :=
  { decls := [.iter p8l 2]
  , stmts := [.scan "S" [p8l]
      [.assign "S" [.free p8j, .iterAt p8l 0] (t4rhs "X" [.axis p8j])]
      [.assign "S" [.free p8j, .iterNext p8l]
        (t4rhs2 "S" [.axis p8j, .axis p8l] "A" [.axis p8j] (.pointwise .relu))]
      false]
  , env := {}, extNames := {"X", "A"}
  , explicitSizes := ({} : HashMap UID Nat).insert p8l.uid 2 }
def persistentNonlinRecurInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" ⟨[1], #[1]⟩).insert "A" ⟨[1], #[-1]⟩
def fixture8Check : Except String Unit :=
  t4run "T4.8 persistentNonlinRecur" persistentNonlinRecur persistentNonlinRecurInputs "S"
    ⟨[1, 2], #[1, 0]⟩
run_cmd match fixture8Check with | .ok _ => pure () | .error m => throwError m

/-! ### Fixture 9 — coupled linear/nonlinear states (= EvalExamplesTest example 5)
`G[j,0]:=X`; `G[j,l+1]:=relu(G·W_G + H·U)`; `H[j,0]:=Y`; `H[j,l+1]:=relu(H·W_H + G·V)`, all weights
`[[1]]`, `X=[1]`, `Y=[2]` ⇒ `G=[1,3,6]`, `H=[2,3,6]`. -/
def cj : AxisSpec := ⟨"j", 4911, .real⟩
def ck : AxisSpec := ⟨"k", 4912, .real⟩
def cl : AxisSpec := ⟨"l", 4913, .nat⟩
def coupledScan : ScheduledProgram :=
  { decls := [.iter cl 3]
  , stmts := [.scan "G" [cl]
      [ .assign "G" [.free cj, .iterAt cl 0] (t4rhs "X" [.axis cj])
      , .assign "H" [.free cj, .iterAt cl 0] (t4rhs "Y" [.axis cj]) ]
      [ .assign "G" [.free cj, .iterNext cl]
          { body := { terms :=
              [ { factors := [.read "G" [.axis cj, .axis cl], .read "W_G" [.axis cj, .axis ck]] }
              , { factors := [.read "H" [.axis cj, .axis cl], .read "U" [.axis cj, .axis ck]] } ] }
          , nonlin := .pointwise .relu }
      , .assign "H" [.free cj, .iterNext cl]
          { body := { terms :=
              [ { factors := [.read "H" [.axis cj, .axis cl], .read "W_H" [.axis cj, .axis ck]] }
              , { factors := [.read "G" [.axis cj, .axis cl], .read "V" [.axis cj, .axis ck]] } ] }
          , nonlin := .pointwise .relu } ]
      false]
  , env := {}
  , extNames := insert "X" (insert "Y" (insert "W_G" (insert "U" (insert "W_H"
      (insert "V" (∅ : Finset String))))))
  , explicitSizes := ({} : HashMap UID Nat).insert cl.uid 3 }
def coupledScanInputs : HashMap String DenseTensor :=
  ((((((({} : HashMap String DenseTensor).insert "X" ⟨[1], #[1]⟩).insert "Y" ⟨[1], #[2]⟩).insert
    "W_G" ⟨[1, 1], #[1]⟩).insert "U" ⟨[1, 1], #[1]⟩).insert "W_H" ⟨[1, 1], #[1]⟩).insert
    "V" ⟨[1, 1], #[1]⟩)
def fixture9CheckG : Except String Unit :=
  t4run "T4.9 coupled G" coupledScan coupledScanInputs "G" ⟨[1, 3], #[1, 3, 6]⟩
def fixture9CheckH : Except String Unit :=
  t4run "T4.9 coupled H" coupledScan coupledScanInputs "H" ⟨[1, 3], #[2, 3, 6]⟩
run_cmd match fixture9CheckG with | .ok _ => pure () | .error m => throwError m
run_cmd match fixture9CheckH with | .ok _ => pure () | .error m => throwError m

/-! ### Fixture 10 — exact capture order after a nonlinear logical statement
`T := relu(S[l]·A[l])`; `S[l+1] := T·C[l]` — the external `C` is read in the statement AFTER the
nonlinear `T`. The step-block captures must be `S` (state), then `A`, then `C` in source order; a
capture set derived out of order (mutation 6) reorders them. -/
def p10l : AxisSpec := ⟨"l", 41001, .nat⟩
def captureOrderScan : ScheduledProgram :=
  { decls := [.iter p10l 3]
  , stmts := [.scan "S" [p10l]
      [.assign "S" [.iterAt p10l 0] (t4rhs "X" [])]
      [ .assign "T" [] (t4rhs2 "S" [.axis p10l] "A" [.axis p10l] (.pointwise .relu))
      , .assign "S" [.iterNext p10l] (t4rhs2 "T" [] "C" [.axis p10l]) ]
      false]
  , env := {}, extNames := insert "X" (insert "A" (insert "C" (∅ : Finset String)))
  , explicitSizes := ({} : HashMap UID Nat).insert p10l.uid 3 }
def captureOrderInputs : HashMap String DenseTensor :=
  ((({} : HashMap String DenseTensor).insert "X" ⟨[], #[1]⟩).insert "A" ⟨[3], #[2, -3, 4]⟩).insert
    "C" ⟨[3], #[1, 1, 1]⟩
def fixture10Check : Except String Unit :=
  withPrepared "T4.10 captureOrder" captureOrderScan captureOrderInputs (fun p => do
    match scanAt p 0 with
    | none => .error "T4.10: step 0 is not a scan"
    | some s =>
        expectEq "T4.10: step capture sources"
          (s.stepCaptures.map (·.source)) #[.state 0, .external 1, .external 2])
run_cmd match fixture10Check with | .ok _ => pure () | .error m => throwError m

/-! ### Fixtures 14-15 — masked axiswise scan (Slice 5.3: rejection → ACCEPT + value)

Formerly negative (`maskedAxiswiseNotSupported`); Slice 5.3 lowers a scan-block mask through
`lowerMaskPredicate` (local NON-SEEDED output basis, empty pins) so both are now accepted and
value-checked, source→checked differential. Both `t4mask`s below are trivially true, so the value
equals the unmasked reduction — what they pin is that a masked base / masked recurrence COMPILES and
RUNS through the checked path (mask width check, non-seeded basis) and agrees with the reference. -/

def t4mask : BoolExpr := .rel .eq (.embed (.const 0)) (.embed (.const 0))

/-- Fixture 14 — masked axiswise BASE, now accepted. `normalize(where 0=0)(X)` over `i`, then
    `S[i,l+1] := S[i,l]·A[i]`. `X=[1,3]`→base `normalize([1,3])=[0.25,0.75]`; `A=[2,-1]` ⇒ history
    (row-major `S[i][l]`) `[0.25,0.5,1.0, 0.75,-0.75,0.75]`. -/
def p14i : AxisSpec := ⟨"i", 41401, .real⟩
def p14l : AxisSpec := ⟨"l", 41402, .nat⟩
def maskedAxiswiseBase : ScheduledProgram :=
  { decls := [.iter p14l 3]
  , stmts := [.scan "S" [p14l]
      [.assign "S" [.freeNorm p14i, .iterAt p14l 0]
        (t4rhs "X" [.axis p14i] (.axiswise .normalize (some t4mask)))]
      [.assign "S" [.free p14i, .iterNext p14l]
        (t4rhs2 "S" [.axis p14i, .axis p14l] "A" [.axis p14i])]
      false]
  , env := {}, extNames := {"X", "A"}
  , explicitSizes := ({} : HashMap UID Nat).insert p14l.uid 3 }
def maskedAxiswiseBaseInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" ⟨[2], #[1, 3]⟩).insert "A" ⟨[2], #[2, -1]⟩
def maskedAxiswiseBaseCheck : Except String Unit :=
  t4diff "T5.3 maskedAxiswiseBase" maskedAxiswiseBase maskedAxiswiseBaseInputs "S"
    ⟨[2, 3], #[0.25, 0.5, 1.0, 0.75, -0.75, 0.75]⟩
run_cmd match maskedAxiswiseBaseCheck with | .ok _ => pure () | .error m => throwError m

/-- Fixture 15 — masked axiswise RECURRENCE, now accepted. `S[l+1,i] := normalize(where 0=0)(S[l,i])`
    over `i`; `S[0]=X=[1,3]` ⇒ history (row-major `S[l][i]`) `[1,3, 0.25,0.75, 0.25,0.75]`. -/
def p15i : AxisSpec := ⟨"i", 41501, .real⟩
def p15l : AxisSpec := ⟨"l", 41502, .nat⟩
def maskedAxiswiseRecur : ScheduledProgram :=
  { decls := [.iter p15l 3]
  , stmts := [.scan "S" [p15l]
      [.assign "S" [.iterAt p15l 0, .free p15i] (t4rhs "X" [.axis p15i])]
      [.assign "S" [.iterNext p15l, .freeNorm p15i]
        (t4rhs "S" [.axis p15l, .axis p15i] (.axiswise .normalize (some t4mask)))]
      false]
  , env := {}, extNames := {"X"}
  , explicitSizes := ({} : HashMap UID Nat).insert p15l.uid 3 }
def maskedAxiswiseRecurInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[2], #[1, 3]⟩
def maskedAxiswiseRecurCheck : Except String Unit :=
  t4diff "T5.3 maskedAxiswiseRecur" maskedAxiswiseRecur maskedAxiswiseRecurInputs "S"
    ⟨[3, 2], #[1, 3, 0.25, 0.75, 0.25, 0.75]⟩
run_cmd match maskedAxiswiseRecurCheck with | .ok _ => pure () | .error m => throwError m

/-! ### Fixture — Seeded-axis-zero parity (Slice 5.3)

The recurrence donor (fixture 15) with `where l = 0`. `l` is the SEEDED scan axis (`.iterNext`), so
it is ABSENT from the mask's non-seeded output basis `[i]`; `lowerMaskPredicate` densifies it to no
column and its EMPTY pins never bind it, so `l` evaluates as coordinate 0 at EVERY step. Hence
`l = 0` is TRUE every step ⇒ no masking ⇒ the value equals fixture 15's unmasked recurrence. Were
live scan context substituted for `l` (mutation 4), `l = 0` would be false at `l = 1`, all-masking
that step's row → zeros, giving `[1,3,0.25,0.75,0,0]` instead. -/
def p9i : AxisSpec := ⟨"i", 41901, .real⟩
def p9l : AxisSpec := ⟨"l", 41902, .nat⟩
def seededAxisZeroMask : BoolExpr := .rel .eq (.embed (.axis p9l)) (.embed (.const 0))
def seededAxisZero : ScheduledProgram :=
  { decls := [.iter p9l 3]
  , stmts := [.scan "S" [p9l]
      [.assign "S" [.iterAt p9l 0, .free p9i] (t4rhs "X" [.axis p9i])]
      [.assign "S" [.iterNext p9l, .freeNorm p9i]
        (t4rhs "S" [.axis p9l, .axis p9i] (.axiswise .normalize (some seededAxisZeroMask)))]
      false]
  , env := {}, extNames := {"X"}
  , explicitSizes := ({} : HashMap UID Nat).insert p9l.uid 3 }
def seededAxisZeroInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[2], #[1, 3]⟩
def seededAxisZeroCheck : Except String Unit :=
  t4diff "T5.3 seededAxisZero" seededAxisZero seededAxisZeroInputs "S"
    ⟨[3, 2], #[1, 3, 0.25, 0.75, 0.25, 0.75]⟩
run_cmd match seededAxisZeroCheck with | .ok _ => pure () | .error m => throwError m

/-! ### Fixture — Eliminated `.free` scan coordinate (Slice 5.3, template6-derived)

A `c`-scan whose base reduces over a SEPARATE `.freeNorm i` while retaining a non-seeded `.free r`,
with base mask `where r ≠ 0`. `r` is NOT the reduction axis, yet it is a non-seeded output axis, so
it keeps its own column in the mask basis `[r, i]` and the mask sees its ACTUAL coordinate. With
`Z=[[1,3],[2,6]]`: the `r=0` face is all-masked (`0≠0` false) → zeros; the `r=1` face includes and
`normalize([2,6])=[0.25,0.75]`. The recurrence copies each `c=0` face forward to `c=1`. Substituting
0 for `r`'s coordinate during lowering (mutation 5) would all-mask the `r=1` face too → all zeros. -/
def p10r : AxisSpec := ⟨"r", 42010, .nat⟩
def p10i : AxisSpec := ⟨"i", 42011, .real⟩
def p10c : AxisSpec := ⟨"c", 42012, .nat⟩
def elimFreeMask : BoolExpr := .rel .ne (.embed (.axis p10r)) (.embed (.const 0))
def eliminatedFree : ScheduledProgram :=
  { decls := [.iter p10c 2]
  , stmts := [.scan "G" [p10c]
      [.assign "G" [.free p10r, .freeNorm p10i, .iterAt p10c 0]
        (t4rhs "Z" [.axis p10r, .axis p10i] (.axiswise .normalize (some elimFreeMask)))]
      [.assign "G" [.free p10r, .free p10i, .iterNext p10c]
        (t4rhs "G" [.axis p10r, .axis p10i, .axis p10c])]
      false]
  , env := {}, extNames := {"Z"}
  , explicitSizes := ((({} : HashMap UID Nat).insert p10r.uid 2).insert p10i.uid 2).insert p10c.uid 2 }
def eliminatedFreeInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "Z" ⟨[2,2], #[1, 3, 2, 6]⟩
def eliminatedFreeCheck : Except String Unit :=
  t4diff "T5.3 eliminatedFree" eliminatedFree eliminatedFreeInputs "G"
    ⟨[2, 2, 2], #[0, 0, 0, 0, 0.25, 0.25, 0.75, 0.75]⟩
run_cmd match eliminatedFreeCheck with | .ok _ => pure () | .error m => throwError m

/-! ### Fixture — Eliminated `.freeNorm` scan coordinate (Slice 5.3, exact source)

`iter r = 2, c = 2; tensor Z(r); G[r., 0] := normalize(where r ≠ 0)(Z[r]); G[r+1, c+1] := G[r, c]`,
`Z=[1,3]`. Here the ELIMINATED (reduction, `.freeNorm`) axis `r` is itself the mask's only basis
axis: `normalize(where r≠0)` over `r` excludes `r=0` and keeps `r=1` (`Z=3`) ⇒ base column
`G[:,0]=[0,1]`; the diagonal recurrence copies `G[0,0]→G[1,1]`. Source == checked == hand-expected
`[0,0,1,0]` (shape `[2,2]`). Zeroing `r`'s coordinate during lowering (mutation 6) makes `r≠0` false
everywhere → all-masked → `G[:,0]=[0,0]` → all zeros. Pinned HERE, NOT by the Task 5.4 oracle. -/
def p11r : AxisSpec := ⟨"r", 42110, .nat⟩
def p11rNorm : AxisSpec := { p11r with kind := .real }
def p11c : AxisSpec := ⟨"c", 42111, .nat⟩
def elimFreeNormMask : BoolExpr := .rel .ne (.embed (.axis p11r)) (.embed (.const 0))
def eliminatedFreeNorm : ScheduledProgram :=
  { decls := [.iter p11r 2, .iter p11c 2]
  , stmts := [.scan "G" [p11r, p11c]
      [.assign "G" [.freeNorm p11rNorm, .iterAt p11c 0]
        (t4rhs "Z" [.axis p11r] (.axiswise .normalize (some elimFreeNormMask)))]
      [.assign "G" [.iterNext p11r, .iterNext p11c]
        (t4rhs "G" [.axis p11r, .axis p11c])]
      false]
  , env := {}, extNames := {"Z"}
  , explicitSizes := (({} : HashMap UID Nat).insert p11r.uid 2).insert p11c.uid 2 }
def eliminatedFreeNormInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "Z" ⟨[2], #[1, 3]⟩
def eliminatedFreeNormCheck : Except String Unit :=
  t4diff "T5.3 eliminatedFreeNorm" eliminatedFreeNorm eliminatedFreeNormInputs "G"
    ⟨[2, 2], #[0, 0, 1, 0]⟩
run_cmd match eliminatedFreeNormCheck with | .ok _ => pure () | .error m => throwError m

/-! ### Negative fixtures 16-19 -/

/-- Fixture 16 — `.freeNorm` marker on a `.pointwise` statement (inconsistent): rejected as
    `unmarkedReductionAxis` at `resolveNonlinAxis`. -/
def p16l : AxisSpec := ⟨"l", 41601, .nat⟩
def p16j : AxisSpec := ⟨"j", 41602, .real⟩
def freeNormPointwise : ScheduledProgram :=
  { decls := [.iter p16l 3]
  , stmts := [.scan "S" [p16l]
      [.assign "S" [.iterAt p16l 0, .free p16j] (t4rhs "X" [.axis p16j])]
      [.assign "S" [.iterNext p16l, .freeNorm p16j]
        (t4rhs "S" [.axis p16l, .axis p16j] (.pointwise .relu))]
      false]
  , env := {}, extNames := {"X"}
  , explicitSizes := ({} : HashMap UID Nat).insert p16l.uid 3 }
def freeNormPointwiseInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[2], #[1, 3]⟩
#guard t4cause freeNormPointwise freeNormPointwiseInputs
  == some (.nonlin (.unmarkedReductionAxis "S" 1))

/-- Fixture 17 — `.freeNorm` on a scan CONTEXT axis in a scratch: rejected as
    `contextAxisAsFreeOutput`. A scratch `T` normalizes over the scan's own iteration axis `l`, which
    is never a legal retained output axis. This is the locator for the scratch context-axis
    `.freeNorm` guard (mutation 5). -/
def p17l : AxisSpec := ⟨"l", 41701, .nat⟩
def p17lNorm : AxisSpec := { p17l with kind := .real }
def freeNormContextAxis : ScheduledProgram :=
  { decls := [.iter p17l 3]
  , stmts := [.scan "S" [p17l]
      [.assign "S" [.iterAt p17l 0] (t4rhs "X" [])]
      [ .assign "T" [.freeNorm p17lNorm] (t4rhs "S" [.axis p17l] (.axiswise .normalize none))
      , .assign "S" [.iterNext p17l] (t4rhs "T" [.axis p17l]) ]
      false]
  , env := {}, extNames := {"X"}
  , explicitSizes := ({} : HashMap UID Nat).insert p17l.uid 3 }
def freeNormContextAxisInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[], #[1]⟩
#guard t4cause freeNormContextAxis freeNormContextAxisInputs
  == some (.scan (.contextAxisAsFreeOutput "S" "T" 0 p17l.uid))

/-- Fixture 18 — a state write map that targets the PREACTIVATION slot instead of the published
    result slot is rejected by `checkScanPlan` as `writeSourceNotBlockOutput`, because the
    preactivation is never a block output. Built by compiling a real nonlinear scan
    (`persistentNonlinRecur`) and repointing its step write at the nonlinear step's source (the
    preactivation), which the compiler itself never does. -/
def fixture18Check : Except String Unit :=
  withPrepared "T4.18 stateWriteToPreact" persistentNonlinRecur persistentNonlinRecurInputs (fun p => do
    match scanAt p 0 with
    | none => .error "T4.18: step 0 is not a scan"
    | some raw =>
        let preacts := raw.stepBlock.steps.filterMap (fun st => match st with
          | .pointwise q => some q.sourceSlot | .axiswise a => some a.sourceSlot | .assign _ => none)
        match preacts[0]?, raw.stepWrites[0]? with
        | some preSlot, some w0 =>
            let bad := { raw with
              stepWrites := raw.stepWrites.set! 0 { w0 with outputSlot := preSlot } }
            match checkScanPlan p.plan.raw.tensorSigs bad with
            | .error (.writeSourceNotBlockOutput false 0 s) =>
                if s == preSlot then .ok ()
                else .error s!"T4.18: rejected slot {s}, expected preactivation {preSlot}"
            | other => .error s!"T4.18: expected writeSourceNotBlockOutput, got {repr other}"
        | _, _ => .error "T4.18: no preactivation step or step write found")
run_cmd match fixture18Check with | .ok _ => pure () | .error m => throwError m

/-- Fixture 19 — mixed identity + nonlinear state outputs: the block outputs hold each state's RESULT
    slot and no preactivation. `G` advances by an identity recurrence, `H` by a pointwise nonlinear
    one; the step block publishes exactly the two result slots. This is the sharper witness for the
    `Array.range`-outputs regression (Task 1 mutation 3, re-confirmed here). -/
def m19j : AxisSpec := ⟨"j", 41901, .real⟩
def m19l : AxisSpec := ⟨"l", 41902, .nat⟩
def mixedIdentityNonlinear : ScheduledProgram :=
  { decls := [.iter m19l 3]
  , stmts := [.scan "G" [m19l]
      [ .assign "G" [.free m19j, .iterAt m19l 0] (t4rhs "X" [.axis m19j])
      , .assign "H" [.free m19j, .iterAt m19l 0] (t4rhs "Y" [.axis m19j]) ]
      [ .assign "G" [.free m19j, .iterNext m19l] (t4rhs2 "G" [.axis m19j, .axis m19l] "A" [.axis m19j])
      , .assign "H" [.free m19j, .iterNext m19l]
          (t4rhs2 "H" [.axis m19j, .axis m19l] "B" [.axis m19j] (.pointwise .relu)) ]
      false]
  , env := {}, extNames := insert "X" (insert "Y" (insert "A" (insert "B" (∅ : Finset String))))
  , explicitSizes := ({} : HashMap UID Nat).insert m19l.uid 3 }
def mixedIdentityNonlinearInputs : HashMap String DenseTensor :=
  (((({} : HashMap String DenseTensor).insert "X" ⟨[1], #[1]⟩).insert "Y" ⟨[1], #[-1]⟩).insert
    "A" ⟨[1], #[2]⟩).insert "B" ⟨[1], #[-3]⟩
def fixture19Check : Except String Unit :=
  withPrepared "T4.19 mixedIdentityNonlinear" mixedIdentityNonlinear mixedIdentityNonlinearInputs
    (fun p => do
      match scanAt p 0 with
      | none => .error "T4.19: step 0 is not a scan"
      | some s => do
          -- two states published, each its own result slot; no preactivation leaks in.
          expectEq "T4.19: step output count" s.stepBlock.outputs.size 2
          expectEq "T4.19: materialized names" (p.bindings.materializedNames.map (·.name)) #["G", "H"])
run_cmd match fixture19Check with | .ok _ => pure () | .error m => throwError m

/-! ### Structural facts for the four freshly-authored oracle groups (§3.6)

The values of groups 1, 2, 4, 5 exist nowhere else, so asserting the number alone would pin a number
without pinning the shape it came from. These guards pin the shape each group's value must come from,
so a fixture that ran and returned the right number while exercising the wrong shape cannot pass. -/

-- group 1 (leadingPointwiseScratch): scratch `T`'s local axis is at slot index 0 with no `.iterAt`
-- slot, and `T` has exactly one writing statement.
#guard match leadingPointwiseScratch.stmts with
  | [.scan _ _ base recur _] =>
      (recur.filterMap (fun s => match s with | .assign "T" sl _ => some sl | _ => none)) == [[.free p4i]]
      && ((base ++ recur).filter (fun s => match s with | .assign "T" _ _ => true | _ => false)).length == 1
  | _ => false
-- group 2 (interleavedAxiswise): the `.freeNorm` slot sits at index 1, strictly between iteration
-- slots 0 and 2; unmasked normalize.
#guard match interleavedAxiswise.stmts with
  | [.scan _ _ _ [.assign _ slots rhs] _] =>
      slots == [.iterNext p2l, .freeNorm p2i, .iterNext p2m] && rhs.nonlin == .axiswise .normalize none
  | _ => false
-- group 4 (nonlinearBase): the base statement's nonlin is pointwise and the recurrence's is identity
-- — the opposite of groups 1/3.
#guard match nonlinearBase.stmts with
  | [.scan _ _ [.assign _ _ base] [.assign _ _ recur] _] =>
      base.nonlin == .pointwise .relu && recur.nonlin == .identity
  | _ => false
-- group 5 (scratchToScratchToState): three destinations `T`, `U`, `S` in dependency order; the two
-- scratches have no base write while the state does.
#guard match scratchToScratchToState.stmts with
  | [.scan _ _ base recur _] =>
      (recur.filterMap (fun s => match s with | .assign nm _ _ => some nm | _ => none)) == ["T", "U", "S"]
      && !(base.any (fun s => match s with | .assign "T" _ _ => true | _ => false))
      && !(base.any (fun s => match s with | .assign "U" _ _ => true | _ => false))
      && base.any (fun s => match s with | .assign "S" _ _ => true | _ => false)
  | _ => false

end LeanNCD.Eval.Plan.ScanCompileTest

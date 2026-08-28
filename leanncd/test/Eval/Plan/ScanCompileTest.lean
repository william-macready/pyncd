import LeanNCD.Eval.Plan.Compile

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
                         , factors := #[{ sourceSlot := 0, map := { coeffs := #[], bias := #[] }
                                        , sourceShape := #[], oobPolicy := .zeroPad }] }]
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
                , factors := #[{ sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
                               , sourceShape := #[3], oobPolicy := .zeroPad }] }
              , { iterationShape := #[2], contextPos := #[0], outputPos := #[], reductionPos := #[]
                , factors := #[{ sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }
                               , sourceShape := #[3], oobPolicy := .zeroPad }] }]
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
          #[{ sourceSlot := 2, map := { coeffs := #[], bias := #[] }
            , sourceShape := #[], oobPolicy := .zeroPad }]
        checkerAgrees "C" p 0)

run_cmd match scratchCheck with | .ok _ => pure () | .error m => throwError m

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
        expectEq "D-E: state read map" (t.factors.getD 0 default).map
          { coeffs := #[#[1, 0]], bias := #[0] }
        -- `M[k, l]`: read at the CURRENT coordinate — row 0 selects `k`, row 1 selects `l` with no
        -- bias — against `M`'s full declared shape, which is the history length, not the step count.
        expectEq "D-E: external read map" (t.factors.getD 1 default).map
          { coeffs := #[#[0, 1], #[1, 0]], bias := #[0, 0] }
        expectEq "D-E: external read shape" (t.factors.getD 1 default).sourceShape #[2, 4]
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
        expectEq "F: immediate read" ((a.terms.getD 0 default).factors.getD 0 default).map
          { coeffs := #[#[1]], bias := #[0] }
        expectEq "F: look-back read" ((a.terms.getD 1 default).factors.getD 0 default).map
          { coeffs := #[#[1]], bias := #[-2] }
        expectEq "F: zero padding" ((a.terms.getD 1 default).factors.getD 0 default).oobPolicy
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
          ((((s.stepBlock.steps.getD 0 default).assign?.getD default).terms.getD 0 default).factors.getD 0 default).map
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
        expectEq "I-J: pinned bias accumulation" (pointTerm.factors.getD 0 default).map
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
          ((a.terms.getD 0 default).factors.map (·.sourceSlot)) #[2, 3]
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

/-- Compile a one-axis playground program and return its failure cause (`none` if it was accepted —
    which is itself a fixture failure everywhere below). -/
def rej (base recur : List Stmt) : Option PlanCompileCause :=
  causeOf (prepareEvalPlan (rejSched base recur) rejSig)

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

def badFreeNorm (nm : String) (adv : LHSSlot) : Stmt := .assign nm [.freeNorm axJ, adv]
  { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }
def badAffineLhs (nm : String) : Stmt := .assign nm [.affine (.axis axL)]
  { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity }
def badAgg (nm : String) (adv : LHSSlot) (op : AggOp) : Stmt := .assign nm [adv]
  { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity, agg := op }
def badNonlin (nm : String) (adv : LHSSlot) (n : Nonlin) : Stmt := .assign nm [adv]
  { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := n }
def badIverson (nm : String) (adv : LHSSlot) : Stmt := .assign nm [adv]
  { body := { terms := [{ factors := [.iverson (.rel .eq (.embed (.const 0)) (.embed (.const 0)))] }] }
  , nonlin := .identity }
def badUnary (nm : String) (adv : LHSSlot) : Stmt := .assign nm [adv]
  { body := { terms := [{ factors := [.unaryFn .log "X" [.axis axL]] }] }, nonlin := .identity }
def badScatter (nm : String) : Stmt :=
  .scatter nm [] { body := { terms := [] }, nonlin := .identity } {}
def badRecurMorphism (nm : String) : Stmt := .recurMorphism nm axL default

def pinL : LHSSlot := .iterAt axL 0
def nextL : LHSSlot := .iterNext axL

-- in the BASE list
#guard rej [badFreeNorm "S" pinL] [okRecur] == some (.capability (.unsupportedLhsSlot "S: freeNorm j"))
#guard rej [badAffineLhs "S"] [okRecur] == some (.capability (.scatterOrAffineLhs "S: affine LHS slot"))
#guard rej [badAgg "S" pinL .max] [okRecur] == some (.capability (.unsupportedAgg "S: max aggregation"))
#guard rej [badAgg "S" pinL .min] [okRecur] == some (.capability (.unsupportedAgg "S: min aggregation"))
#guard rej [badNonlin "S" pinL (.pointwise .relu)] [okRecur]
  == some (.capability (.unsupportedNonlin "S: pointwise nonlinearity"))
#guard rej [badNonlin "S" pinL (.axiswise .softmax none)] [okRecur]
  == some (.capability (.unsupportedNonlin "S: axiswise nonlinearity"))
#guard rej [badIverson "S" pinL] [okRecur] == some (.capability (.maskOrPredicate "S: iverson factor"))
#guard rej [badUnary "S" pinL] [okRecur] == some (.capability (.unaryFactor "S: unary function on X"))
#guard rej [badScatter "S"] [okRecur] == some (.capability (.scatterOrAffineLhs "S"))
#guard rej [badRecurMorphism "S"] [okRecur] == some (.capability (.recurrenceOrCallback "S"))

-- in the RECURRENCE list
#guard rej [okBase] [badFreeNorm "S" nextL] == some (.capability (.unsupportedLhsSlot "S: freeNorm j"))
#guard rej [okBase] [badAffineLhs "S"] == some (.capability (.scatterOrAffineLhs "S: affine LHS slot"))
#guard rej [okBase] [badAgg "S" nextL .max] == some (.capability (.unsupportedAgg "S: max aggregation"))
#guard rej [okBase] [badAgg "S" nextL .min] == some (.capability (.unsupportedAgg "S: min aggregation"))
#guard rej [okBase] [badNonlin "S" nextL (.pointwise .relu)]
  == some (.capability (.unsupportedNonlin "S: pointwise nonlinearity"))
#guard rej [okBase] [badNonlin "S" nextL (.axiswise .softmax none)]
  == some (.capability (.unsupportedNonlin "S: axiswise nonlinearity"))
#guard rej [okBase] [badIverson "S" nextL] == some (.capability (.maskOrPredicate "S: iverson factor"))
#guard rej [okBase] [badUnary "S" nextL] == some (.capability (.unaryFactor "S: unary function on X"))
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

-- a base read of a name that is neither a state nor an available outer tensor.
#guard rej [.assign "S" [.iterAt axL 0]
      { body := { terms := [{ factors := [.read "NOPE" []] }] }, nonlin := .identity }] [okRecur]
  == some (.scan (.blockReadNotAvailable "sc" true 0 "NOPE" .unknownName))

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
-- separate code paths).
#guard rej [okBase]
    [ .assign "T" [] { body := { terms := [{ factors := [.read "NOPE" []] }] }
                     , nonlin := .identity }
    , okRecur ]
  == some (.scan (.blockReadNotAvailable "sc" false 0 "NOPE" .unknownName))

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

/-! ## Part 3: precedence

The first failure in the phase order `capability → input signature → shape → scan specialization`
wins, regardless of how many later phases the same program would also fail. -/

-- Unsupported nested syntax (phase A) PLUS a missing input signature (phase B): capability wins.
def emptySig : InputSignature := InputSignature.mk ({} : HashMap String TensorSignature)
#guard causeOf (prepareEvalPlan
    (rejSched [okBase] [badNonlin "S" nextL (.pointwise .relu)]) emptySig)
  == some (.capability (.unsupportedNonlin "S: pointwise nonlinearity"))

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

end LeanNCD.Eval.Plan.ScanCompileTest

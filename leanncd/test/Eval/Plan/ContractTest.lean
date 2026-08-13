import LeanNCD.DSL.Ast
import LeanNCD.DSL.Pipeline.Types
import LeanNCD.Eval.Entry

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

/-- A `Stmt` is accepted only if every LHS slot, the aggregation op, the nonlinearity, and every
    factor classify as accepted. The sub-construct order (LHS slots, then `agg`, then nonlin, then
    factors) is a locally-chosen deterministic order for this classifier — it is NOT derived from
    §4.2/A.4's phase-level `prepareEvalPlan` ordering (that total order governs coarser phases:
    capability preflight, signature validation, shape inference, ...; it says nothing about the
    relative order of sub-constructs within one already-capability-checked statement). `agg` is
    checked right after the LHS slot because both are properties of the assignment's shape/target
    rather than its value expression, ahead of `nonlin`/factors which classify the RHS value
    computation. The first rejected sub-construct determines the reported category. -/
def classifyStmt : Stmt → Classification
  | .assign _ slots rhs =>
      match slots.findSome? (fun s => match classifyLHSSlot s with
        | .accepted => none | .rejected c => some c) with
      | some c => .rejected c
      | none =>
          match classifyAggOp rhs.agg with
          | .rejected c => .rejected c
          | .accepted =>
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
-- LHS ok, agg rejected.
#guard classifyStmt (.assign "Y" [.free ⟨"i", 0, .nat⟩]
  { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity, agg := .max }) ==
  .rejected "unsupportedAgg"
-- LHS+agg ok, nonlin rejected.
#guard classifyStmt (.assign "Y" [.free ⟨"i", 0, .nat⟩]
  { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .pointwise .relu }) ==
  .rejected "unsupportedNonlin"
-- LHS+agg+nonlin ok, factor rejected.
#guard classifyStmt (.assign "Y" [.free ⟨"i", 0, .nat⟩]
  { body := { terms := [{ factors := [.unaryFn .log "X" []] }] }, nonlin := .identity }) ==
  .rejected "unaryFactor"
#guard classifyScanStmt (.scan "s" [] [] [] false) == .rejected "scanNode"
#guard classifyScanStmt (.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
  { body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })) == .accepted
end

-- NumericMode: deferred to C1/C2, where it is defined; Wave C admits only `reference64SumProduct`.

open LeanNCD.Eval (DenseTensor)

private def expectTensor (t : Option DenseTensor) (shape : List Nat) (data : Array Float) : Bool :=
  t.map (fun d => d.shape == shape && d.data == data) |>.getD false

namespace LeanNCD.PlanContract.Fixtures
open LeanNCD LeanNCD.Eval Std

/-- `Y[i] := X[i - 2]`: for `i = 0, 1` the read is out of range (padded 0); for `i = 2` the read is
    `X[0]`. Only `X[0]` is ever read — `X[1]`/`X[2]` are present but unused, which is itself part
    of the pin (a negative-shift read must not accidentally consult a neighboring in-range index). -/
private def negShiftProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := X[i - 2]
}

private def negShiftInputs (x0 : Float) : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[3], #[x0, 20.0, 30.0]⟩

-- Baseline: X = [10, 20, 30] → Y = [0, 0, 10] (verified against the real evaluator).
run_cmd do
  match TLProgram.eval negShiftProg (negShiftInputs 10.0) with
  | .error e => throwError s!"negShift baseline eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Y"]? [3] #[0.0, 0.0, 10.0] do
        throwError s!"negShift baseline mismatch: {repr (report.env["Y"]?)}"

-- Mutation: only X[0] is ever read (i=2 reads index 0), so changing X[0] must change Y[2];
-- verified against the real evaluator (10 → 99 flows through to Y[2]).
run_cmd do
  match TLProgram.eval negShiftProg (negShiftInputs 99.0) with
  | .error e => throwError s!"negShift mutation eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Y"]? [3] #[0.0, 0.0, 99.0] do
        throwError s!"negShift mutation did not change as expected: {repr (report.env["Y"]?)}"

/-- `Y[i, j] := X[2*i + j]` over `i:2, j:3`, X fully sized (no padding — that's the previous
    fixture's concern). Row-major: Y[0,·] = X[0,1,2], Y[1,·] = X[2,3,4]. -/
private def multiAxisProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  Y[i, j] := X[2 * i + j]
}

private def multiAxisInputs (x4 : Float) : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[6], #[1.0, 2.0, 3.0, 4.0, x4, 6.0]⟩

-- Baseline: verified Y = [1,2,3, 3,4,5].
run_cmd do
  match TLProgram.eval multiAxisProg (multiAxisInputs 5.0) with
  | .error e => throwError s!"multiAxis baseline eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Y"]? [2, 3] #[1.0, 2.0, 3.0, 3.0, 4.0, 5.0] do
        throwError s!"multiAxis baseline mismatch: {repr (report.env["Y"]?)}"

-- Mutation: X[4] is read only by Y[1,2] (2*1+2=4); verified Y[1,2] alone changes to 99.
run_cmd do
  match TLProgram.eval multiAxisProg (multiAxisInputs 99.0) with
  | .error e => throwError s!"multiAxis mutation eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Y"]? [2, 3] #[1.0, 2.0, 3.0, 3.0, 4.0, 99.0] do
        throwError s!"multiAxis mutation did not isolate to Y[1,2]: {repr (report.env["Y"]?)}"

/-- `Y[i] := A[i] · B[j]` contracted over `j`: `A[i]`'s own read never mentions `j` (its densified
    affine map over the term basis `{i, j}` has a zero column for `j`), yet §7.4 requires `A[i]` be
    folded once per coordinate of `j`, not read once and treated as independent of the reduction.
    NOTE: for a pure sum-product term this value is mathematically identical whether `A[i]` is
    folded per-`j` or hoisted and multiplied by `Σ_j B[j]` once (multiplication distributes over
    addition) — this fixture pins the expected value and shape precisely; it does not by itself
    discriminate that specific implementation strategy. (§7.4's warning becomes value-discriminating
    once a non-distributive algebra, e.g. `max` reduction, exists — out of scope for C0.) -/
private def zeroCoeffProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  Y[i] := A[i] · B[j]
}

private def zeroCoeffInputs (b1 : Float) : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" ⟨[2], #[10.0, 100.0]⟩).insert "B" ⟨[3], #[1.0, b1, 3.0]⟩

-- Baseline: B = [1,2,3], ΣB = 6 → Y = A * 6 = [60, 600] (verified).
run_cmd do
  match TLProgram.eval zeroCoeffProg (zeroCoeffInputs 2.0) with
  | .error e => throwError s!"zeroCoeff baseline eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Y"]? [2] #[60.0, 600.0] do
        throwError s!"zeroCoeff baseline mismatch: {repr (report.env["Y"]?)}"

-- Mutation: B[1] 2 → 20, ΣB = 24 → Y = A * 24 = [240, 2400] (verified).
run_cmd do
  match TLProgram.eval zeroCoeffProg (zeroCoeffInputs 20.0) with
  | .error e => throwError s!"zeroCoeff mutation eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Y"]? [2] #[240.0, 2400.0] do
        throwError s!"zeroCoeff mutation did not change as expected: {repr (report.env["Y"]?)}"

/-- `X` is produced once and read by two later statements (`Y` and `Z`) — pins that fan-out reuse
    of one tensor slot is ordinary, not a special case requiring re-materialization. -/
private def fanOutProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  X[i] := A[i]
  Y[i] := X[i]
  Z[i] := X[i] + Y[i]
}

private def fanOutInputs (a0 : Float) : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "A" ⟨[2], #[a0, 20.0]⟩

-- Baseline: A = [10, 20] → X = [10,20], Y = [10,20], Z = X+Y = [20,40] (verified).
run_cmd do
  match TLProgram.eval fanOutProg (fanOutInputs 10.0) with
  | .error e => throwError s!"fanOut baseline eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["X"]? [2] #[10.0, 20.0] do
        throwError s!"fanOut baseline X mismatch: {repr (report.env["X"]?)}"
      unless expectTensor report.env["Y"]? [2] #[10.0, 20.0] do
        throwError s!"fanOut baseline Y mismatch: {repr (report.env["Y"]?)}"
      unless expectTensor report.env["Z"]? [2] #[20.0, 40.0] do
        throwError s!"fanOut baseline Z mismatch: {repr (report.env["Z"]?)}"

-- Mutation: A[0] 10 → 99 propagates through both fan-out readers (verified).
run_cmd do
  match TLProgram.eval fanOutProg (fanOutInputs 99.0) with
  | .error e => throwError s!"fanOut mutation eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Z"]? [2] #[198.0, 40.0] do
        throwError s!"fanOut mutation did not propagate through fan-out: {repr (report.env["Z"]?)}"

/-- `Y` is assigned twice; `Z` reads `Y` after both writes. Pins two properties at once: (a) the
    materialized binding for `Y` is the LAST write, and (b) that binding is truly overwritten, not
    combined — mutating the FIRST (discarded) write must change nothing. -/
private def repeatAssignProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Y[i] := B[i]
  Z[i] := Y[i]
}

private def repeatAssignInputs (a0 : Float) : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" ⟨[2], #[a0, 2.0]⟩).insert "B" ⟨[2], #[100.0, 200.0]⟩

-- Baseline: last write (B) is what both Y and Z observe (verified).
run_cmd do
  match TLProgram.eval repeatAssignProg (repeatAssignInputs 1.0) with
  | .error e => throwError s!"repeatAssign baseline eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Y"]? [2] #[100.0, 200.0] do
        throwError s!"repeatAssign baseline Y mismatch: {repr (report.env["Y"]?)}"
      unless expectTensor report.env["Z"]? [2] #[100.0, 200.0] do
        throwError s!"repeatAssign baseline Z mismatch: {repr (report.env["Z"]?)}"

-- Mutation: changing A (the discarded first write) must change NOTHING — proves true overwrite,
-- not e.g. an accidental combine of both writes.
run_cmd do
  match TLProgram.eval repeatAssignProg (repeatAssignInputs 999.0) with
  | .error e => throwError s!"repeatAssign discarded-write eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Y"]? [2] #[100.0, 200.0] do
        throwError s!"repeatAssign: discarded first write leaked through: {repr (report.env["Y"]?)}"

/-- An input tensor not referenced anywhere in the program must still appear, unchanged, in the
    final environment (§5.4: `env` starts at `inputs`, nothing is filtered out). -/
private def extraInputProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
}

private def extraInputInputs (unused0 : Float) : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" ⟨[2], #[1.0, 2.0]⟩).insert
    "Unused" ⟨[1], #[unused0]⟩

-- Baseline: verified.
run_cmd do
  match TLProgram.eval extraInputProg (extraInputInputs 0.0) with
  | .error e => throwError s!"extraInput baseline eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Y"]? [2] #[1.0, 2.0] do
        throwError s!"extraInput baseline Y mismatch: {repr (report.env["Y"]?)}"
      unless expectTensor report.env["Unused"]? [1] #[0.0] do
        throwError s!"extraInput baseline did not preserve unused input: {repr (report.env["Unused"]?)}"

-- Mutation: changing the unused input's value passes through unchanged, and Y is unaffected.
run_cmd do
  match TLProgram.eval extraInputProg (extraInputInputs 42.0) with
  | .error e => throwError s!"extraInput mutation eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Unused"]? [1] #[42.0] do
        throwError s!"extraInput mutation not reflected: {repr (report.env["Unused"]?)}"
      unless expectTensor report.env["Y"]? [2] #[1.0, 2.0] do
        throwError s!"extraInput mutation of Unused incorrectly affected Y: {repr (report.env["Y"]?)}"

/-- Empty factor products and empty term arrays have no surface syntax (every parsed term has at
    least one factor). Compile an ordinary one-factor schedule, then splice a hand-built `RHSExpr`
    onto its existing (already correctly UID-resolved) LHS slot, reusing the compiled `env`/
    `explicitSizes` — the same technique `EntryTest.lean` uses `compileToScheduled` for. -/
private def spliceRhs (prog : TLProgram) (rhs : RHSExpr) : Except CompileError ScheduledProgram := do
  let sched ← match prog.compileToScheduled.run 0 with
    | .ok sched _ => pure sched
    | .error e _ => throw e
  match sched.stmts with
  | [.plain (.assign nm (slot :: _) _)] =>
      pure { sched with stmts := [.plain (.assign nm [slot] rhs)] }
  | _ => throw (.undeclaredName "skeleton did not compile to the expected single-slot shape")

private def emptySkeletonSize3 : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := X[i]
}

private def emptySkeletonSize5 : TLProgram := tlprog!{
  axis i : ℕ = 5
  Y[i] := X[i]
}

-- Empty factor product: each term contributes `factorId = 1.0`; one term per output coordinate.
-- Baseline verified: size 3 → Y = [1,1,1].
run_cmd do
  match spliceRhs emptySkeletonSize3 { body := { terms := [{ factors := [] }] }, nonlin := .identity } with
  | .error e => throwError s!"emptyProduct splice failed: {repr e}"
  | .ok sched =>
      match evalScheduled sched ({} : HashMap String DenseTensor) with
      | .error e => throwError s!"emptyProduct eval failed: {e}"
      | .ok report =>
          unless expectTensor report.env["Y"]? [3] #[1.0, 1.0, 1.0] do
            throwError s!"emptyProduct baseline mismatch: {repr (report.env["Y"]?)}"

-- Mutation: vary the axis size (3 → 5); the identity-fill must scale with shape, not stay fixed.
run_cmd do
  match spliceRhs emptySkeletonSize5 { body := { terms := [{ factors := [] }] }, nonlin := .identity } with
  | .error e => throwError s!"emptyProduct size mutation splice failed: {repr e}"
  | .ok sched =>
      match evalScheduled sched ({} : HashMap String DenseTensor) with
      | .error e => throwError s!"emptyProduct size mutation eval failed: {e}"
      | .ok report =>
          unless expectTensor report.env["Y"]? [5] #[1.0, 1.0, 1.0, 1.0, 1.0] do
            throwError s!"emptyProduct did not scale with axis size: {repr (report.env["Y"]?)}"

private def emptySkeletonSize4 : TLProgram := tlprog!{
  axis i : ℕ = 4
  Y[i] := X[i]
}

-- Empty term array: the output fold starts and ends at `reduceId = 0.0`.
-- Baseline verified: size 3 → Y = [0,0,0].
run_cmd do
  match spliceRhs emptySkeletonSize3 { body := { terms := [] }, nonlin := .identity } with
  | .error e => throwError s!"emptyTerms splice failed: {repr e}"
  | .ok sched =>
      match evalScheduled sched ({} : HashMap String DenseTensor) with
      | .error e => throwError s!"emptyTerms eval failed: {e}"
      | .ok report =>
          unless expectTensor report.env["Y"]? [3] #[0.0, 0.0, 0.0] do
            throwError s!"emptyTerms baseline mismatch: {repr (report.env["Y"]?)}"

-- Mutation: vary the axis size (3 → 4); the zero-fill must scale with shape.
run_cmd do
  match spliceRhs emptySkeletonSize4 { body := { terms := [] }, nonlin := .identity } with
  | .error e => throwError s!"emptyTerms size mutation splice failed: {repr e}"
  | .ok sched =>
      match evalScheduled sched ({} : HashMap String DenseTensor) with
      | .error e => throwError s!"emptyTerms size mutation eval failed: {e}"
      | .ok report =>
          unless expectTensor report.env["Y"]? [4] #[0.0, 0.0, 0.0, 0.0] do
            throwError s!"emptyTerms did not scale with axis size: {repr (report.env["Y"]?)}"

/-- `Y[i] := A[i, j]` with `axis j : ℕ = 0`: `j` is contracted (it doesn't appear in `Y`'s LHS), and
    its zero size means the reduction folds zero coordinates — `reduceId = 0.0` for every `i`. This
    is a different case from the empty-term-array fixture above: here there IS one real term with
    one real factor; only the reduction *domain* is empty. -/
private def zeroRedProgSize2 : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 0
  Y[i] := A[i, j]
}

private def zeroRedProgSize3 : TLProgram := tlprog!{
  axis i : ℕ = 3
  axis j : ℕ = 0
  Y[i] := A[i, j]
}

private def zeroRedInputsSize2 : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "A" ⟨[2, 0], #[]⟩

private def zeroRedInputsSize3 : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "A" ⟨[3, 0], #[]⟩

-- Baseline: verified, i size 2 → Y = [0, 0].
run_cmd do
  match TLProgram.eval zeroRedProgSize2 zeroRedInputsSize2 with
  | .error e => throwError s!"zeroRed baseline eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Y"]? [2] #[0.0, 0.0] do
        throwError s!"zeroRed baseline mismatch: {repr (report.env["Y"]?)}"

-- Mutation: vary the (non-contracted) output axis size 2 → 3; the zero-fill must scale with it.
run_cmd do
  match TLProgram.eval zeroRedProgSize3 zeroRedInputsSize3 with
  | .error e => throwError s!"zeroRed size mutation eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Y"]? [3] #[0.0, 0.0, 0.0] do
        throwError s!"zeroRed did not scale with output axis size: {repr (report.env["Y"]?)}"

/-- A zero-size axis produces an empty tensor, not an error — contrasted against size 1 to show the
    zero case is a genuine boundary, not an accidentally-always-empty result. -/
private def sizeVariantProgSize0 : TLProgram := tlprog!{
  axis i : ℕ = 0
  Y[i] := X[i]
}

private def sizeVariantProgSize1 : TLProgram := tlprog!{
  axis i : ℕ = 1
  Y[i] := X[i]
}

private def sizeVariantInputsSize0 : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[0], #[]⟩

private def sizeVariantInputsSize1 : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[1], #[7.0]⟩

-- Zero extent: verified shape [0], empty data.
run_cmd do
  match TLProgram.eval sizeVariantProgSize0 sizeVariantInputsSize0 with
  | .error e => throwError s!"zeroExtent eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Y"]? [0] #[] do
        throwError s!"zeroExtent mismatch: {repr (report.env["Y"]?)}"

-- Contrast: size 1 produces one real element (verified), showing zero-extent isn't a fixed result.
run_cmd do
  match TLProgram.eval sizeVariantProgSize1 sizeVariantInputsSize1 with
  | .error e => throwError s!"size-one eval failed: {e}"
  | .ok report =>
      unless expectTensor report.env["Y"]? [1] #[7.0] do
        throwError s!"size-one mismatch: {repr (report.env["Y"]?)}"

end LeanNCD.PlanContract.Fixtures

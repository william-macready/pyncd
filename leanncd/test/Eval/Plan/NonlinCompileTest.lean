import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter

/-!
# Thread 4 (nonlinearity) Task 3 — source compiler tests

`prepareEvalPlan`'s new two-step chaining (`.assign → .pointwise`/`.axiswise`), `resolveNonlinAxis`'s
five compile-tier cases run through the REAL `prepareEvalPlan` (not the standalone function),
end-to-end compiled examples for every nonlin function against their real Portfolio donors, explicit
slot-count/step-count regression pins for the `.identity` (byte-for-byte unchanged) vs. nonlin-bearing
(two-step) branches, and the two deliberate legacy-narrowing fixtures (§3) proving `evalScheduled`
accepts what `prepareEvalPlan` now rejects.

`CompileTest.lean` covers the capability-preflight-level admission (`.pointwise`/`.axiswise` now
passing `capabilityPreflight` at the top level; scan-block `.pointwise`/`.axiswise` still rejected) —
this file is compile-tier only, downstream of preflight.
-/

namespace LeanNCD.Eval.Plan.NonlinCompileTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan
open Std

/-- Local tensor-literal helper, mirroring `Eval/Portfolio/Harness.lean`'s `tl` (not imported here
    to avoid pulling in LSpec — this file follows `CompileTest.lean`/`DifferentialTest.lean`'s own
    `#guard`/`run_cmd` convention, not the Portfolio suite's `#lspec` one). -/
def tl (shape : List Nat) (xs : List Float) : DenseTensor := ⟨shape, xs.toArray⟩

/-- Extract `prepareEvalPlan`'s failure cause, `none` on success. -/
def compileCauseOf (r : Except PlanCompileFailure PreparedPlan) : Option PlanCompileCause :=
  match r with | .ok _ => none | .error e => some e.cause

/-- Compile one `TLProgram` all the way to `PlanCompileCause` (or `none` on success), threading
    `compileToScheduled` and `prepareEvalPlan` together — a source-text-level counterpart to
    `compileCauseOf` above, for the legacy-narrowing fixtures which need a real parsed marker rather
    than a hand-built `ScheduledProgram`. A `compileToScheduled` failure also reports `none`: no
    fixture below is expected to fail source compilation itself. -/
def sourceCompileCauseOf (p : TLProgram) (inputs : HashMap String DenseTensor) :
    Option PlanCompileCause :=
  match p.compileToScheduled.run 0 with
  | .error _ _ => none
  | .ok sched _ => compileCauseOf (prepareEvalPlan sched (InputSignature.ofDenseInputs inputs))

/-- Whether the LEGACY evaluator (`TLProgram.eval`, through `evalScheduled`/`resolveNonlin`) accepts
    a program — used by the legacy-narrowing fixtures, which need to show `evalScheduled` accepts
    what `prepareEvalPlan` now rejects. -/
def legacyAccepts (p : TLProgram) (inputs : HashMap String DenseTensor) : Bool :=
  match TLProgram.eval p inputs with
  | .ok _ => true
  | .error _ => false

/-- Compile one `TLProgram` through the Thread-4 pipeline (source → `ScheduledProgram` →
    `prepareEvalPlan` → `runPreparedDense`) and compare one named output against `expect` via
    `DenseTensor.approxEq`. Mirrors `Harness.lean`'s `evalEqB`, but through the compiled-plan path
    instead of `evalScheduled` — this is what actually exercises Task 3's real
    `.assign → .pointwise`/`.axiswise` chain end-to-end, not just that it type-checks. -/
def compiledEqB (p : TLProgram) (inputs : HashMap String DenseTensor) (key : String)
    (expect : DenseTensor) : Bool :=
  match p.compileToScheduled.run 0 with
  | .error _ _ => false
  | .ok sched _ =>
      match prepareEvalPlan sched (InputSignature.ofDenseInputs inputs) with
      | .error _ => false
      | .ok prepared =>
          match runPreparedDense prepared inputs with
          | .error _ => false
          | .ok report =>
              match report.env[key]? with
              | none => false
              | some t => DenseTensor.approxEq t expect

/-! ## Section 1 — `resolveNonlinAxis`'s five compile-tier cases, through real `prepareEvalPlan`

The same five cases §3's `check-snippet.sh` pass verified against the standalone function directly,
re-run here through `prepareEvalPlan` end-to-end: a hand-built two-axis `Y[·] := A[q, s]`-shaped
`ScheduledProgram` (mirrors `CompileTest.lean`'s own hand-built-schedule convention), varied only in
LHS slots and `Nonlin`. -/

def axQ1 : AxisSpec := { name := "q", uid := 101, kind := .nat }
def axS1 : AxisSpec := { name := "s", uid := 102, kind := .nat }

def axiswiseSched (slots : List LHSSlot) (nonlin : Nonlin) : ScheduledProgram :=
  { decls := [.axis axQ1 (some 2), .axis axS1 (some 2)]
  , stmts := [.plain (.assign "Y" slots
      { body := { terms := [{ factors := [.read "A" [.axis axQ1, .axis axS1]] }] }, nonlin })]
  , env := {}, extNames := insert "A" (∅ : Finset String)
  , explicitSizes := ((({} : HashMap UID Nat).insert axQ1.uid 2).insert axS1.uid 2) }

def axiswiseSig : InputSignature :=
  InputSignature.ofDenseInputs
    (({} : HashMap String DenseTensor).insert "A" (tl [2,2] [0, 0, 0, Float.log 3]))

-- 1a. Valid single-marker axiswise: `Y[q, s.] := softmax(A[q, s])` — compiles successfully.
#guard (prepareEvalPlan (axiswiseSched [.free axQ1, .freeNorm axS1] (.axiswise .softmax none))
    axiswiseSig).toOption.isSome

-- 1b. Unmarked identity pass-through: no `.freeNorm` marker, `.identity` nonlin — compiles
-- successfully (the trivial, always-should-succeed case).
#guard (prepareEvalPlan (axiswiseSched [.free axQ1, .free axS1] .identity) axiswiseSig).toOption.isSome

-- 1c. No-marker rejection: `.axiswise` with no `.freeNorm` marker anywhere on the LHS.
#guard compileCauseOf
    (prepareEvalPlan (axiswiseSched [.free axQ1, .free axS1] (.axiswise .softmax none)) axiswiseSig)
  == some (.nonlin (.noMarkedReductionAxis "Y"))

-- 1d. Masked-axiswise rejection: rejected unconditionally by `resolveNonlinAxis`'s FIRST match arm,
-- before `normPositions` is even inspected — confirming the rejection happens before any
-- `RawAxiswisePlan` could be built, regardless of whether a marker is present.
def sampleMask : BoolExpr := .rel .eq (.embed (.const 0)) (.embed (.const 0))
#guard compileCauseOf
    (prepareEvalPlan
      (axiswiseSched [.free axQ1, .freeNorm axS1] (.axiswise .softmax (some sampleMask)))
      axiswiseSig)
  == some (.nonlin (.maskedAxiswiseNotSupported "Y"))

-- 1e. Marker-present-but-pointwise rejection: a `.freeNorm` marker with no `.axiswise` to belong to.
#guard compileCauseOf
    (prepareEvalPlan (axiswiseSched [.free axQ1, .freeNorm axS1] (.pointwise .relu)) axiswiseSig)
  == some (.nonlin (.unmarkedReductionAxis "Y" 1))

/-! ## Section 2 — end-to-end compiled examples (donors named per the task brief)

Every fixture below is the EXACT source program and tensors from its named donor, run through the
Thread-4 compiled pipeline instead of the donor's own `evalScheduled` path. -/

-- relu: donor `FeedforwardTest.lean` FF2 (`W=[[1,-1],[-2,1]]`, `x=[1,1]` → `H=[0,0]`).
#guard compiledEqB (tlprog!{ H[i] := relu(W[i, j] · x[j]) })
    (HashMap.ofList [("W", tl [2,2] [1,-1, -2,1]), ("x", tl [2] [1,1])])
    "H" (tl [2] [0,0])

-- sigmoid: donor FF5 (`W=I₂`, `x=[-2,2]`).
#guard compiledEqB (tlprog!{ H[i] := sigmoid(W[i, j] · x[j]) })
    (HashMap.ofList [("W", tl [2,2] [1,0, 0,1]), ("x", tl [2] [-2,2])])
    "H" (tl [2] [0.11920292202211755, 0.8807970779778823])

-- tanh: donor FF6.
#guard compiledEqB (tlprog!{ H[i] := tanh(W[i, j] · x[j]) })
    (HashMap.ofList [("W", tl [2,2] [1,0, 0,1]), ("x", tl [2] [-2,2])])
    "H" (tl [2] [-0.9640275800758169, 0.9640275800758169])

-- gelu: donor FF7 (tanh approximation).
#guard compiledEqB (tlprog!{ H[i] := gelu(W[i, j] · x[j]) })
    (HashMap.ofList [("W", tl [2,2] [1,0, 0,1]), ("x", tl [2] [-2,2])])
    "H" (tl [2] [-0.045402305912, 1.954597694088])

-- leakyrelu: donor FF8.
#guard compiledEqB (tlprog!{ H[i] := leakyrelu(W[i, j] · x[j]) })
    (HashMap.ofList [("W", tl [2,2] [1,0, 0,1]), ("x", tl [2] [-2,2])])
    "H" (tl [2] [-0.02, 2])

-- normalize: donor `NormTest.lean` NM1 (`A=[[1,3],[2,2]]`).
#guard compiledEqB (tlprog!{ Y[q, s.] := normalize(A[q, s]) })
    (HashMap.ofList [("A", tl [2,2] [1,3, 2,2])])
    "Y" (tl [2,2] [0.25,0.75, 0.5,0.5])

-- softmax: donor NM2 (`A=[[0,0],[0,ln3]]`).
#guard compiledEqB (tlprog!{ Y[q, s.] := softmax(A[q, s]) })
    (HashMap.ofList [("A", tl [2,2] [0, 0, 0, Float.log 3])])
    "Y" (tl [2,2] [0.5,0.5, 0.25,0.75])

-- l2normalize: donor `GenerativeTest.lean` CL3 (`Z1=[[3,4]] → [0.6,0.8]`, cosine similarity).
#guard compiledEqB (tlprog!{
    Z1n[i, d.] := l2normalize(Z1[i, d])
    Z2n[j, d.] := l2normalize(Z2[j, d])
    S[i, j] := Z1n[i, d] · Z2n[j, d]
  })
    (HashMap.ofList [("Z1", tl [1,2] [3,4]), ("Z2", tl [1,2] [1,0])])
    "S" (tl [1,1] [0.6])

-- l2normalize, degenerate all-zero row: donor CL3b.
#guard compiledEqB (tlprog!{ Y[i, d.] := l2normalize(X[i, d]) })
    (HashMap.ofList [("X", tl [1,2] [0,0])])
    "Y" (tl [1,2] [0,0])

/-! ## Section 3 — regression pins: `.identity`'s single-slot/single-step shape vs. a nonlin
    statement's two internal-slot/two-step shape.

No existing `CompileTest.lean` fixture pins `raw.tensorSigs.size`/`raw.steps.size` directly (checked
by grep before writing these) — the mutation check that "always allocate an internal slot, even for
`.identity`" is a silent regression needs a fixture that actually counts slots/steps, not merely
`.toOption.isSome`.

**A real finding from writing these, worth stating plainly**: a source-text-authored nonlin
statement compiles through TWO independent splitting layers, not one — `splitNonlins`
(`DSL/Pipeline/Lowering.lean`, pre-existing, unrelated to Thread 4) ALREADY splits any
non-`.identity` statement into a linear step (`%nl{uid}`) plus a nonlin step reading it, before
`ScheduledProgram`/`prepareEvalPlan` ever see it; `prepareEvalPlan`'s own two-step chain (this task)
then splits the nonlin step's OWN body a second time (a redundant, but harmless, identity-copy
`.assign` immediately followed by the real `.pointwise`/`.axiswise` step). The two isolated fixtures
right below use a hand-built, `splitNonlins`-free `ScheduledProgram` (via `axiswiseSched` from
Section 1) to pin TASK 3's OWN two-slot/two-step contribution cleanly; the TLProgram-sourced
fixtures further down additionally pin the composed (both-layers) reality real source text produces. -/

/-- `PlanStep` field-access helper for pinning the exact step-kind sequence a nonlin-bearing
    statement compiles to. -/
def stepKind : PlanStep → String
  | .assign _ => "assign" | .scan _ => "scan" | .pointwise _ => "pointwise" | .axiswise _ => "axiswise"

-- Task 3's own contribution in isolation (no `splitNonlins` involved): `.identity` allocates
-- exactly 2 slots (A input, Y destination — no internal slot) and 1 step.
def identityIsolatedPrepared : Option PreparedPlan :=
  (prepareEvalPlan (axiswiseSched [.free axQ1, .free axS1] .identity) axiswiseSig).toOption
#guard identityIsolatedPrepared.map (fun p => p.plan.raw.tensorSigs.size) == some 2
#guard identityIsolatedPrepared.map (fun p => p.plan.raw.steps.size) == some 1
#guard identityIsolatedPrepared.map (fun p => p.bindings.materializedNames.map (·.name)) == some #["Y"]

-- `.pointwise` in isolation: 3 slots (A input; internal; published Y) and 2 steps
-- (`.assign` → `.pointwise`) — one MORE slot and one MORE step than `.identity` above, and only the
-- PUBLISHED slot is materialized under "Y" (the internal slot is never named).
def pointwiseIsolatedPrepared : Option PreparedPlan :=
  (prepareEvalPlan (axiswiseSched [.free axQ1, .free axS1] (.pointwise .relu)) axiswiseSig).toOption
#guard pointwiseIsolatedPrepared.map (fun p => p.plan.raw.tensorSigs.size) == some 3
#guard pointwiseIsolatedPrepared.map (fun p => p.plan.raw.steps.size) == some 2
#guard pointwiseIsolatedPrepared.map (fun p => p.plan.raw.steps.map stepKind) == some #["assign", "pointwise"]
#guard pointwiseIsolatedPrepared.map (fun p => p.bindings.materializedNames.map (·.name)) == some #["Y"]

-- `.axiswise` in isolation: same 3-slot/2-step shape as `.pointwise` above.
def axiswiseIsolatedPrepared : Option PreparedPlan :=
  (prepareEvalPlan (axiswiseSched [.free axQ1, .freeNorm axS1] (.axiswise .softmax none)) axiswiseSig).toOption
#guard axiswiseIsolatedPrepared.map (fun p => p.plan.raw.tensorSigs.size) == some 3
#guard axiswiseIsolatedPrepared.map (fun p => p.plan.raw.steps.size) == some 2
#guard axiswiseIsolatedPrepared.map (fun p => p.plan.raw.steps.map stepKind) == some #["assign", "axiswise"]

-- The COMPOSED reality for real source text: `splitNonlins` contributes its own extra `%nl`
-- linear step ahead of Task 3's two-step chain, so a real `relu` program's total is
-- `.identity`-isolated's 2-slot/1-step PLUS `splitNonlins`' 1 extra slot/step PLUS Task 3's own
-- 1 extra slot/step = 5 slots / 3 steps overall (one MORE input than the isolated fixtures above,
-- since this program has two external tensors, W and x).
def reluProg : TLProgram := tlprog!{ H[i] := relu(W[i, j] · x[j]) }
def reluProgInputs : HashMap String DenseTensor :=
  HashMap.ofList [("W", tl [2,2] [1,-1, -2,1]), ("x", tl [2] [1,1])]
def reluProgPrepared : Option PreparedPlan := Id.run do
  match reluProg.compileToScheduled.run 0 with
  | .error _ _ => none
  | .ok sched _ => (prepareEvalPlan sched (InputSignature.ofDenseInputs reluProgInputs)).toOption

#guard reluProgPrepared.map (fun p => p.plan.raw.tensorSigs.size) == some 5
#guard reluProgPrepared.map (fun p => p.plan.raw.steps.size) == some 3
#guard reluProgPrepared.map (fun p => p.plan.raw.steps.map stepKind) == some #["assign", "assign", "pointwise"]
-- Only "H" (the final published name) and the `splitNonlins`-minted "%nl..." intermediate are
-- materialized under a name — Task 3's OWN internal slot (this task's two-step chain's middle slot)
-- is never named, exactly as the isolated fixtures above already pin.
#guard reluProgPrepared.map (fun p => (p.bindings.materializedNames.map (·.name)).contains "H")
  == some true

def softmaxProg : TLProgram := tlprog!{ Y[q, s.] := softmax(A[q, s]) }
def softmaxProgInputs : HashMap String DenseTensor :=
  HashMap.ofList [("A", tl [2,2] [0, 0, 0, Float.log 3])]
def softmaxProgPrepared : Option PreparedPlan := Id.run do
  match softmaxProg.compileToScheduled.run 0 with
  | .error _ _ => none
  | .ok sched _ => (prepareEvalPlan sched (InputSignature.ofDenseInputs softmaxProgInputs)).toOption

-- Same composed shape as `relu` above, but with only ONE external input (A): 4 slots, 3 steps.
#guard softmaxProgPrepared.map (fun p => p.plan.raw.tensorSigs.size) == some 4
#guard softmaxProgPrepared.map (fun p => p.plan.raw.steps.size) == some 3
#guard softmaxProgPrepared.map (fun p => p.plan.raw.steps.map stepKind) == some #["assign", "assign", "axiswise"]

/-! ## Section 4 — deliberate legacy-narrowing fixtures (§3)

Two program shapes the legacy evaluator (`evalScheduled`/`resolveNonlin`) silently accepts, that
`prepareEvalPlan` now rejects — proving the delta is real, understood, and intentional, not a
differential-testing surprise Task 5 would otherwise discover unexplained. -/

-- Legacy-narrowing #1: a spurious `.freeNorm` marker on an otherwise-`.pointwise` statement
-- (clones the `relu` fixture above, marking `i`). `resolveNonlin`'s `.pointwise` branch never
-- inspects `slots` (`Nonlin.lean:124-133`) — `evalScheduled` executes this exactly as the unmarked
-- `relu` fixture above. `prepareEvalPlan` rejects it: the marker has no `.axiswise` to belong to.
def spuriousMarkerPointwise : TLProgram := tlprog!{ H[i.] := relu(W[i, j] · x[j]) }
def spuriousMarkerPointwiseInputs : HashMap String DenseTensor :=
  HashMap.ofList [("W", tl [2,2] [1,-1, -2,1]), ("x", tl [2] [1,1])]

#guard legacyAccepts spuriousMarkerPointwise spuriousMarkerPointwiseInputs
#guard sourceCompileCauseOf spuriousMarkerPointwise spuriousMarkerPointwiseInputs
  == some (.nonlin (.unmarkedReductionAxis "H" 0))

-- Legacy-narrowing #2: a second `.freeNorm` marker on an unrelated output axis of an axiswise
-- statement (clones the `normalize` fixture above, additionally marking `q`). `normAxisUidOf` is
-- `slots.findSome?` (`Slots.lean:23-24`) — first match wins, so `evalScheduled` silently reduces
-- over `q` (the FIRST marked axis) instead of `s`, no error. `prepareEvalPlan` rejects the ambiguity
-- outright.
def doubleMarkerAxiswise : TLProgram := tlprog!{ Y[q., s.] := normalize(A[q, s]) }
def doubleMarkerAxiswiseInputs : HashMap String DenseTensor :=
  HashMap.ofList [("A", tl [2,2] [1,3, 2,2])]

#guard legacyAccepts doubleMarkerAxiswise doubleMarkerAxiswiseInputs
#guard sourceCompileCauseOf doubleMarkerAxiswise doubleMarkerAxiswiseInputs
  == some (.nonlin (.multipleMarkedReductionAxes "Y" 0 1))

end LeanNCD.Eval.Plan.NonlinCompileTest

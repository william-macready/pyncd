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
def axS1 : AxisSpec := { name := "s", uid := 102, kind := .real }

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

-- 1d. Masked-axiswise ADMISSION (Slice 5.3): a masked `.axiswise` is now lowered, not rejected.
-- `resolveNonlinAxis` resolves its marked axis like any axiswise; the mask lowers via
-- `lowerMaskPredicate` (local non-seeded output basis, empty pins). `sampleMask` (always-true,
-- width-2 over the `[q,s]` basis) satisfies `checkAxiswise`'s mask width check, so it compiles.
def sampleMask : BoolExpr := .rel .eq (.embed (.const 0)) (.embed (.const 0))
#guard (prepareEvalPlan
      (axiswiseSched [.free axQ1, .freeNorm axS1] (.axiswise .softmax (some sampleMask)))
      axiswiseSig).toOption.isSome

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

**Historical note, kept because the fixture numbers below moved because of it**: a
source-text-authored nonlin statement used to compile through TWO independent splitting layers.
`splitNonlins` (`DSL/Pipeline/Lowering.lean`) split any non-`.identity` statement into a linear
step (`%nl{uid}`) plus a nonlin step reading it BEFORE `ScheduledProgram`/`prepareEvalPlan` ever
saw it, and `prepareEvalPlan`'s own two-step chain (this task) then split the nonlin step's OWN
body a second time. The logical-schedule flip
(`papers/nonlinearity_split_pair_direct_lowering.md` §2.1) removed the first layer from the
production chain: `compileToScheduled` now hands Eval the LOGICAL schedule (one statement per
source statement, zero generated names) and the private producer/consumer pair is built inside
`route`, which the Eval path never calls. So there is exactly ONE splitting layer today — this
task's. The isolated fixtures right below use a hand-built `ScheduledProgram` (via `axiswiseSched`
from Section 1) to pin TASK 3's OWN two-slot/two-step contribution cleanly; the TLProgram-sourced
fixtures further down pin what real source text now produces end to end. -/

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

-- The reality for real source text. There is now exactly ONE splitting layer, not two: the
-- schedule `compileToScheduled` hands to `prepareEvalPlan` is LOGICAL (§2.1 — `splitNonlins` left
-- the production chain; the private producer/consumer pair is built inside `route`, which the Eval
-- path never calls), so the only split here is Task 3's own two-step chain. The relu program's
-- total is therefore `.identity`-isolated's 2-slot/1-step PLUS Task 3's own 1 extra slot/step,
-- PLUS one more input than the isolated fixtures (this program has two external tensors, W and x)
-- = 4 slots / 2 steps. Before the logical-schedule flip this read 5 slots / 3 steps, the extra
-- slot/step being the `%nl{uid}` linear statement `splitNonlins` manufactured.
def reluProg : TLProgram := tlprog!{ H[i] := relu(W[i, j] · x[j]) }
def reluProgInputs : HashMap String DenseTensor :=
  HashMap.ofList [("W", tl [2,2] [1,-1, -2,1]), ("x", tl [2] [1,1])]
def reluProgPrepared : Option PreparedPlan := Id.run do
  match reluProg.compileToScheduled.run 0 with
  | .error _ _ => none
  | .ok sched _ => (prepareEvalPlan sched (InputSignature.ofDenseInputs reluProgInputs)).toOption

#guard reluProgPrepared.map (fun p => p.plan.raw.tensorSigs.size) == some 4
#guard reluProgPrepared.map (fun p => p.plan.raw.steps.size) == some 2
#guard reluProgPrepared.map (fun p => p.plan.raw.steps.map stepKind) == some #["assign", "pointwise"]
-- Only "H" (the final published name) is materialized under a name — Task 3's OWN internal slot
-- (this task's two-step chain's middle slot) is never named, exactly as the isolated fixtures
-- above already pin. §2.1 property: NO generated name reaches the Plan compiler at all now, so
-- there is no `%nl…` materialized name beside it either — pinned exactly below.
#guard reluProgPrepared.map (fun p => (p.bindings.materializedNames.map (·.name)).contains "H")
  == some true
#guard reluProgPrepared.map (fun p => p.bindings.materializedNames.map (·.name)) == some #["H"]

def softmaxProg : TLProgram := tlprog!{ Y[q, s.] := softmax(A[q, s]) }
def softmaxProgInputs : HashMap String DenseTensor :=
  HashMap.ofList [("A", tl [2,2] [0, 0, 0, Float.log 3])]
def softmaxProgPrepared : Option PreparedPlan := Id.run do
  match softmaxProg.compileToScheduled.run 0 with
  | .error _ _ => none
  | .ok sched _ => (prepareEvalPlan sched (InputSignature.ofDenseInputs softmaxProgInputs)).toOption

-- Same shape as `relu` above, but with only ONE external input (A): 3 slots, 2 steps.
-- (Was 4 slots / 3 steps before the logical-schedule flip.)
#guard softmaxProgPrepared.map (fun p => p.plan.raw.tensorSigs.size) == some 3
#guard softmaxProgPrepared.map (fun p => p.plan.raw.steps.size) == some 2
#guard softmaxProgPrepared.map (fun p => p.plan.raw.steps.map stepKind) == some #["assign", "axiswise"]

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

/-! ## Section 5 — Slice 5.3 masked-axiswise fixtures (source→checked differential)

Each fixture below carries a source `(where …)` mask through the WHOLE compiled pipeline
(`runPreparedDense`, the checked path — `compiledEqB`) AND through the legacy reference evaluator
(`TLProgram.eval` — `sourceEvalOf`), asserting BOTH agree with the same hand/spike value. That makes
each a source→checked differential, not a one-sided pin: the checked mask (`lowerMaskPredicate` +
`RawAxiswisePlan.mask` + `runDenseAxiswise`) reproduces the reference masked reduction exactly.

Inclusion polarity: a mask TRUE at a coordinate INCLUDES it. An all-masked row → zeros (never a
uniform row). Softmax excludes masked entries from the row MAXIMUM as well as the sum. -/

/-- The legacy reference evaluator's output tensor for one named key, `none` on any failure. -/
def sourceEvalOf (p : TLProgram) (inputs : HashMap String DenseTensor) (key : String) :
    Option DenseTensor :=
  match TLProgram.eval p inputs with
  | .error _ => none
  | .ok report => report.env[key]?

/-- Source→checked differential: BOTH the checked pipeline and the legacy reference evaluator
    approx-equal `expect`. -/
def diffEqB (p : TLProgram) (inputs : HashMap String DenseTensor) (key : String)
    (expect : DenseTensor) : Bool :=
  compiledEqB p inputs key expect &&
    (match sourceEvalOf p inputs key with
     | some t => DenseTensor.approxEq t expect
     | none => false)

def nm4Inputs : HashMap String DenseTensor := HashMap.ofList [("A", tl [2,3] [1,2,3, 4,1,1])]

-- Fixture: Top-level masked normalize (donor NM4, unchanged). Mask `s ≠ 0` keeps the survivors and
-- renormalizes; masked column → 0. row0 [1,2,3]→[0,0.4,0.6], row1 [4,1,1]→[0,0.5,0.5].
#guard diffEqB (tlprog!{ Y[q, s.] := normalize(where s ≠ 0)(A[q, s]) })
    nm4Inputs "Y" (tl [2,3] [0, 0.4, 0.6, 0, 0.5, 0.5])

-- Fixture: Masked softmax (NM4, function changed to softmax). Masked entries leave BOTH the row sum
-- and the row maximum. row0 survivors [2,3]→[0, e^{-1}/(1+e^{-1}), 1/(1+e^{-1})]; row1 [1,1]→[0,½,½].
#guard diffEqB (tlprog!{ Y[q, s.] := softmax(where s ≠ 0)(A[q, s]) })
    nm4Inputs "Y"
    (tl [2,3] [0, 0.2689414213699951, 0.7310585786300049, 0, 0.5, 0.5])

-- Fixture: Masked L2 normalize (NM4, function changed to l2normalize). row0 survivors [2,3] →
-- [0, 2/√13, 3/√13]; row1 [1,1] → [0, 1/√2, 1/√2].
#guard diffEqB (tlprog!{ Y[q, s.] := l2normalize(where s ≠ 0)(A[q, s]) })
    nm4Inputs "Y"
    (tl [2,3] [0, 0.5547001962252291, 0.8320502943378437, 0, 0.7071067811865475, 0.7071067811865475])

-- Fixture: Three all-masked rows — one per axiswise function — `where s < 0` masks EVERY entry, so
-- each row is zeros (NOT a uniform distribution). One `#guard` per function.
def allMaskedInputs : HashMap String DenseTensor := HashMap.ofList [("A", tl [2,3] [1,2,3, 4,1,1])]
#guard diffEqB (tlprog!{ Y[q, s.] := normalize(where s < 0)(A[q, s]) })
    allMaskedInputs "Y" (tl [2,3] [0,0,0, 0,0,0])
#guard diffEqB (tlprog!{ Y[q, s.] := softmax(where s < 0)(A[q, s]) })
    allMaskedInputs "Y" (tl [2,3] [0,0,0, 0,0,0])
#guard diffEqB (tlprog!{ Y[q, s.] := l2normalize(where s < 0)(A[q, s]) })
    allMaskedInputs "Y" (tl [2,3] [0,0,0, 0,0,0])

-- Fixture: Masked extreme — softmax, with `1000` planted in the already-excluded `s=0` entry
-- (mask `s ≠ 0`). The `1000` must NEVER enter the row maximum: max over the unmasked survivors of
-- row0 is `max(2,3)=3`, so row0 = [0, e^{-1}/(1+e^{-1}), 1/(1+e^{-1})] ≈ [0,.269,.731]. Were `1000`
-- admitted to the max, `exp(2-1000)=exp(3-1000)=0` would collapse the row to all-zeros/NaN.
#guard diffEqB (tlprog!{ Y[q, s.] := softmax(where s ≠ 0)(A[q, s]) })
    (HashMap.ofList [("A", tl [2,3] [1000,2,3, 4,1,1])]) "Y"
    (tl [2,3] [0, 0.2689414213699951, 0.7310585786300049, 0, 0.5, 0.5])

-- Fixture: Non-last mask basis (donor NM5, adding the asymmetric `where s < q`). The reduction axis
-- is `s` (`A[s., q]`), so the mask basis is the OUTPUT order `[s, q]`. Q=K=I₂ ⇒ scores S[s,q]=[s=q].
-- column q=0: mask `s<0` excludes both ⇒ zeros; column q=1: mask `s<1` keeps only s=0 (value 0) ⇒
-- softmax of the single survivor = 1. Result (row-major A[s][q]) = [0,1, 0,0]. Swapping the two
-- mask basis positions would compute `q<s` and yield [0,0, 1,0] instead — mutation 7's target.
#guard diffEqB (tlprog!{ A[s., q] := softmax(where s < q)(Q[q, d] · K[s, d]) })
    (HashMap.ofList [("Q", tl [2,2] [1,0, 0,1]), ("K", tl [2,2] [1,0, 0,1])])
    "A" (tl [2,2] [0,1, 0,0])

-- Fixture: Unmasked nonlinear unchanged — the `included?`-callback refactor changes no unmasked
-- value. Re-pins the Section-2 donors' exact values through the same differential harness.
#guard diffEqB (tlprog!{ Y[q, s.] := normalize(A[q, s]) })
    (HashMap.ofList [("A", tl [2,2] [1,3, 2,2])]) "Y" (tl [2,2] [0.25,0.75, 0.5,0.5])
#guard diffEqB (tlprog!{ Y[q, s.] := softmax(A[q, s]) })
    (HashMap.ofList [("A", tl [2,2] [0, 0, 0, Float.log 3])]) "Y" (tl [2,2] [0.5,0.5, 0.25,0.75])

end LeanNCD.Eval.Plan.NonlinCompileTest
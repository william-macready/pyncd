# Thread 4 — implement nonlinearity (Dense-only)

## 0. Session verification record (2026-08-20)

Everything below was re-verified directly against the repo at `main` (b5bb00e, Wave F complete),
not carried over from an earlier summary.

- `LeanNCD/DSL/Ast.lean`: `PointwiseFn | relu | sigmoid | tanh | gelu | leakyrelu` and
  `AxiswiseFn | softmax | normalize | l2normalize` each derive `DecidableEq, Repr, Lean.ToExpr,
  Inhabited` — **no `BEq`**. `Nonlin | identity | pointwise PointwiseFn | axiswise AxiswiseFn
  (Option BoolExpr)` attaches to `RHSExpr.nonlin`, carried by `Stmt.assign`/`Stmt.scatter`.
  `Stmt.recurMorphism` structurally forces `.identity` (`Stmt.nonlinOf`) — independent confirming
  evidence for the scan-block scope boundary below.
- `LHSSlot.freeNorm : AxisSpec → LHSSlot` is the **sole** surface mechanism that names an axiswise
  reduction axis (the `s.`/`m.` marker). `RHSExpr.nonlin`'s `.axiswise` case carries no axis
  reference of its own.
- `LeanNCD/Eval/Plan/RawStep.lean`: `PlanStep | assign (a : AssignPlan) | scan (s : RawScanPlan)`,
  `deriving DecidableEq, BEq, Repr, Inhabited`. Imports only `Kernel.lean`.
- `LeanNCD/Eval/Plan/EvalPlan.lean`: three exhaustive matches over `PlanStep`/
  `CheckedPlanStepEvidence` — `PlanStep.sourceSlots`, `PlanStep.destinationSlots`, and `checkPlan`'s
  three separate `match step with` blocks (context-check, destination-availability loop,
  source-availability + dispatch), plus `CheckedPlanStepEvidence`'s own 2-constructor mirror and
  `runDensePlan`'s match over it. `.assign`'s source-read check is a direct per-term/per-factor loop
  (preserves `ti`/`fi` locators); `.scan`'s uses the generic `PlanStep.sourceSlots`/
  `destinationSlots` accessors with placeholder locators `0 0`.
- `LeanNCD/Eval/Plan/Compile.lean`: `checkNonlin` (the `unsupportedNonlin` rejection) has exactly
  two call sites — `checkStmt` (plain top-level statements) and `checkScanBlockStmt` (scan
  base/recurrence statements). `checkLHSSlot` (used by `checkStmt`) unconditionally rejects
  `.freeNorm` via `unsupportedLhsSlot`; `checkScanLHSSlot` (used by `checkScanBlockStmt`) admits
  `.iterAt`/`.iterNext` but still rejects `.freeNorm` too. `freeUidOrFail` (Step D helper) throws
  `unsupportedLhsSlot` on `.freeNorm`, justified by a doc comment claiming this is unreachable
  post-preflight — true only as long as `checkLHSSlot` keeps rejecting it.
- `LeanNCD/Eval/Nonlin.lean`: `reluT`/`sigmoidT`/`tanhT`/`geluT`/`leakyReluT` are pure
  `DenseTensor → DenseTensor` maps (`⟨t.shape, t.data.map f⟩` — shape-preserving by construction,
  no coordinate arithmetic that can go out of range). `softmaxT`/`normalizeT`/`l2normalizeT` take
  `(axisPos : Nat) (axisUids : List UID) (mask? : Option BoolExpr) (t : DenseTensor)`, built on a
  shared `perRow` combinator; `axisUids`/`mask?` are used **only** inside the `mask? = some _`
  branch of `perRow` (to build `coordMap` for `evalBool`) — when `mask? = none`, `axisUids` is
  never read. `gelu` is the tanh approximation (matches JAX's default; PyTorch's default is exact
  erf and needs `approximate='tanh'`).
- `LeanNCD/Eval/Plan/Error.lean`: `CapabilityError.unsupportedNonlin (context : String)` — single
  bare string, no pointwise/axiswise distinction. `ScanCompileError` (this file, not `Scan.lean`)
  is the precedent for "a second closed error family beside `CapabilityError`, for obligations that
  need more than bare-AST decidability" — several of its own constructors (e.g.
  `noPersistentState`, `duplicateContextAxis`) are in fact syntactically decidable too, so
  "needs inferred sizes" is not literally `ScanCompileError`'s membership test; "belongs to one
  named construct's own compile-tier obligations, not general per-statement preflight" is.
  `ScanPlanError` (checker-level, for `checkScanPlan`) lives in `Scan.lean` itself, not here.
- `LeanNCD/Eval/Plan/Types.lean`: `NumericMode | reference64SumProduct`, single constructor.
  `LeanNCD/Eval/Plan/Graph.lean`: `RawEvalPlan.numericMode : NumericMode`. `EvalPlan.lean`'s
  `checkPlan` throws `PlanError.numericModeNotAdmitted` if it's not `.reference64SumProduct`
  (structurally impossible, and a `GraphCheckTest.lean` comment already calls this "structurally
  unreachable"). `Compile.lean`'s `prepareEvalPlan` sets `numericMode := .reference64SumProduct` in
  the one `RawEvalPlan` literal it builds.
- Every `numericMode`/`reference64SumProduct`/`NumericMode`/`numericModeNotAdmitted` occurrence in
  the repo, from a direct grep (paths relative to `leanncd/`):
  - Production: `LeanNCD/Eval/Plan/Types.lean` (the type), `LeanNCD/Eval/Plan/Graph.lean` (the
    field), `LeanNCD/Eval/Plan/Error.lean` (the `PlanError` constructor),
    `LeanNCD/Eval/Plan/EvalPlan.lean` (the `checkPlan` guard/throw),
    `LeanNCD/Eval/Plan/Compile.lean` (the `RawEvalPlan` literal in `prepareEvalPlan`).
  - Tests, each setting `numericMode := .reference64SumProduct` in a `RawEvalPlan` literal unless
    noted: `test/Eval/Plan/EvalPlanTest.lean` (4 occurrences), `test/Eval/Plan/GraphCheckTest.lean`
    (`chainPlan`, `diamondPlan`, plus a direct `#guard (PlanError.numericModeNotAdmitted ...)  ==
    ...` line and an adjacent comment calling it "structurally unreachable"),
    `test/Eval/Plan/GraphDenseTest.lean` (5 occurrences), `test/Eval/Plan/KernelCheckTest.lean` (1),
    `test/Eval/Plan/ExecutableTest.lean` (2). Comment-only stale references once the constructor is
    gone: `test/Eval/Plan/CompileTest.lean` ("same pattern as `checkAssign`'s single-valued-vocabulary
    unreachables (`numericModeNotAdmitted`, C2/C3)"), `test/Eval/Plan/AdapterTest.lean` ("same
    pattern as `PlanError.numericModeNotAdmitted` (C3)"), `test/Eval/Plan/ContractTest.lean`
    ("`NumericMode`: deferred to C1/C2 ... Wave C admits only `reference64SumProduct`").
  - `experiments/jax_bridge/EvalPlanCodegen.lean` also sets `numericMode := .reference64SumProduct`
    in one `RawEvalPlan` literal — **left untouched**, see the JAX scope note below.
- **`experiments/jax_bridge/EvalPlanCodegen.lean` is confirmed broken independent of this thread**,
  by directly running `lake build JaxExperiment` this session (real command, real failure, not
  assumed): it fails with `Invalid field 'plan': ... CheckedPlanStepEvidence.plan` (two call sites),
  a non-exhaustive `match` over `PlanCompileCause.scan (ScanCompileError...)` variants, `'version'
  is not a field of structure 'RawEvalPlan'`, and an `AssignPlan`/`PlanStep` type mismatch in a
  `RawEvalPlan` literal — exactly the stale-`.plan`-access / removed-`version` / `PlanStep`
  generalization breakage the architecture doc already documents as Wave F leaving this file behind,
  a later unscheduled wave's problem, not this thread's. This plan does not touch that file.
- `test/Eval/Plan/DifferentialTest.lean`'s pinned corpus split (`total=17 accepted=9
  unsupportedNonlin=4 unsupportedAgg=4`) is `scanCorpusSplit` (its `enumScanCases` sweep), not the
  separate 3,832-program `enumPrograms` sweep (which has zero nonlin/scatter/scan/predicate/agg
  constructs and is unaffected either way). **Correction to the task brief's framing**: those four
  `unsupportedNonlin` cases are `ScanGen.lean`'s `template2`, whose `.pointwise .relu` sits on the
  **recurrence statement inside the scan block** (`nonlin := .pointwise .relu` on the step-block
  assignment), not at top level. Per the ruled scope boundary (scan-block nonlin stays rejected,
  ruling 6), **this split does not change** as a mechanical consequence of this thread — it is not
  "some of those 4 may now compile." Task 5 re-runs it as a confirmatory regression check, not an
  expected-to-change count.
- `test/Eval/Portfolio/ScatterNonlinRejectTest.lean` (RSN1-4) tests **scatter** statements, rejected
  by `checkStmt`'s `.scatter nm .. => throw (.scatterOrAffineLhs nm)` **unconditionally**, before
  `checkNonlin` is ever reached — confirmed by reading `checkStmt` directly. This file needs no
  change; it is not testing the same mechanism this thread touches at all (it also exercises the
  legacy `DSL/Pipeline/Structural.lean`'s own `checkScatterNonlin`, a completely separate rejection
  path).
- Real, hand-verified-elsewhere fixture donors exist for all eight nonlin functions already, so no
  new fixture value needs deriving from scratch — see each task's Fixtures list for exact
  `test`/`#guard` names and expected tensors.
- `.claude/skills/slice-plan/check-snippet.sh` ran clean against every Lean fragment this plan
  ships (four snippets: raw types + manual `BEq` instances for `PointwiseFn`/`AxiswiseFn`; the
  full `checkPointwise`/`checkAxiswise`/`CheckedPointwisePlan`/`CheckedAxiswisePlan`/
  `runDensePointwise`/`runDenseAxiswise` block plus a `sourceSlots`/`destinationSlots` mirror match;
  `resolveNonlinAxis`/`NonlinCompileError` with five `#guard`s against real `LHSSlot`/`Nonlin`
  values; and a 4-constructor `PlanStep`-shaped sum using the **real** `RawScanPlan`/`AssignPlan`
  deriving `DecidableEq, BEq, Repr, Inhabited`) — all four compiled clean on the first pass except
  for one unused-variable lint warning in an illustrative (non-shipped) snippet.

### 0a. Extensibility/code-sharing vetting addendum (same day, follow-up pass)

Requested explicitly: before executing this plan, re-examine whether it is the best design for
future nonlinearity additions and whether more code sharing is possible. Two real gaps were found
by reading `Eval/Nonlin.lean` and the drafted checker/worker signatures side by side — an
asymmetry between `PointwiseFn`'s and `AxiswiseFn`'s dispatch, and duplicated geometry checks
between `checkPointwise`/`checkAxiswise`. Both are fixed in the task text below; the resulting
design (`AxiswiseFn.apply`, `checkNonlinIO`) and its rationale are written up in §3's two new "Why"
subsections (**"Why `AxiswiseFn.apply` exists"** and **"Why `checkPointwise`/`checkAxiswise` share
`checkNonlinIO`"**) alongside this thread's other design decisions, not repeated here. This entry
records only what was verified: both fixes were checked via `check-snippet.sh` against the real
repo (two more snippets beyond the original four, both green on the corrected pass — full tally in
§8), and one confirmed-but-out-of-scope limit was noted rather than solved: `PointwiseFn`/
`AxiswiseFn` are bare (payload-free) enum constructors, so a future *parametric* nonlinearity
(configurable-α ELU, temperature-scaled softmax) would need a constructor carrying its own
field(s) — a `DSL/Ast.lean` language-design change, outside this thread's remit and not something
either fix forecloses or complicates.

## 1. Purpose

Implement Backend Eval IR's nonlinearity thread (architecture doc §7.6 thread 4) for the **Dense**
interpreter only: two new `PlanStep` cases (`.pointwise`, `.axiswise`) mirroring `Nonlin`'s AST
step-kind shape — the **unmasked** admitted subset of it, see §2.2 — reachable from real surface
DSL syntax at the top level (not inside a scan block), checked and executed by reusing
`Eval/Nonlin.lean`'s existing float64 math rather than reimplementing it.

**Dense's role here is to establish checked reference semantics, not to be the permanent
consumer** — JAX, not Dense, is the intended primary long-term backend for this Eval IR (per the
user's own stated intent). See §2.2's JAX bullet for why JAX support itself is out of this thread's
scope, why that's a near-term follow-up rather than an indefinite deferral, and why the checked
types this thread introduces are already backend-neutral enough for that follow-up to build on
directly.

## 2. Scope

### 2.1 In scope

- New raw types `RawPointwisePlan`/`RawAxiswisePlan`, a closed checker-level error family
  (`NonlinPlanError`), a shared geometry-check helper (`checkNonlinIO`, factoring the case×class
  rows common to both step kinds) plus the two checkers built on it (`checkPointwise`/
  `checkAxiswise`), and dense workers (`runDensePointwise`/`runDenseAxiswise`) in a new file
  `LeanNCD/Eval/Plan/Nonlin.lean`.
- A small, additive, behavior-preserving edit to `LeanNCD/Eval/Nonlin.lean`: a new
  `AxiswiseFn.apply`, symmetric with the file's existing `PointwiseFn.apply` ("owned by the enum,
  so a new [pointwise] function has exactly one place to be interpreted"), and `applyNonlin`
  refactored to delegate both cases to their enum's own method (§0a) — closes the one asymmetry
  found while vetting this design for future extensibility.
- Two new `PlanStep` constructors, wired into every exhaustive match `RawStep.lean`'s doc comment
  already warns touches (`checkPlan`, `runDensePlan`, `PlanStep.sourceSlots`/`destinationSlots`,
  `CheckedPlanStepEvidence`).
- Real top-level source compilation: `checkNonlin`'s **top-level statement** call site
  (`checkStmt`) admits `.pointwise`/`.axiswise`; `checkLHSSlot` admits `.freeNorm` (relaxed, not
  removed — consistency with `Nonlin` is deferred to compile tier, mirroring
  `checkScanLHSSlot`'s own "admit syntactically, validate later" split); `prepareEvalPlan`'s Step D
  compiles a nonlin-bearing plain statement into **two** chained `PlanStep`s (see Architecture).
  A new `NonlinCompileError` family (in `Error.lean`, alongside `ScanCompileError`) and a
  `resolveNonlinAxis` function (in `Compile.lean`) own the freeNorm-axis/`Nonlin`-kind consistency
  check this needs.
- Deleting `RawEvalPlan.numericMode`/`NumericMode`/`PlanError.numericModeNotAdmitted` and every
  reference (ruling 3 — see §0's exact file/test list).
- Correcting `papers/jax_evalplan_architecture.md` §7.6's thread 4 row and §2.2's closing sentence
  to state Dense-only landed, with PyTorch and JAX given distinct framing rather than one merged
  "deferred" clause (folded into Task 6's closure; rationale in §2.2's JAX bullet).
- New hand-built differential fixtures exercising top-level pointwise/axiswise end-to-end (no
  existing generator produces such a program), plus a confirmatory (not expected-to-change) re-run
  of the existing scan corpus split.

### 2.2 Explicitly out of scope (deliberate, not deferred silently)

- **Nonlinearity inside a scan base/step block stays rejected.** `checkScanBlockStmt`'s
  `checkNonlin` call site is unchanged. `Stmt.recurMorphism`'s forced `.identity` (`Stmt.nonlinOf`)
  is independent structural evidence this was never meant to be a live combination; the
  architecture doc's thread 4 text describes new *outer* `PlanStep` cases only. State this in the
  completion record as a scope boundary, not a gap.
- **Masked axiswise nonlinearities (`Nonlin.axiswise fn (some _)`) are rejected**, at the compile
  tier (`NonlinCompileError.maskedAxiswiseNotSupported`, thrown by `resolveNonlinAxis`), before a
  `RawAxiswisePlan` can exist. `RawAxiswisePlan` carries **no mask field at all** — not a
  reserved-but-unused one. Rationale: Plan-level `TensorSignature` is `{ shape : Array Nat; dtype :
  ScalarDType }` with **no axis-UID information whatsoever** (compiled away by design —
  `Kernel.lean`'s own doc comment: "no graph scheduling, no source names, no axis UIDs").
  `softmaxT`/`normalizeT`/`l2normalizeT`'s mask branch needs `axisUids : List UID` to build a
  `HashMap UID Int` for `evalBool`; building a UID-free, position-based compiled predicate IR to
  support this would be new IR design work with no precedent in this codebase — clearly outside
  "implement nonlinearity new `PlanStep` cases." This is a **finding from this session's
  verification pass, not one of the pre-agreed rulings** — flagged prominently per the task
  brief's own instruction to report such findings plainly.

  **This is a compile-tier rejection, not a capability-preflight one — a corrected claim from an
  earlier draft, verified against the real `checkNonlin`.** `checkNonlin`'s current body is
  `.axiswise .. => throw (.unsupportedNonlin ...)`: the `..` wildcard matches the mask field
  without inspecting it, so it never distinguishes masked from unmasked today, and it must not
  gain that distinction once real — `checkNonlin`'s established role (mirrored by every other
  `checkStmt` sub-check) is classifying broad *syntactic categories*, not validating field-level
  combinations; that's exactly the same reason the freeNorm-marker/`Nonlin`-kind consistency check
  above is deferred to `resolveNonlinAxis` rather than re-litigated as a second preflight rule. An
  earlier draft of this plan additionally claimed `CapabilityError.maskOrPredicate` gets "reused
  verbatim" for this rejection — checked against the real code and **false**: `maskOrPredicate` is
  thrown today only from `checkFactor`'s `.iverson` case, an unrelated syntactic construct (an
  Iverson-bracket factor in an assignment's RHS body), never from anything touching `Nonlin`'s own
  mask field. `NonlinCompileError.maskedAxiswiseNotSupported` is the sole, real mechanism; the plan
  reuses no existing constructor for this rejection.
- **PyTorch interpreter support is deferred with no scheduled thread** — mirrors thread 5's own
  precedent phrasing verbatim ("no client has asked for it... deferred with no scheduled thread,
  not merely sequenced later"). Nothing about this thread changes that status.
- **JAX interpreter support is out of scope for this thread, but not for the reason PyTorch is.**
  Per the user's own stated intent, JAX — not Dense — is the intended **primary long-term
  consumer** of this whole Eval IR; Dense's role in this thread is to establish the checked
  reference semantics (§2.2's `reference64Transcendental` contract) a future JAX lowering must
  match, not to be a permanent parallel backend. JAX is excluded here purely because
  `experiments/jax_bridge/EvalPlanCodegen.lean` is already broken against Wave F's `PlanStep`/
  `CheckedPlanStepEvidence` generalization — confirmed by directly running `lake build
  JaxExperiment` this session (§0) — an unrelated, pre-existing repair with its own blast radius,
  not something to rush into this thread's tail end alongside new nonlinearity semantics. **This is
  a near-term follow-up priority, not an indefinitely-deferred one like PyTorch**: the natural next
  slice after this one is (a) repair `EvalPlanCodegen.lean`'s `PlanStep` breakage on its own, with
  no nonlinearity content, then (b) add `.pointwise`/`.axiswise` JAX lowering on top of the checked
  types this thread introduces (`RawPointwisePlan`/`RawAxiswisePlan`/`CheckedPointwisePlan`/
  `CheckedAxiswisePlan` are already backend-neutral — only `runDensePointwise`/`runDenseAxiswise`
  are Dense-specific, exactly the same relationship `.assign`/`.scan` already have with thread 5's
  `loweringToAffineTableCandidate`/`loweringToEinsumCandidate`). A future JAX lowering should also
  follow §0a's "owned by the enum" single-dispatch-point pattern (a `PointwiseFn.toJax`/
  `AxiswiseFn.toJax`-shaped pair, analogous to `PointwiseFn.apply`/`AxiswiseFn.apply` but lowering
  to JAX expressions instead of computing `DenseTensor`s directly) rather than inlining a fresh
  match in the lowering file. Do not conflate this bullet's framing with PyTorch's above when
  writing Task 6's doc correction or completion record — they are deferred for different
  reasons and at different urgency, and treating them identically would misstate JAX's real
  priority to the next thread's author.
- `reference64Transcendental`'s per-function ULP bounds (architecture doc §2.2 table) are **not
  represented as Lean constants anywhere in this thread** — a corrected claim from an earlier
  draft, which asserted they'd be "recorded as named Lean constants" without any task, file, or
  fixture actually producing one (caught by grepping the plan itself for "ULP"/"named Lean
  constant" and finding no consumer). The four 0-ULP functions (`relu`, `leakyrelu`, `normalize`,
  `l2normalize`) are pinned by **bit-exact fixtures** (Tasks 1/3), which is already the correct,
  sufficient representation of a 0-ULP bound — a separate `def reluUlpBound : Nat := 0` constant
  with no consumer would be pure decoration. The remaining four functions' bounds
  (2/2/4/2-per-element) genuinely have no Lean representation and none is added here: per the
  architecture doc's own text, turning a bound into "an actual Lean constant with a pinning test"
  is tied to having *real measured output* to pin against, which doesn't exist until a second
  backend does — creating an unconsumed placeholder constant now would be speculative code this
  thread has no use for. The architecture doc's thread 1 status ("Specified, not validated") is
  unchanged by this thread; state this explicitly in the completion record rather than silently
  dropping the distinction.

## 3. Architecture: how a nonlin statement compiles (new, not previously documented)

This is the part of the design not literally spelled out in the pre-agreed rulings; it was worked
out this session to make "checkNonlin's top-level call site becomes real compilation" concrete and
is verified against real code, not asserted.

**The problem.** `RHSExpr.nonlin` attaches to the *same* statement as the affine/contraction body
(`RHSExpr { body; nonlin; agg }`), but `PlanStep.assign`'s payload, `AssignPlan`, has no nonlin
field of its own — and per ruling 1, the new `PlanStep` cases are entirely separate node kinds.
`.axiswise`'s reduction axis is named only by a `.freeNorm`-marked LHS slot (`s.`/`m.` surface
syntax), and `checkLHSSlot` (the top-level LHS-slot preflight) currently rejects `.freeNorm`
outright — meaning **no source program using `softmax`/`normalize`/`l2normalize` can compile
through the Plan pipeline unless `checkLHSSlot` is also relaxed**; leaving it rejecting would make
`.axiswise` type- and checker-complete but permanently unreachable from surface syntax, which is
not "Dense interpreter support" as the architecture doc's thread 4 row states it.

**The design.** A nonlin-bearing plain statement compiles to **two chained `PlanStep`s**: the
existing linear `AssignPlan` (unchanged, publishing into a new *internal* slot instead of the
statement's name), followed by a `.pointwise`/`.axiswise` step reading that internal slot and
writing the slot actually published under the statement's name. `rhs.nonlin = .identity` keeps
today's single-step behavior exactly (no internal slot, the `AssignPlan` publishes directly).

```text
rhs.nonlin = .identity        : [ .assign  → publish as `nm` ]                      (unchanged)
rhs.nonlin = .pointwise pf    : [ .assign  → internal slot ] → [ .pointwise → publish as `nm` ]
rhs.nonlin = .axiswise fn none: [ .assign  → internal slot ] → [ .axiswise  → publish as `nm` ]
rhs.nonlin = .axiswise _ (some _) : rejected at compile tier (NonlinCompileError), no PlanStep built
```

`checkLHSSlot` relaxes `.freeNorm` to `pure ()` (same treatment as `.free`) — syntactically
admitted, exactly like `checkScanLHSSlot` already admits `.iterAt`/`.iterNext` while deferring
cross-construct consistency. Consistency between a statement's LHS markers and its `Nonlin` kind
is **not** re-litigated as another preflight rule (`checkStmt`'s existing sub-construct order is
unchanged) — it moves to a new, dedicated compile-tier function, `resolveNonlinAxis`, mirroring
`ScanCompileError`'s own "second closed family beside `CapabilityError`" precedent (§0):

```lean
inductive NonlinCompileError
  | noMarkedReductionAxis       (stmtName : String)
  | multipleMarkedReductionAxes (stmtName : String) (firstPos secondPos : Nat)
  | unmarkedReductionAxis       (stmtName : String) (pos : Nat)
  | maskedAxiswiseNotSupported  (stmtName : String)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Resolve which output-slot position (if any) is the axiswise reduction axis, checking it
    agrees with the statement's own `Nonlin`. `slots` is the statement's LHS slot list — the
    returned position indexes directly into it, and 1:1 into the `outputShape`/`retainedUids` a
    `.free`/`.freeNorm`-only slot list produces, since `freeUidOrFail` drops no slots. -/
def resolveNonlinAxis (stmtName : String) (nonlin : Nonlin) (slots : List LHSSlot) :
    Except NonlinCompileError (Option Nat) := do
  let normPositions : List Nat :=
    slots.zipIdx.filterMap (fun (sl, i) => match sl with | .freeNorm _ => some i | _ => none)
  match nonlin with
  | .axiswise _ (some _) => throw (.maskedAxiswiseNotSupported stmtName)
  | .axiswise _ none =>
      match normPositions with
      | [] => throw (.noMarkedReductionAxis stmtName)
      | [p] => pure (some p)
      | p1 :: p2 :: _ => throw (.multipleMarkedReductionAxes stmtName p1 p2)
  | .identity | .pointwise _ =>
      match normPositions with
      | [] => pure none
      | p :: _ => throw (.unmarkedReductionAxis stmtName p)
```

Verified via `check-snippet.sh` against real `LHSSlot`/`Nonlin`/`DSL.Ast` values, including five
`#guard`s: a valid single-freeNorm axiswise case, a missing-marker rejection, a masked-axiswise
rejection, a marker-present-but-pointwise rejection, and the unmarked-identity pass-through.

`PlanCompileCause` (`EvalPlan.lean`) gains a `.nonlin (cause : NonlinCompileError)` arm alongside
its existing `.scan (cause : ScanCompileError)`, with a matching `liftNonlin` in `Compile.lean`
beside `liftCapability`/`liftShape`/`liftPlanError`/`liftBindings`.

**`resolveNonlinAxis` deliberately rejects two program shapes the legacy evaluator silently
accepts — verified against the real `resolveNonlin`/`normAxisUidOf`, not assumed.** This is a real
behavioral delta, not "mere consistency checking," and must be documented as an intentional
tightening rather than left implicit:

1. **A `.freeNorm` marker combined with `.identity`/`.pointwise` nonlin.** The legacy
   `resolveNonlin` (`Eval/Nonlin.lean`) never inspects `slots` in its `.identity`/`.pointwise`
   branches — it accepts unconditionally regardless of any marker present. `resolveNonlinAxis`
   rejects this combination as `unmarkedReductionAxis`.
2. **Multiple `.freeNorm` markers on an axiswise statement.** The legacy `normAxisUidOf` is
   `slots.findSome? (·.normUID?)` — first match wins, extras silently ignored, no error.
   `resolveNonlinAxis` rejects multiple markers as `multipleMarkedReductionAxes`.

Both tightenings are judged correct — marking an axis for normalization while not normalizing
over it, or marking two axes for a single reduction, both look like unconditional user error in
any real program, not an intentional pattern the legacy evaluator's silence was ever protecting.
But "may be preferable" is not the same claim as "consistency checking," and Task 3 must add a
fixture for each showing `evalScheduled` accepts (or, for case 1, treats the marker as a no-op)
while `prepareEvalPlan` rejects with the exact constructor above — proving the delta is real,
understood, and intentional, not an accidental narrowing discovered later by a confused
differential-testing failure.

**Why this doesn't need a second local-operation representation.** The new `.pointwise`/
`.axiswise` steps are single-source/single-destination with no term/factor/reduction structure at
all — closer to `.scan`'s "generic path" through `PlanStep.sourceSlots`/`destinationSlots` than to
`.assign`'s per-term/per-factor loop. `checkPlan`'s three match blocks each gain a `.pointwise _ |
.axiswise _` arm sitting beside the existing `.scan _` arm (same generic-path treatment, same
placeholder `0 0` locators for `invalidForwardRead`), not a new loop shape.

**Why `sourceSlot == destinationSlot` needs no guard inside `checkPointwise`/`checkAxiswise`.**
`checkPlan`'s own wiring discipline makes this unreachable structurally, not by luck: a step's
destination must be *unavailable* immediately before the step (checked first), and (via the
generic `sourceSlots` path) its source must be *available* at that same point, read from the same
`available` table before this step's own destination is marked produced. The same table entry
cannot be both `false` (required for the destination check to pass) and `true` (required for the
source check to pass) at once, so a hand-built `RawPointwisePlan`/`RawAxiswisePlan` with
`sourceSlot == destinationSlot` is rejected by `checkPlan` (as `invalidForwardRead`) before
`checkPointwise`/`checkAxiswise` is ever called with it, for **every** destination that was not
already produced by an earlier step. (If the destination *was* already produced — e.g. reused as
an unrelated later output — `checkPlan`'s destination-availability check rejects it even earlier,
as `inputSlotOverwritten`/`duplicateDestination`.) This is a call-site precondition the checker
relies on rather than re-verifies, in the same spirit `Scan.lean` flags for `baseWriteRowsOk`'s own
preconditions (§4's case×class table) — Task 2 pins it with a regression fixture at the `checkPlan`
level specifically, not inside `checkPointwise`/`checkAxiswise`'s own tests, so the reliance is
tested rather than folklore.

**Why `AxiswiseFn.apply` exists, mirroring the already-existing `PointwiseFn.apply`.**
`Eval/Nonlin.lean` already has `PointwiseFn.apply : PointwiseFn → DenseTensor → DenseTensor`,
whose own doc comment states the design intent explicitly: "owned by the enum, so a new pointwise
function has exactly one place to be interpreted." `AxiswiseFn` never got the same treatment — the
legacy `applyNonlin`'s `.axiswise` case inlines a 3-way match over `softmax`/`normalize`/
`l2normalize` directly, and a first draft of this plan's `runDenseAxiswise` would have duplicated
that same inline match a second time, permanently losing the single-touch-point property
`PointwiseFn` already has. Adding `AxiswiseFn.apply : AxiswiseFn → Nat → List UID → Option
BoolExpr → DenseTensor → DenseTensor` to `Eval/Nonlin.lean`, symmetric with `PointwiseFn.apply`,
and refactoring `applyNonlin` to delegate both cases to the enum's own method, closes that gap —
verified compiling and **behavior-preserving** (five `#guard`s comparing the refactored
`applyNonlin` against its real pre-refactor form on identity/pointwise/all-three-axiswise cases,
all equal on `.data`; §0a). After this, a future new pointwise or axiswise function touches
exactly: its constructor in `DSL/Ast.lean`, its own `*T` implementation plus one match arm in
`PointwiseFn.apply`/`AxiswiseFn.apply` (both `Eval/Nonlin.lean`), and a new fixture — nothing in
`Eval/Plan/Nonlin.lean` changes, since the Plan-layer checker is fully function-agnostic (§4's
table: no row depends on `fn`) and the Plan-layer worker (`runDensePointwise`/`runDenseAxiswise`,
Task 2) delegates its entire per-function dispatch to the enum, exactly as pointwise already does.
One pre-existing, unavoidable cost this doesn't remove: `PointwiseFn.toBrOp`/`AxiswiseFn.toBrOp`
(`DSL/Ast.lean`, the old `Br`/categorical lowering, unrelated to `Eval/Plan/`) still gains a new
match arm per future constructor — a property of the AST's own shape, not introduced or worsened
by this thread's design. A future JAX lowering (§2.2's next-slice note) should follow this same
single-dispatch-point pattern (`PointwiseFn.toJax`/`AxiswiseFn.toJax`) rather than inlining a fresh
match of its own.

**Why `checkPointwise`/`checkAxiswise` share a `checkNonlinIO` helper instead of each checking
their own geometry inline.** §4's case×class table rows 1-7 are identical obligations for both
step kinds (slot range, dtype, shape agreement) — only row 8 (`axisPos` range) is
axiswise-specific. Writing both checks out inline in both functions would put two near-identical
~6-guard blocks in the same new file, exactly the shape a reviewer can miss precisely *because*
both are new (a diff shows no prior version to compare drift against). `checkNonlinIO (sigs)
(sourceSlot destinationSlot : TensorSlot) (shape : Array Nat) : Except NonlinPlanError
(TensorSignature × TensorSignature)` factors rows 1-7 once; `checkPointwise` calls it and returns,
`checkAxiswise` calls it then adds row 8 on top. Verified compiling with five `#guard`s (a passing
case, a `slotOutOfRange`, a `sourceShapeMismatch`, and a passing/failing `axisPositionOutOfRange`
pair through `checkAxiswise` specifically, confirming the shared helper's failures propagate
through the axiswise-specific wrapper correctly; §0a). This also lets Task 1's mutation-testing
cover rows 1-7 once (through `checkPointwise`) plus one delegation check (through `checkAxiswise`),
rather than mutating all seven rows through both functions independently.

**Why `PointwiseFn`/`AxiswiseFn` need a manual `BEq` instance, not a `deriving` clause edit.**
Both derive `DecidableEq, Repr, Lean.ToExpr, Inhabited` in `DSL/Ast.lean` — no `BEq`. `PlanStep`
derives `DecidableEq, BEq, Repr, Inhabited` today, and many existing tests compare `RawEvalPlan`/
`PlanStep` values with `==` (needs `BEq`, not just `DecidableEq`), so `PlanStep`'s new payload
types must support `BEq` too, or `PlanStep`'s own `deriving BEq` breaks. Rather than touching
`DSL/Ast.lean` (surgical-changes discipline — this thread does not otherwise touch that file), add

```lean
instance : BEq LeanNCD.PointwiseFn := ⟨fun a b => decide (a = b)⟩
instance : BEq LeanNCD.AxiswiseFn := ⟨fun a b => decide (a = b)⟩
```

in the new `Nonlin.lean` (built from the existing `DecidableEq` instance, standard and verified to
compile and behave correctly via two `#guard`s). `AggOp`/`BoolExpr` have the identical
missing-`BEq` shape and are not touched — nothing downstream of them needs to derive `BEq` today.

## 4. Case × class table — `checkPointwise`/`checkAxiswise` geometry obligations

Required per the slice-plan skill: a new geometry-checking predicate family gets this table as an
explicit deliverable even though it is not an *instance* of the write-geometry defect family found
four times in F3/F4 (free-extent, pinned-literal, write-map-rank, `stepWriteRowsOk`) — verified
below, not assumed, since every `(c)` cell is a candidate instance *N+1* regardless of ancestry.

| # | Case | Pointwise | Axiswise | Class |
|---|---|---|---|---|
| 1 | `sourceSlot` in range | checked (`slotOutOfRange`) | checked | **Required** |
| 2 | `destinationSlot` in range | checked | checked | **Required** |
| 3 | source dtype `== .f64` | checked (`dtypeNotAdmitted`) | checked | **Required** |
| 4 | destination dtype `== .f64` | checked | checked | **Required** |
| 5 | source dtype `==` destination dtype | checked (`dtypeMismatch`) | checked | **Required**, vacuous today — only `.f64` exists (same single-valued-vocabulary shape as `checkAssign`'s own `dtypeMismatch`) |
| 6 | source signature shape `==` declared `shape` | checked (`sourceShapeMismatch`) | checked | **Required** |
| 7 | destination signature shape `==` declared `shape` | checked (`destinationShapeMismatch`) | checked | **Required** |
| 8 | `axisPos < shape.size` | n/a | checked (`axisPositionOutOfRange`) | **Required** (axiswise only) |
| 9 | rank-0 (scalar) `shape` | admitted | rejected as a corollary of #8 (`0 < 0` is false) | Silently admitted (pointwise, harmless — elementwise map over a 1-element array); not a separate case for axiswise |
| 10 | mask present (`Nonlin.axiswise fn (some _)`) | n/a | **Forbidden**, but at the compile tier (`NonlinCompileError.maskedAxiswiseNotSupported`) before a `RawAxiswisePlan` can exist — the raw type carries no mask field at all | Forbidden by type absence, not by a runtime-checked predicate |
| 11 | negative `axisPos` | n/a | Forbidden by type (`axisPos : Nat`) | Forbidden by type |
| 12 | `sourceSlot == destinationSlot` (self-aliasing) | not checked locally | not checked locally | Silently ignored *here*, but proven unreachable by `checkPlan`'s own availability discipline (§3) — pinned by a Task 2 regression fixture at the `checkPlan` level, not treated as folklore |
| 13 | two steps writing the same `destinationSlot` | not checked | not checked | Silently ignored by design — owned by `checkPlan`'s outer wiring loop (`duplicateDestination`/`inputSlotOverwritten`), identical division of labor to `checkAssign` |
| 14 | `sourceSlot` read before produced/available | not checked | not checked | Silently ignored by design — owned by `checkPlan`'s outer wiring loop (`invalidForwardRead` via the generic `sourceSlots` path), identical to `.scan`'s own treatment |
| 15 | worker-side out-of-bounds write | n/a | n/a | **Not a write-path predicate at all** — verified by reading every reused function: `reluT`/`sigmoidT`/`tanhT`/`geluT`/`leakyReluT` are `⟨t.shape, t.data.map f⟩` (shape- and length-preserving by construction); `softmaxT`/`normalizeT`/`l2normalizeT`'s `perRow` writes back only to coordinates it read from the same tensor. There is no second "target" tensor addressed via an independently-boundable affine map the way `commitWrite` (`Scan.lean`) has — this is the structural reason this family is not a 5th instance of the free-extent/pinned-literal/write-rank/`stepWriteRowsOk` defect shape, not merely an unexamined absence |

## 5. Task graph and review weight

```text
Task 1: raw types + checker
    │  (Task 2's implementer may start drafting once Task 1's code exists,
    │   without waiting for Task 1's review — but must not merge ahead of it)
    ▼
Task 2: dense worker + wiring
    │
    ▼
Task 3: source compiler ──────┐
                               ├─> Task 5: differential/corpus ─> Task 6: closure
Task 4: numericMode removal ──┘                                  (doc corrections,
                                                                   discoverability,
                                                                   completion record,
                                                                   whole-branch review)
```

Task 2 genuinely depends on Task 1 — it edits the file Task 1 creates and needs Task 1's raw and
checked types to exist — this is a real dependency, not a parallel branch; the diagram's earlier
draft drew them side-by-side, which was misleading on its own even though the surrounding prose
already correctly described the dependency. Tasks 1 and 2 both touch the closed `PlanStep`/
`CheckedPlanStepEvidence` sums that every backend depends on — soundness-relevant, per the task
brief's own instruction. Task 3 is the thread's architectural centerpiece (§3). Task 4 is
independent of Tasks 1-3 and can run fully in parallel with them. Task 5 depends on Task 3 (needs
real compiled nonlin steps to differential-test) and on Task 4 (fixture literals must already have
`numericMode` gone). Task 6 is the mandatory whole-branch close, and now also owns the architecture
doc corrections (folded in from what was originally a standalone Task 5 — see Task 6's own
opening note for why).

| Task | Outcome | Independent review reason | Risk / process weight |
|---|---|---|---|
| 1 | `RawPointwisePlan`/`RawAxiswisePlan`, `NonlinPlanError`, `checkPointwise`/`checkAxiswise` | New checker over a soundness-relevant closed family; the case×class table is itself a review artifact | **Moderate.** ~10-11 assertions, not 6 (2 passing baselines + 2 slot-range + 2 dtype + 2 shape + 1 axis-range + 2 scalar-shape cases), each mutation-tested except `dtypeMismatch` (structurally unreachable given today's single-valued `f64`-only dtype vocabulary — no fixture can reach it, same as `checkAssign`'s own case) — small production surface, but wrong here means silently-wrong nonlin results everywhere. |
| 2 | `runDensePointwise`/`runDenseAxiswise`, `PlanStep` extended to 4 constructors, all four exhaustive matches updated | Touches the closed sum every backend and every existing `.assign`/`.scan` test depends on — a regression here is invisible in a diff that only shows added match arms | **High.** Two independent final reviewers for this task specifically (not just the whole-branch review) — this is the "touches a soundness-relevant closed sum" case the task brief calls out by name. ~5-6 fixtures (one hand-built hybrid graph per new constructor, plus the two `sourceSlot==destinationSlot` regressions — `invalidForwardRead` and `duplicateDestination` — from §3/§4 row 12). |
| 3 | `checkLHSSlot` relaxed, `checkNonlin` real at top level, `resolveNonlinAxis`/`NonlinCompileError`, `prepareEvalPlan` two-step chaining | Main production feature; new classification logic with no precedent to copy (§3) | **High.** No fixture count discount — this is genuinely new compiler logic, and its gate now runs the full `Eval.Plan.*` suite (not just its own two new files) since it edits `prepareEvalPlan`'s sole production compiler path. Expect at least one fix round; do not compress its review because Tasks 1/2 land clean. |
| 4 | `numericMode`/`NumericMode`/`numericModeNotAdmitted` deleted everywhere (§0's exact list) | Touches every `RawEvalPlan` literal in the test suite — a reviewer needs the exact file list to confirm nothing was missed, not just skim a diff | **Low-moderate.** Mechanical but wide (5 production files, 9 test files by exact count in §0). One review round. |
| 5 | New end-to-end pointwise/axiswise differential fixtures, including the two deliberate legacy-narrowing fixtures from §3; confirmatory (not expected-to-change) re-run of the scan corpus split; `ScatterNonlinRejectTest.lean` confirmed out of scope | No existing generator exercises the new reachable fragment — this task's fixtures are the only evidence the Dense path is *actually* correct end-to-end, not just checker-clean | **Moderate-high.** 8 new fixtures (one per nonlin function, donors named in Task 3), each compared against `evalScheduled` bit-for-bit. |
| 6 | Architecture doc corrections (§7.6, §2.2, §5.1), `AGENTS.md`/`LeanNCD.lean` discoverability, completion record, whole-branch review | Every prior slice's most valuable finding came from the whole-branch tier, never a per-task diff (skill §4); the doc corrections are sequenced here specifically because their own claims depend on Tasks 1-3 having actually landed | **High.** Two independent final reviewers (soundness-relevant closed sum, per the task brief) — schedule both, do not compress to one because Tasks 1-5 passed clean. |

## Task 1: raw types, closed error family, geometry checkers

### Outcome

`LeanNCD/Eval/Plan/Nonlin.lean` exists with `RawPointwisePlan`/`RawAxiswisePlan`,
`NonlinPlanError`, `CheckedPointwisePlan`/`CheckedAxiswisePlan`, a shared `checkNonlinIO` helper,
and `checkPointwise`/`checkAxiswise` built on it, each satisfying every "Required" row of §4's
table.

### Files

- `LeanNCD/Eval/Plan/Nonlin.lean` (new)
- `test/Eval/Plan/NonlinCheckTest.lean` (new)
- `leanncd/lakefile.toml` (`Tests` library's `globs` list gains `"Eval.Plan.NonlinCheckTest"`)

### Implementation

1. **Add `"Eval.Plan.NonlinCheckTest"` to `lakefile.toml`'s `Tests` `globs` list** (alphabetically
   near the other `Eval.Plan.*` entries) in the same commit that adds the file. `globs` is
   explicit, not auto-discovered — confirmed by reading `lakefile.toml` directly, `defaultTargets
   = ["LeanNCD", "Tests"]` — so a bare `lake build` silently skips any test module not listed here,
   regardless of whether `lake build <module-name>` (naming it directly, as this task's own Gate
   does) happens to still work. Do this for every new test module in Tasks 1-3, as each lands, not
   deferred to Task 6/closure — a module absent from `globs` for even one intermediate task's own
   review means that reviewer's "green build" claim doesn't include the file they're reviewing.
2. `import LeanNCD.Eval.Plan.Kernel` and `import LeanNCD.Eval.Nonlin` (gives `TensorSlot`/
   `TensorSignature`/`ScalarDType` and `LeanNCD.PointwiseFn`/`AxiswiseFn`/the dense math
   transitively via `DSL.Ast`/`Eval.Tensor`). Add the manual `BEq` instances from §3.
3. Add `RawPointwisePlan { sourceSlot destinationSlot : TensorSlot; shape : Array Nat; fn :
   LeanNCD.PointwiseFn }` and `RawAxiswisePlan { sourceSlot destinationSlot : TensorSlot; shape :
   Array Nat; axisPos : Nat; fn : LeanNCD.AxiswiseFn }`, both `deriving DecidableEq, BEq, Repr,
   Inhabited` — verified via `check-snippet.sh` (§0).
4. Add `NonlinPlanError` exactly as drafted in §4's row list (`slotOutOfRange`, `dtypeNotAdmitted`,
   `dtypeMismatch`, `sourceShapeMismatch`, `destinationShapeMismatch`, `axisPositionOutOfRange`),
   `deriving DecidableEq, BEq, Repr, Inhabited`.
5. Add `CheckedPointwisePlan`/`CheckedAxiswisePlan` with `private mk ::` (not bare `structure ...
   where private` — the F2/Wave-C-documented trap), each wrapping a `raw` field, `deriving Repr`.
6. Implement `checkNonlinIO (sigs) (sourceSlot destinationSlot : TensorSlot) (shape : Array Nat) :
   Except NonlinPlanError (TensorSignature × TensorSignature)` exactly as verified in §0a, covering
   §4's rows 1-7 (the obligations common to both step kinds) in the same order `checkAssign` uses
   (destination lookup, source lookup, dtype checks, shape checks). `checkPointwise` calls it and
   returns; `checkAxiswise` calls it then adds row 8's `axisPos < shape.size` check on top — neither
   function repeats rows 1-7's checks itself.

### Fixtures (donors named, per skill discipline)

All in `test/Eval/Plan/NonlinCheckTest.lean`, mirroring `GraphDenseTest.lean`'s `oneNodeSigs`-style
hand-built signature tables (not cloned from an existing Plan-layer fixture — no prior
pointwise/axiswise Plan fixture exists to clone from; each is a minimal 2-slot table, `shape :=
#[2]`, built directly per §4's row):

- One passing `RawPointwisePlan`/`RawAxiswisePlan` each (baseline — clone this table for every
  mutation below, changing exactly the one field named).
- Row 1/2: `sourceSlot`/`destinationSlot` set past `sigs.size` → `slotOutOfRange`.
- Row 3/4: a signature with `dtype := .bool` at the source/destination slot → `dtypeNotAdmitted`.
- Row 5 (`dtypeMismatch`): **no fixture** — structurally unreachable, since both guards above must
  already pass (both dtypes `== .f64`) before this check runs, making them trivially equal; same
  vacuous shape as `checkAssign`'s own `dtypeMismatch`. Do not attempt to construct one.
- Row 6/7: `shape := #[3]` on the raw plan against a `#[2]`-shaped signature → `sourceShapeMismatch`/
  `destinationShapeMismatch`.
- Row 8 (axiswise only): `axisPos := 2` against `shape := #[2]` (**rank 1** — one array element
  means one axis, of size 2; the only valid position is `0`) → `axisPositionOutOfRange`.
- Row 9: `shape := #[]` (rank 0) pointwise passes; rank-0 axiswise with `axisPos := 0` is rejected
  by row 8's own guard (`0 < 0` false) — one fixture confirming this, not a separate check.

### Mutation checks

- Remove each `unless` guard in `checkNonlinIO` **except row 5's `dtypeMismatch` guard**
  independently; confirm the corresponding fixture through `checkPointwise` starts passing when it
  should fail (i.e. the guard was load-bearing), **then confirm the same guard's removal is also
  visible through `checkAxiswise`** with one fixture (not all six) — this confirms delegation
  rather than re-mutating rows 1-7 a second time. Remove row 8's `axisPos` guard independently
  (axiswise-only, no pointwise analogue). Do not attempt to mutate-test row 5's guard — no fixture
  can reach it (Fixtures section above), so there is nothing to remove-and-observe; leave it as an
  inline code-review check that the guard exists and matches `checkAssign`'s own precedent, not a
  mutation test.
- Restore; confirm all fixtures pass again.

### Gate

```bash
cd leanncd
grep -n "NonlinCheckTest" lakefile.toml   # confirm the module is in Tests' globs list
lake build Eval.Plan.NonlinCheckTest
lake build Tests   # confirms the module builds as part of the DEFAULT target, not just standalone
lake build LeanNCD
```

Independent task review before Task 3 (Task 2 can run in parallel with this review since it only
needs Task 1's *types*, not its passing review, to start drafting — but must not merge ahead of
Task 1's review completing).

## Task 2: dense workers and `PlanStep` wiring

### Outcome

`PlanStep` has four constructors; `checkPlan`/`runDensePlan`/`PlanStep.sourceSlots`/
`destinationSlots`/`CheckedPlanStepEvidence` all handle `.pointwise`/`.axiswise` via the generic
(non-`.assign`) path; a hand-built `RawEvalPlan` chaining `.assign → .pointwise` and `.assign →
.axiswise` end-to-end passes `checkPlan` + `runDensePlan` and produces the expected tensor.

### Files

- `LeanNCD/Eval/Plan/Nonlin.lean` (adds `runDensePointwise`/`runDenseAxiswise`)
- `LeanNCD/Eval/Nonlin.lean` (adds `AxiswiseFn.apply`; refactors `applyNonlin` to delegate to
  `PointwiseFn.apply`/`AxiswiseFn.apply` — small, additive, behavior-preserving, §0a)
- `LeanNCD/Eval/Plan/RawStep.lean` (adds `import LeanNCD.Eval.Plan.Nonlin`; `PlanStep` gains
  `.pointwise (p : RawPointwisePlan)` / `.axiswise (a : RawAxiswisePlan)`)
- `LeanNCD/Eval/Plan/EvalPlan.lean` (`CheckedPlanStepEvidence`, `PlanStep.sourceSlots`,
  `PlanStep.destinationSlots`, `checkPlan`'s three match blocks, `runDensePlan`'s dispatch)
- `test/Eval/Plan/NonlinDenseTest.lean` (new)
- `test/Eval/Plan/GraphCheckTest.lean` (two new regression fixtures, §3's `sourceSlot ==
  destinationSlot` unreachability claim — see Fixtures below)
- `leanncd/lakefile.toml` (`Tests` `globs` list gains `"Eval.Plan.NonlinDenseTest"`)

### Implementation

1. Add `"Eval.Plan.NonlinDenseTest"` to `lakefile.toml`'s `Tests` `globs` list, same rationale as
   Task 1 item 1 — do this before or alongside adding the file, not deferred.
2. In `LeanNCD/Eval/Nonlin.lean`: add `AxiswiseFn.apply (fn : AxiswiseFn) (axisPos : Nat)
   (axisUids : List UID) (mask? : Option BoolExpr) (t : DenseTensor) : DenseTensor`, matching
   `fn` to call `softmaxT`/`normalizeT`/`l2normalizeT` — symmetric with the file's existing
   `PointwiseFn.apply`, verified compiling in §0a. Refactor `applyNonlin`'s `.pointwise`/
   `.axiswise` cases to `pf.apply t` / `fn.apply p axisUids m t` respectively — verified
   **behavior-preserving** via five `#guard`s against the real (pre-refactor) `applyNonlin` in §0a;
   re-run `test/Eval/NonlinTest.lean` unchanged afterward as the production regression check (it
   already exercises `resolveNonlin`/`applyNonlin` directly and must stay green with zero edits).
3. `runDensePointwise (c : CheckedPointwisePlan) (src : DenseTensor) : DenseTensor :=
   c.raw.fn.apply src` (reuses `PointwiseFn.apply` — no new math).
4. `runDenseAxiswise (c : CheckedAxiswisePlan) (src : DenseTensor) : DenseTensor :=
   c.raw.fn.apply c.raw.axisPos [] none src` (reuses the new `AxiswiseFn.apply` from item 2 — no
   new math, no new match). `[]`/`none` because a checked `RawAxiswisePlan` can never carry a mask
   or axis-UID (§3 — Plan-layer `TensorSignature` is UID-free by design); verified via
   `check-snippet.sh` that this compiles against the real functions.
5. `RawStep.lean`: add the import, extend `PlanStep`'s `deriving` list unchanged (`DecidableEq,
   BEq, Repr, Inhabited` — already verified compiling with the two new constructors, §0).
6. `EvalPlan.lean`:
   - `CheckedPlanStepEvidence` gains `| pointwise (c : CheckedPointwisePlan) | axiswise (c :
     CheckedAxiswisePlan)`.
   - `PlanStep.sourceSlots`/`destinationSlots` gain `| .pointwise p => #[p.sourceSlot]` / `#
     [p.destinationSlot]` and the `.axiswise` analogues.
   - `checkPlan`'s context-check match: `.scan _ => pure ()` becomes `.scan _ | .pointwise _ |
     .axiswise _ => pure ()` (no top-level context obligation for any of the three).
   - `checkPlan`'s source-check match: the `.scan _ => (generic sourceSlots loop)` arm becomes `|
     .scan _ | .pointwise _ | .axiswise _ => (same loop)`.
   - `PlanStepError` gains a third constructor, `| nonlin (stepIndex : Nat) (cause :
     NonlinPlanError)`, mirroring `.scan (stepIndex : Nat) (cause : ScanPlanError)`'s shape exactly
     — `NonlinPlanError` is not a `PlanError`, so it cannot go through the existing `.assign (cause
     : PlanError)` arm the way a bare-`AST`-decidable failure would. Verify this against
     `checkPlan`'s real call sites before writing the throw expressions below.
   - `checkPlan`'s dispatch match gains `| .pointwise p => match checkPointwise raw.tensorSigs p
     with .error e => throw (.nonlin ni e) | .ok c => checkedNodes := checkedNodes.push (.pointwise
     c)`, and the `.axiswise` arm the same shape with `checkAxiswise`.
   - `runDensePlan`'s dispatch gains `| .pointwise c => store := store.set! c.raw.destinationSlot
     (runDensePointwise c (store.getD c.raw.sourceSlot placeholder))` and the `.axiswise` analogue.
7. Re-derive `PlanStepError`'s `DecidableEq, BEq, Repr, Inhabited` (already required fields all
   support it, per item 6's new constructor).

### Fixtures (donors named)

`test/Eval/Plan/NonlinDenseTest.lean`, cloning `GraphDenseTest.lean`'s `idRead`/`idNode`/
`oneNodeSigs`/`oneNodePlan` shape directly (same donor style: hand-computed expected tensor, not
read back from the interpreter):

- **Pointwise chain**: clone `oneNodePlan`, change `steps` to `#[.assign (idNode 1 0), .pointwise {
  sourceSlot := 1, destinationSlot := 2, shape := #[2], fn := .relu }]` over input `#[-1.0, 2.0]` —
  expect `#[0.0, 2.0]` (donor value: `NonlinTest.lean`'s `reluT (t1 [-1, 2, -3, 4]) == t1 [0, 2, 0,
  4]`, same function, smaller vector).
- **Axiswise chain**: clone the pointwise fixture, change the second step to `.axiswise {
  sourceSlot := 1, destinationSlot := 2, shape := #[2,2], axisPos := 1, fn := .normalize }` over a
  source **shaped** `#[2,2]` with **data** `#[1,3,2,2]` (donor: `NormTest.lean`'s NM1,
  `A=[[1,3],[2,2]] ⇒ [[0.25,0.75],[0.5,0.5]]` — the flattened `1,3,2,2` is `A`'s data in row-major
  order, not its shape; an earlier draft of this fixture conflated the two).
- **`sourceSlot == destinationSlot`, never-produced case** (§3/§4 row 12, the `invalidForwardRead`
  path), in `GraphCheckTest.lean`: a plan whose **only** step is `.pointwise { sourceSlot := 1,
  destinationSlot := 1, shape := #[2], fn := .relu }`, where slot 1 is **not** an input slot and
  has no earlier producer — `available[1]` starts `false`, so the destination-check (which only
  rejects an *already-produced* destination) passes, and the source-check then finds slot 1
  unavailable — confirm `checkPlan` rejects it as `invalidForwardRead`. This is the fixture the
  original draft's single self-aliasing case was actually meant to prove, and didn't: the original
  chained an `.assign` producing slot 1 first, which makes the destination-check reject it earlier
  (below) — verified by reading `checkPlan`'s real loop order (destination-availability runs
  before source-availability, per step), not assumed.
- **`sourceSlot == destinationSlot`, already-produced case** (the `duplicateDestination` path),
  also in `GraphCheckTest.lean`: clone `oneNodePlan`, add a `.pointwise { sourceSlot := 1,
  destinationSlot := 1, shape := #[2], fn := .relu }` step *after* an `.assign` that already
  produced slot 1 — confirm `checkPlan` rejects it as `duplicateDestination` (destination-check
  fires first, since `available[1]` is already `true` by the time this step's own checks run). This
  is the original draft's fixture, relabeled to its real, verified expected error rather than the
  wrong one.

### Mutation checks

- Remove the new `.pointwise`/`.axiswise` arms from `runDensePlan`'s dispatch one at a time; the
  corresponding dense fixture must fail to compile (exhaustiveness) or panic, not silently produce
  a wrong tensor.
- Swap the never-produced self-aliasing fixture's slot 1 to *also* be an input slot (still with no
  `.assign` producer): confirm it now fails via `inputSlotOverwritten` instead of
  `invalidForwardRead` — a third real rejection path for the same self-aliasing shape, distinct
  from both fixtures above, worth knowing rather than silently indistinguishable from
  `duplicateDestination`. Restore.
- Confirm the `applyNonlin` refactor (item 2) is behavior-preserving in the real tree, not just in
  the §0a scratch snippet: `lake build Eval.NonlinTest` must stay green with **zero edits** to that
  file. If it doesn't, the refactor changed behavior and must be fixed before proceeding — do not
  edit `NonlinTest.lean` to make it pass.

### Gate

```bash
cd leanncd
grep -n "NonlinDenseTest" lakefile.toml   # confirm the module is in Tests' globs list
lake build Eval.Plan.NonlinDenseTest
lake build Eval.Plan.GraphCheckTest
lake build Eval.NonlinTest
lake build Tests
lake build LeanNCD
```

**Two independent final reviewers for this task specifically**, per the task brief's instruction
that this touches a soundness-relevant closed sum — do not fold this into Task 6's single
whole-branch pass only; get an early, task-scoped second opinion here too, since Task 3 builds on
top of this wiring and a defect found only at Task 6 would be far more expensive to unwind.

## Task 3: source compiler — real top-level compilation

### Outcome

A surface program like `Y[i] := relu(W[i,j]·x[j])` or `Y[i, s.] := softmax(A[i,s])` compiles
through `prepareEvalPlan` into a real two-step `PlanStep` chain and executes correctly; a masked
axiswise statement, an unmarked axiswise statement, and a marked-but-non-axiswise statement are all
rejected with the exact `NonlinCompileError` constructor from §3.

### Files

- `LeanNCD/Eval/Plan/Error.lean` (`NonlinCompileError`, alongside `ScanCompileError`)
- `LeanNCD/Eval/Plan/EvalPlan.lean` (`PlanCompileCause` gains `.nonlin (cause : NonlinCompileError)`)
- `LeanNCD/Eval/Plan/Compile.lean` (`checkLHSSlot`, `checkNonlin`'s top-level admission,
  `resolveNonlinAxis`, `liftNonlin`, `prepareEvalPlan`'s `.plain` branch)
- `test/Eval/Plan/CompileTest.lean` (capability-preflight-level fixtures)
- `test/Eval/Plan/NonlinCompileTest.lean` (new — compile-tier fixtures)
- `leanncd/lakefile.toml` (`Tests` `globs` list gains `"Eval.Plan.NonlinCompileTest"`)

### Implementation

1. Add `"Eval.Plan.NonlinCompileTest"` to `lakefile.toml`'s `Tests` `globs` list, same rationale as
   Task 1 item 1.
2. `Error.lean`: add `NonlinCompileError` exactly as drafted in §3, `deriving DecidableEq, BEq,
   Repr, Inhabited`. No new imports needed (`String`/`Nat` payloads only).
3. `EvalPlan.lean`: `PlanCompileCause` gains `| nonlin (cause : NonlinCompileError)`.
4. `Compile.lean`:
   - `checkLHSSlot`: change `| .freeNorm a => throw (.unsupportedLhsSlot ...)` to `| .freeNorm _ =>
     pure ()`.
   - `checkNonlin` (the function itself, both call sites currently share it): the **call site
     inside `checkStmt`** now admits — but since `checkNonlin` is shared code, either split it into
     two functions (`checkNonlinTopLevel`/`checkNonlinScanBlock`, the latter unchanged) or keep one
     function parameterized by an `admitNonlin : Bool` flag threaded from each caller. Prefer the
     split — matches this file's existing `checkLHSSlot`/`checkScanLHSSlot` naming precedent more
     directly than a boolean flag would.
   - Add `liftNonlin` beside `liftCapability`/`liftShape`/`liftPlanError`/`liftBindings`.
   - Add `resolveNonlinAxis` exactly as drafted and verified in §3.
   - `prepareEvalPlan`'s `.plain` branch: after computing `retainedUids`/`outputShape` exactly as
     today, call `resolveNonlinAxis nm rhs.nonlin slots` (lifted via `liftNonlin`). Build the
     existing `AssignPlan` targeting an **internal** slot (not `nm`'s eventual published slot) when
     `rhs.nonlin ≠ .identity`; when `.identity`, behavior is byte-for-byte unchanged (single
     `.assign`, published directly) — this is the regression-sensitive branch Task 2's parity
     fixture (F4's own precedent — Compile.lean's Task 2 established `residualizeAssignment` with
     scan-free parity as its explicit gate) must also re-confirm here.
   - For `.pointwise pf`: push a `.pointwise { sourceSlot := internalSlot, destinationSlot :=
     publishedSlot, shape := outputShape, fn := pf }` step; publish `nm` at `publishedSlot`.
   - For `.axiswise fn none` with `resolveNonlinAxis` returning `some p`: push the `.axiswise`
     analogue with `axisPos := p`.
   - `freeUidOrFail` must accept `.freeNorm a => pure a.uid` (currently throws) — update its doc
     comment too (it currently claims "unreachable post-preflight," which becomes false for
     `.freeNorm` once `checkLHSSlot` admits it).

### Fixtures (donors named)

- **Capability preflight** (`CompileTest.lean`, clone existing accepted/rejected fixture pattern
  from that file): confirm `.pointwise`/`.axiswise` (mask `none`) now pass `capabilityPreflight`
  at the top level; confirm scan-block `.pointwise`/`.axiswise` **still** reject via
  `unsupportedNonlin` (clone `ScanContractTest.lean`/`CompileTest.lean`'s existing
  scan-block-rejection fixture, change nothing but confirm the constructor is unchanged).
- **`resolveNonlinAxis` compile-tier fixtures** (`NonlinCompileTest.lean`): the five cases already
  verified via `check-snippet.sh` in §3 (valid single-marker, no-marker, masked, marker-without-
  axiswise, unmarked-identity), each re-run through the real `prepareEvalPlan` end-to-end rather
  than the standalone function, confirming the exact `NonlinCompileError` surfaces as
  `PlanCompileCause.nonlin`.
- **End-to-end compiled examples**, donors named precisely (reused again by Task 5's differential
  fixtures — do not duplicate the tensors, cite the same donor):
  - `relu`: clone `FeedforwardTest.lean` FF2 (`W=[[1,-1],[-2,1]]`, `x=[1,1]` → `H=[0,0]`).
  - `sigmoid`/`tanh`/`gelu`/`leakyrelu`: clone FF5/FF6/FF7/FF8 (`W=I₂`, `x=[-2,2]`, exact expected
    tensors already given in §0).
  - `normalize`/`softmax`: clone `NormTest.lean` NM1/NM2 (`A=[[1,3],[2,2]]`/`A=[[0,0],[0,ln3]]`).
  - `l2normalize`: clone `GenerativeTest.lean` CL3 (`Z1=[[3,4]] → [0.6,0.8]`) and CL3b (all-zero
    row → all-zero, the degenerate-norm edge case).
- **Deliberate legacy-narrowing fixtures** (`NonlinCompileTest.lean`), proving §3's two documented
  deltas from `evalScheduled` are real, understood, and intentional — not discovered later as a
  differential-testing surprise:
  - Clone the `relu` fixture above, add a spurious `.freeNorm` marker to an otherwise-`.pointwise`
    statement's LHS: confirm `evalScheduled` still executes it (the legacy `resolveNonlin` never
    inspects `slots` for `.pointwise`, per §3) while `prepareEvalPlan` rejects it with
    `NonlinCompileError.unmarkedReductionAxis`.
  - Clone the `normalize`/`softmax` fixture above, add a second `.freeNorm` marker on an unrelated
    output axis: confirm `evalScheduled` silently uses only the first marker (`normAxisUidOf` is
    `slots.findSome?`, first match wins, per §3) while `prepareEvalPlan` rejects it with
    `NonlinCompileError.multipleMarkedReductionAxes`.

### Mutation checks

- Revert `checkLHSSlot`'s relaxation; confirm every axiswise end-to-end fixture starts failing at
  preflight instead of compiling (proves the relaxation, not something else, is what makes them
  reachable).
- Revert `resolveNonlinAxis`'s masked-rejection branch (make it fall through to `some p`); confirm
  the masked-axiswise fixture stops being rejected and instead silently builds a `RawAxiswisePlan`
  — restore, confirm rejection returns.
- Swap the `.identity` branch's slot allocation to also always allocate an internal slot (even when
  unused); confirm this changes `tensorSigs.size`/slot numbering versus today's baseline and would
  therefore have been a silent regression — restore the branch, confirm parity.

### Gate

```bash
cd leanncd
grep -n "NonlinCompileTest" lakefile.toml   # confirm the module is in Tests' globs list
lake build Eval.Plan.CompileTest
lake build Eval.Plan.NonlinCompileTest
lake build Tests   # the FULL Eval.Plan.* suite, per §7.1's own requirement below — this task
  # edits prepareEvalPlan's Step D, the one existing production compiler path, so a regression
  # here can silently break any Wave C/F fixture, not just new nonlin ones; two named modules
  # above are not sufficient on their own
lake build LeanNCD
```

Independent task review — this is the architectural centerpiece (§5's task table). Expect at least
one fix round.

## Task 4: delete `numericMode`/`NumericMode`/`numericModeNotAdmitted`

### Outcome

`RawEvalPlan` has no `numericMode` field; `NumericMode` and `PlanError.numericModeNotAdmitted` no
longer exist; every occurrence listed in §0 is gone or updated.

### Files

Production: `LeanNCD/Eval/Plan/Types.lean`, `LeanNCD/Eval/Plan/Graph.lean`,
`LeanNCD/Eval/Plan/Error.lean`, `LeanNCD/Eval/Plan/EvalPlan.lean`, `LeanNCD/Eval/Plan/Compile.lean`.
Tests: `test/Eval/Plan/EvalPlanTest.lean`, `test/Eval/Plan/GraphCheckTest.lean`,
`test/Eval/Plan/GraphDenseTest.lean`, `test/Eval/Plan/KernelCheckTest.lean`,
`test/Eval/Plan/ExecutableTest.lean`, `test/Eval/Plan/CompileTest.lean`,
`test/Eval/Plan/AdapterTest.lean`, `test/Eval/Plan/ContractTest.lean`.
**Not touched**: `experiments/jax_bridge/EvalPlanCodegen.lean` (§0 — already broken, out of scope).

### Implementation

1. `Types.lean`: delete `NumericMode`.
2. `Graph.lean`: delete `RawEvalPlan.numericMode`.
3. `Error.lean`: delete `PlanError.numericModeNotAdmitted`.
4. `EvalPlan.lean`: delete `checkPlan`'s `unless raw.numericMode == .reference64SumProduct do throw
   (.assign (.numericModeNotAdmitted raw.numericMode))` guard.
5. `Compile.lean`: delete `numericMode := .reference64SumProduct` from `prepareEvalPlan`'s
   `RawEvalPlan` literal.
6. Every test-site `RawEvalPlan` literal in the file list above: delete the
   `numericMode := .reference64SumProduct` field.
7. `GraphCheckTest.lean`: delete the direct `#guard (PlanError.numericModeNotAdmitted ...) ==
   PlanError.numericModeNotAdmitted ...` line and its preceding "structurally unreachable" comment
   (the constructor no longer exists — this is not exercising anything after deletion).
8. `CompileTest.lean`, `AdapterTest.lean`, `ContractTest.lean`: update the three stale comment
   references identified in §0 (each cites `numericModeNotAdmitted`/`NumericMode` as a "same
   pattern" precedent for something else) so they don't cite a deleted constructor — reword to the
   remaining precedent only (`CompileTest.lean`/`AdapterTest.lean` each still have their own
   *other* single-valued-vocabulary unreachable to point to independent of this one:
   `unsupportedDtype`/`dynamicShape` for `CompileTest.lean`, nothing else for `AdapterTest.lean` —
   if no independent precedent remains for a given comment, drop the "same pattern as" clause
   entirely rather than leave a dangling reference).

### Mutation checks

Not applicable in the usual sense (this task deletes, it doesn't add a guard to break/restore) —
the verification is that `lake build LeanNCD` and the full test suite are green with the field
gone, confirming no other production or test site depends on it beyond the exact list in §0.

### Gate

```bash
cd leanncd
lake build LeanNCD
lake build Eval.Plan.EvalPlanTest Eval.Plan.GraphCheckTest Eval.Plan.GraphDenseTest \
  Eval.Plan.KernelCheckTest Eval.Plan.ExecutableTest Eval.Plan.CompileTest \
  Eval.Plan.AdapterTest Eval.Plan.ContractTest
grep -rn "numericMode\|NumericMode\|reference64SumProduct" LeanNCD/ test/  # must return nothing
  # under LeanNCD/Eval/Plan and test/Eval/Plan except inside experiments/jax_bridge, which is
  # explicitly excluded from this grep's scope (or confirm it only matches that one file)
```

Independent task review. Can run fully in parallel with Tasks 1-3.

## Task 5: differential/corpus re-verification

### Outcome

Eight new hand-built differential fixtures (one per nonlin function) prove the compiled Dense path
agrees bit-for-bit with `evalScheduled` for real top-level nonlin programs — the first such
evidence, since no existing generator produces one. The scan corpus split is re-run and confirmed
**unchanged** (17/9/4/4), correcting the task brief's own assumption (§0).

### Files

- `test/Eval/Plan/DifferentialTest.lean`

### Implementation

1. Add eight `checkEntry`-style comparisons (or a small dedicated loop, matching this file's
   existing `checkEntry`/`envEq` helpers) for the end-to-end fixtures named in Task 3, each
   comparing `prepareEvalPlan` + `runPreparedDense` against `evalScheduled` on the identical
   program and input, asserting `envEq` and warnings equality exactly as `checkEntry` already does
   for `enumPrograms`.
2. Re-run `scanCorpusSplit` unchanged (no code edit expected) and confirm the pinned
   `total == 17 && accepted == 9 && nonlin == 4 && agg == 4` guard still passes — this is a
   **confirmation**, not a re-baseline. If it ever disagrees, that is a real Task 3 defect to
   report (per DifferentialTest.lean's own stop-condition precedent for this exact guard), not a
   number to update in this task.
3. No change to `test/Eval/Portfolio/ScatterNonlinRejectTest.lean` — confirmed out of scope in §0
   (tests scatter, an unconditional rejection unrelated to `checkNonlin`).

### Fixtures

The eight from Task 3's "end-to-end compiled examples" list, reused verbatim (same donor tensors,
same expected values) rather than re-derived — this task's own value is running them through the
*differential* comparison (`runPreparedDense` vs. `evalScheduled`), which Task 3's own tests do not
do (Task 3 only confirms the compiled plan itself produces the right tensor, not that it agrees
with the independent legacy evaluator on the identical source program).

### Mutation checks

- Temporarily break one new differential fixture's expected value (off by a small delta); confirm
  the new comparison loop fails loudly rather than silently passing via a `DenseTensor.approxEq`-
  style tolerance mismatch with the legacy evaluator's own convention — restore.
- Confirm `scanCorpusSplit`'s guard fails loudly (not silently re-baselines) if temporarily changed
  to expect e.g. `nonlin == 0`, then restore the real pinned values.

### Gate

```bash
cd leanncd
lake build Eval.Plan.DifferentialTest
```

Independent task review.

## Task 6: closure — doc corrections, discoverability, completion record, whole-branch review

Folds what was originally a standalone "Task 5: architecture doc corrections" into this task
(§8's revision record) — its own deliverable ("PlanStep now has .pointwise/.axiswise... reachable
from top-level source syntax") only becomes true once Task 3 has actually landed, so a separate,
independently-dispatched doc task drawn with no dependency on Tasks 1-3 risked describing a design
that could still change during Task 3's own review, and cost a dispatch for a deliverable with no
failure mode independent of this task's own completion record. Sequencing it here, last, fixes
both problems at once.

### Outcome

`papers/jax_evalplan_architecture.md` §7.6's thread 4 row, §2.2's closing sentence, **and §5.1's
`RawEvalPlan` field table + `checkPlan` admission sentence** (an additional stale passage found
this session, not in the original two-passage scope — see Implementation item 3) are corrected;
`LeanNCD.lean` imports the new file; `Eval/AGENTS.md`'s `Plan/` file table, entry-points list, and
`PlanCompileCause` triage row all mention the new `.nonlin` case; a completion record states
exactly what shipped, what was deliberately deferred and why — applying §2.2's PyTorch/JAX
distinction rather than lumping both under one "deferred" label — plus scan-block nonlin, masked
axiswise, the two deliberate legacy-narrowing deltas (§3), and the four unvalidated ULP bounds, and
the corrected corpus/differential numbers from Task 5. Two independent whole-branch reviewers have
signed off.

### Files

- `papers/jax_evalplan_architecture.md` (§7.6, §2.2, §5.1)
- `LeanNCD.lean` (add `import LeanNCD.Eval.Plan.Nonlin`, placed with the other Wave F direct
  imports per the existing convention noted in `Eval/AGENTS.md`'s `Plan/` subtree section)
- `LeanNCD/Eval/AGENTS.md` (the `Plan/` file table gains a `Nonlin.lean` row; the "Add a new
  nonlinearity" entry-point row gets a second line for the Plan-layer path, distinct from the
  existing legacy-`Nonlin.lean` entry; the file-count-16 note in the "Find It Fast" table becomes
  17; the `PlanCompileCause`-triage entry-point row — "Understand why a source scan was rejected,"
  which enumerates `.capability`/`.scan`/`.invalidPlan` — gains a fourth clause for `.nonlin =
  NonlinCompileError` from `resolveNonlinAxis`, pointing to `test/Eval/Plan/NonlinCompileTest.lean`
  for fixtures, matching the existing per-constructor pattern exactly)
- A completion record — follow this directory's own convention of appending to the relevant design
  doc rather than a new file; since this thread has no `papers/wave_*_proposal.md` of its own,
  append the record directly to this plan file's own closing section (matching how earlier
  standalone-thread plans in this directory, e.g. `2026-08-13-thread-5-jax-executable-kernels.md`,
  close themselves) rather than inventing a new doc

### Implementation

1. §7.6's thread 4 table row: change `Open — the only thread still open` to reflect Dense-only
   completion, and its "Why" cell to state: `PlanStep` now has `.pointwise`/`.axiswise` (thread 4),
   checked and executed by Dense, reachable from top-level source syntax, serving as the reference
   semantics a future JAX lowering must match; scan-block nonlinearity stays rejected (deliberate
   scope boundary, §2.2 above). Then, as two visibly distinct clauses, not one merged
   "JAX/PyTorch deferred" clause, using §2.2's exact PyTorch/JAX distinction: **PyTorch** —
   deferred with no scheduled thread, quoting thread 5's own sentence structure verbatim as the
   template. **JAX** — blocked solely by `EvalPlanCodegen.lean`'s pre-existing `PlanStep` breakage,
   with repairing that file and adding `.pointwise`/`.axiswise` lowering named as the natural next
   slice, not indefinitely deferred.
2. §2.2's sentence "Once Dense, JAX, and PyTorch gain checked nonlinear support, re-measure against
   real output..." — change to name Dense's real support as landed by this thread (the reference
   semantics JAX will eventually be diffed against), apply the same PyTorch/JAX distinction as
   item 1, and state that the four transcendental-call functions' ULP bounds specifically remain
   unvalidated even for Dense (no second backend to differential against yet) per this plan's §2.2.
3. **§5.1's `RawEvalPlan` load-bearing-content table row** ("Format version, tensor signatures,
   ordered input slots, ordered steps, numeric mode") and **the sentence "`checkPlan` currently
   admits the plan version and `reference64SumProduct` numeric mode..."** — found this session by
   grepping the whole doc for `NumericMode`/`numericMode`/`reference64SumProduct` (not assumed from
   the original two-passage scope). Both already describe a removed field (`version`, gone since
   Wave F F3) and would describe a second removed field (`numericMode`, gone since Task 4 of this
   plan) if left as-is — drop "Format version" and "numeric mode" from the table row, and drop "the
   plan version and `reference64SumProduct` numeric mode" from the admission sentence, leaving what
   `checkPlan` genuinely still admits generically (tensor signatures, slot bounds, graph order).
   Do not touch Appendix B/C/D's own `NumericMode`-parameterized dependent-type sketches (in the
   architecture doc's own "## 8. Appendices" section, not this plan's §8) — those are Stage B/C
   candidate material describing a different, non-adopted dependent type system, not the real
   `LeanNCD/Eval/Plan/Types.lean` type this task deletes, and are already understood repo-wide
   (thread 5's own precedent) to not track live code.
4. Do not touch any other section of the architecture doc (§4.3, §5.4, Appendix D) — those describe
   JAX/PyTorch executable architecture in the abstract and are unaffected by a Dense-only thread.
5. Add the `LeanNCD.lean` import.
6. Update `Eval/AGENTS.md`'s `Plan/` table row list, file count, and `PlanCompileCause` triage row
   (Files above).
7. Write the completion record: what shipped (two `PlanStep` cases, real top-level compilation, the
   `numericMode` deletion, the three doc corrections above), what was deliberately deferred and why
   (§2.2 of this plan, verbatim reasons — scan-block nonlin, masked axiswise, unvalidated
   transcendental ULP bounds, and the PyTorch/JAX distinction stated separately per §2.2, not
   merged into one "backends deferred" line), the two deliberate legacy-narrowing deltas from §3
   with their fixture names, and the real Task 5 numbers (scan corpus split confirmed unchanged;
   the eight new differential fixtures, named).
8. **Verify every claim in the completion record against the actual code/output before writing it**
   — per the skill's own rule 1, a completion record is exactly the kind of templated prose that
   must be checked, not asserted from design intent. In particular: do not write "no second
   local-operation representation was added" without diffing `Nonlin.lean` against `Kernel.lean`'s
   `AssignPlan` to confirm it, and do not write the Task 5 corpus numbers without pasting the real
   `lake build` output.

### Gate

```bash
cd leanncd
grep -n "thread 4" ../papers/jax_evalplan_architecture.md   # confirm the row reads as updated
grep -n "Once Dense, JAX, and PyTorch" ../papers/jax_evalplan_architecture.md  # must return nothing
grep -n "numericMode\|numeric mode" ../papers/jax_evalplan_architecture.md
  # confirm §5.1's table row and admission sentence no longer mention it (Appendix B/C/D's
  # NumericMode-parameterized candidate sketches are expected and out of scope, per item 3 above)
lake build LeanNCD
lake build   # full suite
```

**Two independent final whole-branch reviewers**, per the task brief's explicit instruction (this
touches a soundness-relevant closed sum) and this repo's own standing lesson (skill §4: the
whole-branch tier is where every prior slice's most valuable finding came from, never a per-task
diff). Do not compress this because Tasks 1-5 land clean — F3's and F4's own final reviews each
found something no per-task review caught.

## 6. Definition of done

- [ ] `LeanNCD/Eval/Plan/Nonlin.lean` exists with `RawPointwisePlan`/`RawAxiswisePlan`,
      `NonlinPlanError`, a shared `checkNonlinIO` helper, `checkPointwise`/`checkAxiswise` built on
      it, and `runDensePointwise`/`runDenseAxiswise`.
- [ ] `LeanNCD/Eval/Nonlin.lean` has a new `AxiswiseFn.apply`, symmetric with `PointwiseFn.apply`;
      `applyNonlin` delegates to both; `test/Eval/NonlinTest.lean` is unchanged and still green
      (§0a — confirms the refactor is behavior-preserving, not just independently verified).
- [ ] `PlanStep` has four constructors; `checkPlan`/`runDensePlan`/`sourceSlots`/`destinationSlots`/
      `CheckedPlanStepEvidence` all handle all four.
- [ ] `checkLHSSlot` admits `.freeNorm`; the top-level `checkNonlin` call site admits
      `.pointwise`/`.axiswise`; the scan-block call site is unchanged (still rejects both).
- [ ] `NonlinCompileError`/`resolveNonlinAxis` exist and reject masked axiswise, unmarked axiswise,
      marker-without-axiswise, **and multiple markers**, each with the exact named constructor —
      including the two deliberate legacy-narrowing fixtures (§3) proving `evalScheduled` accepts
      what `prepareEvalPlan` intentionally rejects.
- [ ] `prepareEvalPlan` compiles a nonlin-bearing plain statement into the two-step chain from §3;
      `.identity` statements are byte-for-byte unchanged.
- [ ] `numericMode`/`NumericMode`/`numericModeNotAdmitted` are gone from every site in §0's list;
      `experiments/jax_bridge/EvalPlanCodegen.lean` is untouched.
- [ ] `NonlinCheckTest`/`NonlinDenseTest`/`NonlinCompileTest` are all present in `lakefile.toml`'s
      `Tests` `globs` list, confirmed by `lake build Tests` actually exercising them, not merely
      `lake build <module-name>` standalone.
- [ ] The two `sourceSlot == destinationSlot` regression fixtures (Task 2) each prove their own,
      distinct, verified expected error (`invalidForwardRead` for the never-produced case,
      `duplicateDestination` for the already-produced case) — not the same fixture asserting the
      wrong one of the two.
- [ ] Architecture doc §7.6 thread 4 row, §2.2's closing sentence, **and §5.1's `RawEvalPlan` field
      table + admission sentence** corrected, giving PyTorch and JAX distinct framing (§2.2's
      ruling) rather than one merged deferral clause.
- [ ] Eight new end-to-end differential fixtures pass; the scan corpus split (17/9/4/4) is
      confirmed unchanged by a real re-run, not assumed.
- [ ] `LeanNCD.lean`/`Eval/AGENTS.md` updated for discoverability, **including the
      `PlanCompileCause` triage row gaining its `.nonlin` clause**.
- [ ] Completion record written and verified against real code/output, not asserted.
- [ ] `lake build` (full suite) green.
- [ ] Two independent reviewers signed off on Task 2 (closed-sum wiring) and two independent
      reviewers signed off on the final whole-branch review (Task 6).

## 7. Risks and stop conditions

### 7.1 Expected high-effort areas

- Task 3's two-step chaining touches `prepareEvalPlan`'s Step D, the one existing production
  compiler path — any regression there silently breaks every Wave C/F fixture, not just new nonlin
  ones. Task 3's own gate must re-run the FULL `Eval.Plan.*` test suite, not just its own new file.
- Task 2's exhaustive-match wiring is exactly the shape of defect F3/F4 review found expensive to
  catch late (a diff showing only *added* arms cannot show whether an *existing* arm's behavior
  silently changed) — hence the two-independent-reviewer requirement on that task specifically.

### 7.2 Stop rather than broaden scope

- If implementing `resolveNonlinAxis`/the two-step chain reveals that `.freeNorm`'s relaxation has
  a THIRD consumer beyond `checkLHSSlot`/`freeUidOrFail` this plan didn't find (e.g. a scatter-path
  or `Structural.lean` check that also assumes `.freeNorm` is globally unreachable) — stop and
  report; do not silently widen this plan's Compile.lean edits to cover it without re-scoping.
- If Task 5's differential fixtures disagree with `evalScheduled` for any function — this is a
  genuine Task 3 compiler defect (per §0's scan-corpus stop-condition precedent), not a fixture to
  adjust. Stop and report to the plan owner rather than "fixing" the fixture's expected value.
- Do not attempt to relax the mask-rejection scope boundary (§2.2) mid-implementation even if it
  looks small once `resolveNonlinAxis` exists — it requires new UID-free predicate IR design with
  no precedent in this codebase, which is out of this plan's sizing entirely.

## 8. Plan-authoring verification record

- Every Lean code block in this plan (§3's `NonlinCompileError`/`resolveNonlinAxis`, the raw types
  and manual `BEq` instances, `checkPointwise`/`checkAxiswise`/`runDensePointwise`/
  `runDenseAxiswise`, and a 4-constructor `PlanStep`-shaped sum built from the **real**
  `RawScanPlan`/`AssignPlan`) was compiled via `check-snippet.sh` against the real repo this
  session (four separate snippet files, all green — one harmless unused-variable lint warning in
  an illustrative, non-shipped snippet).
- §0a's follow-up extensibility/code-sharing vetting pass added two more verified snippets: the new
  `AxiswiseFn.apply` plus refactored `applyNonlin`, checked both for compilation and for
  **behavior equivalence** to the real (pre-refactor) `applyNonlin` via five `#guard`s comparing
  `.data` output on identity/pointwise/all-three-axiswise cases (all equal, first pass after fixing
  `DenseTensor.shape`'s real type being `List Nat` not `Array Nat`); and the shared `checkNonlinIO`
  helper plus `checkPointwise`/`checkAxiswise` built on it, checked with five `#guard`s covering a
  passing case, `slotOutOfRange`, `sourceShapeMismatch`, and a passing/failing `axisPositionOutOfRange`
  pair through `checkAxiswise` specifically (first pass caught one authoring error — `shape :=
  #[2]` has `.size == 1`, not `2`, corrected before the snippet was accepted). Six snippets total,
  all green in their final form.
- Every prose claim of the "X reuses Y" / "no second Z" shape was checked against real code before
  being written: `PointwiseFn.apply`'s existing dispatch (confirmed identical to what
  `runDensePointwise` needs), `checkPlan`'s exact three-match-block structure and its `.scan`
  generic-path precedent (confirmed by reading `EvalPlan.lean` directly, not summarized from
  memory), `checkStmt`'s scatter-rejection ordering relative to `checkNonlin` (confirmed
  `ScatterNonlinRejectTest.lean` needs no change), and the scan corpus split's real composition
  (confirmed `template2`'s nonlin sits inside the recurrence block, correcting the task brief's own
  framing).
- Every file path this plan names was verified with `ls`/`grep`/`Read` this session, including
  finding `papers/jax_evalplan_architecture.md` at the pyncd repo root (not under `leanncd/`,
  where an initial search for it failed) and confirming `.claude/skills/slice-plan/` lives at the
  pyncd repo root too, not inside `leanncd/`.
- No `File.lean:NNN` line numbers appear in any task's Implementation/Files/Gate text above, or in
  the completion-record instructions Task 6 is handed — every locator is by function/constructor
  name.
- `experiments/jax_bridge/EvalPlanCodegen.lean`'s pre-existing breakage was confirmed by directly
  running `lake build JaxExperiment` this session, not assumed from the task brief's description —
  the real failure output matches the description (stale `.plan` field access, non-exhaustive
  `PlanCompileCause.scan` match, removed `RawEvalPlan.version`, an `AssignPlan`/`PlanStep`
  mismatch), independently confirming ruling 4 rather than merely repeating it.

### 8a. External review response (2026-08-20, second follow-up pass)

An external review (`papers/2026-08-20-thread-4-nonlinearity-plan-review.md`, Copilot, against
commit `514e2ba`) raised 10 numbered concerns. Each was independently re-verified against the real
code or the plan's own exact text — not accepted or dismissed on the reviewer's word — before any
revision. **8 of 10 confirmed real and fixed**, in this pass:

1. Lakefile `globs` gap — confirmed by reading `lakefile.toml` directly (`Tests`' `globs` is
   explicit, `defaultTargets = ["LeanNCD", "Tests"]`). Fixed: Tasks 1-3 each add their own new
   module to `globs` as it lands, with a gate check confirming it.
2. `dtypeMismatch` classified as vacuous but instructed to be mutation-tested regardless, and the
   fixture/mutation count (~6) undercounted the real list (~10-11). Confirmed by recounting the
   plan's own fixture list and re-deriving `dtypeMismatch`'s reachability from `checkNonlinIO`'s
   guard order. Fixed in both the risk table and Task 1's Fixtures/Mutation Checks.
3. The self-aliasing fixture's expected error — confirmed wrong by reading `checkPlan`'s real loop
   order (destination-check before source-check, per step): the original fixture chains an
   `.assign` producing slot 1 then reuses it, which hits `duplicateDestination` first, never
   reaching the `invalidForwardRead` path it claimed to prove. Fixed: split into two fixtures, one
   per real rejection path (Task 2).
4. `resolveNonlinAxis` narrows legacy semantics undocumented — confirmed against the real
   `resolveNonlin`/`normAxisUidOf` (identity/pointwise never inspect `slots`; `findSome?` silently
   keeps only the first marker). Fixed: documented as two deliberate tightenings in §3, with two
   new differential fixtures (Task 3) proving `evalScheduled` accepts what `prepareEvalPlan`
   intentionally rejects.
5. Mask-rejection mechanism self-contradictory — confirmed by reading `checkNonlin`'s and
   `maskOrPredicate`'s real current bodies: `maskOrPredicate` fires today only from
   `Factor.iverson`, never from anything touching `Nonlin`'s own mask field, so the plan's claim
   that it gets "reused verbatim" for masked axiswise was simply false. Fixed: removed that claim,
   clarified that `NonlinCompileError.maskedAxiswiseNotSupported` (compile tier) is the sole real
   mechanism, consistent with `resolveNonlinAxis` already owning this class of structural check.
6. Task 3's gate ran two named files while its own risk section demanded the full `Eval.Plan.*`
   suite — confirmed as a literal, direct self-contradiction in the plan's own prior text. Fixed:
   gate now runs `lake build Tests`.
7. The dependency diagram drew Task 1/Task 2 as parallel branches despite genuine dependency, and
   Task 5 (doc corrections) was drawn independent of Tasks 1-3 despite asserting claims that are
   only true once Task 3 lands. Confirmed by re-reading the diagram against the prose beneath it.
   Fixed: redrew the diagram as a real chain, and folded the doc-corrections task into what is now
   Task 6 (closure) — both fixing the sequencing problem and cutting a low-value standalone
   dispatch, resulting in 6 tasks instead of 7.
8. `Eval/AGENTS.md`'s `PlanCompileCause` triage row (enumerating `.capability`/`.scan`/
   `.invalidPlan`) would go stale without a `.nonlin` clause — confirmed by reading the real row.
   Fixed: added to Task 6's Implementation/Files.
9. Three drafting bugs — confirmed by re-reading the exact cited text: Task 2's error-wrapping
   paragraph really did state `.assign (.nodeError ...)` then reverse itself to `.nonlin` in the
   same item (fixed, kept only the correct answer); `shape := #[2]` really was described as rank 2
   with positions 0-1 when it's rank 1 (fixed); the axiswise fixture's `#[1,3,2,2]`-shaped source
   really did conflate flattened data with shape (fixed, `#[2,2]` is the shape).

**1 confirmed only partially, main recommendation not adopted**: the `NumericMode` deletion itself
was NOT reversed — most of the reviewer's cited evidence (`NumericMode`-parameterized dependent
types) lives in Appendix B/C/D, explicitly non-canonical Stage B/C candidate material built on
types that don't exist in the real codebase (the same conclusion thread 5's own research reached
about that appendix), and reopening ruling 3 would re-litigate a decision already made and approved
this session, for reasons (the numeric contract is fully determined by which `PlanStep` constructor
a step is, so a redundant plan-level tag adds no information) that still hold. Two real
sub-findings inside the same point were confirmed and fixed
independently of that disagreement: §5.1's `RawEvalPlan` table row and admission sentence go stale
(now Task 6 item 3, found by grepping the *entire* doc for `NumericMode`/`numericMode`/
`reference64SumProduct`, not just the two passages originally in scope); and the "ULP bounds
recorded as named Lean constants" claim had no task actually producing one (corrected in §2.2 to
state honestly that none is created, rather than adding an unconsumed placeholder constant).

**1 explicitly not adopted**: moving `PointwiseFn`/`AxiswiseFn`'s `BEq` onto their `deriving`
clause in `DSL/Ast.lean`, rather than the plan's local orphan-instance approach — a reasonable
alternative, but one that would touch a file this thread's surgical-changes discipline deliberately
leaves alone, for a theoretical future-conflict risk this codebase already tolerates identically
for `AggOp`/`BoolExpr` today. Left as-is; flagged rather than silently overridden either way.

## Completion record

Tasks 1-5 completed 2026-08-20/21 on the `leanncd-thread4-nonlinearity` worktree, commits `98daf31`
(Task 1) through `93f706d` (Task 5); this section and its surrounding doc/discoverability work are
Task 6's own contribution, landing on top of that range. Task 1 took one fix round (`7bcef52`): drop
a `BEq` deriving that had crept onto `CheckedPointwisePlan`/`CheckedAxiswisePlan` beyond what the
brief specified, a fixture-naming typo, and a misleading "mutation checks" section rewritten as an
honest note (the Row-N fixtures already prove each guard load-bearing; nothing was actually
toggled-and-restored in the shipped file). Task 2 took one fix round with **two independent
reviewers** (`4a23de6`, per the DoD's closed-sum requirement) — Reviewer A approved with only Minor
findings deferred to whole-branch triage; Reviewer B found the core wiring correct but flagged two
Important findings, both fixed: stale doc comments across `EvalPlan.lean` that still described
`PlanStep`/`CheckedPlanStepEvidence`/`PlanStepError` as `.assign`/`.scan`-only, and a missing
regression fixture for `PlanStepError.nonlin`'s own throw path (added to `GraphCheckTest.lean`,
pinning that a `checkPointwise`/`checkAxiswise` failure surfaces as `.nonlin stepIndex cause`, not
mis-wrapped through `.assign`). Task 3 took one doc-accuracy fix round (`833c887`, correcting its own
characterization of the `Lowering.lean` fix below). Task 4 and Task 5 landed clean, no fix round.

### What shipped

Two new `PlanStep` constructors, `.pointwise`/`.axiswise` (`RawStep.lean`), each carrying a
`RawPointwisePlan`/`RawAxiswisePlan` (`Eval/Plan/Nonlin.lean`, new) — single-source/single-destination
steps with no term/factor/reduction structure at all, confirmed by direct comparison against
`Kernel.lean`'s `AssignPlan` (which has `terms : Array TermPlan`, each with `factors : Array
ReadPlan`): this is not a second local-operation representation, it is structurally simpler than the
one that already exists. A shared geometry-check helper, `checkNonlinIO`, covers the seven checks
common to both step kinds; `checkPointwise`/`checkAxiswise` build on it (the latter adding the
`axisPos` range check); `runDensePointwise`/`runDenseAxiswise` execute a checked step by delegating
entirely to `Eval/Nonlin.lean`'s `PointwiseFn.apply`/new `AxiswiseFn.apply` — no new math, and
`test/Eval/NonlinTest.lean` stayed green with zero edits, confirming the `applyNonlin` refactor
behind `AxiswiseFn.apply` is behavior-preserving. All four exhaustive matches over the closed
`PlanStep`/`CheckedPlanStepEvidence` sums (`checkPlan`, `runDensePlan`,
`PlanStep.sourceSlots`/`destinationSlots`) now handle all four constructors.

Real top-level source compilation: `checkLHSSlot` admits `.freeNorm` (relaxed, not removed);
`checkNonlin`'s top-level call site (inside `checkStmt`) admits `.pointwise`/`.axiswise`; the
scan-block call site (`checkScanBlockStmt`) is unchanged and still rejects both, confirmed by the
`ScanContractTest.lean`/`CompileTest.lean` fixtures Task 3 re-ran unedited. `resolveNonlinAxis`
(`Compile.lean`) and a new `NonlinCompileError` family (`Error.lean`) own the freeNorm-marker/`Nonlin`
-kind consistency check `checkNonlin` deliberately does not re-litigate. `prepareEvalPlan`'s `.plain`
branch now compiles a nonlin-bearing statement into the two-step chain from §3 (verified by reading
`Compile.lean` directly): `.identity` allocates one slot and pushes one `.assign`, byte-for-byte as
before Task 3; `.pointwise`/`.axiswise` allocate an internal slot for the unchanged `AssignPlan` plus
a published slot for the new step, in that order. For real source text, this two-step chain composes
with `splitNonlins`' own pre-existing split (a linear step plus a nonlin step, built before
`prepareEvalPlan` ever runs) into three compiled steps total, not two: the linear step's real
contraction, then a redundant, value-preserving identity-copy `.assign` (this task's own internal
slot, reading the nonlin step's trivial single-read body), then the actual `.pointwise`/`.axiswise`
step — pinned directly by `NonlinCompileTest.lean` §3's `reluProgPrepared`/`softmaxProgPrepared`
fixtures (`steps.size == 3`) and documented there. A real, load-bearing bug outside the brief's own
file list was found and fixed during Task 3: `DSL/Pipeline/Lowering.lean`'s `splitStmt` was leaving
the original `.freeNorm` marker on the split-off *linear* half of a nonlin statement, which
`resolveNonlinAxis` then correctly rejected as `unmarkedReductionAxis` — making every real axiswise
program (softmax/normalize/l2normalize) uncompilable through the exact machinery meant to admit them.
Fixed by degrading `.freeNorm → .free` on the linear step's own slots only; documented in
`LeanNCD/DSL/AGENTS.md`'s Pitfalls section (including the phase-order caveat that makes this fix
correct today but not permanent-by-construction), reviewed and confirmed safe by two independent
reviewers.

`RawEvalPlan.numericMode`, `NumericMode`, and `PlanError.numericModeNotAdmitted` are deleted from
every production and test site Task 4 enumerated; `experiments/jax_bridge/EvalPlanCodegen.lean` is
untouched (confirmed still broken independent of this thread — `lake build JaxExperiment` fails today
exactly as before, with a stale `CheckedPlanStepEvidence.plan` field access, a non-exhaustive
`PlanCompileCause.scan` match, `RawEvalPlan.version`/`RawEvalPlan.numericMode` field-not-found errors,
and an `AssignPlan`/`PlanStep` literal mismatch — re-run directly during this task, not assumed).

Eight new hand-built differential fixtures (`test/Eval/Plan/DifferentialTest.lean`, one per nonlin
function — `relu`, `sigmoid`, `tanh`, `gelu`, `leakyrelu`, `normalize`, `softmax`, `l2normalize`)
prove `prepareEvalPlan` + `runPreparedDense` agrees bit-for-bit (`envEq`, exact) with the independent
legacy `evalScheduled` on real top-level nonlin programs — reusing Task 3's own donor
programs/tensors verbatim. The scan corpus split was re-run, not assumed: a real `lake build
Eval.Plan.DifferentialTest` today (2026-08-21) still reports `total=17 accepted=9 unsupportedNonlin=4
unsupportedAgg=4`, confirming the pinned split is genuinely unchanged by this thread, per §0's
correction of the task brief's original assumption.

The two deliberate legacy-narrowing deltas from §3 are each pinned by their own fixture in
`test/Eval/Plan/NonlinCompileTest.lean`, verified present: `spuriousMarkerPointwise` (a `.freeNorm`
marker on an otherwise-`.pointwise` statement) shows `evalScheduled` still executes it while
`prepareEvalPlan` rejects with `NonlinCompileError.unmarkedReductionAxis "H" 0`; `doubleMarkerAxiswise`
(two `.freeNorm` markers on one axiswise statement) shows `evalScheduled` silently reduces over the
first marker while `prepareEvalPlan` rejects with `NonlinCompileError.multipleMarkedReductionAxes "Y"
0 1`.

This task (6) additionally corrected `papers/jax_evalplan_architecture.md` in the three places found
stale: §7.6's thread 4 row (now **Done — Dense-only**, with PyTorch and JAX given the distinct
framing §2.2 rules for them — PyTorch deferred with no scheduled thread, mirroring thread 5's own
phrasing verbatim; JAX blocked solely by `EvalPlanCodegen.lean`'s pre-existing breakage and named as
the natural next slice); §2.2's closing paragraph (removed the now-false "checked pipeline accepts
none of these steps" and "Once Dense, JAX, and PyTorch gain..." framing, stated that Dense's real
support is landed while the four transcendental functions' ULP bounds remain unvalidated — no second
backend exists to differential against yet — leaving thread 1's own status, "Specified, not
validated," unchanged); and §5.1's `RawEvalPlan` field-table row and `checkPlan` admission sentence
(both dropped "Format version"/"the plan version" and "numeric mode", the second stale field found
this session by grepping the whole doc for `NumericMode`/`numericMode`/`reference64SumProduct`).
That identifier-only grep pattern missed four further main-body passages phrased as the lowercase
prose "numeric mode" rather than the camelCase identifier, plus one Appendix A sentence this task's
own appendix exemption skipped even though it asserts a real (non-sketch) claim; a follow-up
final-review pass (this dispatch) found and corrected all five. Added
`import LeanNCD.Eval.Plan.Nonlin` to `LeanNCD.lean` (already transitively reachable via `RawStep.lean`
's own import, but added directly per the file's documented convention of direct top-level imports for
each Wave-F-era `Plan/` addition). Updated `LeanNCD/Eval/AGENTS.md`: the `Plan/` file table gained a
`Nonlin.lean` row (placed immediately before `RawStep.lean`, which depends on it) and the "Find It
Fast" file count went 16 → 17; the "Add a new nonlinearity" entry-point row now names both the legacy
evaluator path and the distinct Plan-layer path (constructor in `DSL/Ast.lean`, one match arm in
`PointwiseFn.apply`/`AxiswiseFn.apply`, a new fixture — nothing in `Plan/Nonlin.lean` itself changes,
since its checker is fully function-agnostic); the `PlanCompileCause` triage row gained its `.nonlin`
clause, pointing at `test/Eval/Plan/NonlinCompileTest.lean` for fixtures distinct from the
`.capability`/`.scan`/`.invalidPlan` trio's own `ScanCompileTest.lean`.

### What was deliberately deferred, and why (§2.2)

- **Scan-block nonlinearity** stays rejected — `checkScanBlockStmt`'s `checkNonlin` call site is
  unchanged, confirmed unedited by Task 3's own gate re-running `ScanContractTest.lean`/
  `CompileTest.lean`'s scan-block-rejection fixtures. This is a deliberate scope boundary
  (`Stmt.recurMorphism` structurally forces `.identity` independent of this thread), not a gap.
- **Masked axiswise nonlinearities** (`Nonlin.axiswise fn (some _)`) are rejected at the compile
  tier, by `resolveNonlinAxis` throwing `NonlinCompileError.maskedAxiswiseNotSupported`, before a
  `RawAxiswisePlan` can even exist — `RawAxiswisePlan` carries no mask field at all, not a
  reserved-but-unused one, because Plan-layer `TensorSignature` is UID-free by design and there is no
  precedent in this codebase for a UID-free, position-based compiled predicate IR that could support
  one.
- **PyTorch interpreter support** is deferred with no scheduled thread — no client has asked for it,
  mirroring thread 5's own PyTorch deferral for the executable-lowering phase.
- **JAX interpreter support** is out of scope for this thread specifically because
  `experiments/jax_bridge/EvalPlanCodegen.lean` is already broken against Wave F's
  `PlanStep`/`CheckedPlanStepEvidence` generalization — confirmed again during this task by directly
  running `lake build JaxExperiment` (failure output pasted above) — not because it is a low
  priority: the checked types this thread introduces (`RawPointwisePlan`/`RawAxiswisePlan`/
  `CheckedPointwisePlan`/`CheckedAxiswisePlan`) are already backend-neutral, and repairing
  `EvalPlanCodegen.lean` then adding `.pointwise`/`.axiswise` JAX lowering on top of them is named as
  the natural next slice, not indefinitely deferred like PyTorch.
- **The four transcendental-call nonlin functions' ULP bounds** (`sigmoid`/`tanh`/`gelu`/`softmax`)
  remain "specified, not validated" — architecture doc thread 1's status is unchanged by this thread.
  `relu`/`leakyrelu`/`normalize`/`l2normalize`'s 0-ULP bounds ARE pinned, but by bit-exact fixtures
  (Tasks 1/3), not by a named Lean constant — no second backend exists yet to differential the
  nonzero bounds against, and an unconsumed placeholder constant would be pure decoration.

### Gate, at this task's close

```text
$ lake build LeanNCD
Build completed successfully (8542 jobs).
$ lake build
Build completed successfully (8656 jobs).
```

Both re-run after this task's own edits (the `LeanNCD.lean` import plus the doc/AGENTS.md changes
above), on top of Tasks 1-5's own green state. `grep -n "Once Dense, JAX, and PyTorch"
papers/jax_evalplan_architecture.md` returns nothing, as the Gate requires.

### Outstanding

The final whole-branch review (two independent reviewers, per this task's own brief and the DoD's
last item) has **not** run yet as of this writing — it is dispatched separately, after this task's
own implementation passes its own task-scoped review, and is not part of what this completion record
attests to. Nothing else from Tasks 1-5's own scope is left open beyond what "What was deliberately
deferred, and why" states above.

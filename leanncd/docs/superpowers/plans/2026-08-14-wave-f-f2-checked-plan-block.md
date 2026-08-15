# Wave F, F2: Checked Plan-Block Vertical Slice

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add `RawPlanBlock`, its private-constructor checked wrapper `CheckedPlanBlock`,
`checkPlanBlock`, and `runDenseBlock` — the local, acyclic, context-parameterized dataflow graph
that a future scan's base and step blocks will be built from (`papers/wave_f_scanplan_proposal.md`
§6.2). This is F2 in the Wave F sequence (F0 and F1 already landed; see Status below). **Do not**
add a scan constructor to `RawEvalPlan`, touch `RawEvalPlan`/`checkPlan`/`runDensePlan`, or start
F3/F4 — those are separate slices with their own plans, written only after this one lands
(`papers/wave_f_scanplan_proposal.md` §13's own instruction, and this repo's standing "one plan per
slice" rule).

**Status.** F0 (executable scan contract, 2026-08-08) and F1 (contextual local kernel, 2026-08-08)
are landed — `AssignPlan`/`TermPlan` already carry `contextShape`/`contextPos`, and
`runDenseAssignAt` already executes a checked assignment at an arbitrary runtime context
coordinate, verified by re-reading `LeanNCD/Eval/Plan/Kernel.lean`, `Check.lean`, and `Dense.lean`
directly (not assumed from the proposal doc's prose) before drafting this plan. F2-F4 are open;
`papers/jax_evalplan_architecture.md` §7.6 (thread 3) names "F2-F4: checked block and scan layers"
as the next recommended work, independent of threads 1/2/4/5/6.

**Architecture — reuse mandate.** A block's local graph of assignments is structurally the *same*
kind of graph `RawEvalPlan`/`CheckedEvalPlan` already validate and run — an array of `AssignPlan`s,
positional slots, availability/production-order wiring — just scoped to the block's own
`tensorSigs` instead of the outer plan's, and carrying a non-empty declared `contextShape` instead
of the empty one `checkPlan` requires at the top level. F2 must not fork a second implementation of
that graph discipline:

- `checkPlanBlock` calls the *existing* `checkAssign` for every block-local assignment — unchanged,
  no new local-kernel logic. F1 generalized `AssignPlan`/`checkAssign`/`runDenseAssignAt` to carry
  an explicit context specifically so a block could reuse them without a second near-copy
  (`papers/wave_f_scanplan_proposal.md` §6.1); F2 is where that investment gets spent.
- `checkPlanBlock`'s slot-availability/production-order loop is the same loop shape as `checkPlan`'s
  (`Check.lean` lines 112-159): plain `Array Bool`/`Array (Option Nat)` availability tracking, one
  pass over ordered steps. It is parameterized differently (block's own `tensorSigs`/`inputs`
  instead of the raw plan's `tensorSigs`/`inputSlots`) but the wiring rules — a source must already
  be available, a destination cannot overwrite an input or duplicate an earlier producer, every
  non-input slot must be produced exactly once — are identical, so `BlockError.wiring` wraps
  `PlanError` and reuses its constructors verbatim (`slotOutOfRange`, `duplicateInputSlot`,
  `inputSlotsNotOrdered`, `inputSlotOverwritten`, `duplicateDestination`, `missingProduction`,
  `invalidForwardRead`, `nodeError`) rather than redefining eight lookalike constructors on a new
  type. Only the two obligations a block has and the outer plan does not — output-slot uniqueness,
  and requiring a *specific declared* context instead of the empty one — get new `BlockError`
  constructors (`duplicateOutputSlot`, `blockContextMismatch`).
- `runDenseBlock` calls the *existing* `runDenseAssignAt` per node, exactly as `runDensePlan` does
  for the outer graph (`Dense.lean` lines 179-181) — same store-threading loop, scoped locally.
- `Coordinates.lean`'s shared row-major primitives are untouched and continue to back both graphs
  through the `AssignPlan`s each contains — no new coordinate math.

The result: `checkPlanBlock`/`runDenseBlock` are a parameterized *reuse* of `checkPlan`/`runDensePlan`
plus two new checks and two new error cases, not a parallel scan-shaped code path. F3 (scans) will
in turn build on `CheckedPlanBlock`, not on a second block-shaped thing.

**Tech Stack:** Lean 4, LeanNCD type discipline (`private mk ::` for checked wrappers, closed
inductive error families, no `unsupported : String` escape hatches).

**Spec:** `papers/wave_f_scanplan_proposal.md` §6.2 (plan blocks), §7.2 (block checks — this plan's
`checkPlanBlock` implements exactly this bullet list), §13's F2 entry (deliverables and gate).
`papers/jax_evalplan_architecture.md` §2.3 ("blocks... explain how assignments participate in
larger stateful graphs") and Appendix C's `CheckedLocalKernelInterface`/block sketch (non-copy-ready
— see the naming note below). §7.6 thread 3.

**Naming note (expected drift, not a gap).** Appendix C's sketch is explicitly a "non-copy-ready"
dependent-type design exploration for a *later*, not-yet-adopted Stage C, parameterized over an
abstract `CheckedLocalKernelInterface`. This plan's `RawPlanBlock`/`CheckedPlanBlock`/`BlockError`
are concrete, flat (non-dependent) types instantiated directly over the *current* Wave C/Stage A
`AssignPlan`/`CheckedAssignPlan` — the same divergence pattern `Executable.lean`'s header comment
already documents for Appendix D vs. its own `JaxKernelCandidate` et al. Do not copy Appendix C's
Lean syntax into production code.

## Global Constraints

- **Additive only.** No existing file (`Types.lean`, `Kernel.lean`, `Graph.lean`, `Error.lean`,
  `Check.lean`, `Dense.lean`, `Coordinates.lean`, `Compile.lean`, `Adapter.lean`,
  `Signature.lean`, `Prepared.lean`, `Executable.lean`) changes in this slice. Every new type and
  function lives in a new `Block.lean` (+ its test file). This is a real, checked property of the
  design, not just a target: nothing here requires touching `checkAssign`, `checkPlan`,
  `runDenseAssignAt`, or `runDensePlan`.
- **No scan constructor yet.** `RawEvalPlan.steps` stays `Array AssignPlan`. `PlanStep`, `RawScanPlan`,
  and the four-phase scan worker are F3. A block that is never referenced by anything outside its
  own test file is the correct end state for F2 — F3 is what gives it a caller.
- **Reuse `PlanError`, don't re-derive it.** Every `BlockError` case that means the same thing a
  `PlanError` case already means (see Architecture above) must be `BlockError.wiring (cause :
  PlanError)`, not a new constructor. If implementation reveals a wiring failure mode with no
  `PlanError` analogue, that is a signal to stop and reconsider, not to add a lookalike constructor
  — flag it in the task's own review rather than improvising past it.
- **Private constructor pattern.** `CheckedPlanBlock` follows `CheckedAssignPlan`/`CheckedEvalPlan`'s
  `private mk ::` discipline exactly (`structure ... where private mk ::`, not a bare `where
  private` — the latter compiles but does not privatize, per this repo's own recorded Wave C
  mistake).
- **Fixture values are observed, not hand-derived.** The context-indexed fixture below reuses the
  exact assignment `test/Eval/Plan/KernelDenseTest.lean`'s `ctxPlan` already exercises and whose
  values (`ctx=0 -> [1,2,3]`, `ctx=1 -> [4,5,6]`) that file's own comment records as independently
  verified — this plan does not re-derive new numbers by hand, it reuses an already-observed result
  under a new block wrapper.
- **Every Lean block in this plan has already been compiled** against the real `leanncd` environment
  via `.claude/skills/slice-plan/check-snippet.sh` before being written here, including the two
  mutation fixtures and the arity-mismatch fixture (their `run_cmd`/`#guard` bodies execute at
  elaboration time, so a clean compile of this plan's snippets is itself the mutation-sensitivity
  evidence the `slice-plan` skill requires — not a separate claim to re-verify from scratch, but
  worth re-running once more after this plan is transcribed into real files, per that skill's
  "re-verify after assembly" rule, since transcription is itself an edit).

---

## File Structure

**Create:**
- `leanncd/LeanNCD/Eval/Plan/Block.lean` — `RawPlanBlock`, `BlockError`, `CheckedPlanBlock`,
  `checkPlanBlock`, `runDenseBlock`
- `leanncd/test/Eval/Plan/BlockTest.lean` — construction, checking, execution, and mutation fixtures

**Modify:**
- `leanncd/lakefile.toml` — add `"Eval.Plan.BlockTest"` to the `Tests` library's `globs`
- `leanncd/LeanNCD.lean` — add `import LeanNCD.Eval.Plan.Block` (discoverability: `Block.lean` is
  core Wave F production code, not an experiment, so — unlike `Executable.lean` — it belongs on the
  default `import LeanNCD` graph)
- `leanncd/LeanNCD/Eval/AGENTS.md` — add `Block.lean` to the `Plan/` subtree's file table and file
  count
- `papers/wave_f_scanplan_proposal.md` — append an "F2 completion record" under §13, matching the
  F0/F1 completion-record convention already there

---

## Task 1: `RawPlanBlock`, `BlockError`, `checkPlanBlock`

**Files:**
- Create: `leanncd/LeanNCD/Eval/Plan/Block.lean`
- Create: `leanncd/test/Eval/Plan/BlockTest.lean`
- Modify: `leanncd/lakefile.toml` (register the test module so `lake build` runs it)

**Interfaces:**
- Consumes: `AssignPlan`, `TensorSignature`, `TensorSlot`, `checkAssign`, `CheckedAssignPlan`,
  `PlanError` (all from `Kernel.lean`/`Check.lean`, unchanged)
- Produces:
  - `RawPlanBlock` (`contextShape`, `tensorSigs`, `inputs`, `assignments`, `outputs`)
  - `BlockError` (`wiring : PlanError → BlockError`, `duplicateOutputSlot`, `blockContextMismatch`)
  - `CheckedPlanBlock` (private constructor)
  - `checkPlanBlock : RawPlanBlock → Except BlockError CheckedPlanBlock`

This plan's snippets are transcribed verbatim from a spike file already compiled end-to-end via
`check-snippet.sh` against the real `leanncd` environment (COMPILES, including the two mutation
`run_cmd` blocks actually hitting their `.error` branch at elaboration time). Re-run
`check-snippet.sh` once more on the transcribed files before committing, per the Global Constraints
note above.

- [ ] **Step 1: Implement `RawPlanBlock`, `BlockError`, and `checkPlanBlock`**

```lean
-- leanncd/LeanNCD/Eval/Plan/Block.lean
import LeanNCD.Eval.Plan.Dense

/-!
# Wave F checked plan-block vertical slice (F2)

A local, acyclic, context-parameterized dataflow graph — the base block or the step block of a
future scan (`papers/wave_f_scanplan_proposal.md` §6.2). Local assignments are plain `AssignPlan`s
sharing this block's `contextShape` — the same node type the outer graph uses (`Graph.lean`'s
`RawEvalPlan.steps`), so F2 introduces no second local-operation representation.
`checkPlanBlock` is the local-graph analogue of `checkPlan` (proposal §7.2), not a special
evaluator convention: it reuses `checkAssign` per node and the identical availability/production-
order wiring loop `checkPlan` already applies to the outer graph. `runDenseBlock` is the
corresponding analogue of `runDensePlan`, reusing `runDenseAssignAt` per node. No scan constructor
exists yet — `RawEvalPlan` is untouched by this file.
-/

namespace LeanNCD.Eval.Plan

/-- A local, acyclic, context-parameterized dataflow graph — the base block or the step block of a
    future scan (`papers/wave_f_scanplan_proposal.md` §6.2). Local assignments are plain
    `AssignPlan`s sharing this block's `contextShape` — the same node type the outer graph uses, so
    F2 introduces no second local-operation representation. -/
structure RawPlanBlock where
  contextShape : Array Nat
  tensorSigs   : Array TensorSignature
  inputs       : Array TensorSlot
  assignments  : Array AssignPlan
  outputs      : Array TensorSlot
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A raw `RawPlanBlock` violates a local-graph invariant. `wiring` reuses `PlanError` verbatim for
    every failure mode `checkPlanBlock`'s wiring loop shares with `checkPlan`'s outer-graph loop
    (slot range, input uniqueness/order, overwrite, duplicate destination, missing production,
    invalid forward read, and per-node `checkAssign` failure) — no second copy of those
    constructors. Only the two obligations a block has and the outer plan does not get their own
    constructors. -/
inductive BlockError
  | wiring                (cause : PlanError)
  | duplicateOutputSlot   (slot : TensorSlot)
  | blockContextMismatch  (nodeIndex : Nat) (expected actual : Array Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- First slot in `slots` that recurs later in the list, if any. Mirrors `Prepared.lean`'s
    `firstDuplicateName`, generalized to `TensorSlot` so `duplicateOutputSlot` can carry a
    witness. -/
private def firstDuplicateSlot : List TensorSlot → Option TensorSlot
  | [] => none
  | s :: rest => if rest.contains s then some s else firstDuplicateSlot rest

/-- Evidence that one `RawPlanBlock` is a sound local graph: every local assignment is checked
    against `block.contextShape`, inputs are in-range/unique/ordered, outputs are in-range/unique,
    no assignment overwrites an input, and every non-input local slot — outputs included — is
    produced exactly once. -/
structure CheckedPlanBlock where private mk ::
  raw          : RawPlanBlock
  checkedNodes : Array CheckedAssignPlan
  deriving Repr

/-- Validate one local block graph. Reuses `checkAssign` per assignment and the identical
    availability/production-order discipline `checkPlan` (`Check.lean`) already applies to the
    outer graph — the same loop shape, parameterized by this block's own `tensorSigs`/`inputs`
    instead of `RawEvalPlan`'s `tensorSigs`/`inputSlots`, plus the one block-specific obligation
    `checkPlan` has no analogue for: every assignment's `contextShape` must equal the block's
    declared `contextShape` (`checkPlan` instead requires empty context, via
    `topLevelContextNotEmpty`). -/
def checkPlanBlock (block : RawPlanBlock) : Except BlockError CheckedPlanBlock := do
  let n := block.tensorSigs.size
  for h : i in [0 : block.inputs.size] do
    let s := block.inputs[i]
    unless s < n do throw (.wiring (.slotOutOfRange s n))
    if h2 : i + 1 < block.inputs.size then
      let s2 := block.inputs[i + 1]
      if s == s2 then throw (.wiring (.duplicateInputSlot s))
      else if s2 < s then throw (.wiring (.inputSlotsNotOrdered i))
  for h : i in [0 : block.outputs.size] do
    let s := block.outputs[i]
    unless s < n do throw (.wiring (.slotOutOfRange s n))
  unless (block.outputs.toList).Nodup do
    throw (.duplicateOutputSlot
      ((firstDuplicateSlot block.outputs.toList).getD 0))
  let mut available : Array Bool := Array.replicate n false
  let mut producedBy : Array (Option Nat) := Array.replicate n none
  for s in block.inputs do
    available := available.set! s true
  let mut checkedNodes : Array CheckedAssignPlan := #[]
  for h : ni in [0 : block.assignments.size] do
    let step := block.assignments[ni]
    unless step.contextShape == block.contextShape do
      throw (.blockContextMismatch ni block.contextShape step.contextShape)
    let destSlot := step.destinationSlot
    match available[destSlot]? with
    | none => throw (.wiring (.nodeError ni (.slotOutOfRange destSlot n)))
    | some isAvail =>
        if isAvail then
          match producedBy[destSlot]?.join with
          | none => throw (.wiring (.inputSlotOverwritten destSlot ni))
          | some firstNode => throw (.wiring (.duplicateDestination destSlot firstNode ni))
    for h2 : ti in [0 : step.terms.size] do
      let t := step.terms[ti]
      for h3 : fi in [0 : t.factors.size] do
        let f := t.factors[fi]
        match available[f.sourceSlot]? with
        | none => throw (.wiring (.nodeError ni (.slotOutOfRange f.sourceSlot n)))
        | some true => pure ()
        | some false => throw (.wiring (.invalidForwardRead ni ti fi f.sourceSlot))
    match checkAssign block.tensorSigs step with
    | .error e => throw (.wiring (.nodeError ni e))
    | .ok c =>
        checkedNodes := checkedNodes.push c
        available := available.set! destSlot true
        producedBy := producedBy.set! destSlot (some ni)
  for h : i in [0 : n] do
    unless available[i]! do throw (.wiring (.missingProduction i))
  return CheckedPlanBlock.mk block checkedNodes

end LeanNCD.Eval.Plan
```

- [ ] **Step 2: Add construction, checking, and checker-mutation fixtures**

```lean
-- leanncd/test/Eval/Plan/BlockTest.lean
import LeanNCD.Eval.Plan.Block

/-!
# Wave F F2 block-checker tests

The context-indexed positive fixture reuses `KernelDenseTest.lean`'s `ctxPlan` verbatim (same
assignment, same expected values `ctx=0 -> [1,2,3]`, `ctx=1 -> [4,5,6]`, already independently
observed there) under a `RawPlanBlock` wrapper, so this file adds no new hand-derived numbers.
-/

namespace LeanNCD.Eval.Plan.BlockTest
open LeanNCD.Eval LeanNCD.Eval.Plan

-- One step block, contextShape=#[2]: input X (shape [2,3]), output Y (shape [3]),
-- Y[o] := X[ctx,o] — the exact assignment KernelDenseTest.lean's `ctxPlan` already verifies at
-- ctx=0 -> [1,2,3] and ctx=1 -> [4,5,6], now wrapped in a block with input/output ports.

def blockSigs : Array TensorSignature :=
  #[{ shape := #[2,3], dtype := .f64 }, { shape := #[3], dtype := .f64 }]

def blockReadX : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1,0], #[0,1]], bias := #[0,0] }
  , sourceShape := #[2,3], oobPolicy := .zeroPad }

def blockAssign : AssignPlan :=
  { contextShape := #[2], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[2,3], contextPos := #[0], outputPos := #[1], reductionPos := #[]
               , factors := #[blockReadX] }]
  , algebra := admittedAlgebra }

def stepBlock : RawPlanBlock :=
  { contextShape := #[2], tensorSigs := blockSigs, inputs := #[0]
  , assignments := #[blockAssign], outputs := #[1] }

run_cmd do
  match checkPlanBlock stepBlock with
  | .error e => throwError s!"checkPlanBlock rejected a well-formed block: {repr e}"
  | .ok _checked => pure ()

-- Mutation: duplicate output slot must be rejected with the exact witness, not merely "some error".
def dupOutputBlock : RawPlanBlock :=
  { stepBlock with outputs := #[1, 1] }

run_cmd do
  match checkPlanBlock dupOutputBlock with
  | .ok _ => throwError "duplicate output slot should have been rejected"
  | .error e =>
      unless e == .duplicateOutputSlot 1 do
        throwError s!"duplicate output: wrong error {repr e}"

-- Mutation: an assignment whose contextShape disagrees with the block's declared contextShape
-- must be rejected with the exact witness.
def wrongContextAssign : AssignPlan := { blockAssign with contextShape := #[3] }

def wrongContextBlock : RawPlanBlock :=
  { stepBlock with assignments := #[wrongContextAssign] }

run_cmd do
  match checkPlanBlock wrongContextBlock with
  | .ok _ => throwError "context-mismatched assignment should have been rejected"
  | .error e =>
      unless e == .blockContextMismatch 0 #[2] #[3] do
        throwError s!"context mismatch: wrong error {repr e}"

end LeanNCD.Eval.Plan.BlockTest
```

- [ ] **Step 3: Register the test module**

```toml
# leanncd/lakefile.toml — insert "Eval.Plan.BlockTest" into the Tests library's globs,
# right after "Eval.Plan.CheckedPrivacyTest" and before "Eval.Plan.GraphCheckTest"
```

- [ ] **Step 4: Run**

Run: `cd leanncd && lake build Eval.Plan.BlockTest`
Expected: PASS (all three `run_cmd` blocks execute at elaboration time; a failing `throwError` in
any of them fails the build, so a green build is itself the mutation-sensitivity evidence).

- [ ] **Step 5: Commit**

```bash
cd leanncd
git add LeanNCD/Eval/Plan/Block.lean test/Eval/Plan/BlockTest.lean lakefile.toml
git commit -m "feat(leanncd): add checked plan-block construction (Wave F F2, part 1)

- Add RawPlanBlock: local, acyclic, context-parameterized dataflow graph
- Add BlockError, wrapping PlanError for every wiring failure a block shares
  with the outer graph, plus duplicateOutputSlot/blockContextMismatch for the
  two obligations a block alone has
- Add CheckedPlanBlock (private mk) and checkPlanBlock, reusing checkAssign
  per node and checkPlan's availability/production-order loop shape
- Fixtures: a context-indexed well-formed block (reusing KernelDenseTest's
  already-observed ctxPlan values) plus duplicate-output and context-mismatch
  checker mutations
"
```

---

## Task 2: `runDenseBlock`

**Files:**
- Modify: `leanncd/LeanNCD/Eval/Plan/Block.lean` (append)
- Modify: `leanncd/test/Eval/Plan/BlockTest.lean` (append execution + mutation fixtures)

**Interfaces:**
- Consumes: `CheckedPlanBlock` (Task 1), `runDenseAssignAt`, `DenseTensor`, `PositionalInputError`
  (all unchanged)
- Produces: `runDenseBlock : CheckedPlanBlock → List Int → Array DenseTensor → Except
  PositionalInputError (Array DenseTensor)`

This is a separate, independently rejectable task from Task 1: a checker can be sound while a
worker is buggy, or vice versa, and `runDenseBlock` has its own failure mode (`PositionalInputError`)
distinct from `BlockError`.

- [ ] **Step 1: Implement `runDenseBlock`**

```lean
-- leanncd/LeanNCD/Eval/Plan/Block.lean (append, inside `namespace LeanNCD.Eval.Plan`)

/-- Execute one checked block at a fixed enclosing-scan context coordinate. Positional store is
    local to this invocation — sized to the block's own `tensorSigs`, not the outer plan's. Reuses
    `runDenseAssignAt` per node exactly as `runDensePlan` does for the outer graph; this is the only
    place F2 evaluates a local assignment. -/
def runDenseBlock (c : CheckedPlanBlock) (ctx : List Int) (inputs : Array DenseTensor) :
    Except PositionalInputError (Array DenseTensor) := do
  let raw := c.raw
  unless inputs.size == raw.inputs.size do
    throw (.arityMismatch raw.inputs.size inputs.size)
  let n := raw.tensorSigs.size
  let placeholder : DenseTensor := { shape := [], data := #[] }
  let mut store : Array DenseTensor := Array.replicate n placeholder
  for h : i in [0 : raw.inputs.size] do
    let slot := raw.inputs[i]
    let t := inputs[i]!
    let sig := raw.tensorSigs.getD slot { shape := #[], dtype := .f64 }
    unless t.shape == sig.shape.toList do
      throw (.shapeMismatch slot sig.shape t.shape)
    unless t.data.size == sig.shape.toList.foldl (· * ·) 1 do
      throw (.storageMismatch slot t.shape t.data.size)
    store := store.set! slot t
  for node in c.checkedNodes do
    let result ← runDenseAssignAt node ctx store
    store := store.set! node.plan.destinationSlot result
  return store
```

- [ ] **Step 2: Add execution and arity-mismatch fixtures**

```lean
-- leanncd/test/Eval/Plan/BlockTest.lean (append, inside `namespace LeanNCD.Eval.Plan.BlockTest`)

-- Execution: same `stepBlock` as Task 1, run at ctx=0 and ctx=1. Expected values are the same
-- [1,2,3]/[4,5,6] KernelDenseTest.lean's `ctxPlan` already observed for this exact assignment.
run_cmd do
  match checkPlanBlock stepBlock with
  | .error e => throwError s!"checkPlanBlock rejected a well-formed block: {repr e}"
  | .ok checked =>
      let x : DenseTensor := { shape := [2,3], data := #[1,2,3,4,5,6] }
      match runDenseBlock checked [0] #[x] with
      | .error e => throwError s!"ctx=0 failed: {repr e}"
      | .ok store => unless store[1]!.data == #[1,2,3] do
          throwError s!"ctx=0 wrong: {repr store[1]!.data}"
      match runDenseBlock checked [1] #[x] with
      | .error e => throwError s!"ctx=1 failed: {repr e}"
      | .ok store => unless store[1]!.data == #[4,5,6] do
          throwError s!"ctx=1 wrong: {repr store[1]!.data}"

-- Mutation: `runDenseBlock` arity mismatch (checked block expects exactly one input) must be
-- rejected with the same `PositionalInputError.arityMismatch` constructor `runDensePlan` uses.
run_cmd do
  match checkPlanBlock stepBlock with
  | .error e => throwError s!"checkPlanBlock rejected a well-formed block: {repr e}"
  | .ok checked =>
      match runDenseBlock checked [0] #[] with
      | .ok _ => throwError "arity mismatch should have been rejected"
      | .error e =>
          unless e == .arityMismatch 1 0 do
            throwError s!"arity mismatch: wrong error {repr e}"
```

- [ ] **Step 3: Run**

Run: `cd leanncd && lake build Eval.Plan.BlockTest`
Expected: PASS.

- [ ] **Step 4: Commit**

```bash
cd leanncd
git add LeanNCD/Eval/Plan/Block.lean test/Eval/Plan/BlockTest.lean
git commit -m "feat(leanncd): add checked plan-block execution (Wave F F2, part 2)

- Add runDenseBlock, reusing runDenseAssignAt per node exactly as
  runDensePlan does for the outer graph
- Fixtures: context-indexed execution (reusing KernelDenseTest's observed
  ctxPlan values) plus an arity-mismatch worker mutation
"
```

---

## Task 3: Discoverability, whole-slice review, and completion record

**Files:**
- Modify: `leanncd/LeanNCD.lean`
- Modify: `leanncd/LeanNCD/Eval/AGENTS.md`
- Modify: `papers/wave_f_scanplan_proposal.md`

This task is the whole-branch review the `slice-plan` skill calls "the one earning its keep" — it
is not a per-task mechanical step, and should not be skipped or merged away.

- [ ] **Step 1: Make `Block.lean` reachable from `import LeanNCD`**

`Block.lean` is core Wave F production code (unlike `Executable.lean`, which is deliberately *not*
on the default import graph because it's consumed only by `experiments/jax_bridge`). Add to
`leanncd/LeanNCD.lean`, alongside the existing `import LeanNCD.Eval.Plan.Adapter` line:

```lean
import LeanNCD.Eval.Plan.Block
```

- [ ] **Step 2: Update `LeanNCD/Eval/AGENTS.md`**

In the "Find It Fast" table's `Plan/` row, update the file count and list (currently "12 files:
`Types`, `Kernel`, `Graph`, `Error`, `Check`, `Coordinates`, `Dense`, `Signature`, `Prepared`,
`Compile`, `Adapter`, `Executable`") to add `Block`. In the `Plan/` subtree's file table, add a row:

```markdown
| `Block.lean` | checked plan-block vertical slice (F2) — `RawPlanBlock`, `BlockError`, `CheckedPlanBlock`/`checkPlanBlock`, `runDenseBlock`; reuses `checkAssign`/`runDenseAssignAt` per node and `checkPlan`'s wiring-loop shape, not a second local-graph implementation |
```

- [ ] **Step 3: Full build**

Run: `cd leanncd && lake build`
Expected: PASS with no skipped module. Record the exact job count (the completion record below
must state it, per this repo's own convention for F0/F1's completion records — do not restate a
prior count from memory).

- [ ] **Step 4: Append an F2 completion record**

In `papers/wave_f_scanplan_proposal.md`, under the F2 entry in §13 (immediately after the existing
F1 completion record, before the F3 heading), add a completion record matching the F0/F1 convention:
concrete file/type names landed, the exact `lake build` job count from Step 3, and — since this is
the reuse-focused slice — an explicit note of what was *not* duplicated (no second local-kernel
check, no second graph-wiring loop, no new coordinate math) so a later reader auditing Wave F for
duplication has a citable record rather than needing to re-derive it from the diff.

- [ ] **Step 5: Whole-slice review**

Before committing, re-read `Block.lean` and `BlockTest.lean` together against
`papers/wave_f_scanplan_proposal.md` §6.2/§7.2 and this plan's Global Constraints, specifically
checking:
- No existing file outside `Block.lean`/`BlockTest.lean`/`lakefile.toml`/`LeanNCD.lean`/
  `Eval/AGENTS.md`/the proposal doc was touched.
- Every `BlockError` case that duplicates a `PlanError` case is `.wiring (...)`, not a
  freestanding lookalike.
- `checkPlanBlock`/`runDenseBlock` call `checkAssign`/`runDenseAssignAt` directly — no
  reimplementation of local-kernel semantics anywhere in `Block.lean`.

- [ ] **Step 6: Commit**

```bash
cd leanncd
git add LeanNCD.lean LeanNCD/Eval/AGENTS.md
git -C .. add papers/wave_f_scanplan_proposal.md
git commit -m "docs(leanncd): close Wave F F2 — discoverability and completion record

- Add LeanNCD.Eval.Plan.Block to the default import LeanNCD graph
- Update Eval/AGENTS.md's Plan/ file table and count
- Append F2 completion record to wave_f_scanplan_proposal.md
"
```

---

## Plan Verification Checklist

- **§6.2 coverage:** `RawPlanBlock` (context shape, tensor signatures, inputs, ordered assignments,
  outputs)? ✓
- **§7.2 coverage:** input range/order, input/destination disjointness (via reused
  `inputSlotOverwritten`), assignment destination uniqueness, source availability/production order,
  local `checkAssign` composition, context-shape agreement, output range/uniqueness, output
  production? ✓ — traced constructor-by-constructor in Task 1's `checkPlanBlock`.
- **Reuse mandate honored:** no second local-kernel checker, no second graph-wiring loop, no second
  coordinate-math module — verified explicitly in Task 3 Step 5, not merely asserted in this
  document's prose.
- **Private constructor pattern:** `CheckedPlanBlock where private mk ::`? ✓ (matches
  `CheckedAssignPlan`/`CheckedEvalPlan`).
- **Every Lean snippet compiled** via `check-snippet.sh` against the real environment before being
  written into this plan, including both checker mutations and the arity-mismatch worker mutation
  (all three execute — not just type-check — at `run_cmd` elaboration time)? ✓
- **Fixture values observed, not hand-derived:** the `[1,2,3]`/`[4,5,6]` values are
  `KernelDenseTest.lean`'s own already-independently-verified `ctxPlan` result, reused verbatim
  under a block wrapper, not a new hand computation? ✓
- **No scan constructor added; `RawEvalPlan` untouched:** ✓ — F3's own plan will wire
  `CheckedPlanBlock` into a scan node.
- **Discoverability:** `import LeanNCD.Eval.Plan.Block` added; `Eval/AGENTS.md` updated; F2
  completion record appended to the proposal doc — not deferred to a later audit slice the way
  Wave C's C0-C4 discoverability gap was only caught by C6? ✓ (Task 3).

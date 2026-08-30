# Unary factor functions in the checked `EvalPlan` backend

**Status:** **Plan — verified, not yet executed.** Every code block and fixture value below was
applied to the tree in this worktree (with the `.lake` Mathlib cache synced per
`.claude/skills/new-slice/`, so builds take seconds), compiled, and the fixture values observed from a
real run; then **all source and test edits were reverted** — this branch currently carries only this
plan document. `lake build LeanNCD` was green (`8543 jobs`) with the production changes applied and
`lake build Tests` was green (`8657 jobs`) with the test flips applied. See §5.

This plan closes item 6 (the "Low–moderate" row) of
[`backend_missing_functionality.md`](backend_missing_functionality.md): the checked plan compiler
rejects a **unary factor** — a transcendental function (`log`/`exp`/`sin`/`cos`/`sqrt`/`recip`)
applied to a read inside a term, e.g. `L[] := Y[i]·log(P[i])` — at preflight, even though the
reference dense interpreter already evaluates it via `applyUnaryFn`.

**Decision.** Carry the function on the factor itself. `ReadPlan` gains an `Option UnaryOp` field; the
Dense `gatherFactor` applies it to the gathered value **after** the out-of-bounds zero-pad, reusing a
single context-free math core (`UnaryOp.applyChecked`) that the reference `applyUnaryFn` also wraps.
No new `PlanStep`, no new geometry, no new dtype, no `ContractionAlgebra` change — a unary factor is a
per-read scalar transform, not a new operation.

**Table of contents**

- [1. Background and the two real subtleties](#1-background-and-the-two-real-subtleties)
- [2. Design contract](#2-design-contract)
  - [2.1 Why not a pointwise temp](#21-why-not-a-pointwise-temp)
  - [2.2 Interaction with plain assigns and scans](#22-interaction-with-plain-assigns-and-scans)
  - [2.3 The JAX bridge is out of scope](#23-the-jax-bridge-is-out-of-scope)
- [3. Implementation tasks](#3-implementation-tasks)
  - [3.1 Task 1 — admit and lower unary factors (production)](#31-task-1--admit-and-lower-unary-factors-production)
  - [3.2 Task 2 — test corpus: flip rejections, add fixtures](#32-task-2--test-corpus-flip-rejections-add-fixtures)
  - [3.3 Task 3 — documentation sweep](#33-task-3--documentation-sweep)
- [4. Task and risk summary](#4-task-and-risk-summary)
- [5. Pre-authoring verification record](#5-pre-authoring-verification-record)
- [6. Stop conditions and definition of done](#6-stop-conditions-and-definition-of-done)

## 1. Background and the two real subtleties

The gap is confined and single-sited on the read path:

- The source AST already carries `Factor.unaryFn : UnaryOp → String → List IdxExpr → Factor`
  (`DSL/Ast.lean`), with `UnaryOp | log | exp | sin | cos | sqrt | recip`. `recip` has no keyword — it
  is produced only by the infix `/` sugar (`X[i]/Z[i]` desugars to `X[i]·recip(Z[i])`).
- The reference interpreter is the ready-made oracle: `applyUnaryFn` (`LeanNCD/Eval/Gather.lean`)
  reads exactly like a `.read` (via `gatherRead`, out-of-range ⇒ `0.0`) and then applies the function
  to the resulting value. `log`/`sqrt`/`recip` fail loud on a domain violation via
  `EvalError.unaryDomain`; `exp`/`sin`/`cos` are total.
- The backend rejects a unary factor in exactly one place — `checkFactor` in
  `LeanNCD/Eval/Plan/Compile.lean` throws `unaryFactor` — and the `ReadPlan` IR has no way to carry a
  function, so `residualizeAssignment`'s factor loop has a second (post-preflight unreachable)
  `.unaryFn` throw.

**Subtlety 1 — the out-of-bounds pad interacts with the function, and must stay `f(0)`.** A read is
zero-padded out of bounds. The reference reads `0.0` *then* applies `f`, so an out-of-bounds read of a
unary factor contributes `f(0)` — which for a total function is **nonzero** (`exp(0)=1`, `cos(0)=1`)
and for a partial function is a **domain error** (`log(0)`, `recip(0)`). The checked backend must do
the identical thing: apply the function inside `gatherFactor`, after the existing zero-pad, so
`f(0)` — not `0` — flows into the factor product. This is confirmed end-to-end in §5 (`expOobProg`).

**Subtlety 2 — fail-loud domain errors are a Dense-evaluator concern, and force the read path to
become failable.** `log`/`sqrt`/`recip` reject part of their domain, and the checked backend must fail
loud identically to the reference — which means `gatherFactor` (today a total `... → Float`) becomes
`... → Except PositionalInputError Float`, and the pure `List.map` nest in `runDenseAssignAt` becomes
`mapM`-threaded. That threading is the whole cost of this change (§4). It is unavoidable for
fail-loud semantics: a domain violation depends on the actual gathered value at a coordinate, which is
exactly what the loop computes. (This is also why the JAX bridge is out of scope — §2.3.)

**Not a write-path change.** The `stepWriteRowsOk`/`baseWriteRowsOk`/`checkWrites` write-geometry
predicate family documented in the Wave F plans is untouched: unary factors touch only the
read/reduction path (`gatherFactor`, and the shared `UnaryOp.applyChecked` math). No write predicate
is added, edited, or made newly reachable, so no case × class sibling audit is required.

## 2. Design contract

1. **`ReadPlan` gains `unary : Option UnaryOp := none`.** A unary factor is a per-read scalar
   transform, so it rides on the factor, not on a new `PlanStep` (contrast the nonlinearity thread,
   whose whole-tensor `.pointwise`/`.axiswise` operations got their own raw types and step cases). The
   AST-layer `UnaryOp` enum is reused directly, exactly as `Plan/Nonlin.lean`'s `RawPointwisePlan`
   reuses the AST `PointwiseFn` rather than minting a positional twin. The `Option`-with-default keeps
   every existing `ReadPlan` literal (tests, `experiments/jax_bridge/` fixtures) compiling unchanged.
   `Kernel.lean` imports `DSL.Ast` for the enum (the plan layer already depends on `DSL.Ast` at the
   `Compile.lean` tier), and adds one `instance : BEq LeanNCD.UnaryOp` because `UnaryOp` derives
   `DecidableEq` but not `BEq` and `ReadPlan` derives `BEq` — the same manual instance `Plan/Nonlin.lean`
   already adds for `PointwiseFn`/`AxiswiseFn`.

2. **One context-free math core, `UnaryOp.applyChecked`, shared by both evaluators.** The function
   math and its domain partiality live once, in `LeanNCD/Eval/Error.lean` (which already imports
   `DSL.Ast` and owns `UnaryDomainOp`), reachable by the reference `Gather.lean` and — transitively via
   `Plan/Error.lean` → `Eval/Error.lean` — by the Dense `Dense.lean` (which by design imports neither
   `Gather` nor `Contract`). Each layer wraps the returned `UnaryDomainOp` into its own error channel.
   Adding a future unary operator is then one `UnaryOp` constructor and one arm here; both evaluators
   inherit it and differential parity holds by construction. This mirrors the once-defined
   `PointwiseFn.apply` that both `applyNonlin` and `runDensePointwise` call.

3. **The reference `applyUnaryFn` is refactored to wrap the core — behavior-preserving.** It becomes
   `(op.applyChecked v).mapError (fun dop => .unaryDomain dop v ctx)`, re-attaching its `EvalContext`.
   Same domain rules, same value, same `EvalContext`, so the byte-for-byte `EvalError` messages
   (`RejectTest.lean`'s UF3/UF4) are unchanged. Kept green is the evidence the refactor changed
   nothing (§5).

4. **The plan-layer domain error is UID-free and stores the value as bits.** `PositionalInputError`
   gains `unaryDomain (op : UnaryDomainOp) (valueBits : UInt64) (slot : TensorSlot)`. It stores
   `Float.toBits value`, not a `Float`, because `PositionalInputError` derives `DecidableEq`/`BEq` and a
   `Float` field blocks `DecidableEq` — the same reason `ScalarConst.f64` stores `UInt64` bits.
   `UnaryDomainOp` gains `BEq, Repr` (it had only `DecidableEq`) so the derivations still hold.

5. **`gatherFactor` applies the function after the pad; `runDenseAssignAt` threads `Except`.**
   `gatherFactor`'s sole functional caller is `runDenseAssignAt`; the scan and block workers reuse
   `runDenseAssignAt` (already `Except`-returning), so the change propagates through one chokepoint.

6. **`checkFactor` admits `.unaryFn`; `residualizeAssignment` lowers it** to the same `ReadPlan` a
   `.read` produces, with `unary := some op`. No new geometry check: the source is already forced to
   `f64` with `zeroPad`, and the affine map is validated identically to a plain read.

7. **The `unaryFactor` `CapabilityError` constructor is retained, producer-less.** Like `scanNode`
   after nonlinear scans and `unsupportedAgg` after max/min, deleting a shipped closed-family
   constructor is itself a semantic-version change and a serialized rejection may still carry it. Both
   its throw sites become admissions; the constructor stays on the enum with a note that it is now
   unreachable from preflight.

8. **C0's frozen classifier stays frozen, divergence documented.** `test/Eval/Plan/ContractTest.lean`'s
   `classifyFactor` still classifies `.unaryFn` as `.rejected "unaryFactor"`. Leave it and document the
   divergence in `checkFactor`'s doc comment, exactly as the nonlinearity thread did for
   `.pointwise`/`.axiswise` and the max/min thread did for `.max`/`.min`. Do **not** edit
   `classifyFactor`.

### 2.1 Why not a pointwise temp

`backend_missing_functionality.md` suggests `f(read)` could residualize into a `.pointwise` temp `T`
the term then reads. **Rejected — it disagrees with the reference on two counts:**

- **Out-of-bounds.** A pointwise temp is computed over the source's in-bounds elements; reading it
  with `zeroPad` yields `0` at out-of-bounds coordinates, whereas the reference yields `f(0)` (often
  nonzero, or a domain error). §5's `expOobProg` observes `exp(0)=1` at the boundary — a pointwise
  temp would give `0` there.
- **Spurious domain errors.** Pre-applying `f` over the *whole* source throws on elements the term
  never reads (a masked or shifted subset), so `log`/`sqrt`/`recip` would fail on programs the
  reference accepts.

Applying the function per-read inside `gatherFactor`, after the pad and only on values actually read,
reproduces the reference exactly.

### 2.2 Interaction with plain assigns and scans

The unary is a **per-factor** property carried on `ReadPlan`, so both plain assigns and scans need no
special handling — both run the same Dense per-slice assign (`runDenseAssignAt`), and a scan step is a
plain assign with some iteration axes pinned (pins become affine substitutions into factor *reads* via
`substitutePins`, never into anything the unary touches). `residualizeAssignment`'s `.unaryFn` case is
shared by all three of its callers — plain, scan base, scan step — so a unary factor inside a scan
recurrence lowers identically to one at top level. The differential scan corpus (`enumScanCases`,
`DifferentialTest.lean`) contains no unary case today and is unaffected; its `17/17/0/0` split is left
exactly as the max/min thread set it.

### 2.3 The JAX bridge is out of scope

`experiments/jax_bridge/` is an experimental spike, not a Lake target (`lake build` does not typecheck
its drivers), and it explicitly accepts only projection-only affine `einsum` contractions with no
nonlinearities. Its `ReadPlan` fixtures keep compiling (the `Option` default). Wiring unary factors
into its codegen/runtime is deliberately **not** done here, for a structural reason: the fail-loud
domain behavior (Subtlety 2) cannot transfer — a JIT/`vmap`-compiled array computation yields IEEE
`inf`/`nan` on `log(0)`, not a typed error. The out-of-bounds `f(0)` parity *would* already hold via
its `jnp.where`-based zero-pad gather if it were wired, but that is future work owned by a JAX-backend
slice, not this one.

## 3. Implementation tasks

### 3.1 Task 1 — admit and lower unary factors (production)

**Files:** `LeanNCD/Eval/Error.lean`, `LeanNCD/Eval/Gather.lean`, `LeanNCD/Eval/Plan/Kernel.lean`,
`LeanNCD/Eval/Plan/Error.lean`, `LeanNCD/Eval/Plan/Dense.lean`, `LeanNCD/Eval/Plan/Compile.lean`.

**(a) `Eval/Error.lean` — the shared math core.** Give `UnaryDomainOp` the `BEq, Repr` it lacks (they
are required transitively by the new `PositionalInputError` constructor in (d)), and add the
context-free core right after it:

```lean
inductive UnaryDomainOp
  | log
  | sqrt
  | recip
  deriving DecidableEq, BEq, Repr

/-- The single, context-free home for every unary transcendental's math and domain partiality
    (`log`/`sqrt`/`recip` fail loud; `exp`/`sin`/`cos` are total). Both evaluators call this and wrap
    the returned `UnaryDomainOp` into their own error channel — the reference `applyUnaryFn` below
    re-attaches its `EvalContext` (`EvalError.unaryDomain`), the checked-plan `gatherFactor`
    (`Eval/Plan/Dense.lean`) attaches a positional slot (`PositionalInputError.unaryDomain`). Adding a
    future unary operator is one `UnaryOp` constructor and one arm here; both evaluators inherit it
    and parity holds by construction. -/
def _root_.LeanNCD.UnaryOp.applyChecked : LeanNCD.UnaryOp → Float → Except UnaryDomainOp Float
  | .log,   v => if v ≤ 0.0 then .error .log else .ok (Float.log v)
  | .sqrt,  v => if v < 0.0 then .error .sqrt else .ok (Float.sqrt v)
  | .exp,   v => .ok (Float.exp v)
  | .sin,   v => .ok (Float.sin v)
  | .cos,   v => .ok (Float.cos v)
  | .recip, v => if v == 0.0 then .error .recip else .ok (1.0 / v)
```

**(b) `Eval/Gather.lean` — refactor `applyUnaryFn` to wrap the core** (behavior-preserving — same
domain rules, same value `v`, same `ctx`, so the rendered messages are byte-identical):

```lean
def applyUnaryFn (ctx : EvalContext) : UnaryOp → Float → Except EvalError Float
  | op, v => (op.applyChecked v).mapError (fun dop => .unaryDomain dop v ctx)
```

**(c) `Eval/Plan/Kernel.lean` — the IR field.** Add the import, the `BEq` instance, and the field:

```lean
import LeanNCD.Eval.Plan.Types
import LeanNCD.DSL.Ast
```

```lean
/-- `UnaryOp` (`DSL/Ast.lean`) derives `DecidableEq` but not `BEq`; `ReadPlan` derives `BEq`, so it
    needs one for its `Option UnaryOp` field. Mirrors the manual instances `Plan/Nonlin.lean` adds
    for `PointwiseFn`/`AxiswiseFn`. -/
instance : BEq LeanNCD.UnaryOp := ⟨fun a b => decide (a = b)⟩
```

```lean
/-- One factor: a gather from `sourceSlot` through `map`, against a shape the checker has already
    verified equals that slot's signature. `unary`, when present, is a transcendental function
    (`log`/`exp`/…) applied to the gathered value AFTER the out-of-bounds zero-pad — so an
    out-of-bounds read contributes `f(0)`, matching the reference `gather` exactly. -/
structure ReadPlan where
  sourceSlot  : TensorSlot
  map         : AffineMap
  sourceShape : Array Nat
  oobPolicy   : OutOfBoundsPolicy
  unary       : Option UnaryOp := none
  deriving DecidableEq, BEq, Repr, Inhabited
```

The `instance` goes inside `namespace LeanNCD.Eval.Plan`, above `AffineMap` (before its first use).

**(d) `Eval/Plan/Error.lean` — the plan-layer domain error.** Add one constructor to
`PositionalInputError` (bits, not `Float`, to preserve the derivations):

```lean
  | unaryDomain     (op : UnaryDomainOp) (valueBits : UInt64) (slot : TensorSlot)
```

**(e) `Eval/Plan/Dense.lean` — apply after the pad, thread `Except`.** `gatherFactor` becomes
failable; the pure `map` nest in `runDenseAssignAt` becomes `mapM`. The three fold-law `example`
proofs operate on `List Float` and are untouched.

```lean
/-- Gather one factor. Every source dimension is range-tested BEFORE flattening (`inBoundsPerDim`,
    `Coordinates.lean`): testing the flat offset instead can alias distinct invalid coordinates onto
    a valid address (proposal §8.3). A `unary` function is applied to the gathered value AFTER the
    out-of-bounds zero-pad (so an out-of-bounds read contributes `f(0)`, matching the reference
    `gather`), and can fail loud on a domain violation (`log`/`sqrt`/`recip`) via the shared
    `UnaryOp.applyChecked` — the same oracle the reference `applyUnaryFn` wraps. -/
private def gatherFactor (store : Array DenseTensor) (f : ReadPlan) (iter : List Int) :
    Except PositionalInputError Float :=
  let base : Float :=
    match store[f.sourceSlot]? with
    | none => 0.0
    | some t =>
        let src := applyAffine f.map iter
        let shape := f.sourceShape.toList
        if inBoundsPerDim shape src then (t.data[flatIndex shape (src.map Int.toNat)]?).getD 0.0
        else 0.0
  match f.unary with
  | none => .ok base
  | some op => (op.applyChecked base).mapError (fun dop => .unaryDomain dop (Float.toBits base) f.sourceSlot)
```

The `runDenseAssignAt` body (everything after `validateContext`/`validateStore`) becomes:

```lean
  let a := c.plan
  let alg := a.algebra
  let out ← (allCoords a.outputShape.toList).mapM (fun oc => do
    let termAccs ← a.terms.toList.mapM (fun t => do
      let redShape := t.reductionPos.toList.filterMap (fun p => t.iterationShape[p]?)
      let prods ← (allCoords redShape).mapM (fun rc => do
        let iter : Array Int := Id.run do
          let mut iter : Array Int := Array.replicate t.iterationShape.size 0
          for (p, v) in t.contextPos.toList.zip ctx do iter := iter.set! p v
          for (p, v) in t.outputPos.toList.zip oc do iter := iter.set! p v
          for (p, v) in t.reductionPos.toList.zip rc do iter := iter.set! p v
          return iter
        let factorVals ← t.factors.toList.mapM (fun f => gatherFactor store f iter.toList)
        return factorFold alg factorVals)
      return reductionFold alg prods)
    return termFold alg termAccs)
  return { shape := a.outputShape.toList, data := out.toArray }
```

**(f) `Eval/Plan/Compile.lean` — admit at preflight, lower.** `checkFactor`'s `.unaryFn` arm becomes
`pure ()`; add one sentence to its doc comment noting it now diverges from C0's frozen `classifyFactor`
(as `checkNonlinTopLevel`/`checkAggOp` note their divergences):

```lean
def checkFactor (stmtName : String) : Factor → Except CapabilityError Unit
  | .read ..       => pure ()
  | .iverson _     => throw (.maskOrPredicate s!"{stmtName}: iverson factor")
  | .unaryFn _ _ _ => pure ()
```

and `residualizeAssignment`'s factor loop replaces the `.unaryFn` throw with real lowering (reads
exactly like `.read`, then carries the function):

```lean
      | .unaryFn op name idxs =>
          -- Reads exactly like `.read name idxs` (same slot resolution, same affine rows, same
          -- zero-pad), then carries the unary function so `gatherFactor` applies it after the pad.
          let (sourceSlot, sourceShape) := resolveSource name
          let rows := idxs.map (fun e => substitutePins pins basisUids (idxToRow basisUids e))
          let coeffs : Array (Array Int) := (rows.map (fun r => r.1.toArray)).toArray
          let biasArr : Array Int := (rows.map (fun r => r.2)).toArray
          factorsAcc := factorsAcc.push
            { sourceSlot, map := { coeffs, bias := biasArr }, sourceShape, oobPolicy := .zeroPad
            , unary := some op }
```

Leave the `unaryFactor` constructor on `CapabilityError` (`Eval/Plan/Error.lean`); update its inline
comment to note it is now producer-less (kept per §9.2, as `scanNode`/`unsupportedAgg` are). Confirm
with a grep that no other producer remains.

**Verification for Task 1:** `cd leanncd && "$HOME/.elan/bin/lake" build LeanNCD` is green (§5 observed
`8543 jobs`).

### 3.2 Task 2 — test corpus: flip rejections, add fixtures

**Files:** `test/Eval/Plan/CompileTest.lean`, `test/Eval/Plan/ScanCompileTest.lean`,
`test/Eval/Plan/KernelDenseTest.lean`, `test/Eval/Plan/DifferentialTest.lean`.

**(a) `CompileTest.lean` — the top-level `unaryFactor` preflight fixture now accepts.** Convert the
rejection `#guard` (the `.unaryFn .log "X" []` donor) to an `isOk` accept, exactly as the max/min
thread did for its two `unsupportedAgg` donors immediately below it in the same file:

```lean
-- unaryFactor: log/exp/… are now ADMITTED (they lower to a unary-carrying `ReadPlan` factor) —
-- preflight returns none, so this donor program becomes an accepted-case fixture rather than a
-- rejection.
#guard isOk (capabilityPreflight
    { acceptedSched with stmts :=
        [.plain (.assign "Y" [.free ⟨"i", 0, .nat⟩]
          { body := { terms := [{ factors := [.unaryFn .log "X" []] }] }, nonlin := .identity })] })
```

**(b) `ScanCompileTest.lean` — the two `badUnary` scan rejections now accept.** There are exactly
**two** (one base-side, one recur-side), not four — unlike max/min, whose `badAgg` had `max`×`min`.
Point the `badUnary` helper at the resolvable `S0` (so it compiles cleanly once admitted, matching the
`badAgg` helper) and flip both assertions to `== none`:

```lean
def badUnary (nm : String) (adv : LHSSlot) : Stmt := .assign nm [adv]
  { body := { terms := [{ factors := [.unaryFn .log "S0" []] }] }, nonlin := .identity }
```
```lean
#guard rej [badUnary "S" pinL] [okRecur] == none   -- unary factor now admitted
```
```lean
#guard rej [okBase] [badUnary "S" nextL] == none   -- unary factor now admitted
```

Update the two section notes (base list and recurrence list) to add unary factors alongside the
`.freeNorm`/`.pointwise`/`.axiswise`/`max`/`min` constructs they already list as no-longer-preflight
rejections. The `badUnary` helper name is now a slight misnomer (it no longer rejects); keep it for
minimal churn, matching how the max/min thread kept `badAgg`.

**(c) `KernelDenseTest.lean` — new Dense unit fixtures.** These bypass the compiler and set `unary`
directly, locking the Dense worker's apply-after-pad and fail-loud behavior independently of Task 1's
lowering. Add a two-slot signature (`A` at slot 0 shape `#[4]`, `Y` at slot 1 shape `#[4]`, both
`f64`) and a single-factor identity plan `Y[i] := f(A[i])`; **donor for the factor: `readA`'s shape**,
adding `unary := some op` and using coeff row `#[#[1]]` for the rank-1 iteration basis. Observed
values (from §5 — confirm via run, do not hand-derive):

| Fixture | `unary` / store | Observed `Y` |
|---|---|---|
| log | `some .log`, `A=[1,2,4,8]` | `#[0.0, 0.693147, 1.386294, 2.079442]` |
| sqrt | `some .sqrt`, `A=[1,2,4,8]` | `#[1.0, 1.414214, 2.0, 2.828427]` |
| exp | `some .exp`, `A=[1,1,1,1]` | `#[2.718282, 2.718282, 2.718282, 2.718282]` |
| **exp OOB** (`f(0)` at edge) | `some .exp`, bias `+1`, `A=[1,1,1,1]` | `#[2.718282, 2.718282, 2.718282, 1.0]` |
| **sqrt domain violation** | `some .sqrt`, `A=[1,-4,4,9]` | `.error (.unaryDomain .sqrt 13839561654909534208 0)` |
| **recip domain violation** | `some .recip`, `A=[2,0,4,8]` | `.error (.unaryDomain .recip 0 0)` |

`13839561654909534208 == Float.toBits (-4.0)` and `0 == Float.toBits (0.0)` (observed, §5). The exp-OOB
fixture (last element `1.0 = exp(0)`) is what distinguishes the correct apply-after-pad from a
pointwise-temp lowering (which would give `0.0`); the two domain fixtures distinguish op, value, and
slot in the payload — each has exactly one violating element, so the reported value is unambiguous.

**(d) `DifferentialTest.lean` — end-to-end parity fixtures (the load-bearing check).** Add three
dedicated fixtures on the `maxPlainProg` pattern (compile → `prepareEvalPlan` → `runPreparedDense`,
cross-checked against `evalScheduled` via `planAgrees`, plus an explicit expected value). Observed
values from §5:

- **`xentProg`**: `L[] := Y[i]·log(P[i])`, `Y=[1,0]`, `P=[0.5,0.5]` ⇒ plan `L = [-0.693147]` = reference
  `L`. **Mutation-verified (teeth):** dropping the unary threading (`unary := none` in the
  `residualizeAssignment` `.unaryFn` case) makes the plan compute `Y·P = [0.5]`, disagreeing with the
  reference `[-0.693147]` — a `DISAGREEMENT (env)` via `planAgrees`. Restoring returns it to green.
  Record both observations in the completion note.
- **`expOobProg`**: `E[i] := exp(A[i + 1])`, `A=[0,1,2]` ⇒ plan `E = [2.718282, 7.389056, 1.0]` =
  reference `E`. The last element (`exp(0)=1` from the out-of-bounds read at `i=2`) is the end-to-end
  confirmation of Subtlety 1 through the whole TL pipeline. Write the shift with spaces (`A[i + 1]`):
  the DSL tokenizes `A[i +1]` differently (`+1` as a signed literal).
- **`divProg`**: `Y[i] := X[i] / Z[i]`, `X=[6,8,9]`, `Z=[2,4,3]` ⇒ plan `Y = [3.0, 2.0, 3.0]` =
  reference `Y`. Exercises the friendly `/` sugar (`Factor.unaryFn .recip`) end-to-end.

The `enumPrograms` sweep and its `total == 3832 && accepted == 3832` gate are **not** touched: no unary
case is woven into the generator (which would risk a reference-side domain error becoming a hard sweep
failure), exactly as the max/min thread kept the plain corpus stable and relied on dedicated fixtures.

**Reference regression (must stay green, not edited):** `RejectTest.lean`'s UF1–UF4 assert the
reference `EvalError` domain messages byte-for-byte. They are the evidence that the `applyUnaryFn`
refactor (Task 1(b)) is behavior-preserving; do not modify them.

**Verification for Task 2:** `"$HOME/.elan/bin/lake" build Tests` is fully green (§5 observed
`8657 jobs` with the flips applied; the new fixtures add to that).

### 3.3 Task 3 — documentation sweep

**Files:** `papers/backend_missing_functionality.md`, `papers/wave_f_scanplan_proposal.md`,
`papers/wave_f_capability_manifest.md`, `papers/eval_ir.md`, `leanncd/LeanNCD/Eval/AGENTS.md`.

- **`backend_missing_functionality.md`**: remove the unary-factor row from the Missing-capabilities
  table and its rationale item #6; add a bullet to "Already closed (do not re-list as missing)"
  describing the per-factor `ReadPlan.unary` lowering and the shared `UnaryOp.applyChecked` core, and
  naming the `DifferentialTest.lean` fixtures (`xentProg`/`expOobProg`/`divProg`) as its differential
  evidence. Add this plan to "Related documents". Bump the "Last re-derived" date.
- **`wave_f_scanplan_proposal.md`**: in the §5.2 "Wave F continues to reject" list, remove the
  `unary factors;` bullet. In the "Functionality still missing" table, flip the **Unary factor
  functions** row from "Rejected in ordinary assignments and scans" to **Admitted** (describe the
  `ReadPlan.unary` lowering and `gatherFactor`'s apply-after-pad). In the corpus-split quotation
  paragraph, drop "unary factors" from the "remaining §5.1 restrictions … unchanged" list, and add
  unary factors to the sentence listing what `prepareEvalPlan` now admits.
- **`wave_f_capability_manifest.md`**: in the "remaining still-rejected families are …" sentence,
  remove "unary factor functions".
- **`eval_ir.md`**: in the capability-preflight rejection sentence ("returns a typed `CapabilityError`
  for … unary factors, `max` or `min` aggregation, …"), remove **both** "unary factors" **and**
  "`max` or `min` aggregation" — the latter is a **stale claim the max/min thread left behind** (max/min
  was admitted; `eval_ir.md` was not in that thread's edit set). Also document the new `ReadPlan.unary`
  field in the `ReadPlan` description near the affine-lookup-table section.
- **`LeanNCD/Eval/AGENTS.md`**: if any row states unary factors are rejected on the checked-plan path,
  flip it; the "unary math fns → `Gather.lean`" row already describes the reference and is fine.
- **`wave_c_capability_manifest.md` §3 — leave frozen.** That table is the closed-enum catalog of every
  `CapabilityError` constructor and what it *rejects*; it still lists `scanNode`/`unsupportedNonlin`/
  `unsupportedAgg` as rejecting even after those were admitted (a deliberate frozen catalog). Flipping
  only the `unaryFactor` row would make it inconsistent, so — matching the max/min precedent — leave it
  and track the live boundary in the Wave-F docs above.

Cite identifiers only in all shipped doc text — no `File.lean:NNN` line numbers (a later code commit in
this slice would invalidate them). Before declaring the sweep complete, grep the repo for
`unary factor`/`unaryFactor` and confirm every remaining hit is either the frozen enum catalog, a
dated ledger under `leanncd/docs/superpowers/`, a reference-evaluator (`Gather`/KnownGap) statement
that is still true, or C0's frozen classifier — not a live checked-plan "rejected" claim.

## 4. Task and risk summary

| Task | Deliverable | Risk | Fixtures / cycles |
|---|---|---|---|
| 1 | `ReadPlan.unary`; shared `UnaryOp.applyChecked`; wrap `applyUnaryFn`; `PositionalInputError.unaryDomain` (bits); `gatherFactor` apply-after-pad + `Except`; `runDenseAssignAt` `mapM`; `checkFactor`/`residualizeAssignment` admit+lower; retain `unaryFactor` | **Low–moderate.** Wider than max/min: it makes the Dense read path failable, so `gatherFactor`'s type change ripples through `runDenseAssignAt`'s hot loop — but `gatherFactor` has a single functional caller and the scan/block workers already bind `runDenseAssignAt` with `←`, so a green `lake build Tests` proves every caller handles it. | 0 new; `lake build LeanNCD` |
| 2 | Flip 1 CompileTest + 2 ScanCompileTest rejections; 6 Dense unit fixtures; 3 end-to-end differential fixtures | **Moderate.** The differential fixtures are the load-bearing check; 6 Dense fixtures + 3 differential fixtures, **1 mutation cycle** (drop-unary-threading, already demonstrated in §5). | 9 new fixtures, 1 mutation cycle |
| 3 | Doc sweep incl. the stale `eval_ir.md` max/min fix + `ReadPlan.unary` doc + C0 divergence note | **Low.** Prose only; the grep is the guard against a live "rejected" claim lingering. | none |

Task boundaries pass the reviewer test: a reviewer could reject the fixture work (Task 2) while
approving the lowering (Task 1), and reject a doc claim (Task 3) independently of both. Task 1's six
files are one coherent, compiler-forced change (the shared core, the IR field, the error constructor,
the worker threading, and the two admission sites have no failure mode independent of each other and
share one build cycle), so they are one task, not six.

**Sequencing note (per the slice-plan discipline on early independent verification):** Task 1's
`gatherFactor`/`runDenseAssignAt` `Except`-threading is the one place a subtle bug could hide (it
touches the hot loop reused by scans). The `xentProg` mutation and the scan-corpus green build are its
independent checks; run them while Task 1 is still fresh, not only at the end.

## 5. Pre-authoring verification record

All of the following was run against the tree at `main` (`af48c99`, which already includes the max/min
thread) in this worktree, with the `.lake` Mathlib cache synced (per `.claude/skills/new-slice/`) so
builds take seconds, then **all source and test edits were reverted** — this branch currently carries
only this plan document.

- **Every Lean block in §3.1 was applied and compiled**: `lake build LeanNCD` →
  `Build completed successfully (8543 jobs)`. Two derivation failures were hit and fixed during
  verification, not hypothetical: `PositionalInputError`'s `deriving Repr`/`BEq` forced `Repr`/`BEq`
  onto `UnaryDomainOp` (fixed in (a)); a `Float` field on `PositionalInputError` would have broken its
  `deriving DecidableEq`, which is why the value is stored as `UInt64` bits.
- **The three flipped test fixtures were confirmed to be exactly the expected ones**, and no others
  failed: with Task 1 applied, `lake build Tests` failed only on `CompileTest.lean`'s `unaryFactor`
  `#guard` and `ScanCompileTest.lean`'s two `badUnary` `#guard`s; after the §3.2(a)/(b) flips,
  `lake build Tests` → `Build completed successfully (8657 jobs)`. The `ReadPlan` field addition broke
  no existing `ReadPlan` literal (the `Option` default held).
- **Every fixture value in §3.2 was observed from a real run**, not hand-derived — the Dense table
  (`log`/`sqrt`/`exp`/exp-OOB and the two `.unaryDomain` payloads with `valueBits` `13839561654909534208`
  and `0`), and the three end-to-end results (`xentProg` `[-0.693147]`, `expOobProg`
  `[2.718282, 7.389056, 1.0]`, `divProg` `[3.0, 2.0, 3.0]`), each with `plan == reference` byte-for-byte.
- **The `xentProg` mutation was run and recorded.** Setting `unary := none` in the
  `residualizeAssignment` `.unaryFn` case (rebuilt) made the plan compute `[0.5]` while the reference
  stayed `[-0.693147]`; restoring returned them to agreement. This proves the unary threading is
  load-bearing and the fixture has teeth.
- **The `applyUnaryFn` refactor is behavior-preserving**, evidenced by `RejectTest.lean`'s UF1–UF4
  staying green in the full `Tests` build (they pin the reference `EvalError` domain messages
  byte-for-byte).
- **All file paths cited in this plan were verified present with `ls`.** The doc-sweep also surfaced a
  stale max/min claim in `eval_ir.md` (still listing `max`/`min` aggregation as rejected) — folded into
  Task 3.

The full-suite green run with the *new* fixtures added is deliberately **not** part of this record — it
depends on Task 2's fixtures, which are the implementer's deliverable, not the author's.

## 6. Stop conditions and definition of done

**Done when:** `ReadPlan` carries `unary : Option UnaryOp`; `UnaryOp.applyChecked` is the single math
core and `applyUnaryFn` wraps it; `PositionalInputError.unaryDomain` carries `(op, valueBits, slot)`;
`gatherFactor` applies the function after the zero-pad and `runDenseAssignAt` threads `Except`;
`checkFactor` and `residualizeAssignment` admit and lower `.unaryFn`; `unaryFactor` is retained
producer-less; `lake build Tests` is fully green; the six Dense fixtures and three differential
fixtures pass and the `xentProg` mutation was demonstrated to break parity; UF1–UF4 stay green; and the
doc sweep's grep returns no live checked-plan document still asserting unary factors are rejected.

**Stop and report (do not improvise) if:** any accepted fixture stops matching `evalScheduled` (a real
oracle disagreement — the apply-after-pad or the shared-core reasoning would be wrong, not a number to
re-baseline); or admitting `.unaryFn` surfaces a second consumer of `gatherFactor`'s old total type
that the `Except` change breaks in a way a green `Tests` build did not reveal (none was found in §5, but
it is the one non-local risk). Both are contract defects, not plan steps.

## Related documents

- [`backend_missing_functionality.md`](backend_missing_functionality.md) — the inventory this plan
  closes a row of.
- [`max_min_aggregation.md`](max_min_aggregation.md) — the immediately-preceding sibling slice; this
  plan mirrors its structure (single-sited lowering, dedicated differential fixtures, frozen-C0
  divergence note, retained producer-less `CapabilityError`).
- [`nonlinearity_split_pair_direct_lowering.md`](nonlinearity_split_pair_direct_lowering.md) — the
  precedent for reusing an AST scalar-fn enum in the plan layer (`RawPointwisePlan` reuses
  `PointwiseFn`) and for a shared, once-defined `.apply` math core.
- [`eval_ir.md`](eval_ir.md) — the eval-IR reference; carries the `ReadPlan` description and a
  capability-rejection list this plan updates.

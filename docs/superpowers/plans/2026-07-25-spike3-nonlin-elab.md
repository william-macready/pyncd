# Spike 3 — make Nonlin wildcard hazards unrepresentable + Elab/Syntax tables Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox (`- [ ]`). Task 1 is a **Lean AST type change** (proof repair — drive with `lean4`/`lean:prove` tooling); Tasks 2–3 are **Lean metaprogramming** (syntax/elab); Task 0 is a small **behavioral** change (a validation reject + regression tests). Verify with `lake build`.

> **Revised 2026-07-26** per the high-effort code analysis in `pyncd.worktrees/agents-gpt-56-vscode-agents-integration/copilot_code_analysis.md` (compiled countermodels + runtime regressions against the current post-6a tree). Changes from the first draft: (a) added **Task 0 (Stage 0)** — freeze + **reject non-identity scatter**, a demonstrated silent-erasure bug the Nonlin refactor would otherwise paper over; (b) renamed `RowwiseFn → AxiswiseFn`; (c) 3b uses **two closed keyword categories** so `relu(where…)` fails at parse ("parse, don't validate"); (d) the equivalence certs stay **independent hand-written references** (not delegating to production); (e) the completion claim is narrowed to **representation closure**, not semantic closure.

**Goal:** (0) Decide and enforce a scatter-nonlinearity policy so the Nonlin refactor doesn't hide a real bug. (3a) Replace `Nonlin`'s 9 flat constructors with `identity | pointwise : PointwiseFn → Nonlin | axiswise : AxiswiseFn → Option BoolExpr → Nonlin`, so no match site can misclassify a nonlinearity or silently swallow a mask — collapsing ~11 match sites and deleting two in-code hazard warnings. (3b) Replace ~16 copy-pasted Syntax/Elab productions with typed keyword-table generators and extract a repeated `identStr` helper. Surface syntax unchanged.

**What this spike does and does NOT establish (the four "closure" guarantees):**
- ✅ **Representation closure** for `Nonlin`: each nonlinearity's category is encoded in the constructor; every match is exhaustive with no semantic wildcard.
- ◐ **Boundary validity** (partial): keyword/mask *shape* is enforced by the grammar (3b), and non-identity scatter is rejected (Task 0). NOT: norm-axis resolution (still recomputed at eval — that's E2/light-typestate, a later stage), NOT ACSet tag decoding.
- ✗ **Semantic closure**: NOT established. `BrBaseP` still has no field for the softmax mask, the `UnaryOp`, `ScatterOpts`, or dtype — so routed lowering can still drop payload. Grouping prevents *misclassification*; it does not manufacture a new function's evaluator/target/codec semantics. A new `AxiswiseFn` still needs all of those.
- ✗ **Proof validity** beyond the migrated traversal/fusion certificates. This spike does not touch `weave_unique`, the flagship graded instance, or the categorical interfaces.

The completion report (Task 4) must state these limits explicitly — do not claim "a new nonlinearity automatically flows through every site," and do not claim general boundary/semantic closure.

**Architecture:** `Nonlin` lives in `DSL/Ast.lean`. Changing its constructors is **atomic** — every match site breaks until migrated — but the blast radius is contained: **RouteSpec has zero `op` projections** (Spike 6a moved the `Nonlin→BrOp` mapping into `ScanStmt.toBrBaseP`, and `buildStep_ok_eq`'s six projections cover the other five `BrBaseP` fields, not `op`), and **Bridge/AcsetCodec are Nonlin-free** (they see only `BrOp`, which stays flat). So 3a is confined to: 3 functional 9→3 collapses (`Nonlin.traverseAxes`, the `op` mapping, `applyNonlin`), 2 eval axis-resolution sites, 1 elab construction site, ~5 Structural fusion proofs, and 2 test proof-reference files. 3b then tables the parser/elab; its nonlin table couples to 3a's new `Nonlin`, so 3a lands before 3b-nonlin.

**Tech Stack:** Lean 4 (toolchain per `lean-toolchain`), mathlib `v4.30.0`, `lake` build.

## Prerequisite / base

Branch from `main` (Spike 6a merged; baseline `lake build` green at 8609 jobs). Order: **Task 0 → Task 1 → (Task 2 any time) → Task 3 → Task 4**. Task 0 must land before Task 1 so the refactor doesn't "look closed while a whole statement constructor still erases the nonlinearity."

## Scope note — out of this spike (do NOT fold in)

The analysis also documents unsized-scan panics, `recurMorphism` accept-then-fail, CSV/ACSet meaning-changing defaults, and `ResolvedNonlin`+checked-`NormAxis`. These are real but are **separate roadmap stages** (light typestate = Stage 4, bridge hardening = Stage 5) with their own fixes; freezing them here would just red the build. Keep Task 0 focused on the **scatter** policy (the one entangled with the Nonlin type). Flag the rest for the doc-level reprioritization, not this plan.

## Global Constraints

- **Behavior preserved (Tasks 1–3); one intended behavioral change (Task 0: non-identity scatter now rejected).** For 3a the new 3-arm matches must be semantically identical to the 9-arm ones (`.relu` ↔ `.pointwise .relu`; `.softmax m` ↔ `.axiswise .softmax m`). The two in-code hazard comments (`specsNonlin` docstring `Structural.lean:29-35`; `evalPlain` pointwise-must-be-explicit `Eval/Eval.lean:30-34`) are deleted — their hazard becomes unrepresentable. DSL-surface tests (FF5–FF8, EvalExamplesTest masked attention, NonlinTest, CompileExamplesTest) are insulated (macro/tensor-fns, not `Nonlin` constructors) — their passing is the behavior check.
- **6a insulation (verified — do not re-touch):** `RouteSpec.lean` must remain unchanged by 3a (never projects `.op`); `LeanNCD/Bridge/*`, `AcsetCodec.lean`, `Csv.lean` must remain unchanged (Nonlin-free — `Csv.lean`'s `.softmax`/`.normalize` are on `OpTag`, a different enum). If a 3a edit forces a change in any, STOP — the insulation assumption was wrong.
- **`BrOp` stays flat.** Only the `Nonlin→BrOp` mapping changes, into `PointwiseFn.toBrOp`/`AxiswiseFn.toBrOp`. `BrOp`, `brOpIdx`/`brOpOfIdx`, `BrOp.toString` untouched.
- **Derives preserved.** New `Nonlin`, `PointwiseFn`, `AxiswiseFn` derive `DecidableEq, Repr, Lean.ToExpr, Inhabited`. `Nonlin`'s `Inhabited` default stays `.identity` (first constructor).
- **Equivalence certs stay independent.** The permanent references in `TraverseAxesEquiv.lean`/`TraverseAxesSpike.lean` must be **hand-written** to reconstruct the 3-arm behavior directly (preserving the mask), NOT rewritten to delegate to `Nonlin.traverseAxes`/`mapUID`. A reference that calls production makes the equivalence tautological; it must still be able to catch a production traversal that drops the mask.
- **Verification gate (every task):** `lake build` from `leanncd/` succeeds. Baseline green: "Build completed successfully (8609 jobs)", 2 expected padded-access warnings. **Stay sorry-free**; add no `set_option maxHeartbeats`/`native_decide`. A stuck proof means fix the approach (or use `lean:prove`/`lean4:proof-repair`), not escalate limits.
- **Commit trailer:** end each commit body with `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`. Don't push/PR unless asked. Re-grep before editing — line numbers shift.

## File Structure

- `DSL/Ast.lean` — `PointwiseFn`, `AxiswiseFn`; restructured `Nonlin`.
- `DSL/TraverseAxes.lean`, `DSL/Pipeline/Structural.lean`, `DSL/Pipeline/Lowering.lean`, `Eval/Nonlin.lean`, `Eval/Eval.lean`, `Eval/Scan.lean`, `DSL/Elab.lean` — migrate match sites (3a).
- `test/DSL/TraverseAxesSpike.lean`, `test/DSL/TraverseAxesEquiv.lean`, `test/DSL/Pipeline/LoweringTest.lean`, `test/DSL/Pipeline/StructuralTest.lean`, `test/DSL/ParseLayer34Test.lean`, `test/Eval/ScanTest.lean`, `test/Eval/PropertyOracle/ScanGen.lean` — `Nonlin` constructors + reference proofs (3a).
- `DSL/Syntax.lean`, `DSL/Elab.lean` — keyword tables + `identStr` (3b).
- Task 0: a `CompileError` constructor + a Structural validation check + a defensive `evalScatter` check + a new regression test.

---

### Task 0: Stage 0 — reject non-identity scatter (freeze the silent-erasure bug)

**Why (verified on `main`):** `splitStmt` passes `.scatter` through unchanged (`Lowering.lean:44`), and `evalScatter` (`Eval/Scatter.lean:15-50`) evaluates `rhs.body` but **never applies `rhs.nonlin`** — the "scatters carry no nonlinearity" claim is only a comment (`Lowering.lean:30,44`). So `Out[2*i] := relu(X[i])` compiles and evaluates with the `relu` silently dropped (analysis: `relu(-2)` returns `-2`). Policy (chosen): `scatter + identity` accepted; `scatter + non-identity` **rejected during validation**. Supporting it later needs a semantic decision (activation before collision-reduction vs after) — out of scope now.

**Files:** `LeanNCD/Exec/*` or wherever `CompileError` lives (add a constructor); `DSL/Pipeline/Structural.lean` (validation check); `DSL/Pipeline/Lowering.lean` (policy comment) and/or `Eval/Scatter.lean` (defensive check); a new/existing test file.

- [ ] **Step 1: Locate `CompileError` and add a constructor** (e.g. `unsupportedNonlinScatter (name : String)`), or reuse `shapeMismatch` with a clear message if adding a constructor ripples too far (grep `inductive CompileError`; check `brOpIdx`-style exhaustive matches on it). Prefer a named constructor.

- [ ] **Step 2: Reject in validation.** In the Structural validation phase (alongside `checkReadRanks`/`checkDtypes`, which run before `Lowering`/`splitStmt`), add a check that throws `unsupportedNonlinScatter nm` for any `.scatter nm _ r _` with `r.nonlin ≠ .identity`. Write the policy in a comment at the check and at `splitStmt`'s `.scatter` arm (`Lowering.lean:44`).

- [ ] **Step 3: Defensive evaluator check.** In `evalScatter` (`Eval/Scatter.lean`), throw an `EvalError` (not a panic) if `rhs.nonlin ≠ .identity` — programmatic callers can build AST without the surface compiler. (This is belt-and-suspenders; validation is the primary gate.)

- [ ] **Step 4: Regression tests.** Add to a test file (e.g. a new `test/Eval/Portfolio/ScatterNonlinRejectTest.lean`, and register it in `lakefile.toml` `Tests` globs): (a) a program `Out[2*i] := relu(X[i])` whose `compile` (or `eval`) returns the rejection error — NOT a value; (b) confirm an identity scatter still compiles/evaluates. Assert on the specific error, not just "is error".

- [ ] **Step 5: Build gate**

Run: `lake build`
Expected: PASS. Existing `ScatterTest` uses only identity nonlin (survey-confirmed) so it's unaffected; the new test's reject path is green.

- [ ] **Step 6: Commit** (separate from 3a, so the behavioral policy is reviewable on its own)

```bash
git add LeanNCD/ test/ lakefile.toml
git commit -m "fix(spike3-stage0): reject non-identity scatter (was silently dropping the nonlinearity)"
```

---

### Task 1: 3a — restructure `Nonlin` into `identity | pointwise | axiswise`

Atomic AST change. Build is red until every site migrates; `lake build LeanNCD.DSL.Ast` first, then let compiler errors drive you file-by-file against this list.

**Files:** `DSL/Ast.lean`, `DSL/TraverseAxes.lean`, `DSL/Pipeline/Structural.lean`, `DSL/Pipeline/Lowering.lean`, `Eval/Nonlin.lean`, `Eval/Eval.lean`, `Eval/Scan.lean`, `DSL/Elab.lean`, + the 7 test files.

**Interfaces:**
- Produces: `inductive PointwiseFn | relu | sigmoid | tanh | gelu | leakyrelu`, `inductive AxiswiseFn | softmax | normalize | l2normalize`, restructured `Nonlin`, `PointwiseFn.toBrOp`/`AxiswiseFn.toBrOp : … → BrOp`, and `PointwiseFn.apply : PointwiseFn → DenseTensor → DenseTensor` (owned by the enum, per the analysis).

- [ ] **Step 1: Define the new types in `Ast.lean`** (replacing old `Nonlin` at `:66-76`)

```lean
inductive PointwiseFn | relu | sigmoid | tanh | gelu | leakyrelu
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- Axis-reducing nonlinearities (softmax/normalize act along ONE designated axis of an
    arbitrary-rank tensor — "axiswise", not intrinsically a matrix row). -/
inductive AxiswiseFn | softmax | normalize | l2normalize
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- A step's nonlinearity. `pointwise` fns carry no mask (by type — a new one *cannot* forget
    mask handling); `axiswise` fns carry the reduction mask once. -/
inductive Nonlin
  | identity
  | pointwise : PointwiseFn → Nonlin
  | axiswise  : AxiswiseFn → Option BoolExpr → Nonlin
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited
```

(`BoolExpr` is at `Ast.lean:58-64`, before `Nonlin`.)

- [ ] **Step 2: Build Ast alone.** `lake build LeanNCD.DSL.Ast` → PASS. Then `lake build` and use the error list to drive Steps 3–8.

- [ ] **Step 3: `Nonlin.traverseAxes`** (`TraverseAxes.lean:80-89`) → 3 arms

```lean
def Nonlin.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : Nonlin → f Nonlin
  | .identity      => pure .identity
  | .pointwise pf  => pure (.pointwise pf)
  | .axiswise fn m => Nonlin.axiswise fn <$> Traversable.traverse (BoolExpr.traverseAxes g) m
```

(`specsNonlin` `Structural.lean:56-57` delegates to this — body unchanged; delete its stale hazard docstring `Structural.lean:29-35` in Step 7.)

- [ ] **Step 4: The `op` mapping** (`Lowering.lean:475-494`, inside `ScanStmt.toBrBaseP`) → 3 arms + two tables

```lean
def PointwiseFn.toBrOp : PointwiseFn → BrOp
  | .relu => .relu | .sigmoid => .sigmoid | .tanh => .tanh | .gelu => .gelu | .leakyrelu => .leakyrelu
def AxiswiseFn.toBrOp : AxiswiseFn → BrOp
  | .softmax => .softmax | .normalize => .normalize | .l2normalize => .l2normalize
```

```lean
    else match s.nonlinOf with
      | .pointwise pf  => pf.toBrOp
      | .axiswise fn _ => fn.toBrOp
      | .identity      => match s with
          | .scatter .. => .scatter   -- (post-Task-0, scatter nonlin is always identity)
          | .assign ..  => match s.agg with | .max => .maxreduce | .min => .minreduce | .sum => .contract
          | .recurMorphism .. => .contract   -- unreachable: scanPre handled above
```

**6a check:** after this edit, `lake build LeanNCD.DSL.Pipeline.RouteSpec` must pass with **no RouteSpec edit**. If RouteSpec breaks, STOP and report.

- [ ] **Step 5: `applyNonlin`** (`Eval/Nonlin.lean:97-108`) → 3 top-level arms; own the pointwise dispatch on the enum

```lean
def PointwiseFn.apply : PointwiseFn → DenseTensor → DenseTensor
  | .relu => reluT | .sigmoid => sigmoidT | .tanh => tanhT | .gelu => geluT | .leakyrelu => leakyReluT

def applyNonlin (nl : Nonlin) (axisPos : Nat) (axisUids : List UID) (t : DenseTensor) : DenseTensor :=
  match nl with
  | .identity      => t
  | .pointwise pf  => pf.apply t
  | .axiswise fn m => match fn with
      | .softmax => softmaxT axisPos axisUids m t | .normalize => normalizeT axisPos axisUids m t | .l2normalize => l2normalizeT axisPos axisUids m t
```

- [ ] **Step 6: The two eval axis-resolution sites** → exhaustive 3-arm, no wildcard, delete hazard comment

`evalPlain` (`Eval/Eval.lean:30-42`): delete the 5-line hazard comment; rewrite the `axisPos` match:

```lean
        let axisPos ← match rhs.nonlin, normAxisUidOf slots with
          | .identity, _         => pure 0
          | .pointwise _, _      => pure 0
          | .axiswise _ _, some nu => match axisUids.findIdx? (· == nu) with
              | some p => pure p
              | none   => throw s!"evalPlain: marked norm axis of {nm} is not among its output axes"
          | .axiswise _ _, none    => throw s!"evalPlain: {nm} applies softmax/normalize but no output axis is marked (·)"
```

`evalStmtSliceSeeded` (`Eval/Scan.lean:42-49`): analogous rewrite (identity+pointwise → non-axiswise behavior; axiswise → mask/norm-axis behavior). Read the current arms and map 1:1.

- [ ] **Step 7: `elabTLNonlin`** (`Elab.lean:142-154`) → new constructors (keep 11 arms for now; Task 3 tables it)

`.relu` → `.pointwise .relu` (×5); `.softmax none` → `.axiswise .softmax none`, `.softmax (some (← elabTLBoolExpr b))` → `.axiswise .softmax (some (← elabTLBoolExpr b))` (×3, bare + masked). Do NOT change syntax productions here. Also delete the stale hazard docstring (`Structural.lean:29-35`) and confirm no other prose references the old wildcard hazard.

- [ ] **Step 8: Repair the fusion proofs + update test references (keep certs INDEPENDENT)**

**Structural fusion proofs (`Structural.lean:273-275, 468-471, 499-500, 508-509, 560-563`** — `nonlinAxisUidFusion`, `specsNonlin_map_uid_eq`, `hNonlin`): rewrite each `.softmax (some m) => boolAxisUIDs m | … | _ => []` reference to `.axiswise _ (some m) => boolAxisUIDs m | _ => []`; repair the proof (`cases`/`rcases` on `Nonlin` is now 3-way; `.axiswise` splits on the mask `Option`). Drive with `lean_goal`/`lean_multi_attempt`.

**Test proof-reference certs — rewrite the reference to 3 arms AND keep it hand-written (must still catch a mask-dropping production):**
- `test/DSL/TraverseAxesSpike.lean:273-281` — `specsNonlin'` (exhaustive) + `traverseAxes_const_eq_specsNonlin`. Rewrite `specsNonlin'` to `.axiswise _ (some m) => specsBool m | _ => []` (hand-written, not `= specsNonlin`); repair.
- `test/DSL/TraverseAxesEquiv.lean:116-158` — `Nonlin.mapUID_ref` + `Nonlin.mapUID_eq_ref`. Rewrite `mapUID_ref` to `.identity | .pointwise pf => .pointwise pf | .axiswise fn m => .axiswise fn (m.map …)` — reconstruct the mask remap **by hand** (do NOT define it as `Nonlin.mapUID`); repair the `show`/`rfl` steps.

**Test constructor updates (mechanical — `.relu`→`.pointwise .relu`, `.softmax m`→`.axiswise .softmax m`, in construction and `match`):** `LoweringTest.lean:12,22,119`; `StructuralTest.lean:97,251,262`; `ParseLayer34Test.lean:12,26,31`; `ScanTest.lean:32`; `ScanGen.lean:62`. (`== Nonlin.identity` and `nonlin := .identity` UNCHANGED.)

- [ ] **Step 9: Build gate + sorry/axiom check**

Run: `lake build` → PASS (8609 jobs). Confirms NonlinTest, FF5–FF8, LoweringTest masked-softmax, EvalExamplesTest masked attention, the fusion proofs, and the two certs hold.
Run: `rg -n "sorry|admit|native_decide|maxHeartbeats" LeanNCD/DSL LeanNCD/Eval test/DSL` — none introduced. Spot-check `#print axioms Nonlin.mapUID_eq_ref` (`lean_verify`) → `[propext, Quot.sound]` or fewer.

- [ ] **Step 10: Commit**

```bash
git add LeanNCD/DSL/Ast.lean LeanNCD/DSL/TraverseAxes.lean LeanNCD/DSL/Pipeline/Structural.lean LeanNCD/DSL/Pipeline/Lowering.lean LeanNCD/Eval/Nonlin.lean LeanNCD/Eval/Eval.lean LeanNCD/Eval/Scan.lean LeanNCD/DSL/Elab.lean test/
git commit -m "refactor(spike3a): split Nonlin into identity|pointwise|axiswise; delete wildcard hazards"
```

---

### Task 2: 3b — `tl_unary_kw` table + `identStr` helper (independent of Tasks 0–1)

Pure syntax/elab refactor; no `Nonlin` dependency — can run any time.

**Files:** `DSL/Elab.lean`, `DSL/Syntax.lean`.

- [ ] **Step 1: Extract `identStr`** — replace all **23** `x.getId.eraseMacroScopes.getString!` in `Elab.lean` (lines 20,39,44,49,52,58,60,97,99,158,161,163,165,167,169,177,224,226,230,233,235,237,248) with:

```lean
private def identStr (x : Lean.Syntax) : String := x.getId.eraseMacroScopes.getString!
```

Place near the top (after imports/`open`). Verify each call site's receiver is an `ident`.

- [ ] **Step 2: `tl_unary_kw` category** — in `Syntax.lean`, replace the 5 `tl_factor` productions (`:121-127`) with:

```lean
declare_syntax_cat tl_unary_kw
syntax "log" : tl_unary_kw
syntax "exp" : tl_unary_kw
syntax "sin" : tl_unary_kw
syntax "cos" : tl_unary_kw
syntax "sqrt" : tl_unary_kw
syntax tl_unary_kw "(" ident "[" tl_idx_expr,* "]" ")" : tl_factor
```

(Leave `recip`/`/` sugar — `Syntax.lean:135`, `Elab.lean:176-178` — alone.)

- [ ] **Step 3: One unary elab arm with a keyword→`UnaryOp` mapping** — replace the 5 arms (`:160-169`):

```lean
  | `(tl_factor| $kw:tl_unary_kw ( $nm:ident [ $idxs,* ] )) => do
      let op ← match kw with
        | `(tl_unary_kw| log) => pure .log | `(tl_unary_kw| exp) => pure .exp | `(tl_unary_kw| sin) => pure .sin
        | `(tl_unary_kw| cos) => pure .cos | `(tl_unary_kw| sqrt) => pure .sqrt
        | _ => throwErrorAt kw "unknown unary function"
      return .unaryFn op (identStr nm) (← idxs.getElems.toList.mapM elabTLIdxExpr)
```

(Per-keyword `` `(tl_unary_kw| log) `` match avoids stringly-typed lookup; if you prefer a `String→UnaryOp` table via an atom accessor, that's fine too — but no wildcard-to-a-default. Do not reintroduce 5 `tl_factor` productions.)

- [ ] **Step 4: Add a minimal unary parse guard** (no test exercises log/exp/sin/cos/sqrt today, so a green build alone would NOT catch a table regression). Add to `test/DSL/SyntaxTest.lean` (or `ParseExamplesTest.lean`) a `#check`/`tlprog!` parsing `Y[i] := log(P[i])`, ideally asserting the built `Factor.unaryFn .log …`.

- [ ] **Step 5: Build gate.** `lake build` → PASS. Confirms ParseLayer34Test/ParseExamplesTest/SyntaxTest/CompileExamplesTest.

- [ ] **Step 6: Commit**

```bash
git add LeanNCD/DSL/Syntax.lean LeanNCD/DSL/Elab.lean test/DSL/SyntaxTest.lean
git commit -m "refactor(spike3b): tl_unary_kw table + identStr helper (23 sites)"
```

---

### Task 3: 3b — two closed nonlin keyword categories (depends on Task 1)

Refactor the nonlin grammar into **two closed categories** so `relu(where…)` is unrepresentable at parse (not just rejected in elaboration), and collapse the 11-arm `elabTLNonlin` into two arms producing 3a's `Nonlin`.

**Design decision (recorded):** two closed categories `tl_pointwise_kw` / `tl_axiswise_kw` — only axiswise admits a `(where …)` mask. Trade-off: `relu(where…)` becomes a *parse* error (blunter message) rather than a tailored "relu takes no mask" elaboration error. **Fallback** if the diagnostic matters more than the type-cleanliness: keep one `tl_nonlin_kw` category with the mask production, and have the elab classifier return `Except`/`Option` with **no default**, rejecting a pointwise+mask in elaboration. Either way: no keyword may map through a fallback constructor.

**Files:** `DSL/Syntax.lean`, `DSL/Elab.lean`.

- [ ] **Step 1: Two closed categories** — in `Syntax.lean`, replace the 11 productions (`:143-153`), **preserving the `atomic("(" "where")` lookahead verbatim** on the axiswise production (the sole `softmax(sum)` vs `softmax(where …)` disambiguator):

```lean
declare_syntax_cat tl_pointwise_kw
syntax "relu"      : tl_pointwise_kw
syntax "sigmoid"   : tl_pointwise_kw
syntax "tanh"      : tl_pointwise_kw
syntax "gelu"      : tl_pointwise_kw
syntax "leakyrelu" : tl_pointwise_kw

declare_syntax_cat tl_axiswise_kw
syntax "softmax"     : tl_axiswise_kw
syntax "normalize"   : tl_axiswise_kw
syntax "l2normalize" : tl_axiswise_kw

syntax tl_pointwise_kw : tl_nonlin
syntax tl_axiswise_kw (atomic("(" "where") tl_bool_expr ")")? : tl_nonlin
```

Both feed the existing `tl_nonlin` category, so `tl_rhs`'s `syntax tl_nonlin "(" tl_sum_expr ")"` (`Syntax.lean:159`) still composes — **verify this** (a bare pointwise/axiswise keyword followed by `(sum)` must still parse). Keep/adjust the left-factoring comment (`:140-142`).

- [ ] **Step 2: Two `elabTLNonlin` arms**

```lean
partial def elabTLNonlin : Syntax → MetaM Nonlin
  | `(tl_nonlin| $kw:tl_pointwise_kw) => do
      match kw with
      | `(tl_pointwise_kw| relu) => return .pointwise .relu
      | `(tl_pointwise_kw| sigmoid) => return .pointwise .sigmoid
      | `(tl_pointwise_kw| tanh) => return .pointwise .tanh
      | `(tl_pointwise_kw| gelu) => return .pointwise .gelu
      | `(tl_pointwise_kw| leakyrelu) => return .pointwise .leakyrelu
      | _ => throwUnsupportedSyntax
  | `(tl_nonlin| $kw:tl_axiswise_kw $[( where $b )]?) => do
      let mask? ← b.mapM elabTLBoolExpr
      match kw with
      | `(tl_axiswise_kw| softmax) => return .axiswise .softmax mask?
      | `(tl_axiswise_kw| normalize) => return .axiswise .normalize mask?
      | `(tl_axiswise_kw| l2normalize) => return .axiswise .l2normalize mask?
      | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax
```

(No pointwise+mask arm exists — the grammar makes it unrepresentable. If you took the shared-category fallback instead, this is where the `Except` reject lives.)

- [ ] **Step 3: Verify disambiguation + the three test levels** (the load-bearing check)

Run `lake build`, then confirm `ParseLayer34Test` + `CompileExamplesTest`:
1. **Parser shape:** unmasked `softmax(A[i] + B[i])` → `.axiswise .softmax none` with two sum terms (the `atomic` left-factoring); masked `softmax(where s ≤ q)(…)` → `.axiswise .softmax (some _)`. If `softmax(sum)` misparses, the `atomic(...)` was altered — fix first.
2. **Elaboration:** every keyword maps to the expected enum; masks retained.
3. **Negative:** add a test that `relu(where …)` is rejected (with two categories this is a parse failure — assert it does not elaborate; document that the message is a parse error, or switch to the fallback design for a tailored message).

- [ ] **Step 4: Commit**

```bash
git add LeanNCD/DSL/Syntax.lean LeanNCD/DSL/Elab.lean test/DSL/ParseLayer34Test.lean
git commit -m "refactor(spike3b): two closed nonlin keyword categories; relu(where) unrepresentable"
```

---

### Task 4: Mark Spike 3 done in `restructure_suggestions.md` — with an HONEST completion statement

**Files:** `papers/restructure_suggestions.md`

- [ ] **Step 1:** Prepend `✅ **DONE.**` to the 3a/3b leads (`:329`, `:359`); mark them in the ordering diagrams (`:657`, `:762`). Record the actuals AND the limits, verbatim intent:
  - Naming: `AxiswiseFn` (not `RowwiseFn`); `identStr` was **23** sites; the two tables are `PointwiseFn.toBrOp`/`AxiswiseFn.toBrOp`; RouteSpec insulation held (zero op-mapping repair — the 6a payoff).
  - Task 0: non-identity scatter is now rejected (a real silent-erasure bug, per the code analysis).
  - **Honest scope statement (required):** "Spike 3 establishes **representation closure** for `Nonlin` and source-keyword/mask shape validity; it does **not** establish semantic closure — `BrBaseP` still carries no mask/`UnaryOp`/`ScatterOpts`/dtype payload (routed lowering can drop it) — nor does it repair the categorical proof gaps (`weave_unique`, the flagship graded instance). ACSet operation-tag decoding remains outside the validated boundary until bridge hardening."
- [ ] **Step 2:** Commit `docs(spike3): mark 3a/3b done; record scatter-reject + honest representation-closure-only scope`.

---

### Task 5 (deferred, not in this spike): 3c — merge `Factor.unaryFn` into `Factor.read`

**Keep deferred — with a sharper reason than "evaluate if it pays."** The urgent question isn't duplication; it's that **`BrBaseP` has no field for the `UnaryOp`** — an inline `log(X[i])` and a plain `X[i]` lower to the *same* `BrBaseP` (same read name + reindexing). So the `UnaryOp` is already erased at the bridge. Merging the source constructor before that is designed (the **semantic payload audit**, roadmap Stage 3) would make the loss *less visible*, not fix it. Do 3c only after `UnaryOp` has a preservation-or-explicit-rejection design.

---

## Self-Review

**Spec coverage (against §3 + the code analysis's Spike 3 assessment):**
- Nonlinear-scatter silent erasure (analysis finding #3, verified on `main`) → **Task 0**. ✅
- 3a restructure + 11 sites + delete both hazard comments → Task 1. ✅ (`AxiswiseFn` per decision; `PointwiseFn.apply` added.)
- `BrOp` flat + two `toBrOp` tables + RouteSpec-insulation budget ≈ 0 → Task 1 Step 4. ✅
- Certs stay independent (analysis's explicit warning) → Task 1 Step 8 + Global Constraint. ✅
- 3b typed categories so `relu(where…)` fails at the language boundary → Task 3 (two closed categories, fallback documented). ✅
- `identStr` (23) + `tl_unary_kw` → Task 2. ✅
- Narrowed completion claim (representation closure only; semantic closure NOT established) → the "four guarantees" section + Task 4's honest statement. ✅
- 3c deferred with the `UnaryOp`-erasure reason → Task 5. ✅

**Placeholder scan:** none — the per-keyword antiquotation matches in Tasks 2–3 are concrete (the earlier `<keyword string>` markers are gone).

**Type consistency:** `PointwiseFn`/`AxiswiseFn`/`Nonlin` (Task 1) consumed identically in traverseAxes/applyNonlin/op-mapping/eval/elab and Task 3's two elab arms; `PointwiseFn.toBrOp`/`AxiswiseFn.toBrOp : … → BrOp`; `PointwiseFn.apply : PointwiseFn → DenseTensor → DenseTensor`; `identStr : Syntax → String`.

**Residual risk / assumptions to verify at execution:**
- Task 0's reject must land before Task 1 (else 3a "looks closed" over the bug). Its policy comment must state the reject is a Spike-3 short-term decision, not a permanent one.
- Task 1 is atomic; the survey site list is the completeness check. If an unlisted site breaks, migrate identity/pointwise/axiswise the same way and note it.
- 6a insulation (no RouteSpec/Bridge/Codec edit) — verify at Task 1 Step 4; STOP if any must change.
- Task 3: preserve the `atomic("(" "where")` lookahead char-for-char and verify `tl_rhs`'s `tl_nonlin "(" tl_sum_expr ")"` still composes over the two new sub-categories; `ParseLayer34Test` is the guard.
- Out of scope (do NOT fold in): unsized-scan panic, `recurMorphism` accept-then-fail, CSV/ACSet defaults, `ResolvedNonlin`/`NormAxis` — separate roadmap stages.

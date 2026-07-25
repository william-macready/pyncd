# Spike 3 — make Nonlin wildcard hazards unrepresentable + Elab/Syntax tables Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox (`- [ ]`). Task 1 is a **Lean AST type change** (proof repair involved — drive with `lean4`/`lean:prove` tooling); Tasks 2–3 are **Lean metaprogramming** (syntax/elab). Verify with `lake build`.

**Goal:** (3a) Replace `Nonlin`'s 9 flat constructors with a structurally-exhaustive `identity | pointwise : PointwiseFn → Nonlin | rowwise : RowwiseFn → Option BoolExpr → Nonlin` split, so no match site can forget the pointwise-vs-rowwise distinction or silently swallow a mask (two real bugs this cycle) — collapsing ~11 match sites and deleting two in-code hazard warnings. (3b) Replace ~16 copy-pasted Syntax/Elab productions with two keyword-table generators and extract a repeated `identStr` helper. Surface syntax unchanged.

**Architecture:** `Nonlin` lives in `DSL/Ast.lean`. Changing its constructors is an **atomic** edit — every match site breaks until migrated — but the survey confirms the blast radius is contained: **RouteSpec has zero `op` projections** (Spike 6a moved the `Nonlin→BrOp` mapping into `ScanStmt.toBrBaseP`, and `buildStep_ok_eq`'s six projections cover the other five `BrBaseP` fields, not `op`), and **Bridge/AcsetCodec are Nonlin-free** (they see only `BrOp`, which stays flat). So the change is confined to: 3 functional 9→3 collapses (`Nonlin.traverseAxes`, the `op` mapping, `applyNonlin`), 2 eval axis-resolution sites, 1 elab construction site, ~5 Structural fusion proofs, and 2 test proof-reference files. 3b then tables the parser/elab; its nonlin table couples to 3a's new `Nonlin` shape, so 3a lands first.

**Tech Stack:** Lean 4 (toolchain per `lean-toolchain`), mathlib `v4.30.0`, `lake` build.

## Prerequisite / base

Branch from `main` (Spike 6a merged — its insulation is what makes 3a's `buildStep`/`op` touch cheap; baseline `lake build` green at 8609 jobs). 3a should precede 3b-nonlin (Task 3).

## Global Constraints

- **Surface syntax unchanged; behavior preserved.** The new 3-arm matches must be semantically identical to the 9-arm ones (`.relu` ↔ `.pointwise .relu`; `.softmax m` ↔ `.rowwise .softmax m`; etc.). The two in-code hazard comments (`specsNonlin`'s 8-line module docstring at `Structural.lean:29-35`; the `evalPlain` pointwise-must-be-explicit comment at `Eval/Eval.lean:30-34`) are **deleted** — their hazard becomes unrepresentable by construction. The DSL-surface tests (FF5–FF8 unmarked activations, EvalExamplesTest masked attention, NonlinTest, CompileExamplesTest) are **insulated** (they go through the macro/tensor-fns, not `Nonlin` constructors) — their passing is the end-to-end behavior check.
- **6a insulation (verified — do not re-touch these):** `RouteSpec.lean` must remain unchanged by 3a (it never projects `.op`); `LeanNCD/Bridge/*` and `AcsetCodec.lean`/`Csv.lean` must remain unchanged (Nonlin-free — `Csv.lean`'s `.softmax`/`.normalize` matches are on `OpTag`, a *different* enum). If a 3a edit forces a change in any of these, STOP — the insulation assumption was wrong.
- **`BrOp` stays flat.** Only the `Nonlin→BrOp` *mapping* changes (into two tiny `PointwiseFn.toBrOp`/`RowwiseFn.toBrOp` tables). `BrOp`, `brOpIdx`/`brOpOfIdx`, `BrOp.toString` are untouched.
- **Derives preserved.** New `Nonlin` (and new `PointwiseFn`/`RowwiseFn`) must derive `DecidableEq, Repr, Lean.ToExpr, Inhabited`. `Nonlin`'s `Inhabited` default stays `.identity` (first constructor) — several `nonlin := .identity` literals and `default` uses depend on it.
- **Verification gate (every task):** `lake build` from `leanncd/` completes successfully (elaborates `LeanNCD` + `Tests`). Baseline green: "Build completed successfully (8609 jobs)", 2 expected padded-access warning kinds only. **Stay sorry-free** (baseline has zero `sorry` in every involved file) and add no `set_option maxHeartbeats`/`native_decide`. A stuck proof means fix the approach (or use `lean:prove`/`lean4:proof-repair`), not escalate limits.
- **Commit trailer:** end each commit body with `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`. Don't push/PR unless asked. Re-grep before editing — survey line numbers shift.

## File Structure

- `DSL/Ast.lean` — add `PointwiseFn`, `RowwiseFn`; restructure `Nonlin`.
- `DSL/TraverseAxes.lean`, `DSL/Pipeline/Structural.lean`, `DSL/Pipeline/Lowering.lean`, `Eval/Nonlin.lean`, `Eval/Eval.lean`, `Eval/Scan.lean`, `DSL/Elab.lean` — migrate match sites (3a).
- `test/DSL/TraverseAxesSpike.lean`, `test/DSL/TraverseAxesEquiv.lean`, `test/DSL/Pipeline/LoweringTest.lean`, `test/DSL/Pipeline/StructuralTest.lean`, `test/DSL/ParseLayer34Test.lean`, `test/Eval/ScanTest.lean`, `test/Eval/PropertyOracle/ScanGen.lean` — update `Nonlin` constructors + reference proofs (3a).
- `DSL/Syntax.lean`, `DSL/Elab.lean` — keyword tables + `identStr` (3b).

---

### Task 1: 3a — restructure `Nonlin` into `identity | pointwise | rowwise`

Atomic AST change. The build is red until every site below is migrated; use `lake build LeanNCD.DSL.Ast` first, then let the compiler errors drive you file-by-file, checking each site against this list so none is missed.

**Files:** `DSL/Ast.lean`, `DSL/TraverseAxes.lean`, `DSL/Pipeline/Structural.lean`, `DSL/Pipeline/Lowering.lean`, `Eval/Nonlin.lean`, `Eval/Eval.lean`, `Eval/Scan.lean`, `DSL/Elab.lean`, and the 7 test files above.

**Interfaces:**
- Produces: `inductive PointwiseFn | relu | sigmoid | tanh | gelu | leakyrelu`, `inductive RowwiseFn | softmax | normalize | l2normalize`, restructured `Nonlin`, and `PointwiseFn.toBrOp : PointwiseFn → BrOp`, `RowwiseFn.toBrOp : RowwiseFn → BrOp` (the "two tiny tables").

- [ ] **Step 1: Define the new types in `Ast.lean`** (replacing the old `Nonlin` at `:66-76`)

```lean
inductive PointwiseFn | relu | sigmoid | tanh | gelu | leakyrelu
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

inductive RowwiseFn | softmax | normalize | l2normalize
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- A step's nonlinearity. `pointwise` fns carry no mask (by type — a new one *cannot* forget mask
    handling); `rowwise` fns carry the softmax/normalize reduction mask once. -/
inductive Nonlin
  | identity
  | pointwise : PointwiseFn → Nonlin
  | rowwise   : RowwiseFn → Option BoolExpr → Nonlin
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited
```

Note: `BoolExpr` is defined at `Ast.lean:58-64`, before `Nonlin` — good. `PointwiseFn`/`RowwiseFn` need no `BoolExpr`, so their order is free.

- [ ] **Step 2: Build Ast alone**

Run: `lake build LeanNCD.DSL.Ast`
Expected: PASS (types + derives elaborate). Then run `lake build` and use the error list to drive Steps 3–8.

- [ ] **Step 3: `Nonlin.traverseAxes`** (`TraverseAxes.lean:80-89`) → 3 arms

```lean
def Nonlin.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : Nonlin → f Nonlin
  | .identity     => pure .identity
  | .pointwise pf => pure (.pointwise pf)
  | .rowwise rf m => Nonlin.rowwise rf <$> Traversable.traverse (BoolExpr.traverseAxes g) m
```

(`specsNonlin` at `Structural.lean:56-57` delegates to this — its body is unchanged, but delete the now-false 8-line hazard docstring at `Structural.lean:29-35` in Step 7.)

- [ ] **Step 4: The `op` mapping** (`Lowering.lean:475-494`, inside `ScanStmt.toBrBaseP`) → 3 arms + two tables

Add the two tables (near `toBrBaseP`, or in `Ast.lean`/`Target.lean` if `BrOp` is in scope there — `BrOp` is in `Target.lean`, imported by Lowering):

```lean
def PointwiseFn.toBrOp : PointwiseFn → BrOp
  | .relu => .relu | .sigmoid => .sigmoid | .tanh => .tanh | .gelu => .gelu | .leakyrelu => .leakyrelu
def RowwiseFn.toBrOp : RowwiseFn → BrOp
  | .softmax => .softmax | .normalize => .normalize | .l2normalize => .l2normalize
```

Then the `else match s.nonlinOf with` block becomes:

```lean
    else match s.nonlinOf with
      | .pointwise pf => pf.toBrOp
      | .rowwise rf _ => rf.toBrOp
      | .identity    => match s with
          | .scatter .. => .scatter
          | .assign ..  => match s.agg with | .max => .maxreduce | .min => .minreduce | .sum => .contract
          | .recurMorphism .. => .contract   -- unreachable: scanPre handled above
```

**6a check:** after this edit, `lake build LeanNCD.DSL.Pipeline.RouteSpec` must still pass with **no RouteSpec edit** (it never projects `.op`). If RouteSpec breaks, STOP and report.

- [ ] **Step 5: `applyNonlin`** (`Eval/Nonlin.lean:97-108`) → 3 top-level arms

```lean
def applyNonlin (nl : Nonlin) (axisPos : Nat) (axisUids : List UID) (t : DenseTensor) : DenseTensor :=
  match nl with
  | .identity     => t
  | .pointwise pf => match pf with
      | .relu => reluT t | .sigmoid => sigmoidT t | .tanh => tanhT t | .gelu => geluT t | .leakyrelu => leakyReluT t
  | .rowwise rf m => match rf with
      | .softmax => softmaxT axisPos axisUids m t | .normalize => normalizeT axisPos axisUids m t | .l2normalize => l2normalizeT axisPos axisUids m t
```

- [ ] **Step 6: The two eval axis-resolution sites** → exhaustive 3-arm, no wildcard, delete hazard comment

`evalPlain` (`Eval/Eval.lean:30-42`): delete the 5-line hazard comment; rewrite the `axisPos` match:

```lean
        let axisPos ← match rhs.nonlin, normAxisUidOf slots with
          | .identity, _      => pure 0
          | .pointwise _, _   => pure 0
          | .rowwise _ _, some nu => match axisUids.findIdx? (· == nu) with
              | some p => pure p
              | none   => throw s!"evalPlain: marked norm axis of {nm} is not among its output axes"
          | .rowwise _ _, none    => throw s!"evalPlain: {nm} applies softmax/normalize but no output axis is marked (·)"
```

`evalStmtSliceSeeded` (`Eval/Scan.lean:42-49`): apply the analogous rewrite (identity+pointwise → the non-rowwise behavior; rowwise → the mask/norm-axis behavior). Preserve its exact current semantics — read the current arms and map 1:1.

- [ ] **Step 7: `elabTLNonlin`** (`Elab.lean:142-154`) → new constructors (keep 11 arms for now; Task 3 tables it)

Each arm now builds the new shape: `.relu` → `.pointwise .relu` (×5 pointwise); `.softmax none` → `.rowwise .softmax none`, `.softmax (some (← elabTLBoolExpr b))` → `.rowwise .softmax (some (← elabTLBoolExpr b))` (×3 rowwise, bare + masked). Do NOT change the syntax productions here.

Also in Step 7, delete the stale hazard docstring (`Structural.lean:29-35`) and confirm no other prose references the old wildcard hazard.

- [ ] **Step 8: Repair the fusion proofs + update test references**

**Structural fusion proofs (`Structural.lean:273-275, 468-471, 499-500, 508-509, 560-563`** — `nonlinAxisUidFusion`, `specsNonlin_map_uid_eq`, `hNonlin`): each enumerates `.softmax (some m) => boolAxisUIDs m | .normalize (some m) => … | .l2normalize (some m) => … | _ => []`. Rewrite the reference match to `.rowwise _ (some m) => boolAxisUIDs m | _ => []` and repair the proof (`cases`/`rcases` on `Nonlin` is now 3-way; the `.rowwise` case splits on the mask `Option`). Drive with `lean_goal`/`lean_multi_attempt`.

**Test proof-reference files (these carry E1's Nonlin equivalence certificates — update the reference match AND repair the proof):**
- `test/DSL/TraverseAxesSpike.lean:273-281` — `specsNonlin'` exhaustive 9-arm match + `traverseAxes_const_eq_specsNonlin`. Rewrite to the 3-arm shape; repair.
- `test/DSL/TraverseAxesEquiv.lean:116-158` — `Nonlin.mapUID_ref` exhaustive 9-arm + `Nonlin.mapUID_eq_ref` (its `.softmax/.normalize/.l2normalize` arms do `show (Nonlin.softmax (some …) : Id Nonlin) = …`). Rewrite to `.identity | .pointwise pf | .rowwise rf m` and repair the `show`/`rfl` steps.

**Test constructor updates (mechanical — `.relu`→`.pointwise .relu`, `.softmax m`→`.rowwise .softmax m`, in both construction and `match`):**
`LoweringTest.lean:12,22,119`; `StructuralTest.lean:97,251,262`; `ParseLayer34Test.lean:12,26,31`; `ScanTest.lean:32`; `ScanGen.lean:62`. (`== Nonlin.identity` sites and `nonlin := .identity` literals are UNCHANGED — `.identity` survives verbatim.)

- [ ] **Step 9: Full build gate + sorry check**

Run: `lake build`
Expected: PASS (8609 jobs). Confirms NonlinTest, FF5–FF8, LoweringTest masked-softmax, EvalExamplesTest masked attention, the fusion proofs, and the two equivalence certificates all hold against the new type.
Run: `rg -n "sorry|admit|native_decide|maxHeartbeats" LeanNCD/DSL LeanNCD/Eval test/DSL` — expect none introduced. Spot-check `#print axioms Nonlin.mapUID_eq_ref` (via `lean_verify`) → `[propext, Quot.sound]` or fewer.

- [ ] **Step 10: Commit**

```bash
git add LeanNCD/DSL/Ast.lean LeanNCD/DSL/TraverseAxes.lean LeanNCD/DSL/Pipeline/Structural.lean LeanNCD/DSL/Pipeline/Lowering.lean LeanNCD/Eval/Nonlin.lean LeanNCD/Eval/Eval.lean LeanNCD/Eval/Scan.lean LeanNCD/DSL/Elab.lean test/
git commit -m "refactor(spike3a): split Nonlin into identity|pointwise|rowwise; delete wildcard hazards"
```

---

### Task 2: 3b — `tl_unary_kw` table + `identStr` helper (independent of 3a)

Pure syntax/elab refactor; no `Nonlin` dependency, so this can run before or after Task 1.

**Files:** `DSL/Elab.lean` (add `identStr`; unary elab arm), `DSL/Syntax.lean` (unary productions).

- [ ] **Step 1: Extract `identStr`** — replace all **23** occurrences of `x.getId.eraseMacroScopes.getString!` in `Elab.lean` (lines 20,39,44,49,52,58,60,97,99,158,161,163,165,167,169,177,224,226,230,233,235,237,248) with a call to a new private helper:

```lean
private def identStr (x : Lean.Syntax) : String := x.getId.eraseMacroScopes.getString!
```

Place it near the top of `Elab.lean` (after the imports/`open`). Verify each call site's receiver is an `ident` `Syntax` (it is at all 23).

- [ ] **Step 2: `tl_unary_kw` category** — in `Syntax.lean`, replace the 5 copy-pasted `tl_factor` productions (`:121-127`, log/exp/sin/cos/sqrt) with one keyword category + one production:

```lean
declare_syntax_cat tl_unary_kw
syntax "log" : tl_unary_kw
syntax "exp" : tl_unary_kw
syntax "sin" : tl_unary_kw
syntax "cos" : tl_unary_kw
syntax "sqrt" : tl_unary_kw
syntax tl_unary_kw "(" ident "[" tl_idx_expr,* "]" ")" : tl_factor
```

(Leave `recip`/`/` sugar — `Syntax.lean:135`, `Elab.lean:176-178` — alone; it has no keyword form.)

- [ ] **Step 3: One unary elab arm with a `String → UnaryOp` table** — in `Elab.lean`, replace the 5 arms (`:160-169`) with one arm over `tl_unary_kw`, mapping the keyword string to `UnaryOp` (fail-loud on an unknown keyword — unreachable, but no wildcard-to-a-default):

```lean
  | `(tl_factor| $kw:tl_unary_kw ( $nm:ident [ $idxs,* ] )) => do
      let op ← match kw.raw.getAtomVal? with  -- or the appropriate token accessor for the kw category
        | "log" => pure .log | "exp" => pure .exp | "sin" => pure .sin | "cos" => pure .cos | "sqrt" => pure .sqrt
        | other => throwErrorAt kw s!"unknown unary function '{other}'"
      return .unaryFn op (identStr nm) (← idxs.getElems.toList.mapM elabTLIdxExpr)
```

The exact token-extraction (`kw.raw.getAtomVal?` vs matching `` `(tl_unary_kw| log) `` per keyword) is an implementation detail to resolve with `lean_hover_info`/`lean_completions` — if extracting the atom string is awkward, a small per-keyword `` `(tl_unary_kw| log) => .log `` match inside the arm is an acceptable fallback (still one `tl_factor` arm, one production). Do not reintroduce 5 `tl_factor` productions.

- [ ] **Step 4: Add a minimal unary parse guard** (coverage gap: no test exercises log/exp/sin/cos/sqrt at the parse layer today, so a green build alone would NOT catch a table regression). Add to `test/DSL/SyntaxTest.lean` (or `ParseExamplesTest.lean`) a `#check`/`tlprog!` that parses `Y[i] := log(P[i])` and (ideally) an example asserting the built `Factor.unaryFn .log …`. Keep it small.

- [ ] **Step 5: Build gate**

Run: `lake build`
Expected: PASS (8609+ jobs; the new test adds a check). Confirms ParseLayer34Test, ParseExamplesTest, SyntaxTest, CompileExamplesTest still parse/elaborate.

- [ ] **Step 6: Commit**

```bash
git add LeanNCD/DSL/Syntax.lean LeanNCD/DSL/Elab.lean test/DSL/SyntaxTest.lean
git commit -m "refactor(spike3b): tl_unary_kw table + identStr helper (23 sites)"
```

---

### Task 3: 3b — `tl_nonlin_kw` table (depends on Task 1's new `Nonlin`)

Refactor `elabTLNonlin` (now producing the 3a shape from Task 1) into a keyword-table generator, preserving the `atomic("(" "where")` disambiguation.

**Files:** `DSL/Syntax.lean` (nonlin productions), `DSL/Elab.lean` (`elabTLNonlin`).

- [ ] **Step 1: `tl_nonlin_kw` category** — in `Syntax.lean`, replace the 11 productions (`:143-153`) with one keyword category + a single production carrying the optional mask, **preserving the `atomic("(" "where")` lookahead verbatim** (it is the sole `softmax(sum)` vs `softmax(where …)` disambiguator):

```lean
declare_syntax_cat tl_nonlin_kw
syntax "relu"        : tl_nonlin_kw
syntax "sigmoid"     : tl_nonlin_kw
syntax "tanh"        : tl_nonlin_kw
syntax "gelu"        : tl_nonlin_kw
syntax "leakyrelu"   : tl_nonlin_kw
syntax "softmax"     : tl_nonlin_kw
syntax "normalize"   : tl_nonlin_kw
syntax "l2normalize" : tl_nonlin_kw
syntax tl_nonlin_kw (atomic("(" "where") tl_bool_expr ")")? : tl_nonlin
```

Keep the explanatory comment (`Syntax.lean:140-142`) about the left-factoring, adjusted to the single production.

- [ ] **Step 2: One `elabTLNonlin` arm** — map the keyword string to `PointwiseFn`/`RowwiseFn`, attach the optional mask on rowwise, and (bonus, per the doc) **reject a mask on a pointwise keyword with a clean elaboration error** instead of relying on an unreachable parse failure:

```lean
partial def elabTLNonlin : Syntax → MetaM Nonlin
  | `(tl_nonlin| $kw:tl_nonlin_kw $[( where $b )]?) => do
      let mask? ← b.mapM (fun bb => elabTLBoolExpr bb)   -- Option (← …)
      match <keyword string of kw> with
      | "relu" | "sigmoid" | "tanh" | "gelu" | "leakyrelu" =>
          if mask?.isSome then throwErrorAt kw s!"{kwStr} is pointwise and takes no (where …) mask"
          else return .pointwise <the PointwiseFn>
      | "softmax" | "normalize" | "l2normalize" => return .rowwise <the RowwiseFn> mask?
      | other => throwErrorAt kw s!"unknown nonlinearity '{other}'"
  | _ => throwUnsupportedSyntax
```

Resolve the keyword-string extraction as in Task 2 Step 3 (atom accessor, or a small per-keyword `` `(tl_nonlin_kw| relu) `` match returning the `PointwiseFn`/`RowwiseFn` directly — the latter avoids string-typos and is preferable if the atom accessor is awkward). The **pointwise-mask rejection is new behavior** (previously an unreachable parse error) — this is the doc's intended improvement; keep the message clear.

- [ ] **Step 3: Verify the disambiguation survives** — this is the load-bearing check the doc calls out.

Run: `lake build` (must be green), then specifically confirm `ParseLayer34Test` and `CompileExamplesTest` pass — they assert unmasked `softmax(A[i] + B[i])` → `.rowwise .softmax none` with two sum terms (the `atomic` left-factoring) and masked `softmax(where s ≤ q)(…)` → `.rowwise .softmax (some _)`. If `softmax(sum)` now misparses (the mask lookahead over-committing), the `atomic(...)` production was altered — fix before proceeding. Optionally add a `ParseLayer34Test` case asserting `relu(where …)` now throws a *clear elaboration* error (documents the new behavior).

- [ ] **Step 4: Commit**

```bash
git add LeanNCD/DSL/Syntax.lean LeanNCD/DSL/Elab.lean test/DSL/ParseLayer34Test.lean
git commit -m "refactor(spike3b): tl_nonlin_kw table; pointwise-mask is now a clean elab error"
```

---

### Task 4: Mark Spike 3 done in `restructure_suggestions.md`

**Files:** `papers/restructure_suggestions.md`

- [ ] **Step 1:** Prepend `✅ **DONE.**` to the 3a and 3b leads (`:329`, `:359`); note the survey corrections (identStr was **23** sites not 19; the "two toBrOp tables" are `PointwiseFn.toBrOp`/`RowwiseFn.toBrOp`; RouteSpec insulation held — zero op-mapping proof repair, the 6a payoff). Mark 3a/3b in the ordering diagrams (`:657`, `:762`). Leave 3c as the remaining optional item.
- [ ] **Step 2:** Commit `docs(spike3): mark 3a/3b done; note actuals + 6a insulation payoff`.

---

### Task 5 (optional): evaluate 3c — merge `Factor.unaryFn` into `Factor.read`

The doc says do this "only after Spike 2a … evaluate then whether it still pays." 2a is done, so the nine duplicated `.unaryFn` arms are already gone (folded into `Factor.read?`). Before implementing, **evaluate**: grep the remaining `.unaryFn` match sites (survey found the op is inspected at exactly one consumer, `Eval/Gather.lean:75-78`) and estimate the honesty-refactor cost (changing `Factor.read` to `read : Option UnaryOp → String → List IdxExpr → Factor` touches `Factor.read?`, Traverse, Gather, Elab). If the remaining duplication is ≤ a handful of arms, record a "not worth it" decision in the doc instead of implementing. Do not implement without confirming it still pays.

---

## Self-Review

**Spec coverage (against §3):**
- 3a "restructure the AST" + "eleven match sites collapse" → Task 1 (survey mapped them: 3 functional 9→3, 2 eval, 1 elab, ~5 fusion proofs, 2 test certs). ✅
- "delete the 8-line hazard warning" + "second hazard comment" → Task 1 Steps 6–7. ✅
- "`BrOp` stays flat; only the mapping changes" + "two tiny toBrOp tables" → Task 1 Step 4 (`PointwiseFn.toBrOp`/`RowwiseFn.toBrOp`). ✅
- "Budget RouteSpec repair … cheaper if 6a landed" → Task 1 Step 4's 6a check; survey confirmed **zero** RouteSpec op-projection, so the budget is ~0. ✅
- 3b `tl_unary_kw` + `tl_nonlin_kw` + `identStr` → Tasks 2–3 (identStr is 23 sites, not 19). ✅
- 3b "verify `softmax(sum)` disambiguation … run ParseLayer34Test + CompileExamplesTest" → Task 3 Step 3. ✅
- 3c → Task 5, gated on an explicit evaluate-first decision. ✅

**Placeholder scan:** the `<keyword string of kw>` / token-extraction markers in Tasks 2–3 are deliberate — the exact Lean antiquotation for reading a keyword-category token must be resolved live (with a documented per-keyword-match fallback); every other step is concrete.

**Type consistency:** `PointwiseFn`/`RowwiseFn`/restructured `Nonlin` (Task 1) are consumed identically in `traverseAxes`/`applyNonlin`/op-mapping/eval/elab and in Task 3's `elabTLNonlin`. `PointwiseFn.toBrOp`/`RowwiseFn.toBrOp` produce `BrOp` (unchanged). `identStr : Syntax → String` (Task 2) is used in the unary and nonlin elab arms.

**Residual risk / assumptions to verify at execution:**
- Task 1 is atomic — the build is red until all sites migrate; the survey's site list is the completeness check. If a match site the survey didn't list breaks, migrate it the same way (identity/pointwise/rowwise) and note it.
- The 6a insulation (no RouteSpec/Bridge/Codec edit) is the key de-risker — verify it holds at Task 1 Step 4; if any of those files must change, STOP and reassess.
- Task 3's `atomic("(" "where")` lookahead must be preserved character-for-character; `ParseLayer34Test` is the guard.
- 3a and 3b-nonlin both edit `elabTLNonlin` — Task 1 updates its constructors (11 arms), Task 3 collapses it to the table; run Task 1 before Task 3.

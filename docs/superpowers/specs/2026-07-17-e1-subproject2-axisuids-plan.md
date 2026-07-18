# E1 Sub-project 2 — migrate the `*AxisUIDs` family to `traverseAxes` — Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended)
> or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Re-express the UID-collecting `*AxisUIDs` functions in `LeanNCD/Eval/Contract.lean` as
instantiations of the production `traverseAxes` machinery at `ConstL (List UID)`, each verified
behavior-preserving against its real prior body by a kernel-checked equality theorem — the UID-direction
analogue of sub-project 1's `specs*` migration.

**Architecture:** Same pattern as sub-project 1 (rename `_old`, define via `traverseAxes`, prove
`_eq_old`, keep-or-delete). The proofs are **direct ports of theorems the spike already proved**
(`traverseAxes_const_eq_*AxisUIDs` in `test/DSL/TraverseAxesSpike.lean`), so no new proof search is
expected. The one strategic wrinkle — the interaction with `Structural.lean`'s UID proofs — is the
subject of the "Sequencing decision" section and drives the whole plan.

**Tech Stack:** Lean 4 (v4.30.0), Mathlib, Lake. Verification = `lake build` green + `#print axioms`.

## Global Constraints

- Lean toolchain `leanprover/lean4:v4.30.0`; Mathlib rev `v4.30.0` (see `leanncd/lakefile.toml`). Do not bump.
- Every `*AxisUIDs_eq_old` must close **kernel-checked** (never `sorry`/`admit`/"by inspection").
- Full test suite (`lake build`, incl. `DSL.Pipeline.StructuralTest`) must stay green at **every** task,
  not just the end. Match sub-project 1's cadence.
- Axiom hygiene: `LeanNCD.Stmt.uids_eq` must stay `[propext, Quot.sound]` (no `sorryAx`); the
  `Eval`-side collectors feed `checkReadRanks`/shape inference and must not acquire new axioms.
- Conform to `Contract.lean`'s existing style (public `def`s, doc-comments). Match, don't reformat.
- **Comment the generated code** to the standard in "Commenting requirements" below — this is a hard
  requirement, not a nicety. Every migrated function keeps its existing `/-- … -/` doc-comment, and every
  non-obvious proof step (especially the fusion lemma and any transparency gotcha) carries an inline
  explanation. Sub-project 1 under-commented its proofs (reasoning lived in commit messages); do better here.
- New file created by sub-project 1 (`LeanNCD/DSL/TraverseAxes.lean`) is the shared home of the traversal
  machinery; sub-project 2 **consumes** it and adds nothing to it (all eleven `NodeName.traverseAxes` +
  `traverseAxesNoMask` are already there).

---

## Findings from researching the actual blast radius (before assuming scope)

**The family lives in `LeanNCD/Eval/Contract.lean`** (NOT `Structural.lean`), and unlike sub-project 1's
`private` `specs*`, these are **public `def`s** with cross-module consumers. Six functions exist:

| Function | Type | Shape | Migratable? |
|---|---|---|---|
| `idxAxisUIDs` | `IdxExpr → List UID` | leaf (`[a.uid]`, `xs.map (·.2.uid)`) | ✅ yes |
| `predAxisUIDs` | `PredArith → List UID` | recursive | ✅ yes |
| `boolAxisUIDs` | `BoolExpr → List UID` | recursive | ✅ yes |
| `termAxisUIDs` | `ProdTerm → List UID` | inlined factor match | ✅ yes |
| `readAxisUIDs` | `RHSExpr → List UID` | `body.terms.flatMap termAxisUIDs` — **mask EXCLUDED** | ✅ yes (via `traverseAxesNoMask`) |
| `freeAxisUIDs` | `List LHSSlot → List UID` | `slots.filterMap lhsAxisUID?` | ❌ **NO — see below** |

**`freeAxisUIDs` is out of scope — do not migrate it.** `lhsAxisUID?` (`Eval/Shape.lean:501`) returns
`none` for `.affine` slots and `some a.uid` for the four bare-axis slots. So `freeAxisUIDs` collects a
deliberate *subset* — the "free" (non-affine) axes only — not all axes. `LHSSlot.traverseAxes` visits
*every* axis (including the affine slot's `IdxExpr`), so `freeAxisUIDs` is **not** a `traverseAxes`
instantiation. The spike proves no equivalence for it (confirmed: no `traverseAxes_const_eq_freeAxisUIDs`).
It stays hand-written, exactly as `TLProgram.axisNames` stayed hand-written on top of `axisSpecs` in
sub-project 1. (It also has no production callers today — used only in tests/legacy — a further reason to
leave it alone.)

**`readAxisUIDs` excludes the nonlin mask.** It is `body.terms.flatMap termAxisUIDs` — no `nonlin` arm —
the documented asymmetry vs. `specsRHS` (which *includes* the mask). Its migration therefore uses
`RHSExpr.traverseAxesNoMask` (already in `TraverseAxes.lean:79`), NOT `traverseAxesWithMask`. The spike's
`traverseAxes_const_eq_readAxisUIDs` (line 700) proves exactly this via `NoMask`.

**No standalone `factorAxisUIDs`/`nonlinAxisUIDs` in production** — `termAxisUIDs` inlines the factor
match; nothing collects nonlin-mask UIDs (consistent with the mask exclusion). The spike's
`factorAxisUIDs`/`nonlinAxisUIDs` theorems used local copies; production introduces no standalone
functions for them (mirrors sub-project 1's `specsProdTerm`/`specsSumExpr` handling).

**Proof blast radius — who reaches through these functions' structural shape:**
- `Eval/Scatter.lean` (`scatterSourceAxes`, `evalScatter`) uses `idxAxisUIDs`/`readAxisUIDs` **as values
  only** — no proof unfolds their shape. Safe; behavior-preservation by `_eq_old` is enough.
- `DSL/Pipeline/Structural.lean` is the hazard. Four proofs name these collectors on the RHS of an
  equality and reason against their **current hand-written shape**:
  - `specsIdx_map_uid_eq  : (specsIdx e).map (·.uid) = idxAxisUIDs e`
  - `specsPred_map_uid_eq : (specsPred e).map (·.uid) = predAxisUIDs e`
  - `specsBool_map_uid_eq : (specsBool b).map (·.uid) = boolAxisUIDs b`
  - `Stmt.uids_eq` — its statement + proof spell out `idxAxisUIDs`/`boolAxisUIDs`/`termAxisUIDs`.
- No other production theorems reference the family (`AcsetCodec`'s `axisUid*` lemmas are unrelated).

## The sequencing decision (READ THIS FIRST — it changes the whole plan)

Migrating `idxAxisUIDs`/`predAxisUIDs`/`boolAxisUIDs`/`termAxisUIDs` changes their **definitional shape**
from a hand-written match to `(NodeName.traverseAxes (ConstL (List UID)) …).run`. The four
`Structural.lean` proofs above currently close by matching that old shape. So **naively migrating the
family will break those four proofs**, and the sub-project-1-style fix would be to add a *second* layer of
`_old`/`_eq_old` scaffolding — this time on the UID side (`idxAxisUIDs_old`/`idxAxisUIDs_eq_old` + a
`rw [idxAxisUIDs_eq_old]` in each broken proof).

That is **exactly the scaffolding the deeper-refactor follow-up
(`docs/superpowers/specs/2026-07-17-e1-scaffolding-refactor-followup.md`) exists to dissolve.** The
follow-up wants `specsX_map_uid_eq`/`Stmt.uids_eq` re-derived so they relate the AxisSpec-collecting
traversal to the UID-collecting traversal *directly* (via a `ConstL` fusion lemma), depending on neither
side's structural shape. Once that holds, both the `specs*` scaffolding AND any `*AxisUIDs` scaffolding
become unnecessary.

**Recommendation:** do the deeper refactor and sub-project 2 as **one combined effort**, unified by a
single `ConstL` map-`.uid`-over-traverse fusion lemma. Concretely:

1. Prove the fusion lemma: for a node's `traverseAxes`, `((traverseAxes (ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) x).run).map (·.uid) = (traverseAxes (ConstL (List UID)) (fun a => ⟨[a.uid]⟩) x).run`. This is the crux — one lemma, reused everywhere.
2. Migrate the five `*AxisUIDs` to the `ConstL (List UID)` traversal (this plan's Tasks 1–5).
3. Re-derive the four `Structural.lean` proofs through the fusion lemma (the follow-up's work) — which lets the remaining four `specs*_old`/`_eq_old` pairs be deleted too.

Doing sub-project 2 **in isolation first** is possible (Tasks 1–5 below stand alone), but it will
temporarily add UID-side scaffolding to `Structural.lean` that step 3 later removes — churn for no end
gain. **Preferred order: fusion lemma → migrate family → re-derive proofs → delete all scaffolding.**

The task list below covers the family migration (Tasks 1–5) plus the fusion+re-derivation (Task 6),
sequenced in the preferred order. If you deliberately choose the isolated path, Task 6 is replaced by
"add UID-side `_old`/`_eq_old` for the reached-into functions," which is explicitly the worse option.

## File layout

- `LeanNCD/Eval/Contract.lean` (modify) — 5 functions migrated to `traverseAxes`; `freeAxisUIDs`,
  `readNames`, `cartesian`, etc. untouched.
- `LeanNCD/DSL/Pipeline/Structural.lean` (modify, Task 6) — re-derive the 4 UID proofs via the fusion
  lemma; delete the 4 surviving `specs*_old`/`_eq_old` pairs and the scaffolding pointer comment.
- `LeanNCD/DSL/TraverseAxes.lean` — **no change** (machinery already present).
- No test file changes expected (`StructuralTest` exercises the pipeline end-to-end and should stay green
  by behavior-preservation).

## Commenting requirements (hard requirement — the generated code must be well commented)

The migration re-expresses concrete, readable recursive functions as opaque `(traverseAxes …).run` one-liners
whose behavior and correctness are non-obvious at the call site. The comments are what keep the result
readable. A reviewer must be able to understand *why* each declaration exists and *why* each non-trivial
proof step is there, without reading the spike or the commit log. Required, per declaration:

- **Migrated function (e.g. `idxAxisUIDs`):** keep its existing `/-- … -/` doc-comment verbatim on the new
  definition (semantics are unchanged — the doc-comment is still true). Add one line noting it is now the
  `ConstL (List UID)` instantiation of `NodeName.traverseAxes`, and that `<fn>_eq_old` certifies it equals
  the prior hand-written body. Never drop a doc-comment during the rename.
- **`readAxisUIDs` specifically:** comment the `traverseAxesNoMask` choice prominently — *why* the nonlin
  mask is excluded (the documented `specsRHS`-vs-`readAxisUIDs` asymmetry). This is the one place a future
  editor could "fix" it to `WithMask` and silently corrupt shape inference; the comment is the guardrail.
- **`<fn>_old`:** a one-line comment that it is the frozen pre-migration body, kept only as the structural
  anchor that `Structural.lean`'s UID proofs `rw` back to, and slated for deletion in Task 6. Match the
  tone of the existing `SPIKE EXCEPTION` block in `Structural.lean`.
- **`<fn>_eq_old`:** a doc-comment naming the spike theorem it ports (from the Spike-coverage map) and the
  one-line strategy. Inline-comment any tactic that is non-obvious — in particular an **explicit `rfl`
  after `rw`** must carry `-- rw's reducible-transparency close can't unfold <def>; rfl (default) does`
  (the exact gotcha sub-project 1 hit in `specsRHS`/`specsStmt`), and any `simp only [...]; rfl` used for a
  cross-node delegation must say so.
- **Fusion lemma (Task 6 Step 1) — the most important comment in the sub-project:** a full doc-comment
  explaining it is the monoid-homomorphism naturality of the `Const` applicative — that `List.map (·.uid)`
  is a `(List, ++, [])` hom and `(fun a => ⟨[a]⟩)` post-composed with it is `(fun a => ⟨[a.uid]⟩)` — why
  that makes it the one bridge the spike never built, and (if the per-node fallback is used) why each node's
  case mirrors its `traverseAxes_const_eq_*` proof.
- **`freeAxisUIDs` (NOT migrated):** add a comment at its definition stating it is deliberately excluded
  from the `traverseAxes` migration because `lhsAxisUID?` returns `none` for `.affine` slots, so it collects
  a *subset* (free axes only), not all axes — it is not a `traverseAxes` instantiation. Without this note a
  future reader will "helpfully" migrate it and change its meaning. This is a required addition even though
  the function body is untouched.

Do not over-comment the trivial (a bare `| nil => rfl` needs nothing). Comment the surprising: the
indirection, the mask asymmetry, the transparency gotchas, and the fusion rationale.

## Migration pattern (Tasks 1–5, per function; leaf-to-root order)

Order: `idxAxisUIDs` → `predAxisUIDs` → `boolAxisUIDs` → `termAxisUIDs` → `readAxisUIDs`. For each:

1. Rename the current body to `<fn>_old` (keep `def`, same signature), renaming self-recursive calls too.
2. Define `<fn>` as the `ConstL (List UID)` instantiation:
   `(NodeName.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) x).run`
   — except `readAxisUIDs`, which uses `RHSExpr.traverseAxesNoMask` (mask excluded).
3. Prove `theorem <fn>_eq_old (x) : <fn> x = <fn>_old x` by **porting the named spike theorem** (table
   below): same induction/case structure, with `specsX'`/local-copy references replaced by the real
   production `<fn>` calls, which are now definitional (so spike `exact <lemma>` steps often become `rfl`,
   and any final `.run` vs def-unfold gap closes with an explicit `rfl` after `rw` — the reducible-`rfl`
   caveat learned in sub-project 1's `specsRHS`).
4. `lake build DSL.Pipeline.StructuralTest` then full `lake build`; confirm green.
5. Because these are reached into by `Structural.lean` proofs, **keep `<fn>_old`/`<fn>_eq_old`** until
   Task 6 re-derives those proofs; then Task 6 deletes them. (Do not delete per-function.)

**Spike proof templates to port (all already proven in `test/DSL/TraverseAxesSpike.lean`):**

| Task | Function | Instantiation | Port from spike theorem |
|---|---|---|---|
| 1 | `idxAxisUIDs` | `IdxExpr.traverseAxes` @ `ConstL (List UID)` | `traverseAxes_const_eq_idxAxisUIDs` (L134) |
| 2 | `predAxisUIDs` | `PredArith.traverseAxes` | `traverseAxes_const_eq_predAxisUIDs` (L205) |
| 3 | `boolAxisUIDs` | `BoolExpr.traverseAxes` | `traverseAxes_const_eq_boolAxisUIDs` (L256) |
| 4 | `termAxisUIDs` | `ProdTerm.traverseAxes` | `traverseAxes_const_eq_termAxisUIDs` (L474) + inlined factor match (`traverseAxes_const_eq_factorAxisUIDs`, L360) |
| 5 | `readAxisUIDs` | `RHSExpr.traverseAxesNoMask` @ `ConstL (List UID)` | `traverseAxes_const_eq_readAxisUIDs` (L700) |

### Task 1: migrate `idxAxisUIDs`

**Files:** Modify `LeanNCD/Eval/Contract.lean` (the `idxAxisUIDs` block, ~L7–13).

**Interfaces:**
- Consumes: `IdxExpr.traverseAxes`, `ConstL` from `LeanNCD.DSL.TraverseAxes` (add `import`/`open` if
  `Contract.lean` does not already transitively see them — check first; `TraverseAxes` imports may need
  wiring, since `Contract.lean` is in `Eval/`, not `DSL/`).
- Produces: `idxAxisUIDs : IdxExpr → List UID` (unchanged signature); `idxAxisUIDs_old`,
  `idxAxisUIDs_eq_old : ∀ e, idxAxisUIDs e = idxAxisUIDs_old e`.

- [ ] **Step 1: confirm `Contract.lean` can see the traversal machinery.**
  Run: `grep -n "import\|TraverseAxes" LeanNCD/Eval/Contract.lean`. If `LeanNCD.DSL.TraverseAxes` is not
  transitively imported, add `import LeanNCD.DSL.TraverseAxes`. **Watch for an import cycle**: `TraverseAxes`
  must not depend on `Eval/Contract`. Verify with `lake build LeanNCD.Eval.Contract` after adding.
- [ ] **Step 2: rename to `idxAxisUIDs_old`.** Copy the current body verbatim into
  `def idxAxisUIDs_old : IdxExpr → List UID` (no self-recursion to rename — it's a leaf).
- [ ] **Step 3: define new `idxAxisUIDs`** as
  `(IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) e).run`.
- [ ] **Step 4: prove `idxAxisUIDs_eq_old`** by porting `traverseAxes_const_eq_idxAxisUIDs` (spike L134):
  the `.affine` arm's list-`map` core is the non-trivial case; the four other arms should be `rfl`. If a
  case does not close on first attempt, STOP and diagnose (per sub-project 1's effort policy) — do not force.
- [ ] **Step 5: build.** Run `lake build DSL.Pipeline.StructuralTest` then `lake build`. Expected: green
  (only `padded-access` warnings). Note: `specsIdx_map_uid_eq`/`Stmt.uids_eq` may now FAIL to build because
  `idxAxisUIDs` changed shape — that is expected and is fixed in Task 6. If you are running Tasks 1–5 in
  isolation, this is where the UID-side scaffolding decision bites (see Sequencing decision).
- [ ] **Step 6: axiom check.** Run a scratch `#print axioms LeanNCD.Eval.idxAxisUIDs`; expect standard axioms only.
- [ ] **Step 7: commit** `prod: migrate idxAxisUIDs to traverseAxes (E1 migration sub-project 2)`.

### Tasks 2–5: `predAxisUIDs`, `boolAxisUIDs`, `termAxisUIDs`, `readAxisUIDs`

Identical shape to Task 1, porting the spike theorem named in the template table. Per-task specifics:

- **Task 2 (`predAxisUIDs`):** recursive; port `traverseAxes_const_eq_predAxisUIDs`. `.embed` arm delegates
  to `idxAxisUIDs` (now definitional → likely `rfl`/`exact`); `.mul`/`.iabs` recurse via IH.
- **Task 3 (`boolAxisUIDs`):** recursive; port `traverseAxes_const_eq_boolAxisUIDs`. `.rel`/`.ieq` delegate
  to `predAxisUIDs` (cross-node → expect `simp only [...]; rfl`, not bare `show`, per sub-project 1's
  same-node-vs-cross-node asymmetry); `.and`/`.or`/`.not` recurse.
- **Task 4 (`termAxisUIDs`):** inlined factor match; port `traverseAxes_const_eq_termAxisUIDs` (which uses
  `traverseAxes_const_eq_factorAxisUIDs` for the per-factor arms — `.read`/`.unaryFn` fold `idxAxisUIDs`
  over the index list, `.iverson` delegates to `boolAxisUIDs`). Mirror sub-project 1's `specsFactor`/inlined
  `specsRHS` core-lemma style.
- **Task 5 (`readAxisUIDs`):** use `RHSExpr.traverseAxesNoMask (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)`;
  port `traverseAxes_const_eq_readAxisUIDs`, which reduces to `termAxisUIDs` over `body.terms` (mask never
  touched). Confirm the `NoMask` form is used — a `WithMask` here would wrongly pull in nonlin-mask UIDs and
  the `_eq_old` proof would fail (a useful correctness tripwire).

Each ends with the same build + axiom check + commit steps as Task 1.

### Task 6: fusion lemma + re-derive `Structural.lean` UID proofs + delete all scaffolding

**Files:** Modify `LeanNCD/DSL/Pipeline/Structural.lean`; delete `<fn>_old`/`_eq_old` in
`LeanNCD/Eval/Contract.lean` (Tasks 1–5's scaffolding) once the re-derived proofs no longer reference them.

**Interfaces:**
- Consumes: the migrated `specsX` (sub-project 1) and `*AxisUIDs` (Tasks 1–5), all now `ConstL`
  instantiations of the same `traverseAxes`.
- Produces: re-derived `specsIdx_map_uid_eq`, `specsPred_map_uid_eq`, `specsBool_map_uid_eq`,
  `Stmt.uids_eq` — proven via the fusion lemma; and the removal of every `specs*_old`/`_eq_old`
  (sub-project 1) and `*AxisUIDs_old`/`_eq_old` (Tasks 1–5).

> **This is the ONLY genuinely-new proof obligation in the whole sub-project.** The spike proves both
> collection directions (`traverseAxes_const_eq_specsX` and `traverseAxes_const_eq_*AxisUIDs`) but never
> *bridges* them — it compares each direction to its own hand-written reference and stops. Everything in
> Steps 2–3 below is a port of an existing spike theorem; only Step 1's fusion lemma is new. See the
> "Spike-coverage map" at the end of this plan for the full audit.

- [ ] **Step 1: state and prove the `ConstL` fusion lemma.** This is **not open-ended research** — it is the
  standard **monoid-homomorphism naturality of the `Const` applicative**. `List.map (·.uid) : List AxisSpec
  → List UID` is a monoid hom on `(List, ++, [])`, and `(fun a => ⟨[a]⟩)` post-composed with it is exactly
  `(fun a => ⟨[a.uid]⟩)`. Target statement (per node, and/or generic):
  `((NodeName.traverseAxes (ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) x).run).map (·.uid) = (NodeName.traverseAxes (ConstL (List UID)) (fun a => ⟨[a.uid]⟩) x).run`.
  **Preferred:** prove one generic naturality lemma — for a monoid hom `φ : M → N`,
  `φ ((traverse (fun a => ⟨g a⟩ : ConstL M) x).run) = (traverse (fun a => ⟨φ (g a)⟩ : ConstL N) x).run` — via
  `LawfulTraversable`, then instantiate at `φ := List.map (·.uid)`, `g := fun a => [a]`. **Fallback:**
  per-node fusion lemmas by induction, reusing the exact case structure of the spike's
  `traverseAxes_const_eq_*` proofs (which already do this induction over each node). Record which route was taken.
- [ ] **Step 2: re-derive `specsIdx_map_uid_eq`/`specsPred_map_uid_eq`/`specsBool_map_uid_eq`** — rewrite each
  through the fusion lemma: after fusion turns `(specsX x).map (·.uid)` into
  `(NodeName.traverseAxes (ConstL (List UID)) …).run`, that is `*AxisUIDs x` by the Tasks 1–5 definitions
  (closes by `rfl`, since post-migration `*AxisUIDs` **is** that run). Drop the `rw [specsX_eq_old]`
  openers. No structural matching on either side remains.
- [ ] **Step 3: re-derive `Stmt.uids_eq`** (its `hRHS` `have` and top-level) — **port the spike's
  `traverseAxes_const_eq_stmtUids` (L797) proof body** as the template, together with its recursion
  scaffold `traverseAxes_const_eq_termAxisUIDsSumExpr` (L543), `traverseAxes_const_eq_factorAxisUIDs`
  (L360), and `traverseAxes_const_eq_nonlinAxisUIDs` (L629). Path: `Stmt.uids s = (specsStmt s).map (·.uid)`
  [def] `= (Stmt.traverseAxes (ConstL (List UID)) …).run` [Stmt-level fusion, Step 1] `=` the explicit
  UID-list RHS [the ported `*AxisUIDs` theorems]. Drop the `rw [specsRHS_eq_old]`/`rw [specsStmt_eq_old]`
  openers. **Circularity note:** the spike's `traverseAxes_const_eq_stmtUids` is itself proved *via*
  `rw [Stmt.uids_eq]`, so use it only as a *proof-shape template*, never as a lemma the re-derived
  `Stmt.uids_eq` depends on — otherwise the dependency is circular. The re-derived `Stmt.uids_eq` must
  bottom out only in Step 1's fusion lemma and the Tasks 1–5 `*AxisUIDs` facts.
- [ ] **Step 4: delete scaffolding.** Remove `specsIdx_old`/`_eq_old`, `specsFactor_old`/`_eq_old`,
  `specsRHS_old`/`_eq_old`, `specsStmt_old`/`_eq_old` (Structural.lean) and all five `*AxisUIDs_old`/`_eq_old`
  (Contract.lean), plus the scaffolding pointer comment in `Structural.lean`.
- [ ] **Step 5: verify.** Full `lake build` green (incl. `DSL.Pipeline.StructuralTest`);
  `#print axioms LeanNCD.Stmt.uids_eq` == `[propext, Quot.sound]`. Update/close the follow-up note.
- [ ] **Step 6: commit** `refactor: re-derive UID proofs via ConstL fusion; drop all specs*/AxisUIDs _old scaffolding`.

## Success criteria

**Go:** all five `*AxisUIDs_eq_old` close kernel-checked; `readAxisUIDs` uses `NoMask` (mask stays
excluded); `freeAxisUIDs` untouched (and its exclusion comment added); the fusion lemma lets every
`specs*`/`*AxisUIDs` `_old`/`_eq_old` pair be deleted; full suite green at every step; `Stmt.uids_eq`
axiom-clean; **and the generated code meets every item in "Commenting requirements"** (doc-comments
preserved, `NoMask`/fusion/transparency-gotcha comments present) — treat a missing required comment as a
task failure, same as a red build.

**No-go / interesting either way:** if any `*AxisUIDs_eq_old` fails to close despite the spike having proven
the identical statement, that signals a drift between the spike's model and current production — investigate
fully before working around. If the fusion lemma resists a single generic statement, fall back to per-node
fusion lemmas (still eliminates the scaffolding) and record why.

## Risks / notes

- `Contract.lean` is in `Eval/` and may need a new `import LeanNCD.DSL.TraverseAxes` — **check for an import
  cycle** first (Task 1 Step 1). This is the single most likely surprise; if `TraverseAxes` transitively
  imports anything in `Eval/`, the family cannot import it and the migration needs the machinery factored
  to a lower module. Stage this before committing to the plan.
- These are **public** functions feeding `checkReadRanks`/shape inference/`scatterSourceAxes`; behavior
  preservation is load-bearing for the evaluator, not just internal tidiness. The `_eq_old` proofs are the
  guarantee; keep the full suite green throughout.
- Sub-project 2 is independent of sub-project 3 (`mapUID` family) and can precede or follow it.
- If the deeper refactor (Task 6) is deferred, Tasks 1–5 leave `Structural.lean` needing UID-side
  scaffolding — capture that debt in the follow-up note rather than leaving the build red.

## Spike-coverage map (audit: what this plan reuses vs. proves new)

Every proof obligation below, mapped to its source in `test/DSL/TraverseAxesSpike.lean`. The point:
**exactly one obligation is new** (the fusion lemma); all others are ports of already-proven spike theorems.

| Plan obligation | Spike theorem to port | Status |
| --- | --- | --- |
| Task 1 `idxAxisUIDs_eq_old` | `traverseAxes_const_eq_idxAxisUIDs` (L134) | PORT |
| Task 2 `predAxisUIDs_eq_old` | `traverseAxes_const_eq_predAxisUIDs` (L205) | PORT |
| Task 3 `boolAxisUIDs_eq_old` | `traverseAxes_const_eq_boolAxisUIDs` (L256) | PORT |
| Task 4 `termAxisUIDs_eq_old` | `traverseAxes_const_eq_termAxisUIDs` (L474) + `…factorAxisUIDs` (L360) | PORT |
| Task 5 `readAxisUIDs_eq_old` | `traverseAxes_const_eq_readAxisUIDs` (L700, via `NoMask`) + `…termAxisUIDsSumExpr` (L543) | PORT |
| Task 6 Step 1 fusion lemma | *(none — spike never bridges specs↔uid)* | **NEW** |
| Task 6 Step 2 `specs{Idx,Pred,Bool}_map_uid_eq` | fusion (Step 1) + Tasks 1–3 defs | DERIVED |
| Task 6 Step 3 `Stmt.uids_eq` | `traverseAxes_const_eq_stmtUids` (L797) as shape template + `…nonlinAxisUIDs` (L629), `…termAxisUIDsSumExpr` (L543), `…factorAxisUIDs` (L360) | PORT (shape) |

**Not needed by sub-project 2** (belongs to sub-project 3, the `mapUID` family): the entire
`traverseAxes_id_eq_*MapUID` set (L87, 180, 292, 401, 414, 498, 567, 671, 714, 753, 867, 871, 888, 942,
1016). Listed here only so a reader confirms nothing UID-relevant was overlooked.

**The one non-ported obligation — the fusion lemma — is standard, not speculative:** it is the
monoid-hom naturality of the `Const` applicative (`List.map (·.uid)` is a `(List, ++, [])` hom). If the
generic `LawfulTraversable` route is fiddly, the per-node fallback reuses the spike's own
`traverseAxes_const_eq_*` case structure verbatim, so even the fallback is spike-shaped.

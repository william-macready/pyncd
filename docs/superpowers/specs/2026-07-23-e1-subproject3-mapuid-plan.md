# E1 Sub-project 3 — migrate the `mapUID` family to `traverseAxes @ Id` — Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended)
> or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Re-express every node `mapUID` (the UID-remap family in `LeanNCD/DSL/Traverse.lean`) as an
instantiation of the production `NodeName.traverseAxes` at the `Id` applicative with leaf action
`AxisSpec.mapUID f`, each certified behaviour-preserving against its prior hand-written body by a
kernel-checked equality — the `Id`-direction analogue of sub-project 1 (`specs*`) and 2 (`*AxisUIDs`).

**Architecture:** Same rename-`_old` / define-via-`traverseAxes` / prove-`_eq_old` / delete-scaffolding
pattern as sub-projects 1 & 2, but **simpler**: no production theorem reasons about `mapUID`'s shape
(the family is consumed only computationally, at one site), so migrating it breaks no downstream proof —
there is no fusion step and no proof re-derivation. Each `_eq_old` is a direct port of a remap-equivalence
theorem the E1 prototype already proved in `test/DSL/TraverseAxesSpike.lean` (`traverseAxes_id_eq_*`).

**Tech Stack:** Lean 4 (v4.30.0), Mathlib, Lake. Verification = `lake build` green + `#print axioms`.

## Global Constraints

- Lean toolchain `leanprover/lean4:v4.30.0`; Mathlib rev per `leanncd/lakefile.toml`. Do not bump.
- Every `*.mapUID_eq_old` must close **kernel-checked** (never `sorry`/`admit`/"by inspection").
- Full test suite (`lake build`, incl. `DSL.Pipeline.StructuralTest`) green at **every** task, not just the end.
- Behaviour preservation is load-bearing: `mapUID` (via `TermTraversable.traverseUID`) drives the
  `assignUIDs` relabel phase (`Structural.lean:608`). The `_eq_old` proofs are the guarantee.
- `AxisSpec.mapUID` is **not** migrated — it is the leaf action `g : AxisSpec → AxisSpec` passed to
  `traverseAxes`, not a node traversal. Leave it exactly as-is.
- Comment new code to the sub-project 1/2 standard: keep each `mapUID` doc-comment; note it is now the
  `Id` instantiation; comment the `Id`-applicative transparency gotcha (below) wherever it appears.
- **Out of scope (→ future sub-project 4):** collapsing `Exec/Traversable.lean`'s `TermTraversable` into
  the `Id` instantiation. The `TermTraversable X` instances stay as `traverseUID := X.mapUID`.

---

## Findings from researching the blast radius (before assuming scope)

- The `mapUID` family lives entirely in `LeanNCD/DSL/Traverse.lean`. Nodes:
  `IdxExpr, PredArith, BoolExpr, Nonlin, Factor, ProdTerm, SumExpr, RHSExpr, LHSSlot, Decl, Stmt`, plus
  the inline `TermTraversable TLProgram` instance. `AxisSpec.mapUID` is the leaf action (not migrated).
- **The only external consumer** is `Structural.lean:608` (`TermTraversable.traverseUID relabel p`, the
  `assignUIDs` relabel). It uses `mapUID` **as a value only** — no proof unfolds its shape.
- **No theorem anywhere reasons about `mapUID`'s structure** (grep: zero `theorem`/`lemma` mention it).
  So — unlike sub-project 2's `Structural.lean` UID proofs — migrating `mapUID` breaks nothing to
  re-derive. No fusion lemmas, no `map_uid_eq`-style bridges. Just behaviour-preservation `_eq_old`.

## Foundation already landed (Task 0 — DONE)

Commit `6dc085d` (this branch) dropped `partial` from `IdxExpr.mapUID`, `PredArith.mapUID`,
`BoolExpr.mapUID` (the other `mapUID`s were already non-`partial`). They are ordinary structural
recursion (`IdxExpr.mapUID` does not even recurse). This generates the equation lemmas that the
`_eq_old` proofs need — the sole thing that blocked the remap direction throughout the prototype.
Full `lake build` was green (8610 jobs), no regression. See
`docs/superpowers/specs/2026-07-23-e1-subproject3-mapuid-spike.md` (go/no-go = GO).

## Migration pattern (per node; leaf-to-root)

For each node `X` (in the dependency order fixed by the tasks below):

1. **Freeze the old body** as `def X.mapUID_old (f) : X → X` — the current hand-written body verbatim,
   with every child call `Child.mapUID` renamed to `Child.mapUID_old` (so `_old` is the faithful
   frozen original; the child's `_old` already exists because children migrate first).
2. **Redefine `X.mapUID`** as the `Id` instantiation (note: `Id α = α`, so **no `.run`** and the result
   type is just `X`):
   ```
   def X.mapUID (f : UData → UData) (x : X) : X :=
     X.traverseAxes (f := Id) (AxisSpec.mapUID f) x
   ```
   The `TermTraversable X` instance (`traverseUID := X.mapUID`) is unchanged — it now transparently
   uses the instantiation.
3. **Prove** `theorem X.mapUID_eq_old (f) (x) : X.mapUID f x = X.mapUID_old f x` by porting the spike's
   remap theorem for `X` (table below), retargeting its RHS from the (previously-live) `X.mapUID` to
   `X.mapUID_old`, and discharging any hypotheses of a *conditional* prototype lemma directly via the
   children's now-unconditional `Child.mapUID_eq_old` (see "Conditional → unconditional" below).
4. `lake build` (incl. `DSL.Pipeline.StructuralTest`); confirm green.
5. Scratch `#print axioms LeanNCD.X.mapUID_eq_old`; expect `[propext, Quot.sound]` (from
   `List.traverse_eq_map_id`) and **no `sorryAx`**.
6. Keep `X.mapUID_old`/`X.mapUID_eq_old` until the final cleanup task deletes them.

### The one proof gotcha (spike-confirmed — encode in every recursive/wrapping proof)

At `Id`, `C <$> x` and `C <$> x <*> y` are **not** reduced by `rw`'s built-in closer (reducible
transparency). The working shape is:
```
simp only [X.traverseAxes, X.mapUID_old]   -- unfold the traversal AND the frozen body (equation lemmas)
rw [<child IHs or Child.mapUID_eq_old ...>]
rfl                                        -- explicit, default-transparency rfl collapses Id <$>/<*>
```
Leaf/list arms reuse the prototype's technique: a `have hEq : (fun a => Prod.mk _ <$> g a) = pure ∘ _ := rfl`
plus `simp only [..., Traversable.traverse, hEq, List.traverse_eq_map_id]; rfl`
(see `traverseAxes_id_eq_mapUID`'s `.affine` arm, spike L92-98).

### Conditional → unconditional

The prototype could only prove `ProdTerm`/`SumExpr`/`RHSExpr`/`Stmt`/`Nonlin`-mask remap **conditionally**
(hypothesis: "every `Factor`/`BoolExpr` inside satisfies its own remap"), because `Factor.iverson`/
`BoolExpr` were blocked. Post Task 0 they are unconditional, so those hypotheses are now discharged by the
child `_eq_old` theorems and the ported lemmas become **unconditional** (drop the `_of_factors`/`_of_terms`/
`_of_mask`/`(hbody)(hnonlin)` hypotheses; supply the child `_eq_old` where the hypothesis was consumed).

### Spike remap templates to port (all in `test/DSL/TraverseAxesSpike.lean`)

| Node | Port from spike theorem | Prototype status → here |
|---|---|---|
| `IdxExpr` | `traverseAxes_id_eq_mapUID` (L85) | unconditional; verbatim (retarget RHS to `_old`) |
| `PredArith` | `traverseAxes_id_eq_predMapUID` (L148, was commented-out) | now closes — proof in Task 2 |
| `BoolExpr` | `traverseAxes_id_eq_boolMapUID` (L216, was commented-out) | now closes — proof in Task 2 |
| `Nonlin` | `…_nonlinMapUID_of_mask` (L463) + unmasked `example` (L455) | conditional → unconditional |
| `Factor` | `…_factorMapUID_read` (L276), `…_unaryFn` (L289); `.iverson` (L301, "NOT ATTEMPTED") | `.iverson` now closes via `BoolExpr.mapUID_eq_old` |
| `ProdTerm` | `…_prodTermMapUID_of_factors` (L346) | conditional → unconditional |
| `SumExpr` | `…_sumExprMapUID_of_terms` (L394) | conditional → unconditional |
| `RHSExpr` | `…_rhsExprMapUID` (L496) | conditional (2 hyps) → unconditional |
| `LHSSlot` | `…_lhsSlotMapUID` (L535) | unconditional; verbatim |
| `Decl` | `…_declMapUID` (L654) | unconditional; verbatim |
| `Stmt` | `…_stmtMapUID_{recurMorphism,assign,scatter}` (L579/583/600) | conditional → unconditional |
| `TLProgram` | `…_tlProgramMapUID` (L728) | conditional → unconditional |

## File layout

- `LeanNCD/DSL/Traverse.lean` (modify) — every node `mapUID` migrated; `AxisSpec.mapUID` untouched;
  `TermTraversable` instances untouched. `_old`/`_eq_old` added then deleted (final task).
- No other production file changes (blast radius is computational-only).
- No test file changes expected — `StructuralTest` exercises the relabel path and stays green by
  behaviour preservation. (The spike's `traverseAxes_id_eq_*` templates in `TraverseAxesSpike.lean`
  are left as-is; they remain valid against the migrated defs.)

---

### Task 1: migrate `IdxExpr.mapUID`

**Files:** Modify `LeanNCD/DSL/Traverse.lean` (the `IdxExpr.mapUID` block).

**Interfaces:**
- Consumes: `IdxExpr.traverseAxes`, `ConstL`-free (`Id`) from `LeanNCD.DSL.TraverseAxes`;
  `AxisSpec.mapUID`. `Traverse.lean` already imports `LeanNCD.DSL.Ast`; it must also see
  `LeanNCD.DSL.TraverseAxes` — **check the import** (Step 1).
- Produces: `IdxExpr.mapUID : (UData → UData) → IdxExpr → IdxExpr` (unchanged signature);
  `IdxExpr.mapUID_old`; `IdxExpr.mapUID_eq_old : ∀ f e, IdxExpr.mapUID f e = IdxExpr.mapUID_old f e`.

- [ ] **Step 1: confirm the traversal import.** Run `grep -n "import\|traverseAxes" LeanNCD/DSL/Traverse.lean`.
  `TraverseAxes` is in `LeanNCD/DSL/`; if `Traverse.lean` does not already import it, add
  `import LeanNCD.DSL.TraverseAxes`. **Watch for an import cycle** — `TraverseAxes` must not import
  `Traverse`; verify with `lake build LeanNCD.DSL.Traverse` after adding.
- [ ] **Step 2: freeze the old body** as `def IdxExpr.mapUID_old (f : UData → UData) : IdxExpr → IdxExpr`
  with the current arms verbatim (no child renames — `IdxExpr.mapUID` calls only `AxisSpec.mapUID`).
- [ ] **Step 3: redefine** `def IdxExpr.mapUID (f : UData → UData) (e : IdxExpr) : IdxExpr := IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) e`.
- [ ] **Step 4: prove `IdxExpr.mapUID_eq_old`** by porting `traverseAxes_id_eq_mapUID` (spike L85):
  ```
  theorem IdxExpr.mapUID_eq_old (f : UData → UData) (e : IdxExpr) :
      IdxExpr.mapUID f e = IdxExpr.mapUID_old f e := by
    cases e with
    | axis a => rfl
    | const n => rfl
    | scale c a => rfl
    | shift a n => rfl
    | affine n xs =>
        have hEq : (fun (ca : Int × AxisSpec) => Prod.mk ca.1 <$> AxisSpec.mapUID f ca.2 :
              Int × AxisSpec → Id (Int × AxisSpec))
            = pure ∘ (fun ca => (ca.1, AxisSpec.mapUID f ca.2)) := rfl
        simp only [IdxExpr.mapUID, IdxExpr.traverseAxes, IdxExpr.mapUID_old, Traversable.traverse,
          hEq, List.traverse_eq_map_id]
        rfl
  ```
  If any arm does not close first attempt, STOP and diagnose (per the sub-project effort policy) — do not force.
- [ ] **Step 5: build.** `lake build DSL.Pipeline.StructuralTest` then `lake build`. Expected green
  (only `padded-access` warnings).
- [ ] **Step 6: axiom check.** Scratch `#print axioms LeanNCD.IdxExpr.mapUID_eq_old`; expect
  `[propext, Quot.sound]`, no `sorryAx`.
- [ ] **Step 7: commit** `prod: migrate IdxExpr.mapUID to traverseAxes @ Id (E1 sub-project 3)`.

### Task 2: migrate `PredArith.mapUID` and `BoolExpr.mapUID`

**Files:** Modify `LeanNCD/DSL/Traverse.lean`.

**Interfaces:**
- Consumes: `IdxExpr.mapUID_eq_old` (Task 1); `PredArith.traverseAxes`, `BoolExpr.traverseAxes`.
- Produces: `PredArith.mapUID_old`, `PredArith.mapUID_eq_old`; `BoolExpr.mapUID_old`, `BoolExpr.mapUID_eq_old`.

These are the two nodes whose remap was **blocked** in the prototype (the whole reason for the Task 0
spike). Their `_eq_old` proofs were verified in the spike scratch and are given in full here.

- [ ] **Step 1: `PredArith`** — freeze `PredArith.mapUID_old` (arms verbatim; rename `PredArith.mapUID`→
  `PredArith.mapUID_old` and `IdxExpr.mapUID`→`IdxExpr.mapUID_old` inside it), redefine
  `PredArith.mapUID f e := PredArith.traverseAxes (f := Id) (AxisSpec.mapUID f) e`, and prove:
  ```
  theorem PredArith.mapUID_eq_old (f : UData → UData) (e : PredArith) :
      PredArith.mapUID f e = PredArith.mapUID_old f e := by
    induction e with
    | embed e => simp only [PredArith.mapUID, PredArith.traverseAxes, PredArith.mapUID_old]; rw [IdxExpr.mapUID_eq_old f e]; rfl
    | mul a b iha ihb => simp only [PredArith.mapUID, PredArith.traverseAxes, PredArith.mapUID_old]; rw [iha, ihb]; rfl
    | iabs a iha => simp only [PredArith.mapUID, PredArith.traverseAxes, PredArith.mapUID_old]; rw [iha]; rfl
  ```
- [ ] **Step 2: `BoolExpr`** — freeze `BoolExpr.mapUID_old` (rename `BoolExpr.mapUID`→`_old` and
  `PredArith.mapUID`→`PredArith.mapUID_old` inside), redefine via `BoolExpr.traverseAxes`, and prove:
  ```
  theorem BoolExpr.mapUID_eq_old (f : UData → UData) (e : BoolExpr) :
      BoolExpr.mapUID f e = BoolExpr.mapUID_old f e := by
    induction e with
    | rel op a b => simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_old]; rw [PredArith.mapUID_eq_old f a, PredArith.mapUID_eq_old f b]; rfl
    | and a b iha ihb => simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_old]; rw [iha, ihb]; rfl
    | or a b iha ihb => simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_old]; rw [iha, ihb]; rfl
    | not a iha => simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_old]; rw [iha]; rfl
    | ieq a b => simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_old]; rw [PredArith.mapUID_eq_old f a, PredArith.mapUID_eq_old f b]; rfl
  ```
- [ ] **Step 3: build** `lake build DSL.Pipeline.StructuralTest` then `lake build`; green.
- [ ] **Step 4: axiom check** both `_eq_old`; expect `[propext, Quot.sound]`, no `sorryAx`.
- [ ] **Step 5: commit** `prod: migrate PredArith/BoolExpr.mapUID to traverseAxes @ Id (E1 sub-project 3)`.

### Task 3: migrate `Nonlin.mapUID` and `Factor.mapUID`

**Files:** Modify `LeanNCD/DSL/Traverse.lean`.

**Interfaces:**
- Consumes: `IdxExpr.mapUID_eq_old`, `BoolExpr.mapUID_eq_old`; `Nonlin.traverseAxes`, `Factor.traverseAxes`.
- Produces: `Nonlin.mapUID_old`/`_eq_old`, `Factor.mapUID_old`/`_eq_old`.

- [ ] **Step 1: `Nonlin`** — freeze `Nonlin.mapUID_old` (rename mask calls `BoolExpr.mapUID`→`_old`),
  redefine via `Nonlin.traverseAxes`. Prove `Nonlin.mapUID_eq_old` by `cases n`: the six mask-free arms
  (`identity`/`relu`/`sigmoid`/`tanh`/`gelu`/`leakyrelu`) close by `rfl`; `softmax`/`normalize`/
  `l2normalize` split on the `Option` — `none` by `rfl`, `some b` reduces to
  `BoolExpr.mapUID_eq_old f b` (port the unmasked `example` L455 + the `_of_mask` body L463, dropping the
  hypothesis and using `BoolExpr.mapUID_eq_old`; mind the `Option.traverse`/`Id` reduction — the spike's
  `_of_mask` used `simp only [Traversable.traverse, Option.traverse, Option.mapA_eq_mapM, Option.mapM_some, ...]; rfl`).
- [ ] **Step 2: `Factor`** — freeze `Factor.mapUID_old` (rename `IdxExpr.mapUID`→`_old`,
  `BoolExpr.mapUID`→`_old`), redefine via `Factor.traverseAxes`. Prove `Factor.mapUID_eq_old` by
  `cases x`: `.read`/`.unaryFn` port L276/L289 (list-fold via `hEq` + `List.traverse_eq_map_id`, using
  `IdxExpr.mapUID_eq_old`); **`.iverson b`** — the arm blocked in the prototype — now closes:
  ```
  | iverson b =>
      simp only [Factor.mapUID, Factor.traverseAxes, Factor.mapUID_old]
      rw [BoolExpr.mapUID_eq_old f b]; rfl
  ```
- [ ] **Step 3: build** green (incl. StructuralTest). **Step 4: axiom-check** both. **Step 5: commit**
  `prod: migrate Nonlin/Factor.mapUID to traverseAxes @ Id (E1 sub-project 3)`.

### Task 4: migrate `ProdTerm.mapUID`, `SumExpr.mapUID`, `RHSExpr.mapUID`

**Files:** Modify `LeanNCD/DSL/Traverse.lean`.

**Interfaces:**
- Consumes: `Factor.mapUID_eq_old`, `Nonlin.mapUID_eq_old`; `ProdTerm/SumExpr/RHSExpr.traverseAxes`.
- Produces: `ProdTerm/SumExpr/RHSExpr.mapUID_old` + `_eq_old`.

All three were **conditional** in the prototype; they are now **unconditional**.

- [ ] **Step 1: `ProdTerm`** — freeze `ProdTerm.mapUID_old (p) := { factors := p.factors.map (Factor.mapUID_old f) }`,
  redefine via `ProdTerm.traverseAxes`. Prove `ProdTerm.mapUID_eq_old` by porting
  `…_prodTermMapUID_of_factors` (L346) **without** the `h` hypothesis: the list-fold's per-element step is
  `Factor.mapUID_eq_old f hd` (unconditional now). Shape: `show`/`simp only [ProdTerm.traverseAxes,
  ProdTerm.mapUID, ProdTerm.mapUID_old]` then a `List` induction closing each cons via
  `rw [Factor.mapUID_eq_old f hd, ih]; rfl`.
- [ ] **Step 2: `SumExpr`** — identical shape one layer up (`{ terms := s.terms.map (ProdTerm.mapUID_old f) }`);
  port `…_sumExprMapUID_of_terms` (L394) unconditional; per-element step `ProdTerm.mapUID_eq_old f hd`.
- [ ] **Step 3: `RHSExpr`** — freeze `RHSExpr.mapUID_old (r) := { body := SumExpr.mapUID_old f r.body,
  nonlin := Nonlin.mapUID_old f r.nonlin, agg := r.agg }`, redefine via `RHSExpr.traverseAxes`
  (**`traverseAxesWithMask`** — `RHSExpr.mapUID` includes the mask, matching `specsRHS`). Port
  `…_rhsExprMapUID` (L496) **without** the two hypotheses: discharge them with `SumExpr.mapUID_eq_old f r.body`
  and `Nonlin.mapUID_eq_old f r.nonlin`.
- [ ] **Step 4: build** green. **Step 5: axiom-check** the three. **Step 6: commit**
  `prod: migrate ProdTerm/SumExpr/RHSExpr.mapUID to traverseAxes @ Id (E1 sub-project 3)`.

### Task 5: migrate `LHSSlot.mapUID` and `Decl.mapUID`

**Files:** Modify `LeanNCD/DSL/Traverse.lean`.

**Interfaces:**
- Consumes: `IdxExpr.mapUID_eq_old`; `LHSSlot/Decl.traverseAxes`.
- Produces: `LHSSlot/Decl.mapUID_old` + `_eq_old`. Both were **unconditional** in the prototype.

- [ ] **Step 1: `LHSSlot`** — freeze `LHSSlot.mapUID_old` (four bare-axis arms via `AxisSpec.mapUID`;
  `.affine` via `IdxExpr.mapUID_old`), redefine via `LHSSlot.traverseAxes`. Prove `LHSSlot.mapUID_eq_old`
  by porting `…_lhsSlotMapUID` (L535): `cases sl`; `free`/`freeNorm`/`iterAt`/`iterNext` close by `rfl`;
  `affine e` reduces to `IdxExpr.mapUID_eq_old f e` (`simp only [...]; rw [IdxExpr.mapUID_eq_old f e]; rfl`).
- [ ] **Step 2: `Decl`** — freeze `Decl.mapUID_old` (all arms map `AxisSpec.mapUID` over axis lists / a bare
  axis; no nested-node recursion), redefine via `Decl.traverseAxes`. Prove `Decl.mapUID_eq_old` by porting
  `…_declMapUID` (L654) — `cases d`, each arm the list-`map`/leaf shape (`hEq` + `List.traverse_eq_map_id`
  for the `ax.map` arms; `rfl`-close).
- [ ] **Step 3: build** green. **Step 4: axiom-check** both. **Step 5: commit**
  `prod: migrate LHSSlot/Decl.mapUID to traverseAxes @ Id (E1 sub-project 3)`.

### Task 6: migrate `Stmt.mapUID` and the `TLProgram` remap

**Files:** Modify `LeanNCD/DSL/Traverse.lean`.

**Interfaces:**
- Consumes: `LHSSlot.mapUID_eq_old`, `RHSExpr.mapUID_eq_old`, `Decl.mapUID_eq_old`, `Stmt.mapUID_eq_old`;
  `Stmt/TLProgram.traverseAxes`.
- Produces: `Stmt.mapUID_old`/`_eq_old`; migrated `TLProgram` remap (see Step 2) + `TLProgram.mapUID_eq_old`.

- [ ] **Step 1: `Stmt`** — freeze `Stmt.mapUID_old` (`.assign`/`.scatter` map `LHSSlot.mapUID_old` over `ls`
  and `RHSExpr.mapUID_old` over `r`; `.recurMorphism` via `AxisSpec.mapUID`), redefine via
  `Stmt.traverseAxes`. Prove `Stmt.mapUID_eq_old` by porting `…_stmtMapUID_{recurMorphism,assign,scatter}`
  (L579/583/600) **unconditional**: `recurMorphism` by `rfl`; `.assign`/`.scatter` do the `LHSSlot`
  list-fold (per-element `LHSSlot.mapUID_eq_old f hd`) `++`-composed with `RHSExpr.mapUID_eq_old f r`,
  then the `Id` `<$>/<*>` collapse (`rfl`).
- [ ] **Step 2: `TLProgram`** — the current `TermTraversable TLProgram` instance is inline
  (`{ decls := p.decls.map (Decl.mapUID f), stmts := p.stmts.map (Stmt.mapUID f) }`). Introduce a named
  `def TLProgram.mapUID (f) (p) := TLProgram.traverseAxes (f := Id) (AxisSpec.mapUID f) p` and repoint the
  instance to `traverseUID f p := TLProgram.mapUID f p` (matching every other node). Freeze
  `TLProgram.mapUID_old (p) := { decls := p.decls.map (Decl.mapUID_old f), stmts := p.stmts.map (Stmt.mapUID_old f) }`.
  Prove `TLProgram.mapUID_eq_old` by porting `…_tlProgramMapUID` (L728) **unconditional**: two `List`
  folds, per-element `Decl.mapUID_eq_old f hd` / `Stmt.mapUID_eq_old f hd`.
- [ ] **Step 3: build** green (incl. StructuralTest — the `Structural.lean:608` relabel consumer now
  routes through the migrated `TLProgram.mapUID`). **Step 4: axiom-check** both `_eq_old`. **Step 5: commit**
  `prod: migrate Stmt/TLProgram.mapUID to traverseAxes @ Id (E1 sub-project 3)`.

### Task 7: delete all `mapUID_old`/`mapUID_eq_old` scaffolding

**Files:** Modify `LeanNCD/DSL/Traverse.lean`.

By construction nothing outside the `_old`/`_eq_old` cluster references them (the `TermTraversable`
instances and `Structural.lean:608` use only `X.mapUID`). Grep to confirm, then delete.

- [ ] **Step 1: confirm dead.** `grep -rn --include='*.lean' "mapUID_old\|mapUID_eq_old" LeanNCD/` — every
  hit must be inside a `_old` def or `_eq_old` theorem (its own cluster). If any live consumer appears, STOP.
- [ ] **Step 2: delete** all `X.mapUID_old` defs and `X.mapUID_eq_old` theorems (all eleven nodes +
  `TLProgram`). Leave the migrated `X.mapUID` defs, `AxisSpec.mapUID`, and all `TermTraversable` instances.
- [ ] **Step 3: comment pass.** Ensure each migrated `X.mapUID` keeps its doc-comment + a one-line note
  that it is the `Id` instantiation of `X.traverseAxes`; no stale `_old`/`_eq_old` references remain.
- [ ] **Step 4: verify.** Full `lake build` green (incl. `DSL.Pipeline.StructuralTest`). Scratch
  `#print axioms` on `TermTraversable`-driven results is unnecessary (defs carry no axioms); instead
  confirm the build is green and `grep` shows zero `mapUID_old`/`mapUID_eq_old` remaining.
- [ ] **Step 5: commit** `refactor: drop mapUID _old/_eq_old scaffolding; mapUID family is now traverseAxes @ Id (E1 sub-project 3)`.

## Success criteria

**Go:** every node `mapUID` is `X.traverseAxes (f := Id) (AxisSpec.mapUID f) ·`; every `mapUID_eq_old`
closed kernel-checked (`[propext, Quot.sound]`, no `sorryAx`) before the cleanup deleted it; full suite
green at every task; `TermTraversable` instances and the `Structural.lean:608` relabel consumer unchanged
and green; `AxisSpec.mapUID` untouched; end state has zero `_old`/`_eq_old`.

**No-go / interesting either way:** if any `mapUID_eq_old` fails to close despite the spike having proven
the identical shape, that signals drift between the spike model and current production — investigate fully
before working around. If the `Id`-applicative `rfl` gotcha resists on a node, capture the exact incantation
that worked (do not paper over with `native_decide`/`sorry`).

## Risks / notes

- **`Traverse.lean` may need `import LeanNCD.DSL.TraverseAxes`** — check for an import cycle first
  (Task 1 Step 1). `TraverseAxes` imports `Ast`/`Traversable`, not `Traverse`, so no cycle is expected.
- `mapUID` feeds the `assignUIDs` relabel; behaviour preservation is load-bearing. The `_eq_old` proofs +
  green `StructuralTest` are the guarantee — keep the suite green throughout.
- The `Id`-applicative transparency gotcha (explicit `rfl` after `rw`) recurs in every recursive/wrapping
  proof — the code blocks above already encode it.
- Sub-project 3 is independent of the deferred `TermTraversable` collapse (sub-project 4) and of
  sub-projects 1/2 (merged). It can be reviewed and merged on its own.

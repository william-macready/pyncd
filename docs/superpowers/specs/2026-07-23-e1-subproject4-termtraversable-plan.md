# E1 Sub-project 4 — retire the `TermTraversable` typeclass (collapse into `traverseAxes @ Id`) — Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended)
> or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Remove the now-vestigial `TermTraversable` typeclass (`LeanNCD/Exec/Traversable.lean`) — the
last piece of E1's "one traversal to rule the collectors." After sub-project 3, every `traverseUID`
instance is `X.mapUID` = `X.traverseAxes (f := Id) (AxisSpec.mapUID f)`, and the class has exactly one
monomorphic consumer, so the abstraction earns nothing: repoint the consumer to `TLProgram.mapUID` and
delete the class (and the co-located unused `WithUID` struct / whole file).

**Architecture:** Two-step retirement. (1) Remove all *uses* — repoint the sole consumer
(`Structural.lean:608`, `assignUIDs`) to `TLProgram.mapUID relabel p`, delete the 7 `TermTraversable`
instances, drop the `import LeanNCD.Exec.Traversable`. (2) Delete the now-unimported
`Exec/Traversable.lean` file (the `TermTraversable` class + the unused `WithUID` struct). No proof
reasons about `TermTraversable`/`traverseUID`, so nothing downstream breaks; `DSL.Pipeline.StructuralTest`
is the behaviour guard for the relabel path.

**Tech Stack:** Lean 4 (v4.30.0), Mathlib, Lake. Verification = `lake build` green + `StructuralTest`.

**Depends on:** E1 sub-project 3 (PR #3 — the named `TLProgram.mapUID` def and the `mapUID`-family
migration). **Execute this only after sub-project 3 is merged to `main`** (branch fresh off `main`), or
branch off sub-project 3's tip if done beforehand.

## Global Constraints

- Lean toolchain `leanprover/lean4:v4.30.0`; Mathlib rev per `leanncd/lakefile.toml`. Do not bump.
- Full test suite (`lake build`, incl. `DSL.Pipeline.StructuralTest`) green at **every** task.
- Behaviour of `assignUIDs` must be unchanged — `TLProgram.mapUID relabel p` computes exactly what
  `TermTraversable.traverseUID relabel p` did (the instance was literally `traverseUID f p := TLProgram.mapUID f p`).
- Do NOT touch the `X.mapUID` defs or `AxisSpec.mapUID` — those are the surviving public API.
- No `sorry`/`admit`/`native_decide`.

---

## Findings from researching the blast radius (verified at sub-project-3 tip)

- `TermTraversable` (`LeanNCD/Exec/Traversable.lean`): `class TermTraversable (α) where traverseUID : (UData → UData) → α → α`.
- **7 instances** (all in `LeanNCD/DSL/Traverse.lean`): `AxisSpec, IdxExpr, PredArith, BoolExpr, Decl,
  Stmt, TLProgram` — each `traverseUID := X.mapUID` (AxisSpec/TLProgram spelled `traverseUID f x := …`).
- **Exactly one consumer:** `LeanNCD/DSL/Pipeline/Structural.lean:608`, inside `assignUIDs`:
  `let p' := TermTraversable.traverseUID relabel p` — **monomorphic on `TLProgram`**.
- **No proof** references `TermTraversable`/`traverseUID` (grep: zero theorems). No forward-looking use:
  the class doc mentions future `BrBase`/`ThreadedComposed` instances "in Milestone E", but none exist
  and nothing references them.
- `Exec.Traversable` is **imported only by** `LeanNCD/DSL/Traverse.lean`.
- `WithUID` (a struct co-defined in `Exec/Traversable.lean`) has **no usages in `LeanNCD/`** — appears dead.

## File layout

- `LeanNCD/DSL/Pipeline/Structural.lean` (modify) — repoint the one `assignUIDs` call.
- `LeanNCD/DSL/Traverse.lean` (modify) — delete the 7 `TermTraversable` instances; drop `import LeanNCD.Exec.Traversable`.
- `LeanNCD/Exec/Traversable.lean` (delete) — the `TermTraversable` class + unused `WithUID`.
- No test file changes expected (no spike/test references `TermTraversable`; verify in Task 1 Step 1).

---

### Task 1: remove all uses of `TermTraversable`

**Files:** Modify `LeanNCD/DSL/Pipeline/Structural.lean` and `LeanNCD/DSL/Traverse.lean`.

**Interfaces:**
- Consumes: `TLProgram.mapUID : (UData → UData) → TLProgram → TLProgram` (from sub-project 3).
- Produces: an `assignUIDs` that no longer mentions `TermTraversable`; a `Traverse.lean` with no
  `TermTraversable` instances and no `Exec.Traversable` import.

- [ ] **Step 1: confirm the blast radius at the current tip.** Run
  `grep -rn --include='*.lean' "TermTraversable\|traverseUID" LeanNCD/ test/ | grep -v '\.lake'` and
  `grep -rn --include='*.lean' "WithUID" LeanNCD/ test/ | grep -v '\.lake'`.
  Expect: `TermTraversable`/`traverseUID` only at the class def (`Exec/Traversable.lean`), the 7
  instances (`Traverse.lean`), and the one consumer (`Structural.lean:608`); `WithUID` only at its def.
  **If `WithUID` has any real usage, STOP** and narrow scope (keep `WithUID`; Task 2 then trims the class
  only). **If any second consumer of `traverseUID` appears, STOP and report** (the repoint below assumes
  the single monomorphic `TLProgram` site).
- [ ] **Step 2: repoint the consumer.** In `LeanNCD/DSL/Pipeline/Structural.lean` (`assignUIDs`), replace
  `let p' := TermTraversable.traverseUID relabel p`
  with
  `let p' := TLProgram.mapUID relabel p`.
  Leave the surrounding `return { decls := p'.decls, stmts := p'.stmts }` unchanged (`p'` is still a `TLProgram`).
- [ ] **Step 3: build + behaviour check.** `lake build DSL.Pipeline.StructuralTest 2>&1 | grep -v padded-access | tail -5`.
  Expected: "Build completed successfully". `StructuralTest` exercises `assignUIDs` end-to-end; a green
  run is the behaviour-preservation evidence (the repoint is defeq — the instance was `:= TLProgram.mapUID`).
- [ ] **Step 4: delete the 7 instances.** In `LeanNCD/DSL/Traverse.lean` remove the seven
  `instance : TermTraversable X where …` lines (`AxisSpec`, `IdxExpr`, `PredArith`, `BoolExpr`, `Decl`,
  `Stmt`, `TLProgram`). Keep every `X.mapUID` def and `AxisSpec.mapUID`.
- [ ] **Step 5: drop the import.** Remove `import LeanNCD.Exec.Traversable` from `Traverse.lean`
  (nothing else in that file now references anything from it — the `X.mapUID` defs use only `Ast` +
  `TraverseAxes`). Remove/adjust any header comment in `Traverse.lean` that referred to `TermTraversable`.
- [ ] **Step 6: full build.** `lake build 2>&1 | grep -v padded-access | tail -5` → "Build completed successfully".
  (`Exec/Traversable.lean` may still compile standalone as an orphan module — that's fine; Task 2 deletes it.)
- [ ] **Step 7: commit** `refactor: repoint assignUIDs off TermTraversable to TLProgram.mapUID; drop instances (E1 sub-project 4)`.

### Task 2: delete `Exec/Traversable.lean`

**Files:** Delete `LeanNCD/Exec/Traversable.lean`.

**Interfaces:**
- Consumes: nothing (after Task 1, nothing imports `Exec.Traversable`).
- Produces: removal of the `TermTraversable` class and the unused `WithUID` struct.

- [ ] **Step 1: re-confirm no importers/references remain.**
  `grep -rn --include='*.lean' "Exec.Traversable\|TermTraversable\|WithUID" LeanNCD/ test/ | grep -v '\.lake'`
  → ZERO hits. Also check the root module: `grep -n "Exec.Traversable" LeanNCD.lean` (if it lists modules)
  → none. **If anything remains, STOP** and resolve it (do not delete a still-referenced file).
- [ ] **Step 2: delete the file.** `git rm LeanNCD/Exec/Traversable.lean`. If any lakefile / root module
  file names it explicitly (not just a glob), remove that entry too (grep in Step 1 catches this).
- [ ] **Step 3: full build.** `lake build 2>&1 | grep -v padded-access | tail -5` → "Build completed
  successfully" (incl. `DSL.Pipeline.StructuralTest`).
- [ ] **Step 4: commit** `refactor: delete Exec/Traversable.lean (retire TermTraversable + unused WithUID) (E1 sub-project 4)`.

## Success criteria

**Go:** `TermTraversable`, `traverseUID`, and `WithUID` no longer appear anywhere in `LeanNCD/`/`test/`
(grep empty); `Exec/Traversable.lean` deleted; `assignUIDs` computes UIDs via `TLProgram.mapUID`; full
`lake build` green (incl. `StructuralTest`) at every commit; the `X.mapUID`/`AxisSpec.mapUID` API and all
sub-project-1/2/3 results are untouched. E1's three collector/mapper directions now run through one
`traverseAxes` per node with no residual bespoke traversal abstraction.

**No-go / stop:** `WithUID` turns out to be used (keep it — retire only the class, do not delete the file);
or a second `traverseUID` consumer exists (the monomorphic repoint no longer suffices — reassess whether
the typeclass is actually load-bearing).

## Risks / notes

- Smallest of the four sub-projects: ~3 files, no new proofs, no proof breakage (nothing reasons about
  `traverseUID`). The only behaviour-bearing edit is the one-line `assignUIDs` repoint, guarded by `StructuralTest`.
- The repoint is definitionally the same computation (the deleted `TermTraversable TLProgram` instance was
  `traverseUID f p := TLProgram.mapUID f p`), so no `_eq_old`-style certificate is needed — but keep every
  commit green as the check.
- If a future "decorated types" effort (Br / `ThreadedComposed`, the SMC track) wants a shared
  UID-traversal interface, it can reintroduce a purpose-built typeclass then; the current one is not that
  (no such instances/consumers exist), so retiring it now removes dead weight, not a live abstraction.

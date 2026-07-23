# E1 Sub-project 3 — migrate the `mapUID` family to `traverseAxes @ Id` — go/no-go spike

**Status:** spike DONE — **verdict: GO.** Foundational `partial`-elimination landed; full migration not yet done.
**Date:** 2026-07-23
**Branch/worktree:** `worktree-e1-subproject3-mapuid` (`.claude/worktrees/e1-subproject3-mapuid`), off `main`.
**Companion to:** E1 (`papers/restructure_suggestions.md`), sub-projects 1 (`specs*`) and 2 (`*AxisUIDs`), both merged.

## Goal

Complete E1's collector/mapper unification: re-express the **remap** family
(`LeanNCD/DSL/Traverse.lean`'s `*.mapUID`) as the `Id` instantiation of the production
`NodeName.traverseAxes`, the third and last direction after `specs*` (`ConstL (List AxisSpec)`)
and `*AxisUIDs` (`ConstL (List UID)`). Per the E1 vision this also collapses the `Exec`
`TermTraversable` rebuild tower into the same traversal.

## The blocker (why this needed a spike first)

Throughout the E1 prototype, the **remap-equivalence** theorems
(`traverseAxes_id_eq_*MapUID : NodeName.traverseAxes (f := Id) (AxisSpec.mapUID f) x = NodeName.mapUID f x`)
were **blocked** for `PredArith`, `BoolExpr`, and `Factor.iverson` — not by proof difficulty but
because `PredArith.mapUID`, `BoolExpr.mapUID` (and `IdxExpr.mapUID`) were declared **`partial def`**
(`Traverse.lean`). Lean generates no usable equation lemmas for a recursive `partial def`, so
`simp`/`rw`/`unfold`/`rfl` cannot unfold `mapUID` at all — even in non-recursive arms. The
collecting directions (`specs*`, `*AxisUIDs`) were unaffected because their `traverseAxes`
instantiations are ordinary structural recursion; only the pre-existing hand-written `mapUID`
family carried `partial`. Every prototype design doc named the fix: *drop `partial` in favour of
ordinary structural recursion, which the functions' shapes support.*

## Spike finding

The three `partial def`s have **no genuine termination obstacle**:

- `IdxExpr.mapUID` — `IdxExpr` has no nested `IdxExpr` (its `.affine` maps a `List (Int × AxisSpec)`);
  the function **does not recurse at all**. `partial` was pure noise.
- `PredArith.mapUID` / `BoolExpr.mapUID` — self-recurse only on **structural subterms**
  (`.mul a b => … (mapUID a) (mapUID b)`, `.and`/`.or`/`.not`, …) of finite inductive types.
  Textbook structural recursion.

**Change made:** dropped `partial` from the three defs in `Traverse.lean` (the other `mapUID`
defs were already non-`partial`).

**Results:**
1. `Traverse.lean` elaborates clean — structural recursion accepted, no annotation needed.
2. **Full `lake build` green (8610 jobs)** — no downstream regression. `mapUID` is used only
   computationally (rebuild/remap); structural recursion computes identical values.
3. The previously-blocked remap-equivalence theorems now **close sorry-free**
   (axioms `[propext, Quot.sound]` only — the standard pair from `List.traverse_eq_map_id`),
   verified in a scratch against the de-`partial`ed defs:
   - `predMapUID` and `boolMapUID` (the two documented blockers);
   - the **full, unconditional** `Factor.mapUID` remap — including the `.iverson` arm that was
     blocked, so it no longer needs the hypothesis-gated `_of_factors` form.

Proof shape that works (per node): `simp only [Node.traverseAxes, Node.mapUID]` (unfold both the
traversal and the now-available `mapUID` equation lemmas) `; rw [<IHs / child remap lemmas>]; rfl`.
The trailing **explicit `rfl` is required** — `rw`'s built-in closer runs at reducible
transparency and won't reduce the `Id` applicative `<$>`/`<*>`; a default-transparency `rfl` does.
(Leaf/list arms reuse the prototype's `hEq` + `List.traverse_eq_map_id` technique.)

## Verdict: GO

The `partial` wall was the only obstacle, and removing it is a trivial, behaviour-preserving,
regression-free change that immediately unblocks the remap direction for every node. Sub-project 3
is feasible with no new proof-search risk — the remap theorems are ports of the shapes above.

## Remaining work (full sub-project 3 — not this spike)

1. **Landed here:** the `partial`-elimination in `Traverse.lean` (foundation).
2. Promote the eleven `NodeName.traverseAxes` remap-equivalence theorems into production and
   re-express each `NodeName.mapUID` as `(NodeName.traverseAxes (f := Id) (AxisSpec.mapUID f) x)`
   — keeping `_old`/`_eq_old` behaviour-preservation certificates per the sub-project 1/2 cadence
   (green at every commit), or fusion-first if a cross-file bridge is needed.
3. Collapse `Exec/Traversable.lean`'s `TermTraversable` into the `Id` instantiation (the E1
   endgame: "makes `TermTraversable` its `Id` special case").
4. A full task-by-task plan doc (as sub-project 2 had) should precede the migration.

## Risks / notes

- Removing `partial` is safe on its own and green; it can be committed independently of the rest.
- Watch the `Id`-applicative `rfl` caveat above when porting proofs.
- Confirm no consumer relied on `mapUID`'s `partial`/opaque nature (full build green says none did).

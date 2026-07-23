# FOLLOW-UP: eliminate the remaining `specs*_old` / `specs*_eq_old` scaffolding

**Status:** DONE — folded into E1 sub-project 2 (Task B1 re-derivation, Task B2 deletion), 2026-07-22.
**Created:** 2026-07-17 (during E1 production migration sub-project 1)
**Owner:** unassigned
**Companion to:** [`2026-07-17-e1-production-migration-specs-design.md`](2026-07-17-e1-production-migration-specs-design.md)
**Code:** `leanncd/LeanNCD/DSL/Pipeline/Structural.lean`

> **RESOLVED.** This follow-up was executed as part of E1 sub-project 2 rather than as a separate
> task. **Task B1** proved the `ConstL` map-`(·.uid)`-over-traverse fusion lemmas (the per-node
> `*AxisUidFusion` lemmas in `Structural.lean`) and re-derived `specsIdx_map_uid_eq`,
> `specsFactor_map_uid_eq`, and `Stmt.uids_eq` directly against `traverseAxes` through them —
> dropping every `rw [specsX_eq_old]` bridge. `Stmt.uids_eq` is proved straight from the traversal
> (not via the spike's circular `traverseAxes_const_eq_stmtUids`) and its axioms tightened to
> `[propext]` (the old proof pulled `Quot.sound`). **Task B2** deleted all four
> `specsIdx/Factor/RHS/Stmt _old`/`_eq_old` pairs (and the five UID-side `*AxisUIDs_old`/`_eq_old`
> pairs in `Eval/Contract.lean`) and the SCAFFOLDING pointer comment. End state achieved:
> `Structural.lean` has no `specs*_old`/`specs*_eq_old`.
>
> One deviation from the plan below: the six `specsX_map_uid_eq` lemmas were **kept**, not deleted.
> Once sub-project 2 migrated the UID collectors (`idxAxisUIDs` etc.) to opaque `traverseAxes`
> runs, `Stmt.uids_eq` could no longer route through those lemmas, so they are no longer consumed —
> but deleting them would orphan the sub-project-1 `specsIdx..specsLHS`/`specsDecl` production defs
> (they are those lemmas' only remaining consumers). They are retained as the kernel-checked
> AxisSpec↔UID correspondence. Whether to retire the whole now-vestigial AxisSpec-collecting
> specs-side (all `specsX` except `specsStmt`, plus the `specsX_map_uid_eq` lemmas) is a separate
> design question, left open.

> If you touch the `_old`/`_eq_old` scaffolding in `Structural.lean`, read this first.
> There is a pointer comment at the scaffolding in that file linking here.

## What already happened

Sub-project 1 migrated all 10 `specs*` functions to be derived from `traverseAxes`. Eight of
them (the "SPIKE EXCEPTION" set) originally kept a permanent `specsX_old` (a frozen snapshot of
the old hand-written recursive body) plus `specsX_eq_old : ∀ x, specsX x = specsX_old x` (the
bridge proving the new traversal-derived definition equals it).

The **cheap cleanup** (this commit) deleted the **4 pairs that were dead code** — `specsPred`,
`specsBool`, `specsNonlin`, `specsLHS`. Their `_eq_old` was never referenced: the dependent
UID lemmas for those nodes were written in a "layer-preserving" style that stays valid against
the new definition unchanged. Deletion was verified by full `lake build` (green, 8610 jobs).

## What remains (the target of this follow-up)

**4 load-bearing pairs** still exist, because 4 pre-existing UID proofs `rw` through their
`_eq_old` to convert `specsX` back to `specsX_old`'s old structural shape before proceeding
(the proof bodies were written against that concrete recursive shape and can't see it through
the `Applicative`/`Traversable` instance layers of the traversal-derived definition):

| Kept pair | Bridged into (the `rw [specsX_eq_old]` site) |
|---|---|
| `specsIdx_old` / `specsIdx_eq_old` | `specsIdx_map_uid_eq` |
| `specsFactor_old` / `specsFactor_eq_old` | `specsFactor_map_uid_eq` |
| `specsRHS_old` / `specsRHS_eq_old` | `Stmt.uids_eq` — its internal `hRHS` `have` |
| `specsStmt_old` / `specsStmt_eq_old` | `Stmt.uids_eq` — its top-level proof |

Each `_old` is referenced **only** by its own `_eq_old`; each `_eq_old` is referenced **only**
by the one `rw` site above. (Grep `rw \[specs.*_eq_old\]` to re-locate the sites — do not trust
line numbers, they drift.)

## Goal

Delete all 4 remaining `_old`/`_eq_old` pairs by **re-deriving the 4 dependent UID proofs
directly against the `traverseAxes`-based definitions**, removing every dependence on the old
structural shape. End state: `Structural.lean` has no `specs*_old`/`specs*_eq_old` at all.

## Recommended approach

The crux is a **fusion / naturality fact over `ConstL`**: `(specsX x).map (·.uid)` collects
`AxisSpec`s (via `traverseAxes` at `ConstL (List AxisSpec)` with `fun a => ⟨[a]⟩`) and then
projects `.uid`; the UID-direction traversal collects UIDs directly (`traverseAxes` at
`ConstL (List UID)` with `fun a => ⟨[a.uid]⟩`). Relating "map `.uid` over the AxisSpec-collecting
run" to "the UID-collecting run" is a `ConstL`-level fusion lemma; once you have it, each
`specsX_map_uid_eq` / `Stmt.uids_eq` arm follows by the same induction the spike already used —
against the traversal, not the old body.

**Prior art — already proven in `leanncd/test/DSL/TraverseAxesSpike.lean`:** the UID-direction
equivalence theorems model exactly this collection:
- `traverseAxes_const_eq_readAxisUIDs`, `traverseAxes_const_eq_termAxisUIDsSumExpr`,
  `traverseAxes_const_eq_boolAxisUIDs`, and the per-node `*AxisUIDs` theorems;
- `traverseAxes_const_eq_stmtUids : (Stmt.traverseAxes (ConstL (List UID)) (fun a => ⟨[a.uid]⟩) s).run = Stmt.uids s`.

These derive the UID lists straight from a UID-collecting `traverseAxes` instantiation — the
shape the refactored production proofs should take.

### ⚠️ Circularity to untangle
`traverseAxes_const_eq_stmtUids` in the spike is currently proved **from** `Stmt.uids_eq`
(it opens with `rw [Stmt.uids_eq]`). So `Stmt.uids_eq` is upstream today. The refactor must
prove `Stmt.uids_eq` **directly from the traversal** (breaking the current shape dependence)
*without* leaning on any theorem that itself depends on `Stmt.uids_eq` — otherwise it's circular.
Prove `Stmt.uids_eq` from the traversal first; the spike's stmtUids theorem then follows from it
unchanged.

## Steps

1. Prove the `ConstL` map-`.uid`-over-traverse fusion lemma (or reuse the spike's per-node
   `*AxisUIDs` route, promoting what's needed into production).
2. Rewrite `specsIdx_map_uid_eq` and `specsFactor_map_uid_eq` to close against
   `(IdxExpr.traverseAxes …).run` / `(Factor.traverseAxes …).run` directly — drop their
   `rw [specsX_eq_old]` opener.
3. Rewrite `Stmt.uids_eq`'s `hRHS` `have` and its top-level proof to close against
   `specsRHS`/`specsStmt`'s traversal forms — drop both `rw [specs*_eq_old]` openers. Mind the
   circularity note above.
4. Delete `specsIdx_old`/`_eq_old`, `specsFactor_old`/`_eq_old`, `specsRHS_old`/`_eq_old`,
   `specsStmt_old`/`_eq_old`, and remove the pointer comment in `Structural.lean`.
5. **Verify:** full `lake build` green (incl. `DSL.Pipeline.StructuralTest`);
   `#print axioms LeanNCD.Stmt.uids_eq` stays `[propext, Quot.sound]` (no `sorryAx`).

## Risk / sequencing

`Stmt.uids_eq` is central to `assignUIDs`/`resolveDecls`/`checkReadRanks`. This touches
battle-tested proofs, so run it as its **own task with review** — do not fold it into unrelated
work. It is independent of E1 sub-projects 2 (`*AxisUIDs`) and 3 (`mapUID`) and can be done
before or after them.

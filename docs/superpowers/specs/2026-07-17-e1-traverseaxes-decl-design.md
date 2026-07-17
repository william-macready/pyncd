# E1 — `traverseAxes` Prototype (Decl slice) — Design

**Status:** approved 2026-07-17. Feeds `writing-plans`.

## Goal

Extend the E1 prototype (`test/DSL/TraverseAxesSpike.lean`, on branch
`worktree-e1-traverseaxes-prototype`, PR
[william-macready/pyncd#1](https://github.com/william-macready/pyncd/pull/1)) to `Decl`. Per
the checkpoint's own explicit warning not to assume this node's shape — and its new, specific
warning to check whether `Decl` depends on any other private-and-publicly-wrapped production
function the way `Stmt.uids` did — its actual definition was read before scoping: `inductive
Decl | tensor : String → List AxisSpec → Decl | predicate : String → List AxisSpec → Decl |
linear : String → List AxisSpec → (bias : Bool) → Decl | axis : AxisSpec → Option Nat → Decl`
(`DSL/Ast.lean:18-23`) — 4 constructors, all flat: three wrap a `String` (name, untouched) plus
a `List AxisSpec` directly (`linear` also carries an untouched `Bool` bias flag), one (`.axis`)
wraps a single bare `AxisSpec` plus an untouched `Option Nat` (an optional pinned dtype size).

## Findings from checking production before assuming anything

**`Decl` is the flattest node in the series — flatter even than `LHSSlot`.** No constructor
wraps a nested `IdxExpr`/`BoolExpr`/`RHSExpr`/`LHSSlot`; every arm bottoms out directly in either
a bare `AxisSpec` or a `List AxisSpec`. `LHSSlot` still had one `.affine : IdxExpr` arm requiring
delegation to a sub-traversal's own theorems; `Decl` has no such arm at all.

**Remap should be, and was empirically verified to be, fully unconditional for all 4
constructors.** `Decl.mapUID` (`DSL/Traverse.lean:66-70`) is non-partial and flat: `.tensor nm ax
=> .tensor nm (ax.map (AxisSpec.mapUID f))` etc., `.axis ax n => .axis (AxisSpec.mapUID f ax) n`.
`AxisSpec.mapUID` itself carries no `partial`/self-recursion wall anywhere in its own chain (it's
the same leaf operation every prior flat slice has used unconditionally). This was verified
directly: the full theorem was staged into the real codebase and closed, no hypothesis needed
anywhere — matching `LHSSlot`'s and `IdxExpr`'s precedent, not `Stmt`'s conditional shape.

**The `Stmt.uids`-style privacy wall does NOT recur for `Decl` — but is flagged forward to
`TLProgram`.** The only production collector touching `Decl` is `private def specsDecl : Decl →
List AxisSpec` (`Structural.lean:64-66`), consumed by `private def TLProgram.axisSpecs`
(`Structural.lean:74-75`, also private), which in turn feeds the actually-public `def
TLProgram.axisNames : TLProgram → List String` (`Structural.lean:78-79`, mapping to `.name`, not
`.uid`). Unlike `Stmt.uids`, there is no `Decl`-level public wrapper at all (no `Decl.uids`, no
`declAxisUIDs`) — grepped `specsDecl`'s own callers and found only the private
`TLProgram.axisSpecs` (`Structural.lean:74-75`), which itself only feeds the public
`TLProgram.axisNames` (`Structural.lean:78-79`). `TLProgram.axisNames` belongs to `TLProgram` —
the node *after* `Decl` in the remaining slice order — not to `Decl` itself. So this slice needs
**no production-file change**. But `TLProgram.axisNames` has the exact same shape that trapped
`Stmt.uids` (a public function built through a chain of private helpers), so this risk is
expected to resurface when `TLProgram`'s own slice is scoped — worth stating explicitly rather
than re-discovering cold.

**Correction (found during final review): `Decl` DOES have other production functions touching
it — none of them collector-shaped, and none reachable through `specsDecl`'s own chain, so the
"no production-file change" conclusion above is unaffected, but the original claim of "found
none" was an overstatement.** `Decl.name` (`Structural.lean:279`, public) and `declName`
(`Eval/Contract.lean:129`, public) both extract a `Decl`'s name as a bare `String` — unrelated
to axis collection, no `AxisSpec`/`UID` involved at all. `Decl.axisCount : Decl → Nat`
(`Structural.lean:319`, private) is a genuine classify-shaped function in the same spirit as
`LHSSlot`'s `lhsAxisUID?`: it returns `0` for `.axis` (excluded, since axis decls never appear
in the tensor-keyed `DeclEnv` this count validates against) rather than `specsDecl`'s `[ax]`
(length 1) — a real asymmetry, just like `lhsAxisUID?`'s `.affine => none`. None of these three
functions is a *public wrapper over `specsDecl`'s private chain* the way `Stmt.uids` was, so
they don't change this slice's scope or its "no production-file change needed" conclusion — but
`Decl.axisCount` is explicitly out of scope for the same reason `lhsAxisUID?` was: a different
function shape (classify, not collect), not a missing production counterpart.

## Scope

**In:** `Decl.traverseAxes` (4-arm match: three arms call `Traversable.traverse g` over the
`List AxisSpec`, one arm applies `g` directly to the bare `AxisSpec`); a local `specsDecl'`
comparison copy; one collecting-direction theorem against it; one FULLY UNCONDITIONAL remap
theorem covering all 4 constructors.

**Out:** `TLProgram.axisSpecs`/`TLProgram.axisNames` — belong to the `TLProgram` slice, not this
one. `Decl.name`/`declName` (bare `String` extraction, no axis content) and `Decl.axisCount`
(classify-shaped, not collect-shaped — see the correction above) — out of scope for the same
reason `lhsAxisUID?` was for `LHSSlot`. No production-file changes — no `Decl`-level public
wrapper over `specsDecl`'s own chain exists to bridge to, so there is no privacy wall to route
around here (contrast `Stmt`, where one did exist and required a new `Structural.lean`
theorem).

## The traversal

```lean
def Decl.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : Decl → f Decl
  | .tensor nm ax     => Decl.tensor nm <$> Traversable.traverse g ax
  | .predicate nm ax  => Decl.predicate nm <$> Traversable.traverse g ax
  | .linear nm ax b   => (fun ax' => Decl.linear nm ax' b) <$> Traversable.traverse g ax
  | .axis ax n        => (fun ax' => Decl.axis ax' n) <$> g ax
```

Three of four arms traverse a `List AxisSpec` via `Traversable.traverse g` directly (no nested
`traverseAxes` call needed, since the list's elements are already bare `AxisSpec`s — unlike
`Stmt`'s `List LHSSlot`, which needed `Traversable.traverse (LHSSlot.traverseAxes g)`). The
fourth (`.axis`) applies `g` to its single `AxisSpec` directly, same shape as `LHSSlot`'s four
non-`.affine` arms.

## Instantiations and equivalence theorems

```lean
private def specsDecl' : Decl → List AxisSpec
  | .tensor _ ax => ax | .predicate _ ax => ax | .linear _ ax _ => ax
  | .axis ax _ => [ax]

theorem traverseAxes_const_eq_specsDecl (d : Decl) :
    (Decl.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) d).run = specsDecl' d

theorem traverseAxes_id_eq_declMapUID (f : UData → UData) (d : Decl) :
    Decl.traverseAxes (f := Id) (AxisSpec.mapUID f) d = Decl.mapUID f d
```

**Collecting direction:** an inline `core` lemma (`∀ ys : List AxisSpec, (Traversable.traverse
(fun a => (⟨[a]⟩ : ConstL (List AxisSpec) AxisSpec)) ys).run = ys`) proved by list induction —
note the `ConstL (List AxisSpec) AxisSpec` type ascription on the lambda is required (calling
`Traversable.traverse` directly, rather than through a node's own `traverseAxes` wrapper, leaves
its target-element type ambiguous to Lean without it, since `ConstL` ignores its second type
parameter entirely). `.tensor`/`.predicate`/`.linear` each close by `exact core ax`; `.axis`
closes by `rfl`.

**Remap direction:** a parallel `core` lemma (`∀ ys : List AxisSpec, Traversable.traverse (m :=
Id) (AxisSpec.mapUID f) ys = ys.map (AxisSpec.mapUID f)`) proved via `List.traverse_cons` + `rfl`
(same idiom as every prior list-of-bare-leaf induction in this file). `.tensor`/`.predicate`/
`.linear` each close via `show`/`rw [core ax]`; `.axis` closes by `rfl`.

**One naming note discovered during verification:** `Traversable.traverse`'s own implicit
applicative-functor parameter is named `m`, not `f` (`Mathlib.Control.Traversable.Basic`:
`traverse : ∀ {m : Type u → Type u} [Applicative m] {α β}, (α → m β) → t α → m (t β)`) — this
only matters when calling `Traversable.traverse` *directly*; every prior slice's list traversals
went through a node's own `traverseAxes` (which legitimately does name its own type class
argument `f`), so this naming distinction never surfaced before. `Decl` is the first slice
whose traversal calls `Traversable.traverse g` directly on a list of *already-bare* `AxisSpec`s
rather than through a nested node-level `traverseAxes`, which is also why this is the first time
the direct call's own implicit name mattered.

**This exact code (including the `ConstL` type ascription and the `m :=`-not-`f :=` naming
fix above) has already been verified to close, end-to-end, via a standalone staged build during
design** — `lake build DSL.TraverseAxesSpike` (8487 jobs) and a full `lake build` (8609 jobs)
both succeeded, then reverted before writing this doc.

## Effort policy

None needed — every theorem above is pre-verified to close exactly as written.

## File layout

- `test/DSL/TraverseAxesSpike.lean` (extend, not new) — append after the `Stmt` section.
  Already registered in `lakefile.toml`'s `Tests` globs — no new registration needed.

## Success criteria (the go/no-go bar)

**Go:** both theorems close exactly as pre-verified (already confirmed during design).

**No-go / interesting either way:** none anticipated for the code itself. The interesting result
of this slice is negative: `Decl` does NOT reproduce `Stmt.uids`'s privacy-wall obstacle, and no
production file needs to change — worth stating plainly so a future reader doesn't wonder
whether the `Stmt.uids_eq`-style exception was supposed to recur here and didn't. Carrying the
`TLProgram.axisNames` flag forward to the next (final) slice is the real forward-looking result.

## Risks / notes

- `specsDecl'` must stay byte-identical to `Structural.lean:64-66`'s private `specsDecl` by
  inspection — same maintenance hazard as every prior local copy.
- `TLProgram` (the final slice) wraps both `List Decl` and `List Stmt` (`structure TLProgram
  where decls : List Decl; stmts : List Stmt`, `DSL/Ast.lean:123-125` — confirmed while
  scoping this slice) and its own public `axisNames` function has the exact `Stmt.uids` shape
  (public wrapper over a chain of private helpers: `axisNames` → private `axisSpecs` → private
  `specsDecl`/`specsStmt`). Any future `TLProgram` slice wanting to reach `axisNames` in a
  Lean-checked way should expect to repeat the `Stmt.uids_eq`-style bridge-theorem pattern in
  `Structural.lean`, not assume it was a one-off cost unique to `Stmt`.
- This is the first slice since `IdxExpr` where a production-file change was considered and
  correctly ruled out rather than assumed unnecessary — worth noting the check happened, not
  just the absence of a production diff, so a future reader can tell the omission was deliberate.

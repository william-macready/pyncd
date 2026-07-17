# E1 — `traverseAxes` Prototype (TLProgram slice) — Design

**Status:** approved 2026-07-17. Feeds `writing-plans`.

## Goal

Extend the E1 prototype (`test/DSL/TraverseAxesSpike.lean`, on branch
`worktree-e1-traverseaxes-prototype`, PR
[william-macready/pyncd#1](https://github.com/william-macready/pyncd/pull/1)) to `TLProgram` —
**the last node in the AST**, completing full coverage. Per the checkpoint's own caution
(sharpened after `Decl`'s own review found an overstated "grepped and found none" claim), the
actual definitions were checked and re-grepped carefully before scoping, rather than trusting
the checkpoint's own prediction at face value: `structure TLProgram where decls : List Decl;
stmts : List Stmt` (`DSL/Ast.lean:123-126`) — just two fields, both lists of already-proven node
types (`Decl` and `Stmt` are both complete slices).

## Findings from checking production before assuming anything

**Wrinkle 1 — no named `TLProgram.mapUID` exists.** Every prior slice's remap direction targeted
a named `NodeName.mapUID` function, with a separate `instance : TermTraversable NodeName where
traverseUID := NodeName.mapUID` line. For `TLProgram`, the logic is written directly *inline* in
the instance, with no separate named def: `instance : TermTraversable TLProgram where
traverseUID f p := { decls := p.decls.map (Decl.mapUID f), stmts := p.stmts.map (Stmt.mapUID f)
}` (`DSL/Traverse.lean:79-80`). There is no `TLProgram.mapUID` to point a remap theorem's RHS at
by name.

**Resolved by user decision: route through the real call site.** Rather than naming a local
comparison copy (the `specsX'` pattern) or hand-typing the record literal, the remap theorem's
RHS is the actual, real `TermTraversable.traverseUID f p` — the same value downstream code
would get by dispatching through the typeclass. `TermTraversable` itself lives in
`LeanNCD/Exec/Traversable.lean:17-18`: `class TermTraversable (α : Type u) where traverseUID :
(UData → UData) → α → α`. This is the most faithful target for "does remap agree with
production," at the cost of the theorem needing a `show` step to unfold the instance's inline
body — no new proof technique, just a different RHS than every prior slice used.

**Wrinkle 2 — the checkpoint's `Stmt.uids_eq`-recurrence prediction is confirmed real, but is a
strictly harder problem than `Stmt.uids_eq` was.** `TLProgram.axisNames` (`Structural.lean:78-79`,
public) is `(p.axisSpecs.map (·.name)).eraseDups` — it does go through the private
`TLProgram.axisSpecs` (`Structural.lean:74-75`: `p.decls.flatMap specsDecl ++ p.stmts.flatMap
specsStmt`), confirming the predicted private-helper-chain wall is real. But unlike `Stmt.uids`
(`(specsStmt s).map (·.uid)` — one projection, no dedup), `axisNames` also maps to `.name` (not
`.uid`) *and* applies `.eraseDups` afterward — reasoning about list deduplication is a genuinely
harder proof obligation than anything `Stmt.uids_eq` needed.

**Resolved by user decision: scope the dedup step out.** Rather than bridging all the way to the
real `axisNames` (which would need new `List.eraseDups` lemmas E1 has never required), the
collecting-direction theorem targets a local `specsProgram'` copy built from the already-proven
`specsDecl'`/`specsStmt'` — the same "byte-identical by inspection" local-copy pattern every
slice except `Stmt` has used. `.eraseDups`/`.name`-projection is documented as a deliberate
non-goal, matching the precedent set by `Nonlin`'s "no UID theorem, no production path" and
`LHSSlot`'s `lhsAxisUID?` non-goal.

**Direct consequence: no production-file change is needed for this slice, contradicting the
checkpoint's own prediction — worth stating plainly why.** The checkpoint predicted a
`Stmt.uids_eq`-style bridge "should be expected" for `TLProgram`. That prediction assumed the
slice would try to reach the real, public `axisNames`. Once dedup is scoped out, there is nothing
left to bridge to in production — `specsProgram'` is compared only against itself, built from
locals already proven (not Lean-checked against production, same as `specsDecl'`/`specsStmt'`
were never Lean-checked against the real private `specsDecl`/`specsStmt` either, only "by
inspection"). The wall was real; the scoping choice avoids needing to cross it, the same way
choosing not to chase `lhsAxisUID?` avoided a different, unrelated wall at `LHSSlot`.

**Wrinkle 3 — careful re-grep (learning from `Decl`'s own review finding) confirms no other
axis-collector-shaped public function exists for `TLProgram`.** Grepped every file referencing
`TLProgram` (`Bridge/Agreement.lean`, `Eval/Eval.lean`, `DSL/Compile.lean`, `DSL/Elab.lean`, plus
`Structural.lean`/`Traverse.lean`/`Ast.lean`) — the only hits are `TLProgram.compile`/
`compileToScheduled` (pipeline orchestration), `TLProgram.eval` (evaluation), `elabTLProgram`
(parsing): none are `specs*`/`*AxisUIDs`-family functions. No `TLProgram.uids` exists anywhere
(unlike `Stmt`) — the codebase's own module doc (`Structural.lean:35`: "by name
(`TLProgram.axisNames`, de-duplicated) or by uid (`Stmt.uids`)") confirms the "by uid" traversal
stops at the `Stmt` level; there is no program-wide UID collector to reach at all, dedup or not.
Per the `Decl` review's lesson, this claim is stated with its exact scope (functions actually
searched, files actually grepped) rather than a bare "found none."

## Scope

**In:** `TLProgram.traverseAxes` (combines a `List Decl` traversal via `Traversable.traverse
(Decl.traverseAxes g)` with a `List Stmt` traversal via `Traversable.traverse (Stmt.traverseAxes
g)`, via `<$> ... <*> ...`); a local `specsProgram'` copy built from `specsDecl'`/`specsStmt'`;
one collecting-direction theorem against it; one remap theorem against the real
`TermTraversable.traverseUID f p`, conditional on one hypothesis about `p.stmts` (`Decl`'s list
needs no hypothesis, since `Decl`'s own remap is already unconditional).

**Out:** `TLProgram.axisNames`'s `.eraseDups`/`.name`-projection step (see Wrinkle 2). No
production-file changes — the predicted wall is real but this scoping choice avoids needing to
cross it.

## The traversal

```lean
def TLProgram.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) (p : TLProgram) : f TLProgram :=
  (fun decls stmts => ({ decls := decls, stmts := stmts } : TLProgram)) <$>
    Traversable.traverse (Decl.traverseAxes g) p.decls <*> Traversable.traverse (Stmt.traverseAxes g) p.stmts
```

Combines two independent list sub-traversals via `<$> ... <*> ...`, the same shape
`RHSExpr.traverseAxesWithMask` and `Stmt.traverseAxes`'s `.assign`/`.scatter` arms already use to
combine two independent parts of a record.

## Instantiations and equivalence theorems

```lean
private def specsProgram' (p : TLProgram) : List AxisSpec :=
  p.decls.flatMap specsDecl' ++ p.stmts.flatMap specsStmt'

theorem traverseAxes_const_eq_specsProgram (p : TLProgram) :
    (TLProgram.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) p).run = specsProgram' p

theorem traverseAxes_id_eq_tlProgramMapUID (f : UData → UData) (p : TLProgram)
    (hstmts : ∀ s ∈ p.stmts, Stmt.traverseAxes (f := Id) (AxisSpec.mapUID f) s = Stmt.mapUID f s) :
    TLProgram.traverseAxes (f := Id) (AxisSpec.mapUID f) p = TermTraversable.traverseUID f p
```

**Collecting direction:** two independent `core` induction lemmas — one folding
`Traversable.traverse (Decl.traverseAxes g)` over `p.decls` via the already-proven
`traverseAxes_const_eq_specsDecl`, one folding `Traversable.traverse (Stmt.traverseAxes g)` over
`p.stmts` via the already-proven `traverseAxes_const_eq_specsStmt` — then a `show`/`rw` combining
both. No new proof technique; mirrors `Stmt.traverseAxes`'s own `core`-lemma-per-list shape.

**Remap direction:** the `decls` side needs no hypothesis (`Decl`'s remap is unconditional) — a
plain `∀ ds, Traversable.traverse ... = ds.map (Decl.mapUID f)` induction suffices. The `stmts`
side needs the membership-quantified hypothesis `∀ s ∈ ss, ...` (mirroring `ProdTerm`'s own
"if every factor in the list individually satisfies its own remap equality" pattern, generalized
from `List Factor` to `List Stmt`) — proved via list induction using `List.mem_cons_self`/
`List.mem_cons_of_mem` to narrow the hypothesis to the head and thread it to the tail. The final
`show`/`rw` step unfolds the RHS's `TermTraversable.traverseUID f p` to the real instance body
via `show`, then closes with `rw [coreD, coreS]`.

**This exact code has already been verified to close, end-to-end, via a standalone staged
build during design** — `lake build DSL.TraverseAxesSpike` (8487 jobs) and a full `lake build`
(8609 jobs) both succeeded on the first fix (`List.mem_cons_self` takes no explicit arguments,
confirmed against its existing use at `test/DSL/TraverseAxesSpike.lean:547,621` from the
`ProdTerm`/`SumExpr` slices), then reverted before writing this doc.

## Effort policy

None needed — every theorem above is pre-verified to close exactly as written.

## File layout

- `test/DSL/TraverseAxesSpike.lean` (extend, not new) — append after the `Decl` section. This
  is the final slice; no further AST nodes remain to extend to.

## Success criteria (the go/no-go bar)

**Go:** both theorems close exactly as pre-verified (already confirmed during design). With this
slice, E1 achieves full-AST coverage — every node in `DSL/Ast.lean` (`IdxExpr` through
`TLProgram`) now has a `traverseAxes` definition and at least one proven equivalence in each
direction, without a single `sorry`/`native_decide` anywhere in the series.

**No-go / interesting either way:** the interesting result of this slice is architectural, not
proof-theoretic: E1 completing full coverage without a second production-file exception (only
`Stmt` needed one) shows the `Stmt.uids_eq` pattern is not automatically required by "the node
has a public wrapper" — it's required only when the *scope* chosen for that slice demands
reaching the real function exactly. This distinction (privacy wall exists vs. slice chooses to
cross it) is worth carrying into any eventual go/no-go writeup on E1 as a whole.

## Risks / notes

- `specsProgram'` is a comparison copy of a comparison copy (`specsDecl'`/`specsStmt'`
  themselves compared "by inspection" to production, never Lean-checked) — the same
  inspection-based trust chain every non-`Stmt` slice has used, now one level deeper. Not a new
  risk, but worth naming explicitly since this is the top-level aggregation point where that
  chain's depth is most visible.
- This is the final slice. Once implemented, E1's own go/no-go decision against Spike 2a/2b
  becomes answerable in full — there is no further "next slice" to defer it to.
- The `Decl` slice's own review found that a prior design doc's "grepped and found none" claim
  had overstated its actual search. This doc's Wrinkle 3 was written to state precisely what was
  searched (which files, which grep patterns) rather than repeating a bare "found none" — worth
  holding future design docs to the same standard.

# Spike 2 (2c/2d/2e) — deferred equivalence certificates

> **Status:** SPEC / not-yet-built. Written 2026-07-24 alongside the Spike 2 (2c/2d/2e)
> consolidation (branch `spike2-cde-accessor-consolidation`). The consolidation itself is
> verified behavior-preserving by `lake build` green + the pinned test suite; this spec
> captures the *kernel-checked equivalence proofs* that were deliberately deferred, so the
> intent (Rule 9: tests encode WHY) is not lost.

## Why this exists

Spike 2 (2c/2d/2e) unified ~a dozen duplicated AST accessors onto single homes in
`LeanNCD/DSL/Ast.lean`. Each consolidation was claimed byte-identical or a provably-trivial
projection, and each landed behind a green `lake build` (which elaborates `LeanNCD` + the
`Tests` library, firing every `#guard`/example/`#print axioms`). That is strong evidence, but
it is **not** a proof that the new home computes the same function as the deleted twin — and
for two accessors the build cannot even see the risk (see "selectivity" below).

E1 set the precedent for closing exactly this gap: `test/DSL/TraverseAxesEquiv.lean` holds
standing `*_eq_ref` / `*AxisUIDs_eq_ref` certificates, each proving a production
`traverseAxes`-instantiation equals an independent hand-written reference, checked with
`#print axioms` (`[propext, Quot.sound]` or fewer; no `sorry`). This spec asks for the same
treatment for the Spike-2 accessors.

## Where it goes

- New module `test/DSL/Spike2Equiv.lean`, modeled on `test/DSL/TraverseAxesEquiv.lean`.
- Register it in `lakefile.toml`'s `Tests` `globs` list (alongside `DSL.TraverseAxesEquiv`).
- Each certificate: define a **local reference** copy of the *pre-refactor* body (the deleted
  twin, verbatim from git history — commit range `27c32b9..28e6a93`), state
  `theorem foo_eq_ref : <production> = <reference>`, prove it (`rfl`, or
  `by funext …; cases … <;> rfl`), and add a `#print axioms foo_eq_ref` guard.

## Certificates to build

### 2c — the pure relocations (Task 1)

Trivial projections; each should be `rfl` after `cases`:

- `Decl.name_eq_ref` — vs the old `Structural.Decl.name` 4-arm body.
- `Stmt.lhsName_eq_ref` — vs old `Structural.Stmt.lhsName`.
- `Stmt.slots_eq_ref` — vs old `Structural.Stmt.slots` (and note the deleted `stmtSlots` /
  `Stmt.lhsSlots` twins shared this body byte-for-byte).
- `Stmt.nonlinOf_eq_ref` — vs old `Structural.Stmt.nonlinOf`; also
  `Stmt.nonlinOf_eq_lowering_ref` vs the arm-merged `Lowering.Stmt.nonlin` (proves the
  `.assign _ _ r | .scatter _ _ r _` merge equals the split arms).

### 2c — the axis-accessor family (Task 2)

The rich primitive + derivation:

- `LHSSlot.axisUID?_eq_ref` — vs the old 5-arm `Eval/Shape.lhsAxisUID?` body.
- `LHSSlot.axisUID?_eq_axisSpec_map` — `∀ sl, sl.axisUID? = (sl.axisSpec?).map (·.uid)`. This
  proves the *derivation itself* (it holds by `rfl` on the def, but stating it documents that
  `axisUID?` is not an independent hand-copy).
- `Stmt.lhsAxes_eq_ref` — the re-based `Lowering.Stmt.lhsAxes` (`ls.filterMap (·.axisSpec?)`)
  vs the old explicit 5-arm `filterMap` body.
- `stmtLhsRank_axisUID_eq_ref` — the `stmtLhsRank` inner match, now `ls.filterMap (·.axisUID?)`,
  vs its old 5-arm `filterMap`.

The **selective** accessors — these are the ones the build canNOT protect, because
`UID = Nat` and widening `freeUID?`/`normUID?` to `axisUID?` still typechecks:

- `LHSSlot.freeUID?_eq_ref` — vs the old anonymous `.free a => some a.uid | _ => none` match
  from `slotsBecomeScatter` (Structural).
- `normAxisUidOf_eq_ref` — the re-based `normAxisUidOf` (`slots.findSome? (·.normUID?)`) vs the
  old anonymous `.freeNorm a => some a.uid | _ => none` `findSome?` body.
- **Selectivity teeth (the highest-value guard):** `#guard`s / examples proving the selective
  accessors *disagree* with the rich one, so a future "simplification" that widens them fails
  the build:
  - `example : LHSSlot.freeUID? (.freeNorm a) ≠ LHSSlot.axisUID? (.freeNorm a)` (and for
    `.iterAt`/`.iterNext`): `freeUID?` is `none`, `axisUID?` is `some a.uid`.
  - `example : LHSSlot.normUID? (.free a) ≠ LHSSlot.axisUID? (.free a)`.
  These encode WHY the two accessors exist — the diagonal-detection and norm-axis-lookup
  semantics — as a failing-if-widened check.

### 2c — outputShape/stateShape (Task 6)

- `outputShape_eq_stateShape_ref` — `∀ sizes slots, outputShape sizes slots = <old stateShape body>`,
  proving the deleted `stateShape` computed the same list. `by rfl` (bodies were identical).

### 2c — outIdx (Task 3)

- `LHSSlot.outIdx_eq_ref` — vs the old 5-arm `Eval/Scatter.lhsSlotIdx` body (and note the
  deleted `slotOutIdx` shared it byte-for-byte). `by cases sl <;> rfl`.

### 2d — the scatter-extent mirror (Task 4) — highest value

This re-establishes the invariant the deleted "MUST match … kept in sync by mirroring"
comment used to guard:

- `LHSSlot.outExtent_eq_scatterOutDim_ref` — `∀ sizes sl, sl.outExtent (fun u => sizes[u]?) =
  <old scatterOutDim (Option) body applied to sl.outIdx>`. Proves the `Option`-path caller
  (`scatterOutputShapes`) is unchanged. `by cases sl.outIdx <;> simp/rfl` (the `.affine`
  case needs the `xs.all isSome` ↔ `xs.all contains` step).
- `scatterOutShape_agrees_outExtent` — under a *total* sizing (every needed axis present),
  `scatterOutShape sizes slots = .ok (slots.map (fun sl => (sl.outExtent (fun u => sizes[u]?)).getD 0))`,
  and it `.throw`s exactly when some slot's `outExtent` is `none`. Proves the fail-loud
  `Except` caller is the same function as the `Option` one, lifted — i.e. the two mirrors
  really were one function, now provably so.

### 2e — IterSlot (Task 5)

- `Stmt.iterInfo_eq_ref` — the new `List IterSlot` result vs the old
  `List (UID × AxisSpec × Bool × Nat)` tuple reference, via the component mapping
  `IterSlot ↔ (axis.uid, axis, isRecur, pos)`. Prove
  `(s.iterInfo).map (fun it => (it.axis.uid, it.axis, it.isRecur, it.pos)) = <old iterInfo body>`.
  This certifies the dropped leading `UID` component really did equal `axis.uid` at every slot.
- `iterSlotPositions_eq_ref` — the re-signatured projection vs the old
  `List LHSSlot → List (UID × Nat)` body: `∀ s, iterSlotPositions s = <old body> s.slots`.

## Acceptance

- `test/DSL/Spike2Equiv.lean` builds with no `sorry`; every certificate has a
  `#print axioms` guard showing `[propext, Quot.sound]` or fewer (match the E1 bar).
- The selectivity teeth (`freeUID?`/`normUID?` `≠` `axisUID?`) are present and pass.
- Registered in `lakefile.toml` `Tests` globs so `lake build` fires it.

## Notes / risks

- Most certificates are `rfl`/`cases`-trivial; the 2d ones (`outExtent`) carry the real proof
  content (the `.affine` guard-equivalence and the `Except`↔`Option` lift). Budget the effort
  there.
- References must be copied from git history at the pre-refactor commits, not re-derived from
  memory — the point is an *independent* witness of the old behavior.

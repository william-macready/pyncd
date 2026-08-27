-- LeanNCD/DSL/Pipeline/RouteFragments.lean
-- The route-layer boundary between the LOGICAL schedule and the PHYSICAL `routeCore` input.
import LeanNCD.DSL.Pipeline.Types

/-!
# Private physical route fragments

`papers/nonlinearity_split_pair_direct_lowering.md` §2.2–§2.4.

Nonlinearities are **not** split before scheduling (that corrupts scan semantics: `splitScan`
splits nonlinearities *inside* scan base/recur bodies). The schedule stays logical — one statement
per source statement, no generated names — and a nonlinear plain assignment is expanded into a
private two-step *route fragment* only here, at the categorical-routing boundary.

The module imports **only** `Pipeline/Types`. It deliberately does not depend on `Lowering`'s
`ScanStmt.writes`/`outputs`/`reads`, `buildNameToStep`, or `routableInOrder`: `Lowering` imports
this module, not the other way round, so the small accessors below are local by necessity.

## The ten input classes (§2.4)

Every `ScanStmt` constructor shape is classified by `fragmentClass` — there is no catch-all.
`physicalizeOne` and `fragmentWidth` classify **independently**: `fragmentWidth` dispatches on
`fragmentClass`, while `physicalizeOne` re-matches the constructor surface itself (it needs the
payload). They are tied together by `physicalizeOne_length_eq_fragmentWidth`, which forces
agreement on every class `physicalizeOne` *accepts* — so an arm that emits statements where
`fragmentWidth` says reject, or that emits the wrong number of them, cannot compile. That is the
dangerous direction: it is what would let `fragmentLayoutOk` agree with a miscount and hide it.
The converse is **not** covered — the theorem is conditional on `.ok`, so it is vacuous on the
reject class, and relaxing `fragmentClass`'s class-6 arm to `.copy` while `physicalizeOne` still
throws would still compile. Two independent fixtures in `test/DSL/Pipeline/RouteWeaveTest.lean`
catch that direction, one per door below — fixture 13 for the `.scatter` door, fixture 14 for the
`.assign` door. The full table lives in `LeanNCD/DSL/AGENTS.md`.

Class 6 — a nonlinear **scatter-shaped write** — is **rejected** with the existing
`CompileError.unsupportedNonlinScatter`, never copied as one physical step. It has AT LEAST two
known doors, both closed here:

* `.plain (.scatter …)` with a non-identity `rhs.nonlin` — the already-lowered shape; and
* `.plain (.assign nm slots rhs)` with a non-identity `rhs.nonlin` **and** `slotsBecomeScatter
  slots` (an `.affine` slot, or a diagonal LHS repeating a free-axis UID) — the surface shape.

Both matter because the split arms build the consumer's read coordinates from
`slots.filterMap LHSSlot.toReadIdx`, and `toReadIdx` maps `.affine _ => none`: splitting such a
statement would silently DROP the affine placement rather than preserve it. Neither door is
reachable from `TLProgram.compile` (`checkScatterNonlin` rejects both shapes first, with the
identical `unsupportedNonlinScatter` constructor and payload, and `lowerArith` additionally
reclassifies every `slotsBecomeScatter` `.assign` into `Stmt.scatter`), so common-domain error
precedence is unchanged. Both are reachable from a hand-built logical schedule handed straight to
this boundary, which is exactly the caller set this design widens.

⚠️ **A third door is open and NOT closed here** (found in review, recorded in the SDD ledger, not
yet fixed): `toReadIdx` also collapses `.iterAt a n` and `.iterNext a` to `axis a`, discarding the
pinned literal `n` / the `+1` shift — so a `.plain (.assign …)` carrying an iteration slot (a shape
`finalizeScans` should have already grouped into a `.scan` node, and only a hand-built schedule can
still present here) takes the split arm and emits a producer/consumer pair whose read and write
coordinates disagree. Same reachability class as the two doors above (unreachable from `compile`),
same silent-mis-route risk, not yet given a rejection arm — deliberately left open pending a
naming decision (`unsupportedNonlinScatter` would be a misnomer here; these slots do not become a
scatter, they belong to scan grouping). See `.superpowers/sdd/2026-08-26-nonlinearity-t1-logical-schedule/progress.md`
for the reproduction.

⚠️ **A FOURTH door is open and NOT closed here** (found in whole-branch review, 2026-08-27,
recorded in the SDD ledger, not yet fixed) — MORE SEVERE than the other three: it is reachable
from **surface `tlprog!` syntax through public `TLProgram.compile`**, not only from a hand-built
schedule. `slotsBecomeScatter`'s diagonal-write detector (`Ast.lean`) goes through
`LHSSlot.freeUID?`, which returns `some` only for `.free` — never `.freeNorm`. So an LHS like
`[.free a, .freeNorm a]` (the SAME axis, once plain and once norm-marked) has exactly one free
UID by that count, is NOT classified scatter-shaped, and takes the ordinary split arm — but
`producerSlots` then degrades `.freeNorm a → .free a` on the producer, turning it into
`[.free a, .free a]`: a genuine diagonal LHS that no gate ever checked. Confirmed:
`tlprog!{ Y[i, i.] := softmax(X[i]) }` is ACCEPTED by `TLProgram.compile` (steps
`[contract, softmax]`), while the control `tlprog!{ Y[i, i] := softmax(X[i]) }` is correctly
REJECTED with `unsupportedNonlinScatter "Y"` — same mathematical shape, one spelling silently
mis-routed. `wellFormedDom` does not catch it (checks external-slot rank agreement only). Root
cause: `checkScatterNonlin` (`Structural.lean`) and `fragmentClass`/`physicalizeOne` both consult
the SAME `slotsBecomeScatter`, so both gates are blind to this shape at once. Not introduced by
this slice or the prior one — pre-existing in `slotsBecomeScatter`/`producerSlots` — but this
slice's own `.freeNorm`-sweeping fixture (`freeNormProgram` in
`test/DSL/Pipeline/RouteFragmentCorpusTest.lean`) walks past it by using three distinct axes per
case rather than combining `.free a`/`.freeNorm a` on the same axis. See
`.superpowers/sdd/2026-08-26-nonlinearity-t2-route-corpus/progress.md` for the reproduction and
the planned fix (closing this needs `slotsBecomeScatter` — or an equivalent duplicate-UID check —
to also count `.freeNorm` UIDs, then the usual `fragmentClass`/`physicalizeOne` pairing). -/

namespace LeanNCD
open Std

/-! ## Route-name inventory and collision-free private identifiers (§2.3) -/

/-- Tensor names visible in a declaration. Axis declarations are deliberately excluded. -/
def declaredTensorName? : Decl → Option String
  | .tensor nm _ | .predicate nm _ | .linear nm _ _ => some nm
  | .axis _ _ | .iter _ _ => none

/-- Names written by one logical/physical route node. -/
def routeWrites : ScanStmt → List String
  | .plain s => [s.lhsName]
  | .scan _ _ base recur _ =>
      (base.map Stmt.lhsName ++ recur.map Stmt.lhsName).eraseDups
  | .scanPre nm _ _ => [nm]

/-- Public exits of one node. A scan publishes only names present in both halves. -/
def routeOutputs : ScanStmt → List String
  | .plain s => [s.lhsName]
  | .scan _ _ base recur _ =>
      (base.map Stmt.lhsName).filter (fun nm => (recur.map Stmt.lhsName).contains nm)
  | .scanPre nm _ _ => [nm]

/-- All tensor reads, including scan self-reads, for the collision inventory. -/
def routeReads : ScanStmt → List String
  | .plain s => s.readFactors.map (·.1)
  | .scan _ _ base recur _ =>
      ((base.flatMap Stmt.readFactors ++ recur.flatMap Stmt.readFactors).map (·.1)).eraseDups
  | .scanPre _ _ _ => []

/-- Reads that become route wires. Scan-local recurrence reads are deliberately excluded. -/
def routeInputReads (sc : ScanStmt) : List String :=
  match sc with
  | .plain s => s.readFactors.map (·.1)
  | .scan _ _ base recur _ =>
      let reads := base.flatMap Stmt.readFactors ++ recur.flatMap Stmt.readFactors
      (reads.filter (fun rf => !(routeWrites sc).contains rf.1)).map (·.1)
  | .scanPre _ _ _ => []

/-- Complete route-name inventory: declarations, writes, and tensor reads (including unary reads). -/
def routeNameInventory (sp : ScheduledProgram) : List String :=
  (sp.decls.filterMap declaredTensorName? ++
    sp.stmts.flatMap (fun sc => routeWrites sc ++ routeReads sc)).eraseDups

def maxSourceNameLength : List String → Nat
  | [] => 0
  | nm :: names => max nm.length (maxSourceNameLength names)

/-- The executable collision-free name definition used by physicalization: `maxLen + ordinal + 1`
    `#` characters. No prefix (`%nl` or otherwise) is reserved; freshness is proved, not assumed. -/
def routeName (names : List String) (ordinal : Nat) : String :=
  String.ofList (List.replicate (maxSourceNameLength names + ordinal + 1) '#')

@[simp] theorem routeName_length (names : List String) (ordinal : Nat) :
    (routeName names ordinal).length = maxSourceNameLength names + ordinal + 1 := by
  simp [routeName, String.length]

theorem length_le_maxSourceNameLength {nm : String} {names : List String}
    (h : nm ∈ names) : nm.length ≤ maxSourceNameLength names := by
  induction names generalizing nm with
  | nil => simp at h
  | cons hd tl ih =>
      rw [List.mem_cons] at h
      cases h with
      | inl heq =>
          subst nm
          exact Nat.le_max_left _ _
      | inr hmem =>
          exact _root_.le_trans (ih hmem) (Nat.le_max_right _ _)

theorem routeName_longer {nm : String} {names : List String} (h : nm ∈ names)
    (ordinal : Nat) : nm.length < (routeName names ordinal).length := by
  have hle := length_le_maxSourceNameLength h
  rw [routeName_length]
  omega

/-- No generated private name occurs in the source inventory: it is strictly longer than every
    name in it. -/
theorem routeName_not_mem (names : List String) (ordinal : Nat) :
    routeName names ordinal ∉ names := by
  intro h
  have := routeName_longer h ordinal
  omega

/-- Distinct ordinals yield distinct private names (their lengths differ). -/
theorem routeName_injective (names : List String) :
    Function.Injective (routeName names) := by
  intro a b h
  have hl := congrArg String.length h
  simp only [routeName_length] at hl
  omega

/-! ## Fragments and the ten-class classifier (§2.2, §2.4) -/

/-- One logical statement's physical footprint: the contiguous physical step range it occupies,
    plus the private producer name when it was expanded into a nonlinear pair. -/
structure RouteFragment where
  logicalIndex : Nat
  firstStep : Nat
  lastStep : Nat
  internalName : Option String
  deriving DecidableEq, Repr

structure PhysicalizeAcc where
  stmts : List ScanStmt
  fragments : List RouteFragment

/-- The physicalization class of one logical node (§2.4's ten-class table). Exhaustive over the
    `ScanStmt`/`Stmt` constructor surface: there is no catch-all arm. `fragmentWidth` dispatches on
    this function; `physicalizeOne` classifies independently (it re-matches the constructor surface
    because it needs the payload). `physicalizeOne_length_eq_fragmentWidth` ties the two together on
    every class `physicalizeOne` accepts — but it is conditional on `.ok`, so it says nothing about
    the reject class. -/
inductive FragmentClass
  /-- Copied verbatim as one physical step (classes 1, 5, 7, 8, 9, 10). -/
  | copy
  /-- Expanded into an ordered private-producer/logical-consumer pair (classes 2, 3, 4 — only
      when the LHS is NOT scatter-shaped; otherwise class 6). -/
  | split
  /-- Class 6: a nonlinear scatter-shaped write, whether spelled `.plain (.scatter …)` or
      `.plain (.assign …)` with `slotsBecomeScatter` slots. Rejected, never copied. -/
  | rejectNonlinScatter
  deriving DecidableEq, Repr

/-- §2.4's ten-class classification. Every class is reached by an explicit arm, though two pairs
    share one arm where the handling is identical (3/4 — masked and unmasked axiswise; 8/9 — plain
    and affine scans). There is no catch-all: adding a `ScanStmt`, `Stmt`, or `Nonlin` constructor
    breaks this match, which is the point. -/
def fragmentClass : ScanStmt → FragmentClass
  | .plain (.assign _ slots rhs) =>
      match rhs.nonlin with
      | .identity              => .copy                  -- 1
      | .pointwise _           =>                        -- 2
          if slotsBecomeScatter slots then .rejectNonlinScatter else .split
      | .axiswise _ _          =>                        -- 3 (no mask) / 4 (mask rides the
                                                         --   consumer, so the width is the same)
          if slotsBecomeScatter slots then .rejectNonlinScatter else .split
  | .plain (.scatter _ _ rhs _) =>
      match rhs.nonlin with
      | .identity              => .copy                  -- 5
      | .pointwise _           => .rejectNonlinScatter   -- 6  REJECT, never a silent copy
      | .axiswise _ _          => .rejectNonlinScatter   -- 6
  | .plain (.recurMorphism _ _ _) => .copy               -- 7  (carries no RHSExpr)
  | .scan _ _ _ _ _              => .copy                -- 8/9  (verbatim, incl. affine scans)
  | .scanPre _ _ _               => .copy                -- 10 (opaque pre-built morphism)

/-- Physicalize one top-level logical node — one arm per §2.4 class, same order as
    `fragmentClass`. `Except`-valued because class 6 must **reject**: emitting nothing, or a
    one-step copy, would both be wrong. Scans and `scanPre` are opaque one-step fragments. -/
def physicalizeOne (sourceNames : List String) (logicalIndex firstStep : Nat)
    (sc : ScanStmt) : Except CompileError (List ScanStmt × RouteFragment) :=
  let copyOne : Except CompileError (List ScanStmt × RouteFragment) :=
    .ok ([sc], ⟨logicalIndex, firstStep, firstStep, none⟩)
  match sc with
  | .plain (.assign nm slots rhs) =>
      match rhs.nonlin with
      | .identity => copyOne                                                        -- 1
      | .pointwise _ | .axiswise _ _ =>                                             -- 2/3/4
        if slotsBecomeScatter slots then throw (.unsupportedNonlinScatter nm)       -- 6 (`.assign` door)
        else
          let internal := routeName sourceNames logicalIndex
          let producer : Stmt := .assign internal (producerSlots slots)
            { body := rhs.body, nonlin := .identity, agg := rhs.agg }
          let consumer : Stmt := .assign nm slots
            { body := { terms := [{ factors :=
                [.read internal (slots.filterMap LHSSlot.toReadIdx)] }] },
              nonlin := rhs.nonlin, agg := .sum }
          .ok ([.plain producer, .plain consumer],
            ⟨logicalIndex, firstStep, firstStep + 1, some internal⟩)
  | .plain (.scatter nm _ rhs _) =>
      match rhs.nonlin with
      | .identity => copyOne                                                        -- 5
      | .pointwise _ | .axiswise _ _ => throw (.unsupportedNonlinScatter nm)        -- 6
  | .plain (.recurMorphism _ _ _) => copyOne                                        -- 7
  | .scan _ _ _ _ _ => copyOne                                                      -- 8/9
  | .scanPre _ _ _ => copyOne                                                       -- 10

/-- The number of physical steps a class occupies, read off `fragmentClass`.
    `.rejectNonlinScatter`'s `0` is unreachable past `physicalizeOne`'s rejection; it is stated
    (rather than defaulted to 1) so that a layout check on a rejected class also fails. -/
def fragmentWidth (sc : ScanStmt) : Nat :=
  match fragmentClass sc with
  | .copy => 1
  | .split => 2
  | .rejectNonlinScatter => 0

/-- §2.2 obligation 5a: on every class `physicalizeOne` **accepts**, it emits exactly
    `fragmentWidth` statements. This is what makes `fragmentLayoutOk` an independent check rather
    than one that can agree with a `physicalizeOne` miscount — an arm that emits the wrong number
    of statements, or that emits at all where `fragmentWidth` says `0` (the reject class), fails to
    compile.

    **Scope (do not overstate this).** The hypothesis is `= .ok out`, so the statement is vacuous
    on inputs `physicalizeOne` rejects. It therefore does NOT force the converse: relaxing
    `fragmentClass`'s class-6 arm to `.copy` while `physicalizeOne` still throws typechecks fine.
    Only the dangerous direction — silently emitting a physical step for a class that must be
    rejected — is closed here; the other direction is covered by fixture 13 in
    `test/DSL/Pipeline/RouteWeaveTest.lean`. -/
theorem physicalizeOne_length_eq_fragmentWidth (sourceNames : List String)
    (logicalIndex firstStep : Nat) (sc : ScanStmt) (out : List ScanStmt × RouteFragment)
    (h : physicalizeOne sourceNames logicalIndex firstStep sc = .ok out) :
    out.1.length = fragmentWidth sc := by
  simp only [physicalizeOne, fragmentWidth, fragmentClass] at h ⊢
  -- Every reject arm is closed by `simp only … at h` (a `.error` cannot equal `.ok out`); the
  -- surviving goals are the copy/split arms, where `h` pins `out` exactly.
  repeat' split at h
  all_goals simp only [Except.ok.injEq, reduceCtorEq] at h
  all_goals subst h
  all_goals simp_all

/-! ## The one left-to-right physicalization pass (§2.4) -/

/-- One fold step, named separately so the coverage proof can reuse its exact executable body.
    Note it never calls `schedule`: physicalization preserves logical order, it does not recompute
    one. -/
def physicalizeStep (sourceNames : List String) (acc : PhysicalizeAcc)
    (pair : ScanStmt × Nat) : Except CompileError PhysicalizeAcc := do
  let (emitted, fragment) ← physicalizeOne sourceNames pair.2 acc.stmts.length pair.1
  return { stmts := acc.stmts ++ emitted, fragments := acc.fragments ++ [fragment] }

/-- One left-to-right pass over the logical statements. It does not call `schedule`. -/
def physicalizeRaw (sp : ScheduledProgram) : Except CompileError PhysicalizeAcc :=
  sp.stmts.zipIdx.foldlM (physicalizeStep (routeNameInventory sp))
    { stmts := [], fragments := [] }

/-- Each successful fold step appends exactly one fragment. -/
private theorem physicalizeStep_fragmentCount {sourceNames : List String} {acc acc' : PhysicalizeAcc}
    {pair : ScanStmt × Nat} (h : physicalizeStep sourceNames acc pair = .ok acc') :
    acc'.fragments.length = acc.fragments.length + 1 := by
  unfold physicalizeStep at h
  cases hp : physicalizeOne sourceNames pair.2 acc.stmts.length pair.1 with
  | error e => rw [hp] at h; simp at h
  | ok out => rw [hp] at h; simp at h; simp [← h]

private theorem physicalizeFold_fragmentCount (sourceNames : List String)
    (pairs : List (ScanStmt × Nat)) (acc out : PhysicalizeAcc)
    (h : pairs.foldlM (physicalizeStep sourceNames) acc = .ok out) :
    out.fragments.length = acc.fragments.length + pairs.length := by
  induction pairs generalizing acc with
  | nil =>
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp
  | cons pair tail ih =>
      rw [List.foldlM_cons] at h
      cases hs : physicalizeStep sourceNames acc pair with
      | error e => rw [hs] at h; simp [bind, Except.bind] at h
      | ok acc' =>
          rw [hs] at h
          simp only [bind, Except.bind] at h
          have hcount := physicalizeStep_fragmentCount hs
          rw [ih acc' h, hcount, List.length_cons]
          omega

/-- §2.2 obligation 2 (the counting half): one fragment per logical statement. -/
theorem physicalizeRaw_fragmentCount (sp : ScheduledProgram) (raw : PhysicalizeAcc)
    (h : physicalizeRaw sp = .ok raw) : raw.fragments.length = sp.stmts.length := by
  unfold physicalizeRaw at h
  have := physicalizeFold_fragmentCount (routeNameInventory sp) sp.stmts.zipIdx _ _ h
  simpa using this

/-! ## Checkable evidence (§2.2) -/

def generatedRouteNames (fragments : List RouteFragment) : List String :=
  fragments.filterMap (·.internalName)

/-- §2.2 obligation 8: private names are absent from the source inventory and pairwise distinct. -/
def routeNamesFresh (sourceNames : List String) (fragments : List RouteFragment) : Bool :=
  let generated := generatedRouteNames fragments
  generated.all (fun nm => !sourceNames.contains nm) &&
    generated.eraseDups.length == generated.length

def checkFragmentAt (state : Bool × Nat)
    (entry : (ScanStmt × RouteFragment) × Nat) : Bool × Nat :=
  let (ok, cursor) := state
  let ((logical, fragment), index) := entry
  let width := fragmentWidth logical
  let internalShapeOk :=
    if width == 2 then fragment.internalName.isSome else fragment.internalName.isNone
  (ok && fragment.logicalIndex == index && fragment.firstStep == cursor &&
    fragment.lastStep + 1 == cursor + width && internalShapeOk, cursor + width)

/-- §2.2 obligations 2–5: fragments form a contiguous, nonempty partition of the physical
    statements, in logical order, with the per-class width. -/
def fragmentLayoutOk (logical physical : List ScanStmt)
    (fragments : List RouteFragment) : Bool :=
  if logical.length != fragments.length then false
  else
    let result := (logical.zip fragments).zipIdx.foldl checkFragmentAt (true, 0)
    result.1 && result.2 == physical.length

/-- §2.2 obligations 6/7/10: every fragment exits at the logical output, and a nonlinear entry
    publishes ONLY its private name. -/
def fragmentExitsOk (logical physical : List ScanStmt)
    (fragments : List RouteFragment) : Bool :=
  (logical.zip fragments).all fun (logicalStmt, fragment) =>
    let exitOk :=
      routeOutputs (physical.getD fragment.lastStep default) == routeOutputs logicalStmt
    match fragment.internalName with
    | none => exitOk
    | some internal =>
        routeOutputs (physical.getD fragment.firstStep default) == [internal] && exitOk

/-! ## The checked package (§2.2)

**No physical-topology check lives here.** An earlier revision carried a `physicalRouteInOrder`
predicate and a `topological` field on `PhysicalRouteProgram`. Both are gone: `Lowering.routeCore`
— which `route` calls immediately after `physicalizeForRoute` — already gates on its own
`routableInOrder`, and the two predicates are the same last-writer-wins check over the same two
accessor halves (tied by `Lowering.lean`'s `routeOutputs_eq`/`routeInputReads_eq`). Duplicating it
here only moved the rejection one phase earlier and changed the payload string a cyclic program
reports, with no compensating guarantee. `test/DSL/Pipeline/RouteFragmentDiagnosticTest.lean`
pins that a self-referential logical schedule reports `routeCore`'s message. -/

/-- Checked, proof-carrying package: the private physical route program.

    `private mk ::` — a bare `private` on a structure does NOT privatize its constructor, and this
    one must be private: `physicalizeForRoute` is the only way to obtain a value, so a
    `PhysicalRouteProgram` always carries real evidence rather than asserted fields. This is not
    checked Eval IR, a backend API, or a serialization format; it exists only between public
    logical `route` and physical `routeCore`. -/
structure PhysicalRouteProgram where
  private mk ::
  logical : ScheduledProgram
  scheduled : ScheduledProgram
  fragments : List RouteFragment
  sourceNames : List String
  sourceInventory : sourceNames = routeNameInventory logical
  exactPhysicalization :
    physicalizeRaw logical = .ok { stmts := scheduled.stmts, fragments := fragments }
  declarationsPreserved : scheduled.decls = logical.decls
  environmentPreserved : scheduled.env = logical.env
  externalsPreserved : scheduled.extNames = logical.extNames
  explicitSizesPreserved : scheduled.explicitSizes = logical.explicitSizes
  fragmentCount : fragments.length = logical.stmts.length
  layoutChecked : fragmentLayoutOk logical.stmts scheduled.stmts fragments = true
  exitsChecked : fragmentExitsOk logical.stmts scheduled.stmts fragments = true
  freshNames : routeNamesFresh sourceNames fragments = true

/-- The ONLY constructor for `PhysicalRouteProgram`: build exactly (rejecting §2.4 class 6), then
    check layout, exits, and freshness. Physical topology is deliberately NOT checked here — see
    the section note above; `routeCore`'s own `routableInOrder` is the single gate for it. -/
def physicalizeForRoute (logical : ScheduledProgram) :
    Except CompileError PhysicalRouteProgram := do
  let sourceNames := routeNameInventory logical
  match hRaw : physicalizeRaw logical with
  | .error e => throw e
  | .ok raw =>
    let scheduled : ScheduledProgram := { logical with stmts := raw.stmts }
    if hLayout : fragmentLayoutOk logical.stmts scheduled.stmts raw.fragments then
      if hExits : fragmentExitsOk logical.stmts scheduled.stmts raw.fragments then
        if hFresh : routeNamesFresh sourceNames raw.fragments then
          return {
            logical, scheduled, fragments := raw.fragments, sourceNames
            sourceInventory := rfl
            exactPhysicalization := hRaw
            declarationsPreserved := rfl
            environmentPreserved := rfl
            externalsPreserved := rfl
            explicitSizesPreserved := rfl
            fragmentCount := physicalizeRaw_fragmentCount logical raw hRaw
            layoutChecked := hLayout
            exitsChecked := hExits
            freshNames := hFresh
          }
        else
          throw (.shapeMismatch "physicalizeForRoute: private route-name freshness failed"
            "fresh pairwise-distinct route names")
      else
        throw (.shapeMismatch "physicalizeForRoute: fragment exit check failed"
          "logical output at every fragment exit")
    else
      throw (.shapeMismatch "physicalizeForRoute: fragment layout check failed"
        "contiguous nonempty physical partition")

end LeanNCD

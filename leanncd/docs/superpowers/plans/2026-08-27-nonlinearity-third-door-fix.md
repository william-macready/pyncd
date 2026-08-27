# Close the third class-6 door (`.iterAt`/`.iterNext` LHS slots at the route boundary)

**Origin.** The Task-2 route-corpus slice (`docs/superpowers/plans/2026-08-26-nonlinearity-t2-route-corpus.md`,
merged to `main`) found this door and deliberately left it out of scope (its own §0.4). The
just-merged fourth-door slice (`docs/superpowers/plans/2026-08-27-nonlinearity-fourth-door-fix.md`,
`ad81052`/`3e2e239`) closed a *different* class-6 door and, in its own investigation, confirmed this
one has a separate root cause (its §0.5) and stayed out of scope too. This slice closes it.
Production code changes, plus regression tests and doc updates; not tests-only.

---

## §0 Verified baseline

Everything below was re-run against this worktree's base, `main` @ `f17efc2`, using
`.claude/skills/slice-plan/check-snippet.sh` — no production file was edited during this planning
pass; every snippet compiled in gitignored `spikes/` and was cleaned up automatically.

### 0.1 The bug, reproduced independently

`LHSSlot.toReadIdx` (`LeanNCD/DSL/Ast.lean`) today:

```lean
def LHSSlot.toReadIdx : LHSSlot → Option IdxExpr
  | .free a     => some (.axis a)
  | .freeNorm a => some (.axis a)
  | .iterAt a _ => some (.axis a)
  | .iterNext a => some (.axis a)
  | .affine _   => none
```

`physicalizeOne`'s split arm (`LeanNCD/DSL/Pipeline/RouteFragments.lean`) builds the private
nonlinear consumer's read coordinates from `slots.filterMap LHSSlot.toReadIdx`. A hand-built
`ScheduledProgram` whose single `.plain (.assign "Y" [.iterAt l 2] rhs)` statement carries a
non-identity `rhs.nonlin` reproduces the collapse directly:

```lean
import LeanNCD.DSL.Compile
import LeanNCD.DSL.Pipeline.RouteFragments
namespace LeanNCD

private def repAxis : AxisSpec := { name := "l", uid := 1, kind := .nat }

private def repIterAtAssign : ScheduledProgram :=
  { decls := []
  , stmts := [.plain (.assign "Y" [.iterAt repAxis 2]
      { body := { terms := [{ factors := [.read "X" [.axis repAxis]] }] }
      , nonlin := .pointwise .relu, agg := .sum })]
  , env := {}
  , extNames := insert "X" (∅ : Finset String)
  , explicitSizes := ∅ }

-- CURRENT (buggy) behavior: physicalizeForRoute SUCCEEDS (does not reject) and the emitted
-- consumer's read index is `.axis repAxis` — the pinned literal `2` was discarded by `toReadIdx`.
#guard match physicalizeForRoute repIterAtAssign with
  | .ok physical =>
      match physical.scheduled.stmts with
      | [_, .plain (.assign _ _ { body := { terms := [{ factors := [.read _ idxs] }] }, .. })] =>
          idxs == [.axis repAxis]   -- BUG: should have been [.const 2], or rejected outright
      | _ => false
  | .error _ => false

#guard match physicalizeForRoute repIterAtAssign with
  | .ok _ => true
  | .error _ => false

private def repIterNextAssign : ScheduledProgram :=
  { decls := []
  , stmts := [.plain (.assign "Y" [.iterNext repAxis]
      { body := { terms := [{ factors := [.read "X" [.axis repAxis]] }] }
      , nonlin := .pointwise .relu, agg := .sum })]
  , env := {}
  , extNames := insert "X" (∅ : Finset String)
  , explicitSizes := ∅ }

#guard match physicalizeForRoute repIterNextAssign with
  | .ok physical =>
      match physical.scheduled.stmts with
      | [_, .plain (.assign _ _ { body := { terms := [{ factors := [.read _ idxs] }] }, .. })] =>
          idxs == [.axis repAxis]   -- BUG: should have been [.shift repAxis 1], or rejected outright
      | _ => false
  | .error _ => false

end LeanNCD
```

`check-snippet.sh` result: **COMPILES** — all four `#guard`s hold. Confirmed exactly as
`RouteFragments.lean`'s header describes: the door is currently open (`physicalizeForRoute`
succeeds rather than rejecting), and the emitted consumer reads `.axis repAxis` for *both* the
`.iterAt` case (should be `.const 2`) and the `.iterNext` case (should be `.shift repAxis 1`).

### 0.2 Reachability — verified directly, not assumed

`finalizeScans` (`LeanNCD/DSL/Pipeline/Structural.lean:912-1022`) is the phase that groups
`.iterAt`/`.iterNext`-bearing statements into `ScanStmt.scan` nodes. Read directly:

```lean
let iterStmts  := nonPre.filter (fun s => !s.iterInfo.isEmpty)
...
-- plain = non-iter stmts with NO scan dependency (loop-invariant; evaluated once).
let plainStmts := nonPre.filter (fun s => s.iterInfo.isEmpty && (dep.getD s.lhsName []).isEmpty)
return { decls := lp.decls, stmts := plainStmts.map ScanStmt.plain ++ preNodes ++ nodes, ... }
```

Every statement with a nonempty `iterInfo` (i.e. carrying `.iterAt`/`.iterNext`) lands in `nodes`
(via `iterStmts`/the union-find grouping into `ScanStmt.scan`); `plainStmts` — the only stmts that
become `ScanStmt.plain` — is filtered to `s.iterInfo.isEmpty`. **A `ScanStmt.plain` with a nonempty
`iterInfo` is therefore structurally impossible as `finalizeScans`'s output**, for *any* input,
identity-nonlin or not.

`TLProgram.compileToScheduled` (`LeanNCD/DSL/Compile.lean:45`) chains
`... lowerArith >=> finalizeScans >=> schedule`, and `route`/`physicalizeForRoute`
(`RouteFragments.lean:427`) only ever receives `schedule`'s output — i.e. always post-`finalizeScans`.
**Confirmed: this shape is unreachable from `TLProgram.compile`/public `route` on `tlprog!` source.**
It is reachable only from a hand-built `ScheduledProgram` (or `ScanStmt`) handed straight to
`physicalizeForRoute`/`route`, bypassing `finalizeScans` entirely — the same reachability class as
the (now-closed) `.affine`/diagonal `.assign` door (fixture 14) and the freeNorm door (fixture 15),
and *less* severe than the fourth door (which was `compile`-reachable).

### 0.3 `.iterAt`/`.iterNext` semantics — investigated, not assumed

Central design question: does a `.plain` (non-scan) node carrying `.iterAt`/`.iterNext` have a
well-defined *correct* physical reindexing worth preserving (route-correctly), or no legitimate
reading at all outside a scan body (reject)?

**`.iterAt`/`.iterNext` are meaningful only relative to a scan's own per-iteration write
discipline**, implemented by `Scan.evalStmtSliceSeeded` (`Eval/Scan.lean`) and validated by
`finalizeScans`'s base/recurrence machinery (matching base case per `iterAt`, causality check on
`iterNext` reads, `adoptBaseIterAxes`, coupling by shared iteration-axis UID). None of that
apparatus exists for a `ScanStmt.plain` node — there is no "current iteration" for `.iterNext`'s
`+1` to be relative to, and no base/recurrence pairing for a lone `.iterAt` to complete.

Taken in isolation, however, `LHSSlot.outIdx` (`Ast.lean:248-253`) already defines what these slots
write **as plain coordinates**, and that definition is byte-identical to the corresponding
`.affine` case:

```lean
def LHSSlot.outIdx : LHSSlot → IdxExpr
  | .affine e   => e
  | .free a     => .axis a
  | .freeNorm a => .axis a
  | .iterAt _ n => .const n        -- IDENTICAL to `.affine (.const n) => .const n`
  | .iterNext a => .shift a 1      -- IDENTICAL to `.affine (.shift a 1) => .shift a 1`
```

So a standalone `.iterAt a n` write is, coordinate-for-coordinate, the same as the scatter trigger
`.affine (.const n)` (a fixed single-coordinate write); a standalone `.iterNext a` write is the
same as `.affine (.shift a 1)` (a shifted write) — this identity is not incidental: `reclassifyLHSSlot`
(`Structural.lean:638-642`, called by `reclassifyIterSlots`) is precisely the code that promotes a
surface `.affine (.shift a 1)` LHS slot *into* `.iterNext` once its axis is confirmed `iter`-declared.
Outside the scan-grouping
context that `finalizeScans` is supposed to have already applied, `.iterAt`/`.iterNext` are
indistinguishable in effect from the `.affine` scatter shapes class 6 already rejects — `slotsBecomeScatter`
was simply never asked to look for them (by design: `LHSSlot.isAffine`, `Structural.lean:829-834`,
deliberately excludes them, because *inside* a real scan they are not scatter-shaped at all).

**Conclusion: REJECT, mirroring class 6's existing policy** — not route-correctly. There is no
scan context at the `.plain` level for a "corrected" reindexing to be relative to, and the one
literal reading available (`outIdx`) reduces exactly to the scatter shape class 6 already refuses to
route. This mirrors the fourth door's own reject conclusion (§0.2 there) rather than the "expand a
real semantic-preservation fix" alternative flagged as possible in the brief — investigated
directly, not assumed to match by default.

**Diagnostic naming**, resolving the "naming decision" the header docstring left pending
(`unsupportedNonlinScatter` would be a misnomer — these slots do not become a scatter through the
surface compiler): a new `CompileError.unsupportedNonlinIterSlot` constructor is minted (§2, Task 1)
for this trigger specifically, while `fragmentClass`'s shared `FragmentClass.rejectNonlinScatter`
class (which only communicates *step width*, not diagnostic text) is reused unchanged — it already
denotes "class 6: reject, width 0," and this is a second, independently-verified trigger for that
same class, exactly as the header docstring already frames the existing doors ("two known doors,
**one class**"). No `FragmentClass` constructor is added.

### 0.4 The fix, verified in isolation

New local predicate + broadened `fragmentClass`/`physicalizeOne`, checked as a unit against the
real `RouteFragments.lean` environment (only the diagnostic name differs from what ships: the new
`CompileError.unsupportedNonlinIterSlot` constructor does not exist yet, so this stand-in throws the
existing `unsupportedNonlinScatter` in its place — verified separately in §0.4.1 that swapping the
constructor name is a type-preserving, mechanical change):

```lean
import LeanNCD.DSL.Pipeline.RouteFragments
namespace LeanNCD

def slotsCarryIterSlotT (slots : List LHSSlot) : Bool :=
  slots.any (fun sl => match sl with | .iterAt .. | .iterNext _ => true | _ => false)

inductive FragmentClassT
  | copy
  | split
  | rejectNonlinScatter
  deriving DecidableEq, Repr

def fragmentClassT : ScanStmt → FragmentClassT
  | .plain (.assign _ slots rhs) =>
      match rhs.nonlin with
      | .identity              => .copy
      | .pointwise _           =>
          if slotsBecomeScatter slots || slotsCarryIterSlotT slots then .rejectNonlinScatter else .split
      | .axiswise _ _          =>
          if slotsBecomeScatter slots || slotsCarryIterSlotT slots then .rejectNonlinScatter else .split
  | .plain (.scatter _ _ rhs _) =>
      match rhs.nonlin with
      | .identity              => .copy
      | .pointwise _           => .rejectNonlinScatter
      | .axiswise _ _          => .rejectNonlinScatter
  | .plain (.recurMorphism _ _ _) => .copy
  | .scan _ _ _ _ _              => .copy
  | .scanPre _ _ _               => .copy

def physicalizeOneT (sourceNames : List String) (logicalIndex firstStep : Nat)
    (sc : ScanStmt) : Except CompileError (List ScanStmt × RouteFragment) :=
  let copyOne : Except CompileError (List ScanStmt × RouteFragment) :=
    .ok ([sc], ⟨logicalIndex, firstStep, firstStep, none⟩)
  match sc with
  | .plain (.assign nm slots rhs) =>
      match rhs.nonlin with
      | .identity => copyOne
      | .pointwise _ | .axiswise _ _ =>
        if slotsBecomeScatter slots then throw (.unsupportedNonlinScatter nm)
        else if slotsCarryIterSlotT slots then throw (.unsupportedNonlinScatter nm)  -- stand-in for
                                                                                      -- unsupportedNonlinIterSlot
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
      | .identity => copyOne
      | .pointwise _ | .axiswise _ _ => throw (.unsupportedNonlinScatter nm)
  | .plain (.recurMorphism _ _ _) => copyOne
  | .scan _ _ _ _ _ => copyOne
  | .scanPre _ _ _ => copyOne

def fragmentWidthT (sc : ScanStmt) : Nat :=
  match fragmentClassT sc with
  | .copy => 1
  | .split => 2
  | .rejectNonlinScatter => 0

theorem physicalizeOneT_length_eq_fragmentWidthT (sourceNames : List String)
    (logicalIndex firstStep : Nat) (sc : ScanStmt) (out : List ScanStmt × RouteFragment)
    (h : physicalizeOneT sourceNames logicalIndex firstStep sc = .ok out) :
    out.1.length = fragmentWidthT sc := by
  simp only [physicalizeOneT, fragmentWidthT, fragmentClassT] at h ⊢
  repeat' split at h
  all_goals simp only [Except.ok.injEq, reduceCtorEq] at h
  all_goals subst h
  all_goals simp_all

private def repAxis : AxisSpec := { name := "l", uid := 1, kind := .nat }
private def repIterAtStmt : ScanStmt :=
  .plain (.assign "Y" [.iterAt repAxis 2]
    { body := { terms := [{ factors := [.read "X" [.axis repAxis]] }] }
    , nonlin := .pointwise .relu, agg := .sum })

#guard fragmentClassT repIterAtStmt == .rejectNonlinScatter
#guard fragmentWidthT repIterAtStmt == 0
#guard match physicalizeOneT [] 0 0 repIterAtStmt with
  | .error (.unsupportedNonlinScatter "Y") => true
  | _ => false

private def repIterNextStmt : ScanStmt :=
  .plain (.assign "Y" [.iterNext repAxis]
    { body := { terms := [{ factors := [.read "X" [.axis repAxis]] }] }
    , nonlin := .pointwise .relu, agg := .sum })

#guard fragmentClassT repIterNextStmt == .rejectNonlinScatter
#guard fragmentWidthT repIterNextStmt == 0
#guard match physicalizeOneT [] 0 0 repIterNextStmt with
  | .error (.unsupportedNonlinScatter "Y") => true
  | _ => false

-- Positive control: identity nonlin is untouched (still class 1, copy) — `finalizeScans` would
-- normally have consumed this shape into a `.scan`; only a hand-built schedule presents it here,
-- and for `.identity` there is no split (no `toReadIdx` call), so no bug and no new rejection.
private def repIterAtIdentity : ScanStmt :=
  .plain (.assign "Y" [.iterAt repAxis 2]
    { body := { terms := [{ factors := [.read "X" [.axis repAxis]] }] }
    , nonlin := .identity, agg := .sum })

#guard fragmentClassT repIterAtIdentity == .copy
#guard fragmentWidthT repIterAtIdentity == 1

end LeanNCD
```

`check-snippet.sh` result: **COMPILES** — every `#guard` holds and the width-agreement proof
type-checks with the broadened `||` condition (the same generic `repeat' split at h` pattern the
production proof already uses handles the extra `if`-split with no change to the proof's shape).

#### 0.4.1 The constructor-name swap is mechanical

Grepped every file that pattern-matches a `CompileError` value (not just constructs one):
`Eval/Error.lean`, `Eval/Plan/EvalPlan.lean`, `Eval/Plan/Compile.lean`, `DSL/Ast.lean`,
`DSL/Target.lean`, `DSL/Pipeline/Lowering.lean`, `DSL/Pipeline/RouteFragments.lean`,
`DSL/Pipeline/RouteSpec.lean`, `DSL/Pipeline/Structural.lean`. None of them consumes a
`CompileError` with an *exhaustive* match over its constructors (`CompileError` only ever appears as
a `throw`/`Except.error` payload in production code, never destructured exhaustively) — the only
`match`es against specific `CompileError` constructors are in test files, and every one carries a
wildcard `| _ => ...` arm. Adding a twentieth constructor (`unsupportedNonlinIterSlot`, alongside the
nineteen already in `Exec/Uid.lean`, counted directly: `grep -c '^  |' Exec/Uid.lean` = 19) cannot
break any existing exhaustiveness obligation.
`throw (.unsupportedNonlinIterSlot nm)` has the exact same type (`String → CompileError`) as the
`throw (.unsupportedNonlinScatter nm)` stand-in verified in §0.4, so the swap changes only the
diagnostic identity, not the code's shape or the proof.

### 0.5 Regression fixture — verified RED against current code

`test/DSL/Pipeline/RouteWeaveTest.lean`'s fixture 16 (donor: fixture 14's
`f14AffineAssign`/`f14RouteRejects` shape, same file — clone, swap the affine/diagonal trigger
slots for `.iterAt`/`.iterNext`, and swap the expected error constructor):

```lean
import LeanNCD.DSL.Compile
import LeanNCD.DSL.Pipeline.RouteFragments
namespace LeanNCD

private def f16Axis : AxisSpec := { name := "l", uid := 1, kind := .nat }
private def f16IterAtSlots : List LHSSlot := [.iterAt f16Axis 2]
private def f16IterNextSlots : List LHSSlot := [.iterNext f16Axis]

private def f16IterAssign (slots : List LHSSlot) (nl : Nonlin) : ScheduledProgram :=
  { decls := []
  , stmts := [.plain (.assign "Y" slots
      { body := { terms := [{ factors := [.read "X" [.axis f16Axis]] }] }, nonlin := nl, agg := .sum })]
  , env := {}
  , extNames := insert "X" (∅ : Finset String)
  , explicitSizes := ∅ }

private def f16RouteRejects (slots : List LHSSlot) (nl : Nonlin) : Bool :=
  match route (f16IterAssign slots nl) |>.run 0 with
  | .error (.unsupportedNonlinIterSlot "Y") _ => true
  | _ => false

#guard f16RouteRejects f16IterAtSlots (.pointwise .relu)
#guard f16RouteRejects f16IterAtSlots (.axiswise .softmax none)
#guard f16RouteRejects f16IterNextSlots (.pointwise .relu)
#guard f16RouteRejects f16IterNextSlots (.axiswise .softmax none)

end LeanNCD
```

`check-snippet.sh` on this exact block today: **DOES NOT COMPILE** —
`error(lean.unknownIdentifier): Unknown constant 'LeanNCD.CompileError.unsupportedNonlinIterSlot'`.
Confirmed RED — and RED in the expected way (the target diagnostic doesn't exist pre-fix), not
merely "assertion false."

The identity-nonlin positive control and the exact pre-fix `fragmentWidth` values were also pinned
directly against current code:

```lean
#guard match route (f16IterAssign f16IterAtSlots .identity) |>.run 0 with
  | .ok tc _ => tc.steps.length == 1
  | .error _ _ => false
-- Pre-fix: nonlinear iterAt currently takes the SPLIT arm (width 2), confirming the bug is a
-- silent mis-route, not a rejection. Post-fix this becomes 0 (rejected).
#guard fragmentWidth ((f16IterAssign f16IterAtSlots (.pointwise .relu)).stmts.getD 0 default) == 2
#guard fragmentWidth ((f16IterAssign f16IterAtSlots .identity).stmts.getD 0 default) == 1
```

`check-snippet.sh` result: **COMPILES** (all three `#guard`s hold against unmodified `main`). This
pins the exact pre-fix numeric baseline (`fragmentWidth = 2`, i.e. `.split`) that Task 1's mutation
cycle flips to `0` (`.rejectNonlinScatter`), and confirms the identity-nonlin control needs no
change (unaffected before and after).

Both fixture blocks are exactly what Task 1 ships. Task 1's own acceptance check is: apply the fix
(§2), re-run fixture 16, confirm the four reject `#guard`s flip to GREEN and the width/identity
`#guard`s continue to hold with the *post-fix* value (`0`, not `2`, for the nonlinear case).

### 0.6 Recurring-defect sibling sweep

`LHSSlot.toReadIdx` has exactly **two production call sites** (grepped across `LeanNCD/`, both
cited in its own doc comment): `RouteFragments.lean`'s `physicalizeOne` (fixed here) and
`Lowering.lean`'s `splitStmt` (`Lowering.lean:64`). A third textual occurrence,
`RouteWeaveTest.lean:272`, is not a third call site in the relevant sense — fixture F6's own
`#guard`-equivalent oracle calls the real `toReadIdx` to *reconstruct* the expected consumer body
for comparison against `physicalizeOne`'s actual output, on `freeNormAxiswiseProg` (`.free`/`.freeNorm`
only, no `.iterAt`/`.iterNext`) — unaffected by this fix either way, and not an independent code path.

`splitStmt` is explicitly **regression-only** — its section header (`Lowering.lean:10-22`) states
"Nothing in `DSL/Compile.lean` or `Eval/` calls them. Do not put them back on the production
chain," and it is used only to build `oldRouteCore`'s comparison value in
`test/DSL/Pipeline/RouteWeaveTest.lean`'s `sameRoutedPresentation`. `splitScan`'s `.scan` arm
(`Lowering.lean:79-82`) runs `splitStmt` over every `base`/`recur` statement — exactly the
statements that legitimately carry `.iterAt`/`.iterNext` — so a nonlinear scan recurrence
(`f7ReluScan`/`f8AxiswiseScan` in `RouteWeaveTest.lean`) *does* trigger `splitStmt`'s identical
`toReadIdx` collapse when the OLD leg runs.

That corrupted value is provably never consumed, though: `routeCore`'s PASS 2
(`Lowering.lean:235-236`, "for `.scan`, the first recurrence stmt... carries the reads/axes") builds
a scan node's routed representation from only its **first** recurrence statement.
`splitStmt`'s output for a split statement is `[linStep, nlStep]` — `linStep` (the linear producer,
`producerSlots`-degraded but otherwise untouched, `toReadIdx` never invoked on it) always comes
first in the resulting recur list; `nlStep` (the one carrying the collapsed `toReadIdx` result) is
never first, so `routeCore` never reads it. This is exactly why `sameRoutedPresentation "F7 relu
scan"`/`"F8 axiswise scan"` already pass on `main` today despite `splitStmt`'s bug: the corrupted
value is generated but structurally unreachable by the only consumer that exists.

**Conclusion: one other call site found, confirmed inert (dead from a soundness perspective, and
provably unobserved by its one live consumer) — no second live instance, no code change needed
there.** Documented as an explicit out-of-scope item (§1) rather than a silent gap.

### 0.7 Doc-location accuracy check

Six locations currently describe this door as open (verified with `grep`/`ls` against `main` @
`f17efc2`, more than the four the fourth-door slice touched — this door has a wider documentation
footprint because it was left open across two prior slices):

1. `LeanNCD/DSL/Pipeline/RouteFragments.lean` — header docstring, the "⚠️ **A third door is open**"
   paragraph.
2. `LeanNCD/DSL/AGENTS.md` — case-table row 6, the "⚠️ A THIRD door is open" sentence.
3. `papers/nonlinearity_split_pair_direct_lowering.md` — §2.4 table, class-6 row, "A third door —
   ... is known open, not yet closed" sentence.
4. `LeanNCD/DSL/Ast.lean` — `LHSSlot.freeUID?`'s own doc comment cross-reference: "see the third
   class-6 door, still open, `RouteFragments.lean`'s header" (line 228).
5. `test/DSL/Pipeline/RouteFragmentCorpusTest.lean` — module header docstring: "one mechanical guard
   forbids the still-open **third class-6 door**" (line 19).
6. `test/DSL/Pipeline/RouteFragmentCorpusTest.lean` — `G23`'s own doc comment: "The door itself
   remains open and is a later slice's work" (lines 405-412).

All six read as accurate against §0.1-§0.2's confirmed current behavior. `G23`'s own guard logic
(`noPlainIterSlots`, asserting none of the 145 corpus cases hit this shape) needs no code change —
it stays true, and stays meaningful as defense-in-depth, whether the door is open or closed (exactly
the same reasoning the fourth door's `G24` guard used, per its own header note). Only its prose
needs updating (§2, Task 2).

`docs/superpowers/plans/2026-08-26-nonlinearity-t2-route-corpus.md` also mentions this door
extensively, but it is a landed, historical slice plan for an already-merged, already-reviewed
piece of work — the fourth-door slice did not update any historical plan document when it closed
its own door, and this slice follows the same precedent: historical plans are a point-in-time
record, not living documentation. Left untouched, deliberately (§1).

---

## §1 Global constraints

- **Current behavior (exact).** `physicalizeForRoute`/public `route`, given a hand-built
  `ScheduledProgram` whose LHS carries `.iterAt`/`.iterNext` on a non-identity-nonlin `.plain
  (.assign …)`, **succeeds** (`.ok`) and emits a two-step split whose consumer reads
  `.axis a` regardless of whether the producer actually wrote at a pinned literal (`.iterAt a n`)
  or a shifted coordinate (`.iterNext a`) — a genuine read/write coordinate disagreement, silently
  accepted. `fragmentWidth` for this shape is currently `2` (`.split`).
- **Target behavior (exact).** The same input returns `.error (CompileError.unsupportedNonlinIterSlot
  "Y")`. `fragmentClass`/`fragmentWidth` agree (`.rejectNonlinScatter`, width `0`) — obligation 5a's
  converse direction, the one `physicalizeOne_length_eq_fragmentWidth` is vacuous on, exercised
  directly by fixture 16.
- **Unreachable from `TLProgram.compile`/public `tlprog!` surface syntax** (§0.2) — same severity
  class as the (closed) `.affine`/diagonal door, strictly less severe than the (closed) fourth door.
  This does not change common-domain error precedence for any surface program.
- **The fix touches exactly two production files**: a new `CompileError.unsupportedNonlinIterSlot`
  constructor (`Exec/Uid.lean`), and `RouteFragments.lean` (a new local `slotsCarryIterSlot`
  predicate, and a broadened reject condition in `fragmentClass`'s and `physicalizeOne`'s nonlinear
  `.assign` arms). No change to `toReadIdx`, `outIdx`, `producerSlots`, `slotsBecomeScatter`, or any
  other shared cross-layer definition (§0.3's conclusion is reject, not route-correctly, so nothing
  downstream of the new reject arm needs to change).
- **`slotsBecomeScatter` itself is NOT touched.** It has three call sites across two layers
  (`Structural.lean`'s `stmtLhsRank`/`lowerArith`, and `RouteFragments.lean`'s
  `fragmentClass`/`physicalizeOne`) — broadening it to also count `.iterAt`/`.iterNext` would make
  `lowerArith` (which runs *before* `finalizeScans`, while these slots are still legitimately
  present on statements about to be grouped into scans) reclassify ordinary scan base/recurrence
  statements into `Stmt.scatter`, corrupting the normal scan pipeline. The new `slotsCarryIterSlot`
  predicate is local to `RouteFragments.lean` (no cross-layer caller, unlike `slotsBecomeScatter`),
  checked only at the post-`finalizeScans` route boundary where the invariant these slots depend on
  ("already grouped into a scan, or genuinely absent") is supposed to already hold.
- **`FragmentClass` gains no new constructor.** The existing `.rejectNonlinScatter` class already
  means "class 6: reject, width 0" for two independently-verified triggers (`slotsBecomeScatter`,
  the pre-existing `.affine`/diagonal trigger; `slotsCarryIterSlot`, this one) — diagnostic
  precision is carried entirely by the `CompileError` payload `physicalizeOne` throws, not by
  `FragmentClass` (§0.3).
- **Out of scope, deliberately:**
  - `Lowering.lean`'s `splitStmt`, the other `toReadIdx` call site — confirmed regression-only,
    dead from a soundness perspective, and its corrupted value is provably never read by its one
    consumer (§0.6). No code change there.
  - `docs/superpowers/plans/2026-08-26-nonlinearity-t2-route-corpus.md` — a landed historical plan,
    left as a point-in-time record, matching the fourth-door slice's own precedent (§0.7).
  - Any change to `toReadIdx`'s definition, or to how a *legitimate* scan (base+recur, correctly
    grouped by `finalizeScans`) is compiled — `.iterAt`/`.iterNext` inside a real scan body are
    unaffected by this fix; only the malformed "orphan iteration slot on a `.plain` node" shape is
    newly rejected.
  - Whether an **identity-nonlin** `.plain (.assign …)` carrying `.iterAt`/`.iterNext` is itself a
    well-formed `ScheduledProgram` — it is copied verbatim today (class 1, unaffected by this fix,
    §0.4's positive control), and whatever downstream risk that shape carries is a *different*,
    un-scoped question (class 6 is specifically about nonlinear writes; this fix stays inside that
    scope, matching the header docstring's own framing of "the third door" as a class-6 door).
- **No `sorry`/`admit`/`axiom` introduced.**

---

## §2 Task breakdown

**Two tasks.** Same reviewer-test boundary as the fourth-door slice: a reviewer could accept the
code fix and its regression fixture while rejecting a doc edit's prose accuracy, or vice versa —
independent failure modes. The code fix itself (new constructor + new local predicate + two
broadened match arms, all in two small, already-verified pieces, §0.4) does not further split: no
sub-piece has an independent failure mode from its neighbours (the constructor is inert without the
predicate consuming it; the predicate is inert without the `fragmentClass`/`physicalizeOne` arms
checking it), so splitting further would fail the "could a reviewer reject one part while approving
the other" test.

| Task | Deliverable | Fixtures | Mutation cycles | Risk driver |
|---|---|---:|---:|---|
| 1 | the fix (`CompileError.unsupportedNonlinIterSlot`, `slotsCarryIterSlot`, broadened `fragmentClass`/`physicalizeOne`) + one regression fixture | 1 (fixture 16, 4 reject `#guard`s + 1 identity-control `#guard` + 2 width `#guard`s) | 1 | the fix's logic is already verified end-to-end in isolation (§0.4); the risk is confirming the full test suite (`lake build Tests`) stays green, especially the nonlinear-scan fixtures (F7/F8) whose `splitStmt` path shares `toReadIdx` but is confirmed inert (§0.6) |
| 2 | doc updates across the 6 locations that documented this as open | 0 | 0 | pure prose-accuracy risk — six locations (not four) must agree with each other and with the actual fixed behavior; `RouteFragmentCorpusTest.lean` has two separate spots (module header + `G23`'s own comment) |

### Task 1 — the fix + regression test

**Outcome.** `CompileError` (`Exec/Uid.lean`) gains `unsupportedNonlinIterSlot`.
`RouteFragments.lean` gains a local `slotsCarryIterSlot` predicate and rejects a nonlinear `.plain
(.assign …)` whose LHS carries it, exactly like the existing `slotsBecomeScatter` trigger. Fixture
16 pins the target behavior.

**Files:**
- `LeanNCD/Exec/Uid.lean` — new `CompileError` constructor.
- `LeanNCD/DSL/Pipeline/RouteFragments.lean` — the fix (`slotsCarryIterSlot`, the broadened
  `fragmentClass`/`physicalizeOne` arms). The file's header docstring is also stale once this
  lands, but that edit is grouped with the other five doc locations in Task 2 (§0.7), matching the
  fourth-door slice's own precedent exactly — its header-paragraph rewrite was Task 2, item 1
  there, not folded into its code task.
- `test/DSL/Pipeline/RouteWeaveTest.lean` — new fixture 16 (donor: `f14AffineAssign`/`f14RouteRejects`,
  same file).

**The `CompileError` addition** (`Exec/Uid.lean`, appended after `unsupportedNonlinScatter`):

```lean
  | unsupportedNonlinIterSlot : String → CompileError        -- the third class-6 door: a nonlinear
                                                               -- `.plain (.assign …)`'s LHS carries a
                                                               -- scan iteration slot (`.iterAt`/
                                                               -- `.iterNext`) at the route boundary.
                                                               -- `finalizeScans` always groups such a
                                                               -- statement into a `.scan` node, so
                                                               -- this shape is reachable only from a
                                                               -- hand-built `ScheduledProgram` that
                                                               -- bypasses that grouping — see
                                                               -- `RouteFragments.lean`'s header and
                                                               -- `slotsCarryIterSlot`
```

**The `RouteFragments.lean` fix** — verified as a unit in §0.4 (only the throw's constructor name
changes from the stand-in verified there):

```lean
/-- Does this LHS carry a scan iteration slot (`.iterAt`/`.iterNext`)? Local to this file (unlike
    `slotsBecomeScatter`, which needs three cross-layer call sites, §1) — mirrors
    `Pipeline/Structural.lean`'s `checkScatterNoScan`'s inline `hasIterSlot`, checked here at the
    route boundary instead of pre-`finalizeScans`: post-`finalizeScans`, EVERY well-formed
    `ScanStmt.plain` has empty `iterInfo` (a stmt with any iteration slot is always grouped into
    `.scan` — see `finalizeScans`'s `plainStmts` filter), so a nonempty result here can only come
    from a hand-built `ScheduledProgram` that bypassed that grouping (the third class-6 door). -/
def slotsCarryIterSlot (slots : List LHSSlot) : Bool :=
  slots.any (fun sl => match sl with | .iterAt .. | .iterNext _ => true | _ => false)
```

`fragmentClass`'s `.plain (.assign _ slots rhs)` arm — both nonlinear cases gain `||
slotsCarryIterSlot slots`:

```lean
def fragmentClass : ScanStmt → FragmentClass
  | .plain (.assign _ slots rhs) =>
      match rhs.nonlin with
      | .identity              => .copy                  -- 1
      | .pointwise _           =>                        -- 2
          if slotsBecomeScatter slots || slotsCarryIterSlot slots then .rejectNonlinScatter
          else .split
      | .axiswise _ _          =>                        -- 3 (no mask) / 4 (mask rides the
                                                         --   consumer, so the width is the same)
          if slotsBecomeScatter slots || slotsCarryIterSlot slots then .rejectNonlinScatter
          else .split
  | .plain (.scatter _ _ rhs _) =>
      match rhs.nonlin with
      | .identity              => .copy                  -- 5
      | .pointwise _           => .rejectNonlinScatter   -- 6  REJECT, never a silent copy
      | .axiswise _ _          => .rejectNonlinScatter   -- 6
  | .plain (.recurMorphism _ _ _) => .copy               -- 7  (carries no RHSExpr)
  | .scan _ _ _ _ _              => .copy                -- 8/9  (verbatim, incl. affine scans)
  | .scanPre _ _ _               => .copy                -- 10 (opaque pre-built morphism)
```

`physicalizeOne`'s `.plain (.assign nm slots rhs)` arm — the `.pointwise _ | .axiswise _ _` branch
gains one more `if`:

```lean
      | .pointwise _ | .axiswise _ _ =>                                             -- 2/3/4
        if slotsBecomeScatter slots then throw (.unsupportedNonlinScatter nm)       -- 6 (`.assign` door)
        else if slotsCarryIterSlot slots then throw (.unsupportedNonlinIterSlot nm) -- 6 (third door)
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
```

**Regression fixture 16** — exact text, verified RED in §0.5, appended to
`RouteWeaveTest.lean` after fixture 15:

```lean
/-! ### Fixture 16 — §2.4 class 6, the third door: a nonlinear `.plain (.assign …)` whose LHS
carries a scan iteration slot (`.iterAt`/`.iterNext`). `finalizeScans` always groups a statement
with a nonempty `iterInfo` into a `.scan` node (never leaves it `.plain`), so this shape is
reachable only from a hand-built `ScheduledProgram` fed straight to `physicalizeForRoute`/`route` —
same reachability class as fixtures 14/15. Before this fix, `toReadIdx` collapsed `.iterAt a n`/
`.iterNext a` to `.axis a`, silently discarding the pinned literal/shift and emitting a
producer/consumer pair with mismatched read/write coordinates (see `RouteFragments.lean`'s header).
Closed here by rejecting instead, mirroring class 6. Asserted at public `route`, mirroring
fixtures 14/15. -/

private def f16Axis : AxisSpec := { name := "l", uid := 1, kind := .nat }
/-- Base-case trigger: a pinned literal write `Y[2]`. -/
private def f16IterAtSlots : List LHSSlot := [.iterAt f16Axis 2]
/-- Recurrence trigger: a shifted write `Y[l+1]`. -/
private def f16IterNextSlots : List LHSSlot := [.iterNext f16Axis]

private def f16IterAssign (slots : List LHSSlot) (nl : Nonlin) : ScheduledProgram :=
  { decls := []
  , stmts := [.plain (.assign "Y" slots
      { body := { terms := [{ factors := [.read "X" [.axis f16Axis]] }] }, nonlin := nl, agg := .sum })]
  , env := {}
  , extNames := insert "X" (∅ : Finset String)
  , explicitSizes := ∅ }

private def f16RouteRejects (slots : List LHSSlot) (nl : Nonlin) : Bool :=
  match route (f16IterAssign slots nl) |>.run 0 with
  | .error (.unsupportedNonlinIterSlot "Y") _ => true
  | _ => false

-- both triggers × both nonlinearity shapes: REJECTED at public `route`.
#guard f16RouteRejects f16IterAtSlots (.pointwise .relu)
#guard f16RouteRejects f16IterAtSlots (.axiswise .softmax none)
#guard f16RouteRejects f16IterNextSlots (.pointwise .relu)
#guard f16RouteRejects f16IterNextSlots (.axiswise .softmax none)
-- the qualifier bites ONLY on a nonlinearity: an IDENTITY `.iterAt` `.assign` is still class 1/copy.
#guard match route (f16IterAssign f16IterAtSlots .identity) |>.run 0 with
  | .ok tc _ => tc.steps.length == 1
  | .error _ _ => false
-- `fragmentClass`/`fragmentWidth` agree with `physicalizeOne`'s rejection (obligation 5a's
-- converse direction, which the theorem is vacuous on).
#guard fragmentWidth ((f16IterAssign f16IterAtSlots (.pointwise .relu)).stmts.getD 0 default) == 0
#guard fragmentWidth ((f16IterAssign f16IterNextSlots (.pointwise .relu)).stmts.getD 0 default) == 0
#guard fragmentWidth ((f16IterAssign f16IterAtSlots .identity).stmts.getD 0 default) == 1
```

**Gate (mutation cycle 1, to be recorded in the SDD ledger by the implementer):**
1. Confirm fixture 16's four reject `#guard`s fail to compile against unfixed `main` (already done
   in this plan, §0.5 — implementer re-confirms by checking out the fixture alone first, OR trusts
   this plan's recorded RED and proceeds directly to the fix, recording that choice).
2. Apply the `Exec/Uid.lean` and `RouteFragments.lean` fixes.
3. `lake build Tests` (or targeted: `RouteWeaveTest`, `RouteFragmentCorpusTest`, `LoweringTest`,
   `ScatterNonlinRejectTest`) — full green, including fixture 16 now passing (with the *post-fix*
   `fragmentWidth` value, `0`, not the pre-fix `2` pinned in §0.5) and every pre-existing fixture
   unchanged, in particular F7/F8 (the nonlinear-scan fixtures whose `splitStmt` leg shares
   `toReadIdx`, confirmed inert in §0.6 — this build is the direct check that inertness holds, not
   just the static argument).
4. Record the observed RED→GREEN flip for fixture 16 in the ledger — this task's mutation cycle.

### Task 2 — doc updates (the door is now closed)

**Outcome.** All six locations (§0.7) that currently document this as an open, unfixed door are
updated to state it is closed, consistently, each pointing at the fix (`slotsCarryIterSlot`,
`CompileError.unsupportedNonlinIterSlot`) and the regression fixture (fixture 16).

**Files and exact edits:**

1. **`LeanNCD/DSL/Pipeline/RouteFragments.lean`** — replace the header docstring's paragraph
   beginning "⚠️ **A third door is open and NOT closed here**" (currently between the "two known
   doors, both closed here" paragraph and the "✅ A fourth door" paragraph) with:
   ```
   ✅ **A third door was open and is now CLOSED** (found in review, recorded in the SDD ledger,
   closed here): `toReadIdx` also collapsed `.iterAt a n` and `.iterNext a` to `axis a`, discarding
   the pinned literal `n` / the `+1` shift — so a `.plain (.assign …)` carrying an iteration slot (a
   shape `finalizeScans` should already have grouped into a `.scan` node, and only a hand-built
   schedule can still present here) took the split arm and emitted a producer/consumer pair whose
   read and write coordinates disagreed. Same reachability class as the two doors above (unreachable
   from `compile`).

   Fixed not by correcting `toReadIdx` — `.iterAt`/`.iterNext` slots have no defined meaning on a
   `.plain` (non-scan) node: outside a scan body there is no "current iteration" for `.iterNext`'s
   `+1` to shift relative to, and per `LHSSlot.outIdx` itself, `.iterAt a n`/`.iterNext a` write the
   exact same coordinates as `.affine (.const n)`/`.affine (.shift a 1)` — a standalone `.plain`
   node carrying either slot IS a scatter-shaped write in every way that matters at this boundary,
   just one `slotsBecomeScatter` was never asked to look for (deliberately: inside a REAL scan body
   these slots are not scatter-shaped at all, see `LHSSlot.isAffine`). Rejected instead, mirroring
   class 6's existing policy: a new local predicate `slotsCarryIterSlot` (this file — local because,
   unlike `slotsBecomeScatter`, it has no cross-layer caller) flags any `.iterAt`/`.iterNext` slot,
   and `fragmentClass`/`physicalizeOne`'s nonlinear `.assign` arms reject when it holds, with a new
   `CompileError.unsupportedNonlinIterSlot` diagnostic — `unsupportedNonlinScatter` would have been
   a misnomer, since these slots never become a scatter through the surface compiler; they only
   behave like one when illegally isolated from the scan grouping that should own them. See
   `test/DSL/Pipeline/RouteWeaveTest.lean`'s fixture 16 for the regression.
   ```
   Leave the fourth-door paragraph immediately below this one unchanged.

2. **`LeanNCD/DSL/AGENTS.md`** — in the case-table row for class 6, replace the text beginning
   "⚠️ A THIRD door is open and not yet closed:" through "See the SDD ledger's whole-branch-review-fix
   entries for the reproduction." (three sentences: the open-door statement, the naming-decision
   deferral, and the SDD-ledger pointer — all three are stale post-fix) with:
   ```
   ✅ A THIRD door was found and is now CLOSED: `toReadIdx` collapsed `.iterAt a n`/`.iterNext a` to
   `axis a`, discarding the pinned literal/shift — a `.plain (.assign …)` carrying an iteration slot
   (only reachable via a hand-built schedule; `finalizeScans` always groups this shape into a
   `.scan`) took the split arm with mismatched read/write coordinates. Fixed not by correcting
   `toReadIdx` but by rejecting: `.iterAt a n`/`.iterNext a` write the same coordinates as
   `.affine (.const n)`/`.affine (.shift a 1)` (per `LHSSlot.outIdx`) when isolated from a real scan
   body, so a new local `slotsCarryIterSlot` predicate (`RouteFragments.lean`) flags them and
   `fragmentClass`/`physicalizeOne` reject with the new `CompileError.unsupportedNonlinIterSlot`
   diagnostic (`unsupportedNonlinScatter` would have been a misnomer here). See
   `RouteFragments.lean`'s header and regression fixture 16 (`RouteWeaveTest.lean`).
   ```
   Leave the fourth-door sentence immediately after it unchanged.

3. **`papers/nonlinearity_split_pair_direct_lowering.md`** — in §2.4's class-6 table row, replace
   the sentence beginning "A third door — `.iterAt`/`.iterNext` LHS slots" through "the slice's SDD
   ledger for the reproduction." with the same closed-door text as location 2 above (the fourth-door
   slice's own precedent already established these two locations are not byte-identical to each
   other pre-existing, so no verbatim-equality convention is broken by using the same text here).

4. **`LeanNCD/DSL/Ast.lean`** — in `LHSSlot.freeUID?`'s doc comment, replace "see the third class-6
   door, still open, `RouteFragments.lean`'s header" with "see the third class-6 door (now closed),
   `RouteFragments.lean`'s header" — a two-word change, keeping the rest of the sentence (this
   comment's point — `freeUID?` is NOT `axisUID?` because `iterAt`/`iterNext` repeats mean something
   different — is unaffected by the third door's closure and stays accurate as-is).

5. **`test/DSL/Pipeline/RouteFragmentCorpusTest.lean`** — module header docstring: replace "and one
   mechanical guard forbids the\nstill-open **third class-6 door**." with "and one mechanical guard
   defends against the **third class-6 door** (now closed, see `RouteFragments.lean`'s header) ever
   appearing in this corpus."

6. **`test/DSL/Pipeline/RouteFragmentCorpusTest.lean`** — `G23`'s doc comment (lines 405-412):
   replace the whole comment block with:
   ```
   /-! ### G23 — the third class-6 door stays shut for this corpus

   `LHSSlot.toReadIdx` still collapses `.iterAt a n` and `.iterNext a` to `.axis a`, discarding the
   pinned literal / the `+1` shift — that definition is unchanged — but `physicalizeOne` now rejects
   a `.plain (.assign …)` carrying an iteration slot before ever reaching that call
   (`CompileError.unsupportedNonlinIterSlot`), so the door itself is CLOSED (`RouteFragments.lean`'s
   header, `slotsCarryIterSlot`). `finalizeScans` structurally cannot produce this shape, but this
   corpus bypasses `finalizeScans` — so the invariant is ASSERTED here rather than inherited. This
   guard stays as defense-in-depth, so a future corpus family that does hit the shape fails loud
   instead of silently mis-routing. -/
   ```
   `plainIterSlots`/`noPlainIterSlots`/the `run_cmd check` line (lines 414-421) are unchanged — the
   guard's own logic (and the `#guard` at line 806 reusing `plainIterSlots`) stays exactly as-is,
   matching the fourth door's `G24` precedent of keeping a superseded-but-still-true guard as
   defense-in-depth.

**Gate:** re-read each edited location once, side by side with the fix's actual behavior (§0.4/§2
Task 1), confirming no location claims the door is open and no location's fix description
contradicts another's, and every location's cross-reference (`slotsCarryIterSlot`,
`unsupportedNonlinIterSlot`, fixture 16) actually exists post-Task-1. No `lake build` needed for
any of the six edits — all are doc-comment or prose-only (1, 4 edit `.lean` doc comments; 2, 3 edit
`.md` files; 5, 6 edit `.lean` doc comments in a test file) — but confirm 5/6's edits stay inside
the doc-comment boundary and don't spill into or truncate `plainIterSlots`/`noPlainIterSlots`/the
`run_cmd check` line (items 5 and 6 both touch `RouteFragmentCorpusTest.lean`).

---

## §3 Review plan

**One review pass**, covering both tasks together. Justification, by the same standard the
fourth-door slice used: the fix is two small, already-verified pieces (a new inert-until-consumed
`CompileError` constructor, and one local predicate consumed by two already-existing match arms)
with a single already-verified end-to-end behavior test (§0.4); the recurring-defect sibling sweep
(§0.6) already ran at planning time and found exactly one other call site, confirmed inert with a
structural argument this plan states explicitly (not just "found and dismissed"); and the two
"could a reviewer reject one part while approving the other" seams (fix-vs-fixture, code-vs-docs)
both live inside a diff small enough for one reviewer to hold in full context — even with Task 2's
six locations (up from the fourth door's four), each is a few-sentence prose edit, not new logic.

This does not contradict the skill's "don't skimp on the final whole-branch review" guidance — that
guidance targets slices large enough that a per-task reviewer cannot see a cross-file interaction
(`stepWriteRowsOk` in Wave F F4: the bug lived in a function neither Task 1's nor any other task's
diff touched). Here there is no unchanged-and-therefore-invisible function carrying the risk: the
one place that shares `toReadIdx` with the fix (`Lowering.splitStmt`) is not part of this diff at
all, and §0.6 gives an explicit, checkable reason (not a diff-shaped one) for why it needs no
change — exactly the kind of "sibling that a diff review structurally cannot see" the skill asks a
plan to name up front, done here at planning time rather than left for a reviewer to rediscover.

The review must independently check:
- the `Exec/Uid.lean` diff is exactly the one new constructor;
- the `RouteFragments.lean` diff is exactly `slotsCarryIterSlot` plus the two broadened `if`
  conditions plus the header paragraph rewrite — no other function touched, and in particular that
  `slotsBecomeScatter` itself is untouched (§1's "why not" is a real constraint, not a style choice —
  broadening it would corrupt scan compilation, so a reviewer should treat any diff touching
  `slotsBecomeScatter` in this slice as an automatic reject pending investigation);
- fixture 16 actually exercises both `.iterAt` and `.iterNext` triggers (not a copy-paste that
  silently reverted to an affine/diagonal trigger — compare against `f14AffineSlots`/`f14DiagSlots`
  textually) and that its width/identity `#guard`s carry the *post-fix* value (`0`, not the pre-fix
  `2` this plan pinned in §0.5);
- the full test suite (`lake build`) is green, specifically including F7/F8 (§0.6's inertness claim)
  and every fixture named in Task 1's gate;
- all six Task-2 locations agree with each other and with the actual fixed behavior (re-run §0.1's
  repro one more time post-fix, confirming it now returns `.error (.unsupportedNonlinIterSlot "Y")`
  for both the `.iterAt` and `.iterNext` cases, and compare against what the docs now claim).

If this single pass surfaces anything unexpected (a fixture failing for a reason other than the
targeted shape, F7/F8 actually regressing, or a doc location this plan did not anticipate),
escalate to a second independent reviewer before merging — per the standing "scale process to task
risk" practice — rather than patching around it in the same pass.

---

## §4 Stop conditions

- Any existing fixture (F1-F11, F13-F16, G1-G26, P1-P3, the `LoweringTest.lean` `PRODUCERSLOTS`
  fixture, RSN1-RSN5, or anything else touched by `lake build Tests`) regresses after the fix —
  stop, do not paper over it with a scope change to those fixtures; the fix is expected to be
  behavior-preserving everywhere except the exact bug shape. In particular, F7/F8 regressing would
  falsify §0.6's inertness argument — stop and re-investigate `splitStmt`'s reachability rather than
  assuming the argument still holds.
- Fixture 16 fails to flip to GREEN after applying exactly the `Exec/Uid.lean`/`RouteFragments.lean`
  edits in §2 — stop; this plan's §0.3/§0.4 reasoning has a gap that needs to be found before
  proceeding, not worked around with a different code change.
- Any doc location's post-fix text is found to still describe behavior that doesn't match a fresh
  re-run of §0.1's repro — stop and correct the text; do not merge a doc claim that hasn't been
  checked against the actual post-fix behavior.
- If, during implementation, `.iterAt`/`.iterNext` turn out to have some legitimate non-scan reading
  this plan's §0.3 investigation missed — stop; do not silently switch from "reject" to "route
  correctly" mid-implementation. That would be a different, larger fix (real semantic preservation,
  not a rejection guard) needing its own re-planned task breakdown, not a same-task pivot.

## §5 Definition of done

- `CompileError.unsupportedNonlinIterSlot` exists (`Exec/Uid.lean`), matching §2 Task 1's exact
  text.
- `RouteFragments.lean` has `slotsCarryIterSlot` and the broadened `fragmentClass`/`physicalizeOne`
  arms, matching §2 Task 1's exact blocks.
- Fixture 16 (`RouteWeaveTest.lean`) exists, passes, and was observed to fail (unknown identifier)
  before the fix and pass after (recorded in the SDD ledger), with the width `#guard`s carrying the
  post-fix value.
- `lake build Tests` (or the full `lake build`) is green, including F7/F8.
- All six Task-2 locations (`RouteFragments.lean`'s header, `AGENTS.md`, the papers doc, `Ast.lean`,
  and `RouteFragmentCorpusTest.lean`'s two spots) read as closed, consistently, and were re-checked
  against a post-fix re-run of §0.1's repro.
- No `sorry`/`admit`/`axiom` introduced; no production file touched other than `Exec/Uid.lean` and
  `RouteFragments.lean`.
- Per Rule 13 (standing decisions): once both tasks are green and this plan's final review pass
  (§3) is clean or its findings adjudicated, merge to local `main`, delete the branch, and remove
  the worktree.

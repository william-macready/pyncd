-- test/DSL/Pipeline/RouteFragmentCorpusTest.lean
import LeanNCD.DSL.Pipeline.Lowering
import LeanNCD.Bridge.AcsetCodec
import DSL.Pipeline.RouteWeaveTest

/-!
# Durable nonlinear route corpus

`papers/nonlinearity_split_pair_direct_lowering.md` §3.4, slice T2 Task 1
(`docs/superpowers/plans/2026-08-26-nonlinearity-t2-route-corpus.md`).

A deterministic generator materializes exactly **145** cases in **13** families. The **137**
common-domain cases must compare *exactly* equal — complete `ThreadedComposed`, ACSet encoding, and
ACSet decode∘encode round trip — between the OLD split pipeline and production's public `route` on
the LOGICAL schedule. The eight deliberate `%nl0` collisions pin the old-rejection/new-acceptance
transition. The five scan families pin categorical opacity, and one mechanical guard forbids the
still-open **third class-6 door**.

⚠️ **145 corpus cases, not 145 distinct programs.** `chainProgram`'s `ScheduledProgram` depends on
`n` only through `n % 4` (its LHS names are `H{q}`, never `H{n}{q}`), so the 32 `chains` cases are 4
distinct shapes repeated 8× each. Every other family varies genuinely per case (`contractionProgram`
names its output `Y{n}`, so its 24 cases stay distinct despite `idxs` cycling on `n % 3`). Measured:
**117 distinct `ScheduledProgram` values out of 145** (found in review, 2026-08-26). This is
inherited from `RouteFragmentCorpusSeed.lean` verbatim, per the plan's transplant requirement — not
an implementation defect — but the count is worth stating honestly rather than read as 145
independent structural shapes. The repeats are not wasted: they still confirm route equality holds
identically on repeated calls to the same generator, which has some determinism value even where it
adds no new structural coverage.

## The old leg terminates at `routeCore`, never at public `route`

Public `route` *physicalizes*. Handing it an already-split program splits the still-nonlinear
consumer a **second** time (2 physical steps become 3) — pinned independently by
`test/DSL/Pipeline/RouteFragmentDiagnosticTest.lean`'s case 19, and documented on `route`'s own
docstring in `LeanNCD/DSL/Pipeline/Lowering.lean`. So `oldTC`/`oldErr` below stop at `routeCore` and
assemble the `ThreadedComposed` by hand; only `newTC` calls public `route`.

## Relationship to `test/DSL/Pipeline/RouteWeaveTest.lean`

That module carries the same old-vs-new differential at the **source** level: its legs are
`TLProgram → ScanProgram → FreshM (List BrBaseP × List (List Wire))` (`oldRouteCore`/`newRouteCore`).
This module's corpus is hand-built `ScheduledProgram`s and its legs are
`ScheduledProgram → Option ThreadedComposed`. The signatures do not meet, so the ~10 lines below are
deliberately local rather than factored out of `RouteWeaveTest`; that file is imported here only for
the public `freeNormAxiswiseProg` (G25) and is otherwise untouched.

## No local physicalizer

Production `physicalizeForRoute` (via `route`, or called directly) is the only physicalization in
this file. The corpus is generated as LOGICAL schedules; nothing here reimplements the
producer/consumer split, mints a private name, or re-checks fragment layout. Every mutation cycle
recorded in the SDD ledger mutates **production** `LeanNCD/DSL/Pipeline/RouteFragments.lean`.

## Why the corpus is hand-built rather than `tlprog!` sources

§3.4 wants the *route boundary* exercised over the widened caller set §2.4 admits — hand-built
logical schedules handed straight to `route`. No case here goes through `tlprog!`, `assignUIDs`,
`lowerArith`, or `finalizeScans` (the single source-level cross-check is G25). Rewriting a family as
surface syntax would silently shrink what it covers.
-/

namespace RouteFragmentCorpusTest

open LeanNCD Std
open LeanNCD.AcsetCodec

/-! ## §1 The deterministic 145-case generator (13 families) -/

inductive Family
  | chains | contractions | freeNormPositions | branches | repeatedReads
  | unreadOutputs | adversarialNames | nl0Collisions | nonlinearBase
  | nonlinearRecurrence | aroundScans | coupledScans | multiAxisScans
  deriving DecidableEq, Repr

structure CorpusCase where
  id : Nat
  family : Family
  logical : ScheduledProgram
  collision : Bool

def mkAxis (name : String) (uid : Nat) (kind := AxisKind.real) : AxisSpec :=
  { name, uid, kind }

def i := mkAxis "i" 1
def j := mkAxis "j" 2
def k := mkAxis "k" 3
def l := mkAxis "l" 4 .nat
def m := mkAxis "m" 5 .nat

def rhs (name : String) (idxs : List IdxExpr) (nonlin := Nonlin.identity) : RHSExpr :=
  { body := { terms := [{ factors := [.read name idxs] }] }, nonlin }

def rhs2 (a : String) (ai : List IdxExpr) (b : String) (bi : List IdxExpr)
    (nonlin := Nonlin.identity) : RHSExpr :=
  { body := { terms := [{ factors := [.read a ai, .read b bi] }] }, nonlin }

def scheduled (stmts : List ScanStmt) (exts : Finset String)
    (decls : List Decl := []) : ScheduledProgram :=
  { decls, stmts, env := {}, extNames := exts, explicitSizes := {} }

/-- Nonlinear chains of depth 1–4, alternating `relu`/`tanh`. -/
def chainProgram (n : Nat) : ScheduledProgram :=
  let depth := n % 4 + 1
  let stmts := (List.range depth).map fun q =>
    let input := if q == 0 then "X" else s!"H{q - 1}"
    .plain (.assign s!"H{q}" [.free i]
      (rhs input [.axis i] (.pointwise (if q % 2 == 0 then .relu else .tanh))))
  scheduled stmts {"X"}

/-- Rank-1/2/3 contracted reads under one pointwise nonlinearity. -/
def contractionProgram (n : Nat) : ScheduledProgram :=
  let idxs := match n % 3 with
    | 0 => [.axis i]
    | 1 => [.axis i, .axis j]
    | _ => [.axis i, .axis j, .axis k]
  scheduled [.plain (.assign s!"Y{n}" [.free i]
    (rhs "X" idxs (.pointwise .relu)))] {"X"}

/-- The `.freeNorm` marker in each of the three LHS slot positions. -/
def freeNormProgram (n : Nat) : ScheduledProgram :=
  let slots := match n % 3 with
    | 0 => [.freeNorm i, .free j, .free k]
    | 1 => [.free i, .freeNorm j, .free k]
    | _ => [.free i, .free j, .freeNorm k]
  scheduled [.plain (.assign s!"N{n}" slots
    (rhs "X" [.axis i, .axis j, .axis k] (.axiswise .softmax none)))] {"X"}

/-- Two nonlinear branches joined by one identity statement. -/
def branchProgram (n : Nat) : ScheduledProgram :=
  scheduled [
    .plain (.assign s!"A{n}" [.free i] (rhs "X" [.axis i] (.pointwise .relu))),
    .plain (.assign s!"B{n}" [.free i] (rhs "X" [.axis i] (.pointwise .tanh))),
    .plain (.assign s!"Y{n}" [.free i]
      (rhs2 s!"A{n}" [.axis i] s!"B{n}" [.axis i]))
  ] {"X"}

/-- One nonlinear output read TWICE by the same downstream statement. -/
def repeatedProgram (n : Nat) : ScheduledProgram :=
  scheduled [
    .plain (.assign s!"A{n}" [.free i] (rhs "X" [.axis i] (.pointwise .relu))),
    .plain (.assign s!"Y{n}" [.free i]
      (rhs2 s!"A{n}" [.axis i] s!"A{n}" [.axis i]))
  ] {"X"}

/-- A second nonlinear output that nothing reads (no DCE may remove it). -/
def unreadProgram (n : Nat) : ScheduledProgram :=
  scheduled [
    .plain (.assign s!"Primary{n}" [.free i] (rhs "X" [.axis i] (.pointwise .relu))),
    .plain (.assign s!"Unread{n}" [.free i] (rhs "X" [.axis i] (.pointwise .sigmoid)))
  ] {"X"}

/-- Adversarial names: an all-`#` LHS of growing length against a `%`-bearing external. -/
def adversarialProgram (n : Nat) : ScheduledProgram :=
  let longName := String.ofList (List.replicate (n + 8) '#')
  scheduled [.plain (.assign longName [.free i]
    (rhs "escaped%source" [.axis i] (.pointwise .relu)))] {"escaped%source"}

/-- A source tensor literally named `%nl0` — the name the OLD split pipeline would mint. -/
def collisionProgram (n : Nat) : ScheduledProgram :=
  scheduled [
    .plain (.assign "%nl0" [] (rhs "X" [])),
    .plain (.assign s!"Y{n}" [] (rhs "%nl0" [] (.pointwise .relu)))
  ] {"X"}

def scanNode (baseNonlin recurNonlin : Nonlin) (name : String) : ScanStmt :=
  .scan name [l]
    [.assign name [.free i, .iterAt l 0] (rhs "X" [.axis i] baseNonlin)]
    [.assign name [.free i, .iterNext l]
      (rhs name [.axis i, .axis l] recurNonlin)]
    false

def nonlinearBaseProgram (n : Nat) : ScheduledProgram :=
  scheduled [scanNode (.pointwise .relu) .identity s!"S{n}"] {"X"} [.iter l 3]

def nonlinearRecurrenceProgram (n : Nat) : ScheduledProgram :=
  scheduled [scanNode .identity (.pointwise .relu) s!"S{n}"] {"X"} [.iter l 3]

/-- Nonlinear plain statements on BOTH sides of an opaque scan node. -/
def aroundScanProgram (n : Nat) : ScheduledProgram :=
  let a := s!"A{n}"; let s := s!"S{n}"; let y := s!"Y{n}"
  scheduled [
    .plain (.assign a [.free i] (rhs "X" [.axis i] (.pointwise .relu))),
    .scan s [l]
      [.assign s [.free i, .iterAt l 0] (rhs a [.axis i])]
      [.assign s [.free i, .iterNext l] (rhs s [.axis i, .axis l])]
      true,
    .plain (.assign y [.free i, .free l]
      (rhs s [.axis i, .axis l] (.pointwise .tanh)))
  ] {"X"} [.iter l 3]

def coupledProgram (n : Nat) : ScheduledProgram :=
  let a := s!"A{n}"; let b := s!"B{n}"
  scheduled [
    .scan a [l]
      [.assign a [.free i, .iterAt l 0] (rhs "X" [.axis i]),
       .assign b [.free i, .iterAt l 0] (rhs "Z" [.axis i])]
      [.assign a [.free i, .iterNext l]
        (rhs2 a [.axis i, .axis l] b [.axis i, .axis l] (.pointwise .relu)),
       .assign b [.free i, .iterNext l]
        (rhs2 b [.axis i, .axis l] a [.axis i, .axis l])]
      false
  ] {"X", "Z"} [.iter l 3]

def multiAxisProgram (n : Nat) : ScheduledProgram :=
  let s := s!"M{n}"
  scheduled [
    .scan s [l, m]
      [.assign s [.free i, .iterAt l 0, .iterAt m 0] (rhs "X" [.axis i])]
      [.assign s [.free i, .iterNext l, .iterNext m]
        (rhs s [.axis i, .axis l, .axis m] (.pointwise .relu))]
      false
  ] {"X"} [.iter l 3, .iter m 2]

def generateFamily (family : Family) (count offset : Nat)
    (mk : Nat → ScheduledProgram) (collision := false) : List CorpusCase :=
  (List.range count).map fun n =>
    { id := offset + n, family, logical := mk n, collision }

/-- The corpus. Offsets are contiguous by construction (G2 pins it). -/
def corpus : List CorpusCase :=
  generateFamily .chains 32 0 chainProgram ++
  generateFamily .contractions 24 32 contractionProgram ++
  generateFamily .freeNormPositions 9 56 freeNormProgram ++
  generateFamily .branches 8 65 branchProgram ++
  generateFamily .repeatedReads 8 73 repeatedProgram ++
  generateFamily .unreadOutputs 8 81 unreadProgram ++
  generateFamily .adversarialNames 8 89 adversarialProgram ++
  generateFamily .nl0Collisions 8 97 collisionProgram true ++
  generateFamily .nonlinearBase 8 105 nonlinearBaseProgram ++
  generateFamily .nonlinearRecurrence 8 113 nonlinearRecurrenceProgram ++
  generateFamily .aroundScans 8 121 aroundScanProgram ++
  generateFamily .coupledScans 8 129 coupledProgram ++
  generateFamily .multiAxisScans 8 137 multiAxisProgram

def countFamily (family : Family) : Nat :=
  (corpus.filter (·.family == family)).length

def isScanFamily : Family → Bool
  | .nonlinearBase | .nonlinearRecurrence | .aroundScans | .coupledScans |
      .multiAxisScans => true
  | _ => false

/-! ## §2 The two comparison legs

Both are stated over a LOGICAL `ScheduledProgram`. See the module header for why the OLD leg must
stop at `routeCore`. Mirrors `RouteWeaveTest`'s `oldRouteCore`/`newRouteCore` at a different type.
-/

def toLinear (sp : ScheduledProgram) : LinearProgram :=
  { decls := sp.decls, stmts := sp.stmts, env := sp.env, extNames := sp.extNames }

/-- OLD leg: `splitNonlins → schedule → routeCore`, wrapped into a complete `ThreadedComposed`.
    It must NOT end at public `route`: `route` physicalizes, so it would split the already-split
    consumer a second time (2 steps become 3). -/
private def oldRun (sp : ScheduledProgram) : FreshM ThreadedComposed := do
  let split ← splitNonlins (toLinear sp)
  let ordered ← schedule split
  match routeCore { ordered with explicitSizes := sp.explicitSizes } with
  | .error e => throw e
  | .ok (steps, routing) =>
      return ({ steps, routing, nExternal := ordered.extNames.card } : ThreadedComposed)

def oldTC (sp : ScheduledProgram) : Option ThreadedComposed :=
  match (oldRun sp).run 0 with
  | .ok tc _ => some tc
  | .error .. => none

/-- `oldTC`'s error companion: the same `oldRun`, reporting the `CompileError` instead of the value.
    Supplies the `%nl0` family's old-rejection observation (G21). -/
def oldErr (sp : ScheduledProgram) : Option CompileError :=
  match (oldRun sp).run 0 with
  | .ok .. => none
  | .error e _ => some e

/-- NEW leg: public `route` on the LOGICAL schedule — one physicalization, production code. -/
def newTC (sp : ScheduledProgram) : Option ThreadedComposed :=
  match (route sp).run 0 with
  | .ok tc _ => some tc
  | .error .. => none

/-- The OLD leg's own intermediate — `oldTC` stopped one phase early, before `routeCore`. Needed
    only by G22, which observes that `splitNonlins` rewrites scan BODIES while the complete routes
    stay equal. Production `splitNonlins`/`schedule` only; this is not a physicalizer. -/
def oldSplitSchedule? (sp : ScheduledProgram) : Option ScheduledProgram :=
  match (do
      let split ← splitNonlins (toLinear sp)
      schedule split).run 0 with
  | .ok sched _ => some sched
  | .error .. => none

/-! ## §3 Guards -/

private def failingIds (p : CorpusCase → Bool) : List Nat :=
  (corpus.filter (fun c => !p c)).map (·.id)

/-- Report a guard as `<label>: N FAILURES, ids [...]`, so a mutation cycle yields an OBSERVED
    count rather than a bare `false`. -/
private def check (label : String) (p : CorpusCase → Bool) :
    Lean.Elab.Command.CommandElabM Unit := do
  let bad := failingIds p
  unless bad.isEmpty do
    throwError s!"{label}: {bad.length} FAILURES, ids {bad}"

/-! ### G1–G19 — the shape of the corpus itself -/

#guard corpus.length == 145                                                          -- G1
#guard (corpus.map (·.id)) == List.range 145                                         -- G2
#guard countFamily .chains == 32                                                     -- G3
#guard countFamily .contractions == 24                                               -- G4
#guard countFamily .freeNormPositions == 9                                           -- G5
#guard countFamily .branches == 8                                                    -- G6
#guard countFamily .repeatedReads == 8                                               -- G7
#guard countFamily .unreadOutputs == 8                                               -- G8
#guard countFamily .adversarialNames == 8                                            -- G9
#guard countFamily .nl0Collisions == 8                                               -- G10
#guard countFamily .nonlinearBase == 8                                               -- G11
#guard countFamily .nonlinearRecurrence == 8                                         -- G12
#guard countFamily .aroundScans == 8                                                 -- G13
#guard countFamily .coupledScans == 8                                                -- G14
#guard countFamily .multiAxisScans == 8                                              -- G15
#guard (corpus.filter fun c => !c.collision).length == 137                           -- G16
#guard (corpus.filter (·.collision)).length == 8                                     -- G17
#guard (corpus.filter fun c => isScanFamily c.family).length == 40                   -- G18
#guard (corpus.filter fun c =>
          isScanFamily c.family && c.family != .aroundScans).length == 32            -- G19

/-! ### G20 — the 137 common-domain cases are EXACTLY equal

Complete `ThreadedComposed`, ACSet encoding, ACSet decode∘encode identity, and `wellFormedDom`. -/

def commonExact (c : CorpusCase) : Bool :=
  if c.collision then true else
    match oldTC c.logical, newTC c.logical with
    | some old, some new =>
        old == new &&
        fromThreadedComposed old == fromThreadedComposed new &&
        toThreadedComposed (fromThreadedComposed new) == new &&
        new.wellFormedDom
    | _, _ => false

run_cmd check "G20 common-domain exact (137 cases)" commonExact

/-! ### G21 — the eight `%nl0` collisions transition from rejection to acceptance

The OLD pipeline mints `%nl0`, which the source already binds, so `routeCore` sees a self-read and
rejects with `cyclicDataflow`. Physicalization's `routeName` is fresh by construction, so the same
program routes. This is stated separately from G20: the old bug did NOT accept these. -/

def collisionTransition (c : CorpusCase) : Bool :=
  if !c.collision then true else
    match oldErr c.logical, newTC c.logical with
    | some (.cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)"), some new =>
        new.wellFormedDom &&
        toThreadedComposed (fromThreadedComposed new) == new
    | _, _ => false

run_cmd check "G21 collision transition (8 cases)" collisionTransition

/-! ### G22 — scan opacity, pinned separately from aggregate route equality

For all 40 scan cases, `physicalizeForRoute` copies scan payloads byte-for-byte. For the 32 that are
not `aroundScans`, the OLD split leg's payloads DIFFER — `splitNonlins` splits inside scan bodies —
yet the complete routes are still equal. That last half is exactly G20 restricted to these ids (all
40 are non-collision cases), so it is not recomputed here. -/

abbrev ScanPayload := String × List AxisSpec × List Stmt × List Stmt × Bool

def scanPayloads (sp : ScheduledProgram) : List ScanPayload :=
  sp.stmts.filterMap fun
    | .scan name axes base recur isAffine => some (name, axes, base, recur, isAffine)
    | _ => none

def scanPayloadObservation (c : CorpusCase) : Bool :=
  if !isScanFamily c.family then true else
    match physicalizeForRoute c.logical, oldSplitSchedule? c.logical with
    | .ok physical, some old =>
        scanPayloads physical.scheduled == scanPayloads c.logical &&
        (if c.family == .aroundScans then
            scanPayloads old == scanPayloads c.logical
          else
            scanPayloads old != scanPayloads c.logical)
    | _, _ => false

run_cmd check "G22 scan payload opacity (40 cases, 32 split-body)" scanPayloadObservation

/-! ### G23 — the third class-6 door stays shut for this corpus

`LHSSlot.toReadIdx` collapses `.iterAt a n` and `.iterNext a` to `.axis a`, discarding the pinned
literal / the `+1` shift, so a `.plain (.assign …)` carrying an iteration slot would take
`physicalizeOne`'s split arm and emit a producer/consumer pair whose read and write coordinates
disagree. `finalizeScans` structurally cannot produce that shape, but this corpus bypasses
`finalizeScans` — so the invariant is ASSERTED here rather than inherited. The door itself remains
open and is a later slice's work (`LeanNCD/DSL/Pipeline/RouteFragments.lean`'s header). -/

def plainIterSlots (sp : ScheduledProgram) : Bool :=
  sp.stmts.any fun
    | .plain s => !s.iterInfo.isEmpty
    | _ => false

def noPlainIterSlots (c : CorpusCase) : Bool := !plainIterSlots c.logical

run_cmd check "G23 third class-6 door (no .plain with an iteration slot)" noPlainIterSlots

/-! ### G24 — `.freeNorm` degradation, asserted STRUCTURALLY

⚠️ This guard must NOT be phrased as route equality. Measured directly (slice plan §0.7):
physicalizing all three `.freeNorm` slot positions *without* the `producerSlots` degrade yields a
routed presentation IDENTICAL to production's, because `.free a` and `.freeNorm a` weave the same
axes (see `producerSlots`' docstring in `LeanNCD/DSL/Ast.lean`). A corpus-wide route comparison is
therefore structurally incapable of catching this mutation at ANY case count. The only guard with
teeth compares the producer's SLOT LIST. -/

private def slotsHaveFreeNorm (slots : List LHSSlot) : Bool :=
  slots.any fun | .freeNorm _ => true | _ => false

def freeNormStructural (c : CorpusCase) : Bool :=
  if c.family != .freeNormPositions then true else
    match c.logical.stmts, physicalizeForRoute c.logical with
    | [.plain (.assign _ slots _)], .ok physical =>
        match physical.scheduled.stmts with
        | [.plain (.assign _ producer _), .plain (.assign _ consumer _)] =>
            -- the logical statement really does carry the marker …
            slotsHaveFreeNorm slots &&
            -- … the PRODUCER degrades it, exactly as `producerSlots` prescribes …
            producer == producerSlots slots && !slotsHaveFreeNorm producer &&
            -- … and the CONSUMER keeps it.
            consumer == slots && slotsHaveFreeNorm consumer
        | _ => false
    | _, _ => false

run_cmd check "G24 .freeNorm structural degrade (9 cases)" freeNormStructural

/-! ### G25 — the single source-level `.freeNorm` cross-check

`RouteWeaveTest.freeNormAxiswiseProg` is public for exactly this purpose (its own docstring says
so). Everything else in this file is hand-built, so this is the one case in THIS module going
through the real `tlprog!` surface pipeline (`assignUIDs`/`lowerArith`/`finalizeScans`) rather than
a directly-constructed `ScheduledProgram`. `RouteWeaveTest`'s own fixture 6 already asserts the same
producer/consumer slot relationship on this exact program (and more: internal name, full payloads)
— G25 does not add coverage `RouteWeaveTest` lacks, it corroborates it from the corpus module's own
hand-built-vs-surface-syntax boundary. -/

run_cmd do
  match (TLProgram.compileToScheduled freeNormAxiswiseProg).run 0 with
  | .error e _ => throwError s!"G25: compileToScheduled failed: {repr e}"
  | .ok logical _ =>
      unless logical.stmts.length == 1 do
        throwError s!"G25: expected 1 LOGICAL stmt, got {logical.stmts.length}"
      match physicalizeForRoute logical with
      | .error e => throwError s!"G25: physicalizeForRoute failed: {repr e}"
      | .ok physical =>
          unless physical.scheduled.stmts.length == 2 do
            throwError s!"G25: expected 2 PHYSICAL stmts, got {physical.scheduled.stmts.length}"
          match logical.stmts, physical.scheduled.stmts with
          | [.plain (.assign _ slots _)],
            [.plain (.assign _ producer _), .plain (.assign _ consumer _)] =>
              unless slotsHaveFreeNorm slots do
                throwError "G25: the source statement must carry a `.freeNorm` marker"
              unless producer == producerSlots slots && !slotsHaveFreeNorm producer do
                throwError "G25: the private producer must degrade `.freeNorm` to `.free`"
              unless consumer == slots && slotsHaveFreeNorm consumer do
                throwError "G25: the logical consumer must KEEP the `.freeNorm` marker"
          | _, _ => throwError "G25: unexpected logical/physical statement shape"

end RouteFragmentCorpusTest

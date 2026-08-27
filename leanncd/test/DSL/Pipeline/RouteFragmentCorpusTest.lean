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
transition. The five scan families pin physicalization opacity (G22 — categorical opacity for the
same 40 cases is exactly G20 restricted to those ids, not recomputed separately), and one
mechanical guard forbids the
still-open **third class-6 door**.

⚠️ **145 corpus cases, not 145 distinct programs, and only 16 distinct ROUTED presentations.**
`chainProgram`'s `ScheduledProgram` depends on `n` only through `n % 4` (its LHS names are `H{q}`,
never `H{n}{q}`), so the 32 `chains` cases are 4 distinct shapes repeated 8× each. Every other
family's SOURCE program varies per case (`contractionProgram` names its output `Y{n}`, so its 24
cases stay distinct despite `idxs` cycling on `n % 3`), giving **117 distinct `ScheduledProgram`
values out of 145** (found in review, 2026-08-26) — inherited from `RouteFragmentCorpusSeed.lean`
verbatim, per the plan's transplant requirement, not an implementation defect.

But `ThreadedComposed`/`BrBaseP` carry NO TENSOR NAMES — names enter the routed presentation only
as synthetic external-axis labels (`X_0`, not `X`), so most of that source-level variation is
projected away before G20/G21/P3 ever compare anything. Measured (whole-branch review,
2026-08-27): **only 16 distinct routed `ThreadedComposed` values across all 145 cases** (15 among
the 137 non-collision cases), with multiplicities up to 16. Two cross-family collapses:
`chains`-depth-1 and `contractions`-rank-1 route to the SAME `[contract, relu]` presentation; and
`nonlinearBase`/`nonlinearRecurrence` route to the SAME `[scan]` presentation, because WHICH half
of a scan's recurrence carries the nonlinearity is invisible at the routed level. This does not
weaken G20/G21/P3 — every comparison is still real and independently confirmed correct — but a
prior version of this note claimed "every other family varies genuinely per case" without
qualifying "at the source level, not the routed level", which reads stronger than what the guards
actually exercise. The repeats are not wasted: they confirm route equality holds identically on
repeated/converging inputs, which has determinism value even where it adds no new distinct-route
coverage. G26 below asserts the measured route-diversity floor so a future generator change that
silently collapses coverage further fails the build.

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
        -- non-emptiness is checked explicitly so a scan-family generator that stopped emitting a
        -- `.scan` node would fail here (a byte-identity check on `[] == []` passes vacuously) --
        -- measured today: 0 of 40 scan cases have an empty payload list.
        !(scanPayloads c.logical).isEmpty &&
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
            -- … the degraded producer is not ITSELF scatter-shaped (the fourth class-6 door,
            -- found in whole-branch review 2026-08-27 and CLOSED by broadening `freeUID?`
            -- (`Ast.lean`) to also count `.freeNorm` UIDs — see `RouteFragments.lean`'s header.
            -- A `[.free a, .freeNorm a]` logical LHS is now rejected by `checkScatterNonlin`
            -- before physicalization ever runs, so this conjunct is unreachable-false by
            -- construction rather than merely untested; kept as defense-in-depth, so a future
            -- case that does hit the shape fails the build instead of silently mis-routing) …
            !slotsBecomeScatter producer &&
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

/-! ### G26 — the corpus's actual route-diversity floor

The header's ⚠️ note above measures 16 distinct routed `ThreadedComposed` values across the 145
cases (15 among the 137 non-collision cases) — far fewer than 145, because `ThreadedComposed`
carries no tensor names. This does not weaken G20/G21/P3 (every individual comparison is still a
real, independently-checked equality), but a future edit to any generator that collapses coverage
FURTHER should fail the build rather than silently shrink what the corpus actually distinguishes. -/

run_cmd do
  let distinctRoutes := (corpus.filterMap (fun c => newTC c.logical)).eraseDups
  unless distinctRoutes.length == 16 do
    throwError s!"G26: expected 16 distinct routed presentations, got {distinctRoutes.length}"

/-! ## §4 The 19-case named payload matrix (slice T2 Task 2)

Nineteen **named** fixtures, each a clone of a specific existing donor with **exactly one field
changed**, counted entirely separately from §1's 145 generated cases. `fixtures` and `corpus` are
disjoint lists with disjoint guards (`fixtures.length == 19` is P1; `corpus.length == 145` is G1);
neither may ever be allowed to inflate the other's count.

Donors (§0.5 of the slice plan verified each one's visibility):

| Fixtures | Donor | The single changed field |
|---|---|---|
| `sigmoid`, `tanh`, `gelu`, `leaky-relu` | `NonlinCompileTest.reluProg` (public) | the `PointwiseFn` tag |
| `normalize`, `l2-normalize` | `NonlinCompileTest.softmaxProg` (public) | the `AxiswiseFn` tag |
| `relu-over-max`, `relu-over-min` | `LoweringTest`'s AGG1 construction | `agg` → `.max` / `.min` |
| `causal-mask`, `negated-causal-mask` | `AcsetCodecTest` fixture 2's causal mask | the mask predicate (negated) |
| `band-iverson`, `negated-band-iverson` | `ParsePredicatesTest.band` (**private** — CLONED, not imported) | the Iverson predicate (negated) |
| `tensor-metadata`, `predicate-metadata` | `CompileTest.acceptedSched`'s decl/env shape (public) | the `Decl` → `.tensor` / `.predicate` |
| `scale-read`, `shift-read` | `LoweringTest`'s strided read | the `IdxExpr` |
| `general-affine-read` | `AcsetCodecTest` fixture 3's strided convolution read | the `IdxExpr` |
| `scan-pre-operation`, `scan-pre-output-weave` | `RecurMorphismTest.stepTC` (**private** — CLONED, not imported) | the nested `op` / the nested output weave |

`ParsePredicatesTest.band` and `RecurMorphismTest.stepTC` are `private def`s, so they are
unreachable by import and are reproduced here by construction; the remaining donors are public and
this section reproduces their *construction*, not their identity — nothing under `papers/` is
imported and no donor module is edited.

### Two kinds of payload, and the assertion families that separate them

* **Represented** (11 fixtures — the pointwise/axiswise tags, aggregation, affine reads): the field
  survives physicalization *and* reaches the categorical output, so the old split leg and production
  `route` must agree exactly (P3).
* **Opaque** (8 fixtures in 4 pairs — masks, Iverson predicates, dtype metadata, nested `scanPre`
  bodies): the field survives physicalization (P2) but the *current* categorical projection does not
  carry it, so the two members of each pair route identically (P4).

⚠️ **P4 is a statement about the projection, never about semantics.** Each pair carries **two
separate claims**, deliberately not merged into one sentence: (a) the physical payload really does
differ between the two members, named field by field; and (b) their routed presentations and ACSet
encodings are nonetheless equal — i.e. *the current projection omits this field*. `causal-mask` and
`negated-causal-mask` are NOT semantically equivalent programs, and nothing here asserts that they
are; if the projection is ever widened to carry masks, (b) is expected to break and that break is
the correct signal, not a regression.

### No local physicalizer, same rule as §1

The physical leg below is production `physicalizeForRoute` (its `.scheduled` field) and the routing
legs are §2's `oldTC`/`newTC`. The donor seed's local `physicalize`/`privateName`/`oldPhysicalize`/
`routeOf`/`acsetOf` and its four `enable…Mutation` toggles are deliberately absent: every mutation
cycle for this section mutates **production** `LeanNCD/DSL/Pipeline/RouteFragments.lean`.
-/

/-! ### §4.1 Fixture construction

Axes are §1's `i`/`j`/`k` (`mkAxis "i" 1` etc.) — the payload fixtures deliberately share the
corpus' axis inventory rather than minting a parallel one. -/

/-- One `.read` factor wrapped as a single-term sum. -/
def readBody (name : String) (idxs : List IdxExpr) : SumExpr :=
  { terms := [{ factors := [.read name idxs] }] }

/-- A one-statement logical program. Distinct from §1's `scheduled` (which takes a statement LIST
    and no `env`/`explicitSizes`): the metadata fixtures need both of those fields populated. -/
def one (stmt : ScanStmt) (decls : List Decl := []) (env : DeclEnv := {})
    (exts : Finset String := {"X"}) (explicitSizes : Std.HashMap UID Nat := {}) :
    ScheduledProgram :=
  { decls, env, extNames := exts, explicitSizes, stmts := [stmt] }

inductive PayloadClass
  | represented
  | opaqueMask
  | opaqueIverson
  | opaqueMetadata
  | opaqueScanPre
  deriving DecidableEq, Repr

structure NamedPayloadFixture where
  name : String
  logical : ScheduledProgram
  payloadClass : PayloadClass

/-- Clone of `NonlinCompileTest.reluProg`'s shape (`H[i] := relu(W[i,j] · x[j])` reduced to a single
    read), varying **only** the `PointwiseFn` tag. -/
def pointwise (name : String) (fn : PointwiseFn) : NamedPayloadFixture :=
  { name, payloadClass := .represented
    logical := one (.plain (.assign "Y" [.free i]
      { body := readBody "X" [.axis i], nonlin := .pointwise fn })) }

/-- Clone of `NonlinCompileTest.softmaxProg`'s shape (`Y[q, s.] := softmax(A[q, s])`), varying
    **only** the `AxiswiseFn` tag. The `.freeNorm` marker is the `s.` of the donor's surface form. -/
def axiswise (name : String) (fn : AxiswiseFn) : NamedPayloadFixture :=
  { name, payloadClass := .represented
    logical := one (.plain (.assign "Y" [.free i, .freeNorm j]
      { body := readBody "X" [.axis i, .axis j], nonlin := .axiswise fn none })) }

/-- Clone of `LoweringTest`'s AGG1 construction (`Y[i] := relu(maxreduce over j of P[i,j])`, built
    programmatically there for the same reason — the shape is not spellable in surface syntax),
    varying **only** `agg`. -/
def aggregate (name : String) (agg : AggOp) : NamedPayloadFixture :=
  { name, payloadClass := .represented
    logical := one (.plain (.assign "Y" [.free i]
      { body := readBody "X" [.axis i, .axis k], nonlin := .pointwise .relu, agg })) }

/-- `AcsetCodecTest` fixture 2's causal mask, `where s ≤ q`. -/
def causal : BoolExpr := .rel .le (.embed (.axis j)) (.embed (.axis i))
def antiCausal : BoolExpr := .not causal

def masked (name : String) (mask : BoolExpr) : NamedPayloadFixture :=
  { name, payloadClass := .opaqueMask
    logical := one (.plain (.assign "Y" [.free i, .freeNorm j]
      { body := readBody "X" [.axis i, .axis j],
        nonlin := .axiswise .softmax (some mask) })) }

/-- A two-wide band predicate in `ParsePredicatesTest.band`'s spirit (`private` there, so cloned
    by construction) — NOT a faithful clone: the donor is the symmetric tridiagonal `|i - j| ≤ 1`
    (using `PredArith.iabs`, the reason that file exists); this is the asymmetric one-sided band
    `i ≤ j < i + 2`, expressed without `iabs`. Lifted into the ReLU donor's body as an Iverson
    factor. Both are legitimate Iverson-predicate fixtures for P4's negation-pairing purpose; only
    the "clone" relationship to the donor is looser than for this matrix's other fixtures. -/
def band : BoolExpr :=
  .and (.rel .le (.embed (.axis i)) (.embed (.axis j)))
    (.rel .lt (.embed (.axis j)) (.embed (.shift i 2)))

/-- The parameter is `pred`, not the donor's `predicate`: this module imports
    `DSL.Pipeline.RouteWeaveTest → LeanNCD.DSL.Compile → LeanNCD.DSL.Elab`, which registers
    `predicate` as a TL surface-syntax **token**, so a binder of that name fails to parse. Same
    class of collision as §1's `mkAxis` rename; the body is otherwise the donor's verbatim. -/
def iversonFixture (name : String) (pred : BoolExpr) : NamedPayloadFixture :=
  { name, payloadClass := .opaqueIverson
    logical := one (.plain (.assign "Y" [.free i]
      { body := { terms := [{ factors := [
          .read "X" [.axis i], .iverson pred] }] },
        nonlin := .pointwise .relu })) }

/-- Clone of `CompileTest.acceptedSched`'s declaration/environment shape, varying **only** the
    `Decl` constructor. -/
def metadataFixture (name : String) (decl : Decl) : NamedPayloadFixture :=
  { name, payloadClass := .opaqueMetadata
    logical := one (.plain (.assign "Y" [.free i]
      { body := readBody "X" [.axis i], nonlin := .identity }))
      [decl] (({} : DeclEnv).insert "Meta" decl) {"X"}
      (({} : Std.HashMap UID Nat).insert i.uid 4) }

/-- `scale-read`/`shift-read` clone `LoweringTest`'s strided read; `general-affine-read` clones
    `AcsetCodecTest` fixture 3's strided convolution read. Only the `IdxExpr` varies. -/
def affineFixture (name : String) (idx : IdxExpr) : NamedPayloadFixture :=
  { name, payloadClass := .represented
    logical := one (.plain (.assign "Y" [.free i]
      { body := readBody "X" [idx], nonlin := .pointwise .relu })) }

/-- Clones of `RecurMorphismTest.stepTC` (`private` there — `{ op := .contract, outputWeaves :=
    [[.tiled]], ... }`). `nestedStepA` changes only the `op` (`.contract` → `.relu`), keeping the
    donor's `outputWeaves`. `nestedStepB` changes only `outputWeaves` (`[[.tiled]]` → `[[]]`),
    keeping the donor's `op`. Each differs from the donor in exactly one field, and from each
    other in both — which is exactly what `scan-pre-operation`/`scan-pre-output-weave`'s names
    claim to isolate. -/
def nestedStepA : BrBaseP :=
  { op := .relu, degree := [], inputWeaves := [], outputWeaves := [[.tiled]], reindexings := [] }

def nestedStepB : BrBaseP :=
  { op := .contract, degree := [], inputWeaves := [], outputWeaves := [[]], reindexings := [] }

def nestedA : ThreadedComposed := { steps := [nestedStepA], routing := [[]], nExternal := 0 }
def nestedB : ThreadedComposed := { steps := [nestedStepB], routing := [[]], nExternal := 0 }

def scanPreFixture (name : String) (nested : ThreadedComposed) : NamedPayloadFixture :=
  { name, payloadClass := .opaqueScanPre
    logical := one (.scanPre "S" i nested) [] {} ∅ }

def causalMaskFixture := masked "causal-mask" causal
def negatedMaskFixture := masked "negated-causal-mask" antiCausal
def bandIversonFixture := iversonFixture "band-iverson" band
def negatedIversonFixture := iversonFixture "negated-band-iverson" (.not band)
def tensorMetadataFixture := metadataFixture "tensor-metadata" (.tensor "Meta" [i])
def predicateMetadataFixture := metadataFixture "predicate-metadata" (.predicate "Meta" [i])
-- These two fixtures assert that the CURRENT categorical projection omits the nested `.scanPre`
-- body (P4 below) — NOT that this was always a benign design choice. `RecurMorphismTest.lean`
-- records audit finding #4 (2026-07-30): a routed `.scanPre` step used to have empty
-- degree/inputWeaves/reindexings and a dropped iteration axis, a real payload-loss bug severe
-- enough that `TLProgram.compile` now REJECTS every surface `.scanPre` construction outright
-- (`unsupportedRecurMorphism`) — this class is reachable only via a hand-built schedule, same
-- as this fixture. The opacity claim below is real and independently verified, but it is about
-- an unreachable-from-surface-syntax class whose only prior history at this boundary was a bug.
def scanPreOperationFixture := scanPreFixture "scan-pre-operation" nestedA
def scanPreWeaveFixture := scanPreFixture "scan-pre-output-weave" nestedB

/-- The 19. **Kept out of `corpus` deliberately** — P1 and G1 are independent counts. -/
def fixtures : List NamedPayloadFixture := [
  pointwise "sigmoid" .sigmoid,
  pointwise "tanh" .tanh,
  pointwise "gelu" .gelu,
  pointwise "leaky-relu" .leakyrelu,
  axiswise "normalize" .normalize,
  axiswise "l2-normalize" .l2normalize,
  aggregate "relu-over-max" .max,
  aggregate "relu-over-min" .min,
  causalMaskFixture,
  negatedMaskFixture,
  bandIversonFixture,
  negatedIversonFixture,
  tensorMetadataFixture,
  predicateMetadataFixture,
  affineFixture "scale-read" (.scale 2 i),
  affineFixture "shift-read" (.shift i 1),
  affineFixture "general-affine-read" (.affine 1 [(2, i), (-1, j)]),
  scanPreOperationFixture,
  scanPreWeaveFixture
]

/-! ### §4.2 The physical leg and the payload-conservation predicates

The physical leg is production `physicalizeForRoute` only (§1's "No local physicalizer" note applies
verbatim); the routing legs are §2's `oldTC`/`newTC`. -/

/-- Production `physicalizeForRoute`'s physical schedule. `none` on rejection, which every P-guard
    below treats as a failure — no fixture in this matrix may be rejected at the route boundary. -/
def physicalOf (sp : ScheduledProgram) : Option ScheduledProgram :=
  match physicalizeForRoute sp with
  | .ok physical => some physical.scheduled
  | .error _ => none

/-- Conservation of every field this split is SUPPOSED to preserve, across the producer/consumer
    split: the producer carries the logical body and `agg` at `.identity`, with `.freeNorm`
    degraded exactly as production `producerSlots` prescribes; the consumer republishes the
    logical name and slots, carries the logical `nonlin` (mask included), and contracts nothing
    (`agg = .sum`). An unsplit (identity-nonlin) fixture must come through untouched (and only
    counts if it actually IS identity-nonlin — see the guard below). Deliberately NOT checked,
    because they are not conserved by design: the producer's freshly-minted internal name (owned
    by Task 1's freshness/injectivity proofs, not this matrix), and the consumer's body (derived
    from `LHSSlot.toReadIdx`, not copied from the logical statement). -/
def plainPayloadConserved (logical physical : ScheduledProgram) : Bool :=
  match logical.stmts, physical.stmts with
  | [.plain (.assign logicalName logicalSlots rhs)],
      [.plain (.assign _ producer producerRhs),
       .plain (.assign publishedName consumerSlots consumerRhs)] =>
      producerRhs.body == rhs.body &&
      producerRhs.agg == rhs.agg &&
      producerRhs.nonlin == .identity &&
      producer == producerSlots logicalSlots &&
      publishedName == logicalName &&
      consumerSlots == logicalSlots &&
      consumerRhs.nonlin == rhs.nonlin &&
      consumerRhs.agg == .sum
  | [.plain (.assign nm slots rhs)], [.plain physicalStmt] =>
      -- Only for identity-nonlin fixtures (the metadata pair): guarded so a hypothetical defect
      -- that silently stopped splitting a NONLINEAR statement can't pass here by construction —
      -- an unconditional `logicalStmt == physicalStmt` would be vacuously true for that case too.
      rhs.nonlin == .identity && Stmt.assign nm slots rhs == physicalStmt
  | _, _ => false

/-- Declarations, externals, explicit sizes, and the declaration environment all survive
    physicalization unchanged. -/
def metadataConserved (logical physical : ScheduledProgram) : Bool :=
  logical.decls == physical.decls &&
  logical.extNames == physical.extNames &&
  logical.explicitSizes.toList == physical.explicitSizes.toList &&
  logical.env.toList == physical.env.toList

/-- A `.scanPre` node is opaque: name, iteration axis, and the whole nested `ThreadedComposed` are
    copied byte-for-byte. -/
def scanPreConserved (logical physical : ScheduledProgram) : Bool :=
  match logical.stmts, physical.stmts with
  | [.scanPre logicalName logicalAxis logicalBody],
      [.scanPre physicalName physicalAxis physicalBody] =>
      logicalName == physicalName && logicalAxis == physicalAxis &&
        logicalBody == physicalBody
  | _, _ => false

def payloadConserved (fixture : NamedPayloadFixture) : Bool :=
  match physicalOf fixture.logical with
  | none => false
  | some physical =>
      metadataConserved fixture.logical physical &&
        match fixture.logical.stmts with
        | [.scanPre ..] => scanPreConserved fixture.logical physical
        | _ => plainPayloadConserved fixture.logical physical

/-- P3's per-fixture body: for a `.represented` payload the old split leg and production `route`
    must produce the identical `ThreadedComposed`, the identical ACSet encoding, and a decode∘encode
    identity. Vacuously true on the opaque classes — P4 owns those. -/
def representedMatchesOld (fixture : NamedPayloadFixture) : Bool :=
  if fixture.payloadClass != .represented then true else
    match oldTC fixture.logical, newTC fixture.logical with
    | some old, some new =>
        old == new &&
        fromThreadedComposed old == fromThreadedComposed new &&
        toThreadedComposed (fromThreadedComposed new) == new &&
        new.wellFormedDom
    | _, _ => false

/-! ### §4.3 P1 — the matrix's own shape, counted separately from the corpus -/

private def fixtureNames : List String := fixtures.map (·.name)

-- `fixtures` is a separate list of a separate type from `corpus`; the two counts are pinned
-- independently and neither list may ever absorb the other's members.
#guard fixtures.length == 19                                                          -- P1
#guard fixtureNames.eraseDups.length == 19                                            -- P1
#guard (fixtures.filter (·.payloadClass == .represented)).length == 11                -- P1
#guard (fixtures.filter (·.payloadClass != .represented)).length == 8                 -- P1
-- G23's third-class-6-door guard, extended to the payload matrix (plan §5's "0 of the 19 payload
-- fixtures" requirement) -- not a P1 shape/count guard, tagged separately.
#guard fixtures.all fun f => !plainIterSlots f.logical                          -- door guard

/-! ### §4.4 P2/P3 — physical conservation, and represented-class route agreement

Reported through the same `<label>: N FAILURES` idiom §3 uses, so a mutation cycle yields an
OBSERVED count and the failing fixture NAMES rather than a bare `false`. -/

private def checkFixtures (label : String) (p : NamedPayloadFixture → Bool) :
    Lean.Elab.Command.CommandElabM Unit := do
  let bad := (fixtures.filter (fun f => !p f)).map (·.name)
  unless bad.isEmpty do
    throwError s!"{label}: {bad.length} FAILURES, fixtures {bad}"

run_cmd checkFixtures "P2 physical payload conservation (19 fixtures)" payloadConserved
run_cmd checkFixtures "P3 represented route/ACSet agreement (11)" representedMatchesOld

/-! ### §4.5 P4 — the four opacity pairs, as TWO separate claims

For each pair the guard asserts, independently and with independently reported failures:

* **(a) the physical payloads DIFFER** in the named field — the mask, the Iverson predicate, the
  declaration metadata, or the nested `scanPre` body really is a different value after production
  `physicalizeForRoute`; and
* **(b) the routed presentations and their ACSet encodings are EQUAL** — *the current categorical
  projection omits that field*.

These are not one claim. (b) says nothing whatever about the two programs computing the same thing:
`causal-mask` and `negated-causal-mask` compute different tensors, and this file never says
otherwise. (a) is what makes (b) informative rather than vacuous — without it, "equal routes" could
mean the two fixtures were simply the same program. If the projection is later widened to carry any
of these fields, (b) breaks by design and that break is the signal, not a regression. -/

private def consumerNonlin? (sp : ScheduledProgram) : Option Nonlin :=
  match sp.stmts with
  | [.plain _, .plain (.assign _ _ rhs)] => some rhs.nonlin
  | _ => none

private def producerBody? (sp : ScheduledProgram) : Option SumExpr :=
  match sp.stmts with
  | [.plain (.assign _ _ rhs), .plain _] => some rhs.body
  | _ => none

private def scanPreBody? (sp : ScheduledProgram) : Option ThreadedComposed :=
  match sp.stmts with
  | [.scanPre _ _ nested] => some nested
  | _ => none

structure OpacityPair where
  label : String
  /-- The physical field claim (a) is about — named, so a failure says WHICH field stopped
      differing rather than only that two programs became equal. -/
  field : String
  left : NamedPayloadFixture
  right : NamedPayloadFixture
  /-- Claim (a), over the two PHYSICAL programs. -/
  physicalPayloadsDiffer : ScheduledProgram → ScheduledProgram → Bool

def opacityPairs : List OpacityPair := [
  { label := "causal-mask vs negated-causal-mask"
    field := "the axiswise mask riding the physical consumer's `nonlin`"
    left := causalMaskFixture, right := negatedMaskFixture
    physicalPayloadsDiffer := fun a b =>
      match consumerNonlin? a, consumerNonlin? b with
      | some na, some nb => na != nb
      | _, _ => false },
  { label := "band-iverson vs negated-band-iverson"
    field := "the Iverson predicate inside the physical producer's body"
    left := bandIversonFixture, right := negatedIversonFixture
    physicalPayloadsDiffer := fun a b =>
      match producerBody? a, producerBody? b with
      | some ba, some bb => ba != bb
      | _, _ => false },
  { label := "tensor-metadata vs predicate-metadata"
    field := "the physical program's `decls` and `env`"
    left := tensorMetadataFixture, right := predicateMetadataFixture
    physicalPayloadsDiffer := fun a b =>
      a.decls != b.decls && a.env.toList != b.env.toList },
  { label := "scan-pre-operation vs scan-pre-output-weave"
    field := "the nested `ThreadedComposed` carried by the physical `.scanPre` node"
    left := scanPreOperationFixture, right := scanPreWeaveFixture
    physicalPayloadsDiffer := fun a b =>
      match scanPreBody? a, scanPreBody? b with
      | some na, some nb => na != nb
      | _, _ => false }
]

#guard opacityPairs.length == 4

-- P4's fourth pair positively asserts scan-body opacity only for `.scanPre` (class 10) — the class
-- `TLProgram.compile` cannot reach (see the note above `scanPreOperationFixture`). The classes
-- surface syntax CAN reach, `.scan`/`.scanAffine` (8/9), get only INDIRECT evidence elsewhere in
-- this slice (B8's `steps.map (·.op) == [BrOp.scan]`, plus a negative mutation observation in the
-- ledger). Assert the positive claim directly, on the reachable class, from surface syntax: two
-- scans differing ONLY in the recurrence nonlinearity route identically -- the projection omits
-- the scan body here too, not only for the unreachable `.scanPre` construct.
#guard (tl!{ iter l = 3
             G[j, 0]    := X[j]
             G[j, l +1] := relu(G[j, l] · W_G[j, k]) })
     == (tl!{ iter l = 3
              G[j, 0]    := X[j]
              G[j, l +1] := tanh(G[j, l] · W_G[j, k]) })

/-- Claim (a) for one pair, over the two PHYSICAL programs. -/
def opacityPhysicalDiffers (pair : OpacityPair) : Bool :=
  match physicalOf pair.left.logical, physicalOf pair.right.logical with
  | some physLeft, some physRight => pair.physicalPayloadsDiffer physLeft physRight
  | _, _ => false

/-- Claim (b)'s precondition, reported separately so a route *rejection* is never misread as a
    route *divergence* — the two say very different things about the projection. -/
def opacityBothRoute (pair : OpacityPair) : Bool :=
  (newTC pair.left.logical).isSome && (newTC pair.right.logical).isSome

/-- Claim (b) for one pair, over the two ROUTED programs. Deliberately independent of claim (a):
    a mutation may break one without the other, and the ledger records which. -/
def opacityRouteEqual (pair : OpacityPair) : Bool :=
  match newTC pair.left.logical, newTC pair.right.logical with
  | some tcLeft, some tcRight =>
      tcLeft == tcRight && fromThreadedComposed tcLeft == fromThreadedComposed tcRight
  | _, _ => false

-- The claims are reported independently and none short-circuits the others, so a mutation cycle
-- can observe (for instance) that the physical payload stopped differing while the routes stayed
-- equal — the mirror of §3's G24/G20 split.
run_cmd do
  let badRoute := (opacityPairs.filter (fun p => !opacityBothRoute p)).map (·.label)
  let badA := (opacityPairs.filter (fun p => !opacityPhysicalDiffers p)).map (·.label)
  let badB := (opacityPairs.filter (fun p => opacityBothRoute p && !opacityRouteEqual p)).map (·.label)
  unless badRoute.isEmpty do
    Lean.logError s!"P4 precondition [both members route]: {badRoute.length} FAILURES, \
pairs {badRoute} — `route` REJECTED a member, so claim (b) is un-evaluable for those pairs \
(this is not the same as the routes differing)"
  unless badA.isEmpty do
    Lean.logError s!"P4 claim (a) [physical payloads DIFFER]: {badA.length} FAILURES, \
pairs {badA} — the differing field became equal, so claim (b) is vacuous for those pairs"
  unless badB.isEmpty do
    Lean.logError s!"P4 claim (b) [route + ACSet EQUAL, i.e. the projection omits the field]: \
{badB.length} FAILURES, pairs {badB}"
  unless badRoute.isEmpty && badA.isEmpty && badB.isEmpty do
    throwError "P4 opacity pairs failed (see the per-claim errors above)"

end RouteFragmentCorpusTest

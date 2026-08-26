import LeanNCD.DSL.Compile
import LeanNCD.Bridge.AcsetCodec

/-!
# Route-fragment fixture support seed

This file is deliberately outside `LeanNCD`: it is executable design material, not production code.
It models the proposed logical scheduling boundary and terminal route physicalizer against the
current split pipeline.
-/

namespace NonlinearityRouteFragmentsSeed

open LeanNCD Std

structure RouteFragment where
  logicalIndex : Nat
  firstStep : Nat
  lastStep : Nat
  internalName : Option String
  deriving DecidableEq, Repr

structure PhysicalRouteProgram where
  scheduled : ScheduledProgram
  fragments : List RouteFragment
  sourceNames : List String

def tensorDeclName? : Decl → Option String
  | .tensor n _ | .predicate n _ | .linear n _ _ => some n
  | .axis .. | .iter .. => none

def sourceNames (sp : ScheduledProgram) : List String :=
  let declNames := sp.decls.filterMap tensorDeclName?
  let writeNames := sp.stmts.flatMap ScanStmt.writes
  let readNames := sp.stmts.flatMap ScanStmt.reads
  (declNames ++ writeNames ++ readNames).eraseDups

def internalName (maxSourceNameLength ordinal : Nat) : String :=
  String.ofList (List.replicate (maxSourceNameLength + ordinal + 1) '#')

def degradeFreeNorm : LHSSlot → LHSSlot
  | .freeNorm a => .free a
  | slot => slot

def physicalizePlain (maxLen ordinal : Nat) (s : Stmt) :
    List ScanStmt × Option String :=
  match s with
  | .assign name slots rhs =>
      if rhs.nonlin == Nonlin.identity then ([.plain s], none)
      else
        let privateName := internalName maxLen ordinal
        let producer : Stmt := .assign privateName (slots.map degradeFreeNorm)
          { body := rhs.body, nonlin := .identity, agg := rhs.agg }
        let consumer : Stmt := .assign name slots
          { body := { terms := [{ factors := [
              .read privateName (slots.filterMap LHSSlot.toReadIdx) ] }] },
            nonlin := rhs.nonlin, agg := .sum }
        ([.plain producer, .plain consumer], some privateName)
  | _ => ([.plain s], none)

def physicalizeLoop (maxLen : Nat) :
    List ScanStmt → Nat → Nat → List ScanStmt → List RouteFragment →
      List ScanStmt × List RouteFragment
  | [], _, _, out, fragments => (out, fragments)
  | logical :: rest, logicalIndex, firstStep, out, fragments =>
      let (emitted, privateName) := match logical with
        | .plain s => physicalizePlain maxLen logicalIndex s
        | .scan .. | .scanPre .. => ([logical], none)
      let lastStep := firstStep + emitted.length - 1
      physicalizeLoop maxLen rest (logicalIndex + 1) (firstStep + emitted.length)
        (out ++ emitted)
        (fragments ++ [{ logicalIndex, firstStep, lastStep, internalName := privateName }])

def fragmentsContiguous (fragments : List RouteFragment) (physicalCount : Nat) : Bool :=
  let final := fragments.foldl (fun (state : Bool × Nat) fragment =>
    (state.1 && fragment.firstStep == state.2 &&
        decide (fragment.lastStep ≥ fragment.firstStep),
      fragment.lastStep + 1)) (true, 0)
  final.1 && final.2 == physicalCount

def privateNamesFresh (names : List String) (fragments : List RouteFragment) : Bool :=
  let privateNames := fragments.filterMap (·.internalName)
  privateNames.eraseDups.length == privateNames.length &&
    privateNames.all (fun n => !names.contains n)

def fragmentShapesOk (logical : List ScanStmt) (fragments : List RouteFragment) : Bool :=
  logical.zip fragments |>.all fun (stmt, fragment) =>
    let width := fragment.lastStep + 1 - fragment.firstStep
    match stmt with
    | .plain (.assign _ _ rhs) =>
        if rhs.nonlin == Nonlin.identity then width == 1 && fragment.internalName.isNone
        else width == 2 && fragment.internalName.isSome
    | _ => width == 1 && fragment.internalName.isNone

def physicalizeForRoute (sp : ScheduledProgram) : Except String PhysicalRouteProgram :=
  let names := sourceNames sp
  let maxLen := names.foldl (fun n s => max n s.length) 0
  let (stmts, fragments) := physicalizeLoop maxLen sp.stmts 0 0 [] []
  if fragmentsContiguous fragments stmts.length &&
      privateNamesFresh names fragments &&
      fragmentShapesOk sp.stmts fragments then
    .ok {
      scheduled := { sp with stmts }
      fragments
      sourceNames := names
    }
  else
    .error "route-fragment evidence failed"

def logicalSchedule (p : TLProgram) : FreshM ScheduledProgram := do
  let a ← assignUIDs p
  let b ← resolveDecls a
  let b ← reclassifyIterSlots b
  let b ← checkReadRanks b
  let b ← checkDtypes b
  let b ← checkScatterNonlin b
  let b ← checkScatterNoScan b
  let d ← lowerArith b
  let e ← finalizeScans d
  let schedulable : LinearProgram :=
    { decls := e.decls, stmts := e.stmts, env := e.env, extNames := e.extNames }
  schedule schedulable

def proposedCompile (p : TLProgram) : FreshM ThreadedComposed := do
  let logical ← logicalSchedule p
  match physicalizeForRoute logical with
  | .error message => throw (.shapeMismatch "valid route fragments" message)
  | .ok physical => route physical.scheduled

def oldPhysicalSchedule (p : TLProgram) : FreshM ScheduledProgram := p.compileToScheduled

def proposedPhysicalSchedule (p : TLProgram) :
    FreshM (ScheduledProgram × List RouteFragment) := do
  let logical ← logicalSchedule p
  match physicalizeForRoute logical with
  | .error message => throw (.shapeMismatch "valid route fragments" message)
  | .ok physical => pure (physical.scheduled, physical.fragments)

def acsetRoundTrips (tc : ThreadedComposed) : Bool :=
  LeanNCD.AcsetCodec.toThreadedComposed
    (LeanNCD.AcsetCodec.fromThreadedComposed tc) == tc

def sameOldAndProposedRoute (p : TLProgram) : Bool :=
  match p.compile.run 0, proposedCompile p |>.run 0 with
  | .ok old oldState, .ok proposed proposedState =>
      old == proposed && decide (oldState ≥ proposedState) && acsetRoundTrips proposed
  | .error old oldState, .error proposed proposedState =>
      old == proposed && decide (oldState ≥ proposedState)
  | _, _ => false

def supportSmoke : TLProgram := tlprog!{ H[i] := relu(W[i, j] · x[j]) }

def supportBranch : TLProgram := tlprog!{
  A[i] := relu(X[i])
  B[i] := tanh(X[i])
  Y[i] := A[i] · B[i]
}

run_cmd do
  match logicalSchedule supportSmoke |>.run 0 with
  | .error e _ => throwError s!"logical schedule failed: {repr e}"
  | .ok logical state =>
      unless logical.stmts.length == 1 do
        throwError "logical schedule must retain one source nonlinearity"
      unless state == 3 do throwError s!"expected i/j axis mints to finish at state 3, got {state}"
      match physicalizeForRoute logical with
      | .error e => throwError e
      | .ok physical =>
          unless physical.scheduled.stmts.length == 2 do
            throwError "one nonlinear logical statement must physicalize to two route steps"
          unless fragmentsContiguous physical.fragments 2 do
            throwError "fragment interval is not contiguous"
          unless privateNamesFresh physical.sourceNames physical.fragments do
            throwError "private route name is not fresh"

#guard sameOldAndProposedRoute supportSmoke

run_cmd do
  match proposedPhysicalSchedule supportBranch |>.run 0 with
  | .error error _ => throwError s!"branch physicalization failed: {repr error}"
  | .ok (physical, fragments) _ =>
      unless physical.stmts.length == 5 do
        throwError s!"expected 3 logical/5 physical branch steps, got {physical.stmts.length}"
      unless fragments.map (fun f => (f.firstStep, f.lastStep)) ==
          [(0, 1), (2, 3), (4, 4)] do
        throwError s!"unexpected branch intervals: {repr fragments}"
      let privateNames := fragments.filterMap (·.internalName)
      unless privateNames.length == 2 && privateNames.eraseDups.length == 2 do
        throwError s!"expected two distinct private names, got {repr privateNames}"

#guard sameOldAndProposedRoute supportBranch

end NonlinearityRouteFragmentsSeed

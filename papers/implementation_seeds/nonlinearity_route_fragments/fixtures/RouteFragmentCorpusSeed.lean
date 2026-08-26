import LeanNCD.DSL.Pipeline.Lowering
import LeanNCD.Bridge.AcsetCodec

/-!
# Deterministic route-fragment corpus seed

This compact generator materializes exactly 145 cases in the plan's 13 families. The 137
common-domain cases compare complete routed presentations and ACSet encodings; eight deliberate
`%nl0` collisions pin old rejection/new acceptance.
-/

namespace RouteFragmentCorpusSeed

open LeanNCD Std
open LeanNCD.AcsetCodec

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

def axis (name : String) (uid : Nat) (kind := AxisKind.real) : AxisSpec :=
  { name, uid, kind }

def i := axis "i" 1
def j := axis "j" 2
def k := axis "k" 3
def l := axis "l" 4 .nat
def m := axis "m" 5 .nat

def rhs (name : String) (idxs : List IdxExpr) (nonlin := Nonlin.identity) : RHSExpr :=
  { body := { terms := [{ factors := [.read name idxs] }] }, nonlin }

def rhs2 (a : String) (ai : List IdxExpr) (b : String) (bi : List IdxExpr)
    (nonlin := Nonlin.identity) : RHSExpr :=
  { body := { terms := [{ factors := [.read a ai, .read b bi] }] }, nonlin }

def scheduled (stmts : List ScanStmt) (exts : Finset String)
    (decls : List Decl := []) : ScheduledProgram :=
  { decls, stmts, env := {}, extNames := exts, explicitSizes := {} }

def chainProgram (n : Nat) : ScheduledProgram :=
  let depth := n % 4 + 1
  let stmts := (List.range depth).map fun q =>
    let input := if q == 0 then "X" else s!"H{q - 1}"
    .plain (.assign s!"H{q}" [.free i]
      (rhs input [.axis i] (.pointwise (if q % 2 == 0 then .relu else .tanh))))
  scheduled stmts {"X"}

def contractionProgram (n : Nat) : ScheduledProgram :=
  let idxs := match n % 3 with
    | 0 => [.axis i]
    | 1 => [.axis i, .axis j]
    | _ => [.axis i, .axis j, .axis k]
  scheduled [.plain (.assign s!"Y{n}" [.free i]
    (rhs "X" idxs (.pointwise .relu)))] {"X"}

def freeNormProgram (n : Nat) : ScheduledProgram :=
  let slots := match n % 3 with
    | 0 => [.freeNorm i, .free j, .free k]
    | 1 => [.free i, .freeNorm j, .free k]
    | _ => [.free i, .free j, .freeNorm k]
  scheduled [.plain (.assign s!"N{n}" slots
    (rhs "X" [.axis i, .axis j, .axis k] (.axiswise .softmax none)))] {"X"}

def branchProgram (n : Nat) : ScheduledProgram :=
  scheduled [
    .plain (.assign s!"A{n}" [.free i] (rhs "X" [.axis i] (.pointwise .relu))),
    .plain (.assign s!"B{n}" [.free i] (rhs "X" [.axis i] (.pointwise .tanh))),
    .plain (.assign s!"Y{n}" [.free i]
      (rhs2 s!"A{n}" [.axis i] s!"B{n}" [.axis i]))
  ] {"X"}

def repeatedProgram (n : Nat) : ScheduledProgram :=
  scheduled [
    .plain (.assign s!"A{n}" [.free i] (rhs "X" [.axis i] (.pointwise .relu))),
    .plain (.assign s!"Y{n}" [.free i]
      (rhs2 s!"A{n}" [.axis i] s!"A{n}" [.axis i]))
  ] {"X"}

def unreadProgram (n : Nat) : ScheduledProgram :=
  scheduled [
    .plain (.assign s!"Primary{n}" [.free i] (rhs "X" [.axis i] (.pointwise .relu))),
    .plain (.assign s!"Unread{n}" [.free i] (rhs "X" [.axis i] (.pointwise .sigmoid)))
  ] {"X"}

def adversarialProgram (n : Nat) : ScheduledProgram :=
  let longName := String.ofList (List.replicate (n + 8) '#')
  scheduled [.plain (.assign longName [.free i]
    (rhs "escaped%source" [.axis i] (.pointwise .relu)))] {"escaped%source"}

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

def declName? : Decl → Option String
  | .tensor name _ | .predicate name _ | .linear name _ _ => some name
  | .axis .. | .iter .. => none

def allSourceNames (sp : ScheduledProgram) : List String :=
  (sp.decls.filterMap declName? ++
    sp.stmts.flatMap fun s => s.writes ++ s.reads).eraseDups

def enableReusePrivateNameMutation : Bool := false
def enableKeepFreeNormMutation : Bool := false
def enableRouteFromEntryMutation : Bool := false

def mutateRouteFromEntry (enabled : Bool) (wire : Wire) : Wire :=
  if enabled then
    match wire with | .internal step slot => .internal (step - 1) slot | w => w
  else wire

def mutateRoutedProgram (enabled : Bool) (tc : ThreadedComposed) : ThreadedComposed :=
  if enabled then { tc with routing := tc.routing.map (·.map (mutateRouteFromEntry true)) } else tc

def producerSlot : LHSSlot → LHSSlot
  | .freeNorm a => if enableKeepFreeNormMutation then .freeNorm a else .free a
  | slot => slot

def physicalize (sp : ScheduledProgram) : ScheduledProgram :=
  let names := allSourceNames sp
  let maxLen := names.foldl (fun n s => max n s.length) 0
  let stmts := sp.stmts.zipIdx.flatMap fun (scanStmt, ordinal) =>
    match scanStmt with
    | .plain s@(.assign name slots expression) =>
        if expression.nonlin == Nonlin.identity then [.plain s] else
          let internal :=
            String.ofList (List.replicate
              (maxLen + (if enableReusePrivateNameMutation then 1 else ordinal + 1)) '#')
          let producerSlots := slots.map producerSlot
          [.plain (.assign internal producerSlots
            { body := expression.body, nonlin := .identity, agg := expression.agg }),
           .plain (.assign name slots
            { body := { terms := [{ factors := [
                .read internal (slots.filterMap LHSSlot.toReadIdx) ] }] },
              nonlin := expression.nonlin, agg := .sum })]
    | _ => [scanStmt]
  { sp with stmts }

def oldRoute (sp : ScheduledProgram) : EStateM.Result CompileError Nat ThreadedComposed :=
  (do
    let split ← splitNonlins {
      decls := sp.decls, stmts := sp.stmts, env := sp.env, extNames := sp.extNames }
    let ordered ← schedule split
    route { ordered with explicitSizes := sp.explicitSizes }).run 0

def newRoute (sp : ScheduledProgram) : EStateM.Result CompileError Nat ThreadedComposed :=
  match route (physicalize sp) |>.run 0 with
  | .ok tc state => .ok (mutateRoutedProgram enableRouteFromEntryMutation tc) state
  | .error error state => .error error state

def value? : EStateM.Result CompileError Nat ThreadedComposed → Option ThreadedComposed
  | .ok tc _ => some tc
  | .error .. => none

def commonExact (c : CorpusCase) : Bool :=
  if c.collision then true else
    match value? (oldRoute c.logical), value? (newRoute c.logical) with
    | some old, some new =>
        old == new &&
        fromThreadedComposed old == fromThreadedComposed new &&
        toThreadedComposed (fromThreadedComposed new) == new &&
        new.wellFormedDom
    | _, _ => false

def collisionTransition (c : CorpusCase) : Bool :=
  if !c.collision then true else
    match oldRoute c.logical, newRoute c.logical with
    | .error (.cyclicDataflow
        "routeCore: cyclic dataflow (topoSort fallback)") 1, .ok new 0 =>
        new.wellFormedDom &&
        toThreadedComposed (fromThreadedComposed new) == new
    | _, _ => false

def countFamily (family : Family) : Nat :=
  (corpus.filter (·.family == family)).length

abbrev ScanPayload := String × List AxisSpec × List Stmt × List Stmt × Bool

def scanPayloads (sp : ScheduledProgram) : List ScanPayload :=
  sp.stmts.filterMap fun
    | .scan name axes base recur isAffine => some (name, axes, base, recur, isAffine)
    | _ => none

def isScanFamily : Family → Bool
  | .nonlinearBase | .nonlinearRecurrence | .aroundScans | .coupledScans |
      .multiAxisScans => true
  | _ => false

def oldPhysicalSchedule? (sp : ScheduledProgram) : Option ScheduledProgram :=
  match (do
      let split ← splitNonlins {
        decls := sp.decls, stmts := sp.stmts, env := sp.env, extNames := sp.extNames }
      schedule split).run 0 with
  | .ok scheduled _ => some scheduled
  | .error .. => none

def scanPayloadObservation (c : CorpusCase) : Bool :=
  if !isScanFamily c.family then true else
    let proposed := physicalize c.logical
    match oldPhysicalSchedule? c.logical with
    | none => false
    | some old =>
        scanPayloads proposed == scanPayloads c.logical &&
        if c.family == .aroundScans then
          scanPayloads old == scanPayloads c.logical
        else
          -- These 32 cases expose the categorical opacity boundary: the old physical scan body
          -- is split, the proposed body is byte-for-byte logical, yet complete routes are equal.
          scanPayloads old != scanPayloads c.logical &&
            value? (route old |>.run 0) == value? (route proposed |>.run 0)

#guard corpus.length == 145
#guard (corpus.map (·.id)) == List.range 145
#guard countFamily .chains == 32
#guard countFamily .contractions == 24
#guard countFamily .freeNormPositions == 9
#guard countFamily .branches == 8
#guard countFamily .repeatedReads == 8
#guard countFamily .unreadOutputs == 8
#guard countFamily .adversarialNames == 8
#guard countFamily .nl0Collisions == 8
#guard countFamily .nonlinearBase == 8
#guard countFamily .nonlinearRecurrence == 8
#guard countFamily .aroundScans == 8
#guard countFamily .coupledScans == 8
#guard countFamily .multiAxisScans == 8
#guard (corpus.filter (·.collision)).length == 8
#guard (corpus.filter fun c => !c.collision).length == 137
#guard (corpus.filter fun c => isScanFamily c.family).length == 40
#guard (corpus.filter fun c => isScanFamily c.family && c.family != .aroundScans).length == 32
#guard corpus.all commonExact
#guard corpus.all collisionTransition
#guard corpus.all scanPayloadObservation

#guard mutateRouteFromEntry false (.internal 3 0) == .internal 3 0
#guard producerSlot (.freeNorm i) == .free i

end RouteFragmentCorpusSeed

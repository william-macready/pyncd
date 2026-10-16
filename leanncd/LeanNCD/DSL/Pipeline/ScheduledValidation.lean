import LeanNCD.DSL.Pipeline.Structural
import LeanNCD.DSL.Pipeline.Collect

namespace LeanNCD

/-- Tensor names a `ScanStmt` writes (its LHS name(s)). -/
def ScanStmt.writes : ScanStmt → List String
  | .plain s        => [s.lhsName]
  | .scan _ _ b r _ => (b.map Stmt.lhsName ++ r.map Stmt.lhsName).eraseDups
  | .scanPre nm _ _ => [nm]

/-- Tensor names a `ScanStmt` publishes after execution. Recurrence-only destinations are
    block-local scratch, not scan outputs. -/
def ScanStmt.outputs : ScanStmt → List String
  | .plain s        => [s.lhsName]
  | .scan _ _ b r _ => (b.map Stmt.lhsName).filter (fun n => (r.map Stmt.lhsName).contains n)
  | .scanPre nm _ _ => [nm]

/-- Tensor names a `ScanStmt` reads. -/
def ScanStmt.reads : ScanStmt → List String
  | .plain s        => s.readNames
  | .scan _ _ b r _ => (b.flatMap Stmt.readNames ++ r.flatMap Stmt.readNames).eraseDups
  | .scanPre _ _ _  => []

/-- The publications a node adds to the emitted list: each name it publishes, ONCE per node. A scan
    whose state has two base faces lists that state twice in `ScanStmt.outputs`; readiness counts
    nodes, so the duplicate must not count as a second writer. -/
def ScanStmt.publications (sc : ScanStmt) : List String := sc.outputs.eraseDups

/-- A node is ready when each read is internal to its own scan block, or ALL of the read's writers
    have published it: the number of emitted publications of `r` equals the number of nodes that
    write `r` (an external name has zero of both). This is all-writers readiness (additive
    collection, decision note §C.2): a reader of a multi-writer tensor waits for every writer. A
    plain write is not available to its own RHS (its own publication is never emitted before it),
    and scan scratch is never emitted, so a reader of it is never ready. -/
private def eligible (sc : ScanStmt) (all : List ScanStmt) (emitted : List String) : Bool :=
  sc.reads.all (fun r =>
    (match sc with
     | .scan .. => sc.writes.contains r
     | _ => false) ||
    emitted.count r == (all.filter (fun s => s.writes.contains r)).length)

/-- Fuel-bounded stable Kahn's sort. -/
def topoSortFuel : Nat → List ScanStmt → List ScanStmt → List String →
    List ScanStmt → List ScanStmt
  | 0,    _,   remaining, _,       acc => acc ++ remaining
  | _,    _,   [],        _,       acc => acc
  | n+1,  all, remaining, emitted, acc =>
      match remaining.findIdx? (fun sc => eligible sc all emitted) with
      | none   => acc ++ remaining
      | some i =>
          let sc := remaining[i]!
          topoSortFuel n all (remaining.eraseIdx i) (emitted ++ sc.publications) (acc ++ [sc])

/-- Topological sort of scheduled statements. -/
def topoSort (stmts : List ScanStmt) : List ScanStmt :=
  topoSortFuel stmts.length stmts stmts [] []

/-- Whether `ordered` is a producer-before-consumer ordering of `all`. -/
def isTopoOrdered (all : List ScanStmt) (ordered : List ScanStmt) : Bool :=
  (ordered.foldl (fun (acc : Bool × List String) sc =>
      let (ok, emitted) := acc
      (ok && eligible sc all emitted, emitted ++ sc.publications))
    (true, ([] : List String))).1

/-- External read names in first-seen scheduled-read order. -/
def orderedExternalNames (stmts : List ScanStmt) : List String :=
  let produced : List String := stmts.flatMap ScanStmt.writes
  stmts.foldl (fun acc sc =>
    sc.reads.foldl (fun acc nm =>
      if produced.contains nm || acc.contains nm then acc else acc ++ [nm]) acc)
    []

/-! ## Schedule-wide storage-kind derivation

One scan, in USED-NAME order, shared by every consumer that must answer "what precision is this
whole schedule?" — `Eval.Plan.prepareEvalPlan` (which rejects a mixed schedule) and
`Eval.evalScheduled` (which rejects every f32 schedule,
since the reference workers are `Float`/binary64 throughout). -/

/-- The tensor names a schedule USES, in the order the storage scan visits them: external reads
    first (`orderedExternalNames`, first-seen-read order), then every written name.

    `ScanStmt.writes`, NOT `ScanStmt.outputs`: a scan's recurrence-only destination is block-local
    scratch that `outputs` deliberately omits, but it is still a real tensor whose declaration
    commits it to a storage kind. Deriving from `outputs` would silently admit a mixed-precision
    schedule whose only f32 name is scan scratch. -/
def scheduleStorageNames (stmts : List ScanStmt) : List String :=
  (orderedExternalNames stmts ++ stmts.flatMap ScanStmt.writes).eraseDups

/-- The storage constraint each USED name places on a schedule, in `scheduleStorageNames` order;
    names that constrain nothing (a `.predicate` declaration) are dropped. The one scan both
    schedule-wide questions below are projections of. -/
def scheduleStorageConstraints (env : DeclEnv) (stmts : List ScanStmt) :
    List (String × StorageKind) :=
  (scheduleStorageNames stmts).filterMap (fun nm =>
    (storageConstraintOfName? env nm).map (fun k => (nm, k)))

/-- The single storage kind a schedule commits to, or the FIRST used name that conflicts with the
    kind an earlier used name already established.

    The first constrained name in used-name order establishes the kind; the scan stops at the
    first name that disagrees, so a schedule with several conflicts reports the earliest one. A
    schedule no used name constrains (a bool-only graph) defaults to `.float64`. -/
def scheduleStorageKind (env : DeclEnv) (stmts : List ScanStmt) : Except String StorageKind := do
  let mut established : Option StorageKind := none
  for (nm, k) in scheduleStorageConstraints env stmts do
    match established with
    | none    => established := some k
    | some k0 => if k0 != k then throw nm
  return established.getD .float64

/-- The first USED name a schedule's declarations commit to `.float32`, if any — the question
    `Eval.evalScheduled` asks, since the reference evaluator rejects EVERY f32 schedule (mixed or
    homogeneous) and wants to name an actually-f32 tensor when it does. -/
def scheduleFloat32Name? (env : DeclEnv) (stmts : List ScanStmt) : Option String :=
  ((scheduleStorageConstraints env stmts).find? (fun nk => nk.2 == .float32)).map (·.1)

/-- Additive collection (decision note §C): `desugarMultiWriters`, with its result asserted to be in
    producer-before-consumer order. The one entry every boundary calls (`validateScheduled` here;
    `route` before `physicalizeForRoute`). The identity on single-writer schedules. -/
def collectDefinitions (sched : ScheduledProgram) :
    Except CompileError (ScheduledProgram × List String) := do
  let (collected, privateNames) ← desugarMultiWriters sched
  unless isTopoOrdered collected.stmts collected.stmts do
    throw (.cyclicDataflow "collectDefinitions: desugared schedule is not in producer-before-consumer order")
  return (collected, privateNames)

/-- A scheduled program whose source invariants and derived authority have been checked.

    `program` is the COLLECTED schedule (`collectDefinitions`): at most one writer per name, with
    the private per-writer tensors `T#k` it introduced listed in `privateNames`. The constructor is
    private, so only `validateScheduled` can pair a program with its hiding list; every consumer
    must erase `privateNames` from what it reports. -/
structure CheckedScheduledProgram where private mk ::
  program       : ScheduledProgram
  declEnv       : DeclEnv
  explicitSizes : Std.HashMap UID Nat
  extNames      : List String
  privateNames  : List String

/-- Check the complete source-invariant boundary for a direct scheduled program, then collect
    multi-writer tensors. The source checks run on the program as written; the declaration
    environment and derived fields come from the collected program (whose private tensors carry
    cloned declarations). -/
def validateScheduled (sched : ScheduledProgram) : Except CompileError CheckedScheduledProgram := do
  let sourceEnv ← buildDeclEnv sched.decls
  checkScheduledReadRanks sourceEnv sched.stmts
  checkScheduledDtypes sourceEnv sched.stmts
  unless isTopoOrdered sched.stmts sched.stmts do
    throw (.cyclicDataflow "scheduled program: statements are not in producer-before-consumer order")
  let (collected, privateNames) ← collectDefinitions sched
  let declEnv ← buildDeclEnv collected.decls
  return { program := collected
         , declEnv
         , explicitSizes := declaredAxisSizes collected.decls
         , extNames := orderedExternalNames collected.stmts
         , privateNames }

end LeanNCD

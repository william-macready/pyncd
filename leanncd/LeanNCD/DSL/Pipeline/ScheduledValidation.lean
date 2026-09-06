import LeanNCD.DSL.Pipeline.Structural

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

/-- A node is ready when each read is external, was published by an earlier node, or is internal to
    a scan block. A plain write is not available to its own RHS, and scan scratch is never emitted. -/
private def eligible (sc : ScanStmt) (all : List ScanStmt) (emitted : List String) : Bool :=
  sc.reads.all (fun r =>
    (match sc with
     | .scan .. => sc.writes.contains r
     | _ => false) ||
    emitted.contains r ||
    all.all (fun s => !s.writes.contains r))

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
          topoSortFuel n all (remaining.eraseIdx i) (emitted ++ sc.outputs) (acc ++ [sc])

/-- Topological sort of scheduled statements. -/
def topoSort (stmts : List ScanStmt) : List ScanStmt :=
  topoSortFuel stmts.length stmts stmts [] []

/-- Whether `ordered` is a producer-before-consumer ordering of `all`. -/
def isTopoOrdered (all : List ScanStmt) (ordered : List ScanStmt) : Bool :=
  (ordered.foldl (fun (acc : Bool × List String) sc =>
      let (ok, emitted) := acc
      (ok && eligible sc all emitted, emitted ++ sc.outputs))
    (true, ([] : List String))).1

/-- External read names in first-seen scheduled-read order. -/
def orderedExternalNames (stmts : List ScanStmt) : List String :=
  let produced : List String := stmts.flatMap ScanStmt.writes
  stmts.foldl (fun acc sc =>
    sc.reads.foldl (fun acc nm =>
      if produced.contains nm || acc.contains nm then acc else acc ++ [nm]) acc)
    []

/-- A scheduled program whose source invariants and derived authority have been checked. -/
structure CheckedScheduledProgram where private mk ::
  program       : ScheduledProgram
  declEnv       : DeclEnv
  explicitSizes : Std.HashMap UID Nat
  extNames      : List String

/-- Check the complete source-invariant boundary for a direct scheduled program. -/
def validateScheduled (sched : ScheduledProgram) : Except CompileError CheckedScheduledProgram := do
  let declEnv ← buildDeclEnv sched.decls
  checkScheduledReadRanks declEnv sched.stmts
  checkScheduledDtypes declEnv sched.stmts
  unless isTopoOrdered sched.stmts sched.stmts do
    throw (.cyclicDataflow "scheduled program: statements are not in producer-before-consumer order")
  return { program := sched
         , declEnv
         , explicitSizes := declaredAxisSizes sched.decls
         , extNames := orderedExternalNames sched.stmts }

end LeanNCD

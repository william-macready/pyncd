import LeanNCD.DSL.Pipeline.RouteFragments

/-! # Additive collection of multi-writer tensors

A tensor written by several plain statements is the ⊕ of the statements' single-statement
collections (spec §19.2, grouped form; Lean `Program.collect_grouped`). Production realizes that
by a desugar, not by a new evaluator: writer `k` (1-based, schedule order) of `T` is renamed to
the private tensor `T#k` in place, and one collector statement

  `T[slots'] := T#1[idx] + … + T#n[idx]`

is inserted immediately after the last writer. The collector carries the identity nonlinearity
and the writers' agreed annotation, so each `T#k` keeps its own nonlinearity, and a predicate `T`
collects by `Combine.bool` (OR) through its own declaration.

`desugarMultiWriters` is the identity on every schedule in which each name has at most one writer,
so single-writer programs are byte-identical through every later phase.

Slice 1 admits only real-sum and predicate multi-writer sets whose writers are plain `.assign`
statements with bare free slots on the same axis UIDs; every other multi-writer set fails loud
(`multiWriterScatter`, `multiWriterAlgebra`, `writerShapeMismatch`). A name any scan node writes is
left alone (scan mixing stays rejected downstream). The topological-order assertion on the result
is `collectDefinitions` (`ScheduledValidation.lean`), which wraps this pass, because the readiness
predicate lives there. -/

namespace LeanNCD

/-- The private name of writer `k` (1-based, schedule order) of `nm`. -/
def collectorName (nm : String) (k : Nat) : String := s!"{nm}#{k}"

/-- A tensor-bearing declaration cloned under `fresh`: same constructor, element type and axes.
    `none` for axis declarations. -/
def Decl.cloneAs (fresh : String) : Decl → Option Decl
  | .tensor _ ax => some (.tensor fresh ax)
  | .typedTensor ty _ ax => some (.typedTensor ty fresh ax)
  | .predicate _ ax => some (.predicate fresh ax)
  | .linear _ ax b => some (.linear fresh ax b)
  | .typedLinear ty _ ax b => some (.typedLinear ty fresh ax b)
  | .axis .. | .iter .. => none

/-- One multi-writer destination: its name and the schedule positions of its writers, in order. -/
structure WriterGroup where
  name    : String
  writers : List Nat
  deriving Repr, DecidableEq

/-- The plain statement at a schedule position, if that node is `.plain`. -/
private def plainAt? (stmts : List ScanStmt) (i : Nat) : Option Stmt :=
  match stmts[i]? with
  | some (.plain s) => some s
  | _ => none

/-- The names with two or more writers that this pass collects, in first-writer order. A name is
    skipped when a scan node writes it, or when one of its writers is a `.recurMorphism` (the
    escape hatch every entry rejects on its own terms). -/
def writerGroups (stmts : List ScanStmt) : List WriterGroup :=
  let names := (stmts.flatMap routeWrites).eraseDups
  names.filterMap fun nm =>
    let writers := (List.range stmts.length).filter fun i =>
      (stmts[i]?.map (fun sc => (routeWrites sc).contains nm)).getD false
    let allPlain := writers.all fun i => match plainAt? stmts i with
      | some (.assign ..) | some (.scatter ..) => true
      | _ => false
    if writers.length ≥ 2 && allPlain then some ⟨nm, writers⟩ else none

/-- The slice-1 admission rule for one multi-writer set, checked writer by writer in schedule
    order: no scatter, then no `max`/`min` annotation, then bare free slots whose UIDs agree with
    writer 1's position by position. -/
def checkWriterGroup (stmts : List ScanStmt) (g : WriterGroup) : Except CompileError Unit := do
  let ws := g.writers.filterMap (plainAt? stmts)
  for s in ws do
    match s with
    | .scatter .. => throw (.multiWriterScatter g.name)
    | .assign _ ls _ => if slotsBecomeScatter ls then throw (.multiWriterScatter g.name)
    | .recurMorphism .. => pure ()
  for s in ws do
    match s with
    | .assign _ _ r => unless r.agg == .sum do throw (.multiWriterAlgebra g.name)
    | _ => pure ()
  let first := (ws.head?.map Stmt.slots).getD []
  for (s, k) in ws.zipIdx 1 do
    let ls := s.slots
    for (sl, pos) in ls.zipIdx do
      match sl.freeUID?, (first[pos]?).bind LHSSlot.freeUID? with
      | some u, some u0 => unless u == u0 do throw (.writerShapeMismatch g.name k pos)
      | _, _ => throw (.writerShapeMismatch g.name k pos)
    unless ls.length == first.length do
      throw (.writerShapeMismatch g.name k (min ls.length first.length))

/-- The collector statement for `T` with `n` writers, built from writer 1's slots. -/
def collectorStmt (nm : String) (firstSlots : List LHSSlot) (n : Nat) : Stmt :=
  let slots' := producerSlots firstSlots
  let idx := slots'.filterMap LHSSlot.toReadIdx
  .assign nm slots'
    { body := ⟨(List.range n).map fun k => ⟨[.read (collectorName nm (k + 1)) idx]⟩⟩
      nonlin := .identity
      agg := .sum }

/-- Additive-collection desugar (decision note §C). Returns the desugared schedule and the
    generated private names in group order. The identity on single-writer schedules. -/
def desugarMultiWriters (sched : ScheduledProgram) :
    Except CompileError (ScheduledProgram × List String) := do
  let groups := writerGroups sched.stmts
  if groups.isEmpty then return (sched, [])
  for g in groups do checkWriterGroup sched.stmts g
  let generated := groups.flatMap fun g =>
    (List.range g.writers.length).map fun k => collectorName g.name (k + 1)
  let inventory := routeNameInventory sched
  for (nm, i) in generated.zipIdx do
    if inventory.contains nm || (generated.take i).contains nm then
      throw (.reservedNameCollision nm)
  -- Rename each writer in place; emit the collector right after its group's last writer.
  let stmts := sched.stmts.zipIdx.flatMap fun (sc, i) =>
    match groups.find? (fun g => g.writers.contains i) with
    | none => [sc]
    | some g =>
        let k := g.writers.idxOf i + 1
        let renamed : ScanStmt := match sc with
          | .plain (.assign _ ls r) => .plain (.assign (collectorName g.name k) ls r)
          | other => other
        if some i == g.writers.getLast? then
          let firstSlots := ((g.writers.head?.bind (plainAt? sched.stmts)).map Stmt.slots).getD []
          [renamed, .plain (collectorStmt g.name firstSlots g.writers.length)]
        else [renamed]
  -- One clone per writer of each DECLARED destination; undeclared destinations get none.
  let clones := groups.flatMap fun g =>
    match sched.decls.find? (fun d => declaredTensorName? d == some g.name) with
    | none => []
    | some d => (List.range g.writers.length).filterMap fun k =>
        d.cloneAs (collectorName g.name (k + 1))
  return ({ sched with
              stmts
              decls := sched.decls ++ clones
              env := clones.foldl (fun m d => m.insert d.name d) sched.env },
          generated)

end LeanNCD

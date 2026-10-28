import LeanNCD.DSL.Pipeline.RouteFragments

/-! # Additive collection of multi-writer tensors

A tensor written by several plain statements is the ⊕ of the statements' single-statement
collections (spec §19.2, grouped form; Lean `Program.collect_grouped`). Production realizes that
by a desugar, not by a new evaluator: writer `k` (1-based, schedule order) of `T` is renamed to
the private tensor `T#k` in place, and one collector statement

  `T[slots'] := T#1[idx] + … + T#n[idx]`

is inserted immediately after the last writer. The collector carries the identity nonlinearity
and the group's agreed annotation (`writerSort?`: `sum` for a real or predicate group, `max`/`min`
for a tropical one), so each `T#k` keeps its own nonlinearity, and a predicate `T` collects by
`Combine.bool` (OR) through its own declaration.

`desugarMultiWriters` is the identity on every schedule in which each name has at most one writer,
so single-writer programs are byte-identical through every later phase.

Existing all-bare groups keep positionwise UID agreement. Real and tropical groups may also
contain bounded scatter writers, using a distinct declared coordinate basis or the first ordinary
bare assignment. Their retained shape obligations require exact realized extent equality after
inference; predicate, explicit-constant and multi-axis scatter groups remain refused.
A group's sort is the one its writers' votes agree on (`writerSort?`); sort-neutral copy writers
abstain beside a non-neutral writer and are rewritten to the agreed sort (`Stmt.withAgg`), so a
copy's bare out-of-range read pads the group's `0_K` and a copy of a predicate reads it through the group's
bool -> tropical cast (true/false as `1_K`/`0_K`, i.e. `0`/`-inf` for max, not `1`/`0`: the cast follows
the statement's annotation, so the rewrite changes values, not only the pad). A name written by two or more
nodes of which one is a scan node is rejected outright (`multiWriterScan`). The topological-order
assertion on the result is made by `collectDefinitions` in `ScheduledValidation.lean`, which wraps
this pass (`desugarMultiWriters` itself does not check order), because the readiness predicate
lives there. -/

namespace LeanNCD

/-- The private name of writer `k` (1-based, schedule order) of `nm`. -/
def collectorName (nm : String) (k : Nat) : String := s!"{nm}#{k}"

/-- The public tensor a private writer name `collectorName nm k` belongs to (everything before the
    last `#`). Only meaningful for names `desugarMultiWriters` generated: any name without a `#`
    is returned unchanged. Used to name the user's tensor in a diagnostic that would otherwise
    name the private clone. -/
def collectorOwner (nm : String) : String :=
  match nm.splitOn "#" with
  | [] | [_] => nm
  | parts => "#".intercalate parts.dropLast

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

/-- The first name (in first-writer order) written by two or more nodes of which at least one is a
    scan node (`.scan`/`.scanPre`): plain + scan, or scan + scan. Writers are counted per NODE
    (`stmts.filter … (routeWrites sc).contains nm`), so one scan node that writes a name in both
    its base and recurrence halves is a single writer; `routeWrites`' own `eraseDups` only
    dedups the names within one node, and the `eraseDups` here only dedups the candidate names. -/
def scanWriterConflict? (stmts : List ScanStmt) : Option String :=
  (stmts.flatMap routeWrites).eraseDups.find? fun nm =>
    let writers := stmts.filter fun sc => (routeWrites sc).contains nm
    writers.length ≥ 2 && writers.any fun sc => match sc with | .plain _ => false | _ => true

/-- The names with two or more writers that this pass collects, in first-writer order. A name is
    skipped when one of its writers is a `.recurMorphism` (the escape hatch every entry rejects on
    its own terms) or a scan node (`desugarMultiWriters` rejects such multi-writer names first,
    through `scanWriterConflict?`). -/
def writerGroups (stmts : List ScanStmt) : List WriterGroup :=
  let names := (stmts.flatMap routeWrites).eraseDups
  names.filterMap fun nm =>
    let writers := (List.range stmts.length).filter fun i =>
      (stmts[i]?.map (fun sc => (routeWrites sc).contains nm)).getD false
    let allPlain := writers.all fun i => match plainAt? stmts i with
      | some (.assign ..) | some (.scatter ..) => true
      | _ => false
    if writers.length ≥ 2 && allPlain then some ⟨nm, writers⟩ else none

/-- True only for the newly admitted collection surface, not legacy all-bare groups. -/
def WriterGroup.needsB5 (g : WriterGroup) (stmts : List ScanStmt) : Bool :=
  (g.writers.filterMap (plainAt? stmts)).any fun
    | .scatter .. => true
    | .assign _ ls _ => slotsBecomeScatter ls
    | _ => false

def Decl.tensorAxes? : Decl → Option (List AxisSpec)
  | .tensor _ ax | .typedTensor _ _ ax | .predicate _ ax
  | .linear _ ax _ | .typedLinear _ _ ax _ => some ax
  | _ => none

/-- Select a full-domain basis. An explicit bare scatter is not a fallback assignment. -/
def writerGroupBasis (env : DeclEnv) (stmts : List ScanStmt) (g : WriterGroup) :
    Except CompileError (List LHSSlot) := do
  if let some ax := (env[g.name]?).bind Decl.tensorAxes? then
    let us := ax.map (·.uid)
    unless us.length == us.eraseDups.length do throw (.multiWriterRepeatedBasis g.name)
    return ax.map LHSSlot.free
  let ws := g.writers.filterMap (plainAt? stmts)
  match ws.find? (fun
    | .assign _ ls _ => !slotsBecomeScatter ls && ls.all (fun s => s.freeUID?.isSome)
    | _ => false) with
  | some s => return producerSlots s.slots
  | none => throw (.multiWriterNeedsDeclaredShape g.name)

/-- Source geometry retained across renaming for a post-inference equality check. -/
structure CollectorShapeObligation where
  name : String
  basis : List LHSSlot
  writers : List (List LHSSlot)

def collectorShapeObligations (sched : ScheduledProgram) :
    Except CompileError (List CollectorShapeObligation) :=
  ((writerGroups sched.stmts).filter (·.needsB5 sched.stmts)).mapM fun g => do
    return { name := g.name
             basis := ← writerGroupBasis sched.env sched.stmts g
             writers := (g.writers.filterMap (plainAt? sched.stmts)).map Stmt.slots }

/-- Static geometry, agreed sort, then basis/rank checks for bounded scatter groups.
    Legacy all-bare groups instead retain positionwise UID agreement. -/
def checkWriterGroup (env : DeclEnv) (stmts : List ScanStmt) (g : WriterGroup) :
    Except CompileError SortAlgebra := do
  let ws := g.writers.filterMap (plainAt? stmts)
  for s in ws do
    match s with
    | .scatter _ ls _ =>
        unless ls.all LHSSlot.boundedScatter && env.declAlgebra g.name != .bool do
          throw (.multiWriterScatter g.name)
    | .assign _ ls _ =>
        if slotsBecomeScatter ls ||
            (g.needsB5 stmts && ls.any (fun s => s.freeUID?.isNone)) then
          throw (.multiWriterScatter g.name)
    | .recurMorphism .. => pure ()
  let agreed ← match writerSort? env ws with
    | none => throw (.multiWriterAlgebra g.name)
    | some a => pure a
  if g.needsB5 stmts then
    let basis ← writerGroupBasis env stmts g
    for s in ws do
      unless s.slots.length == basis.length do
        throw (.rankMismatch g.name basis.length s.slots.length)
    return agreed
  let first := (ws.head?.map Stmt.slots).getD []
  for (s, k) in ws.zipIdx 1 do
    let ls := s.slots
    for (sl, pos) in ls.zipIdx do
      match sl.freeUID?, (first[pos]?).bind LHSSlot.freeUID? with
      | some u, some u0 => unless u == u0 do throw (.writerShapeMismatch g.name k pos)
      | _, _ => throw (.writerShapeMismatch g.name k pos)
    unless ls.length == first.length do
      throw (.writerShapeMismatch g.name k (min ls.length first.length))
  return agreed

/-- The collector statement for `T` with `n` writers, built from the group's coordinate basis
    (writer 1's slots for a legacy all-bare group); `agg` is the group's agreed annotation. -/
def collectorStmt (nm : String) (basis : List LHSSlot) (n : Nat) (agg : AggOp) : Stmt :=
  let slots' := producerSlots basis
  let idx := slots'.filterMap LHSSlot.toReadIdx
  .assign nm slots'
    { body := ⟨(List.range n).map fun k => ⟨[.read (collectorName nm (k + 1)) idx]⟩⟩
      nonlin := .identity
      agg }

/-- Additive-collection desugar (decision note §C). Returns the desugared schedule and the
    generated private names in group order. The identity on single-writer schedules.

    Error priority (the first failing check wins, whatever the order of names in the schedule):
    `multiWriterScan` (any name, `scanWriterConflict?`) first; then, per group in first-writer
    order, geometry, algebra, then basis/shape diagnostics (the order of checks
    inside `checkWriterGroup`; a group's failure stops the pass before the next group is looked
    at); `reservedNameCollision` last, after every group has passed. -/
def desugarMultiWriters (sched : ScheduledProgram) :
    Except CompileError (ScheduledProgram × List String) := do
  if let some nm := scanWriterConflict? sched.stmts then throw (.multiWriterScan nm)
  let groups := writerGroups sched.stmts
  if groups.isEmpty then return (sched, [])
  let mut agreed : List SortAlgebra := []
  let mut bases : List (List LHSSlot) := []
  for g in groups do
    agreed := agreed ++ [← checkWriterGroup sched.env sched.stmts g]
    bases := bases ++ [← if g.needsB5 sched.stmts then writerGroupBasis sched.env sched.stmts g
      else pure (((g.writers.head?.bind (plainAt? sched.stmts)).map Stmt.slots).getD [])]
  let generated := groups.flatMap fun g =>
    (List.range g.writers.length).map fun k => collectorName g.name (k + 1)
  let inventory := routeNameInventory sched
  for (nm, i) in generated.zipIdx do
    if inventory.contains nm || (generated.take i).contains nm then
      throw (.reservedNameCollision nm)
  -- Rename each writer in place; emit the collector right after its group's last writer.
  let stmts := sched.stmts.zipIdx.flatMap fun (sc, i) =>
    match groups.zip (agreed.zip bases) |>.find? (fun (g, _) => g.writers.contains i) with
    | none => [sc]
    | some (g, sort, basis) =>
        let k := g.writers.idxOf i + 1
        let renamed : ScanStmt := match sc with
          | .plain (.assign _ ls r) =>
              let w := Stmt.assign (collectorName g.name k) ls r
              .plain (if w.isSortNeutral then w.withAgg sort.stateAgg else w)
          | .plain (.scatter _ ls r) =>
              let w := Stmt.scatter (collectorName g.name k) ls r
              .plain (if w.isSortNeutral then w.withAgg sort.stateAgg else w)
          | other => other
        if some i == g.writers.getLast? then
          [renamed, .plain (collectorStmt g.name basis g.writers.length sort.stateAgg)]
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

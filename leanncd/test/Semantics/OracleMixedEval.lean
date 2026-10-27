import LeanNCD.Semantics.Source.SortedDifferential
import Semantics.OracleSortRules

/-! Oracle sorts T3: the heterogeneous exact evaluator.

Where `Oracle.runWith` runs one carrier `K` over a whole program, `runMixed` runs EACH statement in
the sort the independent predictor assigns it (`Prediction.stmtSorts`, the sort of its destination's
writer group), over the shared value type `ExtVal`. The sort operations are restated here by hand
from the design (real `+`/`*`; max-plus `max`/`+` with `-inf` absorbing; min-plus `min`/`+` with
`+inf` absorbing); this file uses no `Semiring` or `Carrier` instance, so it cannot share a defect
with the typed path. The finite-rational input embedding is `ExtVal.fin`.

An occurrence is the `mul` of its reads; a statement's occurrences at a cell combine with that
sort's `add`; the statements writing one tensor combine with the tensor's sort `add`. A real
statement may not read a non-finite value (design D5: `nonFiniteIntoReal`). A tropical statement
reading a tensor of the other tropical sort is a harness bug (the predictor refuses it), reported as
`inconsistent`. Real <-> tropical reads are the identity on finite values. -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source Oracle

namespace LeanNCD.OracleSorts

/-! ### Sort operations over `ExtVal` -/

/-- Larger of two values (`-inf` least, `+inf` greatest). -/
def extMax : ExtVal → ExtVal → ExtVal
  | .negInf, y => y
  | x, .negInf => x
  | .posInf, _ => .posInf
  | _, .posInf => .posInf
  | .fin x, .fin y => if x ≤ y then .fin y else .fin x

/-- Smaller of two values. -/
def extMin : ExtVal → ExtVal → ExtVal
  | .posInf, y => y
  | x, .posInf => x
  | .negInf, _ => .negInf
  | _, .negInf => .negInf
  | .fin x, .fin y => if x ≤ y then .fin x else .fin y

/-- The additive identity of a sort. Bool is not modelled by the evaluator (it is rejected up front). -/
def MSort.zero : MSort → ExtVal
  | .real => .fin 0
  | .bool => .fin 0
  | .maxPlus => .negInf
  | .minPlus => .posInf

/-- The multiplicative identity of a sort. -/
def MSort.one : MSort → ExtVal
  | .real => .fin 1
  | .bool => .fin 1
  | .maxPlus => .fin 0
  | .minPlus => .fin 0

/-- The sort's `+`. A real operand is always finite (the read cast guards it), so the fallback arm
for a non-finite real operand is never reached. -/
def MSort.add : MSort → ExtVal → ExtVal → ExtVal
  | .real, .fin x, .fin y => .fin (x + y)
  | .bool, .fin x, .fin y => .fin (x + y)
  | .real, x, _ => x
  | .bool, x, _ => x
  | .maxPlus, x, y => extMax x y
  | .minPlus, x, y => extMin x y

/-- The sort's `*`: real multiplication; tropical addition with the sort's zero absorbing. -/
def MSort.mul : MSort → ExtVal → ExtVal → ExtVal
  | .real, .fin x, .fin y => .fin (x * y)
  | .bool, .fin x, .fin y => .fin (x * y)
  | .real, x, _ => x
  | .bool, x, _ => x
  | .maxPlus, .negInf, _ => .negInf
  | .maxPlus, _, .negInf => .negInf
  | .maxPlus, .fin x, .fin y => .fin (x + y)
  | .maxPlus, _, _ => .posInf
  | .minPlus, .posInf, _ => .posInf
  | .minPlus, _, .posInf => .posInf
  | .minPlus, .fin x, .fin y => .fin (x + y)
  | .minPlus, _, _ => .negInf

/-! ### The evaluator -/

inductive MixedEvalError
  | unavailable (u : Oracle.Unavailable)
  | nonFiniteIntoReal (declaration : Nat) (coordinate : List Nat)
  | inconsistent (message : String)
  deriving DecidableEq, Repr

/-- One occurrence: its statement (original ordinal), destination coordinate, assignment, the sort it
RAN in, the sort of the statement's own annotation, and the read values after the cast. -/
structure MixedOccurrence where
  statement : Nat
  coordinate : List Nat
  assignment : List (UID × Nat)
  sort : MSort
  own : MSort
  reads : List ExtVal
  deriving Repr

structure MixedResult where
  tensors : List (Oracle.Tensor ExtVal)
  occurrences : List MixedOccurrence

private abbrev M := Except MixedEvalError

private def lift {α : Type} (e : Except Oracle.Unavailable α) : M α := e.mapError .unavailable

/-- The cast of a read value into a statement running in `run`. A real statement takes finite values
only (D5). A tropical statement takes real or same-sort values unchanged; a tensor of the other
tropical sort is refused by the predictor, so it is a harness error here. -/
def readCast (run src : MSort) (declaration : Nat) (coordinate : List Nat) (v : ExtVal) :
    Except MixedEvalError ExtVal :=
  if run == .real then
    match v with
    | .fin _ => pure v
    | .negInf | .posInf => throw (.nonFiniteIntoReal declaration coordinate)
  else if src.isTropical && src != run then
    throw (.inconsistent s!"{repr run} statement reads a {repr src} tensor")
  else pure v

private def tensorAt (store : List (Oracle.Tensor ExtVal)) (declaration : Nat) :
    Except Oracle.Unavailable (Oracle.Tensor ExtVal) :=
  match store.find? (fun t => t.declaration == declaration) with
  | some t => .ok t
  | none => .error ⟨{ side := .declaration, declaration := some declaration },
      .missingTensor declaration⟩

private def initialInputs (admitted : AdmittedSource) :
    Except Oracle.Unavailable (List (Oracle.Tensor ExtVal)) := do
  let mut store := []
  for t in List.finRange admitted.source.table.entries.length do
    let entry := admitted.source.table.entry t
    if h : entry.role = .input then
      let values := (admitted.source.inputs.buffers t h).values
      let shape := entry.axes.map (·.extent)
      unless values.length == Oracle.cellCount shape do
        throw ⟨{ side := .input, declaration := some entry.declaration },
          .length (Oracle.cellCount shape) values.length⟩
      store := store ++ [⟨entry.declaration, entry.name, entry.role, shape, values.map .fin⟩]
  pure store

/-- One term at one destination cell: the occurrences whose write image is the cell, each the `mul`
of its (cast) reads, combined by the statement's sort `add`. -/
private def termAt (admitted : AdmittedSource) (store : List (Oracle.Tensor ExtVal))
    (sortOfDecl : Nat → MSort) (statement : AdmittedStatement admitted.source)
    (run own : MSort)
    (term : Term admitted.source.context statement.output.context
      admitted.source.table.declarations)
    (coordinate : List Nat) : M (ExtVal × List MixedOccurrence) := do
  let support := statement.output.forms.flatMap WriteForm.uids ++
    term.sourceReads.flatMap (·.indices)
  let axes := admitted.source.context.axes.filter (fun a => a.uid ∈ support)
  let shape := (admitted.source.table.entry statement.output.tensor).axes.map (·.extent)
  let mut occurrences : List MixedOccurrence := []
  let mut total : ExtVal := run.zero
  for assignment in Oracle.assignments axes do
    let output ← lift (Oracle.destination statement.output.origin shape assignment
      statement.output.forms)
    if output == coordinate then
      let mut product : ExtVal := run.one
      let mut reads : List ExtVal := []
      for read in term.sourceReads do
        let entry := admitted.source.table.entry read.read.tensor
        let src ← lift (tensorAt store entry.declaration)
        let readCoordinate ← lift (Oracle.slots read.origin assignment read.indices)
        let raw ← lift (Oracle.lookup read.origin (entry.axes.map (·.extent)) src readCoordinate)
        let value ← readCast run (sortOfDecl entry.declaration) entry.declaration readCoordinate raw
        reads := reads ++ [value]
        product := run.mul product value
      occurrences := occurrences ++ [⟨statement.original, coordinate, assignment, run, own, reads⟩]
      total := run.add total product
  pure (total, occurrences)

/-- The heterogeneous evaluator. `stmts` are the snapshot's statements (`AdmittedStatement.original`
indexes them; their annotations are recorded as each occurrence's `own` sort and never used to
compute); `p.stmtSorts` gives the sort each statement RUNS in. `order` names the original
declaration ordinals of the non-input tensors in dependency order. -/
def runMixed (admitted : AdmittedSource) (stmts : List Stmt) (p : Prediction) (order : List Nat) :
    Except MixedEvalError MixedResult := do
  lift (Oracle.checkOrder admitted order)
  -- the sort each statement runs in: its writer group's (never its own annotation)
  let mut runs : List (Nat × MSort × MSort) := []
  for statement in admitted.statements do
    let run ← match p.stmtSorts[statement.original]? with
      | some k => pure k
      | none => throw (.inconsistent s!"no predicted sort for statement {statement.original}")
    let own ← match stmts[statement.original]? with
      | some s => pure (annotationSort (annotationOf s))
      | none => throw (.inconsistent s!"no statement {statement.original}")
    if run == .bool then throw (.inconsistent "bool statements are outside the Source sublanguage")
    runs := runs ++ [(statement.original, run, own)]
  let runOf (i : Nat) : MSort := ((runs.find? (·.1 == i)).map (·.2.1)).getD .real
  let ownOf (i : Nat) : MSort := ((runs.find? (·.1 == i)).map (·.2.2)).getD .real
  -- a tensor's sort: its writers' common run sort (an input or unwritten tensor is real)
  let writersOf (decl : Nat) :=
    admitted.statements.filter fun s =>
      (admitted.source.table.entry s.output.tensor).declaration == decl
  let mut tensorSorts : List (Nat × MSort) := []
  for entry in admitted.source.table.entries do
    let ks := ((writersOf entry.declaration).map (fun s => runOf s.original)).eraseDups
    match ks with
    | [] => tensorSorts := tensorSorts ++ [(entry.declaration, .real)]
    | [k] => tensorSorts := tensorSorts ++ [(entry.declaration, k)]
    | _ => throw (.inconsistent s!"tensor {entry.declaration} is written in several sorts")
  let sortOfDecl (d : Nat) : MSort := ((tensorSorts.find? (·.1 == d)).map (·.2)).getD .real
  let mut store ← lift (initialInputs admitted)
  let mut occurrences : List MixedOccurrence := []
  for target in order do
    let origin : SourceOrigin := { side := .declaration, declaration := some target }
    let entry ← match admitted.source.table.entries.find? (fun t => t.declaration == target) with
      | some entry => pure entry
      | none => throw (.unavailable ⟨origin, .missingTensor target⟩)
    let shape := entry.axes.map (·.extent)
    let tsort := sortOfDecl target
    let mut values : List ExtVal := []
    for coordinate in Oracle.coordinates shape do
      let mut cell : ExtVal := tsort.zero
      for statement in admitted.statements do
        if (admitted.source.table.entry statement.output.tensor).declaration == target then
          let mut stmtTotal : ExtVal := (runOf statement.original).zero
          for term in statement.terms do
            let (t, occs) ← termAt admitted store sortOfDecl statement
              (runOf statement.original) (ownOf statement.original) term coordinate
            occurrences := occurrences ++ occs
            stmtTotal := (runOf statement.original).add stmtTotal t
          cell := tsort.add cell stmtTotal
      values := values ++ [cell]
    store := store ++ [⟨entry.declaration, entry.name, entry.role, shape, values⟩]
  let tensors ← lift (admitted.source.table.entries.mapM fun entry =>
    tensorAt store entry.declaration)
  pure ⟨tensors, occurrences⟩

end LeanNCD.OracleSorts

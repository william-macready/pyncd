import LeanNCD.Semantics.Source.Admission

namespace LeanNCD.Semantics.Source.Oracle

inductive Cause
  | missingOrder
  | duplicateTarget (declaration : Nat)
  | unexpectedTarget (declaration : Nat)
  | omittedTarget (declaration : Nat)
  | dependencyNotEarlier (declaration : Nat)
  | missingTensor (declaration : Nat)
  | missingUID (uid : UID)
  | shape (expected actual : List Nat)
  | length (expected actual : Nat)
  | coordinateRank (expected actual : Nat)
  | coordinateBound (slot coordinate extent : Nat)
  | offsetBound (offset length : Nat)
  deriving DecidableEq, Repr

structure Unavailable where
  origin : SourceOrigin
  cause : Cause
  deriving DecidableEq, Repr

structure Tensor where
  declaration : Nat
  name : String
  role : TensorRole
  shape : List Nat
  values : List ℚ
  deriving DecidableEq, Repr

structure ReadValue where
  origin : SourceOrigin
  declaration : Nat
  coordinate : List Nat
  value : ℚ
  deriving DecidableEq, Repr

structure Occurrence where
  origin : SourceOrigin
  assignment : List (UID × Nat)
  output : List Nat
  reads : List ReadValue
  value : ℚ
  deriving DecidableEq, Repr

structure TermFiber where
  origin : SourceOrigin
  occurrences : List Occurrence
  value : ℚ
  deriving DecidableEq, Repr

structure Contribution where
  origin : SourceOrigin
  coordinate : List Nat
  terms : List TermFiber
  value : ℚ
  deriving DecidableEq, Repr

structure Result where
  tensors : List Tensor
  contributions : List Contribution
  deriving DecidableEq, Repr

private def unavailable (origin : SourceOrigin) (cause : Cause) : Unavailable :=
  ⟨origin, cause⟩

def cellCount (shape : List Nat) : Nat :=
  shape.foldl (· * ·) 1

def coordinates : List Nat → List (List Nat)
  | [] => [[]]
  | n :: rest => (List.range n).flatMap fun i => (coordinates rest).map (i :: ·)

private def offset (origin : SourceOrigin) (shape coordinate : List Nat) :
    Except Unavailable Nat := do
  unless coordinate.length == shape.length do
    throw (unavailable origin (.coordinateRank shape.length coordinate.length))
  go shape coordinate 0 0
where
  go : List Nat → List Nat → Nat → Nat → Except Unavailable Nat
    | [], [], _, acc => .ok acc
    | n :: ns, i :: is, slot, acc =>
      if i < n then go ns is (slot + 1) (acc * n + i)
      else .error (unavailable { origin with slot := some slot } (.coordinateBound slot i n))
    | ns, is, _, _ =>
      .error (unavailable origin (.coordinateRank ns.length is.length))

def lookup (origin : SourceOrigin) (expectedShape : List Nat)
    (tensor : Tensor) (coordinate : List Nat) : Except Unavailable ℚ := do
  unless tensor.shape == expectedShape do
    throw (unavailable origin (.shape expectedShape tensor.shape))
  unless tensor.values.length == cellCount tensor.shape do
    throw (unavailable origin (.length (cellCount tensor.shape) tensor.values.length))
  let i ← offset origin tensor.shape coordinate
  if h : i < tensor.values.length then
    pure tensor.values[i]
  else
    throw (unavailable origin (.offsetBound i tensor.values.length))

private def slots (origin : SourceOrigin) (assignment : List (UID × Nat))
    (uids : List UID) : Except Unavailable (List Nat) :=
  uids.zipIdx.mapM fun (uid, slot) =>
    match assignment.find? (fun p => p.1 == uid) with
    | some p => .ok p.2
    | none => .error (unavailable { origin with slot := some slot } (.missingUID uid))

private def assignments : List Axis → List (List (UID × Nat))
  | [] => [[]]
  | a :: rest =>
    (List.range a.extent).flatMap fun i => (assignments rest).map ((a.uid, i) :: ·)

private def tensorAt (origin : SourceOrigin) (store : List Tensor) (declaration : Nat) :
    Except Unavailable Tensor :=
  match store.find? (fun t => t.declaration == declaration) with
  | some t => .ok t
  | none => .error (unavailable origin (.missingTensor declaration))

private def checkOrder (admitted : AdmittedSource) (order : List Nat) :
    Except Unavailable Unit := do
  let entries := admitted.source.table.entries
  let targets := (entries.filter (fun t => t.role != .input)).map (·.declaration)
  let mut seen : List Nat := []
  for target in order do
    let origin : SourceOrigin := { side := .declaration, declaration := some target }
    if target ∈ seen then throw (unavailable origin (.duplicateTarget target))
    unless target ∈ targets do throw (unavailable origin (.unexpectedTarget target))
    seen := seen ++ [target]
  for target in targets do
    unless target ∈ order do
      throw (unavailable { side := .declaration, declaration := some target }
        (.omittedTarget target))
  let mut earlier := (entries.filter (fun t => t.role == .input)).map (·.declaration)
  for target in order do
    for statement in admitted.statements do
      if (admitted.source.table.entry statement.output.tensor).declaration == target then
        for term in statement.terms do
          for read in term.sourceReads do
            let dependency := (admitted.source.table.entry read.read.tensor).declaration
            unless dependency ∈ earlier do
              throw (unavailable read.origin (.dependencyNotEarlier dependency))
    earlier := earlier ++ [target]

private def initialInputs (admitted : AdmittedSource) : Except Unavailable (List Tensor) := do
  let mut store := []
  for t in List.finRange admitted.source.table.entries.length do
    let entry := admitted.source.table.entry t
    if h : entry.role = .input then
      let values := (admitted.source.inputs.buffers t h).values
      let shape := entry.axes.map (·.extent)
      unless values.length == cellCount shape do
        throw (unavailable { side := .input, declaration := some entry.declaration }
          (.length (cellCount shape) values.length))
      store := store ++ [⟨entry.declaration, entry.name, entry.role, shape, values⟩]
  pure store

private def termFiber (admitted : AdmittedSource) (store : List Tensor)
    (statement : AdmittedStatement admitted.source)
    (term : Term admitted.source.context statement.output.context
      admitted.source.table.declarations)
    (coordinate : List Nat) : Except Unavailable TermFiber := do
  let support := statement.output.indices ++ term.sourceReads.flatMap (·.indices)
  let axes := admitted.source.context.axes.filter (fun a => a.uid ∈ support)
  let mut occurrences := []
  let mut total : ℚ := 0
  for assignment in assignments axes do
    let output ← slots statement.output.origin assignment statement.output.indices
    if output == coordinate then
      let mut product : ℚ := 1
      let mut reads := []
      for read in term.sourceReads do
        let entry := admitted.source.table.entry read.read.tensor
        let tensor ← tensorAt read.origin store entry.declaration
        let readCoordinate ← slots read.origin assignment read.indices
        let value ← lookup read.origin (entry.axes.map (·.extent)) tensor readCoordinate
        reads := reads ++ [⟨read.origin, entry.declaration, readCoordinate, value⟩]
        product := product * value
      occurrences := occurrences ++ [⟨term.origin, assignment, output, reads, product⟩]
      total := total + product
  pure ⟨term.origin, occurrences, total⟩

private def contribution (admitted : AdmittedSource) (store : List Tensor)
    (statement : AdmittedStatement admitted.source) (coordinate : List Nat) :
    Except Unavailable Contribution := do
  let terms ← statement.terms.mapM (termFiber admitted store statement · coordinate)
  pure ⟨statement.output.origin, coordinate, terms,
    terms.foldl (fun sum term => sum + term.value) 0⟩

/-- Exact acyclic fixture evaluator. The order names original tensor declaration ordinals.
Dependency checking is syntactic and conservative, even for empty fibers. -/
def run (admitted : AdmittedSource) (dependencyOrder : Option (List Nat)) :
    Except Unavailable Result := do
  let order ← match dependencyOrder with
    | none => throw (unavailable {} .missingOrder)
    | some order => pure order
  checkOrder admitted order
  let mut store ← initialInputs admitted
  let mut contributions := []
  for target in order do
    let origin : SourceOrigin := { side := .declaration, declaration := some target }
    let entry ← match admitted.source.table.entries.find? (fun t => t.declaration == target) with
      | some entry => pure entry
      | none => throw (unavailable origin (.missingTensor target))
    let shape := entry.axes.map (·.extent)
    let mut values := []
    for coordinate in coordinates shape do
      let mut total : ℚ := 0
      for statement in admitted.statements do
        if (admitted.source.table.entry statement.output.tensor).declaration == target then
          let c ← contribution admitted store statement coordinate
          contributions := contributions ++ [c]
          total := total + c.value
      values := values ++ [total]
    store := store ++ [⟨entry.declaration, entry.name, entry.role, shape, values⟩]
  let tensors ← admitted.source.table.entries.mapM fun entry =>
    tensorAt { side := .declaration, declaration := some entry.declaration } store entry.declaration
  let canonical := admitted.statements.flatMap fun statement =>
    contributions.filter (fun c => c.origin.statement == some statement.original)
  pure ⟨tensors, canonical⟩

end LeanNCD.Semantics.Source.Oracle

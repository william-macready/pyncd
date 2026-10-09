import LeanNCD.Semantics.Source.Statement

namespace LeanNCD.Semantics.Source

instance sourceTensorFinite (table : TensorTable) : Fintype table.declarations.Tensor :=
  inferInstanceAs (Fintype (Fin table.entries.length))

instance sourceTensorEq (table : TensorTable) : DecidableEq table.declarations.Tensor :=
  inferInstanceAs (DecidableEq (Fin table.entries.length))

def AdmittedSource.isInput (source : AdmittedSource) (t : source.source.table.declarations.Tensor) :
    Bool :=
  decide ((source.source.table.entry t).role = .input)

def AdmittedSource.isOutput (source : AdmittedSource) (t : source.source.table.declarations.Tensor) :
    Bool :=
  decide ((source.source.table.entry t).role = .output)

structure StatementTag (source : AdmittedSource) (t : source.source.table.declarations.Tensor) where
  sourceIndex : Fin source.statements.length
  target : (source.statements.get sourceIndex).output.tensor = t

def StatementTag.statement (tag : StatementTag source t) : AdmittedStatement source.source :=
  source.statements.get tag.sourceIndex

def StatementTag.original (tag : StatementTag source t) : Nat :=
  tag.statement.original

def targetStatements (source : AdmittedSource) (t : source.source.table.declarations.Tensor) :
    List (StatementTag source t) :=
  (List.finRange source.statements.length).filterMap fun i =>
    if h : (source.statements.get i).output.tensor = t then some ⟨i, h⟩ else none

theorem StatementTag.mem_targetStatements (tag : StatementTag source t) :
    tag ∈ targetStatements source t := by
  rcases tag with ⟨i, h⟩
  apply List.mem_filterMap.mpr
  exact ⟨i, List.mem_finRange i, dif_pos h⟩

def StatementTag.layout (tag : StatementTag source t) :
    Layout tag.statement.output.context.axes :=
  canonicalLayout tag.statement.output.context.axes

def StatementTag.valuation (tag : StatementTag source t) (v : Fin tag.layout.count) :
    Coord tag.statement.output.context.axes :=
  tag.layout.enumerate v

def AdmittedSource.program {K : Type} [Semiring K] (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) :
    Program (fun _ => K) source.source.table.declarations r where
  tensors := inferInstance
  input := source.isInput
  output := source.isOutput
  output_defined := by
    intro t h
    simp only [AdmittedSource.isOutput, decide_eq_true_eq] at h
    simp [AdmittedSource.isInput, h]
  statements := fun t => (targetStatements source t.val).length
  valuations := fun t s => ((targetStatements source t.val).get s).layout.count
  guard := fun _ _ _ => true
  destination := fun t s v =>
    let tag := (targetStatements source t.val).get s
    tag.target ▸ tag.statement.destination (tag.valuation v.val)
  body := fun t s =>
    let tag := (targetStatements source t.val).get s
    tag.statement.body (fun v => tag.valuation v.val)

def AdmittedSource.statementTag {K : Type} [Semiring K] (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t : (source.program r).Defined)
    (s : Fin ((source.program r).statements t)) : StatementTag source t.val :=
  (targetStatements source t.val).get s

theorem AdmittedSource.program_defined_iff {K : Type} [Semiring K] (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t : source.source.table.declarations.Tensor) :
    (source.program r).input t = false ↔ (source.source.table.entry t).role ≠ .input := by
  simp [AdmittedSource.program, AdmittedSource.isInput]

theorem AdmittedSource.program_output_iff {K : Type} [Semiring K] (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t : source.source.table.declarations.Tensor) :
    (source.program r).output t = true ↔ (source.source.table.entry t).role = .output := by
  simp [AdmittedSource.program, AdmittedSource.isOutput]

theorem AdmittedSource.program_guard {K : Type} [Semiring K] (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t : (source.program r).Defined)
    (s : Fin ((source.program r).statements t)) (v : Fin ((source.program r).valuations t s)) :
    (source.program r).guard t s v = true := rfl

theorem AdmittedSource.program_interpret_body {K : Type} [Semiring K] (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (ρ : Store (fun _ => K) source.source.table.declarations)
    (t : (source.program r).Defined) (s : Fin ((source.program r).statements t))
    (v : {v : Fin ((source.program r).valuations t s) // (source.program r).guard t s v = true}) :
    interpret semiringOps ρ ((source.program r).body t s) v =
      some (((source.statementTag r t s).statement.terms.map
        (fun term => term.value ρ ((source.statementTag r t s).valuation v.val))).sum) :=
  (source.statementTag r t s).statement.interpret_body ρ _ v

theorem AdmittedSource.program_footprint_body {K : Type} [Semiring K] (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t : (source.program r).Defined)
    (s : Fin ((source.program r).statements t))
    (v : {v : Fin ((source.program r).valuations t s) // (source.program r).guard t s v = true}) :
    footprint ((source.program r).body t s) v =
      (source.statementTag r t s).statement.terms.flatMap
        (fun term => term.readFootprint ((source.statementTag r t s).valuation v.val)) :=
  (source.statementTag r t s).statement.footprint_body _ v

theorem AdmittedSource.program_destination {K : Type} [Semiring K] (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t : (source.program r).Defined)
    (s : Fin ((source.program r).statements t))
    (v : {v : Fin ((source.program r).valuations t s) // (source.program r).guard t s v = true}) :
    (source.program r).destination t s v =
      (source.statementTag r t s).target ▸
        (source.statementTag r t s).statement.destination
          ((source.statementTag r t s).valuation v.val) := rfl

abbrev LoweredSource (source : AdmittedSource) :=
  Program RationalReference.Carrier source.source.table.declarations RationalReference.registry

def elaborateSource (source : AdmittedSource) : LoweredSource source :=
  source.program RationalReference.registry

end LeanNCD.Semantics.Source

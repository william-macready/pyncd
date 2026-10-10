import LeanNCD.Semantics.Source.RawCorrespondence
import LeanNCD.Semantics.Source.RawSemanticConnection
import Semantics.SourceAdmissionFixtures
import Semantics.SourceProgramFixtures
import LeanNCD.DSL.Elab

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source SourceAdmissionFixtures

namespace SourceRawCorrespondenceTest

def parsed : TLProgram := tlprog!{
  axis a : ℕ = 2
  tensor f64 X(a), Y(a)
  Y[a] := X[a]
}

def parsedSpecs : List TensorSpec := [⟨1, .input, [2]⟩, ⟨2, .output, [2]⟩]
def parsedInputs : List InputBinding := [⟨1, [2], [3, 5]⟩]

def asymmetric : TLProgram := ⟨decls, [
  .assign "Y" [.free i] (rhs [
    [.read "B" [.axis i], .read "A" [.axis i, .axis k], .read "B" [.axis i]],
    [.read "A" [.axis i, .axis k]], []]),
  .assign "Diagonal" [.free i, .free i] (rhs [[]]),
  .assign "Y" [.free i] (rhs [])]⟩

abbrev ReadView := String × Nat × List UID × SourceOrigin
abbrev WriteView := Nat × String × Nat × List UID × List (List ReadView)

def view (raw : TLProgram) (ss : List TensorSpec) (ins : List InputBinding) :
    Option (List WriteView) :=
  (admitRawSource raw ss ins).toOption.map fun a =>
    a.statements.map fun st =>
      (st.original, (a.source.table.entry st.output.tensor).name,
       (a.source.table.entry st.output.tensor).declaration, st.output.indices,
       st.terms.map fun term => term.sourceReads.map fun r =>
         ((a.source.table.entry r.read.tensor).name,
          (a.source.table.entry r.read.tensor).declaration, r.indices, r.origin))

def ro (statement term factor declaration : Nat) : SourceOrigin :=
  { side := .read, statement := some statement, term := some term,
    factor := some factor, declaration := some declaration }

def expected : List WriteView := [
  (0, "Y", 5, [1], [
    [("B", 4, [1], ro 0 0 0 4), ("A", 3, [1, 2], ro 0 0 1 3),
     ("B", 4, [1], ro 0 0 2 4)],
    [("A", 3, [1, 2], ro 0 1 0 3)], []]),
  (1, "Diagonal", 7, [1, 1], [[]]),
  (2, "Y", 5, [1], [])]

def AsymmetricOrder := view asymmetric specs inputs == some expected
#guard AsymmetricOrder
#eval view asymmetric specs inputs

def ParsedMetadata : Bool :=
  match resolveSource parsed parsedSpecs parsedInputs with
  | .error _ => false
  | .ok s =>
    parsed.decls == [.axis ⟨"a", 0, .nat⟩ (some 2),
      .typedTensor .f64 "X" [⟨"a", 0, .real⟩],
      .typedTensor .f64 "Y" [⟨"a", 0, .real⟩]] &&
    s.resolved.decls == [.axis ⟨"a", 1, .nat⟩ (some 2),
      .typedTensor .f64 "X" [⟨"a", 1, .real⟩],
      .typedTensor .f64 "Y" [⟨"a", 1, .real⟩]]
#guard ParsedMetadata
#eval ParsedMetadata

def ParsedRead := view parsed parsedSpecs parsedInputs ==
  some [(0, "Y", 2, [1], [[("X", 1, [1], ro 0 0 0 1)]])]
#guard ParsedRead
#eval view parsed parsedSpecs parsedInputs

def EmptyAndDiagonal : Bool :=
  match view asymmetric specs inputs with
  | some [(_, _, _, _, [_, _, []]), (_, "Diagonal", 7, [1, 1], [[]]),
      (_, "Y", 5, [1], [])] => true
  | _ => false
#guard EmptyAndDiagonal
#eval EmptyAndDiagonal

def ZeroExtent : Bool :=
  match resolveSource asymmetric specs inputs with
  | .error _ => false
  | .ok s => admissionView s |>.any fun (axes, table, _) =>
    axes == [1, 2, 3] && table ==
      [(3, .input, [2, 3]), (4, .input, [2]), (5, .output, [2]),
       (6, .input, [0]), (7, .defined, [2, 2])]
#guard ZeroExtent
#eval ZeroExtent

def refusal : TLProgram := { asymmetric with stmts := [
  .assign "Missing" [.free i] { body := ⟨[]⟩, nonlin := .pointwise .relu, agg := .max }] }

def ErrorOrder : Bool :=
  match admitRawSource refusal specs inputs with
  | .error d =>
    d.stage == .statement && d.origin ==
      { side := .output, statement := some 0 } &&
    match d.cause with | .unsupported .nonSum => true | _ => false
  | .ok _ => false
#guard ErrorOrder
#eval ErrorOrder

def refusalSum : TLProgram := { refusal with stmts := refusal.stmts.map fun s =>
  match s with
  | .assign name slots rhs => .assign name slots { rhs with agg := .sum }
  | _ => s }

def refusalIdentity : TLProgram := { refusalSum with stmts := refusalSum.stmts.map fun s =>
  match s with
  | .assign name slots rhs => .assign name slots { rhs with nonlin := .identity }
  | _ => s }

def refusalAccepted : TLProgram :=
  { refusalIdentity with stmts := refusalIdentity.stmts.map fun s =>
    match s with
    | .assign _ slots rhs => .assign "Y" slots rhs
    | _ => s }

def diagnosticView (raw : TLProgram) : Option (SourceStage × SourceOrigin × String) :=
  match admitRawSource raw specs inputs with
  | .error d => some (d.stage, d.origin, reprStr d.cause)
  | .ok _ => none

#eval ("ErrorOrder.diagnostics", [diagnosticView refusal, diagnosticView refusalSum,
  diagnosticView refusalIdentity])
#guard (admitRawSource refusalAccepted specs inputs).toOption.isSome

def ExactErrorOrder : Bool :=
  [diagnosticView refusal, diagnosticView refusalSum, diagnosticView refusalIdentity] ==
    [some (.statement, { side := .output, statement := some 0 },
      reprStr (SourceCause.unsupported .nonSum)),
     some (.statement, { side := .output, statement := some 0 },
      reprStr (SourceCause.unsupported .nonIdentity)),
     some (.output, { side := .output, statement := some 0 },
      reprStr (SourceCause.undeclaredTensor "Missing"))]

#guard ExactErrorOrder
#eval ("ExactErrorOrder", ExactErrorOrder)
#eval ("ErrorOrder.accepted", view refusalAccepted specs inputs)

example (a : AdmittedSource) (h : admitRawSource asymmetric specs inputs = .ok a) :
    RawAdmissionFields asymmetric specs inputs a :=
  admitRawSource_fields _ _ _ _ h

example : (adaptSource snapshot).toOption.isSome = true := by rfl

example (source : AdaptedSource) (h : adaptSource snapshot = .ok source)
    (t : source.table.declarations.Tensor) :
    TensorEntryDeclaration source.context snapshot.resolved.decls snapshot.specs
      (source.table.entry t) :=
  adaptSource_entry_declaration _ _ h t

-- Clone parsed with disagreeing initial UIDs and kinds at declaration, output and read sites.
def inconsistentUIDs : TLProgram := ⟨[
  .axis ⟨"a", 17, .nat⟩ (some 2),
  .typedTensor .f64 "X" [⟨"a", 29, .real⟩],
  .typedTensor .f64 "Y" [⟨"a", 43, .nat⟩]], [
  .assign "Y" [.free ⟨"a", 81, .real⟩]
    (rhs [[.read "X" [.axis ⟨"a", 19, .nat⟩]]])]⟩

theorem inconsistentUIDs_start_zero : (assignUIDs inconsistentUIDs).run 0 = .ok
    { decls := (inconsistentUIDs.mapUID (fun u => { u with uid := 1 })).decls,
      stmts := (inconsistentUIDs.mapUID (fun u => { u with uid := 1 })).stmts } 2 := by
  cbv

theorem inconsistentUIDs_start_seven : (assignUIDs inconsistentUIDs).run 7 = .ok
    { decls := (inconsistentUIDs.mapUID (fun u => { u with uid := 7 })).decls,
      stmts := (inconsistentUIDs.mapUID (fun u => { u with uid := 7 })).stmts } 8 := by
  cbv

example (raw : TLProgram) (ss : List TensorSpec) (ins : List InputBinding)
    (s : SourceSnapshot) (h : resolveSource raw ss ins = .ok s) :
    ∃ memo : Std.HashMap String UID,
      (∀ a ∈ raw.axisSpecs, ∃ uid, memo[a.name]? = some uid) ∧
      s.resolved.decls = (raw.mapUID (sourceUIDRelabel memo)).decls ∧
      s.resolved.stmts = (raw.mapUID (sourceUIDRelabel memo)).stmts := by
  obtain ⟨memo, hc, hd, hs, _, _⟩ := resolveSource_mapUID_covered raw ss ins s h
  exact ⟨memo, fun a ha => hc a.name (raw.axisSpec_name_mem a ha), hd, hs⟩

#print axioms TLProgram.mem_axisNames_iff
#print axioms TLProgram.axisSpec_name_mem
#print axioms AxisSpec.mapUID_metadata
#print axioms forIn_insert_coverage
#print axioms assignUIDMemo_covers
#print axioms AxisSpec.mapUID_sourceUIDRelabel
#print axioms AxisSpec.mapUID_sourceUIDRelabel_same_name
#print axioms assignUIDs_eq_inline
#print axioms assignUIDs_mapUID_covered
#print axioms assignUIDs_mapUID
#print axioms resolveSource_mapUID_covered
#print axioms resolveSource_mapUID
#print axioms inconsistentUIDs_start_zero
#print axioms inconsistentUIDs_start_seven

#print axioms forIn_append_selection
#print axioms AxisDeclarations.pinned
#print axioms checkAxes_declarations
#print axioms sourceAxis_declared
#print axioms checkTable_declarations
#print axioms TableDeclarations.entry
#print axioms DeclaredAxisSlots.pinned
#print axioms adaptSource_declarations
#print axioms adaptSource_entry_declaration

def parsedAdmitted : AdmittedSource :=
  (admitRawSource parsed parsedSpecs parsedInputs).toOption.get (by cbv)

private theorem except_ok_of_some {ε α : Type} (x : Except ε α)
    (h : x.toOption.isSome = true) : x = .ok (x.toOption.get h) := by
  cases x with
  | error _ => cases h
  | ok _ => rfl

theorem parsed_success :
    admitRawSource parsed parsedSpecs parsedInputs = .ok parsedAdmitted := by
  exact except_ok_of_some _ _

theorem parsed_raw_fields : RawAdmissionFields parsed parsedSpecs parsedInputs parsedAdmitted :=
  admitRawSource_fields _ _ _ _ parsed_success

def asymmetricAdmitted : AdmittedSource :=
  (admitRawSource asymmetric specs inputs).toOption.get (by cbv)

theorem asymmetric_success :
    admitRawSource asymmetric specs inputs = .ok asymmetricAdmitted := by
  exact except_ok_of_some _ _

theorem asymmetric_raw_fields : RawAdmissionFields asymmetric specs inputs asymmetricAdmitted :=
  admitRawSource_fields _ _ _ _ asymmetric_success

def inconsistentAdmitted : AdmittedSource :=
  (admitRawSource inconsistentUIDs parsedSpecs parsedInputs).toOption.get (by cbv)

theorem inconsistent_success :
    admitRawSource inconsistentUIDs parsedSpecs parsedInputs = .ok inconsistentAdmitted := by
  exact except_ok_of_some _ _

theorem inconsistent_raw_fields :
    RawAdmissionFields inconsistentUIDs parsedSpecs parsedInputs inconsistentAdmitted :=
  admitRawSource_fields _ _ _ _ inconsistent_success

example (a : AdmittedSource) (h : admitRawSource asymmetric specs inputs = .ok a) :
    ∃ (snapshot : SourceSnapshot) (memo : Std.HashMap String UID),
      List.Forall₂ (fun (s, i) st => RawStatementFields asymmetric memo a.source i s st)
        asymmetric.stmts.zipIdx a.statements ∧
      ∀ t, RawTensorEntryFields asymmetric memo a.source.context specs
        snapshot.resolved.decls (a.source.table.entry t) := by
  obtain ⟨snapshot, memo, hc⟩ := admitRawSource_fields _ _ _ _ h
  exact ⟨snapshot, memo, hc.statement_fields, hc.tensor⟩

#print axioms admitRawSource_fields
#print axioms RawCorrespondence.tensor
#print axioms RawCorrespondence.pinned
#print axioms RawCorrespondence.statement
#print axioms RawCorrespondence.read
#print axioms RawCorrespondence.output
#print axioms RawAxisFields.metadata
#print axioms RawAxisFields.same_name
#print axioms RawDeclaredAxisSlots.slot
#print axioms RawTermFields.factor_count
#print axioms RawTermFields.factor
#print axioms RawStatementFields.term
#print axioms RawStatementFields.term_count
#print axioms RawCheckedFactorFields.slots
#print axioms RawStatementFields.output_slots
#print axioms RawReadSlots.slot
#print axioms RawOutputSlots.slot
#print axioms parsed_success
#print axioms parsed_raw_fields
#print axioms asymmetric_success
#print axioms asymmetric_raw_fields
#print axioms inconsistent_success
#print axioms inconsistent_raw_fields

namespace Structural

abbrev EntryView := Nat × Nat × String × TensorElementType × TensorRole × List (UID × Nat)

def entries (raw : TLProgram) (ss : List TensorSpec) (ins : List InputBinding) :
    Option (List EntryView) :=
  (admitRawSource raw ss ins).toOption.map fun a =>
    a.source.table.entries.zipIdx.map fun (e, tableIndex) =>
      (tableIndex, e.declaration, e.name, e.elementType, e.role,
        e.axes.map fun b => (b.uid, b.extent))

def pins (raw : TLProgram) (ss : List TensorSpec) (ins : List InputBinding) :
    Option (List (UID × Nat)) :=
  (admitRawSource raw ss ins).toOption.map fun a =>
    a.source.context.axes.map fun b => (b.uid, b.extent)

def spacer : AxisSpec := ⟨"spacer", 19, .nat⟩

def interleavedSnapshot : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls.take 4 ++ [.axis spacer (some 0)] ++ decls.drop 4 }
    specs := specs.map fun s => if s.declaration > 3 then
      { s with declaration := s.declaration + 1 } else s
    inputs := inputs.map fun b => if b.declaration > 3 then
      { b with declaration := b.declaration + 1 } else b }

def interleaved : TLProgram :=
  ⟨interleavedSnapshot.resolved.decls, interleavedSnapshot.resolved.stmts⟩

def equalExtent (reversed : Bool) : TLProgram :=
  { interleaved with
    decls := interleaved.decls.map fun d => match d with
      | .axis a _ => if a.name == "k" then .axis a (some 2) else d
      | .tensor "A" _ => .tensor "A" (if reversed then [k, i] else [i, k])
      | _ => d
    stmts := [.assign "Y" [.free i]
      (rhs [[.read "A" [.axis k, .axis i]], [.read "B" [.axis i]]]),
      .assign "Diagonal" [.free i, .free i] (rhs [[]]),
      .assign "Y" [.free i] (rhs [])] }

def equalSpecs : List TensorSpec :=
  interleavedSnapshot.specs.map fun s => if s.declaration == 3 then
    { s with shape := [2, 2] } else s

def equalInputs : List InputBinding :=
  interleavedSnapshot.inputs.map fun b => if b.declaration == 3 then
    { b with shape := [2, 2], values := [1, 2, 3, 4] } else b

def sameExtentIdentity : TLProgram :=
  { equalExtent false with
    decls := (equalExtent false).decls.map fun d => match d with
      | .tensor "A" _ => .tensor "A" [i, i]
      | _ => d }

def expectedEntries (aSlots : List (UID × Nat)) : List EntryView := [
  (0, 3, "A", .f32, .input, aSlots),
  (1, 5, "B", .f32, .input, [(1, 2)]),
  (2, 6, "Y", .f32, .output, [(1, 2)]),
  (3, 7, "Empty", .f32, .input, [(3, 0)]),
  (4, 8, "Diagonal", .f32, .defined, [(1, 2), (1, 2)])]

def DeclarationIdentity : Bool :=
  entries interleaved interleavedSnapshot.specs interleavedSnapshot.inputs ==
      some (expectedEntries [(1, 2), (2, 3)]) &&
    pins interleaved interleavedSnapshot.specs interleavedSnapshot.inputs ==
      some [(1, 2), (2, 3), (3, 0), (4, 0)] &&
    entries (equalExtent false) equalSpecs equalInputs ==
      some (expectedEntries [(1, 2), (2, 2)]) &&
    entries (equalExtent true) equalSpecs equalInputs ==
      some (expectedEntries [(2, 2), (1, 2)]) &&
    entries sameExtentIdentity equalSpecs equalInputs ==
      some (expectedEntries [(1, 2), (1, 2)]) &&
    view (equalExtent false) equalSpecs equalInputs ==
      view (equalExtent true) equalSpecs equalInputs &&
    view (equalExtent false) equalSpecs equalInputs == some [
      (0, "Y", 6, [1], [[("A", 3, [2, 1], ro 0 0 0 3)],
        [("B", 5, [1], ro 0 1 0 5)]]),
      (1, "Diagonal", 8, [1, 1], [[]]), (2, "Y", 6, [1], [])]

#guard DeclarationIdentity
#eval ("DeclarationIdentity", DeclarationIdentity)
#eval ("interleaved.entries", entries interleaved interleavedSnapshot.specs interleavedSnapshot.inputs)
#eval ("interleaved.pins", pins interleaved interleavedSnapshot.specs interleavedSnapshot.inputs)
#eval ("equalExtent.entries", [entries (equalExtent false) equalSpecs equalInputs,
  entries (equalExtent true) equalSpecs equalInputs,
  entries sameExtentIdentity equalSpecs equalInputs])
#eval ("equalExtent.reads", view (equalExtent false) equalSpecs equalInputs)

theorem interleaved_adapter (source : AdaptedSource)
    (h : adaptSource interleavedSnapshot = .ok source)
    (t : source.table.declarations.Tensor) :
    TensorEntryDeclaration source.context interleavedSnapshot.resolved.decls
      interleavedSnapshot.specs (source.table.entry t) :=
  adaptSource_entry_declaration _ _ h t

example : (adaptSource interleavedSnapshot).toOption.isSome = true := by cbv

def interleavedAdmitted : AdmittedSource :=
  (admitRawSource interleaved interleavedSnapshot.specs interleavedSnapshot.inputs).toOption.get
    (by cbv)

theorem interleaved_success :
    admitRawSource interleaved interleavedSnapshot.specs interleavedSnapshot.inputs =
      .ok interleavedAdmitted :=
  except_ok_of_some _ _

set_option maxHeartbeats 2000000 in
theorem interleaved_tensor :
    ∃ s memo, RawCorrespondence interleaved interleavedSnapshot.specs
      interleavedSnapshot.inputs interleavedAdmitted s memo ∧
      RawTensorEntryFields interleaved memo interleavedAdmitted.source.context
        interleavedSnapshot.specs s.resolved.decls
        ⟨5, "B", .f32, .input, [⟨1, 2⟩]⟩ := by
  obtain ⟨s, memo, hc⟩ := admitRawSource_fields _ _ _ _ interleaved_success
  have ht := hc.tensor ⟨1, by cbv⟩
  have he : (admitRawSource interleaved interleavedSnapshot.specs
      interleavedSnapshot.inputs).toOption.map
      (fun a => a.source.table.entries[1]?) =
      some (some ⟨5, "B", .f32, .input, [⟨1, 2⟩]⟩) := by cbv
  rw [interleaved_success] at he
  simp only [Except.toOption, Option.map, Option.some.injEq] at he
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp he
  have he' : interleavedAdmitted.source.table.entry ⟨1, by cbv⟩ =
      ⟨5, "B", .f32, .input, [⟨1, 2⟩]⟩ := by
    simpa only [TensorTable.entry, List.get_eq_getElem] using he
  rw [he'] at ht
  exact ⟨s, memo, hc, ht⟩

theorem interleaved_pinned :
    ∃ s memo, RawCorrespondence interleaved interleavedSnapshot.specs
      interleavedSnapshot.inputs interleavedAdmitted s memo ∧
      ∀ b ∈ interleavedAdmitted.source.context.axes,
        ∃ a, .axis a (some b.extent) ∈ interleaved.decls ∧ RawAxisFields interleaved memo a b.uid := by
  obtain ⟨s, memo, hc⟩ := admitRawSource_fields _ _ _ _ interleaved_success
  exact ⟨s, memo, hc, fun _ hb => hc.pinned hb⟩

def equalAdmitted (reversed : Bool) : AdmittedSource :=
  (admitRawSource (equalExtent reversed) equalSpecs equalInputs).toOption.get
    (by cases reversed <;> cbv)

theorem equal_success (reversed : Bool) :
    admitRawSource (equalExtent reversed) equalSpecs equalInputs = .ok (equalAdmitted reversed) :=
  except_ok_of_some _ _

set_option maxHeartbeats 2000000 in
theorem equal_tensor (reversed : Bool) :
    ∃ s memo, RawCorrespondence (equalExtent reversed) equalSpecs equalInputs
      (equalAdmitted reversed) s memo ∧
      RawTensorEntryFields (equalExtent reversed) memo (equalAdmitted reversed).source.context
        equalSpecs s.resolved.decls
        ⟨3, "A", .f32, .input,
          if reversed then [⟨2, 2⟩, ⟨1, 2⟩] else [⟨1, 2⟩, ⟨2, 2⟩]⟩ := by
  obtain ⟨s, memo, hc⟩ := admitRawSource_fields _ _ _ _ (equal_success reversed)
  refine ⟨s, memo, hc, ?_⟩
  have ht := hc.tensor ⟨0, by cases reversed <;> cbv⟩
  have he : (admitRawSource (equalExtent reversed) equalSpecs equalInputs).toOption.map
      (fun a => a.source.table.entries[0]?) =
      some (some ⟨3, "A", .f32, .input,
        if reversed then [⟨2, 2⟩, ⟨1, 2⟩] else [⟨1, 2⟩, ⟨2, 2⟩]⟩) := by
    cases reversed <;> cbv
  rw [equal_success] at he
  simp only [Except.toOption, Option.map, Option.some.injEq] at he
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp he
  have he' : (equalAdmitted reversed).source.table.entry ⟨0, by cases reversed <;> cbv⟩ =
      ⟨3, "A", .f32, .input,
        if reversed then [⟨2, 2⟩, ⟨1, 2⟩] else [⟨1, 2⟩, ⟨2, 2⟩]⟩ := by
    simpa only [TensorTable.entry, List.get_eq_getElem] using he
  rw [he'] at ht
  exact ht

def formAxis : AxisSpec := ⟨"a", 0, .nat⟩
def formUse : AxisSpec := ⟨"a", 0, .real⟩

def declarationForms : List (String × Decl × TensorElementType) := [
  ("tensor", .tensor "X" [formAxis], .f32),
  ("tensor.f32", .typedTensor .f32 "X" [formAxis], .f32),
  ("tensor.f64", .typedTensor .f64 "X" [formAxis], .f64),
  ("linear", .linear "X" [formAxis] false, .f32),
  ("linear.bias", .linear "X" [formAxis] true, .f32),
  ("linear.f32", .typedLinear .f32 "X" [formAxis] false, .f32),
  ("linear.f32.bias", .typedLinear .f32 "X" [formAxis] true, .f32),
  ("linear.f64", .typedLinear .f64 "X" [formAxis] false, .f64),
  ("linear.f64.bias", .typedLinear .f64 "X" [formAxis] true, .f64)]

def formRaw (f : String × Decl × TensorElementType) : TLProgram := ⟨[
  .axis formAxis (some 2), f.2.1, .typedTensor f.2.2 "Y" [formAxis]], [
  .assign "Y" [.free formUse] (rhs [
    [.read "X" [.axis formUse], .read "X" [.axis formUse]],
    [.read "X" [.axis formUse]]])]⟩

def formInputs : List InputBinding := [⟨1, [2], [1 / 3, 5 / 7]⟩]

def DeclarationForms : Bool :=
  declarationForms.all fun f =>
    (formRaw f).decls[1]? == some f.2.1 &&
    entries (formRaw f) parsedSpecs formInputs == some [
      (0, 1, "X", f.2.2, .input, [(1, 2)]), (1, 2, "Y", f.2.2, .output, [(1, 2)])] &&
    view (formRaw f) parsedSpecs formInputs == some [
      (0, "Y", 2, [1], [[("X", 1, [1], ro 0 0 0 1), ("X", 1, [1], ro 0 0 1 1)],
        [("X", 1, [1], ro 0 1 0 1)]])]

#guard DeclarationForms
#eval ("DeclarationForms", DeclarationForms)
#eval declarationForms.map fun f =>
  (f.1, entries (formRaw f) parsedSpecs formInputs, view (formRaw f) parsedSpecs formInputs)

def formAdmitted (j : Fin declarationForms.length) : AdmittedSource :=
  (admitRawSource (formRaw (declarationForms.get j)) parsedSpecs formInputs).toOption.get
    (by fin_cases j <;> cbv)

theorem form_success (j : Fin declarationForms.length) :
    admitRawSource (formRaw (declarationForms.get j)) parsedSpecs formInputs =
      .ok (formAdmitted j) :=
  except_ok_of_some _ _

set_option maxHeartbeats 2000000 in
theorem form_tensor (j : Fin declarationForms.length) :
    ∃ s memo, RawCorrespondence (formRaw (declarationForms.get j)) parsedSpecs formInputs
      (formAdmitted j) s memo ∧
      RawTensorEntryFields (formRaw (declarationForms.get j)) memo (formAdmitted j).source.context
        parsedSpecs s.resolved.decls
        ⟨1, "X", (declarationForms.get j).2.2, .input, [⟨1, 2⟩]⟩ := by
  obtain ⟨s, memo, hc⟩ := admitRawSource_fields _ _ _ _ (form_success j)
  refine ⟨s, memo, hc, ?_⟩
  have ht := hc.tensor ⟨0, by fin_cases j <;> cbv⟩
  have he : (admitRawSource (formRaw (declarationForms.get j)) parsedSpecs formInputs).toOption.map
      (fun a => a.source.table.entries[0]?) =
      some (some ⟨1, "X", (declarationForms.get j).2.2, .input, [⟨1, 2⟩]⟩) := by
    fin_cases j <;> cbv
  rw [form_success] at he
  simp only [Except.toOption, Option.map, Option.some.injEq] at he
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp he
  have he' : (formAdmitted j).source.table.entry ⟨0, by fin_cases j <;> cbv⟩ =
      ⟨1, "X", (declarationForms.get j).2.2, .input, [⟨1, 2⟩]⟩ := by
    simpa only [TensorTable.entry, List.get_eq_getElem] using he
  rw [he'] at ht
  exact ht

def indexed : TLProgram :=
  { asymmetric with
    stmts := asymmetric.stmts ++ [asymmetric.stmts[0],
      .assign "Diagonal" [.free i, .free i] (rhs [[.read "Diagonal" [.axis i, .axis i]]])] }

def indexedExpected : List WriteView :=
  expected ++ [
    (3, "Y", 5, [1], [
      [("B", 4, [1], ro 3 0 0 4), ("A", 3, [1, 2], ro 3 0 1 3),
        ("B", 4, [1], ro 3 0 2 4)],
      [("A", 3, [1, 2], ro 3 1 0 3)], []]),
    (4, "Diagonal", 7, [1, 1], [[("Diagonal", 7, [1, 1], ro 4 0 0 7)]])]

def IndexedOccurrences : Bool := view indexed specs inputs == some indexedExpected
#guard IndexedOccurrences
#eval ("IndexedOccurrences", IndexedOccurrences)
#eval ("indexed.reads", view indexed specs inputs)

def indexedAdmitted : AdmittedSource :=
  (admitRawSource indexed specs inputs).toOption.get (by cbv)

theorem indexed_success : admitRawSource indexed specs inputs = .ok indexedAdmitted :=
  except_ok_of_some _ _

theorem indexed_projections :
    ∃ s memo, RawCorrespondence indexed specs inputs indexedAdmitted s memo ∧
      ∀ (i : Fin indexedAdmitted.statements.length),
        ∃ ast, indexed.stmts[i.val]? = some ast ∧
          RawStatementFields indexed memo indexedAdmitted.source i.val ast
            (indexedAdmitted.statements.get i) ∧
          ∀ (j : Fin (indexedAdmitted.statements.get i).terms.length),
            ∃ name slots r t, ast = .assign name slots r ∧ r.body.terms[j.val]? = some t ∧
              RawTermFields indexed memo indexedAdmitted.source
                { side := .read, statement := some i.val, term := some j.val } t
                ((indexedAdmitted.statements.get i).terms.get j) ∧
              ∀ (k : Fin ((indexedAdmitted.statements.get i).terms.get j).sourceReads.length),
                ∃ f, t.factors[k.val]? = some f ∧
                  RawCheckedFactorFields indexed memo indexedAdmitted.source
                    { side := .read, statement := some i.val, term := some j.val,
                      factor := some k.val } f
                    (((indexedAdmitted.statements.get i).terms.get j).sourceReads.get k) := by
  obtain ⟨s, memo, hc⟩ := admitRawSource_fields _ _ _ _ indexed_success
  refine ⟨s, memo, hc, ?_⟩
  intro i
  obtain ⟨ast, ha, hs⟩ := hc.statement i
  refine ⟨ast, ha, hs, ?_⟩
  intro j
  obtain ⟨name, slots, r, t, he, hl, ht⟩ := hs.term j
  exact ⟨name, slots, r, t, he, hl, ht, fun k => ht.factor k⟩

theorem indexed_read_slots :
    ∃ s memo, RawCorrespondence indexed specs inputs indexedAdmitted s memo ∧
      ∀ (origin : SourceOrigin) (factor : Factor)
        (read : CheckedRead indexedAdmitted.source.context indexedAdmitted.source.table.declarations),
        RawCheckedFactorFields indexed memo indexedAdmitted.source origin factor read →
        ∃ name es, factor = .read name es ∧
          ∀ q : Fin read.read.slots.uids.length, ∃ a,
            es[q.val]? = some (.axis a) ∧
            RawAxisFields indexed memo a (read.read.slots.uids.get q) := by
  obtain ⟨s, memo, hc⟩ := admitRawSource_fields _ _ _ _ indexed_success
  refine ⟨s, memo, hc, ?_⟩
  intro origin factor read hr
  obtain ⟨name, es, he, _, _, hs, _⟩ := hc.read hr
  exact ⟨name, es, he, fun q => hs.slot q⟩

def sentinel : TLProgram :=
  { parsed with
    decls := [.axis ⟨"a", 0, .nat⟩ (some 2), .axis ⟨"b", 0, .nat⟩ (some 2),
      .typedTensor .f64 "X" [⟨"a", 0, .real⟩, ⟨"b", 0, .real⟩],
      .typedTensor .f64 "Y" [⟨"a", 0, .real⟩]]
    stmts := [.assign "Y" [.free ⟨"a", 0, .real⟩]
      (rhs [[.read "X" [.axis ⟨"b", 0, .real⟩, .axis ⟨"a", 0, .real⟩]]])] }

def sentinelSpecs : List TensorSpec := [⟨2, .input, [2, 2]⟩, ⟨3, .output, [2]⟩]
def sentinelInputs : List InputBinding := [⟨2, [2, 2], [3, 5, 7, 11]⟩]

def RawSentinelNames : Bool :=
  entries sentinel sentinelSpecs sentinelInputs == some [
    (0, 2, "X", .f64, .input, [(1, 2), (2, 2)]),
    (1, 3, "Y", .f64, .output, [(1, 2)])] &&
    view sentinel sentinelSpecs sentinelInputs ==
      some [(0, "Y", 3, [1], [[("X", 2, [2, 1], ro 0 0 0 2)]])]

#guard RawSentinelNames
#eval ("RawSentinelNames", RawSentinelNames)
#eval ("sentinel.entries", entries sentinel sentinelSpecs sentinelInputs)
#eval ("sentinel.resolved", (resolveSource sentinel sentinelSpecs sentinelInputs).toOption.map
  fun s => (s.resolved.decls, s.resolved.stmts))

def sentinelAdmitted : AdmittedSource :=
  (admitRawSource sentinel sentinelSpecs sentinelInputs).toOption.get (by cbv)

theorem sentinel_success :
    admitRawSource sentinel sentinelSpecs sentinelInputs = .ok sentinelAdmitted :=
  except_ok_of_some _ _

theorem sentinel_raw_fields : RawAdmissionFields sentinel sentinelSpecs sentinelInputs sentinelAdmitted :=
  admitRawSource_fields _ _ _ _ sentinel_success

def distinctZero : TLProgram :=
  (equalExtent false).mapUID (fun u => { u with uid := 0 })

def ResolverMetadataFidelity : Bool :=
  match resolveSource inconsistentUIDs parsedSpecs parsedInputs,
      resolveSource parsed parsedSpecs parsedInputs,
      resolveSource distinctZero equalSpecs equalInputs with
  | .ok mismatch, .ok baseline, .ok distinct =>
    mismatch.resolved.decls == [.axis ⟨"a", 1, .nat⟩ (some 2),
      .typedTensor .f64 "X" [⟨"a", 1, .real⟩], .typedTensor .f64 "Y" [⟨"a", 1, .nat⟩]] &&
    mismatch.resolved.stmts == [.assign "Y" [.free ⟨"a", 1, .real⟩]
      (rhs [[.read "X" [.axis ⟨"a", 1, .nat⟩]]])] &&
    baseline.resolved.decls == [.axis ⟨"a", 1, .nat⟩ (some 2),
      .typedTensor .f64 "X" [⟨"a", 1, .real⟩], .typedTensor .f64 "Y" [⟨"a", 1, .real⟩]] &&
    distinct.resolved.decls[3]? == some (.tensor "A" [⟨"i", 1, .nat⟩, ⟨"k", 2, .nat⟩]) &&
    view inconsistentUIDs parsedSpecs parsedInputs == view parsed parsedSpecs parsedInputs &&
    entries distinctZero equalSpecs equalInputs == entries (equalExtent false) equalSpecs equalInputs &&
    view distinctZero equalSpecs equalInputs == view (equalExtent false) equalSpecs equalInputs
  | _, _, _ => false

#guard ResolverMetadataFidelity
#eval ("ResolverMetadataFidelity", ResolverMetadataFidelity)
#eval ("distinctZero.entries", entries distinctZero equalSpecs equalInputs)
#eval ("distinctZero.pins", pins distinctZero equalSpecs equalInputs)
#eval ("mismatch.resolved", (resolveSource inconsistentUIDs parsedSpecs parsedInputs).toOption.map
  fun s => (s.resolved.decls, s.resolved.stmts))
#eval ("parsed.resolved", (resolveSource parsed parsedSpecs parsedInputs).toOption.map
  fun s => (s.resolved.decls, s.resolved.stmts))

#print axioms interleaved_adapter
#print axioms interleaved_tensor
#print axioms interleaved_pinned
#print axioms equal_tensor
#print axioms form_tensor
#print axioms indexed_projections
#print axioms indexed_read_slots
#print axioms sentinel_raw_fields

end Structural

namespace Endpoint

def outputTarget (z : Bool) : TLProgram :=
  { Structural.interleaved with
    decls := Structural.interleaved.decls ++ [.tensor "Z" [i]]
    stmts := Structural.interleaved.stmts.take 1 |>.map fun s => match s with
      | .assign name slots rhs => .assign (if z then "Z" else name) slots rhs
      | _ => s }

def outputSpecs : List TensorSpec :=
  Structural.interleavedSnapshot.specs ++ [⟨9, .output, [2]⟩]

def outputTargetView (z : Bool) :=
  (admitRawSource (outputTarget z) outputSpecs
    Structural.interleavedSnapshot.inputs).toOption.map fun a =>
    a.statements.map fun st =>
      let entry := a.source.table.entry st.output.tensor
      (st.original, st.output.tensor.val, entry.declaration, entry.name, entry.role,
        entry.axes.map (fun ax => (ax.uid, ax.extent)), st.output.origin)

def OutputTargetNames : Bool :=
  outputTargetView false == some [
    (0, 2, 6, "Y", .output, [(1, 2)],
      { side := .output, statement := some 0, declaration := some 6 })] &&
  outputTargetView true == some [
    (0, 5, 9, "Z", .output, [(1, 2)],
      { side := .output, statement := some 0, declaration := some 9 })] &&
  (outputTarget false).decls[6]? == some (.tensor "Y" [i]) &&
  (outputTarget true).decls[9]? == some (.tensor "Z" [i])

#guard OutputTargetNames
#eval ("OutputTargetNames", OutputTargetNames)
#eval ("OutputTargetNames.targets", [outputTargetView false, outputTargetView true])

end Endpoint

private def DonorReadConnection (raw : TLProgram) (specs : List TensorSpec)
    (admitted : AdmittedSource) : Prop :=
    ∀ (i : Fin admitted.statements.length) (j : Fin (admitted.statements.get i).terms.length)
    (k : Fin ((admitted.statements.get i).terms.get j).sourceReads.length)
    (v : UIDVal admitted.source.context),
    let term := (admitted.statements.get i).terms.get j
    let read := term.sourceReads.get k
    ∃ snapshot memo ast product name es,
      CertifiedRawTerm raw specs admitted snapshot memo i j ast product ∧
      product.factors[k.val]? = some (.read name es) ∧
      RawCheckedFactorFields raw memo admitted.source
        { side := .read, statement := some i.val, term := some j.val, factor := some k.val }
        (.read name es) read ∧
      RawTensorEntryFields raw memo admitted.source.context specs snapshot.resolved.decls
        (admitted.source.table.entry read.read.tensor) ∧
      (admitted.source.table.entry read.read.tensor).name = name ∧
      RawReadSlots raw memo es read.read.slots.uids ∧
      (term.reads k).slots.project
        (uidCoordEquiv term.partition.context (indexPullback term.partition.embedding.map v)) =
        read.read.slots.project (uidCoordEquiv admitted.source.context v) ∧
      ∀ q : Fin (admitted.source.table.declarations.signature read.read.tensor).axes.length,
        ∃ a, ∃ u : admitted.source.context.Key, es[q.val]? = some (.axis a) ∧
          RawAxisFields raw memo a u.val ∧ memo[a.name]? = some u.val ∧
          Coord.raw ((term.reads k).slots.project
            (uidCoordEquiv term.partition.context
              (indexPullback term.partition.embedding.map v))) q = (v u).val ∧
          Coord.raw (read.read.slots.project
            (uidCoordEquiv admitted.source.context v)) q = (v u).val

private theorem donor_read_connection
    {raw : TLProgram} {specs : List TensorSpec} {inputs : List InputBinding}
    {admitted : AdmittedSource}
    (ha : admitRawSource raw specs inputs = .ok admitted) :
    DonorReadConnection raw specs admitted := by
  intro i j k v
  obtain ⟨snapshot, memo, hc⟩ := admitRawSource_certified ha
  obtain ⟨ast, hs⟩ := hc.statements i
  obtain ⟨product, ht⟩ := hs.term j
  obtain ⟨name, es, hf, hr, hd, hn, hslots, hp, hcoords⟩ :=
    ht.read_projection hc.correspondence k v
  exact ⟨snapshot, memo, ast, product, name, es, ht, hf, hr, hd, hn, hslots, hp, hcoords⟩

theorem parsed_read_connection : DonorReadConnection parsed parsedSpecs parsedAdmitted :=
  donor_read_connection parsed_success
theorem asymmetric_read_connection : DonorReadConnection asymmetric specs asymmetricAdmitted :=
  donor_read_connection asymmetric_success
theorem inconsistent_read_connection :
    DonorReadConnection inconsistentUIDs parsedSpecs inconsistentAdmitted :=
  donor_read_connection inconsistent_success

private def DonorBodyConnection (raw : TLProgram) (specs : List TensorSpec)
    (admitted : AdmittedSource) (K : Type) [Semiring K]
    (r : Registry (fun _ : Unit => K)) : Prop :=
    ∀ (ρ : Store (fun _ => K) admitted.source.table.declarations)
    (i : Fin admitted.statements.length)
    (x : Coord (admitted.statements.get i).output.context.axes)
    (p : Coord (admitted.source.table.declarations.signature
      (admitted.statements.get i).output.tensor).axes),
    let statement := admitted.statements.get i
    ∃ snapshot memo ast,
      CertifiedRawStatement raw specs admitted snapshot memo i ast ∧
      (∃ name slots rhs, ast = .assign name slots rhs ∧
        rhs.body.terms.length = statement.terms.length) ∧
      interpret semiringOps ρ (statement.body (r := r) id) x =
        some ((statement.terms.map fun term =>
          ∑ w : UIDVal term.globalContext,
            if (term.partitionCoordEquiv w).1 = x then term.globalProduct ρ w else 0).sum) ∧
      footprint (statement.body (K := K) (r := r) id) x =
        statement.terms.flatMap (fun term => term.readFootprint x) ∧
      statement.globalFiber ρ p =
        ∑ y : Coord statement.output.context.axes,
          if statement.destination y = p then
            (statement.terms.map (fun term => term.value ρ y)).sum else 0

private theorem donor_body_connection
    {raw : TLProgram} {specs : List TensorSpec} {inputs : List InputBinding}
    {admitted : AdmittedSource} {K : Type} [Semiring K]
    {r : Registry (fun _ : Unit => K)}
    (ha : admitRawSource raw specs inputs = .ok admitted) :
    DonorBodyConnection raw specs admitted K r := by
  intro ρ i x p
  obtain ⟨snapshot, memo, hc⟩ := admitRawSource_certified ha
  obtain ⟨ast, hs⟩ := hc.statements i
  exact ⟨snapshot, memo, ast, hs.semantics ρ x p⟩

theorem parsed_body_connection {K : Type} [Semiring K]
    {r : Registry (fun _ : Unit => K)} :
    DonorBodyConnection parsed parsedSpecs parsedAdmitted K r :=
  donor_body_connection (r := r) parsed_success
theorem asymmetric_body_connection {K : Type} [Semiring K]
    {r : Registry (fun _ : Unit => K)} :
    DonorBodyConnection asymmetric specs asymmetricAdmitted K r :=
  donor_body_connection (r := r) asymmetric_success
theorem inconsistent_body_connection {K : Type} [Semiring K]
    {r : Registry (fun _ : Unit => K)} :
    DonorBodyConnection inconsistentUIDs parsedSpecs inconsistentAdmitted K r :=
  donor_body_connection (r := r) inconsistent_success

private def DonorOutputConnection (raw : TLProgram) (specs : List TensorSpec)
    (admitted : AdmittedSource) : Prop :=
    ∀ (i : Fin admitted.statements.length) (v : UIDVal admitted.source.context),
    let statement := admitted.statements.get i
    ∃ snapshot memo ast,
      CertifiedRawStatement raw specs admitted snapshot memo i ast ∧
      ∃ name slots rhs, ast = .assign name slots rhs ∧
      ∀ q : Fin (admitted.source.table.declarations.signature statement.output.tensor).axes.length,
        ∃ a, ∃ u : admitted.source.context.Key, slots[q.val]? = some (.free a) ∧
          RawAxisFields raw memo a u.val ∧ memo[a.name]? = some u.val ∧
          Coord.raw (statement.destination
            (uidCoordEquiv statement.output.context
              (indexPullback statement.output.embedding.map v))) q = (v u).val ∧
          Coord.raw (statement.output.sourceSlots.project
            (uidCoordEquiv admitted.source.context v)) q = (v u).val

private theorem donor_output_connection
    {raw : TLProgram} {specs : List TensorSpec} {inputs : List InputBinding}
    {admitted : AdmittedSource}
    (ha : admitRawSource raw specs inputs = .ok admitted) :
    DonorOutputConnection raw specs admitted := by
  intro i v
  obtain ⟨snapshot, memo, hc⟩ := admitRawSource_certified ha
  obtain ⟨ast, hs⟩ := hc.statements i
  obtain ⟨name, slots, rhs, he, _, _, _, _, _, _, _, hcoords⟩ := hs.output_projection v
  exact ⟨snapshot, memo, ast, hs, name, slots, rhs, he, hcoords⟩

theorem parsed_output_connection : DonorOutputConnection parsed parsedSpecs parsedAdmitted :=
  donor_output_connection parsed_success
theorem asymmetric_output_connection : DonorOutputConnection asymmetric specs asymmetricAdmitted :=
  donor_output_connection asymmetric_success
theorem inconsistent_output_connection :
    DonorOutputConnection inconsistentUIDs parsedSpecs inconsistentAdmitted :=
  donor_output_connection inconsistent_success

namespace Endpoint

def parsedRun : ActualValidatedResult parsedAdmitted :=
  ⟨sourceInput parsedAdmitted, Program.Executor.run (elaborateSource parsedAdmitted)
    RationalReference.ops (sourceSchedule parsedAdmitted) (sourceInput parsedAdmitted)⟩

def asymmetricRun : ActualValidatedResult asymmetricAdmitted :=
  ⟨sourceInput asymmetricAdmitted, Program.Executor.run (elaborateSource asymmetricAdmitted)
    RationalReference.ops (sourceSchedule asymmetricAdmitted) (sourceInput asymmetricAdmitted)⟩

def executionView (admitted : AdmittedSource) (result : ActualValidatedResult admitted) :=
  (SourceProgramFixtures.outcomeKind admitted result.result.outcome,
    SourceProgramFixtures.tensorObservations admitted result.result.outcome,
    result.result.events.length)

#eval ("CertifiedParsedSemantics.execution", executionView parsedAdmitted parsedRun)
#eval ("CertifiedAsymmetricSemantics.execution", executionView asymmetricAdmitted asymmetricRun)

def CertifiedParsedSemantics : Bool :=
  SourceProgramFixtures.outcomeKind parsedAdmitted parsedRun.result.outcome == .complete

def CertifiedAsymmetricSemantics : Bool :=
  SourceProgramFixtures.outcomeKind asymmetricAdmitted asymmetricRun.result.outcome == .complete

#guard CertifiedParsedSemantics
#guard CertifiedAsymmetricSemantics
#eval ("CertifiedParsedSemantics", CertifiedParsedSemantics)
#eval ("CertifiedAsymmetricSemantics", CertifiedAsymmetricSemantics)

def CertifiedExecution (raw : TLProgram) (specs : List TensorSpec)
    (inputs : List InputBinding) (admitted : AdmittedSource)
    (result : ActualValidatedResult admitted) : Prop :=
  runSource admitted = .ok result ∧
  DonorReadConnection raw specs admitted ∧
  DonorOutputConnection raw specs admitted ∧
  DonorBodyConnection raw specs admitted ℚ RationalReference.registry ∧
  ∃ c complete, ∃ (hr : result.result.outcome = .complete c complete), ∃ snapshot memo,
      CertifiedRawSource raw specs inputs admitted snapshot memo ∧
      admitted.GlobalModels (r := RationalReference.registry) result.input
        ((elaborateSource admitted).finalStore c complete) ∧
      (∀ t : (elaborateSource admitted).Defined,
        RawTensorEntryFields raw memo admitted.source.context specs snapshot.resolved.decls
          (admitted.source.table.entry t.val) ∧
        ∀ p, (elaborateSource admitted).finalStore c complete ⟨t.val, p⟩ =
          admitted.globalFiber ((elaborateSource admitted).finalStore c complete) t.val p) ∧
      (∀ ρ, admitted.GlobalModels (r := RationalReference.registry) result.input ρ →
        ρ = (elaborateSource admitted).finalStore c complete) ∧
      (∀ (ρ : Store (fun _ : Unit => ℚ) admitted.source.table.declarations)
        (t : (elaborateSource admitted).Defined) p,
        (elaborateSource admitted).collect semiringOps ρ (admitted.total_admEnv ρ) t p =
          admitted.globalFiber ρ t.val p) ∧
      (∀ ρ, (elaborateSource admitted).Models semiringOps result.input ρ ↔
        admitted.GlobalModels (r := RationalReference.registry) result.input ρ) ∧
      (∀ (t : {t // (elaborateSource admitted).output t = true}) p,
        (elaborateSource admitted).denotation RationalReference.ops result.input
          ((elaborateSource admitted).successful_admInput RationalReference.ops result.input c
            (Program.Executor.result_success _ _ result.input result.result c complete hr)) t p =
          admitted.globalFiber ((elaborateSource admitted).finalStore c complete) t.val p)

private theorem certified_execution
    {raw : TLProgram} {specs : List TensorSpec} {inputs : List InputBinding}
    {admitted : AdmittedSource} {result : ActualValidatedResult admitted}
    (ha : admitRawSource raw specs inputs = .ok admitted)
    (hrun : runSource admitted = .ok result)
    (hcomplete : ∃ c complete, result.result.outcome = .complete c complete) :
    CertifiedExecution raw specs inputs admitted result := by
  refine ⟨hrun, donor_read_connection ha, donor_output_connection ha,
    donor_body_connection ha, ?_⟩
  obtain ⟨c, complete, hr⟩ := hcomplete
  obtain ⟨snapshot, memo, hc, hm, he, hu⟩ := admitRawSource_reached ha result c complete hr
  refine ⟨c, complete, hr, snapshot, memo, hc, hm, he, hu, ?_, ?_, ?_⟩
  · intro ρ t p
    exact (hc.collect (r := RationalReference.registry) ρ t p).2.2
  · intro ρ
    exact (hc.models (r := RationalReference.registry) result.input ρ).2.2
  · intro t p
    obtain ⟨_, _, _, _, hd⟩ :=
      admitRawSource_reached_denotation ha result c complete hr t p
    exact hd

theorem parsed_certified_execution (c complete)
    (hr : parsedRun.result.outcome = .complete c complete) :
    CertifiedExecution parsed parsedSpecs parsedInputs parsedAdmitted parsedRun :=
  certified_execution parsed_success (runSource_eq _) ⟨c, complete, hr⟩

theorem asymmetric_certified_execution (c complete)
    (hr : asymmetricRun.result.outcome = .complete c complete) :
    CertifiedExecution asymmetric specs inputs asymmetricAdmitted asymmetricRun :=
  certified_execution asymmetric_success (runSource_eq _) ⟨c, complete, hr⟩

#check parsed_certified_execution
#check asymmetric_certified_execution
#print axioms parsed_certified_execution
#print axioms asymmetric_certified_execution

end Endpoint

#print axioms Slots.uids_length
#print axioms Slots.project_lookup
#print axioms RawReadSlots.coordinate
#print axioms RawOutputSlots.coordinate
#print axioms RawCorrespondence.certifiedStatement
#print axioms CertifiedRawStatement.term
#print axioms CertifiedRawTerm.read_projection
#print axioms CertifiedRawStatement.output_projection
#print axioms CertifiedRawTerm.semantics
#print axioms CertifiedRawStatement.semantics
#print axioms RawCorrespondence.certifiedSource
#print axioms admitRawSource_certified
#print axioms CertifiedRawSource.collect
#print axioms CertifiedRawSource.models
#print axioms admitRawSource_reached
#print axioms admitRawSource_reached_denotation
#print axioms parsed_read_connection
#print axioms asymmetric_read_connection
#print axioms inconsistent_read_connection
#print axioms parsed_body_connection
#print axioms asymmetric_body_connection
#print axioms inconsistent_body_connection
#print axioms parsed_output_connection
#print axioms asymmetric_output_connection
#print axioms inconsistent_output_connection

end SourceRawCorrespondenceTest

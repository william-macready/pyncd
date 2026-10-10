import LeanNCD.Semantics.Source.Context
import LeanNCD.DSL.Pipeline.Structural
import LeanNCD.Semantics.RationalReference

namespace LeanNCD.Semantics.Source

inductive SourceSide
  | program | declaration | input | output | read
  deriving DecidableEq, Repr

structure SourceOrigin where
  side : SourceSide := .program
  declaration : Option Nat := none
  statement : Option Nat := none
  term : Option Nat := none
  factor : Option Nat := none
  slot : Option Nat := none
  deriving DecidableEq, Repr

inductive SourceStage
  | resolution | declarations | signatures | inputs | statement | output | read | support
  deriving DecidableEq, Repr

inductive TensorRole
  | input | defined | output
  deriving DecidableEq, Repr

inductive UnsupportedSource
  | iteration | predicate | complex
  | scatter | recurMorphism | marked | scanSlot | affine
  | nonSum | nonIdentity | iverson | unary
  deriving DecidableEq, Repr

inductive SourceCause
  | resolution (error : CompileError)
  | unsupported (form : UnsupportedSource)
  | duplicateAxis (uid : UID)
  | duplicateTensor (name : String)
  | duplicateSpec (declaration : Nat)
  | duplicateInput (declaration : Nat)
  | missingDomain (uid : UID)
  | unbound (uid : UID)
  | axisKind (uid : UID) (actual : AxisKind)
  | undeclaredTensor (name : String)
  | missingSpec (declaration : Nat)
  | unexpectedSpec (declaration : Nat)
  | missingInput (declaration : Nat)
  | unexpectedInput (declaration : Nat)
  | role (expected actual : TensorRole)
  | shape (expected actual : List Nat)
  | length (expected actual : Nat)
  | domain (uid : UID) (expected actual : Nat)
  | rank (expected actual : Nat)
  | context (error : Diagnostic)
  deriving Repr

structure SourceDiagnostic where
  stage : SourceStage
  cause : SourceCause
  origin : SourceOrigin
  deriving Repr

def sourceError (stage : SourceStage) (origin : SourceOrigin) (cause : SourceCause) :
    SourceDiagnostic := ⟨stage, cause, origin⟩

structure TensorSpec where
  declaration : Nat
  role : TensorRole
  shape : List Nat
  deriving Repr

structure InputBinding where
  declaration : Nat
  shape : List Nat
  values : List ℚ
  deriving Repr

structure SourceSnapshot where
  resolved : ResolvedProgram
  specs : List TensorSpec
  inputs : List InputBinding

private def tensorName : Decl → Option String
  | .tensor name _ | .typedTensor _ name _ | .predicate name _
    | .linear name _ _ | .typedLinear _ name _ _ => some name
  | .axis .. | .iter .. => none

private def resolutionOrigin (raw : TLProgram) : CompileError → SourceOrigin
  | .duplicateTensorDecl name =>
    { side := .declaration, declaration :=
      ((raw.decls.zipIdx.filter (fun (d, _) => tensorName d == some name))[1]?).map Prod.snd }
  | .unsupportedElementType name spelling =>
    { side := .declaration, declaration :=
      (raw.decls.zipIdx.find? (fun (d, _) =>
        d.name == name && d.elementType?.any (fun ty => ty.spelling == spelling))).map Prod.snd }
  | _ => {}

/-- Raw name binding is performed exactly once, by the production resolution seam. -/
def resolveSource (raw : TLProgram) (specs : List TensorSpec) (inputs : List InputBinding) :
    Except SourceDiagnostic SourceSnapshot :=
  match (do
    let labeled ← assignUIDs raw
    resolveDecls labeled : FreshM ResolvedProgram).run 0 with
  | .ok resolved _ => .ok ⟨resolved, specs, inputs⟩
  | .error e _ => .error (sourceError .resolution (resolutionOrigin raw e) (.resolution e))

structure TensorEntry where
  declaration : Nat
  name : String
  elementType : TensorElementType
  role : TensorRole
  axes : Shape
  deriving Repr

theorem resolveSource_mapUID_covered (raw : TLProgram) (specs : List TensorSpec)
    (inputs : List InputBinding) (snapshot : SourceSnapshot)
    (h : resolveSource raw specs inputs = .ok snapshot) :
    ∃ memo : Std.HashMap String UID,
      (∀ name ∈ raw.axisNames, ∃ uid, memo[name]? = some uid) ∧
      snapshot.resolved.decls = (TLProgram.mapUID (sourceUIDRelabel memo) raw).decls ∧
      snapshot.resolved.stmts = (TLProgram.mapUID (sourceUIDRelabel memo) raw).stmts ∧
      snapshot.specs = specs ∧ snapshot.inputs = inputs := by
  cases ha : assignUIDs raw 0 with
  | error e n =>
    simp [resolveSource, EStateM.bind, EStateM.run, bind, pure, ha] at h
  | ok lp n =>
    obtain ⟨memo, hc, hd, hs⟩ := assignUIDs_mapUID_covered raw 0 n lp ha
    cases hb : buildDeclEnv lp.decls with
    | error e =>
      simp [resolveSource, resolveDecls, EStateM.bind, EStateM.run, bind, pure, ha, hb,
        throw, MonadExceptOf.throw, throwThe, EStateM.throw] at h
    | ok env =>
      simp [resolveSource, resolveDecls, EStateM.bind, EStateM.run, bind, pure, ha, hb,
        EStateM.pure] at h
      subst snapshot
      exact ⟨memo, hc, hd, hs, rfl, rfl⟩

theorem resolveSource_mapUID (raw : TLProgram) (specs : List TensorSpec)
    (inputs : List InputBinding) (snapshot : SourceSnapshot)
    (h : resolveSource raw specs inputs = .ok snapshot) :
    ∃ memo : Std.HashMap String UID,
      snapshot.resolved.decls = (TLProgram.mapUID (sourceUIDRelabel memo) raw).decls ∧
      snapshot.resolved.stmts = (TLProgram.mapUID (sourceUIDRelabel memo) raw).stmts ∧
      snapshot.specs = specs ∧ snapshot.inputs = inputs := by
  obtain ⟨memo, _, hd, hs, hp, hi⟩ :=
    resolveSource_mapUID_covered raw specs inputs snapshot h
  exact ⟨memo, hd, hs, hp, hi⟩

structure TensorTable where
  entries : List TensorEntry

def TensorTable.declarations (table : TensorTable) : Declarations Unit where
  Tensor := Fin table.entries.length
  uid := Fin.val
  unique := Fin.val_injective
  signature := fun t => ⟨(), (table.entries.get t).axes⟩

def TensorTable.find (table : TensorTable) (name : String) :
    Option table.declarations.Tensor :=
  (List.finRange table.entries.length).find? (fun i => (table.entries.get i).name == name)

def TensorTable.entry (table : TensorTable) (t : table.declarations.Tensor) : TensorEntry :=
  table.entries.get t

theorem TensorTable.find_name (table : TensorTable) (name : String)
    (t : table.declarations.Tensor) (h : table.find name = some t) :
    (table.entry t).name = name := by
  unfold TensorTable.find at h
  have found := List.find?_some h
  simpa [TensorTable.entry] using found

structure InputBuffer (axes : Shape) where
  values : List ℚ
  length : values.length = (canonicalLayout axes).count

def InputBuffer.value (buffer : InputBuffer axes) (p : Coord axes) : ℚ :=
  buffer.values.get ⟨((canonicalLayout axes).enumerate.symm p).val, by
    rw [buffer.length]
    exact ((canonicalLayout axes).enumerate.symm p).isLt⟩

structure CheckedInputs (table : TensorTable) where
  buffers : (t : table.declarations.Tensor) →
    (table.entry t).role = .input → InputBuffer (table.entry t).axes

structure AdaptedSource where
  context : Context
  table : TensorTable
  inputs : CheckedInputs table
  statements : List (Nat × Stmt)

private def axisOrigin (i : Nat) : SourceOrigin :=
  { side := .declaration, declaration := some i }

/-- An ordered scan may omit an input only when its structural classifier permits it. -/
inductive OrderedSelection {α β : Type} (R : α → Option β → Prop) :
    List α → List β → Prop
  | nil : OrderedSelection R [] []
  | skip {a xs ys} : R a none → OrderedSelection R xs ys →
      OrderedSelection R (a :: xs) ys
  | emit {a b xs ys} : R a (some b) → OrderedSelection R xs ys →
      OrderedSelection R (a :: xs) (b :: ys)

theorem forIn_append_selection {α β ε : Type} (R : α → Option β → Prop)
    (body : α → List β → Except ε (ForInStep (List β)))
    (step : ∀ a acc result, body a acc = .ok result →
      ∃ b, R a b ∧ result = .yield (acc ++ b.toList))
    (xs : List α) (init out : List β) (h : forIn xs init body = .ok out) :
    ∃ ys, OrderedSelection R xs ys ∧ out = init ++ ys := by
  induction xs generalizing init with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨[], .nil, by simpa using h.symm⟩
  | cons a xs ih =>
    rw [List.forIn_cons] at h
    cases hb : body a init with
    | error e => simp [hb, bind, Except.bind] at h
    | ok result =>
      obtain ⟨b, hr, rfl⟩ := step a init result hb
      simp only [hb, bind, Except.bind] at h
      obtain ⟨ys, hy, ho⟩ := ih _ h
      cases b with
      | none => exact ⟨ys, .skip hr hy, by simpa using ho⟩
      | some b => exact ⟨b :: ys, .emit hr hy, by simpa [List.append_assoc] using ho⟩

def PinnedAxisDeclaration (d : Decl) (axis : Option Axis) : Prop :=
  match d with
  | .axis a size => ∃ n, size = some n ∧ axis = some ⟨a.uid, n⟩
  | .iter .. => False
  | .tensor .. | .typedTensor .. | .predicate .. | .linear .. | .typedLinear .. =>
    axis = none

def AxisDeclarations (decls : List Decl) (axes : Shape) : Prop :=
  OrderedSelection PinnedAxisDeclaration decls axes

theorem OrderedSelection.map_inputs {α β γ : Type} {R : γ → Option β → Prop}
    (f : α → γ) {xs ys} (h : OrderedSelection (fun a => R (f a)) xs ys) :
    OrderedSelection R (xs.map f) ys := by
  induction h with
  | nil => exact .nil
  | skip hr _ ih => exact .skip hr ih
  | emit hr _ ih => exact .emit hr ih

theorem OrderedSelection.member {α β : Type} {R : α → Option β → Prop}
    {xs ys} (h : OrderedSelection R xs ys) {b} (hb : b ∈ ys) :
    ∃ a ∈ xs, R a (some b) := by
  induction h with
  | nil => simp at hb
  | skip hr h ih =>
    obtain ⟨a, ha, hr⟩ := ih hb
    exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩
  | emit hr h ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨a, ha, hr⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem AxisDeclarations.pinned {decls : List Decl} {axes : Shape}
    (h : AxisDeclarations decls axes) {b : Axis} (hb : b ∈ axes) :
    ∃ a, .axis a (some b.extent) ∈ decls ∧ a.uid = b.uid := by
  obtain ⟨d, hd, hr⟩ := h.member hb
  cases d <;> simp only [PinnedAxisDeclaration, reduceCtorEq] at hr
  all_goals try { contradiction }
  obtain ⟨n, rfl, he⟩ := hr
  cases he
  exact ⟨_, hd, rfl⟩

private def checkAxes (decls : List Decl) : Except SourceDiagnostic Context := do
  let mut axes : Shape := []
  for (i, d) in decls.zipIdx |>.map (fun (d, i) => (i, d)) do
    let origin := axisOrigin i
    match d with
    | .axis a size =>
      if a.uid ∈ axes.map Axis.uid then
        throw (sourceError .declarations origin (.duplicateAxis a.uid))
      match size with
      | none => throw (sourceError .declarations origin (.missingDomain a.uid))
      | some n => axes := axes ++ [⟨a.uid, n⟩]
    | .iter _ _ => throw (sourceError .declarations origin (.unsupported .iteration))
    | .tensor .. | .typedTensor .. | .predicate .. | .linear .. | .typedLinear .. => pure ()
  (checkContext axes).mapError (fun e => sourceError .declarations {} (.context e))
    |>.map Subtype.val

theorem checkAxes_declarations (decls : List Decl) (c : Context)
    (h : checkAxes decls = .ok c) : AxisDeclarations decls c.axes := by
  unfold checkAxes at h
  simp only [List.forIn_map] at h
  generalize hl : forIn (m := Except SourceDiagnostic) decls.zipIdx ([] : Shape) _ =
    result at h
  cases result with
  | error e => simp [bind, Except.bind] at h
  | ok axes =>
    obtain ⟨ys, hy, he⟩ := forIn_append_selection
      (fun p : Decl × Nat => PinnedAxisDeclaration p.1) _ (by
        rintro ⟨d, i⟩ acc result hs
        cases d <;>
          simp only [bind, pure, Except.bind, Except.pure, throw,
            MonadExceptOf.throw, throwThe] at hs
        all_goals try {
          exact ⟨none, rfl, by simpa using (Except.ok.inj hs).symm⟩ }
        · split at hs
          · simp at hs
          · split at hs
            · simp at hs
            · simp only [Except.ok.injEq] at hs
              exact ⟨some _, ⟨_, rfl, rfl⟩, hs.symm⟩
        · simp at hs) _ [] axes hl
    simp only [List.nil_append] at he
    subst axes
    have hd : AxisDeclarations decls ys := by
      simpa [AxisDeclarations] using hy.map_inputs Prod.fst
    simp only [bind, Except.bind] at h
    unfold checkContext at h
    split at h
    · simp [Except.mapError, Except.map] at h
      subst c
      exact hd
    · simp [Except.mapError, Except.map] at h

def sourceAxis (c : Context) (stage : SourceStage) (origin : SourceOrigin)
    (a : AxisSpec) : Except SourceDiagnostic Axis := do
  match c.axes.find? (fun b => b.uid == a.uid) with
  | none => throw (sourceError stage origin (.unbound a.uid))
  | some b => pure b

theorem sourceAxis_declared (c : Context) (stage : SourceStage) (origin : SourceOrigin)
    (a : AxisSpec) (b : Axis) (h : sourceAxis c stage origin a = .ok b) :
    b.uid = a.uid ∧ b ∈ c.axes := by
  unfold sourceAxis at h
  cases hf : c.axes.find? (fun b => b.uid == a.uid) with
  | none => simp [hf, throw, throwThe, MonadExceptOf.throw] at h
  | some found =>
    simp [hf, pure, Except.pure] at h
    subst b
    exact ⟨by simpa using List.find?_some hf, List.mem_of_find?_eq_some hf⟩

/-- Supported declaration spelling, independent of the executable classifier.
    Untyped declarations default to f32; linear bias does not affect classification. -/
def SupportedTensorDeclaration (d : Decl) (name : String) (ty : TensorElementType)
    (axes : List AxisSpec) : Prop :=
  match d with
  | .tensor n slots | .linear n slots _ => name = n ∧ ty = .f32 ∧ axes = slots
  | .typedTensor t n slots | .typedLinear t n slots _ =>
    (t = .f32 ∨ t = .f64) ∧ name = n ∧ ty = t ∧ axes = slots
  | .axis .. | .iter .. | .predicate .. => False

def DeclaredAxisSlots (c : Context) (slots : List AxisSpec) (axes : Shape) : Prop :=
  List.Forall₂ (fun a b => b.uid = a.uid ∧ b ∈ c.axes) slots axes

def TensorDeclarationSelection (c : Context) (specs : List TensorSpec)
    (pair : Decl × Nat) (entry : Option TensorEntry) : Prop :=
  match entry with
  | none => ∃ a size, pair.1 = .axis a size
  | some e =>
    e.declaration = pair.2 ∧
    ∃ slots, SupportedTensorDeclaration pair.1 e.name e.elementType slots ∧
      DeclaredAxisSlots c slots e.axes ∧
      ∃ spec, specs.find? (fun s => s.declaration == pair.2) = some spec ∧
        e.role = spec.role ∧ e.axes.map Axis.extent = spec.shape

def TableDeclarations (c : Context) (decls : List Decl) (specs : List TensorSpec)
    (table : TensorTable) : Prop :=
  OrderedSelection (TensorDeclarationSelection c specs) decls.zipIdx table.entries

def TensorEntryDeclaration (c : Context) (decls : List Decl) (specs : List TensorSpec)
    (entry : TensorEntry) : Prop :=
  ∃ d, decls[entry.declaration]? = some d ∧
    ∃ slots, SupportedTensorDeclaration d entry.name entry.elementType slots ∧
      DeclaredAxisSlots c slots entry.axes ∧
      ∃ spec, specs.find? (fun s => s.declaration == entry.declaration) = some spec ∧
        spec.declaration = entry.declaration ∧ entry.role = spec.role ∧
        entry.axes.map Axis.extent = spec.shape

theorem TableDeclarations.entry {c : Context} {decls : List Decl}
    {specs : List TensorSpec} {table : TensorTable}
    (h : TableDeclarations c decls specs table) (t : table.declarations.Tensor) :
    TensorEntryDeclaration c decls specs (table.entry t) := by
  obtain ⟨⟨d, i⟩, hd, hi, slots, hc, ha, spec, hf, hr, hs⟩ :=
    h.member (List.get_mem table.entries t)
  change (table.entry t).declaration = i at hi
  have hlookup := List.mk_mem_zipIdx_iff_getElem?.mp hd
  refine ⟨d, ?_, slots, hc, ha, spec, ?_, ?_, hr, hs⟩
  · simpa [hi] using hlookup
  · simpa [hi] using hf
  · have found := List.find?_some hf
    simpa [hi] using found

theorem DeclaredAxisSlots.pinned {c : Context} {decls : List Decl}
    {slots : List AxisSpec} {axes : Shape}
    (hc : AxisDeclarations decls c.axes) (h : DeclaredAxisSlots c slots axes) :
    List.Forall₂ (fun slot axis => axis.uid = slot.uid ∧ axis ∈ c.axes ∧
      ∃ a, .axis a (some axis.extent) ∈ decls ∧ a.uid = axis.uid) slots axes :=
  h.imp (fun _ _ hab => ⟨hab.1, hab.2, hc.pinned hab.2⟩)

theorem OrderedSelection.all_emitted {α β : Type} {R : α → β → Prop}
    {xs ys} (h : OrderedSelection (fun a b => ∃ value, b = some value ∧ R a value) xs ys) :
    List.Forall₂ R xs ys := by
  induction h with
  | nil => exact .nil
  | skip hr _ _ => obtain ⟨_, h, _⟩ := hr; cases h
  | emit hr _ ih =>
    obtain ⟨_, h, hr⟩ := hr
    cases h
    exact .cons hr ih

private def tensorDecl (origin : SourceOrigin) :
    Decl → Except SourceDiagnostic (Option (String × TensorElementType × List AxisSpec))
  | .axis .. => .ok none
  | .iter .. => .error (sourceError .declarations origin (.unsupported .iteration))
  | .tensor name axes | .linear name axes _ => .ok (some (name, .f32, axes))
  | .typedTensor ty name axes | .typedLinear ty name axes _ =>
    match ty with
    | .f32 | .f64 => .ok (some (name, ty, axes))
    | .complex64 | .complex128 =>
      .error (sourceError .declarations origin (.unsupported .complex))
  | .predicate .. => .error (sourceError .declarations origin (.unsupported .predicate))

private theorem tensorDecl_classifies (origin : SourceOrigin) (d : Decl) (result)
    (h : tensorDecl origin d = .ok result) :
    match result with
    | none => ∃ a size, d = .axis a size
    | some (name, ty, axes) => SupportedTensorDeclaration d name ty axes := by
  cases d with
  | axis a size =>
    simp [tensorDecl] at h
    subst result
    exact ⟨a, size, rfl⟩
  | tensor name slots =>
    simp [tensorDecl] at h
    subst result
    exact ⟨rfl, rfl, rfl⟩
  | linear name slots bias =>
    simp [tensorDecl] at h
    subst result
    exact ⟨rfl, rfl, rfl⟩
  | typedTensor ty name slots =>
    cases ty <;> simp [tensorDecl] at h <;> subst result <;>
      simp [SupportedTensorDeclaration]
  | typedLinear ty name slots bias =>
    cases ty <;> simp [tensorDecl] at h <;> subst result <;>
      simp [SupportedTensorDeclaration]
  | iter a n => simp [tensorDecl] at h
  | predicate name slots => simp [tensorDecl] at h

private def checkTable (c : Context) (decls : List Decl) (specs : List TensorSpec) :
    Except SourceDiagnostic TensorTable := do
  let mut seen : List Nat := []
  for spec in specs do
    let origin := axisOrigin spec.declaration
    if spec.declaration ∈ seen then
      throw (sourceError .signatures origin (.duplicateSpec spec.declaration))
    seen := seen ++ [spec.declaration]
  let mut entries : List TensorEntry := []
  for (d, i) in decls.zipIdx do
    let origin := axisOrigin i
    match ← tensorDecl origin d with
    | none => pure ()
    | some (name, ty, axes) =>
      if entries.any (fun t => t.name == name) then
        throw (sourceError .declarations origin (.duplicateTensor name))
      let mut shape : Shape := []
      for (a, j) in axes.zipIdx do
        shape := shape ++ [← sourceAxis c .declarations { origin with slot := some j } a]
      let spec ← match specs.find? (fun s => s.declaration == i) with
        | none => throw (sourceError .signatures origin (.missingSpec i))
        | some s => pure s
      if shape.map Axis.extent != spec.shape then
        throw (sourceError .signatures origin (.shape (shape.map Axis.extent) spec.shape))
      entries := entries ++ [⟨i, name, ty, spec.role, shape⟩]
  for spec in specs do
    unless entries.any (fun t => t.declaration == spec.declaration) do
      throw (sourceError .signatures (axisOrigin spec.declaration)
        (.unexpectedSpec spec.declaration))
  pure ⟨entries⟩

theorem checkTable_declarations (c : Context) (decls : List Decl)
    (specs : List TensorSpec) (table : TensorTable)
    (h : checkTable c decls specs = .ok table) :
    TableDeclarations c decls specs table := by
  unfold checkTable at h
  dsimp only at h
  generalize hspecs : forIn (m := Except SourceDiagnostic) specs ([] : List Nat) _ =
    seen at h
  cases seen with
  | error e => simp [bind, Except.bind] at h
  | ok seen =>
    simp only [bind, Except.bind] at h
    generalize hl : forIn (m := Except SourceDiagnostic) decls.zipIdx
      ([] : List TensorEntry) _ = result at h
    cases result with
    | error e => simp [bind, Except.bind] at h
    | ok entries =>
      obtain ⟨ys, hy, he⟩ := forIn_append_selection (TensorDeclarationSelection c specs) _
        (by
          rintro ⟨d, i⟩ acc result hs
          dsimp only at hs
          simp only [bind, pure, Except.bind, Except.pure] at hs
          generalize ht : tensorDecl (axisOrigin i) d = classified at hs
          cases classified with
          | error e => simp at hs
          | ok classified =>
            cases classified with
            | none =>
              exact ⟨none, tensorDecl_classifies _ _ _ ht,
                by simpa using (Except.ok.inj hs).symm⟩
            | some classified =>
              rcases classified with ⟨name, ty, slots⟩
              have hc := tensorDecl_classifies _ _ _ ht
              dsimp only at hs hc
              split at hs
              · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hs
              · generalize hshape : forIn (m := Except SourceDiagnostic) slots.zipIdx
                  ([] : Shape) _ = shapeResult at hs
                cases shapeResult with
                | error e => simp at hs
                | ok shape =>
                  obtain ⟨axes, ha, he⟩ := forIn_append_selection
                    (fun p : AxisSpec × Nat => fun b =>
                      ∃ axis, b = some axis ∧ axis.uid = p.1.uid ∧ axis ∈ c.axes) _
                    (by
                      rintro ⟨a, j⟩ acc result hs
                      dsimp only at hs
                      generalize hx : sourceAxis c .declarations _ a = value at hs
                      cases value with
                      | error e => simp at hs
                      | ok axis =>
                        exact ⟨some axis, ⟨axis, rfl, sourceAxis_declared _ _ _ _ _ hx⟩,
                          (Except.ok.inj hs).symm⟩) _ [] shape hshape
                  simp only [List.nil_append] at he
                  subst shape
                  have hslots : DeclaredAxisSlots c slots axes := by
                    have hs' : List.Forall₂ (fun a b => b.uid = a.uid ∧ b ∈ c.axes)
                        (slots.zipIdx.map Prod.fst) axes :=
                      List.forall₂_map_left_iff.mpr ha.all_emitted
                    simpa [DeclaredAxisSlots] using hs'
                  dsimp only at hs
                  cases hf : specs.find? (fun s => s.declaration == i) with
                  | none =>
                    simp [hf, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hs
                  | some spec =>
                    simp only [hf, pure, Except.pure, bind, Except.bind] at hs
                    split at hs
                    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hs
                    · rename_i hshape
                      simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hs
                      exact ⟨some ⟨i, name, ty, spec.role, axes⟩,
                        ⟨rfl, slots, hc, hslots, spec, hf, rfl, by simpa using hshape⟩,
                        hs.symm⟩) _ [] entries hl
      simp only [List.nil_append] at he
      subst entries
      simp only [bind, Except.bind] at h
      generalize hu : forIn (m := Except SourceDiagnostic) specs PUnit.unit _ =
        checked at h
      cases checked with
      | error e => simp at h
      | ok unit =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst table
        exact hy

private def inputBuffer (entry : TensorEntry) (bindings : List InputBinding) :
    Except SourceDiagnostic (InputBuffer entry.axes) := do
  let origin : SourceOrigin := { side := .input, declaration := some entry.declaration }
  let binding ← match bindings.find? (fun b => b.declaration == entry.declaration) with
    | none => throw (sourceError .inputs origin (.missingInput entry.declaration))
    | some b => pure b
  let expected := entry.axes.map Axis.extent
  if expected != binding.shape then
    throw (sourceError .inputs origin (.shape expected binding.shape))
  if hl : binding.values.length = (canonicalLayout entry.axes).count then
    pure ⟨binding.values, hl⟩
  else
    throw (sourceError .inputs origin
      (.length (canonicalLayout entry.axes).count binding.values.length))

private def inputBuffers (bindings : List InputBinding) :
    (entries : List TensorEntry) →
    Except SourceDiagnostic ((t : Fin entries.length) →
      (entries.get t).role = .input → InputBuffer (entries.get t).axes)
  | [] => .ok (fun t => nomatch t)
  | entry :: entries => do
    let head ← if h : entry.role = .input then do
      let buffer ← inputBuffer entry bindings
      pure (fun (_ : entry.role = .input) => buffer)
    else
      pure (fun (hi : entry.role = .input) => False.elim (h hi))
    let rest ← inputBuffers bindings entries
    pure (Fin.cases head rest)

private def checkInputs (table : TensorTable) (bindings : List InputBinding) :
    Except SourceDiagnostic (CheckedInputs table) := do
  let mut seen : List Nat := []
  for binding in bindings do
    let origin : SourceOrigin := { side := .input, declaration := some binding.declaration }
    if binding.declaration ∈ seen then
      throw (sourceError .inputs origin (.duplicateInput binding.declaration))
    seen := seen ++ [binding.declaration]
    match table.entries.find? (fun t => t.declaration == binding.declaration) with
    | none => throw (sourceError .inputs origin (.unexpectedInput binding.declaration))
    | some t =>
      if t.role != .input then throw (sourceError .inputs origin (.role .input t.role))
  let buffers ← inputBuffers bindings table.entries
  pure ⟨buffers⟩

/-- Neither the cached environment nor external-name classification determines semantic roles. -/
def adaptSource (snapshot : SourceSnapshot) : Except SourceDiagnostic AdaptedSource := do
  let context ← checkAxes snapshot.resolved.decls
  let table ← checkTable context snapshot.resolved.decls snapshot.specs
  let inputs ← checkInputs table snapshot.inputs
  pure ⟨context, table, inputs,
    snapshot.resolved.stmts.zipIdx |>.map (fun (s, i) => (i, s))⟩

theorem adaptSource_statements (snapshot : SourceSnapshot) (source : AdaptedSource)
    (h : adaptSource snapshot = .ok source) :
    source.statements = snapshot.resolved.stmts.zipIdx.map (fun (s, i) => (i, s)) := by
  unfold adaptSource at h
  simp only [bind, pure, Except.bind, Except.pure] at h
  repeat' split at h
  all_goals simp only [Except.ok.injEq, reduceCtorEq] at h
  all_goals subst source
  all_goals rfl

/-- A certificate of the actual adapter success, not a field on arbitrary adapted values. -/
def AdaptSourceDeclarations (snapshot : SourceSnapshot) (source : AdaptedSource) : Prop :=
  AxisDeclarations snapshot.resolved.decls source.context.axes ∧
    TableDeclarations source.context snapshot.resolved.decls snapshot.specs source.table

theorem adaptSource_declarations (snapshot : SourceSnapshot) (source : AdaptedSource)
    (h : adaptSource snapshot = .ok source) : AdaptSourceDeclarations snapshot source := by
  unfold adaptSource at h
  cases hc : checkAxes snapshot.resolved.decls with
  | error e => simp [hc, bind, Except.bind] at h
  | ok c =>
    cases ht : checkTable c snapshot.resolved.decls snapshot.specs with
    | error e => simp [hc, ht, bind, Except.bind] at h
    | ok table =>
      cases hi : checkInputs table snapshot.inputs with
      | error e => simp [hc, ht, hi, bind, Except.bind] at h
      | ok inputs =>
        simp [hc, ht, hi, bind, Except.bind, pure, Except.pure] at h
        subst source
        exact ⟨checkAxes_declarations _ _ hc, checkTable_declarations _ _ _ _ ht⟩

theorem adaptSource_entry_declaration (snapshot : SourceSnapshot) (source : AdaptedSource)
    (h : adaptSource snapshot = .ok source) (t : source.table.declarations.Tensor) :
    TensorEntryDeclaration source.context snapshot.resolved.decls snapshot.specs
      (source.table.entry t) :=
  (adaptSource_declarations snapshot source h).2.entry t

end LeanNCD.Semantics.Source

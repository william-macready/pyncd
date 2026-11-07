import IndexedComponentCompositionScope

namespace IndexedComponentComposition

open LeanNCD.Semantics
open IndexedComponentTransport

variable {σA σB : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB)
variable (wire : Boundary A B)

def program : Program K (declarations A B) R where
  tensors := by
    classical
    change Fintype (σA.Tensor ⊕ B.program.Defined)
    letI : Fintype B.program.Defined :=
      Subtype.fintype (fun t => B.program.input t = false)
    exact inferInstance
  input
    | .inl t => A.program.input t
    | .inr _ => false
  output
    | .inl _ => false
    | .inr t => B.program.output t.val
  output_defined := by
    intro t h
    cases t with
    | inl t => contradiction
    | inr t => rfl
  statements := fun t =>
    match t with
    | ⟨.inl t, h⟩ => A.program.statements ⟨t, h⟩
    | ⟨.inr t, _⟩ => B.program.statements t
  valuations := fun t s =>
    match t with
    | ⟨.inl t, h⟩ => A.program.valuations ⟨t, h⟩ s
    | ⟨.inr t, _⟩ => B.program.valuations t s
  guard := fun t s v =>
    match t with
    | ⟨.inl t, h⟩ => A.program.guard ⟨t, h⟩ s v
    | ⟨.inr t, _⟩ => B.program.guard t s v
  destination := fun t s v =>
    match t with
    | ⟨.inl t, h⟩ =>
        ((upstream A B).domain t).coord (A.program.destination ⟨t, h⟩ s v)
    | ⟨.inr t, _⟩ =>
        B.program.destination t s v
  body := fun t s =>
    match t with
    | ⟨.inl t, h⟩ =>
        transport (upstream A B) id (A.program.body ⟨t, h⟩ s)
    | ⟨.inr t, _⟩ =>
        transport (downstream A B wire) id (B.program.body t s)

def upstreamDefined (t : A.program.Defined) : (program A B wire).Defined :=
  ⟨.inl t.val, t.property⟩

def downstreamDefined (t : B.program.Defined) : (program A B wire).Defined :=
  ⟨.inr t, rfl⟩

theorem upstream_body (t : A.program.Defined) (s : Fin (A.program.statements t)) :
    (program A B wire).body (upstreamDefined A B wire t) s =
      transport (upstream A B) id (A.program.body t s) := rfl

theorem downstream_body (t : B.program.Defined) (s : Fin (B.program.statements t)) :
    (program A B wire).body (downstreamDefined A B wire t) s =
      transport (downstream A B wire) id (B.program.body t s) := rfl

theorem upstream_destination (t : A.program.Defined)
    (s : Fin (A.program.statements t))
    (v : {v : Fin (A.program.valuations t s) // A.program.guard t s v = true}) :
    (program A B wire).destination (upstreamDefined A B wire t) s v =
      ((upstream A B).domain t.val).coord (A.program.destination t s v) := rfl

theorem downstream_destination (t : B.program.Defined)
    (s : Fin (B.program.statements t))
    (v : {v : Fin (B.program.valuations t s) // B.program.guard t s v = true}) :
    (program A B wire).destination (downstreamDefined A B wire t) s v =
      B.program.destination t s v := rfl

theorem upstream_footprint (t : A.program.Defined)
    (s : Fin (A.program.statements t))
    (v : {v : Fin (A.program.valuations t s) // A.program.guard t s v = true}) :
    footprint ((program A B wire).body (upstreamDefined A B wire t) s) v =
      (footprint (A.program.body t s) v).map (upstream A B).address := by
  rw [upstream_body]
  exact footprint_transport (upstream A B) (A.program.body t s) id v

theorem downstream_footprint (t : B.program.Defined)
    (s : Fin (B.program.statements t))
    (v : {v : Fin (B.program.valuations t s) // B.program.guard t s v = true}) :
    footprint ((program A B wire).body (downstreamDefined A B wire t) s) v =
      (footprint (B.program.body t s) v).map (downstream A B wire).address := by
  rw [downstream_body]
  exact footprint_transport (downstream A B wire) (B.program.body t s) id v

def definedEquiv : (program A B wire).Defined ≃
    A.program.Defined ⊕ B.program.Defined where
  toFun
    | ⟨.inl t, h⟩ => .inl ⟨t, h⟩
    | ⟨.inr t, _⟩ => .inr t
  invFun
    | .inl t => upstreamDefined A B wire t
    | .inr t => downstreamDefined A B wire t
  left_inv := by
    rintro ⟨t, h⟩
    cases t <;> apply Subtype.ext <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

def occurrenceEquiv : IndexedOpenComposition.SourceOccurrence (program A B wire) ≃
    IndexedOpenComposition.SourceOccurrence A.program ⊕
    IndexedOpenComposition.SourceOccurrence B.program where
  toFun
    | ⟨⟨.inl t, h⟩, o⟩ => .inl ⟨⟨t, h⟩, o⟩
    | ⟨⟨.inr t, _⟩, o⟩ => .inr ⟨t, o⟩
  invFun
    | .inl ⟨t, o⟩ => ⟨upstreamDefined A B wire t, o⟩
    | .inr ⟨t, o⟩ => ⟨downstreamDefined A B wire t, o⟩
  left_inv := by
    rintro ⟨⟨t, h⟩, o⟩
    cases t <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

def inputPort (p : Port σA) : Port (declarations A B) where
  tensor := .inl p.tensor
  sort := p.sort
  axes := p.axes
  sort_eq := p.sort_eq
  axes_eq := p.axes_eq

def outputPort (p : Port σB) (hp : B.program.output p.tensor = true) :
    Port (declarations A B) where
  tensor := .inr ⟨p.tensor, B.program.output_defined p.tensor hp⟩
  sort := p.sort
  axes := p.axes
  sort_eq := p.sort_eq
  axes_eq := p.axes_eq

def inputPorts : List (Port (declarations A B)) :=
  A.inputs.map (inputPort A B)

def outputPorts : List (Port (declarations A B)) :=
  B.outputs.attach.map fun p =>
    outputPort A B p.val
      ((B.outputs_exact p.val.tensor).mp
        (List.mem_map.mpr ⟨p.val, p.property, rfl⟩))

theorem inputPorts_exact (t : (declarations A B).Tensor) :
    t ∈ (inputPorts A B).map Port.tensor ↔ (program A B wire).input t = true := by
  cases t with
  | inl t =>
    change (Sum.inl t ∈ (inputPorts A B).map Port.tensor) ↔
      A.program.input t = true
    simp only [inputPorts, List.map_map]
    constructor
    · intro h
      rcases List.mem_map.mp h with ⟨p, hp, he⟩
      change Sum.inl p.tensor = Sum.inl t at he
      exact (A.inputs_exact t).mp
        (List.mem_map.mpr ⟨p, hp, Sum.inl.inj he⟩)
    · intro h
      rcases List.mem_map.mp ((A.inputs_exact t).mpr h) with ⟨p, hp, he⟩
      exact List.mem_map.mpr ⟨p, hp, congrArg Sum.inl he⟩
  | inr t =>
    simp [inputPorts, inputPort, program]

theorem inputPorts_nodup : ((inputPorts A B).map Port.tensor).Nodup := by
  simpa [inputPorts, inputPort, List.map_map] using
    A.inputs_nodup.map Sum.inl_injective

theorem outputPorts_exact (t : (declarations A B).Tensor) :
    t ∈ (outputPorts A B).map Port.tensor ↔ (program A B wire).output t = true := by
  cases t with
  | inl t =>
    simp [outputPorts, outputPort, program]
  | inr t =>
    constructor
    · intro h
      simp only [outputPorts, List.map_map] at h
      rcases List.mem_map.mp h with ⟨p, hp, he⟩
      have hv : B.program.output p.val.tensor = true :=
        (B.outputs_exact p.val.tensor).mp
          (List.mem_map.mpr ⟨p.val, p.property, rfl⟩)
      have ht : p.val.tensor = t.val :=
        congrArg (fun x : (declarations A B).Tensor =>
          match x with | .inl _ => t.val | .inr x => x.val) he
      simpa [program, ← ht] using hv
    · intro h
      have ht : t.val ∈ B.outputs.map Port.tensor :=
        (B.outputs_exact t.val).mpr (by simpa [program] using h)
      rcases List.mem_map.mp ht with ⟨p, hp, he⟩
      simp only [outputPorts, List.map_map]
      apply List.mem_map.mpr
      refine ⟨⟨p, hp⟩, List.mem_attach _ _, ?_⟩
      · apply congrArg Sum.inr
        apply Subtype.ext
        exact he

theorem outputPorts_nodup : ((outputPorts A B).map Port.tensor).Nodup := by
  have hn : B.outputs.Nodup := List.Nodup.of_map Port.tensor B.outputs_nodup
  have ha : B.outputs.attach.Nodup := List.nodup_attach.mpr hn
  simp only [outputPorts, List.map_map]
  apply (List.nodup_map_iff_inj_on ha).mpr
  intro p hp q hq he
  apply Subtype.ext
  apply (List.nodup_map_iff_inj_on hn).mp B.outputs_nodup
    p.val p.property q.val q.property
  exact congrArg Subtype.val (Sum.inr.inj he)

end IndexedComponentComposition

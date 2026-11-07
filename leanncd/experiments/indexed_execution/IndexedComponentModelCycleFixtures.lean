import IndexedComponentCompositionScope
import IndexedComponentCompositionPortFixtures
import LeanNCD.Semantics.Completeness

namespace IndexedComponentModelCycleFixtures

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor
open IndexedOpenComposition
open IndexedComponentComposition
open IndexedComponentTransport

@[reducible] def declarations : Declarations Unit :=
  ⟨Fin 2, fun t => t.val, fun _ _ h => Fin.ext h, fun _ => ⟨(), []⟩⟩

def privateTensor : declarations.Tensor := 0
def boundaryTensor : declarations.Tensor := 1

def scalarPolicy : ReadPolicy ℚ [] :=
  ⟨fun _ => .at (), by intro p; cases p; rfl⟩

def readScalar (Γ : Type) (t : declarations.Tensor) :
    Expr RationalReference.Carrier declarations RationalReference.registry Γ (.scalar ()) :=
  .read t ⟨scalarPolicy, fun _ => Fin.elim0, fun _ => .at (), by intro _; rfl⟩

def squareBody (Γ : Type) :
    Expr RationalReference.Carrier declarations RationalReference.registry Γ (.scalar ()) :=
  .prim (r := RationalReference.registry) RationalReference.Primitive.square
    (fun _ => readScalar Γ privateTensor)

def reciprocalBody (Γ : Type) :
    Expr RationalReference.Carrier declarations RationalReference.registry Γ (.scalar ()) :=
  .prim (r := RationalReference.registry) RationalReference.Primitive.reciprocal
    (fun _ => readScalar Γ privateTensor)

def totalBody (Γ : Type) :
    Expr RationalReference.Carrier declarations RationalReference.registry Γ (.scalar ()) :=
  .binary .add (readScalar Γ privateTensor) (.lit 1)

@[reducible] def upstreamProgram (hidden : Bool) :
    Program RationalReference.Carrier declarations RationalReference.registry where
  tensors := inferInstance
  input := fun _ => false
  output := fun t => t == boundaryTensor
  output_defined := by intro _ _; rfl
  statements := fun _ => 1
  valuations := fun _ _ => 1
  guard := fun _ _ _ => true
  destination := fun _ _ _ => ()
  body := fun t _ => if t.val == privateTensor then squareBody _
    else if hidden then .lit 0 else readScalar _ privateTensor

def upstreamSchedule (hidden : Bool) : Schedule (upstreamProgram hidden) where
  tensors := [privateTensor, boundaryTensor]
  tensors_nodup := by decide
  tensors_complete := by intro t; fin_cases t <;> simp [privateTensor, boundaryTensor]
  keys := [
    .occurrence ⟨privateTensor, rfl⟩ ⟨0, ⟨0, rfl⟩⟩,
    .publication ⟨privateTensor, rfl⟩ (),
    .occurrence ⟨boundaryTensor, rfl⟩ ⟨0, ⟨0, rfl⟩⟩,
    .publication ⟨boundaryTensor, rfl⟩ ()]
  keys_nodup := by
    simp [List.nodup_cons, privateTensor, boundaryTensor]
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨t, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      fin_cases t <;> fin_cases s <;> fin_cases v <;> simp [privateTensor, boundaryTensor]
    | publication t p =>
      rcases t with ⟨t, ht⟩
      cases p
      fin_cases t <;> simp [privateTensor, boundaryTensor]

def upstreamContract : Contract declarations :=
  ⟨[privateTensor, boundaryTensor], fun _ => false,
    [(⟨privateTensor, ()⟩, [101]), (⟨boundaryTensor, ()⟩, [201])],
    [⟨privateTensor, ()⟩], [⟨boundaryTensor, ()⟩]⟩

def upstreamFragment (hidden : Bool) : Fragment declarations :=
  ⟨[⟨10, 101, ⟨privateTensor, ()⟩, [⟨privateTensor, ()⟩], squareBody Unit⟩,
    ⟨20, 201, ⟨boundaryTensor, ()⟩,
      if hidden then [] else [⟨privateTensor, ()⟩],
      if hidden then .lit 0 else readScalar Unit privateTensor⟩]⟩

def upstreamGraph (hidden : Bool) : Closed declarations :=
  ⟨upstreamContract, canonicalSteps upstreamContract (upstreamFragment hidden)⟩

def upstreamEquiv (hidden : Bool) :
    SourceOccurrence (upstreamProgram hidden) ≃
      Fin (upstreamFragment hidden).writers.length where
  toFun := fun o => o.1.val
  invFun := fun i => ⟨⟨i, rfl⟩, ⟨0, ⟨0, rfl⟩⟩⟩
  left_inv := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    have hv' : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases t <;> fin_cases s <;> rfl
  right_inv := fun _ => rfl

def upstreamMatch (hidden : Bool) : SourceContractMatch
    (upstreamProgram hidden) (upstreamSchedule hidden)
    upstreamContract (upstreamFragment hidden) (upstreamGraph hidden) where
  close_ok := by cases hidden <;> rfl
  input_roles := rfl
  tensor_order := rfl
  outputs_exact := by
    rintro ⟨t, p⟩
    cases p
    fin_cases t <;> simp [upstreamContract, boundaryTensor, privateTensor]
  sourceToWriter := upstreamEquiv hidden
  writer_destination := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    fin_cases t <;> fin_cases s <;> fin_cases v <;> rfl
  writer_reads := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    cases hidden <;> fin_cases t <;> fin_cases s <;> fin_cases v <;> rfl
  eval_agrees := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩ store
    cases hidden <;> fin_cases t <;> fin_cases s <;> fin_cases v <;> rfl
  priority := by cases hidden <;> rfl

def upstreamComponent (hidden : Bool) : MatchedComponent declarations where
  program := upstreamProgram hidden
  schedule := upstreamSchedule hidden
  contract := upstreamContract
  fragment := upstreamFragment hidden
  graph := upstreamGraph hidden
  matched := upstreamMatch hidden
  inputs := []
  outputs := [⟨boundaryTensor, (), [], rfl, rfl⟩]
  inputs_nodup := by simp
  outputs_nodup := by simp
  inputs_exact := by intro t; fin_cases t <;> simp
  outputs_exact := by intro t; fin_cases t <;> simp [boundaryTensor]

@[reducible] def downstreamProgram (strict : Bool) :
    Program RationalReference.Carrier declarations RationalReference.registry where
  tensors := inferInstance
  input := fun t => t == privateTensor
  output := fun t => t == boundaryTensor
  output_defined := by intro t h; fin_cases t <;> simp_all [privateTensor, boundaryTensor]
  statements := fun _ => 1
  valuations := fun _ _ => 1
  guard := fun _ _ _ => true
  destination := fun _ _ _ => ()
  body := fun _ _ => if strict then reciprocalBody _ else totalBody _

def downstreamSchedule (strict : Bool) : Schedule (downstreamProgram strict) where
  tensors := [privateTensor, boundaryTensor]
  tensors_nodup := by decide
  tensors_complete := by intro t; fin_cases t <;> simp [privateTensor, boundaryTensor]
  keys := [
    .occurrence ⟨boundaryTensor, rfl⟩ ⟨0, ⟨0, rfl⟩⟩,
    .publication ⟨boundaryTensor, rfl⟩ ()]
  keys_nodup := by
    simp [List.nodup_cons, privateTensor, boundaryTensor]
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨t, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      change (t == privateTensor) = false at ht
      fin_cases t <;> fin_cases s <;> fin_cases v <;>
        first | exact False.elim (Bool.noConfusion ht) |
          simp [privateTensor, boundaryTensor]
    | publication t p =>
      rcases t with ⟨t, ht⟩
      change (t == privateTensor) = false at ht
      cases p
      fin_cases t <;>
        first | exact False.elim (Bool.noConfusion ht) |
          simp [privateTensor, boundaryTensor]

def downstreamContract : Contract declarations :=
  ⟨[privateTensor, boundaryTensor], fun t => t == privateTensor,
    [(⟨boundaryTensor, ()⟩, [301])],
    [⟨privateTensor, ()⟩], [⟨boundaryTensor, ()⟩]⟩

def downstreamFragment (strict : Bool) : Fragment declarations :=
  ⟨[⟨30, 301, ⟨boundaryTensor, ()⟩, [⟨privateTensor, ()⟩],
    if strict then reciprocalBody Unit else totalBody Unit⟩]⟩

def downstreamGraph (strict : Bool) : Closed declarations :=
  ⟨downstreamContract, canonicalSteps downstreamContract (downstreamFragment strict)⟩

def downstreamEquiv (strict : Bool) :
    SourceOccurrence (downstreamProgram strict) ≃
      Fin (downstreamFragment strict).writers.length where
  toFun := fun _ => ⟨0, by simp [downstreamFragment]⟩
  invFun := fun _ => ⟨⟨boundaryTensor, rfl⟩, ⟨0, ⟨0, rfl⟩⟩⟩
  left_inv := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    fin_cases t <;> fin_cases s <;> fin_cases v <;>
      first | exact False.elim (Bool.noConfusion ht) | rfl
  right_inv := by intro i; fin_cases i; rfl

def downstreamMatch (strict : Bool) : SourceContractMatch
    (downstreamProgram strict) (downstreamSchedule strict)
    downstreamContract (downstreamFragment strict) (downstreamGraph strict) where
  close_ok := by cases strict <;> rfl
  input_roles := rfl
  tensor_order := rfl
  outputs_exact := by
    rintro ⟨t, p⟩
    cases p
    fin_cases t <;> simp [downstreamContract, privateTensor, boundaryTensor]
  sourceToWriter := downstreamEquiv strict
  writer_destination := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    fin_cases t <;> fin_cases s <;> fin_cases v <;>
      first | exact False.elim (Bool.noConfusion ht) | rfl
  writer_reads := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩
    cases strict <;> fin_cases t <;> fin_cases s <;> fin_cases v <;>
      first | exact False.elim (Bool.noConfusion ht) | rfl
  eval_agrees := by
    rintro ⟨⟨t, ht⟩, ⟨s, ⟨v, hv⟩⟩⟩ store
    cases strict <;> fin_cases t <;> fin_cases s <;> fin_cases v <;>
      first | exact False.elim (Bool.noConfusion ht) | rfl
  priority := by cases strict <;> rfl

def downstreamComponent (strict : Bool) : MatchedComponent declarations where
  program := downstreamProgram strict
  schedule := downstreamSchedule strict
  contract := downstreamContract
  fragment := downstreamFragment strict
  graph := downstreamGraph strict
  matched := downstreamMatch strict
  inputs := [⟨privateTensor, (), [], rfl, rfl⟩]
  outputs := [⟨boundaryTensor, (), [], rfl, rfl⟩]
  inputs_nodup := by simp
  outputs_nodup := by simp
  inputs_exact := by intro t; fin_cases t <;> simp [privateTensor]
  outputs_exact := by intro t; fin_cases t <;> simp [boundaryTensor]

def cycleUpstream := upstreamComponent false
def cycleDownstream := downstreamComponent true
def hiddenUpstream := upstreamComponent true
def totalDownstream := downstreamComponent false

def scalarBoundary (hidden strict : Bool) :
    Boundary (upstreamComponent hidden) (downstreamComponent strict) where
  matched :=
    { toFun := fun _ => ⟨boundaryTensor, rfl⟩
      invFun := fun _ => ⟨privateTensor, rfl⟩
      left_inv := by
        rintro ⟨t, ht⟩
        change (t == privateTensor) = true at ht
        fin_cases t <;> first | rfl | exact False.elim (Bool.noConfusion ht)
      right_inv := by
        rintro ⟨t, ht⟩
        change (t == boundaryTensor) = true at ht
        fin_cases t <;> first | rfl | exact False.elim (Bool.noConfusion ht) }
  domain := fun _ => Domain.id []

def cycleBoundary : Boundary cycleUpstream cycleDownstream := scalarBoundary false true
def hiddenBoundary : Boundary hiddenUpstream totalDownstream := scalarBoundary true false

def upstreamInput (hidden : Bool) : (upstreamProgram hidden).Input :=
  ⟨fun _ => none, by intro t; rfl⟩

def downstreamInput (strict : Bool) (x : ℚ) : (downstreamProgram strict).Input :=
  ⟨fun t => if t == privateTensor then some (fun _ => x) else none,
    by intro t; fin_cases t <;> rfl⟩

def scalarStore (t u : ℚ) : Store RationalReference.Carrier declarations :=
  fun a => if a.1 == privateTensor then t else u

private theorem sequence_one (x : ℚ) :
    LeanNCD.Semantics.sequence (fun _ : Fin 1 => some x) =
      some (fun _ : Fin 1 => x) := by
  apply LeanNCD.Semantics.sequence_complete
  intro i
  rfl

theorem scalarStore_private (t u : ℚ) :
    scalarStore t u ⟨privateTensor, ()⟩ = t := rfl

theorem scalarStore_boundary (t u : ℚ) :
    scalarStore t u ⟨boundaryTensor, ()⟩ = u := rfl

theorem scalarStore_distinct :
    scalarStore 0 0 ≠ scalarStore 1 1 := by
  intro h
  have cell := congrFun h ⟨privateTensor, ()⟩
  norm_num [scalarStore, privateTensor] at cell

theorem hiddenStore_distinct :
    scalarStore 0 0 ≠ scalarStore 1 0 := by
  intro h
  have cell := congrFun h ⟨privateTensor, ()⟩
  norm_num [scalarStore, privateTensor] at cell

theorem hidden_boundary_equal :
    (upstreamProgram true).outputProjection (scalarStore 0 0) =
      (upstreamProgram true).outputProjection (scalarStore 1 0) := by
  funext t p
  rcases t with ⟨t, ht⟩
  cases p
  change (t == boundaryTensor) = true at ht
  fin_cases t <;> first | exact False.elim (Bool.noConfusion ht) |
    simp [boundaryTensor, privateTensor, outputProjection, scalarStore]

theorem upstream_model (hidden : Bool) (x : ℚ) (hx : x = 0 ∨ x = 1) :
    (upstreamProgram hidden).Models RationalReference.ops (upstreamInput hidden)
      (scalarStore x (if hidden then 0 else x)) := by
  rcases hx with rfl | rfl <;> cases hidden
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · intro t o
      rcases t with ⟨t, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      fin_cases t <;> fin_cases s <;> fin_cases v <;>
        decide +revert
    · intro t f hf p
      fin_cases t <;> simp [upstreamInput] at hf
    · intro t p
      rcases t with ⟨t, ht⟩
      cases p
      fin_cases t <;>
        norm_num [Program.collect, pushforward, Program.contribution,
          Program.outcome, upstreamProgram, squareBody, readScalar, interpret,
          evalWith, Registry.apply, RationalReference.registry,
          sequence_one, Finset.sum_sigma', Finset.sum_subtype,
          scalarStore, privateTensor, boundaryTensor]

theorem cycle_upstream_zero_model :
    cycleUpstream.program.Models RationalReference.ops
      (upstreamInput false) (scalarStore 0 0) :=
  upstream_model false 0 (Or.inl rfl)

theorem cycle_upstream_one_model :
    cycleUpstream.program.Models RationalReference.ops
      (upstreamInput false) (scalarStore 1 1) :=
  upstream_model false 1 (Or.inr rfl)

theorem cycle_upstream_not_admissible :
    ¬ cycleUpstream.program.AdmInput RationalReference.ops (upstreamInput false) := by
  rintro ⟨ρ, _, unique⟩
  have h0 := unique (scalarStore 0 0) cycle_upstream_zero_model
  have h1 := unique (scalarStore 1 1) cycle_upstream_one_model
  exact scalarStore_distinct (h0.trans h1.symm)

theorem hidden_upstream_zero_model :
    hiddenUpstream.program.Models RationalReference.ops
      (upstreamInput true) (scalarStore 0 0) :=
  upstream_model true 0 (Or.inl rfl)

theorem hidden_upstream_one_model :
    hiddenUpstream.program.Models RationalReference.ops
      (upstreamInput true) (scalarStore 1 0) :=
  upstream_model true 1 (Or.inr rfl)

theorem reciprocal_zero_no_model :
    ¬ ∃ ρ, cycleDownstream.program.Models RationalReference.ops
      (downstreamInput true 0) ρ := by
  rintro ⟨ρ, h, agree, _⟩
  have hp : ρ ⟨privateTensor, ()⟩ = 0 :=
    agree privateTensor (fun _ => 0) rfl ()
  change (downstreamProgram true).AdmEnv RationalReference.ops ρ at h
  have bad := h ⟨boundaryTensor, rfl⟩ ⟨0, ⟨0, rfl⟩⟩
  have hp0 : ρ ⟨(0 : Fin 2), ()⟩ = 0 := hp
  simp [Program.outcome, downstreamProgram, reciprocalBody, readScalar,
    interpret, evalWith, Registry.apply, sequence_one, hp0,
    privateTensor, boundaryTensor] at bad

theorem downstream_input_agreement (strict : Bool) :
    (downstreamProgram strict).InputAgreement
      (downstreamInput strict (if strict then 1 else 0))
      (scalarStore (if strict then 1 else 0) 1) := by
  intro t f hf p
  fin_cases t
  · have hfun : (fun _ : Unit => (if strict then (1 : ℚ) else 0)) = f := by
      simpa [downstreamInput, privateTensor] using hf
    simpa [scalarStore, privateTensor] using congrFun hfun p
  · simp [downstreamInput, privateTensor] at hf

theorem downstream_model (strict : Bool) :
    (downstreamProgram strict).Models RationalReference.ops
      (downstreamInput strict (if strict then 1 else 0))
      (scalarStore (if strict then 1 else 0) 1) := by
  cases strict
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · intro t o
      rcases t with ⟨t, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      change (t == privateTensor) = false at ht
      fin_cases t <;> fin_cases s <;> fin_cases v <;>
        first | exact False.elim (Bool.noConfusion ht) | decide +revert
    · exact downstream_input_agreement _
    · intro t p
      rcases t with ⟨t, ht⟩
      cases p
      change (t == privateTensor) = false at ht
      fin_cases t <;>
        first | exact False.elim (Bool.noConfusion ht) |
          norm_num [Program.collect, pushforward, Program.contribution,
            Program.outcome, downstreamProgram, totalBody, reciprocalBody,
            readScalar, interpret, evalWith, Registry.apply, RationalReference.registry,
            RationalReference.ops, ScalarOps.combine,
            sequence_one, Finset.sum_sigma', Finset.sum_subtype,
            scalarStore, privateTensor, boundaryTensor]

theorem reciprocal_one_model :
    cycleDownstream.program.Models RationalReference.ops
      (downstreamInput true 1) (scalarStore 1 1) := by
  exact downstream_model true

theorem total_zero_model :
    totalDownstream.program.Models RationalReference.ops
      (downstreamInput false 0) (scalarStore 0 1) := by
  exact downstream_model false

theorem reciprocal_one_unique :
    ∀ ρ, cycleDownstream.program.Models RationalReference.ops
      (downstreamInput true 1) ρ → ρ = scalarStore 1 1 := by
  rintro ρ ⟨h, agree, equations⟩
  have hp : ρ ⟨privateTensor, ()⟩ = 1 :=
    agree privateTensor (fun _ => 1) rfl ()
  funext a
  rcases a with ⟨t, p⟩
  cases p
  fin_cases t
  · simpa [scalarStore, privateTensor] using hp
  · have eq := equations ⟨boundaryTensor, rfl⟩ ()
    change ρ ⟨boundaryTensor, ()⟩ =
      (downstreamProgram true).collect RationalReference.ops ρ h ⟨boundaryTensor, rfl⟩ ()
      at eq
    have hp0 : ρ ⟨(0 : Fin 2), ()⟩ = 1 := hp
    have hc : (downstreamProgram true).collect RationalReference.ops ρ h
        ⟨boundaryTensor, rfl⟩ () = 1 := by
      norm_num [Program.collect, pushforward, Program.contribution, Program.outcome,
        downstreamProgram, reciprocalBody, readScalar, interpret, evalWith,
        Registry.apply, sequence_one, Finset.sum_sigma', Finset.sum_subtype,
        hp, hp0, privateTensor, boundaryTensor]
    simpa [scalarStore, privateTensor, boundaryTensor] using eq.trans hc

#eval ((upstreamProgram false).outcome RationalReference.ops
  (scalarStore 0 0) ⟨privateTensor, rfl⟩ ⟨0, ⟨0, rfl⟩⟩,
  (upstreamProgram false).outcome RationalReference.ops
    (scalarStore 1 1) ⟨privateTensor, rfl⟩ ⟨0, ⟨0, rfl⟩⟩)

#eval ((downstreamProgram true).outcome RationalReference.ops
  (scalarStore 0 0) ⟨boundaryTensor, rfl⟩ ⟨0, ⟨0, rfl⟩⟩,
  (downstreamProgram true).outcome RationalReference.ops
    (scalarStore 1 1) ⟨boundaryTensor, rfl⟩ ⟨0, ⟨0, rfl⟩⟩)

#eval ((upstreamProgram true).outputProjection (scalarStore 0 0)
    ⟨boundaryTensor, rfl⟩ (),
  (upstreamProgram true).outputProjection (scalarStore 1 0)
    ⟨boundaryTensor, rfl⟩ (),
  (downstreamProgram false).outcome RationalReference.ops
    (scalarStore 0 1) ⟨boundaryTensor, rfl⟩ ⟨0, ⟨0, rfl⟩⟩)

end IndexedComponentModelCycleFixtures

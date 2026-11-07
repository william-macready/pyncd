import IndexedComponentCompositionClosure
import IndexedComponentCompositionSchedule
import IndexedComponentCompositionProgram

namespace IndexedComponentComposition

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open IndexedComponentTransport
open IndexedOpenComposition

variable {σA σB : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB)
variable (wire : Boundary A B)

instance compositeFintype : Fintype (declarations A B).Tensor := by
  letI : Fintype B.program.Defined :=
    Subtype.fintype (fun t => B.program.input t = false)
  change Fintype (σA.Tensor ⊕ B.program.Defined)
  infer_instance

instance compositeDecidableEq : DecidableEq (declarations A B).Tensor := by
  change DecidableEq (σA.Tensor ⊕ B.program.Defined)
  infer_instance

def contract : Contract (declarations A B) :=
  assembledContract (upstream A B) (downstream A B wire)
    upstreamId downstreamId (tensorOrder A B) (program A B wire).input
    A.contract B.contract

def fragment : Fragment (declarations A B) :=
  assembledFragment (upstream A B) (downstream A B wire)
    upstreamId downstreamId A.fragment B.fragment

def graph : Closed (declarations A B) :=
  assembledGraph (upstream A B) (downstream A B wire)
    upstreamId downstreamId (tensorOrder A B) (program A B wire).input
    A.contract B.contract A.fragment B.fragment

private theorem address_lift {src dst : Declarations Unit} (f : Embedding src dst)
    (z : Address dst) (t : src.Tensor) (ht : f.tensor t = z.1) :
    ∃ p : Coord (src.signature t).axes, f.address ⟨t, p⟩ = z := by
  rcases z with ⟨u, q⟩
  change f.tensor t = u at ht
  subst u
  exact ⟨(f.domain t).coord.symm q, by simp [Embedding.address]⟩

theorem closureScope :
    ClosureScope (upstream A B) (downstream A B wire)
      (program A B wire).input A.contract B.contract := by
  have ha := ClosureFacts.of_close A.matched.close_ok
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    simpa [upstream, program] using congrFun A.matched.input_roles t |>.symm
  · intro t ht
    have ht' : B.program.input t = false := by
      simpa [← B.matched.input_roles] using ht
    simp [downstream, downstreamTensor, ht', program]
  · rintro ⟨t, p⟩ ht
    cases t with
    | inl t =>
      refine Or.inl ⟨⟨t, p⟩, ?_, ?_⟩
      · simpa [← A.matched.input_roles, program] using ht
      · rfl
    | inr t =>
      obtain ⟨q, hq⟩ := address_lift (downstream A B wire)
        ⟨.inr t, p⟩ t.val (downstreamTensor_defined A B wire t)
      exact Or.inr ⟨⟨t.val, q⟩,
        by simpa [← B.matched.input_roles] using t.property, hq⟩
  · rintro ⟨tx, px⟩ ⟨ty, py⟩ hx hy he
    have hy' : B.program.input ty = false := by
      simpa [← B.matched.input_roles] using hy
    have ht : (upstream A B).tensor tx =
        (downstream A B wire).tensor ty := congrArg Sigma.fst he
    simp [upstream, downstream, downstreamTensor, hy'] at ht
  · rintro ⟨t, p⟩ ht
    have ht' : B.program.input t = true := by
      simpa [← B.matched.input_roles] using ht
    let i : {t : σB.Tensor // B.program.input t = true} := ⟨t, ht'⟩
    let a := (wire.matched i).val
    have hout : A.program.output a = true := (wire.matched i).property
    have hdefined : A.contract.input a = false := by
      rw [A.matched.input_roles]
      exact A.program.output_defined a hout
    let z := (downstream A B wire).address ⟨t, p⟩
    have htarget : (upstream A B).tensor a = z.1 := by
      simpa [upstream, z, Embedding.address, a, i] using
        (downstreamTensor_input A B wire i).symm
    obtain ⟨q, hq⟩ := address_lift (upstream A B) z a htarget
    let x : Address σA := ⟨a, q⟩
    have hx : x ∈ A.contract.collectors.map Prod.fst :=
      (ha.collector_iff x).mpr hdefined
    change z ∈ A.contract.collectors.map
      (fun row => (upstream A B).address row.1)
    rw [← hq]
    simpa only [List.map_map, Function.comp_apply] using
      (List.mem_map.mpr ⟨x, hx, rfl⟩ :
        (upstream A B).address x ∈
          (A.contract.collectors.map Prod.fst).map (upstream A B).address)

theorem tensorOrder_length :
    (tensorOrder A B).length = Fintype.card (declarations A B).Tensor := by
  classical
  have hall : (tensorOrder A B).toFinset = Finset.univ := by
    ext t
    simp [tensorOrder_complete A B t]
  rw [← List.toFinset_card_of_nodup (tensorOrder_nodup A B), hall]
  simp

theorem close_ok :
    close (contract A B wire) (fragment A B wire) = .ok (graph A B wire) := by
  exact close_assembled (upstream A B) (downstream A B wire)
    upstreamId downstreamId upstreamId_injective downstreamId_injective
    ids_disjoint (tensorOrder A B) (program A B wire).input
    A.contract B.contract A.fragment B.fragment A.graph B.graph
    A.matched.close_ok B.matched.close_ok
    (closureScope A B wire) (tensorOrder_nodup A B) (tensorOrder_length A B)

theorem input_roles : (contract A B wire).input = (program A B wire).input := rfl

theorem tensor_order :
    (contract A B wire).tensors = (schedule A B wire).tensors := rfl

theorem canonical_steps :
    canonicalSteps (contract A B wire) (fragment A B wire) =
      (canonicalSteps A.contract A.fragment).map
        (mapStep (upstream A B) upstreamId) ++
      (canonicalSteps B.contract B.fragment).map
        (mapStep (downstream A B wire) downstreamId) := by
  exact canonicalSteps_assembled (upstream A B) (downstream A B wire)
    upstreamId downstreamId upstreamId_injective downstreamId_injective
    ids_disjoint (tensorOrder A B) (program A B wire).input
    A.contract B.contract A.fragment B.fragment

theorem graph_steps :
    (graph A B wire).steps =
      (canonicalSteps A.contract A.fragment).map
        (mapStep (upstream A B) upstreamId) ++
      (canonicalSteps B.contract B.fragment).map
        (mapStep (downstream A B wire) downstreamId) := rfl

theorem outputs_exact (z : Address (declarations A B)) :
    z ∈ (contract A B wire).outputs ↔
      (program A B wire).output z.1 = true := by
  rcases z with ⟨t, p⟩
  cases t with
  | inl t =>
    constructor
    · intro h
      change (⟨.inl t, p⟩ : Address (declarations A B)) ∈
        B.contract.outputs.map (downstream A B wire).address at h
      obtain ⟨y, hy, he⟩ := List.mem_map.mp h
      have hout := (B.matched.outputs_exact y).mp hy
      have hdefined := B.program.output_defined y.1 hout
      have ht := congrArg Sigma.fst he
      simp [Embedding.address, downstream, downstreamTensor, hdefined] at ht
    · intro h
      simp [program] at h
  | inr t =>
    constructor
    · intro h
      change (⟨.inr t, p⟩ : Address (declarations A B)) ∈
        B.contract.outputs.map (downstream A B wire).address at h
      obtain ⟨y, hy, he⟩ := List.mem_map.mp h
      have hout : B.program.output y.1 = true :=
        (B.matched.outputs_exact y).mp hy
      have hd : B.program.input y.1 = false :=
        B.program.output_defined y.1 hout
      have hty : y.1 = t.val := by
        have he' := congrArg Sigma.fst he
        have he'' : (⟨y.1, hd⟩ : B.program.Defined) = t := by
          have hm : (downstream A B wire).tensor y.1 =
              .inr (⟨y.1, hd⟩ : B.program.Defined) := by
            simp [downstream, downstreamTensor, hd]
          change (downstream A B wire).tensor y.1 = .inr t at he'
          rw [hm] at he'
          exact Sum.inr.inj he'
        exact congrArg Subtype.val he''
      simpa [program, ← hty] using hout
    · intro h
      have hB : B.program.output t.val = true := by simpa [program] using h
      obtain ⟨q, hq⟩ := address_lift (downstream A B wire)
        ⟨.inr t, p⟩ t.val (downstreamTensor_defined A B wire t)
      change (⟨.inr t, p⟩ : Address (declarations A B)) ∈
        B.contract.outputs.map (downstream A B wire).address
      exact List.mem_map.mpr ⟨⟨t.val, q⟩,
        (B.matched.outputs_exact ⟨t.val, q⟩).mpr hB, hq⟩

end IndexedComponentComposition

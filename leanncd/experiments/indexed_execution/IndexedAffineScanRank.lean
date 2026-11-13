import IndexedAffineScanMatch
import LeanNCD.Semantics.Ranks
import IndexedComponentCompositionScope

namespace IndexedExecutionExperiment.AffineScan

open LeanNCD.Semantics LeanNCD.Eval.Plan

variable (p : Profile d n)

theorem Profile.external_bound (cap : BlockCapture) (hcap : cap ∈ allCaptures p.checked)
    (slot : Nat) (hs : cap.source = .external slot) : slot < p.checked.sigs.size := by
  have h := p.fields
  simp only [profileOk, Bool.and_eq_true] at h
  have bounded : capturesBounded p.checked = true := by tauto
  have hb := List.all_eq_true.mp bounded cap hcap
  simpa only [hs, decide_eq_true_eq] using hb

theorem outerSlot_selected (i : Fin (externalSlots p).length) :
    externalCapture p.checked (outerSlot p i).val = true :=
  (List.mem_filter.mp (List.get_mem (externalSlots p) i)).2

theorem input_outer_iff (slot : Nat) :
    (∃ i : Fin (externalSlots p).length, (outerSlot p i).val = slot) ↔
      ∃ cap ∈ allCaptures p.checked, cap.source = .external slot := by
  constructor
  · rintro ⟨i, hi⟩
    have selected := outerSlot_selected p i
    rw [hi] at selected
    exact List.any_eq_true.mp selected |>.imp (fun cap h => ⟨h.1, of_decide_eq_true h.2⟩)
  · rintro ⟨cap, hcap, hs⟩
    have bound := p.external_bound cap hcap slot hs
    have selected : externalCapture p.checked slot = true :=
      List.any_eq_true.mpr ⟨cap, hcap, by simp [hs]⟩
    exact ⟨externalIndex p ⟨slot, bound⟩ selected,
      congrArg Fin.val (outerSlot_externalIndex p ⟨slot, bound⟩ selected)⟩

theorem input_signature (i : Fin (externalSlots p).length) :
    (declarations p).signature (.inl i) =
      ⟨(), slotShape ((outerSlot p i).val + 1)
        p.checked.sigs[outerSlot p i].shape.toList⟩ := rfl

theorem Profile.base_capture :
    ∃ slot, p.checked.raw.baseCaptures = #[{ inputSlot := 0, source := .external slot }] ∧
      p.checked.sigs[slot]? = some { shape := #[d], dtype := .f64 } := by
  let z := p.checked.raw.baseCaptures.getD 0 default
  let outer := match z.source with | .external slot => some slot | .state _ => none
  have h := p.fields
  simp only [profileOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have single : p.checked.raw.baseCaptures = #[z] := by tauto
  have input : z.inputSlot = 0 := by tauto
  have external : outer.isSome = true := by tauto
  have sig : outer.bind (fun slot => p.checked.sigs[slot]?) =
      some { shape := #[d], dtype := .f64 } := by tauto
  cases hs : z.source with
  | state si => simp only [outer, hs, Option.isSome_none, Bool.false_eq_true] at external
  | external slot =>
      refine ⟨slot, ?_, ?_⟩
      · have hz : z = { inputSlot := 0, source := .external slot } := by
          have eta : z = { inputSlot := z.inputSlot, source := z.source } := by
            cases z
            rfl
          exact eta.trans (congrArg₂ BlockCapture.mk input hs)
        exact single.trans (congrArg (fun cap => #[cap]) hz)
      · simpa only [outer, hs, Option.bind_some] using sig

theorem slot_bound {sigs : Array TensorSignature} {slot : Nat} {sig : TensorSignature}
    (hs : sigs[slot]? = some sig) : slot < sigs.size := by
  rcases Array.getElem?_eq_some_iff.mp hs with ⟨bound, _⟩
  exact bound

theorem read_footprint {tx : (declarations p).Tensor}
    (access : AdmittedRead ℚ ((declarations p).signature tx).axes Γ)
    (γ : Γ) (a : Address (declarations p))
    (ha : a ∈ footprint
      (Expr.read tx access : Expr RationalReference.Carrier (declarations p)
        RationalReference.registry Γ (.scalar ())) γ) :
    ∃ q, access.resolved γ = .at q ∧ a = ⟨tx, q⟩ := by
  cases hq : access.resolved γ with
  | const value => simp only [footprint, hq, List.not_mem_nil] at ha
  | «at» q =>
      refine ⟨q, rfl, ?_⟩
      simpa only [footprint, hq, List.mem_cons, List.not_mem_nil, or_false] using ha

theorem paddedResolve_at {zero : K} {sh : Shape} {raw : RawCoord sh} {q : Coord sh}
    (h : paddedResolve zero sh raw = .at q) : decodeRaw sh raw = some q := by
  cases hd : decodeRaw sh raw with
  | none =>
      simp only [paddedResolve, hd] at h
      cases h
  | some v =>
      have he : v = q := by simpa only [paddedResolve, hd, Resolved.at.injEq] using h
      simp [he]

private def stateAccess (r : ReadPlan) (basis : Γ → List Int) :
    AdmittedRead ℚ (historyShape d n) Γ where
  policy := zeroPolicy 0 _
  raw := fun γ j => (applyAffine r.map (basis γ)).getD j.val 0
  resolved := fun γ => paddedResolve 0 _
    (fun j => (applyAffine r.map (basis γ)).getD j.val 0)
  admission := fun _ => rfl

theorem factor_rank (t : TermPlan) (supported : termSupported p.checked d n t = true)
    (f : FactorPlan) (hf : f ∈ t.factors) (i : Int) (clock : Nat) (γ : Γ)
    (a : Address (declarations p))
    (ha : a ∈ footprint (factorBody p p.checked.raw.stepCaptures
      (fun _ : Γ => termBasis t i clock) f) γ) :
    addressRank p a ≤ clock + 1 := by
  cases f with
  | iverson pred => simp only [factorBody, footprint, List.not_mem_nil] at ha
  | read r =>
      have captured := supported_capture p.checked t supported r hf
      cases hc : p.checked.raw.stepCaptures.find? (fun cap => cap.inputSlot == r.sourceSlot) with
      | none => simp only [hc] at captured
      | some cap =>
          cases hs : cap.source with
          | external slot =>
              simp only [hc, hs] at captured
              obtain ⟨sig, sig_eq, selected⟩ := captured
              have bound := slot_bound sig_eq
              let inputSlot := externalIndex p ⟨slot, bound⟩ selected
              have tensor_eq : readTensor p p.checked.raw.stepCaptures r = .inl inputSlot := by
                cases cap with
                | mk input source =>
                    change source = .external slot at hs
                    subst source
                    simp [readTensor, hc, bound, selected, inputSlot]
              obtain ⟨q, _, he⟩ := read_footprint p
                (actualAccess p p.checked.raw.stepCaptures r (fun _ : Γ => termBasis t i clock))
                γ a ha
              have ht : a.1 = .inl inputSlot :=
                (congrArg Sigma.fst he).trans tensor_eq
              rcases a with ⟨tx, aq⟩
              cases ht
              exact Nat.zero_le _
          | state si =>
              simp only [hc, hs] at captured
              have tensor_eq : readTensor p p.checked.raw.stepCaptures r = .inr () := by
                cases cap with
                | mk input source =>
                    change source = .state si at hs
                    subst source
                    simp [readTensor, hc]
              have ha' : a ∈ footprint
                  (@Expr.read Unit RationalReference.Carrier (declarations p)
                    RationalReference.registry Γ (Sum.inr ())
                    (stateAccess (d := d) (n := n) r (fun _ : Γ => termBasis t i clock)) :
                    Expr RationalReference.Carrier (declarations p)
                      RationalReference.registry Γ (.scalar ())) γ := by
                have he := congrArg (fun tx : (declarations p).Tensor =>
                  footprint (@Expr.read Unit RationalReference.Carrier (declarations p)
                    RationalReference.registry Γ tx
                    (tensorAccess p tx r (fun _ : Γ => termBasis t i clock))) γ) tensor_eq
                exact Eq.mp (congrArg (fun fp => a ∈ fp) he) ha
              obtain ⟨q, resolved, he⟩ := read_footprint p _ γ a ha'
              subst a
              have inside := paddedResolve_at resolved
              have earlier := captured_state_earlier t r
                (supported_basis p.checked t supported) captured i clock q inside
              exact Nat.succ_le_succ earlier

theorem orderedProduct_footprint (caps : Array BlockCapture) (basis : Γ → List Int)
    (fs : List FactorPlan) (γ : Γ) :
    footprint (orderedProduct p caps basis fs) γ =
      fs.flatMap (fun f => footprint (factorBody p caps basis f) γ) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp only [orderedProduct, footprint, List.flatMap_cons, ih]

theorem orderedSum_footprint (caps : Array BlockCapture) (i clock : Γ → Int)
    (ts : List TermPlan) (γ : Γ) :
    footprint (orderedSum p caps i clock ts) γ =
      ts.flatMap (fun t => t.factors.toList.flatMap
        (fun f => footprint (factorBody p caps
          (fun γ => termBasis t (i γ) (clock γ)) f) γ)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [orderedSum, footprint, orderedProduct_footprint, List.flatMap_cons, ih]

theorem step_rank (i : Int) (clock : Nat) (γ : Γ) (a : Address (declarations p))
    (ha : a ∈ footprint (orderedSum p p.checked.raw.stepCaptures
      (fun _ : Γ => i) (fun _ => clock) (stepAssign p.checked).terms.toList) γ) :
    addressRank p a ≤ clock + 1 := by
  rw [orderedSum_footprint] at ha
  rcases List.mem_flatMap.mp ha with ⟨t, ht, ha⟩
  rcases List.mem_flatMap.mp ha with ⟨f, hf, ha⟩
  exact factor_rank p t (p.step_terms t (by simpa using ht)) f (by simpa using hf)
    i clock γ a ha

theorem base_rank (i : Int) (γ : Γ) (a : Address (declarations p))
    (ha : a ∈ footprint (orderedSum p p.checked.raw.baseCaptures
      (fun _ : Γ => i) (fun _ => 0) (baseAssign p.checked).terms.toList) γ) :
    addressRank p a = 0 := by
  obtain ⟨slot, caps, sig⟩ := p.base_capture
  have bound := slot_bound sig
  have selected : externalCapture p.checked slot = true := by
    simp [externalCapture, allCaptures, caps]
  let inputSlot := externalIndex p ⟨slot, bound⟩ selected
  rw [p.base_identity] at ha
  simp only [identityBase, orderedSum, orderedProduct, footprint,
    List.append_nil] at ha
  obtain ⟨q, _, he⟩ := read_footprint p _ γ a ha
  have tensor_eq : readTensor p p.checked.raw.baseCaptures
      { sourceSlot := 0, map := { coeffs := #[#[1]], «bias» := #[0] },
        sourceShape := #[d], oobPolicy := .zeroPad } = .inl inputSlot := by
    simp [readTensor, caps, bound, selected, inputSlot]
  have ht : a.1 = .inl inputSlot := (congrArg Sigma.fst he).trans tensor_eq
  rcases a with ⟨tx, aq⟩
  cases ht
  rfl

theorem body_rank (q : Coord (historyShape d n)) (γ : Γ) (a : Address (declarations p))
    (ha : a ∈ footprint (addressBody p q) γ) :
    addressRank p a < q.2.1.val + 1 := by
  unfold addressBody at ha
  split at ha
  · have hz := base_rank p q.1.val γ a ha
    omega
  · rename_i nonzero
    have clock_eq : (q.2.1.val : Int) - 1 = ((q.2.1.val - 1 : Nat) : Int) := by omega
    rw [clock_eq] at ha
    have hr := step_rank p q.1.val (q.2.1.val - 1) γ a ha
    omega

def rankCertificate : (program p).RankCertificate where
  rank := addressRank p
  decreases := by
    rintro a b ⟨tx, ⟨s, v⟩, rfl, hb⟩
    rcases tx with ⟨tx, ht⟩
    cases tx with
    | inl slot => contradiction
    | inr u =>
        cases u
        exact body_rank p ((canonicalLayout (historyShape d n)).enumerate s) v b hb

def inputPorts : List (IndexedComponentComposition.Port (declarations p)) :=
  (List.finRange (externalSlots p).length).map fun i =>
    { «tensor» := .inl i
      sort := ()
      axes := ((declarations p).signature (.inl i)).axes
      sort_eq := rfl
      axes_eq := rfl }

def outputPorts : List (IndexedComponentComposition.Port (declarations p)) :=
  [{ «tensor» := .inr ()
     sort := ()
     axes := historyShape d n
     sort_eq := rfl
     axes_eq := rfl }]

def component : IndexedComponentComposition.MatchedComponent (declarations p) where
  program := program p
  schedule := schedule p
  contract := contract p
  fragment := fragment p
  graph := graphCandidate p
  matched := sourceMatch p
  inputs := inputPorts p
  outputs := outputPorts p
  inputs_nodup := by
    simpa [inputPorts, List.map_map, Function.comp_def] using
      (List.nodup_finRange (externalSlots p).length).map
        (Sum.inl_injective : Function.Injective
          (Sum.inl : Fin (externalSlots p).length → (declarations p).Tensor))
  outputs_nodup := by simp [outputPorts]
  inputs_exact := by
    intro tx
    simp only [inputPorts, List.map_map, Function.comp_def]
    cases tx with
    | inl i =>
        constructor
        · intro _; rfl
        · intro _; exact List.mem_map.mpr ⟨i, by simp, rfl⟩
    | inr u =>
        constructor
        · intro hm
          rcases List.mem_map.mp hm with ⟨i, _, hi⟩
          cases hi
        · intro hf; contradiction
  outputs_exact := by
    intro tx
    cases tx with
    | inl i => simp [outputPorts, program]
    | inr u => cases u; simp [outputPorts, program]

end IndexedExecutionExperiment.AffineScan

#print axioms IndexedExecutionExperiment.AffineScan.rankCertificate
#print axioms IndexedExecutionExperiment.AffineScan.component
#print axioms IndexedExecutionExperiment.AffineScan.input_outer_iff
#audit_axioms IndexedExecutionExperiment.AffineScan

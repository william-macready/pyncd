import IndexedAffineScanRead
import IndexedAffineScanProfile
import IndexedCompositionClosure
import IndexedCompositionMatch
import Semantics.AxiomAudit
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup

namespace IndexedExecutionExperiment.AffineScan

open LeanNCD.Semantics LeanNCD.Eval.Plan

theorem Profile.step_terms (p : Profile d n) :
    ∀ t ∈ (stepAssign p.checked).terms, termSupported p.checked d n t = true := by
  have h := p.fields
  simp only [profileOk, Bool.and_eq_true, beq_iff_eq] at h
  intro t ht
  rcases Array.mem_iff_getElem.mp ht with ⟨i, hi, rfl⟩
  exact Array.all_eq_true.mp h.1.2 i hi

theorem supported_factor (c : CheckedScanPlan) (t : TermPlan)
    (h : termSupported c d n t = true) (r : ReadPlan)
    (hr : FactorPlan.read r ∈ t.factors) :
    plainRead r = true ∧
    r.map.coeffs.size = r.sourceShape.size ∧
    r.map.bias.size = r.sourceShape.size ∧
    (∀ row ∈ r.map.coeffs, row.size = t.iterationShape.size) := by
  simp only [termSupported, Bool.and_eq_true, beq_iff_eq] at h
  rcases Array.mem_iff_getElem.mp hr with ⟨i, hi, he⟩
  have hf := Array.all_eq_true.mp h.2 i hi
  rw [he] at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  refine ⟨hf.1.1.1.1, hf.1.1.1.2, hf.1.1.2, ?_⟩
  intro row hr
  rcases Array.mem_iff_getElem.mp hr with ⟨j, hj, rfl⟩
  simpa only [beq_iff_eq] using Array.all_eq_true.mp hf.1.2 j hj

def slotShape (slot : Nat) (extents : List Nat) : Shape :=
  extents.zipIdx.map fun (extent, pos) => ⟨Nat.pair slot pos + 2, extent⟩

def historyShape (d n : Nat) : Shape :=
  [⟨0, d⟩, ⟨1, n + 1⟩]

def externalSlots (p : Profile d n) : List (Fin p.checked.sigs.size) :=
  (List.finRange p.checked.sigs.size).filter
    (fun slot => externalCapture p.checked slot.val)

theorem externalSlots_nodup (p : Profile d n) : (externalSlots p).Nodup :=
  (List.nodup_finRange _).filter _

def outerSlot (p : Profile d n) (slot : Fin (externalSlots p).length) :
    Fin p.checked.sigs.size :=
  (externalSlots p).get slot

def externalIndex (p : Profile d n) (slot : Fin p.checked.sigs.size)
    (h : externalCapture p.checked slot.val = true) : Fin (externalSlots p).length :=
  ⟨(externalSlots p).idxOf slot,
    List.idxOf_lt_length_iff.mpr (List.mem_filter.mpr ⟨by simp, h⟩)⟩

theorem outerSlot_externalIndex (p : Profile d n) (slot : Fin p.checked.sigs.size)
    (h : externalCapture p.checked slot.val = true) :
    outerSlot p (externalIndex p slot h) = slot :=
  List.idxOf_get _

/-- The right summand is captured history, not an external snapshot at the same outer slot. -/
def declarations (p : Profile d n) : Declarations Unit where
  Tensor := Fin (externalSlots p).length ⊕ Unit
  uid
    | .inl slot => 2 * slot.val + 2
    | .inr _ => 1
  unique := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            change 2 * a.val + 2 = 2 * b.val + 2 at h
            congr 1
            apply Fin.ext
            omega
        | inr b => change 2 * a.val + 2 = 1 at h; omega
    | inr a =>
        cases b with
        | inl b => change 1 = 2 * b.val + 2 at h; omega
        | inr b => congr 1
  signature := fun tx => ⟨(), match tx with
    | .inl slot => slotShape ((outerSlot p slot).val + 1)
        p.checked.sigs[outerSlot p slot].shape.toList
    | .inr _ => historyShape d n⟩

def termBasis (t : TermPlan) (i clock : Int) : List Int :=
  (List.range t.iterationShape.size).map fun pos =>
    if t.contextPos.contains pos then clock
    else if t.outputPos.contains pos then i else 0

def readTensor (p : Profile d n) (captures : Array BlockCapture)
    (r : ReadPlan) : (declarations p).Tensor :=
  match captures.find? (fun cap => cap.inputSlot == r.sourceSlot) with
  | some { source := .external slot, .. } =>
      if h : slot < p.checked.sigs.size then
        if selected : externalCapture p.checked slot = true then
          .inl (externalIndex p ⟨slot, h⟩ selected)
        else .inr ()
      else .inr ()
  | _ => .inr ()

def tensorAccess (p : Profile d n) (tx : (declarations p).Tensor)
    (r : ReadPlan) (basis : Γ → List Int) :
    AdmittedRead ℚ ((declarations p).signature tx).axes Γ where
  policy := zeroPolicy 0 _
  raw := fun γ pos => (applyAffine r.map (basis γ)).getD pos.val 0
  resolved := fun γ => paddedResolve 0 _
    (fun pos => (applyAffine r.map (basis γ)).getD pos.val 0)
  admission := fun _ => rfl

def actualAccess (p : Profile d n) (captures : Array BlockCapture)
    (r : ReadPlan) (basis : Γ → List Int) :
    AdmittedRead ℚ ((declarations p).signature (readTensor p captures r)).axes Γ :=
  tensorAccess p (readTensor p captures r) r basis

def factorBody (p : Profile d n) (captures : Array BlockCapture) (basis : Γ → List Int) :
    FactorPlan → Expr RationalReference.Carrier (declarations p)
      RationalReference.registry Γ (.scalar ())
  | .read r => .read (readTensor p captures r) (actualAccess p captures r basis)
  | .iverson _ => .lit 0

def orderedProduct (p : Profile d n) (captures : Array BlockCapture) (basis : Γ → List Int) :
    List FactorPlan → Expr RationalReference.Carrier (declarations p)
      RationalReference.registry Γ (.scalar ())
  | [] => .lit 1
  | f :: fs => .binary .mul (factorBody p captures basis f)
      (orderedProduct p captures basis fs)

def orderedSum (p : Profile d n) (captures : Array BlockCapture) (i clock : Γ → Int) :
    List TermPlan → Expr RationalReference.Carrier (declarations p)
      RationalReference.registry Γ (.scalar ())
  | [] => .lit 0
  | t :: ts => .binary .add
      (orderedProduct p captures (fun γ => termBasis t (i γ) (clock γ)) t.factors.toList)
      (orderedSum p captures i clock ts)

theorem supported_no_iverson (c : CheckedScanPlan) (t : TermPlan)
    (h : termSupported c d n t = true) (pred : PosBoolExpr) :
    FactorPlan.iverson pred ∉ t.factors := by
  intro hm
  simp only [termSupported, Bool.and_eq_true, beq_iff_eq] at h
  rcases Array.mem_iff_getElem.mp hm with ⟨i, hi, he⟩
  have hf := Array.all_eq_true.mp h.2 i hi
  rw [he] at hf
  contradiction

theorem supported_basis (c : CheckedScanPlan) (t : TermPlan)
    (h : termSupported c d n t = true) :
    t.iterationShape.size = 2 ∧
      ((t.contextPos = #[0] ∧ t.outputPos = #[1]) ∨
        (t.contextPos = #[1] ∧ t.outputPos = #[0])) := by
  simp only [termSupported, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2⟩

theorem supported_capture (c : CheckedScanPlan) (t : TermPlan)
    (h : termSupported c d n t = true) (r : ReadPlan)
    (hr : FactorPlan.read r ∈ t.factors) :
    match c.raw.stepCaptures.find? (fun cap => cap.inputSlot == r.sourceSlot) with
    | none => False
    | some cap => match cap.source with
      | .external slot => ∃ sig, c.sigs[slot]? = some sig ∧ externalCapture c slot = true
      | .state _ => stateRowsOk t r = true := by
  simp only [termSupported, Bool.and_eq_true, beq_iff_eq] at h
  rcases Array.mem_iff_getElem.mp hr with ⟨i, hi, he⟩
  have hf := Array.all_eq_true.mp h.2 i hi
  rw [he] at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  cases hs : c.raw.stepBlock.tensorSigs[r.sourceSlot]? with
  | none =>
      simp only [hs, Bool.false_eq_true] at hf
      exact hf.2.elim
  | some sig =>
      rw [hs] at hf
      cases hc : c.raw.stepCaptures.find? (fun cap => cap.inputSlot == r.sourceSlot) with
      | none => simpa only [hc, Bool.and_false, Bool.false_eq_true] using hf.2
      | some cap =>
          rw [hc] at hf
          cases hsource : cap.source with
          | external slot =>
              simp only [hsource]
              simp only [hsource, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
              exact ⟨sig, hf.2.2⟩
          | state si =>
              simp only [hsource]
              simp only [hsource, Bool.and_eq_true, beq_iff_eq] at hf
              exact hf.2.2.1.2

theorem state_time (t : TermPlan) (r : ReadPlan)
    (basis : t.iterationShape.size = 2 ∧
      ((t.contextPos = #[0] ∧ t.outputPos = #[1]) ∨
        (t.contextPos = #[1] ∧ t.outputPos = #[0])))
    (rows : stateRowsOk t r = true) (i clock : Int) :
    (applyAffine r.map (termBasis t i clock)).getD 1 0 =
      clock + r.map.bias.getD 1 0 := by
  simp only [stateRowsOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at rows
  rcases basis with ⟨size, (⟨ctx, out⟩ | ⟨ctx, out⟩)⟩ <;>
    simp [applyAffine, rows.1.1, rows.1.2, termBasis, size, ctx, out,
      List.range_succ, Int.add_comm]

theorem Profile.base_identity (p : Profile d n) :
    baseAssign p.checked = identityBase d := by
  have h := p.fields
  simp only [profileOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.2

theorem Profile.canonical_fields (p : Profile d n) :
    p.checked.storageKind = .float64 ∧
    p.checked.raw.states = #[{ destSlot := (p.checked.raw.states.getD 0 default).destSlot, advancingDims := #[1], materialization := .completeHistory, initValue := .zero }] ∧
    p.checked.sigs[(p.checked.raw.states.getD 0 default).destSlot]? =
      some { shape := #[d, n + 1], dtype := .f64 } ∧
    p.checked.raw.baseWrites = #[{ outputSlot := 1, stateIndex := 0, map := { coeffs := #[#[1], #[0]], «bias» := #[0, 0] } }] ∧
    p.checked.raw.stepWrites = #[{ outputSlot := (stepAssign p.checked).destinationSlot, stateIndex := 0, map := { coeffs := #[#[0, 1], #[1, 0]], «bias» := #[0, 1] } }] ∧
    (stepAssign p.checked).algebra = admittedAlgebra := by
  have h := p.fields
  simp only [profileOk, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

def addressBody (p : Profile d n) (dest : Coord (historyShape d n)) :
    Expr RationalReference.Carrier (declarations p) RationalReference.registry Γ (.scalar ()) :=
  if dest.2.1.val = 0 then
    orderedSum p p.checked.raw.baseCaptures (fun _ => dest.1.val) (fun _ => 0)
      (baseAssign p.checked).terms.toList
  else
    orderedSum p p.checked.raw.stepCaptures (fun _ => dest.1.val)
      (fun _ => (dest.2.1.val : Int) - 1) (stepAssign p.checked).terms.toList

def program (p : Profile d n) :
    Program RationalReference.Carrier (declarations p) RationalReference.registry where
  tensors := inferInstanceAs (Fintype (Fin (externalSlots p).length ⊕ Unit))
  input := fun t => match t with | .inl _ => true | .inr _ => false
  output := fun t => match t with | .inl _ => false | .inr _ => true
  output_defined := by intro t; cases t <;> simp
  statements := fun _ => (canonicalLayout (historyShape d n)).count
  valuations := fun _ _ => 1
  guard := fun _ _ _ => true
  destination := fun ⟨t, ht⟩ s _ =>
    match t, ht with
    | .inl _, ht => False.elim (Bool.noConfusion ht)
    | .inr _, _ => (canonicalLayout (historyShape d n)).enumerate s
  body := fun ⟨t, ht⟩ s =>
    match t, ht with
    | .inl _, ht => False.elim (Bool.noConfusion ht)
    | .inr _, _ => addressBody p ((canonicalLayout (historyShape d n)).enumerate s)

def addressRank (p : Profile d n) : Address (declarations p) → Nat
  | ⟨.inl _, _⟩ => 0
  | ⟨.inr _, q⟩ => q.2.1.val + 1

def occurrenceEquiv (p : Profile d n) :
    IndexedOpenComposition.SourceOccurrence (program p) ≃
      Fin (canonicalLayout (historyShape d n)).count where
  toFun := fun o => o.2.1
  invFun := fun s => ⟨⟨.inr (), rfl⟩, s, ⟨⟨0, by change 0 < 1; omega⟩, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨tx, ht⟩, s, v, hv⟩
    cases tx with
    | inl slot => contradiction
    | inr u =>
        cases u
        change Fin 1 at v
        have he : v = ⟨0, by omega⟩ := Subsingleton.elim _ _
        subst v
        rfl
  right_inv := fun _ => rfl

def writer (p : Profile d n) (s : Fin (canonicalLayout (historyShape d n)).count) :
    IndexedOpenComposition.Writer (declarations p) :=
  let dest := (canonicalLayout (historyShape d n)).enumerate s
  { tag := s.val
    capability := s.val
    destination := ⟨.inr (), dest⟩
    reads := footprint (addressBody p dest) ()
    body := addressBody p dest }

def fragment (p : Profile d n) : IndexedOpenComposition.Fragment (declarations p) :=
  ⟨(List.finRange (canonicalLayout (historyShape d n)).count).map (writer p)⟩

def tensorOrder (p : Profile d n) : List (declarations p).Tensor :=
  (List.finRange (externalSlots p).length).map Sum.inl ++ [.inr ()]

def contract (p : Profile d n) : IndexedOpenComposition.Contract (declarations p) where
  tensors := tensorOrder p
  input := (program p).input
  collectors := (List.finRange (canonicalLayout (historyShape d n)).count).map
    (fun s => ((writer p s).destination, [s.val]))
  readable := (tensorOrder p).flatMap fun t =>
    (List.finRange (canonicalLayout ((declarations p).signature t).axes).count).map
      (fun s => ⟨t, (canonicalLayout ((declarations p).signature t).axes).enumerate s⟩)
  outputs := (List.finRange (canonicalLayout (historyShape d n)).count).map
    (fun s => (writer p s).destination)

def graphCandidate (p : Profile d n) : IndexedOpenComposition.Closed (declarations p) :=
  ⟨contract p, IndexedOpenComposition.canonicalSteps (contract p) (fragment p)⟩

theorem captured_state_earlier (t : TermPlan) (r : ReadPlan)
    (basis : t.iterationShape.size = 2 ∧
      ((t.contextPos = #[0] ∧ t.outputPos = #[1]) ∨
        (t.contextPos = #[1] ∧ t.outputPos = #[0])))
    (rows : stateRowsOk t r = true) (i : Int) (clock : Nat)
    (q : Coord (historyShape d n))
    (inside : decodeRaw (historyShape d n)
      (fun j => (applyAffine r.map (termBasis t i clock)).getD j.val 0) = some q) :
    q.2.1.val ≤ clock := by
  have coordinates := decodeRaw_sound _ _ q inside
  have time := congrFun coordinates ⟨1, by simp [historyShape]⟩
  have affine := state_time t r basis rows i clock
  have offsets := rows
  simp only [stateRowsOk, Bool.and_eq_true, decide_eq_true_eq] at offsets
  have nonpositive : r.map.bias.getD 1 0 ≤ 0 := offsets.2
  change (q.2.1.val : Int) =
    (applyAffine r.map (termBasis t i clock)).getD 1 0 at time
  omega

#print axioms program
#print axioms occurrenceEquiv
#print axioms captured_state_earlier

end IndexedExecutionExperiment.AffineScan

#audit_axioms IndexedExecutionExperiment.AffineScan

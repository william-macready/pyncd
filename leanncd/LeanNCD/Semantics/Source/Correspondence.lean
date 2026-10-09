import LeanNCD.Semantics.Source.Fiber

namespace LeanNCD.Semantics.Source

variable {K : Type} [Semiring K] {σ : Declarations Unit}
  {r : Registry (fun _ : Unit => K)}

theorem Term.globalProduct_partition (term : Term source out σ)
    (ρ : Store (fun _ => K) σ) (v : UIDVal term.globalContext) :
    term.globalProduct ρ v =
      operandProduct ρ term.operands
        (term.environment (term.partitionCoordEquiv v).1 (term.partitionCoordEquiv v).2) := by
  rw [term.partition_environment]
  unfold Term.globalProduct operandProduct Term.operands
  rw [List.map_ofFn]
  congr 1
  congr 1
  funext i
  congr 1
  change (⟨(term.sourceReads.get i).read.tensor, _⟩ : Address σ) =
    ⟨(term.sourceReads.get i).read.tensor, _⟩
  congr 1
  exact Slots.projectWithin_transport term.globalEmbedding term.partitionTransport
    (fun _ => rfl) _ (term.reads i).slots (term.read_global_support i)
    ((term.reads i).linked.trans (term.sourceReads.get i).linked.symm) v

theorem Term.globalDestination_partition (output : AdmittedOutput source σ)
    (term : Term source output.context σ) (v : UIDVal term.globalContext) :
    Term.globalDestination output term v =
      output.slots.project (term.partitionCoordEquiv v).1 := by
  let localized : Slots term.partition.context.axes (σ.signature output.tensor).axes :=
    term.partition.context_axes.symm ▸ output.slots.appendLeft
  have hl : localized.uids = output.sourceSlots.uids := by
    rw [Slots.cast_uids, Slots.appendLeft_uids, output.linked, output.source_linked]
  have hp := Slots.projectWithin_transport term.globalEmbedding term.partitionTransport
    (fun _ => rfl) output.sourceSlots localized (term.output_global_support output) hl v
  rw [Slots.cast_project, Slots.appendLeft_project] at hp
  exact hp

theorem Term.value_eq_globalSlice (term : Term source out σ)
    (ρ : Store (fun _ => K) σ) (x : Coord out.axes) :
    term.value ρ x =
      ∑ v : UIDVal term.globalContext,
        if (term.partitionCoordEquiv v).1 = x then term.globalProduct ρ v else 0 := by
  rw [← Equiv.sum_comp term.partitionCoordEquiv.symm
    (fun v => if (term.partitionCoordEquiv v).1 = x then term.globalProduct ρ v else 0)]
  simp_rw [term.globalProduct_partition, Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  simp [Term.value]

/-- The actual checked nested reduction, over a total store, equals the relevant UID sum. -/
theorem Term.body_correspondence (term : Term source out σ)
    (ρ : Store (fun _ => K) σ) (env : Γ → Coord out.axes) (γ : Γ) :
    interpret semiringOps ρ (term.body (r := r) env) γ =
      some (∑ v : UIDVal term.globalContext,
        if (term.partitionCoordEquiv v).1 = env γ then term.globalProduct ρ v else 0) := by
  rw [term.interpret_body, term.value_eq_globalSlice]

theorem Term.fiber_partition (output : AdmittedOutput source σ)
    (term : Term source output.context σ) (ρ : Store (fun _ => K) σ)
    (p : Coord (σ.signature output.tensor).axes) :
    term.globalFiber output ρ p =
      ∑ x : Coord output.context.axes,
        if output.slots.project x = p then term.value ρ x else 0 := by
  unfold Term.globalFiber
  rw [← Equiv.sum_comp term.partitionCoordEquiv.symm
    (fun v => if Term.globalDestination output term v = p then term.globalProduct ρ v else 0)]
  simp_rw [Term.globalDestination_partition, Term.globalProduct_partition,
    Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : output.slots.project x = p <;> simp [h, Term.value]

/-- Finite pushforward of interpreted bodies; undefinedness is not erased. -/
def Term.collectedBody (output : AdmittedOutput source σ)
    (term : Term source output.context σ) (ρ : Store (fun _ => K) σ)
    (p : Coord (σ.signature output.tensor).axes) : Option K :=
  let layout := canonicalLayout output.context.axes
  foldValues (semiringOps ())
    ((List.finRange layout.count).map fun i =>
      let x := layout.enumerate i
      if output.slots.project x = p then
        interpret semiringOps ρ (term.body (r := r) id) x else some 0)

theorem Term.collectedBody_correspondence (output : AdmittedOutput source σ)
    (term : Term source output.context σ) (ρ : Store (fun _ => K) σ)
    (p : Coord (σ.signature output.tensor).axes) :
    term.collectedBody (r := r) output ρ p = some (term.globalFiber output ρ p) := by
  unfold Term.collectedBody
  simp_rw [term.interpret_body]
  simp only [id_eq]
  have hi : (fun i : Fin (canonicalLayout output.context.axes).count =>
      if output.slots.project ((canonicalLayout output.context.axes).enumerate i) = p then
        some (term.value ρ ((canonicalLayout output.context.axes).enumerate i)) else some 0) =
      (fun i => some (if output.slots.project
        ((canonicalLayout output.context.axes).enumerate i) = p then
          term.value ρ ((canonicalLayout output.context.axes).enumerate i) else 0)) := by
    funext i
    split <;> rfl
  have hf := fold_some ((List.finRange (canonicalLayout output.context.axes).count).map
    (fun i => if output.slots.project
      ((canonicalLayout output.context.axes).enumerate i) = p then
        term.value ρ ((canonicalLayout output.context.axes).enumerate i) else 0))
  simp only [List.map_map, Function.comp_def] at hf
  rw [hi, hf, List.finRange, List.map_ofFn, List.sum_ofFn]
  congr 1
  rw [term.fiber_partition]
  exact Equiv.sum_comp (canonicalLayout output.context.axes).enumerate
    (fun x => if output.slots.project x = p then term.value ρ x else 0)

/-- Proposition 19.1, term-level: a pure normalized body pushes forward to its
original-read global fiber. Program collection is a separate occurrence-relabeling step. -/
theorem pure_correspondence (output : AdmittedOutput source σ)
    (term : Term source output.context σ) (h : term.classification = .pure)
    (ρ : Store (fun _ => K) σ) (p : Coord (σ.signature output.tensor).axes) :
    term.globalContext = source.select (term.sourceReads.flatMap CheckedRead.indices) ∧
      term.collectedBody (r := r) output ρ p = some (term.globalFiber output ρ p) :=
  ⟨term.pure_globalContext h, term.collectedBody_correspondence output ρ p⟩

theorem Term.empty_fiber (output : AdmittedOutput source σ)
    (term : Term source output.context σ) (ρ : Store (fun _ => K) σ)
    (p : Coord (σ.signature output.tensor).axes)
    (h : ∀ x, output.slots.project x ≠ p) :
    term.globalFiber output ρ p = 0 := by
  rw [term.fiber_partition]
  simp [h]

end LeanNCD.Semantics.Source

import Semantics.SourceCorrespondenceFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceAdmissionFixtures SourceCorrespondenceFixtures SourceProgramFixtures

namespace SourceCorrespondenceTransportTest

private def transportSnapshot : SourceSnapshot :=
  ⟨⟨[.axis k (some 3), .axis e (some 0), .axis i (some 2),
      .tensor "A" [i, k], .tensor "Y" [i]],
    [.assign "Y" [.free i] (rhs [[.read "A" [.axis i, .axis k]]])], {}, ∅⟩,
    [⟨3, .input, [2, 3]⟩, ⟨4, .output, [2]⟩],
    [⟨3, [2, 3], [1, 2, 5, 10, 25, 45]⟩]⟩

private def transportSource : AdmittedSource :=
  (admitSource transportSnapshot).toOption.get (by decide)

private def transportStatement : AdmittedStatement transportSource.source :=
  transportSource.statements.get ⟨0, by decide⟩

private def transportTerm :
    Term transportSource.source.context transportStatement.output.context
      transportSource.source.table.declarations :=
  transportStatement.terms.get ⟨0, by decide⟩

private def transportRead :
    CheckedRead transportSource.source.context transportSource.source.table.declarations :=
  transportTerm.sourceReads.get ⟨0, by decide⟩

private def scope : BinderScope transportTerm.globalContext where
  source := [11]
  output := [7]
  free := []
  generated := [3]
  covers := by
    intro u
    have h := u.property
    change u.val ∈ [3, 7] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h <;> simp [h]
  generatedOnly := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    subst u
    decide

private def renamedContext := renameBinders transportTerm.globalContext scope
private def renameTransport : UIDTransport transportTerm.globalContext renamedContext :=
  binderTransport transportTerm.globalContext scope

private def localRead :
    {s : Slots transportTerm.globalContext.axes
      (transportSource.source.table.declarations.signature transportRead.read.tensor).axes //
      s.uids = transportRead.indices} :=
  (resolveSourceSlots transportTerm.globalContext.axes .read transportRead.origin
    (transportSource.source.table.declarations.signature transportRead.read.tensor).axes
    transportRead.indices).toOption.get (by decide)

private def renamedRead :
    {s : Slots renamedContext.axes
      (transportSource.source.table.declarations.signature transportRead.read.tensor).axes //
      s.uids = transportRead.indices.map scope.renameUID} :=
  (resolveSourceSlots renamedContext.axes .read transportRead.origin
    (transportSource.source.table.declarations.signature transportRead.read.tensor).axes
    (transportRead.indices.map scope.renameUID)).toOption.get (by decide)

private def localDestination :
    {s : Slots transportTerm.globalContext.axes
      (transportSource.source.table.declarations.signature transportStatement.output.tensor).axes //
      s.uids = transportStatement.output.indices} :=
  (resolveSourceSlots transportTerm.globalContext.axes .output transportStatement.output.origin
    (transportSource.source.table.declarations.signature transportStatement.output.tensor).axes
    transportStatement.output.indices).toOption.get (by decide)

private def renamedDestinationSlots :
    {s : Slots renamedContext.axes
      (transportSource.source.table.declarations.signature transportStatement.output.tensor).axes //
      s.uids = transportStatement.output.indices.map scope.renameUID} :=
  (resolveSourceSlots renamedContext.axes .output transportStatement.output.origin
    (transportSource.source.table.declarations.signature transportStatement.output.tensor).axes
    (transportStatement.output.indices.map scope.renameUID)).toOption.get (by decide)

private theorem slots_transport {c d : Context} (t : UIDTransport c d)
    (f : UID → UID) (ht : ∀ u, (t.equiv u).val = f u.val)
    (a : Slots c.axes sh) (b : Slots d.axes sh)
    (h : b.uids = a.uids.map f) (v : UIDVal c) :
    b.project (uidCoordEquiv d (t.valuationEquiv v)) =
      a.project (uidCoordEquiv c v) := by
  induction a with
  | nil => cases b; rfl
  | cons r rest ih =>
    cases b with
    | cons s tail =>
      have hu : s.uid = f r.uid := (List.cons.inj h).1
      have hk : t.equiv (r.key c) = s.key d := by
        apply Subtype.ext
        rw [ht, Ref.key_uid, Ref.key_uid, hu]
      apply Prod.ext
      · rw [Slots.project, Slots.project, Ref.get_uidCoordEquiv, Ref.get_uidCoordEquiv]
        apply Fin.ext
        change (t.valuationEquiv v (s.key d)).val = (v (r.key c)).val
        rw [← hk, UIDTransport.lookup]
      · exact ih tail (List.cons.inj h).2

private theorem localized_projection {c source : Context} (e : IdentityEmbedding c source)
    (a : Slots source.axes sh) (b : Slots c.axes sh)
    (hs : a.uids ⊆ c.axes.map Axis.uid) (hl : b.uids = a.uids) (v : UIDVal c) :
    a.projectWithin e v hs = b.project (uidCoordEquiv c v) := by
  let identity : UIDTransport c c := ⟨Equiv.refl _, fun _ => rfl⟩
  exact Slots.projectWithin_transport e identity (fun _ => rfl) a b hs hl v

private theorem renamed_read_projection (v : UIDVal transportTerm.globalContext) :
    renamedRead.val.project (uidCoordEquiv renamedContext (renameTransport.valuationEquiv v)) =
      transportRead.read.slots.projectWithin transportTerm.globalEmbedding v
        (transportTerm.read_global_support ⟨0, by decide⟩) := by
  calc
    _ = localRead.val.project (uidCoordEquiv transportTerm.globalContext v) := by
      apply slots_transport renameTransport scope.renameUID
        (fun u => Context.mapUIDTransport_uid _ _ _ u)
      rw [renamedRead.property, localRead.property]
    _ = transportRead.read.slots.projectWithin transportTerm.globalEmbedding v
        (transportTerm.read_global_support ⟨0, by decide⟩) :=
      (localized_projection transportTerm.globalEmbedding _ _
      (transportTerm.read_global_support ⟨0, by decide⟩)
      (localRead.property.trans transportRead.linked.symm) v).symm

private theorem renamed_destination_projection (v : UIDVal transportTerm.globalContext) :
    renamedDestinationSlots.val.project
        (uidCoordEquiv renamedContext (renameTransport.valuationEquiv v)) =
      Term.globalDestination transportStatement.output transportTerm v := by
  calc
    _ = localDestination.val.project (uidCoordEquiv transportTerm.globalContext v) := by
      apply slots_transport renameTransport scope.renameUID
        (fun u => Context.mapUIDTransport_uid _ _ _ u)
      rw [renamedDestinationSlots.property, localDestination.property]
    _ = _ := (localized_projection transportTerm.globalEmbedding _ _
      (transportTerm.output_global_support transportStatement.output)
      (localDestination.property.trans transportStatement.output.source_linked.symm) v).symm

private def renamedProduct {K : Type}
    (ρ : Store (fun _ => K) transportSource.source.table.declarations)
    (v : UIDVal renamedContext) : K :=
  ρ ⟨transportRead.read.tensor, renamedRead.val.project (uidCoordEquiv renamedContext v)⟩

private theorem renamed_product {K : Type} [Semiring K]
    (ρ : Store (fun _ => K) transportSource.source.table.declarations)
    (v : UIDVal transportTerm.globalContext) :
    renamedProduct ρ (renameTransport.valuationEquiv v) = transportTerm.globalProduct ρ v := by
  change ρ ⟨transportRead.read.tensor,
    renamedRead.val.project (uidCoordEquiv renamedContext (renameTransport.valuationEquiv v))⟩ =
      ρ ⟨transportRead.read.tensor,
        transportRead.read.slots.projectWithin transportTerm.globalEmbedding v
          (transportTerm.read_global_support ⟨0, by decide⟩)⟩ * 1
  rw [mul_one, renamed_read_projection]

private def renamedFiber {K : Type} [Semiring K]
    (ρ : Store (fun _ => K) transportSource.source.table.declarations)
    (p : Coord
      (transportSource.source.table.declarations.signature transportStatement.output.tensor).axes) :
    K :=
  ∑ v : UIDVal renamedContext,
    if renamedDestinationSlots.val.project (uidCoordEquiv renamedContext v) = p then
      renamedProduct ρ v else 0

private theorem renamed_fiber {K : Type} [Semiring K]
    (ρ : Store (fun _ => K) transportSource.source.table.declarations) (p) :
    renamedFiber ρ p = transportTerm.globalFiber transportStatement.output ρ p := by
  have hp (v : UIDVal renamedContext) :
      renamedProduct ρ v =
        transportTerm.globalProduct ρ (renameTransport.valuationEquiv.symm v) := by
    simpa only [Equiv.apply_symm_apply] using
      renamed_product ρ (renameTransport.valuationEquiv.symm v)
  have hd (v : UIDVal renamedContext) :
      renamedDestinationSlots.val.project (uidCoordEquiv renamedContext v) =
        Term.globalDestination transportStatement.output transportTerm
          (renameTransport.valuationEquiv.symm v) := by
    simpa only [Equiv.apply_symm_apply] using
      renamed_destination_projection (renameTransport.valuationEquiv.symm v)
  unfold renamedFiber
  simp_rw [hp, hd]
  exact uidFiber_reindex renameTransport _ _ p

private theorem partition_left (v : UIDVal transportTerm.globalContext) :
    transportTerm.partitionEquiv.symm (transportTerm.partitionEquiv v) = v :=
  transportTerm.partitionEquiv.symm_apply_apply v

private theorem partition_right
    (v : UIDVal transportStatement.output.context × UIDVal transportTerm.contractedContext) :
    transportTerm.partitionEquiv (transportTerm.partitionEquiv.symm v) = v :=
  transportTerm.partitionEquiv.apply_symm_apply v

private def permutation :
    transportTerm.globalContext.axes.Perm [⟨7, 2⟩, ⟨3, 3⟩] :=
  List.Perm.swap ..

private def reorderedContext := transportTerm.globalContext.reenumerate _ permutation
private def reorderTransport := transportTerm.globalContext.reenumerateTransport _ permutation

private def reorderedRead :
    {s : Slots reorderedContext.axes
      (transportSource.source.table.declarations.signature transportRead.read.tensor).axes //
      s.uids = transportRead.indices} :=
  (resolveSourceSlots reorderedContext.axes .read transportRead.origin
    (transportSource.source.table.declarations.signature transportRead.read.tensor).axes
    transportRead.indices).toOption.get (by decide)

private theorem reenumerated_fiber {K : Type} [Semiring K]
    (ρ : Store (fun _ => K) transportSource.source.table.declarations) (p) :
    (∑ v : UIDVal reorderedContext,
      if Term.globalDestination transportStatement.output transportTerm
          (reorderTransport.valuationEquiv.symm v) = p then
        transportTerm.globalProduct ρ (reorderTransport.valuationEquiv.symm v) else 0) =
      transportTerm.globalFiber transportStatement.output ρ p :=
  transportTerm.globalFiber_reenumerate transportStatement.output _ permutation ρ p

private def partitionRows :=
  let term := transportTerm
  (List.finRange (canonicalLayout term.globalContext.axes).count).map fun index =>
    let v := (uidCoordEquiv term.globalContext).symm
      ((canonicalLayout term.globalContext.axes).enumerate index)
    let pair := term.partitionEquiv v
    (coordList _ (uidCoordEquiv term.globalContext v),
      coordList _ (uidCoordEquiv transportStatement.output.context pair.1),
      coordList _ (uidCoordEquiv term.contractedContext pair.2),
      coordList _ (Term.globalDestination transportStatement.output term v),
      coordList _ (localRead.val.project (uidCoordEquiv term.globalContext v)),
      term.globalProduct (natStore transportSource) v,
      decide (term.partitionEquiv.symm pair = v))

private def independentPartitionRight : Bool :=
  let output := transportStatement.output.context
  let bound := transportTerm.contractedContext
  (List.finRange (canonicalLayout output.axes).count).all fun x =>
    (List.finRange (canonicalLayout bound.axes).count).all fun y =>
      let pair := ((uidCoordEquiv output).symm ((canonicalLayout output.axes).enumerate x),
        (uidCoordEquiv bound).symm ((canonicalLayout bound.axes).enumerate y))
      decide (transportTerm.partitionEquiv (transportTerm.partitionEquiv.symm pair) = pair)

private def mappedRows :=
  (List.finRange (canonicalLayout transportTerm.globalContext.axes).count).map fun index =>
    let v := (uidCoordEquiv transportTerm.globalContext).symm
      ((canonicalLayout transportTerm.globalContext.axes).enumerate index)
    let renamed := renameTransport.valuationEquiv v
    let reordered := reorderTransport.valuationEquiv v
    (coordAssignments _ (uidCoordEquiv renamedContext renamed),
      coordList _ (renamedRead.val.project (uidCoordEquiv renamedContext renamed)),
      coordList _ (reorderedRead.val.project (uidCoordEquiv reorderedContext reordered)),
      renamedProduct (natStore transportSource) renamed)

private def transportFibers :=
  let output := transportStatement.output
  let layout := canonicalLayout
    (transportSource.source.table.declarations.signature output.tensor).axes
  (List.finRange layout.count).map fun index =>
    let p := layout.enumerate index
    let ρ := natStore transportSource
    (transportTerm.collectedBody (r := natRegistry) output ρ p,
      transportTerm.globalFiber output ρ p, renamedFiber ρ p,
      ∑ v : UIDVal reorderedContext,
        if Term.globalDestination output transportTerm
            (reorderTransport.valuationEquiv.symm v) = p then
          transportTerm.globalProduct ρ (reorderTransport.valuationEquiv.symm v) else 0)

def B7 : Bool :=
  transportSource.source.context.axes == [⟨3, 3⟩, ⟨11, 0⟩, ⟨7, 2⟩] &&
  transportTerm.globalContext.axes == [⟨3, 3⟩, ⟨7, 2⟩] &&
  transportTerm.partition.context.axes == [⟨7, 2⟩, ⟨3, 3⟩] &&
  transportTerm.contractedContext.axes == [⟨3, 3⟩] &&
  renamedContext.axes == [⟨15, 3⟩, ⟨7, 2⟩] &&
  transportTerm.partition.bound.map (fun a => { a with uid := scope.renameUID a.uid }) ==
    [⟨15, 3⟩] &&
  renamedRead.val.uids == [7, 15] &&
  renamedDestinationSlots.val.uids == [7] &&
  (renameTransport.equiv ⟨7, by decide⟩).val == 7 &&
  renamedContext.domain (renameTransport.equiv ⟨3, by decide⟩) == 3 &&
  renamedContext.domain (renameTransport.equiv ⟨7, by decide⟩) == 2 &&
  (renameBindersRequested transportTerm.globalContext scope (fun _ => 7)).axes ==
    renamedContext.axes &&
  reorderedContext.axes == [⟨7, 2⟩, ⟨3, 3⟩] &&
  partitionRows ==
    [([0, 0], [0], [0], [0], [0, 0], 1, true),
     ([0, 1], [1], [0], [1], [1, 0], 10, true),
     ([1, 0], [0], [1], [0], [0, 1], 2, true),
     ([1, 1], [1], [1], [1], [1, 1], 25, true),
     ([2, 0], [0], [2], [0], [0, 2], 5, true),
     ([2, 1], [1], [2], [1], [1, 2], 45, true)] &&
  independentPartitionRight &&
  mappedRows ==
    [([(15, 0), (7, 0)], [0, 0], [0, 0], 1),
     ([(15, 0), (7, 1)], [1, 0], [1, 0], 10),
     ([(15, 1), (7, 0)], [0, 1], [0, 1], 2),
     ([(15, 1), (7, 1)], [1, 1], [1, 1], 25),
     ([(15, 2), (7, 0)], [0, 2], [0, 2], 5),
     ([(15, 2), (7, 1)], [1, 2], [1, 2], 45)] &&
  transportFibers == [(some 8, 8, 8, 8), (some 80, 80, 80, 80)]

private def nestedSnapshot : SourceSnapshot :=
  ⟨⟨[.axis i (some 2), .axis k (some 3), .axis e (some 0),
      .tensor "A" [i, k], .tensor "B" [i], .tensor "S" []],
    [.assign "S" []
      (rhs [[.read "A" [.axis i, .axis k], .read "B" [.axis i],
        .read "A" [.axis i, .axis k]]])], {}, ∅⟩,
    [⟨3, .input, [2, 3]⟩, ⟨4, .input, [2]⟩, ⟨5, .output, []⟩],
    [⟨3, [2, 3], [1 / 3, 2 / 3, 5, 10, 25, 45]⟩, ⟨4, [2], [2, 7]⟩]⟩

private def nestedSource : AdmittedSource :=
  (admitSource nestedSnapshot).toOption.get (by decide)

private def nestedStatement : AdmittedStatement nestedSource.source :=
  nestedSource.statements.get ⟨0, by decide⟩

private def nestedTerm :
    Term nestedSource.source.context nestedStatement.output.context
      nestedSource.source.table.declarations :=
  nestedStatement.terms.get ⟨0, by decide⟩

private def reductionBounds {K : Type} {σ : Declarations Unit}
    {r : Registry (fun _ : Unit => K)} :
    {Γ : Type} → Expr (fun _ => K) σ r Γ (.scalar ()) → List Nat
  | _, .reduce n body => n :: reductionBounds body
  | _, .binary _ left right => reductionBounds left ++ reductionBounds right
  | _, _ => []

private theorem nested_correspondence {K : Type} [Semiring K]
    (r : Registry (fun _ : Unit => K))
    (ρ : Store (fun _ => K) nestedSource.source.table.declarations) :
    (∀ x : Coord nestedStatement.output.context.axes,
      interpret semiringOps ρ (nestedTerm.body (r := r) id) x =
        some (∑ v : UIDVal nestedTerm.globalContext,
          if (nestedTerm.partitionCoordEquiv v).1 = x then
            nestedTerm.globalProduct ρ v else 0)) ∧
    (∀ p, nestedTerm.collectedBody (r := r) nestedStatement.output ρ p =
      some (nestedTerm.globalFiber nestedStatement.output ρ p)) ∧
    (∀ (t : (nestedSource.program r).Defined) p,
      (nestedSource.program r).collect semiringOps ρ (nestedSource.total_admEnv ρ) t p =
        nestedSource.globalFiber ρ t.val p) :=
  ⟨fun x => nestedTerm.body_correspondence ρ id x,
    fun p => nestedTerm.collectedBody_correspondence nestedStatement.output ρ p,
    fun t p => nestedSource.collect_correspondence ρ (nestedSource.total_admEnv ρ) t p⟩

private theorem nested_nat :
    (∀ x : Coord nestedStatement.output.context.axes,
      interpret semiringOps (natStore nestedSource) (nestedTerm.body (r := natRegistry) id) x =
        some (∑ v : UIDVal nestedTerm.globalContext,
          if (nestedTerm.partitionCoordEquiv v).1 = x then
            nestedTerm.globalProduct (natStore nestedSource) v else 0)) ∧
    (∀ p, nestedTerm.collectedBody (r := natRegistry) nestedStatement.output
      (natStore nestedSource) p =
        some (nestedTerm.globalFiber nestedStatement.output (natStore nestedSource) p)) ∧
    (∀ (t : (nestedSource.program natRegistry).Defined) p,
      (nestedSource.program natRegistry).collect semiringOps (natStore nestedSource)
        (nestedSource.total_admEnv (natStore nestedSource)) t p =
          nestedSource.globalFiber (natStore nestedSource) t.val p) :=
  nested_correspondence natRegistry (natStore nestedSource)

private theorem nested_rat :
    (∀ x : Coord nestedStatement.output.context.axes,
      interpret semiringOps (ratStore nestedSource)
        (nestedTerm.body (r := RationalReference.registry) id) x =
        some (∑ v : UIDVal nestedTerm.globalContext,
          if (nestedTerm.partitionCoordEquiv v).1 = x then
            nestedTerm.globalProduct (ratStore nestedSource) v else 0)) ∧
    (∀ p, nestedTerm.collectedBody (r := RationalReference.registry) nestedStatement.output
      (ratStore nestedSource) p =
        some (nestedTerm.globalFiber nestedStatement.output (ratStore nestedSource) p)) ∧
    (∀ (t : (nestedSource.program RationalReference.registry).Defined) p,
      (nestedSource.program RationalReference.registry).collect semiringOps (ratStore nestedSource)
        (nestedSource.total_admEnv (ratStore nestedSource)) t p =
          nestedSource.globalFiber (ratStore nestedSource) t.val p) :=
  nested_correspondence RationalReference.registry (ratStore nestedSource)

private def nestedReads :=
  (footprint (nestedTerm.body (r := RationalReference.registry) id) ()).map fun a =>
    ((nestedSource.source.table.entry a.1).declaration,
      coordList (nestedSource.source.table.declarations.signature a.1).axes a.2)

private def swapBounds (a b : Axis) : Coord [b, a] ≃ Coord [a, b] where
  toFun p := (p.2.1, p.1, ())
  invFun p := (p.2.1, p.1, ())
  left_inv p := by rcases p with ⟨x, y, ⟨⟩⟩; rfl
  right_inv p := by rcases p with ⟨x, y, ⟨⟩⟩; rfl

private def reversedNestedBody {K : Type} [Semiring K]
    (r : Registry (fun _ : Unit => K)) :
    Expr (fun _ => K) nestedSource.source.table.declarations r Unit (.scalar ()) :=
  contract [⟨3, 3⟩, ⟨7, 2⟩] nestedTerm.operands
    (fun _ p => nestedTerm.environment () (swapBounds ⟨7, 2⟩ ⟨3, 3⟩ p))

private theorem nested_reordered {K : Type} [Semiring K]
    (r : Registry (fun _ : Unit => K))
    (ρ : Store (fun _ => K) nestedSource.source.table.declarations) :
    interpret semiringOps ρ (reversedNestedBody r) () =
      interpret semiringOps ρ (nestedTerm.body (r := r) id) () :=
  interpret_contract_reindex ρ nestedTerm.partition.bound [⟨3, 3⟩, ⟨7, 2⟩]
    (swapBounds ⟨7, 2⟩ ⟨3, 3⟩) nestedTerm.operands
    (fun x => nestedTerm.environment x) ()

example {K : Type} [Semiring K] {σ : Declarations Unit}
    (r : Registry (fun _ : Unit => K)) (ρ : Store (fun _ => K) σ)
    (reads : List (Read ctx σ)) (env : Unit → Coord [⟨7, 0⟩, ⟨3, 2⟩] → Coord ctx) :
    interpret semiringOps ρ
      (contract (r := r) [⟨3, 2⟩, ⟨7, 0⟩] reads
        (fun x p => env x (swapBounds ⟨7, 0⟩ ⟨3, 2⟩ p))) () =
      interpret semiringOps ρ (contract (r := r) [⟨7, 0⟩, ⟨3, 2⟩] reads env) () :=
  interpret_contract_reindex ρ _ _ (swapBounds ⟨7, 0⟩ ⟨3, 2⟩) reads env ()

example {K : Type} [Semiring K] {σ : Declarations Unit}
    (r : Registry (fun _ : Unit => K)) (ρ : Store (fun _ => K) σ)
    (reads : List (Read ctx σ)) (env : Unit → Coord [] → Coord ctx) :
    interpret semiringOps ρ
      (contract (r := r) [] reads (fun x p => env x ((Equiv.refl (Coord [])) p))) () =
      interpret semiringOps ρ (contract (r := r) [] reads env) () :=
  interpret_contract_reindex ρ [] [] (Equiv.refl _) reads env ()

#guard reductionBounds (reversedNestedBody natRegistry) == [3, 2]
#guard interpret semiringOps (natStore nestedSource)
  (reversedNestedBody natRegistry) () == some 19310
#guard interpret semiringOps (ratStore nestedSource)
  (reversedNestedBody RationalReference.registry) () == some (173710 / 9)

def B8 : Bool :=
  nestedSource.source.context.axes == [⟨7, 2⟩, ⟨3, 3⟩, ⟨11, 0⟩] &&
  nestedTerm.globalContext.axes == [⟨7, 2⟩, ⟨3, 3⟩] &&
  nestedTerm.partition.bound == [⟨7, 2⟩, ⟨3, 3⟩] &&
  nestedTerm.sourceReads.map (fun read =>
    ((nestedSource.source.table.entry read.read.tensor).declaration, read.indices)) ==
      [(3, [7, 3]), (4, [7]), (3, [7, 3])] &&
  ratStore nestedSource
    ⟨(nestedTerm.sourceReads.get ⟨0, by decide⟩).read.tensor, (0, 0, ())⟩ == 1 / 3 &&
  natStore nestedSource
    ⟨(nestedTerm.sourceReads.get ⟨0, by decide⟩).read.tensor, (0, 0, ())⟩ == 1 &&
  reductionBounds (nestedTerm.body (r := natRegistry) id) == [2, 3] &&
  reductionBounds (nestedTerm.body (r := RationalReference.registry) id) == [2, 3] &&
  interpret semiringOps (natStore nestedSource) (nestedTerm.body (r := natRegistry) id) () ==
    some 19310 &&
  interpret semiringOps (ratStore nestedSource)
    (nestedTerm.body (r := RationalReference.registry) id) () == some (173710 / 9) &&
  nestedTerm.collectedBody (r := natRegistry) nestedStatement.output (natStore nestedSource) () ==
    some 19310 &&
  nestedTerm.collectedBody (r := RationalReference.registry) nestedStatement.output
    (ratStore nestedSource) () == some (173710 / 9) &&
  fiberRows natRegistry nestedSource (natStore nestedSource) ==
    [⟨5, "S", [], [19310], [19310]⟩] &&
  fiberRows RationalReference.registry nestedSource (ratStore nestedSource) ==
    [⟨5, "S", [], [173710 / 9], [173710 / 9]⟩] &&
  nestedReads ==
    [(3, [0, 0]), (4, [0]), (3, [0, 0]),
     (3, [0, 1]), (4, [0]), (3, [0, 1]),
     (3, [0, 2]), (4, [0]), (3, [0, 2]),
     (3, [1, 0]), (4, [1]), (3, [1, 0]),
     (3, [1, 1]), (4, [1]), (3, [1, 1]),
     (3, [1, 2]), (4, [1]), (3, [1, 2])]

#guard B7
#guard B8
#eval ("B7", B7, transportFibers)
#eval ("B8", B8, fiberRows natRegistry nestedSource (natStore nestedSource),
  fiberRows RationalReference.registry nestedSource (ratStore nestedSource))
#print axioms slots_transport
#print axioms renamed_fiber
#print axioms partition_left
#print axioms partition_right
#print axioms reenumerated_fiber
#print axioms nested_correspondence
#print axioms nested_nat
#print axioms nested_rat
#print axioms nested_reordered

end SourceCorrespondenceTransportTest

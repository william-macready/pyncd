import IndexedSourceSyntax
import IndexedOperationalHistoryComposition
import IndexedOperationalObservationLaws
import IndexedOperationalAssociativity

namespace IndexedRankedOperationalCore

open LeanNCD.Semantics IndexedSource IndexedWitness
open IndexedComponentComposition IndexedComponentTransport IndexedOpenComposition
open IndexedOperationalHistory IndexedOperationalHistoryComposition

variable {σA σB : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]

def connectingBoundary (A : MatchedComponent σA) (B : MatchedComponent σB)
    (w : Wire (output A) (input B)) : Boundary A B :=
  ⟨w.ports, w.domain⟩

theorem connectingBoundary_wire (A : MatchedComponent σA) (B : MatchedComponent σB)
    (w : Wire (output A) (input B)) :
    boundaryWire A B (connectingBoundary A B w) = w := by cases w; rfl

theorem connectingBoundary_boundary (A : MatchedComponent σA) (B : MatchedComponent σB)
    (b : Boundary A B) :
    connectingBoundary A B (boundaryWire A B b) = b := by cases b; rfl

theorem connectingBoundary_domain (A : MatchedComponent σA) (B : MatchedComponent σB)
    (w : Wire (output A) (input B)) (i) :
    (connectingBoundary A B w).domain i = w.domain i := rfl

theorem connectingBoundary_env (A : MatchedComponent σA) (B : MatchedComponent σB)
    (w : Wire (output A) (input B)) :
    boundaryEnvEquiv A B (connectingBoundary A B w) = w.env := rfl

def boundaryEquiv (A : MatchedComponent σA) (B : MatchedComponent σB) :
    Boundary A B ≃ Wire (output A) (input B) where
  toFun := boundaryWire A B
  invFun := connectingBoundary A B
  left_inv := connectingBoundary_boundary A B
  right_inv := connectingBoundary_wire A B

theorem domain_comp_id {x y : Shape} (d : Domain x y) :
    d.comp (Domain.id y) = d := by cases d; rfl

theorem domain_id_comp {x y : Shape} (d : Domain x y) :
    (Domain.id x).comp d = d := by cases d; rfl

theorem wire_ext {X Y : Object} (a b : Wire X Y)
    (ports : a.ports = b.ports) (domains : HEq a.domain b.domain) : a = b := by
  cases a
  cases b
  cases ports
  cases domains
  rfl

theorem domain_ext {x y : Shape} (a b : Domain x y)
    (axes : a.axes = b.axes) (coord : a.coord = b.coord) (raw : a.raw = b.raw) :
    a = b := by
  cases a
  cases b
  cases axes
  cases coord
  cases raw
  rfl

theorem wire_comp_id {X Y : Object} (w : Wire X Y) :
    w.comp (Wire.identity Y) = w := by cases w; rfl

theorem wire_id_comp {X Y : Object} (w : Wire X Y) :
    (Wire.identity X).comp w = w := by cases w; rfl

theorem wire_assoc {W X Y Z : Object} (a : Wire W X) (b : Wire X Y) (c : Wire Y Z) :
    (a.comp b).comp c = a.comp (b.comp c) := by cases a; cases b; cases c; rfl

theorem domain_inverse_comp {x y : Shape} (d : Domain x y) :
    d.inverse.comp d = Domain.id y := by
  apply domain_ext
  · exact Equiv.symm_trans_self _
  · exact Equiv.symm_trans_self _
  · exact Equiv.symm_trans_self _

theorem domain_comp_inverse {x y : Shape} (d : Domain x y) :
    d.comp d.inverse = Domain.id x := by
  apply domain_ext
  · exact Equiv.self_trans_symm _
  · exact Equiv.self_trans_symm _
  · exact Equiv.self_trans_symm _

theorem wire_ext_pointwise {X Y : Object} (a b : Wire X Y)
    (ports : a.ports = b.ports) (domains : ∀ t, HEq (a.domain t) (b.domain t)) :
    a = b := by
  cases a
  cases b
  cases ports
  apply wire_ext
  · rfl
  · apply heq_of_eq
    funext t
    exact eq_of_heq (domains t)

theorem domain_comp_inverseAt {X Y : Object} (w : Wire X Y)
    (t s : Y.interface.Tensor) (same : s = t) (h : w.ports s = w.ports t) :
    HEq ((w.domain t).comp (w.inverseAt s (w.ports t) h))
      (Domain.id (Y.interface.signature t).axes) := by
  subst s
  exact heq_of_eq (domain_comp_inverse (w.domain t))

theorem domain_inverseAt_comp {X Y : Object} (w : Wire X Y)
    (s : Y.interface.Tensor) (t : X.interface.Tensor) (h : w.ports s = t) :
    HEq ((w.inverseAt s t h).comp (w.domain s))
      (Domain.id (X.interface.signature t).axes) := by
  subst t
  exact heq_of_eq (domain_inverse_comp (w.domain s))

theorem wire_inverse_comp {X Y : Object} (w : Wire X Y) :
    w.inverse.comp w = Wire.identity Y := by
  apply wire_ext_pointwise
  · exact Equiv.self_trans_symm _
  · intro t
    exact domain_comp_inverseAt w t _ (w.ports.symm_apply_apply t) _

theorem wire_comp_inverse {X Y : Object} (w : Wire X Y) :
    w.comp w.inverse = Wire.identity X := by
  apply wire_ext_pointwise
  · exact Equiv.symm_trans_self _
  · intro t
    exact domain_inverseAt_comp w _ t _

theorem wire_inverse_unique {X Y : Object} (f : Wire X Y) (a b : Wire Y X)
    (right : f.comp a = Wire.identity X) (left : b.comp f = Wire.identity Y) :
    a = b := by
  calc
    a = (Wire.identity Y).comp a := (wire_id_comp a).symm
    _ = (b.comp f).comp a := congrArg (fun w => w.comp a) left.symm
    _ = b.comp (f.comp a) := wire_assoc b f a
    _ = b := by rw [right, wire_comp_id]

theorem wire_inverse_inverse {X Y : Object} (w : Wire X Y) :
    w.inverse.inverse = w :=
  wire_inverse_unique w.inverse _ _ (wire_comp_inverse _) (wire_comp_inverse _)

theorem wire_inverse_identity (X : Object) :
    (Wire.identity X).inverse = Wire.identity X :=
  wire_inverse_unique (Wire.identity X) _ _ (wire_comp_inverse _)
    (wire_comp_id _)

theorem wire_inverse_composite {X Y Z : Object} (a : Wire X Y) (b : Wire Y Z) :
    (a.comp b).inverse = b.inverse.comp a.inverse := by
  apply wire_inverse_unique (a.comp b) _ _ (wire_comp_inverse _)
  calc
    (b.inverse.comp a.inverse).comp (a.comp b) =
        b.inverse.comp ((a.inverse.comp a).comp b) := by simp only [wire_assoc]
    _ = Wire.identity Z := by
      rw [wire_inverse_comp, wire_id_comp, wire_inverse_comp]

def wireReindex {X Y X' Y' : Object} (left : Wire X' X) (right : Wire Y Y') :
    Wire X Y ≃ Wire X' Y' where
  toFun := fun w => (left.comp w).comp right
  invFun := fun w => (left.inverse.comp w).comp right.inverse
  left_inv := by
    intro w
    calc
      (left.inverse.comp ((left.comp w).comp right)).comp right.inverse =
          (left.inverse.comp left).comp (w.comp (right.comp right.inverse)) := by
            simp only [wire_assoc]
      _ = w := by rw [wire_inverse_comp, wire_comp_inverse, wire_id_comp, wire_comp_id]
  right_inv := by
    intro w
    calc
      (left.comp ((left.inverse.comp w).comp right.inverse)).comp right =
          (left.comp left.inverse).comp (w.comp (right.inverse.comp right)) := by
            simp only [wire_assoc]
      _ = w := by rw [wire_comp_inverse, wire_inverse_comp, wire_id_comp, wire_comp_id]

theorem wireReindex_identity (X Y : Object) :
    wireReindex (Wire.identity X) (Wire.identity Y) = Equiv.refl (Wire X Y) := by
  ext w
  rfl

theorem wireReindex_comp {X Y X' Y' X'' Y'' : Object}
    (l : Wire X' X) (r : Wire Y Y')
    (l' : Wire X'' X') (r' : Wire Y' Y'') :
    (wireReindex l r).trans (wireReindex l' r') =
      wireReindex (l'.comp l) (r.comp r') := by
  ext w
  rfl

noncomputable def boundaryReindex
    {σA' σB' : Declarations Unit}
    [Fintype σA'.Tensor] [DecidableEq σA'.Tensor]
    [Fintype σB'.Tensor] [DecidableEq σB'.Tensor]
    (A : MatchedComponent σA) (B : MatchedComponent σB)
    (A' : MatchedComponent σA') (B' : MatchedComponent σB')
    (left : Wire (output A') (output A)) (right : Wire (input B) (input B')) :
    Boundary A B ≃ Boundary A' B' :=
  (boundaryEquiv A B).trans ((wireReindex left right).trans (boundaryEquiv A' B').symm)

section Squares

variable {σC : Declarations Unit} [Fintype σC.Tensor] [DecidableEq σC.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB) (C : MatchedComponent σC)
variable (ab : Boundary A B) (bc : Boundary B C)

theorem left_square_full :
    boundaryWire (compose A B ab) C (leftNestedBoundary A B C ab bc) =
      (outputWire A B ab).comp (boundaryWire B C bc) := by
  apply wire_ext
  · rfl
  · apply heq_of_eq
    funext i
    exact (domain_comp_id (bc.domain i)).symm

theorem right_square_full :
    boundaryWire A (compose B C bc) (rightNestedBoundary A B C ab bc) =
      (boundaryWire A B ab).comp (inputWire B C bc) := by
  apply wire_ext
  · rfl
  · apply heq_of_eq
    funext i
    rcases i with ⟨t, h⟩
    cases t with
    | inl t => exact (domain_id_comp (ab.domain ⟨t, h⟩)).symm
    | inr t => cases h

noncomputable def leftBoundaryEquiv : Boundary B C ≃ Boundary (compose A B ab) C :=
  boundaryReindex B C (compose A B ab) C (outputWire A B ab) (Wire.identity _)

noncomputable def rightBoundaryEquiv : Boundary A B ≃ Boundary A (compose B C bc) :=
  boundaryReindex A B A (compose B C bc) (Wire.identity _) (inputWire B C bc)

theorem leftBoundaryEquiv_apply :
    leftBoundaryEquiv A B C ab bc = leftNestedBoundary A B C ab bc := by
  apply (boundaryEquiv (compose A B ab) C).injective
  change ((outputWire A B ab).comp (boundaryWire B C bc)).comp (Wire.identity _) = _
  rw [wire_comp_id]
  exact (left_square_full A B C ab bc).symm

theorem rightBoundaryEquiv_apply :
    rightBoundaryEquiv A B C bc ab = rightNestedBoundary A B C ab bc := by
  apply (boundaryEquiv A (compose B C bc)).injective
  change ((Wire.identity _).comp (boundaryWire A B ab)).comp (inputWire B C bc) = _
  rw [wire_id_comp]
  exact (right_square_full A B C ab bc).symm

theorem leftBoundaryEquiv_recover :
    (leftBoundaryEquiv A B C ab).symm (leftNestedBoundary A B C ab bc) = bc := by
  rw [← leftBoundaryEquiv_apply]
  exact (leftBoundaryEquiv A B C ab).symm_apply_apply bc

theorem rightBoundaryEquiv_recover :
    (rightBoundaryEquiv A B C bc).symm (rightNestedBoundary A B C ab bc) = ab := by
  rw [← rightBoundaryEquiv_apply]
  exact (rightBoundaryEquiv A B C bc).symm_apply_apply ab

end Squares

/-- Opaque compiled components do not acquire a fictional internal assembly history. -/
inductive Origin : {σ : Declarations Unit} →
    [Fintype σ.Tensor] → [DecidableEq σ.Tensor] → MatchedComponent σ → Type 1
  | opaque {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
      (A : MatchedComponent σ) (ranked : Nonempty A.program.RankCertificate) : Origin A
  | joined {σ τ : Declarations Unit}
      [Fintype σ.Tensor] [DecidableEq σ.Tensor]
      [Fintype τ.Tensor] [DecidableEq τ.Tensor]
      (A : MatchedComponent σ) (B : MatchedComponent τ) (b : Boundary A B)
      (left : Origin A) (right : Origin B) : Origin (compose A B b)

inductive Normal : Object → Object → Type 1
  | admin {X Y} (wire : Wire X Y) : Normal X Y
  | compute {X Y} {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
      (component : MatchedComponent σ) (rank : component.program.RankCertificate)
      (origin : Origin component)
      (before : Wire X (input component)) (after : Wire (output component) Y) :
      Normal X Y

noncomputable def Normal.comp {X Y Z : Object} : Normal X Y → Normal Y Z → Normal X Z
  | .admin a, .admin b => .admin (a.comp b)
  | .admin a, @Normal.compute _ _ σ _ _ B rB origin before after =>
      .compute (σ := σ) B rB origin (a.comp before) after
  | @Normal.compute _ _ σ _ _ A rA origin before after, .admin b =>
      .compute (σ := σ) A rA origin before (after.comp b)
  | @Normal.compute _ _ _ _ _ A rA originA beforeA afterA,
      @Normal.compute _ _ _ _ _ B rB originB beforeB afterB =>
      let b := connectingBoundary A B (afterA.comp beforeB)
      .compute (σ := declarations A B) (compose A B b)
        (compositeRankCertificate A B b rA rB) (.joined A B b originA originB)
        (beforeA.comp (inputWire A B b)) ((outputWire A B b).comp afterB)

noncomputable def Normal.identity (X : Object) : Normal X X :=
  .admin (Wire.identity X)

noncomputable def Normal.leaf (A : MatchedComponent σA)
    (rank : A.program.RankCertificate) : Normal (input A) (output A) :=
  .compute A rank (.opaque A ⟨rank⟩) (Wire.identity _) (Wire.identity _)

theorem Normal.identity_comp {X Y : Object} (f : Normal X Y) :
    (Normal.identity X).comp f = f := by cases f <;> rfl

theorem Normal.comp_identity {X Y : Object} (f : Normal X Y) :
    f.comp (Normal.identity Y) = f := by cases f <;> rfl

theorem Normal.admin_slide {W X Y Z : Object}
    (A : MatchedComponent σA) (B : MatchedComponent σB)
    (rA : A.program.RankCertificate) (rB : B.program.RankCertificate)
    (oa : Origin A) (ob : Origin B)
    (beforeA : Wire W (input A)) (afterA : Wire (output A) X)
    (w : Wire X Y)
    (beforeB : Wire Y (input B)) (afterB : Wire (output B) Z) :
    ((Normal.compute A rA oa beforeA afterA).comp (.admin w)).comp
        (.compute B rB ob beforeB afterB) =
      (Normal.compute A rA oa beforeA afterA).comp
        ((Normal.admin w).comp (.compute B rB ob beforeB afterB)) := rfl

theorem Normal.admin_cancel_right {X Y Z : Object} (f : Normal X Y) (w : Wire Y Z) :
    (f.comp (.admin w)).comp (.admin w.inverse) = f := by
  cases f with
  | admin a =>
      change Normal.admin ((a.comp w).comp w.inverse) = Normal.admin a
      rw [wire_assoc, wire_comp_inverse, wire_comp_id]
  | compute A rank origin before after =>
      change Normal.compute A rank origin before ((after.comp w).comp w.inverse) =
        Normal.compute A rank origin before after
      rw [wire_assoc, wire_comp_inverse, wire_comp_id]

theorem Normal.admin_cancel_left {X Y Z : Object} (w : Wire Z X) (f : Normal X Y) :
    (Normal.admin w.inverse).comp ((Normal.admin w).comp f) = f := by
  cases f with
  | admin a =>
      change Normal.admin (w.inverse.comp (w.comp a)) = Normal.admin a
      rw [← wire_assoc, wire_inverse_comp, wire_id_comp]
  | compute A rank origin before after =>
      change Normal.compute A rank origin (w.inverse.comp (w.comp before)) after =
        Normal.compute A rank origin before after
      rw [← wire_assoc, wire_inverse_comp, wire_id_comp]

noncomputable def Normal.source : {X Y : Object} → Normal X Y → Term X Y
  | _, _, .admin w => .wire w
  | _, _, @Normal.compute _ _ _ _ _ A _ _ before after =>
      .seq (.wire before) (.seq (.leaf A) (.wire after))

theorem Normal.source_rank_independent {X Y : Object} (A : MatchedComponent σA)
    (r s : A.program.RankCertificate)
    (origin : Origin A) (before : Wire X (input A)) (after : Wire (output A) Y) :
    (Normal.compute A r origin before after).source =
      (Normal.compute A s origin before after).source := rfl

noncomputable def actualHistory (A : MatchedComponent σA)
    (η : A.program.Input) (rank : A.program.RankCertificate) : GraphHistory σA :=
  Classical.choose (GraphHistory.ranked_default_exists A η rank)

theorem actualHistory_spec (A : MatchedComponent σA)
    (η : A.program.Input) (rank : A.program.RankCertificate) :
    (actualHistory A η rank).Admissible ∧
      (actualHistory A η rank).toRun = runChecked A.contract A.fragment η.val ∧
      (actualHistory A η rank).start = initial η.val :=
  Classical.choose_spec (GraphHistory.ranked_default_exists A η rank)

theorem actualHistory_rank_independent (A : MatchedComponent σA)
    (η : A.program.Input) (r s : A.program.RankCertificate) :
    actualHistory A η r = actualHistory A η s :=
  GraphHistory.toRun_injective
    ((actualHistory_spec A η r).2.1.trans (actualHistory_spec A η s).2.1.symm)

theorem actual_binary (A : MatchedComponent σA) (B : MatchedComponent σB)
    (w : Wire (output A) (input B)) (η : A.program.Input)
    (rA : A.program.RankCertificate) (rB : B.program.RankCertificate) :
    BinaryHistory A B (connectingBoundary A B w) (actualHistory A η rA)
      (actualHistory (compose A B (connectingBoundary A B w))
        (liftInput A B (connectingBoundary A B w) η)
        (compositeRankCertificate A B (connectingBoundary A B w) rA rB)) := by
  obtain ⟨h, binary, run⟩ := compose_history A B (connectingBoundary A B w) η rA rB
    (actualHistory A η rA) (actualHistory_spec A η rA).2.1
  have eq := GraphHistory.toRun_injective
    (run.trans (actualHistory_spec _ _
      (compositeRankCertificate A B (connectingBoundary A B w) rA rB)).2.1.symm)
  exact eq ▸ binary

def Origin.Adapters : {σ : Declarations Unit} →
    [Fintype σ.Tensor] → [DecidableEq σ.Tensor] →
    {A : MatchedComponent σ} → Origin A → Type
  | _, _, _, _, @Origin.opaque _ _ _ _ _ => Unit
  | _, _, _, _, @Origin.joined _ _ _ _ _ _ A B _ left right =>
      left.Adapters × Boundary A B × right.Adapters

def Origin.adapters : {σ : Declarations Unit} →
    [Fintype σ.Tensor] → [DecidableEq σ.Tensor] →
    {A : MatchedComponent σ} → (o : Origin A) → o.Adapters
  | _, _, _, _, @Origin.opaque _ _ _ _ _ => ()
  | _, _, _, _, @Origin.joined _ _ _ _ _ _ _ _ b left right =>
      (left.adapters, b, right.adapters)

theorem Origin.ranked : {σ : Declarations Unit} →
    [Fintype σ.Tensor] → [DecidableEq σ.Tensor] →
    {A : MatchedComponent σ} → Origin A → Nonempty A.program.RankCertificate
  | _, _, _, _, @Origin.opaque _ _ _ _ ranked => ranked
  | _, _, _, _, @Origin.joined _ _ _ _ _ _ A B b left right => by
      obtain ⟨rA⟩ := left.ranked
      obtain ⟨rB⟩ := right.ranked
      exact ⟨compositeRankCertificate A B b rA rB⟩

def Origin.metadata {A : MatchedComponent σA} (o : Origin A)
    (η : A.program.Input) : GraphMetadata σA o.Adapters :=
  GraphMetadata.ofComponent A η o.adapters

noncomputable def actualObservation (A : MatchedComponent σA) (o : Origin A)
    (η : A.program.Input) (rank : A.program.RankCertificate) :
    CompleteObservation σA o.Adapters :=
  ⟨o.metadata η, actualHistory A η rank, (actualHistory_spec A η rank).1⟩

theorem actualObservation_rank_independent (A : MatchedComponent σA) (o : Origin A)
    (η : A.program.Input) (r s : A.program.RankCertificate) :
    actualObservation A o η r = actualObservation A o η s := by
  simp only [actualObservation, actualHistory_rank_independent A η r s]

theorem joined_metadata_adapter (A : MatchedComponent σA) (B : MatchedComponent σB)
    (b : Boundary A B) (left : Origin A) (right : Origin B)
    (η : (compose A B b).program.Input) :
    ((Origin.joined A B b left right).metadata η).adapters =
      (left.adapters, b, right.adapters) := rfl

theorem opaque_metadata_adapter (A : MatchedComponent σA)
    (ranked : Nonempty A.program.RankCertificate) (η : A.program.Input) :
    ((Origin.opaque A ranked).metadata η).adapters = () := rfl

section Provenance

variable {σC : Declarations Unit} [Fintype σC.Tensor] [DecidableEq σC.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB) (C : MatchedComponent σC)
variable (ab : Boundary A B) (bc : Boundary B C)
variable (oa : Origin A) (ob : Origin B) (oc : Origin C)

noncomputable def leftOrigin : Origin (leftBracket A B C ab bc) :=
  .joined (compose A B ab) C (leftNestedBoundary A B C ab bc)
    (.joined A B ab oa ob) oc

noncomputable def rightOrigin : Origin (rightBracket A B C ab bc) :=
  .joined A (compose B C bc) (rightNestedBoundary A B C ab bc)
    oa (.joined B C bc ob oc)

noncomputable def nestedAdapterEquiv :
    (leftOrigin A B C ab bc oa ob oc).Adapters ≃
      (rightOrigin A B C ab bc oa ob oc).Adapters where
  toFun := fun x =>
    (x.1.1, rightBoundaryEquiv A B C bc x.1.2.1,
      (x.1.2.2, (leftBoundaryEquiv A B C ab).symm x.2.1, x.2.2))
  invFun := fun y =>
    ((y.1, (rightBoundaryEquiv A B C bc).symm y.2.1, y.2.2.1),
      leftBoundaryEquiv A B C ab y.2.2.2.1, y.2.2.2.2)
  left_inv := by
    rintro ⟨⟨a, b, c⟩, d, e⟩
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv := by
    rintro ⟨a, b, c, d, e⟩
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem nestedAdapterEquiv_actual :
    nestedAdapterEquiv A B C ab bc oa ob oc
        (leftOrigin A B C ab bc oa ob oc).adapters =
      (rightOrigin A B C ab bc oa ob oc).adapters := by
  change (oa.adapters, rightBoundaryEquiv A B C bc ab,
    (ob.adapters,
      (leftBoundaryEquiv A B C ab).symm (leftNestedBoundary A B C ab bc),
      oc.adapters)) = _
  rw [rightBoundaryEquiv_apply, leftBoundaryEquiv_recover]
  rfl

theorem nestedAdapterEquiv_originals
    (x : (leftOrigin A B C ab bc oa ob oc).Adapters) :
    ((rightBoundaryEquiv A B C bc).symm
        (nestedAdapterEquiv A B C ab bc oa ob oc x).2.1,
      (nestedAdapterEquiv A B C ab bc oa ob oc x).2.2.2.1) =
      (x.1.2.1, (leftBoundaryEquiv A B C ab).symm x.2.1) := by
  exact congrArg (fun b => (b, (leftBoundaryEquiv A B C ab).symm x.2.1))
    ((rightBoundaryEquiv A B C bc).symm_apply_apply x.1.2.1)

theorem leftOrigin_originals :
    ((leftOrigin A B C ab bc oa ob oc).adapters.1.2.1,
      (leftBoundaryEquiv A B C ab).symm
        (leftOrigin A B C ab bc oa ob oc).adapters.2.1) = (ab, bc) := by
  change (ab, (leftBoundaryEquiv A B C ab).symm (leftNestedBoundary A B C ab bc)) = _
  rw [leftBoundaryEquiv_recover]

theorem rightOrigin_originals :
    ((rightBoundaryEquiv A B C bc).symm
        (rightOrigin A B C ab bc oa ob oc).adapters.2.1,
      (rightOrigin A B C ab bc oa ob oc).adapters.2.2.2.1) = (ab, bc) := by
  change ((rightBoundaryEquiv A B C bc).symm (rightNestedBoundary A B C ab bc), bc) = _
  rw [rightBoundaryEquiv_recover]

theorem nestedOrigin_metadata (η : A.program.Input) :
    (IndexedOperationalAssociativity.metadataTransport A B C ab bc).Agrees
      (nestedAdapterEquiv A B C ab bc oa ob oc)
      ((leftOrigin A B C ab bc oa ob oc).metadata
        (liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc)
          (liftInput A B ab η)))
      ((rightOrigin A B C ab bc oa ob oc).metadata
        (liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η)) := by
  have native := IndexedOperationalAssociativity.nested_metadata A B C ab bc η
  exact ⟨native.1, native.2.1, native.2.2.1, native.2.2.2.1,
    (nestedAdapterEquiv_actual A B C ab bc oa ob oc).symm⟩

end Provenance

theorem no_unit_boundary_equiv (A : MatchedComponent σA) (B : MatchedComponent σB)
    (b c : Boundary A B) (distinct : b ≠ c) :
    ¬ Nonempty (Unit ≃ Boundary A B) := by
  rintro ⟨e⟩
  have h : e.symm b = e.symm c := Subsingleton.elim _ _
  exact distinct (e.symm.injective h)

theorem origin_opaque_ne_joined (A : MatchedComponent σA) (B : MatchedComponent σB)
    (b : Boundary A B) (left : Origin A) (right : Origin B) :
    ∀ ranked, Origin.opaque (compose A B b) ranked ≠ Origin.joined A B b left right := by
  intro ranked h
  cases h

section Scope

variable {σ τ ρ ω : Declarations Unit}

/-- These are structural map squares, not assumptions that composite executions agree. -/
theorem history_map_square
    (leafTransport : GraphTransport σ τ) (ambient : GraphTransport ρ ω)
    (leftState : State σ → State ρ) (rightState : State τ → State ω)
    (leftEvent : Event σ → Event ρ) (rightEvent : Event τ → Event ω)
    (leftId rightId : Nat → Nat)
    (states : ∀ s, ambient.mapState (leftState s) = rightState (leafTransport.mapState s))
    (events : ∀ e, ambient.mapEvent (leftEvent e) = rightEvent (leafTransport.mapEvent e))
    (identities : ∀ n, ambient.identity (leftId n) = rightId (leafTransport.identity n))
    (h : GraphHistory σ) :
    ambient.history.apply (h.map leftState leftEvent leftId id) =
      (leafTransport.history.apply h).map rightState rightEvent rightId id := by
  induction h with
  | done s a => exact congrArg (fun s => History.done s a) (states s)
  | step s e h ih =>
      simp only [Transport.apply] at ih
      change History.step (ambient.mapState (leftState s))
        (ambient.mapEvent (leftEvent e)) _ = History.step _ _ _
      rw [states, events, ih]
      rfl
  | failed s e f =>
      change History.failed (ambient.mapState (leftState s))
        (ambient.mapEvent (leftEvent e)) (ambient.identity (leftId f)) =
          History.failed _ _ _
      rw [states, events, identities]
      rfl

theorem observation_lift_congr {Adapters Other : Type*}
    (leafTransport : MetadataTransport σ τ) (adapters : Adapters ≃ Other)
    (ambient : GraphTransport ρ ω)
    (x : CompleteObservation σ Adapters) (y : CompleteObservation τ Other)
    (agree : CompleteObservation.Agrees leafTransport adapters x y)
    (leftState : State σ → State ρ) (rightState : State τ → State ω)
    (leftEvent : Event σ → Event ρ) (rightEvent : Event τ → Event ω)
    (leftId rightId : Nat → Nat)
    (states : ∀ s, ambient.mapState (leftState s) = rightState (leafTransport.mapState s))
    (events : ∀ e, ambient.mapEvent (leftEvent e) = rightEvent (leafTransport.mapEvent e))
    (identities : ∀ n, ambient.identity (leftId n) = rightId (leafTransport.identity n)) :
    y.history.map rightState rightEvent rightId id =
      ambient.history.apply (x.history.map leftState leftEvent leftId id) := by
  rw [agree.2]
  exact (history_map_square leafTransport.toGraphTransport ambient leftState rightState
    leftEvent rightEvent leftId rightId states events identities x.history).symm

theorem append_transport (t : GraphTransport σ τ) (h k : GraphHistory σ) :
    t.history.apply (SharedSplice.append h k) =
      SharedSplice.append (t.history.apply h) (t.history.apply k) := by
  exact History.map_bind h _ _ _ _ _ (fun _ _ => k)
    (fun _ _ => t.history.apply k) (fun _ _ => rfl)

theorem lifted_append_congr (t : GraphTransport σ τ)
    (h k : GraphHistory σ) (h' k' : GraphHistory τ)
    (prefixEq : h' = t.history.apply h) (suffixEq : k' = t.history.apply k) :
    SharedSplice.append h' k' = t.history.apply (SharedSplice.append h k) := by
  rw [prefixEq, suffixEq, append_transport]

theorem observation_shape_does_not_assert_start
    (A : MatchedComponent σA) (η : A.program.Input) (s : State σA)
    (different : s ≠ initial η.val) :
    ∃ x : CompleteObservation σA Unit,
      x.metadata = GraphMetadata.ofComponent A η () ∧
      x.Agrees (MetadataTransport.refl σA) (Equiv.refl Unit) x ∧
      x.history.start ≠ initial η.val := by
  let x : CompleteObservation σA Unit :=
    ⟨GraphMetadata.ofComponent A η (), .done s (), .done s⟩
  exact ⟨x, rfl, x.agrees_refl, different⟩

end Scope

#print axioms connectingBoundary_wire
#print axioms left_square_full
#print axioms right_square_full
#print axioms Normal.comp
#print axioms Origin.ranked
#print axioms actualHistory_rank_independent
#print axioms actual_binary
#print axioms actualObservation_rank_independent
#print axioms no_unit_boundary_equiv
#print axioms observation_lift_congr
#print axioms append_transport
#print axioms observation_shape_does_not_assert_start
#print axioms wire_comp_id
#print axioms wire_id_comp
#print axioms wire_assoc
#print axioms wire_inverse_comp
#print axioms wire_comp_inverse
#print axioms wire_inverse_inverse
#print axioms wire_inverse_identity
#print axioms wire_inverse_composite
#print axioms wireReindex
#print axioms wireReindex_comp
#print axioms boundaryReindex
#print axioms leftBoundaryEquiv_recover
#print axioms rightBoundaryEquiv_recover
#print axioms nestedAdapterEquiv
#print axioms nestedAdapterEquiv_actual
#print axioms nestedAdapterEquiv_originals
#print axioms nestedOrigin_metadata
#print axioms Normal.admin_slide
#print axioms Normal.admin_cancel_left
#print axioms Normal.admin_cancel_right

end IndexedRankedOperationalCore

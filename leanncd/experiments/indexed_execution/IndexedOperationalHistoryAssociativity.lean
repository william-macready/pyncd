import IndexedOperationalHistoryComposition
import IndexedOperationalAssociativity
import IndexedOperationalRunsPhases

namespace IndexedOperationalHistoryAssociativity

open LeanNCD.Semantics LeanNCD.Semantics.Program
open IndexedOpenComposition IndexedComponentComposition IndexedComponentExecution
open IndexedComponentTransport IndexedWitness IndexedOperationalReassociation
open IndexedOperationalHistory IndexedOperationalHistoryComposition
open IndexedOperationalAssociativity

variable {σA σB σC : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable [Fintype σC.Tensor] [DecidableEq σC.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB) (C : MatchedComponent σC)
variable (ab : Boundary A B) (bc : Boundary B C)

abbrev L := declarations (compose A B ab) C
abbrev R := declarations A (compose B C bc)

theorem state_A (a : State σA) :
    (graphTransport A B C ab bc).mapState
      (upstreamState (compose A B ab) C (upstreamState A B a)) =
      upstreamState A (compose B C bc) a := by
  have available : ((graphTransport A B C ab bc).mapState
      (upstreamState (compose A B ab) C (upstreamState A B a))).available =
      (upstreamState A (compose B C bc) a).available := by
    funext x
    rcases x with ⟨t | ⟨t | t, h⟩, p⟩ <;> rfl
  apply congrArg₂ State.mk available
  simp [graphTransport, upstreamState, mapLedger,
    List.map_map, Function.comp_def, identity_A]

theorem state_B (a : State σA) (b : State σB) :
    (graphTransport A B C ab bc).mapState
      (upstreamState (compose A B ab) C (downstreamState A B a b)) =
      downstreamState A (compose B C bc) a (upstreamState B C b) := by
  have available : ((graphTransport A B C ab bc).mapState
      (upstreamState (compose A B ab) C (downstreamState A B a b))).available =
      (downstreamState A (compose B C bc) a (upstreamState B C b)).available := by
    funext x
    rcases x with ⟨t | ⟨t | t, h⟩, p⟩ <;> rfl
  apply congrArg₂ State.mk available
  simp [graphTransport, upstreamState, downstreamState,
    mapLedger, List.map_append, List.map_map, Function.comp_def, identity_A, identity_B]

theorem state_C (a : State σA) (b : State σB) (c : State σC) :
    (graphTransport A B C ab bc).mapState
      (downstreamState (compose A B ab) C (downstreamState A B a b) c) =
      downstreamState A (compose B C bc) a (downstreamState B C b c) := by
  have available : ((graphTransport A B C ab bc).mapState
      (downstreamState (compose A B ab) C (downstreamState A B a b) c)).available =
      (downstreamState A (compose B C bc) a (downstreamState B C b c)).available := by
    funext x
    rcases x with ⟨t | ⟨t | t, h⟩, p⟩ <;> rfl
  apply congrArg₂ State.mk available
  simp [graphTransport, downstreamState, mapLedger,
    List.map_append, List.map_map, Function.comp_def, identity_A, identity_B,
    identity_C, List.append_assoc]

theorem event_A (e : Event σA) :
    (graphTransport A B C ab bc).mapEvent
      (mapEvent (upstream (compose A B ab) C) upstreamId
        (mapEvent (upstream A B) upstreamId e)) =
      mapEvent (upstream A (compose B C bc)) upstreamId e := by
  cases e <;> simp [GraphTransport.mapEvent, graphTransport, mapEvent, identity_A, address_A]

theorem event_B (e : Event σB) :
    (graphTransport A B C ab bc).mapEvent
      (mapEvent (upstream (compose A B ab) C) upstreamId
        (mapEvent (downstream A B ab) downstreamId e)) =
      mapEvent (downstream A (compose B C bc) (rightNestedBoundary A B C ab bc)) downstreamId
        (mapEvent (upstream B C) upstreamId e) := by
  cases e <;> simp [GraphTransport.mapEvent, graphTransport, mapEvent, identity_B, address_B]

theorem event_C (e : Event σC) :
    (graphTransport A B C ab bc).mapEvent
      (mapEvent (downstream (compose A B ab) C (leftNestedBoundary A B C ab bc)) downstreamId e) =
      mapEvent (downstream A (compose B C bc) (rightNestedBoundary A B C ab bc)) downstreamId
        (mapEvent (downstream B C bc) downstreamId e) := by
  cases e <;> simp [GraphTransport.mapEvent, graphTransport, mapEvent, identity_C, address_C]

theorem map_append {S E F T D G : Type*} (h k : History S E F Unit)
    (s : S → T) (e : E → D) (f : F → G) :
    (SharedSplice.append h k).map s e f id =
      SharedSplice.append (h.map s e f id) (k.map s e f id) := by
  induction h <;> simp_all [SharedSplice.append, History.bind, History.map]

theorem map_ext {S E F T D G : Type*} (h : History S E F Unit)
    (s t : S → T) (e d : E → D) (f g : F → G)
    (hs : ∀ x, s x = t x) (he : ∀ x, e x = d x) (hf : ∀ x, f x = g x) :
    h.map s e f id = h.map t d g id := by
  induction h <;> simp_all [History.map]

def leafA (h : GraphHistory σA) : GraphHistory (R A B C bc) :=
  liftUpstream A (compose B C bc) h

def leafB (a : State σA) (h : GraphHistory σB) : GraphHistory (R A B C bc) :=
  liftDownstream A (compose B C bc) (rightNestedBoundary A B C ab bc) a
    (liftUpstream B C h)

def leafC (a : State σA) (b : State σB) (h : GraphHistory σC) :
    GraphHistory (R A B C bc) :=
  liftDownstream A (compose B C bc) (rightNestedBoundary A B C ab bc) a
    (liftDownstream B C bc b h)

theorem lift_A (h : GraphHistory σA) :
    (graphTransport A B C ab bc).history.apply
      (liftUpstream (compose A B ab) C (liftUpstream A B h)) =
      leafA A B C bc h := by
  simp only [Transport.apply, GraphTransport.history, liftUpstream, History.map_comp, leafA]
  apply map_ext
  · exact state_A A B C ab bc
  · exact event_A A B C ab bc
  · exact identity_A

theorem lift_B (a : State σA) (h : GraphHistory σB) :
    (graphTransport A B C ab bc).history.apply
      (liftUpstream (compose A B ab) C (liftDownstream A B ab a h)) =
      leafB A B C ab bc a h := by
  simp only [Transport.apply, GraphTransport.history, liftUpstream, liftDownstream,
    History.map_comp, leafB]
  apply map_ext
  · exact state_B A B C ab bc a
  · exact event_B A B C ab bc
  · exact identity_B

theorem lift_C (a : State σA) (b : State σB) (h : GraphHistory σC) :
    (graphTransport A B C ab bc).history.apply
      (liftDownstream (compose A B ab) C (leftNestedBoundary A B C ab bc)
        (downstreamState A B a b) h) =
      leafC A B C ab bc a b h := by
  simp only [Transport.apply, GraphTransport.history, liftDownstream, History.map_comp, leafC]
  apply map_ext
  · exact state_C A B C ab bc a b
  · exact event_C A B C ab bc
  · exact identity_C

theorem right_input (a : Store RationalReference.Carrier σA) :
    boundaryInput A (compose B C bc) (rightNestedBoundary A B C ab bc) a =
      liftInput B C bc (boundaryInput A B ab a) := by
  apply Subtype.ext
  funext t
  cases t with
  | inl t =>
      by_cases h : B.program.input t = true
      · simp [boundaryInput, liftInput, rightNestedBoundary, rightInputIndexEquiv,
          compose, program, h]; rfl
      · simp [boundaryInput, liftInput, rightNestedBoundary, rightInputIndexEquiv,
          compose, program, h]; rfl
  | inr t => rfl

theorem shared_right (a : State σA) (hB : GraphHistory σB)
    {hBC : GraphHistory (declarations B C)}
    (shared : (liftDownstream A B ab a hB).start = upstreamState A B a)
    (binary : BinaryHistory B C bc hB hBC) :
    (liftDownstream A (compose B C bc) (rightNestedBoundary A B C ab bc) a hBC).start =
      upstreamState A (compose B C bc) a := by
  obtain ⟨suffix, joined⟩ := binary.splices B C bc
  have starts := SharedSplice.start joined
  have coherent := congrArg
    (fun s => (graphTransport A B C ab bc).mapState (upstreamState (compose A B ab) C s))
    shared
  simp only [liftDownstream, History.start_map] at coherent
  rw [state_B, state_A] at coherent
  simpa only [liftDownstream, History.start_map, starts, liftUpstream] using coherent

theorem append_finish {S E F : Type*} (h k : History S E F Unit) {s}
    (finished : h.finish = .ok (s, ())) :
    (SharedSplice.append h k).finish = k.finish := by
  obtain ⟨_, _, _, _, hf⟩ := SharedSplice.cut h k finished
  exact hf

theorem boundary_C (a : State σA) (b : State σB)
    (storeAB : Store RationalReference.Carrier (declarations A B))
    (storeB : Store RationalReference.Carrier σB)
    (fullAB : ∀ x, (downstreamState A B a b).available x = some (storeAB x))
    (fullB : ∀ x, b.available x = some (storeB x)) :
    boundaryInput (compose A B ab) C (leftNestedBoundary A B C ab bc) storeAB =
      boundaryInput B C bc storeB := by
  rw [IndexedOperationalRunsPhases.original_bc_input]
  apply Subtype.ext
  funext t
  by_cases h : C.program.input t = true
  · simp only [boundaryInput, h, ↓reduceDIte]
    congr 1
    funext p
    let output := bc.matched ⟨t, h⟩
    let q := (bc.domain ⟨t, h⟩).coord p
    have defined := B.program.output_defined output.val output.property
    have eq := fullAB ⟨.inr ⟨output.val, defined⟩, q⟩
    change b.available ⟨output.val, q⟩ = some (storeAB _) at eq
    rw [fullB] at eq
    have values := Option.some.inj eq
    change restrictDownstream A B ab storeAB ⟨output.val, q⟩ = storeB ⟨output.val, q⟩
    unfold restrictDownstream Embedding.pullComplete
    rw [downstream_defined_address A B ab ⟨output.val, defined⟩ q]
    exact values.symm
  · simp [boundaryInput, h]

theorem transport_append {σ τ : Declarations Unit} (t : GraphTransport σ τ)
    (h k : GraphHistory σ) :
    t.history.apply (SharedSplice.append h k) =
      SharedSplice.append (t.history.apply h) (t.history.apply k) :=
  map_append _ _ _ _ _

theorem up_append {σ τ : Declarations Unit}
    [Fintype σ.Tensor] [DecidableEq σ.Tensor] [Fintype τ.Tensor] [DecidableEq τ.Tensor]
    (X : MatchedComponent σ) (Y : MatchedComponent τ) (h k : GraphHistory σ) :
    liftUpstream X Y (SharedSplice.append h k) =
      SharedSplice.append (liftUpstream X Y h) (liftUpstream X Y k) :=
  map_append _ _ _ _ _

theorem down_append {σ τ : Declarations Unit}
    [Fintype σ.Tensor] [DecidableEq σ.Tensor] [Fintype τ.Tensor] [DecidableEq τ.Tensor]
    (X : MatchedComponent σ) (Y : MatchedComponent τ) (wire : Boundary X Y)
    (completed : State σ) (h k : GraphHistory τ) :
    liftDownstream X Y wire completed (SharedSplice.append h k) =
      SharedSplice.append (liftDownstream X Y wire completed h)
        (liftDownstream X Y wire completed k) := map_append _ _ _ _ _

theorem binary_associativity
    (rankB : B.program.RankCertificate) (rankC : C.program.RankCertificate)
    {hA : GraphHistory σA} {hAB : GraphHistory (declarations A B)}
    {hL : GraphHistory (L A B C ab)}
    (inner : BinaryHistory A B ab hA hAB)
    (outer : BinaryHistory (compose A B ab) C (leftNestedBoundary A B C ab bc) hAB hL) :
    ∃ hR, BinaryHistory A (compose B C bc) (rightNestedBoundary A B C ab bc) hA hR ∧
      (graphTransport A B C ab bc).history.apply hL = hR := by
  cases inner with
  | failed tag a failedA =>
      cases outer with
      | failed =>
          exact ⟨_, .failed tag a failedA, lift_A A B C ab bc hA⟩
      | complete a' store hC finished =>
          simp [liftUpstream, finish_map, failedA] at finished
  | complete a storeA hB finishedA fullA admittedB runB sharedAB =>
      obtain ⟨hBC, bcTree, bcRun⟩ := compose_history B C bc
        (boundaryInput A B ab storeA) rankB rankC hB runB
      have tree := bcTree
      have rightShared := shared_right A B C ab bc a hB sharedAB tree
      have rightRun : hBC.toRun = runChecked (compose B C bc).contract
          (compose B C bc).fragment
          (boundaryInput A (compose B C bc) (rightNestedBoundary A B C ab bc) storeA).val := by
        rw [right_input]
        exact bcRun
      have rightAdmitted := tree.admissible B C bc admittedB
      have sourceFinish :
          (SharedSplice.append (liftUpstream A B hA)
            (liftDownstream A B ab a hB)).finish =
            (liftDownstream A B ab a hB).finish :=
        append_finish _ _ (s := upstreamState A B a)
          (by simp [liftUpstream, finish_map, finishedA])
      cases bcTree with
      | failed tag b failedB =>
          cases outer with
          | complete a' store hC finished =>
              rw [sourceFinish] at finished
              simp [liftDownstream, finish_map, failedB] at finished
          | failed =>
              refine ⟨_, .complete a storeA _ finishedA fullA rightAdmitted rightRun
                rightShared, ?_⟩
              rw [up_append, transport_append, lift_A, lift_B]
              rfl
      | complete b storeB hC finishedB fullB admittedC runC sharedBC =>
          cases outer with
          | failed tag endpoint failed =>
              rw [sourceFinish] at failed
              simp [liftDownstream, finish_map, finishedB] at failed
          | complete completedAB storeAB hC' finishedAB fullAB admittedC' runC' sharedLeft =>
              rw [sourceFinish] at finishedAB
              have endeq : downstreamState A B a b = completedAB := by
                simpa [liftDownstream, finish_map, finishedB] using finishedAB
              subst completedAB
              have inputs := boundary_C A B C ab bc a b storeAB storeB fullAB fullB
              rw [inputs] at runC'
              have sameC : hC' = hC := GraphHistory.toRun_injective (runC'.trans runC.symm)
              subst hC'
              refine ⟨_, .complete a storeA _ finishedA fullA rightAdmitted rightRun
                rightShared, ?_⟩
              rw [up_append, transport_append, transport_append, lift_A, lift_B]
              rw [lift_C, down_append]
              let aa := leafA A B C bc hA
              let bb := leafB A B C ab bc a hB
              let cc := leafC A B C ab bc a b hC
              have first : SharedSplice.Splice aa (some bb) (SharedSplice.append aa bb) := by
                have joined := SharedSplice.success (liftUpstream A B hA)
                  (liftDownstream A B ab a hB)
                  (by simp [liftUpstream, finish_map, finishedA]) sharedAB
                have mapped := SharedSplice.transport (upstreamState (compose A B ab) C)
                  (mapEvent (upstream (compose A B ab) C) upstreamId) upstreamId joined
                have moved := SharedSplice.transport
                  (graphTransport A B C ab bc).stateEquiv
                  (graphTransport A B C ab bc).eventEquiv identityEquiv mapped
                change SharedSplice.Splice
                  ((graphTransport A B C ab bc).history.apply
                    (liftUpstream (compose A B ab) C (liftUpstream A B hA)))
                  (some ((graphTransport A B C ab bc).history.apply
                    (liftUpstream (compose A B ab) C (liftDownstream A B ab a hB))))
                  ((graphTransport A B C ab bc).history.apply
                    (liftUpstream (compose A B ab) C
                      (SharedSplice.append (liftUpstream A B hA)
                        (liftDownstream A B ab a hB)))) at moved
                rw [up_append, transport_append, lift_A, lift_B] at moved
                exact moved
              have second : SharedSplice.Splice bb (some cc) (SharedSplice.append bb cc) := by
                have joined := SharedSplice.success (liftUpstream B C hB)
                  (liftDownstream B C bc b hC)
                  (by simp [liftUpstream, finish_map, finishedB]) sharedBC
                have moved := SharedSplice.transport
                  (downstreamState A (compose B C bc) a)
                  (mapEvent (downstream A (compose B C bc)
                    (rightNestedBoundary A B C ab bc)) downstreamId) downstreamId joined
                simpa only [Option.map_some, map_append] using moved
              have leftJoin : SharedSplice.Splice (SharedSplice.append aa bb) (some cc)
                  (SharedSplice.append (SharedSplice.append aa bb) cc) := by
                apply SharedSplice.success (s := downstreamState A (compose B C bc) a
                  (upstreamState B C b))
                · rw [append_finish aa bb (s := upstreamState A (compose B C bc) a)
                    (by simp [aa, leafA, liftUpstream,
                    finish_map, finishedA])]
                  simp [bb, leafB, liftUpstream, liftDownstream, finish_map, finishedB]
                · have moved := congrArg (graphTransport A B C ab bc).mapState sharedLeft
                  simp only [liftDownstream, History.start_map] at moved
                  rw [state_C, state_B] at moved
                  simpa only [cc, leafC, liftDownstream, History.start_map] using moved
              have rightJoin : SharedSplice.Splice aa (some (SharedSplice.append bb cc))
                  (SharedSplice.append aa (SharedSplice.append bb cc)) := by
                apply SharedSplice.success (s := upstreamState A (compose B C bc) a)
                · simp [aa, leafA, liftUpstream, finish_map, finishedA]
                · simpa only [down_append] using rightShared
              exact SharedSplice.associative_eq first second leftJoin rightJoin

theorem right_nested_tree
    (rankB : B.program.RankCertificate) (rankC : C.program.RankCertificate)
    {hA : GraphHistory σA} {hR : GraphHistory (R A B C bc)}
    (right : BinaryHistory A (compose B C bc) (rightNestedBoundary A B C ab bc) hA hR) :
    (∃ tag a, hA.finish = .error (a, tag) ∧
      hR = liftUpstream A (compose B C bc) hA) ∨
    (∃ (a : State σA) (storeA : Store RationalReference.Carrier σA)
      (hB : GraphHistory σB) (hBC : GraphHistory (declarations B C)),
      hA.finish = .ok (a, ()) ∧
      (∀ x, a.available x = some (storeA x)) ∧ hB.Admissible ∧
      hB.toRun = runChecked B.contract B.fragment (boundaryInput A B ab storeA).val ∧
      BinaryHistory B C bc hB hBC ∧
      hR = SharedSplice.append (liftUpstream A (compose B C bc) hA)
        (liftDownstream A (compose B C bc) (rightNestedBoundary A B C ab bc) a hBC)) := by
  cases right with
  | failed tag a finished => exact .inl ⟨tag, a, finished, rfl⟩
  | complete a storeA hBC finished full admitted run shared =>
      obtain ⟨hB, admittedB, runB, _⟩ :=
        GraphHistory.ranked_default_exists B (boundaryInput A B ab storeA) rankB
      obtain ⟨otherBC, inner, otherRun⟩ :=
        compose_history B C bc (boundaryInput A B ab storeA) rankB rankC hB runB
      rw [right_input] at run
      have same : otherBC = hBC := GraphHistory.toRun_injective (otherRun.trans run.symm)
      subst otherBC
      exact .inr ⟨a, storeA, hB, hBC, finished, full, admittedB, runB, inner, rfl⟩

theorem actual_nested_histories (η : A.program.Input)
    (rankA : A.program.RankCertificate) (rankB : B.program.RankCertificate)
    (rankC : C.program.RankCertificate) :
    ∃ (hA : GraphHistory σA) (hAB : GraphHistory (declarations A B))
      (hL : GraphHistory (L A B C ab)) (hR : GraphHistory (R A B C bc)),
      hA.Admissible ∧ hL.Admissible ∧ hR.Admissible ∧
      hA.toRun = runChecked A.contract A.fragment η.val ∧
      BinaryHistory A B ab hA hAB ∧
      BinaryHistory (compose A B ab) C (leftNestedBoundary A B C ab bc) hAB hL ∧
      BinaryHistory A (compose B C bc) (rightNestedBoundary A B C ab bc) hA hR ∧
      hL.toRun = runChecked (leftBracket A B C ab bc).contract
        (leftBracket A B C ab bc).fragment
        (liftInput (compose A B ab) C (leftNestedBoundary A B C ab bc)
          (liftInput A B ab η)).val ∧
      hR.toRun = runChecked (rightBracket A B C ab bc).contract
        (rightBracket A B C ab bc).fragment
        (liftInput A (compose B C bc) (rightNestedBoundary A B C ab bc) η).val ∧
      (graphTransport A B C ab bc).history.apply hL = hR := by
  obtain ⟨hA, admitted, hArun, _⟩ := GraphHistory.ranked_default_exists A η rankA
  obtain ⟨hAB, hL, first, second, hLrun⟩ :=
    left_nested_history A B ab C bc η rankA rankB rankC hA hArun
  obtain ⟨hR, right, associative⟩ := binary_associativity A B C ab bc rankB rankC first second
  have hRrun := right.sound A (compose B C bc) (rightNestedBoundary A B C ab bc) η rankA
    (compositeRankCertificate B C bc rankB rankC) hArun
  exact ⟨hA, hAB, hL, hR, admitted,
    second.admissible _ _ _ (first.admissible _ _ _ admitted),
    right.admissible _ _ _ admitted, hArun, first, second, right, hLrun, hRrun, associative⟩

#print axioms binary_associativity
#print axioms right_nested_tree
#print axioms actual_nested_histories

end IndexedOperationalHistoryAssociativity

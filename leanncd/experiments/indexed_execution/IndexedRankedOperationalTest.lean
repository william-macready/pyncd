import IndexedOperationalWireFrame
import IndexedRankedOperationalCore
import IndexedRankedOperationalSource
import IndexedRankedOperationalInterpretation
import IndexedOperationalAssociativityFixtures

namespace IndexedRankedOperationalTest

open LeanNCD.Semantics IndexedOpenComposition IndexedComponentTransport IndexedSource
open IndexedOperationalHistory IndexedOperationalWireFrame IndexedWitness

@[reducible] def cube : Shape := [⟨11, 2⟩, ⟨12, 2⟩, ⟨13, 2⟩]

def rotateAxes : Fin 3 ≃ Fin 3 where
  toFun i := if i = 0 then 1 else if i = 1 then 2 else 0
  invFun i := if i = 0 then 2 else if i = 1 then 0 else 1
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

def rotateDomain : Domain cube cube where
  axes := rotateAxes
  extent := by intro i; fin_cases i <;> rfl
  coord :=
    { toFun := fun p => (p.2.2.1, p.1, p.2.1, ())
      invFun := fun p => (p.2.1, p.2.2.1, p.1, ())
      left_inv := by rintro ⟨i, j, k, ⟨⟩⟩; rfl
      right_inv := by rintro ⟨i, j, k, ⟨⟩⟩; rfl }
  raw :=
    { toFun := fun q i => q (rotateAxes.symm i)
      invFun := fun q i => q (rotateAxes i)
      left_inv := by intro q; funext i; simp
      right_inv := by intro q; funext i; simp }
  raw_axis := by
    intro q i
    exact congrArg q (rotateAxes.symm_apply_apply i)
  coherent := by
    rintro ⟨i, j, k, ⟨⟩⟩
    funext a
    fin_cases a <;> rfl

@[reducible] def object : Object where
  interface :=
    { Tensor := Fin 1
      uid := fun t => t.val
      unique := fun _ _ h => Fin.ext h
      signature := fun _ => ⟨(), cube⟩
      ports := [0]
      ports_nodup := by simp
      ports_complete := by intro t; fin_cases t; simp }

@[reducible] def ambient : Declarations Unit :=
  ⟨Fin 2, fun t => t.val, fun _ _ h => Fin.ext h, fun _ => ⟨(), cube⟩⟩

def scope : Scope object ambient where
  «tensor» := fun _ => 0
  injective := fun _ _ _ => Subsingleton.elim _ _
  domain := fun _ => Domain.id cube

def coordinateIndex (p : Coord cube) : Nat :=
  100 * p.1.val + 10 * p.2.1.val + p.2.2.1.val

def coordinateValue (p : Coord cube) : ℚ := coordinateIndex p

def incoming : State ambient where
  available := fun a => some ((1000 * a.1.val + coordinateIndex a.2 : Nat) : ℚ)
  produced := [(101, 1), (102, -1)]

def view : AvailableView scope incoming where
  env := fun _ => coordinateValue
  available := by
    intro t p
    change some ((0 + coordinateIndex p : Nat) : ℚ) = some (coordinateValue p)
    rw [Nat.zero_add]
    rfl

def rotate : Wire object object where
  ports := Equiv.refl _
  domain := fun _ => rotateDomain

def point : Coord cube := (0, 1, 1, ())

def outputAt (h : History (State ambient) (Event ambient) Nat object.interface.Env) :
    Option ℚ :=
  match h.finish with
  | .ok (_, env) => some (env 0 point)
  | .error _ => none

def wireObservation :=
  let history := runWire view rotate
  (history.events.length, history.states.length, history.start.produced,
    history.start.available ⟨1, point⟩, outputAt history)

def wireControls :=
  (outputAt (runWire view (Wire.identity object)),
    outputAt (runWire view rotate.inverse),
    outputAt (runWire view (rotate.comp rotate)),
    outputAt (runWire view (rotate.comp rotate.inverse)))

example : wireObservation = (0, 1, [(101, 1), (102, -1)], some 1011, some 101) := by
  decide
example : wireControls = (some 11, some 110, some 110, some 11) := by decide

example : outputAt (runWire view rotate) ≠ outputAt (runWire view rotate.inverse) := by
  decide
example : outputAt (runWire view (rotate.comp rotate)) ≠ outputAt (runWire view rotate) := by
  decide

#eval wireObservation
#eval wireControls

open IndexedRankedOperationalInterpretation
open IndexedRankedOperationalCategory
open IndexedOperationalHistoryComposition

example : Realizes (IndexedRankedOperationalCore.Normal.identity object) scope incoming
    view.env (.done incoming view.env) := realizes_identity view

example : SourceRealizes
    (.identity (⟨object⟩ : IndexedRankedOperationalSource.Object))
    scope incoming view.env (.done incoming view.env) := source_identity view

example : SourceRealizes
    (.wire (X := (⟨object⟩ : IndexedRankedOperationalSource.Object))
      (Y := (⟨object⟩ : IndexedRankedOperationalSource.Object)) rotate)
    scope incoming view.env (.done incoming (rotate.env view.env)) := source_wire view rotate

example : Realizes ((IndexedRankedOperationalCore.Normal.admin rotate).comp
    (.admin rotate.inverse)) scope incoming view.env
    ((runWire view rotate).bind (fun s env => .done s (rotate.inverse.env env))) :=
  realizes_wire_composition view rotate rotate.inverse

open IndexedComponentComposition IndexedComponentCompositionLocalFixtures
open IndexedComponentCompositionPortFixtures IndexedComponentRankedExecutionFixtures
open IndexedOperationalAssociativityFixtures IndexedRankedOperationalCore

def privateOrigin (a : ℚ) : Origin (consumerComponent a) :=
  .opaque _ ⟨consumerRank a⟩

noncomputable def privateLeft (a b c : ℚ) :=
  IndexedRankedOperationalSource.leftNested
    (consumerComponent a) (consumerComponent b) (consumerComponent c)
    (privateBoundary a b) (privateBoundary b c)
    (consumerRank a) (consumerRank b) (consumerRank c)
    (privateOrigin a) (privateOrigin b) (privateOrigin c)

noncomputable def privateRight (a b c : ℚ) :=
  IndexedRankedOperationalSource.rightNested
    (consumerComponent a) (consumerComponent b) (consumerComponent c)
    (privateBoundary a b) (privateBoundary b c)
    (consumerRank a) (consumerRank b) (consumerRank c)
    (privateOrigin a) (privateOrigin b) (privateOrigin c)

theorem privateReassociation (a b c : ℚ) :
    IndexedRankedOperationalCategory.Agrees (privateLeft a b c).normalize
      (privateRight a b c).normalize :=
  IndexedRankedOperationalSource.bracket_sound
    (consumerComponent a) (consumerComponent b) (consumerComponent c)
    (privateBoundary a b) (privateBoundary b c)
    (consumerRank a) (consumerRank b) (consumerRank c)
    (privateOrigin a) (privateOrigin b) (privateOrigin c)

example : IndexedRankedOperationalCategory.Agrees (privateLeft 4 4 4).normalize
    (privateRight 4 4 4).normalize := privateReassociation 4 4 4
example : IndexedRankedOperationalCategory.Agrees (privateLeft 0 4 4).normalize
    (privateRight 0 4 4).normalize := privateReassociation 0 4 4
example : IndexedRankedOperationalCategory.Agrees (privateLeft 4 0 4).normalize
    (privateRight 4 0 4).normalize := privateReassociation 4 0 4
example : IndexedRankedOperationalCategory.Agrees (privateLeft 4 4 0).normalize
    (privateRight 4 4 0).normalize := privateReassociation 4 4 0

noncomputable def privatePairWithUnit (a b : ℚ) :=
  IndexedRankedOperationalSource.Term.seq
    (.seq (.leaf (consumerComponent a) (consumerRank a) (privateOrigin a))
      (.wire (boundaryWire (consumerComponent a) (consumerComponent b) (privateBoundary a b))))
    (.seq (.identity _)
      (.leaf (consumerComponent b) (consumerRank b) (privateOrigin b)))

theorem privateInteriorUnit (a b : ℚ) :
    IndexedRankedOperationalCategory.Agrees (privatePairWithUnit a b).normalize
      (IndexedRankedOperationalSource.pair
        (consumerComponent a) (consumerComponent b) (privateBoundary a b)
        (consumerRank a) (consumerRank b) (privateOrigin a) (privateOrigin b)).normalize :=
  IndexedRankedOperationalSource.sound
    (.seq (.refl _) (.id_left _))

example : IndexedRankedOperationalCategory.Agrees (privatePairWithUnit 4 4).normalize
    (IndexedRankedOperationalSource.pair
      (consumerComponent 4) (consumerComponent 4) (privateBoundary 4 4)
      (consumerRank 4) (consumerRank 4) (privateOrigin 4) (privateOrigin 4)).normalize :=
  privateInteriorUnit 4 4

/-- Local computation owns the left summand; the right summand keeps the
populated cube donor, including availability not present at the boundary. -/
def framedDeclarations (σ : Declarations Unit) : Declarations Unit where
  Tensor := σ.Tensor ⊕ ambient.Tensor
  uid := Sum.elim (fun t => Nat.pair 0 (σ.uid t)) (fun t => Nat.pair 1 (ambient.uid t))
  unique := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        change Nat.pair 0 (σ.uid a) = Nat.pair 0 (σ.uid b) at h
        exact congrArg Sum.inl (σ.unique (Nat.pair_eq_pair.mp h).2)
      | inr b =>
        change Nat.pair 0 (σ.uid a) = Nat.pair 1 (ambient.uid b) at h
        exact False.elim (Nat.noConfusion (Nat.pair_eq_pair.mp h).1)
    | inr a =>
      cases b with
      | inl b =>
        change Nat.pair 1 (ambient.uid a) = Nat.pair 0 (σ.uid b) at h
        exact False.elim (Nat.noConfusion (Nat.pair_eq_pair.mp h).1)
      | inr b =>
        change Nat.pair 1 (ambient.uid a) = Nat.pair 1 (ambient.uid b) at h
        exact congrArg Sum.inr (ambient.unique (Nat.pair_eq_pair.mp h).2)
  signature := Sum.elim σ.signature ambient.signature

def populatedFrame {σ : Declarations Unit} [Fintype σ.Tensor] [DecidableEq σ.Tensor]
    (A : MatchedComponent σ) (η : A.program.Input) : Frame σ (framedDeclarations σ) where
  place := ⟨Sum.inl, Sum.inl_injective, fun _ => Domain.id _⟩
  identity := ⟨fun n => 1000 + n, fun _ _ h => Nat.add_left_cancel h⟩
  inherited := {
    available := fun a => match a with
      | ⟨.inl t, p⟩ => (initial η.val).available ⟨t, p⟩
      | ⟨.inr t, p⟩ => incoming.available ⟨t, p⟩
    produced := incoming.produced }
  fresh := by
    intro row member n
    change row ∈ [(101, (1 : ℚ)), (102, -1)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> dsimp <;> omega

theorem populatedFrame_fresh {σ : Declarations Unit}
    [Fintype σ.Tensor] [DecidableEq σ.Tensor]
    (A : MatchedComponent σ) (η : A.program.Input) :
    (populatedFrame A η).FreshInput A η := fun _ => rfl

noncomputable def privateFrame (a : ℚ) :=
  populatedFrame (consumerComponent a) (privateInput a)

example (a : ℚ) :
    Realizes (Normal.leaf (consumerComponent a) (consumerRank a))
      (((privateFrame a).scope (inputScope (consumerComponent a))).reindex (Wire.identity _).inverse)
      (privateFrame a).inherited (inputEnv _ (privateInput a))
      (computeHistory (consumerComponent a) (consumerRank a) (Wire.identity _)
        (Wire.identity _) (privateFrame a) (inputEnv _ (privateInput a))) := by
  apply Realizes.compute
  simpa only [externalInput, Wire.env_identity, Equiv.refl_apply, envInput_inputEnv] using
    populatedFrame_fresh (consumerComponent a) (privateInput a)

example (a : ℚ) :
    (computeHistory (consumerComponent a) (consumerRank a) (Wire.identity _)
      (Wire.identity _) (privateFrame a) (inputEnv _ (privateInput a))).start.produced =
        [(101, 1), (102, -1)] := by
  rw [computeHistory_start]
  rfl

example (a : ℚ) :
    (computeHistory (consumerComponent a) (consumerRank a) (Wire.identity _)
      (Wire.identity _) (privateFrame a) (inputEnv _ (privateInput a))).start.available
        ⟨.inr 1, point⟩ = some 1011 := by
  rw [computeHistory_start]
  rw [Frame.outside]
  · rfl
  · rintro ⟨⟨t, p⟩, impossible⟩
    cases impossible

example (a : ℚ) :
    (computeHistory (consumerComponent a) (consumerRank a) (Wire.identity _)
      (Wire.identity _) (privateFrame a) (inputEnv _ (privateInput a))).map id id id (fun _ => ()) =
      (actualHistory (consumerComponent a) (externalInput _ (Wire.identity _)
        (inputEnv _ (privateInput a))) (consumerRank a)).map
        (privateFrame a).state (privateFrame a).event (privateFrame a).identity id :=
  compute_history_exact _ _ _ _ _ _

noncomputable def pairFrame (a b : ℚ) :=
  populatedFrame (privateComposite a b)
    (liftInput (consumerComponent a) (consumerComponent b) (privateBoundary a b) (privateInput a))

theorem pairFrame_coherent (a b : ℚ) :
    Coherent (MetadataTransport.refl _).toGraphTransport (pairFrame a b) (pairFrame a b) :=
  ⟨fun _ => rfl, fun _ => rfl, rfl⟩

example : (pairFrame 4 0).FreshInput (privateComposite 4 0)
    (liftInput (consumerComponent 4) (consumerComponent 0) (privateBoundary 4 0) (privateInput 4)) :=
  populatedFrame_fresh _ _

example : HistoryAgrees
    (τ := framedDeclarations (declarations (consumerComponent 4) (consumerComponent 0)))
    (privatePairWithUnit 4 0).normalize
    (IndexedRankedOperationalSource.pair
      (consumerComponent 4) (consumerComponent 0) (privateBoundary 4 0)
      (consumerRank 4) (consumerRank 0) (privateOrigin 4) (privateOrigin 0)).normalize :=
  agrees_history (privateInteriorUnit 4 0)

example :
    computeHistory (privateComposite 4 0) (privateRank 4 0)
      (inputWire (consumerComponent 4) (consumerComponent 0) (privateBoundary 4 0))
      (outputWire (consumerComponent 4) (consumerComponent 0) (privateBoundary 4 0))
      (pairFrame 4 0) (inputEnv _ (privateInput 4)) =
    computeHistory (privateComposite 4 0) (privateRank 4 0)
      (inputWire (consumerComponent 4) (consumerComponent 0) (privateBoundary 4 0))
      (outputWire (consumerComponent 4) (consumerComponent 0) (privateBoundary 4 0))
      (pairFrame 4 0) (inputEnv _ (privateInput 4)) := by
  let origin := Origin.joined (consumerComponent 4) (consumerComponent 0)
    (privateBoundary 4 0) (privateOrigin 4) (privateOrigin 0)
  exact compute_history_congruence _ _ _ _ origin origin _ _ _ _
    (MetadataTransport.refl _) (Equiv.refl _)
    (fun _ => CompleteObservation.agrees_refl _)
    (reindexExterior_refl _) _ _ (pairFrame_coherent 4 0) _

theorem private_failure_no_output :
    ∃ (s : State IndexedComponentCompositionLocalFixtures.consumerDeclarations) (tag : Nat),
      (actualHistory (consumerComponent 0) (privateInput 0) (consumerRank 0)).finish =
        .error (s, tag) := by
  have failed : (runChecked (consumerComponent 0).contract (consumerComponent 0).fragment
      (privateInput 0).val).outcome.kind = "failed" := by
    rw [IndexedComponentExecution.checked_eq_stepFuel (consumerComponent 0).matched (privateInput 0)]
    decide +kernel
  rw [← (actualHistory_spec (consumerComponent 0) (privateInput 0) (consumerRank 0)).2.1]
    at failed
  cases hf : (actualHistory (consumerComponent 0) (privateInput 0) (consumerRank 0)).finish with
  | ok pair => simp [GraphHistory.toRun, hf, Outcome.kind] at failed
  | error pair => exact ⟨pair.1, pair.2, rfl⟩

example :
    ∃ s tag,
      (computeHistory (consumerComponent 0) (consumerRank 0) (Wire.identity _)
        (Wire.identity _) (privateFrame 0) (inputEnv _ (privateInput 0))).finish =
        .error ((privateFrame 0).state s, (privateFrame 0).identity tag) := by
  obtain ⟨s, tag, failed⟩ := private_failure_no_output
  refine ⟨s, tag, compute_failure _ _ _ _ _ _ ?_⟩
  simpa only [externalInput, Wire.env_identity, Equiv.refl_apply, envInput_inputEnv] using failed

example :
    let A := consumerComponent 4
    let B := consumerComponent 0
    let w := boundaryWire A B (privateBoundary 4 0)
    let b := connectingBoundary A B w
    let source := actualHistory A (privateInput 4) (consumerRank 4)
    let result := actualHistory (compose A B b) (liftInput A B b (privateInput 4))
      (compositeRankCertificate A B b (consumerRank 4) (consumerRank 0))
    (∃ s tag, source.finish = .error (s, tag) ∧ result = liftUpstream A B source) ∨
    ∃ (s : State IndexedComponentCompositionLocalFixtures.consumerDeclarations)
      (store : Store RationalReference.Carrier IndexedComponentCompositionLocalFixtures.consumerDeclarations)
      (suffix : GraphHistory (declarations A B))
      (v : AvailableView ((upstreamOutputScope A B).reindex w) (upstreamState A B s)),
      source.finish = .ok (s, ()) ∧
      (∀ a, s.available a = some (store a)) ∧ suffix.start = upstreamState A B s ∧
      (outputContinuation ((upstreamOutputScope A B).reindex w)
        (Wire.identity (input B))).run (upstreamState A B s) () =
          runWire v (Wire.identity (input B)) ∧
      result = (liftUpstream A B source).bind (fun cut _ =>
        ((outputContinuation ((upstreamOutputScope A B).reindex w)
          (Wire.identity (input B))).run cut ()).bind (fun _ _ => suffix)) :=
  actual_join_identity _ _ _ _ _ _

example :
    (actualObservation emptyProducerComponent (.opaque _ ⟨emptyProducerRank⟩)
      emptyValidatedInput emptyProducerRank).metadata.inputs =
        emptyProducerComponent.inputs ∧
    (computeHistory emptyProducerComponent emptyProducerRank (Wire.identity _)
      (Wire.identity _) (populatedFrame emptyProducerComponent emptyValidatedInput)
      (inputEnv _ emptyValidatedInput)).map id id id (fun _ => ()) =
        (actualHistory emptyProducerComponent emptyValidatedInput emptyProducerRank).map
          (populatedFrame emptyProducerComponent emptyValidatedInput).state
          (populatedFrame emptyProducerComponent emptyValidatedInput).event
          (populatedFrame emptyProducerComponent emptyValidatedInput).identity id := by
  refine ⟨rfl, ?_⟩
  simpa only [externalInput, Wire.env_identity, Equiv.refl_apply, envInput_inputEnv] using
    compute_history_exact emptyProducerComponent emptyProducerRank (Wire.identity _)
      (Wire.identity _) (populatedFrame emptyProducerComponent emptyValidatedInput)
      (inputEnv _ emptyValidatedInput)

def emptyReassociation :=
  IndexedRankedOperationalSource.bracket_sound
    emptyProducerComponent emptyConsumerComponent emptyConsumerComponent
    emptyBoundary emptyTailBoundary emptyProducerRank emptyConsumerRank emptyConsumerRank
    (.opaque _ ⟨emptyProducerRank⟩) (.opaque _ ⟨emptyConsumerRank⟩)
    (.opaque _ ⟨emptyConsumerRank⟩)

def axisReassociation :=
  IndexedRankedOperationalSource.bracket_sound
    IndexedComponentCompositionAxisFixtures.axisProducer
    IndexedComponentCompositionAxisFixtures.axisConsumer (consumerComponent 4)
    IndexedComponentCompositionAxisFixtures.axisBoundary axisTailBoundary
    IndexedComponentRankedExecutionRankTest.Axis.producerRank
    IndexedComponentRankedExecutionRankTest.Axis.consumerRank (consumerRank 4)
    (.opaque _ ⟨IndexedComponentRankedExecutionRankTest.Axis.producerRank⟩)
    (.opaque _ ⟨IndexedComponentRankedExecutionRankTest.Axis.consumerRank⟩)
    (privateOrigin 4)

example : ¬Nonempty IndexedComponentModelCycleFixtures.hiddenUpstream.program.RankCertificate :=
  hidden_no_rank

#eval [privateCounts 4 4 4, privateCounts 0 4 4, privateCounts 4 0 4, privateCounts 4 4 0]
#print axioms privateInteriorUnit
#print axioms privateReassociation
#print axioms emptyReassociation
#print axioms axisReassociation

end IndexedRankedOperationalTest

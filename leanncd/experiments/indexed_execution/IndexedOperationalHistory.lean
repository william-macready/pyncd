import IndexedComponentExecutionReference
import IndexedWitnessInterface
import IndexedComponentCompositionPortFixtures

namespace IndexedOperationalHistory

/-- Every ordinary event has its pre-state; failure has only its terminal pre-state. -/
inductive History (S E F A : Type*)
  | done (state : S) (value : A)
  | step (state : S) (event : E) (tail : History S E F A)
  | failed (state : S) (event : E) (failure : F)
  deriving Repr

namespace History

variable {S E F A T D G B U V W C : Type*}

def start : History S E F A → S
  | .done s _ | .step s _ _ | .failed s _ _ => s

def states : History S E F A → List S
  | .done s _ | .failed s _ _ => [s]
  | .step s _ h => s :: h.states

def events : History S E F A → List E
  | .done _ _ => []
  | .failed _ e _ => [e]
  | .step _ e h => e :: h.events

def finish : History S E F A → Except (S × F) (S × A)
  | .done s a => .ok (s, a)
  | .failed s _ f => .error (s, f)
  | .step _ _ h => h.finish

def map (s : S → T) (e : E → D) (f : F → G) (a : A → B) :
    History S E F A → History T D G B
  | .done x y => .done (s x) (a y)
  | .failed x y z => .failed (s x) (e y) (f z)
  | .step x y h => .step (s x) (e y) (h.map s e f a)

@[simp] theorem map_id (h : History S E F A) : h.map id id id id = h := by
  induction h <;> simp_all [map]

theorem map_comp (h : History S E F A)
    (s : S → T) (e : E → D) (f : F → G) (a : A → B)
    (t : T → U) (d : D → V) (g : G → W) (b : B → C) :
    (h.map s e f a).map t d g b =
      h.map (t ∘ s) (d ∘ e) (g ∘ f) (b ∘ a) := by
  induction h <;> simp_all [map]

@[simp] theorem start_map (h : History S E F A)
    (s : S → T) (e : E → D) (f : F → G) (a : A → B) :
    (h.map s e f a).start = s h.start := by
  cases h <;> rfl

@[simp] theorem states_map (h : History S E F A)
    (s : S → T) (e : E → D) (f : F → G) (a : A → B) :
    (h.map s e f a).states = h.states.map s := by
  induction h <;> simp_all [map, states]

@[simp] theorem events_map (h : History S E F A)
    (s : S → T) (e : E → D) (f : F → G) (a : A → B) :
    (h.map s e f a).events = h.events.map e := by
  induction h <;> simp_all [map, events]

/-- Internal recursion; use `splice` for a compatible, shared-snapshot join. -/
def bind (h : History S E F A) (k : S → A → History S E F B) : History S E F B :=
  match h with
  | .done s a => k s a
  | .failed s e f => .failed s e f
  | .step s e tail => .step s e (tail.bind k)

structure Continuation (S E F A B : Type*) where
  run : S → A → History S E F B
  shared : ∀ s a, (run s a).start = s

def splice (h : History S E F A) (k : Continuation S E F A B) :
    History S E F B := h.bind k.run

theorem start_bind (h : History S E F A) (k : Continuation S E F A B) :
    (h.bind k.run).start = h.start := by
  cases h with
  | done s a => exact k.shared s a
  | step _ _ _ | failed _ _ _ => rfl

def Continuation.then (k : Continuation S E F A B)
    (l : Continuation S E F B C) : Continuation S E F A C :=
  ⟨fun s a => (k.run s a).splice l,
    fun s a => (start_bind (k.run s a) l).trans (k.shared s a)⟩

theorem bind_assoc (h : History S E F A)
    (k : S → A → History S E F B) (l : S → B → History S E F C) :
    (h.bind k).bind l = h.bind (fun s a => (k s a).bind l) := by
  induction h <;> simp_all [bind]

theorem splice_assoc (h : History S E F A)
    (k : Continuation S E F A B) (l : Continuation S E F B C) :
    (h.splice k).splice l = h.splice (k.then l) :=
  bind_assoc h k.run l.run

theorem splice_congr {h h' : History S E F A} (hh : h = h')
    (k l : Continuation S E F A B) (hk : ∀ s a, k.run s a = l.run s a) :
    h.splice k = h'.splice l := by
  subst h'
  have : k.run = l.run := funext fun s => funext (hk s)
  simp only [splice, this]

theorem map_bind (h : History S E F A)
    (s : S → T) (e : E → D) (f : F → G) (a : A → B)
    (b : C → U) (k : S → A → History S E F C)
    (l : T → B → History T D G U)
    (compatible : ∀ x y, l (s x) (a y) = (k x y).map s e f b) :
    (h.bind k).map s e f b = (h.map s e f a).bind l := by
  induction h with
  | done x y => exact (compatible x y).symm
  | failed _ _ _ => rfl
  | step x y tail ih => simp only [bind, map, ih]

/-- A successful prefix contributes all but its final snapshot. The suffix owns the cut. -/
theorem success_cut (h : History S E F A) (k : Continuation S E F A B)
    {s : S} {a : A} (done : h.finish = .ok (s, a)) :
    ∃ pre, h.states = pre ++ [s] ∧
      (h.splice k).states = pre ++ (k.run s a).states ∧
      (h.splice k).events = h.events ++ (k.run s a).events := by
  induction h with
  | done x y =>
      simp only [finish, Except.ok.injEq, Prod.mk.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact ⟨[], rfl, rfl, rfl⟩
  | failed _ _ _ => cases done
  | step x e tail ih =>
      obtain ⟨pre, hp, hs, he⟩ := ih done
      exact ⟨x :: pre, congrArg (List.cons x) hp,
        congrArg (List.cons x) hs, congrArg (List.cons e) he⟩

theorem failure_absorbs (h : History S E F A) (k : Continuation S E F A B)
    {s : S} {f : F} (failed : h.finish = .error (s, f)) :
    (h.splice k).states = h.states ∧ (h.splice k).events = h.events ∧
      (h.splice k).finish = .error (s, f) := by
  induction h with
  | done _ _ => cases failed
  | failed x e g =>
      simp only [finish, Except.error.injEq, Prod.mk.injEq] at failed
      rcases failed with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
  | step x e tail ih =>
      obtain ⟨hs, he, hf⟩ := ih failed
      exact ⟨congrArg (List.cons x) hs, congrArg (List.cons e) he, hf⟩

end History

structure Transport (S E F A T D G B : Type*) where
  state : S ≃ T
  event : E ≃ D
  failure : F ≃ G
  value : A ≃ B

namespace Transport

variable {S E F A T D G B U V W C : Type*}

def apply (t : Transport S E F A T D G B) (h : History S E F A) :
    History T D G B := h.map t.state t.event t.failure t.value

def refl : Transport S E F A S E F A :=
  ⟨Equiv.refl _, Equiv.refl _, Equiv.refl _, Equiv.refl _⟩

def symm (t : Transport S E F A T D G B) : Transport T D G B S E F A :=
  ⟨t.state.symm, t.event.symm, t.failure.symm, t.value.symm⟩

def trans (t : Transport S E F A T D G B) (u : Transport T D G B U V W C) :
    Transport S E F A U V W C :=
  ⟨t.state.trans u.state, t.event.trans u.event,
    t.failure.trans u.failure, t.value.trans u.value⟩

@[simp] theorem apply_refl (h : History S E F A) : refl.apply h = h :=
  History.map_id h

theorem apply_trans (t : Transport S E F A T D G B)
    (u : Transport T D G B U V W C) (h : History S E F A) :
    u.apply (t.apply h) = (t.trans u).apply h := History.map_comp h _ _ _ _ _ _ _ _

@[simp] theorem apply_symm (t : Transport S E F A T D G B)
    (h : History S E F A) : t.symm.apply (t.apply h) = h := by
  induction h <;> simp_all [apply, symm, History.map]

def continuation (t : Transport S E F A T D G B)
    (result : C ≃ U) (k : History.Continuation S E F A C) :
    History.Continuation T D G B U where
  run s a := (k.run (t.state.symm s) (t.value.symm a)).map
    t.state t.event t.failure result
  shared s a := by simp [k.shared]

theorem apply_splice (t : Transport S E F A T D G B)
    (result : C ≃ U) (h : History S E F A)
    (k : History.Continuation S E F A C) :
    (h.splice k).map t.state t.event t.failure result =
      (t.apply h).splice (t.continuation result k) := by
  apply History.map_bind
  intro s a
  simp [continuation]

end Transport

/-- Metadata is compared too, not existentially erased before comparing histories. -/
structure Observation (M S E F A : Type*) where
  metadata : M
  history : History S E F A

def Observed {M N S E F A T D G B : Type*} (metadata : M ≃ N)
    (transport : Transport S E F A T D G B)
    (source : Observation M S E F A) (target : Observation N T D G B) : Prop :=
  target.metadata = metadata source.metadata ∧ target.history = transport.apply source.history

theorem observed_refl {M S E F A : Type*} (x : Observation M S E F A) :
    Observed (Equiv.refl M) Transport.refl x x := ⟨rfl, (Transport.apply_refl _).symm⟩

theorem observed_symm {M N S E F A T D G B : Type*} (m : M ≃ N)
    (t : Transport S E F A T D G B)
    {x : Observation M S E F A} {y : Observation N T D G B}
    (h : Observed m t x y) : Observed m.symm t.symm y x := by
  constructor
  · rw [h.1]; simp
  · rw [h.2]; simp

theorem observed_trans {M N P S E F A T D G B U V W C : Type*}
    (m : M ≃ N) (n : N ≃ P) (t : Transport S E F A T D G B)
    (u : Transport T D G B U V W C)
    {x : Observation M S E F A} {y : Observation N T D G B}
    {z : Observation P U V W C} (h : Observed m t x y) (k : Observed n u y z) :
    Observed (m.trans n) (t.trans u) x z := by
  constructor
  · rw [k.1, h.1]; rfl
  · rw [k.2, h.2, Transport.apply_trans]

section Graph

open LeanNCD.Semantics LeanNCD.Semantics.Program
open IndexedOpenComposition IndexedComponentComposition IndexedComponentTransport

variable {σ τ : Declarations Unit}

/-- Explicit bijections. Integration must certify their leaf ownership equations;
the algebra does not choose a renaming by searching for agreement. -/
structure GraphTransport (σ τ : Declarations Unit) where
  address : Address σ ≃ Address τ
  identity : Nat ≃ Nat

def GraphTransport.mapState (t : GraphTransport σ τ) (s : State σ) : State τ :=
  ⟨fun a => s.available (t.address.symm a),
    IndexedComponentExecution.mapLedger t.identity s.produced⟩

def GraphTransport.mapEvent (t : GraphTransport σ τ) : Event σ → Event τ
  | .produced tag cap v => .produced (t.identity tag) (t.identity cap) v
  | .sealed a v => .sealed (t.address a) v
  | .undefined tag => .undefined (t.identity tag)

def GraphTransport.symm (t : GraphTransport σ τ) : GraphTransport τ σ :=
  ⟨t.address.symm, t.identity.symm⟩

@[simp] theorem GraphTransport.symm_address (t : GraphTransport σ τ) :
    t.symm.address = t.address.symm := rfl

@[simp] theorem GraphTransport.symm_identity (t : GraphTransport σ τ) :
    t.symm.identity = t.identity.symm := rfl

@[simp] theorem GraphTransport.state_inverse (t : GraphTransport σ τ) (s : State σ) :
    t.symm.mapState (t.mapState s) = s := by
  cases s
  simp [mapState, symm, IndexedComponentExecution.mapLedger, List.map_map, Function.comp_def]

@[simp] theorem GraphTransport.event_inverse (t : GraphTransport σ τ) (e : Event σ) :
    t.symm.mapEvent (t.mapEvent e) = e := by
  cases e <;> simp [mapEvent, symm]

def GraphTransport.stateEquiv (t : GraphTransport σ τ) : State σ ≃ State τ where
  toFun := t.mapState
  invFun := t.symm.mapState
  left_inv := t.state_inverse
  right_inv := t.symm.state_inverse

def GraphTransport.eventEquiv (t : GraphTransport σ τ) : Event σ ≃ Event τ where
  toFun := t.mapEvent
  invFun := t.symm.mapEvent
  left_inv := t.event_inverse
  right_inv := t.symm.event_inverse

def GraphTransport.history (t : GraphTransport σ τ) :
    Transport (State σ) (Event σ) Nat Unit (State τ) (Event τ) Nat Unit :=
  ⟨t.stateEquiv, t.eventEquiv, t.identity, Equiv.refl _⟩

/-- The complete metadata-bearing ports and validated Option input are retained separately
from addresses, so an empty input tensor cannot disappear. Adapters are supplied explicitly. -/
structure GraphMetadata (σ : Declarations Unit) (Adapters : Type*) where
  inputs : List (Port σ)
  outputs : List (Port σ)
  inputRole : σ.Tensor → Bool
  input : InputBinding (K := RationalReference.Carrier) (σ := σ)
  valid : ∀ t, (input t).isSome = inputRole t
  adapters : Adapters
  inputs_nodup : (inputs.map Port.tensor).Nodup
  outputs_nodup : (outputs.map Port.tensor).Nodup
  inputs_exact : ∀ t, t ∈ inputs.map Port.tensor ↔ inputRole t = true

def GraphMetadata.ofComponent [Fintype σ.Tensor] [DecidableEq σ.Tensor]
    {Adapters : Type*} (A : MatchedComponent σ) (η : A.program.Input)
    (adapters : Adapters) : GraphMetadata σ Adapters :=
  ⟨A.inputs, A.outputs, A.program.input, η.val, η.property, adapters,
    A.inputs_nodup, A.outputs_nodup, A.inputs_exact⟩

/-- Tensor and raw/domain metadata must accompany a graph transport, not be reconstructed
from address enumeration (which is empty for a zero-sized tensor). -/
structure MetadataTransport (σ τ : Declarations Unit) extends GraphTransport σ τ where
  tensor : σ.Tensor ≃ τ.Tensor
  domain : ∀ t, Domain (σ.signature t).axes (τ.signature (tensor t)).axes
  address_eq : ∀ a, address a = ⟨tensor a.1, (domain a.1).coord a.2⟩

def MetadataTransport.port (t : MetadataTransport σ τ) (p : Port σ) : Port τ :=
  ⟨t.tensor p.tensor, (), (τ.signature (t.tensor p.tensor)).axes, rfl, rfl⟩

def MetadataTransport.Agrees {Adapters Other : Type*} (t : MetadataTransport σ τ)
    (adapters : Adapters ≃ Other)
    (x : GraphMetadata σ Adapters) (y : GraphMetadata τ Other) : Prop :=
  y.inputs = x.inputs.map t.port ∧ y.outputs = x.outputs.map t.port ∧
  (∀ a, y.inputRole (t.tensor a) = x.inputRole a) ∧
  (∀ a, y.input (t.tensor a) =
    (x.input a).map (fun values p => values ((t.domain a).coord.symm p))) ∧
  y.adapters = adapters x.adapters

abbrev GraphHistory (σ : Declarations Unit) := History (State σ) (Event σ) Nat Unit

def GraphHistory.toRun (h : GraphHistory σ) : Run σ :=
  ⟨match h.finish with
    | .ok (s, _) => .complete s
    | .error (s, tag) => .failed tag s,
    h.events, h.states⟩

/-- Admission excludes a fake failure event and an undefined event with a following state. -/
inductive GraphHistory.Admissible : GraphHistory σ → Prop
  | done (s) : Admissible (.done s ())
  | produced (s tag cap value h) : Admissible h →
      Admissible (.step s (.produced tag cap value) h)
  | sealed (s a value h) : Admissible h → Admissible (.step s (.sealed a value) h)
  | failed (s tag) : Admissible (.failed s (.undefined tag) tag)

theorem GraphHistory.transport_admissible (t : GraphTransport σ τ)
    {h : GraphHistory σ} (admitted : h.Admissible) :
    GraphHistory.Admissible (t.history.apply h) := by
  induction admitted with
  | done => exact .done _
  | produced _ _ _ _ _ _ ih => exact .produced _ _ _ _ _ ih
  | sealed _ _ _ _ _ ih => exact .sealed _ _ _ _ ih
  | failed => exact .failed _ _

theorem GraphHistory.splice_admissible {h : GraphHistory σ} (ha : h.Admissible)
    (k : History.Continuation (State σ) (Event σ) Nat Unit Unit)
    (hk : ∀ s a, GraphHistory.Admissible (k.run s a)) :
    GraphHistory.Admissible (h.splice k) := by
  induction ha with
  | done => exact hk _ _
  | produced _ _ _ _ _ _ ih => exact .produced _ _ _ _ _ ih
  | sealed _ _ _ _ _ ih => exact .sealed _ _ _ _ ih
  | failed => exact .failed _ _

def GraphTransport.mapOutcome (t : GraphTransport σ τ) (tensor : σ.Tensor → τ.Tensor) :
    Outcome σ → Outcome τ
  | .complete s => .complete (t.mapState s)
  | .failed tag s => .failed (t.identity tag) (t.mapState s)
  | .blocked s missing => .blocked (t.mapState s)
      (missing.map fun row => (t.identity row.1, row.2.map t.address))
  | .exhausted s => .exhausted (t.mapState s)
  | .invalidInput a => .invalidInput (tensor a)
  | .invalidGraph error => .invalidGraph error
  | .contractMismatch tag s => .contractMismatch (t.identity tag) (t.mapState s)
  | .collectorMismatch a s => .collectorMismatch (t.address a) (t.mapState s)

def GraphTransport.mapRun (t : GraphTransport σ τ) (tensor : σ.Tensor → τ.Tensor)
    (r : Run σ) : Run τ :=
  ⟨t.mapOutcome tensor r.outcome, r.events.map t.mapEvent, r.states.map t.mapState⟩

theorem GraphTransport.run_inverse (t : GraphTransport σ τ) (tensor : σ.Tensor ≃ τ.Tensor)
    (r : Run σ) : t.symm.mapRun tensor.symm (t.mapRun tensor r) = r := by
  cases r with
  | mk outcome events states =>
    cases outcome <;>
      simp [mapRun, mapOutcome, List.map_map, Function.comp_def]

theorem GraphHistory.toRun_transport (t : GraphTransport σ τ)
    (tensor : σ.Tensor → τ.Tensor) (h : GraphHistory σ) :
    GraphHistory.toRun (t.history.apply h) = t.mapRun tensor h.toRun := by
  induction h with
  | done _ a => cases a; rfl
  | failed => rfl
  | step s e tail ih =>
      simp only [GraphHistory.toRun, Transport.apply, History.map,
        History.states, History.events, History.finish, GraphTransport.history,
        GraphTransport.mapRun, List.map_cons, Run.mk.injEq] at ih ⊢
      exact ⟨ih.1, congrArg (List.cons (t.mapEvent e)) ih.2.1,
        congrArg (List.cons (t.mapState s)) ih.2.2⟩

theorem GraphHistory.toRun_injective :
    Function.Injective (GraphHistory.toRun (σ := σ)) := by
  intro h k equal
  induction h generalizing k with
  | done s a =>
      cases a
      cases k <;> simp_all [toRun, History.finish, History.events, History.states]
  | failed s e f =>
      cases k with
      | done => simp [toRun, History.finish] at equal
      | failed => simp_all [toRun, History.finish, History.events, History.states]
      | step x y tail =>
          have hs := congrArg Run.states equal
          cases tail <;> simp [toRun, History.states] at hs
  | step s e tail ih =>
      cases k with
      | done => simp [toRun, History.events] at equal
      | failed =>
          have hs := congrArg Run.states equal
          cases tail <;> simp [toRun, History.states] at hs
      | step x y rest =>
          have he := congrArg Run.events equal
          have hs := congrArg Run.states equal
          have ho := congrArg Run.outcome equal
          simp only [toRun, History.events, List.cons.injEq] at he
          simp only [toRun, History.states, List.cons.injEq] at hs
          obtain ⟨rfl, he⟩ := he
          obtain ⟨rfl, hs⟩ := hs
          have ht : GraphHistory.toRun tail = GraphHistory.toRun rest := by
            simp only [toRun, Run.mk.injEq]
            exact ⟨ho, he, hs⟩
          rw [ih ht]

/-- Existing graph execution is embedded without changing its runner or its budget. -/
theorem GraphHistory.stepFuel_exists [DecidableEq σ.Tensor]
    (steps : List (Step σ)) (fuel : Nat)
    (state : State σ)
    (terminal : IndexedComponentExecution.SuccessfulOrFailed (stepFuel steps fuel state)) :
    ∃ h : GraphHistory σ, h.Admissible ∧ h.toRun = stepFuel steps fuel state ∧
      h.start = state := by
  induction fuel using Nat.strong_induction_on generalizing state with
  | h fuel ih =>
    rw [stepFuel] at terminal ⊢
    cases hc : complete steps state with
    | true =>
        exact ⟨.done state (), .done state, by
          simp [toRun, History.finish, History.events, History.states], rfl⟩
    | false =>
      cases hs : steps.find? (enabled state) with
      | none =>
          simp [IndexedComponentExecution.SuccessfulOrFailed, hc, hs] at terminal
      | some action =>
        cases fuel with
        | zero =>
            simp [IndexedComponentExecution.SuccessfulOrFailed, hc, hs] at terminal
        | succ n =>
          cases action with
          | write w =>
            cases hv : evalReady RationalReference.ops state.available w.body () with
            | notReady =>
                simp [IndexedComponentExecution.SuccessfulOrFailed,
                  hc, hs, hv] at terminal
            | evaluated value =>
              cases value with
              | none =>
                  exact ⟨.failed state (.undefined w.tag) w.tag, .failed state w.tag, by
                    simp [toRun, History.finish, History.events, History.states,
                      hv], rfl⟩
              | some value =>
                let next : State σ := {state with
                  produced := state.produced ++ [(w.capability, value)]}
                have ht : IndexedComponentExecution.SuccessfulOrFailed
                    (stepFuel steps n next) := by
                  simpa [IndexedComponentExecution.SuccessfulOrFailed,
                    hc, hs, hv, next] using terminal
                obtain ⟨h, ha, hr, _⟩ := ih n (Nat.lt_succ_self n) next ht
                refine ⟨.step state (.produced w.tag w.capability value) h,
                  .produced _ _ _ _ _ ha, ?_, rfl⟩
                simp only [Bool.false_eq_true, ↓reduceIte, hv]
                rw [← hr]
                rfl
          | collect a caps =>
            cases hv : caps.mapM (producedValue state) with
            | none =>
                simp [IndexedComponentExecution.SuccessfulOrFailed,
                  hc, hs, hv] at terminal
            | some values =>
              let value := values.foldl (· + ·) (0 : ℚ)
              letI := Program.Executor.addressEq (σ := σ)
              let next : State σ := {state with
                available := Function.update state.available a (some value)}
              have ht : IndexedComponentExecution.SuccessfulOrFailed
                  (stepFuel steps n next) := by
                simpa [IndexedComponentExecution.SuccessfulOrFailed,
                  hc, hs, hv, next, value] using terminal
              obtain ⟨h, ha, hr, _⟩ := ih n (Nat.lt_succ_self n) next ht
              refine ⟨.step state (.sealed a value) h, .sealed _ _ _ _ ha, ?_, rfl⟩
              simp only [Bool.false_eq_true, ↓reduceIte, hv]
              change toRun (.step state (.sealed a value) h) =
                ⟨(stepFuel steps n next).outcome,
                  .sealed a value :: (stepFuel steps n next).events,
                  state :: (stepFuel steps n next).states⟩
              rw [← hr]
              rfl

theorem GraphHistory.ranked_default_exists [Fintype σ.Tensor] [DecidableEq σ.Tensor]
    (A : MatchedComponent σ) (η : A.program.Input) (rank : A.program.RankCertificate) :
    ∃ h : GraphHistory σ, h.Admissible ∧
      h.toRun = runChecked A.contract A.fragment η.val ∧ h.start = initial η.val := by
  have terminal := IndexedComponentExecution.ranked_default_terminal A η rank
  rw [IndexedComponentExecution.checked_eq_stepFuel A.matched η] at terminal ⊢
  exact GraphHistory.stepFuel_exists _ _ _ terminal

structure CompleteObservation (σ : Declarations Unit) (Adapters : Type*) where
  metadata : GraphMetadata σ Adapters
  history : GraphHistory σ
  admissible : history.Admissible

def CompleteObservation.Agrees {Adapters Other : Type*}
    (t : MetadataTransport σ τ) (adapters : Adapters ≃ Other)
    (x : CompleteObservation σ Adapters) (y : CompleteObservation τ Other) : Prop :=
  t.Agrees adapters x.metadata y.metadata ∧
    y.history = t.toGraphTransport.history.apply x.history

section Reference

variable [Fintype σ.Tensor] [DecidableEq σ.Tensor]
variable {P : Program RationalReference.Carrier σ RationalReference.registry}
variable {schedule : Executor.Schedule P} {contract : Contract σ}
variable {fragment : Fragment σ} {graph : Closed σ}

/-- No part of `Running` is quotiented away: published, pending and accumulators
remain data. The graph side additionally retains the entire ordered ledger. -/
structure ReferenceSnapshot
    (M : SourceContractMatch P schedule contract fragment graph) where
  graphState : State σ
  running : P.Running
  ledger : LedgerInvariant M graphState
  relation : Relation M graphState running

structure ReferenceObservation
    (M : SourceContractMatch P schedule contract fragment graph) (Adapters : Type*) where
  observation : CompleteObservation σ Adapters
  start : P.Running
  result : Executor.Result P RationalReference.ops (.running start)
  correspondence : Correspondence.ExecutionCorrespondence M
    (GraphHistory.toRun observation.history) start result

/-- This explicitly exposes the full reference snapshots, including the terminal
failed state only once, using the existing normalization. -/
def ReferenceObservation.snapshots
    {M : SourceContractMatch P schedule contract fragment graph} {Adapters : Type*}
    (r : ReferenceObservation M Adapters) : List P.Running :=
  Correspondence.referenceSnapshots r.start r.result.events

theorem ReferenceObservation.full_relations
    {M : SourceContractMatch P schedule contract fragment graph} {Adapters : Type*}
    (r : ReferenceObservation M Adapters) :
    List.Forall₂ (fun g c => LedgerInvariant M g ∧ Relation M g c)
      r.observation.history.states r.snapshots := r.correspondence.states

end Reference

end Graph

namespace Fixtures

open History

def first : History Nat Nat Nat Unit := .step 0 10 (.done 1 ())

def second : Continuation Nat Nat Nat Unit Unit :=
  ⟨fun s _ => .step s 20 (.done (s + 1) ()), fun _ _ => rfl⟩

def third : Continuation Nat Nat Nat Unit Unit :=
  ⟨fun s _ => .step s 30 (.done (s + 1) ()), fun _ _ => rfl⟩

def privateFailure : History Nat Nat Nat Unit :=
  .step 0 10 (.step 1 11 (.failed 2 99 7))

example : ((first.splice second).splice third).events = [10, 20, 30] := rfl
example : ((first.splice second).splice third).states = [0, 1, 2, 3] := rfl
example : (first.splice second).splice third = first.splice (second.then third) :=
  splice_assoc _ _ _
example : ((.done 1 () : History Nat Nat Nat Unit).splice second).states = [1, 2] := rfl
example : (privateFailure.splice third).events = [10, 11, 99] := rfl
example : (privateFailure.splice third).states = [0, 1, 2] := rfl
example : (privateFailure.splice third).finish = .error (2, 7) := rfl
example : (first.splice second).states ≠ [0, 1, 1, 2] := by decide
example : (privateFailure.splice third).events ≠ [10, 99] := by decide
example : (first.splice second).events ≠ [20, 10] := by decide
example : ¬∃ k : Continuation Nat Nat Nat Unit Unit,
    k.run = (fun s _ => .done (s + 1) ()) := by
  rintro ⟨k, hk⟩
  have h := k.shared 0 ()
  simp [hk, History.start] at h

def swapping : Transport Nat Nat Nat Unit Nat Nat Nat Unit :=
  ⟨Equiv.swap 0 2, Equiv.swap 10 99, Equiv.swap 7 8, Equiv.refl _⟩

example : (swapping.apply privateFailure).events = [99, 11, 10] := by decide
example : (swapping.apply privateFailure).states = [2, 1, 0] := by decide
example : (swapping.apply privateFailure).finish = .error (0, 8) := by decide
example : swapping.symm.apply (swapping.apply privateFailure) = privateFailure :=
  Transport.apply_symm _ _
example : Transport.refl.apply privateFailure = privateFailure :=
  Transport.apply_refl _
example : swapping.apply (swapping.apply privateFailure) =
    (swapping.trans swapping).apply privateFailure := Transport.apply_trans _ _ _

example : (swapping.apply (first.splice second)).states =
    ((swapping.apply first).splice
      (swapping.continuation (Equiv.refl Unit) second)).states := by
  exact congrArg History.states (Transport.apply_splice _ _ _ _)

open LeanNCD.Semantics IndexedOpenComposition
open IndexedComponentCompositionLocalFixtures IndexedComponentCompositionPortFixtures

def ledgerLeft : State producerDeclarations :=
  ⟨fun _ => none, [(101, 1), (102, -1)]⟩

def ledgerRight : State producerDeclarations :=
  ⟨fun _ => none, [(102, -1), (101, 1)]⟩

def privateAvailable : State producerDeclarations :=
  ⟨fun _ => some 42, [(101, 1), (102, -1)]⟩

def graphIdentity : GraphTransport producerDeclarations producerDeclarations :=
  ⟨Equiv.refl _, Equiv.refl _⟩

example : (graphIdentity.mapState ledgerLeft).produced = [(101, 1), (102, -1)] := rfl
example : (graphIdentity.mapState privateAvailable).available ⟨0, ()⟩ = some 42 := rfl

example : ledgerLeft ≠ ledgerRight := by
  intro h
  have := congrArg State.produced h
  contradiction

example : ledgerLeft ≠ privateAvailable := by
  intro h
  have := congrArg (fun s : State producerDeclarations => s.available ⟨0, ()⟩) h
  contradiction

def emptyMetadata : GraphMetadata emptyProducerDeclarations Unit :=
  GraphMetadata.ofComponent emptyProducerComponent emptyValidatedInput ()

example : emptyMetadata.inputs.length = 1 := rfl
example : (emptyMetadata.input emptyExternalInput).isSome = true := rfl
example : ∀ a : Address emptyProducerDeclarations,
    (initial emptyPresentInput).available a = (initial emptyMissingInput).available a := by
  intro a
  exact Fin.elim0 a.2.1
example : emptyPresentInput ≠ emptyMissingInput := by
  intro h
  have := congrArg (fun f => (f emptyExternalInput).isSome) h
  contradiction

#print axioms History.splice_assoc
#print axioms History.success_cut
#print axioms Transport.apply_splice
#print axioms GraphHistory.stepFuel_exists
#print axioms GraphHistory.ranked_default_exists
#print axioms GraphHistory.toRun_injective
#print axioms ReferenceObservation.full_relations

end Fixtures

end IndexedOperationalHistory

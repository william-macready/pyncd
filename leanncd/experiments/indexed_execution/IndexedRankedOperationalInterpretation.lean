import IndexedRankedOperationalSource
import IndexedRankedOperationalReference
import IndexedOperationalWireFrame

namespace IndexedRankedOperationalInterpretation

open LeanNCD.Semantics IndexedOpenComposition IndexedComponentTransport IndexedWitness
open IndexedSource IndexedOperationalHistory IndexedRankedOperationalCore
open IndexedRankedOperationalCategory IndexedComponentExecution
open IndexedOperationalWireFrame
open IndexedComponentComposition
open IndexedOperationalHistoryComposition

variable {σ τ υ : Declarations Unit}

theorem state_ext {s t : State τ} (a : s.available = t.available)
    (p : s.produced = t.produced) : s = t := by
  cases s
  cases t
  cases a
  cases p
  rfl

/-- Local addresses and computational identities occupy fresh parts of an inherited frame.
The inherited ledger is an ordered prefix, not a set of capabilities. -/
structure Frame (σ τ : Declarations Unit) where
  place : Embedding σ τ
  identity : Nat ↪ Nat
  inherited : State τ
  fresh : ∀ row ∈ inherited.produced, ∀ n, row.1 ≠ identity n

noncomputable def Frame.state (f : Frame σ τ) (s : State σ) : State τ := by
  classical
  exact {
    available := fun b => if h : ∃ a, f.place.address a = b then
      s.available (Classical.choose h) else f.inherited.available b
    produced := f.inherited.produced ++ mapLedger f.identity s.produced }

theorem Frame.owned (f : Frame σ τ) (s : State σ) (a : Address σ) :
    (f.state s).available (f.place.address a) = s.available a := by
  classical
  have h : ∃ b, f.place.address b = f.place.address a := ⟨a, rfl⟩
  have eq := f.place.address_injective (Classical.choose_spec h)
  simp only [Frame.state, dif_pos h, eq]

theorem Frame.outside (f : Frame σ τ) (s : State σ) (b : Address τ)
    (outside : ¬ ∃ a, f.place.address a = b) :
    (f.state s).available b = f.inherited.available b := by
  classical
  exact dif_neg outside

theorem Frame.ledger (f : Frame σ τ) (s : State σ) :
    (f.state s).produced = f.inherited.produced ++ mapLedger f.identity s.produced := rfl

def Frame.event (f : Frame σ τ) : Event σ → Event τ :=
  mapEvent f.place f.identity

def Frame.scope (f : Frame σ τ) {X : Object} (scope : Scope X σ) : Scope X τ where
  tensor t := f.place.tensor (scope.tensor t)
  injective := f.place.injective.comp scope.injective
  domain t := (scope.domain t).comp (f.place.domain (scope.tensor t))

noncomputable def Frame.view (f : Frame σ τ) {X : Object} {scope : Scope X σ}
    {s : State σ} (v : AvailableView scope s) : AvailableView (f.scope scope) (f.state s) where
  env := v.env
  available t p := (f.owned s ⟨scope.tensor t, (scope.domain t).coord p⟩).trans
    (v.available t p)

def inputScope [Fintype σ.Tensor] [DecidableEq σ.Tensor] (A : MatchedComponent σ) :
    Scope (input A) σ where
  tensor t := t.val
  injective := Subtype.val_injective
  domain t := Domain.id (σ.signature t.val).axes

def outputScope [Fintype σ.Tensor] [DecidableEq σ.Tensor] (A : MatchedComponent σ) :
    Scope (output A) σ where
  tensor t := t.val
  injective := Subtype.val_injective
  domain t := Domain.id (σ.signature t.val).axes

def readEnv {X : Object} (scope : Scope X τ) (s : State τ) : X.interface.Env :=
  fun t p => (s.available ⟨scope.tensor t, (scope.domain t).coord p⟩).getD 0

theorem readEnv_view {X : Object} {scope : Scope X τ} {s : State τ}
    (v : AvailableView scope s) : readEnv scope s = v.env := by
  funext t p
  simp [readEnv, v.available]

def outputContinuation {X Y : Object} (scope : Scope X τ) (w : Wire X Y) :
    History.Continuation (State τ) (Event τ) Nat Unit Y.interface.Env :=
  ⟨fun s _ => .done s (w.env (readEnv scope s)), fun _ _ => rfl⟩

theorem outputContinuation_runWire {X Y : Object} {scope : Scope X τ} {s : State τ}
    (v : AvailableView scope s) (w : Wire X Y) :
    (outputContinuation scope w).run s () = runWire v w := by
  simp [outputContinuation, runWire, AvailableView.reindex, readEnv_view v]

variable [Fintype σ.Tensor] [DecidableEq σ.Tensor]

noncomputable def inputView (A : MatchedComponent σ) (η : A.program.Input) :
    AvailableView (inputScope A) (initial η.val) where
  env := inputEnv A η
  available t p := by
    change (η.val t.val).map (fun values => values p) = some ((inputEnv A η) t p)
    have h : (η.val t.val).isSome := by simpa [t.property] using η.property t.val
    exact (congrArg (fun z => z.map (fun values => values p)) (Option.some_get h)).symm

theorem actualHistory_full (A : MatchedComponent σ) (η : A.program.Input)
    (rank : A.program.RankCertificate) {s : State σ}
    (finished : (actualHistory A η rank).finish = .ok (s, ())) :
    ∃ store : Store RationalReference.Carrier σ, ∀ a, s.available a = some (store a) := by
  have run : (runChecked A.contract A.fragment η.val).outcome = .complete s := by
    rw [← (actualHistory_spec A η rank).2.1]
    simp [GraphHistory.toRun, finished]
  obtain ⟨c, done, full, _⟩ := Correspondence.completed_model A.matched η s run
  exact ⟨A.program.finalStore c done, full⟩

noncomputable def successfulView (A : MatchedComponent σ) (η : A.program.Input)
    (rank : A.program.RankCertificate) {s : State σ}
    (finished : (actualHistory A η rank).finish = .ok (s, ())) :
    AvailableView (outputScope A) s where
  env := fun t p => Classical.choose (actualHistory_full A η rank finished) ⟨t.val, p⟩
  available t p := Classical.choose_spec (actualHistory_full A η rank finished) ⟨t.val, p⟩

/-- Only the existing default actual history is lifted. No checked execution is started
on the inherited state. The suffix is justified by `successfulView` below. -/
noncomputable def computeHistory {X Y : Object} (A : MatchedComponent σ)
    (rank : A.program.RankCertificate) (before : Wire X (input A))
    (after : Wire (output A) Y) (f : Frame σ τ) (x : X.interface.Env) :
    History (State τ) (Event τ) Nat Y.interface.Env :=
  ((actualHistory A (externalInput A before x) rank).map f.state f.event f.identity id).splice
    (outputContinuation (f.scope (outputScope A)) after)

theorem computeHistory_start {X Y : Object} (A : MatchedComponent σ)
    (rank : A.program.RankCertificate) (before : Wire X (input A))
    (after : Wire (output A) Y) (f : Frame σ τ) (x : X.interface.Env) :
    (computeHistory A rank before after f x).start =
      f.state (initial (externalInput A before x).val) := by
  rw [computeHistory, History.splice, History.start_bind, History.start_map,
    (actualHistory_spec _ _ _).2.2]

theorem successful_suffix {X Y : Object} (A : MatchedComponent σ)
    (rank : A.program.RankCertificate) (before : Wire X (input A))
    (after : Wire (output A) Y) (f : Frame σ τ) (x : X.interface.Env) {s : State σ}
    (finished : (actualHistory A (externalInput A before x) rank).finish = .ok (s, ())) :
    (outputContinuation (f.scope (outputScope A)) after).run (f.state s) () =
      runWire (f.view (successfulView A _ rank finished)) after :=
  outputContinuation_runWire _ _

def Frame.FreshInput (f : Frame σ τ) (A : MatchedComponent σ) (η : A.program.Input) :
    Prop :=
  ∀ a, f.inherited.available (f.place.address a) = (initial η.val).available a

theorem Frame.initial_eq (f : Frame σ τ) (A : MatchedComponent σ) (η : A.program.Input)
    (fresh : f.FreshInput A η) : f.state (initial η.val) = f.inherited := by
  classical
  have ha : (f.state (initial η.val)).available = f.inherited.available := by
    funext b
    by_cases h : ∃ a, f.place.address a = b
    · obtain ⟨a, rfl⟩ := h
      exact (f.owned _ a).trans (fresh a).symm
    · exact f.outside _ b h
  apply state_ext
  · exact ha
  · simp [Frame.state, initial, mapLedger]

theorem computeHistory_inherited_start {X Y : Object} (A : MatchedComponent σ)
    (rank : A.program.RankCertificate) (before : Wire X (input A))
    (after : Wire (output A) Y) (f : Frame σ τ) (x : X.interface.Env)
    (fresh : f.FreshInput A (externalInput A before x)) :
    (computeHistory A rank before after f x).start = f.inherited :=
  (computeHistory_start A rank before after f x).trans (f.initial_eq A _ fresh)

/-- This relation has both administrative and actual-computation constructors.
In particular there is no arbitrary admissible-history constructor. -/
inductive Realizes : {X Y : Object} → Normal X Y → Scope X τ → State τ →
    X.interface.Env → History (State τ) (Event τ) Nat Y.interface.Env → Prop
  | admin {X Y : Object} {scope : Scope X τ} {s : State τ}
      (w : Wire X Y) (v : AvailableView scope s) :
      Realizes (.admin w) scope s v.env (runWire v w)
  | compute {X Y : Object} {σ : Declarations Unit}
      [Fintype σ.Tensor] [DecidableEq σ.Tensor]
      (A : MatchedComponent σ) (rank : A.program.RankCertificate)
      (origin : Origin A) (before : Wire X (input A)) (after : Wire (output A) Y)
      (f : Frame σ τ) (x : X.interface.Env)
      (fresh : f.FreshInput A (externalInput A before x)) :
      Realizes (.compute A rank origin before after)
        ((f.scope (inputScope A)).reindex before.inverse) f.inherited x
        (computeHistory A rank before after f x)

theorem realizes_identity {X : Object} {scope : Scope X τ} {s : State τ}
    (v : AvailableView scope s) :
    Realizes (Normal.identity X) scope s v.env (.done s v.env) := by
  simpa only [Normal.identity, runWire_identity] using Realizes.admin (Wire.identity X) v

theorem realizes_wire {X Y : Object} {scope : Scope X τ} {s : State τ}
    (v : AvailableView scope s) (w : Wire X Y) :
    Realizes (.admin w) scope s v.env (.done s (w.env v.env)) :=
  Realizes.admin w v

theorem compute_pre_wire {W X Y : Object} (A : MatchedComponent σ)
    (rank : A.program.RankCertificate) (before : Wire X (input A))
    (after : Wire (output A) Y) (f : Frame σ τ) (x : W.interface.Env)
    (w : Wire W X) {scope : Scope W τ} (v : AvailableView scope f.inherited)
    (env : v.env = x) :
    (runWire v w).bind (fun _ y => computeHistory A rank before after f y) =
      computeHistory A rank (w.comp before) after f x := by
  simp only [runWire, AvailableView.reindex, History.bind, env]
  rfl

theorem compute_post_wire {X Y Z : Object} (A : MatchedComponent σ)
    (rank : A.program.RankCertificate) (before : Wire X (input A))
    (after : Wire (output A) Y) (f : Frame σ τ) (x : X.interface.Env)
    (w : Wire Y Z) :
    (computeHistory A rank before after f x).bind (fun s y => .done s (w.env y)) =
      computeHistory A rank before (after.comp w) f x := by
  unfold computeHistory History.splice
  rw [History.bind_assoc]
  simp [outputContinuation, History.bind, Wire.env_comp]

theorem compute_failure {X Y : Object} (A : MatchedComponent σ)
    (rank : A.program.RankCertificate) (before : Wire X (input A))
    (after : Wire (output A) Y) (f : Frame σ τ) (x : X.interface.Env)
    {s : State σ} {tag : Nat}
    (failed : (actualHistory A (externalInput A before x) rank).finish = .error (s, tag)) :
    (computeHistory A rank before after f x).finish =
      .error (f.state s, f.identity tag) := by
  unfold computeHistory
  apply (History.failure_absorbs _ _ ?_).2.2
  rw [finish_map, failed]

structure Coherent (t : GraphTransport σ υ) (f : Frame σ τ) (g : Frame υ τ) : Prop where
  address : ∀ a, g.place.address (t.address a) = f.place.address a
  identity : ∀ n, g.identity (t.identity n) = f.identity n
  inherited : g.inherited = f.inherited

theorem Coherent.state {t : GraphTransport σ υ} {f : Frame σ τ} {g : Frame υ τ}
    (h : Coherent t f g) (s : State σ) : g.state (t.mapState s) = f.state s := by
  classical
  apply state_ext
  · funext b
    by_cases owned : ∃ a, f.place.address a = b
    · obtain ⟨a, rfl⟩ := owned
      rw [← h.address a, g.owned, h.address a, f.owned]
      simp [GraphTransport.mapState]
    · rw [f.outside _ _ owned, g.outside]
      · exact congrArg (fun s : State τ => s.available b) h.inherited
      · rintro ⟨a, ha⟩
        apply owned
        refine ⟨t.address.symm a, ?_⟩
        rw [← h.address, Equiv.apply_symm_apply, ha]
  · simp only [Frame.state, GraphTransport.mapState, h.inherited, mapLedger, List.map_map]
    congr 1
    apply List.map_congr_left
    intro row _
    simp [Function.comp_def, h.identity]

theorem Coherent.event {t : GraphTransport σ υ} {f : Frame σ τ} {g : Frame υ τ}
    (h : Coherent t f g) (e : Event σ) : g.event (t.mapEvent e) = f.event e := by
  cases e <;> simp [Frame.event, mapEvent, GraphTransport.mapEvent, h.address, h.identity]

theorem Coherent.history {t : GraphTransport σ υ} {f : Frame σ τ} {g : Frame υ τ}
    (h : Coherent t f g) (a : GraphHistory σ) :
    (t.history.apply a).map g.state g.event g.identity id =
      a.map f.state f.event f.identity id := by
  induction a <;> simp_all [Transport.apply, GraphTransport.history, History.map,
    GraphTransport.stateEquiv, GraphTransport.eventEquiv, h.state, h.event, h.identity]

variable [Fintype υ.Tensor] [DecidableEq υ.Tensor]

theorem coherent_output {Y : Object} (A : MatchedComponent σ) (B : MatchedComponent υ)
    (afterA : Wire (output A) Y) (afterB : Wire (output B) Y)
    (t : MetadataTransport σ υ) (f : Frame σ τ) (g : Frame υ τ)
    (coherent : Coherent t.toGraphTransport f g)
    (square : reindexExterior t (outputExterior A afterA) = outputExterior B afterB)
    (s : State τ) :
    afterB.env (readEnv (g.scope (outputScope B)) s) =
      afterA.env (readEnv (f.scope (outputScope A)) s) := by
  funext y p
  have localAddress := congrArg (locatedAddress p) (congrFun square y)
  have located : t.toGraphTransport.address
      (locatedAddress p (outputExterior A afterA y)) =
      locatedAddress p (outputExterior B afterB y) := by
    rw [t.address_eq]
    exact localAddress
  have ambient := coherent.address (locatedAddress p (outputExterior A afterA y))
  rw [located] at ambient
  change (s.available (g.place.address (locatedAddress p (outputExterior B afterB y)))).getD 0 =
    (s.available (f.place.address (locatedAddress p (outputExterior A afterA y)))).getD 0
  rw [ambient]

theorem compute_history_congruence {X Y : Object}
    (A : MatchedComponent σ) (B : MatchedComponent υ)
    (rA : A.program.RankCertificate) (rB : B.program.RankCertificate)
    (oa : Origin A) (ob : Origin B)
    (beforeA : Wire X (input A)) (afterA : Wire (output A) Y)
    (beforeB : Wire X (input B)) (afterB : Wire (output B) Y)
    (t : MetadataTransport σ υ) (e : oa.Adapters ≃ ob.Adapters)
    (actual : ∀ x : X.interface.Env,
      (actualObservation A oa (externalInput A beforeA x) rA).Agrees t e
        (actualObservation B ob (externalInput B beforeB x) rB))
    (square : reindexExterior t (outputExterior A afterA) = outputExterior B afterB)
    (f : Frame σ τ) (g : Frame υ τ) (coherent : Coherent t.toGraphTransport f g)
    (x : X.interface.Env) :
    computeHistory B rB beforeB afterB g x = computeHistory A rA beforeA afterA f x := by
  have histories := (actual x).2
  change actualHistory B (externalInput B beforeB x) rB =
    t.toGraphTransport.history.apply (actualHistory A (externalInput A beforeA x) rA) at histories
  unfold computeHistory
  rw [histories, coherent.history]
  unfold History.splice
  congr 1
  funext s u
  cases u
  exact congrArg (History.done s) (coherent_output A B afterA afterB t f g coherent square s)

/-- In contrast to normalized-syntax equality, this observation includes equality
of lifted full histories for every structurally coherent inherited frame. -/
def HistoryAgrees : {X Y : Object} → Normal X Y → Normal X Y → Prop
  | _, _, .admin a, .admin b => a = b ∧
      ∀ (scope : Scope _ τ) (s : State τ) (v : AvailableView scope s),
        runWire v a = runWire v b
  | _, _, @Normal.compute _ _ _ _ _ A rA oa beforeA afterA,
      @Normal.compute _ _ _ _ _ B rB ob beforeB afterB =>
      ∃ (t : MetadataTransport _ _) (e : oa.Adapters ≃ ob.Adapters),
        ProvenanceIso oa ob t e ∧
        reindexExterior t (inputExterior A beforeA) = inputExterior B beforeB ∧
        reindexExterior t (outputExterior A afterA) = outputExterior B afterB ∧
        (∀ x, (actualObservation A oa (externalInput A beforeA x) rA).Agrees t e
          (actualObservation B ob (externalInput B beforeB x) rB)) ∧
        ∀ (f : Frame _ τ) (g : Frame _ τ), Coherent t.toGraphTransport f g →
          ∀ x, computeHistory B rB beforeB afterB g x = computeHistory A rA beforeA afterA f x
  | _, _, _, _ => False

theorem agrees_history {X Y : Object} {a b : Normal X Y} (h : Agrees a b) :
    HistoryAgrees (τ := τ) a b := by
  cases a <;> cases b
  · exact ⟨h, fun _ _ _ => congrArg (runWire _) h⟩
  · exact False.elim h
  · exact False.elim h
  · obtain ⟨t, e, origin, before, after, actual⟩ := h
    exact ⟨t, e, origin, before, after, actual,
      fun f g coherent x => compute_history_congruence _ _ _ _ _ _ _ _ _ _
        t e actual after f g coherent x⟩

theorem target_history {X Y : Object} (a b : Normal X Y)
    (equal : (Quotient.mk (normalSetoid X Y) a : Arrow X Y) = Quotient.mk _ b) :
    HistoryAgrees (τ := τ) a b :=
  agrees_history (Quotient.exact equal)

def SourceRealizes {X Y : IndexedRankedOperationalSource.Object}
    (term : IndexedRankedOperationalSource.Term X Y) (scope : Scope X.base τ)
    (s : State τ) (x : X.base.interface.Env)
    (h : History (State τ) (Event τ) Nat Y.base.interface.Env) : Prop :=
  Realizes term.normalize scope s x h

theorem source_history {X Y : IndexedRankedOperationalSource.Object}
    {a b : IndexedRankedOperationalSource.Term X Y}
    (h : IndexedRankedOperationalSource.Rel a b) :
    HistoryAgrees (τ := τ) a.normalize b.normalize :=
  agrees_history (IndexedRankedOperationalSource.sound h)

theorem semantics_history {X Y : IndexedRankedOperationalSource.Object}
    (a b : IndexedRankedOperationalSource.Term X Y)
    (equal : IndexedRankedOperationalSource.semantics.map
        (IndexedRankedOperationalSource.arrow a) =
      IndexedRankedOperationalSource.semantics.map
        (IndexedRankedOperationalSource.arrow b)) :
    HistoryAgrees (τ := τ) a.normalize b.normalize :=
  target_history _ _ equal

theorem source_identity {X : IndexedRankedOperationalSource.Object}
    {scope : Scope X.base τ} {s : State τ} (v : AvailableView scope s) :
    SourceRealizes (.identity X) scope s v.env (.done s v.env) :=
  realizes_identity v

theorem source_wire {X Y : IndexedRankedOperationalSource.Object}
    {scope : Scope X.base τ} {s : State τ} (v : AvailableView scope s)
    (w : Wire X.base Y.base) :
    SourceRealizes (.wire w) scope s v.env (runWire v w) :=
  Realizes.admin w v

theorem realizes_wire_composition {X Y Z : Object} {scope : Scope X τ} {s : State τ}
    (v : AvailableView scope s) (a : Wire X Y) (b : Wire Y Z) :
    Realizes ((Normal.admin a).comp (.admin b)) scope s v.env
      ((runWire v a).bind (fun s env => .done s (b.env env))) := by
  rw [runWire_composition]
  exact Realizes.admin (a.comp b) v

theorem realizes_wire_inverse {X Y : Object} {scope : Scope X τ} {s : State τ}
    (v : AvailableView scope s) (a : Wire X Y) :
    Realizes (Normal.identity X) scope s v.env
      ((runWire v a).bind (fun s env => .done s (a.inverse.env env))) := by
  rw [runWire_inverse]
  exact realizes_identity v

theorem compute_input_view {X : Object} (A : MatchedComponent σ)
    (before : Wire X (input A)) (f : Frame σ τ) (x : X.interface.Env)
    (fresh : f.FreshInput A (externalInput A before x)) :
    ∃ v : AvailableView ((f.scope (inputScope A)).reindex before.inverse) f.inherited,
      v.env = x := by
  let v := (f.view (inputView A (externalInput A before x))).reindex before.inverse
  have env : v.env = x := by
    change before.inverse.env (inputEnv A (envInput A (before.env x))) = x
    rw [inputEnv_envInput, Wire.env_inverse, Equiv.symm_apply_apply]
  have start := f.initial_eq A (externalInput A before x) fresh
  refine ⟨⟨x, ?_⟩, rfl⟩
  intro t p
  rw [← start]
  simpa only [env] using v.available t p

theorem realizes_pre_wire {W X Y : Object} (A : MatchedComponent σ)
    (rank : A.program.RankCertificate) (origin : Origin A)
    (before : Wire X (input A)) (after : Wire (output A) Y)
    (f : Frame σ τ) (x : W.interface.Env) (w : Wire W X)
    (fresh : f.FreshInput A (externalInput A (w.comp before) x))
    (v : AvailableView ((f.scope (inputScope A)).reindex (w.comp before).inverse) f.inherited)
    (env : v.env = x) :
    Realizes ((Normal.admin w).comp (.compute A rank origin before after))
      ((f.scope (inputScope A)).reindex (w.comp before).inverse) f.inherited x
      ((runWire v w).bind (fun _ y => computeHistory A rank before after f y)) := by
  rw [compute_pre_wire A rank before after f x w v env]
  exact Realizes.compute A rank origin (w.comp before) after f x fresh

theorem realizes_post_wire {X Y Z : Object} (A : MatchedComponent σ)
    (rank : A.program.RankCertificate) (origin : Origin A)
    (before : Wire X (input A)) (after : Wire (output A) Y)
    (f : Frame σ τ) (x : X.interface.Env) (w : Wire Y Z)
    (fresh : f.FreshInput A (externalInput A before x)) :
    Realizes ((Normal.compute A rank origin before after).comp (.admin w))
      ((f.scope (inputScope A)).reindex before.inverse) f.inherited x
      ((computeHistory A rank before after f x).bind (fun s y => .done s (w.env y))) := by
  rw [compute_post_wire]
  exact Realizes.compute A rank origin before (after.comp w) f x fresh

theorem realizes_start {X Y : Object} {n : Normal X Y} {scope : Scope X τ}
    {s : State τ} {x : X.interface.Env}
    {h : History (State τ) (Event τ) Nat Y.interface.Env}
    (real : Realizes n scope s x h) : h.start = s := by
  cases real with
  | admin w v => rfl
  | compute A rank origin before after f x fresh =>
      exact computeHistory_inherited_start A rank before after f x fresh

theorem realizes_input {X Y : Object} {n : Normal X Y} {scope : Scope X τ}
    {s : State τ} {x : X.interface.Env}
    {h : History (State τ) (Event τ) Nat Y.interface.Env}
    (real : Realizes n scope s x h) :
    ∃ v : AvailableView scope s, v.env = x := by
  cases real with
  | admin w v => exact ⟨v, rfl⟩
  | compute A rank origin before after f x fresh =>
      exact compute_input_view A before f x fresh

theorem compute_history_exact {X Y : Object} (A : MatchedComponent σ)
    (rank : A.program.RankCertificate) (before : Wire X (input A))
    (after : Wire (output A) Y) (f : Frame σ τ) (x : X.interface.Env) :
    (computeHistory A rank before after f x).map id id id (fun _ => ()) =
      (actualHistory A (externalInput A before x) rank).map f.state f.event f.identity id := by
  unfold computeHistory History.splice
  generalize actualHistory A (externalInput A before x) rank = h
  induction h <;> simp_all [History.map, History.bind, outputContinuation]

theorem compute_states_events {X Y : Object} (A : MatchedComponent σ)
    (rank : A.program.RankCertificate) (before : Wire X (input A))
    (after : Wire (output A) Y) (f : Frame σ τ) (x : X.interface.Env) :
    (computeHistory A rank before after f x).states =
        (actualHistory A (externalInput A before x) rank).states.map f.state ∧
      (computeHistory A rank before after f x).events =
        (actualHistory A (externalInput A before x) rank).events.map f.event := by
  have hs := congrArg History.states (compute_history_exact A rank before after f x)
  have he := congrArg History.events (compute_history_exact A rank before after f x)
  simpa only [History.states_map, History.events_map, List.map_id] using And.intro hs he

def upstreamOutputScope (A : MatchedComponent σ) (B : MatchedComponent υ) :
    Scope (output A) (declarations A B) where
  tensor t := (upstream A B).tensor t.val
  injective := (upstream A B).injective.comp Subtype.val_injective
  domain t := (upstream A B).domain t.val

noncomputable def cutView (A : MatchedComponent σ) (B : MatchedComponent υ)
    (s : State σ) (store : Store RationalReference.Carrier σ)
    (full : ∀ a, s.available a = some (store a)) :
    AvailableView (upstreamOutputScope A B) (upstreamState A B s) where
  env := fun t p => store ⟨t.val, p⟩
  available t p := full ⟨t.val, p⟩

theorem interior_wire_neutral {X : Object} (scope : Scope X τ)
    (h k : GraphHistory τ) :
    h.bind (fun s _ =>
      ((outputContinuation scope (Wire.identity X)).run s ()).bind (fun _ _ => k)) =
      SharedSplice.append h k := rfl

/-- This cut is obtained from the actual binary run. On failure no output view
or suffix exists; on success the supplied original boundary reindexes a full view. -/
theorem actual_join_identity (A : MatchedComponent σ) (B : MatchedComponent υ)
    (w : Wire (output A) (input B)) (η : A.program.Input)
    (rA : A.program.RankCertificate) (rB : B.program.RankCertificate) :
    let b := connectingBoundary A B w
    let source := actualHistory A η rA
    let result := actualHistory (compose A B b) (liftInput A B b η)
      (compositeRankCertificate A B b rA rB)
    (∃ s tag, source.finish = .error (s, tag) ∧ result = liftUpstream A B source) ∨
    ∃ (s : State σ) (store : Store RationalReference.Carrier σ)
      (suffix : GraphHistory (declarations A B))
      (v : AvailableView ((upstreamOutputScope A B).reindex w) (upstreamState A B s)),
      source.finish = .ok (s, ()) ∧
      (∀ a, s.available a = some (store a)) ∧
      suffix.start = upstreamState A B s ∧
      (outputContinuation ((upstreamOutputScope A B).reindex w)
        (Wire.identity (input B))).run (upstreamState A B s) () =
          runWire v (Wire.identity (input B)) ∧
      result = (liftUpstream A B source).bind (fun cut _ =>
        ((outputContinuation ((upstreamOutputScope A B).reindex w)
          (Wire.identity (input B))).run cut ()).bind (fun _ _ => suffix)) := by
  dsimp only
  generalize resultEq : actualHistory (compose A B (connectingBoundary A B w))
    (liftInput A B (connectingBoundary A B w) η)
    (compositeRankCertificate A B (connectingBoundary A B w) rA rB) = result
  have binary := actual_binary A B w η rA rB
  rw [resultEq] at binary
  cases binary with
  | failed tag endpoint failed => exact .inl ⟨endpoint, tag, failed, rfl⟩
  | complete s store suffix finished full admitted run shared =>
      refine .inr ⟨s, store, liftDownstream A B (connectingBoundary A B w) s suffix,
        (cutView A B s store full).reindex w, finished, full, shared, ?_, ?_⟩
      · exact outputContinuation_runWire _ _
      · exact (interior_wire_neutral _ _ _).symm

end IndexedRankedOperationalInterpretation

import IndexedOperationalHistory
import IndexedSourceWire

namespace IndexedOperationalWireFrame

open LeanNCD.Semantics IndexedOpenComposition
open IndexedComponentTransport IndexedOperationalHistory IndexedSource

structure Scope (X : Object) (σ : Declarations Unit) where
  tensor : X.interface.Tensor → σ.Tensor
  injective : Function.Injective tensor
  domain : ∀ t, Domain (X.interface.signature t).axes (σ.signature (tensor t)).axes

def Scope.reindex {X Y : Object} {σ : Declarations Unit}
    (scope : Scope X σ) (wire : Wire X Y) : Scope Y σ where
  tensor t := scope.tensor (wire.ports t)
  injective := scope.injective.comp wire.ports.injective
  domain t := (wire.domain t).comp (scope.domain (wire.ports t))

structure AvailableView {X : Object} {σ : Declarations Unit}
    (scope : Scope X σ) (state : State σ) where
  env : X.interface.Env
  available : ∀ t p,
    state.available ⟨scope.tensor t, (scope.domain t).coord p⟩ = some (env t p)

def AvailableView.reindex {X Y : Object} {σ : Declarations Unit}
    {scope : Scope X σ} {state : State σ} (view : AvailableView scope state)
    (wire : Wire X Y) : AvailableView (scope.reindex wire) state where
  env := wire.env view.env
  available t p := by
    change state.available
      ⟨scope.tensor (wire.ports t),
        (scope.domain (wire.ports t)).coord ((wire.domain t).coord p)⟩ =
      some ((wire.env view.env) t p)
    simpa only [Wire.env_apply] using view.available (wire.ports t) ((wire.domain t).coord p)

def runWire {X Y : Object} {σ : Declarations Unit}
    {scope : Scope X σ} {state : State σ} (view : AvailableView scope state)
    (wire : Wire X Y) : History (State σ) (Event σ) Nat Y.interface.Env :=
  .done state (view.reindex wire).env

theorem runWire_start {X Y : Object} {σ : Declarations Unit}
    {scope : Scope X σ} {state : State σ} (view : AvailableView scope state)
    (wire : Wire X Y) : (runWire view wire).start = state := rfl

theorem runWire_states {X Y : Object} {σ : Declarations Unit}
    {scope : Scope X σ} {state : State σ} (view : AvailableView scope state)
    (wire : Wire X Y) : (runWire view wire).states = [state] := rfl

theorem runWire_events {X Y : Object} {σ : Declarations Unit}
    {scope : Scope X σ} {state : State σ} (view : AvailableView scope state)
    (wire : Wire X Y) : (runWire view wire).events = [] := rfl

theorem scope_identity {X : Object} {σ : Declarations Unit}
    (scope : Scope X σ) : scope.reindex (Wire.identity X) = scope := by
  cases scope
  rfl

theorem scope_composition {X Y Z : Object} {σ : Declarations Unit}
    (scope : Scope X σ) (a : Wire X Y) (b : Wire Y Z) :
    (scope.reindex a).reindex b = scope.reindex (a.comp b) := rfl

theorem runWire_identity {X : Object} {σ : Declarations Unit}
    {scope : Scope X σ} {state : State σ} (view : AvailableView scope state) :
    runWire view (Wire.identity X) = .done state view.env := by
  simp [runWire, AvailableView.reindex, Wire.env_identity]

theorem runWire_composition {X Y Z : Object} {σ : Declarations Unit}
    {scope : Scope X σ} {state : State σ} (view : AvailableView scope state)
    (a : Wire X Y) (b : Wire Y Z) :
    (runWire view a).bind (fun s env => .done s (b.env env)) =
      runWire view (a.comp b) := by
  simp [runWire, AvailableView.reindex, History.bind, Wire.env_comp]

theorem runWire_inverse {X Y : Object} {σ : Declarations Unit}
    {scope : Scope X σ} {state : State σ} (view : AvailableView scope state)
    (wire : Wire X Y) :
    (runWire view wire).bind (fun s env => .done s (wire.inverse.env env)) =
      .done state view.env := by
  simp [runWire, AvailableView.reindex, History.bind, Wire.env_inverse]

#print axioms AvailableView.reindex
#print axioms scope_identity
#print axioms scope_composition
#print axioms runWire_identity
#print axioms runWire_composition
#print axioms runWire_inverse

end IndexedOperationalWireFrame

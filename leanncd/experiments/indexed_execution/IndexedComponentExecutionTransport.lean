import IndexedComponentComposition
import IndexedComponentTransportEval

namespace IndexedComponentExecution

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open IndexedOpenComposition
open IndexedComponentTransport
open IndexedComponentComposition

variable {src dst : Declarations Unit}

def mapLedger (rename : Nat → Nat) (rows : List (Nat × ℚ)) : List (Nat × ℚ) :=
  rows.map fun row => (rename row.1, row.2)

def mapEvent (f : Embedding src dst) (rename : Nat → Nat) : Event src → Event dst
  | .produced tag cap value => .produced (rename tag) (rename cap) value
  | .sealed a value => .sealed (f.address a) value
  | .undefined tag => .undefined (rename tag)

structure Projection (f : Embedding src dst) (rename : Nat → Nat)
    (ledgerPrefix : List (Nat × ℚ)) (source : State src) (target : State dst) : Prop where
  available : ∀ a, target.available (f.address a) = source.available a
  produced : target.produced = ledgerPrefix ++ mapLedger rename source.produced

theorem producedValue_projection (f : Embedding src dst) (rename : Nat → Nat)
    (injective : Function.Injective rename) (ledgerPrefix : List (Nat × ℚ))
    (outside : ∀ row ∈ ledgerPrefix, ∀ cap, row.1 ≠ rename cap)
    {source : State src} {target : State dst}
    (related : Projection f rename ledgerPrefix source target)
    (cap : Nat) :
    producedValue target (rename cap) = producedValue source cap := by
  unfold producedValue
  rw [related.produced, List.find?_append]
  have hp : ledgerPrefix.find? (fun row => row.1 == rename cap) = none := by
    apply List.find?_eq_none.mpr
    intro row hr
    simpa using outside row hr cap
  rw [hp]
  have hm : (mapLedger rename source.produced).find?
      (fun row => row.1 == rename cap) =
      (source.produced.find? (fun row => row.1 == cap)).map
        (fun row => (rename row.1, row.2)) := by
    induction source.produced with
    | nil => rfl
    | cons row rows ih =>
        by_cases h : row.1 = cap
        · simp [mapLedger, List.find?, h]
        · have hn := injective.ne h
          have hb : (row.1 == cap) = false :=
            Bool.eq_false_iff.mpr (fun ht => h (beq_iff_eq.mp ht))
          have hbn : (rename row.1 == rename cap) = false :=
            Bool.eq_false_iff.mpr (fun ht => hn (beq_iff_eq.mp ht))
          simpa only [mapLedger, List.map_cons, List.find?_cons, hbn,
            hb, ↓reduceIte] using ih
  rw [hm]
  cases source.produced.find? (fun row => row.1 == cap) <;> rfl

theorem enabled_projection (f : Embedding src dst) (rename : Nat → Nat)
    (injective : Function.Injective rename) (ledgerPrefix : List (Nat × ℚ))
    (outside : ∀ row ∈ ledgerPrefix, ∀ cap, row.1 ≠ rename cap)
    {source : State src} {target : State dst}
    (related : Projection f rename ledgerPrefix source target)
    (step : Step src) :
    enabled target (mapStep f rename step) = enabled source step := by
  have hp := producedValue_projection f rename injective ledgerPrefix outside related
  cases step with
  | write w =>
      simp [mapStep, mapWriter, enabled, hp, List.all_map, related.available,
        Function.comp_def]
  | collect a caps =>
      simp [mapStep, enabled, hp, List.all_map, related.available, Function.comp_def]

theorem complete_projection (f : Embedding src dst) (rename : Nat → Nat)
    (injective : Function.Injective rename) (ledgerPrefix : List (Nat × ℚ))
    (outside : ∀ row ∈ ledgerPrefix, ∀ cap, row.1 ≠ rename cap)
    {source : State src} {target : State dst}
    (related : Projection f rename ledgerPrefix source target)
    (steps : List (Step src)) :
    complete (steps.map (mapStep f rename)) target = complete steps source := by
  have hp := producedValue_projection f rename injective ledgerPrefix outside related
  simp only [complete, List.all_map]
  apply congrArg (fun predicate : Step src → Bool => steps.all predicate)
  funext step
  cases step <;> simp [mapStep, mapWriter, Function.comp_def, hp, related.available]

theorem evalReady_projection (f : Embedding src dst) (rename : Nat → Nat)
    (ledgerPrefix : List (Nat × ℚ)) {source : State src} {target : State dst}
    (related : Projection f rename ledgerPrefix source target) (w : Writer src) :
    evalReady RationalReference.ops target.available (mapWriter f rename w).body () =
      evalReady RationalReference.ops source.available w.body () := by
  rw [mapWriter, evalReady_transport]
  have he : f.pull target.available = source.available := funext related.available
  rw [he]

theorem selected_projection (f : Embedding src dst) (rename : Nat → Nat)
    (injective : Function.Injective rename) (ledgerPrefix : List (Nat × ℚ))
    (outside : ∀ row ∈ ledgerPrefix, ∀ cap, row.1 ≠ rename cap)
    {source : State src} {target : State dst}
    (related : Projection f rename ledgerPrefix source target)
    (steps : List (Step src)) (suffix : List (Step dst)) (step : Step src)
    (selected : steps.find? (enabled source) = some step) :
    (steps.map (mapStep f rename) ++ suffix).find? (enabled target) =
      some (mapStep f rename step) := by
  have he : enabled target ∘ mapStep f rename = enabled source :=
    funext (enabled_projection f rename injective ledgerPrefix outside related)
  simp [List.find?_append, List.find?_map, he, selected]

theorem collector_values_projection (f : Embedding src dst) (rename : Nat → Nat)
    (injective : Function.Injective rename) (ledgerPrefix : List (Nat × ℚ))
    (outside : ∀ row ∈ ledgerPrefix, ∀ cap, row.1 ≠ rename cap)
    {source : State src} {target : State dst}
    (related : Projection f rename ledgerPrefix source target) (caps : List Nat) :
    (caps.map rename).mapM (producedValue target) =
      caps.mapM (producedValue source) := by
  induction caps with
  | nil => rfl
  | cons cap caps ih =>
      simp [producedValue_projection f rename injective ledgerPrefix outside related, ih]

theorem projection_produce (f : Embedding src dst) (rename : Nat → Nat)
    (ledgerPrefix : List (Nat × ℚ)) {source : State src} {target : State dst}
    (related : Projection f rename ledgerPrefix source target) (cap : Nat) (value : ℚ) :
    Projection f rename ledgerPrefix
      { source with produced := source.produced ++ [(cap, value)] }
      { target with produced := target.produced ++ [(rename cap, value)] } := by
  refine ⟨related.available, ?_⟩
  simp [related.produced, mapLedger, List.map_append, List.append_assoc]

variable [DecidableEq src.Tensor] [DecidableEq dst.Tensor]

theorem projection_collect (f : Embedding src dst) (rename : Nat → Nat)
    (ledgerPrefix : List (Nat × ℚ)) {source : State src} {target : State dst}
    (related : Projection f rename ledgerPrefix source target) (a : Address src) (value : ℚ) :
    letI := Executor.addressEq (σ := src)
    letI := Executor.addressEq (σ := dst)
    Projection f rename ledgerPrefix
      { source with available := Function.update source.available a (some value) }
      { target with available := Function.update target.available (f.address a) (some value) } := by
  letI := Executor.addressEq (σ := src)
  letI := Executor.addressEq (σ := dst)
  refine ⟨?_, related.produced⟩
  intro b
  by_cases h : b = a
  · subst b
    simp
  · have hn := f.address_injective.ne h
    simp [Function.update_apply, h, hn, related.available]

end IndexedComponentExecution

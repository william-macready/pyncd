import LeanNCD.Semantics.Source.Program
import LeanNCD.Semantics.Source.Carrier
import LeanNCD.Semantics.ReferenceExecutor
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma

namespace LeanNCD.Semantics.Source

open Program.Executor

def sourceTensors (source : AdmittedSource) : List source.source.table.declarations.Tensor :=
  List.finRange source.source.table.entries.length

theorem sourceTensors_nodup (source : AdmittedSource) : (sourceTensors source).Nodup :=
  List.nodup_finRange _

theorem sourceTensors_complete (source : AdmittedSource)
    (t : source.source.table.declarations.Tensor) : t ∈ sourceTensors source :=
  List.mem_finRange t

section Generic

/-! S2b: the schedule is carrier-generic (`source.program r` at any semiring `K`); the real names
below are abbreviations at `RationalReference.registry`, so every existing caller is unchanged. -/

variable {K : Type} [Semiring K]

def sourceDefinedAt (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) : List (source.program r).Defined :=
  (sourceTensors source).filterMap fun t =>
    if h : (source.program r).input t = false then some ⟨t, h⟩ else none

theorem sourceDefinedAt_nodup (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) : (sourceDefinedAt source r).Nodup := by
  apply List.Nodup.filterMap _ (sourceTensors_nodup source)
  intro a b t ha hb
  split at ha <;> simp_all
  obtain ⟨_, hb⟩ := hb
  exact (congrArg Subtype.val ha).trans (congrArg Subtype.val hb).symm

theorem sourceDefinedAt_complete (source : AdmittedSource) (r : Registry (fun _ : Unit => K))
    (t : (source.program r).Defined) : t ∈ sourceDefinedAt source r := by
  apply List.mem_filterMap.mpr
  exact ⟨t.val, sourceTensors_complete source t.val, dif_pos t.property⟩

def sourceValuationsAt (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t : (source.program r).Defined)
    (s : Fin ((source.program r).statements t)) :
    List {v : Fin ((source.program r).valuations t s) //
      (source.program r).guard t s v = true} :=
  (List.finRange ((source.program r).valuations t s)).map fun v => ⟨v, rfl⟩

theorem sourceValuationsAt_nodup (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t s) :
    (sourceValuationsAt source r t s).Nodup :=
  (List.nodup_finRange _).map (fun _ _ h => congrArg Subtype.val h)

theorem sourceValuationsAt_complete (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t s v) :
    v ∈ sourceValuationsAt source r t s := by
  apply List.mem_map.mpr
  exact ⟨v.val, List.mem_finRange v.val, Subtype.ext rfl⟩

def sourceOccurrencesAt (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t : (source.program r).Defined) :
    List ((source.program r).Occurrence t) :=
  (List.finRange ((source.program r).statements t)).sigma (sourceValuationsAt source r t)

theorem sourceOccurrencesAt_nodup (source : AdmittedSource) (r : Registry (fun _ : Unit => K)) (t) :
    (sourceOccurrencesAt source r t).Nodup :=
  (List.nodup_finRange _).sigma (sourceValuationsAt_nodup source r t)

theorem sourceOccurrencesAt_complete (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t o) :
    o ∈ sourceOccurrencesAt source r t :=
  List.mem_sigma.mpr ⟨List.mem_finRange o.1, sourceValuationsAt_complete source r t o.1 o.2⟩

def sourceCoordinatesAt (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t : (source.program r).Defined) :
    List (Coord (source.source.table.declarations.signature t.val).axes) :=
  let layout := canonicalLayout (source.source.table.declarations.signature t.val).axes
  (List.finRange layout.count).map layout.enumerate

theorem sourceCoordinatesAt_nodup (source : AdmittedSource) (r : Registry (fun _ : Unit => K)) (t) :
    (sourceCoordinatesAt source r t).Nodup :=
  (List.nodup_finRange _).map (canonicalLayout _).enumerate.injective

theorem sourceCoordinatesAt_complete (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t p) :
    p ∈ sourceCoordinatesAt source r t := by
  let layout := canonicalLayout (source.source.table.declarations.signature t.val).axes
  apply List.mem_map.mpr
  exact ⟨layout.enumerate.symm p, List.mem_finRange _, layout.enumerate.apply_symm_apply p⟩

def sourceOccurrenceKeysAt (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) : List (Key (source.program r)) :=
  ((sourceDefinedAt source r).sigma (sourceOccurrencesAt source r)).map fun x => .occurrence x.1 x.2

def sourcePublicationKeysAt (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) : List (Key (source.program r)) :=
  ((sourceDefinedAt source r).sigma (sourceCoordinatesAt source r)).map fun x =>
    .publication x.1 x.2

theorem sourceOccurrenceKeysAt_nodup (source : AdmittedSource) (r : Registry (fun _ : Unit => K)) :
    (sourceOccurrenceKeysAt source r).Nodup := by
  apply ((sourceDefinedAt_nodup source r).sigma (sourceOccurrencesAt_nodup source r)).map
  rintro ⟨t, o⟩ ⟨u, p⟩ h
  cases h
  rfl

theorem sourcePublicationKeysAt_nodup (source : AdmittedSource) (r : Registry (fun _ : Unit => K)) :
    (sourcePublicationKeysAt source r).Nodup := by
  apply ((sourceDefinedAt_nodup source r).sigma (sourceCoordinatesAt_nodup source r)).map
  rintro ⟨t, o⟩ ⟨u, p⟩ h
  cases h
  rfl

theorem sourceOccurrenceKeysAt_complete (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t o) :
    Key.occurrence t o ∈ sourceOccurrenceKeysAt source r :=
  List.mem_map.mpr ⟨⟨t, o⟩, List.mem_sigma.mpr
    ⟨sourceDefinedAt_complete source r t, sourceOccurrencesAt_complete source r t o⟩, rfl⟩

theorem sourcePublicationKeysAt_complete (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) (t p) :
    Key.publication t p ∈ sourcePublicationKeysAt source r :=
  List.mem_map.mpr ⟨⟨t, p⟩, List.mem_sigma.mpr
    ⟨sourceDefinedAt_complete source r t, sourceCoordinatesAt_complete source r t p⟩, rfl⟩

def sourceScheduleAt (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) : Schedule (source.program r) where
  tensors := sourceTensors source
  tensors_nodup := sourceTensors_nodup source
  tensors_complete := sourceTensors_complete source
  keys := sourceOccurrenceKeysAt source r ++ sourcePublicationKeysAt source r
  keys_nodup := by
    rw [List.nodup_append]
    refine ⟨sourceOccurrenceKeysAt_nodup source r, sourcePublicationKeysAt_nodup source r, ?_⟩
    intro a ha b hb h
    obtain ⟨⟨t, o⟩, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨⟨u, p⟩, _, rfl⟩ := List.mem_map.mp hb
    cases h
  keys_complete := by
    intro k
    cases k with
    | occurrence t o => exact List.mem_append_left _ (sourceOccurrenceKeysAt_complete source r t o)
    | publication t p =>
      exact List.mem_append_right _ (sourcePublicationKeysAt_complete source r t p)

end Generic

abbrev sourceDefined (source : AdmittedSource) := sourceDefinedAt source RationalReference.registry
abbrev sourceValuations (source : AdmittedSource) :=
  sourceValuationsAt source RationalReference.registry
abbrev sourceOccurrences (source : AdmittedSource) :=
  sourceOccurrencesAt source RationalReference.registry
abbrev sourceCoordinates (source : AdmittedSource) :=
  sourceCoordinatesAt source RationalReference.registry
abbrev sourceSchedule (source : AdmittedSource) : Schedule (elaborateSource source) :=
  sourceScheduleAt source RationalReference.registry

theorem sourceDefined_nodup (source : AdmittedSource) : (sourceDefined source).Nodup :=
  sourceDefinedAt_nodup source _
theorem sourceDefined_complete (source : AdmittedSource) (t : (elaborateSource source).Defined) :
    t ∈ sourceDefined source := sourceDefinedAt_complete source _ t
theorem sourceCoordinates_nodup (source : AdmittedSource) (t : (elaborateSource source).Defined) :
    (sourceCoordinates source t).Nodup := sourceCoordinatesAt_nodup source _ t
theorem sourceCoordinates_complete (source : AdmittedSource) (t : (elaborateSource source).Defined)
    (p) : p ∈ sourceCoordinates source t := sourceCoordinatesAt_complete source _ t p

def sourceInputBinding (source : AdmittedSource) :
    Program.InputBinding (K := RationalReference.Carrier) (σ := source.source.table.declarations) :=
  fun t => if h : (source.source.table.entry t).role = .input then
    some (source.source.inputs.buffers t h).value else none

def sourceInput (source : AdmittedSource) : (elaborateSource source).Input :=
  ⟨sourceInputBinding source, by
    intro t
    by_cases h : (source.source.table.entry t).role = .input <;>
      simp [sourceInputBinding, elaborateSource, AdmittedSource.program, AdmittedSource.isInput, h]⟩

def runSource (source : AdmittedSource) :
    Except source.source.table.declarations.Tensor
      (ValidatedResult (elaborateSource source) RationalReference.ops) :=
  runValidated (elaborateSource source) RationalReference.ops
    (sourceSchedule source) (sourceInputBinding source)

theorem runSource_eq (source : AdmittedSource) :
    runSource source = .ok ⟨sourceInput source,
      run (elaborateSource source) RationalReference.ops (sourceSchedule source) (sourceInput source)⟩ := by
  unfold runSource runValidated
  have accepted : validate (elaborateSource source) (sourceSchedule source)
      (sourceInputBinding source) = .ok (sourceInput source) :=
    validate_accepts (elaborateSource source) (sourceSchedule source) (sourceInput source)
  rw [accepted]

theorem runSource_not_exhausted (source : AdmittedSource) :
    (run (elaborateSource source) RationalReference.ops (sourceSchedule source)
      (sourceInput source)).outcome.isExhausted = false :=
  run_not_exhausted (elaborateSource source) RationalReference.ops _ _

def runSourceDebug (source : AdmittedSource) (fuel : Option Nat := none) :
    Except source.source.table.declarations.Tensor
      (ValidatedResult (elaborateSource source) RationalReference.ops) :=
  match fuel with
  | none => runSource source
  | some fuel =>
    match validate (elaborateSource source) (sourceSchedule source) (sourceInputBinding source) with
    | .error t => .error t
    | .ok input => .ok ⟨input,
        runFuel (elaborateSource source) RationalReference.ops (sourceSchedule source)
          fuel (.running ((elaborateSource source).initial input))⟩

theorem sourceResult_model (source : AdmittedSource)
    (result : ValidatedResult (elaborateSource source) RationalReference.ops) (c complete)
    (h : result.result.outcome = .complete c complete) :
    (elaborateSource source).Models RationalReference.ops result.input
      ((elaborateSource source).finalStore c complete) :=
  result_model _ _ result.input result.result c complete h

theorem sourceResult_unique (source : AdmittedSource)
    (result : ValidatedResult (elaborateSource source) RationalReference.ops) (c complete)
    (h : result.result.outcome = .complete c complete) :
    ∀ ρ, (elaborateSource source).Models RationalReference.ops result.input ρ →
      ρ = (elaborateSource source).finalStore c complete :=
  result_unique _ _ result.input result.result c complete h

theorem sourceResult_denotation (source : AdmittedSource)
    (result : ValidatedResult (elaborateSource source) RationalReference.ops) (c complete)
    (h : result.result.outcome = .complete c complete) :
    (elaborateSource source).denotation RationalReference.ops result.input
      ((elaborateSource source).successful_admInput RationalReference.ops result.input c
        (result_success _ _ result.input result.result c complete h)) =
      (elaborateSource source).outputProjection ((elaborateSource source).finalStore c complete) :=
  result_denotation _ _ result.input result.result c complete h

/-! S2b: the Core leg at a carrier. Input cells (finite rationals) embed through `C.ofRat`;
arithmetic is `semiringOps`, the same instance the oracle uses. -/

def sourceInputBindingAt {K : Type} [Semiring K] (C : Oracle.Carrier K) (source : AdmittedSource) :
    Program.InputBinding (K := fun _ : Unit => K) (σ := source.source.table.declarations) :=
  fun t => if h : (source.source.table.entry t).role = .input then
    some fun p => C.ofRat ((source.source.inputs.buffers t h).value p) else none

def runSourceAt {K : Type} [Semiring K] (C : Oracle.Carrier K) (source : AdmittedSource)
    (r : Registry (fun _ : Unit => K)) :
    Except source.source.table.declarations.Tensor
      (ValidatedResult (source.program r) semiringOps) :=
  runValidated (source.program r) semiringOps (sourceScheduleAt source r)
    (sourceInputBindingAt C source)

end LeanNCD.Semantics.Source

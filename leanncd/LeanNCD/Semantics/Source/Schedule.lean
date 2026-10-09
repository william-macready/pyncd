import LeanNCD.Semantics.Source.Program
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

def sourceDefined (source : AdmittedSource) : List (elaborateSource source).Defined :=
  (sourceTensors source).filterMap fun t =>
    if h : (elaborateSource source).input t = false then some ⟨t, h⟩ else none

theorem sourceDefined_nodup (source : AdmittedSource) : (sourceDefined source).Nodup := by
  apply List.Nodup.filterMap _ (sourceTensors_nodup source)
  intro a b t ha hb
  split at ha <;> simp_all
  obtain ⟨_, hb⟩ := hb
  exact (congrArg Subtype.val ha).trans (congrArg Subtype.val hb).symm

theorem sourceDefined_complete (source : AdmittedSource)
    (t : (elaborateSource source).Defined) : t ∈ sourceDefined source := by
  apply List.mem_filterMap.mpr
  exact ⟨t.val, sourceTensors_complete source t.val, dif_pos t.property⟩

def sourceValuations (source : AdmittedSource) (t : (elaborateSource source).Defined)
    (s : Fin ((elaborateSource source).statements t)) :
    List {v : Fin ((elaborateSource source).valuations t s) //
      (elaborateSource source).guard t s v = true} :=
  (List.finRange ((elaborateSource source).valuations t s)).map fun v => ⟨v, rfl⟩

theorem sourceValuations_nodup (source : AdmittedSource) (t s) :
    (sourceValuations source t s).Nodup :=
  (List.nodup_finRange _).map (fun _ _ h => congrArg Subtype.val h)

theorem sourceValuations_complete (source : AdmittedSource) (t s v) :
    v ∈ sourceValuations source t s := by
  apply List.mem_map.mpr
  exact ⟨v.val, List.mem_finRange v.val, Subtype.ext rfl⟩

def sourceOccurrences (source : AdmittedSource) (t : (elaborateSource source).Defined) :
    List ((elaborateSource source).Occurrence t) :=
  (List.finRange ((elaborateSource source).statements t)).sigma (sourceValuations source t)

theorem sourceOccurrences_nodup (source : AdmittedSource) (t) :
    (sourceOccurrences source t).Nodup :=
  (List.nodup_finRange _).sigma (sourceValuations_nodup source t)

theorem sourceOccurrences_complete (source : AdmittedSource) (t o) :
    o ∈ sourceOccurrences source t :=
  List.mem_sigma.mpr ⟨List.mem_finRange o.1, sourceValuations_complete source t o.1 o.2⟩

def sourceCoordinates (source : AdmittedSource) (t : (elaborateSource source).Defined) :
    List (Coord (source.source.table.declarations.signature t.val).axes) :=
  let layout := canonicalLayout (source.source.table.declarations.signature t.val).axes
  (List.finRange layout.count).map layout.enumerate

theorem sourceCoordinates_nodup (source : AdmittedSource) (t) :
    (sourceCoordinates source t).Nodup :=
  (List.nodup_finRange _).map (canonicalLayout _).enumerate.injective

theorem sourceCoordinates_complete (source : AdmittedSource) (t p) :
    p ∈ sourceCoordinates source t := by
  let layout := canonicalLayout (source.source.table.declarations.signature t.val).axes
  apply List.mem_map.mpr
  exact ⟨layout.enumerate.symm p, List.mem_finRange _, layout.enumerate.apply_symm_apply p⟩

def sourceOccurrenceKeys (source : AdmittedSource) : List (Key (elaborateSource source)) :=
  ((sourceDefined source).sigma (sourceOccurrences source)).map fun x => .occurrence x.1 x.2

def sourcePublicationKeys (source : AdmittedSource) : List (Key (elaborateSource source)) :=
  ((sourceDefined source).sigma (sourceCoordinates source)).map fun x => .publication x.1 x.2

theorem sourceOccurrenceKeys_nodup (source : AdmittedSource) :
    (sourceOccurrenceKeys source).Nodup := by
  apply ((sourceDefined_nodup source).sigma (sourceOccurrences_nodup source)).map
  rintro ⟨t, o⟩ ⟨u, p⟩ h
  cases h
  rfl

theorem sourcePublicationKeys_nodup (source : AdmittedSource) :
    (sourcePublicationKeys source).Nodup := by
  apply ((sourceDefined_nodup source).sigma (sourceCoordinates_nodup source)).map
  rintro ⟨t, o⟩ ⟨u, p⟩ h
  cases h
  rfl

theorem sourceOccurrenceKeys_complete (source : AdmittedSource) (t o) :
    Key.occurrence t o ∈ sourceOccurrenceKeys source :=
  List.mem_map.mpr ⟨⟨t, o⟩, List.mem_sigma.mpr
    ⟨sourceDefined_complete source t, sourceOccurrences_complete source t o⟩, rfl⟩

theorem sourcePublicationKeys_complete (source : AdmittedSource) (t p) :
    Key.publication t p ∈ sourcePublicationKeys source :=
  List.mem_map.mpr ⟨⟨t, p⟩, List.mem_sigma.mpr
    ⟨sourceDefined_complete source t, sourceCoordinates_complete source t p⟩, rfl⟩

def sourceSchedule (source : AdmittedSource) : Schedule (elaborateSource source) where
  tensors := sourceTensors source
  tensors_nodup := sourceTensors_nodup source
  tensors_complete := sourceTensors_complete source
  keys := sourceOccurrenceKeys source ++ sourcePublicationKeys source
  keys_nodup := by
    rw [List.nodup_append]
    refine ⟨sourceOccurrenceKeys_nodup source, sourcePublicationKeys_nodup source, ?_⟩
    intro a ha b hb h
    obtain ⟨⟨t, o⟩, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨⟨u, p⟩, _, rfl⟩ := List.mem_map.mp hb
    cases h
  keys_complete := by
    intro k
    cases k with
    | occurrence t o => exact List.mem_append_left _ (sourceOccurrenceKeys_complete source t o)
    | publication t p => exact List.mem_append_right _ (sourcePublicationKeys_complete source t p)

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

end LeanNCD.Semantics.Source

import IndexedComponentCompositionAssemble
import IndexedComponentCompositionPortFixtures

namespace IndexedComponentCompositionTest

open LeanNCD.Semantics
open LeanNCD.Semantics.Program
open LeanNCD.Semantics.Program.Executor
open IndexedOpenComposition
open IndexedComponentComposition
open IndexedComponentCompositionPortFixtures

abbrev EventRow := String × Nat × Nat × Option ℚ

def graphEventRow {σ : Declarations Unit} : IndexedOpenComposition.Event σ → EventRow
  | .produced tag cap value => ("write", tag, cap, some value)
  | .sealed a value => ("publish", σ.uid a.1, 0, some value)
  | .undefined tag => ("undefined", tag, 0, none)

def sourceEventRow {σ : Declarations Unit}
    {P : Program RationalReference.Carrier σ RationalReference.registry} :
    LeanNCD.Semantics.Program.Executor.Event P → EventRow
  | .contribution t o value => ("write", σ.uid t.val, o.1.val, some value)
  | .publication t _ value => ("publish", σ.uid t.val, 0, some value)
  | .undefined t o => ("undefined", σ.uid t.val, o.1.val, none)

def graphStepRow {σ : Declarations Unit} : Step σ → String × Nat × List Nat
  | .write w => ("write", w.tag, [w.capability])
  | .collect a caps => ("publish", σ.uid a.1, caps)

abbrev scalarDeclarations (other : ℚ) :=
  declarations producerComponent (consumerComponent other)
def scalarProgram (other : ℚ) := program producerComponent (consumerComponent other) (scalarBoundary other)
def scalarSchedule (other : ℚ) := schedule producerComponent (consumerComponent other) (scalarBoundary other)
def scalarContract (other : ℚ) := contract producerComponent (consumerComponent other) (scalarBoundary other)
def scalarFragment (other : ℚ) := fragment producerComponent (consumerComponent other) (scalarBoundary other)
def scalarGraph (other : ℚ) := graph producerComponent (consumerComponent other) (scalarBoundary other)
def scalarRawInput (other : ℚ) : InputBinding
    (K := RationalReference.Carrier) (σ := scalarDeclarations other) := fun _ => none
def scalarGraphRun (other : ℚ) :=
  execute (scalarGraph other) (scalarRawInput other)
def scalarSourceResult (other : ℚ) :=
  runValidated (scalarProgram other) RationalReference.ops (scalarSchedule other) (scalarRawInput other)

def scalarPre (other : ℚ) : Address (scalarDeclarations other) := ⟨.inl producerPre, ()⟩
def scalarOut (other : ℚ) : Address (scalarDeclarations other) := ⟨.inr ⟨consumerOut, rfl⟩, ()⟩
def scalarAudit (other : ℚ) : Address (scalarDeclarations other) := ⟨.inr ⟨strictAudit, rfl⟩, ()⟩

theorem scalarClose_ok (other : ℚ) :
    close (scalarContract other) (scalarFragment other) = .ok (scalarGraph other) :=
  close_ok producerComponent (consumerComponent other) (scalarBoundary other)

def scalarSourceObservation (other : ℚ) :=
  match scalarSourceResult other with
  | .error t => ("invalidInput", [], [], some ((scalarDeclarations other).uid t))
  | .ok result =>
    let c := match result.result.outcome.state with
      | .running c => c
      | .failed _ _ c => c
    (result.result.outcome.kind, result.result.events.map sourceEventRow,
      [c.published (scalarPre other), c.published (scalarOut other),
        c.published (scalarAudit other)], none)

def scalarWriterPrefix : List EventRow :=
  [("write", 20, 202, some 1), ("write", 22, 204, some (-1)),
    ("publish", 0, 0, some 0), ("write", 41, 403, some 0),
    ("publish", 3, 0, some 0)]

def scalarSourcePrefix : List EventRow :=
  [("write", 0, 0, some 1), ("write", 0, 1, some (-1)),
    ("publish", 0, 0, some 0), ("write", 3, 0, some 0),
    ("publish", 3, 0, some 0)]

#eval IndexedCompositionParityTest.check "composite-scalar-structure"
  ((scalarFragment 4).writers.map (fun w =>
      (w.tag, w.capability, (scalarDeclarations 4).uid w.destination.1)),
    (scalarContract 4).collectors.map (fun row =>
      ((scalarDeclarations 4).uid row.1.1, row.2)),
    (scalarGraph 4).steps.length, (scalarSchedule 4).keys.length,
    (scalarContract 4).outputs.map (fun a => (scalarDeclarations 4).uid a.1),
    (scalarProgram 4).output (scalarAudit 4).1)
  ([(20, 202, 0), (22, 204, 0), (41, 403, 3), (61, 603, 5)],
    [(0, [202, 204]), (3, [403]), (5, [603])], 7, 7, [3], false)

#eval IndexedCompositionParityTest.check "composite-scalar-graph-steps"
  ((scalarGraph 4).steps.map graphStepRow)
  [("write", 20, [202]), ("write", 22, [204]), ("publish", 0, [202, 204]),
    ("write", 41, [403]), ("publish", 3, [403]),
    ("write", 61, [603]), ("publish", 5, [603])]

#eval IndexedCompositionParityTest.check "composite-scalar-strict-graph"
  ((scalarGraphRun 0).outcome.kind, (scalarGraphRun 0).events.map graphEventRow,
    (scalarGraphRun 0).states.getLast?.map (fun s =>
      [s.available (scalarPre 0), s.available (scalarOut 0), s.available (scalarAudit 0)]))
  ("failed", scalarWriterPrefix ++ [("undefined", 61, 0, none)],
    some [some (0 : ℚ), some 0, none])

#eval IndexedCompositionParityTest.check "composite-scalar-total-graph"
  ((scalarGraphRun 4).outcome.kind, (scalarGraphRun 4).events.map graphEventRow,
    (scalarGraphRun 4).states.getLast?.map (fun s =>
      [s.available (scalarPre 4), s.available (scalarOut 4), s.available (scalarAudit 4)]))
  ("complete", scalarWriterPrefix ++
    [("write", 61, 603, some (1 / 2)), ("publish", 5, 0, some (1 / 2))],
    some [some (0 : ℚ), some 0, some (1 / 2)])

#eval IndexedCompositionParityTest.check "composite-scalar-strict-source"
  (scalarSourceObservation 0)
  ("failed", scalarSourcePrefix ++ [("undefined", 5, 0, none)],
    [some (0 : ℚ), some 0, none], none)

#eval IndexedCompositionParityTest.check "composite-scalar-total-source"
  (scalarSourceObservation 4)
  ("complete", scalarSourcePrefix ++
    [("write", 5, 0, some (1 / 2)), ("publish", 5, 0, some (1 / 2))],
    [some (0 : ℚ), some 0, some (1 / 2)], none)

abbrev zeroDeclarations := declarations zeroProducerComponent (consumerComponent 4)
def zeroProgram := program zeroProducerComponent (consumerComponent 4) zeroBoundary
def zeroSchedule := schedule zeroProducerComponent (consumerComponent 4) zeroBoundary
def zeroContract := contract zeroProducerComponent (consumerComponent 4) zeroBoundary
def zeroFragment := fragment zeroProducerComponent (consumerComponent 4) zeroBoundary
def zeroGraph := graph zeroProducerComponent (consumerComponent 4) zeroBoundary
def zeroRawInput : InputBinding (K := RationalReference.Carrier) (σ := zeroDeclarations) :=
  fun _ => none
def zeroGraphRun := execute zeroGraph zeroRawInput
def zeroSourceResult := runValidated zeroProgram RationalReference.ops zeroSchedule zeroRawInput
def zeroPre : Address zeroDeclarations := ⟨.inl producerPre, ()⟩
def zeroOut : Address zeroDeclarations := ⟨.inr ⟨consumerOut, rfl⟩, ()⟩
def zeroAudit : Address zeroDeclarations := ⟨.inr ⟨strictAudit, rfl⟩, ()⟩

theorem zeroClose_ok : close zeroContract zeroFragment = .ok zeroGraph :=
  close_ok zeroProducerComponent (consumerComponent 4) zeroBoundary

def zeroSourceObservation :=
  match zeroSourceResult with
  | .error t => ("invalidInput", [], [], some (zeroDeclarations.uid t))
  | .ok result =>
    let c := match result.result.outcome.state with
      | .running c => c
      | .failed _ _ c => c
    (result.result.outcome.kind, result.result.events.map sourceEventRow,
      [c.published zeroPre, c.published zeroOut, c.published zeroAudit], none)

#eval IndexedCompositionParityTest.check "composite-zero-structure"
  (zeroFragment.writers.map (fun w => (w.tag, w.capability, zeroDeclarations.uid w.destination.1)),
    zeroContract.collectors.map (fun row => (zeroDeclarations.uid row.1.1, row.2)),
    zeroGraph.steps.length, zeroSchedule.keys.length)
  ([(41, 403, 3), (61, 603, 5)], [(0, []), (3, [403]), (5, [603])], 5, 5)

#eval IndexedCompositionParityTest.check "composite-zero-graph"
  (zeroGraphRun.outcome.kind, zeroGraphRun.events.map graphEventRow,
    zeroGraphRun.states.getLast?.map (fun s =>
      [s.available zeroPre, s.available zeroOut, s.available zeroAudit]))
  ("complete", [("publish", 0, 0, some (0 : ℚ)), ("write", 41, 403, some 0),
    ("publish", 3, 0, some 0), ("write", 61, 603, some (1 / 2)),
    ("publish", 5, 0, some (1 / 2))], some [some (0 : ℚ), some 0, some (1 / 2)])

#eval IndexedCompositionParityTest.check "composite-zero-source"
  zeroSourceObservation
  ("complete", [("publish", 0, 0, some (0 : ℚ)), ("write", 3, 0, some 0),
    ("publish", 3, 0, some 0), ("write", 5, 0, some (1 / 2)),
    ("publish", 5, 0, some (1 / 2))], [some (0 : ℚ), some 0, some (1 / 2)], none)

abbrev emptyDeclarations := declarations emptyProducerComponent emptyConsumerComponent
def emptyProgram := program emptyProducerComponent emptyConsumerComponent emptyBoundary
def emptySchedule := schedule emptyProducerComponent emptyConsumerComponent emptyBoundary
def emptyContract := contract emptyProducerComponent emptyConsumerComponent emptyBoundary
def emptyFragment := fragment emptyProducerComponent emptyConsumerComponent emptyBoundary
def emptyGraph := graph emptyProducerComponent emptyConsumerComponent emptyBoundary
def emptyInputTensor : emptyDeclarations.Tensor := .inl emptyExternalInput
def emptyPreTensor : emptyDeclarations.Tensor := .inl emptyProducerPre
def emptyOutTensor : emptyDeclarations.Tensor := .inr ⟨emptyConsumerOut, rfl⟩
def emptyInputs := inputPorts emptyProducerComponent emptyConsumerComponent
def emptyOutputs := outputPorts emptyProducerComponent emptyConsumerComponent

def emptyPresentRaw : InputBinding (K := RationalReference.Carrier) (σ := emptyDeclarations)
  | .inl t => emptyPresentInput t
  | .inr _ => none

def emptyMissingRaw : InputBinding (K := RationalReference.Carrier) (σ := emptyDeclarations) :=
  fun _ => none

def emptyBothFaultsRaw : InputBinding (K := RationalReference.Carrier) (σ := emptyDeclarations)
  | .inl _ => none
  | .inr _ => some (fun p => Fin.elim0 p.1)

def emptyGraphRun := execute emptyGraph emptyPresentRaw
def emptySourceResult := runValidated emptyProgram RationalReference.ops emptySchedule emptyPresentRaw

theorem emptyClose_ok : close emptyContract emptyFragment = .ok emptyGraph :=
  close_ok emptyProducerComponent emptyConsumerComponent emptyBoundary

theorem emptyOutput_provenance : emptyOutputs.map Port.tensor = [emptyOutTensor] := rfl
theorem emptyOutput_role : emptyProgram.output emptyOutTensor = true := rfl
theorem emptyPre_private : emptyProgram.output emptyPreTensor = false := rfl
theorem emptyAddressOutputs : emptyContract.outputs = [] := rfl
theorem emptyMissing_rejection :
    validate emptyProgram emptySchedule emptyMissingRaw = .error emptyInputTensor := rfl
theorem emptyBothFaults_rejection :
    validate emptyProgram emptySchedule emptyBothFaultsRaw = .error emptyInputTensor := rfl
theorem emptyBothFaults_reverse_rejection :
    validate emptyProgram emptySchedule.reverse emptyBothFaultsRaw = .error emptyOutTensor := rfl

def emptyUidSortedSchedule : Schedule emptyProgram where
  tensors := [emptyPreTensor, emptyOutTensor, emptyInputTensor]
  tensors_nodup := by decide
  tensors_complete := by
    intro t
    cases t with
    | inl t =>
      fin_cases t <;>
        simp [emptyPreTensor, emptyOutTensor, emptyInputTensor,
          emptyProducerPre, emptyExternalInput]
    | inr t =>
      rcases t with ⟨t, ht⟩
      change (t == 0) = false at ht
      fin_cases t
      · exact False.elim (Bool.noConfusion ht)
      · simp [emptyPreTensor, emptyOutTensor, emptyInputTensor, emptyConsumerOut]
  keys := emptySchedule.keys
  keys_nodup := emptySchedule.keys_nodup
  keys_complete := emptySchedule.keys_complete

theorem emptyBothFaults_sorted_rejection :
    validate emptyProgram emptyUidSortedSchedule emptyBothFaultsRaw = .error emptyOutTensor := rfl

#eval IndexedCompositionParityTest.check "composite-empty-whole-output"
  (emptyInputs.map (fun p => emptyDeclarations.uid p.tensor),
    emptyOutputs.map (fun p => (emptyDeclarations.uid p.tensor, p.sort, p.axes)),
    emptyContract.outputs.length, emptyProgram.output emptyOutTensor,
    emptyProgram.output emptyPreTensor,
    emptyContract.tensors.map emptyDeclarations.uid,
    emptyUidSortedSchedule.tensors.map emptyDeclarations.uid,
    emptyFragment.writers.length, emptyGraph.steps.length, emptySchedule.keys.length)
  ([20], [(3, (), [⟨51, 0⟩])], 0, true, false, [20, 0, 3], [0, 3, 20], 0, 0, 0)

#eval IndexedCompositionParityTest.check "composite-empty-present"
  (emptyGraphRun.outcome.kind, emptyGraphRun.events.length,
    match emptySourceResult with
    | .error _ => ("invalidInput", 0)
    | .ok result => (result.result.outcome.kind, result.result.events.length))
  ("complete", 0, "complete", 0)

#eval IndexedCompositionParityTest.check "composite-empty-missing"
  (match runChecked emptyContract emptyFragment emptyMissingRaw |>.outcome with
    | .invalidInput t => some (emptyDeclarations.uid t)
    | _ => none)
  (some 20)

#eval IndexedCompositionParityTest.check "composite-empty-simultaneous-faults"
  ((emptyBothFaultsRaw emptyInputTensor).isSome, emptyProgram.input emptyInputTensor,
    (emptyBothFaultsRaw emptyOutTensor).isSome, emptyProgram.input emptyOutTensor,
    match runChecked emptyContract emptyFragment emptyBothFaultsRaw |>.outcome with
    | .invalidInput t => some (emptyDeclarations.uid t)
    | _ => none)
  (false, true, true, false, some 20)

#eval IndexedCompositionParityTest.check "composite-empty-validation-order"
  ((match validate emptyProgram emptySchedule emptyBothFaultsRaw with
    | .error t => some (emptyDeclarations.uid t)
    | .ok _ => none),
    (match validate emptyProgram emptySchedule.reverse emptyBothFaultsRaw with
    | .error t => some (emptyDeclarations.uid t)
    | .ok _ => none),
    (match validate emptyProgram emptyUidSortedSchedule emptyBothFaultsRaw with
    | .error t => some (emptyDeclarations.uid t)
    | .ok _ => none))
  (some 20, some 3, some 3)

end IndexedComponentCompositionTest

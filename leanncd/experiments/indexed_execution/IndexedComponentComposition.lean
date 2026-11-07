import IndexedComponentCompositionPriority

namespace IndexedComponentComposition

open LeanNCD.Semantics
open IndexedOpenComposition

variable {σA σB : Declarations Unit}
variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
variable (A : MatchedComponent σA) (B : MatchedComponent σB) (wire : Boundary A B)

def compose_match : SourceContractMatch (program A B wire) (schedule A B wire)
    (contract A B wire) (fragment A B wire) (graph A B wire) where
  close_ok := close_ok A B wire
  input_roles := input_roles A B wire
  tensor_order := tensor_order A B wire
  outputs_exact := outputs_exact A B wire
  sourceToWriter := sourceToWriter A B wire
  writer_destination := writer_destination A B wire
  writer_reads := writer_reads A B wire
  eval_agrees := eval_agrees A B wire
  priority := priority A B wire

def compose : MatchedComponent (declarations A B) where
  program := program A B wire
  schedule := schedule A B wire
  contract := contract A B wire
  fragment := fragment A B wire
  graph := graph A B wire
  matched := compose_match A B wire
  inputs := inputPorts A B
  outputs := outputPorts A B
  inputs_nodup := inputPorts_nodup A B
  outputs_nodup := outputPorts_nodup A B
  inputs_exact := inputPorts_exact A B wire
  outputs_exact := outputPorts_exact A B wire

end IndexedComponentComposition

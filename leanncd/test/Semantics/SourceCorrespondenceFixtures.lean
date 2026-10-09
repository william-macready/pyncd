import LeanNCD.Semantics.Source.ProgramCorrespondence
import Semantics.SourceProgramFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source

namespace SourceCorrespondenceFixtures

def natRegistry : Registry (fun _ : Unit => Nat) where
  Op := Empty
  arity := fun f => nomatch f
  input := fun f => nomatch f
  output := fun f => nomatch f
  domain := fun f => nomatch f
  meaning := fun f => nomatch f

def ratStore (source : AdmittedSource) :
    Store (fun _ => Rat) source.source.table.declarations :=
  fun a => if h : (source.source.table.entry a.1).role = .input then
    (source.source.inputs.buffers a.1 h).value a.2 else 7

def natStore (source : AdmittedSource) :
    Store (fun _ => Nat) source.source.table.declarations :=
  fun a => (ratStore source a).num.toNat

structure FiberRow (K : Type) where
  declaration : Nat
  name : String
  shape : List Nat
  collected : List K
  global : List K
  deriving DecidableEq, Repr

def fiberRows {K : Type} [Semiring K] (r : Registry (fun _ : Unit => K))
    (source : AdmittedSource) (ρ : Store (fun _ => K) source.source.table.declarations) :
    List (FiberRow K) :=
  (sourceDefined source).map fun t =>
    let entry := source.source.table.entry t.val
    let layout := canonicalLayout (source.source.table.declarations.signature t.val).axes
    ⟨entry.declaration, entry.name, entry.axes.map Axis.extent,
      (List.finRange layout.count).map fun i =>
        (source.program r).collect semiringOps ρ (source.total_admEnv ρ) t (layout.enumerate i),
      (List.finRange layout.count).map fun i =>
        source.globalFiber ρ t.val (layout.enumerate i)⟩

end SourceCorrespondenceFixtures

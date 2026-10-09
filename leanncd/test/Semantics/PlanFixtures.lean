import LeanNCD.Semantics.Plan
import Semantics.ExecutableReferenceTest

/- Plan-layer fixtures. Donors: ExecutableReferenceFixtures.tagged (four
   occurrences into point 1, values 2,2,5,5) and scalarRole/scalarInput. -/

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

/-- Output-flagged copy of `tagged`. -/
@[reducible] def taggedOut : Program Carrier declarations registry where
  tensors := inferInstance
  input := fun _ => false
  output := fun _ => true
  output_defined := fun _ _ => rfl
  statements := fun _ => 2
  valuations := fun _ _ => 2
  guard := fun _ _ _ => true
  destination := fun _ _ _ => point 1
  body := fun _ s => .lit (if s = 0 then 2 else 5)

def T : taggedOut.Defined := ⟨(), rfl⟩

def occ (s v : Fin 2) : OccRef taggedOut := ⟨T, ⟨s, ⟨v, rfl⟩⟩⟩

def addr (i : Fin 3) : DefAddr taggedOut := ⟨T, point i⟩

def group : List (OccRef taggedOut) := [occ 0 0, occ 0 1, occ 1 0, occ 1 1]
def groupPerm : List (OccRef taggedOut) := [occ 1 1, occ 0 1, occ 1 0, occ 0 0]
def block : List (DefAddr taggedOut) := [addr 0, addr 1, addr 2]

/-- materialise all three zeros; one batch of all four occurrences; one block. -/
def plan : taggedOut.Plan := ⟨[[.initZero block], [.acc group], [.pub block]]⟩

def η0 : taggedOut.Input := noInput taggedOut (fun _ => rfl)

def start0 : taggedOut.Running := taggedOut.initial η0

/-- The successful body values, written independently of `evalReady`. -/
def values : Values taggedOut := fun x => if x.2.1 = 0 then 2 else 5

def accRow (c : taggedOut.Running) : List ℚ :=
  [c.accumulators T (point 0), c.accumulators T (point 1), c.accumulators T (point 2)]

/-- A hand-built memory at pc = 3 holding the published vector `[0, 14, 0]`. -/
def mem3 : Memory Carrier declarations :=
  fun ξ => some (if ξ.2.val = 1 then 14 else 0)

/-- The same memory with the point-2 slot uninitialised. -/
def mem3Hole : Memory Carrier declarations :=
  fun ξ => if ξ.2.val = 2 then none else some (if ξ.2.val = 1 then 14 else 0)

def outT : {t : declarations.Tensor // taggedOut.output t = true} := ⟨(), rfl⟩

def decodeRow (o : Option taggedOut.Output) : Option (List ℚ) :=
  o.map (fun out => [out outT (point 0), out outT (point 1), out outT (point 2)])

end LeanNCD.Semantics.PlanFixtures

import Semantics.PlanFixtures

/- Observed-value checks for memory, the slot view, Start, Decode and R_start. -/

namespace LeanNCD.Semantics.PlanFixtures

open Program Program.Executor Program.Plan RationalReference ExecutableReferenceFixtures

-- One buffer per tensor: the three coordinates occupy three distinct slots.
#eval check "place-indices" (block.map (fun x => (place x.addr).2.val)) [0, 1, 2]

example : Function.Injective (place (σ := declarations)) := place_injective

-- Start installs validated inputs and leaves every other slot uninitialised.
def scalarSlot (t : Fin 3) : Slot scalarDeclarations := ⟨t, ⟨0, Nat.zero_lt_one⟩⟩

#eval check "start-scalar"
  ((List.finRange 3).map (fun t => Start (scalarInput true) (scalarSlot t)))
  [some 7, none, none]
#eval check "start-tagged" (block.map (fun x => Start η0 (place x.addr))) [none, none, none]

-- The slot view depends only on pc and the commands.
#eval check "slotview-acc"
  ((List.range 4).map (fun pc => (plan.SlotView pc (.acc (addr 1))).isSome))
  [false, true, true, false]
#eval check "slotview-pub"
  ((List.range 4).map (fun pc => (plan.SlotView pc (.pub (addr 1).addr)).isSome))
  [false, false, false, true]

-- R_start on both fixture programs.
example : plan.R ops η0 0 (Start η0) start0 := plan.R_start ops η0
example : (scalarPlan true []).R ops (scalarInput true) 0
    (Start (scalarInput true)) ((scalarRole true).initial (scalarInput true)) :=
  Plan.R_start _ ops _

-- Decode is partial: it fails before publication and on a missing slot,
-- and never supplies zeros.
#eval check "decode"
  (decodeRow (plan.Decode 0 (Start η0)), decodeRow (plan.Decode 2 mem3),
    decodeRow (plan.Decode 3 mem3), decodeRow (plan.Decode 3 mem3Hole))
  (none, none, some [0, 14, 0], none)

-- Read view at pc = 3 agrees with the reference post-state's published store.
#eval check "readview-pc3"
  ([0, 1, 2].map (fun i => plan.readPub 3 mem3 (addr i).addr),
    (plan.refState ops η0 3).map vectorStore)
  ([some 0, some 14, some 0], some [some 0, some 14, some 0])

end LeanNCD.Semantics.PlanFixtures

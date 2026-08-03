import LeanNCD.DSL.Ast
import Std.Data.HashMap

namespace LeanNCD.Eval
open Std

-- Owns the shared LHS-slot shape vocabulary: reading a slot list's axis-size role (the
-- normalization axis) and turning a slot list plus known axis sizes into a concrete output
-- shape. `Nonlin.resolveNonlin` uses `normAxisUidOf`, while `Scan.evalScan` uses `outputShape`
-- when allocating full scan states. `Contract.evalAssignSeeded` has a distinct seeded-output
-- shape calculation because it must remove every pinned axis; it deliberately does not call the
-- unseeded `outputShape` helper. This module therefore sits below the callers that need slot
-- vocabulary but not the size solver, and depends only on `DSL.Ast` — no `Tensor`/`EvalError`,
-- since neither function here can fail.
--
-- `LHSSlot.outExtent` (the scatter-slot extent formula) already lives in `DSL/Ast.lean` and is
-- deliberately NOT duplicated here — see that file's docstring and `Eval/AGENTS.md`'s
-- `scatterOutShape`/`scatterOutputShapes` contract.

/-- The UID of the slot marked (`m.`) as the softmax/normalize reduction axis, if any.
    This is how the reduction axis is identified for a stmt (the norm flag moved off the
    tensor decl onto the output slot); `none` means no axis was marked. -/
def normAxisUidOf (slots : List LHSSlot) : Option UID :=
  slots.findSome? (·.normUID?)

/-- The output shape: the size of each LHS slot's axis (free/iterAt/iterNext), in slot order.
    `affine` slots (scatter) have no axis size here and yield `0`; their real output extents
    are computed separately on the scatter path (`LHSSlot.outExtent`), not by this function. -/
def outputShape (sizes : HashMap UID Nat) (slots : List LHSSlot) : List Nat :=
  slots.map (fun sl => match sl.axisUID? with
    | some u => (sizes[u]?).getD 0
    | none   => 0)

end LeanNCD.Eval

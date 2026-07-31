-- test/DSL/Pipeline/RecurMorphismTest.lean
import LeanNCD.DSL.Compile
namespace LeanNCD
open Lean

private def hasOp (p : TLProgram) (op : BrOp) : Bool :=
  match TLProgram.compile p |>.run 0 with
  | .ok tc _ => tc.steps.any (·.op == op)
  | .error _ _ => false

private def isErr (p : TLProgram) : Bool :=
  match TLProgram.compile p |>.run 0 with
  | .ok _ _ => false
  | .error _ _ => true

private def iterAxis : AxisSpec := { name := "l", uid := 0, kind := .nat }

-- a well-formed pre-built step morphism (one BrBaseP, no inputs):
private def stepTC : ThreadedComposed :=
  { steps := [{ op := BrOp.contract, degree := [], inputWeaves := [], outputWeaves := [[.tiled]],
                reindexings := [] }],
    routing := [[]], nExternal := 0 }

-- REVERSED 2026-07-30 (audit finding #4). This file previously asserted
--     #guard hasOp recurProg BrOp.scanPre
-- i.e. that a `recurMorphism` COMPILES to a routed step tagged op="scan_pre". Probing showed that
-- was an accepted-then-discarded state, the worst of the available options:
--   * `compile` returned `.ok` with `ops=[BrOp.scanPre]`, but `toBrBaseP` DISCARDED the supplied
--     `ThreadedComposed` — the emitted step had empty degree/inputWeaves/reindexings and the
--     iteration axis was dropped, so the payload never reached the bridge; and
--   * `eval` rejected the very same program with "scanPre unsupported".
-- Note the old assertion could not have caught this: `stepTC` below carries
-- `outputWeaves := [[.tiled]]`, yet the guard only checked the op TAG, never the content.
-- `compile` now rejects the construct outright (`checkScatterNonlin`, Structural.lean).
private def recurProg : TLProgram :=
  { decls := [], stmts := [ .recurMorphism "S" iterAxis stepTC ] }

-- Non-empty pre-built morphism: now a NAMED compile rejection, not a look-alike `.scanPre` step.
run_cmd do
  match TLProgram.compile recurProg |>.run 0 with
  | .error (.unsupportedRecurMorphism "S") _ => pure ()
  | .error e _ => throwError s!"recurProg: wrong CompileError: {repr e}"
  | .ok _ _    => throwError "recurProg: expected unsupportedRecurMorphism, compile succeeded"

-- ...and it must NOT reach the routed output as a scanPre step any more.
#guard ! hasOp recurProg BrOp.scanPre

-- An EMPTY pre-built morphism was already rejected (by `buildStep`'s `tc.steps.isEmpty` guard);
-- it still is, now earlier and by name. Kept as a distinct case so that if the reject above is
-- ever relaxed, the empty-payload path is still pinned.
private def emptyTC : ThreadedComposed := { steps := [], routing := [], nExternal := 0 }
private def badProg : TLProgram :=
  { decls := [], stmts := [ .recurMorphism "S" iterAxis emptyTC ] }
#guard isErr badProg
end LeanNCD

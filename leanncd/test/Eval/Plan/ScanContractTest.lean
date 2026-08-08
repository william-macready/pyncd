import LeanNCD.DSL.Ast
import LeanNCD.DSL.Pipeline.Types
import Eval.Plan.ContractTest

/-!
# Wave F capability classification (F0)

Pins, as a compiler-checked exhaustive match, exactly which `ScanStmt.scan` shapes are
syntactically admissible under Wave F's initial fragment (`papers/wave_f_scanplan_proposal.md`
§5.1/§5.2) — reusing Wave C's per-statement classifiers (`Eval.Plan.ContractTest`) for base/step
block content, since that admitted local kernel is unchanged inside a scan. This classifier is
necessary but not sufficient for Wave F acceptance: extent zero/one, base-write geometry and
disjointness, and causality all need axis sizes a bare `ScanStmt` does not carry, so they are
`ScanCompileError`-tier (post-shape) checks belonging to F4, not classified here.

`classifyScanBlockStmt` is also applied uniformly to `base ++ recur`, so several §5.1 structural
requirements that do not depend on axis sizes are likewise left unchecked here and deferred to
F2/F3: an empty `base` list (§5.1 requires one or more base results), a `base` statement using
`.iterNext` or a `recur` statement using `.iterAt` (base/recur slot discipline is not verified in
either direction), and two or more `.iterNext` writes for one state (§5.1 requires exactly one
next-state result). These are syntactically decidable without shape information but are not yet
built, not axis-size-dependent gaps like the ones above.
-/

namespace LeanNCD.PlanContract.WaveF
open LeanNCD LeanNCD.PlanContract

/-- Scan-block statements may legitimately use `.iterAt`/`.iterNext` — the scan-context analogue
    of Wave C's `classifyLHSSlot`, which rejects both unconditionally for the scan-free fragment. -/
def classifyScanLHSSlot : LHSSlot → Classification
  | .free _     => .accepted
  | .freeNorm _ => .rejected "unsupportedLhsSlot"
  | .iterAt ..  => .accepted
  | .iterNext _ => .accepted
  | .affine _   => .rejected "scatterOrAffineLhs"

/-- A scan base/recur statement is accepted under the same local-kernel restriction as an ordinary
    Wave C assignment: same `agg`/`nonlin`/factor classifiers, `classifyScanLHSSlot` in place of
    `classifyLHSSlot`. Sub-construct check order matches `classifyStmt`'s (LHS slots, then `agg`,
    then nonlin, then factors) for the same reason: that order is local to this classifier, not
    derived from any coarser phase ordering. -/
def classifyScanBlockStmt : Stmt → Classification
  | .assign _ slots rhs =>
      match slots.findSome? (fun s => match classifyScanLHSSlot s with
        | .accepted => none | .rejected c => some c) with
      | some c => .rejected c
      | none =>
          match classifyAggOp rhs.agg with
          | .rejected c => .rejected c
          | .accepted =>
              match classifyNonlin rhs.nonlin with
              | .rejected c => .rejected c
              | .accepted =>
                  match rhs.body.terms.findSome? (fun t => t.factors.findSome? (fun f =>
                    match classifyFactor f with
                    | .accepted => none | .rejected c => some c)) with
                  | some c => .rejected c
                  | none => .accepted
  | .scatter .. => .rejected "scatterOrAffineLhs"
  | .recurMorphism .. => .rejected "recurrenceOrCallback"

/-- Wave F's syntactic (pre-shape) classification of one `ScanStmt`. `.plain` delegates unchanged
    to Wave C's `classifyStmt`. `.scanPre` is always rejected (§5.2 — its callback-bearing payload
    never gets a checked-plan meaning). A `.scan` node is syntactically admissible only if it
    declares at least one advancing axis and every base/recur statement individually classifies as
    accepted — a NECESSARY, not SUFFICIENT, condition; see the module doc comment for what this
    cannot check. -/
def classifyScanStmtF : ScanStmt → Classification
  | .plain s => LeanNCD.PlanContract.classifyStmt s
  | .scanPre .. => .rejected "recurrenceOrCallback"
  | .scan _ axes base recur _ =>
      if axes.isEmpty then .rejected "noAdvancingAxis" else
      match (base ++ recur).findSome? (fun s => match classifyScanBlockStmt s with
        | .accepted => none | .rejected c => some c) with
      | some c => .rejected c
      | none => .accepted

end LeanNCD.PlanContract.WaveF

open LeanNCD LeanNCD.PlanContract LeanNCD.PlanContract.WaveF in
section
private def j : AxisSpec := ⟨"j", 1, .real⟩
private def l : AxisSpec := ⟨"l", 9, .nat⟩

private def acceptedBase : Stmt :=
  .assign "S" [.free j, .iterAt l 0]
    { agg := .sum, body := { terms := [{ factors := [.read "X" [.axis j]] }] }, nonlin := .identity }
private def acceptedRecur : Stmt :=
  .assign "S" [.free j, .iterNext l]
    { agg := .sum,
      body := { terms := [{ factors := [.read "S" [.axis j, .axis l], .read "A" [.axis j]] }] },
      nonlin := .identity }
private def nonlinRecur : Stmt :=
  .assign "S" [.free j, .iterNext l]
    { agg := .sum, body := { terms := [{ factors := [.read "S" [.axis j, .axis l]] }] },
      nonlin := .pointwise .relu }
private def freeNormBase : Stmt :=
  .assign "S" [.freeNorm j, .iterAt l 0]
    { agg := .sum, body := { terms := [{ factors := [.read "X" [.axis j]] }] }, nonlin := .identity }

-- accepted: a well-formed self-recurrence, same shape as ScanTest.lean's own linear-scan fixture.
#guard classifyScanStmtF (.scan "S" [l] [acceptedBase] [acceptedRecur] false) == .accepted
-- rejected: no advancing axis (syntactically visible without any axis size).
#guard classifyScanStmtF (.scan "S" [] [acceptedBase] [acceptedRecur] false) ==
  .rejected "noAdvancingAxis"
-- rejected: a nonlinearity inside the step block (propagated from classifyScanBlockStmt).
#guard classifyScanStmtF (.scan "S" [l] [acceptedBase] [nonlinRecur] false) ==
  .rejected "unsupportedNonlin"
-- rejected: `.freeNorm` inside a base statement (propagated from classifyScanLHSSlot).
#guard classifyScanStmtF (.scan "S" [l] [freeNormBase] [acceptedRecur] false) ==
  .rejected "unsupportedLhsSlot"
-- rejected: `.scanPre` unconditionally.
#guard classifyScanStmtF (.scanPre "S" l default) == .rejected "recurrenceOrCallback"
-- `.plain` delegates unchanged to Wave C's classifyStmt.
#guard classifyScanStmtF (.plain (.assign "Y" [.free j]
  { agg := .sum, body := { terms := [{ factors := [.read "X" []] }] }, nonlin := .identity })) ==
  .accepted
end

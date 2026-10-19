import Semantics.SourceDifferentialFixtures
import Semantics.SourceDiagnosticFixtures

/-! S2a P3: the four-leg differential on affine write slots and scatters.

Inputs: `X[a] = [1, 2, 3, 4]` (declaration 3), `W[b] = [1, 10, 100]` (declaration 4); `|a| = 4`,
`|b| = 3`; `Y` is declaration 5 over `k` with the declared extent `|k|` (the oracle's shape);
production derives its own shape from the write forms. Fixtures are appended at the END of the
file only. -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Source.Debug
open LeanNCD.Semantics.Source.NativeLegs
open LeanNCD.Semantics.Source.Differential
open LeanNCD.Semantics.Source.NumericalProfile

namespace SourceDifferentialScatterTest

private def a : AxisSpec := ⟨"a", 7, .real⟩
private def b : AxisSpec := ⟨"b", 8, .real⟩
private def k : AxisSpec := ⟨"k", 9, .real⟩

private def rhs (terms : List (List Factor)) : RHSExpr :=
  ⟨⟨terms.map ProdTerm.mk⟩, .identity, .sum⟩

private def readX : RHSExpr := rhs [[.read "X" [.axis a]]]
private def readW : RHSExpr := rhs [[.read "W" [.axis b]]]
private def readXW : RHSExpr := rhs [[.read "X" [.axis a], .read "W" [.axis b]]]

private def snap (kExtent : Nat) (yAxes : List AxisSpec) (stmts : List Stmt) : SourceSnapshot :=
  let extent (ax : AxisSpec) : Nat :=
    if ax.uid = 7 then 4 else if ax.uid = 8 then 3 else kExtent
  { resolved := {
      decls := [.axis a (some 4), .axis b (some 3), .axis k (some kExtent),
        .typedTensor .f64 "X" [a], .typedTensor .f64 "W" [b], .typedTensor .f64 "Y" yAxes]
      stmts := stmts
      env := {}, extNames := ∅ }
    specs := [⟨3, .input, [4]⟩, ⟨4, .input, [3]⟩, ⟨5, .output, yAxes.map extent⟩]
    inputs := [⟨3, [4], [1, 2, 3, 4]⟩, ⟨4, [3], [1, 10, 100]⟩] }

private def bits (o : NativeObservation) : String :=
  match o.outputs with
  | .error issues => s!"binding issues {repr issues}"
  | .ok bs => s!"{bs.map fun x => (x.metadata.name, x.shape, x.bits.toList.map (toString ∘ Float.ofBits))}"

/-- Compact per-leg report used to record the observed table. -/
def observe (s : SourceSnapshot) : String :=
  match compareSource s (some [5]) with
  | .error e => s!"ERROR {renderExecutionError e}"
  | .ok run =>
    let oracle := match run.oracle with
      | .error u => s!"unavailable {repr u}"
      | .ok r =>
        let ys := r.tensors.filter (fun (t : Oracle.Tensor) => t.declaration == 5)
        s!"{ys.map fun (t : Oracle.Tensor) => (t.name, t.shape, t.values)}"
    let legacy := match run.native with
      | .error d => s!"admission {repr d.cause}"
      | .ok n => match n.legacy with
        | .unavailable r => s!"unavailable {repr r}"
        | .failure e => s!"failure phase={repr e.phase} cause={e.original.error}"
        | .observed o => s!"value {bits o}"
    let checked := match run.native with
      | .error _ => "-"
      | .ok n => match n.checked with
        | .unavailable r => s!"unavailable {repr r}"
        | .sourceCompilation e => s!"sourceCompilation {repr e.cause}"
        | .preparation e => s!"preparation {((renderChecked (.preparation e)).splitOn "\n").head!}"
        | .runtime e => s!"runtime {repr e.original.cause}"
        | .observed o _ => s!"value {bits o}"
    s!"class={repr run.classification}\n  oracle={oracle}\n  legacy={legacy}\n  checked={checked}"

/-- `snap` with `|b|` as a parameter (`W` is `[5]` when `|b| = 1`). -/
private def snapB (bExtent kExtent : Nat) (yAxes : List AxisSpec) (stmts : List Stmt) :
    SourceSnapshot :=
  let s := snap kExtent yAxes stmts
  if bExtent = 1 then
    { s with
      resolved := { s.resolved with decls := s.resolved.decls.map fun d =>
        match d with | .axis ax _ => if ax.uid = 8 then .axis ax (some 1) else d | _ => d }
      inputs := [⟨3, [4], [1, 2, 3, 4]⟩, ⟨4, [1], [5]⟩]
      specs := [⟨3, .input, [4]⟩, ⟨4, .input, [1]⟩, ⟨5, .output, yAxes.map fun ax =>
        if ax.uid = 7 then 4 else if ax.uid = 8 then 1 else kExtent⟩] }
  else s

private def sumOpts : ScatterOpts := { reduce := .sum }
private def convSlot : LHSSlot := .affine (.affine 0 [(1, a), (1, b)])

/-- Classification name only (the full per-leg report is `observe`). -/
def tag (s : SourceSnapshot) (order : List Nat := [5]) : String :=
  match compareSource s (some order) with
  | .error e => if ((renderExecutionError e).splitOn "writeOutOfRange").length > 1
      then "refused:writeOutOfRange" else "error"
  | .ok run => match run.classification with
    | .fourLegParity => "parity"
    | .knownContractDifference (.scatterCollisionRejected _) => "known:collision"
    | .knownContractDifference (.multiWriterScatter _) => "known:multiWriter"
    | .knownContractDifference (.scatterExtentOverridesDeclared ..) => "known:extent"
    | .knownContractDifference (.usedDType ..) => "known:usedDType"
    | .nativeFailure => "nativeFailure"
    | .nativeDiscrepancy => "nativeDiscrepancy"
    | .comparisonRefused => "comparisonRefused"
    | .nativeUnavailable => "nativeUnavailable"
    | _ => "other"

-- fixtures (appended; guards below)
private def fA := snap 8 [k] [.assign "Y" [.affine (.scale 2 a)] readX]
private def fB := snap 6 [k] [.assign "Y" [.affine (.shift a 2)] readX]
private def fC := snap 4 [a, a] [.assign "Y" [.free a, .free a] readX]
private def fD := snap 7 [k] [.scatter "Y" [convSlot] readXW sumOpts]
private def fD' := snap 4 [k] [.scatter "Y" [.affine (.const 3)] readX sumOpts]
private def fE := snap 8 [k] [.assign "Y" [.affine (.scale 2 a)] readXW]
private def fF := snap 6 [k] [.assign "Y" [convSlot] readXW]
private def fF' := snap 12 [k] [.assign "Y" [.affine (.affine 0 [(1, a), (4, b)])] readXW]
private def fG := snap 8 [k] [.assign "Y" [.affine (.scale 2 a)] readX,
  .assign "Y" [.affine (.shift a 1)] readX]
private def fH6 := snap 6 [k] [.assign "Y" [.affine (.scale 2 a)] readX]
private def fH9 := snap 9 [k] [.assign "Y" [.affine (.scale 2 a)] readX]
private def fI1 := snapB 1 5 [k] [.assign "Y" [.affine (.const 3)] readW]
private def fI2 := snap 5 [k] [.assign "Y" [.affine (.const 3)] readX]
/-- Masking negative: the collision of `fE` plus an independent constant-slot statement on `Z`
that makes the legacy leg fail at COMPILATION (not at the predicted evaluation-time collision). -/
private def fMask : SourceSnapshot :=
  let s := snap 8 [k] [.assign "Y" [.affine (.scale 2 a)] readXW,
    .assign "Z" [.affine (.const 3)] readX]
  { s with
    resolved := { s.resolved with decls := s.resolved.decls ++ [.typedTensor .f64 "Z" [k]] }
    specs := s.specs ++ [⟨6, .output, [8]⟩] }

-- Observed classifications (p3_observed.md). Parity: C is a diagonal write.
#guard tag fA == "parity"
#guard tag fB == "parity"
#guard tag fC == "parity"
-- Checked leg refuses the multi-axis / constant slot (capability); legacy sums like the oracle.
#guard tag fD == "nativeFailure"
#guard tag fD' == "nativeFailure"
-- Collision under the reject policy: E vs its parity neighbour A (one RHS factor).
#guard tag fE == "known:collision"
#guard tag fF == "known:collision"
-- F's non-colliding neighbour (b coefficient 1 -> 4): no condition, native refusal stays a failure.
#guard tag fF' == "nativeFailure"
-- Multi-writer vs single writer; extent override vs equal extent (A); out-of-range refusal.
#guard tag fG == "known:multiWriter"
#guard tag (snap 8 [k] [.assign "Y" [.affine (.scale 2 a)] readX]) == "parity"
#guard tag fH9 == "known:extent"
#guard tag fH6 == "refused:writeOutOfRange"
-- Constant slots: compile `overlappingScatter` under the reject policy, whatever the RHS.
#guard tag fI1 == "nativeFailure"
#guard tag fI2 == "nativeFailure"
-- Masking negative: fE's collision is detected, but legacy fails at compilation (the independent
-- constant-slot statement on Z), not with the predicted collision, so no condition applies.
#guard tag fMask [5, 6] == "nativeFailure"

/-- Profile verdict on `fE`'s oracle result with one occurrence of the first nonempty fiber dropped
and every sum (fiber, contribution, tensor cell) adjusted so only the COUNT is inconsistent. -/
private def dropOccurrence (drop : Bool) : String :=
  match Debug.sourceDebugAffine fE none with
  | .error _ => "no run"
  | .ok run => match Oracle.run run.source.admitted (some [5]) with
    | .error _ => "no oracle"
    | .ok r =>
      match r.contributions.find? (fun c => c.terms.any (fun f => !f.occurrences.isEmpty)) with
      | none => "no occurrence"
      | some c => match c.terms with
        | [f] => match f.occurrences with
          | o :: rest =>
            let d : ℚ := if drop then o.value else 0
            let f' := if drop then { f with occurrences := rest, value := f.value - d } else f
            let c' := { c with terms := [f'], value := c.value - d }
            let idx := c.coordinate.headD 0
            let r' : Oracle.Result := {
              tensors := r.tensors.map fun t => if t.declaration == 5 then
                { t with values := t.values.set idx (t.values.getD idx 0 - d) } else t
              contributions := r.contributions.map fun x =>
                if x.coordinate == c.coordinate && x.origin == c.origin then c' else x }
            match NumericalProfile.checkRunProfile run (.ok r') with
            | .error (.receipt _ (.occurrences e n)) => s!"occurrences {e} {n}"
            | .error u => s!"other {repr u}"
            | .ok _ => "accepted"
          | [] => "empty"
        | _ => "terms"

#guard dropOccurrence false == "accepted"
#guard dropOccurrence true == "occurrences 3 2"

end SourceDifferentialScatterTest

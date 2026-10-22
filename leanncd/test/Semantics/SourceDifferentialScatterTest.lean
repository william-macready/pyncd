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
/-- `fE` (now parity) plus an independent constant-slot statement on `Z` that makes the legacy leg
fail at COMPILATION (`overlappingScatter "Z"`). -/
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
-- Collisions sum (S3a): E (`b` contracted onto one cell) is parity like its one-factor neighbour A.
-- F (`a+b`) and its neighbour F' (b coefficient 4) stay `nativeFailure`: the checked leg refuses the
-- multi-axis slot (the capability refusal is pinned after `mentions` is defined).
#guard tag fE == "parity"
#guard tag fF == "nativeFailure"
#guard tag fF' == "nativeFailure"
-- Multi-writer vs single writer; extent override vs equal extent (A); out-of-range refusal.
#guard tag fG == "known:multiWriter"
#guard tag (snap 8 [k] [.assign "Y" [.affine (.scale 2 a)] readX]) == "parity"
#guard tag fH9 == "known:extent"
#guard tag fH6 == "refused:writeOutOfRange"
-- Constant slots: compile `overlappingScatter` under the reject policy, whatever the RHS.
#guard tag fI1 == "nativeFailure"
#guard tag fI2 == "nativeFailure"
-- Legacy fails at compilation (the independent constant-slot statement on Z) and the checked leg
-- refuses it the same way: `nativeFailure`, no condition applies.
#guard tag fMask [5, 6] == "nativeFailure"

/-- The structural conditions the source alone predicts for `s` (`compareSource`'s `conditions`). -/
private def conditionCount (s : SourceSnapshot) : Nat :=
  match compareSource s (some [5]) with
  | .ok run => run.conditions.length
  | .error _ => 99

-- S3a: collisions sum (production and oracle agree), so a colliding write predicts NO condition:
-- `fE` (`Y[2a] := X[a]*W[b]`, `b` contracted onto one cell) and `fF` (`a+b`) have nothing to detect
-- for collisions; `fF`'s declared extent 6 differs from the derived 7, so it keeps exactly the
-- extent condition, and `fG`'s two non-bare writers keep the multi-writer condition.
#guard conditionCount fE == 0
#guard conditionCount fF == 1
#guard conditionCount fG == 1

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

/-! T4-A2 (review F4): LEGACY-ONLY agreement. The checked plan refuses `fD`/`fD'` by capability,
so four-leg parity is impossible and `tag` is `nativeFailure`; the legacy production leg's VALUES
(which sum collisions) are asserted here against the oracle and against hand-computed cells. -/

/-- Cells of the legacy leg's declaration-5 output, as raw bits (`none` unless the leg is observed
and binds declaration 5). -/
private def legacyCells (s : SourceSnapshot) : Option (List UInt64) :=
  match compareSource s (some [5]) with
  | .error _ => none
  | .ok run => match run.native with
    | .error _ => none
    | .ok n => match n.legacy with
      | .observed o => match o.outputs with
        | .ok bs => (bs.find? fun x => x.metadata.declaration == 5).map fun x => x.bits.toList
        | .error _ => none
      | _ => none

/-- The oracle's declaration-5 cells as the bits of the exactly-representable float of each value
(`none` if any value is not an integer, so the comparison is exact). -/
private def oracleCells (s : SourceSnapshot) : Option (List UInt64) :=
  match compareSource s (some [5]) with
  | .error _ => none
  | .ok run => match run.oracle with
    | .error _ => none
    | .ok r => match r.tensors.find? (fun (t : Oracle.Tensor) => t.declaration == 5) with
      | none => none
      | some t =>
        if t.values.all (fun (q : ℚ) => q.den == 1)
        then some (t.values.map fun (q : ℚ) => (Float.ofInt q.num).toBits) else none

private def handBits (xs : List Float) : Option (List UInt64) := some (xs.map Float.toBits)

/-- The legacy leg is compared against the profile with `agreement` (tolerance profile). -/
private def legacyCompared (s : SourceSnapshot) : Bool :=
  match compareSource s (some [5]) with
  | .error _ => false
  | .ok run => match run.legacyComparison with
    | .compared (.ok .agreement) => true
    | _ => false

/-- LEGACY-ONLY agreement: nonempty, bit-identical to the oracle, and the comparison says agreement. -/
private def legacyMatchesOracle (s : SourceSnapshot) : Bool :=
  match legacyCells s, oracleCells s with
  | some l, some o => !l.isEmpty && l == o && legacyCompared s
  | _, _ => false

-- Hand values, from X = [1,2,3,4], W = [1,10,100], Y[a+b] += X[a]*W[b], |k| = 7:
--   cell0 = 1*1 = 1; cell1 = 2*1 + 1*10 = 12; cell2 = 3*1 + 2*10 + 1*100 = 123;
--   cell3 = 4*1 + 3*10 + 2*100 = 234; cell4 = 4*10 + 3*100 = 340; cell5 = 4*100 = 400; cell6 = 0.
-- A last-write-wins or dropped-occurrence total changes cells 1..5 (e.g. cell1 would be 10 or 2).
#guard legacyCells fD == handBits [1, 12, 123, 234, 340, 400, 0]
#guard oracleCells fD == handBits [1, 12, 123, 234, 340, 400, 0]
#guard legacyMatchesOracle fD
-- fD': Y[3] += X[a] over a: 1+2+3+4 = 10; the other cells are 0 (|k| = 4).
#guard legacyCells fD' == handBits [0, 0, 0, 10]
#guard oracleCells fD' == handBits [0, 0, 0, 10]
#guard legacyMatchesOracle fD'

-- ACCEPT-NEIGHBOURS (collision-free `.scatter`, same assertion shape; not vacuous):
-- fN: Y[a+4b] += X[a]*W[b], |k| = 16 (production derives shape 16 from the write form, p3_observed
--   (f'): a declared 12 gives a shape-binding issue, not a value): slots a+4b are distinct, so
--   Y = X[a]*W[b] laid out as b=0: 1,2,3,4; b=1: 10,20,30,40; b=2: 100,200,300,400; cells 12..15 = 0.
private def fN := snap 16 [k] [.scatter "Y" [.affine (.affine 0 [(1, a), (4, b)])] readXW sumOpts]
-- fN': Y[2a] += X[a], |k| = 8: Y = 1,0,2,0,3,0,4,0.
private def fN' := snap 8 [k] [.scatter "Y" [.affine (.scale 2 a)] readX sumOpts]
#guard legacyCells fN == handBits [1, 2, 3, 4, 10, 20, 30, 40, 100, 200, 300, 400, 0, 0, 0, 0]
#guard legacyMatchesOracle fN
#guard legacyCells fN' == handBits [1, 0, 2, 0, 3, 0, 4, 0]
#guard legacyMatchesOracle fN'

/-! T4-A1 two-tensor programs, after S3a (collisions sum, so the origin-bound collision rows that
named `Y`/`Z` in a native collision error lost their referent and are deleted; `Z` is declaration 6,
over `a`). Kept: the stale-`rejectCollisions` bare scatter (now parity) and the checked-leg
constant-slot refusal naming `Z`. -/

private def rejOpts : ScatterOpts := { reduce := .rejectCollisions }

private def withZ (kExtent : Nat) (stmts : List Stmt) : SourceSnapshot :=
  let s := snap kExtent [k] stmts
  { s with
    resolved := { s.resolved with decls := s.resolved.decls ++ [.typedTensor .f64 "Z" [a]] }
    specs := s.specs ++ [⟨6, .output, [4]⟩] }

/-- The per-leg report (`observe`) mentions `needle` (pins which tensor each leg's error names). -/
private def mentions (s : SourceSnapshot) (needle : String) : Bool :=
  ((observe s).splitOn needle).length > 1

-- Review F11 probe: a BARE-slot scatter with the stale `rejectCollisions` option and `b` contracted,
-- `Z[a] := X[a]*W[b]`. Production ignores the option and sums (Z = X[a]*(1+10+100)), like the
-- oracle: four-leg parity (observed; before S3a both native legs rejected it as a collision).
private def zBare : Stmt := .scatter "Z" [.free a] readXW rejOpts
private def fF11 := withZ 8 [zBare, .assign "Y" [.affine (.scale 2 a)] readX]
#guard tag fF11 [5, 6] == "parity"
#guard mentions fF11 "legacy=value [(Y, ([8], [1.000000, 0.000000, 2.000000, 0.000000, 3.000000, 0.000000, 4.000000, 0.000000])), (Z, ([4], [111.000000, 222.000000, 333.000000, 444.000000]))]"
#guard mentions fF11 "checked=value [(Y, ([8], [1.000000, 0.000000, 2.000000, 0.000000, 3.000000, 0.000000, 4.000000, 0.000000])), (Z, ([4], [111.000000, 222.000000, 333.000000, 444.000000]))]"

-- fF/fF' stay `nativeFailure` through the checked leg's multi-axis capability refusal, not a collision.
#guard mentions fF "multiAxisScatterLhs \"Y: affine LHS slot\""
#guard mentions fF' "multiAxisScatterLhs \"Y: affine LHS slot\""
#guard !mentions fF "collision"

-- CHECKED-only refusal: Z's constant-slot scatter (legacy sums it into Z = [0,0,0,10]; the checked
-- plan refuses it at preparation naming Z) next to fE's agreeing write on Y: the program is still a
-- `nativeFailure` and the refusal names Z.
private def fOriginC := withZ 8 [.scatter "Z" [.affine (.const 3)] readX sumOpts,
  .assign "Y" [.affine (.scale 2 a)] readXW]
#guard mentions fOriginC "scatterOrAffineLhs \"Z: constant affine LHS slot\""
#guard mentions fOriginC "(Z, ([4], [0.000000, 0.000000, 0.000000, 10.000000]))"
#guard tag fOriginC [5, 6] == "nativeFailure"

-- S3a: the colliding `fE` (`b` contracted onto the cell `2a`) is four-leg parity and its values are
-- the contraction sums Y[2a] = X[a] * (1 + 10 + 100), from legacy and from the oracle alike.
#guard legacyCells fE == handBits [111, 0, 222, 0, 333, 0, 444, 0]
#guard oracleCells fE == handBits [111, 0, 222, 0, 333, 0, 444, 0]
#guard legacyMatchesOracle fE
-- Accept-neighbour: the injective affine `.scatter` fN' (no collision before or after S3a) stays parity.
#guard tag fN' == "parity"

end SourceDifferentialScatterTest

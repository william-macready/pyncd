import LeanNCD.Eval.Plan.Scan

namespace IndexedExecutionExperiment.AffineScan

open LeanNCD.Eval.Plan

def baseAssign (c : CheckedScanPlan) : AssignPlan :=
  ((c.raw.baseBlock.steps.getD 0 default).assign?).getD default

def stepAssign (c : CheckedScanPlan) : AssignPlan :=
  ((c.raw.stepBlock.steps.getD 0 default).assign?).getD default

def plainRead (r : ReadPlan) : Bool :=
  r.unary.isNone && !r.boolToTropical && !r.realToBool

def allCaptures (c : CheckedScanPlan) : List BlockCapture :=
  c.raw.baseCaptures.toList ++ c.raw.stepCaptures.toList

def externalCapture (c : CheckedScanPlan) (slot : Nat) : Bool :=
  (allCaptures c).any (fun cap => decide (cap.source = .external slot))

def capturesBounded (c : CheckedScanPlan) : Bool :=
  (allCaptures c).all (fun cap => match cap.source with
    | .external slot => decide (slot < c.sigs.size)
    | .state _ => true)

def stateRowsOk (t : TermPlan) (r : ReadPlan) : Bool :=
  r.map.coeffs.toList ==
    [r.map.coeffs.getD 0 #[],
      if t.contextPos == #[0] then #[1, 0] else #[0, 1]] &&
  r.map.bias.toList == [r.map.bias.getD 0 0, r.map.bias.getD 1 0] &&
  decide (r.map.bias.getD 1 0 ≤ 0)

def termSupported (c : CheckedScanPlan) (d n : Nat) (t : TermPlan) : Bool :=
  t.iterationShape.size == 2 &&
  ((t.contextPos == #[0] && t.outputPos == #[1]) ||
    (t.contextPos == #[1] && t.outputPos == #[0])) &&
  t.positionsPartition && t.contextProjection == #[n] &&
  t.outputProjection == #[d] && t.reductionPos.isEmpty &&
  t.contextPos.size == 1 && t.outputPos.size == 1 &&
  t.factors.all (fun
    | .iverson _ => false
    | .read r =>
        plainRead r &&
        r.map.coeffs.size == r.sourceShape.size &&
        r.map.bias.size == r.sourceShape.size &&
        r.map.coeffs.all (fun row => row.size == t.iterationShape.size) &&
        match c.raw.stepBlock.tensorSigs[r.sourceSlot]? with
        | none => false
        | some sig =>
            decide (sig.dtype = .f64) && sig.shape == r.sourceShape &&
            match c.raw.stepCaptures.find? (fun cap => cap.inputSlot == r.sourceSlot) with
            | none => false
            | some cap => match cap.source with
                | .external outer => decide (c.sigs[outer]? = some sig) &&
                    externalCapture c outer
                | .state si => si == 0 &&
                    stateReadCausal #[1] t.contextPos r &&
                    stateRowsOk t r &&
                    decide (c.sigs[(c.raw.states.getD 0 default).destSlot]? = some sig))

def identityBase (d : Nat) : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[d], algebra := admittedAlgebra, terms := #[{ iterationShape := #[d], contextPos := #[], outputPos := #[0], reductionPos := #[], factors := #[.read { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[d], oobPolicy := .zeroPad }] }] }

/-- First profile door: binary64 metadata, exact rational sum/product interpretation. -/
def profileOk (c : CheckedScanPlan) (d n : Nat) : Bool :=
  let state := c.raw.states.getD 0 default
  let base := baseAssign c
  let step := stepAssign c
  let z := (c.raw.baseCaptures.getD 0 default)
  let zOuter := match z.source with | .external slot => some slot | .state _ => none
  capturesBounded c && decide (c.storageKind = .float64) &&
  decide (c.raw.states = #[{ destSlot := state.destSlot, advancingDims := #[1], materialization := .completeHistory, initValue := .zero }]) &&
  decide (c.sigs[state.destSlot]? = some { shape := #[d, n + 1], dtype := .f64 }) &&
  c.raw.historyExtents == #[n + 1] && c.stepExtents == #[n] &&
  c.raw.baseBlock.contextShape == #[] && c.raw.stepBlock.contextShape == #[n] &&
  decide (c.raw.baseBlock.steps = #[.assign base]) && decide (c.raw.stepBlock.steps = #[.assign step]) &&
  decide (c.raw.baseCaptures = #[z]) && z.inputSlot == 0 && zOuter.isSome &&
  zOuter != some state.destSlot &&
  decide ((zOuter.bind (fun slot => c.sigs[slot]?)) = some { shape := #[d], dtype := .f64 }) &&
  c.raw.baseBlock.inputs == #[0] && c.raw.baseBlock.outputs == #[1] &&
  decide (c.raw.baseBlock.tensorSigs =
    #[{ shape := #[d], dtype := .f64 }, { shape := #[d], dtype := .f64 }]) &&
  decide (base = identityBase d) &&
  decide (c.raw.baseWrites = #[{ outputSlot := 1, stateIndex := 0, map := { coeffs := #[#[1], #[0]], bias := #[0, 0] } }]) &&
  c.raw.stepBlock.outputs == #[step.destinationSlot] &&
  step.contextShape == #[n] && step.outputShape == #[d] && decide (step.algebra = admittedAlgebra) &&
  step.terms.all (termSupported c d n) &&
  decide (c.raw.stepWrites = #[{ outputSlot := step.destinationSlot, stateIndex := 0, map := { coeffs := #[#[0, 1], #[1, 0]], bias := #[0, 1] } }])

structure Profile (d n : Nat) where
  checked : CheckedScanPlan
  origin : ∃ sigs raw, checkScanPlan sigs raw = .ok checked
  fields : profileOk checked d n = true

inductive ProfileError
  | checker (error : ScanPlanError)
  | unsupported
  deriving Repr

def certifyProfile (sigs : Array TensorSignature) (raw : RawScanPlan) (d n : Nat) :
    Except ProfileError (Profile d n) :=
  match h : checkScanPlan sigs raw with
  | .error e => .error (.checker e)
  | .ok c =>
      if fields : profileOk c d n = true then
        .ok ⟨c, ⟨sigs, raw, h⟩, fields⟩
      else .error .unsupported

end IndexedExecutionExperiment.AffineScan

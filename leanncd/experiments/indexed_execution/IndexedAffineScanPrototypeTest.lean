import Eval.Plan.ScanCompileTest
import IndexedAffineScanRead
import IndexedAffineScanProfile

namespace IndexedExecutionExperiment.AffineScan.Prototype

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.Eval.Plan.ScanCompileTest Std

/-- `axisPosSched` donor: spatial dimension `d`, history time extent `n + 1`. -/
def spatialSched (d n : Nat) : ScheduledProgram :=
  { axisPosSched with
    decls := [.iter axL (n + 1), .axis axJ (some d)]
    explicitSizes := (({} : HashMap UID Nat).insert axL.uid (n + 1)).insert axJ.uid d }

def spatialInputs (d : Nat) : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "S0" ⟨[d], Array.replicate d 1.0⟩

def boundaryCheck (d n : Nat) : Except String Unit :=
  withPrepared "affine prototype boundary" (spatialSched d n) (spatialInputs d) fun p => do
    let some raw := scanAt p 0 | .error "not a scan"
    expectEq "historyExtents" raw.historyExtents #[n + 1]
    expectEq "step context" raw.stepBlock.contextShape #[n]
    expectEq "state signature" p.plan.raw.tensorSigs[1]?
      (some { shape := #[d, n + 1], dtype := .f64 })
    checkerAgrees "boundary" p 0
    match certifyProfile p.plan.raw.tensorSigs raw d n with
    | .ok _ => pure ()
    | .error e => .error s!"profile: {repr e}"

run_cmd
  for (d, n) in [(2, 2), (2, 0), (0, 2), (0, 0)] do
    match boundaryCheck d n with
    | .ok _ => Lean.logInfo m!"accepted spatial={d}, recurrence={n}"
    | .error e => throwError e

end IndexedExecutionExperiment.AffineScan.Prototype

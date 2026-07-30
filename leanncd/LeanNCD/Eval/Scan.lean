import LeanNCD.Eval.Contract
import LeanNCD.Eval.Nonlin
import LeanNCD.DSL.Pipeline.Types
namespace LeanNCD.Eval
open Std

/-- All iteration slots `(uid, position)` of a base/recur stmt, in slot order
    (ascending position). One entry per `.iterAt`/`.iterNext` slot — multi-axis scans yield
    several. -/
def iterSlotPositions (s : Stmt) : List (UID × Nat) :=
  s.iterInfo.map (fun it => (it.axis.uid, it.pos))

/-- Cartesian product of a list of index ranges → list of tuples (each tuple a `List Nat`), in
    reverse-lexicographic order (last axis slowest). This order is a linear extension of the
    componentwise ≤ order, so a cell writing at `+1` on every advancing axis (reading only cells at
    offset ≤ 0 — the causality guarantee) always sees its dependencies already computed. -/
def cartesianList : List (List Nat) → List (List Nat)
  | []      => [[]]
  | r :: rs => (cartesianList rs).flatMap (fun tail => r.map (fun x => x :: tail))

/-- Evaluate ONE stmt with a SET of iteration axes pinned (`seed : uid ↦ value`), over the
    remaining (non-seeded) free axes, returning `(name, slice)` where `slice` has the non-seeded
    free-axis shape. Reads gather from `env`, which holds the partial state at ALL iterations, so a
    read `G[…,l]` works. The seeded axes are pinned via `evalAssignSeeded`. Applies the RHS nonlin.

    The slice's axes are the NON-seeded free slots in slot order (see `evalAssignSeeded`), so the
    softmax/normalize reduction axis is the position of the output slot marked `m.` (the norm flag
    lives on the output slot — see `normAxisUidOf`) within that slice-axis list. This holds uniformly
    whether or not the stmt is itself a scan-state; pinned by the `!seed.contains ·` filter, which
    drops every seeded axis exactly as `evalAssignSeeded` does. -/
def evalStmtSliceSeeded (env : HashMap String DenseTensor) (sizes : HashMap UID Nat)
    (seed : HashMap UID Int) (s : Stmt) : Except EvalError (String × DenseTensor) := do
  match s with
  | .assign nm slots rhs =>
      -- honor the contraction aggregator (KG-scanagg): `maxreduce`/`minreduce` ⇒ tropical max/min, else ℝ sum.
      let c : Combine := match rhs.agg with
        | .max => Combine.max
        | .min => Combine.min
        | .sum => Combine.real
      let (_, slice) ← evalAssignSeeded c.mul c.combine c.unit0 env sizes seed nm slots rhs
      let sliceUids := (slots.filterMap (·.axisUID?)).filter (fun u => ! seed.contains u)
      let pos ← match rhs.nonlin with
        | .identity | .pointwise _ =>
            pure 0     -- pointwise: reduction axis irrelevant
        | .axiswise _ _ => match normAxisUidOf slots with
            | some nu => match sliceUids.findIdx? (· == nu) with
                | some p => pure p
                | none   => throw s!"evalStmtSliceSeeded: marked norm axis of {nm} is not among its slice axes"
            | none    => throw s!"evalStmtSliceSeeded: {nm} applies softmax/normalize but no output axis is marked (·)"
      return (nm, applyNonlin rhs.nonlin pos sliceUids slice)
  | _ => throw "evalStmtSliceSeeded: only assign stmts are supported in scans"

/-- Write a non-iter `slice` into the full state tensor `out`, given the iteration `(position, index)`
    pairs (one per advancing axis of the stmt). The slice's coords are the out-coords with all
    iteration positions removed; rebuild the full coord by inserting each iteration index at its
    position in ASCENDING position order (so earlier insertions don't shift later ones). -/
def writeSliceAtMulti (out : DenseTensor) (iters : List (Nat × Nat)) (slice : DenseTensor) : DenseTensor :=
  let sorted := iters.mergeSort (fun a b => a.1 ≤ b.1)   -- ascending by position
  (DenseTensor.allCoords slice.shape).foldl (fun cur scoord =>
    let ocoord := sorted.foldl (fun acc (pos, idx) => acc.insertIdx pos idx) scoord
    cur.set! ocoord (slice.get! scoord)) out

/-- Evaluate a ScanStmt → the scanned state tensors. Multi-axis (n-D) scans iterate the cartesian
    product of `[0 … L_a − 2]` over every advancing axis. Boundary semantics (zero-default): the
    step writes only fully-advanced cells (every advancing index `+1 ≥ 1`); boundary cells (any
    advancing index `= 0`) keep the zero-allocated state, except where an explicit base stmt pins
    a slice at index 0. -/
def evalScan (env : HashMap String DenseTensor) (sizes : HashMap UID Nat) :
    ScanStmt → Except EvalError (List (String × DenseTensor))
  | .plain _      => .error "evalScan: plain handled by evalScheduled, not here"
  | .scanPre nm _ _ => .error s!"evalScan: scanPre (recurMorphism escape hatch) evaluation unsupported ({nm})"
  | .scan _ axes base recur _ => do
      if axes.isEmpty then .error "evalScan: scan node has no iteration axis" else
      let axUids := axes.map (·.uid)
      -- Per-axis length, in `axes` order. FAIL LOUD on an unsized iteration axis: an unspecified
      -- extent is NOT an extent of zero. The former `(sizes[u]?).getD 0` conflated the two, which
      -- made `List.range (L-1)` run no recurrence steps AND drove an unchecked `Array.set!` in the
      -- base-slice write below — so a plain surface program with no `axis l` pin
      -- (`tensor X(j); G[j,0] := X[j]; G[j,l+1] := G[j,l]`) PANICKED with "index out of bounds"
      -- instead of returning an error. Reproduced 2026-07-30; see `papers/semantic_payload_audit.md`
      -- finding #5. This reverses the `RJ6` entry in `test/Eval/Portfolio/RejectTest.lean`, which
      -- recorded "do NOT reject" without knowing the path panicked.
      -- NOTE (untested adjacent case): an axis pinned explicitly to `0` still yields `L = 0`; that is
      -- a stated intent rather than a sizing gap, and is not covered by this check.
      let Ls ← axes.mapM (fun a =>
        match sizes[a.uid]? with
        | some n => pure n
        | none   => throw s!"evalScan: unsized iteration axis '{a.name}' (uid {a.uid}) — pin it with \
`axis {a.name} : ℕ = N`, or ensure some read fixes its extent")
      let stateNames := (base.map Stmt.lhsName).eraseDups
      -- 1. allocate each state tensor (zeros at full shape) from its base slots.
      let mut work := env
      for s in base do
        match s with
        | .assign nm slots _ => work := work.insert nm (DenseTensor.zeros (outputShape sizes slots))
        | _ => throw "evalScan: base stmts must be assigns"
      -- 2. fill boundaries from base stmts: each base pins a subset of axes to their literal index
      --    and fills that slice over its free axes (e.g. `G[r,0]` fills the c=0 column for all r).
      for s in base do
        let seed : HashMap UID Int := ((s.slots).filterMap (fun
            | .iterAt a n => some (a.uid, n) | _ => none)).foldl (fun m (u, n) => m.insert u n) {}
        let (nm, slice) ← evalStmtSliceSeeded work sizes seed s
        let iters := (iterSlotPositions s).map (fun (u, p) => (p, ((seed[u]?).getD 0).toNat))
        work := work.insert nm (writeSliceAtMulti ((work[nm]?).getD (DenseTensor.zeros [])) iters slice)
      -- 3. nested loop over ∏ [0 … L_a − 2]: run the recur list at each tuple; intermediates into
      --    the step env; write final state slices at (position, index+1) per advancing axis.
      let ranges := Ls.map (fun L => List.range (L - 1))
      for tup in cartesianList ranges do          -- tup : one index per axis, in `axes` order
        let seed : HashMap UID Int := (axUids.zip tup).foldl (fun m (u, v) => m.insert u (Int.ofNat v)) {}
        let mut stepEnv := work
        for s in recur do
          let (nm, slice) ← evalStmtSliceSeeded stepEnv sizes seed s
          -- classify by NAME: only the allocated scan states (`stateNames`) are written into `work`.
          -- A per-step intermediate may itself carry an iteration slot (e.g. a `splitNonlins`-lifted
          -- `%nl…` derived from the recurrence), but it is NOT an allocated state — keep it as a raw
          -- slice in the step env only. (This is the crucial distinction from a slot-based test.)
          if stateNames.contains nm then
            -- a state slice: write at (position, currentIndex+1) for each of THIS stmt's advancing axes
            let iters := (iterSlotPositions s).map (fun (u, p) => (p, ((seed[u]?).getD 0).toNat + 1))
            let updated := writeSliceAtMulti ((work[nm]?).getD (DenseTensor.zeros [])) iters slice
            work := work.insert nm updated
            stepEnv := stepEnv.insert nm updated
          else
            stepEnv := stepEnv.insert nm slice
      -- 4. return the scanned state tensors
      return stateNames.filterMap (fun nm => (work[nm]?).map (fun t => (nm, t)))

end LeanNCD.Eval

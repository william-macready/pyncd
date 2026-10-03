import LeanNCD.Eval.Contract
import LeanNCD.Eval.Error
import LeanNCD.Eval.Nonlin
import LeanNCD.Eval.Slots
import LeanNCD.Eval.SizeSolve
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

/-- Normalized nonzero LHS source axes for scan-scatter computation, de-duplicated by UID in
    first-seen order. Raw canceled axes remain sizing obligations through `LHSSlot.outExtent`, but
    they are contractions rather than dense output coordinates. -/
def scanScatterSourceAxes (slots : List LHSSlot) : List AxisSpec :=
  (slots.flatMap (fun sl =>
    let rawAxes :=
      (IdxExpr.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩) sl.outIdx).run
    let (_, coeffs) := idxAffineForm sl.outIdx
    let normalized := SizeSolve.normalizeCoeffs coeffs
    rawAxes.filter (fun a => normalized.any (fun (_, u) => u == a.uid)))).foldl
    (fun acc a =>
      if acc.any (fun seen => seen.uid == a.uid) then acc else acc ++ [a]) []

/-- Evaluate ONE stmt with a SET of iteration axes pinned (`seed : uid ↦ value`), over its
    remaining dense source axes, returning `(name, slice)`. Reads gather from `env`, which holds the
    partial state at ALL iterations, so a read `G[…,l]` works. The seeded axes are pinned via
    `evalAssignSeeded`. A scatter is computed as a plain projection over its non-seeded LHS source
    axes; its original affine slots are used only later, when placing the completed dense slice.

    The slice's axes are the NON-seeded free slots in slot order (see `evalAssignSeeded`), so the
    softmax/normalize reduction axis is the position of the output slot marked `m.` (the norm flag
    lives on the output slot — see `normAxisUidOf`) within that slice-axis list. This holds uniformly
    whether or not the stmt is itself a scan-state; pinned by the `!seed.contains ·` filter, which
    drops every seeded axis exactly as `evalAssignSeeded` does.

    The storage refusal (`rejectUnsupportedStorage`, `Contract.lean`) is installed at the ENTRY for
    the same reason it is on `evalPlain`: the `.scatter` arm reaches its own
    `unsupportedScatterNonlin` check and rebuilds its slots before delegating, so an f32 scatter
    would otherwise be reported as a nonlinearity failure rather than a dtype one. -/
def evalStmtSliceSeeded (decls : List Decl) (env : HashMap String DenseTensor) (sizes : HashMap UID Nat)
    (seed : HashMap UID Int) (s : Stmt) : Except EvalError (String × DenseTensor) := do
  rejectUnsupportedStorage decls (stmtStorageNames s)
  match s with
  | .assign nm slots rhs =>
      let (_, slice) ← evalAssignDtypedSeeded decls env sizes seed nm slots rhs
      let sliceUids := (slots.filterMap (·.axisUID?)).filter (fun u => ! seed.contains u)
      let rn ← resolveNonlin rhs.nonlin slots sliceUids
      return (nm, applyNonlin rn sliceUids slice)
  | .scatter nm slots rhs _ =>
      if rhs.nonlin ≠ Nonlin.identity then
        throw (.unsupportedScatterNonlin nm)
      let sourceAxes := (scanScatterSourceAxes slots).filter (fun a => ! seed.contains a.uid)
      evalAssignDtypedSeeded decls env sizes seed nm (sourceAxes.map LHSSlot.free) rhs
  | .recurMorphism _ _ _ => throw (.invalidScanNode .onlyAssignInSlice)

/-- Full persistent-state shape for one scan statement. Iteration slots retain their declared
    history extent; every other slot uses the shared scatter-output extent rule. -/
def scanStateShape (sizes : HashMap UID Nat) (slots : List LHSSlot) :
    Except EvalError (List Nat) :=
  slots.mapM (fun sl => match sl with
    | .iterAt a _ | .iterNext a =>
        match sizes[a.uid]? with
        | some n => pure n
        | none   => throw (.shape (.unsizedAxis a.uid (.scanIteration a.name)))
    | _ =>
        match sl.outExtent (fun u => sizes[u]?) with
        | some n => pure n
        | none   => throw (.shape (.unsizedScatterOutput sl)))

/-- Place a completed dense source slice into a persistent scan state. Ordinary assignments retain
    their slot-order source basis; scatters use their first-seen LHS source-axis basis. In both cases
    every original LHS expression is evaluated only after RHS contraction has produced `slice`. -/
def writeScanStmtSlice (out : DenseTensor) (seed : HashMap UID Int) (s : Stmt)
    (slice : DenseTensor) : DenseTensor :=
  let sliceUids : List UID := match s with
    | .assign _ slots _ =>
        (slots.filterMap LHSSlot.axisUID?).filter (fun u => ! seed.contains u)
    | .scatter _ slots _ _ =>
        ((scanScatterSourceAxes slots).filter
          (fun a => ! seed.contains a.uid)).map AxisSpec.uid
    | .recurMorphism _ _ _ => []
  (DenseTensor.allCoords slice.shape).foldl (fun cur scoord =>
    let coord := (sliceUids.zip scoord).foldl
      (fun m (u, v) => m.insert u (Int.ofNat v)) seed
    let outCoordZ := s.slots.map (fun sl => evalIdx coord sl.outIdx)
    if outCoordZ.length == out.shape.length &&
        (outCoordZ.zip out.shape).all (fun (z, d) => 0 ≤ z && z < (d : Int)) then
      cur.set! (outCoordZ.map Int.toNat) (slice.get! scoord)
    else
      cur) out

/-- One state dimension of a base write, read off its LHS slot. This is the reference's OWN
    classification (it deliberately does not call the checked backend's `classifyWriteRow`): a
    pinned literal, a free face spanning the dimension, a positive-scale strided placement, or
    anything else (never separates two writes). -/
private inductive BaseDim
  | pinned (lit : Int)
  | face
  | strided (scale offset : Int)
  | other

private def baseDimOf : LHSSlot → BaseDim
  | .iterAt _ n => .pinned n
  | .free _ | .freeNorm _ | .iterNext _ => .face
  | .affine e =>
      let (c0, cf) := idxAffineForm e
      match SizeSolve.normalizeCoeffs cf with
      | []        => .pinned c0
      | [(c, _)]  => if c > 0 && c0 ≥ 0 then .strided c c0 else .other
      | _         => .other

/-- Whether one dimension forces two base writes apart: different pinned literals, or two strided
    placements of equal positive scale whose offsets differ modulo that scale. Everything else is
    conservatively overlapping. -/
private def baseDimsSeparate : BaseDim → BaseDim → Bool
  | .pinned a, .pinned b => a != b
  | .strided sa oa, .strided sb ob => sa > 0 && sa == sb && oa % sa != ob % sb
  | _, _ => false

/-- A base write touches a scan boundary iff the slot carrying some scan axis is `.iterAt _ 0`.
    A base that omits a scan axis from its LHS altogether is a different fault (the checked
    backend's `advancingAxisNotInLhs`) and is left alone here. -/
private def baseTouchesBoundary (axUids : List UID) (slots : List LHSSlot) : Bool :=
  let dims := axUids.map (fun u => slots.findIdx? (fun sl => sl.axisUID? == some u))
  dims.any Option.isNone ||
    dims.any (fun d? => match d?.bind (fun d => slots[d]?) with
      | some (.iterAt _ n) => n == 0
      | _ => false)

/-- Shapes 6 and 7: producers of one scan's recurrence block, counted over the WHOLE `recur` list
    in order (reads in between do not reset the count), the first repeat winning. A statement whose
    destination is a state (an assign OR a scatter) is that state's result; any other destination is
    a per-step scratch. Each may be produced once. -/
private def checkRecurProducers (scanName : String) (stateNames : List String)
    (recur : List Stmt) : Except EvalError Unit := do
  let mut results : List (String × Nat) := []
  let mut scratch : List (String × Nat) := []
  for (s, ri) in recur.zipIdx do
    let nm := s.lhsName
    if stateNames.contains nm then
      match results.lookup nm with
      | some first => throw (.duplicateStateResult scanName nm first ri)
      | none => results := (nm, ri) :: results
    else
      match scratch.lookup nm with
      | some first => throw (.duplicateScratchProducer scanName nm first ri)
      | none => scratch := (nm, ri) :: scratch

/-- Shape 8 (and, once added, 9): per-state geometry. Each state's placements are its base
    statements in `base` order, then its (first) result statement; every placement's declared
    extents (`scanStateShape`: history extent on scan-axis slots, the shared LHS-slot extent
    elsewhere, e.g. `2*n` for a stride-2 write) must equal the FIRST placement's, dimension by
    dimension. The old reference allocated each base's shape in turn, so a later base overwrote an
    earlier one's zeros and a mismatched extent silently cropped writes. This needs the inferred
    `sizes`, which `evalScan` already holds when it calls the check, so it is still raised before any
    state is allocated. Placements of different rank are skipped (the checked backend's
    `inconsistentStateRank`, not in scope). -/
private def checkStatePlacements (scanName : String) (sizes : HashMap UID Nat)
    (stateNames : List String) (base recur : List Stmt) : Except EvalError Unit := do
  for st in stateNames do
    let result := (recur.filter (fun s => s.lhsName == st && match s with
      | .recurMorphism .. => false
      | _ => true)).take 1
    let placements := base.filter (·.lhsName == st) ++ result
    let mut expected : Option (List Nat) := none
    for s in placements do
      let shape ← scanStateShape sizes s.slots
      match expected with
      | none => expected := some shape
      | some prev =>
          if prev.length == shape.length then
            for ((p, a), d) in (prev.zip shape).zipIdx do
              if p != a then throw (.inconsistentStateExtent scanName st d p a)

/-- Static structural validation of a scan, run by `evalScan` BEFORE any state is allocated, so
    every rejection precedes evaluation. A scan with several faults reports the FIRST of these, in
    this order (it mirrors the checked backend's phase order in `Plan/Compile.lean`: recurrence
    classification, then per-state geometry, then base-block reads, then base-write placement):
    0. a non-assign base statement (`baseMustBeAssign`, hoisted here so it keeps precedence);
    1. `duplicateStateResult` / `duplicateScratchProducer`, over the `recur` list in order (the
       repeat at the lowest later index wins, whichever kind it is);
    2. `inconsistentStateExtent`, states in first-base order, each placement (bases, then the
       result) against the state's first placement, lowest dimension first;
    3. `baseWriteNotAtBoundary`, in `base` order;
    4. `baseWritesOverlap`, states in first-base order, then the first pair `(a, b)`, `a < b`, in
       `base` order. -/
def checkScanStructure (scanName : String) (axes : List AxisSpec) (sizes : HashMap UID Nat)
    (stateNames : List String) (base recur : List Stmt) : Except EvalError Unit := do
  let axUids := axes.map (·.uid)
  for s in base do
    match s with
    | .recurMorphism .. => throw (.invalidScanNode .baseMustBeAssign)
    | _ => pure ()
  checkRecurProducers scanName stateNames recur
  checkStatePlacements scanName sizes stateNames base recur
  for (s, bi) in base.zipIdx do
    unless baseTouchesBoundary axUids s.slots do
      throw (.baseWriteNotAtBoundary scanName s.lhsName bi)
  for st in stateNames do
    let mine := base.zipIdx.filter (fun (s, _) => s.lhsName == st)
    for (sa, ia) in mine do
      for (sb, ib) in mine do
        if ia < ib &&
            !((sa.slots.zip sb.slots).any
              (fun (x, y) => baseDimsSeparate (baseDimOf x) (baseDimOf y))) then
          throw (.baseWritesOverlap scanName st ia ib)

/-- Evaluate a ScanStmt → the scanned state tensors. Multi-axis (n-D) scans iterate the cartesian
    product of `[0 … L_a − 2]` over every advancing axis. Boundary semantics (zero-default): the
    step writes only fully-advanced cells (every advancing index `+1 ≥ 1`); boundary cells (any
    advancing index `= 0`) keep the zero-allocated state, except where an explicit base stmt pins
    a slice at index 0.

    The storage refusal (`rejectUnsupportedStorage`, `Contract.lean`) is installed at this public
    ENTRY, over every base and recurrence statement's names in `base ++ recur` order, BEFORE the
    scan-structure and iteration-extent checks below — those would otherwise report an f32 scan's
    unrelated structural or sizing defect first, and a well-formed f32 scan would never reach a
    guard at all until `evalStmtSliceSeeded` (after state allocation). -/
def evalScan (decls : List Decl) (env : HashMap String DenseTensor) (sizes : HashMap UID Nat) :
    ScanStmt → Except EvalError (List (String × DenseTensor))
  | .plain _      => .error (.invalidScanNode .plainNotHandledHere)
  | .scanPre nm _ _ => .error (.unsupportedRecurMorphism .evalScanNode nm)
  | .scan scanName axes base recur _ => do
      rejectUnsupportedStorage decls ((base ++ recur).flatMap stmtStorageNames)
      if axes.isEmpty then .error (.invalidScanNode .noIterationAxis) else
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
        | none   => throw (.shape (.unsizedAxis a.uid (.scanIteration a.name))))
      let stateNames := (base.map Stmt.lhsName).eraseDups
      for s in recur do
        if !(stateNames.contains s.lhsName) then
          match s with
          | .scatter _ _ _ _ => throw (.invalidScanNode .onlyAssignInSlice)
          | _ => pure ()
      checkScanStructure scanName axes sizes stateNames base recur
      -- 1. allocate each state tensor (zeros at full shape) from its base slots.
      let mut work := env
      for s in base do
        match s with
        | .assign nm slots _ | .scatter nm slots _ _ =>
            let stateShape ← scanStateShape sizes slots
            work := work.insert nm (DenseTensor.zeros stateShape)
        | _ => throw (.invalidScanNode .baseMustBeAssign)
      -- 2. fill boundaries from base stmts: each base pins a subset of axes to their literal index
      --    and fills that slice over its free axes (e.g. `G[r,0]` fills the c=0 column for all r).
      for s in base do
        let seed : HashMap UID Int := ((s.slots).filterMap (fun
            | .iterAt a n => some (a.uid, n) | _ => none)).foldl (fun m (u, n) => m.insert u n) {}
        let (nm, slice) ← evalStmtSliceSeeded decls work sizes seed s
        let priorState := (work[nm]?).getD (DenseTensor.zeros [])
        work := work.insert nm (writeScanStmtSlice priorState seed s slice)
      -- 3. nested loop over ∏ [0 … L_a − 2]: run the recur list at each tuple; intermediates into
      --    the step env; write final state slices at (position, index+1) per advancing axis.
      let ranges := Ls.map (fun L => List.range (L - 1))
      for tup in cartesianList ranges do          -- tup : one index per axis, in `axes` order
        let seed : HashMap UID Int := (axUids.zip tup).foldl (fun m (u, v) => m.insert u (Int.ofNat v)) {}
        let mut stepEnv := work
        for s in recur do
          let (nm, slice) ← evalStmtSliceSeeded decls stepEnv sizes seed s
          -- classify by NAME: only the allocated scan states (`stateNames`) are written into `work`.
          -- A per-step intermediate may itself carry an iteration slot (a recurrence-only
          -- destination with the same all-axis `+1` shape as a state result — nothing in the
          -- production chain manufactures this today, but a hand-built schedule still can), and it
          -- is NOT an allocated state — keep it as a raw slice in the step env only. (This is the
          -- crucial distinction from a slot-based test.)
          if stateNames.contains nm then
            let updated :=
              writeScanStmtSlice ((work[nm]?).getD (DenseTensor.zeros [])) seed s slice
            work := work.insert nm updated
            stepEnv := stepEnv.insert nm updated
          else
            stepEnv := stepEnv.insert nm slice
      -- 4. return the scanned state tensors
      return stateNames.filterMap (fun nm => (work[nm]?).map (fun t => (nm, t)))

end LeanNCD.Eval

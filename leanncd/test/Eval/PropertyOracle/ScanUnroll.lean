import Eval.PropertyOracle.Compare
import Eval.PropertyOracle.ScanGen

/-!
# Independent scan unroller (Wave F F4, Task 5)

A scan is unrolled into an ordinary **scan-free** program: one leaf tensor per (persistent state,
history coordinate) and one leaf per (block-local scratch name, step iteration). The leaves are
evaluated by the ordinary assignment evaluator — no scan construct survives the rewrite — and the
complete history tensors are then reassembled with `DenseTensor.ofFn`.

## Why this file may not call the implementations it checks

This is the third leg of F4's differential gate. Legs 1 and 2 (`prepareEvalPlan → runPreparedDense`
and `evalScheduled`) share the source language's front end; this leg reduces the program to a form
with no scan at all, so agreement is evidence rather than tautology. Plan §4.8 therefore forbids the
oracle from calling `runDenseScan`, `evalScan`, `writeRowKinds`, `applyAffine`, the compiler's
residualization helpers, and the scan worker's write helpers (`writeSliceAtMulti` and friends)
during history reconstruction. It may evaluate the mechanically generated scan-free program.

Accordingly this file imports only `Eval.PropertyOracle.Compare` and `Eval.PropertyOracle.ScanGen`
(whose own transitive `LeanNCD.Eval.Entry` provides `evalScheduled`), and the ONLY evaluation entry
point it names is `evalScheduled`, always on a program whose statements are all `ScanStmt.plain`.
Everything else here — geometry resolution, base-region enumeration, index substitution, leaf
routing, and history reassembly — is written out in this file. The predecessor file's
`sliceTensorAtMulti` (whose contract was "the inverse of `LeanNCD.Eval.writeSliceAtMulti`", and
whose round-trip test called that worker helper directly) is gone: reconstruction from per-
coordinate leaves needs no slicing, and dropping it removes the last worker dependency.

## The fragment

The admitted F4 source fragment: rectangular all-axis `+1` step geometry, `iterAt`-pinned (or
whole-axis free) base regions, arbitrary advancing-dimension positions and order, affine history
reads with non-positive bias, external reads, contractions, extent one, multiple scan axes, several
disjoint base writes, block-local scratch, and — for the predicate/mask parity thread (Task 5.4) —
source Iverson predicate factors and axiswise `where`-masks, rewritten to the leaf's own coordinates
by `substBool` (an Iverson takes the actual scan coordinate; a mask zeros seeded scan axes and takes
the current coordinate of free base scan axes). Nonlinearity and aggregation are carried through
unchanged, so the two `enumScanCases`
templates F4 rejects as capability failures (`relu` steps, tropical aggregation) are still unrollable
and still checked against the legacy evaluator. S-B adds positive one-axis affine placement in any
non-advancing state dimension, including multiple distinct affine dimensions and disjoint base
contributions. Everything outside the fragment (`recurMorphism`, non-literal history coordinates,
scatter-shaped scratch, and an axiswise reduction along an ELIMINATED scan coordinate —
`fragment.eliminatedNormalizationAxis`) is rejected with a message rather than silently mis-unrolled.
-/
namespace LeanNCD.PropertyOracle
open LeanNCD LeanNCD.Eval Std

/-! ## Affine index arithmetic -/

/-- An `IdxExpr` as `(bias, [(coefficient, axis)])`, KEEPING each `AxisSpec` — unlike the DSL's
    `idxAffineForm`, which projects to bare `UID`s and therefore cannot rebuild an `IdxExpr` for
    the residual axes. -/
def idxTerms : IdxExpr → Int × List (Int × AxisSpec)
  | .axis a      => (0, [(1, a)])
  | .const n     => (n, [])
  | .scale c a   => (0, [(c, a)])
  | .shift a n   => (n, [(1, a)])
  | .affine n xs => (n, xs)

/-- Combine duplicate UID coefficients in first-seen order and drop canceled terms. -/
private def normalizeIdx (e : IdxExpr) : IdxExpr :=
  let (c0, raw) := idxTerms e
  let axes := raw.foldl (fun acc (_, a) =>
    if acc.any (fun b => b.uid == a.uid) then acc else acc ++ [a]) []
  let terms := axes.filterMap (fun a =>
    let c := raw.foldl (fun total (d, b) => if b.uid == a.uid then total + d else total) (0 : Int)
    if c == 0 then none else some (c, a))
  if terms.isEmpty then .const c0 else .affine c0 terms

/-- Substitute literal values for the axes `σ` names, folding every substituted coefficient into
    the bias and keeping the rest of the expression. A duplicated axis contributes once per
    occurrence (`1 + 2r + 4r` at `r = 1` is `7`, not `3`). -/
def substIdx (σ : UID → Option Int) (e : IdxExpr) : IdxExpr :=
  let (c0, xs) := idxTerms e
  -- NB: `bias` is a reserved token of the TL surface syntax, so this cannot be named `bias`.
  let b := xs.foldl (fun acc (c, a) => match σ a.uid with
    | some v => acc + c * v
    | none   => acc) c0
  let rest := xs.filter (fun (_, a) => (σ a.uid).isNone)
  if rest.isEmpty then .const b else .affine b rest

/-- The literal value of `e` once `σ` is applied; `none` if any axis survives substitution. -/
def constIdx (σ : UID → Option Int) (e : IdxExpr) : Option Int :=
  match substIdx σ e with
  | .const n => some n
  | _        => none

-- TEST-THE-TESTER: substitution arithmetic, including the duplicate-coefficient case plan §4.4
-- pins by hand (`7 + 2·5 + 4·5 = 37` over a residual basis `[v]`).
private def sx : AxisSpec := ⟨"u", 901, .nat⟩
private def sy : AxisSpec := ⟨"v", 902, .nat⟩
private def pinX : UID → Option Int := fun u => if u == sx.uid then some 5 else none
#guard constIdx pinX (.affine 7 [(2, sx), (-3, sy), (4, sx)]) == none
#guard substIdx pinX (.affine 7 [(2, sx), (-3, sy), (4, sx)]) == IdxExpr.affine 37 [(-3, sy)]
#guard constIdx pinX (.affine 1 [(2, sx), (4, sx)]) == some 31
#guard constIdx pinX (.shift sx (-2)) == some 3
#guard constIdx pinX (.scale 2 sx) == some 10
#guard constIdx pinX (.axis sx) == some 5
#guard constIdx pinX (.const 4) == some 4

/-! ## Predicate / mask index substitution

The oracle rewrites a source Iverson factor and a source axiswise mask INDEPENDENTLY of the checked
predicate lowering it cross-checks: it substitutes its own literal coordinates into every `IdxExpr`
leaf of the UID-bearing source `PredArith`/`BoolExpr` with the same `substIdx` used for reads, and
never calls `lowerFactorPredicate`/`lowerMaskPredicate`, the private positional core, or any
`PosBoolExpr`/`evalPosBool` machinery. `substPredArith`/`substBool` are the arithmetic/Boolean lifts
of `substIdx`; a substituted-away axis becomes a literal, an unsubstituted one stays an expression
that the ordinary assignment evaluator resolves against the leaf's own coordinate. -/

/-- Substitute `σ` into every `IdxExpr` leaf of a `PredArith`, folding literals as `substIdx` does. -/
def substPredArith (σ : UID → Option Int) : PredArith → PredArith
  | .embed e => .embed (substIdx σ e)
  | .mul a b => .mul (substPredArith σ a) (substPredArith σ b)
  | .iabs a  => .iabs (substPredArith σ a)

/-- Substitute `σ` into every `IdxExpr` leaf of a `BoolExpr`, preserving the Boolean/`RelOp`
    structure verbatim. -/
def substBool (σ : UID → Option Int) : BoolExpr → BoolExpr
  | .rel op a b => .rel op (substPredArith σ a) (substPredArith σ b)
  | .and a b    => .and (substBool σ a) (substBool σ b)
  | .or a b     => .or (substBool σ a) (substBool σ b)
  | .not a      => .not (substBool σ a)
  | .ieq a b    => .ieq (substPredArith σ a) (substPredArith σ b)

-- TEST-THE-TESTER: an Iverson-style substitution takes the actual scan coordinate; a mask-style one
-- zeros the seed. Over the pin `sx = 5` (from the block above), `[sx = 5]` becomes `[5 = 5]` and
-- `[sx = 0]` over the zeroing map becomes `[0 = 0]`.
private def zeroX : UID → Option Int := fun u => if u == sx.uid then some 0 else none
#guard substBool pinX (.rel .eq (.embed (.axis sx)) (.embed (.const 5)))
  == BoolExpr.rel .eq (.embed (.const 5)) (.embed (.const 5))
#guard substBool zeroX (.rel .eq (.embed (.axis sx)) (.embed (.const 0)))
  == BoolExpr.rel .eq (.embed (.const 0)) (.embed (.const 0))
#guard substBool pinX (.rel .lt (.embed (.axis sy)) (.embed (.axis sx)))
  == BoolExpr.rel .lt (.embed (.affine 0 [(1, sy)])) (.embed (.const 5))

/-- The named fragment rejection for an axiswise operation whose normalization axis is an
    ELIMINATED scan coordinate. The per-coordinate leaf unroller writes one scan-free leaf per
    history coordinate, so it cannot group leaves for a reduction along an axis it has already
    eliminated into leaf coordinates; that shape is pinned directly in Task 5.3, not re-verified by
    an unrolling here, so the oracle refuses it loudly rather than mis-unrolling. -/
def fragment.eliminatedNormalizationAxis : String :=
  "ScanUnroll.fragment.eliminatedNormalizationAxis: an axiswise normalization axis is an eliminated \
scan coordinate — the per-coordinate leaf unroller cannot group those leaves"

/-! ## Coordinate enumeration -/

/-- Every tuple of a list of per-position ranges, lexicographically with position 0 slowest.
    Lexicographic order refines the componentwise order, which is all the emission order below
    needs: a step at `u` reads only coordinates `≤ u` and writes only `u + 1`. -/
def tuplesOf : List (List Nat) → List (List Nat)
  | []      => [[]]
  | r :: rs => r.flatMap (fun i => (tuplesOf rs).map (fun t => i :: t))

/-- Every coordinate of a rectangular extent list. -/
def coordsOf (ext : List Nat) : List (List Nat) := tuplesOf (ext.map List.range)

#guard coordsOf [2, 3] == [[0,0],[0,1],[0,2],[1,0],[1,1],[1,2]]
#guard coordsOf [] == [[]]
#guard coordsOf [0] == []      -- extent one ⇒ `ext - 1 = 0` step iterations

/-! ## Scan geometry -/

/-- One persistent state's geometry, derived from its recurrence RESULT statement's LHS — the only
    statement guaranteed to name every context axis exactly once, and the reason the base list may
    leave a context axis free (§5.1's free-axis boundary face) without confusing the mapping. -/
structure StateGeom where
  name      : String
  rank      : Nat
  /-- `advDim[k]` is the tensor dimension carrying context axis `k`. NOT assumed to be trailing,
      contiguous, or in context order. -/
  advDim    : List Nat
  /-- The remaining tensor dimensions, ascending, and their source placement slots. -/
  slicePos   : List Nat
  sliceSlots : List LHSSlot
  /-- Independently derived destination extents and collision-free axes for the complete state
      slice. Canonical leaves use these axes rather than any source placement axis. -/
  sliceExt   : List Nat
  sliceAxes  : List AxisSpec

/-- One scan node's resolved structure.

    Block-local scratch comes in two shapes, which the rewrite must tell apart:

    * `scratch` — a recurrence-only destination with no iteration slot at all (`ScanCompileTest`'s
      `T`), the form F4's source compiler admits;
    * `advScratch` — a recurrence-only destination whose LHS carries the same all-axis `+1` slots
      the state result does, and which later statements in the SAME step read back at the current
      coordinate. `splitNonlins` used to manufacture exactly this shape for a nonlinear recurrence
      (`%nl…[j, l+1] := …` followed by `S[j, l+1] := relu(%nl…[j, l])`), so it appeared in every
      compiled `enumScanCases` template 2 case. The logical-schedule flip
      (`papers/nonlinearity_split_pair_direct_lowering.md` §2.1) removed `splitNonlins` from
      `compileToScheduled`, so `schedOfCase` no longer produces it — `scratch` and `advScratch` are
      both always empty for every current `enumScanCases` case (`ScanOracle.lean` pins this). The
      classification stays general, for any `ScheduledProgram` a future hand-built or LEGACY-only
      fixture presents in this shape, but nothing in this generator does today. -/
structure ScanGeom where
  axes       : List AxisSpec
  ext        : List Nat
  states     : List StateGeom
  scratch    : List String
  advScratch : List StateGeom
  base       : List Stmt
  recur      : List Stmt

structure StmtParts where
  rhs     : RHSExpr
  scatter : Option ScatterOpts

/-- Preserve whether a source statement is an assignment or a scatter; the latter's placement and
    options survive into the scan-free leaf program. -/
private def partsOf (s : Stmt) : Except String StmtParts :=
  match s with
  | .assign _ _ r         => .ok ⟨r, none⟩
  | .scatter nm _ r opts  =>
      if opts.fill == 0 then .ok ⟨r, some opts⟩
      else .error s!"scatter `{nm}` has nonzero fill, outside the oracle's fragment"
  | .recurMorphism nm _ _ => .error s!"recurMorphism `{nm}` inside a scan is outside the fragment"

/-- Oracle-local copy of §2's extent rule. This deliberately does not call `LHSSlot.outExtent` or
    either checked-plan extent helper: production and oracle must be able to disagree. -/
private def oracleSlotExtent (sizes : HashMap UID Nat) (sl : LHSSlot) : Except String Nat := do
  let e := sl.outIdx
  match e with
  | .const n => return (n + 1).toNat
  | _ =>
      let (c0, raw) := idxTerms e
      for (_, a) in raw do
        unless sizes.contains a.uid do
          .error s!"oracle extent: axis {a.name} (uid {a.uid}) is unsized in {repr sl}"
      let legacy := raw.foldl
        (fun acc (c, a) => acc + c * Int.ofNat ((sizes[a.uid]?).getD 0)) c0
      let axes := raw.foldl (fun acc (_, a) =>
        if acc.any (fun b => b.uid == a.uid) then acc else acc ++ [a]) []
      let coeffs := axes.map (fun a =>
        (raw.foldl (fun acc (c, b) => if b.uid == a.uid then acc + c else acc) (0 : Int), a))
      match coeffs.filter (fun (c, _) => c != 0) with
      | [(c, a)] =>
          let n := (sizes[a.uid]?).getD 0
          if c > 0 && c0 >= 0 && n > 0 then
            return (c * Int.ofNat n + (c0 / c) * c).toNat
          else
            return legacy.toNat
      | _ => return legacy.toNat

/-- Resolve the non-advancing placement of `s` against an already identified state geometry. -/
private def slicePlacement (sizes : HashMap UID Nat) (st : StateGeom) (s : Stmt) :
    Except String (List LHSSlot × List Nat) := do
  if s.slots.length != st.rank then
    .error s!"write for {st.name} has rank {s.slots.length}, expected {st.rank}"
  let slots : List LHSSlot ← st.slicePos.mapM (fun p => match s.slots[p]? with
    | some (LHSSlot.free a)     => pure (LHSSlot.free a)
    | some (LHSSlot.freeNorm a) => pure (LHSSlot.freeNorm a)
    | some (LHSSlot.affine e)   => pure (LHSSlot.affine e)
    | some sl => .error s!"{st.name}: non-advancing dimension {p} has unsupported placement {repr sl}"
    | none    => .error s!"{st.name}: dimension {p} is out of range")
  let ext ← slots.mapM (oracleSlotExtent sizes)
  pure (slots, ext)

/-- Resolve one state's dimension mapping from its recurrence result. -/
private def buildGeom (sizes : HashMap UID Nat) (axes : List AxisSpec) (fresh : UID)
    (result : Stmt) : Except String StateGeom := do
  let nm := result.lhsName
  let slots := result.slots
  let advDim ← axes.mapM (fun a =>
    match slots.zipIdx.filter (fun (sl, _) => match sl with
      | .iterNext b => b.uid == a.uid
      | _           => false) with
    | [(_, p)] => pure p
    | []       => .error s!"{nm}: the recurrence result has no `{a.name}+1` slot, so its write \
geometry is not the admitted rectangular all-axis `+1` form"
    | _        => .error s!"{nm}: context axis {a.name} advances in more than one slot")
  let slicePos := (List.range slots.length).filter (fun p => !advDim.contains p)
  let sliceSlots ← slicePos.mapM (fun p =>
    match slots[p]? with
    | some (LHSSlot.free a) => pure (LHSSlot.free a)
    | some (LHSSlot.freeNorm a) => pure (LHSSlot.freeNorm a)
    | some (LHSSlot.affine e) => pure (LHSSlot.affine e)
    | some sl        => .error s!"{nm}: dimension {p} is neither advancing nor an admitted \
non-advancing placement ({repr sl})"
    | none           => .error s!"{nm}: dimension {p} is out of range")
  let sliceExt ← sliceSlots.mapM (oracleSlotExtent sizes)
  let sliceAxes := slicePos.zipIdx.map (fun (_, k) =>
    ({ name := s!"%slice_{nm}_{k}", uid := fresh + k, kind := .real } : AxisSpec))
  pure { name := nm, rank := slots.length, advDim, slicePos, sliceSlots, sliceExt, sliceAxes }

/-- All source axes named by declarations and statements, including RHS-only contraction axes. -/
private def programAxes (decls : List Decl) (axes : List AxisSpec) (base recur : List Stmt) :
    List AxisSpec :=
  let fromDecls :=
    (Traversable.traverse
      (Decl.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) decls).run
  let fromStmts :=
    (Traversable.traverse
      (Stmt.traverseAxes (f := ConstL (List AxisSpec)) (fun a => ⟨[a]⟩)) (base ++ recur)).run
  axes ++ fromDecls ++ fromStmts

/-- Classify a scan node: extents, persistent states (base destinations, source order), and
    block-local scratch (recurrence destinations with no base statement). Deliberately traverses
    the node's own `base`/`recur` lists rather than `ScanStmt.outputs`, for plan §4.2's reasons. -/
def analyzeScan (sizes : HashMap UID Nat) (decls : List Decl) (sc : ScanStmt) :
    Except String ScanGeom :=
  match sc with
  | .scan _ axes base recur _ => do
      if axes.isEmpty then .error "scan node with no advancing axis"
      let ext ← axes.mapM (fun a =>
        match sizes[a.uid]? with
        | some 0 => .error s!"axis {a.name} has extent zero"
        | some n => pure n
        | none   => .error s!"axis {a.name} has no pinned extent (`explicitSizes`)")
      let stateNames := (base.map Stmt.lhsName).eraseDups
      let stateResults ← stateNames.mapM (fun nm =>
        match recur.filter (fun s => s.lhsName == nm) with
        | [r] => pure r
        | []  => .error s!"state {nm} has a base case but no recurrence result"
        | _   => .error s!"state {nm} has more than one recurrence result")
      let firstFresh := (programAxes decls axes base recur).foldl
        (fun n a => Nat.max n a.uid) (sizes.toList.foldl (fun n p => Nat.max n p.1) 0) + 1
      let states ← stateResults.zipIdx.mapM (fun (r, i) =>
        let offset := (stateResults.take i).foldl (fun n s => n + s.slots.length) 0
        buildGeom sizes axes (firstFresh + offset) r)
      for st in states do
        for s in (base ++ recur).filter (fun s => s.lhsName == st.name) do
          let (_, ext) ← slicePlacement sizes st s
          unless ext == st.sliceExt do
            .error s!"{st.name}: placement implies state-slice shape {ext}, expected {st.sliceExt}"
      let localNames := ((recur.map Stmt.lhsName).eraseDups).filter
        (fun nm => !stateNames.contains nm)
      let locals ← localNames.mapM (fun nm =>
        match recur.filter (fun s => s.lhsName == nm) with
        | [s] =>
            match s with
            | .scatter .. =>
                .error s!"scatter-shaped block-local scratch {nm} is outside the oracle's fragment"
            | _ =>
                if s.slots.any (fun sl => match sl with
                    | .iterAt _ _ | .iterNext _ => true
                    | _ => false) then
                  (buildGeom sizes axes (firstFresh + stateResults.foldl
                    (fun n r => n + r.slots.length) 0) s).map (fun g => (nm, some g))
                else pure (nm, none)
        | _ => .error s!"block-local scratch {nm} has more than one producer")
      pure { axes, ext, states
           , scratch := (locals.filter (fun p => p.2.isNone)).map Prod.fst
           , advScratch := locals.filterMap Prod.snd
           , base, recur }
  | .plain _        => .error "analyzeScan: not a scan node"
  | .scanPre nm _ _ => .error s!"`.scanPre` node {nm} is outside the oracle's fragment"

/-! ## Leaf names

`%`-prefixed so they cannot collide with a source tensor name (the DSL's own internal names use the
same prefix). The history coordinate — not a step index — is part of a state leaf's name, so
multi-axis scans and non-trailing advancing dimensions need no special case. -/

private def tag (t : List Nat) : String := t.foldl (fun s i => s ++ "_" ++ toString i) ""

/-- The leaf holding state `nm`'s value at history coordinate `t`. -/
def stateLeafName (nm : String) (t : List Nat) : String := "%U_" ++ nm ++ tag t
/-- One source statement's private contribution to a base history coordinate. -/
def contributionLeafName (nm : String) (sourceIndex : Nat) (t : List Nat) : String :=
  "%B_" ++ nm ++ "_" ++ toString sourceIndex ++ tag t
/-- Dense pre-placement value of one affine source statement. -/
def denseTempName (phase nm : String) (sourceIndex : Nat) (t : List Nat) : String :=
  "%D_" ++ phase ++ "_" ++ nm ++ "_" ++ toString sourceIndex ++ tag t
/-- The all-zero leaf for state `nm`: the value of every history coordinate no base write and no
    step iteration ever reaches, and the target of every out-of-range state read. -/
def zeroLeafName (nm : String) : String := "%Z_" ++ nm
/-- The leaf holding block-local scratch `nm` produced during step iteration `u`. -/
def scratchLeafName (nm : String) (u : List Nat) : String := "%T_" ++ nm ++ tag u

/-! ## Base regions -/

private def ctxSubst (axes : List AxisSpec) (t : List Nat) : UID → Option Int := fun u =>
  (axes.zipIdx.find? (fun (a, _) => a.uid == u)).map (fun (_, k) => Int.ofNat (t.getD k 0))

/-- The context coordinates one base statement writes. Each context axis is either pinned by an
    `iterAt` literal (one coordinate) or left free (the whole axis, §5.1's boundary face). -/
private def baseRegion (g : ScanGeom) (st : StateGeom) (s : Stmt) :
    Except String (List (List Nat)) := do
  if s.slots.length != st.rank then
    .error s!"base write for {st.name} has rank {s.slots.length}, but the state has rank {st.rank}"
  let ranges ← (g.axes.zipIdx).mapM (fun (a, k) => do
    let p := st.advDim.getD k 0
    let e := g.ext.getD k 0
    match s.slots[p]? with
    | some (.iterAt b n) =>
        if b.uid != a.uid then
          .error s!"base write for {st.name}: dimension {p} pins {b.name}, expected {a.name}"
        else if n < 0 || n ≥ Int.ofNat e then
          .error s!"base write for {st.name}: `{a.name}` pinned to {n}, outside `[0, {e})`"
        else pure [n.toNat]
    | some (.free b) =>
        if b.uid != a.uid then
          .error s!"base write for {st.name}: dimension {p} is free over {b.name}, expected {a.name}"
        else pure (List.range e)
    | some sl =>
        .error s!"base write for {st.name}: dimension {p} is {repr sl}, not a pin or a free face"
    | none => .error s!"base write for {st.name}: dimension {p} is out of range")
  pure (tuplesOf ranges)

/-- First-seen normalized nonzero source-axis basis of a residual placement, independently of
    `scanScatterSourceAxes`. Syntactically mentioned axes whose coefficients cancel remain visible to
    the oracle's separate extent calculation, but not to dense computation. -/
private def placementAxes (slots : List LHSSlot) : List AxisSpec :=
  slots.flatMap (fun sl => (idxTerms (normalizeIdx sl.outIdx)).2.map Prod.snd)
  |>.foldl (fun acc a => if acc.any (fun b => b.uid == a.uid) then acc else acc ++ [a]) []

/-- Evaluate an affine expression without using a production placement helper. -/
private def oracleEvalIdx (coord : HashMap UID Int) (e : IdxExpr) : Int :=
  let (c0, xs) := idxTerms e
  xs.foldl (fun acc (c, a) => acc + c * (coord[a.uid]?).getD 0) c0

/-- Residual non-context placement of one source statement. -/
private def residualPlacement (st : StateGeom) (s : Stmt) (σ : UID → Option Int) :
    Except String (List LHSSlot) :=
  st.slicePos.mapM (fun p => show Except String LHSSlot from match s.slots[p]? with
    | some (LHSSlot.free a)     => pure (LHSSlot.free a)
    | some (LHSSlot.freeNorm a) => pure (LHSSlot.freeNorm a)
    | some (LHSSlot.affine e)   => pure (LHSSlot.affine (normalizeIdx (substIdx σ e)))
    | some sl => .error s!"{st.name}: unsupported residual placement {repr sl} at dimension {p}"
    | none    => .error s!"{st.name}: residual placement dimension {p} is missing")

/-- Independently enumerate a contribution's destination coordinates and reject malformed maps. -/
private def contributionDestinations (sizes : HashMap UID Nat) (st : StateGeom)
    (slots : List LHSSlot) : Except String (List (List Nat)) := do
  let axes := placementAxes slots
  let ext ← axes.mapM (fun a => match sizes[a.uid]? with
    | some n => pure n
    | none   => .error s!"{st.name}: placement source axis {a.name} is unsized")
  let coords := (coordsOf ext).map (fun src =>
    let m := (axes.zip src).foldl
      (fun acc (a, v) => acc.insert a.uid (Int.ofNat v)) ({} : HashMap UID Int)
    slots.map (fun sl => oracleEvalIdx m sl.outIdx))
  for dst in coords do
    unless dst.length == st.sliceExt.length &&
        (dst.zip st.sliceExt).all (fun (v, n) => 0 ≤ v && v < Int.ofNat n) do
      .error s!"{st.name}: contribution destination {dst} is outside state slice {st.sliceExt}"
  let natural := coords.map (·.map Int.toNat)
  unless natural.eraseDups.length == natural.length do
    .error s!"{st.name}: one contribution writes the same destination more than once"
  pure natural

/-- Rename retained source axes to a state's synthetic slice axes. -/
private def leafAxisRename (st : StateGeom) (s : Stmt) : Except String (UID → Option AxisSpec) := do
  let pairs ← (st.slicePos.zip st.sliceAxes).mapM (fun (p, synthetic) =>
    match s.slots[p]? with
    | some (.free a) | some (.freeNorm a) => pure (a.uid, synthetic)
    | some sl => .error s!"{st.name}: ordinary assignment has non-free placement {repr sl}"
    | none    => .error s!"{st.name}: ordinary assignment dimension {p} is missing")
  pure (fun u => (pairs.find? (fun p => p.1 == u)).map Prod.snd)

private def renameIdx (ρ : UID → Option AxisSpec) : IdxExpr → IdxExpr
  | .axis a      => .axis ((ρ a.uid).getD a)
  | .const n     => .const n
  | .scale c a   => .scale c ((ρ a.uid).getD a)
  | .shift a n   => .shift ((ρ a.uid).getD a) n
  | .affine n xs => .affine n (xs.map (fun (c, a) => (c, (ρ a.uid).getD a)))

private def renamePredArith (ρ : UID → Option AxisSpec) : PredArith → PredArith
  | .embed e => .embed (renameIdx ρ e)
  | .mul a b => .mul (renamePredArith ρ a) (renamePredArith ρ b)
  | .iabs a  => .iabs (renamePredArith ρ a)

private def renameBool (ρ : UID → Option AxisSpec) : BoolExpr → BoolExpr
  | .rel op a b => .rel op (renamePredArith ρ a) (renamePredArith ρ b)
  | .and a b    => .and (renameBool ρ a) (renameBool ρ b)
  | .or a b     => .or (renameBool ρ a) (renameBool ρ b)
  | .not a      => .not (renameBool ρ a)
  | .ieq a b    => .ieq (renamePredArith ρ a) (renamePredArith ρ b)

private def renameRHS (ρ : UID → Option AxisSpec) (r : RHSExpr) : RHSExpr :=
  let terms := r.body.terms.map (fun t => { t with factors := t.factors.map (fun
    | .read nm es       => .read nm (es.map (renameIdx ρ))
    | .unaryFn op nm es => .unaryFn op nm (es.map (renameIdx ρ))
    | .iverson b        => .iverson (renameBool ρ b)) })
  let nonlin := match r.nonlin with
    | .axiswise fn mask => .axiswise fn (mask.map (renameBool ρ))
    | other => other
  { r with body := { terms }, nonlin }

private def ordinaryLeafSlots (st : StateGeom) (s : Stmt) : Except String (List LHSSlot) :=
  (st.slicePos.zip st.sliceAxes).mapM (fun (p, synthetic) => match s.slots[p]? with
    | some (.free _)     => pure (.free synthetic)
    | some (.freeNorm _) => pure (.freeNorm synthetic)
    | some sl => .error s!"{st.name}: ordinary assignment has non-free placement {repr sl}"
    | none    => .error s!"{st.name}: ordinary assignment dimension {p} is missing")

/-! ## The rewrite -/

/-- Where a read resolves to inside the unrolled program.

    * a persistent state → the leaf at the read's (literal) history coordinate, or the state's zero
      leaf when that coordinate is out of range or was never written;
    * block-local scratch → this step iteration's own scratch leaf (so a same-step producer is
      visible to later statements and a previous iteration's value never is);
    * anything else → itself, with every context axis replaced by its literal.

    `stepCoord` is `none` inside a base block, where a state or scratch read is a source error the
    production compiler rejects. -/
private def rewriteRead (g : ScanGeom) (σ : UID → Option Int)
    (hasLeaf : String → List Nat → Bool) (stepCoord : Option (List Nat))
    (nm : String) (idxs : List IdxExpr) : Except String (String × List IdxExpr) := do
  match g.states.find? (fun st => st.name == nm) with
  | some st =>
      if stepCoord.isNone then
        .error s!"a base block reads persistent state {nm} — outside the admitted fragment"
      else if idxs.length != st.rank then
        .error s!"read of state {nm} has {idxs.length} indices, but the state has rank {st.rank}"
      else do
        let hist ← st.advDim.mapM (fun p =>
          match (idxs[p]?).bind (constIdx σ) with
          | some v => pure v
          | none   => .error s!"read of state {nm} at dimension {p} does not reduce to a literal \
history coordinate — outside the admitted affine fragment")
        let frees := st.slicePos.filterMap (fun p => (idxs[p]?).map (substIdx σ))
        let inRange := (hist.zip g.ext).all (fun (v, e) => 0 ≤ v && v < Int.ofNat e)
        if inRange && hasLeaf nm (hist.map Int.toNat) then
          pure (stateLeafName nm (hist.map Int.toNat), frees)
        else
          pure (zeroLeafName nm, frees)
  | none =>
      if g.scratch.contains nm then
        match stepCoord with
        | none   => .error s!"a base block reads block-local scratch {nm}"
        | some u => pure (scratchLeafName nm u, idxs.map (substIdx σ))
      else match g.advScratch.find? (fun st => st.name == nm) with
      | some st =>
          match stepCoord with
          | none   => .error s!"a base block reads block-local scratch {nm}"
          | some u =>
              if idxs.length != st.rank then
                .error s!"read of scratch {nm} has {idxs.length} indices, expected {st.rank}"
              else do
                let hist ← st.advDim.mapM (fun p =>
                  match (idxs[p]?).bind (constIdx σ) with
                  | some v => pure v
                  | none   => .error s!"read of scratch {nm} at dimension {p} does not reduce to a \
literal coordinate")
                unless hist == u.map Int.ofNat do
                  .error s!"read of block-local scratch {nm} at {hist} during step {u}: scratch \
does not persist across iterations, so only the current step's value is defined"
                pure (scratchLeafName nm u, st.slicePos.filterMap (fun p =>
                  (idxs[p]?).map (substIdx σ)))
      | none => pure (nm, idxs.map (substIdx σ))

private def rewriteFactor (g : ScanGeom) (σ : UID → Option Int)
    (hasLeaf : String → List Nat → Bool) (stepCoord : Option (List Nat)) :
    Factor → Except String Factor
  | .read nm idxs => do
      let (nm', idxs') ← rewriteRead g σ hasLeaf stepCoord nm idxs
      pure (.read nm' idxs')
  | .unaryFn op nm idxs => do
      let (nm', idxs') ← rewriteRead g σ hasLeaf stepCoord nm idxs
      pure (.unaryFn op nm' idxs')
  | .iverson b =>
      -- A predicate factor takes the ACTUAL scan coordinate: `σ` maps every eliminated scan axis to
      -- its literal step/base coordinate and leaves every retained output axis as an expression, so
      -- `substBool σ b` is the residual predicate the ordinary evaluator resolves against the leaf.
      pure (.iverson (substBool σ b))

/-- The mask substitution induced by a source statement's LHS. Seeded scan axes are absent from the
    local output basis and therefore read as zero; a scan axis left free by a base statement is
    evaluated at the current base coordinate represented by `σ`. -/
private def maskSubst (g : ScanGeom) (σ : UID → Option Int) (sourceSlots : List LHSSlot) :
    UID → Option Int := fun u =>
  if g.axes.any (·.uid == u) then
    if sourceSlots.any (fun
        | .free a | .freeNorm a => a.uid == u
        | _ => false) then σ u
    else some 0
  else none

/-- Rewrite one statement's nonlinearity for the leaf program. `identity`/`pointwise` pass through.
    An `.axiswise` operation whose marked normalization axis (`.freeNorm` among `sourceSlots`) is an
    eliminated scan coordinate is REJECTED with the named fragment
    error — the per-coordinate leaf unroller cannot reduce along an axis it has eliminated. Its mask
    (when present) is rewritten with the MASK policy, DISTINCT from the Iverson-factor policy: every
    seeded scan axis reads ZERO, while a free base scan axis takes its enumerated base coordinate;
    every retained non-scan output axis stays an expression resolved against the leaf's coordinate. -/
private def rewriteNonlin (g : ScanGeom) (σ : UID → Option Int) (sourceSlots : List LHSSlot) :
    Nonlin → Except String Nonlin
  | .axiswise fn m => do
      match sourceSlots.findSome? (fun sl => match sl with | .freeNorm a => some a | _ => none) with
      | some a =>
          if g.axes.any (·.uid == a.uid) then .error fragment.eliminatedNormalizationAxis
      | none => pure ()
      pure (.axiswise fn (m.map (substBool (maskSubst g σ sourceSlots))))
  | other => pure other

private def maskTestGeom : ScanGeom :=
  { axes := [sx], ext := [6], states := [], scratch := [], advScratch := [], base := [], recur := [] }

private def scanAxisMask : BoolExpr :=
  .rel .eq (.embed (.axis sx)) (.embed (.const 5))

-- A free base scan axis remains an output coordinate before leaf specialization, whereas a seeded
-- scan axis is absent from the output basis and therefore reads as zero.
#guard substBool (maskSubst maskTestGeom pinX [.free sx, .freeNorm sy]) scanAxisMask
  == BoolExpr.rel .eq (.embed (.const 5)) (.embed (.const 5))
#guard substBool (maskSubst maskTestGeom pinX [.iterAt sx 0, .freeNorm sy]) scanAxisMask
  == BoolExpr.rel .eq (.embed (.const 0)) (.embed (.const 5))

/-- Rewrite a whole RHS, preserving source term and factor order, and rewriting the nonlinearity
    (`rewriteNonlin`) — the mask must be lowered to the leaf's coordinates and an eliminated-axis
    reduction rejected — so a step's `relu` or masked contraction is applied to the leaf exactly as
    the source applies it to the slice. -/
private def rewriteRHS (g : ScanGeom) (σ : UID → Option Int)
    (hasLeaf : String → List Nat → Bool) (stepCoord : Option (List Nat))
    (outSlots : List LHSSlot) (r : RHSExpr) :
    Except String RHSExpr := do
  let terms ← r.body.terms.mapM (fun t => do
    let fs ← t.factors.mapM (rewriteFactor g σ hasLeaf stepCoord)
    pure ({ factors := fs } : ProdTerm))
  let nonlin ← rewriteNonlin g σ outSlots r.nonlin
  pure { r with body := { terms }, nonlin }

/-- One unrolled scan node. -/
structure Unrolled where
  geom  : ScanGeom
  /-- The scan-free leaf program, in dependency-safe emission order. -/
  stmts : List Stmt
  /-- Per state, the history coordinates that carry a real leaf (everything else is zero). -/
  live  : List (String × List (List Nat))
  /-- Synthetic state-slice axis sizes to add only while evaluating this private leaf program. -/
  sizes : List (UID × Nat)
  axisDecls : List Decl
  /-- Every contribution/canonical leaf whose runtime shape must equal the independent geometry. -/
  checks : List (String × List Nat)
  /-- Generated `.predicate` declarations for every leaf whose ORIGINAL source name (a state or
      block-local scratch) is itself `.predicate`-declared in the caller's `decls` (Task 4.4). The
      leaf names (`%Z_…`, `%U_…_*`, `%T_…_*`) never appear in the source program's own `decls`, so
      without this the leaf-name lookup `combineFor`/`dtypeOfDecl` performs against `decls` always
      misses and a Boolean scan state's independent unrolling would silently run real sum-product
      instead of Boolean disjunction/conjunction — the gap the plan's §1 (`predicate_boolean_
      backend_parity.md` supersession note) names as one of the three requirements this whole plan
      closes. `independentRun` merges this list into the schedule it hands to `evalScheduled`. -/
  decls : List Decl

/-- Whether `nm` (an ORIGINAL source name — a state, a scratch, or any statement's LHS) is declared
    `.predicate` in `decls`. Mirrors `Contract.lean`'s `combineFor`: `.axis`/`.iter` declarations
    name an axis, not a tensor, and must be excluded before matching by name, or an axis sharing a
    tensor's name could hide its real declaration. -/
private def isPredicateName (decls : List Decl) (nm : String) : Bool :=
  match decls.find? (fun d => match d with | .axis _ _ | .iter _ _ => false | _ => d.name == nm) with
  | some (.predicate _ _) => true
  | _ => false

/-- Declare a generated predicate leaf over exactly the axes retained by its assignment. -/
private def predicateLeafDecl (decls : List Decl) (sourceName : String)
    (fallbackAxes : List AxisSpec) (leaf : Stmt) : Option Decl :=
  if isPredicateName decls sourceName then
    match leaf with
    | .assign leafName slots _ => some (.predicate leafName (slots.filterMap (·.axisSpec?)))
    | .scatter leafName _ _ _ => some (.predicate leafName fallbackAxes)
    | .recurMorphism .. => none
  else none

structure LeafEmission where
  stmts  : List Stmt
  decls  : List Decl
  checks : List (String × List Nat)

/-- Emit one state-slice leaf. Affine sources become an assignment over their LHS source basis
    followed immediately by a scatter; ordinary sources remain one assignment. -/
private def emitStateLeaf (decls : List Decl) (g : ScanGeom)
    (st : StateGeom) (source : Stmt) (sourceIndex : Nat) (phase : String)
    (hist : List Nat) (leafName : String) (σ : UID → Option Int)
    (hasLeaf : String → List Nat → Bool) (stepCoord : Option (List Nat)) :
    Except String LeafEmission := do
  let parts ← partsOf source
  match parts.scatter with
  | none =>
      let slots ← ordinaryLeafSlots st source
      let rename ← leafAxisRename st source
      let rhs ← rewriteRHS g σ hasLeaf stepCoord source.slots parts.rhs
      let leaf := Stmt.assign leafName slots (renameRHS rename rhs)
      pure { stmts := [leaf]
           , decls := (predicateLeafDecl decls source.lhsName st.sliceAxes leaf).toList
           , checks := [(leafName, st.sliceExt)] }
  | some opts =>
      let slots ← residualPlacement st source σ
      let sourceAxes := placementAxes slots
      let rhs ← rewriteRHS g σ hasLeaf stepCoord source.slots parts.rhs
      let tempName := denseTempName phase st.name sourceIndex hist
      let temp := Stmt.assign tempName (sourceAxes.map LHSSlot.free) rhs
      let placedRhs : RHSExpr :=
        { body := { terms := [{ factors := [.read tempName (sourceAxes.map IdxExpr.axis)] }] }
        , nonlin := .identity }
      let leaf := Stmt.scatter leafName slots placedRhs opts
      pure { stmts := [temp, leaf]
           , decls :=
               (predicateLeafDecl decls source.lhsName sourceAxes temp).toList ++
               (predicateLeafDecl decls source.lhsName st.sliceAxes leaf).toList
           , checks := [(leafName, st.sliceExt)] }

structure BaseInstance where
  state       : StateGeom
  source      : Stmt
  sourceIndex : Nat
  hist        : List Nat
  destinations : List (List Nat)

structure MergePart where
  sourceName : String
  stmt       : Stmt
  axes       : List AxisSpec
  expected   : List Nat

/-- Unroll one scan node into scan-free leaf statements.

    Emission order is: every state's zero leaf, every base contribution in source order, the
    contribution-to-canonical merges, then step iterations in lexicographic order. A step at `u`
    reads only coordinates `≤ u` and writes only `u + 1`, so this order both satisfies every read
    and gives the checked worker's immutable-pre-step (Jacobi) snapshot for free: no read inside
    iteration `u` can name a leaf that iteration `u` writes. -/
def unrollScanNode (sizes : HashMap UID Nat) (decls : List Decl) (sc : ScanStmt) :
    Except String Unrolled := do
  let g ← analyzeScan sizes decls sc
  -- 1. resolve and independently enumerate every base contribution.
  let baseParts ← g.base.zipIdx.mapM (fun (s, sourceIndex) => do
    let st ← match g.states.find? (fun st => st.name == s.lhsName) with
      | some st => pure st
      | none    => .error s!"base statement writes {s.lhsName}, which is not a persistent state"
    let reg ← baseRegion g st s
    let _ ← partsOf s
    pure (st, s, sourceIndex, reg))
  let baseInstances ← baseParts.flatMapM (fun (st, source, sourceIndex, reg) =>
    reg.mapM (fun hist => do
      let slots ← residualPlacement st source (ctxSubst g.axes hist)
      let destinations ← contributionDestinations sizes st slots
      pure ({ state := st, source, sourceIndex, hist, destinations } : BaseInstance)))
  for (a, i) in baseInstances.zipIdx do
    for b in baseInstances.drop (i + 1) do
      if a.state.name == b.state.name && a.hist == b.hist &&
          a.destinations.any (fun dst => b.destinations.contains dst) then
        .error s!"{a.state.name}: base contributions {a.sourceIndex} and {b.sourceIndex} overlap \
at history coordinate {a.hist}"
  -- 2. which history coordinates carry a real leaf: a base region, or a step's `u + 1`.
  let stepCoords := coordsOf (g.ext.map (fun n => n - 1))
  let advanced := stepCoords.map (fun u => u.map (· + 1))
  let live : List (String × List (List Nat)) := g.states.map (fun st =>
    let fromBase := baseInstances.filterMap (fun b =>
      if b.state.name == st.name then some b.hist else none)
    (st.name, (fromBase ++ advanced).eraseDups))
  let hasLeaf : String → List Nat → Bool := fun nm t =>
    match live.find? (fun p => p.1 == nm) with
    | some (_, ts) => ts.contains t
    | none         => false
  -- 3. zero leaves.
  let zeroParts : List (String × Stmt) := g.states.map (fun st =>
    (st.name, .assign (zeroLeafName st.name) (st.sliceAxes.map LHSSlot.free)
      { body := { terms := [] }, nonlin := .identity }))
  let zeroStmts := zeroParts.map Prod.snd
  let zeroDecls := zeroParts.filterMap (fun (sourceName, leaf) =>
    let axes := (g.states.find? (fun st => st.name == sourceName)).map (·.sliceAxes) |>.getD []
    predicateLeafDecl decls sourceName axes leaf)
  -- 4. base contribution leaves, preserving source order and assignment-then-scatter adjacency.
  let baseEmissions ← baseInstances.mapM (fun b =>
    emitStateLeaf decls g b.state b.source b.sourceIndex "B" b.hist
      (contributionLeafName b.state.name b.sourceIndex b.hist)
      (ctxSubst g.axes b.hist) hasLeaf none)
  let baseStmts := baseEmissions.flatMap (·.stmts)
  let baseDecls := baseEmissions.flatMap (·.decls)
  let baseChecks := baseEmissions.flatMap (·.checks)
  -- 5. merge every base coordinate's disjoint zero-filled contributions into its canonical leaf.
  let mergeParts := g.states.flatMap (fun st =>
    let hist := baseInstances.filterMap (fun b =>
      if b.state.name == st.name then some b.hist else none) |>.eraseDups
    hist.map (fun t =>
      let names := baseInstances.filterMap (fun b =>
        if b.state.name == st.name && b.hist == t then
          some (contributionLeafName st.name b.sourceIndex t)
        else none)
      let rhs : RHSExpr :=
        { body := { terms := names.map (fun nm =>
            { factors := [.read nm (st.sliceAxes.map IdxExpr.axis)] }) }
        , nonlin := .identity }
      ({ sourceName := st.name
       , stmt := Stmt.assign (stateLeafName st.name t) (st.sliceAxes.map LHSSlot.free) rhs
       , axes := st.sliceAxes, expected := st.sliceExt } : MergePart)))
  let mergeStmts := mergeParts.map (·.stmt)
  let mergeDecls := mergeParts.filterMap (fun p =>
    predicateLeafDecl decls p.sourceName p.axes p.stmt)
  let mergeChecks := mergeParts.map (fun p => (p.stmt.lhsName, p.expected))
  -- 6. step leaves: the whole recurrence list, once per step iteration, in source order.
  let stepParts ← stepCoords.flatMapM (fun u => do
    let σ := ctxSubst g.axes u
    g.recur.zipIdx.mapM (fun (s, sourceIndex) => do
      match g.states.find? (fun st => st.name == s.lhsName) with
      | some st =>
          emitStateLeaf decls g st s sourceIndex "R" u
            (stateLeafName st.name (u.map (· + 1))) σ hasLeaf (some u)
      | none =>
          match g.advScratch.find? (fun st => st.name == s.lhsName) with
          | some st =>
              emitStateLeaf decls g st s sourceIndex "R" u
                (scratchLeafName s.lhsName u) σ hasLeaf (some u)
          | none =>
              let parts ← partsOf s
              let rhs ← rewriteRHS g σ hasLeaf (some u) s.slots parts.rhs
              let leaf := Stmt.assign (scratchLeafName s.lhsName u) s.slots rhs
              pure { stmts := [leaf]
                   , decls := (predicateLeafDecl decls s.lhsName [] leaf).toList
                   , checks := [] }))
  let stepStmts := stepParts.flatMap (·.stmts)
  let stepDecls := stepParts.flatMap (·.decls)
  let stepChecks := stepParts.flatMap (·.checks)
  let syntheticSizes := g.states.flatMap (fun st => (st.sliceAxes.zip st.sliceExt).map
    (fun (a, n) => (a.uid, n)))
  let syntheticDecls := g.states.flatMap (fun st => (st.sliceAxes.zip st.sliceExt).map
    (fun (a, n) => Decl.axis a (some n)))
  pure { geom := g
       , stmts := zeroStmts ++ baseStmts ++ mergeStmts ++ stepStmts
       , live, sizes := syntheticSizes, axisDecls := syntheticDecls
       , checks := baseChecks ++ mergeChecks ++ stepChecks
       , decls := zeroDecls ++ baseDecls ++ mergeDecls ++ stepDecls }

/-! ## History reconstruction -/

/-- Reassemble one state's complete history from its per-coordinate leaves with
    `DenseTensor.ofFn`. Each output coordinate is split into its advancing part (which selects the
    leaf) and its free part (which indexes into it) using the state's OWN dimension mapping, so
    nothing here assumes the advancing dimensions trail, are contiguous, or follow context order —
    and no scan-worker write helper is involved. -/
def reconstructHistory (un : Unrolled) (st : StateGeom) (leafEnv : HashMap String DenseTensor) :
    Except String DenseTensor := do
  let g := un.geom
  let zt ← match leafEnv[zeroLeafName st.name]? with
    | some t => pure t
    | none   => .error s!"the zero leaf for {st.name} is missing from the unrolled run"
  if zt.shape != st.sliceExt then
    .error s!"{st.name}: the zero leaf has shape {zt.shape}, expected {st.sliceExt}"
  -- every coordinate a base write or a step must have produced has to be present, so a lost or
  -- misplaced leaf fails loudly instead of silently reading as the zero default.
  let liveCoords := match un.live.find? (fun p => p.1 == st.name) with
    | some (_, ts) => ts
    | none         => []
  for t in liveCoords do
    unless leafEnv.contains (stateLeafName st.name t) do
      .error s!"{st.name}: leaf for history coordinate {t} was never produced by the unrolled program"
  let advAt  : List (Nat × Nat) := st.advDim.zipIdx.map (fun (p, k) => (p, g.ext.getD k 0))
  let freeAt : List (Nat × Nat) := st.slicePos.zipIdx.map (fun (p, i) => (p, st.sliceExt.getD i 0))
  let dims := (List.range st.rank).map (fun p =>
    match (advAt ++ freeAt).find? (fun (q, _) => q == p) with
    | some (_, d) => d
    | none        => 0)
  pure (DenseTensor.ofFn dims (fun coord =>
    let hist := st.advDim.map (fun p => coord.getD p 0)
    let free := st.slicePos.map (fun p => coord.getD p 0)
    match leafEnv[stateLeafName st.name hist]? with
    | some t => t.get! free
    | none   => zt.get! free))

/-! ## Running a whole schedule independently -/

/-- Evaluate a `ScheduledProgram` with every scan replaced by its mechanical unrolling.

    Statements are processed in schedule order, so a plain statement downstream of a scan sees the
    reconstructed history exactly as the compiled and legacy paths see the published one. Leaf names
    stay inside the per-scan sub-evaluation and never enter the returned environment. The only
    evaluator entry point used is `evalScheduled`, always on an all-`.plain` program. -/
def independentRun (sched : ScheduledProgram) (inputs : HashMap String DenseTensor) :
    Except String (HashMap String DenseTensor) := do
  let mut env := inputs
  for sc in sched.stmts do
    match sc with
    | .plain s =>
        match evalScheduled { sched with stmts := [.plain s] } env with
        | .ok r    => env := r.env
        | .error e => .error s!"independent run: plain statement `{s.lhsName}` failed: {e.error}"
    | .scan _ _ base recur _ => do
        let sizeStmts := (base ++ recur).map (fun
          | .scatter nm slots rhs _ => Stmt.assign nm slots rhs
          | s => s)
        let sizes ← match inferAxisSizes (declaredAxisSizes sched.decls) env
            sizeStmts with
          | .ok (sizes, _) => pure sizes
          | .error e => .error s!"independent run: scan size inference failed: {e.error}"
        let un ← unrollScanNode sizes sched.decls sc
        -- Task 4.4: the leaf program's OWN decls are `sched.decls` (needed by a `.plain` statement
        -- reading an unrelated declared name) PLUS the generated predicate decls for THIS scan's
        -- leaves (`un.decls`) — the leaf names never collide with any source name (`%`-prefixed),
        -- so appending is safe and there is nothing to deduplicate.
        let leafSizes := un.sizes.foldl (fun m (u, n) => m.insert u n) sizes
        let leafEnv ←
            match evalScheduled { sched with stmts := un.stmts.map ScanStmt.plain
                                            , decls := sched.decls ++ un.axisDecls ++ un.decls
                                            , explicitSizes := leafSizes } env with
          | .ok r    => pure r.env
          | .error e => .error s!"independent run: the unrolled scan-free program failed: {e.error}"
        for (nm, expected) in un.checks do
          match leafEnv[nm]? with
          | none => .error s!"independent run: checked leaf {nm} is missing"
          | some t =>
              unless t.shape == expected do
                .error s!"independent run: leaf {nm} has shape {t.shape}, expected {expected}"
        for st in un.geom.states do
          let h ← reconstructHistory un st leafEnv
          env := env.insert st.name h
    | .scanPre nm _ _ => .error s!"independent run: `.scanPre` node {nm} is outside the fragment"
  pure env

/-- The persistent-state names a schedule's scans publish, in scan-then-base order. -/
def scannedStateNames (sched : ScheduledProgram) : List String :=
  sched.stmts.flatMap (fun
    | .scan _ _ base _ _ => (base.map Stmt.lhsName).eraseDups
    | _                  => [])

/-- Compile a generated `ScanCase` to the scheduled form both the legacy evaluator and this oracle
    consume. (`assignUIDs` relabels every axis, so the case's own `axes` field must never be used
    against the compiled program.) -/
def schedOfCase (c : ScanCase) : Except String ScheduledProgram :=
  match c.prog.compileToScheduled.run 0 with
  | .ok s _    => .ok s
  | .error e _ => .error s!"the generator produced a program that fails to compile: {repr e}"

/-! ## TEST-THE-TESTER

Point checks with hand-derived values, so the unroller is known to be right on its own before any
differential trusts it. -/

private def unrollCaseStates (c : ScanCase) : Except String (HashMap String DenseTensor) := do
  let sched ← schedOfCase c
  independentRun sched c.inputs

-- Template 1 (linear self-scan), the same recurrence `ScanTest.lean`'s `linearScan` encodes:
-- `X = [1,2]`, `A = [2,3]`, `L = 3` ⇒ `S[:,0] = [1,2]`, `S[:,1] = [2,6]`, `S[:,2] = [4,18]`.
-- The advancing axis is dimension 1 here, so this also pins that reconstruction indexes the
-- history by the state's own dimension mapping.
run_cmd do
  match unrollCaseStates (template1 3 false) with
  | .error m => throwError s!"template1 unroll failed: {m}"
  | .ok env => match env["S"]? with
    | some s =>
        unless denseEq s ⟨[2, 3], #[1.0, 2.0, 4.0, 2.0, 6.0, 18.0]⟩ do
          throwError s!"template1 history wrong: {repr s.shape}/{repr s.data}"
    | none => throwError "template1: no S in the independent environment"

-- Template 6 (2-D grid DP), hand-verified against RC6 (`RecurrenceTest.lean`): the `c = 0` column
-- is the base face, `G[1,1] = G[0,0] + A[0,0] = 1`, and `G[0,1]` is reached by neither the base nor
-- any step, so it must come back as the zero leaf.
run_cmd do
  match unrollCaseStates template6 with
  | .error m => throwError s!"template6 unroll failed: {m}"
  | .ok env => match env["G"]? with
    | some g =>
        unless denseEq g ⟨[2, 2], #[0.0, 0.0, 0.0, 1.0]⟩ do
          throwError s!"template6 history wrong: {repr g.shape}/{repr g.data}"
    | none => throwError "template6: no G in the independent environment"

-- Template 3 (coupled states) — `C = 1`; `G[0] = H[0] = 1`; `G[l+1] = G[l] + H[l]`,
-- `H[l+1] = G[l]`. Fibonacci: G = [1,2,3], H = [1,1,2]. Both states must be reconstructed from
-- the SAME step iteration's pre-step snapshot (`H[2] = G[1] = 2`, not the just-written `G[2]`).
run_cmd do
  match unrollCaseStates (template3 3) with
  | .error m => throwError s!"template3 unroll failed: {m}"
  | .ok env => match env["G"]?, env["H"]? with
    | some g, some h =>
        unless denseEq g ⟨[3], #[1.0, 2.0, 3.0]⟩ do
          throwError s!"template3 G wrong: {repr g.data}"
        unless denseEq h ⟨[3], #[1.0, 1.0, 2.0]⟩ do
          throwError s!"template3 H wrong: {repr h.data}"
    | _, _ => throwError "template3: G/H missing from the independent environment"

-- The unrolled program really is scan-free and really does name per-coordinate leaves.
run_cmd do
  match schedOfCase (template1 3 false) with
  | .error m => throwError m
  | .ok sched =>
      match sched.stmts.find? (fun s => match s with | .scan .. => true | _ => false) with
      | none => throwError "template1 did not compile to a scan node"
      | some sc => match unrollScanNode sched.explicitSizes sched.decls sc with
        | .error m => throwError s!"unrollScanNode failed: {m}"
        | .ok un =>
            let names := un.stmts.map Stmt.lhsName
            unless names == ["%Z_S", "%B_S_0_0", "%U_S_0", "%U_S_1", "%U_S_2"] do
              throwError s!"unexpected leaf statements: {names}"
            unless un.stmts.all (fun s => match s with | .assign .. => true | _ => false) do
              throwError "the unrolled program is not made of plain assignments"

/- Task 4.4, fixture 8: the same leaf-name assertion above, cloned onto `template4Bool` (Task 4.4
   fixture 1's `predicate S(l)` case) instead of `template1` — its ONE state `S` has no free axis,
   so its leaves are `%Z_S`/`%B_S_0_0`/`%U_S_0`/`%U_S_1`/`%U_S_2` (for `L = 3`). Every generated
   declaration for them must be `.predicate`, since `S` itself is: without it (temporarily
   verified by dropping the decl-generation entirely, see the mutation cycle for this site) the
   independent leg's leaf assignments have no declaration at all, `combineFor` defaults to
   `Combine.real`, and the leaf history disagrees with the checked/legacy legs (a real running sum
   instead of Boolean disjunction) — a THREE-WAY differential failure the registration below (in
   `DifferentialTest.lean`) is what actually observes. -/
run_cmd do
  match schedOfCase (template4Bool 3) with
  | .error m => throwError m
  | .ok sched =>
      match sched.stmts.find? (fun s => match s with | .scan .. => true | _ => false) with
      | none => throwError "template4Bool did not compile to a scan node"
      | some sc => match unrollScanNode sched.explicitSizes sched.decls sc with
        | .error m => throwError s!"unrollScanNode (template4Bool) failed: {m}"
        | .ok un =>
            let names := un.stmts.map Stmt.lhsName
            unless names == ["%Z_S", "%B_S_0_0", "%U_S_0", "%U_S_1", "%U_S_2"] do
              throwError s!"template4Bool: unexpected leaf statements: {names}"
            let declNames := un.decls.map Decl.name
            unless declNames == ["%Z_S", "%B_S_0_0", "%U_S_0", "%U_S_1", "%U_S_2"] do
              throwError s!"template4Bool: unexpected generated decls: {declNames}"
            unless un.decls.all (fun d => match d with | .predicate _ _ => true | _ => false) do
              throwError s!"template4Bool: every generated declaration must be predicate: {repr un.decls}"

/- A predicate state retaining `j` distinguishes scalar leaf declarations from correctly ranked
   ones. Its generated leaves assign over the synthetic state-slice axis, so each declaration must
   carry that same fresh AxisSpec while the scan coordinate `l` is eliminated into the leaf name. -/
private def retainedPredL : AxisSpec := ⟨"l", 7701, .nat⟩
private def retainedPredJ : AxisSpec := ⟨"j", 7702, .nat⟩

def retainedPredicateSched : ScheduledProgram :=
  { decls := [.iter retainedPredL 3, .axis retainedPredJ (some 2),
              .predicate "S" [retainedPredJ, retainedPredL]]
  , stmts := [.scan "S" [retainedPredL]
      [ .assign "S" [.free retainedPredJ, .iterAt retainedPredL 0]
          { body := { terms := [{ factors := [.read "S0" [.axis retainedPredJ]] }] },
            nonlin := .identity } ]
      [ .assign "S" [.free retainedPredJ, .iterNext retainedPredL]
          { body := { terms := [
              { factors := [.read "S" [.axis retainedPredJ, .axis retainedPredL]] },
              { factors := [.read "X" [.axis retainedPredJ, .axis retainedPredL]] }] },
            nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "S0" (insert "X" (∅ : Finset String))
  , explicitSizes := ((({} : HashMap UID Nat).insert retainedPredL.uid 3).insert
      retainedPredJ.uid 2) }

def retainedPredicateInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "S0" ⟨[2], #[0.0, 1.0]⟩).insert
    "X" ⟨[2, 3], #[1.0, 1.0, 0.0, 1.0, 0.0, 0.0]⟩

run_cmd do
  match retainedPredicateSched.stmts.find? (fun s => match s with | .scan .. => true | _ => false) with
  | none => throwError "retained predicate fixture has no scan node"
  | some sc =>
      match unrollScanNode retainedPredicateSched.explicitSizes retainedPredicateSched.decls sc with
      | .error m => throwError s!"retained predicate fixture failed to unroll: {m}"
      | .ok un =>
          let declNames := un.decls.map Decl.name
          unless declNames == ["%Z_S", "%B_S_0_0", "%U_S_0", "%U_S_1", "%U_S_2"] do
            throwError s!"retained predicate fixture has unexpected generated decls: {declNames}"
          match un.geom.states with
          | [st] =>
              unless un.decls.all (fun d => match d, st.sliceAxes with
                  | .predicate _ [a], [expected] => a.uid == expected.uid
                  | _, _ => false) do
                throwError s!"retained predicate leaf declarations lost their slice axis: {repr un.decls}"
          | _ => throwError "retained predicate fixture must have exactly one state"
  match independentRun retainedPredicateSched retainedPredicateInputs with
  | .error m => throwError s!"retained predicate independent run failed: {m}"
  | .ok env => match env["S"]? with
    | some s =>
        unless denseEq s ⟨[2, 3], #[0.0, 1.0, 1.0, 1.0, 1.0, 1.0]⟩ do
          throwError s!"retained predicate history wrong: {repr s.shape}/{repr s.data}"
    | none => throwError "retained predicate fixture: no S in the independent environment"

/-! ## S-B scan-scatter fixtures

These are direct scheduled clones of the five Task 3 semantic cases. Keeping them hand-built avoids
depending on the source compiler's later S-B reachability work. -/

structure ScanScatterOracleCase where
  label    : String
  sched    : ScheduledProgram
  inputs   : HashMap String DenseTensor
  expected : DenseTensor

private def sbJ : AxisSpec := ⟨"j", 8101, .real⟩
private def sbK : AxisSpec := ⟨"k", 8106, .real⟩
private def sbO : AxisSpec := ⟨"o", 8103, .real⟩
private def sbP : AxisSpec := ⟨"p", 8104, .real⟩
private def sbL : AxisSpec := ⟨"l", 8105, .nat⟩

private def sbSchedule (decls : List Decl) (sizes : HashMap UID Nat)
    (external : Finset String) (base recur : List Stmt) : ScheduledProgram :=
  { decls, stmts := [.scan "S" [sbL] base recur false], env := {}
  , extNames := external, explicitSizes := sizes }

private def sbSizes1 (j o l : Nat) : HashMap UID Nat :=
  ((({} : HashMap UID Nat).insert sbJ.uid j).insert sbO.uid o).insert sbL.uid l

private def interleaveCase : ScanScatterOracleCase :=
  let evenBase : Stmt := .scatter "S" [.affine (.scale 2 sbJ), .iterAt sbL 0]
    { body := { terms := [{ factors := [.read "E" [.axis sbJ]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let oddBase : Stmt := .scatter "S" [.affine (.affine 1 [(2, sbJ)]), .iterAt sbL 0]
    { body := { terms := [{ factors := [.read "O" [.axis sbJ]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.free sbO, .iterNext sbL]
    { body := { terms := [{ factors := [.read "S" [.axis sbO, .axis sbL]] }] },
      nonlin := .identity }
  { label := "even/odd interleave"
  , sched := sbSchedule
      [.axis sbJ (some 3), .axis sbO (some 6), .iter sbL 2,
       .tensor "E" [sbJ], .tensor "O" [sbJ]]
      (sbSizes1 3 6 2) (insert "E" (insert "O" ∅)) [evenBase, oddBase] [recur]
  , inputs := (({} : HashMap String DenseTensor).insert "E" ⟨[3], #[1, 2, 3]⟩).insert
      "O" ⟨[3], #[10, 20, 30]⟩
  , expected := ⟨[6, 2], #[1,1, 10,10, 2,2, 20,20, 3,3, 30,30]⟩ }

private def stridedRecurrenceCase : ScanScatterOracleCase :=
  let base : Stmt := .assign "S" [.free sbO, .iterAt sbL 0]
    { body := { terms := [{ factors := [.read "X" [.axis sbO]] }] }, nonlin := .identity }
  let recur : Stmt := .scatter "S" [.affine (.affine 1 [(2, sbJ)]), .iterNext sbL]
    { body := { terms := [{ factors := [.read "S" [.scale 2 sbJ, .axis sbL]] }] },
      nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  { label := "strided recurrence"
  , sched := sbSchedule
      [.axis sbJ (some 3), .axis sbO (some 6), .iter sbL 3, .tensor "X" [sbO]]
      (sbSizes1 3 6 3) (insert "X" ∅) [base] [recur]
  , inputs := ({} : HashMap String DenseTensor).insert "X" ⟨[6], #[1,2,3,4,5,6]⟩
  , expected := ⟨[6,3], #[1,0,0, 2,1,0, 3,0,0, 4,3,0, 5,0,0, 6,5,0]⟩ }

private def contractionCase : ScanScatterOracleCase :=
  let base : Stmt := .scatter "S" [.affine (.scale 2 sbJ), .iterAt sbL 0]
    { body := { terms := [{ factors :=
        [.read "X" [.axis sbJ, .axis sbK], .read "W" [.axis sbK]] }] },
      nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.free sbO, .iterNext sbL]
    { body := { terms := [{ factors := [.read "S" [.axis sbO, .axis sbL]] }] },
      nonlin := .identity }
  { label := "RHS contraction"
  , sched := sbSchedule
      [.axis sbJ (some 3), .axis sbK none, .axis sbO (some 6), .iter sbL 2,
       .tensor "X" [sbJ, sbK], .tensor "W" [sbK]]
      (sbSizes1 3 6 2) (insert "X" (insert "W" ∅)) [base] [recur]
  , inputs := (({} : HashMap String DenseTensor).insert
      "X" ⟨[3,2], #[1,10, 2,20, 3,30]⟩).insert "W" ⟨[2], #[1,2]⟩
  , expected := ⟨[6,2], #[21,21, 0,0, 42,42, 0,0, 63,63, 0,0]⟩ }

private def nonTrailingCase : ScanScatterOracleCase :=
  let base : Stmt := .scatter "S" [.iterAt sbL 0, .affine (.affine 1 [(2, sbJ)])]
    { body := { terms := [{ factors := [.read "X" [.axis sbJ]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.iterNext sbL, .free sbO]
    { body := { terms := [{ factors := [.read "S" [.axis sbL, .axis sbO]] }] },
      nonlin := .identity }
  { label := "non-trailing advancing dimension"
  , sched := sbSchedule
      [.axis sbJ (some 3), .axis sbO (some 6), .iter sbL 3, .tensor "X" [sbJ]]
      (sbSizes1 3 6 3) (insert "X" ∅) [base] [recur]
  , inputs := ({} : HashMap String DenseTensor).insert "X" ⟨[3], #[4,5,6]⟩
  , expected := ⟨[3,6], #[0,4,0,5,0,6, 0,4,0,5,0,6, 0,4,0,5,0,6]⟩ }

private def twoAffineCase : ScanScatterOracleCase :=
  let base : Stmt := .scatter "S"
    [.affine (.scale 2 sbJ), .affine (.affine 1 [(2, sbK)]), .iterAt sbL 0]
    { body := { terms := [{ factors := [.read "X" [.axis sbJ, .axis sbK]] }] },
      nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.free sbO, .free sbP, .iterNext sbL]
    { body := { terms := [{ factors :=
        [.read "S" [.axis sbO, .axis sbP, .axis sbL]] }] }, nonlin := .identity }
  let sizes := ((((({} : HashMap UID Nat).insert sbJ.uid 2).insert sbK.uid 2).insert
    sbO.uid 4).insert sbP.uid 4).insert sbL.uid 2
  { label := "two affine non-advancing dimensions"
  , sched := sbSchedule
      [.axis sbJ (some 2), .axis sbK (some 2), .axis sbO (some 4), .axis sbP (some 4),
       .iter sbL 2, .tensor "X" [sbJ, sbK]]
      sizes (insert "X" ∅) [base] [recur]
  , inputs := ({} : HashMap String DenseTensor).insert "X" ⟨[2,2], #[1,2,3,4]⟩
  , expected := ⟨[4,4,2],
      #[0,0,1,1,0,0,2,2, 0,0,0,0,0,0,0,0,
        0,0,3,3,0,0,4,4, 0,0,0,0,0,0,0,0]⟩ }

/-- Two base contributions with the same affine image must be rejected by the oracle's own
    coordinate enumeration, independently of checked-plan collision classification. -/
private def overlappingBaseSchedule : ScheduledProgram :=
  let first : Stmt := .scatter "S" [.affine (.scale 2 sbJ), .iterAt sbL 0]
    { body := { terms := [{ factors := [.read "E" [.axis sbJ]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let second : Stmt := .scatter "S" [.affine (.scale 2 sbJ), .iterAt sbL 0]
    { body := { terms := [{ factors := [.read "O" [.axis sbJ]] }] }, nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.free sbO, .iterNext sbL]
    { body := { terms := [{ factors := [.read "S" [.axis sbO, .axis sbL]] }] },
      nonlin := .identity }
  sbSchedule
    [.axis sbJ (some 3), .axis sbO (some 6), .iter sbL 2,
     .tensor "E" [sbJ], .tensor "O" [sbJ]]
    (sbSizes1 3 6 2) (insert "E" (insert "O" ∅)) [first, second] [recur]

/-- The five Task 4 S-B oracle fixtures, exported for `ScanOracle`'s feature-presence guards. -/
def scanScatterOracleCases : List ScanScatterOracleCase :=
  [interleaveCase, stridedRecurrenceCase, contractionCase, nonTrailingCase, twoAffineCase]

private def scanNodeOf (sched : ScheduledProgram) : Except String ScanStmt :=
  match sched.stmts with
  | [.scan name axes base recur flag] => pure (.scan name axes base recur flag)
  | _ => .error "S-B oracle fixture must contain exactly one scan node"

/-- Every emitted scatter consumes exactly the dense temporary assigned immediately before it. -/
private def assignmentThenScatter (stmts : List Stmt) : Bool :=
  stmts.zipIdx.all (fun (s, i) => match s with
    | .scatter _ _ rhs _ =>
        match stmts[i - 1]?, rhs.body.terms with
        | some (.assign temp _ _), [{ factors := [.read source _] }] =>
            i > 0 && temp == source
        | _, _ => false
    | _ => true)

run_cmd do
  match scanNodeOf overlappingBaseSchedule with
  | .error m => throwError s!"overlap fixture has no scan node: {m}"
  | .ok sc =>
      match unrollScanNode overlappingBaseSchedule.explicitSizes overlappingBaseSchedule.decls sc with
      | .ok _ => throwError "overlapping affine base contributions were accepted"
      | .error m =>
          unless m == "S: base contributions 0 and 1 overlap at history coordinate [0]" do
            throwError s!"overlap fixture produced the wrong diagnostic: {m}"

-- All five fixtures assert structure, private-name exclusion, independent shape, and exact value.
run_cmd do
  unless scanScatterOracleCases.length == 5 do
    throwError "the S-B oracle fixture corpus must contain exactly five cases"
  for c in scanScatterOracleCases do
    let sc ← match scanNodeOf c.sched with
      | .ok sc => pure sc
      | .error m => throwError s!"{c.label}: {m}"
    let un ← match unrollScanNode c.sched.explicitSizes c.sched.decls sc with
      | .ok un => pure un
      | .error m => throwError s!"{c.label}: unroll failed: {m}"
    unless un.stmts.any (fun s => match s with | .scatter .. => true | _ => false) do
      throwError s!"{c.label}: no scatter survived scan-free leaf emission"
    unless assignmentThenScatter un.stmts do
      throwError s!"{c.label}: an emitted scatter is not immediately preceded by its dense assignment"
    match independentRun c.sched c.inputs with
    | .error m => throwError s!"{c.label}: independent run failed: {m}"
    | .ok env =>
        match env["S"]? with
        | none => throwError s!"{c.label}: reconstructed state S is missing"
        | some actual =>
            unless denseEq actual c.expected do
              throwError s!"{c.label}: wrong history {actual.shape}/{actual.data}"
        unless un.stmts.all (fun s => !env.contains s.lhsName) do
          throwError s!"{c.label}: a private leaf or dense temporary escaped reconstruction"

-- Interleaved bases have distinct contribution names followed by one canonical merge, all before
-- the recurrence reads `%U_S_0`.
#guard match scanNodeOf interleaveCase.sched with
  | .error _ => false
  | .ok sc => match unrollScanNode interleaveCase.sched.explicitSizes interleaveCase.sched.decls sc with
      | .error _ => false
      | .ok un => un.stmts.map Stmt.lhsName ==
          ["%Z_S", "%D_B_S_0_0", "%B_S_0_0", "%D_B_S_1_0", "%B_S_1_0", "%U_S_0", "%U_S_1"]

-- The merge reads both contributions in source order, and the first recurrence leaf reads only the
-- canonical merge. This pins both dependency order and the contribution/canonical distinction.
#guard match scanNodeOf interleaveCase.sched with
  | .error _ => false
  | .ok sc => match unrollScanNode interleaveCase.sched.explicitSizes interleaveCase.sched.decls sc with
      | .error _ => false
      | .ok un =>
          match un.stmts.find? (fun s => s.lhsName == "%U_S_0"),
                un.stmts.find? (fun s => s.lhsName == "%U_S_1") with
          | some (.assign _ _ merge), some (.assign _ _ recur) =>
              merge.body.terms.filterMap (fun t => match t.factors with
                | [.read nm _] => some nm | _ => none) == ["%B_S_0_0", "%B_S_1_0"] &&
              recur.body.terms.any (fun t => t.factors.any (fun
                | .read "%U_S_0" _ => true
                | _ => false))
          | _, _ => false

-- The contraction-only axis `k` remains in the temporary RHS but not its one-axis output basis.
#guard match scanNodeOf contractionCase.sched with
  | .error _ => false
  | .ok sc => match unrollScanNode contractionCase.sched.explicitSizes contractionCase.sched.decls sc with
      | .error _ => false
      | .ok un => match un.stmts.find? (fun s => s.lhsName == "%D_B_S_0_0") with
          | some (.assign _ [.free a] _) => a.uid == sbJ.uid
          | _ => false

-- Two independent affine dimensions produce one rank-two dense temporary and one rank-two scatter.
#guard match scanNodeOf twoAffineCase.sched with
  | .error _ => false
  | .ok sc => match unrollScanNode twoAffineCase.sched.explicitSizes twoAffineCase.sched.decls sc with
      | .error _ => false
      | .ok un => match un.stmts.drop 1 with
          | .assign _ [.free a, .free b] _ :: .scatter _ [.affine _, .affine _] _ _ :: _ =>
              a.uid == sbJ.uid && b.uid == sbK.uid
          | _ => false

end LeanNCD.PropertyOracle

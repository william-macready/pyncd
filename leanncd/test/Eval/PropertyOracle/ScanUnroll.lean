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
by `substBool` (an Iverson takes the actual scan coordinate; a mask zeros every eliminated scan
seed). Nonlinearity and aggregation are carried through unchanged, so the two `enumScanCases`
templates F4 rejects as capability failures (`relu` steps, tropical aggregation) are still unrollable
and still checked against the legacy evaluator. Everything outside the fragment (scatter,
`recurMorphism`, non-literal history coordinates, and an axiswise reduction along an ELIMINATED scan
coordinate — `fragment.eliminatedNormalizationAxis`) is rejected with a message rather than silently
mis-unrolled — plan §4.8's "the oracle need not support source syntax rejected by production
preflight".
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
  /-- The remaining tensor dimensions, ascending, and their LHS slots. -/
  freePos   : List Nat
  freeSlots : List LHSSlot

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

private def rhsOf (s : Stmt) : Except String RHSExpr :=
  match s with
  | .assign _ _ r         => .ok r
  | .scatter nm _ _ _     => .error s!"scatter `{nm}` inside a scan is outside the oracle's fragment"
  | .recurMorphism nm _ _ => .error s!"recurMorphism `{nm}` inside a scan is outside the fragment"

/-- Resolve one state's dimension mapping from its recurrence result. -/
private def buildGeom (axes : List AxisSpec) (result : Stmt) : Except String StateGeom := do
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
  let freePos := (List.range slots.length).filter (fun p => !advDim.contains p)
  let freeSlots ← freePos.mapM (fun p =>
    match slots[p]? with
    | some (LHSSlot.free a) => pure (LHSSlot.free a)
    | some (LHSSlot.freeNorm a) => pure (LHSSlot.freeNorm a)
    | some sl        => .error s!"{nm}: dimension {p} is neither advancing nor a plain free axis \
({repr sl}) — outside the oracle's fragment"
    | none           => .error s!"{nm}: dimension {p} is out of range")
  pure { name := nm, rank := slots.length, advDim, freePos, freeSlots }

/-- Classify a scan node: extents, persistent states (base destinations, source order), and
    block-local scratch (recurrence destinations with no base statement). Deliberately traverses
    the node's own `base`/`recur` lists rather than `ScanStmt.outputs`, for plan §4.2's reasons. -/
def analyzeScan (sizes : HashMap UID Nat) (sc : ScanStmt) : Except String ScanGeom :=
  match sc with
  | .scan _ axes base recur _ => do
      if axes.isEmpty then .error "scan node with no advancing axis"
      let ext ← axes.mapM (fun a =>
        match sizes[a.uid]? with
        | some 0 => .error s!"axis {a.name} has extent zero"
        | some n => pure n
        | none   => .error s!"axis {a.name} has no pinned extent (`explicitSizes`)")
      let stateNames := (base.map Stmt.lhsName).eraseDups
      let states ← stateNames.mapM (fun nm =>
        match recur.filter (fun s => s.lhsName == nm) with
        | [r] => buildGeom axes r
        | []  => .error s!"state {nm} has a base case but no recurrence result"
        | _   => .error s!"state {nm} has more than one recurrence result")
      let localNames := ((recur.map Stmt.lhsName).eraseDups).filter
        (fun nm => !stateNames.contains nm)
      let locals ← localNames.mapM (fun nm =>
        match recur.filter (fun s => s.lhsName == nm) with
        | [s] =>
            if s.slots.any (fun sl => match sl with
                | .iterAt _ _ | .iterNext _ => true
                | _ => false) then
              (buildGeom axes s).map (fun g => (nm, some g))
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

/-- A base statement's own non-advancing LHS slots, which become the leaf's slots. -/
private def baseFreeSlots (st : StateGeom) (s : Stmt) : Except String (List LHSSlot) :=
  st.freePos.mapM (fun p =>
    match s.slots[p]? with
    | some (LHSSlot.free a) => pure (LHSSlot.free a)
    | some (LHSSlot.freeNorm a) => pure (LHSSlot.freeNorm a)
    | _ => .error s!"base write for {st.name}: dimension {p} must be a plain free axis")

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
        let frees := st.freePos.filterMap (fun p => (idxs[p]?).map (substIdx σ))
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
                pure (scratchLeafName nm u, st.freePos.filterMap (fun p =>
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

/-- Rewrite one statement's nonlinearity for the leaf program. `identity`/`pointwise` pass through.
    An `.axiswise` operation whose marked normalization axis (`.freeNorm` among `outSlots`, the
    leaf's own output slots) is an eliminated scan coordinate is REJECTED with the named fragment
    error — the per-coordinate leaf unroller cannot reduce along an axis it has eliminated. Its mask
    (when present) is rewritten with the MASK policy, DISTINCT from the Iverson-factor policy: every
    source seed (scan axis) reads ZERO, mirroring the checked lowering's absence of a seeded axis
    from the local non-seeded output basis; every eliminated non-seeded `.free`/`.freeNorm` output
    slot and every retained output axis stays an expression, resolved against the leaf's own
    enumerated coordinate. -/
private def rewriteNonlin (g : ScanGeom) (σ : UID → Option Int) (outSlots : List LHSSlot) :
    Nonlin → Except String Nonlin
  | .axiswise fn m => do
      match outSlots.findSome? (fun sl => match sl with | .freeNorm a => some a | _ => none) with
      | some a =>
          if g.axes.any (·.uid == a.uid) then .error fragment.eliminatedNormalizationAxis
      | none => pure ()
      -- Mask policy (DISTINCT from the Iverson-factor policy `σ`): every source seed (scan axis)
      -- reads ZERO, never the live step coordinate `σ` — mirroring the checked lowering, whose local
      -- non-seeded output basis omits the seeded axis so it densifies to coordinate 0 every step.
      let σmask : UID → Option Int := fun u => if g.axes.any (·.uid == u) then some 0 else none
      pure (.axiswise fn (m.map (substBool σmask)))
  | other => pure other

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

/-- Unroll one scan node into scan-free leaf statements.

    Emission order is: every state's zero leaf, then every base write (source order, so a later
    base statement overrides an earlier one exactly as the raw plan's ordered base writes do), then
    the step iterations in lexicographic order. A step at `u` reads only coordinates `≤ u` and
    writes only `u + 1`, so this order both satisfies every read and gives the checked worker's
    immutable-pre-step (Jacobi) snapshot for free: no read inside iteration `u` can name a leaf that
    iteration `u` writes. -/
def unrollScanNode (sizes : HashMap UID Nat) (decls : List Decl) (sc : ScanStmt) :
    Except String Unrolled := do
  let g ← analyzeScan sizes sc
  -- 1. resolve each base statement's state, leaf slots, written region and RHS.
  let baseParts ← g.base.mapM (fun s => do
    let st ← match g.states.find? (fun st => st.name == s.lhsName) with
      | some st => pure st
      | none    => .error s!"base statement writes {s.lhsName}, which is not a persistent state"
    let fs  ← baseFreeSlots st s
    let reg ← baseRegion g st s
    let r   ← rhsOf s
    pure (st, fs, reg, r))
  -- 2. which history coordinates carry a real leaf: a base region, or a step's `u + 1`.
  let stepCoords := coordsOf (g.ext.map (fun n => n - 1))
  let advanced := stepCoords.map (fun u => u.map (· + 1))
  let live : List (String × List (List Nat)) := g.states.map (fun st =>
    let fromBase := baseParts.flatMap (fun (bst, _, reg, _) =>
      if bst.name == st.name then reg else [])
    (st.name, (fromBase ++ advanced).eraseDups))
  let hasLeaf : String → List Nat → Bool := fun nm t =>
    match live.find? (fun p => p.1 == nm) with
    | some (_, ts) => ts.contains t
    | none         => false
  -- 3. zero leaves.
  let zeroStmts : List Stmt := g.states.map (fun st =>
    .assign (zeroLeafName st.name) st.freeSlots { body := { terms := [] }, nonlin := .identity })
  let zeroDecls : List Decl := g.states.filterMap (fun st =>
    if isPredicateName decls st.name then some (.predicate (zeroLeafName st.name) []) else none)
  -- 4. base leaves: one per (base statement, coordinate in its region), pins substituted.
  let baseStmts ← baseParts.flatMapM (fun (st, fs, reg, r) =>
    reg.mapM (fun t => do
      let rhs ← rewriteRHS g (ctxSubst g.axes t) hasLeaf none fs r
      pure (Stmt.assign (stateLeafName st.name t) fs rhs)))
  let baseDecls : List Decl := baseParts.flatMap (fun (st, _, reg, _) =>
    if isPredicateName decls st.name then reg.map (fun t => .predicate (stateLeafName st.name t) [])
    else [])
  -- 5. step leaves: the whole recurrence list, once per step iteration, in source order.
  let stepStmts ← stepCoords.flatMapM (fun u => do
    let σ := ctxSubst g.axes u
    g.recur.mapM (fun s => do
      let r   ← rhsOf s
      -- The leaf's own output slots (`.freeNorm`/`.free` faces), resolved BEFORE the rewrite so the
      -- mask/normalization rewrite sees them: a state or advancing-scratch leaf keeps the state's
      -- non-advancing free slots, a plain scratch keeps its own slots.
      let (leafName, leafSlots) :=
        match g.states.find? (fun st => st.name == s.lhsName) with
        | some st => (stateLeafName st.name (u.map (· + 1)), st.freeSlots)
        | none =>
            match g.advScratch.find? (fun st => st.name == s.lhsName) with
            | some st => (scratchLeafName s.lhsName u, st.freeSlots)
            | none    => (scratchLeafName s.lhsName u, s.slots)
      let rhs ← rewriteRHS g σ hasLeaf (some u) leafSlots r
      pure (Stmt.assign leafName leafSlots rhs)))
  -- `nm`/`u` here mirror the SAME leaf-name derivation as step 5 above, but predicate-lookup is
  -- always keyed by the ORIGINAL recurrence destination `s.lhsName` (state or scratch alike),
  -- matching `checkPredicateOutput`'s own dispatch on the LHS name.
  let stepDecls : List Decl := stepCoords.flatMap (fun u =>
    g.recur.filterMap (fun s =>
      if isPredicateName decls s.lhsName then
        let leafName := match g.states.find? (fun st => st.name == s.lhsName) with
          | some st => stateLeafName st.name (u.map (· + 1))
          | none    => scratchLeafName s.lhsName u
        some (.predicate leafName [])
      else none))
  pure { geom := g, stmts := zeroStmts ++ baseStmts ++ stepStmts
       , live, decls := zeroDecls ++ baseDecls ++ stepDecls }

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
  if zt.shape.length != st.freePos.length then
    .error s!"{st.name}: the zero leaf has rank {zt.shape.length}, expected {st.freePos.length}"
  -- every coordinate a base write or a step must have produced has to be present, so a lost or
  -- misplaced leaf fails loudly instead of silently reading as the zero default.
  let liveCoords := match un.live.find? (fun p => p.1 == st.name) with
    | some (_, ts) => ts
    | none         => []
  for t in liveCoords do
    unless leafEnv.contains (stateLeafName st.name t) do
      .error s!"{st.name}: leaf for history coordinate {t} was never produced by the unrolled program"
  let advAt  : List (Nat × Nat) := st.advDim.zipIdx.map (fun (p, k) => (p, g.ext.getD k 0))
  let freeAt : List (Nat × Nat) := st.freePos.zipIdx.map (fun (p, i) => (p, zt.shape.getD i 0))
  let dims := (List.range st.rank).map (fun p =>
    match (advAt ++ freeAt).find? (fun (q, _) => q == p) with
    | some (_, d) => d
    | none        => 0)
  pure (DenseTensor.ofFn dims (fun coord =>
    let hist := st.advDim.map (fun p => coord.getD p 0)
    let free := st.freePos.map (fun p => coord.getD p 0)
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
    | .scan .. => do
        let un ← unrollScanNode sched.explicitSizes sched.decls sc
        -- Task 4.4: the leaf program's OWN decls are `sched.decls` (needed by a `.plain` statement
        -- reading an unrelated declared name) PLUS the generated predicate decls for THIS scan's
        -- leaves (`un.decls`) — the leaf names never collide with any source name (`%`-prefixed),
        -- so appending is safe and there is nothing to deduplicate.
        let leafEnv ←
            match evalScheduled { sched with stmts := un.stmts.map ScanStmt.plain
                                            , decls := sched.decls ++ un.decls } env with
          | .ok r    => pure r.env
          | .error e => .error s!"independent run: the unrolled scan-free program failed: {e.error}"
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
            unless names == ["%Z_S", "%U_S_0", "%U_S_1", "%U_S_2"] do
              throwError s!"unexpected leaf statements: {names}"
            unless un.stmts.all (fun s => match s with | .assign .. => true | _ => false) do
              throwError "the unrolled program is not made of plain assignments"

/- Task 4.4, fixture 8: the same leaf-name assertion above, cloned onto `template4Bool` (Task 4.4
   fixture 1's `predicate S(l)` case) instead of `template1` — its ONE state `S` has no free axis,
   so its leaves are exactly the un-tagged `%Z_S`/`%U_S_0`/`%U_S_1`/`%U_S_2` (for `L = 3`). Every
   generated declaration for them must be `.predicate`, since `S` itself is: without it (temporarily
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
            unless names == ["%Z_S", "%U_S_0", "%U_S_1", "%U_S_2"] do
              throwError s!"template4Bool: unexpected leaf statements: {names}"
            let declNames := un.decls.map Decl.name
            unless declNames == ["%Z_S", "%U_S_0", "%U_S_1", "%U_S_2"] do
              throwError s!"template4Bool: unexpected generated decls: {declNames}"
            unless un.decls.all (fun d => match d with | .predicate _ _ => true | _ => false) do
              throwError s!"template4Bool: every generated declaration must be predicate: {repr un.decls}"

end LeanNCD.PropertyOracle

import LeanNCD.Base.SizeExpr
import LeanNCD.Exec.Uid   -- reuse the canonical `UID := Nat`; do NOT redefine it (duplicate-def error)
import LeanNCD.DSL.Target

namespace LeanNCD

inductive AxisKind
  | real
  | nat
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure AxisSpec where
  name : String
  uid  : UID
  kind : AxisKind
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

inductive Decl
  | tensor    : String → List AxisSpec → Decl
  | predicate : String → List AxisSpec → Decl
  | linear    : String → List AxisSpec → (bias : Bool) → Decl
  | axis      : AxisSpec → Option Nat → Decl   -- `axis l : ℕ = 3`: declares an axis's dtype + optional pinned size
  | iter      : AxisSpec → Nat → Decl          -- `iter l = 3`: the ONLY way to declare a scan iteration
                                                 -- axis (#5b) — pinned-only (no `Option`), kind is always
                                                 -- `.nat` (forced at elaboration, `Elab.lean`), never `ℝ`
  deriving DecidableEq, Repr, Lean.ToExpr

inductive IdxExpr
  | axis   : AxisSpec → IdxExpr
  | const  : Int → IdxExpr
  | scale  : Int → AxisSpec → IdxExpr
  | shift  : AxisSpec → Int → IdxExpr
  | affine : Int → List (Int × AxisSpec) → IdxExpr
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Normalize an `IdxExpr` to canonical integer-affine form `(c0, [(coef, uid)])`. The single
    affine-lowering primitive shared by the compile path (`idxToRow`, dense over a degree basis) and
    the eval size solver (`Eval/Shape.lean`, sparse) — see `idxDensify`. -/
def idxAffineForm : IdxExpr → Int × List (Int × UID)
  | .axis a      => (0, [(1, a.uid)])
  | .const n     => (n, [])
  | .scale c a   => (0, [(c, a.uid)])
  | .shift a n   => (n, [(1, a.uid)])
  | .affine n xs => (n, xs.map (fun (c, a) => (c, a.uid)))

/-- Densify a sparse affine coefficient list over a degree basis `us` (column order = `us`): the
    `u`-th entry is the sum of the coefficients whose uid is `u`. The bridge from `idxAffineForm`
    (basis-free) to the dense row `idxToRow` needs. -/
def idxDensify (cf : List (Int × UID)) (us : List UID) : List Int :=
  us.map (fun u => cf.foldl (fun acc p => if p.2 == u then acc + p.1 else acc) 0)

inductive PredArith
  | embed : IdxExpr → PredArith
  | mul   : PredArith → PredArith → PredArith
  | iabs  : PredArith → PredArith
  deriving DecidableEq, Repr, Lean.ToExpr

inductive RelOp | lt | le | eq | ne | ge | gt
  deriving DecidableEq, Repr, Lean.ToExpr

inductive BoolExpr
  | rel  : RelOp → PredArith → PredArith → BoolExpr
  | and  : BoolExpr → BoolExpr → BoolExpr
  | or   : BoolExpr → BoolExpr → BoolExpr
  | not  : BoolExpr → BoolExpr
  | ieq  : PredArith → PredArith → BoolExpr
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Pointwise (elementwise) nonlinearities: they carry no mask and no axis, because they act on
    each entry independently. -/
inductive PointwiseFn | relu | sigmoid | tanh | gelu | leakyrelu
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- Axis-reducing nonlinearities (softmax/normalize act along ONE designated axis of an
    arbitrary-rank tensor — "axiswise", not intrinsically a matrix row; `perRow` is the
    implementation view, not the semantics). -/
inductive AxiswiseFn | softmax | normalize | l2normalize
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- A step's nonlinearity. `pointwise` fns carry no mask (by type — a new one *cannot* forget
    mask handling); `axiswise` fns carry the reduction mask once.
    `identity` stays FIRST so the derived `Inhabited` default remains `.identity`. -/
inductive Nonlin
  | identity
  | pointwise : PointwiseFn → Nonlin
  | axiswise  : AxiswiseFn → Option BoolExpr → Nonlin
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- The `BrOp` label a pointwise nonlinearity lowers to. `BrOp` stays flat (its indices are a
    wire format — see `brOpIdx`); only the mapping from the `Nonlin` side is structured. -/
def PointwiseFn.toBrOp : PointwiseFn → BrOp
  | .relu => .relu | .sigmoid => .sigmoid | .tanh => .tanh | .gelu => .gelu
  | .leakyrelu => .leakyrelu

/-- The `BrOp` label an axiswise nonlinearity lowers to (the mask is not part of the op label). -/
def AxiswiseFn.toBrOp : AxiswiseFn → BrOp
  | .softmax => .softmax | .normalize => .normalize | .l2normalize => .l2normalize

-- Reduction operation for contraction (sum is standard; max/min are tropical).
inductive AggOp | sum | max | min
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

-- Unary transcendental functions applicable inline to a single factor's read (`log(P[i])`).
-- `recip` has no keyword form of its own — it's produced only by the infix `/` sugar.
inductive UnaryOp | log | exp | sin | cos | sqrt | recip
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

inductive Factor
  | read    : String → List IdxExpr → Factor
  | iverson : BoolExpr → Factor
  | unaryFn : UnaryOp → String → List IdxExpr → Factor
  deriving DecidableEq, Repr, Lean.ToExpr

structure ProdTerm where factors : List Factor
  deriving DecidableEq, Repr, Lean.ToExpr
structure SumExpr  where terms   : List ProdTerm
  deriving DecidableEq, Repr, Lean.ToExpr
structure RHSExpr  where
  body   : SumExpr
  nonlin : Nonlin
  agg    : AggOp := .sum   -- contraction operation (sum = standard; max = tropical)
  deriving DecidableEq, Repr, Lean.ToExpr

inductive LHSSlot
  | free     : AxisSpec → LHSSlot
  | freeNorm : AxisSpec → LHSSlot   -- a free output axis marked (`m.`) as the softmax/normalize reduction axis
  | iterAt   : AxisSpec → Int → LHSSlot
  | iterNext : AxisSpec → LHSSlot
  | affine   : IdxExpr → LHSSlot
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Scatter collision-reduction policy: how to merge multiple source coordinates that write the
    same output coordinate. Distinct from `RHSExpr.agg` (the 4b `Combine` selection in
    `Contract`/`Scatter`), which governs how a SINGLE source coordinate's own RHS terms combine —
    the two are independent (an RHS `maxreduce` with collision `sum` differs from RHS `sum` with
    collision `max`). `rejectCollisions` is the default: absence of an explicit policy means a
    collision is a validation failure, not an implicit overwrite. -/
inductive CollisionReduce
  | rejectCollisions
  | overwrite
  | sum
  | max
  | min
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure ScatterOpts where
  fill   : Int := 0
  reduce : CollisionReduce := .rejectCollisions
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

inductive Stmt
  | assign  : String → List LHSSlot → RHSExpr → Stmt
  | scatter : String → List LHSSlot → RHSExpr → ScatterOpts → Stmt
  | recurMorphism : String → AxisSpec → ThreadedComposed → Stmt
    -- escape hatch (§12.2): tensor name, iteration axis, a pre-built step morphism (programmatic-only)
  deriving DecidableEq, Repr, Lean.ToExpr

structure TLProgram where
  decls : List Decl
  stmts : List Stmt
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/- ── AST accessors (shared by the DSL pipeline and Eval layers) ── -/

/-- The declaration's tensor name. (`axis` decls name an AXIS, not a tensor; `resolveDecls`
    skips them when building the tensor-keyed `DeclEnv`.) -/
def Decl.name : Decl → String
  | .tensor n _ => n | .predicate n _ => n | .linear n _ _ => n | .axis ax _ => ax.name
  | .iter ax _  => ax.name

/-- The tensor name a stmt writes to (its LHS). -/
def Stmt.lhsName : Stmt → String
  | .assign n _ _ => n | .scatter n _ _ _ => n | .recurMorphism n _ _ => n

/-- The LHS slots of a statement. -/
def Stmt.slots : Stmt → List LHSSlot
  | .assign _ ls _ => ls | .scatter _ ls _ _ => ls | .recurMorphism _ _ _ => []

/-- The nonlinearity wrapping a stmt's step. A `recurMorphism` is pre-built (already-lowered),
    so it is affine-neutral (`identity`). Used by `finalizeScans` to detect ScanAffine (Prop 8.7):
    a scan whose every recurrence stmt is `identity`-nonlin carries no nonlinearity and is thus
    associative/parallel-prefix-able. This MUST be checked here (pre-`splitNonlins`), since
    `splitNonlins` later lifts nonlinearities out of `RHSExpr.nonlin` into separate steps. -/
def Stmt.nonlinOf : Stmt → Nonlin
  | .assign _ _ r => r.nonlin
  | .scatter _ _ r _ => r.nonlin
  | .recurMorphism _ _ _ => .identity

/-- One iteration slot of a stmt: its axis, whether it advances a recurrence (`iterNext`),
    and its slot position. Replaces the old anonymous `UID × AxisSpec × Bool × Nat` tuple
    (the UID component was redundant — it is `axis.uid`). -/
structure IterSlot where
  axis    : AxisSpec
  isRecur : Bool
  pos     : Nat
  deriving DecidableEq, Repr

/-- All iteration slots of a stmt: one entry per `iterAt`/`iterNext` slot.
    A 1-D scan yields a single-element list; multi-axis scans yield one entry per advancing slot. -/
def Stmt.iterInfo (s : Stmt) : List IterSlot :=
  s.slots.zipIdx.filterMap (fun (sl, i) => match sl with
    | .iterAt a _ => some { axis := a, isRecur := false, pos := i }
    | .iterNext a => some { axis := a, isRecur := true,  pos := i }
    | _           => none)

/-- The retained placement axis of an LHS slot, if any: the named axis of a
    `free`/`freeNorm`/`iterAt`/`iterNext` slot; `none` for an `affine` (scatter) slot.
    The one classifier the UID/AxisSpec projections below derive from. -/
def LHSSlot.axisSpec? : LHSSlot → Option AxisSpec
  | .free a     => some a
  | .freeNorm a => some a
  | .iterAt a _ => some a
  | .iterNext a => some a
  | .affine _   => none

/-- The UID of a slot's retained placement axis (`none` for `affine`). -/
def LHSSlot.axisUID? (sl : LHSSlot) : Option UID := (sl.axisSpec?).map (·.uid)

/-- The UID of a *plain* `free` slot only (`none` for freeNorm/iter/affine).
    Intentionally selective: a repeated `freeUID?` across a stmt's slots is how a
    diagonal LHS (`Y[i,i]`) is detected and routed to `scatter`. NOT `axisUID?`. -/
def LHSSlot.freeUID? : LHSSlot → Option UID
  | .free a => some a.uid
  | _       => none

/-- The UID of the slot marked (`m.`) as the softmax/normalize reduction axis
    (`freeNorm`), if any. Intentionally selective: this is how the reduction axis
    is identified for a stmt. NOT `axisUID?`. -/
def LHSSlot.normUID? : LHSSlot → Option UID
  | .freeNorm a => some a.uid
  | _           => none

/-- The index expression an LHS slot maps to (for `evalIdx`): the affine output coordinate. -/
def LHSSlot.outIdx : LHSSlot → IdxExpr
  | .affine e   => e
  | .free a     => .axis a
  | .freeNorm a => .axis a
  | .iterAt _ n => .const n
  | .iterNext a => .shift a 1

/-- Axis indices that index the output of a stmt (its free/scan slots). An `.affine` slot is a
    scatter output; `lowerArith` (`Pipeline/Structural.lean`) reclassifies every
    `slotsBecomeScatter` `.assign` into `Stmt.scatter` before Phase 6 runs, so no `.assign`
    carrying an `.affine` slot can reach `splitStmt` at all — unreachable from `splitStmt`
    post-`lowerArith`; kept total for exhaustiveness.

    Lives here (not in `Pipeline/Lowering.lean`, where it used to) so that both
    `Pipeline/Lowering.lean`'s `splitStmt` and `Pipeline/RouteFragments.lean`'s
    `physicalizeOne` build the nonlinear consumer's read coordinates from ONE definition —
    `RouteFragments` imports only `Pipeline/Types`, so it cannot reach `Lowering`. -/
def LHSSlot.toReadIdx : LHSSlot → Option IdxExpr
  | .free a     => some (.axis a)
  | .freeNorm a => some (.axis a)
  | .iterAt a _ => some (.axis a)
  | .iterNext a => some (.axis a)
  | .affine _   => none      -- scatter outputs: skipped (see doc above)

/-- Output extent of one scatter LHS slot under a sizing lookup `sz`.
    The single home of the scatter-extent convention (upsample stride semantics —
    deliberately not derivable from `idxAffineForm`). `none` if a source axis is unsized. -/
def LHSSlot.outExtent (sl : LHSSlot) (sz : UID → Option Nat) : Option Nat :=
  match sl.outIdx with
  | .axis a       => sz a.uid
  | .const n      => some (n + 1).toNat
  | .scale c a    => (sz a.uid).map (fun s => (c * Int.ofNat s).toNat)
  | .shift a c    => (sz a.uid).map (fun s => (Int.ofNat s + c).toNat)
  | .affine c0 xs =>
      if xs.all (fun (_, a) => (sz a.uid).isSome) then
        some (xs.foldl (fun acc (c, a) => acc + c * Int.ofNat ((sz a.uid).getD 0)) c0).toNat
      else none

/-- Classify a `Factor` as a tensor read: `read`/`unaryFn` keep (name, index-exprs);
    `iverson` (a mask/predicate) reads no tensor. The ONE place a new `Factor` constructor
    gets classified as a read — every read collector below is a projection of this. -/
def Factor.read? : Factor → Option (String × List IdxExpr)
  | .read nm es       => some (nm, es)
  | .unaryFn _ nm es  => some (nm, es)
  | .iverson _        => none

/-- The read factors (tensor name + read index exprs) of an RHS, in traversal order,
    with duplicates preserved (callers dedup if they need to). -/
def RHSExpr.readFactors (r : RHSExpr) : List (String × List IdxExpr) :=
  r.body.terms.flatMap (fun t => t.factors.filterMap Factor.read?)

/-- The read factors of a stmt, in order (`recurMorphism` reads are not introspected). -/
def Stmt.readFactors : Stmt → List (String × List IdxExpr)
  | .assign _ _ r | .scatter _ _ r _ => r.readFactors
  | .recurMorphism _ _ _ => []

end LeanNCD

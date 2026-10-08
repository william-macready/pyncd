import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter32

/-!
# The binary32 default AS a default (F32 flip, slice 2 acceptance fixture)

The flip's claim is "an unannotated program behaves exactly like the same program with every real
storage name declared `tensor f32`", end to end. The other f32 suites test EXPLICIT `f32` programs
and the classification pins test the default in isolation; this module tests the equivalence.

Every corpus program is written with EXPLICIT `f32` declarations (the authoritative spelling, by
hand, so no helper has to guess ranks). Two variants are derived mechanically from it:
* `plain`      — every `tensor f32`/`linear f32` re-spelled plain `tensor`/`linear`;
* `undeclared` — every `tensor f32` declaration dropped (`linear f32` re-spelled plain, since a
  linear's bias flag is not recoverable from use).
Predicates, axes and iters are untouched. For each program the three variants must agree on the
WHOLE `prepareEvalPlan` outcome (rejection cause, or the checked plan's `Repr` — raw plan, per-step
evidence and algebra, storage kind — plus bindings and warnings) and, when accepted, on the exact
`runPreparedDense32` result bits of every published name.

Mutation (observed): reverting `dtypeOfDecl`'s `none` arm to `.f64` makes the `undeclared` variant
of every accepted program with an undeclared external diverge (see the slice-2 audit record).
-/

namespace LeanNCD.Eval.Plan.DefaultF32Test
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

inductive Variant | explicit | plain | undeclared
  deriving Repr, BEq

def respell : Variant → List Decl → List Decl
  | .explicit, ds => ds
  | .plain, ds => ds.map fun
      | .typedTensor .f32 n as => .tensor n as
      | .typedLinear .f32 n as b => .linear n as b
      | d => d
  | .undeclared, ds => ds.filterMap fun
      | .typedTensor .f32 _ _ => none
      | .typedLinear .f32 n as b => some (.linear n as b)
      | d => some d

private def renderCompileCause : PlanCompileCause → String
  | .inputSignature c => s!"inputSignature: {repr c}"
  | .capability c     => s!"capability: {repr c}"
  | .shape c          => s!"shape: {c}"
  | .scan c           => s!"scan: {repr c}"
  | .invalidPlan c    => s!"invalidPlan: {repr c}"
  | .bindings c       => s!"bindings: {repr c}"
  | .nonlin c         => s!"nonlin: {repr c}"
  | .sourceInvariant c => s!"sourceInvariant: {repr c}"

/-- A corpus entry: surface source or a hand-built schedule, written with explicit `f32`. -/
structure Case where
  name   : String
  src    : TLProgram ⊕ ScheduledProgram
  inputs : NamedDenseEnv32

/-- Everything observable about one variant, as comparable data. `accepted` is the storage kind
    of an accepted plan (`none` on rejection). -/
structure Outcome where
  accepted : Option String
  prep     : String
  out      : String
  deriving BEq, Repr

def schedOf (v : Variant) : TLProgram ⊕ ScheduledProgram → Except String ScheduledProgram
  | .inl p => match ({ p with decls := respell v p.decls }).compileToScheduled.run 0 with
      | .ok s _ => .ok s
      | .error e _ => .error s!"compile: {repr e}"
  | .inr s => .ok { s with decls := respell v s.decls }

def outcome (c : Case) (v : Variant) : Outcome :=
  match schedOf v c.src with
  | .error e => ⟨none, e, ""⟩
  | .ok sched =>
    match InputSignature.ofDenseInputs32ForDecls sched.decls c.inputs with
    | .error e => ⟨none, s!"signature: {repr e}", ""⟩
    | .ok sig =>
      match prepareEvalPlan sched sig with
      | .error f => ⟨none, s!"prepare: {renderCompileCause f.cause}", ""⟩
      | .ok p =>
        let prep := s!"{repr p.plan}\n{repr p.bindings}\nwarnings={p.warnings.length}"
        let out := match runPreparedDense32 p c.inputs with
          | .error e => s!"run: {repr e.cause}"
          | .ok r =>
            let rows := r.env.toList.map fun (k, t) => (k, t.shape, t.data.toList.map Float32.toBits)
            toString (repr (rows.mergeSort fun a b => decide (a.1 ≤ b.1)))
        ⟨some (toString (repr p.plan.storageKind)), prep, out⟩

/-! ## Corpus -/

def env32 (xs : List (String × List Nat × Array Float32)) : NamedDenseEnv32 :=
  xs.foldl (fun m (n, sh, d) => m.insert n ⟨sh, d⟩) {}

def lA : AxisSpec := ⟨"l", 1, .nat⟩
def jA : AxisSpec := ⟨"j", 2, .real⟩
def kA : AxisSpec := ⟨"k", 3, .real⟩
def oA : AxisSpec := ⟨"o", 4, .real⟩

/-- Linear scan with an external initial state and an external input (clone of
    `ScanDense32Test.linProg`): after the flip `S0`, `X` and the state `S` are undeclared. -/
def linScan : ScheduledProgram :=
  { decls := [ .iter lA 3, .typedTensor .f32 "S0" [], .typedTensor .f32 "X" [lA]
             , .typedTensor .f32 "S" [lA] ]
  , stmts := [.scan "S" [lA]
      [ .assign "S" [.iterAt lA 0]
          { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity } ]
      [ .assign "S" [.iterNext lA]
          { body := { terms := [ { factors := [.read "S" [.axis lA]] }
                               , { factors := [.read "X" [.axis lA]] } ] }
          , nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "S0" (insert "X" (∅ : Finset String))
  , explicitSizes := (({} : HashMap UID Nat).insert lA.uid 3) }

/-- Scatter base inside a scan (clone of `ScanDense32Test.scatProg`). -/
def scatScan : ScheduledProgram :=
  let base : Stmt := .scatter "S" [.affine (.scale 2 jA), .iterAt lA 0]
    { body := { terms := [{ factors := [.read "X" [.axis jA, .axis kA], .read "W" [.axis kA]] }] },
      nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.free oA, .iterNext lA]
    { body := { terms := [{ factors := [.read "S" [.axis oA, .axis lA]] }] }, nonlin := .identity }
  { decls := [.axis jA (some 3), .axis kA none, .axis oA (some 6), .iter lA 2,
              .typedTensor .f32 "X" [jA, kA], .typedTensor .f32 "W" [kA], .typedTensor .f32 "S" [oA, lA]]
  , stmts := [.scan "S" [lA] [base] [recur] false], env := {}
  , extNames := insert "X" (insert "W" ∅)
  , explicitSizes := ((({} : HashMap UID Nat).insert jA.uid 3).insert oA.uid 6).insert lA.uid 2 }

/-- A predicate-only scan next to a real assignment (clone of `ScanDense32Test.predProg`): the
    scan block's table is bool-only, the outer real names are undeclared after the flip. -/
def predScan : ScheduledProgram :=
  { decls := [ .iter lA 3, .predicate "P0" [], .predicate "P" [lA], .typedTensor .f32 "Y" []
             , .typedTensor .f32 "Z" [] ]
  , stmts := [ .plain (.assign "Z" [] { body := { terms := [{ factors := [.read "Y" []] }] }, nonlin := .identity })
             , .scan "P" [lA]
      [ .assign "P" [.iterAt lA 0] { body := { terms := [{ factors := [.read "P0" []] }] }, nonlin := .identity } ]
      [ .assign "P" [.iterNext lA] { body := { terms := [{ factors := [.read "P" [.axis lA]] }] }, nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "P0" (insert "Y" ∅)
  , explicitSizes := (({} : HashMap UID Nat).insert lA.uid 3) }

/-- Probe (a): a predicate-only external `M` feeding a real scan state `S` (undeclared after the
    flip): the only external is Boolean, the state is real scratch built from it. -/
def predExtScan : ScheduledProgram :=
  { decls := [ .iter lA 3, .predicate "M" [], .typedTensor .f32 "S" [lA] ]
  , stmts := [ .scan "S" [lA]
      [ .assign "S" [.iterAt lA 0] { body := { terms := [{ factors := [.read "M" []] }] }, nonlin := .identity } ]
      [ .assign "S" [.iterNext lA] { body := { terms := [{ factors := [.read "S" [.axis lA]] }] }, nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "M" ∅
  , explicitSizes := (({} : HashMap UID Nat).insert lA.uid 3) }

/-- Probe (c): a real scan state with an external real initial value and an external predicate
    mask in the step, `S[l+1] := S[l] · P[l]`. -/
def maskScan : ScheduledProgram :=
  { decls := [ .iter lA 3, .typedTensor .f32 "S0" [], .predicate "P" [lA], .typedTensor .f32 "S" [lA] ]
  , stmts := [ .scan "S" [lA]
      [ .assign "S" [.iterAt lA 0] { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity } ]
      [ .assign "S" [.iterNext lA]
          { body := { terms := [{ factors := [.read "S" [.axis lA], .read "P" [.axis lA]] }] }
          , nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "S0" (insert "P" ∅)
  , explicitSizes := (({} : HashMap UID Nat).insert lA.uid 3) }

def corpus : List Case :=
  [ ⟨"contract", .inl tlprog!{
        axis i : ℕ = 2
        axis j : ℕ = 3
        tensor f32 A(i), B(j), Y(i)
        Y[i] := A[i] · B[j] },
      env32 [("A", [2], #[10, 100]), ("B", [3], #[1, 2, 3])]⟩
  , ⟨"rounding-chain", .inl tlprog!{
        tensor f32 X(), K(), P(), Y()
        P[] := X[] · X[]
        Y[] := P[] + K[] },
      env32 [("X", [], #[4097]), ("K", [], #[-16785408])]⟩
  , ⟨"relu", .inl tlprog!{
        axis i : ℕ = 2
        axis j : ℕ = 2
        tensor f32 W(i, j), x(j), H(i)
        H[i] := relu(W[i, j] · x[j]) },
      env32 [("W", [2, 2], #[1, -1, -2, 1]), ("x", [2], #[1, 1])]⟩
  , ⟨"sigmoid", .inl tlprog!{
        axis i : ℕ = 2
        axis j : ℕ = 2
        tensor f32 W(i, j), x(j), H(i)
        H[i] := sigmoid(W[i, j] · x[j]) },
      env32 [("W", [2, 2], #[1, -1, -2, 1]), ("x", [2], #[1, 1])]⟩
  , ⟨"tanh", .inl tlprog!{
        axis i : ℕ = 2
        axis j : ℕ = 2
        tensor f32 W(i, j), x(j), H(i)
        H[i] := tanh(W[i, j] · x[j]) },
      env32 [("W", [2, 2], #[1, -1, -2, 1]), ("x", [2], #[1, 1])]⟩
  , ⟨"gelu", .inl tlprog!{
        axis i : ℕ = 2
        axis j : ℕ = 2
        tensor f32 W(i, j), x(j), H(i)
        H[i] := gelu(W[i, j] · x[j]) },
      env32 [("W", [2, 2], #[1, -1, -2, 1]), ("x", [2], #[1, 1])]⟩
  , ⟨"exp", .inl tlprog!{
        axis i : ℕ = 2
        tensor f32 A(i), Y(i)
        Y[i] := exp(A[i]) },
      env32 [("A", [2], #[0.5, -1.5])]⟩
  , ⟨"log", .inl tlprog!{
        axis i : ℕ = 2
        tensor f32 A(i), Y(i)
        Y[i] := log(A[i]) },
      env32 [("A", [2], #[0.5, 3])]⟩
  , ⟨"softmax", .inl tlprog!{
        axis q : ℕ = 2
        axis s : ℕ = 3
        tensor f32 A(q, s), Y(q, s)
        Y[q, s.] := softmax(A[q, s]) },
      env32 [("A", [2, 3], #[0.1, 0.2, 0.3, 1, -1, 0.5])]⟩
  , ⟨"normalize-where", .inl tlprog!{
        axis q : ℕ = 2
        axis s : ℕ = 3
        tensor f32 A(q, s), Y(q, s)
        Y[q, s.] := normalize(where s ≠ 0)(A[q, s]) },
      env32 [("A", [2, 3], #[1, 2, 3, 4, 5, 6])]⟩
  , ⟨"scatter", .inl tlprog!{
        axis i : ℕ = 3
        axis o : ℕ = 6
        tensor f32 X(i), Out(o)
        Out[2*i] := X[i] },
      env32 [("X", [3], #[1, 2, 3])]⟩
  , ⟨"pred-mixed", .inl tlprog!{
        axis i : ℕ = 3
        predicate P(i)
        tensor f32 A(i), Y(i)
        Y[i] := A[i] · P[i] },
      env32 [("A", [3], #[1.5, 2.5, 3.5]), ("P", [3], #[1, 0, 1])]⟩
  , ⟨"lin-scan", .inr linScan, env32 [("S0", [], #[16777216]), ("X", [3], #[1, 1, 1])]⟩
  , ⟨"scatter-scan", .inr scatScan,
      env32 [("X", [3, 2], #[16777216, 1, 2, 20, 3, 30]), ("W", [2], #[1, 1])]⟩
  , ⟨"pred-scan", .inr predScan, env32 [("P0", [], #[1]), ("Y", [], #[3])]⟩
  , ⟨"pred-ext-scan", .inr predExtScan, env32 [("M", [], #[1])]⟩
  , ⟨"mask-scan", .inr maskScan, env32 [("S0", [], #[2]), ("P", [3], #[1, 0, 1])]⟩ ]

/-! ## The equivalence -/

run_cmd do
  let mut accepted := 0
  let mut bad : Array String := #[]
  for c in corpus do
    let e := outcome c .explicit
    if e.accepted.isSome then accepted := accepted + 1
    for v in [Variant.plain, .undeclared] do
      let o := outcome c v
      unless o == e do
        bad := bad.push s!"{c.name} [{repr v}]:\n  explicit = {e.accepted} {e.prep.take 300} | {e.out}\n  variant  = {o.accepted} {o.prep.take 300} | {o.out}"
    -- every corpus program is accepted as binary32: a corpus that silently became all-reject
    -- would make the equivalence vacuous
    unless e.accepted == some (toString (repr LeanNCD.StorageKind.float32)) do
      throwError s!"{c.name}: explicit-f32 program not accepted as float32: {e.accepted} {e.prep.take 300}"
    -- ... and runs to exact bits (a `run:` error would make the bit comparison vacuous)
    if e.out.startsWith "run:" then
      throwError s!"{c.name}: explicit-f32 program accepted but its run failed: {e.out}"
  unless bad.isEmpty do
    throwError s!"unannotated ≠ explicit f32 on {bad.size} variant(s):\n{String.intercalate "\n" bad.toList}"
  unless corpus.length == 17 && accepted == 17 do
    throwError s!"corpus drifted: {corpus.length} programs, {accepted} accepted"

end LeanNCD.Eval.Plan.DefaultF32Test

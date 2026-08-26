import LeanNCD.DSL.Pipeline.Lowering
import LeanNCD.DSL.Compile
namespace LeanNCD
-- Masked attention: A[q,s] := softmax(where s≤q)(Q[q,d]·K[s,d]) splits into a linear step
-- (identity nonlin) + a softmax step (carries the mask).
run_cmd do
  let ax (nm : String) : AxisSpec := { name := nm, uid := 1, kind := .real }
  let mask : BoolExpr := .rel .le (.embed (.axis (ax "s"))) (.embed (.axis (ax "q")))
  let attn : Stmt := .assign "A" [ .free (ax "q"), .free (ax "s") ]
    { body := { terms := [ { factors := [ .read "Q" [.axis (ax "q"), .axis (ax "d")],
                                            .read "K" [.axis (ax "s"), .axis (ax "d")] ] } ] },
      nonlin := .axiswise .softmax (some mask) }
  let sp : ScanProgram :=
    { decls := [], stmts := [ .plain attn ], env := {}, extNames := ∅ }
  match splitNonlins sp |>.run 0 with
  | .ok lp _ =>
      let stmts := lp.stmts.filterMap (fun | .plain s => some s | .scan .. => none | .scanPre .. => none)
      -- exactly two stmts: a linear (identity) and a softmax-carrying step
      unless stmts.length == 2 do throwError s!"expected 2 stmts after split, got {stmts.length}"
      let nlins := stmts.map (fun | .assign _ _ r => r.nonlin | .scatter _ _ r _ => r.nonlin | .recurMorphism .. => .identity)
      unless nlins.any (· == .identity) do throwError "missing linear (identity) step"
      unless nlins.any (fun n => match n with | .axiswise .softmax (some _) => true | _ => false) do
        throwError "missing masked-softmax step"
  | .error e _ => throwError s!"splitNonlins errored: {repr e}"

-- A plain identity assign is unchanged (one stmt out).
run_cmd do
  let ax (nm : String) : AxisSpec := { name := nm, uid := 1, kind := .real }
  let mm : Stmt := .assign "Y" [ .free (ax "i") ]
    { body := { terms := [ { factors := [ .read "X" [.axis (ax "i")] ] } ] }, nonlin := .identity }
  let sp : ScanProgram :=
    { decls := [], stmts := [ .plain mm ], env := {}, extNames := ∅ }
  match splitNonlins sp |>.run 0 with
  | .ok lp _ => unless lp.stmts.length == 1 do throwError "identity assign should not split"
  | .error e _ => throwError s!"errored: {repr e}"

-- No DCE for unread top-level statements (KG-multiout fix): `schedule` used to eliminate any
-- produced-but-unread, non-tail statement as "dead", which is indistinguishable from a
-- legitimate secondary output using only read/unread status — this silently dropped intended
-- multi-output programs. `Second` (produced, never read, not the tail statement) now survives
-- alongside `Y` (the tail output) and `T` (Y's dependency), same as every other statement.
run_cmd do
  let ax (nm : String) : AxisSpec := { name := nm, uid := 1, kind := .real }
  let rd (nm : String) : RHSExpr :=
    { body := { terms := [ { factors := [ .read nm [ .axis (ax "i") ] ] } ] }, nonlin := .identity }
  let tStmt      : ScanStmt := .plain (.assign "T" [ .free (ax "i") ] (rd "X"))      -- T := X
  let secondStmt : ScanStmt := .plain (.assign "Second" [ .free (ax "i") ] (rd "X")) -- Second := X (independent output, unread)
  let yStmt      : ScanStmt := .plain (.assign "Y" [ .free (ax "i") ] (rd "T"))      -- Y := T (tail output)
  let lp : LinearProgram := { decls := [], stmts := [tStmt, secondStmt, yStmt], env := {}, extNames := ∅ }
  match schedule lp |>.run 0 with
  | .ok sp _ =>
      let names := sp.stmts.flatMap ScanStmt.writes
      unless names.contains "Y" && names.contains "T" && names.contains "Second" do
        throwError s!"Y, T, and Second must all survive; got {names}"
  | .error e _ => throwError s!"schedule errored: {repr e}"

-- Matmul Y[i,j] := W[i,k]·X[k,j]: W,X external ⇒ nExternal=2; one step; k contracted ⇒
-- exactly one .tiled slot in the output weave; W,X reindexings present.
run_cmd do
  let ax (nm : String) (u : Nat) : AxisSpec := { name := nm, uid := u, kind := .real }
  let i := ax "i" 1; let j := ax "j" 2; let k := ax "k" 3
  let mm : Stmt := .assign "Y" [ .free i, .free j ]
    { body := { terms := [ { factors := [ .read "W" [.axis i, .axis k], .read "X" [.axis k, .axis j] ] } ] },
      nonlin := .identity }
  let sp : ScheduledProgram := { decls := [], stmts := [ .plain mm ], env := {}, extNames := (insert "W" (insert "X" (∅ : Finset String))), explicitSizes := {} }
  match route sp |>.run 0 with
  | .ok tc _ =>
      unless tc.nExternal == 2 do throwError s!"nExternal should be 2, got {tc.nExternal}"
      unless tc.steps.length == 1 do throwError s!"expected 1 step, got {tc.steps.length}"
      let step := tc.steps.head!
      -- output weave: i,j fixed, k tiled ⇒ exactly one tiled
      let nTiled := step.outputWeaves.head!.filter (fun | .tiled => true | .fixed _ => false) |>.length
      unless nTiled == 1 do throwError s!"expected exactly one contracted (tiled) axis, got {nTiled}"
      unless step.reindexings.length == 2 do throwError s!"expected 2 input reindexings, got {step.reindexings.length}"
      -- both inputs route to externals
      unless tc.routing.head!.all (fun w => match w with | .external _ => true | .internal .. => false) do throwError "matmul inputs should be external"
  | .error e _ => throwError s!"route errored: {repr e}"

-- Strided read: Y[i] := X[2*i] ⇒ the X reindexing row has coefficient 2.
run_cmd do
  let ax (nm : String) (u : Nat) : AxisSpec := { name := nm, uid := u, kind := .real }
  let i := ax "i" 1
  let conv : Stmt := .assign "Y" [ .free i ]
    { body := { terms := [ { factors := [ .read "X" [ .scale 2 i ] ] } ] }, nonlin := .identity }
  let sp : ScheduledProgram := { decls := [], stmts := [ .plain conv ], env := {}, extNames := (insert "X" (∅ : Finset String)), explicitSizes := {} }
  match route sp |>.run 0 with
  | .ok tc _ =>
      let sm := tc.steps.head!.reindexings.head!
      unless sm.coeffs == [[2]] do throwError s!"expected strided coeff [[2]], got {sm.coeffs}"
  | .error e _ => throwError s!"route errored: {repr e}"

-- Unresolved read: `Ghost` is neither produced by a step nor declared external ⇒ `route` must
-- FAIL LOUD with `undeclaredName`, not silently route it to external slot 0 (the former
-- `(extIndex …).getD 0` fallback, which masked upstream dataflow errors).
run_cmd do
  let ax (nm : String) (u : Nat) : AxisSpec := { name := nm, uid := u, kind := .real }
  let i := ax "i" 1
  let s : Stmt := .assign "Y" [ .free i ]
    { body := { terms := [ { factors := [ .read "Ghost" [ .axis i ] ] } ] }, nonlin := .identity }
  let sp : ScheduledProgram := { decls := [], stmts := [ .plain s ], env := {}, extNames := (∅ : Finset String), explicitSizes := {} }
  match route sp |>.run 0 with
  | .ok tc _ => throwError s!"expected route to reject unresolved read, got {tc.steps.length} step(s)"
  | .error (.undeclaredName nm) _ => unless nm == "Ghost" do throwError s!"wrong undeclared name: {nm}"
  | .error e _ => throwError s!"expected undeclaredName, got {repr e}"

-- topoSort: out-of-order source (Y reads H; H is written by a LATER stmt) must be
-- reordered so H precedes Y after schedule+route, i.e. every internal wire in routing
-- satisfies producer-step-index < consumer-step-index.
-- Source order: [yStmt (reads H), hStmt (writes H, reads X ext)]. Y is NOT last, so
-- we make Y the output by adding a sink Sink[i,j] := Y[i,j] at the end.
-- After schedule: live = {Sink, Y, H}; non-topological order without sort: [Y, H, Sink].
-- After topoSort: [H, Y, Sink]. routing[1] should contain internal 0 0 (j=0 < i=1).
run_cmd do
  let ax (nm : String) (u : Nat) : AxisSpec := { name := nm, uid := u, kind := .real }
  let i := ax "i" 1; let j := ax "j" 2; let k := ax "k" 3; let d := ax "d" 4
  let mkRd (nm : String) (es : List IdxExpr) : RHSExpr :=
    { body := { terms := [ { factors := [ .read nm es ] } ] }, nonlin := .identity }
  let mkRd2 (nm1 : String) (es1 : List IdxExpr) (nm2 : String) (es2 : List IdxExpr) : RHSExpr :=
    { body := { terms := [ { factors := [ .read nm1 es1, .read nm2 es2 ] } ] }, nonlin := .pointwise .relu }
  -- Y[i,j] := relu(W2[j,k] · H[i,k])   -- consumer of H
  let yStmt : ScanStmt := .plain (.assign "Y" [.free i, .free j]
    (mkRd2 "W2" [.axis j, .axis k] "H" [.axis i, .axis k]))
  -- H[i,k] := W1[k,d] · X[i,d]         -- producer of H (reads only externals)
  let hStmt : ScanStmt := .plain (.assign "H" [.free i, .free k]
    { body := { terms := [ { factors := [ .read "W1" [.axis k, .axis d], .read "X" [.axis i, .axis d] ] } ] }, nonlin := .identity })
  -- Sink[i,j] := Y[i,j]                 -- output (reads Y, keeps Y+H alive via DCE)
  let sinkStmt : ScanStmt := .plain (.assign "Sink" [.free i, .free j] (mkRd "Y" [.axis i, .axis j]))
  -- Source order: [yStmt, hStmt, sinkStmt] -- NOT topological (Y before H)
  let exts : Finset String := insert "W2" (insert "W1" (insert "X" ∅))
  let lp : LinearProgram := { decls := [], stmts := [yStmt, hStmt, sinkStmt], env := {}, extNames := exts }
  match (do let sp ← schedule lp; route sp) |>.run 0 with
  | .ok tc _ =>
      -- After topoSort, every internal wire internal j _ at step i must have j < i.
      let bad := tc.routing.zipIdx.filter fun p =>
        p.1.any fun w => match w with | .internal j _ => decide (j ≥ p.2) | .external _ => false
      unless bad.isEmpty do
        throwError s!"routing has producer-after-consumer wires: {repr (bad.map (·.1))}"
  | .error e _ => throwError s!"schedule/route errored: {repr e}"

-- Cyclic dataflow must be rejected fail-loud (Spike 1h), not silently source-ordered.
run_cmd do
  let ax (nm : String) : AxisSpec := { name := nm, uid := 1, kind := .real }
  let rd (nm : String) : RHSExpr :=
    { body := { terms := [ { factors := [ .read nm [ .axis (ax "i") ] ] } ] }, nonlin := .identity }
  let aStmt : ScanStmt := .plain (.assign "A" [ .free (ax "i") ] (rd "B"))  -- A := B
  let bStmt : ScanStmt := .plain (.assign "B" [ .free (ax "i") ] (rd "A"))  -- B := A
  let lp : LinearProgram := { decls := [], stmts := [aStmt, bStmt], env := {}, extNames := ∅ }
  match schedule lp |>.run 0 with
  | .ok _ _ => throwError "expected cyclicDataflow, got .ok (schedule silently source-ordered a cycle)"
  | .error (.cyclicDataflow _) _ => pure ()
  | .error e _ => throwError s!"expected cyclicDataflow, got: {repr e}"

-- AGG1/AGG2 (audit finding C): `splitStmt` must thread `agg` onto the LINEAR step and leave the
-- nonlinear step at `.sum`.  The linear step is the one that actually contracts, so dropping `agg`
-- there silently substitutes `RHSExpr`'s `.sum` default for a `max`/`min` aggregation — an EVAL bug
-- (the evaluator reads `rhs.agg` off post-split stmts), not merely a routing-label one.
--
-- This state is NOT constructible from surface syntax: `tl_nonlin (…)` and `tl_agg (…)` are mutually
-- exclusive `tl_rhs` alternatives, so `relu(maxreduce(…))` is a parse error.  Hence this test builds
-- the `Stmt` programmatically — without it nothing guards the fix.
run_cmd do
  let ax (nm : String) : AxisSpec := { name := nm, uid := 1, kind := .real }
  -- Y[i] := relu(maxreduce over j of P[i,j])  — non-identity nonlin AND non-sum agg together.
  let s : Stmt := .assign "Y" [ .free (ax "i") ]
    { body := { terms := [ { factors := [ .read "P" [ .axis (ax "i"), .axis (ax "j") ] ] } ] },
      nonlin := .pointwise .relu, agg := .max }
  let sp : ScanProgram := { decls := [], stmts := [ .plain s ], env := {}, extNames := ∅ }
  match splitNonlins sp |>.run 0 with
  | .ok lp _ =>
      let stmts := lp.stmts.filterMap (fun | .plain t => some t | .scan .. => none | .scanPre .. => none)
      unless stmts.length == 2 do throwError s!"AGG: expected 2 stmts after split, got {stmts.length}"
      let pairs := stmts.map (fun | .assign _ _ r => (r.nonlin, r.agg) | .scatter _ _ r _ => (r.nonlin, r.agg) | .recurMorphism .. => (Nonlin.identity, AggOp.sum))
      -- AGG1: the linear (identity-nonlin) step must carry the original `.max`.
      unless pairs.any (fun (n, a) => n == .identity && a == .max) do
        throwError s!"AGG1: linear step lost agg (expected .max); got {repr pairs}"
      -- AGG2: the relu step contracts nothing, so it must be `.sum`, not an inherited `.max`.
      unless pairs.any (fun (n, a) => n == .pointwise .relu && a == .sum) do
        throwError s!"AGG2: nonlin step should be .sum; got {repr pairs}"
  | .error e _ => throwError s!"AGG: splitNonlins errored: {repr e}"

-- FREENORM1/FREENORM2 (Thread 4 Task 3 fix, in `splitStmt`): the split-off LINEAR step of a
-- `.freeNorm`-marked axiswise statement must have that marker degraded to plain `.free` — the
-- marker names which axis the NONLIN step reduces over, and on the `.identity` linear step (which
-- reduces nothing) it is meaningless; undegraded, it would fire
-- `NonlinCompileError.unmarkedReductionAxis` at the Plan compiler on every axiswise statement's
-- linear half, a marker the USER never wrote. The nonlin step itself must keep the ORIGINAL marker
-- unchanged — it is the statement `resolveNonlinAxis` needs to see it on. This pins the fix at the
-- layer it actually lives in (`splitStmt`), one phase upstream of where
-- `NonlinCompileTest.lean`/`NonlinCheckTest.lean` currently exercise it. See `Lowering.lean`'s
-- `splitStmt` comment and `LeanNCD/DSL/AGENTS.md`'s Pitfalls entry.
run_cmd do
  let q : AxisSpec := { name := "q", uid := 1, kind := .real }
  let s : AxisSpec := { name := "s", uid := 2, kind := .real }
  -- Y[q, s.] := softmax(A[q, s])  -- axiswise nonlin, freeNorm-marked reduction axis `s`.
  let stmt : Stmt := .assign "Y" [ .free q, .freeNorm s ]
    { body := { terms := [ { factors := [ .read "A" [.axis q, .axis s] ] } ] },
      nonlin := .axiswise .softmax none }
  let sp : ScanProgram := { decls := [], stmts := [ .plain stmt ], env := {}, extNames := ∅ }
  let slotsOf : Stmt → List LHSSlot :=
    fun | .assign _ slots _ => slots | .scatter _ slots _ _ => slots | .recurMorphism .. => []
  let isIdentity : Stmt → Bool :=
    fun | .assign _ _ r => (match r.nonlin with | .identity => true | _ => false)
        | .scatter _ _ r _ => (match r.nonlin with | .identity => true | _ => false)
        | .recurMorphism .. => true
  let hasFreeNorm : List LHSSlot → Bool :=
    fun slots => slots.any (fun sl => match sl with | .freeNorm _ => true | _ => false)
  match splitNonlins sp |>.run 0 with
  | .ok lp _ =>
      let stmts := lp.stmts.filterMap (fun | .plain t => some t | .scan .. => none | .scanPre .. => none)
      unless stmts.length == 2 do
        throwError s!"FREENORM: expected 2 stmts after split, got {stmts.length}"
      match stmts.find? isIdentity, stmts.find? (fun t => !isIdentity t) with
      | some lin, some nl =>
          -- FREENORM1: the linear step's slots carry no `.freeNorm` marker (degraded to `.free`).
          unless !(hasFreeNorm (slotsOf lin)) do
            throwError s!"FREENORM1: linear step still carries a freeNorm marker: {repr (slotsOf lin)}"
          -- FREENORM2: the nonlin step still carries the ORIGINAL freeNorm marker.
          unless hasFreeNorm (slotsOf nl) do
            throwError s!"FREENORM2: nonlin step lost its freeNorm marker: {repr (slotsOf nl)}"
      | _, _ => throwError s!"FREENORM: could not find both a linear and a nonlin step: {repr stmts}"
  | .error e _ => throwError s!"FREENORM: splitNonlins errored: {repr e}"

-- PRODUCERSLOTS (Task 2, logical-schedule flip): `splitStmt` (regression leg, above) and
-- `RouteFragments.physicalizeOne` (production route boundary) both degrade a `.freeNorm` marker on
-- their split-off LINEAR/producer step via the SAME shared `Ast.producerSlots` — route equality
-- cannot see the two call sites drift (`.free`/`.freeNorm` yield identical `slotWeave` axes), so
-- this fixture compares their producers' slot lists directly. Runs both on the identical statement
-- used by FREENORM1/2 above.
run_cmd do
  let q : AxisSpec := { name := "q", uid := 1, kind := .real }
  let s : AxisSpec := { name := "s", uid := 2, kind := .real }
  let stmt : Stmt := .assign "Y" [ .free q, .freeNorm s ]
    { body := { terms := [ { factors := [ .read "A" [.axis q, .axis s] ] } ] },
      nonlin := .axiswise .softmax none }
  let slotsOf : Stmt → List LHSSlot :=
    fun | .assign _ slots _ => slots | .scatter _ slots _ _ => slots | .recurMorphism .. => []
  let isIdentity : Stmt → Bool :=
    fun | .assign _ _ r => (match r.nonlin with | .identity => true | _ => false)
        | .scatter _ _ r _ => (match r.nonlin with | .identity => true | _ => false)
        | .recurMorphism .. => true
  match splitStmt stmt |>.run 0 with
  | .error e _ => throwError s!"PRODUCERSLOTS: splitStmt errored: {repr e}"
  | .ok splitStmts _ =>
      match splitStmts.find? isIdentity with
      | none => throwError s!"PRODUCERSLOTS: splitStmt produced no linear step: {repr splitStmts}"
      | some regressionProducer =>
          match physicalizeOne [] 0 0 (.plain stmt) with
          | .error e => throwError s!"PRODUCERSLOTS: physicalizeOne errored: {repr e}"
          | .ok (physStmts, _) =>
              match physStmts.find? (fun sc => match sc with | .plain t => isIdentity t | _ => false) with
              | some (.plain physProducer) =>
                  unless slotsOf regressionProducer == slotsOf physProducer do
                    throwError s!"PRODUCERSLOTS: producer slots diverged — \
splitStmt={repr (slotsOf regressionProducer)} physicalizeOne={repr (slotsOf physProducer)}"
              | _ => throwError s!"PRODUCERSLOTS: physicalizeOne produced no linear step \
(got {physStmts.length} stmts)"

end LeanNCD

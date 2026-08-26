import LeanNCD.DSL.Compile

/-!
# Route-fragment diagnostic differential seed

Exactly 19 compile cases, two direct route-domain cases, and the plan's 3×3 nonzero-state
composition observations. `old` is today's split pipeline. `proposed` schedules logical statements
and applies a local terminal physicalizer. This seed intentionally does not alter production imports.
-/

namespace RouteFragmentDiagnosticSeed

open LeanNCD Std

def degrade : LHSSlot → LHSSlot
  | .freeNorm a => .free a
  | s => s

def privateName (maxLen ordinal : Nat) : String :=
  String.ofList (List.replicate (maxLen + ordinal + 1) '#')

def declName? : Decl → Option String
  | .tensor n _ | .predicate n _ | .linear n _ _ => some n
  | .axis .. | .iter .. => none

def allNames (sp : ScheduledProgram) : List String :=
  (sp.decls.filterMap declName? ++ sp.stmts.flatMap ScanStmt.writes ++
    sp.stmts.flatMap ScanStmt.reads).eraseDups

def physicalizePlain (maxLen ordinal : Nat) : Stmt → List ScanStmt
  | s@(.assign name slots rhs) =>
      if rhs.nonlin == Nonlin.identity then [.plain s] else
        let internal := privateName maxLen ordinal
        [.plain (.assign internal (slots.map degrade)
          { body := rhs.body, nonlin := .identity, agg := rhs.agg }),
         .plain (.assign name slots
          { body := { terms := [{ factors := [
              .read internal (slots.filterMap LHSSlot.toReadIdx) ] }] },
            nonlin := rhs.nonlin, agg := .sum })]
  | s => [.plain s]

def physicalize (sp : ScheduledProgram) : ScheduledProgram :=
  let maxLen := (allNames sp).foldl (fun n s => max n s.length) 0
  let stmts := sp.stmts.zipIdx.flatMap fun (stmt, ordinal) =>
    match stmt with
    | .plain s => physicalizePlain maxLen ordinal s
    | .scan .. | .scanPre .. => [stmt]
  { sp with stmts }

def logicalScheduleWithCheckOrder (swapReadRankAndDtype : Bool) (p : TLProgram) :
    FreshM ScheduledProgram := do
  let a ← assignUIDs p
  let b ← resolveDecls a
  let b ← reclassifyIterSlots b
  let b ← if swapReadRankAndDtype then do
      let b ← checkDtypes b
      checkReadRanks b
    else do
      let b ← checkReadRanks b
      checkDtypes b
  let b ← checkScatterNonlin b
  let b ← checkScatterNoScan b
  let d ← lowerArith b
  let e ← finalizeScans d
  schedule { decls := e.decls, stmts := e.stmts, env := e.env, extNames := e.extNames }

def logicalSchedule (p : TLProgram) : FreshM ScheduledProgram :=
  logicalScheduleWithCheckOrder false p

-- Disabled-by-default production-mutation stand-ins. Toggling the first changes case 4's
-- precedence; toggling the second breaks all successful public-composition observations.
def enableCheckOrderMutation : Bool := false
def enableExternalArityMutation : Bool := false

def mutateExternalArity (enabled : Bool) (tc : ThreadedComposed) : ThreadedComposed :=
  if enabled then { tc with nExternal := tc.nExternal + 1 } else tc

def proposedCompile (p : TLProgram) : FreshM ThreadedComposed := do
  let logical ← logicalScheduleWithCheckOrder enableCheckOrderMutation p
  let routed ← route (physicalize logical)
  pure (mutateExternalArity enableExternalArityMutation routed)

def expectSame (old new : EStateM.Result CompileError Nat ThreadedComposed)
    (oldState newState : Nat) : Bool :=
  match old, new with
  | .ok a sa, .ok b sb => a == b && sa == oldState && sb == newState
  | .error a sa, .error b sb => a == b && sa == oldState && sb == newState
  | _, _ => false

def expectErrors (old new : EStateM.Result CompileError Nat ThreadedComposed)
    (error : CompileError) (oldState newState : Nat) : Bool :=
  match old, new with
  | .error a sa, .error b sb =>
      a == error && b == error && sa == oldState && sb == newState
  | _, _ => false

def ax (name : String) (kind := AxisKind.real) : AxisSpec := { name, uid := 0, kind }

def read1 (name : String) (a : AxisSpec) : RHSExpr :=
  { body := { terms := [{ factors := [.read name [.axis a]] }] }, nonlin := .identity }

def case01 : TLProgram := {
  decls := [], stmts := [.assign "Y" [.free (ax "i")] (read1 "Ghost" (ax "i"))] }

def case02 : TLProgram := {
  decls := [.tensor "W" [ax "i", ax "k"]]
  stmts := [.assign "Y" [.free (ax "i")] (read1 "W" (ax "i"))] }

def case03 : TLProgram := tlprog!{
  A[i] := X[i]
  B[i] := X[i, j]
}

def case04 : TLProgram := {
  decls := [
    .tensor "W" [ax "i", ax "k"],
    .axis (ax "m" .nat) none
  ]
  stmts := [.assign "Y" [.freeNorm (ax "m" .nat)]
    { body := { terms := [{ factors := [.read "W" [.axis (ax "m" .nat)]] }] },
      nonlin := .axiswise .softmax none }] }

def case05 : TLProgram := tlprog!{
  axis m : ℕ
  Y[m.] := softmax(X[m])
}

def case06 : TLProgram := {
  decls := [.axis (ax "m" .nat) none]
  stmts := [.assign "Y" [.freeNorm (ax "m" .nat)]
    { body := { terms := [{ factors := [.read "X" [.axis (ax "m" .nat)]] }] },
      nonlin := .axiswise .softmax none }] }

def case07 : TLProgram := {
  decls := []
  stmts := [.assign "H" [.iterAt (ax "l" .real) 0]
    { body := { terms := [] }, nonlin := .identity }] }

def case08 : TLProgram := tlprog!{
  predicate P(i)
  P[i] := relu(X[i])
}
def case09 : TLProgram := tlprog!{
  predicate P(i)
  P[i] := maxreduce(X[i])
}
def case10 : TLProgram := tlprog!{ Out[2 * i] := relu(X[i]) }
def case11 : TLProgram := tlprog!{
  iter l = 3
  Out[2 * i, l + 1] := X[i, l]
}
def case12 : TLProgram := tlprog!{
  tensor X(j)
  S[j, 0] := X[j]
  S[j, l + 1] := S[j, l]
}
def case13 : TLProgram := tlprog!{
  iter l = 3
  S[j, 0] := X[j, 0]
  S[j, l + 1] := S[j, l] + X[j, l + 1]
}
def case14 : TLProgram := tlprog!{
  iter l = 3
  h[j, 0] := h0[j]
  h[j, l + 1] := A[j, k] · h[k, l] + B[j] · u[l]
  y[j, l] := C[j, k] · h[k, l]
}
def case15 : TLProgram := tlprog!{
  A[i] := B[i]
  B[i] := A[i]
}
def case16 : TLProgram := tlprog!{
  A[i] := relu(B[i])
  B[i] := relu(A[i])
}
def case17 : TLProgram := tlprog!{
  A[q, s.] := softmax(where s ≤ q)(Q[q, d] · K[s, d])
}
def case18 : TLProgram := {
  decls := []
  stmts := [.assign "################" [.free (ax "i")]
    { body := { terms := [{ factors := [.read "X" [.axis (ax "i")]] }] },
      nonlin := .pointwise .relu }] }

def case19 : TLProgram := {
  decls := []
  stmts := [
    .assign "%nl2" [.free (ax "i")] (read1 "X" (ax "i")),
    .assign "Y" [.free (ax "i")]
      { body := { terms := [{ factors := [.read "%nl2" [.axis (ax "i")]] }] },
        nonlin := .pointwise .relu }
  ] }

def old (p : TLProgram) (start := 0) := p.compile.run start
def proposed (p : TLProgram) (start := 0) := proposedCompile p |>.run start

-- The 14 common failures/successes before or independent of split minting.
#guard expectSame (old case01) (proposed case01) 2 2
#guard expectErrors (old case02) (proposed case02) (.rankMismatch "W" 2 1) 3 3
#guard expectErrors (old case03) (proposed case03) (.rankMismatch "X" 1 2) 3 3
#guard expectErrors (old case04) (proposed case04) (.rankMismatch "W" 2 1) 4 4
#guard expectErrors (old case06) (proposed case06) (.normAxisNotReal "m") 2 2
#guard expectErrors (old case07) (proposed case07) (.iterAxisNotNat "l") 2 2
#guard expectErrors (old case08) (proposed case08) (.predicateNonlin "P") 2 2
#guard expectErrors (old case09) (proposed case09) (.predicateAgg "P") 2 2
#guard expectErrors (old case10) (proposed case10) (.unsupportedNonlinScatter "Out") 2 2
#guard expectErrors (old case11) (proposed case11) (.scatterInScan "Out") 3 3
#guard expectErrors (old case12) (proposed case12) (.scanAxisNotIter "l") 4 4
#guard expectErrors (old case13) (proposed case13) (.causalityViolation "S") 4 4
#guard expectErrors (old case14) (proposed case14) (.scanProjectionUnsupported "y") 5 5
#guard expectErrors (old case15) (proposed case15)
  (.cyclicDataflow "schedule: cyclic dataflow") 2 2

-- Three successful programs have equal categorical values and exactly one removed split mint.
#guard expectSame (old case05) (proposed case05) 3 2
#guard expectSame (old case17) (proposed case17) 5 4
#guard expectSame (old case18) (proposed case18) 3 2

-- Two nonlinear cycle mints disappear; the collision bug changes old rejection to new acceptance.
#guard expectErrors (old case16) (proposed case16)
  (.cyclicDataflow "schedule: cyclic dataflow") 4 2
#guard
  match old case19, proposed case19 with
  | .error (.cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)") 3, .ok _ 2 => true
  | _, _ => false

-- Two direct route-domain cases, both starting at state 7.
def routeUndeclared : ScheduledProgram := {
  decls := [], env := {}, extNames := ∅, explicitSizes := {}
  stmts := [.plain (.assign "Y" [.free (ax "i")] (read1 "Ghost" (ax "i")))] }

def routeUnusedExternal : ScheduledProgram := {
  decls := [], env := {}, extNames := {"X", "Unused"}, explicitSizes := {}
  stmts := [.plain (.assign "Y" [.free (ax "i")] (read1 "X" (ax "i")))] }

#guard
  match route routeUndeclared |>.run 7 with
  | .error (.undeclaredName "Ghost") 7 => true
  | _ => false
#guard
  match route routeUnusedExternal |>.run 7 with
  | .error (.shapeMismatch
      "route: wellFormedDom failed (unreferenced external slot or read-rank mismatch)"
      "wellFormedDom") 7 => true
  | _ => false

-- Public-composition seed: cases 1, 2, and 16 at zero and two nonzero starting states.
-- This deliberately uses the unmutated `logicalSchedule` helper, whereas `proposedCompile`
-- spells the future public entry point separately above; the arity/check-order toggles therefore
-- make these checks fail rather than mutating both sides in lockstep.
def proposedComposition (p : TLProgram) : FreshM ThreadedComposed := do
  let logical ← logicalSchedule p
  route (physicalize logical)

def resultExact
    (a b : EStateM.Result CompileError Nat ThreadedComposed) : Bool :=
  match a, b with
  | .ok x sx, .ok y sy => x == y && sx == sy
  | .error x sx, .error y sy => x == y && sx == sy
  | _, _ => false

def compositionExact (p : TLProgram) (start : Nat) : Bool :=
  resultExact ((proposedCompile p).run start) ((proposedComposition p).run start)

#guard compositionExact case01 0
#guard compositionExact case01 7
#guard compositionExact case01 41
#guard compositionExact case02 0
#guard compositionExact case02 7
#guard compositionExact case02 41
#guard compositionExact case16 0
#guard compositionExact case16 7
#guard compositionExact case16 41

#guard mutateExternalArity false default == (default : ThreadedComposed)

end RouteFragmentDiagnosticSeed

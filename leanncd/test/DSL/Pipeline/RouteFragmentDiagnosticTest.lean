-- test/DSL/Pipeline/RouteFragmentDiagnosticTest.lean
import LeanNCD.DSL.Compile

/-!
# Route-fragment diagnostic differential (Task 3 of `nonlinearity_split_pair_direct_lowering.md`)

The §2.1 flip moved the nonlinearity split out of the scheduling chain and into the `route`
boundary (`physicalizeForRoute`). This file is the **differential**: it pins that the flip changed
*no* common-domain diagnostic, and that every final-`FreshM`-state delta is exactly the split mints
the flip removed.

Every observation goes through a **production** entry point — `TLProgram.compile`,
`TLProgram.compileToScheduled`, public `route`. There is deliberately no local scheduler,
physicalizer, or compiler here: a passing test that exercised a cloned pipeline would not be a
production regression. (The donor
`papers/implementation_seeds/nonlinearity_route_fragments/fixtures/RouteFragmentDiagnosticSeed.lean`
compares its own `old`/`proposed` legs; this file compares production against *recorded constants*,
which is what survives the donor's `old` leg going stale.)

## The 19 compile observations

Column "old" is the pre-flip `splitNonlins → schedule → route` state recorded by the donor;
"new" is what production produces today (measured, not inherited). `Δ` is the removed split mints.

| Case | Outcome | old | new | Δ | Note |
|---|---|---|---|---|---|
| 1  | success                                    | @2 | @2 | 0 | |
| 2  | `rankMismatch "W" 2 1`                     | @3 | @3 | 0 | pre-split failure |
| 3  | `rankMismatch "X" 1 2`                     | @3 | @3 | 0 | pre-split failure |
| 4  | `rankMismatch "W" 2 1`                     | @4 | @4 | 0 | **dual defect**: rank wins over `normAxisNotReal` |
| 5  | success                                    | @3 | @2 | 1 | one nonlinear stmt |
| 6  | `normAxisNotReal "m"`                      | @2 | @2 | 0 | pre-split failure |
| 7  | `iterAxisNotNat "l"`                       | @2 | @2 | 0 | pre-split failure |
| 8  | `predicateNonlin "P"`                      | @2 | @2 | 0 | pre-split failure |
| 9  | `predicateAgg "P"`                         | @2 | @2 | 0 | pre-split failure |
| 10 | `unsupportedNonlinScatter "Out"`           | @2 | @2 | 0 | pre-split failure |
| 11 | `scatterInScan "Out"`                      | @3 | @3 | 0 | pre-split failure |
| 12 | `scanAxisNotIter "l"`                      | @4 | @4 | 0 | pre-split failure |
| 13 | `causalityViolation "S"`                   | @4 | @4 | 0 | pre-split failure |
| 14 | `scanProjectionUnsupported "y"`            | @5 | @5 | 0 | pre-split failure |
| 15 | `cyclicDataflow "schedule: cyclic dataflow"`| @2 | @2 | 0 | identity cycle |
| 16 | `cyclicDataflow "schedule: cyclic dataflow"`| @4 | @2 | 2 | two nonlinear stmts; see below |
| 17 | success                                    | @5 | @4 | 1 | one nonlinear stmt |
| 18 | success                                    | @3 | @2 | 1 | one nonlinear stmt |
| 19 | old: `cyclicDataflow` / new: success            | @3 | @2 | 1 | intentional fix; see below |

### Case 16 — same constructor *and* same payload string

The plan anticipated that case 16's message might move from `schedule:` to
`physicalizeForRoute: physical fragment topology failed`, because an intermediate revision of
`physicalizeForRoute` carried its own topology check that ran before `routeCore`'s. It does **not**:
the cycle `A := relu(B); B := relu(A)` is a cycle *between the logical statements*, so `schedule`
rejects it before `route` is ever reached, and the payload is byte-identical to the pre-flip one.
The only change is the state: 4 → 2, exactly the two split mints the two ReLUs no longer spend. The
message-string change is therefore unobserved on the whole 19-case corpus — recorded here so a
future reader does not go looking for it. (That duplicate check has since been removed, so the
string no longer exists anywhere; the route-domain section below pins `routeCore`'s original message
for the hand-built cyclic schedules that *were* affected.)

### Case 19 — old rejected, new accepts (intentional bug fix, not a regression)

The source writes to a name, `%nl2`, that collides with the *old* split phase's generated-name
scheme. Pre-flip, the split minted its own `%nl2` for the ReLU on the next statement, the two
collapsed into one node, and the resulting self-edge was reported as
`cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)"` @3 — a source program rejected
for a name the compiler itself chose. Post-flip the internal name is minted inside
`physicalizeForRoute` from the *program's own* name inventory, so it cannot collide, and the program
compiles (@2, three physical steps). Accepting this is the point.
-/

namespace LeanNCD.RouteFragmentDiagnostic

open Std

private def ax (name : String) (kind := AxisKind.real) : AxisSpec := { name, uid := 0, kind }

private def read1 (name : String) (a : AxisSpec) : RHSExpr :=
  { body := { terms := [{ factors := [.read name [.axis a]] }] }, nonlin := .identity }

/-! ## The 19 cases (donor map in `fixtures/README.md`) -/

private def case01 : TLProgram := {
  decls := [], stmts := [.assign "Y" [.free (ax "i")] (read1 "Ghost" (ax "i"))] }

private def case02 : TLProgram := {
  decls := [.tensor "W" [ax "i", ax "k"]]
  stmts := [.assign "Y" [.free (ax "i")] (read1 "W" (ax "i"))] }

private def case03 : TLProgram := tlprog!{
  A[i] := X[i]
  B[i] := X[i, j]
}

/-- Dual defect: `W` is read at rank 1 against a rank-2 declaration, AND the `freeNorm` slot uses a
    `nat`-kinded axis. `checkReadRanks` runs before `checkDtypes`, so the rank error must win. -/
private def case04 : TLProgram := {
  decls := [
    .tensor "W" [ax "i", ax "k"],
    .axis (ax "m" .nat) none
  ]
  stmts := [.assign "Y" [.freeNorm (ax "m" .nat)]
    { body := { terms := [{ factors := [.read "W" [.axis (ax "m" .nat)]] }] },
      nonlin := .axiswise .softmax none }] }

private def case05 : TLProgram := tlprog!{
  axis m : ℕ
  Y[m.] := softmax(X[m])
}

private def case06 : TLProgram := {
  decls := [.axis (ax "m" .nat) none]
  stmts := [.assign "Y" [.freeNorm (ax "m" .nat)]
    { body := { terms := [{ factors := [.read "X" [.axis (ax "m" .nat)]] }] },
      nonlin := .axiswise .softmax none }] }

private def case07 : TLProgram := {
  decls := []
  stmts := [.assign "H" [.iterAt (ax "l" .real) 0]
    { body := { terms := [] }, nonlin := .identity }] }

private def case08 : TLProgram := tlprog!{
  predicate P(i)
  P[i] := relu(X[i])
}
private def case09 : TLProgram := tlprog!{
  predicate P(i)
  P[i] := maxreduce(X[i])
}
private def case10 : TLProgram := tlprog!{ Out[2 * i] := relu(X[i]) }
private def case11 : TLProgram := tlprog!{
  iter l = 3
  Out[2 * i, l + 1] := X[i, l]
}
private def case12 : TLProgram := tlprog!{
  tensor X(j)
  S[j, 0] := X[j]
  S[j, l + 1] := S[j, l]
}
private def case13 : TLProgram := tlprog!{
  iter l = 3
  S[j, 0] := X[j, 0]
  S[j, l + 1] := S[j, l] + X[j, l + 1]
}
private def case14 : TLProgram := tlprog!{
  iter l = 3
  h[j, 0] := h0[j]
  h[j, l + 1] := A[j, k] · h[k, l] + B[j] · u[l]
  y[j, l] := C[j, k] · h[k, l]
}
private def case15 : TLProgram := tlprog!{
  A[i] := B[i]
  B[i] := A[i]
}
/-- Case 15's cycle with both statements made nonlinear: two split mints disappear. -/
private def case16 : TLProgram := tlprog!{
  A[i] := relu(B[i])
  B[i] := relu(A[i])
}
private def case17 : TLProgram := tlprog!{
  A[q, s.] := softmax(where s ≤ q)(Q[q, d] · K[s, d])
}
/-- Adversarial source name: 16 `#`s, the character the internal route name is built from. -/
private def case18 : TLProgram := {
  decls := []
  stmts := [.assign "################" [.free (ax "i")]
    { body := { terms := [{ factors := [.read "X" [.axis (ax "i")]] }] },
      nonlin := .pointwise .relu }] }

/-- Escaped `%nl2`: a source name colliding with the OLD split phase's generated-name scheme. -/
private def case19 : TLProgram := {
  decls := []
  stmts := [
    .assign "%nl2" [.free (ax "i")] (read1 "X" (ax "i")),
    .assign "Y" [.free (ax "i")]
      { body := { terms := [{ factors := [.read "%nl2" [.axis (ax "i")]] }] },
        nonlin := .pointwise .relu }
  ] }

/-! ## Observation combinators — production `TLProgram.compile` only

`compileErrorIs` pins the exact error CONSTRUCTOR, its exact PAYLOAD, and the exact final `FreshM`
state. `compileOkIs` pins the routed presentation's ARITY, WIDTH, and WIRING (`nExternal`, step
COUNT, full `routing` wire lists) and the final state — it does NOT inspect the emitted `steps`
payload itself (`List BrBaseP`), so a step-order/content corruption that preserves those four
values would not be caught here. That coverage lives elsewhere: `Bridge/Agreement.lean`'s
`compile_eq_physical_route`, `Bridge/AcsetCodecTest.lean`, and `DSL/Pipeline/RouteWeaveTest.lean`
all pin the routed steps directly (§4 below already says so for the composition-adjacent claims;
this note is about `compileOkIs` specifically). What IS a failure here: a changed payload, a
changed precedence, or a one-off state in nExternal/step-count/routing/finalState. -/

private def compileErrorIs (p : TLProgram) (e : CompileError) (finalState : Nat)
    (start : Nat := 0) : Bool :=
  match p.compile.run start with
  | .error a s => a == e && s == finalState
  | .ok _ _    => false

private def compileOkIs (p : TLProgram) (nExternal nSteps : Nat) (routing : List (List Wire))
    (finalState : Nat) (start : Nat := 0) : Bool :=
  match p.compile.run start with
  | .ok tc s => tc.nExternal == nExternal && tc.steps.length == nSteps &&
                tc.routing == routing && s == finalState
  | .error _ _ => false

/-! ### D1–D4: success, then the three exact `rankMismatch` payloads

D4 is the error-PRECEDENCE observation: swapping `checkReadRanks`/`checkDtypes` turns this into
`normAxisNotReal "m"` and fails here. -/

#guard compileOkIs case01 1 1 [[Wire.external 0]] 2
#guard compileErrorIs case02 (.rankMismatch "W" 2 1) 3
#guard compileErrorIs case03 (.rankMismatch "X" 1 2) 3
#guard compileErrorIs case04 (.rankMismatch "W" 2 1) 4

/-! ### D5: first removed split mint — old @3, new @2 -/

#guard compileOkIs case05 1 2 [[Wire.external 0], [Wire.internal 0 0]] 2

/-! ### D6–D15: ten exact named errors, every state unchanged by the flip

All ten fail strictly before the (former) split phase, so a state delta here would mean the flip
moved a *pre-split* failure — a §4 stop condition, not a fixture to update. -/

#guard compileErrorIs case06 (.normAxisNotReal "m") 2
#guard compileErrorIs case07 (.iterAxisNotNat "l") 2
#guard compileErrorIs case08 (.predicateNonlin "P") 2
#guard compileErrorIs case09 (.predicateAgg "P") 2
#guard compileErrorIs case10 (.unsupportedNonlinScatter "Out") 2
#guard compileErrorIs case11 (.scatterInScan "Out") 3
#guard compileErrorIs case12 (.scanAxisNotIter "l") 4
#guard compileErrorIs case13 (.causalityViolation "S") 4
#guard compileErrorIs case14 (.scanProjectionUnsupported "y") 5
#guard compileErrorIs case15 (.cyclicDataflow "schedule: cyclic dataflow") 2

/-! ### D16: same constructor, same payload string, two removed split mints (old @4 → new @2)

Pinning the payload BYTE-FOR-BYTE is the point: `schedule` owns this rejection, both before and
after the flip, and only the state moved. (An intermediate revision briefly had `route` surface a
`physicalizeForRoute`-owned `cyclicDataflow` text instead; that duplicate check is gone — see the
route-domain cyclic guards below.) -/

#guard compileErrorIs case16 (.cyclicDataflow "schedule: cyclic dataflow") 2

/-! ### D17–D18: two more removed split mints (old @5 → @4, old @3 → @2) -/

#guard compileOkIs case17 2 2 [[Wire.external 0, Wire.external 1], [Wire.internal 0 0]] 4
#guard compileOkIs case18 1 2 [[Wire.external 0], [Wire.internal 0 0]] 2

/-! ### D19: old rejected, new ACCEPTS — the intentional collision fix

Pre-flip this was `cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)"` @3. If this
guard ever goes back to an error, the internal-name minting has stopped consulting the program's
own name inventory. -/

#guard compileOkIs case19 1 3
  [[Wire.external 0], [Wire.internal 0 0], [Wire.internal 1 0]] 2

/-! ## The two direct route-domain observations, both at start 7

These call **public `route`** on hand-built logical schedules, checking that the route boundary's
own two rejections are unchanged and that neither consumes a mint (7 → 7). -/

private def routeUndeclared : ScheduledProgram := {
  decls := [], env := {}, extNames := ∅, explicitSizes := {}
  stmts := [.plain (.assign "Y" [.free (ax "i")] (read1 "Ghost" (ax "i")))] }

private def routeUnusedExternal : ScheduledProgram := {
  decls := [], env := {}, extNames := {"X", "Unused"}, explicitSizes := {}
  stmts := [.plain (.assign "Y" [.free (ax "i")] (read1 "X" (ax "i")))] }

private def routeErrorIs (sp : ScheduledProgram) (e : CompileError) (finalState : Nat)
    (start : Nat) : Bool :=
  match route sp |>.run start with
  | .error a s => a == e && s == finalState
  | .ok _ _    => false

#guard routeErrorIs routeUndeclared (.undeclaredName "Ghost") 7 7
#guard routeErrorIs routeUnusedExternal
  (.shapeMismatch
    "route: wellFormedDom failed (unreferenced external slot or read-rank mismatch)"
    "wellFormedDom") 7 7

/-! ### A cyclic logical schedule reports `routeCore`'s message, not physicalization's

The 19 compile cases structurally cannot contain a self-read: `schedule` rejects a logical cycle
before `route` is reached (see case 16 above), so this class of program is only observable by
handing `route` a hand-built schedule. It matters because an intermediate revision of
`physicalizeForRoute` carried its own `physicalRouteInOrder` gate, duplicating `routeCore`'s
`routableInOrder`. Running first, it moved the payload to
`cyclicDataflow "physicalizeForRoute: physical fragment topology failed"` and — for a single
self-referential statement — moved which phase rejected the program, with no split-mint accounting
to license the change (§4.3 stop condition). The duplicate gate is gone; these pin the ORIGINAL
pre-flip payload at all three arities the phase distinction could show up in.

`selfRef .identity` is the one the removed check uniquely changed: one statement, no split, so
physicalization was the only phase that had run. Its ReLU twin additionally confirms the message
does not depend on whether the statement was split into a pair first. -/

private def selfRef (nl : Nonlin) : ScheduledProgram := {
  decls := [], env := {}, extNames := ∅, explicitSizes := {}
  stmts := [.plain (.assign "A" [.free (ax "i")]
    { body := { terms := [{ factors := [.read "A" [.axis (ax "i")] ] }] }, nonlin := nl })] }

/-- A cycle between two identity statements: physical-only, so `schedule` never sees it. -/
private def physicalOnlyCycle : ScheduledProgram := {
  decls := [], env := {}, extNames := ∅, explicitSizes := {}
  stmts := [ .plain (.assign "A" [.free (ax "i")] (read1 "B" (ax "i")))
           , .plain (.assign "B" [.free (ax "i")] (read1 "A" (ax "i"))) ] }

private def cyclicRouteMsg : CompileError :=
  .cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)"

#guard routeErrorIs (selfRef .identity) cyclicRouteMsg 7 7
#guard routeErrorIs (selfRef (.pointwise .relu)) cyclicRouteMsg 7 7
#guard routeErrorIs physicalOnlyCycle cyclicRouteMsg 7 7

/-! ## The nine composition observations: `compile` ≡ `compileToScheduled >>= route`

`compile` (a `do`-bind chain) and `compileToScheduled` (a `>=>` Kleisli chain) are spelled
*separately* in `DSL/Compile.lean`, so this is a real equality of two independent expressions, not a
tautology. Cases 1 (success), 2 (pre-split error) and 16 (post-split-state error) are compared at
one zero and two nonzero starting states; the nonzero starts matter because `assignUIDs` spends an
extra mint at start 0 to avoid UID zero, so a uniform zero-start delta would hide a mint bug.

This is the *fixture* side of the factorization. `Bridge/Agreement.lean`'s
`compile_eq_physical_route` proves the same thing as a `FreshM` function equality, which is strictly
stronger; these guards additionally pin the concrete final states. -/

private def compositionExact (p : TLProgram) (start : Nat) : Bool :=
  match p.compile.run start, (p.compileToScheduled >>= route).run start with
  | .ok x sx,    .ok y sy    => x == y && sx == sy
  | .error x sx, .error y sy => x == y && sx == sy
  | _, _                     => false

/-- Final states of the nine composition observations, so a mint drift at a nonzero start cannot
    hide behind a both-sides-mutated equality. -/
private def compositionState (p : TLProgram) (start finalState : Nat) : Bool :=
  match p.compile.run start with
  | .ok _ s    => s == finalState
  | .error _ s => s == finalState

#guard compositionExact case01 0  && compositionState case01 0 2
#guard compositionExact case01 7  && compositionState case01 7 8
#guard compositionExact case01 41 && compositionState case01 41 42
#guard compositionExact case02 0  && compositionState case02 0 3
#guard compositionExact case02 7  && compositionState case02 7 9
#guard compositionExact case02 41 && compositionState case02 41 43
#guard compositionExact case16 0  && compositionState case16 0 2
#guard compositionExact case16 7  && compositionState case16 7 8
#guard compositionExact case16 41 && compositionState case16 41 42

end LeanNCD.RouteFragmentDiagnostic

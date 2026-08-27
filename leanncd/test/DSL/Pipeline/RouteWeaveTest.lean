import LeanNCD.DSL.Compile
import LeanNCD.DSL.Pipeline.RouteFragments
namespace LeanNCD
-- BEFORE refactor this elaborates against the current `route`; it must still hold AFTER.
#guard (tl!{ Y[i,j] := W[i,k] · X[k,j] }).steps.length == 1
#guard (tl!{ Y[i,j] := W[i,k] · X[k,j] }).routing == [[Wire.external 0, Wire.external 1]]
#guard (tl!{
    H[i,k] := W1[k,d] · X[i,d]
    Y[i,j] := relu(W2[j,k] · H[i,k])
  }).routing == [[Wire.external 0, Wire.external 1],
                 [Wire.external 2, Wire.internal 0 0],
                 [Wire.internal 1 0]]

-- Fixed-axis NAME list of a presentation weave (computable surrogate of weaveToArrayType shape).
def fixedNames (w : WeaveShapeP) : List (Option String) :=
  w.filterMap fun s => match s with | .fixed a => some a.name | .tiled => none

-- After the fix: the H-read input weave of step 1 must have targetAxes = H's output axes [i,k],
-- NOT the degenerate [i,j]. The H wire is routing[1][1] = internal 0 0.
#guard
  let tc := tl!{
    H[i,k] := W1[k,d] · X[i,d]
    Y[i,j] := relu(W2[j,k] · H[i,k])
  }
  fixedNames ((tc.steps.getD 1 default).inputWeaves.getD 1 [])
    == fixedNames ((tc.steps.getD 0 default).outputWeaves.getD 0 [])

/-! ## Route-fragment physicalization (Task 1 of `nonlinearity_split_pair_direct_lowering.md`)

Route equality is established **without** touching any public API: the old leg is
`splitNonlins → schedule → routeCore` and the new leg is
`schedule → physicalizeForRoute → routeCore`, on the same source. Public `route` is deliberately
NOT used on either side — its input contract changes in Task 2 (§2.4), so a fixture routed through
it would have to be rewritten then.

The four `#guard`s above are the route-equality ORACLE for this work: they pin exact `.routing`
wire lists for a two-statement program whose second statement is a ReLU (three physical steps).
Physicalization must reproduce them exactly; if they ever need editing, route equality has broken
(§4.3 stop condition), it is not a fixture to update. -/

/-- Everything through `finalizeScans`: the LOGICAL program, before any nonlinearity split. -/
private def toLogicalScan : TLProgram → FreshM ScanProgram :=
  assignUIDs >=> resolveDecls >=> reclassifyIterSlots >=> checkReadRanks >=> checkDtypes >=>
    checkScatterNonlin >=> checkScatterNoScan >=> lowerArith >=> finalizeScans

/-- NEW leg: logical schedule (no split) → checked physicalization → unchanged `routeCore`. -/
private def newRouteCore (sp : ScanProgram) : FreshM (List BrBaseP × List (List Wire)) := do
  let sched ← schedule sp
  match physicalizeForRoute sched with
  | .error e => throw e
  | .ok physical =>
      match routeCore physical.scheduled with
      | .error e => throw e
      | .ok pair => return pair

/-- OLD leg: `splitNonlins` → `schedule` → `routeCore`. Deliberately not public `route`. -/
private def oldRouteCore (sp : ScanProgram) : FreshM (List BrBaseP × List (List Wire)) := do
  let sched ← schedule (← splitNonlins sp)
  match routeCore sched with
  | .error e => throw e
  | .ok pair => return pair

/-- Old/new routed presentations agree exactly (steps AND routing) on a source program. -/
private def sameRoutedPresentation (label : String) (p : TLProgram) : Lean.Elab.Command.CommandElabM Unit := do
  match (toLogicalScan p).run 0 with
  | .error e _ => throwError s!"{label}: logical pipeline failed: {repr e}"
  | .ok sp s =>
      match (oldRouteCore sp).run s, (newRouteCore sp).run s with
      | .ok (oldSteps, oldRouting) _, .ok (newSteps, newRouting) _ =>
          unless oldSteps == newSteps do
            throwError s!"{label}: routed STEPS differ between old split pipeline and physicalization"
          unless oldRouting == newRouting do
            throwError s!"{label}: routed WIRES differ: old {repr oldRouting}, new {repr newRouting}"
      | .error e _, _ => throwError s!"{label}: OLD leg failed: {repr e}"
      | _, .error e _ => throwError s!"{label}: NEW leg failed: {repr e}"

/-- The logical schedule and its checked physicalization, at FreshM start 0. -/
private def logicalAndPhysical (p : TLProgram) :
    Except CompileError (ScheduledProgram × PhysicalRouteProgram) :=
  match (toLogicalScan p).run 0 with
  | .error e _ => .error e
  | .ok sp s =>
      match (schedule sp).run s with
      | .error e _ => .error e
      | .ok logical _ => (physicalizeForRoute logical).map (fun ph => (logical, ph))

/-- Byte-for-byte equality of two `ScanStmt`s. `ScanStmt` derives only `Inhabited`, so this
    spells out the per-constructor comparison over its (all `DecidableEq`) payload fields. -/
private def sameScanStmt : ScanStmt → ScanStmt → Bool
  | .plain a, .plain b => a == b
  | .scan n₁ ax₁ b₁ r₁ f₁, .scan n₂ ax₂ b₂ r₂ f₂ =>
      n₁ == n₂ && ax₁ == ax₂ && b₁ == b₂ && r₁ == r₂ && f₁ == f₂
  | .scanPre n₁ ax₁ t₁, .scanPre n₂ ax₂ t₂ => n₁ == n₂ && ax₁ == ax₂ && t₁ == t₂
  | _, _ => false

private def sameScanStmts (xs ys : List ScanStmt) : Bool :=
  xs.length == ys.length && (xs.zip ys).all (fun (x, y) => sameScanStmt x y)

private def slotsHaveFreeNorm (slots : List LHSSlot) : Bool :=
  slots.any fun | .freeNorm _ => true | _ => false

/-! ### Fixture 1 — ReLU: 1 logical stmt, 0 generated names, exact old/new route equality.
Source construction cloned from `test/Eval/Plan/NonlinCompileTest.lean`'s `reluProg`
(`H[i] := relu(W[i, j] · x[j])`); the test module is deliberately not imported. -/

private def f1Relu : TLProgram := tlprog!{ H[i] := relu(W[i, j] · x[j]) }

run_cmd do
  match logicalAndPhysical f1Relu with
  | .error e => throwError s!"F1: {repr e}"
  | .ok (logical, physical) =>
      unless logical.stmts.length == 1 do
        throwError s!"F1: expected 1 LOGICAL stmt, got {logical.stmts.length}"
      unless logical.stmts.flatMap routeWrites == ["H"] do
        throwError s!"F1: logical schedule must publish only source names, got {logical.stmts.flatMap routeWrites}"
      unless physical.scheduled.stmts.length == 2 do
        throwError s!"F1: expected 2 PHYSICAL stmts, got {physical.scheduled.stmts.length}"
      match physical.fragments with
      | [f] =>
          unless f.logicalIndex == 0 && f.firstStep == 0 && f.lastStep == 1 && f.internalName.isSome do
            throwError s!"F1: fragment interval changed: {repr f}"
      | fs => throwError s!"F1: expected exactly one fragment, got {fs.length}"
run_cmd sameRoutedPresentation "F1 relu" f1Relu

/-! ### Fixture 2 — axiswise (softmax) equivalent. Source construction cloned from
`NonlinCompileTest.softmaxProg` (`Y[q, s.] := softmax(A[q, s])`). -/

private def f2Softmax : TLProgram := tlprog!{
  tensor Y(q, s)
  Y[q, s.] := softmax(A[q, s])
}

run_cmd do
  match logicalAndPhysical f2Softmax with
  | .error e => throwError s!"F2: {repr e}"
  | .ok (logical, physical) =>
      unless logical.stmts.length == 1 do
        throwError s!"F2: expected 1 LOGICAL stmt, got {logical.stmts.length}"
      unless logical.stmts.flatMap routeWrites == ["Y"] do
        throwError s!"F2: logical schedule must publish only source names, got {logical.stmts.flatMap routeWrites}"
      unless physical.scheduled.stmts.length == 2 do
        throwError s!"F2: expected 2 PHYSICAL stmts, got {physical.scheduled.stmts.length}"
run_cmd sameRoutedPresentation "F2 softmax" f2Softmax

/-! ### Fixture 3 — ReLU followed by a downstream contraction reading its output.
Asserts the fragment-**exit** lookup: the downstream read must wire to the fragment's LAST step
(the nonlinear consumer), never its private producer. -/

private def f3Chain : TLProgram := tlprog!{
  H[i] := relu(W[i, j] · x[j])
  Z[k] := H[i] · V[i, k]
}

run_cmd do
  match logicalAndPhysical f3Chain with
  | .error e => throwError s!"F3: {repr e}"
  | .ok (logical, physical) =>
      unless logical.stmts.length == 2 do
        throwError s!"F3: expected 2 LOGICAL stmts, got {logical.stmts.length}"
      unless physical.scheduled.stmts.length == 3 do
        throwError s!"F3: expected 3 PHYSICAL stmts, got {physical.scheduled.stmts.length}"
      match physical.fragments with
      | [nonlinFrag, tailFrag] =>
          unless nonlinFrag.firstStep == 0 && nonlinFrag.lastStep == 1 do
            throwError s!"F3: nonlinear fragment interval changed: {repr nonlinFrag}"
          unless tailFrag == ⟨1, 2, 2, none⟩ do
            throwError s!"F3: identity fragment changed: {repr tailFrag}"
          -- the EXIT step publishes H; the ENTRY step publishes only the private name
          unless routeOutputs (physical.scheduled.stmts.getD nonlinFrag.lastStep default) == ["H"] do
            throwError "F3: fragment exit does not publish the logical output H"
          unless routeOutputs (physical.scheduled.stmts.getD nonlinFrag.firstStep default)
              == [nonlinFrag.internalName.getD ""] do
            throwError "F3: fragment entry does not publish ONLY the private internal name"
      | fs => throwError s!"F3: expected 2 fragments, got {fs.length}"
      -- and the downstream wire points at the exit step (index 1), not the entry step (index 0)
      match routeCore physical.scheduled with
      | .error e => throwError s!"F3: routeCore failed: {repr e}"
      | .ok (_, routing) =>
          unless (routing.getD 2 []).contains (Wire.internal 1 0) do
            throwError s!"F3: downstream H-read must wire to fragment EXIT (internal 1 0), got {repr (routing.getD 2 [])}"
run_cmd sameRoutedPresentation "F3 chain" f3Chain

/-! ### Fixture 4 — two nonlinear branches joined by one statement.
Asserts private-name injectivity: two fragments, two DISTINCT generated names. -/

private def f4Join : TLProgram := tlprog!{
  P[i] := relu(A[i, j] · U[j])
  Q[i] := relu(B[i, j] · V[j])
  R[i] := P[i] · Q[i]
}

run_cmd do
  match logicalAndPhysical f4Join with
  | .error e => throwError s!"F4: {repr e}"
  | .ok (logical, physical) =>
      unless logical.stmts.length == 3 do
        throwError s!"F4: expected 3 LOGICAL stmts, got {logical.stmts.length}"
      unless physical.scheduled.stmts.length == 5 do
        throwError s!"F4: expected 5 PHYSICAL stmts, got {physical.scheduled.stmts.length}"
      match generatedRouteNames physical.fragments with
      | [a, b] =>
          if a == b then throwError s!"F4: private route names collide: {a}"
          if physical.sourceNames.contains a || physical.sourceNames.contains b then
            throwError "F4: a private route name occurs in the source inventory"
      | gs => throwError s!"F4: expected exactly 2 generated names, got {gs.length}"
      -- §2.4 Global Constraint: "no physicalization case may reorder logical statements."
      -- Fragments come out in logical order …
      unless physical.fragments.map (·.logicalIndex) == List.range logical.stmts.length do
        throwError s!"F4: fragment logical indices are not 0…n-1: {repr (physical.fragments.map (·.logicalIndex))}"
      -- … and fragment k's EXIT publishes logical statement k's output. This second half is the
      -- one with teeth: `logicalIndex` is assigned by `zipIdx` INSIDE `physicalizeRaw`, so a
      -- permutation applied before that fold still yields `0…n-1`. Comparing against
      -- `logical.stmts` — the unpermuted input the package stores separately — is what actually
      -- detects a reordering.
      unless physical.fragments.map (fun f =>
            routeOutputs (physical.scheduled.stmts.getD f.lastStep default))
          == logical.stmts.map routeOutputs do
        throwError "F4: physicalization REORDERED the logical statements (fragment exits do not follow logical order)"
run_cmd sameRoutedPresentation "F4 join" f4Join

/-! ### Fixture 5 — fixture 4 without the join: the second nonlinear output is never read.
Asserts it survives scheduling AND physicalization (no DCE, both fragments intact). -/

private def f5Unread : TLProgram := tlprog!{
  P[i] := relu(A[i, j] · U[j])
  Q[i] := relu(B[i, j] · V[j])
}

run_cmd do
  match logicalAndPhysical f5Unread with
  | .error e => throwError s!"F5: {repr e}"
  | .ok (logical, physical) =>
      unless logical.stmts.length == 2 do
        throwError s!"F5: expected 2 LOGICAL stmts, got {logical.stmts.length}"
      unless physical.scheduled.stmts.length == 4 do
        throwError s!"F5: expected 4 PHYSICAL stmts, got {physical.scheduled.stmts.length}"
      let exits := physical.fragments.map (fun f =>
        routeOutputs (physical.scheduled.stmts.getD f.lastStep default))
      unless exits == [["P"], ["Q"]] do
        throwError s!"F5: unread secondary nonlinear output did not survive: {repr exits}"
run_cmd sameRoutedPresentation "F5 unread" f5Unread

/-! ### Fixture 6 — named axiswise source fixture: `.freeNorm` is degraded on the PRODUCER only.
**Public on purpose** — the MASTER PLAN's own (later, unrelated) Task 2, the 145-case corpus slice,
reuses this exact construction. Not this slice's own Task 2 (already done). -/

def freeNormAxiswiseProg : TLProgram := tlprog!{
  tensor Y(q, s)
  Y[q, s.] := normalize(W[q, d] · X[d, s])
}

run_cmd do
  match logicalAndPhysical freeNormAxiswiseProg with
  | .error e => throwError s!"F6: {repr e}"
  | .ok (logical, physical) =>
      match logical.stmts, physical.scheduled.stmts with
      | [.plain (.assign output slots rhs)],
        [.plain (.assign internal producer producerRhs), .plain (.assign exit consumer consumerRhs)] =>
          unless slotsHaveFreeNorm slots do
            throwError "F6: the LOGICAL statement must carry a `.freeNorm` marker"
          unless producer == producerSlots slots && !slotsHaveFreeNorm producer do
            throwError "F6: the private producer must degrade `.freeNorm` to `.free`"
          unless consumer == slots && slotsHaveFreeNorm consumer do
            throwError "F6: the logical consumer must KEEP the `.freeNorm` marker"
          unless internal == routeName physical.sourceNames 0 && exit == output do
            throwError "F6: producer/exit names changed"
          unless producerRhs.body == rhs.body && producerRhs.nonlin == .identity
              && producerRhs.agg == rhs.agg do
            throwError "F6: producer payload was not preserved exactly"
          unless consumerRhs.nonlin == rhs.nonlin && consumerRhs.agg == .sum
              && consumerRhs.body == { terms := [{ factors :=
                    [.read internal (slots.filterMap LHSSlot.toReadIdx)] }] } do
            throwError "F6: consumer payload changed"
      | _, _ => throwError "F6: expected exactly one logical / two physical statements"
run_cmd sameRoutedPresentation "F6 freeNorm axiswise" freeNormAxiswiseProg

/-! ### Fixture 7 — a ReLU scan is ONE opaque copied node (the §1.2 scan-semantics fix).
Source construction cloned from `test/DSL/Pipeline/ScanAffineTest.lean`'s private `reluScan`. -/

private def f7ReluScan : TLProgram := tlprog!{
  iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := relu(S[j, l] · A[j, k])
}

run_cmd do
  match logicalAndPhysical f7ReluScan with
  | .error e => throwError s!"F7: {repr e}"
  | .ok (logical, physical) =>
      unless sameScanStmts logical.stmts physical.scheduled.stmts do
        throwError "F7: the scan node was NOT copied byte-for-byte (a scan body was split?)"
      unless physical.fragments == [⟨0, 0, 0, none⟩] do
        throwError s!"F7: expected one width-1 opaque fragment, got {repr physical.fragments}"
      match logical.stmts with
      | [.scan _ _ _ recur _] =>
          unless recur.length == 1 do
            throwError s!"F7: the logical recurrence must stay unsplit, got {recur.length} stmts"
      | _ => throwError "F7: expected a single `.scan` node"
run_cmd sameRoutedPresentation "F7 relu scan" f7ReluScan

/-! ### Fixture 8 — fixture 6's axiswise construction inside a recurrence: also ONE opaque node. -/

private def f8AxiswiseScan : TLProgram := tlprog!{
  iter l = 3
  tensor S(q, s, l)
  S[q, s, 0]     := A[q, s]
  S[q, s., l +1] := normalize(S[q, s, l])
}

run_cmd do
  match logicalAndPhysical f8AxiswiseScan with
  | .error e => throwError s!"F8: {repr e}"
  | .ok (logical, physical) =>
      unless sameScanStmts logical.stmts physical.scheduled.stmts do
        throwError "F8: the axiswise scan node was NOT copied byte-for-byte"
      unless physical.fragments == [⟨0, 0, 0, none⟩] do
        throwError s!"F8: expected one width-1 opaque fragment, got {repr physical.fragments}"
      unless generatedRouteNames physical.fragments == [] do
        throwError "F8: a private name was minted for an opaque scan"
run_cmd sameRoutedPresentation "F8 axiswise scan" f8AxiswiseScan

/-! ### Fixture 9 — coupled scans. Construction cloned from the public
`test/Eval/Plan/ScanCompileTest.lean` `coupledSched`; it is a hand-built `ScheduledProgram`, so the
old/new comparison is at the `routeCore` boundary directly (every nonlinearity is `.identity`, so
`splitNonlins` is the identity on it).

The clone is used in TWO shapes because the donor's own shape is deliberately unroutable: its `H`
state permutes the context axes (`H[c, r]` against `G[r, j, c]`), which is exactly what
`buildStep`'s `outputAxesConsistent` guard rejects with `inconsistentScanAxes`. `f9Coupled` keeps
that shape and asserts physicalization is a verbatim copy whose routed OUTCOME (the same error) is
unchanged; `f9CoupledRoutable` re-orders `H` to `[r, c]` so the routed steps and wires themselves
can be compared. -/

private def f9AxR : AxisSpec := ⟨"r", 11, .nat⟩
private def f9AxC : AxisSpec := ⟨"c", 12, .nat⟩
private def f9AxJ : AxisSpec := ⟨"j", 13, .nat⟩

private def f9Coupled : ScheduledProgram :=
  { decls := [.iter f9AxR 3, .iter f9AxC 3, .axis f9AxJ (some 2)]
  , stmts := [.scan "G" [f9AxR, f9AxC]
      [ .assign "G" [.iterAt f9AxR 0, .free f9AxJ, .iterAt f9AxC 0]
          { body := { terms := [{ factors := [.read "G0" [.axis f9AxJ]] }] }, nonlin := .identity }
      , .assign "H" [.iterAt f9AxC 0, .iterAt f9AxR 0]
          { body := { terms := [{ factors := [.read "H0" []] }] }, nonlin := .identity } ]
      [ .assign "G" [.iterNext f9AxR, .free f9AxJ, .iterNext f9AxC]
          { body := { terms := [{ factors :=
              [.read "G" [.axis f9AxR, .axis f9AxJ, .axis f9AxC], .read "W" [.axis f9AxJ]] }] }
          , nonlin := .identity }
      , .assign "H" [.iterNext f9AxC, .iterNext f9AxR]
          { body := { terms := [ { factors := [.read "H" [.axis f9AxC, .axis f9AxR]] }
                               , { factors := [.read "G" [.axis f9AxR, .axis f9AxJ, .axis f9AxC]] } ] }
          , nonlin := .identity } ]
      false ]
  , env := {}
  , extNames := insert "G0" (insert "H0" (insert "W" (∅ : Finset String)))
  , explicitSizes :=
      (((∅ : Std.HashMap UID Nat).insert f9AxR.uid 3).insert f9AxC.uid 3).insert f9AxJ.uid 2 }

run_cmd do
  match physicalizeForRoute f9Coupled with
  | .error e => throwError s!"F9: physicalization failed: {repr e}"
  | .ok physical =>
      unless sameScanStmts physical.scheduled.stmts f9Coupled.stmts do
        throwError "F9: a coupled scan node was not copied byte-for-byte"
      unless physical.fragments == [⟨0, 0, 0, none⟩] do
        throwError s!"F9: expected one width-1 opaque fragment, got {repr physical.fragments}"
      unless generatedRouteNames physical.fragments == [] do
        throwError "F9: a private name was minted for a coupled scan"
      match routeCore f9Coupled, routeCore physical.scheduled with
      | .ok (oldSteps, oldRouting), .ok (newSteps, newRouting) =>
          unless oldSteps == newSteps && oldRouting == newRouting do
            throwError "F9: routed presentation of the coupled scan changed"
      | .error oldErr, .error newErr =>
          unless oldErr == newErr do
            throwError s!"F9: routed OUTCOME changed: old {repr oldErr}, new {repr newErr}"
      | _, _ => throwError "F9: physicalization changed whether the coupled scan routes at all"

private def f9CoupledRoutable : ScheduledProgram :=
  { f9Coupled with
    stmts := [.scan "G" [f9AxR, f9AxC]
      [ .assign "G" [.iterAt f9AxR 0, .free f9AxJ, .iterAt f9AxC 0]
          { body := { terms := [{ factors := [.read "G0" [.axis f9AxJ]] }] }, nonlin := .identity }
      , .assign "H" [.iterAt f9AxR 0, .iterAt f9AxC 0]
          { body := { terms := [{ factors := [.read "H0" []] }] }, nonlin := .identity } ]
      [ .assign "G" [.iterNext f9AxR, .free f9AxJ, .iterNext f9AxC]
          { body := { terms := [{ factors :=
              [.read "G" [.axis f9AxR, .axis f9AxJ, .axis f9AxC], .read "W" [.axis f9AxJ]] }] }
          , nonlin := .identity }
      , .assign "H" [.iterNext f9AxR, .iterNext f9AxC]
          { body := { terms := [ { factors := [.read "H" [.axis f9AxR, .axis f9AxC]] }
                               , { factors := [.read "G" [.axis f9AxR, .axis f9AxJ, .axis f9AxC]] } ] }
          , nonlin := .identity } ]
      false ] }

run_cmd do
  match physicalizeForRoute f9CoupledRoutable with
  | .error e => throwError s!"F9r: physicalization failed: {repr e}"
  | .ok physical =>
      unless sameScanStmts physical.scheduled.stmts f9CoupledRoutable.stmts do
        throwError "F9r: a coupled scan node was not copied byte-for-byte"
      unless physical.fragments == [⟨0, 0, 0, none⟩] do
        throwError s!"F9r: expected one width-1 opaque fragment, got {repr physical.fragments}"
      match routeCore f9CoupledRoutable, routeCore physical.scheduled with
      | .ok (oldSteps, oldRouting), .ok (newSteps, newRouting) =>
          unless oldSteps == newSteps && oldRouting == newRouting do
            throwError "F9r: routed presentation of the coupled scan changed"
      | .error e, _ => throwError s!"F9r: routeCore failed on the ORIGINAL coupled scan: {repr e}"
      | _, .error e => throwError s!"F9r: routeCore failed on the PHYSICALIZED coupled scan: {repr e}"

/-! ### Fixture 10 — adversarial source names: the logical output is an all-`#` name LONGER than
every other source name. The generated private name must still be absent from the source set.
Hand-built (no surface syntax can produce a `#`-named tensor). -/

private def f10LongHash : TLProgram :=
  let i : AxisSpec := { name := "i", uid := 0, kind := .real }
  { decls := [], stmts := [
      .assign "####" [.free i]
        { body := { terms := [{ factors := [.read "###" [.axis i]] }] },
          nonlin := .pointwise .relu, agg := .sum }] }

run_cmd do
  match logicalAndPhysical f10LongHash with
  | .error e => throwError s!"F10: {repr e}"
  | .ok (_, physical) =>
      match generatedRouteNames physical.fragments with
      | [generated] =>
          if physical.sourceNames.contains generated then
            throwError s!"F10: generated route name {generated} collides with a source name"
          unless generated.length > maxSourceNameLength physical.sourceNames do
            throwError "F10: generated route name is not strictly longer than every source name"
      | gs => throwError s!"F10: expected exactly one generated name, got {gs.length}"
run_cmd sameRoutedPresentation "F10 long-# names" f10LongHash

/-! ### Fixture 11 — an existing identity schedule is unchanged, byte-for-byte.
Construction cloned from `test/DSL/Pipeline/LoweringTest.lean`'s "plain identity assign is
unchanged" fixture (`Y[i] := X[i]`). -/

private def f11Identity : ScheduledProgram :=
  let i : AxisSpec := { name := "i", uid := 1, kind := .real }
  { decls := []
  , stmts := [.plain (.assign "Y" [.free i]
      { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := .identity })]
  , env := {}
  , extNames := insert "X" (∅ : Finset String)
  , explicitSizes := ∅ }

run_cmd do
  match physicalizeForRoute f11Identity with
  | .error e => throwError s!"F11: {repr e}"
  | .ok physical =>
      unless sameScanStmts physical.scheduled.stmts f11Identity.stmts do
        throwError "F11: an identity schedule's statements changed"
      unless physical.scheduled.decls == f11Identity.decls
          && physical.scheduled.extNames == f11Identity.extNames do
        throwError "F11: declarations or externals changed"
      unless physical.fragments == [⟨0, 0, 0, none⟩] do
        throwError s!"F11: expected one width-1 fragment, got {repr physical.fragments}"
      unless generatedRouteNames physical.fragments == [] do
        throwError "F11: an identity schedule minted a private name"
      match routeCore f11Identity, routeCore physical.scheduled with
      | .ok old, .ok new =>
          unless old.1 == new.1 && old.2 == new.2 do
            throwError "F11: routed values are not byte-identical"
      | _, _ => throwError "F11: routeCore failed"

/-! ### Fixture 13 — §2.4 class 6: a nonlinear `.plain (.scatter …)` is REJECTED, not copied as
one physical step. Unreachable from `TLProgram.compile` (`checkScatterNonlin` rejects first), so
this asserts at `physicalizeForRoute`, the checked constructor — which is exactly what public
`route` will delegate to in Task 2. Fixture 12 is Task 2's. -/

private def f13ScatterLogical (nl : Nonlin) : ScheduledProgram :=
  let i : AxisSpec := { name := "i", uid := 1, kind := .real }
  { decls := []
  , stmts := [.plain (.scatter "Out" [.affine (.scale 2 i)]
      { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := nl, agg := .sum }
      { fill := 0, reduce := .sum })]
  , env := {}
  , extNames := insert "X" (∅ : Finset String)
  , explicitSizes := ∅ }

-- class 6: REJECT with the existing `unsupportedNonlinScatter` diagnostic, naming the target.
#guard match physicalizeForRoute (f13ScatterLogical (.pointwise .relu)) with
  | .error (.unsupportedNonlinScatter "Out") => true
  | _ => false
#guard match physicalizeForRoute (f13ScatterLogical (.axiswise .softmax none)) with
  | .error (.unsupportedNonlinScatter "Out") => true
  | _ => false
-- class 5 (the positive control): an IDENTITY scatter is still copied as exactly one step.
#guard match physicalizeForRoute (f13ScatterLogical .identity) with
  | .ok physical =>
      sameScanStmts physical.scheduled.stmts (f13ScatterLogical .identity).stmts &&
        physical.fragments == [⟨0, 0, 0, none⟩]
  | .error _ => false
-- and `fragmentWidth` agrees with `physicalizeOne` on both classes (obligation 5a).
#guard fragmentWidth ((f13ScatterLogical (.pointwise .relu)).stmts.getD 0 default) == 0
#guard fragmentWidth ((f13ScatterLogical .identity).stmts.getD 0 default) == 1

/-! ### Fixture 14 — §2.4 class 6 through its OTHER door: a nonlinear `.plain (.assign …)` whose
LHS `slotsBecomeScatter`.

Fixture 13 covers the already-lowered `.plain (.scatter …)` spelling. This one covers the surface
spelling that `lowerArith` would have reclassified — a nonlinear `.assign` with an `.affine` slot
(`Y[i, 2*i]`) or a diagonal LHS (`Y[i, i]`). Without the `slotsBecomeScatter` qualifier on classes
2/3/4 these went down the SPLIT arm, and the consumer's read coordinates come from
`slots.filterMap LHSSlot.toReadIdx`, which maps `.affine _ => none` — so the affine placement was
silently DROPPED and the program routed as if it had never been written. Unreachable from
`TLProgram.compile` (`checkScatterNonlin` rejects both spellings first, with the byte-identical
`unsupportedNonlinScatter` payload), reachable from a hand-built logical schedule — the widened
caller set §2.4 names. Asserted at **public `route`**, which is what a hand-builder actually calls. -/

private def f14AffineAssign (slots : List LHSSlot) (nl : Nonlin) : ScheduledProgram :=
  let i : AxisSpec := { name := "i", uid := 1, kind := .real }
  { decls := []
  , stmts := [.plain (.assign "Y" slots
      { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := nl, agg := .sum })]
  , env := {}
  , extNames := insert "X" (∅ : Finset String)
  , explicitSizes := ∅ }

private def f14Axis : AxisSpec := { name := "i", uid := 1, kind := .real }
/-- Affine trigger: `Y[i, 2*i]`. -/
private def f14AffineSlots : List LHSSlot := [.free f14Axis, .affine (.scale 2 f14Axis)]
/-- Diagonal trigger: `Y[i, i]` repeats the free-axis UID. -/
private def f14DiagSlots : List LHSSlot := [.free f14Axis, .free f14Axis]

private def f14RouteRejects (slots : List LHSSlot) (nl : Nonlin) : Bool :=
  match route (f14AffineAssign slots nl) |>.run 0 with
  | .error (.unsupportedNonlinScatter "Y") _ => true
  | _ => false

-- both triggers × both nonlinearity shapes: REJECTED at public `route`, same diagnostic as F13.
#guard f14RouteRejects f14AffineSlots (.pointwise .relu)
#guard f14RouteRejects f14AffineSlots (.axiswise .softmax none)
#guard f14RouteRejects f14DiagSlots (.pointwise .relu)
#guard f14RouteRejects f14DiagSlots (.axiswise .softmax none)
/-- The `.scatter`-door twin of `f14AffineAssign`: same LHS name, slots, RHS and nonlinearity,
    spelled as an already-lowered `.scatter` instead of an `.assign`. Only for the payload
    comparison below. -/
private def f14ScatterTwin (nl : Nonlin) : ScheduledProgram :=
  { f14AffineAssign f14AffineSlots nl with
    stmts := [.plain (.scatter "Y" f14AffineSlots
      { body := { terms := [{ factors := [.read "X" [.axis f14Axis]] }] }, nonlin := nl
      , agg := .sum } { fill := 0, reduce := .sum })] }

-- byte-identical to the `.scatter` door's diagnostic, error state included (the reason no new
-- constructor was minted: the two doors are indistinguishable to a caller).
#guard match route (f14ScatterTwin (.pointwise .relu)) |>.run 0,
             route (f14AffineAssign f14AffineSlots (.pointwise .relu)) |>.run 0 with
  | .error a sa, .error b sb => a == b && sa == sb
  | _, _ => false
-- the qualifier bites ONLY on a nonlinearity: an IDENTITY affine `.assign` is still class 1.
#guard match route (f14AffineAssign f14AffineSlots .identity) |>.run 0 with
  | .ok tc _ => tc.steps.length == 1
  | .error _ _ => false
-- `fragmentClass`/`fragmentWidth` agree with `physicalizeOne`'s rejection (obligation 5a's
-- converse direction, which the theorem is vacuous on).
#guard fragmentWidth ((f14AffineAssign f14AffineSlots (.pointwise .relu)).stmts.getD 0 default) == 0
#guard fragmentWidth ((f14AffineAssign f14DiagSlots (.pointwise .relu)).stmts.getD 0 default) == 0
#guard fragmentWidth ((f14AffineAssign f14AffineSlots .identity).stmts.getD 0 default) == 1

/-! ### Fixture 15 — §2.4 class 6, the fourth door: a nonlinear `.plain (.assign …)` whose LHS
combines `.free a` and `.freeNorm a` on the SAME axis. Fixture 14 covers the plain-diagonal and
affine triggers of `slotsBecomeScatter`; this covers the `.freeNorm` trigger found in whole-branch
review (2026-08-27) and fixed here — `slotsBecomeScatter`'s `freeUID?` now counts `.freeNorm` too.
Asserted at public `route`, mirroring fixture 14 exactly. -/

private def f15Axis : AxisSpec := { name := "i", uid := 1, kind := .real }
/-- FreeNorm-diagonal trigger: `Y[i, i.]` — the SAME axis, once plain once norm-marked. -/
private def f15FreeNormDiagSlots : List LHSSlot := [.free f15Axis, .freeNorm f15Axis]

private def f15FreeNormDiagAssign (nl : Nonlin) : ScheduledProgram :=
  { decls := []
  , stmts := [.plain (.assign "Y" f15FreeNormDiagSlots
      { body := { terms := [{ factors := [.read "X" [.axis f15Axis]] }] }, nonlin := nl, agg := .sum })]
  , env := {}
  , extNames := insert "X" (∅ : Finset String)
  , explicitSizes := ∅ }

private def f15RouteRejects (nl : Nonlin) : Bool :=
  match route (f15FreeNormDiagAssign nl) |>.run 0 with
  | .error (.unsupportedNonlinScatter "Y") _ => true
  | _ => false

#guard f15RouteRejects (.pointwise .relu)
#guard f15RouteRejects (.axiswise .softmax none)

/-! ### Fixture 16 — §2.4 class 6, the third door: a nonlinear `.plain (.assign …)` whose LHS
carries a scan iteration slot (`.iterAt`/`.iterNext`). `finalizeScans` always groups a statement
with a nonempty `iterInfo` into a `.scan` node (never leaves it `.plain`), so this shape is
reachable only from a hand-built `ScheduledProgram` fed straight to `physicalizeForRoute`/`route` —
same reachability class as fixtures 14/15. Before this fix, `toReadIdx` collapsed `.iterAt a n`/
`.iterNext a` to `.axis a`, silently discarding the pinned literal/shift and emitting a
producer/consumer pair with mismatched read/write coordinates (see `RouteFragments.lean`'s header).
Closed here by rejecting instead, mirroring class 6. Asserted at public `route`, mirroring
fixtures 14/15. -/

private def f16Axis : AxisSpec := { name := "l", uid := 1, kind := .nat }
/-- Base-case trigger: a pinned literal write `Y[2]`. -/
private def f16IterAtSlots : List LHSSlot := [.iterAt f16Axis 2]
/-- Recurrence trigger: a shifted write `Y[l+1]`. -/
private def f16IterNextSlots : List LHSSlot := [.iterNext f16Axis]

private def f16IterAssign (slots : List LHSSlot) (nl : Nonlin) : ScheduledProgram :=
  { decls := []
  , stmts := [.plain (.assign "Y" slots
      { body := { terms := [{ factors := [.read "X" [.axis f16Axis]] }] }, nonlin := nl, agg := .sum })]
  , env := {}
  , extNames := insert "X" (∅ : Finset String)
  , explicitSizes := ∅ }

private def f16RouteRejects (slots : List LHSSlot) (nl : Nonlin) : Bool :=
  match route (f16IterAssign slots nl) |>.run 0 with
  | .error (.unsupportedNonlinIterSlot "Y") _ => true
  | _ => false

-- both triggers × both nonlinearity shapes: REJECTED at public `route`.
#guard f16RouteRejects f16IterAtSlots (.pointwise .relu)
#guard f16RouteRejects f16IterAtSlots (.axiswise .softmax none)
#guard f16RouteRejects f16IterNextSlots (.pointwise .relu)
#guard f16RouteRejects f16IterNextSlots (.axiswise .softmax none)
-- the qualifier bites ONLY on a nonlinearity: an IDENTITY `.iterAt` `.assign` is still class 1/copy.
#guard match route (f16IterAssign f16IterAtSlots .identity) |>.run 0 with
  | .ok tc _ => tc.steps.length == 1
  | .error _ _ => false
-- `fragmentClass`/`fragmentWidth` agree with `physicalizeOne`'s rejection (obligation 5a's
-- converse direction, which the theorem is vacuous on).
#guard fragmentWidth ((f16IterAssign f16IterAtSlots (.pointwise .relu)).stmts.getD 0 default) == 0
#guard fragmentWidth ((f16IterAssign f16IterNextSlots (.pointwise .relu)).stmts.getD 0 default) == 0
#guard fragmentWidth ((f16IterAssign f16IterAtSlots .identity).stmts.getD 0 default) == 1

end LeanNCD

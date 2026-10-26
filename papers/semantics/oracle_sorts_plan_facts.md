# Oracle sorts: plan facts (explore/observe dispatch)

Base 1b8bfc9a, main. Everything marked "observed" was printed by a real `lean-file.sh` run of an untracked scratch file (deleted afterwards; the builder and helper source are reproduced in section 5 so the plan can clone them). "read" = read, not run. Identifiers are cited `@ file`, never by line number.

## 0. T0 HARD GATE: **PASS**

Both native legs return `observed` outputs, with no rejection from `legacyWithInputs` / `prepareNativeInputs`, for every mixed-sort Source program tried, and legacy bits equal checked bits in every case (observed). `compareSortedSource` still refuses every mixed program at selection (`sortSelection (mixedSorts ..)`), exactly as `SourceSortedDifferentialTest` pins (observed).

Programs: exact clone of the fixture `snap`/`bellman` @ test/Semantics/SourceSortedDifferentialTest (`bellman s1 s2 = snap [a] [contY s1, termY s2] [20,2,3,40]`: `Y[a] := s1 Z[a,b]` then `Y[a] := s2 X[a]`), output declaration 6, `X=[20,2,3,40]`, `Z[a,b]=[-5,-4,-3,5,6,7,15,16,17,25,26,27]`.

| program | `runNative snapshot (sorted := true)` legacy | checked | production (`compileToScheduled` then `validateScheduled`) | `compareSortedSource` |
|---|---|---|---|---|
| `bellman .max .max` (control) | observed, 1 output | observed, 1 output | accepted, `algebras = [Y: maxPlus]` | `fourLegParity` |
| `bellman .max .sum` | observed, 1 output, `Y[4]=[20,7,17,40]` | same bits | accepted, `algebras = [Y: maxPlus]` | `refused sortSelection (mixedSorts [max, sum])` |
| `bellman .max .min` | observed, `Y=[20,7,17,40]` | same bits | accepted, `algebras = [Y: maxPlus]` (min neutral copy abstains and runs as max) | `refused ... mixedSorts [max, min]` |
| `bellman .min .sum` | observed, `Y=[-5,2,3,25]` | same bits | accepted, `algebras = [Y: minPlus]` | `refused ... mixedSorts [min, sum]` |
| `bellman .sum .max` | observed, `Y=[8,20,51,118]` | same bits | accepted, `algebras = []` (real group, no entry) | `refused ... mixedSorts [sum, max]` |

No `failure` / `unavailable` / `preparation` text anywhere in the accepted rows. Bindings count is 1 (the single output `Y`, shape `[4]`) in each. Bits are IEEE f64 (e.g. 20.0 = 0x4034000000000000).

Control-flow facts the plan needs (observed + read):
- `compileToScheduled` does NOT call `validateScheduled` (read @ DSL/Compile.lean). Sort votes, casts and collection refusals come from `validateScheduled` @ DSL/Pipeline/ScheduledValidation.lean, which `evalScheduled` (legacy leg: failure text `compile failed: <CompileError>`) and `prepareEvalPlan` (checked leg: `CheckedOutcome.preparation`, cause `.sourceInvariant <CompileError>`) call. So a refused mixed program shows as `legacy failure` + `checked preparation`, never `sourceCompilation`.
- `admitAffineStatement` with `sorted := true` maps `.scatter` with bare slots to an `.assign` (read @ Admission.lean), so a scatter group is a legal Source program.

## 1. (T0) see section 0.

## 2. Interfaces the plan must name (copied from source)

- `SourceSnapshot` @ LeanNCD/Semantics/Source/Adapter.lean: `structure SourceSnapshot where resolved : ResolvedProgram; specs : List TensorSpec; inputs : List InputBinding`. `ResolvedProgram` @ DSL/Pipeline/Types.lean: `decls : List Decl; stmts : List Stmt; env : DeclEnv; extNames : Finset String`. `TensorSpec := ⟨declaration : Nat, role : TensorRole, shape : List Nat⟩`, `TensorRole := input | defined | output`, `InputBinding := ⟨declaration : Nat, shape : List Nat, values : List ℚ⟩`. There is NO helper that turns a TL program into a snapshot: every fixture hand-builds the three lists with `Stmt` constructors (`.assign name [.free a] ⟨⟨terms.map ProdTerm.mk⟩, .identity, agg⟩`), `env := {}`, `extNames := ∅`, and `typedTensor .f64` for every tensor. The declaration index is the position in `decls` (axes first: `a,b,k` are 0,1,2; first tensor 3).
- Fixture style, cloned per file (all `private`): `snap`, `rhs`, `a/b/k`, `zValues`, `contY`, `termY`, `bellman`, `classOf`, `carrierOf`, `yCore` @ test/Semantics/SourceSortedDifferentialTest; `SourceSortedAuditTest` has its own copy (extent of `k` is 7 there, 8 in the differential test). Nothing is shared, so a new module must re-declare (or the plan must un-private and import).
- `admitSourceAffine (snapshot : SourceSnapshot) (sorted : Bool := false) : Except SourceDiagnostic AdmittedSource` @ Admission.lean. `structure AdmittedSource where source : AdaptedSource; statements : List (AdmittedStatement source)`; `AdmittedStatement.original : Nat` indexes `snapshot.resolved.stmts` (so a heterogeneous oracle recovers each original `Stmt`/agg from the snapshot). `private def stmtAgg` and `sortKeys` live there; `admitSourceSorted (snapshot) (table := standardCarriers) : Except SourceDiagnostic (AdmittedSource × Oracle.Sorted)`.
- `runNative (snapshot : SourceSnapshot) (sorted : Bool := false) : Except SourceDiagnostic NativeRun` @ NativeLegs.lean. `NativeRun := {source, identity, shared, inputs, legacy : LegacyOutcome, checked : CheckedOutcome}`. `LegacyOutcome := unavailable (NativeUnavailable) | failure (LegacyFailure) | observed (NativeObservation)`; `CheckedOutcome := unavailable | sourceCompilation (SourceCompileFailure) | preparation (CheckedPreparationFailure) | runtime (CheckedRuntimeFailure) | observed (NativeObservation) (List StatementMapping)`. `structure NativeObservation where report : EvalReport; outputs : Except (List BindingIssue) (List OutputBinding); backendInternals : ... := ...`. `structure OutputBinding where metadata : TensorOrigin; shape : List Nat; bits : Array UInt64`. `TensorOrigin := {tensorUID, declaration : Nat, name : String, origin, axes, shape}`. `LegacyFailure.original : EvalFailure` (`.error : EvalError`, printable); `CheckedPreparationFailure.original : PlanCompileFailure` (`.cause`).
- `compareBindings (cells : List SortedCell) (bindings : List OutputBinding) : Except String (Option CellMismatch)` @ SortedDifferential.lean (compares `normalizeZeroBits cell.expected.bits` to observed bits, per binding; throws on cell-count mismatch). `structure SortedCell := {declaration : Nat, coordinate : List Nat, expected : ExtClass}`; `inductive ExtClass := finite (CheckedValue) | negInf | posInf` with `.bits`.
- `inductive LegResult := agrees | mismatch (cell : CellMismatch) | failure (message : String) | unavailable`.
- `inductive SortedClassification := fourLegParity | referenceUnavailable (reason : String) | referenceDiscrepancy | unsupportedNumericalProfile (reason : Unsupported) | nativeUnavailable | nativeFailure (legacy checked : LegResult) | nativeDiscrepancy (legacy checked : LegResult)` (7 constructors; `deriving Repr`).
- `structure SortedRun := {carrier : String, core oracle : Except String (List (TensorObservation ExtVal)), published : Except String (Comparison (TensorDifference ExtVal)), profile : Except Unsupported (List SortedCell), legacy checked : LegResult, classification : SortedClassification}` (`deriving Repr`). Built positionally exactly once, at the end of `compareSortedSource` @ SortedDifferential.lean (`⟨S.name, core, oracle, published, profile, legacy, checked, classification⟩`).
- `compareSortedSource (snapshot) (order : Option (List Nat)) (table : List Sorted := standardCarriers) : Except SourceDiagnostic SortedRun`. `order` = original declaration ordinals of the non-input tensors in dependency order (for `bellman`: `[6]`).
- `oracleTensorsAt {K} (obs : K → ExtVal) (source : AdmittedSource) (result : Oracle.Result K) : Except String (List (TensorObservation ExtVal))`; `coreTensorsAt (S : Sorted) (source : AdmittedSource) : Except String (List (TensorObservation ExtVal))` (runs `runSourceAt S.carrier source (Registry.none S.K)`; single K).
- `checkSortedProfile {K} (obs : K → ExtVal) (source) (result : Oracle.Result K) : Except Unsupported (List SortedCell)` (per-occurrence bound `bound := bound + |q|` over finite reads, for every statement regardless of sort).
- `Oracle.Result (K := ℚ) := {tensors : List (Tensor K), contributions : List (Contribution K)}`; `Oracle.Tensor K := {declaration : Nat, name : String, role : TensorRole, shape : List Nat, values : List K}`; `Contribution K := {origin, coordinate : List Nat, terms : List (TermFiber K), value : K}`; `TermFiber K := {origin, occurrences : List (Occurrence K), value}`; `Occurrence K := {origin, assignment : List (UID × Nat), output : List Nat, reads : List (ReadValue K), value}`; `ReadValue K := {origin, declaration, coordinate, value : K}`. `Oracle.runWith {K} [Semiring K] (C : Carrier K) (admitted) (dependencyOrder : Option (List Nat)) : Except Unavailable (Result K)` sums (`total := total + c.value`) every statement writing a target cell, in statement order, with no vote (read @ Oracle.lean). `Oracle.coordinates`, `lookup`, `cellCount` are public.
- `ExtVal @ Semantics/Source/Carrier.lean`: `inductive ExtVal | fin (q : ℚ) | negInf | posInf deriving DecidableEq` plus a hand `Repr` instance (prints `-inf` / `+inf`).
- `NumericalProfile.Unsupported` @ Semantics/Source/NumericalProfile.lean, constructors (6): `structural (condition : StructuralCondition)`, `nonIntegral (site) (kind) (numerator : Int) (denominator : Nat)`, `outsideEnvelope (site) (kind) (value : ℚ) (maximum : Nat)`, `oracleUnavailable (reason : Oracle.Unavailable)`, `receipt (site) (condition : ReceiptCondition)`, `coreNotComplete (endpoint : CoreEndpoint)`; `deriving DecidableEq, Repr`. **Match sites (read, via `rg`): there is NO exhaustive `match` on `Unsupported` anywhere in `LeanNCD/` or `test/`.** Every match has a wildcard arm: `ComparisonRun.classification` @ Semantics/Source/Differential.lean (`.error (.structural c)` then `.error reason`); test patterns `| .error (.outsideEnvelope ..) .. | _ => false` @ test/Semantics/SourceDiagnosticPayloadTest, `.error (.receipt _ (.occurrences e n)) .. | .error u` @ SourceDifferentialScatterTest, `.error (.oracleUnavailable r) .. | _` @ SourceDiagnosticAdmissionTest, `reason == .structural condition` (an `==`, not a match) @ SourceDifferentialPolicyTest. Only the derived `DecidableEq`/`Repr` must regenerate (automatic). Other users of the type by name: `NativeUnavailable.input (reason : Unsupported)` @ NativeLegs.lean, `ComparisonRun.profile`/`Classification.unsupportedNumericalProfile` @ Differential.lean, `SortedClassification.unsupportedNumericalProfile` and `checkSortedProfile` @ SortedDifferential.lean. Adding `nonFiniteIntoReal` therefore breaks nothing at compile time; the `SourceDifferentialNumericalTest` `#guard`s that print an `Unsupported` constructor still print the old constructors unchanged.
- Usage counts of the types a new field would touch (read, `rg -c`): `SortedRun` is named in 1 test file (a type ascription in `private def run`, @ SourceSortedDifferentialTest) and constructed in 1 place (SortedDifferential.lean). `r.classification` and `r.core` are the only fields tests read. `SortedClassification.` appears on 20 lines of `SourceSortedDifferentialTest` (printed `repr` strings; the file has 61 `#guard_msgs`). `compareBindings`, `LegResult`, `SortedCell`, `oracleTensorsAt`, `coreTensorsAt`, `checkSortedProfile` are used only inside SortedDifferential.lean (no test file names them). Adding a defaulted field to `SortedRun` or appending `SortedClassification` constructors breaks no existing test (a `deriving Repr` of `SortedRun` is never printed whole by a test).

## 3. Independent-rule precedent (read; import checked by compiling a scratch file, observed)

- `oracleNeutral (s : Stmt) : Bool` @ test/Eval/PropertyOracle/ScanUnroll.lean, namespace `LeanNCD.PropertyOracle`, PUBLIC. Also public there: `localStateAgg (g : ScanGeom) (nm : String) : AggOp`. **`oracleIdxUids : IdxExpr → List UID` and `oracleSlotUids : LHSSlot → List UID` are `private`** (observed: `Unknown identifier LeanNCD.PropertyOracle.oracleIdxUids` / `...oracleSlotUids` from a module importing `Eval.PropertyOracle.ScanUnroll`). So only `oracleNeutral` is a plain `import Eval.PropertyOracle.ScanUnroll`; reusing the two UID helpers needs either dropping `private` in that tracked test file (an edit outside the new module) or re-stating them (6 lines).
- `oracleNeutral` is stated as: `factorCounts == [1] && readFactors.length == 1 && r.nonlin == .identity && contracted.isEmpty && !collidingSlot` (counting `read` and `unaryFn` as read factors, `iverson` not); `recurMorphism` is `false`.
- The agreement guard is in test/Eval/PropertyOracle/ScanOracle.lean (module `Eval.PropertyOracle.ScanOracle`, imports `Eval.PropertyOracle.ScanUnroll`): `private def corpusStmts`, `private def neutralShapes : List (Stmt × Bool)` (24 literal hand-built shapes with pinned verdicts: `nbStmt`, `nbScatter`, `nbRead`, `nbTruth`, axes `nbJ nbK nbT`), and the three `#guard`s `corpusStmts.all (fun s => oracleNeutral s == s.isSortNeutral)`, `corpusStmts.any oracleNeutral`, `corpusStmts.any (fun s => !oracleNeutral s)`, and `#guard neutralShapes.all (fun (s, expected) => oracleNeutral s == expected && s.isSortNeutral == expected)`. All of `corpusStmts`, `neutralShapes`, and the `nb*` helpers are private, so a new module cannot reuse the shape list without un-privatising or copying it. The only production identifier the guard calls is `Stmt.isSortNeutral` (it does not call the vote helpers); `localStateAgg`'s agreement with production (`scanStateAlgebra`) is a separate guard further down that file (read, not inspected in detail).
- Registration: both are listed in the explicit `globs` of `[[lean_lib]] name = "Tests"` @ leanncd/lakefile.toml (`"Eval.PropertyOracle.ScanGen", "Eval.PropertyOracle.ScanUnroll", "Eval.PropertyOracle.ScanOracle", "Eval.PropertyOracleScanTest"`). Building the chain `+Eval.PropertyOracle.ScanOracle` (observed): 21.7 s wall, last four steps 4.1-5.6 s each.

## 4. Production side of the rule-predictor comparison (observed unless stated)

Helper used for every row below (own scratch helper; clone it): 
```
def verdict (s : SourceSnapshot) : String :=
  let p : TLProgram := ⟨s.resolved.decls, s.resolved.stmts⟩
  match p.compileToScheduled.run 0 with
  | .error e _ => s!"compileToScheduled REFUSED {repr e}"
  | .ok sch _ =>
    match validateScheduled sch with
    | .error e => s!"validateScheduled REFUSED {repr e}"
    | .ok c => s!"accepted; algebras={repr (c.algebras.toList)}"
```
Types: `TLProgram.compileToScheduled : TLProgram → FreshM ScheduledProgram` (`.run 0`) @ DSL/Compile.lean; `validateScheduled (sched : ScheduledProgram) : Except CompileError CheckedScheduledProgram` @ DSL/Pipeline/ScheduledValidation.lean (order inside: `scheduleAlgebras` -> `checkSortCasts` -> topo order -> `collectDefinitions`, which raises the `multiWriter*` / `writerShapeMismatch` / `reservedNameCollision` refusals); `CheckedScheduledProgram.algebras : Std.HashMap String SortAlgebra` (partial map), `.algebraOf nm`. Existing-test precedents of the same pipeline:
- test/Eval/Plan/CompileTest.lean (module `Eval.Plan.CompileTest`): `s3bStmt (dest src : String) (nl := .identity) (ag := .sum) : Stmt`, `s3bT nm : Decl`, `s3bSched (extra : List Decl) (stmts : List Stmt) : ScheduledProgram` (hand-built, axis `axIDup` extent 2, inputs `A`,`B`), `s3bChecked (s : ScheduledProgram) : Option CheckedScheduledProgram := match validateScheduled s with ...`, `assertPredicateParity (label) (sched) (expected : CompileError) : CommandElabM Unit` (checks `evalScheduled` and `prepareEvalPlan` both fail with `expected`), `assertSortAccepted (label) (sched)`, `causeOf`. Used in `run_cmd do ...`.
- test/DSL/Pipeline/CollectTest.lean (module `DSL.Pipeline.CollectTest`): surface programs `def c6b : TLProgram := tlprog!{ axis i : ℕ = 2 \n Y[i] := A[i, j] \n Y[i] := maxreduce(B[i, j]) }`; helper `scheduled (p) : Option ScheduledProgram`, `desugared (p) : Option (Except CompileError (ScheduledProgram × List String))` (runs `desugarMultiWriters` AFTER `compileToScheduled`, so it sees only the collection refusals, not sort-cast refusals), `errorOf (p : TLProgram) : Option CompileError`, asserted as `#guard errorOf c6b == some (.multiWriterAlgebra "Y")`.
`CompileError` constructor names (read @ LeanNCD/Exec/Uid.lean, 29): shapeMismatch missingBaseCase causalityViolation overlappingScatter linearWeightAmbiguous undeclaredName rankMismatch iterAxisNotNat normAxisNotReal predicateNonlin predicateAgg tropicalNonlin scanStateAlgebraMismatch sortCastUnsupported cyclicDataflow inconsistentScanAxes emptyScanOutputs scanProjectionUnsupported unsupportedRecurMorphism unsupportedNonlinScatter unsupportedNonlinIterSlot scanAxisNotIter scatterInScan duplicateTensorDecl unsupportedElementType multiWriterScatter multiWriterAlgebra multiWriterScan writerShapeMismatch reservedNameCollision.
Worked observed examples (Source Stmt form, builder in section 5):
- accepted two-writer max group: `Y[a] := maxreduce(Z[a,b])`, `Y[a] := maxreduce(X[a])` (`bellman .max .max`): `accepted; algebras=[("Y", maxPlus)]`.
- `multiWriterAlgebra`: `Y[a] := Z[a,b]` (sum) beside `Y[a] := maxreduce(Q[a,b])`: `validateScheduled REFUSED CompileError.multiWriterAlgebra "Y"`; legacy `failure compile failed: ...multiWriterAlgebra "Y"`; checked `preparation`.
- `sortCastUnsupported`: `M[a] := maxreduce(Z[a,b])`; `O[a] := minreduce(M[a])`: `REFUSED sortCastUnsupported "O" "M"`.
- `multiWriterScatter`: `Y[a] := maxreduce(Z[a,b])` plus `.scatter "Y" [.free a] (maxreduce Q[a,b])`: `REFUSED multiWriterScatter "Y"`.
- Read @ `scheduleAlgebras`: a multi-writer group gets an `algebras` entry only if ALL its writers are plain `.assign` and the agreed sort is tropical; the conflict arm (`writerSort? = none`) inserts nothing (`| none => pure ()`), which is the R10 mutation site.

## 5. Observed outcomes for the planned shapes

Builder (clone; same decl layout as the fixture `snap`: axes `a`(uid 7, extent 4), `b`(8, 3), `k`(9, 8) are declarations 0,1,2, tensors follow):
```
structure T where name : String; axes : List AxisSpec; role : TensorRole; vals : List ℚ := []
def ext (ax : AxisSpec) : Nat := if ax.uid = 7 then 4 else if ax.uid = 8 then 3 else 8
def mk (ts : List T) (stmts : List Stmt) : SourceSnapshot :=
  { resolved := { decls := [.axis a (some 4), .axis b (some 3), .axis k (some 8)]
                    ++ ts.map (fun t => .typedTensor .f64 t.name t.axes)
                  stmts := stmts, env := {}, extNames := ∅ }
    specs := ts.zipIdx.map (fun (t, i) => ⟨i + 3, t.role, t.axes.map ext⟩)
    inputs := (ts.zipIdx.filter (fun (t, _) => t.role == .input)).map
      (fun (t, i) => ⟨i + 3, t.axes.map ext, t.vals⟩) }
-- inputs: X[a]=[20,2,3,40]; Z[a,b]=[-5,-4,-3,5,6,7,15,16,17,25,26,27]; Q[a,b]=B[a,b]=[1,9,2,3,8,4,7,5,6,0,10,11];
--         W8[k]=[1,0,2,3,4,5,6,7]; tensors written then read use role .defined, final ones .output
-- st dst ag f := .assign dst [.free a] (rhs ag [[f]])   (a bare-index copy); zR n ls ag fs := .assign n ls (rhs ag [fs])
-- rd n axes := Factor.read n (axes.map .axis);  free1 := [.free a]
-- compareSortedSource order = decl ordinals of non-input tensors in definition order
```
Surface equivalent (read, not run): `tlprog!{ axis i : ℕ = 4 ...}` as in CollectTest `c6b`; the Source tests cannot use `tlprog!` because a `SourceSnapshot` also needs `specs` and `inputs`.

Notation: "admit" = `admitSourceAffine snapshot true` (all shapes below ADMITTED; none refused). "legacy/checked" = `runNative snapshot (sorted := true)`; where production refuses, legacy = `failure compile failed: <err>` and checked = `preparation`. "sorted" = `compareSortedSource` classification.

(a) R11
| program | production | native (legacy = checked) | sorted |
|---|---|---|---|
| `Y[a]:=Z[a,b]; Y[a]:=maxreduce(X[a])` (sum contraction, neutral max copy) | accepted, `algebras=[]` (real group, no entry) | `Y=[8,20,51,118]` (sum of Z row + X) | `refused mixedSorts [sum,max]` |
| same, reversed order | accepted, `algebras=[]` | `Y=[8,20,51,118]` | `refused mixedSorts [max,sum]` |
| `Y[a]:=maxreduce(Z[a,b]); Y[a]:=X[a]` (max contraction, neutral sum copy) | accepted, `algebras=[Y:maxPlus]` | `Y=[20,7,17,40]` | `refused mixedSorts [max,sum]` |
| same, reversed | accepted, `algebras=[Y:maxPlus]` | `Y=[20,7,17,40]` | `refused mixedSorts [sum,max]` |
Donor: `bellman` (change `s1 s2`). R11 mutation prediction (not run): with neutrals voting, the first row's group conflicts (`multiWriterAlgebra "Y"`).

(b) R16 `Y[a]:=Z[a,b]` (sum, contracted b) beside `Y[a]:=maxreduce(Q[a,b])` (contracted): production `REFUSED multiWriterAlgebra "Y"`; legacy `failure compile failed: multiWriterAlgebra "Y"`; checked `preparation`; sorted `refused mixedSorts [sum,max]` (never reaches the legs). Same constructor for `Y:=maxreduce(Z[a,b]); Y:=minreduce(Q[a,b])` (sorted `refused mixedSorts [max,min]`). Two non-neutral voters that disagree, so this is a vote conflict, not a neutral-copy case. Matches CollectTest `c6b`/`c6c` (read).

(c) R10
- `N[a]:=minreduce(Z[a,b]); T[a]:=maxreduce(N[a]); T[a]:=minreduce(B[a,b])`: **ACCEPTED**, `algebras=[T:minPlus, N:minPlus]`, native `T=[-5,3,5,0]`. NOT a conflict: the max copy is neutral and abstains beside the non-neutral min writer. So the brief's shape does not exercise R10.
- `N[a]:=minreduce(Z[a,b]); T[a]:=maxreduce(N[a]); T[a]:=minreduce(X[a])` (both T writers neutral, votes max and min): production `REFUSED multiWriterAlgebra "T"`; legacy/checked as above. Reversed writer order (min copy first): same `multiWriterAlgebra "T"`.
- R10 mutation prediction (reasoned from the source of `checkSortCasts`, NOT run): leaking the first vote makes `T` maxPlus in the max-first order, so the max writer's bare read of the min-plus `N` raises `sortCastUnsupported "T" "N"` before collection; in the min-first order the leaked vote is minPlus, the max writer's read of `N` (min-plus) is legal, and the refusal stays `multiWriterAlgebra "T"`. So only the max-first order flips; both orders must be in the corpus but only the max-first row kills R10.
- sorted for all three: `refused mixedSorts [min,max]`.

(d) Cast decision A
- direct `M[a]:=maxreduce(Z[a,b]); O[a]:=minreduce(M[a])`: production `REFUSED sortCastUnsupported "O" "M"`; legacy `failure compile failed: sortCastUnsupported "O" "M"`; checked `preparation`; sorted `refused mixedSorts [max,min]`.
- laundered `M:=maxreduce(Z[a,b]); R[a]:=M[a] (sum copy); O[a]:=minreduce(R[a])`: ACCEPTED, `algebras=[M:maxPlus, R:real, O:minPlus]`, native `O=[-3,7,17,27]` (legacy = checked), sorted `refused mixedSorts [max,sum,min]`.

(e) D7 (all admitted, production refuses, and `compareSortedSource` gives a FALSE `nativeFailure`, as the design predicted)
- `Y[a]:=maxreduce(Z[a,b])` + `.scatter "Y" [.free a] (rhs .max [[Q[a,b]]])`: `REFUSED multiWriterScatter "Y"`; sorted `nativeFailure (failure "legacy compile failed: ...multiWriterScatter \"Y\"") (failure "checked preparation")` (selection passes: all max).
- two affine writers `Y[2a]:=maxreduce(X[a])` twice (Y has axis `k`): `REFUSED multiWriterScatter "Y"`, same `nativeFailure`.
- `Y[2a]:=maxreduce(X[a])` + bare `Y[k]:=maxreduce(W8[k])`: `REFUSED multiWriterScatter "Y"`, same `nativeFailure`. (Affine beats the `writerShapeMismatch` check.)

(f) single-writer neutral max copy
- `T[a]:=maxreduce(X[a]); O[a]:=minreduce(T[a])`: production **refused** `sortCastUnsupported "O" "T"` (T is maxPlus by its own annotation); sorted `refused mixedSorts [max,min]`.
- `T:=maxreduce(X[a]); O[a]:=T[a]` (sum): accepted, `algebras=[T:maxPlus, O:real]`, native `O=[20,2,3,40]`, sorted `refused mixedSorts [max,sum]`.
- `T:=maxreduce(X[a]); O:=maxreduce(T[a])`: accepted, `algebras=[T:maxPlus, O:maxPlus]`, native `O=[20,2,3,40]`, sorted **`fourLegParity`** (single sort, existing path).

(g) real <-> tropical identity reads (all admitted)
- all cells written, sum reads max: `M[a]:=maxreduce(Z[a,b]); R[a]:=M[a]`: accepted, `algebras=[M:maxPlus, R:real]`, native `R=[-3,7,17,27]`.
- max statement reads real: `S[a]:=Z[a,b] (sum); O[a]:=maxreduce(S[a])`: accepted, `algebras=[S:real, O:maxPlus]`, native `O=[-12,18,48,78]`.
- UNWRITTEN tropical cells read by a real statement (D5 shape): `M[2*a]:=maxreduce(X[a])` (M has axis `k`, extent 8, odd cells unwritten), `R[k]:=M[k]` (sum copy): accepted, `algebras=[M:maxPlus, R:real]`; native (legacy = checked) `R[8]=[20,-inf,2,-inf,3,-inf,40,-inf]` with `-inf` = `0xFFF0000000000000`.
- same with product `R[k]:=M[k]*W8[k]` (`W8=[1,0,2,3,4,5,6,7]`): native `R=[20,NaN,4,-inf,12,-inf,240,-inf]`, NaN = `0x7FF8000000000000` (`-inf * 0`).
- min-plus unwritten: `M[2*a]:=minreduce(X[a])`, `R[k]:=M[k]`: native `R=[20,+inf,2,+inf,3,+inf,40,+inf]`, `+inf` = `0x7FF0000000000000`.
- sorted for all: `refused mixedSorts [..]`. Every non-finite read, even by a plain copy, must go to `nonFiniteIntoReal` under D5 (the copy row yields `-inf` bits, which `compareBindings` would otherwise have to match).

## 6. Donor fixtures and registration

Nearest donors (name @ file): (a) `bellman` / `contY` / `termY` @ test/Semantics/SourceSortedDifferentialTest; surface `c6bN`/`c6cN` @ test/DSL/Pipeline/CollectTest (the accept neighbours of R11, read). (b) `c6b`/`c6c` @ CollectTest (same shape, surface). (c) CompileTest "all-neutral max + min group is refused by collection" and the `W` rows ("conflicting group has no entry ...", d3) with `s3bSched`/`s3bStmt` @ Eval.Plan.CompileTest (they use input `A`/`B` copies; the two-reader `N` form above is new). (d) the `s3bMN` cast rows ("max-plus statement reads a min-plus tensor") @ CompileTest; no existing fixture does the laundered `R := M` form (searched `launder` in `test/`: only an unrelated ScanTest plan fixture). (e) `c5` @ CollectTest (`multiWriterScatter "S"`), `CollectEvalTest` ("compile failed: ...multiWriterScatter \"S\""); Source-level: `strided` / `bareScatter` @ SourceSortedDifferentialTest / SourceSortedAuditTest. (f) `s3bTG` rows ("real and max-plus statements read a collected max-plus tensor") @ CompileTest. (g) `strided` @ SourceSortedDifferentialTest (Source oracle, empty-fiber cells = `-inf`), `Eval/ScatterTest` (unwritten tropical cell = `-inf`); no existing fixture reads an unwritten tropical cell into a real statement.

Registration: `[[lean_lib]] name = "Tests", srcDir = "test"` with an EXPLICIT `globs` list in leanncd/lakefile.toml (tracked): a new module `Semantics.FooTest` must be added to that list (e.g. next to `"Semantics.SourceSortedAuditTest"`), else it is neither built by default nor by `lake build Tests`. Build a single test module with `bash leanncd/scripts/lake-build.sh <leanncd-dir> +Semantics.FooTest` (observed to work; `Tests:Semantics.FooTest` fails with "unknown lean_lib facet"). The default target builds everything (`defaultTargets = ["LeanNCD", "Tests"]`).

Wall clock (observed): the FIRST `+Semantics.SourceSortedDifferentialTest` build in this checkout took 2 m 04.6 s because ~8,556 jobs rebuilt (the oleans were stale at the start of the session), last step `Built Semantics.SourceSortedDifferentialTest (4.4s)`. A warm chain `+Eval.PropertyOracle.ScanOracle` (8,507 jobs, almost all cached) took 21.7 s, steps 4-6 s each. Typechecking one scratch file with `lean-file.sh` that imports the built `LeanNCD.Semantics.Source.SortedDifferential` and prints 5 `#eval`s: 4.8 s wall. The whole `Tests` target was not run and no record gives its time (searched the S3b/S3b-ii records: none).

## 7. Mutation manifest mechanics

`leanncd/scripts/mutation-manifest.sh [--cd dir] [--check] [--task id] [--out f.md] <leanncd-dir> <manifest.json> [label-prefix...]` (read @ its header). Manifest = JSON array of `{label, task?, file, old, new, targets : [lake module names], expect? : [strings that must appear in the mutated build log]}`; `--check` validates schema and that every selected `old` occurs EXACTLY ONCE, no build. Targets are written as module names (`"Eval.Plan.CompileTest"`). Sample entry @ papers/additive_s3b_mutations_post.json: `{label "T4-M3c (cast table: max-plus <-> min-plus accepted)", task "T4", file "LeanNCD/DSL/Pipeline/ScheduledValidation.lean", old "(k == .bool || (k.isTropical && a != k))", new "(k == .bool)", targets ["Eval.Plan.CompileTest"], expect ["error: test/Eval/Plan/CompileTest.lean:", "max-plus statement reads a min-plus"]}`.

I assembled a scratch manifest (not in the repo: `/private/tmp/claude-501/-Users-williammacready-code-python-pyncd/41d76814-d0ae-476d-88b2-ba0c8e1cd79d/scratchpad/manifest_check.json`) of the three existing entries plus five new ones and ran `mutation-manifest.sh --check` on it: **`manifest OK: 8 entries, 8 selected, every old-string unique`** (observed). Existing entries: `T9-M1` (R1/R12), `T4-M3c` (R4), `T4-M3b` (R4b), all still unique at HEAD in their files. `T9-M1` old text is `"      r.nonlin == .identity &&\n      match r.body.terms with"`, new `"      match r.body.terms with"` (file `LeanNCD/DSL/Ast.lean`).

New entries, proposed `old`/`new` (unique at HEAD; targets/expect to be filled by the plan; none of these mutated builds were run; the R11/R9/R10 replacement bodies were type-checked as copies in a scratch file, observed, no error):
```
R6   file LeanNCD/DSL/Ast.lean
     old "ls.all (fun l => l.axisUids.eraseDups.length ≤ 1) &&\n                  es.all"
     new "es.all"
R16  file LeanNCD/DSL/Ast.lean
     old "(idxAffineForm e).2.all (fun p => lhs.contains p.2)"
     new "(idxAffineForm e).2.all (fun p => lhs.contains p.2 || true)"
R11  file LeanNCD/DSL/Ast.lean          (in writerVotes)
     old "  | own => own\n"
     new "  | own => own ++ (ws.filter Stmt.isSortNeutral).map (Stmt.algebra env)\n"
R9   file LeanNCD/DSL/Ast.lean          (in writerVotes)
     old "  | [] => (ws.map (Stmt.algebra env)).filter (· != .real)"
     new "  | [] => []"
R10  file LeanNCD/DSL/Pipeline/ScheduledValidation.lean   (in scheduleAlgebras, multi-writer arm)
     old "            | none => pure ()\n    | .scan _ _ b r _ =>"
     new "            | none =>\n              match writerVotes env ws with\n              | a :: _ => m := m.insert nm a\n              | [] => pure ()\n    | .scan _ _ b r _ =>"
```
Notes: the source uses `≤` (the audit text says `<=`). R6 also exists in `oracleNeutral` as `!collidingSlot`; the mutation above is production-only, which is the point. R11's `new` makes neutrals vote with their own (incl. `real`) annotation; with it both rows of (a) become conflicts. R16's `new` keeps `lhs` used so no unused-variable warning.

## 8. Stale or contradicted claims

- **`SourceSortedDifferentialTest` comment (before `bellman`)**: "production refuses max + min (`multiWriterAlgebra`) and accepts max + the sum copy". Observed: `bellman .max .min` is ACCEPTED (min copy is neutral, abstains, runs as max; `Y=[20,7,17,40]`). The `multiWriterAlgebra` refusal needs two non-neutral voters (section 5 (b)) or an all-neutral max+min group (5 (c)). The `#guard_msgs` for `classOf (bellman .max .min)` (`refused ... mixedSorts`) is still correct.
- Design section 4 R10 and the brief's shape (c): `T[i]:=maxreduce(N[i])` beside `T[i]:=minreduce(B[i,j])` is accepted (min group). The R10 distinguishing shape is the all-neutral max+min group over a min-plus `N`, max-writer first (section 5 (c)).
- Design section 4 R16 says "oracle predicts refusal": production refuses with `multiWriterAlgebra "Y"` (observed); `compareSortedSource` today refuses it at selection with `mixedSorts [sum,max]`, so the existing path cannot tell R16 apart (no classification to flip) until the new refusal-prediction path exists.
- Design D7: confirmed, the false `nativeFailure` is what `compareSortedSource` reports today for all three group shapes (5 (e)).
- Audit section 0 H4 / design section 5 "NOT yet observed": now observed, PASS (section 0).
- Audit section 3 R11 mutation site "`writerVotes` lets neutrals vote": the real arms are `| [] => ... filter (· != .real)` (all-neutral fallback, R9) and `| own => own` (R11); both single-line unique texts (section 7).
- Audit says private helpers are reusable; `oracleIdxUids`/`oracleSlotUids`/`neutralShapes`/`corpusStmts` are `private` (section 3).
- Design D8 / T5: `Semantics.SourceSortedAuditTest` and `SourceSortedDifferentialTest` do not share fixtures (separate private copies, different `k` extent), so "re-express ~12-16 existing programs" means re-declaring helpers per new module or un-privatising.
- Everything else in the design checked against the tree matched: `SortedRun`/`SortedClassification` are not used by other test files beyond the two Source sorted tests; no exhaustive `match` on `Unsupported` exists, so `nonFiniteIntoReal` is purely additive.

-- test/DSL/ComplexElementTypeTest.lean
import LeanNCD.DSL.Compile
import LeanNCD.Eval.Entry
import LeanNCD.Eval.Scan
import LeanNCD.Eval.Scatter
import LeanNCD.Eval.Plan.Compile
import LeanNCD.Eval.Plan.Signature

/-!
# Complex element types are SPELLED but REJECTED

`tensor complex64 A(i)`, `tensor complex128 A(i)` and `linear complex64 W(a, b)` parse
(`ParseProgramTest.lean`) but have no semantics: complex is a different scalar DOMAIN, not another
real precision, and the categorical branch (`compile` → `route`) erases the element type — sound
only for `f32`/`f64` (`papers/f32_evalplan.md` §1.1–§1.3). So every complex declaration, used or
not, is rejected with `CompileError.unsupportedElementType <name> <spelling>` by `buildDeclEnv`
(`rejectComplexDecls`), before any lowering.

Every program is built with `tlprog!` and compiled at RUNTIME (`.compile`/`.compileToScheduled`):
`tl!{}` would fail the build at elaboration. Each rejected program has an accept-neighbour that
differs only in the element-type word.
-/

namespace LeanNCD.ComplexElementTypeTest

private def compileErr (p : TLProgram) : Option CompileError :=
  match p.compile.run 0 with
  | .error e _ => some e
  | .ok _ _    => none

private def scheduleErr (p : TLProgram) : Option CompileError :=
  match p.compileToScheduled.run 0 with
  | .error e _ => some e
  | .ok _ _    => none

/-- Both source entries reject with exactly `e`. -/
private def bothReject (p : TLProgram) (e : CompileError) : Bool :=
  compileErr p == some e && scheduleErr p == some e

/-- Both source entries accept. -/
private def bothAccept (p : TLProgram) : Bool :=
  compileErr p == none && scheduleErr p == none

/-! ## `tensor complex64`, and its real neighbours -/

private def c64Tensor : TLProgram := tlprog!{
  tensor complex64 A(i)
  Y[i] := A[i]
}
private def f32Tensor : TLProgram := tlprog!{
  tensor f32 A(i)
  Y[i] := A[i]
}
private def f64Tensor : TLProgram := tlprog!{
  tensor f64 A(i)
  Y[i] := A[i]
}
private def plainTensor : TLProgram := tlprog!{
  tensor A(i)
  Y[i] := A[i]
}

#guard bothReject c64Tensor (.unsupportedElementType "A" "complex64")
#guard bothAccept f32Tensor
#guard bothAccept f64Tensor
#guard bothAccept plainTensor

/-! ## `tensor complex128`, grouped: the FIRST complex declaration is named -/

private def c128Group : TLProgram := tlprog!{
  tensor complex128 A(i), B(j)
  Y[i] := A[i]
}
private def f64Group : TLProgram := tlprog!{
  tensor f64 A(i), B(j)
  Y[i] := A[i]
}

#guard bothReject c128Group (.unsupportedElementType "A" "complex128")
#guard bothAccept f64Group

/-! ## `linear complex64` -/

private def c64Linear : TLProgram := tlprog!{
  linear complex64 W(a, b) bias
  Y[a] := W[a, b] · X[b]
}
private def f32Linear : TLProgram := tlprog!{
  linear f32 W(a, b) bias
  Y[a] := W[a, b] · X[b]
}
private def plainLinear : TLProgram := tlprog!{
  linear W(a, b) bias
  Y[a] := W[a, b] · X[b]
}

#guard bothReject c64Linear (.unsupportedElementType "W" "complex64")
#guard bothAccept f32Linear
#guard bothAccept plainLinear

/-! ## An UNUSED complex declaration is still rejected

Unlike an unused `tensor f32 Unused(i)`, which constrains nothing and is accepted, a complex
declaration has no reading at all, so it is refused even when no statement mentions it. -/

private def c128Unused : TLProgram := tlprog!{
  tensor complex128 Unused(i)
  Y[i] := X[i]
}
private def f32Unused : TLProgram := tlprog!{
  tensor f32 Unused(i)
  Y[i] := X[i]
}

#guard bothReject c128Unused (.unsupportedElementType "Unused" "complex128")
#guard bothAccept f32Unused

/-! ## Complex mixed with a real precision reports the COMPLEX rejection

`rejectComplexDecls` runs first inside `buildDeclEnv`, so complex wins over everything that
follows it — on the source path there is no mixed-precision rejection at all (the f32 + explicit
f64 neighbour below compiles), and on the checked backend the f32/f64 mix is `prepareEvalPlan`'s
later Step 0b. The complex declaration is placed SECOND to show order in `decls` does not let the
real one win. -/

private def c64MixF32 : TLProgram := tlprog!{
  tensor f32 A(i)
  tensor complex64 B(i)
  Y[i] := A[i] · B[i]
}
private def c128MixF64 : TLProgram := tlprog!{
  tensor f64 A(i)
  tensor complex128 B(i)
  Y[i] := A[i] · B[i]
}
private def f32MixF64 : TLProgram := tlprog!{
  tensor f32 A(i)
  tensor f64 B(i)
  Y[i] := A[i] · B[i]
}

#guard bothReject c64MixF32 (.unsupportedElementType "B" "complex64")
#guard bothReject c128MixF64 (.unsupportedElementType "B" "complex128")
#guard bothAccept f32MixF64

/-! ## Complex wins over a duplicate declaration of the same name

`buildDeclEnv`'s two rejections are ordered complex-first; a schedule violating both reports the
complex one. -/

private def c64Dup : TLProgram := tlprog!{
  tensor A(i)
  tensor complex64 A(i)
  Y[i] := A[i]
}
#guard bothReject c64Dup (.unsupportedElementType "A" "complex64")

/-! ## Every entry, every case: the case × entry table

Columns are the seven declaration cases. Rows are every public entry that reads `Decl`s, found by
grepping for `List Decl`/`ScheduledProgram`/`DeclEnv` parameters. `R` = rejected, `R*` = rejected
through more than one guard (removing the first still rejects). `evalScheduled`'s `+f32` cell is
plain `R`: without `validateScheduled`'s rejection its f32 refusal (`unsupportedDtype "A"`) fires
before `evalPlain`'s guard. `prepareEvalPlan`'s second guard (`checkDecl`) reports a capability
error, not the `sourceInvariant` one. `rejectionFailures` below runs every entry on every case and
asserts each cell's FINAL rejection (which error the entry reports); it does NOT assert whether a
cell is guarded once or by several guards, so `R` vs `R*` is documentation, not a checked claim.

| entry | guard | t c64 | t c128 | lin c64 | lin c128 | unused | +f32 | +f64 |
|---|---|---|---|---|---|---|---|---|
| `TLProgram.compile` | `resolveDecls`→`buildDeclEnv`, then `route` | R* | R* | R* | R* | R* | R* | R* |
| `TLProgram.compileToScheduled` | `resolveDecls`→`buildDeclEnv` | R | R | R | R | R | R | R |
| `Eval.TLProgram.eval` | via `compileToScheduled`, then `evalScheduled` | R* | R* | R* | R* | R* | R* | R* |
| `route` (hand-built logical schedule) | `physicalizeForRoute`→`rejectComplexDecls` | R | R | R | R | R | R | R |
| `validateScheduled` | `buildDeclEnv` | R | R | R | R | R | R | R |
| `evalScheduled` | `validateScheduled`, then `evalPlain`'s guard | R* | R* | R* | R* | R* | R | R* |
| `prepareEvalPlan` | Step 0 `validateScheduled` (`sourceInvariant`), then `checkDecl` | R* | R* | R* | R* | R* | R* | R* |
| `capabilityPreflight` | `checkDecl` (`unsupportedDtype "<name>: <spelling> element type"`) | R | R | R | R | R | R | R |
| `ofDenseInputsForDecls` / `ofDenseInputs32ForDecls` | `declEnvOrThrow`→`buildDeclEnv` (`.declaration`) | R | R | R | R | R | R | R |
| `evalPlain`, `evalAssignDtyped(Seeded)`, `evalStmtSliceSeeded`, `evalScan` | `rejectUnsupportedStorage`→`buildDeclEnv` (`.compile`) | R | R | R | R | R | R | R |
| `evalScatter` | `rejectComplexDecls` (`.compile`) | R | R | R | R | R | R | R |

Not entries, so no cell (named gaps; each needs a hand-built `DeclEnv`, or a physical program, that
skipped `buildDeclEnv`): `routeCore` (the physical stage behind `route`; a guard there would ripple
into the `RouteSpec` proofs); the env-taking helpers `storageConstraintOfName?`,
`scheduleStorageKind`, `scheduleFloat32Name?`, `checkDeclCarriers`, `checkScheduledReadRanks`,
`checkScheduledDtypes`, and the individual source phases (`checkDtypes`, …) on a hand-built
`ResolvedProgram`; and `combineFor`/`isPredicateDest`, which scan `decls` linearly and would
classify a complex destination as real — every public evaluator entry that calls them is guarded
above. `Acset/`, `Bridge/`, and the `run*` plan executors read no `Decl`.

Each row's NEIGHBOUR is the same list with every complex element type replaced by `.f64` and every
other name the program touches declared `f64` explicitly (an undeclared name is binary32 since the
f32 default flip, which would make the neighbour a mixed-precision schedule): it must be accepted, or (the `+f32` row, whose neighbour mixes f32 and f64) fail as it always did, never
with the complex rejection. -/

namespace Table
open Std Eval Eval.Plan

private def i : AxisSpec := { name := "i", uid := 1, kind := .real }

/-- What an entry did with a declaration list. -/
inductive Obs
  | ok
  | complex (nm ty : String)          -- `CompileError.unsupportedElementType`, in any wrapper
  | capability (context : String)     -- `CapabilityError.unsupportedDtype`
  | other
  deriving BEq, Repr

private def ofCompile : Except CompileError α → Obs
  | .ok _ => .ok
  | .error (.unsupportedElementType nm ty) => .complex nm ty
  | .error _ => .other

private def ofEval : Except EvalError α → Obs
  | .ok _ => .ok
  | .error (.compile (.unsupportedElementType nm ty)) => .complex nm ty
  | .error _ => .other

private def ofFresh : EStateM.Result CompileError Nat α → Obs
  | .ok _ _ => .ok
  | .error e _ => ofCompile (Except.error e : Except CompileError Unit)

structure Row where
  decls : List Decl
  nm : String
  ty : String

private def rows : List Row :=
  [ ⟨[.typedTensor .complex64 "A" [i]], "A", "complex64"⟩
  , ⟨[.typedTensor .complex128 "A" [i]], "A", "complex128"⟩
  , ⟨[.typedLinear .complex64 "A" [i] false], "A", "complex64"⟩
  , ⟨[.typedLinear .complex128 "A" [i] false], "A", "complex128"⟩
  , ⟨[.typedTensor .complex128 "Unused" [i]], "Unused", "complex128"⟩
  , ⟨[.typedTensor .f32 "A" [i], .typedTensor .complex64 "B" [i]], "B", "complex64"⟩
  , ⟨[.typedTensor .f64 "A" [i], .typedTensor .complex128 "B" [i]], "B", "complex128"⟩ ]

private def toF64 : Decl → Decl
  | .typedTensor ty nm ax => .typedTensor (if ty.isComplex then .f64 else ty) nm ax
  | .typedLinear ty nm ax b => .typedLinear (if ty.isComplex then .f64 else ty) nm ax b
  | d => d

/-- The neighbour of a row's declaration list: every complex element type replaced by `.f64`, and
    every name any entry's program reads or writes (`A`, `B`, `Y`; the scan's `X`, `S`) that is still undeclared spelled `f64`
    explicitly. Undeclared names are binary32 since the f32 default flip, so without this the
    all-binary64 neighbour would be a mixed f32/f64 schedule and be refused for the wrong reason. -/
private def neighbour (ds : List Decl) : List Decl :=
  let ds := ds.map toF64
  ds ++ ["A", "B", "Y", "X", "S"].filterMap fun nm =>
    if ds.any (·.name == nm) then none else some (.typedTensor .f64 nm [i])

private def rhsAB : RHSExpr :=
  { body := { terms := [{ factors := [.read "A" [.axis i], .read "B" [.axis i]] }] }
  , nonlin := .identity }
private def stmtY : Stmt := .assign "Y" [.free i] rhsAB
private def prog (decls : List Decl) : TLProgram := { decls, stmts := [stmtY] }
private def sched (decls : List Decl) : ScheduledProgram :=
  { decls, stmts := [.plain stmtY], env := {}, extNames := {"A", "B"}, explicitSizes := {} }
private def vec2 : DenseTensor := ⟨[2], #[1.0, 2.0]⟩
private def inputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" vec2).insert "B" vec2
private def sizes : HashMap UID Nat := ({} : HashMap UID Nat).insert 1 2

-- `ScanTest.lean`'s S-B 1 scan, fully sized: `S[2*j, 0] := X[j]; S[o, l+1] := S[o, l]`.
private def sj : AxisSpec := { name := "j", uid := 11, kind := .real }
private def so : AxisSpec := { name := "o", uid := 12, kind := .real }
private def sl : AxisSpec := { name := "l", uid := 19, kind := .nat }
private def scanNode : ScanStmt :=
  .scan "S" [sl]
    [.scatter "S" [.affine (.scale 2 sj), .iterAt sl 0]
      { body := { terms := [{ factors := [.read "X" [.axis sj]] }] }, nonlin := .identity }
      { fill := 0, reduce := .rejectCollisions }]
    [.assign "S" [.free so, .iterNext sl]
      { body := { terms := [{ factors := [.read "S" [.axis so, .axis sl]] }] }, nonlin := .identity }]
    false
private def scanEnv : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[3], #[1.0, 2.0, 3.0]⟩
private def scanSizes : HashMap UID Nat :=
  ((({} : HashMap UID Nat).insert 11 3).insert 12 6).insert 19 3

/-- Every entry point that reads declarations, by name. -/
private def entries : List (String × (List Decl → Obs)) :=
  [ ("compile", fun ds => ofFresh ((prog ds).compile.run 0))
  , ("compileToScheduled", fun ds => ofFresh ((prog ds).compileToScheduled.run 0))
  , ("TLProgram.eval", fun ds => match LeanNCD.Eval.TLProgram.eval (prog ds) inputs with
      | .ok _ => .ok
      | .error f => ofEval (Except.error f.error : Except EvalError Unit))
  , ("route", fun ds => ofFresh ((route (sched ds)).run 0))
  , ("validateScheduled", fun ds => ofCompile (validateScheduled (sched ds)))
  , ("evalScheduled", fun ds => match evalScheduled (sched ds) inputs with
      | .ok _ => .ok
      | .error f => ofEval (Except.error f.error : Except EvalError Unit))
  , ("prepareEvalPlan", fun ds =>
      match prepareEvalPlan (sched ds) (InputSignature.ofDenseInputs inputs) with
      | .ok _ => .ok
      | .error { cause := .sourceInvariant (.unsupportedElementType nm ty), .. } => .complex nm ty
      | .error _ => .other)
  , ("capabilityPreflight", fun ds => match capabilityPreflight (sched ds) with
      | .ok _ => .ok
      | .error (.unsupportedDtype ctx) => .capability ctx
      | .error _ => .other)
  , ("ofDenseInputsForDecls", fun ds => match InputSignature.ofDenseInputsForDecls ds inputs with
      | .ok _ => .ok
      | .error (.declaration (.unsupportedElementType nm ty)) => .complex nm ty
      | .error _ => .other)
  , ("ofDenseInputs32ForDecls", fun ds =>
      match InputSignature.ofDenseInputs32ForDecls ds ({} : HashMap String DenseTensor32) with
      | .ok _ => .ok
      | .error (.declaration (.unsupportedElementType nm ty)) => .complex nm ty
      | .error _ => .other)
  , ("evalPlain", fun ds => ofEval (evalPlain ds inputs sizes stmtY))
  , ("evalAssignDtyped", fun ds => ofEval (evalAssignDtyped ds inputs sizes "Y" [.free i] rhsAB))
  , ("evalAssignDtypedSeeded", fun ds =>
      ofEval (evalAssignDtypedSeeded ds inputs sizes {} "Y" [.free i] rhsAB))
  , ("evalStmtSliceSeeded", fun ds => ofEval (evalStmtSliceSeeded ds inputs sizes {} stmtY))
  , ("evalScatter", fun ds => ofEval (evalScatter ds inputs sizes "Y" [.affine (.scale 2 i)] rhsAB
      { fill := 0, reduce := .rejectCollisions } [4]))
  , ("evalScan", fun ds => ofEval (evalScan ds scanEnv scanSizes scanNode)) ]

/-- The rejection each entry must report for a row: the typed `CompileError` (in the entry's own
    wrapper), or `capabilityPreflight`'s capability context naming the declaration and spelling. -/
private def expected (entry : String) (r : Row) : Obs :=
  if entry == "capabilityPreflight" then .capability s!"{r.nm}: {r.ty} element type"
  else .complex r.nm r.ty

/-- The failing (entry, row) cells; `[]` means every cell of the table holds. -/
private def rejectionFailures : List (String × String) :=
  entries.flatMap fun (nm, run) =>
    rows.filterMap fun r =>
      if run r.decls == expected nm r then none else some (nm, r.nm ++ ":" ++ r.ty)

/-- The failing neighbour cells: an all-binary64 neighbour must be ACCEPTED; the `+f32` row's
    neighbour may fail as before (`.other`), but never with a complex or capability rejection. -/
private def neighbourFailures : List (String × String) :=
  entries.flatMap fun (nm, run) =>
    rows.filterMap fun r =>
      let mixedF32 := r.decls.any (· == .typedTensor .f32 "A" [i])
      let good := match run (neighbour r.decls) with
        | .ok => true
        | .other => mixedF32
        | _ => false
      if good then none else some (nm, r.nm ++ ":" ++ r.ty)

#guard entries.length == 16
#guard rows.length == 7
#guard rejectionFailures == []
#guard neighbourFailures == []

/-! ### The f32 + f64 neighbour still gets its mixed-precision rejection

Pins only that the `+f32` row's neighbour (the complex declaration replaced by f64) is still
refused by `prepareEvalPlan`'s Step 0b mixed f32/f64 storage rejection, a capability error rather
than the complex one. That the complex declaration's own rejection comes first is asserted by the
`+f32` row of `rejectionFailures` above, not here. -/

#guard match prepareEvalPlan (sched [.typedTensor .f32 "A" [i], .typedTensor .f64 "B" [i]])
    (InputSignature.ofDenseInputs inputs) with
  | .error { cause := .capability (.unsupportedDtype "B: mixed f32/f64 storage in one schedule"), .. } =>
      true
  | _ => false

end Table

end LeanNCD.ComplexElementTypeTest

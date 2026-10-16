import LeanNCD.DSL.Pipeline.Collect
import LeanNCD.DSL.Compile

/-! Structural tests for `desugarMultiWriters` (additive collection, slice 1).

Each fixture pins one structural fact of the desugar on a real schedule (from `tlprog!` through
`compileToScheduled`, or hand-built where surface syntax cannot reach the case): at most one writer
per name afterwards, writers renamed in place and in order, the collector reads exactly its group,
declaration clones, freshness, the identity on single-writer schedules, and the slice-1 rejections.
Values are checked separately, through the evaluator (`test/Eval/EntryTest.lean`). -/

namespace LeanNCD.CollectTest
open LeanNCD

/-- The plain statements of a schedule, or `none` if it has a scan node. -/
private def plainStmts (stmts : List ScanStmt) : Option (List Stmt) :=
  stmts.mapM fun | .plain s => some s | _ => none

private def scheduled (p : TLProgram) : Option ScheduledProgram :=
  match p.compileToScheduled.run 0 with
  | .ok sp _ => some sp
  | .error _ _ => none

private def desugared (p : TLProgram) : Option (Except CompileError (ScheduledProgram × List String)) :=
  (scheduled p).map desugarMultiWriters

/-- Destination names of a desugared schedule, in order. -/
private def dests (p : TLProgram) : Option (List String) :=
  match desugared p with
  | some (.ok (sp, _)) => (plainStmts sp.stmts).map (·.map Stmt.lhsName)
  | _ => none

/-- The read names of the statement writing `nm`. -/
private def readsOf (p : TLProgram) (nm : String) : Option (List String) :=
  match desugared p with
  | some (.ok (sp, _)) => ((plainStmts sp.stmts).bind (·.find? (·.lhsName == nm))).map
      (fun s => s.readFactors.map (·.1))
  | _ => none

private def errorOf (p : TLProgram) : Option CompileError :=
  match desugared p with
  | some (.error e) => some e
  | _ => none

private def generatedOf (p : TLProgram) : Option (List String) :=
  match desugared p with
  | some (.ok (_, g)) => some g
  | _ => none

-- C1 (donor: F14 `multiDefinition`, SourceDifferentialPolicyTest): two writers of Y are renamed
-- in place and in order, the collector follows the last writer and reads exactly Y#1, Y#2.
def c1 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Y[i] := B[i]
}
#guard dests c1 == some ["Y#1", "Y#2", "Y"]
#guard readsOf c1 "Y#1" == some ["A"]
#guard readsOf c1 "Y#2" == some ["B"]
#guard readsOf c1 "Y" == some ["Y#1", "Y#2"]
#guard generatedOf c1 == some ["Y#1", "Y#2"]

-- C2 (clone c1, add a third writer and a reader): at most one writer per name afterwards, and the
-- reader still follows the collector.
def c2 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Y[i] := B[i]
  Y[i] := C[i]
  Z[i] := Y[i]
}
#guard dests c2 == some ["Y#1", "Y#2", "Y#3", "Y", "Z"]
#guard (dests c2).map (fun ds => ds.eraseDups.length == ds.length) == some true

-- C3 identity (accept-neighbour of c1: one writer): the schedule is returned unchanged.
def c3 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Z[i] := Y[i]
}
#guard
  match scheduled c3 with
  | some sp => match desugarMultiWriters sp with
    | .ok (sp', g) => g.isEmpty && plainStmts sp'.stmts == plainStmts sp.stmts && sp'.decls == sp.decls
    | .error _ => false
  | none => false

-- C4 declaration cloning (clone c1, declare Y `predicate`): one predicate clone per writer.
def c4 : TLProgram := tlprog!{
  axis i : ℕ = 2
  predicate Y(i)
  Y[i] := A[i]
  Y[i] := B[i]
}
#guard
  match desugared c4 with
  | some (.ok (sp, _)) =>
      (sp.decls.filter (fun d => d.name.startsWith "Y")).map (fun d => match d with
        | .predicate n _ => n | _ => "") == ["Y", "Y#1", "Y#2"]
  | _ => false

-- C4b (clone c4, declare Y `tensor f64`): clones carry the element type.
def c4b : TLProgram := tlprog!{
  axis i : ℕ = 2
  tensor f64 Y(i)
  Y[i] := A[i]
  Y[i] := B[i]
}
#guard
  match desugared c4b with
  | some (.ok (sp, _)) =>
      (sp.decls.filter (fun d => d.name.startsWith "Y")).map Decl.elementType? ==
        [some .f64, some .f64, some .f64]
  | _ => false

-- C5 rejection: scatter writers (decision note probe `S[2*i]:=X[i]; S[2*i+1]:=Y[i]`).
def c5 : TLProgram := tlprog!{
  axis i : ℕ = 2
  S[2*i] := X[i]
  S[2*i + 1] := Y[i]
}
#guard errorOf c5 == some (.multiWriterScatter "S")

-- C6 rejection: max-annotated multi-writer set (clone c1, change agg to maxreduce).
def c6 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := maxreduce(A[i, j])
  Y[i] := maxreduce(B[i, j])
}
#guard errorOf c6 == some (.multiWriterAlgebra "Y")

-- C7 rejection: axis-UID mismatch (clone c1, writer 2 on axis j).
def c7 : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  Y[i] := A[i]
  Y[j] := B[j]
}
#guard errorOf c7 == some (.writerShapeMismatch "Y" 2 0)

-- C7b accept-neighbour of c7: both writers on i.
#guard (dests c1).isSome

-- C8 rejection: a source name already spells a generated name (programmatic only).
private def ax : AxisSpec := { name := "i", uid := 1, kind := .nat }
private def copyStmt (dst src : String) : Stmt :=
  .assign dst [.free ax] { body := ⟨[⟨[.read src [.axis ax]]⟩]⟩, nonlin := .identity }
private def c8 : ScheduledProgram :=
  { decls := [], env := {}, extNames := ∅, explicitSizes := {}
    stmts := [.plain (copyStmt "Y#1" "A"), .plain (copyStmt "Y" "B"), .plain (copyStmt "Y" "C")] }
#guard match desugarMultiWriters c8 with
  | .error e => e == .reservedNameCollision "Y#1"
  | .ok _ => false
-- C8b accept-neighbour: rename the clashing source name.
#guard match desugarMultiWriters { c8 with stmts := [.plain (copyStmt "Q" "A"),
    .plain (copyStmt "Y" "B"), .plain (copyStmt "Y" "C")] } with
  | .ok (_, g) => g == ["Y#1", "Y#2"]
  | .error _ => false

end LeanNCD.CollectTest

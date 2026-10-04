import Eval.ExplicitF64
/-!
# `explicitF64Decls` — why it exists and what it must never do

The helper lets a reference-evaluator test stay a binary64 regression gate WITHOUT relying on the
pipeline's default storage for undeclared names (the default is planned to become binary32, which
the binary64-only evaluator refuses). Its whole contract is therefore:

1. after it runs, EVERY storage name of the program (`stmtStorageNames`: each destination and
   read source) is DECLARED — so nothing depends on the undeclared-name default any more;
2. it is semantics-neutral today (binary64 is the current default), so the evaluated result is
   unchanged;
3. it adds declarations ONLY for undeclared names: an `f32`, plain, or `predicate` declaration is
   never rewritten, so an `f32`-declared name is still refused (`unsupportedDtype`), never silently
   turned into binary64; `axis`/`iter` declarations are untouched.
-/
namespace LeanNCD.Eval.ExplicitF64Test
open Std LeanNCD LeanNCD.Eval LeanNCD.Eval.ExplicitF64

private def matvec : TLProgram := tlprog!{ y[i] := A[i, j] · x[j] }

private def inputs : HashMap String DenseTensor :=
  HashMap.ofList [("A", ⟨[2, 2], #[1, 2, 3, 4]⟩), ("x", ⟨[2], #[1, 1]⟩)]

/-- Every storage name of `p` is declared (i.e. nothing rides on the undeclared-name default). -/
private def allStorageDeclared (p : TLProgram) : Bool :=
  match buildDeclEnv p.decls with
  | .ok env => (p.stmts.flatMap stmtStorageNames).all env.contains
  | .error _ => false

-- (1) WITHOUT the helper the program leans on the default for all three names (so the planned
-- f32 flip would make the evaluator refuse it); WITH it, none does.
#guard !allStorageDeclared matvec
#guard allStorageDeclared matvec.explicitF64

-- The added declarations are exactly `tensor f64` with the use-site rank (A: 2, x: 1, y: 1).
#guard (matvec.explicitF64.decls.filterMap fun d => match d with
    | .typedTensor .f64 n ax => some (n, ax.length) | _ => none)
  == [("y", 1), ("A", 2), ("x", 1)]

-- (2) The helper's program means exactly what the hand-written explicit-`f64` program means — a
-- comparison that never consults the undeclared-name default, so it holds before AND after the
-- default flips. (Neutrality against the UNDECLARED program is a pre-flip-only fact; it is
-- covered by every migrated module staying green on unflipped code, not asserted here.)
private def matvecDeclared : TLProgram := tlprog!{
  tensor f64 y(i), A(i, j), x(j)
  y[i] := A[i, j] · x[j] }
private def outY (p : TLProgram) : Option (List Float) :=
  ((TLProgram.eval p inputs).toOption.bind (·.env["y"]?)).map (·.data.toList)
#guard outY matvecDeclared == some [3, 7]
#guard outY matvec.explicitF64 == outY matvecDeclared

-- A constant index (`X[0]`) names no axis; the declared rank still comes from the use site, with
-- a program axis standing in for the missing one.
#guard ((tlprog!{ y[i] := X[0] · W[i] }).explicitF64.decls.filterMap fun d => match d with
    | .typedTensor .f64 n ax => some (n, ax.length) | _ => none)
  == [("y", 1), ("X", 1), ("W", 1)]

-- (3) Declared names are left alone. An `f32`-declared destination keeps its declaration and is
-- STILL refused as `unsupportedDtype`; the helper only declares the undeclared reads.
private def f32Dest : TLProgram := tlprog!{
  tensor f32 y(i)
  y[i] := A[i, j] · x[j] }

#guard f32Dest.explicitF64.decls.take f32Dest.decls.length == f32Dest.decls
#guard !(f32Dest.explicitF64.decls.drop f32Dest.decls.length).any (·.name == "y")
#guard match TLProgram.eval f32Dest.explicitF64 inputs with
  | .error f => match f.error with | .unsupportedDtype "y" => true | _ => false
  | .ok _ => false

-- Predicate, plain-`tensor`, and axis declarations are preserved verbatim and not re-declared.
private def mixedDecls : List Decl :=
  [.predicate "P" [], .tensor "T" [], .typedTensor .f32 "F" []]
private def mixedStmts : List Stmt :=
  (tlprog!{ Z[] := P[] · T[] · F[] · U[] }).stmts
#guard (explicitF64Decls mixedDecls mixedStmts).take 3 == mixedDecls
#guard ((explicitF64Decls mixedDecls mixedStmts).drop 3).map (·.name) == ["Z", "U"]

-- A malformed declaration list (duplicate) is returned unchanged, so the evaluator reports it.
#guard explicitF64Decls [.tensor "Y" [], .tensor "Y" []] [] == [.tensor "Y" [], .tensor "Y" []]

end LeanNCD.Eval.ExplicitF64Test

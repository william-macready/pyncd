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

-- Axis, iter, predicate, plain-`tensor`, and `f32` declarations are preserved verbatim, in order,
-- and not re-declared; only the undeclared names are appended after them.
private def axI : AxisSpec := ⟨"i", 1, .real⟩
private def axJ : AxisSpec := ⟨"j", 2, .real⟩
private def axK : AxisSpec := ⟨"k", 3, .real⟩
private def axL : AxisSpec := ⟨"l", 4, .nat⟩
private def mixedDecls : List Decl :=
  [.axis axI (some 2), .iter axL 3, .predicate "P" [], .tensor "T" [], .typedTensor .f32 "F" []]
private def mixedStmts : List Stmt :=
  (tlprog!{ Z[] := P[] · T[] · F[] · U[] }).stmts
#guard (explicitF64Decls mixedDecls mixedStmts).take 5 == mixedDecls
#guard ((explicitF64Decls mixedDecls mixedStmts).drop 5).map (·.name) == ["Z", "U"]

/-! ### Helper edge cases, each on a statement list built directly so the one thing it varies is
the only thing it varies. -/

/-- `Y[ls] := n[es]` as a one-factor assignment. -/
private def asg (y : String) (ls : List LHSSlot) (n : String) (es : List IdxExpr) : Stmt :=
  .assign y ls ⟨⟨[⟨[.read n es]⟩]⟩, .identity, .sum⟩

/-- The declarations `explicitF64Decls decls stmts` appends. -/
private def added (decls : List Decl) (stmts : List Stmt) : List Decl :=
  (explicitF64Decls decls stmts).drop decls.length

-- A malformed declaration list (duplicate) is returned unchanged, so the evaluator reports it.
-- The statement list is NON-EMPTY and reads undeclared names (`Z`, and the written `W`): a helper
-- that skipped its error branch and appended anyway would return a longer list.
#guard explicitF64Decls [.tensor "Y" [], .tensor "Y" []] [asg "W" [] "Z" []]
  == [.tensor "Y" [], .tensor "Y" []]

-- (a) Idempotent: a second pass finds every derivable name already declared (and a name with no
-- derivable axis stays undeclared on both passes).
#guard explicitF64Decls (explicitF64Decls [] matvec.stmts) matvec.stmts
  == explicitF64Decls [] matvec.stmts
#guard explicitF64Decls (explicitF64Decls mixedDecls mixedStmts) mixedStmts
  == explicitF64Decls mixedDecls mixedStmts
#guard explicitF64Decls (explicitF64Decls [] [asg "Y" [.affine (.const 0)] "X" [.const 0]])
    [asg "Y" [.affine (.const 0)] "X" [.const 0]]
  == explicitF64Decls [] [asg "Y" [.affine (.const 0)] "X" [.const 0]]

-- (b) A name that occurs several times in `stmtStorageNames` order is declared exactly ONCE (read
-- twice in one statement, and written-then-read across statements); the result stays well formed.
private def dupStmts : List Stmt :=
  [ .assign "Y" [.free axI] ⟨⟨[⟨[.read "A" [.axis axI, .axis axJ], .read "A" [.axis axJ, .axis axK]]⟩]⟩, .identity, .sum⟩
  , asg "Z" [.free axI] "Y" [.axis axI] ]
#guard (added [] dupStmts).map (·.name) == ["Y", "A", "Z"]
#guard (buildDeclEnv (explicitF64Decls [] dupStmts)).toOption.isSome

-- (c) The first WRITE decides a name's axes, not the first read: `N` is read as `N[i]` before it is
-- written as `N[j]`; the declaration carries `j` (the write's axis), not `i` (the read's).
private def readThenWrite : List Stmt :=
  [asg "Out" [.free axI] "N" [.axis axI], asg "N" [.free axJ] "W" [.axis axJ]]
#guard (added [] readThenWrite).find? (·.name == "N") == some (.typedTensor .f64 "N" [axJ])

-- (d) Slots with no plain `free` axis still give the right RANK: a scatter `.affine` LHS slot, a
-- scan `.iterAt`/`.iterNext` slot, and an `.affine (.const _)` slot that names no axis of its own.
private def slotStmts : List Stmt :=
  [ .scatter "Sc" [.affine (.scale 2 axI), .affine (.shift axJ 1)] ⟨⟨[⟨[.read "X" [.axis axI, .axis axJ]]⟩]⟩, .identity, .sum⟩ {}
  , asg "G" [.free axJ, .iterAt axL 0] "G0" [.axis axJ]
  , asg "H" [.iterNext axL, .free axJ] "G" [.axis axJ, .axis axL]
  , asg "K" [.free axI, .affine (.const 0)] "M" [.axis axI, .axis axI] ]
#guard (added [] slotStmts).filterMap (fun d => match d with
    | .typedTensor .f64 n ax => some (n, ax.length) | _ => none)
  == [("Sc", 2), ("X", 2), ("G", 2), ("G0", 1), ("H", 2), ("K", 2), ("M", 2)]
#guard (added [] slotStmts).find? (·.name == "Sc") == some (.typedTensor .f64 "Sc" [axI, axJ])

-- (e) A name with no usable axis anywhere in the statements stays UNDECLARED (a later refusal stays
-- loud rather than a wrong-rank declaration).
#guard explicitF64Decls [] [asg "Y" [.affine (.const 0)] "X" [.const 0]] == []

-- (f) A predicate used as a DESTINATION keeps its `.predicate` declaration unchanged.
#guard explicitF64Decls [.predicate "P" [axI]] [asg "P" [.free axI] "A" [.axis axI]]
  == [.predicate "P" [axI], .typedTensor .f64 "A" [axI]]

-- (g) A `%`-prefixed generated name is declared like any other name.
#guard added [] [asg "%T_0" [.free axI] "%U_1" [.axis axI]]
  == [.typedTensor .f64 "%T_0" [axI], .typedTensor .f64 "%U_1" [axI]]

end LeanNCD.Eval.ExplicitF64Test

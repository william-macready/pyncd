-- LeanNCD/DSL/Traverse.lean
import LeanNCD.DSL.Ast
import LeanNCD.DSL.TraverseAxes

namespace LeanNCD

/-- Apply a UID remap to a single AxisSpec (name is display-only; preserved). -/
def AxisSpec.mapUID (f : UData → UData) (a : AxisSpec) : AxisSpec :=
  { a with uid := (f ⟨a.uid, some a.name⟩).uid }

theorem AxisSpec.mapUID_metadata (f : UData → UData) (a : AxisSpec) :
    (AxisSpec.mapUID f a).name = a.name ∧ (AxisSpec.mapUID f a).kind = a.kind :=
  ⟨rfl, rfl⟩

/-- The `Id` instantiation of `IdxExpr.traverseAxes`. -/
def IdxExpr.mapUID (f : UData → UData) (e : IdxExpr) : IdxExpr :=
  IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) e

/-- The `ConstL`-free `Id` instantiation of `PredArith.traverseAxes`. -/
def PredArith.mapUID (f : UData → UData) (e : PredArith) : PredArith :=
  PredArith.traverseAxes (f := Id) (AxisSpec.mapUID f) e

/-- The `ConstL`-free `Id` instantiation of `BoolExpr.traverseAxes`. -/
def BoolExpr.mapUID (f : UData → UData) (e : BoolExpr) : BoolExpr :=
  BoolExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) e

/-- The `Id` instantiation of `Nonlin.traverseAxes`. -/
def Nonlin.mapUID (f : UData → UData) (n : Nonlin) : Nonlin :=
  Nonlin.traverseAxes (f := Id) (AxisSpec.mapUID f) n

/-- The `Id` instantiation of `Factor.traverseAxes`. -/
def Factor.mapUID (f : UData → UData) (x : Factor) : Factor :=
  Factor.traverseAxes (f := Id) (AxisSpec.mapUID f) x

/-- The `Id` instantiation of `ProdTerm.traverseAxes`. -/
def ProdTerm.mapUID (f : UData → UData) (p : ProdTerm) : ProdTerm :=
  ProdTerm.traverseAxes (f := Id) (AxisSpec.mapUID f) p

/-- The `Id` instantiation of `SumExpr.traverseAxes`. -/
def SumExpr.mapUID (f : UData → UData) (s : SumExpr) : SumExpr :=
  SumExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) s

/-- The `Id` instantiation of `RHSExpr.traverseAxesWithMask` (mask included, matching
    `specsRHS`/`RHSExpr.mapUID`'s always-remap-the-mask semantics). -/
def RHSExpr.mapUID (f : UData → UData) (r : RHSExpr) : RHSExpr :=
  RHSExpr.traverseAxesWithMask (f := Id) (AxisSpec.mapUID f) r

/-- The `Id` instantiation of `LHSSlot.traverseAxes`. -/
def LHSSlot.mapUID (f : UData → UData) (s : LHSSlot) : LHSSlot :=
  LHSSlot.traverseAxes (f := Id) (AxisSpec.mapUID f) s

/-- The `Id` instantiation of `Decl.traverseAxes`. -/
def Decl.mapUID (f : UData → UData) (d : Decl) : Decl :=
  Decl.traverseAxes (f := Id) (AxisSpec.mapUID f) d

/-- The `Id` instantiation of `Stmt.traverseAxes` (mask included via
    `RHSExpr.traverseAxesWithMask`, matching the always-remap-the-mask semantics). -/
def Stmt.mapUID (f : UData → UData) (s : Stmt) : Stmt :=
  Stmt.traverseAxes (f := Id) (AxisSpec.mapUID f) s

/-- The `Id` instantiation of `TLProgram.traverseAxes`. -/
def TLProgram.mapUID (f : UData → UData) (p : TLProgram) : TLProgram :=
  TLProgram.traverseAxes (f := Id) (AxisSpec.mapUID f) p

theorem traverseAxes_list_id {α β : Type} (g : α → Id β) (xs : List α) :
    Traversable.traverse g xs = xs.map g := by
  exact List.traverse_eq_map_id g xs

theorem traverseAxes_list_collect {α β γ : Type}
    (g : α → ConstL (List γ) β) (xs : List α) :
    (Traversable.traverse g xs).run = xs.flatMap (fun x => (g x).run) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (g x).run ++ (Traversable.traverse g xs).run = _
    rw [ih]
    rfl

theorem ProdTerm.mapUID_factors (f : UData → UData) (p : ProdTerm) :
    (p.mapUID f).factors = p.factors.map (Factor.mapUID f) := by
  change Traversable.traverse (Factor.traverseAxes (f := Id) (AxisSpec.mapUID f)) p.factors = _
  rw [traverseAxes_list_id]
  rfl

theorem RHSExpr.mapUID_terms (f : UData → UData) (r : RHSExpr) :
    (r.mapUID f).body.terms = r.body.terms.map (ProdTerm.mapUID f) := by
  change Traversable.traverse (ProdTerm.traverseAxes (f := Id) (AxisSpec.mapUID f)) r.body.terms = _
  rw [traverseAxes_list_id]
  rfl

theorem TLProgram.mapUID_lists (f : UData → UData) (p : TLProgram) :
    (p.mapUID f).decls = p.decls.map (Decl.mapUID f) ∧
    (p.mapUID f).stmts = p.stmts.map (Stmt.mapUID f) := by
  change Traversable.traverse (Decl.traverseAxes (f := Id) (AxisSpec.mapUID f)) p.decls = _ ∧
    Traversable.traverse (Stmt.traverseAxes (f := Id) (AxisSpec.mapUID f)) p.stmts = _
  simp only [traverseAxes_list_id]
  exact ⟨rfl, rfl⟩

end LeanNCD

-- LeanNCD/DSL/Traverse.lean
import LeanNCD.DSL.Ast
import LeanNCD.DSL.TraverseAxes

namespace LeanNCD

/-- Apply a UID remap to a single AxisSpec (name is display-only; preserved). -/
def AxisSpec.mapUID (f : UData → UData) (a : AxisSpec) : AxisSpec :=
  { a with uid := (f ⟨a.uid, some a.name⟩).uid }

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

end LeanNCD

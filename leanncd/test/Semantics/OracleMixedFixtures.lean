import LeanNCD.Semantics.Source.SortedDifferential

/-! Oracle sorts T2: the snapshot builder shared by the mixed-sort refusal, evaluator and value
modules (a clone of the builder observed in `papers/semantics/oracle_sorts_plan_facts.md` section 5).

Declarations: axes `a` (extent 4), `b` (3), `k` (8) are declarations 0, 1, 2; the first tensor is
declaration 3. Every tensor is `typedTensor .f64` (`checkStructure` requires f64). Inputs:
`X[a]`, `Z[a,b]`, `Q[a,b] = B[a,b]`, `W8[k]`. Helper names here are public and stable: later
modules import them. -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source

namespace OracleMixed

def axA : AxisSpec := ⟨"a", 7, .real⟩
def axB : AxisSpec := ⟨"b", 8, .real⟩
def axK : AxisSpec := ⟨"k", 9, .real⟩

/-- A tensor of a fixture: its name, axes, role and (for an input) its values. -/
structure T where
  name : String
  axes : List AxisSpec
  role : TensorRole
  vals : List ℚ := []

def ext (ax : AxisSpec) : Nat := if ax.uid = 7 then 4 else if ax.uid = 8 then 3 else 8

/-- The snapshot of tensors `ts` (declared in order, from declaration 3) and statements `stmts`. -/
def mk (ts : List T) (stmts : List Stmt) : SourceSnapshot :=
  { resolved := { decls := [.axis axA (some 4), .axis axB (some 3), .axis axK (some 8)]
                    ++ ts.map (fun t => .typedTensor .f64 t.name t.axes)
                  stmts := stmts, env := {}, extNames := ∅ }
    specs := ts.zipIdx.map (fun (t, i) => ⟨i + 3, t.role, t.axes.map ext⟩)
    inputs := (ts.zipIdx.filter (fun (t, _) => t.role == .input)).map
      (fun (t, i) => ⟨i + 3, t.axes.map ext, t.vals⟩) }

/-- Declaration ordinals of the non-input tensors, in definition order (the `order` argument of
`compareSortedSource`). -/
def orderOf (ts : List T) : List Nat :=
  ((ts.zipIdx.filter (fun (t, _) => t.role != .input)).map (fun (_, i) => i + 3))

def xVals : List ℚ := [20, 2, 3, 40]
def zVals : List ℚ := [-5, -4, -3, 5, 6, 7, 15, 16, 17, 25, 26, 27]
def qVals : List ℚ := [1, 9, 2, 3, 8, 4, 7, 5, 6, 0, 10, 11]
def w8Vals : List ℚ := [1, 0, 2, 3, 4, 5, 6, 7]

def tX : T := ⟨"X", [axA], .input, xVals⟩
def tZ : T := ⟨"Z", [axA, axB], .input, zVals⟩
def tQ : T := ⟨"Q", [axA, axB], .input, qVals⟩
def tB : T := ⟨"B", [axA, axB], .input, qVals⟩
def tW8 : T := ⟨"W8", [axK], .input, w8Vals⟩

/-- A written tensor over `a` that a later statement reads. -/
def tDef (name : String) (axes : List AxisSpec := [axA]) : T := ⟨name, axes, .defined, []⟩
/-- A final (output) tensor. -/
def tOut (name : String) (axes : List AxisSpec := [axA]) : T := ⟨name, axes, .output, []⟩

def rhs (agg : AggOp) (terms : List (List Factor)) : RHSExpr :=
  ⟨⟨terms.map ProdTerm.mk⟩, .identity, agg⟩

def rd (n : String) (axes : List AxisSpec) : Factor := .read n (axes.map .axis)

def free1 : List LHSSlot := [.free axA]

/-- A bare-index statement `dst[a] := agg f`. -/
def st (dst : String) (agg : AggOp) (f : Factor) : Stmt :=
  .assign dst free1 (rhs agg [[f]])

/-- A statement with explicit slots and factors (one product term). -/
def zR (n : String) (ls : List LHSSlot) (agg : AggOp) (fs : List Factor) : Stmt :=
  .assign n ls (rhs agg [fs])

end OracleMixed

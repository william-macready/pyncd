import Eval.ScanTest
import Eval.EvalExamplesTest
import LeanNCD.Eval.Entry

/-!
# Task 4 oracle fixture seed

Six legacy-evaluator fixtures for the nonlinear-scan shapes required by Task 4. Fixtures 3 and 6
are exact transcriptions of the imported, already-asserted examples; fixtures 1, 2, 4, and 5 are
fresh programs. All inputs and nonlinearities are unmasked `f64`.
-/

namespace LeanNCD.OracleFixtureSeed

open LeanNCD.Eval Std

def mkAxis (name : String) (uid : Nat) (kind := AxisKind.real) : AxisSpec :=
  { name, uid, kind }

def rhs (name : String) (idxs : List IdxExpr) (nonlin := Nonlin.identity) : RHSExpr :=
  { body := { terms := [{ factors := [.read name idxs] }] }, nonlin }

def rhs2 (a : String) (ai : List IdxExpr) (b : String) (bi : List IdxExpr)
    (nonlin := Nonlin.identity) : RHSExpr :=
  { body := { terms := [{ factors := [.read a ai, .read b bi] }] }, nonlin }

def tensorOf (shape : List Nat) (data : List Float) : DenseTensor :=
  ⟨shape, data.toArray⟩

def statementDestination? : Stmt → Option String
  | .assign name _ _ | .scatter name _ _ _ | .recurMorphism name _ _ => some name

def statementSlots? : Stmt → Option (List LHSSlot)
  | .assign _ slots _ | .scatter _ slots _ _ => some slots
  | .recurMorphism _ _ _ => none

def writingCount (name : String) (stmts : List Stmt) : Nat :=
  (stmts.filter fun stmt => statementDestination? stmt == some name).length

def hasBaseWrite (name : String) (base : List Stmt) : Bool :=
  base.any fun stmt => statementDestination? stmt == some name

def renderTensor (name : String) (value : DenseTensor) : String :=
  name ++ " shape " ++ toString (repr value.shape) ++ " = " ++ toString (repr value.data)

def observedLine (label : String) (sched : ScheduledProgram)
    (inputs : HashMap String DenseTensor) (names : List String) : String :=
  match evalScheduled sched inputs with
  | .error e => label ++ ": ERROR " ++ toString e
  | .ok report =>
      let rendered := names.map fun name =>
        match report.env[name]? with
        | some value => renderTensor name value
        | none => name ++ " MISSING"
      label ++ ": " ++ String.intercalate "; " rendered

def evaluationHas (sched : ScheduledProgram) (inputs : HashMap String DenseTensor)
    (names : List String) : Bool :=
  match evalScheduled sched inputs with
  | .error _ => false
  | .ok report => names.all fun name => report.env.contains name

/-! ## Fixture 1 — leading pointwise scratch -/

def f1i := mkAxis "i" 101
def f1l := mkAxis "l" 102 .nat

def fixture1 : ScheduledProgram :=
  { decls := [.iter f1l 3]
  , stmts := [.scan "S" [f1l]
      [.assign "S" [.free f1i, .iterAt f1l 0] (rhs "X" [.axis f1i])]
      [ .assign "T" [.free f1i]
          (rhs2 "S" [.axis f1i, .axis f1l] "K" [.axis f1i] (.pointwise .relu))
      , .assign "S" [.free f1i, .iterNext f1l] (rhs "T" [.axis f1i]) ]
      false]
  , env := {}
  , extNames := {"X", "K"}
  , explicitSizes := ({} : HashMap UID Nat).insert f1l.uid 3 }

def fixture1Inputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" (tensorOf [2] [-1, 2])).insert
    "K" (tensorOf [2] [-2, 3])

#guard match fixture1.stmts with
  | [.scan _ _ base recur _] =>
      match recur.find? fun stmt => statementDestination? stmt == some "T" with
      | some stmt =>
          statementSlots? stmt == some [.free f1i] &&
          writingCount "T" (base ++ recur) == 1 &&
          match recur with
          | [_, .assign "S" _ result] => result == rhs "T" [.axis f1i]
          | _ => false
      | none => false
  | _ => false

#guard evaluationHas fixture1 fixture1Inputs ["S"]

/-! ## Fixture 2 — interleaved axiswise recurrence -/

def f2l := mkAxis "l" 201 .nat
def f2i := mkAxis "i" 202
def f2m := mkAxis "m" 203 .nat

def fixture2 : ScheduledProgram :=
  { decls := [.iter f2l 3, .iter f2m 3]
  , stmts := [.scan "S" [f2l, f2m]
      [.assign "S" [.iterAt f2l 0, .free f2i, .iterAt f2m 0] (rhs "X" [.axis f2i])]
      [.assign "S" [.iterNext f2l, .freeNorm f2i, .iterNext f2m]
        (rhs "S" [.axis f2l, .axis f2i, .axis f2m] (.axiswise .normalize none))]
      false]
  , env := {}
  , extNames := {"X"}
  , explicitSizes :=
      (({} : HashMap UID Nat).insert f2l.uid 3).insert f2m.uid 3 }

def fixture2Inputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" (tensorOf [2] [1, 3])

#guard match fixture2.stmts with
  | [.scan _ [l, m] _ [.assign _ slots rhs] _] =>
      l == f2l && m == f2m &&
      slots == [.iterNext f2l, .freeNorm f2i, .iterNext f2m] &&
      rhs.nonlin == .axiswise .normalize none
  | _ => false

#guard evaluationHas fixture2 fixture2Inputs ["S"]

/-! ## Fixture 3 — adopted leading persistent nonlinear recurrence

Exact transcription of `Eval.ScanTest`'s imported ReLU-scan `run_cmd`.
-/

def f3j := mkAxis "j" 301
def f3l := mkAxis "l" 302

def fixture3 : ScheduledProgram :=
  { decls := []
  , stmts := [.scan "S" [f3l]
      [.assign "S" [.free f3j, .iterAt f3l 0] (rhs "X" [.axis f3j])]
      [.assign "S" [.free f3j, .iterNext f3l]
        (rhs2 "S" [.axis f3j, .axis f3l] "A" [.axis f3j] (.pointwise .relu))]
      false]
  , env := {}
  , extNames := {"X", "A"}
  , explicitSizes :=
      (({} : HashMap UID Nat).insert f3j.uid 1).insert f3l.uid 2 }

def fixture3Inputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" (tensorOf [1] [1])).insert
    "A" (tensorOf [1] [-1])

#guard match fixture3.stmts with
  | [.scan _ _ [.assign "S" _ base] [.assign "S" _ recur] _] =>
      base.nonlin == .identity && recur.nonlin == .pointwise .relu
  | _ => false

#guard evaluationHas fixture3 fixture3Inputs ["S"]

/-! ## Fixture 4 — nonlinear base, linear recurrence -/

def f4i := mkAxis "i" 401
def f4l := mkAxis "l" 402 .nat

def fixture4 : ScheduledProgram :=
  { decls := [.iter f4l 3]
  , stmts := [.scan "S" [f4l]
      [.assign "S" [.free f4i, .iterAt f4l 0]
        (rhs "X" [.axis f4i] (.pointwise .relu))]
      [.assign "S" [.free f4i, .iterNext f4l]
        (rhs2 "S" [.axis f4i, .axis f4l] "A" [.axis f4i])]
      false]
  , env := {}
  , extNames := {"X", "A"}
  , explicitSizes := ({} : HashMap UID Nat).insert f4l.uid 3 }

def fixture4Inputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" (tensorOf [2] [-2, 3])).insert
    "A" (tensorOf [2] [2, -1])

#guard match fixture4.stmts with
  | [.scan _ _ [.assign "S" _ base] [.assign "S" _ recur] _] =>
      base.nonlin == .pointwise .relu && recur.nonlin == .identity
  | _ => false

#guard evaluationHas fixture4 fixture4Inputs ["S"]

/-! ## Fixture 5 — nonlinear scratch to scratch to state -/

def f5l := mkAxis "l" 501 .nat

def fixture5 : ScheduledProgram :=
  { decls := [.iter f5l 3]
  , stmts := [.scan "S" [f5l]
      [.assign "S" [.iterAt f5l 0] (rhs "X" [])]
      [ .assign "T" [] (rhs2 "S" [.axis f5l] "A" [.axis f5l] (.pointwise .relu))
      , .assign "U" [] (rhs2 "T" [] "B" [.axis f5l])
      , .assign "S" [.iterNext f5l] (rhs "U" []) ]
      false]
  , env := {}
  , extNames := {"X", "A", "B"}
  , explicitSizes := ({} : HashMap UID Nat).insert f5l.uid 3 }

def fixture5Inputs : HashMap String DenseTensor :=
  ((({} : HashMap String DenseTensor).insert "X" (tensorOf [] [1])).insert
    "A" (tensorOf [3] [2, -3, 4])).insert "B" (tensorOf [3] [3, 2, 1])

#guard match fixture5.stmts with
  | [.scan _ _ base recur _] =>
      recur.map statementDestination? == [some "T", some "U", some "S"] &&
      !hasBaseWrite "T" base && !hasBaseWrite "U" base && hasBaseWrite "S" base &&
      match recur with
      | [.assign "T" _ t, .assign "U" _ u, .assign "S" _ state] =>
          t.nonlin == .pointwise .relu &&
          u == rhs2 "T" [] "B" [.axis f5l] &&
          state == rhs "U" []
      | _ => false
  | _ => false

#guard evaluationHas fixture5 fixture5Inputs ["S"]

/-! ## Fixture 6 — adopted coupled states

Exact source from imported `Eval.EvalExamplesTest` example 5.
-/

def fixture6Program : TLProgram := tlprog!{
  iter l = 3
  G[j, 0]    := X[j]
  G[j, l +1] := relu(G[j, l] · W_G[j, k] + H[j, l] · U[j, k])
  H[j, 0]    := Y[j]
  H[j, l +1] := relu(H[j, l] · W_H[j, k] + G[j, l] · V[j, k])
}

def fixture6Inputs : HashMap String DenseTensor :=
  (((((({} : HashMap String DenseTensor).insert "X" (tensorOf [1] [1])).insert
    "Y" (tensorOf [1] [2])).insert "W_G" (tensorOf [1, 1] [1])).insert
    "U" (tensorOf [1, 1] [1])).insert "W_H" (tensorOf [1, 1] [1])).insert
    "V" (tensorOf [1, 1] [1])

def fixture6Scheduled? : Option ScheduledProgram :=
  match fixture6Program.compileToScheduled.run 0 with
  | .ok sched _ => some sched
  | .error _ _ => none

#guard fixture6Scheduled?.isSome

#guard match fixture6Scheduled? with
  | some sched => evaluationHas sched fixture6Inputs ["G", "H"]
  | none => false

run_cmd do
  Lean.logInfo (observedLine "FIXTURE 1" fixture1 fixture1Inputs ["S"])
  Lean.logInfo (observedLine "FIXTURE 2" fixture2 fixture2Inputs ["S"])
  Lean.logInfo (observedLine "FIXTURE 3 (adopted Eval.ScanTest ReLU scan)"
    fixture3 fixture3Inputs ["S"])
  Lean.logInfo (observedLine "FIXTURE 4" fixture4 fixture4Inputs ["S"])
  Lean.logInfo (observedLine "FIXTURE 5" fixture5 fixture5Inputs ["S"])
  match fixture6Scheduled? with
  | none => throwError "FIXTURE 6 source did not compile"
  | some sched =>
      Lean.logInfo (observedLine "FIXTURE 6 (adopted Eval.EvalExamplesTest example 5)"
        sched fixture6Inputs ["G", "H"])

end LeanNCD.OracleFixtureSeed

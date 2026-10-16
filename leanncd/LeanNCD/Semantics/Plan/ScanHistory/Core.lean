import LeanNCD.Semantics.Plan.ScanHistory.Recurrence
import LeanNCD.Semantics.Plan.Syntax
import LeanNCD.Semantics.Source.Context

namespace LeanNCD.Semantics.Program.Plan.ScanHistory

abbrev Carrier (V : Type) : Unit → Type := fun _ => V

def spaceAxis (d : Nat) : Axis := ⟨0, d⟩
def timeAxis (N : Nat) : Axis := ⟨1, N + 1⟩
def stateShape (d : Nat) : ArrayShape := ⟨[spaceAxis d], by simp⟩
def historyShape (d N : Nat) : Shape := [spaceAxis d, timeAxis N]
def stateTy (d : Nat) : Ty Unit := .array () (stateShape d)

def stateLayout (d : Nat) : Layout (stateShape d).axes where
  count := d
  enumerate :=
    { toFun := fun i => (i, ())
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨i, u⟩; cases u; rfl }

def stateCoord {d : Nat} (i : Fin d) : Coord (stateShape d).axes := (i, ())

def historyCoord {d N : Nat} (i : Fin d) (l : Fin (N + 1)) :
    Coord (historyShape d N) := (i, l, ())

inductive Tensor
  | X | Z | H
  deriving DecidableEq, Repr

@[reducible] def declarations (d N : Nat) : Declarations Unit where
  Tensor := Tensor
  uid := fun t => match t with
    | .X => 10
    | .Z => 11
    | .H => 12
  unique := by
    intro t u h
    cases t <;> cases u <;> simp_all
  signature := fun t => ⟨(), match t with
    | .X | .Z => (stateShape d).axes
    | .H => historyShape d N⟩

/-- A certificate for one operator in an arbitrary existing registry. -/
structure RegisteredF {V : Type} (r : Registry (Carrier V)) (d : Nat) where
  op : r.Op
  unary : r.arity op = 1
  input_eq : ∀ i, r.input op i = stateTy d
  output_eq : r.output op = stateTy d
  total : ∀ xs, r.domain op xs = true

variable {V : Type} {d N : Nat} {r : Registry (Carrier V)}

def RegisteredF.arguments (f : RegisteredF r d) (x : State V d) :
    (i : Fin (r.arity f.op)) → Value (Carrier V) (r.input f.op i) :=
  fun i => cast (congrArg (Value (Carrier V)) (f.input_eq i).symm)
    (fun p : Coord (stateShape d).axes => x p.1)

def RegisteredF.transition (f : RegisteredF r d) (x : State V d) : State V d :=
  let y := cast (congrArg (Value (Carrier V)) f.output_eq)
    (r.meaning f.op (f.arguments x) (f.total (f.arguments x)))
  fun i => y (stateCoord i)

def directRead {W Γ : Type} {sh : Shape} (index : Γ → Coord sh) :
    AdmittedRead W sh Γ where
  policy := Source.strictPolicy sh
  raw := fun γ => Coord.raw (index γ)
  resolved := fun γ => .at (index γ)
  admission := fun γ => (Source.strictPolicy sh).inBounds (index γ)

def RegisteredF.arrayExpr {Γ : Type} {σ : Declarations Unit}
    (f : RegisteredF r d) (arg : Expr (Carrier V) σ r Γ (stateTy d)) :
    Expr (Carrier V) σ r Γ (stateTy d) :=
  cast (congrArg (Expr (Carrier V) σ r Γ) f.output_eq)
    (.prim f.op (fun i =>
      cast (congrArg (Expr (Carrier V) σ r Γ) (f.input_eq i).symm) arg))

def priorSlice {Γ : Type} (l : Γ → Fin (N + 1)) :
    Expr (Carrier V) (declarations d N) r Γ (stateTy d) :=
  .tab (stateShape d) (stateLayout d)
    (.read Tensor.H (directRead (fun γ => historyCoord γ.2.1 (l γ.1))))

def recurrenceBody {Γ : Type} (f : RegisteredF r d)
    (i : Γ → Fin d) (l : Γ → Fin (N + 1)) :
    Expr (Carrier V) (declarations d N) r Γ (.scalar ()) :=
  .at (f.arrayExpr (priorSlice l)) (fun γ => stateCoord (i γ))

/-- The three source IDs remain distinct even when their bodies coincide. -/
def persistentID : Fin 3 := 0
def initialID : Fin 3 := 1
def recurrenceID : Fin 3 := 2

def valuationPair (d N : Nat) (v : Fin (d * (N + 1))) :
    Fin d × Fin (N + 1) := finProdFinEquiv.symm v

def valuationIndex {d N : Nat} (i : Fin d) (l : Fin (N + 1)) :
    Fin (d * (N + 1)) := finProdFinEquiv (i, l)

theorem valuationPair_index (i : Fin d) (l : Fin (N + 1)) :
    valuationPair d N (valuationIndex i l) = (i, l) :=
  finProdFinEquiv.symm_apply_apply _

def statementGuard (d N : Nat) (s : Fin 3) (v : Fin (d * (N + 1))) : Bool :=
  if s = initialID then decide ((valuationPair d N v).2.val = 0)
  else if s = recurrenceID then decide ((valuationPair d N v).2.val < N)
  else true

abbrev AdmittedValuation (d N : Nat) (s : Fin 3) :=
  {v : Fin (d * (N + 1)) // statementGuard d N s v = true}

theorem recurrence_lt (v : AdmittedValuation d N recurrenceID) :
    (valuationPair d N v.val).2.val < N := by
  simpa [statementGuard, initialID, recurrenceID] using v.property

def destination (d N : Nat) (s : Fin 3) (v : AdmittedValuation d N s) :
    Coord (historyShape d N) :=
  let p := valuationPair d N v.val
  if h : s = recurrenceID then
    historyCoord p.1 ⟨p.2.val + 1, by
      have hv : p.2.val < N := by
        have hv := v.property
        simpa [statementGuard, h, initialID, recurrenceID] using hv
      omega⟩
  else historyCoord p.1 p.2

def statementBody (f : RegisteredF r d) (N : Nat) (s : Fin 3) :
    Expr (Carrier V) (declarations d N) r (AdmittedValuation d N s) (.scalar ()) :=
  if s = persistentID then
    .read Tensor.X (directRead (fun v => stateCoord (valuationPair d N v.val).1))
  else if s = initialID then
    .read Tensor.Z (directRead (fun v => stateCoord (valuationPair d N v.val).1))
  else
    recurrenceBody f (fun v => (valuationPair d N v.val).1)
      (fun v => (valuationPair d N v.val).2)

def isInput : Tensor → Bool
  | .X | .Z => true
  | .H => false

def isOutput : Tensor → Bool
  | .X | .Z => false
  | .H => true

theorem defined_tensor (t : Tensor) (h : isInput t = false) : t = .H := by
  cases t <;> simp_all [isInput]

@[reducible] def program (f : RegisteredF r d) (N : Nat) :
    Program (Carrier V) (declarations d N) r where
  tensors := ⟨{.X, .Z, .H}, by intro t; cases t <;> simp⟩
  input := isInput
  output := isOutput
  output_defined := by intro t h; cases t <;> simp_all [isOutput, isInput]
  statements := fun _ => 3
  valuations := fun _ _ => d * (N + 1)
  guard := fun _ => statementGuard d N
  destination := fun t s v => by
    have ht := defined_tensor t.val t.property
    exact ht ▸ destination d N s v
  body := fun t s => by
    have ht := defined_tensor t.val t.property
    exact ht ▸ statementBody f N s

def historyDefined (f : RegisteredF r d) (N : Nat) : (program f N).Defined :=
  ⟨.H, rfl⟩

def historyAddress (d N : Nat) (i : Fin d) (l : Fin (N + 1)) :
    Address (declarations d N) := ⟨.H, historyCoord i l⟩

def historyDefAddr (f : RegisteredF r d) (N : Nat) (i : Fin d) (l : Fin (N + 1)) :
    DefAddr (program f N) := ⟨historyDefined f N, historyCoord i l⟩

def persistentOccurrence (f : RegisteredF r d) (N : Nat)
    (i : Fin d) (l : Fin (N + 1)) : (program f N).Occurrence (historyDefined f N) :=
  ⟨persistentID, ⟨valuationIndex i l, by simp [statementGuard, persistentID, initialID,
    recurrenceID]⟩⟩

def initialOccurrence (f : RegisteredF r d) (N : Nat) (i : Fin d) :
    (program f N).Occurrence (historyDefined f N) :=
  ⟨initialID, ⟨valuationIndex i 0, by simp [statementGuard, valuationPair_index]⟩⟩

def recurrenceOccurrence (f : RegisteredF r d) (N : Nat)
    (i : Fin d) (l : Fin N) : (program f N).Occurrence (historyDefined f N) :=
  ⟨recurrenceID, ⟨valuationIndex i ⟨l.val, Nat.lt_succ_of_lt l.isLt⟩, by
    simp [statementGuard, initialID, recurrenceID, valuationPair_index, l.isLt]⟩⟩

theorem priorSlice_footprint {Γ : Type} (l : Γ → Fin (N + 1)) (γ : Γ) :
    footprint (priorSlice (V := V) (r := r) (d := d) l) γ =
      (List.finRange d).map (fun i => historyAddress d N i (l γ)) := by
  simp only [priorSlice, footprint, stateLayout, directRead, historyAddress, historyCoord]
  generalize List.finRange d = is
  induction is <;> simp_all
  rfl

#print axioms valuationPair_index
#print axioms recurrence_lt
#print axioms defined_tensor
#print axioms priorSlice_footprint

end LeanNCD.Semantics.Program.Plan.ScanHistory

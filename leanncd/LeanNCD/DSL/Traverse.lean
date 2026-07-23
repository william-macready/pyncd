-- LeanNCD/DSL/Traverse.lean
import LeanNCD.DSL.Ast
import LeanNCD.DSL.TraverseAxes
import LeanNCD.Exec.Traversable

namespace LeanNCD

/-- Apply a UID remap to a single AxisSpec (name is display-only; preserved). -/
def AxisSpec.mapUID (f : UData → UData) (a : AxisSpec) : AxisSpec :=
  { a with uid := (f ⟨a.uid, some a.name⟩).uid }

instance : TermTraversable AxisSpec where
  traverseUID f a := AxisSpec.mapUID f a

def IdxExpr.mapUID_old (f : UData → UData) : IdxExpr → IdxExpr
  | .axis a       => .axis (AxisSpec.mapUID f a)
  | .const n      => .const n
  | .scale n a    => .scale n (AxisSpec.mapUID f a)
  | .shift a n    => .shift (AxisSpec.mapUID f a) n
  | .affine n xs  => .affine n (xs.map (fun (c, a) => (c, AxisSpec.mapUID f a)))

def IdxExpr.mapUID (f : UData → UData) (e : IdxExpr) : IdxExpr :=
  IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) e

theorem IdxExpr.mapUID_eq_old (f : UData → UData) (e : IdxExpr) :
    IdxExpr.mapUID f e = IdxExpr.mapUID_old f e := by
  cases e with
  | axis a => rfl
  | const n => rfl
  | scale c a => rfl
  | shift a n => rfl
  | affine n xs =>
      have hEq : (fun (ca : Int × AxisSpec) => Prod.mk ca.1 <$> AxisSpec.mapUID f ca.2 :
            Int × AxisSpec → Id (Int × AxisSpec))
          = pure ∘ (fun ca => (ca.1, AxisSpec.mapUID f ca.2)) := rfl
      simp only [IdxExpr.mapUID, IdxExpr.traverseAxes, IdxExpr.mapUID_old, Traversable.traverse,
        hEq, List.traverse_eq_map_id]
      rfl

instance : TermTraversable IdxExpr where traverseUID := IdxExpr.mapUID

-- Temporary scaffolding for `PredArith.mapUID_eq_old` below; slated for removal in the
-- Task 7 cleanup once all `mapUID` callers are migrated.
def PredArith.mapUID_old (f : UData → UData) : PredArith → PredArith
  | .embed e  => .embed (IdxExpr.mapUID_old f e)
  | .mul a b  => .mul (PredArith.mapUID_old f a) (PredArith.mapUID_old f b)
  | .iabs a   => .iabs (PredArith.mapUID_old f a)

/-- The `ConstL`-free `Id` instantiation of `PredArith.traverseAxes`. -/
def PredArith.mapUID (f : UData → UData) (e : PredArith) : PredArith :=
  PredArith.traverseAxes (f := Id) (AxisSpec.mapUID f) e

theorem PredArith.mapUID_eq_old (f : UData → UData) (e : PredArith) :
    PredArith.mapUID f e = PredArith.mapUID_old f e := by
  induction e with
  | embed e =>
      simp only [PredArith.mapUID, PredArith.traverseAxes, PredArith.mapUID_old]
      show (PredArith.embed <$> IdxExpr.mapUID f e : Id PredArith) = PredArith.embed (IdxExpr.mapUID_old f e)
      rw [IdxExpr.mapUID_eq_old f e]
      rfl  -- collapses the `Id` applicative `<$>` (reducible-transparency `rw` won't)
  | mul a b iha ihb =>
      simp only [PredArith.mapUID, PredArith.traverseAxes, PredArith.mapUID_old]
      show (PredArith.mul <$> PredArith.mapUID f a <*> PredArith.mapUID f b : Id PredArith)
        = PredArith.mul (PredArith.mapUID_old f a) (PredArith.mapUID_old f b)
      rw [iha, ihb]
      rfl  -- collapses the `Id` applicative `<$>`/`<*>` (reducible-transparency `rw` won't)
  | iabs a iha =>
      simp only [PredArith.mapUID, PredArith.traverseAxes, PredArith.mapUID_old]
      show (PredArith.iabs <$> PredArith.mapUID f a : Id PredArith) = PredArith.iabs (PredArith.mapUID_old f a)
      rw [iha]
      rfl  -- collapses the `Id` applicative `<$>` (reducible-transparency `rw` won't)

instance : TermTraversable PredArith where traverseUID := PredArith.mapUID

-- Temporary scaffolding for `BoolExpr.mapUID_eq_old` below; slated for removal in the
-- Task 7 cleanup once all `mapUID` callers are migrated.
def BoolExpr.mapUID_old (f : UData → UData) : BoolExpr → BoolExpr
  | .rel op a b => .rel op (PredArith.mapUID_old f a) (PredArith.mapUID_old f b)
  | .and a b    => .and (BoolExpr.mapUID_old f a) (BoolExpr.mapUID_old f b)
  | .or  a b    => .or  (BoolExpr.mapUID_old f a) (BoolExpr.mapUID_old f b)
  | .not a      => .not (BoolExpr.mapUID_old f a)
  | .ieq a b    => .ieq (PredArith.mapUID_old f a) (PredArith.mapUID_old f b)

/-- The `ConstL`-free `Id` instantiation of `BoolExpr.traverseAxes`. -/
def BoolExpr.mapUID (f : UData → UData) (e : BoolExpr) : BoolExpr :=
  BoolExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) e

theorem BoolExpr.mapUID_eq_old (f : UData → UData) (e : BoolExpr) :
    BoolExpr.mapUID f e = BoolExpr.mapUID_old f e := by
  induction e with
  | rel op a b =>
      simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_old]
      show (BoolExpr.rel op <$> PredArith.mapUID f a <*> PredArith.mapUID f b : Id BoolExpr)
        = BoolExpr.rel op (PredArith.mapUID_old f a) (PredArith.mapUID_old f b)
      rw [PredArith.mapUID_eq_old f a, PredArith.mapUID_eq_old f b]
      rfl  -- collapses the `Id` applicative `<$>`/`<*>` (reducible-transparency `rw` won't)
  | and a b iha ihb =>
      simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_old]
      show (BoolExpr.and <$> BoolExpr.mapUID f a <*> BoolExpr.mapUID f b : Id BoolExpr)
        = BoolExpr.and (BoolExpr.mapUID_old f a) (BoolExpr.mapUID_old f b)
      rw [iha, ihb]
      rfl  -- collapses the `Id` applicative `<$>`/`<*>` (reducible-transparency `rw` won't)
  | or a b iha ihb =>
      simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_old]
      show (BoolExpr.or <$> BoolExpr.mapUID f a <*> BoolExpr.mapUID f b : Id BoolExpr)
        = BoolExpr.or (BoolExpr.mapUID_old f a) (BoolExpr.mapUID_old f b)
      rw [iha, ihb]
      rfl  -- collapses the `Id` applicative `<$>`/`<*>` (reducible-transparency `rw` won't)
  | not a iha =>
      simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_old]
      show (BoolExpr.not <$> BoolExpr.mapUID f a : Id BoolExpr) = BoolExpr.not (BoolExpr.mapUID_old f a)
      rw [iha]
      rfl  -- collapses the `Id` applicative `<$>` (reducible-transparency `rw` won't)
  | ieq a b =>
      simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_old]
      show (BoolExpr.ieq <$> PredArith.mapUID f a <*> PredArith.mapUID f b : Id BoolExpr)
        = BoolExpr.ieq (PredArith.mapUID_old f a) (PredArith.mapUID_old f b)
      rw [PredArith.mapUID_eq_old f a, PredArith.mapUID_eq_old f b]
      rfl  -- collapses the `Id` applicative `<$>`/`<*>` (reducible-transparency `rw` won't)

instance : TermTraversable BoolExpr where traverseUID := BoolExpr.mapUID

-- Temporary scaffolding for `Nonlin.mapUID_eq_old` below; slated for removal in the
-- Task 7 cleanup once all `mapUID` callers are migrated.
def Nonlin.mapUID_old (f : UData → UData) : Nonlin → Nonlin
  | .identity      => .identity
  | .relu          => .relu
  | .sigmoid       => .sigmoid
  | .tanh          => .tanh
  | .gelu          => .gelu
  | .leakyrelu     => .leakyrelu
  | .softmax m     => .softmax (m.map (BoolExpr.mapUID_old f))
  | .normalize m   => .normalize (m.map (BoolExpr.mapUID_old f))
  | .l2normalize m => .l2normalize (m.map (BoolExpr.mapUID_old f))

/-- The `Id` instantiation of `Nonlin.traverseAxes`. -/
def Nonlin.mapUID (f : UData → UData) (n : Nonlin) : Nonlin :=
  Nonlin.traverseAxes (f := Id) (AxisSpec.mapUID f) n

theorem Nonlin.mapUID_eq_old (f : UData → UData) (n : Nonlin) :
    Nonlin.mapUID f n = Nonlin.mapUID_old f n := by
  cases n with
  | identity => rfl
  | relu => rfl
  | sigmoid => rfl
  | tanh => rfl
  | gelu => rfl
  | leakyrelu => rfl
  | softmax m =>
      cases m with
      | none => rfl
      | some b =>
          simp only [Nonlin.mapUID, Nonlin.traverseAxes, Nonlin.mapUID_old]
          show (Nonlin.softmax (some (BoolExpr.mapUID f b)) : Id Nonlin)
            = Nonlin.softmax (some (BoolExpr.mapUID_old f b))
          rw [BoolExpr.mapUID_eq_old f b]
  | normalize m =>
      cases m with
      | none => rfl
      | some b =>
          simp only [Nonlin.mapUID, Nonlin.traverseAxes, Nonlin.mapUID_old]
          show (Nonlin.normalize (some (BoolExpr.mapUID f b)) : Id Nonlin)
            = Nonlin.normalize (some (BoolExpr.mapUID_old f b))
          rw [BoolExpr.mapUID_eq_old f b]
  | l2normalize m =>
      cases m with
      | none => rfl
      | some b =>
          simp only [Nonlin.mapUID, Nonlin.traverseAxes, Nonlin.mapUID_old]
          show (Nonlin.l2normalize (some (BoolExpr.mapUID f b)) : Id Nonlin)
            = Nonlin.l2normalize (some (BoolExpr.mapUID_old f b))
          rw [BoolExpr.mapUID_eq_old f b]

-- Temporary scaffolding for `Factor.mapUID_eq_old` below; slated for removal in the
-- Task 7 cleanup once all `mapUID` callers are migrated.
def Factor.mapUID_old (f : UData → UData) : Factor → Factor
  | .read nm es => .read nm (es.map (IdxExpr.mapUID_old f))
  | .iverson b  => .iverson (BoolExpr.mapUID_old f b)
  | .unaryFn op nm es => .unaryFn op nm (es.map (IdxExpr.mapUID_old f))

/-- The `Id` instantiation of `Factor.traverseAxes`. -/
def Factor.mapUID (f : UData → UData) (x : Factor) : Factor :=
  Factor.traverseAxes (f := Id) (AxisSpec.mapUID f) x

theorem Factor.mapUID_eq_old (f : UData → UData) (x : Factor) :
    Factor.mapUID f x = Factor.mapUID_old f x := by
  cases x with
  | read nm es =>
      simp only [Factor.mapUID, Factor.traverseAxes, Factor.mapUID_old]
      show Factor.read nm (Traversable.traverse (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f)) es)
        = Factor.read nm (es.map (IdxExpr.mapUID_old f))
      have hEq : (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) : IdxExpr → Id IdxExpr)
          = pure ∘ IdxExpr.mapUID_old f := by
        funext e
        exact IdxExpr.mapUID_eq_old f e
      simp only [Traversable.traverse, hEq, List.traverse_eq_map_id]
      rfl  -- collapses the `Id` applicative `<$>` (reducible-transparency `rw` won't)
  | iverson b =>
      simp only [Factor.mapUID, Factor.traverseAxes, Factor.mapUID_old]
      show (Factor.iverson (BoolExpr.mapUID f b) : Id Factor) = Factor.iverson (BoolExpr.mapUID_old f b)
      rw [BoolExpr.mapUID_eq_old f b]
  | unaryFn op nm es =>
      simp only [Factor.mapUID, Factor.traverseAxes, Factor.mapUID_old]
      show Factor.unaryFn op nm (Traversable.traverse (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f)) es)
        = Factor.unaryFn op nm (es.map (IdxExpr.mapUID_old f))
      have hEq : (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) : IdxExpr → Id IdxExpr)
          = pure ∘ IdxExpr.mapUID_old f := by
        funext e
        exact IdxExpr.mapUID_eq_old f e
      simp only [Traversable.traverse, hEq, List.traverse_eq_map_id]
      rfl  -- collapses the `Id` applicative `<$>` (reducible-transparency `rw` won't)

def ProdTerm.mapUID (f : UData → UData) (p : ProdTerm) : ProdTerm :=
  { factors := p.factors.map (Factor.mapUID f) }
def SumExpr.mapUID (f : UData → UData) (s : SumExpr) : SumExpr :=
  { terms := s.terms.map (ProdTerm.mapUID f) }
def RHSExpr.mapUID (f : UData → UData) (r : RHSExpr) : RHSExpr :=
  { body := SumExpr.mapUID f r.body, nonlin := Nonlin.mapUID f r.nonlin, agg := r.agg }

def LHSSlot.mapUID (f : UData → UData) : LHSSlot → LHSSlot
  | .free a     => .free (AxisSpec.mapUID f a)
  | .freeNorm a => .freeNorm (AxisSpec.mapUID f a)
  | .iterAt a n => .iterAt (AxisSpec.mapUID f a) n
  | .iterNext a => .iterNext (AxisSpec.mapUID f a)
  | .affine e   => .affine (IdxExpr.mapUID f e)

def Decl.mapUID (f : UData → UData) : Decl → Decl
  | .tensor nm ax        => .tensor nm (ax.map (AxisSpec.mapUID f))
  | .predicate nm ax     => .predicate nm (ax.map (AxisSpec.mapUID f))
  | .linear nm ax b      => .linear nm (ax.map (AxisSpec.mapUID f)) b
  | .axis ax n           => .axis (AxisSpec.mapUID f ax) n
instance : TermTraversable Decl where traverseUID := Decl.mapUID

def Stmt.mapUID (f : UData → UData) : Stmt → Stmt
  | .assign nm ls r      => .assign nm (ls.map (LHSSlot.mapUID f)) (RHSExpr.mapUID f r)
  | .scatter nm ls r o   => .scatter nm (ls.map (LHSSlot.mapUID f)) (RHSExpr.mapUID f r) o
  | .recurMorphism nm ax tc => .recurMorphism nm (AxisSpec.mapUID f ax) tc
instance : TermTraversable Stmt where traverseUID := Stmt.mapUID

instance : TermTraversable TLProgram where
  traverseUID f p := { decls := p.decls.map (Decl.mapUID f), stmts := p.stmts.map (Stmt.mapUID f) }

end LeanNCD

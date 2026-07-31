-- test/DSL/TraverseAxesEquiv.lean
--
-- E1 migrated every AST node's collectors/mappers to instantiations of one `X.traverseAxes`
-- at three applicatives (`Id` → `X.mapUID` remap, `ConstL (List AxisSpec)` → `specs*`,
-- `ConstL (List UID)` → `*AxisUIDs`). The `specs*` direction's permanent equivalence
-- theorems live in `TraverseAxesSpike.lean`. This file is the PERMANENT living-theorem home
-- for the other two directions:
--   * Id direction (12 nodes): each production `X.mapUID` (an `Id` instantiation of
--     `X.traverseAxes`) is proved equal to an independent hand-written reference `X.mapUID_ref`
--     — the original pre-migration recursive body.
--   * uid direction (5 collectors): each production `*AxisUIDs` (a `ConstL (List UID)`
--     instantiation of `traverseAxes`) is proved equal to an independent hand-written
--     reference `*AxisUIDs_ref`.
-- These certificates were originally proved during the E1 migration itself (as `_old`/`_eq_old`
-- scaffolding in `LeanNCD/DSL/Traverse.lean` and `LeanNCD/Eval/Contract.lean`) and later deleted
-- from production once callers were migrated; they are re-instated here, renamed, as permanent
-- regression tests that `traverseAxes` continues to agree with the original hand-written
-- recursions.
import LeanNCD.DSL.Traverse
import LeanNCD.Eval.Contract
import LeanNCD.DSL.TraverseAxes
import Mathlib.Control.Traversable.Instances

open LeanNCD
open LeanNCD.Eval

-- ===== Id direction: X.mapUID = X.mapUID_ref =====

private def IdxExpr.mapUID_ref (f : UData → UData) : IdxExpr → IdxExpr
  | .axis a       => .axis (AxisSpec.mapUID f a)
  | .const n      => .const n
  | .scale n a    => .scale n (AxisSpec.mapUID f a)
  | .shift a n    => .shift (AxisSpec.mapUID f a) n
  | .affine n xs  => .affine n (xs.map (fun (c, a) => (c, AxisSpec.mapUID f a)))

theorem IdxExpr.mapUID_eq_ref (f : UData → UData) (e : IdxExpr) :
    IdxExpr.mapUID f e = IdxExpr.mapUID_ref f e := by
  cases e with
  | axis a => rfl
  | const n => rfl
  | scale c a => rfl
  | shift a n => rfl
  | affine n xs =>
      have hEq : (fun (ca : Int × AxisSpec) => Prod.mk ca.1 <$> AxisSpec.mapUID f ca.2 :
            Int × AxisSpec → Id (Int × AxisSpec))
          = pure ∘ (fun ca => (ca.1, AxisSpec.mapUID f ca.2)) := rfl
      simp only [IdxExpr.mapUID, IdxExpr.traverseAxes, IdxExpr.mapUID_ref, Traversable.traverse,
        hEq, List.traverse_eq_map_id]
      rfl

private def PredArith.mapUID_ref (f : UData → UData) : PredArith → PredArith
  | .embed e  => .embed (IdxExpr.mapUID_ref f e)
  | .mul a b  => .mul (PredArith.mapUID_ref f a) (PredArith.mapUID_ref f b)
  | .iabs a   => .iabs (PredArith.mapUID_ref f a)

theorem PredArith.mapUID_eq_ref (f : UData → UData) (e : PredArith) :
    PredArith.mapUID f e = PredArith.mapUID_ref f e := by
  induction e with
  | embed e =>
      simp only [PredArith.mapUID, PredArith.traverseAxes, PredArith.mapUID_ref]
      show (PredArith.embed <$> IdxExpr.mapUID f e : Id PredArith) = PredArith.embed (IdxExpr.mapUID_ref f e)
      rw [IdxExpr.mapUID_eq_ref f e]
      rfl  -- collapses the `Id` applicative `<$>` (reducible-transparency `rw` won't)
  | mul a b iha ihb =>
      simp only [PredArith.mapUID, PredArith.traverseAxes, PredArith.mapUID_ref]
      show (PredArith.mul <$> PredArith.mapUID f a <*> PredArith.mapUID f b : Id PredArith)
        = PredArith.mul (PredArith.mapUID_ref f a) (PredArith.mapUID_ref f b)
      rw [iha, ihb]
      rfl  -- collapses the `Id` applicative `<$>`/`<*>` (reducible-transparency `rw` won't)
  | iabs a iha =>
      simp only [PredArith.mapUID, PredArith.traverseAxes, PredArith.mapUID_ref]
      show (PredArith.iabs <$> PredArith.mapUID f a : Id PredArith) = PredArith.iabs (PredArith.mapUID_ref f a)
      rw [iha]
      rfl  -- collapses the `Id` applicative `<$>` (reducible-transparency `rw` won't)

private def BoolExpr.mapUID_ref (f : UData → UData) : BoolExpr → BoolExpr
  | .rel op a b => .rel op (PredArith.mapUID_ref f a) (PredArith.mapUID_ref f b)
  | .and a b    => .and (BoolExpr.mapUID_ref f a) (BoolExpr.mapUID_ref f b)
  | .or  a b    => .or  (BoolExpr.mapUID_ref f a) (BoolExpr.mapUID_ref f b)
  | .not a      => .not (BoolExpr.mapUID_ref f a)
  | .ieq a b    => .ieq (PredArith.mapUID_ref f a) (PredArith.mapUID_ref f b)

theorem BoolExpr.mapUID_eq_ref (f : UData → UData) (e : BoolExpr) :
    BoolExpr.mapUID f e = BoolExpr.mapUID_ref f e := by
  induction e with
  | rel op a b =>
      simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_ref]
      show (BoolExpr.rel op <$> PredArith.mapUID f a <*> PredArith.mapUID f b : Id BoolExpr)
        = BoolExpr.rel op (PredArith.mapUID_ref f a) (PredArith.mapUID_ref f b)
      rw [PredArith.mapUID_eq_ref f a, PredArith.mapUID_eq_ref f b]
      rfl  -- collapses the `Id` applicative `<$>`/`<*>` (reducible-transparency `rw` won't)
  | and a b iha ihb =>
      simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_ref]
      show (BoolExpr.and <$> BoolExpr.mapUID f a <*> BoolExpr.mapUID f b : Id BoolExpr)
        = BoolExpr.and (BoolExpr.mapUID_ref f a) (BoolExpr.mapUID_ref f b)
      rw [iha, ihb]
      rfl  -- collapses the `Id` applicative `<$>`/`<*>` (reducible-transparency `rw` won't)
  | or a b iha ihb =>
      simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_ref]
      show (BoolExpr.or <$> BoolExpr.mapUID f a <*> BoolExpr.mapUID f b : Id BoolExpr)
        = BoolExpr.or (BoolExpr.mapUID_ref f a) (BoolExpr.mapUID_ref f b)
      rw [iha, ihb]
      rfl  -- collapses the `Id` applicative `<$>`/`<*>` (reducible-transparency `rw` won't)
  | not a iha =>
      simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_ref]
      show (BoolExpr.not <$> BoolExpr.mapUID f a : Id BoolExpr) = BoolExpr.not (BoolExpr.mapUID_ref f a)
      rw [iha]
      rfl  -- collapses the `Id` applicative `<$>` (reducible-transparency `rw` won't)
  | ieq a b =>
      simp only [BoolExpr.mapUID, BoolExpr.traverseAxes, BoolExpr.mapUID_ref]
      show (BoolExpr.ieq <$> PredArith.mapUID f a <*> PredArith.mapUID f b : Id BoolExpr)
        = BoolExpr.ieq (PredArith.mapUID_ref f a) (PredArith.mapUID_ref f b)
      rw [PredArith.mapUID_eq_ref f a, PredArith.mapUID_eq_ref f b]
      rfl  -- collapses the `Id` applicative `<$>`/`<*>` (reducible-transparency `rw` won't)

/-- Independent hand-written reference for `Nonlin.mapUID`: `.identity`/`.pointwise` pass through
    unchanged, and `.axiswise` remaps the MASK's UIDs (spelled out via `BoolExpr.mapUID_ref`, NOT
    delegated to `Nonlin.mapUID`/`Nonlin.traverseAxes`) — a production traversal that silently
    dropped the mask remap would break `Nonlin.mapUID_eq_ref` below. -/
private def Nonlin.mapUID_ref (f : UData → UData) : Nonlin → Nonlin
  | .identity      => .identity
  | .pointwise pf  => .pointwise pf
  | .axiswise fn m => .axiswise fn (m.map (BoolExpr.mapUID_ref f))

theorem Nonlin.mapUID_eq_ref (f : UData → UData) (n : Nonlin) :
    Nonlin.mapUID f n = Nonlin.mapUID_ref f n := by
  cases n with
  | identity => rfl
  | pointwise pf => rfl
  | axiswise fn m =>
      cases m with
      | none => rfl
      | some b =>
          simp only [Nonlin.mapUID, Nonlin.traverseAxes, Nonlin.mapUID_ref]
          show (Nonlin.axiswise fn (some (BoolExpr.mapUID f b)) : Id Nonlin)
            = Nonlin.axiswise fn (some (BoolExpr.mapUID_ref f b))
          rw [BoolExpr.mapUID_eq_ref f b]

private def Factor.mapUID_ref (f : UData → UData) : Factor → Factor
  | .read nm es => .read nm (es.map (IdxExpr.mapUID_ref f))
  | .iverson b  => .iverson (BoolExpr.mapUID_ref f b)
  | .unaryFn op nm es => .unaryFn op nm (es.map (IdxExpr.mapUID_ref f))

theorem Factor.mapUID_eq_ref (f : UData → UData) (x : Factor) :
    Factor.mapUID f x = Factor.mapUID_ref f x := by
  cases x with
  | read nm es =>
      simp only [Factor.mapUID, Factor.traverseAxes, Factor.mapUID_ref]
      show Factor.read nm (Traversable.traverse (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f)) es)
        = Factor.read nm (es.map (IdxExpr.mapUID_ref f))
      have hEq : (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) : IdxExpr → Id IdxExpr)
          = pure ∘ IdxExpr.mapUID_ref f := by
        funext e
        exact IdxExpr.mapUID_eq_ref f e
      simp only [Traversable.traverse, hEq, List.traverse_eq_map_id]
      rfl  -- collapses the `Id` applicative `<$>` (reducible-transparency `rw` won't)
  | iverson b =>
      simp only [Factor.mapUID, Factor.traverseAxes, Factor.mapUID_ref]
      show (Factor.iverson (BoolExpr.mapUID f b) : Id Factor) = Factor.iverson (BoolExpr.mapUID_ref f b)
      rw [BoolExpr.mapUID_eq_ref f b]
  | unaryFn op nm es =>
      simp only [Factor.mapUID, Factor.traverseAxes, Factor.mapUID_ref]
      show Factor.unaryFn op nm (Traversable.traverse (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f)) es)
        = Factor.unaryFn op nm (es.map (IdxExpr.mapUID_ref f))
      have hEq : (IdxExpr.traverseAxes (f := Id) (AxisSpec.mapUID f) : IdxExpr → Id IdxExpr)
          = pure ∘ IdxExpr.mapUID_ref f := by
        funext e
        exact IdxExpr.mapUID_eq_ref f e
      simp only [Traversable.traverse, hEq, List.traverse_eq_map_id]
      rfl  -- collapses the `Id` applicative `<$>` (reducible-transparency `rw` won't)

private def ProdTerm.mapUID_ref (f : UData → UData) (p : ProdTerm) : ProdTerm :=
  { factors := p.factors.map (Factor.mapUID_ref f) }

theorem ProdTerm.mapUID_eq_ref (f : UData → UData) (p : ProdTerm) :
    ProdTerm.mapUID f p = ProdTerm.mapUID_ref f p := by
  simp only [ProdTerm.mapUID, ProdTerm.traverseAxes, ProdTerm.mapUID_ref]
  show (fun fs => ({ factors := fs } : ProdTerm))
      (Traversable.traverse (Factor.traverseAxes (f := Id) (AxisSpec.mapUID f)) p.factors)
    = { factors := p.factors.map (Factor.mapUID_ref f) }
  have core : ∀ ys : List Factor,
      Traversable.traverse (Factor.traverseAxes (f := Id) (AxisSpec.mapUID f)) ys = ys.map (Factor.mapUID_ref f) := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        simp only [List.traverse_cons]
        show (Factor.mapUID f hd) :: (Traversable.traverse (Factor.traverseAxes (f := Id) (AxisSpec.mapUID f)) tl)
          = Factor.mapUID_ref f hd :: tl.map (Factor.mapUID_ref f)
        rw [Factor.mapUID_eq_ref f hd, ih]
  rw [core p.factors]

private def SumExpr.mapUID_ref (f : UData → UData) (s : SumExpr) : SumExpr :=
  { terms := s.terms.map (ProdTerm.mapUID_ref f) }

theorem SumExpr.mapUID_eq_ref (f : UData → UData) (s : SumExpr) :
    SumExpr.mapUID f s = SumExpr.mapUID_ref f s := by
  simp only [SumExpr.mapUID, SumExpr.traverseAxes, SumExpr.mapUID_ref]
  show (fun ts => ({ terms := ts } : SumExpr))
      (Traversable.traverse (ProdTerm.traverseAxes (f := Id) (AxisSpec.mapUID f)) s.terms)
    = { terms := s.terms.map (ProdTerm.mapUID_ref f) }
  have core : ∀ ys : List ProdTerm,
      Traversable.traverse (ProdTerm.traverseAxes (f := Id) (AxisSpec.mapUID f)) ys = ys.map (ProdTerm.mapUID_ref f) := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        simp only [List.traverse_cons]
        show (ProdTerm.mapUID f hd) :: (Traversable.traverse (ProdTerm.traverseAxes (f := Id) (AxisSpec.mapUID f)) tl)
          = ProdTerm.mapUID_ref f hd :: tl.map (ProdTerm.mapUID_ref f)
        rw [ProdTerm.mapUID_eq_ref f hd, ih]
  rw [core s.terms]

private def RHSExpr.mapUID_ref (f : UData → UData) (r : RHSExpr) : RHSExpr :=
  { body := SumExpr.mapUID_ref f r.body, nonlin := Nonlin.mapUID_ref f r.nonlin, agg := r.agg }

theorem RHSExpr.mapUID_eq_ref (f : UData → UData) (r : RHSExpr) :
    RHSExpr.mapUID f r = RHSExpr.mapUID_ref f r := by
  simp only [RHSExpr.mapUID, RHSExpr.traverseAxesWithMask, RHSExpr.mapUID_ref]
  show (fun body nonlin => ({ body := body, nonlin := nonlin, agg := r.agg } : RHSExpr))
      (SumExpr.mapUID f r.body) (Nonlin.mapUID f r.nonlin)
    = { body := SumExpr.mapUID_ref f r.body, nonlin := Nonlin.mapUID_ref f r.nonlin, agg := r.agg }
  rw [SumExpr.mapUID_eq_ref f r.body, Nonlin.mapUID_eq_ref f r.nonlin]

private def LHSSlot.mapUID_ref (f : UData → UData) : LHSSlot → LHSSlot
  | .free a     => .free (AxisSpec.mapUID f a)
  | .freeNorm a => .freeNorm (AxisSpec.mapUID f a)
  | .iterAt a n => .iterAt (AxisSpec.mapUID f a) n
  | .iterNext a => .iterNext (AxisSpec.mapUID f a)
  | .affine e   => .affine (IdxExpr.mapUID_ref f e)

theorem LHSSlot.mapUID_eq_ref (f : UData → UData) (s : LHSSlot) :
    LHSSlot.mapUID f s = LHSSlot.mapUID_ref f s := by
  cases s with
  | free a => rfl
  | freeNorm a => rfl
  | iterAt a n => rfl
  | iterNext a => rfl
  | affine e =>
      simp only [LHSSlot.mapUID, LHSSlot.traverseAxes, LHSSlot.mapUID_ref]
      show (LHSSlot.affine <$> IdxExpr.mapUID f e : Id LHSSlot) = LHSSlot.affine (IdxExpr.mapUID_ref f e)
      rw [IdxExpr.mapUID_eq_ref f e]
      rfl  -- collapses the `Id` applicative `<$>` (reducible-transparency `rw` won't)

private def Decl.mapUID_ref (f : UData → UData) : Decl → Decl
  | .tensor nm ax        => .tensor nm (ax.map (AxisSpec.mapUID f))
  | .predicate nm ax     => .predicate nm (ax.map (AxisSpec.mapUID f))
  | .linear nm ax b      => .linear nm (ax.map (AxisSpec.mapUID f)) b
  | .axis ax n           => .axis (AxisSpec.mapUID f ax) n
  | .iter ax n           => .iter (AxisSpec.mapUID f ax) n

theorem Decl.mapUID_eq_ref (f : UData → UData) (d : Decl) :
    Decl.mapUID f d = Decl.mapUID_ref f d := by
  have hMap : ∀ ys : List AxisSpec,
      Traversable.traverse (m := Id) (AxisSpec.mapUID f) ys = ys.map (AxisSpec.mapUID f) := by
    intro ys
    show List.traverse ((pure : AxisSpec → Id AxisSpec) ∘ AxisSpec.mapUID f) ys
      = ys.map (AxisSpec.mapUID f)
    rw [List.traverse_eq_map_id]
    rfl  -- collapses the `Id` applicative `pure` (reducible-transparency `rw` won't)
  cases d with
  | tensor nm ax =>
      simp only [Decl.mapUID, Decl.traverseAxes, Decl.mapUID_ref]
      show Decl.tensor nm (Traversable.traverse (m := Id) (AxisSpec.mapUID f) ax) = Decl.tensor nm (ax.map (AxisSpec.mapUID f))
      rw [hMap ax]
  | predicate nm ax =>
      simp only [Decl.mapUID, Decl.traverseAxes, Decl.mapUID_ref]
      show Decl.predicate nm (Traversable.traverse (m := Id) (AxisSpec.mapUID f) ax) = Decl.predicate nm (ax.map (AxisSpec.mapUID f))
      rw [hMap ax]
  | linear nm ax b =>
      simp only [Decl.mapUID, Decl.traverseAxes, Decl.mapUID_ref]
      show Decl.linear nm (Traversable.traverse (m := Id) (AxisSpec.mapUID f) ax) b = Decl.linear nm (ax.map (AxisSpec.mapUID f)) b
      rw [hMap ax]
  | axis ax n => rfl
  | iter ax n => rfl

private def Stmt.mapUID_ref (f : UData → UData) : Stmt → Stmt
  | .assign nm ls r      => .assign nm (ls.map (LHSSlot.mapUID_ref f)) (RHSExpr.mapUID_ref f r)
  | .scatter nm ls r o   => .scatter nm (ls.map (LHSSlot.mapUID_ref f)) (RHSExpr.mapUID_ref f r) o
  | .recurMorphism nm ax tc => .recurMorphism nm (AxisSpec.mapUID f ax) tc

theorem Stmt.mapUID_eq_ref (f : UData → UData) (s : Stmt) :
    Stmt.mapUID f s = Stmt.mapUID_ref f s := by
  have core : ∀ ys : List LHSSlot,
      Traversable.traverse (LHSSlot.traverseAxes (f := Id) (AxisSpec.mapUID f)) ys = ys.map (LHSSlot.mapUID_ref f) := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        simp only [List.traverse_cons]
        show (LHSSlot.mapUID f hd) :: (Traversable.traverse (LHSSlot.traverseAxes (f := Id) (AxisSpec.mapUID f)) tl)
          = LHSSlot.mapUID_ref f hd :: tl.map (LHSSlot.mapUID_ref f)
        rw [LHSSlot.mapUID_eq_ref f hd, ih]
  cases s with
  | assign nm ls r =>
      simp only [Stmt.mapUID, Stmt.traverseAxes, Stmt.mapUID_ref]
      show (fun ls' r' => Stmt.assign nm ls' r')
          (Traversable.traverse (LHSSlot.traverseAxes (f := Id) (AxisSpec.mapUID f)) ls) (RHSExpr.mapUID f r)
        = Stmt.assign nm (ls.map (LHSSlot.mapUID_ref f)) (RHSExpr.mapUID_ref f r)
      rw [core ls, RHSExpr.mapUID_eq_ref f r]
  | scatter nm ls r o =>
      simp only [Stmt.mapUID, Stmt.traverseAxes, Stmt.mapUID_ref]
      show (fun ls' r' => Stmt.scatter nm ls' r' o)
          (Traversable.traverse (LHSSlot.traverseAxes (f := Id) (AxisSpec.mapUID f)) ls) (RHSExpr.mapUID f r)
        = Stmt.scatter nm (ls.map (LHSSlot.mapUID_ref f)) (RHSExpr.mapUID_ref f r) o
      rw [core ls, RHSExpr.mapUID_eq_ref f r]
  | recurMorphism nm ax tc => rfl

private def TLProgram.mapUID_ref (f : UData → UData) (p : TLProgram) : TLProgram :=
  { decls := p.decls.map (Decl.mapUID_ref f), stmts := p.stmts.map (Stmt.mapUID_ref f) }

theorem TLProgram.mapUID_eq_ref (f : UData → UData) (p : TLProgram) :
    TLProgram.mapUID f p = TLProgram.mapUID_ref f p := by
  have coreD : Traversable.traverse (Decl.traverseAxes (f := Id) (AxisSpec.mapUID f)) p.decls = p.decls.map (Decl.mapUID_ref f) := by
    have core : ∀ ds : List Decl,
        Traversable.traverse (Decl.traverseAxes (f := Id) (AxisSpec.mapUID f)) ds = ds.map (Decl.mapUID_ref f) := by
      intro ds
      induction ds with
      | nil => rfl
      | cons hd tl ih =>
          simp only [List.traverse_cons]
          show (Decl.mapUID f hd) :: (Traversable.traverse (Decl.traverseAxes (f := Id) (AxisSpec.mapUID f)) tl)
            = Decl.mapUID_ref f hd :: tl.map (Decl.mapUID_ref f)
          rw [Decl.mapUID_eq_ref f hd, ih]
    exact core p.decls
  have coreS : Traversable.traverse (Stmt.traverseAxes (f := Id) (AxisSpec.mapUID f)) p.stmts = p.stmts.map (Stmt.mapUID_ref f) := by
    have core : ∀ ss : List Stmt,
        Traversable.traverse (Stmt.traverseAxes (f := Id) (AxisSpec.mapUID f)) ss = ss.map (Stmt.mapUID_ref f) := by
      intro ss
      induction ss with
      | nil => rfl
      | cons hd tl ih =>
          simp only [List.traverse_cons]
          show (Stmt.mapUID f hd) :: (Traversable.traverse (Stmt.traverseAxes (f := Id) (AxisSpec.mapUID f)) tl)
            = Stmt.mapUID_ref f hd :: tl.map (Stmt.mapUID_ref f)
          rw [Stmt.mapUID_eq_ref f hd, ih]
    exact core p.stmts
  simp only [TLProgram.mapUID, TLProgram.traverseAxes, TLProgram.mapUID_ref]
  show (fun decls stmts => ({ decls := decls, stmts := stmts } : TLProgram))
      (Traversable.traverse (Decl.traverseAxes (f := Id) (AxisSpec.mapUID f)) p.decls)
      (Traversable.traverse (Stmt.traverseAxes (f := Id) (AxisSpec.mapUID f)) p.stmts)
    = { decls := p.decls.map (Decl.mapUID_ref f), stmts := p.stmts.map (Stmt.mapUID_ref f) }
  rw [coreD, coreS]

-- ===== uid direction: *AxisUIDs = *AxisUIDs_ref =====

private def idxAxisUIDs_ref : IdxExpr → List UID
  | .axis a      => [a.uid]
  | .const _     => []
  | .scale _ a   => [a.uid]
  | .shift a _   => [a.uid]
  | .affine _ xs => xs.map (·.2.uid)

theorem idxAxisUIDs_eq_ref (e : IdxExpr) : idxAxisUIDs e = idxAxisUIDs_ref e := by
  cases e with
  | axis a => rfl
  | const n => rfl
  | scale c a => rfl
  | shift a n => rfl
  | affine n xs =>
      have hmap : (fun (ca : Int × AxisSpec) => Prod.mk ca.1 <$> (⟨[ca.2.uid]⟩ : ConstL (List UID) AxisSpec))
          = (fun ca => (⟨[ca.2.uid]⟩ : ConstL (List UID) (Int × AxisSpec))) := rfl
      have core : ∀ ys : List (Int × AxisSpec),
          (Traversable.traverse (fun ca => (⟨[ca.2.uid]⟩ : ConstL (List UID) (Int × AxisSpec))) ys).run
            = ys.map (·.2.uid) := by
        intro ys
        induction ys with
        | nil => rfl
        | cons hd tl ih =>
            show [hd.2.uid] ++
                (Traversable.traverse (fun ca => (⟨[ca.2.uid]⟩ : ConstL (List UID) (Int × AxisSpec))) tl).run
              = hd.2.uid :: List.map (·.2.uid) tl
            rw [ih]
            rfl
      -- restate the goal with the new `idxAxisUIDs` unfolded to its `.run`; RHS is `idxAxisUIDs_ref`'s
      -- `.affine` arm `xs.map (·.2.uid)`.
      show (IdxExpr.affine n <$>
          Traversable.traverse (fun ca => Prod.mk ca.1 <$> (⟨[ca.2.uid]⟩ : ConstL (List UID) AxisSpec)) xs :
          ConstL (List UID) IdxExpr).run = xs.map (·.2.uid)
      rw [hmap]
      exact core xs

private def predAxisUIDs_ref : PredArith → List UID
  | .embed e => idxAxisUIDs_ref e
  | .mul a b => predAxisUIDs_ref a ++ predAxisUIDs_ref b
  | .iabs a  => predAxisUIDs_ref a

theorem predAxisUIDs_eq_ref (e : PredArith) : predAxisUIDs e = predAxisUIDs_ref e := by
  induction e with
  | embed e => exact idxAxisUIDs_eq_ref e
  | mul a b iha ihb =>
      show predAxisUIDs a ++ predAxisUIDs b = predAxisUIDs_ref a ++ predAxisUIDs_ref b
      rw [iha, ihb]
  | iabs a iha =>
      show predAxisUIDs a = predAxisUIDs_ref a
      exact iha

private def boolAxisUIDs_ref : BoolExpr → List UID
  | .rel _ a b => predAxisUIDs_ref a ++ predAxisUIDs_ref b
  | .and a b   => boolAxisUIDs_ref a ++ boolAxisUIDs_ref b
  | .or  a b   => boolAxisUIDs_ref a ++ boolAxisUIDs_ref b
  | .not a     => boolAxisUIDs_ref a
  | .ieq a b   => predAxisUIDs_ref a ++ predAxisUIDs_ref b

theorem boolAxisUIDs_eq_ref (e : BoolExpr) : boolAxisUIDs e = boolAxisUIDs_ref e := by
  induction e with
  | rel op a b =>
      show predAxisUIDs a ++ predAxisUIDs b = predAxisUIDs_ref a ++ predAxisUIDs_ref b
      rw [predAxisUIDs_eq_ref a, predAxisUIDs_eq_ref b]
  | and a b iha ihb =>
      show boolAxisUIDs a ++ boolAxisUIDs b = boolAxisUIDs_ref a ++ boolAxisUIDs_ref b
      rw [iha, ihb]
  | or a b iha ihb =>
      show boolAxisUIDs a ++ boolAxisUIDs b = boolAxisUIDs_ref a ++ boolAxisUIDs_ref b
      rw [iha, ihb]
  | not a iha =>
      show boolAxisUIDs a = boolAxisUIDs_ref a
      exact iha
  | ieq a b =>
      show predAxisUIDs a ++ predAxisUIDs b = predAxisUIDs_ref a ++ predAxisUIDs_ref b
      rw [predAxisUIDs_eq_ref a, predAxisUIDs_eq_ref b]

private def termAxisUIDs_ref (t : ProdTerm) : List UID :=
  t.factors.flatMap (fun
    | .read _ es => es.flatMap idxAxisUIDs_ref
    | .iverson b => boolAxisUIDs_ref b
    | .unaryFn _ _ es => es.flatMap idxAxisUIDs_ref)

theorem termAxisUIDs_eq_ref (t : ProdTerm) : termAxisUIDs t = termAxisUIDs_ref t := by
  have hfac : ∀ x : Factor,
      (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) x).run
        = (match x with
           | .read _ es => es.flatMap idxAxisUIDs_ref
           | .iverson b => boolAxisUIDs_ref b
           | .unaryFn _ _ es => es.flatMap idxAxisUIDs_ref) := by
    intro x
    cases x with
    | read nm es =>
        show (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) es).run
          = es.flatMap idxAxisUIDs_ref
        induction es with
        | nil => rfl
        | cons hd tl ih =>
            show idxAxisUIDs hd ++
                (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
              = idxAxisUIDs_ref hd ++ tl.flatMap idxAxisUIDs_ref
            rw [idxAxisUIDs_eq_ref hd, ih]
    | iverson b => exact boolAxisUIDs_eq_ref b
    | unaryFn op nm es =>
        show (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) es).run
          = es.flatMap idxAxisUIDs_ref
        induction es with
        | nil => rfl
        | cons hd tl ih =>
            show idxAxisUIDs hd ++
                (Traversable.traverse (IdxExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
              = idxAxisUIDs_ref hd ++ tl.flatMap idxAxisUIDs_ref
            rw [idxAxisUIDs_eq_ref hd, ih]
  -- fold `hfac` over the factor list (`termAxisUIDs_ref t` is `t.factors.flatMap` of that match).
  show (Traversable.traverse (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) t.factors).run
    = termAxisUIDs_ref t
  have core : ∀ ys : List Factor,
      (Traversable.traverse (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ys).run
        = ys.flatMap (fun x =>
            match x with
            | .read _ es => es.flatMap idxAxisUIDs_ref
            | .iverson b => boolAxisUIDs_ref b
            | .unaryFn _ _ es => es.flatMap idxAxisUIDs_ref) := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) hd).run ++
            (Traversable.traverse (Factor.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
          = (match hd with
             | .read _ es => es.flatMap idxAxisUIDs_ref
             | .iverson b => boolAxisUIDs_ref b
             | .unaryFn _ _ es => es.flatMap idxAxisUIDs_ref)
            ++ tl.flatMap (fun x =>
                match x with
                | .read _ es => es.flatMap idxAxisUIDs_ref
                | .iverson b => boolAxisUIDs_ref b
                | .unaryFn _ _ es => es.flatMap idxAxisUIDs_ref)
        rw [hfac hd, ih]
  exact core t.factors

private def readAxisUIDs_ref (rhs : RHSExpr) : List UID :=
  rhs.body.terms.flatMap termAxisUIDs_ref

theorem readAxisUIDs_eq_ref (r : RHSExpr) : readAxisUIDs r = readAxisUIDs_ref r := by
  show (SumExpr.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩) r.body).run
    = r.body.terms.flatMap termAxisUIDs_ref
  have core : ∀ ys : List ProdTerm,
      (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) ys).run
        = ys.flatMap termAxisUIDs_ref := by
    intro ys
    induction ys with
    | nil => rfl
    | cons hd tl ih =>
        show termAxisUIDs hd ++
            (Traversable.traverse (ProdTerm.traverseAxes (f := ConstL (List UID)) (fun a => ⟨[a.uid]⟩)) tl).run
          = termAxisUIDs_ref hd ++ tl.flatMap termAxisUIDs_ref
        rw [termAxisUIDs_eq_ref hd, ih]
  exact core r.body.terms

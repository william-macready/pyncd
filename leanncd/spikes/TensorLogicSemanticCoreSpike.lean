import LeanNCD.Eval.Error
import LeanNCD.Bridge.Realize
import LeanNCD.DSL.Pipeline.Lowering

/-!
Off-production-path scalar feasibility fragment. Contexts are indices of `Expr`, so a
finite reduction really extends its body's context. Operations are data, not algebraic
instances: no associativity, distributivity, or machine-float semiring laws are assumed.

The sole partial primitive is reciprocal. Read lists retain duplicates and enumerate
bound coordinates; readiness is structural, not value-dependent. Reduction is a strict
right fold in increasing coordinate order. Empty bodies are never evaluated.
This is not an array grammar, substitution theory, arbitrary-arity primitive API,
D-graded functor, or Algebra instance. The signed bridge below is one rank-one instance,
not a general categorical action; finite element bounds require separate evidence.
-/

namespace LeanNCD.TensorLogicSemanticCoreSpike
open LeanNCD.Eval

structure Ops (K : Type) where
  zero : K
  add : K → K → K
  mul : K → K → K
  recip : K → Except UnaryDomainOp K

inductive Bin
  | add | mul

def Ops.combine (ops : Ops K) : Bin → K → K → K
  | .add => ops.add
  | .mul => ops.mul

inductive Expr (K Addr : Type) : Type → Type 1
  | lit {Γ : Type} : K → Expr K Addr Γ
  | read {Γ : Type} : (Γ → Addr) → Expr K Addr Γ
  | binary {Γ : Type} : Bin → Expr K Addr Γ → Expr K Addr Γ → Expr K Addr Γ
  | recip {Γ : Type} : Expr K Addr Γ → Expr K Addr Γ
  | reduce {Γ : Type} (n : Nat) : Expr K Addr (Γ × Fin n) → Expr K Addr Γ

def footprint : Expr K Addr Γ → Γ → List Addr
  | .lit _, _ => []
  | .read a, γ => [a γ] -- MUTATION_FOOTPRINT_READ
  | .binary _ l r, γ => footprint l γ ++ footprint r γ
  | .recip e, γ => footprint e γ
  | .reduce n body, γ =>
      (List.finRange n).flatMap (fun i => footprint body (γ, i))

inductive Failure (Addr : Type)
  | unavailable : Addr → Failure Addr
  | domain : UnaryDomainOp → Failure Addr
  deriving DecidableEq, Repr

def foldValues (ops : Ops K) : List (Except (Failure Addr) K) → Except (Failure Addr) K
  | [] => .ok ops.zero -- MUTATION_EMPTY_REDUCTION
  | x :: xs => do
      let a ← x
      let b ← foldValues ops xs
      pure (ops.add a b)

def evalWith (ops : Ops K) (store : Addr → Except (Failure Addr) K) :
    Expr K Addr Γ → Γ → Except (Failure Addr) K
  | .lit x, _ => .ok x
  | .read a, γ => store (a γ)
  | .binary b l r, γ => do
      let x ← evalWith ops store l γ
      let y ← evalWith ops store r γ
      pure (ops.combine b x y)
  | .recip e, γ => do
      let x ← evalWith ops store e γ
      (ops.recip x).mapError Failure.domain
  | .reduce n body, γ =>
      foldValues ops ((List.finRange n).map (fun i => evalWith ops store body (γ, i)))

/-- Equality of the whole result includes both value and undefinedness stability.
    Even the store's error payloads may vary away from the structural footprint. -/
theorem evalWith_stable (ops : Ops K) (e : Expr K Addr Γ) (γ : Γ)
    (s t : Addr → Except (Failure Addr) K)
    (agree : ∀ a ∈ footprint e γ, s a = t a) :
    evalWith ops s e γ = evalWith ops t e γ := by
  induction e with
  | lit x => rfl
  | read a => exact agree (a γ) (by simp [footprint])
  | binary b l r ihl ihr =>
      simp only [evalWith]
      rw [ihl γ (fun a ha => agree a (List.mem_append_left _ ha)),
        ihr γ (fun a ha => agree a (List.mem_append_right _ ha))]
  | recip e ih =>
      simp only [evalWith]
      rw [ih γ agree]
  | reduce n body ih =>
      simp only [evalWith]
      congr 1
      apply List.map_congr_left
      intro i hi
      apply ih (γ, i)
      intro a ha
      apply agree a
      exact List.mem_flatMap.mpr ⟨i, hi, ha⟩

def eval (ops : Ops K) (store : Addr → K) (e : Expr K Addr Γ) (γ : Γ) :=
  evalWith ops (fun a => .ok (store a)) e γ

theorem eval_stable (ops : Ops K) (e : Expr K Addr Γ) (γ : Γ) (s t : Addr → K)
    (agree : ∀ a ∈ footprint e γ, s a = t a) :
    eval ops s e γ = eval ops t e γ :=
  evalWith_stable ops e γ _ _ (fun a ha => congrArg Except.ok (agree a ha))

def partialRead (store : Addr → Option K) (a : Addr) : Except (Failure Addr) K :=
  match store a with
  | some x => .ok x
  | none => .error (.unavailable a)

def checkReads (store : Addr → Option K) : List Addr → Except (Failure Addr) Unit
  | [] => .ok ()
  | a :: as => do
      let _ ← partialRead store a
      checkReads store as

def Ready (store : Addr → Option K) (e : Expr K Addr Γ) (γ : Γ) : Prop :=
  ∀ a ∈ footprint e γ, ∃ x, store a = some x

/-- Preflight gives missing reads priority over primitive failures, even under a zero
    factor. Once ready, evaluation is exactly the same strict scalar interpreter. -/
def evalReady (ops : Ops K) (store : Addr → Option K) (e : Expr K Addr Γ) (γ : Γ) :
    Except (Failure Addr) K := do
  checkReads store (footprint e γ)
  evalWith ops (partialRead store) e γ

theorem checkReads_ok (store : Addr → Option K) (as : List Addr)
    (h : ∀ a ∈ as, ∃ x, store a = some x) : checkReads store as = .ok () := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      obtain ⟨x, hx⟩ := h a (by simp)
      simp only [checkReads, partialRead, hx]
      exact ih (fun b hb => h b (List.mem_cons_of_mem a hb))

/-- Only extension on reads is needed; arbitrary absent/unrelated entries are allowed.
    The conclusion includes a ready primitive's domain failure, not just successful values. -/
theorem ready_consistent (ops : Ops K) (e : Expr K Addr Γ) (γ : Γ)
    (p : Addr → Option K) (s : Addr → K)
    (extension : ∀ a ∈ footprint e γ, p a = some (s a)) :
    evalReady ops p e γ = eval ops s e γ := by
  have ready : Ready p e γ := fun a ha => ⟨s a, extension a ha⟩
  simp only [evalReady, checkReads_ok p _ ready]
  apply evalWith_stable
  intro a ha
  simp [partialRead, extension a ha]

theorem evalReady_stable (ops : Ops K) (e : Expr K Addr Γ) (γ : Γ)
    (p q : Addr → Option K) (agree : ∀ a ∈ footprint e γ, p a = q a) :
    evalReady ops p e γ = evalReady ops q e γ := by
  have checks : checkReads p (footprint e γ) = checkReads q (footprint e γ) := by
    generalize footprint e γ = as at *
    induction as with
    | nil => rfl
    | cons a as ih =>
        simp only [checkReads, partialRead, agree a (by simp)]
        rw [ih (fun b hb => agree b (List.mem_cons_of_mem a hb))]
  simp only [evalReady, checks]
  congr 1
  funext _
  exact evalWith_stable ops e γ _ _ (fun a ha => by simp [partialRead, agree a ha])

def rationalOps : Ops ℚ :=
  ⟨0, (· + ·), (· * ·), fun x => if x = 0 then .error .recip else .ok x⁻¹⟩

def floatOps : Ops Float :=
  ⟨0.0, (· + ·), (· * ·), UnaryOp.applyChecked .recip⟩

def float32Ops : Ops Float32 :=
  ⟨Float32.ofBits 0, (· + ·), (· * ·), UnaryOp.applyChecked32 .recip⟩

noncomputable def complexOps : Ops ℂ := by
  classical
  exact ⟨0, (· + ·), (· * ·), fun x =>
    if x = 0 then .error .recip else .ok x⁻¹⟩

def readSeven : Expr K UID Unit := .read (fun _ => 7)
def badRecip : Expr ℚ UID Unit := .recip (.lit 0)
def emptyBad : Expr ℚ UID Unit := .reduce 0 (.recip (.lit 0))
def boundSum : Expr ℚ UID Unit :=
  .reduce 3 (.read (fun γ => 7 + γ.2.val))
def zeroStrict : Expr ℚ UID Unit := .binary .mul (.lit 0) (.recip readSeven)
def exactStore (a : UID) : ℚ := if a = 7 then 2 else if a = 8 then 3 else 4
def partialStore (a : UID) : Option ℚ := if a = 7 then some 2 else none

example : footprint (readSeven : Expr ℚ UID Unit) () = [7] := rfl
example : footprint emptyBad () = [] := rfl
example : eval complexOps (fun _ => Complex.I)
    (.binary .mul readSeven readSeven) () = .ok (-1 : ℂ) := by
  change Except.ok (Complex.I * Complex.I) = _
  rw [Complex.I_mul_I]
example : eval complexOps (fun _ => 0) (.recip readSeven) () =
    .error (.domain .recip) := by
  change (complexOps.recip (0 : ℂ)).mapError Failure.domain = _
  simp [complexOps, Except.mapError]
example : eval rationalOps exactStore boundSum () = .ok 9 := by
  change Except.ok ((2 : ℚ) + (3 + (4 + 0))) = .ok 9
  congr 1
  norm_num
example : eval rationalOps exactStore (.recip readSeven) () = .ok (1 / 2) := by
  change Except.ok ((2 : ℚ)⁻¹) = .ok (1 / 2)
  congr 1
  norm_num
example : eval rationalOps exactStore emptyBad () = .ok 0 := rfl
example : eval rationalOps exactStore (.recip emptyBad) () = .error (.domain .recip) := by decide
example : eval rationalOps (fun _ => 0) zeroStrict () = .error (.domain .recip) := by decide
example : evalReady rationalOps (fun _ => none) zeroStrict () = .error (.unavailable 7) := rfl
example : evalReady rationalOps (fun _ => some 0) zeroStrict () = .error (.domain .recip) := by decide
example : evalReady rationalOps partialStore readSeven () = .ok 2 := by decide
example : Ready partialStore (readSeven : Expr ℚ UID Unit) () := by
  intro a ha
  simp only [readSeven, footprint, List.mem_singleton] at ha
  subst a
  exact ⟨2, by decide⟩
example : evalReady rationalOps partialStore readSeven () =
    evalReady rationalOps (fun a => if a = 7 then some 2 else some 999) readSeven () := by
  apply evalReady_stable
  intro a ha
  simp only [readSeven, footprint, List.mem_singleton] at ha
  subst a
  rfl
example : eval rationalOps exactStore badRecip () = .error (.domain .recip) := by decide
example : evalReady rationalOps (fun _ => none)
    (.reduce 0 (.read (fun γ => γ.1)) : Expr ℚ UID UID) 7 = .ok 0 := rfl
example : evalReady rationalOps (fun _ => none)
    (.binary .add badRecip readSeven) () = .error (.unavailable 7) := rfl
example : evalReady rationalOps (fun _ => some 0) zeroStrict () =
    eval rationalOps (fun _ => 0) zeroStrict () := by
  apply ready_consistent
  intro _ _
  rfl
example : evalReady rationalOps partialStore (.recip readSeven) () =
    eval rationalOps exactStore (.recip readSeven) () := by
  apply ready_consistent
  intro a ha
  simp only [footprint, readSeven, List.mem_singleton] at ha
  subst a
  rfl
example : footprint boundSum () = [7, 8, 9] := rfl
example : evalReady rationalOps partialStore boundSum () = .error (.unavailable 8) := rfl
example : eval rationalOps (fun _ => 0) boundSum.recip () = .error (.domain .recip) := by
  have hz : eval rationalOps (fun _ => 0) boundSum () = .ok 0 := by
    change Except.ok ((0 : ℚ) + (0 + (0 + 0))) = .ok 0
    congr 1
    norm_num
  change (eval rationalOps (fun _ => 0) boundSum () >>=
    fun x => (rationalOps.recip x).mapError Failure.domain) = _
  rw [hz]
  rfl
example : eval rationalOps (fun _ => 0)
    (.reduce 2 (.recip (.read (fun γ => γ.2.val))) : Expr ℚ UID Unit) () =
    .error (.domain .recip) := by decide

/-- Same syntax builder; inputs deliberately supplied at their native precision.
    (2^24 + 1) - 2^24 is 0 in binary32 and 1 in binary64. -/
def roundingExpr (large one negative : K) : Expr K UID Unit :=
  .binary .add (.binary .add (.lit large) (.lit one)) (.lit negative)

example : eval rationalOps exactStore (roundingExpr 16777216 1 (-16777216)) () = .ok 1 := by
  change Except.ok (((16777216 : ℚ) + 1) + (-16777216)) = .ok 1
  congr 1
  norm_num

def valueBits64 : Except (Failure UID) Float → Option UInt64
  | .ok x => some x.toBits
  | .error _ => none
def valueBits32 : Except (Failure UID) Float32 → Option UInt32
  | .ok x => some x.toBits
  | .error _ => none

def rounding64 := eval floatOps (fun _ => 0.0) (roundingExpr 16777216.0 1.0 (-16777216.0)) ()
def rounding32 := eval float32Ops (fun _ => Float32.ofBits 0)
  (roundingExpr (Float32.ofBits 0x4b800000) (Float32.ofBits 0x3f800000)
    (Float32.ofBits 0xcb800000)) ()

#guard valueBits64 rounding64 == some ((16777216.0 + 1.0 - 16777216.0 : Float).toBits)
#guard valueBits32 rounding32 == some
  (((Float32.ofBits 0x4b800000 + Float32.ofBits 0x3f800000) +
    Float32.ofBits 0xcb800000).toBits)
#guard valueBits64 rounding64 == some 0x3ff0000000000000
#guard valueBits32 rounding32 == some 0x00000000
#guard valueBits64 (eval floatOps (fun _ => 2.0) (.recip readSeven) ()) == some 0x3fe0000000000000
#guard valueBits32 (eval float32Ops (fun _ => Float32.ofBits 0x40000000)
  (.recip readSeven) ()) == some 0x3f000000
#guard match eval floatOps (fun _ => 0.0) (.recip readSeven) () with
  | .error (.domain .recip) => true | _ => false
#guard match eval float32Ops (fun _ => Float32.ofBits 0) (.recip readSeven) () with
  | .error (.domain .recip) => true | _ => false

/-! The actual signed formal stride matrix and its coordinate interpretation. -/

def signedAxis : AxisSpec := ⟨"i", 7, .nat⟩
def signedIdx : IdxExpr := .affine 3 [(-2, signedAxis)]
def signedPresentation : StMatP :=
  { domLen := 1, codLen := 1, coeffs := [(idxToRow [7] signedIdx).1]
    bias := [(idxToRow [7] signedIdx).2] }

example : signedPresentation.wellFormed = true := by decide
example : signedPresentation.coeffs = [[-2]] ∧ signedPresentation.bias = [3] := by decide

abbrev oneAxis : StObj := [{ name := some "i", size := .lit 4 }]
noncomputable def signedMatrix : StMat oneAxis oneAxis :=
  realizeStMat signedPresentation oneAxis oneAxis

noncomputable def coordinate (m : StMat dom cod) (x : Fin dom.length → Coeff) :
    Fin cod.length → Coeff :=
  fun i => (∑ j, m.coeffs i j * x j) + m.bias i

/-- Polynomial coordinates really implement the realized DSL coefficient and bias. -/
theorem signed_coordinate (x : Int) :
    coordinate signedMatrix (fun _ => intToCoeff x) 0 = intToCoeff (-2 * x + 3) := by
  simp [coordinate, signedMatrix, realizeStMat, signedPresentation, signedIdx,
    signedAxis, idxToRow, idxAffineForm, idxDensify, oneAxis, intToCoeff]

noncomputable def integerCoordinate (x : Int) : Int :=
  MvPolynomial.eval (fun _ => (0 : Int))
    (coordinate signedMatrix (fun _ => intToCoeff x) 0)

theorem integerCoordinate_eq (x : Int) : integerCoordinate x = -2 * x + 3 := by
  rw [integerCoordinate, signed_coordinate]
  exact MvPolynomial.eval_C _

def signedRead : Expr K (UID × Int) Int := .read (fun x => (7, -2 * x + 3))

/-- A read in the fragment follows an actual `realizeStMat` coordinate, not a
    separately labelled affine record. This restricted connection needs no element bounds. -/
theorem signedRead_connection (ops : Ops K) (s : UID × Int → K) (x : Int) :
    eval ops s signedRead x = .ok (s (7, integerCoordinate x)) := by
  rw [integerCoordinate_eq]
  rfl

/-- Finite lookup is available only with explicit lower and upper bound proofs. -/
def boundedSigned (x : Int) (n : Nat) (lo : 0 ≤ -2 * x + 3) (hi : -2 * x + 3 < n) :
    Fin n :=
  ⟨(-2 * x + 3).toNat, by omega⟩

example : ¬ (0 ≤ -2 * (2 : Int) + 3) := by decide
example : (boundedSigned 1 4 (by decide) (by decide)).val = 1 := rfl
example : eval rationalOps (fun a => (a.2 : ℚ)) signedRead 2 = .ok (-1) := by decide

#eval eval rationalOps exactStore boundSum ()
#eval eval rationalOps exactStore emptyBad ()
#eval eval rationalOps exactStore (.recip emptyBad) ()
#eval eval rationalOps (fun _ => 0) zeroStrict ()
#eval eval rationalOps exactStore (.recip readSeven) ()
#eval evalReady rationalOps (fun _ => none) zeroStrict ()
#eval evalReady rationalOps (fun _ => some 0) zeroStrict ()
#eval evalReady rationalOps partialStore boundSum ()
#eval eval rationalOps (fun a => (a.2 : ℚ)) signedRead 2
#eval valueBits64 rounding64
#eval valueBits32 rounding32

#print axioms evalWith_stable
#print axioms eval_stable
#print axioms ready_consistent
#print axioms evalReady_stable
#print axioms signed_coordinate
#print axioms integerCoordinate_eq
#print axioms signedRead_connection

end LeanNCD.TensorLogicSemanticCoreSpike

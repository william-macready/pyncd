import LeanNCD.Semantics
import LeanNCD.Eval.Error
import Mathlib.Analysis.Complex.Basic

namespace LeanNCD.Semantics.NativeFixtures

variable {K : Type}

@[reducible] def noTensors : Declarations Unit where
  Tensor := Empty
  uid := Empty.elim
  unique := by intro t; exact Empty.elim t
  signature := Empty.elim

def emptyStore : Store (fun _ : Unit => K) noTensors := fun a => Empty.elim a.1

@[reducible] def unaryRegistry (fn : K → Option K) : Registry (fun _ : Unit => K) where
  Op := Unit
  arity := fun _ => 1
  input := fun _ _ => .scalar ()
  output := fun _ => .scalar ()
  domain := fun _ xs => (fn (xs 0)).isSome
  meaning := fun _ xs h => (fn (xs 0)).get (by simpa using h)

def rounding (fn : K → Option K) (large one negative : K) :
    Expr (fun _ : Unit => K) noTensors (unaryRegistry fn) Unit (.scalar ()) :=
  .binary .add (.binary .add (.lit large) (.lit one)) (.lit negative)

def reciprocal (fn : K → Option K) (x : K) :
    Expr (fun _ : Unit => K) noTensors (unaryRegistry fn) Unit (.scalar ()) :=
  .prim (r := unaryRegistry fn) () (fun _ => .lit x)

def fn64 (x : Float) : Option Float := (UnaryOp.applyChecked .recip x).toOption
def fn32 (x : Float32) : Option Float32 := (UnaryOp.applyChecked32 .recip x).toOption
def ops64 : ScalarOps Float := ⟨0.0, 1.0, (· + ·), (· * ·)⟩
def ops32 : ScalarOps Float32 :=
  ⟨Float32.ofBits 0, Float32.ofBits 0x3f800000, (· + ·), (· * ·)⟩
def result64 := interpret (fun _ => ops64) emptyStore
  (rounding fn64 16777216.0 1.0 (-16777216.0)) ()
def result32 := interpret (fun _ => ops32) emptyStore
  (rounding fn32 (Float32.ofBits 0x4b800000) (Float32.ofBits 0x3f800000)
    (Float32.ofBits 0xcb800000)) ()

#guard result64.map Float.toBits == some 0x3ff0000000000000
#guard result32.map Float32.toBits == some 0x00000000
#guard (interpret (fun _ => ops64) emptyStore
  (reciprocal fn64 2.0) ()).map Float.toBits == some 0x3fe0000000000000
#guard (interpret (fun _ => ops32) emptyStore
  (reciprocal fn32 (Float32.ofBits 0x40000000)) ()).map Float32.toBits == some 0x3f000000
#guard !(interpret (fun _ => ops32) emptyStore
  (reciprocal fn32 (Float32.ofBits 0)) ()).isSome

noncomputable def complexOps : ScalarOps ℂ := ⟨0, 1, (· + ·), (· * ·)⟩
noncomputable def complexRegistry : Registry (fun _ : Unit => ℂ) :=
  unaryRegistry (fun x => some x)
noncomputable def complexSquare :
    Expr (fun _ : Unit => ℂ) noTensors complexRegistry Unit (.scalar ()) :=
  .binary .mul (.lit Complex.I) (.lit Complex.I)

theorem complex_square :
    interpret (fun _ => complexOps) emptyStore complexSquare () =
      some (-1 : ℂ) := by
  change some (Complex.I * Complex.I) = _
  rw [Complex.I_mul_I]

#print axioms complex_square
#eval (result64.map Float.toBits, result32.map Float32.toBits)

end LeanNCD.Semantics.NativeFixtures

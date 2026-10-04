-- test/DSL/ComplexElementTypeTest.lean
import LeanNCD.DSL.Compile

/-!
# Complex element types are SPELLED but REJECTED

`tensor complex64 A(i)`, `tensor complex128 A(i)` and `linear complex64 W(a, b)` parse
(`ParseProgramTest.lean`) but have no semantics: complex is a different scalar DOMAIN, not another
real precision, and the categorical branch (`compile` → `route`) erases the element type — sound
only for `f32`/`f64` (`papers/f32_evalplan.md` §1.1–§1.3). So every complex declaration, used or
not, is rejected with `CompileError.unsupportedElementType <name> <spelling>` by `buildDeclEnv`
(`rejectComplexDecls`), before any lowering.

Every program is built with `tlprog!` and compiled at RUNTIME (`.compile`/`.compileToScheduled`):
`tl!{}` would fail the build at elaboration. Each rejected program has an accept-neighbour that
differs only in the element-type word.
-/

namespace LeanNCD.ComplexElementTypeTest

private def compileErr (p : TLProgram) : Option CompileError :=
  match p.compile.run 0 with
  | .error e _ => some e
  | .ok _ _    => none

private def scheduleErr (p : TLProgram) : Option CompileError :=
  match p.compileToScheduled.run 0 with
  | .error e _ => some e
  | .ok _ _    => none

/-- Both source entries reject with exactly `e`. -/
private def bothReject (p : TLProgram) (e : CompileError) : Bool :=
  compileErr p == some e && scheduleErr p == some e

/-- Both source entries accept. -/
private def bothAccept (p : TLProgram) : Bool :=
  compileErr p == none && scheduleErr p == none

/-! ## `tensor complex64`, and its real neighbours -/

private def c64Tensor : TLProgram := tlprog!{
  tensor complex64 A(i)
  Y[i] := A[i]
}
private def f32Tensor : TLProgram := tlprog!{
  tensor f32 A(i)
  Y[i] := A[i]
}
private def f64Tensor : TLProgram := tlprog!{
  tensor f64 A(i)
  Y[i] := A[i]
}
private def plainTensor : TLProgram := tlprog!{
  tensor A(i)
  Y[i] := A[i]
}

#guard bothReject c64Tensor (.unsupportedElementType "A" "complex64")
#guard bothAccept f32Tensor
#guard bothAccept f64Tensor
#guard bothAccept plainTensor

/-! ## `tensor complex128`, grouped: the FIRST complex declaration is named -/

private def c128Group : TLProgram := tlprog!{
  tensor complex128 A(i), B(j)
  Y[i] := A[i]
}
private def f64Group : TLProgram := tlprog!{
  tensor f64 A(i), B(j)
  Y[i] := A[i]
}

#guard bothReject c128Group (.unsupportedElementType "A" "complex128")
#guard bothAccept f64Group

/-! ## `linear complex64` -/

private def c64Linear : TLProgram := tlprog!{
  linear complex64 W(a, b) bias
  Y[a] := W[a, b] · X[b]
}
private def f32Linear : TLProgram := tlprog!{
  linear f32 W(a, b) bias
  Y[a] := W[a, b] · X[b]
}
private def plainLinear : TLProgram := tlprog!{
  linear W(a, b) bias
  Y[a] := W[a, b] · X[b]
}

#guard bothReject c64Linear (.unsupportedElementType "W" "complex64")
#guard bothAccept f32Linear
#guard bothAccept plainLinear

/-! ## An UNUSED complex declaration is still rejected

Unlike an unused `tensor f32 Unused(i)`, which constrains nothing and is accepted, a complex
declaration has no reading at all, so it is refused even when no statement mentions it. -/

private def c128Unused : TLProgram := tlprog!{
  tensor complex128 Unused(i)
  Y[i] := X[i]
}
private def f32Unused : TLProgram := tlprog!{
  tensor f32 Unused(i)
  Y[i] := X[i]
}

#guard bothReject c128Unused (.unsupportedElementType "Unused" "complex128")
#guard bothAccept f32Unused

/-! ## Complex mixed with a real precision reports the COMPLEX rejection

`rejectComplexDecls` runs first inside `buildDeclEnv`, so complex wins over everything that
follows it — on the source path there is no mixed-precision rejection at all (the f32 + undeclared
f64 neighbour below compiles), and on the checked backend the f32/f64 mix is `prepareEvalPlan`'s
later Step 0b. The complex declaration is placed SECOND to show order in `decls` does not let the
real one win. -/

private def c64MixF32 : TLProgram := tlprog!{
  tensor f32 A(i)
  tensor complex64 B(i)
  Y[i] := A[i] · B[i]
}
private def c128MixF64 : TLProgram := tlprog!{
  tensor f64 A(i)
  tensor complex128 B(i)
  Y[i] := A[i] · B[i]
}
private def f32MixF64 : TLProgram := tlprog!{
  tensor f32 A(i)
  tensor f64 B(i)
  Y[i] := A[i] · B[i]
}

#guard bothReject c64MixF32 (.unsupportedElementType "B" "complex64")
#guard bothReject c128MixF64 (.unsupportedElementType "B" "complex128")
#guard bothAccept f32MixF64

/-! ## Complex wins over a duplicate declaration of the same name

`buildDeclEnv`'s two rejections are ordered complex-first; a schedule violating both reports the
complex one. -/

private def c64Dup : TLProgram := tlprog!{
  tensor A(i)
  tensor complex64 A(i)
  Y[i] := A[i]
}
#guard bothReject c64Dup (.unsupportedElementType "A" "complex64")

end LeanNCD.ComplexElementTypeTest

/-
Axis B / Task B2 construction spikes, part 3 — is a zero-extent scatter output reachable from
SURFACE syntax, not just from a programmatic `Stmt`? FINDINGS-ONLY. Not in lakefile.toml, not in
any default target.
Run with:  lake env lean spikes/AxisBSurfaceZeroExtentProbe.lean

Probe S26. `DSL/Elab.lean`'s `elabTLLHSSlot` builds every affine LHS coefficient and offset as
`Int.ofNat n.getNat` from a `num` literal, so no NEGATIVE affine form (the four B1's S15 measured
as `some 0`) is surface-reachable. A ZERO coefficient is a different matter: `0 * i` is a `num`
times an `ident`, and `LHSSlot.outExtent`'s `.scale` arm then yields `(0 * size).toNat = 0`.

This file imports the `LeanNCD` umbrella (needed for `tlprog!{ … }`) and therefore uses NO
`{ coeffs := …, bias := … }` record literal — `DSL/Syntax.lean` declares `"bias"` as a token.
-/
import LeanNCD

namespace LeanNCD.AxisBProbe5
open LeanNCD LeanNCD.Eval Std

def envX4 : Std.HashMap String DenseTensor :=
  ({} : Std.HashMap String DenseTensor).insert "X" { shape := [4], data := #[1.0, 2.0, 3.0, 4.0] }

/-! ## S26 — `Out[0*i] := X[i]` from real surface syntax -/

def progZeroScale : TLProgram := tlprog!{
  tensor X(i)
  tensor Out(i)
  axis i : ℕ = 4
  Out[0*i] := X[i]
}

def progZeroAffine : TLProgram := tlprog!{
  tensor X(i)
  tensor Out(i)
  axis i : ℕ = 4
  Out[0*i + 0] := X[i]
}

-- CONTROL: the upsample the feature is actually for.
def progStride2 : TLProgram := tlprog!{
  tensor X(i)
  tensor Out(i)
  axis i : ℕ = 4
  Out[2*i] := X[i]
}

def probeProg (label : String) (p : TLProgram) : String :=
  match TLProgram.eval p envX4 with
  | .error f => s!"{label}: eval FAILED: {toString f.error}"
  | .ok rep => match rep.env["Out"]? with
    | none => s!"{label}: eval .ok but no Out"
    | some t => s!"{label}: eval .ok; Out shape = {repr t.shape}, data = {repr t.data}"

#eval probeProg "S26a (Out[0*i] := X[i])" progZeroScale
#eval probeProg "S26b (Out[0*i + 0] := X[i])" progZeroAffine
#eval probeProg "S26c (Out[2*i] := X[i] — CONTROL)" progStride2

-- The slot lists those programs elaborate to.
#eval progZeroScale.stmts.map (fun s => match s with
  | .assign _ sl _ => sl | .scatter _ sl _ _ => sl | .recurMorphism .. => [])

#eval progStride2.stmts.map (fun s => match s with
  | .assign _ sl _ => sl | .scatter _ sl _ _ => sl | .recurMorphism .. => [])

-- Does the zero-extent output get REJECTED once something reads it? (S24's question, at the
-- surface.) `Y[k] := Out[k]` forces the sizing fixpoint to size `k` from the published shape.
def progZeroRead : TLProgram := tlprog!{
  tensor X(i)
  tensor Out(i)
  tensor Y(k)
  axis i : ℕ = 4
  Out[0*i] := X[i]
  Y[k] := Out[k]
}

def progStrideRead : TLProgram := tlprog!{
  tensor X(i)
  tensor Out(i)
  tensor Y(k)
  axis i : ℕ = 4
  Out[2*i] := X[i]
  Y[k] := Out[k]
}

def probeRead (label : String) (p : TLProgram) : String :=
  match TLProgram.eval p envX4 with
  | .error f => s!"{label}: eval FAILED: {toString f.error}"
  | .ok rep =>
      let o := (rep.env["Out"]?).map (·.shape)
      let y := (rep.env["Y"]?).map (·.shape)
      s!"{label}: eval .ok; Out = {repr o}, Y = {repr y}"

#eval probeRead "S26d (Out[0*i], then Y[k] := Out[k])" progZeroRead
#eval probeRead "S26e (Out[2*i], then Y[k] := Out[k] — CONTROL)" progStrideRead

end LeanNCD.AxisBProbe5

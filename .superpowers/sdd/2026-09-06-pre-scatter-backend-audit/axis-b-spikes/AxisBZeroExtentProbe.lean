/-
Axis B / Task B2 construction spikes, part 2 — B1-F9's declined question: is a ZERO-EXTENT scatter
output rejected further down the scatter path? FINDINGS-ONLY. Not in lakefile.toml, not in any
default target.
Run with:  lake env lean spikes/AxisBZeroExtentProbe.lean

Probes S23-S25. B1's S15 measured `LHSSlot.outExtent` returning `some 0` for four distinct
negative affine forms; it deliberately did not chase what the two CALLERS then do with it. Both
callers are exercised here, plus the sizing fixpoint that consumes the second one's output.
-/
import LeanNCD.Eval.Eval
import LeanNCD.Eval.SizeInfer

namespace LeanNCD.Eval.AxisBProbe4
open LeanNCD.Eval
open Std

def axI : AxisSpec := { name := "i", uid := 1, kind := .nat }
def axK : AxisSpec := { name := "k", uid := 2, kind := .nat }

def envX : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" { shape := [4], data := #[1.0, 2.0, 3.0, 4.0] }

def sizesI : HashMap UID Nat := ({} : HashMap UID Nat).insert 1 4

def readX : RHSExpr :=
  { body := { terms := [{ factors := [.read "X" [.axis axI]] }] }, nonlin := .identity }

def declsX : List Decl := [.tensor "X" [axI], .tensor "Out" [axI]]

-- Four scatter statements, one per negative affine form B1's S15 measured as `some 0`,
-- plus one positive control (`.scale 2 i`, extent 8).
def scNegShift : Stmt := .scatter "Out" [.affine (.shift axI (-9))] readX {}
def scNegScale : Stmt := .scatter "Out" [.affine (.scale (-2) axI)] readX {}
def scNegAff   : Stmt := .scatter "Out" [.affine (.affine (-100) [(1, axI)])] readX {}
def scIterNeg  : Stmt := .scatter "Out" [.iterAt axI (-5)] readX {}
def scControl  : Stmt := .scatter "Out" [.affine (.scale 2 axI)] readX {}

/-! ## S23 — caller 1: `Eval.scatterOutShape` -> `Eval.evalScatter`, via `Eval.evalPlain`

`scatterOutShape` fails loud ONLY on `none` (its own comment: "An unsized axis means it is unbound
by any read (an upstream sizing gap), so FAIL LOUD rather than defaulting its size to 0"). A
`some 0` is not that case and flows straight through as a shape dimension. -/

#eval ( scatterOutShape sizesI [.affine (.shift axI (-9))]
      , scatterOutShape sizesI [.affine (.scale (-2) axI)]
      , scatterOutShape sizesI [.affine (.affine (-100) [(1, axI)])]
      , scatterOutShape sizesI [.iterAt axI (-5)]
      , scatterOutShape sizesI [.affine (.scale 2 axI)] )

-- Contrast: an UNSIZED axis in the same position IS rejected (`unsizedScatterOutput`).
#eval scatterOutShape sizesI [.free axK]

def probePlain (label : String) (s : Stmt) : String :=
  match evalPlain declsX envX sizesI s with
  | .error e => s!"{label}: evalPlain ERROR: {toString e}"
  | .ok (nm, t) => s!"{label}: evalPlain .ok; {nm} shape = {repr t.shape}, data = {repr t.data}"

#eval probePlain "S23a (Out[i - 9], extent 0)" scNegShift
#eval probePlain "S23b (Out[-2*i], extent 0)" scNegScale
#eval probePlain "S23c (Out[-100 + i], extent 0)" scNegAff
#eval probePlain "S23d (Out[iterAt i (-5)], extent 0)" scIterNeg
#eval probePlain "S23e (Out[2*i], extent 8 — CONTROL)" scControl

-- Direct `evalScatter` call at `outShape = [0]`, isolating the write loop's bounds guard
-- (`if (outCoordZ.zip outShape).all (fun (z, d) => 0 ≤ z && z < (d : Int))`): with `d = 0` the
-- guard is false at EVERY source coordinate, so every write is skipped — the same
-- "out-of-range output coordinates are skipped" rule that exists for genuine overspill.
#eval match evalScatter envX sizesI "Out" [.affine (.shift axI (-9))] readX {} [0] with
  | .error e => s!"S23f (evalScatter at outShape [0]): ERROR: {toString e}"
  | .ok (nm, t) => s!"S23f (evalScatter at outShape [0]): .ok; {nm} = {repr t.shape}/{repr t.data}"

-- The collision policy cannot fire either: `.rejectCollisions` is only reached INSIDE the bounds
-- guard, so four source coordinates all landing "on" a zero-extent output collide with nothing.
#eval match evalScatter envX sizesI "Out" [.affine (.shift axI (-9))] readX
        { fill := 0, reduce := .rejectCollisions } [0] with
  | .error e => s!"S23g (zero extent + rejectCollisions): ERROR: {toString e}"
  | .ok (nm, t) => s!"S23g (zero extent + rejectCollisions): .ok; {nm} = {repr t.shape}"

/-! ## S24 — caller 2: `SizeInfer.scatterOutputShapes`, and the fixpoint that consumes it

`scatterOutputShapes` inserts `some dims` and drops only `none`, so a zero dimension is published
as a downstream-readable shape. The fixpoint then builds read positions against it. -/

#eval ( (scatterOutputShapes sizesI [scNegShift])["Out"]?
      , (scatterOutputShapes sizesI [scControl])["Out"]?
      , (scatterOutputShapes sizesI [.scatter "Out" [.free axK] readX {}])["Out"]? )

-- A downstream read of the zero-extent scatter output: `Y[k] := Out[k]`, with `k` unsized, so
-- the ONLY thing that can size `k` is the published scatter-out shape.
def downstream : Stmt :=
  .assign "Y" [.free axK]
    { body := { terms := [{ factors := [.read "Out" [.axis axK]] }] }, nonlin := .identity }

def probeInfer (label : String) (stmts : List Stmt) : String :=
  match inferAxisSizes ({} : HashMap UID Nat) envX stmts with
  | .error f => s!"{label}: inferAxisSizes ERROR: {toString f.error}"
  | .ok (sz, ws) =>
      s!"{label}: .ok; i = {repr sz[(1 : UID)]?}, k = {repr sz[(2 : UID)]?}, warnings = {ws.length}"

#eval probeInfer "S24a (zero-extent scatter out, read downstream)" [scNegShift, downstream]
#eval probeInfer "S24b (extent-8 scatter out, read downstream — CONTROL)" [scControl, downstream]

-- And what the whole two-statement program then evaluates to.
def probeChain (label : String) (sc : Stmt) : String :=
  match inferAxisSizes ({} : HashMap UID Nat) envX [sc, downstream] with
  | .error f => s!"{label}: inferAxisSizes ERROR: {toString f.error}"
  | .ok (sz, _) => match evalPlain declsX envX sz sc with
    | .error e => s!"{label}: scatter ERROR: {toString e}"
    | .ok (nm, t) =>
        let env2 := envX.insert nm t
        match evalPlain [.tensor "Out" [axK], .tensor "Y" [axK]] env2 sz downstream with
        | .error e => s!"{label}: downstream ERROR: {toString e}"
        | .ok (nm2, t2) => s!"{label}: .ok; {nm} = {repr t.shape}, {nm2} = {repr t2.shape}/{repr t2.data}"

#eval probeChain "S24c (zero-extent scatter, then read it)" scNegShift
#eval probeChain "S24d (extent-8 scatter, then read it — CONTROL)" scControl

/-! ## S25 — is a zero extent rejected anywhere ELSE on the scatter path?

`ScatterOpts.fill` and `rhs.nonlin` are the only other gates in `evalScatter`, and both run BEFORE
`outShape` is looked at; `scatterSourceAxes`/`srcSizes` fail loud on an unsized SOURCE axis only.
Measured: the non-identity-nonlin gate still fires at a zero extent (so the ordering is
nonlin-before-shape), and an unsized SOURCE axis still fails loud at a zero extent. -/

#eval match evalScatter envX sizesI "Out" [.affine (.shift axI (-9))]
        { readX with nonlin := .pointwise .relu } {} [0] with
  | .error e => s!"S25a (zero extent + relu): ERROR: {toString e}"
  | .ok (nm, t) => s!"S25a (zero extent + relu): .ok; {nm} = {repr t.shape}"

#eval match evalScatter envX ({} : HashMap UID Nat) "Out" [.affine (.shift axI (-9))] readX {} [0] with
  | .error e => s!"S25b (zero extent + UNSIZED source axis): ERROR: {toString e}"
  | .ok (nm, t) => s!"S25b (zero extent + UNSIZED source axis): .ok; {nm} = {repr t.shape}"

end LeanNCD.Eval.AxisBProbe4

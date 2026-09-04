import LeanNCD.DSL.Ast
import LeanNCD.Eval.Entry
import Eval.PropertyOracle.Compare

/-!
# Curated scan-template generator (E6 scan-unrolling oracle, Task 1/2)

`enumScanCases` is a small, curated (not combinatorial) family of six scan templates, each
authored directly as `Stmt`/`Decl` values (same convention as `test/Eval/ScanTest.lean`), varied
over a few parameters (scan length `L`, coefficient signs, aggregator). Scan well-formedness is
materially tighter than the scan-free fragment (causality, matching base/recur names, full-axis-
set coupling), so a curated family is lower-risk than combinatorial enumeration here.

NO SLOT-ORDER INVARIANT. Every generated statement here happens to put its scan-axis LHS slots
last, but nothing may depend on that. This file used to declare it as an invariant "load-bearing
for `ScanUnroll`'s slicing"; F4 Task 5 deleted that slicing and rewrote the oracle to resolve each
state's advancing dimensions from its own recurrence result, precisely so a non-trailing advancing
dimension is handled rather than assumed away (it was one of the four deficiencies plan §4.8
names). A new template with an interior or leading scan-axis slot is therefore welcome, and is
covered by `test/Eval/Plan/ScanCompileTest.lean`'s fixture H on the hand-written side.
-/
namespace LeanNCD.PropertyOracle
open LeanNCD LeanNCD.Eval

/-- One curated scan test case: the full program + its deterministic inputs, plus the scan's
    own structure (axes, per-axis lengths, base/recur statements) as authored — since this
    generator builds `Stmt` values directly, it already knows this grouping and doesn't need to
    re-derive it the way `finalizeScans` does at compile time. -/
structure ScanCase where
  prog   : TLProgram
  inputs : Std.HashMap String DenseTensor
  axes   : List AxisSpec
  Ls     : List Nat
  base   : List Stmt
  recur  : List Stmt

-- ===== Template 1: linear self-scan  S[j,l+1] := S[j,l]·A[j] =====
private def j1 : AxisSpec := ⟨"j", 201, .real⟩
private def l1 : AxisSpec := ⟨"l", 202, .nat⟩

/-- Public (unlike templates 2/4/5) because `ScanUnroll`/`ScanOracle` need a concrete, named
    single-state case: it is the point check for `independentRun`'s hand-derived history and the
    subject of `ScanOracle.lean`'s two teeth checks. -/
def template1 (L : Nat) (Aneg : Bool) : ScanCase :=
  let l := l1
  let base : Stmt := .assign "S" [.free j1, .iterAt l 0]
    { body := { terms := [{ factors := [.read "X0" [.axis j1]] }] }, nonlin := .identity }
  let recur : Stmt := .assign "S" [.free j1, .iterNext l]
    { body := { terms := [{ factors := [.read "S" [.axis j1, .axis l], .read "A" [.axis j1]] }] },
      nonlin := .identity }
  let aVals : Array Float := if Aneg then #[-2.0, 3.0] else #[2.0, 3.0]
  let inputs : Std.HashMap String DenseTensor :=
    (({} : Std.HashMap String DenseTensor).insert "X0" ⟨[2], #[1.0, 2.0]⟩).insert "A" ⟨[2], aVals⟩
  { prog := { decls := [.axis j1 (some 2), .axis l (some L), .tensor "X0" [j1], .tensor "A" [j1]],
              stmts := [base, recur] },
    inputs := inputs, axes := [l], Ls := [L], base := [base], recur := [recur] }

-- ===== Template 2: nonlin self-scan  S[j,l+1] := relu(S[j,l]·A[j]) =====
private def j2 : AxisSpec := ⟨"j", 211, .real⟩
private def l2 : AxisSpec := ⟨"l", 212, .nat⟩

private def template2 (L : Nat) (Aneg : Bool) : ScanCase :=
  let l := l2
  let base : Stmt := .assign "S" [.free j2, .iterAt l 0]
    { body := { terms := [{ factors := [.read "X0" [.axis j2]] }] }, nonlin := .identity }
  let recur : Stmt := .assign "S" [.free j2, .iterNext l]
    { body := { terms := [{ factors := [.read "S" [.axis j2, .axis l], .read "A" [.axis j2]] }] },
      nonlin := .pointwise .relu }
  let aVals : Array Float := if Aneg then #[-1.0, -1.0] else #[1.0, 2.0]
  let inputs : Std.HashMap String DenseTensor :=
    (({} : Std.HashMap String DenseTensor).insert "X0" ⟨[2], #[1.0, 1.0]⟩).insert "A" ⟨[2], aVals⟩
  { prog := { decls := [.axis j2 (some 2), .axis l (some L), .tensor "X0" [j2], .tensor "A" [j2]],
              stmts := [base, recur] },
    inputs := inputs, axes := [l], Ls := [L], base := [base], recur := [recur] }

-- ===== Template 3: coupled 2-state  G[l+1]:=G[l]+H[l]; H[l+1]:=G[l] =====
private def l3 : AxisSpec := ⟨"l", 222, .nat⟩

/-- Public (unlike templates 2/4/5) because `ScanUnroll`'s Task 5 point-check needs a concrete,
    named COUPLED case: it is the only template whose two states must both be reconstructed from
    one step iteration's shared pre-step snapshot. -/
def template3 (L : Nat) : ScanCase :=
  let l := l3
  let baseG : Stmt := .assign "G" [.iterAt l 0]
    { body := { terms := [{ factors := [.read "C" []] }] }, nonlin := .identity }
  let baseH : Stmt := .assign "H" [.iterAt l 0]
    { body := { terms := [{ factors := [.read "C" []] }] }, nonlin := .identity }
  let recurG : Stmt := .assign "G" [.iterNext l]
    { body := { terms := [{ factors := [.read "G" [.axis l]] }, { factors := [.read "H" [.axis l]] }] },
      nonlin := .identity }
  let recurH : Stmt := .assign "H" [.iterNext l]
    { body := { terms := [{ factors := [.read "G" [.axis l]] }] }, nonlin := .identity }
  let inputs : Std.HashMap String DenseTensor := (({} : Std.HashMap String DenseTensor).insert "C" ⟨[], #[1.0]⟩)
  { prog := { decls := [.axis l (some L), .tensor "C" []],
              stmts := [baseG, baseH, recurG, recurH] },
    inputs := inputs, axes := [l], Ls := [L], base := [baseG, baseH], recur := [recurG, recurH] }

/-- Templates 1–3 only; Task 2 extends this into the full six-template `enumScanCases`. -/
def partialScanCases : List ScanCase :=
  ([2, 3].flatMap (fun L => [true, false].map (fun neg => template1 L neg))) ++
  ([2, 3].flatMap (fun L => [true, false].map (fun neg => template2 L neg))) ++
  ([2, 3].map template3)

-- ===== Template 4: state + external read  S[l+1] := S[l] + X[l] =====
private def l4 : AxisSpec := ⟨"l", 232, .nat⟩

private def template4 (L : Nat) : ScanCase :=
  let l := l4
  let base : Stmt := .assign "S" [.iterAt l 0]
    { body := { terms := [{ factors := [.read "C0" []] }] }, nonlin := .identity }
  let recur : Stmt := .assign "S" [.iterNext l]
    { body := { terms := [{ factors := [.read "S" [.axis l]] }, { factors := [.read "X" [.axis l]] }] },
      nonlin := .identity }
  let xData : Array Float := ((List.range L).map (fun i => Float.ofNat i + 1.0)).toArray
  let inputs : Std.HashMap String DenseTensor :=
    (({} : Std.HashMap String DenseTensor).insert "C0" ⟨[], #[1.0]⟩).insert "X" ⟨[L], xData⟩
  { prog := { decls := [.axis l (some L), .tensor "C0" [], .tensor "X" [l]],
              stmts := [base, recur] },
    inputs := inputs, axes := [l], Ls := [L], base := [base], recur := [recur] }

/-- Task 4.4, fixture 1: a `predicate S(l)` clone of `template4`, kept HERE (rather than in
    `DifferentialTest.lean`) precisely because `template4` above is `private` — this file is the
    only place that can build the clone by copying its statements directly. Same base/recurrence
    shape (`S[l+1] := S[l] + X[l]`, two summed terms), with every `X` element `1.0` (`template4`'s
    original `X` counts up `1,2,3,…`, which would make a Boolean history saturate to `1.0` after
    step 0 for an uninteresting reason — every element here is already `1.0`, so a REAL sum would
    strictly grow past `1.0` starting at step 1 while the Boolean disjunction this predicate
    declaration selects stays exactly `1.0` throughout: the two algebras are DISTINGUISHABLE on this
    input, not merely both `≥ 1`). `C0 = 1.0` seeds `S[0] = 1.0`. Public (unlike `template4`) so
    `ScanUnroll.lean`'s Task 4.4 fixture 8 and `DifferentialTest.lean`'s three-way registration can
    both reference it. -/
def template4Bool (L : Nat) : ScanCase :=
  let l := l4
  let base : Stmt := .assign "S" [.iterAt l 0]
    { body := { terms := [{ factors := [.read "C0" []] }] }, nonlin := .identity }
  let recur : Stmt := .assign "S" [.iterNext l]
    { body := { terms := [{ factors := [.read "S" [.axis l]] }, { factors := [.read "X" [.axis l]] }] },
      nonlin := .identity }
  let xData : Array Float := Array.replicate L 1.0
  let inputs : Std.HashMap String DenseTensor :=
    (({} : Std.HashMap String DenseTensor).insert "C0" ⟨[], #[1.0]⟩).insert "X" ⟨[L], xData⟩
  { prog := { decls := [.axis l (some L), .tensor "C0" [], .tensor "X" [l], .predicate "S" [l]],
              stmts := [base, recur] },
    inputs := inputs, axes := [l], Ls := [L], base := [base], recur := [recur] }

-- REGRESSION GUARD: `template4Bool`'s history must be all `1.0` — Boolean disjunction of
-- already-`1.0` values, not a real running sum (which would read `[1, 2, 3]` for `L = 3`).
run_cmd do
  match TLProgram.eval (template4Bool 3).prog (template4Bool 3).inputs with
  | .error e => throwError (toString e)
  | .ok report => match report.env["S"]? with
    | some s => unless denseEq s ⟨[3], #[1.0, 1.0, 1.0]⟩ do
        throwError s!"template4Bool wrong: {repr s.data}"
    | none => throwError "template4Bool: no S in output"

-- ===== Template 5: tropical aggregator  M[j,l+1] := maxreduce/minreduce(M[j,l]·W[j,k]) =====
private def j5 : AxisSpec := ⟨"j", 241, .real⟩
private def k5 : AxisSpec := ⟨"k", 242, .real⟩
private def l5 : AxisSpec := ⟨"l", 243, .nat⟩

private def template5 (L : Nat) (useMax : Bool) : ScanCase :=
  let l := l5
  let base : Stmt := .assign "M" [.free j5, .iterAt l 0]
    { body := { terms := [{ factors := [.read "X0" [.axis j5]] }] }, nonlin := .identity }
  let recur : Stmt := .assign "M" [.free j5, .iterNext l]
    { body := { terms := [{ factors := [.read "M" [.axis j5, .axis l], .read "W" [.axis j5, .axis k5]] }] },
      nonlin := .identity, agg := if useMax then .max else .min }
  let inputs : Std.HashMap String DenseTensor :=
    (({} : Std.HashMap String DenseTensor).insert "X0" ⟨[1], #[2.0]⟩).insert "W" ⟨[1,2], #[1.0, 3.0]⟩
  { prog := { decls := [.axis j5 (some 1), .axis k5 (some 2), .axis l (some L),
                        .tensor "X0" [j5], .tensor "W" [j5, k5]],
              stmts := [base, recur] },
    inputs := inputs, axes := [l], Ls := [L], base := [base], recur := [recur] }

-- ===== Template 6: 2-D grid-DP  G[r,0]:=Z[r]; G[r+1,c+1]:=G[r,c]+A[r,c] =====
private def r6 : AxisSpec := ⟨"r", 251, .nat⟩
private def c6 : AxisSpec := ⟨"c", 252, .nat⟩

/-- Public (unlike templates 2/4/5) because `ScanUnroll`'s point check needs a concrete, named
    TWO-AXIS case: it is the only template whose grid has coordinates that neither the base face nor
    any step reaches, so it is what pins the zero-leaf path. -/
def template6 : ScanCase :=
  let base : Stmt := .assign "G" [.free r6, .iterAt c6 0]
    { body := { terms := [{ factors := [.read "Z" [.axis r6]] }] }, nonlin := .identity }
  let recur : Stmt := .assign "G" [.iterNext r6, .iterNext c6]
    { body := { terms := [{ factors := [.read "G" [.axis r6, .axis c6]] },
                           { factors := [.read "A" [.axis r6, .axis c6]] }] },
      nonlin := .identity }
  let inputs : Std.HashMap String DenseTensor :=
    (({} : Std.HashMap String DenseTensor).insert "Z" ⟨[2], #[0.0, 0.0]⟩).insert "A" ⟨[2,2], #[1.0,1.0,1.0,1.0]⟩
  { prog := { decls := [.axis r6 (some 2), .axis c6 (some 2), .tensor "Z" [r6], .tensor "A" [r6, c6]],
              stmts := [base, recur] },
    inputs := inputs, axes := [r6, c6], Ls := [2, 2], base := [base], recur := [recur] }

-- REGRESSION GUARD (found while hand-deriving the 2-D unroll): template6 must match
-- RC6's own hand-verified result (RecurrenceTest.lean) — an earlier draft had `G[r,c]` and
-- `A[r,c]` crammed into one product term (multiplication) instead of two summed terms
-- (addition), and Task 2's contract tests only checked well-formedness (`.isSome`), never the
-- actual value, so it slipped through. Row-major [r][c]: G = [[0,0],[0,1]].
run_cmd do
  match TLProgram.eval template6.prog template6.inputs with
  | .error e => throwError (toString e)
  | .ok report => match report.env["G"]? with
    | some g => unless denseEq g ⟨[2, 2], #[0.0, 0.0, 0.0, 1.0]⟩ do
        throwError s!"template6 wrong: {repr g.data}"
    | none => throwError "template6: no G in output"

/-- The full curated six-template scan generator. -/
def enumScanCases : List ScanCase :=
  partialScanCases ++
  ([2, 3].map template4) ++
  ([2, 3].flatMap (fun L => [true, false].map (fun m => template5 L m))) ++
  [template6]

-- CONTRACT TESTS (fire on build):
#guard enumScanCases.length == 17   -- 10 (templates 1-3) + 2 (t4) + 4 (t5) + 1 (t6)
#guard enumScanCases.all (fun c => (TLProgram.eval c.prog c.inputs).toOption.isSome)
-- coverage: the 2-D template is present
#guard enumScanCases.any (fun c => c.axes.length == 2)
-- coverage: the coupled 2-state template is present (more than one base stmt)
#guard enumScanCases.any (fun c => c.base.length > 1)
-- coverage: the tropical-aggregator template is present
#guard enumScanCases.any (fun c => c.recur.any (fun s => match s with
  | .assign _ _ rhs => rhs.agg == .max || rhs.agg == .min
  | _ => false))

end LeanNCD.PropertyOracle

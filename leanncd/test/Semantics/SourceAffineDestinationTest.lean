import Semantics.SourceCorrespondenceFixtures

/-!
S2a P1: a hand-built non-bare destination. Admission still produces only bare outputs, so the
affine output is built here by retargeting an admitted bare output `T[x] = X[x]` onto a wider
tensor `S` (extent 8) through an explicit destination index map. The core theorems
(`Term.fiber_partition`, `Term.collectedBody_correspondence`, `AdmittedStatement.fiber_partition`)
are stated for any `dest`; these guards check the computed fibers: a spread write `S[2*x]`
leaves odd fibers empty (0), and a collapsing write `S[x/2]` sums colliding coordinates (⊕).
-/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceAdmissionFixtures SourceProgramFixtures SourceCorrespondenceFixtures

namespace SourceAffineDestinationTest

def x : AxisSpec := ⟨"x", 21, .nat⟩
def w : AxisSpec := ⟨"w", 22, .nat⟩

def affineSnapshot : SourceSnapshot :=
  ⟨⟨[.axis x (some 4), .axis w (some 8), .tensor "X" [x], .tensor "T" [x], .tensor "S" [w]],
    [.assign "T" [.free x] (rhs [[.read "X" [.axis x]]]),
     .assign "S" [.free w] (rhs [])], {}, ∅⟩,
    [⟨2, .input, [4]⟩, ⟨3, .output, [4]⟩, ⟨4, .output, [8]⟩],
    [⟨2, [4], [1, 2, 3, 4]⟩]⟩

/-- Same virtual write coordinates, another destination tensor and index map. -/
def retarget (o : AdmittedOutput source σ) (t : σ.Tensor)
    (dest : Coord o.shape → Coord (σ.signature t).axes) : AdmittedOutput source σ :=
  { o with tensor := t, dest := dest }

def coordOfList : (sh : Shape) → List Nat → Option (Coord sh)
  | [], _ => some ()
  | a :: sh, n :: ns =>
    if h : n < a.extent then (fun p => ((⟨n, h⟩ : Fin a.extent), p)) <$> coordOfList sh ns
    else none
  | _ :: _, [] => none

/-- A coordinatewise integer index map. An out-of-range image would fall back to `d`; the
fixtures below never produce one (checked by `images`), which is the static refusal P2 owes. -/
def indexMap (g : Nat → Nat) (src dst : Shape) (d : Coord dst) (c : Coord src) : Coord dst :=
  (coordOfList dst ((coordList src c).map g)).getD d

structure AffineRow where
  images : List (Option (List Nat))
  termGlobal : List ℚ
  termCollected : List (Option ℚ)
  statementGlobal : List ℚ
  deriving DecidableEq, Repr

def affineRow (g : Nat → Nat) : Option AffineRow := do
  let source ← (admitSource affineSnapshot).toOption
  let statement ← source.statements.head?
  let term ← statement.terms.head?
  let S ← source.source.table.find "S"
  let σ := source.source.table.declarations
  let sh := (σ.signature S).axes
  let d ← coordOfList sh [0]
  let out := retarget statement.output S (indexMap g statement.output.shape sh d)
  let layout := canonicalLayout sh
  let srcLayout := canonicalLayout statement.output.context.axes
  let ps := List.finRange layout.count
  -- Statement level: the affine output in an `AdmittedStatement` (S is not an input).
  let statementGlobal ← if hw : (source.source.table.entry out.tensor).role ≠ .input then
      let affine : AdmittedStatement source.source :=
        { statement with output := out, writable := hw }
      some (ps.map fun n => affine.globalFiber (ratStore source) (layout.enumerate n))
    else none
  pure ⟨(List.finRange srcLayout.count).map (fun n =>
      coordOfList sh ((coordList _ (statement.output.slots.project (srcLayout.enumerate n))).map g)
        |>.map (coordList sh)),
    ps.map (fun n => term.globalFiber out (ratStore source) (layout.enumerate n)),
    ps.map (fun n => term.collectedBody (r := RationalReference.registry) out (ratStore source)
      (layout.enumerate n)),
    statementGlobal⟩

-- Spread write `S[2*x]`: images 0,2,4,6; odd destination fibers are empty and read 0.
#guard affineRow (2 * ·) = some ⟨[some [0], some [2], some [4], some [6]],
  [1, 0, 2, 0, 3, 0, 4, 0],
  [some 1, some 0, some 2, some 0, some 3, some 0, some 4, some 0],
  [1, 0, 2, 0, 3, 0, 4, 0]⟩

-- Collapsing write `S[x/2]`: coordinates 0,1 collide at 0 and 2,3 at 1; fibers sum.
#guard affineRow (· / 2) = some ⟨[some [0], some [0], some [1], some [1]],
  [1 + 2, 3 + 4, 0, 0, 0, 0, 0, 0],
  [some 3, some 7, some 0, some 0, some 0, some 0, some 0, some 0],
  [3, 7, 0, 0, 0, 0, 0, 0]⟩

/-- Bare baseline: the admitted `T[x] = X[x]` is unchanged by the generalisation. -/
def bareRow : Option (List ℚ × Bool) := do
  let source ← (admitSource affineSnapshot).toOption
  let statement ← source.statements.head?
  let term ← statement.terms.head?
  let layout := canonicalLayout
    (source.source.table.declarations.signature statement.output.tensor).axes
  pure ((List.finRange layout.count).map fun n =>
      term.globalFiber statement.output (ratStore source) (layout.enumerate n),
    decide (statement.output.shape =
      (source.source.table.declarations.signature statement.output.tensor).axes))

#guard bareRow = some ([1, 2, 3, 4], true)

/-- The generic correspondence applies to the affine output with no bare hypothesis. -/
example (source : AdmittedSource) (statement : AdmittedStatement source.source)
    (term : Term source.source.context statement.output.context source.source.table.declarations)
    (t : source.source.table.declarations.Tensor)
    (dest : Coord statement.output.shape →
      Coord (source.source.table.declarations.signature t).axes)
    (p : Coord (source.source.table.declarations.signature t).axes) :
    term.globalFiber (retarget statement.output t dest) (ratStore source) p =
      ∑ c : Coord statement.output.context.axes,
        if dest (statement.output.slots.project c) = p then
          term.value (ratStore source) c else 0 :=
  term.fiber_partition (retarget statement.output t dest) (ratStore source) p

/-- Admission's outputs are bare: the raw-parse chain's gate is discharged by admission. -/
example (source : AdmittedSource) (snapshot : SourceSnapshot)
    (h : admitSource snapshot = .ok source) (s : Fin source.statements.length) :
    (source.statements.get s).output.IsBare := by
  obtain ⟨_, hf⟩ := admitSource_fields snapshot source h
  have hs := hf.get (by rw [hf.length_eq]; exact s.isLt) s.isLt
  obtain ⟨_, _, _, _, _, _, _, _, _, hb, _, _⟩ := hs
  exact hb.2

end SourceAffineDestinationTest

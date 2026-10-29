import Eval.Plan.B5BoundaryTest

namespace LeanNCD.Eval.Plan.B5bBoxTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.Eval.Plan.B5NativeTest
  LeanNCD.Eval.Plan.B5BoundaryTest Std

def unpin (n : String) (p : TLProgram) : TLProgram :=
  { p with decls := p.decls.map fun
    | .axis a v => if a.name == n then .axis a none else .axis a v
    | d => d }
def pinTo (n : String) (size : Nat) (p : TLProgram) : TLProgram :=
  { p with decls := p.decls.map fun
    | .axis a v => if a.name == n then .axis a (some size) else .axis a v
    | d => d }

-- Donor: interleave (axes i = 2, k = 4; A(i), B(i), S(k)); concatenation instead of interleave.
def concat : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 4
  tensor f32 A(i), B(i), S(k)
  S[i] := A[i]
  S[1*i + 2] := B[i]
}
def concatExact : TLProgram := unpin "k" concat
def concatExceeds : TLProgram := pinTo "k" 3 concat

-- Donors: tropical / tropMin with the declared box one larger than the scatter extent.
def tropBox : TLProgram := pinTo "k" 5 tropical
def tropMinBox : TLProgram := pinTo "k" 5 tropMin

-- Donor: bareMismatch with the bare writer's axis wider than the box.
def bareExceeds : TLProgram := pinTo "j" 5 bareMismatch
def wideIn64 : NamedDenseEnv := in64.insert "B" ⟨[5], #[10, 20, 30, 40, 50]⟩
def wideIn32 : NamedDenseEnv32 := in32.insert "B" ⟨[5], #[10, 20, 30, 40, 50]⟩

-- Donors: B5BoundaryTest.lateMismatch.
def lateExact : TLProgram := unpin "l" lateMismatch
def lateExceeds : TLProgram := pinTo "m" 4 lateMismatch
def lateWide64 : NamedDenseEnv := late64.insert "Extra" ⟨[4, 4], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]⟩

def refError (p : TLProgram) (i : NamedDenseEnv) : Option EvalError :=
  (scheduled (as64 p)).bind fun s => match evalScheduled s i with
    | .error f => some f.error
    | .ok _ => none
def planCause (p : TLProgram) : Option PlanCompileCause :=
  (scheduled p).bind fun s =>
    (InputSignature.ofDenseInputs32ForDecls s.decls in32).toOption.bind fun sig =>
      match prepareEvalPlan s sig with
      | .error f => some f.cause
      | .ok _ => none

-- Concatenation into a pinned box: three native legs, both writer orders.
#guard agree concat in64 in32 #[-5, -2, -7, -3] #[-5, -2, -7, -3]
#guard agree (reverseWriters concat) in64 in32 #[-5, -2, -7, -3] #[-5, -2, -7, -3]
#guard sourceError concat == none
-- Exact twin: the box size left to inference keeps B5's equality and its payload.
#guard refShape concatExact in64 == some (.writerExtentMismatch "S" 1 0 4 2)
#guard planShape concatExact in64 == some (.writerExtentMismatch "S" 1 0 4 2)
#guard planShape32 concatExact in32 == some (.writerExtentMismatch "S" 1 0 4 2)
-- Nearest refused neighbour: the scatter writer exceeds the box by one.
#guard refShape concatExceeds in64 == some (.writerExtentExceedsBox "S" 2 0 3 4)
#guard planShape concatExceeds in64 == some (.writerExtentExceedsBox "S" 2 0 3 4)
#guard planShape32 concatExceeds in32 == some (.writerExtentExceedsBox "S" 2 0 3 4)
-- Bare writer wider than the box.
#guard refShape bareExceeds wideIn64 == some (.writerExtentExceedsBox "S" 2 0 4 5)
#guard planShape bareExceeds wideIn64 == some (.writerExtentExceedsBox "S" 2 0 4 5)
#guard planShape32 bareExceeds wideIn32 == some (.writerExtentExceedsBox "S" 2 0 4 5)
-- Tropical holes under a larger box, native f32 bits included.
#guard agree tropBox tropIn64 tropIn32 #[-5, -(1/0), -2, -(1/0), -(1/0)]
  #[-5, -(1/0), -2, -(1/0), -(1/0)]
#guard agree tropMinBox tropIn64 tropIn32 #[-7, 1/0, -3, 1/0, 1/0] #[-7, 1/0, -3, 1/0, 1/0]
-- Multi-dimensional box: writer 3's second dimension (2) fits the pinned 3; the exact twin and the
-- exceeding neighbour keep their diagnostics.
#guard (ref64 lateMismatch late64).bind (fun e => e["S"]?.map (·.data)) ==
  some #[3, 6, 6, 3, 4, 0, 13, 16, 12, 7, 8, 0]
#guard (run64 lateMismatch late64).bind (fun e => e["S"]?.map (·.data)) ==
  some #[3, 6, 6, 3, 4, 0, 13, 16, 12, 7, 8, 0]
#guard refShape lateExact late64 == some (.writerExtentMismatch "S" 3 1 3 2)
#guard planShape lateExact late64 == some (.writerExtentMismatch "S" 3 1 3 2)
#guard refShape lateExceeds lateWide64 == some (.writerExtentExceedsBox "S" 3 1 3 4)
#guard planShape lateExceeds lateWide64 == some (.writerExtentExceedsBox "S" 3 1 3 4)
-- B6 is unchanged: the negative writer fits the pinned box by derived extent (1 <= 4)
-- and then fails its own range check on both native paths.
#guard
  match refError negativeWriter in64 with
  | some (.scatterWriteOutOfRange "S#2" [3] [0]) => true
  | _ => false
#guard planCause negativeWriter ==
  some (.shape (.scatterImageOutOfRange "S#2" 0 2 3 1))

-- Coverage widening after the post-landing review. Precision note: the f32 and f64 checked entries
-- share `checkCollectorShapes`, so the f32 guards pin the f32 entry's wiring, not extra logic.
def lateWide32 : NamedDenseEnv32 :=
  late32.insert "Extra" ⟨[4, 4], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]⟩
#guard planShape32 lateExact late32 == some (.writerExtentMismatch "S" 3 1 3 2)
#guard planShape32 lateExceeds lateWide32 == some (.writerExtentExceedsBox "S" 3 1 3 4)
#guard planShape32 bareExact badIn32 == some (.writerExtentMismatch "S" 2 0 4 3)
#guard (run32 lateMismatch late32).bind (fun e => e["S"]?.map (·.data.map Float32.toBits)) ==
  some ((#[3, 6, 6, 3, 4, 0, 13, 16, 12, 7, 8, 0] : Array Float32).map Float32.toBits)

-- The published tensor has the box shape on every native leg, not just the right values.
def shapesOf (p : TLProgram) (i : NamedDenseEnv) (j : NamedDenseEnv32) :=
  ((ref64 p i).bind fun e => e["S"]?.map (·.shape),
   (run64 p i).bind fun e => e["S"]?.map (·.shape),
   (run32 p j).bind fun e => e["S"]?.map (·.shape))
#guard shapesOf concat in64 in32 == (some [4], some [4], some [4])
#guard shapesOf bareMismatch badIn64 badIn32 == (some [4], some [4], some [4])
#guard shapesOf declaredMismatch in64 in32 == (some [5], some [5], some [5])
#guard shapesOf tropBox tropIn64 tropIn32 == (some [5], some [5], some [5])
#guard shapesOf lateMismatch late64 late32 == (some [4, 3], some [4, 3], some [4, 3])

-- A box pinned through an `iter` declaration is a box too (`declaredAxisSizes` seeds both).
def iterPin (size : Nat) (p : TLProgram) : TLProgram :=
  { p with decls := p.decls.map fun
    | .axis a v => if a.name == "k" then .iter a size else .axis a v
    | d => d }
def iterBox : TLProgram := iterPin 4 concat
def iterExceeds : TLProgram := iterPin 3 concat
#guard agree iterBox in64 in32 #[-5, -2, -7, -3] #[-5, -2, -7, -3]
#guard shapesOf iterBox in64 in32 == (some [4], some [4], some [4])
#guard refShape iterExceeds in64 == some (.writerExtentExceedsBox "S" 2 0 3 4)
#guard planShape iterExceeds in64 == some (.writerExtentExceedsBox "S" 2 0 3 4)
#guard planShape32 iterExceeds in32 == some (.writerExtentExceedsBox "S" 2 0 3 4)

end LeanNCD.Eval.Plan.B5bBoxTest

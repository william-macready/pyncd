import Eval.Plan.B5bBoxTest

namespace LeanNCD.Eval.Plan.B5cSingleBoxTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.Eval.Plan.B5NativeTest
  LeanNCD.Eval.Plan.B5BoundaryTest LeanNCD.Eval.Plan.B5bBoxTest Std

-- Donor: B5bBoxTest.concat, reduced to ONE scatter writer into a pinned `S(k)`, `k = 8`.
def one : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 8
  tensor f32 A(i), S(k)
  S[2*i] := A[i]
}
def oneEqual : TLProgram := pinTo "k" 4 one
def oneExceeds : TLProgram := pinTo "k" 3 one
def oneInferred : TLProgram := unpin "k" one

-- A single bare assign over an axis that differs from the declared one.
def bareOne : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 4
  tensor f32 A(i), S(k)
  S[i] := A[i]
}
def bareOneTight : TLProgram := pinTo "k" 2 bareOne
def bareOneExceeds : TLProgram := pinTo "k" 1 bareOne

-- D5: the declared axis is the writer's own source axis (`Out(i)` with `Out[2*i]`).
def idiom : TLProgram := tlprog!{
  axis i : ℕ = 2
  tensor f32 A(i), S(i)
  S[2*i] := A[i]
}
-- A transposed write over the declared axes (`S(i, j)` with `S[j, i]`) uses declared axes as its source
-- axes (D5), so it keeps the derived shape `[3, 2]`; collected as a box it would exceed `[2, 3]`.
def transposeOne : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  tensor f32 M(j, i), S(i, j)
  S[j, i] := M[j, i]
}
def transposeIn64 : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "M" ⟨[3, 2], #[1, 2, 3, 4, 5, 6]⟩
def transposeIn32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "M" ⟨[3, 2], #[1, 2, 3, 4, 5, 6]⟩
-- A scalar (rank-0) destination has nothing to pad: never collected (the D5 test is vacuous for it).
def scalarOne : TLProgram := tlprog!{
  tensor f32 A(), S()
  S[] := A[]
}
def scalarIn64 : NamedDenseEnv := ({} : NamedDenseEnv).insert "A" ⟨[], #[3]⟩
def scalarIn32 : NamedDenseEnv32 := ({} : NamedDenseEnv32).insert "A" ⟨[], #[3]⟩
-- Identity writer: declared axes are the written axes.
def identityOne : TLProgram := tlprog!{
  axis i : ℕ = 2
  tensor f32 A(i), S(i)
  S[i] := A[i]
}
-- Donor: B5NativeTest.tropical reduced to one max writer, holes under a larger box.
def tropOne : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 1
  axis k : ℕ = 8
  tensor f32 A(i, j), S(k)
  S[2*i] := maxreduce(A[i, j])
}
-- A reader of the boxed destination over its declared axis.
def oneReader : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 8
  tensor f32 A(i), S(k), R(k)
  S[2*i] := A[i]
  R[k] := S[k]
}
def predOne : TLProgram := { one with decls := one.decls.map fun
  | .typedTensor _ "S" axes => .predicate "S" axes
  | d => d }

def groupsOf (p : TLProgram) : List String :=
  match scheduled p with
  | some s => (boxedSingleGroups s.env (declaredAxisSizes s.decls) s.stmts).map (·.name)
  | none => []

def replaceSlot (slot : LHSSlot) (p : TLProgram) : TLProgram :=
  { p with stmts := p.stmts.map fun
    | .assign n _ r | .scatter n _ r => .scatter n [slot] r
    | s => s }
def multiAxisOne : TLProgram :=
  replaceSlot (.affine (.affine 0 [(1, ⟨"i", 0, .nat⟩), (1, ⟨"j", 91, .nat⟩)])) one
def constOne : TLProgram := replaceSlot (.affine (.const 3)) one

-- One scatter writer into a pinned box: the declaration decides the shape (three native legs).
#guard agree one in64 in32 #[-5, 0, -2, 0, 0, 0, 0, 0] #[-5, 0, -2, 0, 0, 0, 0, 0]
#guard shapesOf one in64 in32 == (some [8], some [8], some [8])
-- Accept neighbour: the declared extent equals the derived one.
#guard agree oneEqual in64 in32 #[-5, 0, -2, 0] #[-5, 0, -2, 0]
-- Nearest refused neighbour: a declared extent smaller than the derived one, even though the writes
-- at 0 and 2 would fit (the M4 slack, deliberately).
#guard refShape oneExceeds in64 == some (.writerExtentExceedsBox "S" 1 0 3 4)
#guard planShape oneExceeds in64 == some (.writerExtentExceedsBox "S" 1 0 3 4)
#guard planShape32 oneExceeds in32 == some (.writerExtentExceedsBox "S" 1 0 3 4)
-- Unpinned declaration: unchanged, the derived shape.
#guard shapesOf oneInferred in64 in32 == (some [4], some [4], some [4])

-- A single bare assign over a different axis is padded to the box, refused when it exceeds it.
#guard agree bareOne in64 in32 #[-5, -2, 0, 0] #[-5, -2, 0, 0]
#guard shapesOf bareOneTight in64 in32 == (some [2], some [2], some [2])
#guard refShape bareOneExceeds in64 == some (.writerExtentExceedsBox "S" 1 0 1 2)
#guard planShape bareOneExceeds in64 == some (.writerExtentExceedsBox "S" 1 0 1 2)
#guard planShape32 bareOneExceeds in32 == some (.writerExtentExceedsBox "S" 1 0 1 2)

-- D5: a declared axis the writer uses as its own source axis names it, it does not claim an extent.
#guard shapesOf idiom in64 in32 == (some [4], some [4], some [4])
#guard shapesOf transposeOne transposeIn64 transposeIn32 == (some [3, 2], some [3, 2], some [3, 2])
#guard shapesOf scalarOne scalarIn64 scalarIn32 == (some [], some [], some [])
-- An identity writer is untouched.
#guard shapesOf identityOne in64 in32 == (some [2], some [2], some [2])

-- Tropical holes hold `-inf`, native f32 bits included.
#guard agree tropOne tropIn64 tropIn32 #[-5, -(1/0), -2, -(1/0), -(1/0), -(1/0), -(1/0), -(1/0)]
  #[-5, -(1/0), -2, -(1/0), -(1/0), -(1/0), -(1/0), -(1/0)]

-- A reader over the declared axis: `S` and `R` both have the box shape (before the rule this was
-- a `sizeConflict 8 vs 4`).
#guard ((ref64 oneReader in64).bind fun e => e["R"]?.map fun t => (t.shape, t.data)) ==
  some ([8], #[-5, 0, -2, 0, 0, 0, 0, 0])
#guard ((run64 oneReader in64).bind fun e => e["R"]?.map fun t => (t.shape, t.data)) ==
  some ([8], #[-5, 0, -2, 0, 0, 0, 0, 0])
#guard ((run32 oneReader in32).bind fun e => e["R"]?.map (·.shape)) == some [8]

-- D1: a predicate destination keeps the derived shape (reference leg; the checked legs refuse a
-- real-valued input into a predicate unrelated to boxing).
#guard ((ref64 predOne in64).bind fun e => e["S"]?.map (·.shape)) == some [4]

-- Which single writers are collected (`boxedSingleGroups`), with every exclusion: unpinned
-- declaration, D5 idiom, identity and transposed writers (D5), a scalar destination, predicate (D1),
-- multi-axis and constant slots (D2), and a two-writer group (collected by `writerGroups`, not here).
#guard [groupsOf one, groupsOf oneEqual, groupsOf oneInferred, groupsOf bareOne, groupsOf idiom,
  groupsOf identityOne, groupsOf tropOne, groupsOf predOne, groupsOf multiAxisOne, groupsOf constOne,
  groupsOf concat, groupsOf transposeOne, groupsOf scalarOne] ==
  [["S"], ["S"], [], ["S"], [], [], ["S"], [], [], [], [], [], []]

-- `route` is unchanged: a single boxed writer still routes (route carries no extents).
#guard routeError one == none && routeError bareOne == none

end LeanNCD.Eval.Plan.B5cSingleBoxTest

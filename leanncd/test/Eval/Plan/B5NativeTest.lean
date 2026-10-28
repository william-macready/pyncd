import LeanNCD.Eval.Entry
import LeanNCD.Eval.Plan.Adapter32

namespace LeanNCD.Eval.Plan.B5NativeTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

def as64 (p : TLProgram) : TLProgram :=
  { p with decls := p.decls.map fun
    | .typedTensor .f32 nm ax => .typedTensor .f64 nm ax
    | d => d }

def scheduled (p : TLProgram) : Option ScheduledProgram :=
  match p.compileToScheduled.run 0 with
  | .ok s _ => some s
  | .error _ _ => none

def in64 : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "A" ⟨[2], #[-5, -2]⟩ |>.insert "B" ⟨[2], #[-7, -3]⟩
def in32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "A" ⟨[2], #[-5, -2]⟩ |>.insert "B" ⟨[2], #[-7, -3]⟩

def prep64 (p : TLProgram) (i := in64) : Option PreparedPlan :=
  (scheduled (as64 p)).bind fun s =>
    (prepareEvalPlan s (InputSignature.ofDenseInputs i)).toOption
def prep32 (p : TLProgram) (i := in32) : Option PreparedPlan :=
  (scheduled p).bind fun s =>
    (InputSignature.ofDenseInputs32ForDecls s.decls i).toOption.bind fun sig =>
      (prepareEvalPlan s sig).toOption
def ref64 (p : TLProgram) (i := in64) : Option NamedDenseEnv :=
  (scheduled (as64 p)).bind fun s => (evalScheduled s i).toOption.map (·.env)
def run64 (p : TLProgram) (i := in64) : Option NamedDenseEnv :=
  (prep64 p i).bind fun pp => (runPreparedDense pp i).toOption.map (·.env)
def run32 (p : TLProgram) (i := in32) : Option NamedDenseEnv32 :=
  (prep32 p i).bind fun pp => (runPreparedDense32 pp i).toOption.map (·.env)
def obs (p : TLProgram) :=
  ((ref64 p).bind (fun e => e["S"]?.map (·.data)),
   (run64 p).bind (fun e => e["S"]?.map (·.data)),
   (run32 p).bind (fun e => e["S"]?.map (·.data)))

-- Donor: CollectEvalTest.j3 / CollectPlanTest.nbScat; declare destination extent 4
-- and the actual A/B inputs, with an overlap variant leaving identity-filled holes.
def interleave : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 4
  tensor f32 A(i), B(i), S(k)
  S[2*i] := A[i]
  S[2*i + 1] := B[i]
}
def overlap : TLProgram := { interleave with stmts := interleave.stmts.map fun
  | .assign nm _ r => .assign nm [.affine (.scale 2 { name := "i", uid := 0, kind := .nat })] r
  | s => s }

-- Donor: interleave; use the same stride for both writers and max/min annotations.
def tropical : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 1
  axis k : ℕ = 4
  tensor f32 A(i, j), B(i), S(k)
  S[2*i] := maxreduce(A[i, j])
  S[2*i] := B[i]
}
def tropMin : TLProgram := { tropical with stmts := tropical.stmts.map fun
  | .assign nm ls r => .assign nm ls { r with agg := if r.agg == .max then .min else r.agg }
  | s => s }
def tropIn64 : NamedDenseEnv := in64.insert "A" ⟨[2, 1], #[-5, -2]⟩
def tropIn32 : NamedDenseEnv32 := in32.insert "A" ⟨[2, 1], #[-5, -2]⟩

-- Donor: interleave; replace writer 2 with ordinary full-domain assignment.
def mixed : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 4
  tensor f32 A(i), B(k), S(k)
  S[2*i] := A[i]
  S[k] := B[k]
}
def reverseWriters (p : TLProgram) : TLProgram := { p with stmts := p.stmts.reverse }
def undeclare (p : TLProgram) : TLProgram :=
  { p with decls := p.decls.filter (fun d => d.name != "S") }
def mixIn64 : NamedDenseEnv := in64.insert "B" ⟨[4], #[10, 20, 30, 40]⟩
def mixIn32 : NamedDenseEnv32 := in32.insert "B" ⟨[4], #[10, 20, 30, 40]⟩

-- Donor: mixed; bare writer has extent 3, not the basis's 4.
def bareMismatch : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  axis k : ℕ = 4
  tensor f32 A(i), B(j), S(k)
  S[2*i] := A[i]
  S[j] := B[j]
}
def badIn64 : NamedDenseEnv := in64.insert "B" ⟨[3], #[10, 20, 30]⟩
def badIn32 : NamedDenseEnv32 := in32.insert "B" ⟨[3], #[10, 20, 30]⟩

def refShape (p : TLProgram) (i : NamedDenseEnv) : Option ShapeError :=
  (scheduled (as64 p)).bind fun s => match evalScheduled s i with
    | .error f => match f.error with | .shape e => some e | _ => none
    | .ok _ => none
def planShape (p : TLProgram) (i : NamedDenseEnv) : Option ShapeError :=
  (scheduled (as64 p)).bind fun s =>
    match prepareEvalPlan s (InputSignature.ofDenseInputs i) with
    | .error f => match f.cause with | .shape e => some e | _ => none
    | .ok _ => none

-- Donor: interleave; diagonal writes into a square declared on DISTINCT axes.
def diagonal : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 2
  axis l : ℕ = 2
  tensor f32 A(i), B(i), S(k, l)
  S[i, i] := A[i]
  S[i, i] := B[i]
}
def repeatedBasis : TLProgram := { diagonal with decls := diagonal.decls.map fun
  | .typedTensor ty "S" (a :: _) => .typedTensor ty "S" [a, a]
  | d => d }
def sourceError (p : TLProgram) : Option CompileError :=
  (scheduled p).bind fun s => match validateScheduled s with
    | .error e => some e
    | .ok _ => none

def zeroScale : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis k : ℕ = 0
  tensor f32 A(i), B(i), S(k)
  S[0*i] := A[i]
  S[0*i] := B[i]
}
def emptySource : TLProgram := { zeroScale with decls := zeroScale.decls.map fun
  | .axis a _ => .axis a (some 0)
  | d => d }
def emptyIn64 : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "A" ⟨[0], #[]⟩ |>.insert "B" ⟨[0], #[]⟩
def emptyIn32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "A" ⟨[0], #[]⟩ |>.insert "B" ⟨[0], #[]⟩

#eval obs interleave
#eval obs overlap
#eval ((ref64 tropical tropIn64).bind (fun e => e["S"]?.map (·.data)),
       (run64 tropical tropIn64).bind (fun e => e["S"]?.map (·.data)),
       (run32 tropical tropIn32).bind (fun e => e["S"]?.map (·.data)))
#eval ((ref64 tropMin tropIn64).bind (fun e => e["S"]?.map (·.data)),
       (run64 tropMin tropIn64).bind (fun e => e["S"]?.map (·.data)),
       (run32 tropMin tropIn32).bind (fun e => e["S"]?.map (·.data)))
#eval (run32 mixed mixIn32).bind (fun e => e["S"]?.map (·.data))
#eval obs diagonal
#eval (refShape bareMismatch badIn64).map toString
#eval (planShape bareMismatch badIn64).map toString
#eval sourceError (undeclare interleave)
#eval sourceError repeatedBasis
#eval (prep32 zeroScale).isSome
#eval (run32 emptySource emptyIn32).bind (fun e => e["S"]?.map (·.data))

def agree (p : TLProgram) (i : NamedDenseEnv) (j : NamedDenseEnv32)
    (x : Array Float) (y : Array Float32) : Bool :=
  let bits64 := fun (e : Option NamedDenseEnv) =>
    e.bind fun e => e["S"]?.map (fun t => t.data.map Float.toBits)
  let bits32 := fun (e : Option NamedDenseEnv32) =>
    e.bind fun e => e["S"]?.map (fun t => t.data.map Float32.toBits)
  bits64 (ref64 p i) == some (x.map Float.toBits) &&
  bits64 (run64 p i) == some (x.map Float.toBits) &&
  bits32 (run32 p j) == some (y.map Float32.toBits)

#guard agree interleave in64 in32 #[-5, -7, -2, -3] #[-5, -7, -2, -3]
#guard agree overlap in64 in32 #[-12, 0, -5, 0] #[-12, 0, -5, 0]
#guard agree tropical tropIn64 tropIn32 #[-5, -(1/0), -2, -(1/0)] #[-5, -(1/0), -2, -(1/0)]
#guard agree tropMin tropIn64 tropIn32 #[-7, 1/0, -3, 1/0] #[-7, 1/0, -3, 1/0]
#guard agree mixed mixIn64 mixIn32 #[5, 20, 28, 40] #[5, 20, 28, 40]
#guard agree (reverseWriters mixed) mixIn64 mixIn32 #[5, 20, 28, 40] #[5, 20, 28, 40]
#guard agree diagonal in64 in32 #[-12, 0, 0, -5] #[-12, 0, 0, -5]
#guard agree emptySource emptyIn64 emptyIn32 #[] #[]
#guard refShape bareMismatch badIn64 ==
  some (.writerExtentMismatch "S" 2 0 4 3)
#guard planShape bareMismatch badIn64 ==
  some (.writerExtentMismatch "S" 2 0 4 3)
#guard sourceError (undeclare interleave) == some (.multiWriterNeedsDeclaredShape "S")
#guard sourceError repeatedBasis == some (.multiWriterRepeatedBasis "S")

def planShape32 (p : TLProgram) (i : NamedDenseEnv32) : Option ShapeError :=
  (scheduled p).bind fun s =>
    (InputSignature.ofDenseInputs32ForDecls s.decls i).toOption.bind fun sig =>
      match prepareEvalPlan s sig with
      | .error f => match f.cause with | .shape e => some e | _ => none
      | .ok _ => none
#guard planShape32 bareMismatch badIn32 == some (.writerExtentMismatch "S" 2 0 4 3)
#guard (run32 (undeclare mixed) mixIn32).map (fun e => e["S"]!.data.map Float32.toBits) ==
  some ((#[5, 20, 28, 40] : Array Float32).map Float32.toBits)
#guard (run32 (reverseWriters (undeclare mixed)) mixIn32).map
    (fun e => e["S"]!.data.map Float32.toBits) ==
  some ((#[5, 20, 28, 40] : Array Float32).map Float32.toBits)
#guard (prep32 interleave).map (fun pp => pp.bindings.materializedNames.map (·.name)) == some #["S"]
#guard (run64 interleave).map (fun e => e.contains "S#1" || e.contains "S#2") == some false
#guard (run32 interleave).map (fun e => e.contains "S#1" || e.contains "S#2") == some false

def routeError (p : TLProgram) : Option CompileError :=
  (scheduled p).bind fun s => match (route s).run 0 with
    | .error e _ => some e
    | .ok _ _ => none
#guard routeError interleave == some (.routeUnsupportedMultiWriter "S")

-- Donor: tropical; append an illegal max-plus to min-plus direct reader.
def badCast : TLProgram := { tropical with
  decls := tropical.decls ++
    [.typedTensor .f32 "R" [{ name := "k", uid := 0, kind := .nat }]]
  stmts := tropical.stmts ++
    [.assign "R" [.free { name := "k", uid := 0, kind := .nat }]
      { body := ⟨[⟨[.read "S" [.axis { name := "k", uid := 0, kind := .nat }]]⟩]⟩,
        nonlin := .identity, agg := .min }] }
#guard sourceError badCast == some (.sortCastUnsupported "R" "S")

def declaredMismatch : TLProgram := { interleave with decls := interleave.decls.map fun
  | .axis a n => if a.name == "k" then .axis a (some 5) else .axis a n
  | d => d }

-- Donor: overlap; multiple source coordinates expose native f32 fold order.
def orderPin : TLProgram := tlprog!{
  axis i : ℕ = 1
  axis j : ℕ = 3
  axis k : ℕ = 2
  tensor f32 A(i, j), B(i), S(k)
  S[2*i] := A[i, j]
  S[2*i] := B[i]
}
def orderIn64 : NamedDenseEnv :=
  ({} : NamedDenseEnv).insert "A" ⟨[1, 3], #[16777216, 1, -16777216]⟩
    |>.insert "B" ⟨[1], #[1]⟩
def orderIn32 : NamedDenseEnv32 :=
  ({} : NamedDenseEnv32).insert "A" ⟨[1, 3], #[16777216, 1, -16777216]⟩
    |>.insert "B" ⟨[1], #[1]⟩
#eval ((ref64 orderPin orderIn64).bind (fun e => e["S"]?.map (·.data)),
       (run64 orderPin orderIn64).bind (fun e => e["S"]?.map (·.data)),
       (run32 orderPin orderIn32).bind (fun e => e["S"]?.map (·.data)))
#eval (planShape declaredMismatch in64).map toString
#eval (refShape declaredMismatch in64).map toString
#eval (scheduled (as64 zeroScale)).bind fun s =>
  match evalScheduled s in64 with
  | .error f => some (toString f.error)
  | .ok _ => none

#guard agree orderPin orderIn64 orderIn32 #[2, 0] #[1, 0]
#guard planShape declaredMismatch in64 == some (.sizeConflict 2 5 4)
#guard refShape declaredMismatch in64 == some (.sizeConflict 2 5 4)
#guard planShape32 declaredMismatch in32 == some (.sizeConflict 2 5 4)
#guard
  match scheduled (as64 zeroScale) with
  | some s => match evalScheduled s in64 with
    | .error f => match f.error with
      | .scatterWriteOutOfRange "S#1" [0] [0] => true
      | _ => false
    | .ok _ => false
  | none => false

def zeroPlanCause : Option PlanCompileCause :=
  (scheduled zeroScale).bind fun s =>
    (InputSignature.ofDenseInputs32ForDecls s.decls in32).toOption.bind fun sig =>
      match prepareEvalPlan s sig with
      | .error f => some f.cause
      | .ok _ => none
#eval zeroPlanCause.map fun
  | .invalidPlan e => reprStr e
  | _ => "other"
#guard zeroPlanCause ==
  some (.invalidPlan (.assign (.nodeError 0 (.scatterWriteOutOfRange 0 0 0 0))))

-- Donor: interleave; the declaration supplies k's UID but not its extent.
def inferredBasis : TLProgram := { interleave with decls := interleave.decls.map fun
  | .axis a n => .axis a (if a.name == "k" then none else n)
  | d => d }

-- Donor: interleave; constants remove all input-derived size evidence.
def constantWriters : TLProgram := { overlap with
  decls := overlap.decls.filter (fun d => d.name != "A" && d.name != "B")
  stmts := overlap.stmts.map fun
    | .assign nm ls r =>
        .assign nm ls { r with body := { terms := [{ factors := [] }] } }
    | s => s }
def unsizedSource : TLProgram := { constantWriters with decls := constantWriters.decls.map fun
  | .axis a n => .axis a (if a.name == "i" then none else n)
  | d => d }
def unsizedBasis : TLProgram := { unsizedSource with decls := unsizedSource.decls.map fun
  | .axis a _ => .axis a none
  | d => d }
def rankMismatch : TLProgram := { interleave with stmts := interleave.stmts.map fun
  | .assign nm ls r => .assign nm (ls ++ ls) r
  | s => s }
def rankMismatchError : Option CompileError :=
  match rankMismatch.compileToScheduled.run 0 with
  | .error e _ => some e
  | .ok s _ => match validateScheduled s with
    | .error e => some e
    | .ok _ => none

-- Donor: tropical; the neutral writer reads a predicate, not a real tensor.
def predicateNeutral : TLProgram := { tropical with decls := tropical.decls.map fun
  | .typedTensor _ "B" ax => .predicate "B" ax
  | d => d }
def predicateNeutralMin : TLProgram := { tropMin with decls := predicateNeutral.decls }
def predIn64 : NamedDenseEnv := tropIn64.insert "B" ⟨[2], #[1, 0]⟩
def predIn32 : NamedDenseEnv32 := tropIn32.insert "B" ⟨[2], #[1, 0]⟩
def predMinIn64 : NamedDenseEnv := predIn64.insert "A" ⟨[2, 1], #[5, 2]⟩
def predMinIn32 : NamedDenseEnv32 := predIn32.insert "A" ⟨[2, 1], #[5, 2]⟩
def predRun64 (p : TLProgram) (i : NamedDenseEnv) : Option NamedDenseEnv :=
  (scheduled (as64 p)).bind fun s =>
    (InputSignature.ofDenseInputsForDecls s.decls i).toOption.bind fun sig =>
      (prepareEvalPlan s sig).toOption.bind fun pp =>
        (runPreparedDense pp i).toOption.map (·.env)

#eval obs inferredBasis
#eval obs constantWriters
#eval (refShape unsizedSource {}).map toString
#eval (planShape unsizedSource {}).map toString
#eval (planShape32 unsizedSource {}).map toString
#eval (refShape unsizedBasis {}).map toString
#eval (planShape unsizedBasis {}).map toString
#eval (planShape32 unsizedBasis {}).map toString
#eval rankMismatchError
#eval ((ref64 predicateNeutral predIn64).bind (fun e => e["S"]?.map (·.data)),
       (predRun64 predicateNeutral predIn64).bind (fun e => e["S"]?.map (·.data)),
       (run32 predicateNeutral predIn32).bind (fun e => e["S"]?.map (·.data)))
#eval ((ref64 predicateNeutralMin predMinIn64).bind (fun e => e["S"]?.map (·.data)),
       (predRun64 predicateNeutralMin predMinIn64).bind (fun e => e["S"]?.map (·.data)),
       (run32 predicateNeutralMin predMinIn32).bind (fun e => e["S"]?.map (·.data)))

#guard agree inferredBasis in64 in32 #[-5, -7, -2, -3] #[-5, -7, -2, -3]
#guard agree constantWriters {} {} #[2, 0, 2, 0] #[2, 0, 2, 0]
#guard rankMismatchError == some (.rankMismatch "S" 1 2)

def closureUnsizedSource : Bool :=
  let e := some (ShapeError.unsizedScatterOutput
    (.affine (.scale 2 { name := "i", uid := 1, kind := .nat })))
  refShape unsizedSource {} == e && planShape unsizedSource {} == e &&
    planShape32 unsizedSource {} == e
run_cmd do
  unless closureUnsizedSource do
    throwError "B5 closure unsized-source: expected typed unsizedScatterOutput, never default extent 0"

def closureUnsizedBasis : Bool :=
  let e := some (ShapeError.unsizedScatterOutput
    (.free { name := "k", uid := 2, kind := .real }))
  refShape unsizedBasis {} == e && planShape unsizedBasis {} == e &&
    planShape32 unsizedBasis {} == e
#guard closureUnsizedBasis

def predicateAgree (p : TLProgram) (i : NamedDenseEnv) (j : NamedDenseEnv32)
    (x : Array Float) (y : Array Float32) : Bool :=
  let bits64 := fun (e : Option NamedDenseEnv) =>
    e.bind fun e => e["S"]?.map (fun t => t.data.map Float.toBits)
  let bits32 := fun (e : Option NamedDenseEnv32) =>
    e.bind fun e => e["S"]?.map (fun t => t.data.map Float32.toBits)
  bits64 (ref64 p i) == some (x.map Float.toBits) &&
  bits64 (predRun64 p i) == some (x.map Float.toBits) &&
  bits32 (run32 p j) == some (y.map Float32.toBits)
#guard predicateAgree predicateNeutral predIn64 predIn32
  #[0, -(1/0), -2, -(1/0)] #[0, -(1/0), -2, -(1/0)]
#guard predicateAgree predicateNeutralMin predMinIn64 predMinIn32
  #[0, 1/0, 2, 1/0] #[0, 1/0, 2, 1/0]
#eval (ref64 interleave).map (fun e => e.contains "S#1" || e.contains "S#2")
def referenceScratchPrivate : Bool :=
  (ref64 interleave).map (fun e => e.contains "S#1" || e.contains "S#2") == some false
run_cmd do
  unless referenceScratchPrivate do
    throwError "B5 reference scratch privacy: ref64 interleave must hide S#1 and S#2"

-- Donor: undeclare mixed; only the affine writer gains a second destination slot.
def fallbackRankMismatch : TLProgram := { undeclare mixed with
  stmts := mixed.stmts.map fun
    | .assign nm ls r =>
        .assign nm (if ls.any (fun s => s.freeUID?.isNone) then ls ++ ls else ls) r
    | s => s }
#eval sourceError fallbackRankMismatch

def fallbackRankRejected : Bool :=
  sourceError fallbackRankMismatch == some (.rankMismatch "S" 1 2)
run_cmd do
  unless fallbackRankRejected do
    throwError "B5 fallback basis rank: undeclared S[k] basis must reject two-slot affine writer"

-- Donor: interleave; writer 1 stays `S[2*i]`, writer 2 is replaced by an offset or
-- negative-coefficient placement. The offset keeps the stride-aligned extent (4) and collides
-- with writer 1 at S[2]; the negative form takes the legacy linear boundary (3 - 1*2 = 1), so the
-- exact-extent rule refuses it on all three legs instead of reaching a range check.
def withSecondPlacement (slot : LHSSlot) : TLProgram :=
  { interleave with stmts := interleave.stmts.mapIdx fun n s =>
    match s with
    | .assign nm _ r | .scatter nm _ r =>
        .scatter nm [if n == 1 then slot
          else .affine (.scale 2 { name := "i", uid := 0, kind := .nat })] r
    | s => s }
def offsetWriter : TLProgram :=
  withSecondPlacement (.affine (.affine 2 [(1, { name := "i", uid := 0, kind := .nat })]))
def negativeWriter : TLProgram :=
  withSecondPlacement (.affine (.affine 3 [(-1, { name := "i", uid := 0, kind := .nat })]))

#guard sourceError offsetWriter == none
#guard agree offsetWriter in64 in32 #[-5, 0, -9, -3] #[-5, 0, -9, -3]
#guard sourceError negativeWriter == none
#guard refShape negativeWriter in64 == planShape negativeWriter in64
#guard (refShape negativeWriter in64).isSome
#guard (run64 negativeWriter).isNone && (run32 negativeWriter).isNone

end LeanNCD.Eval.Plan.B5NativeTest

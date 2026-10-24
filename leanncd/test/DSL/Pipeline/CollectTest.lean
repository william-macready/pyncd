import LeanNCD.DSL.Pipeline.Collect
import LeanNCD.DSL.Compile

/-! Structural tests for `desugarMultiWriters` (additive collection, slice 1).

Each fixture pins one structural fact of the desugar on a real schedule (from `tlprog!` through
`compileToScheduled`, or hand-built where surface syntax cannot reach the case): at most one writer
per name afterwards, writers renamed in place and in order, the collector reads exactly its group,
declaration clones, freshness, the identity on single-writer schedules, and the slice-1 rejections.
Values are checked separately, through the evaluator (`test/Eval/CollectEvalTest.lean`). -/

namespace LeanNCD.CollectTest
open LeanNCD

/-- The plain statements of a schedule, or `none` if it has a scan node. -/
private def plainStmts (stmts : List ScanStmt) : Option (List Stmt) :=
  stmts.mapM fun | .plain s => some s | _ => none

private def scheduled (p : TLProgram) : Option ScheduledProgram :=
  match p.compileToScheduled.run 0 with
  | .ok sp _ => some sp
  | .error _ _ => none

private def desugared (p : TLProgram) : Option (Except CompileError (ScheduledProgram × List String)) :=
  (scheduled p).map desugarMultiWriters

/-- Destination names of a desugared schedule, in order. -/
private def dests (p : TLProgram) : Option (List String) :=
  match desugared p with
  | some (.ok (sp, _)) => (plainStmts sp.stmts).map (·.map Stmt.lhsName)
  | _ => none

/-- The read names of the statement writing `nm`. -/
private def readsOf (p : TLProgram) (nm : String) : Option (List String) :=
  match desugared p with
  | some (.ok (sp, _)) => ((plainStmts sp.stmts).bind (·.find? (·.lhsName == nm))).map
      (fun s => s.readFactors.map (·.1))
  | _ => none

private def errorOf (p : TLProgram) : Option CompileError :=
  match desugared p with
  | some (.error e) => some e
  | _ => none

private def generatedOf (p : TLProgram) : Option (List String) :=
  match desugared p with
  | some (.ok (_, g)) => some g
  | _ => none

-- C1 (donor: F14 `multiDefinition`, SourceDifferentialPolicyTest): two writers of Y are renamed
-- in place and in order, the collector follows the last writer and reads exactly Y#1, Y#2.
def c1 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Y[i] := B[i]
}
#guard dests c1 == some ["Y#1", "Y#2", "Y"]
#guard readsOf c1 "Y#1" == some ["A"]
#guard readsOf c1 "Y#2" == some ["B"]
#guard readsOf c1 "Y" == some ["Y#1", "Y#2"]
#guard generatedOf c1 == some ["Y#1", "Y#2"]

-- C2 (clone c1, add a third writer and a reader): at most one writer per name afterwards, and the
-- reader still follows the collector.
def c2 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Y[i] := B[i]
  Y[i] := C[i]
  Z[i] := Y[i]
}
#guard dests c2 == some ["Y#1", "Y#2", "Y#3", "Y", "Z"]
#guard readsOf c2 "Y" == some ["Y#1", "Y#2", "Y#3"]
#guard readsOf c2 "Z" == some ["Y"]

-- C3 identity (accept-neighbour of c1: one writer): the schedule is returned unchanged.
def c3 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Z[i] := Y[i]
}
#guard
  match scheduled c3 with
  | some sp => match desugarMultiWriters sp with
    | .ok (sp', g) => g.isEmpty && plainStmts sp'.stmts == plainStmts sp.stmts && sp'.decls == sp.decls
    | .error _ => false
  | none => false

-- C4 declaration cloning (clone c1, declare Y `predicate`): one predicate clone per writer.
def c4 : TLProgram := tlprog!{
  axis i : ℕ = 2
  predicate Y(i)
  Y[i] := A[i]
  Y[i] := B[i]
}
#guard
  match desugared c4 with
  | some (.ok (sp, _)) =>
      (sp.decls.filter (fun d => d.name.startsWith "Y")).map (fun d => match d with
        | .predicate n _ => n | _ => "") == ["Y", "Y#1", "Y#2"]
  | _ => false

-- C4b (clone c4, declare Y `tensor f64`): clones carry the element type.
def c4b : TLProgram := tlprog!{
  axis i : ℕ = 2
  tensor f64 Y(i)
  Y[i] := A[i]
  Y[i] := B[i]
}
#guard
  match desugared c4b with
  | some (.ok (sp, _)) =>
      (sp.decls.filter (fun d => d.name.startsWith "Y")).map Decl.elementType? ==
        [some .f64, some .f64, some .f64]
  | _ => false

-- C5 rejection: scatter writers (decision note probe `S[2*i]:=X[i]; S[2*i+1]:=Y[i]`).
def c5 : TLProgram := tlprog!{
  axis i : ℕ = 2
  S[2*i] := X[i]
  S[2*i + 1] := Y[i]
}
#guard errorOf c5 == some (.multiWriterScatter "S")

-- C6 rejection: max-annotated multi-writer set (clone c1, change agg to maxreduce).
def c6 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := maxreduce(A[i, j])
  Y[i] := maxreduce(B[i, j])
}
#guard errorOf c6 == some (.multiWriterAlgebra "Y")

-- C7 rejection: axis-UID mismatch (clone c1, writer 2 on axis j).
def c7 : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  Y[i] := A[i]
  Y[j] := B[j]
}
#guard errorOf c7 == some (.writerShapeMismatch "Y" 2 0)

-- C7b accept-neighbour of c7 (same text, `axis j` still declared, writer 2 moved to i): accepted,
-- with the generated names and order. Fails on its own if the UID test over-rejects.
def c7b : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  Y[i] := A[i]
  Y[i] := B[i]
}
#guard errorOf c7b == none
#guard dests c7b == some ["Y#1", "Y#2", "Y"]
#guard generatedOf c7b == some ["Y#1", "Y#2"]

-- C7c (clone c7, rank 2, mismatch at position 1): the reported position is 1, not 0.
def c7c : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  axis k : ℕ = 2
  Y[i, j] := A[i, j]
  Y[i, k] := B[i, k]
}
#guard errorOf c7c == some (.writerShapeMismatch "Y" 2 1)

-- C10 slot-count check (`checkWriterGroup`): writer 2 has FEWER slots than writer 1. The position
-- loop never fires on it (every writer-2 slot agrees with writer 1's), so only the length check
-- rejects; payload = the shorter length.
def c10 : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  Y[i, j] := A[i, j]
  Y[i] := B[i]
}
#guard errorOf c10 == some (.writerShapeMismatch "Y" 2 1)
-- C10b (clone c10, swap the writers): LONGER writer 2 fails in the position loop at `first.length`.
def c10b : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  Y[i] := A[i]
  Y[i, j] := B[i, j]
}
#guard errorOf c10b == some (.writerShapeMismatch "Y" 2 1)
-- C10c accept-neighbour (clone c10, writer 2 also rank 2): accepted.
def c10c : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  Y[i, j] := A[i, j]
  Y[i, j] := B[i, j]
}
#guard errorOf c10c == none
#guard dests c10c == some ["Y#1", "Y#2", "Y"]

-- C6b/C6c rejection (clone c6): a MIXED set, one sum writer and one max writer, in both orders, so a
-- check of only the first or only the last writer's annotation survives neither.
def c6b : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Y[i] := maxreduce(B[i, j])
}
#guard errorOf c6b == some (.multiWriterAlgebra "Y")
def c6c : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := maxreduce(A[i, j])
  Y[i] := B[i]
}
#guard errorOf c6c == some (.multiWriterAlgebra "Y")

-- S3b T8: the min twins of C6/C6b/C6c. The refusal is decided from the writers' sorts, so a check
-- that only tested `agg == .max` would admit all three of these.
def c6min : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := minreduce(A[i, j])
  Y[i] := minreduce(B[i, j])
}
#guard errorOf c6min == some (.multiWriterAlgebra "Y")
def c6bm : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Y[i] := minreduce(B[i, j])
}
#guard errorOf c6bm == some (.multiWriterAlgebra "Y")
def c6cm : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := minreduce(A[i, j])
  Y[i] := B[i]
}
#guard errorOf c6cm == some (.multiWriterAlgebra "Y")

-- C11 admitted `.freeNorm` class (donor: `RouteFragmentCorpusTest.axiswise`'s `Y[q, s.] := softmax`):
-- each writer keeps its marker; the collector's slots are plain `.free`, so no
-- `unmarkedReductionAxis` is raised for the collector's sum over `Y#k`.
private def slotsOf (p : TLProgram) (nm : String) : Option (List LHSSlot) :=
  match desugared p with
  | some (.ok (sp, _)) => ((plainStmts sp.stmts).bind (·.find? (·.lhsName == nm))).map Stmt.slots
  | _ => none
private def isFreeNormSlot : LHSSlot → Bool
  | .freeNorm _ => true
  | _ => false
def c11 : TLProgram := tlprog!{
  axis q : ℕ = 2
  axis s : ℕ = 2
  Y[q, s.] := softmax(A[q, s])
  Y[q, s.] := softmax(B[q, s])
}
#guard dests c11 == some ["Y#1", "Y#2", "Y"]
#guard (slotsOf c11 "Y#1").map (·.any isFreeNormSlot) == some true
#guard (slotsOf c11 "Y#2").map (·.any isFreeNormSlot) == some true
#guard (slotsOf c11 "Y").map (·.any isFreeNormSlot) == some false

-- C8 rejection: a source name already spells a generated name (programmatic only).
private def ax : AxisSpec := { name := "i", uid := 1, kind := .nat }
private def copyStmt (dst src : String) : Stmt :=
  .assign dst [.free ax] { body := ⟨[⟨[.read src [.axis ax]]⟩]⟩, nonlin := .identity }
private def c8 : ScheduledProgram :=
  { decls := [], env := {}, extNames := ∅, explicitSizes := {}
    stmts := [.plain (copyStmt "Y#1" "A"), .plain (copyStmt "Y" "B"), .plain (copyStmt "Y" "C")] }
#guard match desugarMultiWriters c8 with
  | .error e => e == .reservedNameCollision "Y#1"
  | .ok _ => false
-- C8b accept-neighbour: rename the clashing source name.
#guard match desugarMultiWriters { c8 with stmts := [.plain (copyStmt "Q" "A"),
    .plain (copyStmt "Y" "B"), .plain (copyStmt "Y" "C")] } with
  | .ok (_, g) => g == ["Y#1", "Y#2"]
  | .error _ => false
-- C8c (clone c8): the clash is a READ of the generated name (an external input called `Y#2`).
#guard match desugarMultiWriters { c8 with stmts := [.plain (copyStmt "Y" "A"),
    .plain (copyStmt "Y" "B"), .plain (copyStmt "U" "Y#2")] } with
  | .error e => e == .reservedNameCollision "Y#2"
  | .ok _ => false
-- C8d (clone c8): the clash is a DECLARATION only; no statement mentions `Y#2`.
private def c8d : ScheduledProgram :=
  { c8 with decls := [.tensor "Y#2" [ax]], stmts := [.plain (copyStmt "Y" "A"), .plain (copyStmt "Y" "B")] }
#guard match desugarMultiWriters c8d with
  | .error e => e == .reservedNameCollision "Y#2"
  | .ok _ => false


/-! ## All-writers readiness (`eligible`, `topoSortFuel`, `isTopoOrdered`)

A read is ready only once EVERY writer of the name has published it. -/

private def scheduledDests (p : TLProgram) : Option (List String) :=
  (scheduled p).bind fun sp => (plainStmts sp.stmts).map (·.map Stmt.lhsName)

-- R1 (decision note §C.2 probe `T:=A; U:=T; T:=B`): `schedule` moves the reader after both
-- writers. Before all-writers readiness it stayed between them (evaluator U = A).
def r1 : TLProgram := tlprog!{
  axis i : ℕ = 2
  T[i] := A[i]
  U[i] := T[i]
  T[i] := B[i]
}
#guard scheduledDests r1 == some ["T", "T", "U"]

-- R2: the same order hand-built as a direct schedule is not producer-before-consumer.
private def r2Stmts : List ScanStmt :=
  [.plain (copyStmt "T" "A"), .plain (copyStmt "U" "T"), .plain (copyStmt "T" "B")]
#guard !isTopoOrdered r2Stmts r2Stmts
-- R2b accept-neighbour: reader after both writers.
private def r2bStmts : List ScanStmt :=
  [.plain (copyStmt "T" "A"), .plain (copyStmt "T" "B"), .plain (copyStmt "U" "T")]
#guard isTopoOrdered r2bStmts r2bStmts

-- R3 self-read of a multi-writer tensor: the second writer can never see all writers of T, so the
-- program is cyclic. Before, it read the first writer's T (overwrite chain).
def r3 : TLProgram := tlprog!{
  axis i : ℕ = 2
  T[i] := A[i]
  T[i] := T[i] · B[i]
}
#guard match r3.compileToScheduled.run 0 with
  | .error (.cyclicDataflow "schedule: cyclic dataflow") _ => true
  | _ => false
-- R3b accept-neighbour: read into a different name.
def r3b : TLProgram := tlprog!{
  axis i : ℕ = 2
  T[i] := A[i]
  U[i] := T[i] · B[i]
}
#guard scheduledDests r3b == some ["T", "U"]


-- R4 readiness counts NODES, not output occurrences: a 2-D scan with two base faces of G lists G
-- twice in `ScanStmt.outputs` (observed: `[G, G]`), yet it is ONE writer of G. A plain reader
-- appended after it (hand-built direct schedule; surface syntax absorbs such a reader into the
-- scan) is ready. Donor: RC10 (`test/Eval/Portfolio/RecurrenceTest.lean`) plus a column-0 face.
def r4 : TLProgram := tlprog!{ iter r = 2, c = 2
  G[r, 0] := Z[r]
  G[0, c] := Q[c]
  G[r +1, c +1] := G[r, c] · W[r, c]
}
#guard match scheduled r4 with
  | some sp =>
      let stmts := sp.stmts ++ [.plain (copyStmt "T" "G")]
      (sp.stmts.map ScanStmt.outputs) == [["G", "G"]] && isTopoOrdered stmts stmts
  | none => false

-- R4b (donor: R4; scan counts as exactly ONE writer inside a multi-writer group): a plain writer of
-- G, R4's scan of G, and a plain reader of G. The reader is ready only after BOTH writers, in
-- either order of the two writers, and not before the scan.
private def ordered (l : List ScanStmt) : Bool := isTopoOrdered l l
#guard match scheduled r4 with
  | some sp =>
      let w : List ScanStmt := [.plain (copyStmt "G" "Z0")]
      let rd : List ScanStmt := [.plain (copyStmt "T" "G")]
      ordered (w ++ sp.stmts ++ rd) && ordered (sp.stmts ++ w ++ rd) && !ordered (w ++ rd ++ sp.stmts)
  | none => false

/-! ## Scan writers (`multiWriterScan`)

A name written by two or more nodes of which one is a scan node is rejected outright, instead of
being skipped. The surface cannot reach these shapes (it absorbs a plain reader of a scan name, and
fails loud with `duplicateScratchProducer` on a second producer), so the schedules are hand-built
from the scan of R4. -/

private def scanErrorOf (extra : List ScanStmt) (dup : Bool := false) : Option CompileError :=
  (scheduled r4).bind fun sp =>
    match desugarMultiWriters { sp with stmts := (if dup then sp.stmts ++ sp.stmts else sp.stmts) ++ extra } with
    | .error e => some e
    | .ok _ => none

-- C9 (donor: R4's scan of G): a plain statement also writes G.
#guard scanErrorOf [.plain (copyStmt "G" "A")] == some (.multiWriterScan "G")
-- C9b (clone C9): a second scan node of the same name instead of the plain writer.
#guard scanErrorOf [] (dup := true) == some (.multiWriterScan "G")
-- C9c accept-neighbour (clone C9, rename the plain writer's destination): one scan writer of G plus
-- an unrelated plain statement is accepted and generates nothing.
#guard scanErrorOf [.plain (copyStmt "T" "A")] == none
#guard match (scheduled r4).map (fun sp => desugarMultiWriters
    { sp with stmts := sp.stmts ++ [.plain (copyStmt "T" "A")] }) with
  | some (.ok (_, g)) => g.isEmpty
  | _ => false

/-! ## Scan scratch also written by a plain node (the order of checks)

R4's scan with one extra recurrence-only statement `S := Z`: `S` is block-local scratch, so the
scan WRITES it (`ScanStmt.writes = [G, S]`) but never publishes it (`outputs = [G, G]`). A plain
node also writing `S` therefore makes two writers of `S` of which only one ever publishes. Decision:
`validateScheduled` keeps asserting topology BEFORE collection, so with a reader of `S` it ends as
`cyclicDataflow` (fail-loud, no collection attempted); `desugarMultiWriters` called directly does
not check order and reports `multiWriterScan`, with or without the reader. -/

private def scratchSched (before after : List ScanStmt) : Option ScheduledProgram :=
  (scheduled r4).bind fun sp => match sp.stmts with
    | [.scan nm axs b r aff] =>
        some { sp with stmts := before ++ [.scan nm axs b (r ++ [.assign "S" [.free ax]
          { body := ⟨[⟨[.read "Z" [.axis ax]]⟩]⟩, nonlin := .identity }]) aff] ++ after }
    | _ => none

private def scratchValidateError (before after : List ScanStmt) : Option CompileError :=
  (scratchSched before after).bind fun sp => match validateScheduled sp with
    | .error e => some e
    | .ok _ => none

private def scratchDesugarError (before after : List ScanStmt) : Option CompileError :=
  (scratchSched before after).bind fun sp => match desugarMultiWriters sp with
    | .error e => some e
    | .ok _ => none

private def plainS : ScanStmt := .plain (copyStmt "S" "A")
private def readS : ScanStmt := .plain (copyStmt "U" "S")

-- X1 sanity (donor: R4): the scratch is written, not published.
#guard match scratchSched [] [] with
  | some sp => sp.stmts.map ScanStmt.writes == [["G", "S"]] && sp.stmts.map ScanStmt.outputs == [["G", "G"]]
  | none => false
-- X2 readiness: reader of S after [plain S, scan] is NOT ready (1 publication of S, 2 writers).
#guard match scratchSched [plainS] [readS] with
  | some sp => !ordered sp.stmts
  | none => false
-- X2b accept-neighbour (clone X2, no reader): ordered.
#guard match scratchSched [plainS] [] with
  | some sp => ordered sp.stmts
  | none => false
-- X3 direct desugar, with and without the reader: `multiWriterScan`.
#guard scratchDesugarError [plainS] [readS] == some (.multiWriterScan "S")
#guard scratchDesugarError [plainS] [] == some (.multiWriterScan "S")
-- X4 validateScheduled with the reader: topology fails first, `cyclicDataflow`, not `multiWriterScan`.
#guard match scratchValidateError [plainS] [readS] with
  | some (.cyclicDataflow _) => true
  | _ => false
-- X4b accept-neighbour (clone X4, no reader): topology passes, collection rejects `multiWriterScan`.
#guard scratchValidateError [plainS] [] == some (.multiWriterScan "S")

/-! ## Route integration (`route` runs `desugarMultiWriters` before `physicalizeForRoute`)

Before this, `route` physicalized the UNCOLLECTED logical schedule, and `buildNameToStep`'s
`HashMap.insert` fold wired every reader of a multi-writer name to its LAST writer, leaving the
earlier writers as dead steps (observed on RT1 and RT2 alike: 3 steps, routing
`[[external 0], [external 1], [internal 1 0]]`, so `U` read only `B`). Now every reader is wired to
the collector, and the collector reads every private writer. The private `Y#k` steps stay in the
routed diagram (`route` hides nothing). Programs here are undeclared, i.e. default f32, except RT3. -/

private def routed (p : TLProgram) : Option (List BrOp × List (List Wire)) :=
  match p.compile.run 0 with
  | .ok tc _ => some (tc.steps.map (·.op), tc.routing)
  | .error _ _ => none

/-- Two private writers (steps 0, 1), the `.contract`-labelled sum collector (step 2) reading both,
    and the reader `U` (step 3) reading the collector. -/
private def collectedRoute : List BrOp × List (List Wire) :=
  ([.contract, .contract, .contract, .contract],
   [[.external 0], [.external 1], [.internal 0 0, .internal 1 0], [.internal 2 0]])

-- RT1 (donor: C1 plus a reader; P1's `T:=A; U:=T; T:=B` probe): the reader sits BETWEEN the writers.
def rt1 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  U[i] := Y[i]
  Y[i] := B[i]
}
#guard routed rt1 == some collectedRoute

-- RT2 (clone RT1, reader after both writers): the same diagram.
def rt2 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Y[i] := B[i]
  U[i] := Y[i]
}
#guard routed rt2 == some collectedRoute

-- RT3 (clone RT1, declare Y `tensor f64` as in C4b): the declared clones route identically.
def rt3 : TLProgram := tlprog!{
  axis i : ℕ = 2
  tensor f64 Y(i)
  Y[i] := A[i]
  U[i] := Y[i]
  Y[i] := B[i]
}
#guard routed rt3 == some collectedRoute

-- RT4 accept-neighbour (clone RT1, rename the second writer to S): one writer per name, so no
-- collector; `U` reads `Y`'s only writer.
def rt4 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  U[i] := Y[i]
  S[i] := B[i]
}
#guard routed rt4 == some ([.contract, .contract, .contract],
  [[.external 0], [.internal 0 0], [.external 1]])

-- RT5 (clone RT2, first writer ReLU): the private writer `Y#1` is itself split into the nonlinear
-- producer/consumer pair (steps 0, 1); the collector (step 3) reads the pair's consumer and `Y#2`.
def rt5 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := relu(A[i])
  Y[i] := B[i]
  U[i] := Y[i]
}
#guard routed rt5 == some ([.contract, .relu, .contract, .contract, .contract],
  [[.external 0], [.internal 0 0], [.external 1], [.internal 1 0, .internal 2 0], [.internal 3 0]])

-- RT6 (clone RT2, a third writer and a ReLU reader): the collector reads all three private writers.
def rt6 : TLProgram := tlprog!{
  axis i : ℕ = 2
  Y[i] := A[i]
  Y[i] := B[i]
  Y[i] := C[i]
  U[i] := relu(Y[i])
}
#guard routed rt6 == some ([.contract, .contract, .contract, .contract, .contract, .relu],
  [[.external 0], [.external 1], [.external 2], [.internal 0 0, .internal 1 0, .internal 2 0],
   [.internal 3 0], [.internal 4 0]])

/-! ## Pins of the scan-writer check's arms and priority (fix group 2)

The scan-scratch counting of `scanWriterConflict?` (a plain writer of recurrence-only scratch) is
pinned by X3 above. Two scans writing one state name are not constructed from surface syntax here:
`finalizeScans` was read (T4 review) to make them reachable only with distinct iteration axes and a
single declaration, and no probe was run, so C9b stays a hand-built schedule. -/

private def preTC : ThreadedComposed := { steps := [], routing := [], nExternal := 0 }

private def r4Desugar (stmts : List ScanStmt) : Option CompileError :=
  (scheduled r4).bind fun sp => match desugarMultiWriters { sp with stmts } with
    | .error e => some e
    | .ok _ => none

-- C9d the `.scanPre` arm (donor: C9): a plain writer of G plus a `scanPre` node of G.
#guard r4Desugar [.plain (copyStmt "G" "A"), .scanPre "G" ax preTC] == some (.multiWriterScan "G")
-- C9d' accept-neighbour (clone C9d, the `scanPre` node writes H): accepted.
#guard r4Desugar [.plain (copyStmt "G" "A"), .scanPre "H" ax preTC] == none

-- C9e "checked first" (donor: C9 and C5): the scatter group `S` comes first in writer order, yet the
-- scan conflict on `G` wins.
private def priorityError (scanConflict : Bool) : Option CompileError :=
  match scheduled c5, scheduled r4 with
  | some s5, some sp =>
      match desugarMultiWriters { sp with stmts :=
          s5.stmts ++ sp.stmts ++ (if scanConflict then [.plain (copyStmt "G" "A")] else []) } with
      | .error e => some e
      | .ok _ => none
  | _, _ => none
#guard priorityError true == some (.multiWriterScan "G")
-- C9e' accept-neighbour (clone C9e, no scan conflict): the scatter group's own error surfaces.
#guard priorityError false == some (.multiWriterScatter "S")

/-! ## Direct `route` on a hand-built schedule (review T6-F4)

`route` skips `collectDefinitions`' topology assertion and relies on `routeCore`'s `routableInOrder`.
RT1 cannot show that this still rejects a reader placed BEFORE the last writer of a multi-writer
name, because `compile` reorders it first. Here `route` receives the schedule directly: after
collection `U := Y` precedes the collector `Y := Y#1 + Y#2`, so it is rejected as `cyclicDataflow`
from `routeCore`. Accept-neighbour (RT2's order): the reader after the last writer routes (4 steps). -/

private def directRoute (stmts : List ScanStmt) : Except CompileError Nat :=
  match (route { c8 with extNames := {"A", "B"}, stmts }).run 7 with
  | .ok tc _ => .ok tc.steps.length
  | .error e _ => .error e

#guard match directRoute [.plain (copyStmt "Y" "A"), .plain (copyStmt "U" "Y"), .plain (copyStmt "Y" "B")] with
  | .error e => e == .cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)"
  | .ok _ => false
-- accept-neighbour (clone, reader after both writers): routes, 2 private writers + collector + reader.
#guard match directRoute [.plain (copyStmt "Y" "A"), .plain (copyStmt "Y" "B"), .plain (copyStmt "U" "Y")] with
  | .ok n => n == 4
  | .error _ => false

end LeanNCD.CollectTest

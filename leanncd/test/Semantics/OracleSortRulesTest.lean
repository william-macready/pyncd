import Semantics.OracleSortRules

/-! Oracle sorts T1: SOURCE and SHAPED agreement corpora for the independent rule predictor.

Every corpus program is run through the real pipeline (`productionVerdict`) and through the
independent predictor (`predict`); `agrees` must hold for all of them.
New B5 candidates additionally reach concrete preparation with actual input signatures.

* C1: pairs and triples of writers over one tensor `Y` (the vote / neutrality / scatter rules).
* C2: reader programs (the cast rules), plus the laundered pair and group readers.
* C3: hand rows, each with the OBSERVED production verdict (and, where stated, the sort each
  statement runs in, which is the predictor's own claim: production publishes no per-statement sort).
* C4: self-checks that the corpora are not vacuous (every claimed distinction has an entry that
  exercises it). -/

open Lean Elab Command
open LeanNCD LeanNCD.PropertyOracle LeanNCD.OracleSorts

namespace OracleSortRulesTest

private def a : AxisSpec := ⟨"a", 1, .nat⟩
private def b : AxisSpec := ⟨"b", 2, .nat⟩
private def c : AxisSpec := ⟨"c", 3, .nat⟩

private def rhs (ag : AggOp) (nl : Nonlin) (terms : List (List Factor)) : RHSExpr :=
  ⟨⟨terms.map ProdTerm.mk⟩, nl, ag⟩

private def rd (n : String) (axes : List AxisSpec) : Factor := .read n (axes.map .axis)

/-- A bare-index neutral copy `dst[a] := agg src[a]` (a one-read, uncontracted statement). -/
private def cp (dst : String) (ag : AggOp) (src : String) : Stmt :=
  .assign dst [.free a] (rhs ag .identity [[rd src [a]]])

/-- A contracted statement `dst[a] := agg src[a, b]` (not sort-neutral). -/
private def ct (dst : String) (ag : AggOp) (src : String) : Stmt :=
  .assign dst [.free a] (rhs ag .identity [[rd src [a, b]]])

private def maxS : MSort := .maxPlus
private def minS : MSort := .minPlus

/-- Fail loudly, naming each offender. -/
private def assertNone (what : String) (fs : List String) : CommandElabM Unit :=
  unless fs.isEmpty do throwError "{what}: {fs}"

private def tag : Except (String × String) (List (String × MSort)) → String
  | .error e => e.1
  | .ok _ => "accepted"

private def histogram (xs : List String) : List (String × Nat) :=
  xs.foldl (fun acc x =>
    if acc.any (·.1 == x) then acc.map (fun p => if p.1 == x then (p.1, p.2 + 1) else p)
    else acc ++ [(x, 1)]) []

/-! ### C1: writer pairs and triples over one tensor -/

/-- Declarations for C1: inputs `X[a]`, `Z[a,b]`, `Q3[a,b,c]`; the shared destination `Y[a]`. -/
private def c1Decls : List Decl :=
  [.axis a (some 4), .axis b (some 3), .axis c (some 2),
   .typedTensor .f64 "X" [a], .typedTensor .f64 "Z" [a, b], .typedTensor .f64 "Q3" [a, b, c],
   .typedTensor .f64 "Y" [a]]

/-- The 7 writer shapes of C1, each over the one tensor `Y`:
    0 bare copy, 1 contracted copy, 2 relu copy, 3 Iverson-only copy, 4 colliding slot `Y[a+b]`,
    5 affine single-axis slot `Y[2a+1]`, 6 bare contracted two-axis copy. -/
private def writer : Nat → AggOp → Stmt
  | 0, ag => .assign "Y" [.free a] (rhs ag .identity [[rd "X" [a]]])
  | 1, ag => .assign "Y" [.free a] (rhs ag .identity [[rd "Z" [a, b]]])
  | 2, ag => .assign "Y" [.free a] (rhs ag (.pointwise .relu) [[rd "X" [a]]])
  | 3, ag => .assign "Y" [.free a]
      (rhs ag .identity [[.iverson (.rel .lt (.embed (.axis a)) (.embed (.const 2)))]])
  | 4, ag => .assign "Y" [.affine (.affine 0 [(1, a), (1, b)])] (rhs ag .identity [[rd "Z" [a, b]]])
  | 5, ag => .assign "Y" [.affine (.affine 1 [(2, a)])] (rhs ag .identity [[rd "X" [a]]])
  | _, ag => .assign "Y" [.free a] (rhs ag .identity [[rd "Q3" [a, b, c]]])

private def writers21 : List Stmt :=
  (List.range 7).flatMap (fun s => [AggOp.sum, .max, .min].map (writer s))

private def writers4 : List Stmt :=
  [writer 1 .sum, writer 0 .max, writer 0 .min, writer 1 .max]

private def pairsC1 : List (List Stmt) :=
  writers21.flatMap (fun w1 => writers21.map (fun w2 => [w1, w2]))

private def triplesC1 : List (List Stmt) :=
  writers4.flatMap (fun w1 => writers4.flatMap (fun w2 => writers4.map (fun w3 => [w1, w2, w3])))

/-- C1: all 441 ordered pairs of the 21 writers plus the 64 ordered triples of `writers4`. -/
private def corpusC1 : List (List Stmt) := pairsC1 ++ triplesC1

#guard writers21.length == 21
#guard pairsC1.length == 441
#guard triplesC1.length == 64

private def disagreements (decls : List Decl) (corpus : List (List Stmt)) : List String :=
  (corpus.zipIdx.filter (fun (ss, _) =>
      !agrees (predict decls ss) (productionVerdict decls ss))).map
    (fun (ss, i) => s!"#{i}: production {tag (productionVerdict decls ss)}, predicted \
      {(predict decls ss).refusals.map (·.1)}")

run_cmd assertNone "C1 predictor/production disagreements" (disagreements c1Decls corpusC1)

/-- How many refusals the predictor names for a C1 program. -/
private def refusalsOf (ss : List Stmt) : Nat := (predict c1Decls ss).refusals.length

-- SOURCE-stage counts only: an empty refusal list does not imply concrete shape acceptance.
-- The first two are the STRICT class (`agreesStrict`: the constructor must equal the
-- single predicted one, and an accepted program must publish the predicted sorts). The last is the
-- MULTI class (`agreesMember`: the observed constructor is among the predicted ones). A spurious EXTRA
-- predicted refusal inside a multi-refusal program is NOT detected (see `agreesMember`); each rule's
-- refusal is pinned by equality on strict programs instead (coverage guard in C4).
#guard [(corpusC1.filter (refusalsOf · == 0)).length,
  (corpusC1.filter (refusalsOf · == 1)).length,
  (corpusC1.filter (refusalsOf · ≥ 2)).length] == [222, 195, 88]

/-- Each program is held to the predicate of its own class, so a strict-class program cannot hide
    behind membership. -/
private def classDisagreements (decls : List Decl) (corpus : List (List Stmt)) : List String :=
  corpus.zipIdx.filterMap (fun (ss, i) =>
    let p := predict decls ss
    let v := productionVerdict decls ss
    if p.refusals.length ≤ 1 then
      if agreesStrict p v then none
      else some s!"#{i}: strict class, production {tag v}, predicted {p.refusals.map (·.1)}"
    else
      if agreesMember p v then none
      else some s!"#{i}: multi class, production {tag v}, predicted {p.refusals.map (·.1)}")

run_cmd assertNone "C1 class-specific disagreements" (classDisagreements c1Decls corpusC1)

-- The two predicates are not interchangeable: membership accepts a wrong constructor only when there
-- are several predicted refusals, and the strict predicate rejects a multi prediction outright.
#guard corpusC1.any (fun ss =>
  let p := predict c1Decls ss
  let v := productionVerdict c1Decls ss
  p.refusals.length == 1 && agreesStrict p v && !agreesMember p v &&
  !agreesStrict { p with refusals := [("sortCastUnsupported", "Y")] } v)
#guard corpusC1.any (fun ss =>
  let p := predict c1Decls ss
  p.refusals.length ≥ 2 && agreesMember p (productionVerdict c1Decls ss) &&
  !agreesStrict p (productionVerdict c1Decls ss) &&
  !agreesMember { p with refusals := [("sortCastUnsupported", "Y"), ("sortCastUnsupported", "Z")] }
    (productionVerdict c1Decls ss))

/-! ### Shared declarations for C2 and C3 -/

/-- Inputs `X[a]`, `Z[a,b]`, `Q[a,b]` and predicate input `P[a]`; every other name is a tensor
    `[a]` that a program may write; `OP` is a predicate destination. -/
private def hDecls : List Decl :=
  [.axis a (some 4), .axis b (some 3),
   .typedTensor .f64 "X" [a], .typedTensor .f64 "Z" [a, b], .typedTensor .f64 "Q" [a, b],
   .predicate "P" [a], .predicate "OP" [a]] ++
  ["M", "N", "R", "T", "O", "Y", "S"].map (fun n => .typedTensor .f64 n [a])

/-! ### C2: readers (the cast rules) -/

/-- Source sorts: real input, max-plus defined, min-plus defined, predicate input. -/
private def c2Sources : List (String × List Stmt) :=
  [("X", []), ("M", [ct "M" .max "Z"]), ("N", [ct "N" .min "Z"]), ("P", [])]

/-- Readers: sum, max, min, predicate destination (each one bare read of the source). -/
private def c2Reader (src : String) : List Stmt :=
  [cp "O" .sum src, cp "O" .max src, cp "O" .min src, cp "OP" .sum src]

/-- The 16 one-read programs: source (row) x reader (column). -/
private def corpusC2 : List (List Stmt) :=
  c2Sources.flatMap (fun (src, defs) => (c2Reader src).map (fun r => defs ++ [r]))

/-- Expected refusal by hand (spec, decision A): a tropical source may be read only by a real
    statement or a statement of its own sort; never by the other tropical sort or a predicate. -/
private def c2Refused : List (List Bool) :=
  [[false, false, false, false],   -- real input
   [false, false, true, true],     -- max-plus
   [false, true, false, true],     -- min-plus
   [false, false, false, false]]   -- predicate input

#guard corpusC2.length == 16

run_cmd assertNone "C2 predictor/production disagreements" (disagreements hDecls corpusC2)

private def c2PinProblems : List String :=
  ((c2Refused.flatten.zip (corpusC2.map (fun ss => tag (productionVerdict hDecls ss)))).zipIdx.filterMap
    (fun ((refused, t), i) =>
      if t == (if refused then "sortCastUnsupported" else "accepted") then none
      else some s!"cell {i}: refused={refused}, production {t}"))

run_cmd assertNone "C2 pinned verdicts" c2PinProblems

/-! ### Rows: a program, the observed (tropical-entry) verdict, optionally the sort each statement
runs in. -/

private structure Row where
  label : String
  stmts : List Stmt
  /-- Observed production verdict, TROPICAL entries only (production also publishes `real` entries for
      single-writer tensors; `agrees` compares those against the full verdict, not against this field). -/
  expect : Except (String × String) (List (String × MSort))
  /-- The sort each input statement runs in (the predictor's claim; not observable at the pipeline). -/
  runs : Option (List MSort) := none

private def tropicalOf (v : Except (String × String) (List (String × MSort))) :
    Except (String × String) (List (String × MSort)) :=
  match v with
  | .ok m => .ok (m.filter (fun p => p.2.isTropical))
  | .error e => .error e

private def sameVerdict (x y : Except (String × String) (List (String × MSort))) : Bool :=
  match x, y with
  | .ok m, .ok n => m.all (n.contains ·) && n.all (m.contains ·)
  | .error e, .error f => e.1 == f.1 && e.2 == f.2
  | _, _ => false

private def rowProblems (decls : List Decl) (r : Row) : List String :=
  let v := productionVerdict decls r.stmts
  let p := predict decls r.stmts
  (if sameVerdict (tropicalOf v) r.expect then [] else [s!"{r.label}: production verdict differs"]) ++
  (if agrees p v then [] else [s!"{r.label}: predictor disagrees with production"]) ++
  (match r.expect with
   | .error e => if p.refusals == [e] then [] else [s!"{r.label}: predicted refusals {repr p.refusals}"]
   | .ok _ => if p.refusals.isEmpty then [] else [s!"{r.label}: predicted refusals {repr p.refusals}"]) ++
  (match r.runs with
   | some s => if p.stmtSorts == s then [] else [s!"{r.label}: statements run in {repr p.stmtSorts}"]
   | none => [])

private def rowsProblems (rows : List Row) : List String :=
  rows.flatMap (rowProblems hDecls)

/-! ### C2 extras: laundered pair, group readers -/

private def c2Rows : List Row :=
  [ { label := "direct max-plus -> min-plus cast is refused (decision A)"
      stmts := [ct "M" .max "Z", cp "O" .min "M"], expect := .error ("sortCastUnsupported", "O") }
  , { label := "laundered through one real copy: accepted"
      stmts := [ct "M" .max "Z", cp "R" .sum "M", cp "O" .min "R"]
      expect := .ok [("M", maxS), ("O", minS)], runs := some [maxS, .real, minS] }
  -- readers of a max-plus group (two max writers)
  , { label := "min reader of a max group: refused"
      stmts := [ct "Y" .max "Z", cp "Y" .max "X", cp "O" .min "Y"]
      expect := .error ("sortCastUnsupported", "O") }
  , { label := "max reader of a max group"
      stmts := [ct "Y" .max "Z", cp "Y" .max "X", cp "O" .max "Y"]
      expect := .ok [("Y", maxS), ("O", maxS)] }
  , { label := "sum reader of a max group"
      stmts := [ct "Y" .max "Z", cp "Y" .max "X", cp "O" .sum "Y"]
      expect := .ok [("Y", maxS)] }
  -- readers of a real group (no entry): any reader accepted
  , { label := "max reader of a real group"
      stmts := [ct "Y" .sum "Z", cp "Y" .sum "X", cp "O" .max "Y"]
      expect := .ok [("O", maxS)] }
  , { label := "min reader of a real group"
      stmts := [ct "Y" .sum "Z", cp "Y" .sum "X", cp "O" .min "Y"]
      expect := .ok [("O", minS)] }
  -- reader of a conflicting group: the group has no entry, so only the vote conflict is raised
  , { label := "min reader of a conflicting group"
      stmts := [ct "Y" .sum "Z", ct "Y" .max "Q", cp "O" .min "Y"]
      expect := .error ("multiWriterAlgebra", "Y") } ]

run_cmd assertNone "C2 extras" (rowsProblems c2Rows)

/-! ### C3: hand rows with observed production verdicts -/

private def c3Rows : List Row :=
  [ -- R11: a neutral copy beside a contracted writer abstains; the group takes the contracted sort
    { label := "R11 sum contraction + neutral max copy"
      stmts := [ct "Y" .sum "Z", cp "Y" .max "X"], expect := .ok [], runs := some [.real, .real] }
  , { label := "R11 neutral max copy + sum contraction"
      stmts := [cp "Y" .max "X", ct "Y" .sum "Z"], expect := .ok [], runs := some [.real, .real] }
  , { label := "R11 max contraction + neutral sum copy"
      stmts := [ct "Y" .max "Z", cp "Y" .sum "X"], expect := .ok [("Y", maxS)]
      runs := some [maxS, maxS] }
  , { label := "R11 neutral sum copy + max contraction"
      stmts := [cp "Y" .sum "X", ct "Y" .max "Z"], expect := .ok [("Y", maxS)]
      runs := some [maxS, maxS] }
  -- a neutral copy whose annotation disagrees with the group runs in the group's sort
  , { label := "min copy beside a max contraction runs as max (bellman .max .min)"
      stmts := [ct "Y" .max "Z", cp "Y" .min "X"], expect := .ok [("Y", maxS)]
      runs := some [maxS, maxS] }
  , { label := "min copy beside a sum contraction runs as sum"
      stmts := [ct "Y" .sum "Z", cp "Y" .min "X"], expect := .ok [], runs := some [.real, .real] }
  , { label := "all-neutral group: sum copy abstains, max copy votes"
      stmts := [cp "Y" .sum "X", cp "Y" .max "X"], expect := .ok [("Y", maxS)]
      runs := some [maxS, maxS] }
  -- R16: two non-neutral voters that disagree
  , { label := "R16 sum vs max contractions"
      stmts := [ct "Y" .sum "Z", ct "Y" .max "Q"], expect := .error ("multiWriterAlgebra", "Y") }
  , { label := "R16 max vs min contractions"
      stmts := [ct "Y" .max "Z", ct "Y" .min "Q"], expect := .error ("multiWriterAlgebra", "Y") }
  -- R10: an all-neutral max + min group over a min-plus `N`; the vote conflict, in both orders
  , { label := "R10 max writer first"
      stmts := [ct "N" .min "Z", cp "T" .max "N", cp "T" .min "X"]
      expect := .error ("multiWriterAlgebra", "T") }
  , { label := "R10 min writer first"
      stmts := [ct "N" .min "Z", cp "T" .min "X", cp "T" .max "N"]
      expect := .error ("multiWriterAlgebra", "T") }
  , { label := "R10 shape with a NON-neutral min writer is accepted (the neutral max copy abstains)"
      stmts := [ct "N" .min "Z", cp "T" .max "N", ct "T" .min "Q"]
      expect := .ok [("N", minS), ("T", minS)] }
  -- a single neutral writer keeps its OWN annotation
  , { label := "single neutral max copy read by a min statement"
      stmts := [cp "T" .max "X", cp "O" .min "T"], expect := .error ("sortCastUnsupported", "O") }
  , { label := "single neutral max copy read by a sum statement"
      stmts := [cp "T" .max "X", cp "O" .sum "T"], expect := .ok [("T", maxS)]
      runs := some [maxS, .real] }
  , { label := "single neutral max copy read by a max statement"
      stmts := [cp "T" .max "X", cp "O" .max "T"], expect := .ok [("T", maxS), ("O", maxS)] }
  -- D7: scatters and non-bare slots in a multi-writer group
  , { label := "plain writer + scatter writer"
      stmts := [ct "Y" .max "Z", .scatter "Y" [.free a] (rhs .max .identity [[rd "Q" [a, b]]])]
      expect := .ok [("Y", maxS)], runs := some [maxS, maxS] }
  , { label := "two affine writers"
      stmts := [writer 5 .max, writer 5 .max], expect := .ok [("Y", maxS)]
      runs := some [maxS, maxS] }
  , { label := "affine writer + bare writer"
      stmts := [writer 5 .max, writer 0 .max], expect := .ok [("Y", maxS)]
      runs := some [maxS, maxS] }
  -- tropical statements take no nonlinearity
  , { label := "relu on a max statement"
      stmts := [.assign "Y" [.free a] (rhs .max (.pointwise .relu) [[rd "X" [a]]])]
      expect := .error ("tropicalNonlin", "Y") } ]

run_cmd assertNone "C3 hand rows" (rowsProblems c3Rows)
#guard c3Rows.length == 19

/-! Supplemental rows use rank-correct declarations without expanding C1's writer product. -/

private def matrixA : AxisSpec := { a with kind := .real }
private def matrixB : AxisSpec := { b with kind := .real }

private def matrixDecls (second : AxisSpec) : List Decl :=
  [.axis matrixA (some 4), .axis second (some 3),
   .typedTensor .f64 "Z" [matrixA, second], .typedTensor .f64 "Y" [matrixA, second]]

private def matrixWriters (slots : List LHSSlot) (second : AxisSpec) : List Stmt :=
  List.replicate 2 (.assign "Y" slots (rhs .sum .identity [[rd "Z" [matrixA, second]]]))

private def sameNameB : AxisSpec := { matrixB with name := matrixA.name }

private def supplementalRows : List (List Decl × Row) :=
  [ (matrixDecls matrixB,
      { label := "duplicate free UID makes diagonal Y[a,a] a scatter"
        stmts := matrixWriters [.free matrixA, .free matrixA] matrixB
        expect := .ok [], runs := some [.real, .real] })
  , (matrixDecls matrixB,
      { label := "free/freeNorm duplicate UID also makes a scatter"
        stmts := matrixWriters [.free matrixA, .freeNorm matrixA] matrixB
        expect := .ok [], runs := some [.real, .real] })
  , (matrixDecls matrixB,
      { label := "distinct bare UIDs Y[a,b] remain legal"
        stmts := matrixWriters [.free matrixA, .free matrixB] matrixB
        expect := .ok [], runs := some [.real, .real] })
  , ((matrixDecls matrixB).map (fun
        | .typedTensor t "Y" _ => .typedTensor t "Y" [matrixA, matrixA]
        | d => d),
      { label := "declared repeated collector UID is refused"
        stmts := matrixWriters [.free matrixA, .free matrixA] matrixB
        expect := .error ("multiWriterRepeatedBasis", "Y") })
  , (hDecls.filter (fun d => d.name != "Y"),
      { label := "undeclared allscatter needs a declared basis"
        stmts := List.replicate 2 (.scatter "Y" [.free a] (rhs .sum .identity [[rd "X" [a]]]))
        expect := .error ("multiWriterNeedsDeclaredShape", "Y") })
  , (hDecls.filter (fun d => d.name != "Y"),
      { label := "ordinary bare assignment supplies undeclared fallback"
        stmts := [.scatter "Y" [.free a] (rhs .sum .identity [[rd "X" [a]]]), cp "Y" .sum "X"]
        expect := .ok [], runs := some [.real, .real] })
  , (hDecls,
      { label := "explicit constant scatter groups remain unsupported"
        stmts := List.replicate 2 (.scatter "Y" [.affine (.const 3)]
          (rhs .sum .identity [[rd "X" [a]]]))
        expect := .error ("multiWriterScatter", "Y") })
  , (hDecls,
      { label := "canceled multi-axis syntax is bounded after UID normalization"
        stmts := List.replicate 2 (.scatter "Y"
          [.affine (.affine 1 [(3, a), (-1, a), (1, b), (-1, b)])]
          (rhs .max .identity [[rd "X" [a]]]))
        expect := .ok [("Y", maxS)], runs := some [maxS, maxS] })
  , (hDecls,
      { label := "predicate scatter groups remain unsupported"
        stmts := List.replicate 2 (.scatter "OP" [.free a]
          (rhs .sum .identity [[rd "X" [a]]]))
        expect := .error ("multiWriterScatter", "OP") })
  -- The structural gate requires sum on predicate outputs; their running sort is still bool.
  , (hDecls,
      { label := "predicate contractions run in bool rather than annotation real"
        stmts := [ct "OP" .sum "Z", ct "OP" .sum "Q"]
        expect := .ok [], runs := some [.bool, .bool] })
  , (hDecls,
      { label := "predicate neutral writers also run in bool rather than annotation real"
        stmts := [cp "OP" .sum "X", cp "OP" .sum "X"]
        expect := .ok [], runs := some [.bool, .bool] })
  , (hDecls,
      { label := "tropical source into predicate multi-writer group is refused"
        stmts := [ct "M" .max "Z", cp "OP" .sum "M", cp "OP" .sum "X"]
        expect := .error ("sortCastUnsupported", "OP"), runs := some [maxS, .bool, .bool] })
  , (hDecls,
      { label := "real source into predicate multi-writer group is accepted"
        stmts := [ct "M" .sum "Z", cp "OP" .sum "M", cp "OP" .sum "X"]
        expect := .ok [], runs := some [.real, .bool, .bool] }) ]

run_cmd assertNone "supplemental hand rows" <|
  (supplementalRows.flatMap (fun (d, r) => rowProblems d r))

#guard (productionVerdict hDecls [ct "OP" .sum "Z", ct "OP" .sum "Q"]).toOption.any
  (·.contains ("OP", .bool))
#guard (productionVerdict hDecls [cp "OP" .sum "X", cp "OP" .sum "X"]).toOption.any
  (·.contains ("OP", .bool))

-- A predictor-only identity control: source compilation re-resolves printable axis names.
#guard (predict (matrixDecls sameNameB)
  (matrixWriters [.free matrixA, .freeNorm sameNameB] sameNameB)).refusals.isEmpty

/-! SHAPED rows are explicitly separate from the SOURCE corpora. Concrete external signatures
    come from each row's real input declarations, not from compiler inference. -/

private def sizesOf (ds : List Decl) : List (UID × Nat) :=
  ds.filterMap (fun | .axis ax (some n) => some (ax.uid, n) | .iter ax n => some (ax.uid, n) | _ => none)

private def signatureOf (ds : List Decl) (ss : List Stmt) : Eval.Plan.InputSignature :=
  let written := ss.filterMap (fun
    | .assign n .. | .scatter n .. => some n
    | _ => none)
  let sizes := sizesOf ds
  let entries := ds.filterMap fun d =>
    let entry := match d with
      | .typedTensor _ n ax | .tensor n ax => some (n, ax, Eval.Plan.ScalarDType.f64)
      | .predicate n ax => some (n, ax, Eval.Plan.ScalarDType.bool)
      | _ => none
    entry.bind fun (n, ax, dt) =>
      if written.contains n then none else
      some (n, ({ shape := (ax.map (fun x =>
        ((sizes.find? (·.1 == x.uid)).map (·.2)).getD 0)).toArray, dtype := dt } :
          Eval.Plan.TensorSignature))
  ⟨Std.HashMap.ofList entries⟩

private def shapedProblems (label : String) (ds : List Decl) (ss : List Stmt) : List String :=
  let p := predictShaped ds ss (sizesOf ds)
  let v := productionShapedVerdict ds ss (signatureOf ds ss)
  if agreesShaped p v then [] else [s!"{label}: predicted {repr p.refusals}, observed {repr v}"]

/-- Stage only newly admitted B5 candidates, not legacy allbare/singlewriter corpus rows.
    All 81 candidates were observed to reach inference, including relu/Iverson neighbours. -/
private def concreteC1 : List (List Stmt) :=
  corpusC1.filter fun ss =>
    (predict c1Decls ss).refusals.isEmpty &&
    ss.any (fun s => [AggOp.sum, .max, .min].any (fun ag => s == writer 5 ag))

run_cmd assertNone "C1 SHAPED disagreements" <|
  (concreteC1.zipIdx.flatMap fun (ss, i) => shapedProblems s!"C1#{i}" c1Decls ss)

private def k : AxisSpec := ⟨"k", 44, .nat⟩
private def extent8Decls : List Decl :=
  .axis k (some 8) :: hDecls.map (fun
    | .typedTensor t "Y" _ => .typedTensor t "Y" [k]
    | d => d)
-- Pinned box 12 holds the realized extent 8 of both writers; the bare writer spans the whole box.
private def box12Decls : List Decl :=
  .axis k (some 12) :: hDecls.map (fun
    | .typedTensor t "Y" _ => .typedTensor t "Y" [k]
    | d => d)
-- The same destination pinned through an `iter` declaration: a box of 12 holds the extent 8, a box
-- of 4 does not.
private def iterBoxDecls (n : Nat) : List Decl :=
  .iter k n :: hDecls.map (fun
    | .typedTensor t "Y" _ => .typedTensor t "Y" [k]
    | d => d)
private def squareDecls : List Decl :=
  (matrixDecls matrixB).map (fun
    | .axis ax _ => .axis ax (some 4)
    | d => d)

private def stagedRows : List (String × List Decl × List Stmt) :=
  (c3Rows.filter (fun r => ["plain writer + scatter writer", "two affine writers",
    "affine writer + bare writer"].contains r.label)).map (fun r => (r.label, hDecls, r.stmts)) ++
  [("two affine box12", box12Decls, [writer 5 .max, writer 5 .max]),
   ("affine/bare box12", box12Decls,
     [writer 5 .max, .assign "Y" [.free k] (rhs .max .identity [[rd "X" [a]]])]),
   ("two affine iter box12", iterBoxDecls 12, [writer 5 .max, writer 5 .max]),
   ("two affine iter box4", iterBoxDecls 4, [writer 5 .max, writer 5 .max]),
   ("two affine extent8 twin", extent8Decls, [writer 5 .max, writer 5 .max]),
   ("affine/bare extent8 twin", extent8Decls,
     [writer 5 .max, .assign "Y" [.free k] (rhs .max .identity [[rd "X" [a]]])])] ++
  [false, true].flatMap (fun norm =>
    let ss := matrixWriters [.free matrixA, if norm then .freeNorm matrixA else .free matrixA] matrixB
    -- Identity statements cannot carry a normalization marker. De-mark the second donor's twin.
    let square := matrixWriters [.free matrixA, .free matrixA] matrixB
    [(s!"diagonal rectangular donor {norm}", matrixDecls matrixB, ss),
     (s!"diagonal square twin {norm}", squareDecls, square)])

run_cmd assertNone "hand SHAPED disagreements" (stagedRows.flatMap fun (l, ds, ss) =>
  shapedProblems l ds ss)

-- Thirteen hand rows: eight shape accepts (two box12, the iter box12, two extent8 twins, two square
-- twins, the max-plus plain+scatter row) and five refusals (two exceed-box affine rows, the iter
-- box4 row, two rectangular diagonals).
#guard stagedRows.length == 13
#guard (stagedRows.filter fun (_, ds, ss) =>
  (predictShaped ds ss (sizesOf ds)).refusals.isEmpty).length == 8

#guard concreteC1.length == 81
-- C1 declares extent 4 against realized extent 8, so no candidate fits the pinned box: all 81 stay
-- refused, now by the box rule itself rather than by a scatter-output `sizeConflict`.
#guard histogram (concreteC1.map (fun ss =>
  tag (productionShapedVerdict c1Decls ss (signatureOf c1Decls ss)))) ==
    [("writerExtentExceedsBox", 81)]
#eval
  let containsShape (shape : Nat) (ss : List Stmt) :=
    ss.any (fun s => [AggOp.sum, .max, .min].any (fun ag => s == writer shape ag))
  [(corpusC1.filter (fun ss => containsShape 4 ss || containsShape 5 ss)).length,
   (corpusC1.filter (containsShape 4)).length,
   (corpusC1.filter (fun ss => containsShape 5 ss && !containsShape 4 ss)).length]
#eval stagedRows.map (fun (l, ds, ss) =>
  (l, (predictShaped ds ss (sizesOf ds)).refusals,
    productionShapedVerdict ds ss (signatureOf ds ss)))

/-- This donor passes B5 geometry and shape but retains its independent, pre-existing marker
    refusal. Do not call a shape-only prediction a full preparation-acceptance prediction. -/
private def markedSquare := matrixWriters [.free matrixA, .freeNorm matrixA] matrixB
#guard (predictShaped squareDecls markedSquare (sizesOf squareDecls)).refusals.isEmpty
#guard productionShapedVerdict squareDecls markedSquare (signatureOf squareDecls markedSquare) ==
  .error ("unmodelled nonlin: LeanNCD.Eval.Plan.NonlinCompileError.unmarkedReductionAxis \"Y#1\" 1", "")

-- Stride alignment, normalization and raw-axis sizing are independent of production's formula.
#eval [predictedExtent (.affine (.affine 1 [(2, a)])) [(a.uid, 4)],
  predictedExtent (.affine (.affine 3 [(2, a)])) [(a.uid, 4)],
  predictedExtent (.affine (.affine 1 [(3, a), (-1, a), (0, b)])) [(a.uid, 4), (b.uid, 3)],
  predictedExtent (.affine (.affine 1 [(3, a), (-1, a), (0, b)])) [(a.uid, 4)],
  predictedExtent (.affine (.scale 0 a)) [(a.uid, 4)]]
#guard predictedExtent (.affine (.affine 1 [(2, a)])) [(a.uid, 4)] == some 8
#guard predictedExtent (.affine (.affine 3 [(2, a)])) [(a.uid, 4)] == some 10
#guard predictedExtent (.affine (.affine 1 [(3, a), (-1, a), (0, b)]))
  [(a.uid, 4), (b.uid, 3)] == some 8
#guard predictedExtent (.affine (.affine 1 [(3, a), (-1, a), (0, b)]))
  [(a.uid, 4)] == none
#guard predictedExtent (.affine (.scale 0 a)) [(a.uid, 4)] == some 0
#guard (predict hDecls (List.replicate 2 (.scatter "Y" [.affine (.scale 0 a)]
  (rhs .sum .identity [[rd "X" [a]]])))).refusals.isEmpty

/-! ### C4: the corpora are not vacuous -/

private def aggOf : Stmt → AggOp
  | .assign _ _ r | .scatter _ _ r => r.agg
  | .recurMorphism .. => .sum

private def nonlinOf : Stmt → Nonlin
  | .assign _ _ r | .scatter _ _ r => r.nonlin
  | .recurMorphism .. => .identity

private def isTropicalAgg (ag : AggOp) : Bool := ag != .sum

private def isRelu (s : Stmt) : Bool := nonlinOf s == .pointwise .relu

private def hasYSort (v : Except (String × String) (List (String × MSort))) (s : MSort) : Bool :=
  match v with
  | .ok m => m.contains ("Y", s)
  | .error _ => false

private def verdictC1 (ss : List Stmt) := productionVerdict c1Decls ss

/-- Every (decls, program) pair in every corpus. -/
private def everything : List (List Decl × List Stmt) :=
  corpusC1.map (c1Decls, ·) ++ corpusC2.map (hDecls, ·) ++ c2Rows.map (hDecls, ·.stmts) ++
  c3Rows.map (hDecls, ·.stmts) ++ supplementalRows.map (fun (d, r) => (d, r.stmts))

private def modelled : List String :=
  ["accepted", "multiWriterAlgebra", "multiWriterScatter", "multiWriterNeedsDeclaredShape",
   "multiWriterRepeatedBasis", "tropicalNonlin", "sortCastUnsupported"]

private def observedTags : List String :=
  (everything.map (fun (d, ss) => tag (productionVerdict d ss))).eraseDups

-- A production refusal the predictor does not model fails loudly, naming it (never skipped).
private def unmodelledTags : List String := observedTags.filter (fun t => !modelled.contains t)

run_cmd assertNone "production constructors the predictor does not model" unmodelledTags

-- Coverage of the strict class. Over-prediction inside a multi-refusal program is undetectable
-- (`agreesMember`), so each modelled refusal must be observed as production's ACTUAL error on at least
-- one STRICT program (at most one predicted refusal), where `agreesStrict` pins the constructor by
-- equality. The strict programs are drawn from every corpus: C1 holds the vote, scatter and
-- nonlinearity refusals; the cast refusal only occurs in C2 / C2 extras / C3, which therefore count
-- as strict here (each of their programs predicts at most one refusal, checked below).
private def strictPrograms : List (List Decl × List Stmt) :=
  everything.filter (fun (d, ss) => (predict d ss).refusals.length ≤ 1)

private def strictFailures : List String :=
  (strictPrograms.filter (fun (d, ss) =>
      !agreesStrict (predict d ss) (productionVerdict d ss))).map (fun (_, ss) => s!"{ss.length} stmts")

run_cmd assertNone "strict programs that do not satisfy agreesStrict" strictFailures

-- Every C2, C2-extras and C3 program is strict: the cast refusal's coverage may rely on them.
#guard (corpusC2.map (hDecls, ·) ++ c2Rows.map (hDecls, ·.stmts) ++ c3Rows.map (hDecls, ·.stmts)).all
  (fun (d, ss) => (predict d ss).refusals.length ≤ 1)
#guard supplementalRows.all (fun (d, r) => (predict d r.stmts).refusals.length ≤ 1)

private def uncoveredStrict : List String :=
  (modelled.filter (· != "accepted")).filter (fun k =>
    !strictPrograms.any (fun (d, ss) => tag (productionVerdict d ss) == k))

run_cmd assertNone "modelled refusal constructors never observed on a strict program" uncoveredStrict

-- C1's strict programs alone cover the vote, scatter and nonlinearity refusals; only the cast refusal
-- needs C2 / C3 (C1's writers read inputs only).
private def strictC1Tags : List String :=
  ((corpusC1.filter (fun ss => refusalsOf ss ≤ 1)).map (fun ss => tag (productionVerdict c1Decls ss))).eraseDups

#guard ["multiWriterAlgebra", "multiWriterScatter", "tropicalNonlin"].all strictC1Tags.contains

-- An accepted REAL group with a neutral tropical copy (the copy abstains).
#guard corpusC1.any (fun ss =>
  (verdictC1 ss).toOption.isSome && !(hasYSort (verdictC1 ss) maxS) && !(hasYSort (verdictC1 ss) minS) &&
  ss.any (fun s => oracleNeutral s && isTropicalAgg (aggOf s)))
-- An accepted all-neutral max-plus group, and an accepted all-neutral min-plus group.
#guard corpusC1.any (fun ss => ss.all oracleNeutral && hasYSort (verdictC1 ss) maxS)
#guard corpusC1.any (fun ss => ss.all oracleNeutral && hasYSort (verdictC1 ss) minS)
-- A vote conflict between two contracted non-neutral writers.
#guard pairsC1.any (fun ss =>
  ss.all (fun s => !oracleNeutral s) && tag (verdictC1 ss) == "multiWriterAlgebra" &&
  ss.any (fun s => aggOf s == .sum) && ss.any (fun s => aggOf s == .max))
-- A vote conflict that exists ONLY because contraction makes a writer vote: the same pair with
-- the contracted writer replaced by its neutral copy is accepted.
#guard pairsC1.any (fun ss => ss == [writer 1 .sum, writer 0 .max] && tag (verdictC1 ss) == "accepted") &&
  pairsC1.any (fun ss => ss == [writer 1 .sum, writer 1 .max] && tag (verdictC1 ss) == "multiWriterAlgebra")
-- A relu x max pair (tropicalNonlin) and a colliding-slot pair (multiWriterScatter).
#guard pairsC1.any (fun ss =>
  ss.any (fun s => isRelu s && aggOf s == .max) && tag (verdictC1 ss) == "tropicalNonlin")
#guard pairsC1.any (fun ss =>
  ss.any (fun s => s == writer 4 .max) && tag (verdictC1 ss) == "multiWriterScatter")
-- Both orders of the same pair occur (order never matters to the predictor).
#guard pairsC1.any (fun ss => ss == [writer 0 .max, writer 0 .min] &&
    tag (verdictC1 ss) == "multiWriterAlgebra") &&
  pairsC1.any (fun ss => ss == [writer 0 .min, writer 0 .max] &&
    tag (verdictC1 ss) == "multiWriterAlgebra")

private def acceptedWith (f : List (String × MSort) → Bool) : Bool :=
  everything.any (fun (d, ss) => match productionVerdict d ss with
    | .ok m => f m
    | .error _ => false)

-- `agrees` compares real entries too: some accepted program publishes one, and a prediction with that
-- sort changed to bool no longer agrees.
#guard acceptedWith (fun m => m.any (fun p => p.2 == .real))
#guard everything.any (fun (d, ss) =>
  match productionVerdict d ss with
  | .ok m =>
    m.any (fun p => p.2 == .real) &&
    !agrees { predict d ss with
              sorts := (predict d ss).sorts.map (fun (n, k) => (n, if k == .real then .bool else k)) } (.ok m)
  | .error _ => false)

-- Each accepted sort class and each modelled refusal occurs at least once.
#guard acceptedWith (fun m => !m.any (fun p => p.2.isTropical))
#guard acceptedWith (fun m => m.any (fun p => p.2 == maxS))
#guard acceptedWith (fun m => m.any (fun p => p.2 == minS))
#guard (modelled.filter (· != "accepted")).all (observedTags.contains ·)

end OracleSortRulesTest

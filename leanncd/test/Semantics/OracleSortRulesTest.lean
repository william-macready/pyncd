import Semantics.OracleSortRules

/-! Oracle sorts T1: agreement corpora for the independent rule predictor (guards only).

Every corpus program is run through the real pipeline (`productionVerdict`) and through the
independent predictor (`predict`); `agrees` must hold for all of them.

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

-- Of the 505 C1 programs: 141 are predicted accepted, 258 have exactly one predicted refusal and 106
-- have two or more. For the last group `agrees` is membership only (the observed constructor is among
-- the predicted ones), so a spurious EXTRA predicted refusal there is not detected; the 258 + 141 are
-- exact (the constructor must equal the single predicted one, and an accepted program must publish the
-- predicted sorts).
#guard (corpusC1.filter (refusalsOf · == 0)).length == 141
#guard (corpusC1.filter (refusalsOf · == 1)).length == 258
#guard (corpusC1.filter (refusalsOf · ≥ 2)).length == 106

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
      expect := .error ("multiWriterScatter", "Y") }
  , { label := "two affine writers"
      stmts := [writer 5 .max, writer 5 .max], expect := .error ("multiWriterScatter", "Y") }
  , { label := "affine writer + bare writer"
      stmts := [writer 5 .max, writer 0 .max], expect := .error ("multiWriterScatter", "Y") }
  -- tropical statements take no nonlinearity
  , { label := "relu on a max statement"
      stmts := [.assign "Y" [.free a] (rhs .max (.pointwise .relu) [[rd "X" [a]]])]
      expect := .error ("tropicalNonlin", "Y") } ]

run_cmd assertNone "C3 hand rows" (rowsProblems c3Rows)
#guard c3Rows.length == 19

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
  c3Rows.map (hDecls, ·.stmts)

private def modelled : List String :=
  ["accepted", "multiWriterAlgebra", "multiWriterScatter", "tropicalNonlin", "sortCastUnsupported"]

private def observedTags : List String :=
  (everything.map (fun (d, ss) => tag (productionVerdict d ss))).eraseDups

-- A production refusal the predictor does not model fails loudly, naming it (never skipped).
private def unmodelledTags : List String := observedTags.filter (fun t => !modelled.contains t)

run_cmd assertNone "production constructors the predictor does not model" unmodelledTags

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

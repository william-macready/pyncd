import LeanNCD.DSL.Compile
import LeanNCD.DSL.Pipeline.ScheduledValidation
import Eval.PropertyOracle.Neutral

/-! Oracle sorts T1: an INDEPENDENT predictor of the sort/vote/cast/refusal rules.

The rules are stated here from the design (`papers/semantics/oracle_sorts_design.md`) and never by
calling production's rule helpers. Production is observed only through the real pipeline
(`compileToScheduled`, then `validateScheduled`), via `productionVerdict`. The one shared piece is
`oracleNeutral`, the test-side neutrality predicate whose agreement with production is pinned in
`Eval.PropertyOracle.ScanOracle`. -/

open LeanNCD LeanNCD.PropertyOracle

namespace LeanNCD.OracleSorts

/-- The four sorts a tensor can run in. -/
inductive MSort | real | maxPlus | minPlus | bool
  deriving DecidableEq, Repr

/-- What the rules say about a program. `refusals` are (constructor name, tensor name) pairs the
    rules say apply (`[]` means accepted); `sorts` has one entry per declared tensor; `stmtSorts` is
    the sort each input statement RUNS in, aligned with the input list. `sorts` and `stmtSorts` are
    meaningful only when `refusals = []`. -/
structure Prediction where
  refusals : List (String × String)
  sorts : List (String × MSort)
  stmtSorts : List MSort

def MSort.isTropical : MSort → Bool
  | .maxPlus | .minPlus => true
  | .real | .bool => false

/-- Production's verdict on a program, observed through the real pipeline: `error` carries the
    `CompileError` constructor name and its first string payload; `ok` carries the published
    sort map (production's partial map, sorted by tensor name for a stable comparison). -/
def productionVerdict (decls : List Decl) (stmts : List Stmt) :
    Except (String × String) (List (String × MSort)) :=
  let p : TLProgram := ⟨decls, stmts⟩
  match p.compileToScheduled.run 0 with
  | .error e _ => .error (refusalOf e)
  | .ok sch _ =>
    match validateScheduled sch with
    | .error e => .error (refusalOf e)
    | .ok c =>
      let entries := c.algebras.toList.map (fun (n, s) => (n, ofAlgebra s))
      .ok (entries.toArray.qsort (fun x y => x.1 < y.1)).toList
where
  ofAlgebra : SortAlgebra → MSort
    | .real => .real | .maxPlus => .maxPlus | .minPlus => .minPlus | .bool => .bool
  refusalOf (e : CompileError) : String × String :=
    let s := (toString (repr e)).replace "\n" " "
    let tokens := (s.splitOn " ").filter (· ≠ "")
    let head := (tokens.headD "").replace "(" ""
    let name := (head.splitOn ".").getLast!
    let quoted := s.splitOn "\""
    (name, if quoted.length ≥ 3 then quoted.getD 1 "" else "")

private def tropicalEntries (m : List (String × MSort)) : List (String × MSort) :=
  m.filter (fun p => p.2.isTropical)

/-- Agreement on the STRICT class: a prediction with zero or exactly one refusal. Accepted: every
    entry production publishes (real entries of single-writer tensors included) has the same predicted
    sort, and the tropical entries agree in both directions (a predicted tropical sort production did
    not publish is a disagreement). One predicted refusal: production's observed constructor name equals
    it (payload names are not compared). `false` for a prediction outside the class (two or more
    refusals); those are `agreesMember`'s. -/
def agreesStrict (p : Prediction) (v : Except (String × String) (List (String × MSort))) : Bool :=
  match p.refusals, v with
  | [], .ok m =>
      let x := tropicalEntries m
      let y := tropicalEntries p.sorts
      m.all (p.sorts.contains ·) && x.all (y.contains ·) && y.all (x.contains ·)
  | [], .error _ => false
  | [r], .error e => r.1 == e.1
  | [_], .ok _ => false
  | _ :: _ :: _, _ => false

/-- Agreement on the MULTI class: a prediction with two or more refusals. Production raised exactly one
    error, so the check is membership: the observed constructor is among the predicted ones.

    Over-prediction stays undetectable here. A spurious extra predicted refusal inside a multi-refusal
    program leaves the observed constructor in the set, so membership still holds. Pinning which
    refusal production raises first would mean modelling production's raise order, which the
    independent predictor deliberately does not do. The rule behind each constructor is instead pinned
    by equality on STRICT programs (see the coverage guard in `OracleSortRulesTest`). `false` for a
    prediction outside the class. -/
def agreesMember (p : Prediction) (v : Except (String × String) (List (String × MSort))) : Bool :=
  match p.refusals, v with
  | _ :: _ :: _, .error e => p.refusals.any (fun r => r.1 == e.1)
  | _, _ => false

/-- Does the prediction match the observed verdict? `agreesStrict` for zero or one predicted refusal,
    `agreesMember` for two or more. -/
def agrees (p : Prediction) (v : Except (String × String) (List (String × MSort))) : Bool :=
  agreesStrict p v || agreesMember p v

/-! ### The rules, stated from the design -/

/-- Annotation sort: `sum` is real, `max` max-plus, `min` min-plus. -/
def annotationSort : AggOp → MSort
  | .sum => .real
  | .max => .maxPlus
  | .min => .minPlus

def annotationOf : Stmt → AggOp
  | .assign _ _ r | .scatter _ _ r => r.agg
  | .recurMorphism .. => .sum

private def destOf : Stmt → String
  | .assign n .. | .scatter n .. | .recurMorphism n .. => n

private def isPlainAssign : Stmt → Bool
  | .assign .. => true
  | _ => false

/-- A write slot that is a plain free axis (the only non-affine, non-scan slot). -/
private def bareSlot : LHSSlot → Bool
  | .free _ | .freeNorm _ => true
  | _ => false

private def hasNonBareSlot : Stmt → Bool
  | .assign _ ls _ | .scatter _ ls _ =>
      let freeUIDs := ls.filterMap (fun
        | .free a | .freeNorm a => some a.uid
        | _ => none)
      ls.any (fun l => !bareSlot l) || freeUIDs.length != freeUIDs.eraseDups.length
  | .recurMorphism .. => false

/-- The source tensors a statement reads through a bare (`read`) factor. Iverson and unary factors
    are not cast-checked. -/
private def bareReads : Stmt → List String
  | .assign _ _ r | .scatter _ _ r =>
      r.body.terms.flatMap (fun t => t.factors.filterMap (fun
        | .read n _ => some n
        | _ => none))
  | .recurMorphism .. => []

private def nonlinOf : Stmt → Nonlin
  | .assign _ _ r | .scatter _ _ r => r.nonlin
  | .recurMorphism .. => .identity

private def predicateNames (decls : List Decl) : List String :=
  decls.filterMap (fun | .predicate n _ => some n | _ => none)

private def declaredNames (decls : List Decl) : List String :=
  decls.filterMap (fun
    | .tensor n _ | .typedTensor _ n _ | .predicate n _ | .linear n _ _ | .typedLinear _ n _ _ => some n
    | _ => none)

/-- The sort a group of writers of one tensor computes in, or `none` on a vote conflict.
    Non-neutral writers vote their annotation; neutral writers abstain while any non-neutral writer
    exists, and otherwise vote their non-`sum` annotations (`sum` abstains); no vote is real.
    One writer is the same rule: it votes its OWN annotation unless it is a neutral `sum` (real). -/
private def groupSort (ws : List Stmt) : Option MSort :=
  let nonNeutral := ws.filter (fun s => !oracleNeutral s)
  let votes :=
    if nonNeutral.isEmpty then
      (ws.map (fun s => annotationSort (annotationOf s))).filter (fun v => v != .real)
    else nonNeutral.map (fun s => annotationSort (annotationOf s))
  match votes with
  | [] => some .real
  | v :: vs => if vs.all (· == v) then some v else none

/-- The refusals, tensor sorts and statement sorts the design's rules give for a program. -/
def predict (decls : List Decl) (stmts : List Stmt) : Prediction :=
  let preds := predicateNames decls
  let dests := (stmts.map destOf).eraseDups
  let writersOf (n : String) := stmts.filter (fun s => destOf s == n)
  -- a group's sort: a predicate destination is bool; else the vote (`none` = conflict)
  let sortOfGroup (n : String) : Option MSort :=
    if preds.contains n then some .bool else groupSort (writersOf n)
  -- a tropical group publishes an entry, unless it holds a scatter (such a group is refused)
  let entryOf (n : String) : Option MSort :=
    match sortOfGroup n with
    | some k =>
        if k.isTropical && ((writersOf n).length == 1 || (writersOf n).all isPlainAssign)
        then some k else none
    | none => none
  -- the sort a tensor is read at: its entry, else its declaration
  let sourceSort (n : String) : MSort :=
    match entryOf n with
    | some k => k
    | none => if preds.contains n then .bool else .real
  -- cast legality is keyed on the destination's entry (a predicate destination is bool)
  let destSort (n : String) : Option MSort :=
    if preds.contains n then some .bool else entryOf n
  let scatterRefusals := dests.filterMap (fun n =>
    let ws := writersOf n
    if ws.length > 1 && ws.any (fun s => !isPlainAssign s || hasNonBareSlot s)
    then some ("multiWriterScatter", n) else none)
  let voteRefusals := dests.filterMap (fun n =>
    if (writersOf n).length > 1 && (sortOfGroup n).isNone then some ("multiWriterAlgebra", n)
    else none)
  let nonlinRefusals := stmts.filterMap (fun s =>
    if (annotationSort (annotationOf s)).isTropical && nonlinOf s != .identity
    then some ("tropicalNonlin", destOf s) else none)
  let castRefusals := stmts.flatMap (fun s =>
    match destSort (destOf s) with
    | none => []
    | some k =>
        (bareReads s).filterMap (fun src =>
          let a := sourceSort src
          if a.isTropical && (k == .bool || (k.isTropical && k != a))
          then some ("sortCastUnsupported", destOf s) else none))
  let sorts := (declaredNames decls).map (fun n => (n, sourceSort n))
  let stmtSorts := stmts.map (fun s =>
    match sortOfGroup (destOf s) with
    | some k => k
    | none => annotationSort (annotationOf s))
  ⟨(scatterRefusals ++ voteRefusals ++ nonlinRefusals ++ castRefusals).eraseDups, sorts, stmtSorts⟩

end LeanNCD.OracleSorts

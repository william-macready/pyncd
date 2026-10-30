import LeanNCD.DSL.Compile
import LeanNCD.DSL.Pipeline.ScheduledValidation
import Eval.PropertyOracle.Neutral
import LeanNCD.Eval.Plan.Compile

/-! Oracle sorts T1: an INDEPENDENT predictor of the sort/vote/cast/refusal rules.

The rules are stated here from the design (`papers/semantics/oracle_sorts_design.md`) and never by
calling production's rule helpers. SOURCE observations use `compileToScheduled` then
`validateScheduled` via `productionVerdict`; SHAPED observations additionally use real checked
preparation and external input signatures. The one shared piece is
`oracleNeutral`, the test-side neutrality predicate whose agreement with production is pinned in
`Eval.PropertyOracle.ScanOracle`. -/

open LeanNCD LeanNCD.PropertyOracle

namespace LeanNCD.OracleSorts

/-- The four sorts a tensor can run in. -/
inductive MSort | real | maxPlus | minPlus | bool
  deriving DecidableEq, Repr

/-- What the rules say about a program. `refusals` are (constructor name, tensor name) pairs the
    rules say apply (`[]` means no refusal at the predicted stage, not full pipeline acceptance);
    `sorts` has one entry per declared tensor; `stmtSorts` is
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

private def slotsOf : Stmt → List LHSSlot
  | .assign _ ls _ | .scatter _ ls _ => ls
  | .recurMorphism .. => []

/-- Test-side normalization, deliberately independent of the DSL's affine helpers. -/
private def coefficients : IdxExpr → Int × List (Int × UID)
  | .axis a => (0, [(1, a.uid)])
  | .const n => (n, [])
  | .scale c a => (0, [(c, a.uid)])
  | .shift a n => (n, [(1, a.uid)])
  | .affine n cs => (n, cs.map fun (c, a) => (c, a.uid))

private def normalized (cs : List (Int × UID)) : List (Int × UID) :=
  (cs.map (·.2)).eraseDups.map fun u =>
    ((cs.filter (·.2 == u)).foldl (fun n p => n + p.1) 0, u)

private def bounded : LHSSlot → Bool
  | .free _ | .freeNorm _ => true
  | .affine (.const _) => false
  | .affine e => ((normalized (coefficients e).2).filter (·.1 != 0)).length ≤ 1
  | _ => false

private def declaredAxes (decls : List Decl) (n : String) : Option (List AxisSpec) :=
  decls.findSome? fun
    | .tensor m ax | .typedTensor _ m ax | .predicate m ax
    | .linear m ax _ | .typedLinear _ m ax _ => if m == n then some ax else none
    | _ => none

private def basis (decls : List Decl) (n : String) (ws : List Stmt) :
    Except (String × String) (List LHSSlot) :=
  match declaredAxes decls n with
  | some ax =>
      let us := ax.map (·.uid)
      if us.length != us.eraseDups.length then .error ("multiWriterRepeatedBasis", n)
      else .ok (ax.map LHSSlot.free)
  | none =>
      match ws.find? (fun w => isPlainAssign w && !hasNonBareSlot w) with
      | some w => .ok (slotsOf w)
      | none => .error ("multiWriterNeedsDeclaredShape", n)

private def needsB5 (ws : List Stmt) : Bool :=
  ws.length > 1 && ws.any (fun s => !isPlainAssign s || hasNonBareSlot s)

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
  -- Tropical scatter groups publish entries too; geometry is an independent refusal rule.
  let entryOf (n : String) : Option MSort :=
    match sortOfGroup n with
    | some k =>
        if k.isTropical then some k else none
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
    if needsB5 ws then
      if preds.contains n || !(ws.all (fun w => (slotsOf w).all bounded)) then
        some ("multiWriterScatter", n)
      else match basis decls n ws with
        | .error e => some e
        | .ok _ => none
    else none)
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

/-- Independent stride-aligned extent, NOT the maximum visited index plus one. Raw canceled
    axes remain sizing obligations. Explicit constants have their own legacy convention. -/
def predictedExtent (sl : LHSSlot) (sizes : List (UID × Nat)) : Option Nat := do
  let lookup (u : UID) := (sizes.find? (·.1 == u)).map (·.2)
  let e ← match sl with
    | .free a | .freeNorm a => some (IdxExpr.axis a)
    | .affine e => some e
    | _ => none
  match e with
  | .const n => some (n + 1).toNat
  | _ =>
    let (offset, cs) := coefficients e
    let terms ← cs.mapM fun (c, u) => do pure (c * Int.ofNat (← lookup u))
    let legacy := (offset + terms.sum).toNat
    match (normalized cs).filter (·.1 != 0) with
    | [(c, u)] =>
        let n ← lookup u
        if c > 0 && offset ≥ 0 && n > 0 then
          some (c * Int.ofNat n + (offset / c) * c).toNat
        else some legacy
    | _ => some legacy

/-- A box: the destination is declared and every declared axis is pinned by an `axis … = n`
    declaration in the source. Restated from the declarations, not from production's `pinned` map. -/
private def pinnedBox (decls : List Decl) (n : String) : Bool :=
  match declaredAxes decls n with
  | some ax => ax.all fun a => decls.any fun
      | .axis b (some _) => b.uid == a.uid
      | .iter b _ => b.uid == a.uid
      | _ => false
  | none => false

/-- B5c: a single plain writer whose destination is boxed and which production collects like a group
    of one (the declared shape decides, as for a group). Restated from the declarations and the
    statement, not from production's `boxedSingleGroups`: pinned declared destination, not a
    predicate, with at least one axis; a scatter with bounded slots or an assign over distinct free
    axes; and no declared axis among the writer's source axes (D5), which also excludes the identity
    writer. -/
private def singleBoxed (decls : List Decl) (n : String) (ws : List Stmt) : Bool :=
  match ws, declaredAxes decls n with
  | [w], some ax =>
      let declUIDs := ax.map (·.uid)
      let slots := slotsOf w
      let sourceUIDs := slots.flatMap fun
        | .free a | .freeNorm a => [a.uid]
        | .affine e => (coefficients e).2.map (·.2)
        | _ => []
      -- an `.assign` with an affine or repeated slot is a scatter after lowering, so one rule covers
      -- both statement forms: bounded slots
      let shaped := match w with
        | .recurMorphism .. => false
        | _ => slots.all bounded
      !declUIDs.isEmpty && pinnedBox decls n && !(predicateNames decls).contains n && shaped &&
        !sourceUIDs.any declUIDs.contains
  | _, _ => false

/-- Concrete shape-stage prediction. Callers supply independently known concrete axis sizes.
    A boxed group (`pinnedBox`) requires each writer extent to fit the basis extent; every other
    group requires equality. This does not claim to model signature, capability, inference or
    range-check failures. -/
def predictShaped (decls : List Decl) (stmts : List Stmt) (sizes : List (UID × Nat)) :
    Prediction :=
  let p := predict decls stmts
  if !p.refusals.isEmpty then p else
  let errors := (stmts.map destOf).eraseDups.filterMap fun n =>
    let ws := stmts.filter (fun s => destOf s == n)
    if !(needsB5 ws || singleBoxed decls n ws) then none else
    match basis decls n ws with
    | .error e => some e
    | .ok bs =>
      let expected := bs.mapM (predictedExtent · sizes)
      if pinnedBox decls n then
        let fits (w : Stmt) : Bool :=
          match expected, (slotsOf w).mapM (predictedExtent · sizes) with
          | some e, some a => e.length == a.length && (e.zip a).all fun (x, y) => y ≤ x
          | _, _ => false
        if ws.any (!fits ·) then some ("writerExtentExceedsBox", n) else none
      else
        if ws.any (fun w => (slotsOf w).mapM (predictedExtent · sizes) != expected)
        then some ("writerExtentMismatch", n) else none
  { p with refusals := errors }

/-- SHAPED observation uses actual input signatures and checked preparation. SOURCE observation
    remains `productionVerdict`, preserving corpora outside checked backend capabilities. -/
def productionShapedVerdict (decls : List Decl) (stmts : List Stmt)
    (sig : Eval.Plan.InputSignature) : Except (String × String) (List (String × MSort)) := do
  let v ← productionVerdict decls stmts
  let p : TLProgram := ⟨decls, stmts⟩
  match p.compileToScheduled.run 0 with
  | .error _ _ => .error ("sourceCompilation", "")
  | .ok sch _ =>
    match Eval.Plan.prepareEvalPlan sch sig with
    | .ok _ => .ok v
    | .error e =>
      match e.cause with
      | .shape (.writerExtentMismatch n _ _ _ _) => .error ("writerExtentMismatch", n)
      | .shape (.writerExtentExceedsBox n _ _ _ _) => .error ("writerExtentExceedsBox", n)
      | .shape (.sizeConflict _ _ _) => .error ("sizeConflict", "")
      | .shape e => .error (s!"unmodelled shape: {e}", "")
      | .capability e => .error (s!"unmodelled capability: {repr e}", "")
      | .inputSignature e => .error (s!"unmodelled signature: {repr e}", "")
      | .scan e => .error (s!"unmodelled scan: {repr e}", "")
      | .invalidPlan e => .error (s!"unmodelled plan: {repr e}", "")
      | .bindings e => .error (s!"unmodelled bindings: {repr e}", "")
      | .nonlin e => .error (s!"unmodelled nonlin: {repr e}", "")
      | .sourceInvariant e => .error (s!"unmodelled source invariant: {repr e}", "")

/-- Inference may detect inconsistent concrete shapes before the collector equality check.
    Keep the raw observed constructor, allowing it only for a predicted shape disagreement. -/
def agreesShaped (p : Prediction)
    (v : Except (String × String) (List (String × MSort))) : Bool :=
  agrees p v || (match v with
    | .error ("sizeConflict", _) => p.refusals.any (·.1 == "writerExtentMismatch")
    | _ => false)

end LeanNCD.OracleSorts

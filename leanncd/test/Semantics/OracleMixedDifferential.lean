import LeanNCD.Semantics.Source.SortedDifferential
import Semantics.OracleSortRules
import Semantics.OracleMixedFixtures
import Semantics.OracleMixedEval

/-! Oracle sorts T2: the classification of a mixed-sort Source program against the independent rule
predictor (`Semantics.OracleSortRules`).

`MixedClassification` is test-side by design: it must call the test-side predictor, which a library
module cannot import. The typed path (`SortedClassification`, `compareSortedSource`) is untouched.
`compareMixedSource` is the accepted-path driver: predicted refusals go to `classifyRefusal`, the rest
run through the heterogeneous evaluator and the mixed numerical profile. -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open Debug Oracle NativeLegs SortedDifferential NumericalProfile LeanNCD.OracleSorts

namespace OracleMixed

/-- The verdict on a mixed-sort program. `refusalParity` and `refusalMismatch` come from
`classifyRefusal`; the value constructors are produced by later tasks. `threeLegParity` is the
interim classification (oracle, legacy and checked agree; Core not yet run). -/
inductive MixedClassification
  | fourLegParity
  | threeLegParity (note : String)
  | refusalParity (ctor : String)
  | refusalMismatch (predicted : List (String × String)) (observed : String)
  | referenceUnavailable (reason : String)
  | referenceDiscrepancy
  | unsupportedNumericalProfile (reason : NumericalProfile.Unsupported)
  | nativeUnavailable
  | nativeFailure (legacy checked : LegResult)
  | nativeDiscrepancy (legacy checked : LegResult)
  deriving Repr

/-- The constructor name at the head of a printed `CompileError` (`Ns.Err.ctor "Y"` gives `ctor`). -/
def ctorNameOf (printed : String) : String :=
  let tokens := (printed.replace "\n" " ").splitOn " " |>.filter (· ≠ "")
  let head := (tokens.headD "").replace "(" ""
  (head.splitOn ".").getLast!

/-- What the legacy leg observed: `accepted`, `unavailable`, the `CompileError` constructor name of a
`compile failed:` text, or `failure: <text>` for any other failure. -/
def legacyTag : LegacyOutcome → String
  | .observed _ => "accepted"
  | .unavailable _ => "unavailable"
  | .failure f =>
    let text := toString f.original
    match text.splitOn "compile failed:" with
    | [_, rest] => ctorNameOf rest
    | _ => s!"failure: {text}"

/-- What the checked leg observed: `accepted`, `unavailable`, the constructor name of a
`.preparation` failure whose cause is `.sourceInvariant <CompileError>`, or a label for any other
failure. -/
def checkedTag : CheckedOutcome → String
  | .observed .. => "accepted"
  | .unavailable _ => "unavailable"
  | .sourceCompilation _ => "sourceCompilation"
  | .runtime _ => "runtime"
  | .preparation p =>
    match p.original.cause with
    | .sourceInvariant e => ctorNameOf (toString (repr e))
    | _ => "preparation: not a sourceInvariant"

/-- Compare the predicted refusals with what both native legs observed. With predicted refusals:
both legs refused with one constructor, among the predicted names, is `refusalParity`; anything else
(an accepting leg, a constructor outside the predicted set, legs that disagree) is
`refusalMismatch`. With none predicted: a leg that refused is `refusalMismatch [] ..`; both legs
accepting returns `referenceUnavailable "accepted: ..."`, a sentinel meaning "no refusal observed,
values not compared here" (never a mismatch); an unavailable leg is `nativeUnavailable`. -/
def classifyRefusal (p : Prediction) (run : NativeRun) : MixedClassification :=
  let l := legacyTag run.legacy
  let c := checkedTag run.checked
  let observed := if l == c then l else s!"legacy {l}, checked {c}"
  if p.refusals.isEmpty then
    if l == "accepted" && c == "accepted" then
      .referenceUnavailable "accepted: no refusal observed, values not compared by classifyRefusal"
    else if (l == "unavailable" || l == "accepted") && (c == "unavailable" || c == "accepted") then
      .nativeUnavailable
    else .refusalMismatch [] observed
  else if l == c && p.refusals.any (fun r => r.1 == l) then .refusalParity l
  else .refusalMismatch p.refusals observed

/-! ### The mixed run -/

/-- One mixed-sort comparison. `profile` is `.ok []` and `oracle` an error when nothing was evaluated
(a predicted refusal). The rule predictor's `prediction` is kept for the record. -/
structure MixedRun where
  prediction : Prediction
  oracle : Except String (List (TensorObservation ExtVal))
  profile : Except Unsupported (List SortedCell)
  legacy : LegResult
  checked : LegResult
  classification : MixedClassification

/-- The mixed numerical profile. Inputs and every cell are integers inside the envelope. Per
occurrence: a real statement uses the PRODUCT envelope exactly as `NumericalProfile.checkProfile`
does (read, partial product, running `max 1 |read|` product, final product); a tropical statement
the sum-of-magnitudes envelope of `checkSortedProfile` over its finite reads. -/
def checkMixedProfile (source : AdmittedSource) (r : MixedResult) :
    Except Unsupported (List SortedCell) := do
  let _ ← checkStructure source
  for t in r.tensors do
    if t.role == .input then
      for (coordinate, v) in (Oracle.coordinates t.shape).zip t.values do
        let origin : SourceOrigin := { side := .input, declaration := some t.declaration }
        let _ ← checkExt { origin := origin, coordinate := coordinate } .input v
  for o in r.occurrences do
    let site : Site := ⟨{ statement := some o.statement }, o.coordinate, o.assignment, [], none⟩
    if o.sort == .real then
      let mut product : ℚ := 1
      let mut envelope : ℚ := 1
      for read in o.reads do
        match read with
        | .fin q =>
          let _ ← checkValue site .read q
          product := product * q
          let _ ← checkValue site .partialProduct product
          envelope := envelope * max 1 |q|
          let _ ← checkValue site .subsetProductBound envelope
        | _ => pure ()
      let _ ← checkValue site .product product
    else
      let mut bound : ℚ := 0
      for read in o.reads do
        match read with
        | .fin q =>
          let _ ← checkValue site .read q
          bound := bound + |q|
          let _ ← checkValue site .subsetProductBound bound
        | _ => pure ()
  let mut cells := []
  for out in r.tensors do
    if out.role != .input then
      for (coordinate, value) in (Oracle.coordinates out.shape).zip out.values do
        let origin : SourceOrigin := { side := .output, declaration := some out.declaration }
        let expected ← checkExt { origin := origin, coordinate := coordinate } .tensorCell value
        cells := cells ++ [(⟨out.declaration, coordinate, expected⟩ : SortedCell)]
  pure cells

/-- A native leg against the profile cells (`SortedDifferential.legOf` is private; restated). -/
private def mixedLegOf (cells : Except Unsupported (List SortedCell)) :
    Option NativeObservation → String → LegResult
  | none, "" => .unavailable
  | none, message => .failure message
  | some observation, _ =>
    match cells, observation.outputs with
    | .error _, _ => .unavailable
    | _, .error issues => .failure s!"binding issues {repr issues}"
    | .ok cells, .ok bindings =>
      match compareBindings cells bindings with
      | .error message => .failure message
      | .ok none => .agrees
      | .ok (some cell) => .mismatch cell

/-- The legs' results against the profile cells. -/
private def legResults (profile : Except Unsupported (List SortedCell)) (n : NativeRun) :
    LegResult × LegResult :=
  (match n.legacy with
    | .observed o => mixedLegOf profile (some o) ""
    | .failure e => mixedLegOf profile none s!"legacy {e.original.error}"
    | .unavailable _ => .unavailable,
   match n.checked with
    | .observed o _ => mixedLegOf profile (some o) ""
    | .sourceCompilation e => mixedLegOf profile none s!"checked compile {repr e.cause}"
    | .preparation _ => mixedLegOf profile none "checked preparation"
    | .runtime e => mixedLegOf profile none s!"checked runtime {repr e.original.cause}"
    | .unavailable _ => .unavailable)

/-- A leg's result on a predicted-refusal row: no values were evaluated, so only the refusal itself is
recorded (an accepting leg is a contradiction of the prediction). -/
private def refusalLeg (tag : String) : LegResult :=
  if tag == "unavailable" then .unavailable
  else if tag == "accepted" then .failure "accepted although a refusal was predicted"
  else .failure s!"refused {tag}"

/-- The site of a non-finite read: the read tensor's declaration and the cell. -/
private def nonFiniteSite (declaration : Nat) (coordinate : List Nat) : Site :=
  { origin := { side := .declaration, declaration := some declaration }, coordinate := coordinate }

/-- The oracle verdict on a mixed-sort Source program.

Predicted refusals (`p.refusals` non-empty) go to `classifyRefusal`. Otherwise `classifyRefusal` is
consulted first only for a native leg that refuses or is unavailable (`refusalMismatch [] ..`,
`nativeUnavailable`); its sentinel for "both legs accepted" is never a verdict, it means "now compare
values": `runMixed`, the mixed profile and both legs' bits. Both legs agreeing with the oracle is
`threeLegParity` (the Core leg is not run for mixed programs here). `order` names the declaration
ordinals of the non-input tensors in dependency order. `doctor` rewrites the rule predictor's verdict
before it is used (identity by default); it exists only for negative controls, to show that a wrong
prediction is caught rather than agreed with. -/
def compareMixedSource (snapshot : SourceSnapshot) (order : Option (List Nat))
    (doctor : Prediction → Prediction := id) :
    Except SourceDiagnostic MixedRun := do
  let admitted ← admitSourceAffine snapshot true
  let p := doctor (predict snapshot.resolved.decls snapshot.resolved.stmts)
  let n ← runNative snapshot (sorted := true)
  let refusal := classifyRefusal p n
  if !p.refusals.isEmpty then
    pure { prediction := p, oracle := .error "predicted refusal: nothing evaluated", profile := .ok [],
           legacy := refusalLeg (legacyTag n.legacy), checked := refusalLeg (checkedTag n.checked),
           classification := refusal }
  else
    match refusal with
    | .referenceUnavailable _ =>
      -- predicted accept and both legs accepted: evaluate and compare values
      match order with
      | none =>
        let u : Oracle.Unavailable := ⟨{}, .missingOrder⟩
        let profile : Except Unsupported (List SortedCell) := .error (.oracleUnavailable u)
        pure { prediction := p, oracle := .error s!"oracle unavailable {repr u}", profile := profile,
               legacy := .unavailable, checked := .unavailable,
               classification := .referenceUnavailable s!"oracle unavailable {repr u}" }
      | some order =>
        match runMixed admitted snapshot.resolved.stmts p order with
        | .error (.unavailable u) =>
          let profile : Except Unsupported (List SortedCell) := .error (.oracleUnavailable u)
          let (l, c) := legResults profile n
          pure { prediction := p, oracle := .error s!"oracle unavailable {repr u}",
                 profile := profile, legacy := l, checked := c,
                 classification := .referenceUnavailable s!"oracle unavailable {repr u}" }
        | .error (.inconsistent m) =>
          let profile : Except Unsupported (List SortedCell) := .ok []
          pure { prediction := p, oracle := .error m, profile := profile, legacy := .unavailable,
                 checked := .unavailable, classification := .referenceUnavailable m }
        | .error (.nonFiniteIntoReal d c) =>
          let reason := Unsupported.nonFiniteIntoReal (nonFiniteSite d c)
          let profile : Except Unsupported (List SortedCell) := .error reason
          let (l, c') := legResults profile n
          pure { prediction := p, oracle := .error "non-finite cell read by a real statement",
                 profile := profile, legacy := l, checked := c',
                 classification := .unsupportedNumericalProfile reason }
        | .ok r =>
          let oracle := oracleTensorsAt id admitted ⟨r.tensors, []⟩
          let profile := checkMixedProfile admitted r
          let (l, c) := legResults profile n
          let classification : MixedClassification :=
            match oracle, profile with
            | .error e, _ => .referenceUnavailable e
            | _, .error reason => .unsupportedNumericalProfile reason
            | .ok _, .ok _ =>
              match l, c with
              | .agrees, .agrees => .threeLegParity "core leg not run"
              | .unavailable, _ | _, .unavailable => .nativeUnavailable
              | .failure _, _ | _, .failure _ => .nativeFailure l c
              | _, _ => .nativeDiscrepancy l c
          pure { prediction := p, oracle := oracle, profile := profile, legacy := l, checked := c,
                 classification := classification }
    | other =>
      -- a leg refused a predicted-accept program (`refusalMismatch [] ..`), or is unavailable
      pure { prediction := p, oracle := .error "legs did not both accept: nothing evaluated",
             profile := .ok [], legacy := refusalLeg (legacyTag n.legacy),
             checked := refusalLeg (checkedTag n.checked), classification := other }

end OracleMixed

import LeanNCD.Semantics.Source.SortedDifferential
import Semantics.OracleSortRules
import Semantics.OracleMixedFixtures

/-! Oracle sorts T2: the classification of a mixed-sort Source program against the independent rule
predictor (`Semantics.OracleSortRules`).

`MixedClassification` is test-side by design: it must call the test-side predictor, which a library
module cannot import. The typed path (`SortedClassification`, `compareSortedSource`) is untouched.
This file is appended to by later tasks (the heterogeneous run and `compareMixedSource`). -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open NativeLegs SortedDifferential LeanNCD.OracleSorts

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

end OracleMixed

import LeanNCD.Semantics.Source.SortedDifferential
import Semantics.OracleSortRules
import Semantics.OracleMixedFixtures
import Semantics.OracleMixedEval

/-! Oracle sorts T2: the classification of a mixed-sort Source program against the independent rule
predictor (`Semantics.OracleSortRules`).

`MixedClassification` is test-side by design: it must call the test-side predictor, which a library
module cannot import. The typed path (`SortedClassification`, `compareSortedSource`) is untouched.
`compareMixedSource` is the driver. It consults `classifyRefusal` first on every program: a predicted
refusal, or a leg that refused a predicted-accept program, is classified there (`some`); when it
returns `none` (nothing predicted and both legs accepted) the program runs through the heterogeneous
evaluator, the mixed numerical profile, both native legs and the stratified Core leg. -/

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open Debug Oracle NativeLegs SortedDifferential NumericalProfile LeanNCD.OracleSorts

namespace OracleMixed

/-- The verdict on a mixed-sort program. `refusalParity` and `refusalMismatch` come from
`classifyRefusal`; the value constructors come from `compareMixedSource`. `fourLegParity` means the
oracle, the stratified Core leg, legacy and checked all agree. `threeLegParity note` means the oracle,
legacy and checked agree and the Core leg stopped before the end (the note says why: a later statement
needs an earlier non-finite cell, and Core inputs are rationals); the targets it did run before stopping
were still compared with the oracle (a disagreement there is `referenceDiscrepancy`).

"All agree" is as strong as what each leg observes: the native legs (legacy, checked) bind only the
`.output` tensors, so a defined intermediate in a chain is compared oracle-against-Core only, never
against the native legs. -/
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
accepting returns `none`: no refusal verdict, the accepted path continues to value comparison (never
a mismatch); an unavailable leg is `nativeUnavailable`. Every other case is `some`. -/
def classifyRefusal (p : Prediction) (run : NativeRun) : Option MixedClassification :=
  let l := legacyTag run.legacy
  let c := checkedTag run.checked
  let observed := if l == c then l else s!"legacy {l}, checked {c}"
  if p.refusals.isEmpty then
    if l == "accepted" && c == "accepted" then none
    else if (l == "unavailable" || l == "accepted") && (c == "unavailable" || c == "accepted") then
      some .nativeUnavailable
    else some (.refusalMismatch [] observed)
  else if l == c && p.refusals.any (fun r => r.1 == l) then some (.refusalParity l)
  else some (.refusalMismatch p.refusals observed)

/-! ### The mixed run -/

/-- One mixed-sort comparison. `profile` is `.ok []` and `oracle` an error when nothing was evaluated
(a predicted refusal). The rule predictor's `prediction` is kept for the record. `core` is `none` when
the Core leg did not run to completion (a predicted refusal, an oracle that did not evaluate, or a
target blocked by a non-finite intermediate, where `corePrefix` holds what it did run), and
`some (.error ..)` when it ran and failed; the two are never conflated. It defaults
to `none`: only the arm that evaluates sets it. `corePrefix` holds the observations of the targets the
Core leg did run before it stopped at a blocked target (`core` is then `none`); it is compared with the
oracle and is empty otherwise. -/
structure MixedRun where
  prediction : Prediction
  oracle : Except String (List (TensorObservation ExtVal))
  profile : Except Unsupported (List SortedCell)
  legacy : LegResult
  checked : LegResult
  classification : MixedClassification
  core : Option (Except String (List (TensorObservation ExtVal))) := none
  corePrefix : List (TensorObservation ExtVal) := []

/-- The mixed numerical profile. Inputs and every cell are integers inside the envelope. Per
occurrence: a real statement uses the PRODUCT envelope exactly as `NumericalProfile.checkProfile`
does (read, partial product, running `max 1 |read|` product, final product); a tropical statement
the sum-of-magnitudes envelope of `checkSortedProfile` over its finite reads.

Weaker than `checkProfile`: the summation, fiber and collection bounds, and the receipt re-checks of
the oracle's occurrences (occurrence count, assignment, read coordinate), are NOT performed; only the
occurrence-level envelopes above and the per-cell `checkExt` are. A false parity cannot result: every
non-input cell passes `checkExt`, so its exact value is a representable integer, and parity requires
the native bits to equal the exact value's bits. The weaker check can only turn an f64 rounding
difference in an unbounded sum into a `nativeDiscrepancy`, which is loud. -/
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

/-- A leg's result when no values were evaluated: only what the leg did is recorded. On a
predicted-refusal row an accepting leg contradicts the prediction (`accepted`); on a predicted-accept
row where the other leg refused or was unavailable, an accepting leg is merely not the refusing one. -/
private def refusalLeg (accepted : String) (tag : String) : LegResult :=
  if tag == "unavailable" then .unavailable
  else if tag == "accepted" then .failure accepted
  else .failure s!"refused {tag}"

private def predictedRefusal : String := "accepted although a refusal was predicted"

private def otherLegDid : String := "accepted; other leg did not"

/-- The site of a non-finite read: the read tensor's declaration and the cell. -/
private def nonFiniteSite (declaration : Nat) (coordinate : List Nat) : Site :=
  { origin := { side := .declaration, declaration := some declaration }, coordinate := coordinate }

/-! ### The stratified Core leg (K2)

The Core leg interprets one carrier per program, so a mixed-sort program is run one target at a time:
the statements writing the target, with `agg` set to the sort the predictor says they run in (a
neutral copy whose annotation differs from its group's runs as the group), over the program's inputs
plus the Core leg's OWN earlier outputs as rational inputs. Each such sub-program is single-sort, so
`admitSourceSorted` + `coreTensorsAt` interpret it. Nothing the oracle computed feeds Core. -/

/-- The aggregation that spells a sort (`bool` has none: it is outside the Source sublanguage). -/
private def aggOfSort : MSort → Option AggOp
  | .real => some .sum
  | .maxPlus => some .max
  | .minPlus => some .min
  | .bool => none

/-- A statement with its aggregation replaced. -/
private def withAgg (a : AggOp) : Stmt → Stmt
  | .assign n s r => .assign n s { r with agg := a }
  | .scatter n s r => .scatter n s { r with agg := a }
  | other => other

/-- One single-sort group through `admitSourceSorted` + `coreTensorsAt`: the Core observation of
`target`. (A separate function: the selected `Sorted` lives in `Type 1`.) -/
private def coreGroup (sub : SourceSnapshot) (target : Nat) :
    Except String (TensorObservation ExtVal) :=
  match admitSourceSorted sub with
  | .error d => .error s!"core admission {repr d.cause}"
  | .ok (source, S) => do
    let tensors ← coreTensorsAt S source
    match tensors.find? (·.declaration == target) with
    | some t => pure t
    | none => throw s!"core leg: no observation for declaration {target}"

/-- The Core leg over every target in `order`. `error`: it ran and failed. `ok (ts, true)`: it ran to
the end and `ts` are the Core observations of the non-input tensors. `ok (ts, false)`: it STOPPED at a
target because a later group reads an earlier target that has a non-finite Core cell (inputs are
rationals; the check is per read tensor, so it never runs a group on a value it cannot represent);
`ts` are the observations of the targets it did run before stopping, which the caller still compares
with the oracle. `feed` rewrites an earlier target's rational cells (by declaration) before they enter
later groups; it is the identity except in negative controls. -/
private def coreLeg (snapshot : SourceSnapshot) (admitted : AdmittedSource) (p : Prediction)
    (order : List Nat) (feed : Nat → List ℚ → List ℚ) :
    Except String (List (TensorObservation ExtVal) × Bool) := do
  let mut observed : List (TensorObservation ExtVal) := []
  let mut fed : List (Nat × List ℚ) := []
  let mut nonFinite : List Nat := []
  for target in order do
    let group := admitted.statements.filter fun s =>
      (admitted.source.table.entry s.output.tensor).declaration == target
    for s in group do
      for term in s.terms do
        for read in term.sourceReads do
          if (admitted.source.table.entry read.read.tensor).declaration ∈ nonFinite then
            return (observed, false)
    let mut stmts : List Stmt := []
    for s in group do
      let some k := p.stmtSorts[s.original]?
        | throw s!"no predicted sort for statement {s.original}"
      let some a := aggOfSort k | throw s!"statement {s.original} has no Source aggregation"
      let some stmt := snapshot.resolved.stmts[s.original]?
        | throw s!"no statement {s.original}"
      stmts := stmts ++ [withAgg a stmt]
    -- every other non-input tensor enters as an input: an earlier target at the Core leg's value,
    -- a later or unrelated one (never read by this group) as zeros. Reading a zero placeholder would be
    -- unsound; that never happens because `runMixed` ran `Oracle.checkOrder` first, which rejects any
    -- read of a declaration that is not earlier in `order`.
    let extra := snapshot.specs.filterMap fun spec =>
      if spec.declaration == target || spec.role == .input then none
      else
        let values :=
          match fed.find? (·.1 == spec.declaration) with
          | some (_, qs) => qs
          | none => List.replicate (Oracle.cellCount spec.shape) 0
        some (⟨spec.declaration, spec.shape, values⟩ : InputBinding)
    let sub : SourceSnapshot :=
      { resolved := { snapshot.resolved with stmts := stmts }
        specs := snapshot.specs.map fun spec =>
          if spec.declaration == target then spec else { spec with role := .input }
        inputs := snapshot.inputs ++ extra }
    let t ← coreGroup sub target
    observed := observed ++ [t]
    match t.values.mapM (fun v => match v with | some (.fin q) => some q | _ => none) with
    | some qs => fed := fed ++ [(target, feed target qs)]
    | none => nonFinite := nonFinite ++ [target]
  pure (observed, true)

/-- The oracle verdict on a mixed-sort Source program.

`classifyRefusal` is consulted first. Predicted refusals (`p.refusals` non-empty) always get a verdict
from it, as does a native leg that refuses or is unavailable (`refusalMismatch [] ..`,
`nativeUnavailable`). Its `none` ("both legs accepted, nothing predicted") is not a verdict, it means
"now compare values": `runMixed`, the mixed profile, both legs' bits and the stratified Core leg
(`coreLeg`).
Precedence, as in the typed path: oracle or Core unavailable, then Core against oracle
(`referenceDiscrepancy`), then the profile, then the native legs. All four agreeing is `fourLegParity`;
a Core leg that stopped at a blocked target (non-finite intermediate; its `corePrefix` is still
compared) leaves `threeLegParity` with its note (the note string keeps the older "core not run"). `order`
names the declaration ordinals of the non-input tensors in dependency order. `doctor` rewrites the
rule predictor's verdict before it is used (identity by default) and `feed` rewrites the Core leg's
earlier outputs before later groups read them (identity by default); both exist only for negative
controls, to show that a wrong prediction or a wrong intermediate is caught rather than agreed with. -/
def compareMixedSource (snapshot : SourceSnapshot) (order : Option (List Nat))
    (doctor : Prediction → Prediction := id)
    (feed : Nat → List ℚ → List ℚ := fun _ qs => qs) :
    Except SourceDiagnostic MixedRun := do
  let admitted ← admitSourceAffine snapshot true
  let p := doctor (predict snapshot.resolved.decls snapshot.resolved.stmts)
  let n ← runNative snapshot (sorted := true)
  match classifyRefusal p n with
  | some refusal =>
    -- a predicted refusal, or a predicted-accept program a leg refused or was unavailable on
    -- (`refusalMismatch [] ..`, `nativeUnavailable`): nothing is evaluated
    if !p.refusals.isEmpty then
      pure { prediction := p, oracle := .error "predicted refusal: nothing evaluated", profile := .ok [],
             legacy := refusalLeg predictedRefusal (legacyTag n.legacy),
             checked := refusalLeg predictedRefusal (checkedTag n.checked),
             classification := refusal }
    else
      pure { prediction := p, oracle := .error "legs did not both accept: nothing evaluated",
             profile := .ok [], legacy := refusalLeg otherLegDid (legacyTag n.legacy),
             checked := refusalLeg otherLegDid (checkedTag n.checked), classification := refusal }
  | none =>
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
          let core := coreLeg snapshot admitted p order feed
          let classification : MixedClassification :=
            match oracle, core with
            | .error e, _ => .referenceUnavailable e
            | _, .error e => .referenceUnavailable s!"core leg failed: {e}"
            | .ok o, .ok (coreObs, complete) =>
              -- a Core leg that stopped is compared on the targets it did run (its prefix)
              let expected := o.filter fun t =>
                t.role != .input && (complete || coreObs.any (·.declaration == t.declaration))
              let agreement : Except String Bool :=
                match compareTensors (coreObs.filter (·.role != .input)) expected with
                | .error e => .error s!"{repr e}"
                | .ok .agreement => .ok true
                | .ok (.disagreement _) | .ok (.unobserved _) => .ok false
              match agreement with
              | .error e => .referenceUnavailable e
              | .ok false => .referenceDiscrepancy
              | .ok true =>
                match profile with
                | .error reason => .unsupportedNumericalProfile reason
                | .ok _ =>
                  match l, c with
                  | .agrees, .agrees =>
                    if complete then .fourLegParity
                    else .threeLegParity "core not run: non-finite intermediate"
                  | .unavailable, _ | _, .unavailable => .nativeUnavailable
                  | .failure _, _ | _, .failure _ => .nativeFailure l c
                  | _, _ => .nativeDiscrepancy l c
          let coreField : Option (Except String (List (TensorObservation ExtVal))) :=
            match core with
            | .error e => some (.error e)
            | .ok (_, false) => none
            | .ok (cs, true) => some (.ok cs)
          let corePrefix : List (TensorObservation ExtVal) :=
            match core with
            | .ok (cs, false) => cs
            | _ => []
          pure { prediction := p, oracle := oracle, profile := profile, legacy := l, checked := c,
                 classification := classification, core := coreField, corePrefix := corePrefix }

end OracleMixed

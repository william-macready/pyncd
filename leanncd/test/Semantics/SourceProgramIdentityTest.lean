import LeanNCD.Semantics.Source.Permutation
import Semantics.SourceProgramFixtures

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open LeanNCD.Semantics.Program.Executor
open SourceAdmissionFixtures SourceProgramFixtures

namespace SourceProgramIdentityTest

set_option synthInstance.maxSize 512

private def chain : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      decls := decls ++ [.tensor "Mid" [i], .tensor "End" [i]]
      stmts :=
        [.assign "End" [.free i] (rhs [[.read "Mid" [.axis i], .read "B" [.axis i]]]),
         .assign "Y" [.free i] (rhs [[.read "End" [.axis i]], [.read "B" [.axis i]]]),
         .assign "Diagonal" [.free i, .free i] (rhs [[]]),
         .assign "Mid" [.free i] (rhs [[.read "A" [.axis i, .axis k]]])] }
    specs := specs ++ [⟨8, .defined, [2]⟩, ⟨9, .output, [2]⟩] }

private def chainTensors : List TensorObservation :=
  [⟨0, 3, "A", [2, 3], [1, 2, 3, 4, 5, 6].map some⟩,
   ⟨1, 4, "B", [2], [some 10, some 20]⟩,
   ⟨2, 5, "Y", [2], [some 70, some 320]⟩,
   ⟨3, 6, "Empty", [0], []⟩,
   ⟨4, 7, "Diagonal", [2, 2], [some 1, some 0, some 0, some 1]⟩,
   ⟨5, 8, "Mid", [2], [some 6, some 15]⟩,
   ⟨6, 9, "End", [2], [some 60, some 300]⟩]

private def chainOracleTensors : List Oracle.Tensor :=
  [⟨3, "A", .input, [2, 3], [1, 2, 3, 4, 5, 6]⟩,
   ⟨4, "B", .input, [2], [10, 20]⟩,
   ⟨5, "Y", .output, [2], [70, 320]⟩,
   ⟨6, "Empty", .input, [0], []⟩,
   ⟨7, "Diagonal", .defined, [2, 2], [1, 0, 0, 1]⟩,
   ⟨8, "Mid", .defined, [2], [6, 15]⟩,
   ⟨9, "End", .output, [2], [60, 300]⟩]

private inductive ChainError
  | observation (error : ObservationError)
  | oracle (error : Oracle.Unavailable)
  deriving Repr

private def chainReceipt : Except ChainError (Observation × Oracle.Result) := do
  let runtime ← (observe chain).mapError ChainError.observation
  let source ← (admitSource chain).mapError fun e =>
    .observation (.admission e)
  let oracle ← (Oracle.run source (some [7, 8, 9, 5])).mapError ChainError.oracle
  pure (runtime, oracle)

def P1 : Bool :=
  match chainReceipt with
  | .error _ => false
  | .ok (runtime, oracle) =>
    runtime == ⟨.complete, chainTensors, 18⟩ &&
    oracle.tensors == chainOracleTensors &&
    runtime.tensors.map (fun t => (t.declaration, t.name, t.shape, t.values)) ==
      oracle.tensors.map (fun t => (t.declaration, t.name, t.shape, t.values.map some))

private def interleaved : SourceSnapshot :=
  { snapshot with
    resolved := { snapshot.resolved with
      stmts :=
        [.assign "Diagonal" [.free i, .free i] (rhs []),
         .assign "Y" [.free i] (rhs [[.read "B" [.axis i]]]),
         .assign "Diagonal" [.free i, .free i] (rhs [[]]),
         .assign "Y" [.free i] (rhs [[.read "B" [.axis i], .read "B" [.axis i]]])] } }

private def identityTensors : List TensorObservation :=
  [⟨0, 3, "A", [2, 3], [1, 2, 3, 4, 5, 6].map some⟩,
   ⟨1, 4, "B", [2], [some 10, some 20]⟩,
   ⟨2, 5, "Y", [2], [some 110, some 420]⟩,
   ⟨3, 6, "Empty", [0], []⟩,
   ⟨4, 7, "Diagonal", [2, 2], [some 1, some 0, some 0, some 1]⟩]

private structure TagRow where
  tensorUID : Nat
  localIndex : Nat
  sourceIndex : Nat
  original : Nat
  valuations : Nat
  deriving DecidableEq, Repr

private def tagRows (source : AdmittedSource) : List TagRow :=
  (sourceDefined source).flatMap fun t =>
    (List.finRange ((elaborateSource source).statements t)).map fun s =>
      let tag := source.statementTag RationalReference.registry t s
      ⟨t.val.val, s.val, tag.sourceIndex.val, tag.original, tag.layout.count⟩

private structure MapRow where
  original : Nat
  tensorUID : Nat
  localIndex : Nat
  sourceIndex : Nat
  inverse : Bool
  deriving DecidableEq, Repr

private def mapRows (source : IdentifiedSource) : List MapRow :=
  (List.finRange source.admitted.statements.length).map fun index =>
    let id := source.originalEquiv index
    let loc := source.originalToLocal id
    let tag := source.originalTagEquiv id
    ⟨id.val, loc.1.val, loc.2.val, tag.2.sourceIndex.val,
      decide (source.localToOriginal loc = id)⟩

private def localRoundtrips (source : IdentifiedSource) : List Bool :=
  (sourceDefined source.admitted).flatMap fun t =>
    (List.finRange ((elaborateSource source.admitted).statements t)).map fun s =>
      let loc := Sigma.mk t.val s
      decide (source.originalToLocal (source.localToOriginal loc) = loc)

private abbrev OccurrenceKey := Nat × (Nat × List (UID × Nat))

private def occurrenceKey (source : AdmittedSource) (t : (elaborateSource source).Defined)
    (o : (elaborateSource source).Occurrence t) : OccurrenceKey :=
  (t.val.val, (source.statementTag RationalReference.registry t o.1).occurrenceIdentity o.2.val)

private def occurrenceKeys (source : AdmittedSource) : List OccurrenceKey :=
  (sourceDefined source).flatMap fun t =>
    (sourceOccurrences source t).map (occurrenceKey source t)

private structure ContributionRow where
  key : OccurrenceKey
  declaration : Nat
  destination : List Nat
  value : Rat
  deriving DecidableEq, Repr

private def contributionRows (source : AdmittedSource)
    (events : List (Event (elaborateSource source))) : List ContributionRow :=
  events.filterMap fun event =>
    match event with
    | .contribution t o v => some
        ⟨occurrenceKey source t o, (source.source.table.entry t.val).declaration,
          coordList _ ((elaborateSource source).destination t o.1 o.2), v⟩
    | .publication .. | .undefined .. => none

private def expectedContributions : List ContributionRow :=
  [⟨(2, (1, [(7, 0)])), 5, [0], 10⟩,
   ⟨(2, (1, [(7, 1)])), 5, [1], 20⟩,
   ⟨(2, (3, [(7, 0)])), 5, [0], 100⟩,
   ⟨(2, (3, [(7, 1)])), 5, [1], 400⟩,
   ⟨(4, (0, [(7, 0)])), 7, [0, 0], 0⟩,
   ⟨(4, (0, [(7, 1)])), 7, [1, 1], 0⟩,
   ⟨(4, (2, [(7, 0)])), 7, [0, 0], 1⟩,
   ⟨(4, (2, [(7, 1)])), 7, [1, 1], 1⟩]

private def runFor (source : AdmittedSource) (reversed : Bool := false) :
    Except ObservationError (ValidatedResult (elaborateSource source) RationalReference.ops) :=
  (if reversed then
    runValidated (elaborateSource source) RationalReference.ops
      (sourceSchedule source).reverse (sourceInputBinding source)
  else runSource source).mapError fun t =>
    .validation t.val (source.source.table.entry t).declaration

private structure IdentityReceipt where
  tags : List TagRow
  maps : List MapRow
  localInverses : List Bool
  runtime : Observation
  contributions : List ContributionRow
  deriving DecidableEq, Repr

private def identityObservation (source : IdentifiedSource)
    (result : ValidatedResult (elaborateSource source.admitted) RationalReference.ops) :
    IdentityReceipt :=
  ⟨tagRows source.admitted, mapRows source, localRoundtrips source,
    ⟨outcomeKind source.admitted result.result.outcome,
      tensorObservations source.admitted result.result.outcome, result.result.events.length⟩,
    contributionRows source.admitted result.result.events⟩

private def identityReceipt : Except ObservationError IdentityReceipt := do
  let source ← (admitIdentifiedSource interleaved).mapError ObservationError.admission
  let result ← runFor source.admitted
  pure (identityObservation source result)

def P2 : Bool :=
  match identityReceipt with
  | .error _ => false
  | .ok receipt =>
    receipt.tags == [⟨2, 0, 1, 1, 2⟩, ⟨2, 1, 3, 3, 2⟩,
      ⟨4, 0, 0, 0, 2⟩, ⟨4, 1, 2, 2, 2⟩] &&
    receipt.maps == [⟨0, 4, 0, 0, true⟩, ⟨1, 2, 0, 1, true⟩,
      ⟨2, 4, 1, 2, true⟩, ⟨3, 2, 1, 3, true⟩] &&
    receipt.localInverses == List.replicate 4 true &&
    receipt.runtime == ⟨.complete, identityTensors, 14⟩ &&
    receipt.contributions == expectedContributions

private def reverseStatements (source : AdmittedSource) : StatementPermutation source :=
  permuteStatements source
    { toFun := Fin.rev, invFun := Fin.rev,
      left_inv := Fin.rev_rev, right_inv := Fin.rev_rev }

private structure EventRow where
  kind : String
  tensorUID : Nat
  identity : Option (Nat × List (UID × Nat))
  destination : List Nat
  value : Option Rat
  deriving DecidableEq, Repr

private def eventRow (source : AdmittedSource) : Event (elaborateSource source) → EventRow
  | .contribution t o v =>
    ⟨"contribution", t.val.val, some (occurrenceKey source t o).2,
      coordList _ ((elaborateSource source).destination t o.1 o.2), some v⟩
  | .publication t p v => ⟨"publication", t.val.val, none, coordList _ p, some v⟩
  | .undefined t o =>
    ⟨"undefined", t.val.val, some (occurrenceKey source t o).2,
      coordList _ ((elaborateSource source).destination t o.1 o.2), none⟩

private def canonicalContributions (keys : List OccurrenceKey) (rows : List ContributionRow) :
    Option (List ContributionRow) :=
  keys.mapM fun key => rows.find? (fun row => row.key == key)

private def transportChecks (source : AdmittedSource) : List Bool :=
  let p := reverseStatements source
  (sourceDefined source).flatMap fun t =>
    (sourceOccurrences p.reordered t).map fun o =>
      let old := p.occurrenceEquiv RationalReference.registry t o
      decide (occurrenceKey source t old = occurrenceKey p.reordered t o) &&
      decide (coordList _ ((elaborateSource source).destination t old.1 old.2) =
        coordList _ ((elaborateSource p.reordered).destination t o.1 o.2))

private structure PermutationReceipt where
  before : IdentityReceipt
  after : IdentityReceipt
  canonicalBefore : Option (List ContributionRow)
  canonicalAfter : Option (List ContributionRow)
  keysUnique : Bool
  transport : List Bool
  eventsBefore : List EventRow
  eventsAfter : List EventRow
  deriving DecidableEq, Repr

private def permutationReceipt : Except ObservationError PermutationReceipt := do
  let source ← (admitIdentifiedSource interleaved).mapError ObservationError.admission
  let p := reverseStatements source.admitted
  let reordered := StatementPermutation.identified source p
  let beforeResult ← runFor source.admitted
  let afterResult ← runFor reordered.admitted true
  let before := identityObservation source beforeResult
  let after := identityObservation reordered afterResult
  let keys := occurrenceKeys source.admitted
  pure ⟨before, after, canonicalContributions keys before.contributions,
    canonicalContributions keys after.contributions, decide keys.Nodup,
    transportChecks source.admitted,
    beforeResult.result.events.map (eventRow source.admitted),
    afterResult.result.events.map (eventRow reordered.admitted)⟩

def P3 : Bool :=
  match permutationReceipt with
  | .error _ => false
  | .ok receipt =>
    receipt.before.tags == [⟨2, 0, 1, 1, 2⟩, ⟨2, 1, 3, 3, 2⟩,
      ⟨4, 0, 0, 0, 2⟩, ⟨4, 1, 2, 2, 2⟩] &&
    receipt.after.tags == [⟨2, 0, 0, 3, 2⟩, ⟨2, 1, 2, 1, 2⟩,
      ⟨4, 0, 1, 2, 2⟩, ⟨4, 1, 3, 0, 2⟩] &&
    receipt.before.maps == [⟨0, 4, 0, 0, true⟩, ⟨1, 2, 0, 1, true⟩,
      ⟨2, 4, 1, 2, true⟩, ⟨3, 2, 1, 3, true⟩] &&
    receipt.after.maps == [⟨3, 2, 0, 0, true⟩, ⟨2, 4, 0, 1, true⟩,
      ⟨1, 2, 1, 2, true⟩, ⟨0, 4, 1, 3, true⟩] &&
    receipt.before.localInverses == List.replicate 4 true &&
    receipt.after.localInverses == List.replicate 4 true &&
    receipt.before.runtime == ⟨.complete, identityTensors, 14⟩ &&
    receipt.after.runtime == receipt.before.runtime &&
    receipt.before.contributions.length == 8 && receipt.after.contributions.length == 8 &&
    receipt.keysUnique &&
    receipt.canonicalBefore == some expectedContributions &&
    receipt.canonicalAfter == receipt.canonicalBefore &&
    receipt.transport == List.replicate 8 true &&
    receipt.eventsBefore.head? ==
      some ⟨"contribution", 2, some (1, [(7, 0)]), [0], some 10⟩ &&
    receipt.eventsAfter.head? == some ⟨"publication", 4, none, [1, 0], some 0⟩ &&
    receipt.eventsBefore != receipt.eventsAfter

example (source : AdmittedSource) (_hAdmission : admitSource chain = .ok source)
    (result : ValidatedResult (elaborateSource source) RationalReference.ops)
    (_hRun : runSource source = .ok result) (c complete)
    (hComplete : result.result.outcome = .complete c complete) :
    (elaborateSource source).Models RationalReference.ops result.input
      ((elaborateSource source).finalStore c complete) :=
  sourceResult_model source result c complete hComplete

example (source : IdentifiedSource) (id : OriginalStatement source.admitted) :
    source.localToOriginal (source.originalToLocal id) = id :=
  source.local_original_inverse id

example (source : IdentifiedSource)
    (loc : (t : source.admitted.source.table.declarations.Tensor) ×
      Fin (targetStatements source.admitted t).length) :
    source.originalToLocal (source.localToOriginal loc) = loc :=
  source.original_local_inverse loc

example (source : AdmittedSource) (t : (elaborateSource source).Defined)
    (o : (elaborateSource (reverseStatements source).reordered).Occurrence t) :
    (source.statementTag RationalReference.registry t
      ((reverseStatements source).occurrenceEquiv RationalReference.registry t o).1).occurrenceIdentity
      ((reverseStatements source).occurrenceEquiv RationalReference.registry t o).2.val =
      ((reverseStatements source).reordered.statementTag RationalReference.registry t o.1).occurrenceIdentity
        o.2.val :=
  (reverseStatements source).identities RationalReference.registry t o

example (source : AdmittedSource)
    (store : Store RationalReference.Carrier source.source.table.declarations)
    (old : (elaborateSource source).AdmEnv semiringOps store)
    (new : (elaborateSource (reverseStatements source).reordered).AdmEnv semiringOps store)
    (t : (elaborateSource source).Defined) :
    (elaborateSource (reverseStatements source).reordered).collect semiringOps store new t =
      (elaborateSource source).collect semiringOps store old t :=
  (reverseStatements source).collect RationalReference.registry store new old t

example (source : AdmittedSource) (input : (elaborateSource source).Input)
    (store : Store RationalReference.Carrier source.source.table.declarations) :
    (elaborateSource (reverseStatements source).reordered).Models semiringOps input store ↔
      (elaborateSource source).Models semiringOps input store :=
  (reverseStatements source).models RationalReference.registry input store

#eval chainReceipt
#guard P1
#eval P1
#eval identityReceipt
#guard P2
#eval P2
#eval permutationReceipt
#guard P3
#eval P3

end SourceProgramIdentityTest

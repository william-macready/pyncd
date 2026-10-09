import Semantics.SourceAdmissionFixtures
import LeanNCD.DSL.Elab

open LeanNCD LeanNCD.Semantics LeanNCD.Semantics.Source
open SourceAdmissionFixtures

namespace SourceAdmissionAcceptanceTest

private def a (kind : AxisKind) : AxisSpec := ⟨"a", 7, kind⟩

private def copySnapshot (kind : AxisKind) (ty : TensorElementType)
    (values : List ℚ) : SourceSnapshot :=
  { resolved := {
      decls := [.axis (a kind) (some 2), .typedTensor ty "X" [a kind],
        .typedTensor ty "Y" [a kind]]
      stmts := [.assign "Y" [.free (a kind)] (rhs [[.read "X" [.axis (a kind)]]])]
      env := {}, extNames := ∅ }
    specs := [⟨1, .input, [2]⟩, ⟨2, .output, [2]⟩]
    inputs := [⟨1, [2], values⟩] }

private def metadataView (s : SourceSnapshot) :
    Option (List (Nat × String × TensorElementType × TensorRole × List (UID × Nat)) ×
      List (Nat × List ℚ)) := do
  let admitted ← (admitSource s).toOption
  let source := admitted.source
  let entries := source.table.entries.map fun t =>
    (t.declaration, t.name, t.elementType, t.role, t.axes.map fun ax => (ax.uid, ax.extent))
  let buffers := (List.finRange source.table.entries.length).filterMap fun t =>
    if h : (source.table.entry t).role = .input then
      some ((source.table.entry t).declaration, (source.inputs.buffers t h).values)
    else none
  pure (entries, buffers)

private def origins (s : SourceSnapshot) : Option (List SourceOrigin) := do
  let admitted ← (admitSource s).toOption
  pure (admitted.statements.flatMap fun st =>
    st.terms.flatMap fun term => term.sourceReads.map (·.origin))

private def readOrigin : SourceOrigin :=
  { side := .read, declaration := some 1, statement := some 0,
    term := some 0, factor := some 0 }

private def metadataAccepted (s : SourceSnapshot) (uid : UID)
    (ty : TensorElementType) (values : List ℚ) : Bool :=
  metadataView s == some
    ([(1, "X", ty, .input, [(uid, 2)]), (2, "Y", ty, .output, [(uid, 2)])],
     [(1, values)])

private def copyAccepted (s : SourceSnapshot) (uid : UID)
    (ty : TensorElementType) (values : List ℚ) : Bool :=
  metadataAccepted s uid ty values &&
    admissionView s == some
      ([uid], [(1, .input, [2]), (2, .output, [2])],
       [⟨0, [uid], [uid], [⟨[], .pure, [(some 0, some 0, [uid])]⟩]⟩]) &&
    origins s == some [readOrigin]

def FinitePinnedRealCopy : Bool :=
  copyAccepted (copySnapshot .real .f64 [3, 5]) 7 .f64 [3, 5] &&
    copyAccepted (copySnapshot .nat .f64 [3, 5]) 7 .f64 [3, 5] &&
    copyAccepted (copySnapshot .real .f32 [1 / 3, 5 / 7]) 7 .f32 [1 / 3, 5 / 7]

#guard FinitePinnedRealCopy
#eval FinitePinnedRealCopy

private def parsedRaw : TLProgram := tlprog!{
  axis a : ℕ = 2
  tensor f64 X(a), Y(a)
  Y[a] := X[a]
}

private def parsedSpecs : List TensorSpec := [⟨1, .input, [2]⟩, ⟨2, .output, [2]⟩]
private def parsedInputs : List InputBinding := [⟨1, [2], [3, 5]⟩]

-- The actual parser and public resolver retain real-kind use-site placeholders.
private def parsedMetadata : Bool :=
  let use : AxisSpec := ⟨"a", 0, .real⟩
  parsedRaw.decls == [.axis ⟨"a", 0, .nat⟩ (some 2),
    .typedTensor .f64 "X" [use], .typedTensor .f64 "Y" [use]] &&
    parsedRaw.stmts == [.assign "Y" [.free use] (rhs [[.read "X" [.axis use]]])] &&
    match resolveSource parsedRaw parsedSpecs parsedInputs with
    | .error _ => false
    | .ok s =>
      let resolvedUse : AxisSpec := ⟨"a", 1, .real⟩
      s.resolved.decls == [.axis ⟨"a", 1, .nat⟩ (some 2),
        .typedTensor .f64 "X" [resolvedUse], .typedTensor .f64 "Y" [resolvedUse]] &&
        s.resolved.stmts == [
          .assign "Y" [.free resolvedUse] (rhs [[.read "X" [.axis resolvedUse]]])] &&
        s.specs.map (·.declaration) == [1, 2] &&
        s.inputs.map (·.declaration) == [1]

#guard parsedMetadata

def ParsedRawNatCopy : Bool :=
  parsedMetadata &&
    (admitRawSource parsedRaw parsedSpecs parsedInputs).toOption.isSome &&
    match resolveSource parsedRaw parsedSpecs parsedInputs with
    | .error _ => false
    | .ok s => copyAccepted s 1 .f64 [3, 5]

#guard ParsedRawNatCopy
#eval ParsedRawNatCopy

private def sumProductSnapshot (input : Decl) (ty : TensorElementType) : SourceSnapshot :=
  let s := copySnapshot .nat ty [1 / 3, 5 / 7]
  { s with resolved := { s.resolved with
      decls := [.axis (a .nat) (some 2), input, .typedTensor ty "Y" [a .nat]]
      stmts := [.assign "Y" [.free (a .nat)] (rhs [
        [.read "X" [.axis (a .nat)], .read "X" [.axis (a .nat)]],
        [.read "X" [.axis (a .nat)]]])] } }

private def sumProductAccepted (input : Decl) (ty : TensorElementType) : Bool :=
  let s := sumProductSnapshot input ty
  metadataAccepted s 7 ty [1 / 3, 5 / 7] &&
    s.resolved.decls[1]? == some input &&
    admissionView s == some
      ([7], [(1, .input, [2]), (2, .output, [2])],
       [⟨0, [7], [7], [
         ⟨[], .pure, [(some 0, some 0, [7]), (some 0, some 1, [7])]⟩,
         ⟨[], .pure, [(some 1, some 0, [7])]⟩]⟩]) &&
    origins s == some [readOrigin, { readOrigin with factor := some 1 },
      { readOrigin with term := some 1 }]

def RealLinearSumProduct : Bool :=
  [false, true].all (fun hasBias =>
    sumProductAccepted (.linear "X" [a .nat] hasBias) .f32 &&
      sumProductAccepted (.typedLinear .f32 "X" [a .nat] hasBias) .f32 &&
      sumProductAccepted (.typedLinear .f64 "X" [a .nat] hasBias) .f64) &&
    sumProductAccepted (.tensor "X" [a .nat]) .f32 &&
    sumProductAccepted (.typedTensor .f32 "X" [a .nat]) .f32 &&
    sumProductAccepted (.typedTensor .f64 "X" [a .nat]) .f64

#guard RealLinearSumProduct
#eval RealLinearSumProduct

private def diagnosticSummary (result : Except SourceDiagnostic AdmittedSource) : String :=
  match result with
  | .error diagnostic => reprStr diagnostic
  | .ok _ => "accepted"

#eval diagnosticSummary (admitSource (copySnapshot .real .f64 [3, 5]))
#eval diagnosticSummary (admitRawSource parsedRaw parsedSpecs parsedInputs)
#eval diagnosticSummary (admitSource
  (sumProductSnapshot (.typedLinear .f64 "X" [a .nat] false) .f64))

private def refuses (s : SourceSnapshot) (stage : SourceStage) (origin : SourceOrigin)
    (cause : SourceCause → Bool) : Bool :=
  match admitSource s with
  | .error diagnostic =>
    diagnostic.stage == stage && diagnostic.origin == origin && cause diagnostic.cause
  | .ok _ => false

private def realCopy : SourceSnapshot := copySnapshot .real .f64 [3, 5]

#guard refuses { realCopy with resolved := { realCopy.resolved with
    decls := [.axis (a .real) none, .typedTensor .f64 "X" [a .real],
      .typedTensor .f64 "Y" [a .real]] } }
  .declarations { side := .declaration, declaration := some 0 }
  (fun | .missingDomain 7 => true | _ => false)

#guard refuses { realCopy with resolved := { realCopy.resolved with
    decls := [.iter (a .real) 2, .typedTensor .f64 "X" [a .real],
      .typedTensor .f64 "Y" [a .real]] } }
  .declarations { side := .declaration, declaration := some 0 }
  (fun | .unsupported .iteration => true | _ => false)

private def realSlots (slot : LHSSlot) : SourceSnapshot :=
  { realCopy with resolved := { realCopy.resolved with
      stmts := [.assign "Y" [slot] (rhs [[.read "X" [.axis (a .real)]]])] } }

#guard refuses (realSlots (.freeNorm (a .real)))
  .output { side := .output, declaration := some 2, statement := some 0, slot := some 0 }
  (fun | .unsupported .marked => true | _ => false)

#guard refuses (realSlots (.iterNext (a .real)))
  .output { side := .output, declaration := some 2, statement := some 0, slot := some 0 }
  (fun | .unsupported .scanSlot => true | _ => false)

#guard refuses (realSlots (.affine (.shift (a .real) 1)))
  .output { side := .output, declaration := some 2, statement := some 0, slot := some 0 }
  (fun | .unsupported .affine => true | _ => false)

#guard refuses { realCopy with resolved := { realCopy.resolved with
    stmts := [.assign "Y" [.free (a .real)] (rhs [[.read "X" [.shift (a .real) 1]]])] } }
  .read { readOrigin with slot := some 0 }
  (fun | .unsupported .affine => true | _ => false)

#guard refuses { realCopy with resolved := { realCopy.resolved with
    stmts := [.assign "Y" [.free (a .real)] (rhs [
      [.read "X" [.axis ⟨"a", 99, .real⟩]]])] } }
  .read { readOrigin with slot := some 0 }
  (fun | .unbound 99 => true | _ => false)

private def parsedNonSum : TLProgram := tlprog!{
  axis a : ℕ = 2
  tensor f64 X(a), Y(a)
  Y[a] := maxreduce(X[a])
}

private def parsedNonIdentity : TLProgram := tlprog!{
  axis a : ℕ = 2
  tensor f64 X(a), Y(a)
  Y[a] := relu(X[a])
}

private def rawRefuses (raw : TLProgram) (form : UnsupportedSource) : Bool :=
  match admitRawSource raw parsedSpecs parsedInputs with
  | .error d => d.stage == .statement &&
      d.origin == { side := .output, statement := some 0 } &&
      match d.cause with | .unsupported actual => actual == form | _ => false
  | .ok _ => false

#guard rawRefuses parsedNonSum .nonSum
#guard rawRefuses parsedNonIdentity .nonIdentity

private def linearCopy : SourceSnapshot :=
  sumProductSnapshot (.typedLinear .f32 "X" [a .nat] false) .f32

#guard [.complex64, .complex128].all (fun ty =>
  [Decl.typedLinear ty "X" [a .nat] false, .typedLinear ty "X" [a .nat] true,
    .typedTensor ty "X" [a .nat]].all (fun decl =>
    refuses (sumProductSnapshot decl .f32)
      .declarations { side := .declaration, declaration := some 1 }
      (fun | .unsupported .complex => true | _ => false)))

#guard refuses (sumProductSnapshot (.predicate "X" [a .nat]) .f32)
  .declarations { side := .declaration, declaration := some 1 }
  (fun | .unsupported .predicate => true | _ => false)

private def linearFactor (factor : Factor) : SourceSnapshot :=
  { linearCopy with resolved := { linearCopy.resolved with
      stmts := [.assign "Y" [.free (a .nat)] (rhs [[factor]])] } }

#guard refuses (linearFactor
    (.iverson (.rel .lt (.embed (.axis (a .nat))) (.embed (.const 1)))))
  .read { side := .read, statement := some 0, term := some 0, factor := some 0 }
  (fun | .unsupported .iverson => true | _ => false)

#guard refuses (linearFactor (.unaryFn .log "X" [.axis (a .nat)]))
  .read { side := .read, statement := some 0, term := some 0, factor := some 0 }
  (fun | .unsupported .unary => true | _ => false)

#guard refuses { linearCopy with specs := [⟨1, .input, [3]⟩, ⟨2, .output, [2]⟩] }
  .signatures { side := .declaration, declaration := some 1 }
  (fun | .shape [2] [3] => true | _ => false)

#guard refuses { linearCopy with inputs := [⟨1, [3], [1]⟩] }
  .inputs { side := .input, declaration := some 1 }
  (fun | .shape [2] [3] => true | _ => false)

#guard refuses { linearCopy with inputs := [⟨1, [2], [1]⟩] }
  .inputs { side := .input, declaration := some 1 }
  (fun | .length 2 1 => true | _ => false)

#guard refuses { linearCopy with specs := [⟨1, .defined, [2]⟩, ⟨2, .output, [2]⟩] }
  .inputs { side := .input, declaration := some 1 }
  (fun | .role .input .defined => true | _ => false)

#guard refuses { linearCopy with inputs := [] }
  .inputs { side := .input, declaration := some 1 }
  (fun | .missingInput 1 => true | _ => false)

#guard refuses { linearCopy with inputs := [⟨0, [2], [1 / 3, 5 / 7]⟩] }
  .inputs { side := .input, declaration := some 0 }
  (fun | .unexpectedInput 0 => true | _ => false)

end SourceAdmissionAcceptanceTest

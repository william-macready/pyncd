import LeanNCD.Semantics.Source

namespace LeanNCD.Semantics.Source.BindingRenameFixtures

def context : Context :=
  ⟨[⟨7, 2⟩, ⟨11, 2⟩, ⟨13, 2⟩, ⟨3, 4⟩, ⟨5, 3⟩], by decide⟩

def scope : BinderScope context where
  source := [7, 100]
  output := [11, 101]
  free := [13, 102]
  generated := [3, 5]
  covers := by
    intro u
    have h := u.property
    simp [context] at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases h with h | h | h | h | h <;> simp [h]
  generatedOnly := by
    intro u hu
    simp at hu
    rcases hu with rfl | rfl <;> decide

def valuation : UIDVal context :=
  (uidCoordEquiv context).symm (1, 0, 1, 2, 1, ())

def readShape : Shape := [⟨3, 4⟩, ⟨5, 3⟩, ⟨11, 2⟩, ⟨13, 2⟩, ⟨7, 2⟩]

def readMetadata (f : UID → UID) : Shape :=
  readShape.map (fun a => { a with uid := f a.uid })

def readAt (c : Context) (v : UIDVal c) (f : UID → UID) :
    Except Diagnostic (List Nat × Nat) := do
  let metadata := readMetadata f
  let slots ← resolveSlots c.axes metadata (metadata.map Axis.uid)
  let p := slots.project (uidCoordEquiv c v)
  let values := [p.1.val, p.2.1.val, p.2.2.1.val, p.2.2.2.1.val, p.2.2.2.2.1.val]
  let tensorValue := 10000 * p.1.val + 1000 * p.2.1.val + 100 * p.2.2.1.val +
    10 * p.2.2.2.1.val + p.2.2.2.2.1.val
  pure (values, tensorValue)

namespace V4

def renamed : Context := renameBinders context scope
def transport : UIDTransport context renamed := binderTransport context scope
def transported : UIDVal renamed := transport.valuationEquiv valuation
def originalRead := readAt context valuation id
def renamedRead := readAt renamed transported scope.renameUID
def staleMetadataRead := readAt renamed transported id

#guard context.axes.map Axis.uid = [7, 11, 13, 3, 5]
#guard renamed.axes = [⟨7, 2⟩, ⟨11, 2⟩, ⟨13, 2⟩, ⟨106, 4⟩, ⟨108, 3⟩]
#guard renamed.axes.map Axis.extent = context.axes.map Axis.extent
#guard readMetadata scope.renameUID =
  [⟨106, 4⟩, ⟨108, 3⟩, ⟨11, 2⟩, ⟨13, 2⟩, ⟨7, 2⟩]
#guard originalRead = .ok ([2, 1, 0, 1, 1], 21011)
#guard renamedRead = .ok ([2, 1, 0, 1, 1], 21011)
#guard renamedRead = originalRead
#guard staleMetadataRead = .error (.unbound 3)
#guard (transported.lookupRef (Ref.there (Ref.there (Ref.there Ref.here)))).val = 2
#guard (transported.lookupRef (Ref.there Ref.here)).val = 0

theorem domain_preserved (u : context.Key) :
    renamed.domain (transport.equiv u) = context.domain u :=
  transport.domain u

theorem lookup_preserved (v : UIDVal context) (u : context.Key) :
    ((transport.valuationEquiv v) (transport.equiv u)).val = (v u).val :=
  renameBinders_lookup context scope v u

theorem protected_fixed (u : context.Key) (h : u.val ∉ scope.generated) :
    (transport.equiv u).val = u.val :=
  renameBinders_fixed context scope u h

#eval ("V4 original/transported/stale metadata reads",
  originalRead, renamedRead, staleMetadataRead)

end V4

namespace V5

def validRequest (u : UID) : UID := if u = 3 then 203 else 205
def outputCollision (u : UID) : UID := if u = 3 then 101 else 205
def freeCollision (u : UID) : UID := if u = 3 then 102 else 205
def boundOutputCollision (u : UID) : UID := if u = 3 then 11 else 205
def boundFreeCollision (u : UID) : UID := if u = 3 then 13 else 205
def duplicateRequest (_ : UID) : UID := 203

def renamed (request : UID → UID) : Context :=
  renameBindersRequested context scope request

def transport (request : UID → UID) : UIDTransport context (renamed request) :=
  requestedBinderTransport context scope request

def requestedRead (request : UID → UID) :=
  readAt (renamed request) ((transport request).valuationEquiv valuation)
    (scope.requestedUID request)

def outputRead := requestedRead outputCollision
def freeRead := requestedRead freeCollision
def validRead := requestedRead validRequest
def duplicateRead := requestedRead duplicateRequest

#guard scope.RequestFresh validRequest
#guard ¬scope.RequestFresh outputCollision
#guard ¬scope.RequestFresh freeCollision
#guard ¬scope.RequestFresh boundOutputCollision
#guard ¬scope.RequestFresh boundFreeCollision
#guard ¬scope.RequestFresh duplicateRequest
#guard outputCollision 3 = 101
#guard freeCollision 3 = 102
#guard 101 ∈ scope.output
#guard 102 ∈ scope.free
#guard outputCollision 5 = 205
#guard 205 ∉ scope.support
#guard (renamed outputCollision).axes = V4.renamed.axes
#guard (renamed freeCollision).axes = V4.renamed.axes
#guard (renamed boundOutputCollision).axes = V4.renamed.axes
#guard (renamed boundFreeCollision).axes = V4.renamed.axes
#guard (renamed duplicateRequest).axes = V4.renamed.axes
#guard (renamed validRequest).axes =
  [⟨7, 2⟩, ⟨11, 2⟩, ⟨13, 2⟩, ⟨203, 4⟩, ⟨205, 3⟩]
#guard scope.generated.map (scope.requestedUID outputCollision) = [106, 108]
#guard scope.generated.map (scope.requestedUID freeCollision) = [106, 108]
#guard scope.generated.map (scope.requestedUID validRequest) = [203, 205]
#guard 106 ∉ scope.support
#guard 108 ∉ scope.support
#guard (scope.source ++ scope.output ++ scope.free).map
  (scope.requestedUID outputCollision) = [7, 100, 11, 101, 13, 102]
#guard (scope.source ++ scope.output ++ scope.free).map
  (scope.requestedUID freeCollision) = [7, 100, 11, 101, 13, 102]
#guard (scope.source ++ scope.output ++ scope.free).map
  (scope.requestedUID validRequest) = [7, 100, 11, 101, 13, 102]
#guard readMetadata (scope.requestedUID outputCollision) =
  [⟨106, 4⟩, ⟨108, 3⟩, ⟨11, 2⟩, ⟨13, 2⟩, ⟨7, 2⟩]
#guard readMetadata (scope.requestedUID validRequest) =
  [⟨203, 4⟩, ⟨205, 3⟩, ⟨11, 2⟩, ⟨13, 2⟩, ⟨7, 2⟩]
#guard outputRead = .ok ([2, 1, 0, 1, 1], 21011)
#guard freeRead = .ok ([2, 1, 0, 1, 1], 21011)
#guard validRead = .ok ([2, 1, 0, 1, 1], 21011)
#guard duplicateRead = .ok ([2, 1, 0, 1, 1], 21011)
#guard requestedRead boundOutputCollision = V4.originalRead
#guard requestedRead boundFreeCollision = V4.originalRead
#guard readAt (renamed validRequest) ((transport validRequest).valuationEquiv valuation)
  validRequest = .error (.domain 205 2 3)

theorem no_capture (request : UID → UID) (u : context.Key)
    (h : u.val ∈ scope.generated) :
    ((transport request).equiv u).val ∉ scope.support :=
  requestedBinders_noCapture context scope request u h

theorem protected_fixed (request : UID → UID) (u : context.Key)
    (h : u.val ∈ scope.source ++ scope.output ++ scope.free) :
    ((transport request).equiv u).val = u.val :=
  requestedBinders_protected context scope request u h

theorem domain_preserved (request : UID → UID) (u : context.Key) :
    (renamed request).domain ((transport request).equiv u) = context.domain u :=
  (transport request).domain u

theorem lookup_preserved (request : UID → UID) (v : UIDVal context) (u : context.Key) :
    (((transport request).valuationEquiv v) ((transport request).equiv u)).val = (v u).val :=
  requestedBinders_lookup context scope request v u

#eval ("V5 output/free collision, valid and duplicate reads",
  outputRead, freeRead, validRead, duplicateRead)
#eval ("V5 atomic fallback and honored axes",
  (renamed outputCollision).axes, (renamed freeCollision).axes, (renamed validRequest).axes)

end V5

namespace V6

def source4 : Context := ⟨[⟨3, 4⟩], by decide⟩
def source2 : Context := ⟨[⟨3, 2⟩], by decide⟩
def target2 : Context := ⟨[⟨19, 2⟩], by decide⟩
def target4 : Context := ⟨[⟨19, 4⟩], by decide⟩
def target5 : Context := ⟨[⟨19, 5⟩], by decide⟩

def value2 : UIDVal target2 := (uidCoordEquiv target2).symm (1, ())
def value4 : UIDVal target4 := (uidCoordEquiv target4).symm (1, ())
def lastValue4 : UIDVal target4 := (uidCoordEquiv target4).symm (3, ())
def value5 : UIDVal target5 := (uidCoordEquiv target5).symm (1, ())

def substitutionValues (src dst : Context) (v : UIDVal dst) :
    Except Diagnostic (List Nat) := do
  let m ← resolveIndexMap src dst (fun _ => 19)
  let p := uidPositionalEquiv src (indexPullback m v)
  pure ((List.finRange src.axes.length).map (fun i => (p i).val))

def smallerDomain := substitutionValues source4 target2 value2
def largerDomain := substitutionValues source4 target5 value5
def equalDomain := substitutionValues source4 target4 value4
def equalDomainLast := substitutionValues source4 target4 lastValue4
def smallerLegalNeighbor := substitutionValues source2 target2 value2
def reversedMismatch := substitutionValues source2 target4 value4

#guard (value2 ⟨19, by decide⟩).val = 1
#guard (value4 ⟨19, by decide⟩).val = 1
#guard (value5 ⟨19, by decide⟩).val = 1
#guard smallerDomain = .error (.domain 19 4 2)
#guard largerDomain = .error (.domain 19 4 5)
#guard reversedMismatch = .error (.domain 19 2 4)
#guard equalDomain = .ok [1]
#guard equalDomainLast = .ok [3]
#guard smallerLegalNeighbor = .ok [1]

#eval ("V6 unequal full domains and legal neighbors",
  smallerDomain, largerDomain, reversedMismatch, equalDomain, equalDomainLast,
  smallerLegalNeighbor)

end V6

end LeanNCD.Semantics.Source.BindingRenameFixtures

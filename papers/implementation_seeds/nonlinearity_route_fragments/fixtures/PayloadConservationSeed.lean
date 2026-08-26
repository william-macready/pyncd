import LeanNCD.DSL.Pipeline.Lowering
import LeanNCD.Bridge.AcsetCodec

/-!
# Route-fragment payload-conservation seed

The 19 fixtures below are named independently of the generated corpus. Assertions distinguish
physical payload conservation from equality of the intentionally opaque categorical projection.
-/

namespace PayloadConservationSeed

open LeanNCD Std
open LeanNCD.AcsetCodec

def i : AxisSpec := { name := "i", uid := 1, kind := .real }
def j : AxisSpec := { name := "j", uid := 2, kind := .real }
def k : AxisSpec := { name := "k", uid := 3, kind := .real }

def readBody (name : String) (idxs : List IdxExpr) : SumExpr :=
  { terms := [{ factors := [.read name idxs] }] }

def one (stmt : ScanStmt) (decls : List Decl := []) (env : DeclEnv := {})
    (exts : Finset String := {"X"}) (explicitSizes : Std.HashMap UID Nat := {}) :
    ScheduledProgram :=
  { decls, env, extNames := exts, explicitSizes, stmts := [stmt] }

def declName? : Decl → Option String
  | .tensor name _ | .predicate name _ | .linear name _ _ => some name
  | .axis .. | .iter .. => none

def privateName (sp : ScheduledProgram) (ordinal : Nat) : String :=
  let names :=
    (sp.decls.filterMap declName? ++ sp.stmts.flatMap fun s => s.writes ++ s.reads).eraseDups
  let maxLen := names.foldl (fun n s => max n s.length) 0
  String.ofList (List.replicate (maxLen + ordinal + 1) '#')

def mutateDropMask (enabled : Bool) : Nonlin → Nonlin
  | .axiswise fn mask => .axiswise fn (if enabled then none else mask)
  | n => n

def mutateAggregation (enabled : Bool) (agg : AggOp) : AggOp :=
  if enabled then .sum else agg

def enableDropMaskMutation : Bool := false
def enableDropAggregationMutation : Bool := false
def enableDropMetadataMutation : Bool := false
def enableReplaceScanPreMutation : Bool := false

def physicalize (sp : ScheduledProgram) : ScheduledProgram :=
  let stmts := sp.stmts.zipIdx.flatMap fun (scanStmt, ordinal) =>
    let internal := privateName sp ordinal
    match scanStmt with
    | .plain s@(.assign name slots rhs) =>
        if rhs.nonlin == Nonlin.identity then [.plain s] else
          let producerSlots := slots.map fun
            | .freeNorm a => .free a
            | slot => slot
          [.plain (.assign internal producerSlots
            { body := rhs.body, nonlin := .identity, agg :=
               mutateAggregation enableDropAggregationMutation rhs.agg }),
           .plain (.assign name slots
            { body := { terms := [{ factors := [
                .read internal (slots.filterMap LHSSlot.toReadIdx) ] }] },
              nonlin := mutateDropMask enableDropMaskMutation rhs.nonlin, agg := .sum })]
    | .plain s => [.plain s]
    | .scanPre name axis nested =>
        [.scanPre name axis (if enableReplaceScanPreMutation then default else nested)]
    | .scan .. => [scanStmt]
  { sp with
      decls := if enableDropMetadataMutation then [] else sp.decls
      env := if enableDropMetadataMutation then {} else sp.env
      explicitSizes := if enableDropMetadataMutation then {} else sp.explicitSizes
      stmts }

def oldPhysicalize (sp : ScheduledProgram) : Option ScheduledProgram :=
  let scan : ScanProgram :=
    { decls := sp.decls, stmts := sp.stmts, env := sp.env, extNames := sp.extNames }
  match splitNonlins scan |>.run 0 with
  | .error _ _ => none
  | .ok split _ => some {
      decls := split.decls, stmts := split.stmts, env := split.env,
      extNames := split.extNames, explicitSizes := sp.explicitSizes }

def routeOf (sp : ScheduledProgram) : Option ThreadedComposed :=
  match route sp |>.run 0 with
  | .ok tc _ => some tc
  | .error .. => none

def acsetOf (sp : ScheduledProgram) :=
  (routeOf sp).map fromThreadedComposed

def routeAndAcsetRoundTrip (sp : ScheduledProgram) : Bool :=
  match routeOf sp with
  | none => false
  | some tc => toThreadedComposed (fromThreadedComposed tc) == tc

inductive PayloadClass
  | represented
  | opaqueMask
  | opaqueIverson
  | opaqueMetadata
  | opaqueScanPre
  deriving DecidableEq, Repr

structure NamedPayloadFixture where
  name : String
  logical : ScheduledProgram
  payloadClass : PayloadClass

def pointwise (name : String) (fn : PointwiseFn) : NamedPayloadFixture :=
  { name, payloadClass := .represented
    logical := one (.plain (.assign "Y" [.free i]
      { body := readBody "X" [.axis i], nonlin := .pointwise fn })) }

def axiswise (name : String) (fn : AxiswiseFn) : NamedPayloadFixture :=
  { name, payloadClass := .represented
    logical := one (.plain (.assign "Y" [.free i, .freeNorm j]
      { body := readBody "X" [.axis i, .axis j], nonlin := .axiswise fn none })) }

def aggregate (name : String) (agg : AggOp) : NamedPayloadFixture :=
  { name, payloadClass := .represented
    logical := one (.plain (.assign "Y" [.free i]
      { body := readBody "X" [.axis i, .axis k], nonlin := .pointwise .relu, agg })) }

def causal : BoolExpr := .rel .le (.embed (.axis j)) (.embed (.axis i))
def antiCausal : BoolExpr := .not causal

def masked (name : String) (mask : BoolExpr) : NamedPayloadFixture :=
  { name, payloadClass := .opaqueMask
    logical := one (.plain (.assign "Y" [.free i, .freeNorm j]
      { body := readBody "X" [.axis i, .axis j],
        nonlin := .axiswise .softmax (some mask) })) }

def band : BoolExpr :=
  .and (.rel .le (.embed (.axis i)) (.embed (.axis j)))
    (.rel .lt (.embed (.axis j)) (.embed (.shift i 2)))

def iversonFixture (name : String) (predicate : BoolExpr) : NamedPayloadFixture :=
  { name, payloadClass := .opaqueIverson
    logical := one (.plain (.assign "Y" [.free i]
      { body := { terms := [{ factors := [
          .read "X" [.axis i], .iverson predicate] }] },
        nonlin := .pointwise .relu })) }

def metadataFixture (name : String) (decl : Decl) : NamedPayloadFixture :=
  { name, payloadClass := .opaqueMetadata
    logical := one (.plain (.assign "Y" [.free i]
      { body := readBody "X" [.axis i], nonlin := .identity }))
      [decl] (({} : DeclEnv).insert "Meta" decl) {"X"}
      (({} : Std.HashMap UID Nat).insert i.uid 4) }

def affineFixture (name : String) (idx : IdxExpr) : NamedPayloadFixture :=
  { name, payloadClass := .represented
    logical := one (.plain (.assign "Y" [.free i]
      { body := readBody "X" [idx], nonlin := .pointwise .relu })) }

def nestedStepA : BrBaseP := {
  op := .relu
  degree := []
  inputWeaves := []
  outputWeaves := [[]]
  reindexings := []
}

def nestedStepB : BrBaseP := {
  op := .softmax
  degree := []
  inputWeaves := []
  outputWeaves := [[.tiled]]
  reindexings := []
}

def nestedA : ThreadedComposed :=
  { steps := [nestedStepA], routing := [[]], nExternal := 0 }

def nestedB : ThreadedComposed :=
  { steps := [nestedStepB], routing := [[]], nExternal := 0 }

def scanPreFixture (name : String) (nested : ThreadedComposed) : NamedPayloadFixture :=
  { name, payloadClass := .opaqueScanPre
    logical := one (.scanPre "S" i nested) [] {} ∅ }

def causalMaskFixture := masked "causal-mask" causal
def negatedMaskFixture := masked "negated-causal-mask" antiCausal
def bandIversonFixture := iversonFixture "band-iverson" band
def negatedIversonFixture := iversonFixture "negated-band-iverson" (.not band)
def tensorMetadataFixture := metadataFixture "tensor-metadata" (.tensor "Meta" [i])
def predicateMetadataFixture := metadataFixture "predicate-metadata" (.predicate "Meta" [i])
def scanPreOperationFixture := scanPreFixture "scan-pre-operation" nestedA
def scanPreWeaveFixture := scanPreFixture "scan-pre-output-weave" nestedB

def fixtures : List NamedPayloadFixture := [
  pointwise "sigmoid" .sigmoid,
  pointwise "tanh" .tanh,
  pointwise "gelu" .gelu,
  pointwise "leaky-relu" .leakyrelu,
  axiswise "normalize" .normalize,
  axiswise "l2-normalize" .l2normalize,
  aggregate "relu-over-max" .max,
  aggregate "relu-over-min" .min,
  causalMaskFixture,
  negatedMaskFixture,
  bandIversonFixture,
  negatedIversonFixture,
  tensorMetadataFixture,
  predicateMetadataFixture,
  affineFixture "scale-read" (.scale 2 i),
  affineFixture "shift-read" (.shift i 1),
  affineFixture "general-affine-read" (.affine 1 [(2, i), (-1, j)]),
  scanPreOperationFixture,
  scanPreWeaveFixture
]

def plainPayloadConserved (logical physical : ScheduledProgram) : Bool :=
  match logical.stmts, physical.stmts with
  | [.plain (.assign logicalName logicalSlots rhs)],
      [.plain (.assign _ producerSlots producer),
       .plain (.assign publishedName consumerSlots consumer)] =>
      producer.body == rhs.body &&
      producer.agg == rhs.agg &&
      producer.nonlin == .identity &&
      producerSlots == logicalSlots.map (fun
        | .freeNorm a => .free a
        | slot => slot) &&
      publishedName == logicalName &&
      consumerSlots == logicalSlots &&
      consumer.nonlin == rhs.nonlin &&
      consumer.agg == .sum
  | [.plain logicalStmt], [.plain physicalStmt] => logicalStmt == physicalStmt
  | _, _ => false

def metadataConserved (logical physical : ScheduledProgram) : Bool :=
  logical.decls == physical.decls &&
  logical.extNames == physical.extNames &&
  logical.explicitSizes.toList == physical.explicitSizes.toList &&
  logical.env.toList == physical.env.toList

def scanPreConserved (logical physical : ScheduledProgram) : Bool :=
  match logical.stmts, physical.stmts with
  | [.scanPre logicalName logicalAxis logicalBody],
      [.scanPre physicalName physicalAxis physicalBody] =>
      logicalName == physicalName && logicalAxis == physicalAxis &&
        logicalBody == physicalBody
  | _, _ => false

def payloadConserved (fixture : NamedPayloadFixture) : Bool :=
  let physical := physicalize fixture.logical
  metadataConserved fixture.logical physical &&
    match fixture.logical.stmts with
    | [.scanPre ..] => scanPreConserved fixture.logical physical
    | _ => plainPayloadConserved fixture.logical physical

def representedMatchesOld (fixture : NamedPayloadFixture) : Bool :=
  match fixture.payloadClass, oldPhysicalize fixture.logical with
  | .represented, some old =>
      routeOf old == routeOf (physicalize fixture.logical) &&
      acsetOf old == acsetOf (physicalize fixture.logical) &&
      routeAndAcsetRoundTrip (physicalize fixture.logical)
  | .represented, none => false
  | _, _ => true

#guard fixtures.length == 19
#guard (fixtures.map (·.name)).eraseDups.length == fixtures.length
#guard fixtures.all payloadConserved
#guard fixtures.all representedMatchesOld
#guard fixtures.all fun fixture => routeAndAcsetRoundTrip (physicalize fixture.logical)

-- These equalities pin categorical opacity only; physical payload assertions above prove the
-- changed mask, predicate, metadata, and nested scan body survived before routing.
#guard routeOf (physicalize causalMaskFixture.logical) ==
  routeOf (physicalize negatedMaskFixture.logical)
#guard acsetOf (physicalize causalMaskFixture.logical) ==
  acsetOf (physicalize negatedMaskFixture.logical)
#guard routeOf (physicalize bandIversonFixture.logical) ==
  routeOf (physicalize negatedIversonFixture.logical)
#guard acsetOf (physicalize bandIversonFixture.logical) ==
  acsetOf (physicalize negatedIversonFixture.logical)
#guard routeOf (physicalize tensorMetadataFixture.logical) ==
  routeOf (physicalize predicateMetadataFixture.logical)
#guard acsetOf (physicalize tensorMetadataFixture.logical) ==
  acsetOf (physicalize predicateMetadataFixture.logical)
#guard routeOf (physicalize scanPreOperationFixture.logical) ==
  routeOf (physicalize scanPreWeaveFixture.logical)
#guard acsetOf (physicalize scanPreOperationFixture.logical) ==
  acsetOf (physicalize scanPreWeaveFixture.logical)

#guard mutateDropMask false (.axiswise .softmax (some causal)) ==
  .axiswise .softmax (some causal)
#guard mutateAggregation false .max == .max

end PayloadConservationSeed

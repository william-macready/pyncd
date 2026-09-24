import LeanNCD.Eval.Plan.EvalPlan

/-!
# Wave C C3 graph checker tests

Reference graphs plus mutation coverage for `checkPlan`'s wiring invariants (slot availability,
production order) on top of `checkAssign`'s already-tested local invariants.

Migrated (Wave F F3, Task 4) to `RawEvalPlan`'s current shape: no `version` field (removed §2.3),
`steps : Array PlanStep` (every entry wrapped in `.assign`), and `checkPlan`'s error type
generalized to `PlanStepError` (every `PlanError`-shaped expectation below wrapped in `.assign`).
-/

namespace LeanNCD.Eval.Plan.GraphCheckTest
open LeanNCD.Eval.Plan

/-- An identity read: `Y[i] := X[slot][i]`. -/
def idRead (slot : TensorSlot) : ReadPlan :=
  { sourceSlot := slot, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[2], oobPolicy := .zeroPad }

/-- An identity node: destination `dest` copies `src` verbatim. -/
def idNode (dest src : TensorSlot) : AssignPlan :=
  { contextShape := #[], destinationSlot := dest, outputShape := #[2]
  , terms := #[{ iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read (idRead src)] }]
  , algebra := admittedAlgebra }

/-!
## Chain: X -> Y -> Z
-/

def chainSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }   -- 0 = X (input)
   , { shape := #[2], dtype := .f64 }   -- 1 = Y
   , { shape := #[2], dtype := .f64 } ] -- 2 = Z

def chainPlan : RawEvalPlan :=
  { tensorSigs := chainSigs, inputSlots := #[0]
  , steps := #[.assign (idNode 1 0), .assign (idNode 2 1)] }

def isOk : Except PlanStepError CheckedEvalPlan → Bool
  | .ok _ => true | .error _ => false

def errOf : Except PlanStepError CheckedEvalPlan → Option PlanStepError
  | .ok _ => none | .error e => some e

-- the chain is accepted
#guard isOk (checkPlan chainPlan)

/-!
## Diamond / fan-out with an unused input: X -> A, X -> B, {A, B} -> C; slot 4 (`W`) is a second
input never read by any node.
-/

def diamondSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }   -- 0 = X (input)
   , { shape := #[2], dtype := .f64 }   -- 1 = A
   , { shape := #[2], dtype := .f64 }   -- 2 = B
   , { shape := #[2], dtype := .f64 }   -- 3 = C
   , { shape := #[2], dtype := .f64 } ] -- 4 = W (input, unused)

/-- `C[i] := A[i] + B[i]`: two single-factor terms, folded by `reduceOp = add`. -/
def nodeC : AssignPlan :=
  { contextShape := #[], destinationSlot := 3, outputShape := #[2]
  , terms := #[ { iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
                , factors := #[.read (idRead 1)] }
              , { iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
                , factors := #[.read (idRead 2)] } ]
  , algebra := admittedAlgebra }

def diamondPlan : RawEvalPlan :=
  { tensorSigs := diamondSigs, inputSlots := #[0, 4]
  , steps := #[.assign (idNode 1 0), .assign (idNode 2 0), .assign nodeC]
   }

-- the diamond (fan-out + convergence + an unused input) is accepted
#guard isOk (checkPlan diamondPlan)

/-!
## Mutations
-/

-- duplicate input slot
#guard errOf (checkPlan { diamondPlan with inputSlots := #[0, 0] })
  == some (.assign (.duplicateInputSlot 0))

-- input slots not ordered (decreasing, not equal)
#guard errOf (checkPlan { diamondPlan with inputSlots := #[4, 0] })
  == some (.assign (.inputSlotsNotOrdered 0))

-- input slot out of range
#guard errOf (checkPlan { diamondPlan with inputSlots := #[0, 99] })
  == some (.assign (.slotOutOfRange 99 5))

-- node-level destination slot out of range: nodeA (index 0) targets slot 99, which doesn't exist
-- in the 5-slot table. Wrapped with node context via `.nodeError`, matching every other per-node
-- failure in this loop.
#guard errOf (checkPlan
    { diamondPlan with steps := #[.assign (idNode 99 0), .assign (idNode 2 0), .assign nodeC] })
  == some (.assign (.nodeError 0 (.slotOutOfRange 99 5)))

-- node-level source slot out of range: nodeC (index 2) reads slot 99 via its first term/first
-- factor instead of slot 1. Wrapped with node context, same as the destination case above.
#guard errOf (checkPlan
  { diamondPlan with steps := #[.assign (idNode 1 0), .assign (idNode 2 0),
      .assign { nodeC with terms := #[{ nodeC.terms[0]! with factors := #[.read (idRead 99)] }, nodeC.terms[1]!] }] })
  == some (.assign (.nodeError 2 (.slotOutOfRange 99 5)))

-- invalid forward read: nodeC (index 2) reads slot 3 (its own not-yet-produced destination) via
-- its first term/first factor instead of slot 1
#guard errOf (checkPlan
  { diamondPlan with steps := #[.assign (idNode 1 0), .assign (idNode 2 0),
      .assign { nodeC with terms := #[{ nodeC.terms[0]! with factors := #[.read (idRead 3)] }, nodeC.terms[1]!] }] })
  == some (.assign (.invalidForwardRead 2 0 0 3))

-- reordering a DEPENDENT node is rejected outright, not merely "a different but valid result":
-- moving nodeC (which reads slots 1 and 2) before the nodes that produce them is an
-- invalidForwardRead, not a permitted reordering — "reordering preserves results only when
-- dependencies permit it" (A.7) is enforced by rejection here, not by computing a wrong answer.
#guard errOf (checkPlan
    { diamondPlan with steps := #[.assign nodeC, .assign (idNode 1 0), .assign (idNode 2 0)] })
  == some (.assign (.invalidForwardRead 0 0 0 1))

-- duplicate destination: nodeB (index 1) overwritten to also target slot 1 (nodeA's destination)
#guard errOf (checkPlan
    { diamondPlan with steps := #[.assign (idNode 1 0), .assign (idNode 1 0), .assign nodeC] })
  == some (.assign (.duplicateDestination 1 0 1))

-- input slot overwritten: a node targets input slot 4 (W)
#guard errOf (checkPlan
    { diamondPlan with steps := #[.assign (idNode 4 0), .assign (idNode 2 0), .assign nodeC] })
  == some (.assign (.inputSlotOverwritten 4 0))

-- missing production: drop nodeC, so slot 3 (C) is declared in tensorSigs but never produced
#guard errOf (checkPlan { diamondPlan with steps := #[.assign (idNode 1 0), .assign (idNode 2 0)] })
  == some (.assign (.missingProduction 3))

-- local error propagated with node context: nodeA's own outputShape is mutated to disagree with
-- its destination signature, which checkAssign already rejects (destinationShapeMismatch),
-- wrapped here with the node index that produced it
#guard errOf (checkPlan
  { diamondPlan with steps :=
      #[.assign { idNode 1 0 with outputShape := #[3] }, .assign (idNode 2 0), .assign nodeC] })
  == some (.assign (.nodeError 0 (.destinationShapeMismatch #[3] #[2])))

/-!
## Thread 4 (Task 2) regressions: `sourceSlot == destinationSlot` unreachability inside
`checkPointwise`/`checkAxiswise` relies on `checkPlan`'s own availability discipline — these two
fixtures pin that reliance at the `checkPlan` level, not by adding a redundant guard inside the
Nonlin checkers themselves.
-/

/-- Minimal 2-slot table shared by both self-aliasing fixtures below. -/
def selfAliasSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }, { shape := #[2], dtype := .f64 } ]

/-- Never-produced case: the only step reads and writes slot 1, which is neither an input slot
    nor produced by any earlier step. `available[1]` starts `false`, so the destination-check
    (which only rejects an ALREADY-produced destination) passes, and the source-check then finds
    slot 1 unavailable — `invalidForwardRead`, not `duplicateDestination`. -/
def neverProducedSelfAliasPlan : RawEvalPlan :=
  { tensorSigs := selfAliasSigs, inputSlots := #[]
  , steps := #[.pointwise { sourceSlot := 1, destinationSlot := 1, shape := #[2], fn := .relu }]
   }

#guard errOf (checkPlan neverProducedSelfAliasPlan) == some (.assign (.invalidForwardRead 0 0 0 1))

/-- Already-produced case: an `.assign` produces slot 1 first, then a `.pointwise` step reads and
    writes that same slot 1. `available[1]` is already `true` by the time this step's own checks
    run, so the destination-check fires first — `duplicateDestination`, not `invalidForwardRead`. -/
def duplicateSelfAliasPlan : RawEvalPlan :=
  { tensorSigs := selfAliasSigs, inputSlots := #[0]
  , steps := #[.assign (idNode 1 0)
              , .pointwise { sourceSlot := 1, destinationSlot := 1, shape := #[2], fn := .relu }]
   }

#guard errOf (checkPlan duplicateSelfAliasPlan) == some (.assign (.duplicateDestination 1 0 1))

/-!
## `checkPointwise` failure surfacing as `PlanStepError.nonlin` (review finding, Important #2)

Mirrors `EvalPlanTest.lean`'s `scanFailPlan`/`.scan` fixture for the sibling `.nonlin`
constructor: nothing in the original diff pinned that a `checkPointwise`/`checkAxiswise`
failure surfaces as `.nonlin stepIndex cause` rather than being swallowed or mis-wrapped
through `.assign`.
-/

def nonlinFailSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }, { shape := #[2], dtype := .f64 } ]

-- The step's declared `shape := #[3]` disagrees with slot 0's actual signature shape `#[2]`;
-- `checkNonlinIO` catches this as `sourceShapeMismatch` before any dense evaluation is possible.
def nonlinFailPlan : RawEvalPlan :=
  { tensorSigs := nonlinFailSigs, inputSlots := #[0]
  , steps := #[.pointwise { sourceSlot := 0, destinationSlot := 1, shape := #[3], fn := .relu }]
   }

#guard errOf (checkPlan nonlinFailPlan) == some (.nonlin 0 (.sourceShapeMismatch #[3] #[2]))

/-!
## `CheckedEvalPlan` privacy (compile-time check, folded into this file per A.3's module list —
no separate privacy-test module for C3)
-/

-- normal construction via the checker succeeds
#guard (checkPlan diamondPlan).toOption.isSome

-- must NOT compile: def smuggled : CheckedEvalPlan := ⟨diamondPlan, #[], .float64⟩

/-! ## f32 slice Task 2: graph-level storage kind, mixed tables, and the binary32 step-kind fragment

Fixtures 6, 7, 8, 14's `f32UnsupportedStepOrder` half, and 16. All built from `chainPlan` /
`nonlinFailPlan` above, changing only the fields each case names. F32-B Task 3 admitted the two
nonlinearity step kinds in a binary32 graph: fixture 8 and fixture 16's axiswise case are now
acceptances (F32-B fixture 3.10), and `f32UnsupportedStepOrder` is re-pointed at a scatter (F32-B
fixture 3.11). -/

def storageOf : Except PlanStepError CheckedEvalPlan → Option LeanNCD.StorageKind
  | .ok c => some c.storageKind | .error _ => none

/-! ### Fixture 6: an accepted one-node f32 graph, and a located mixed-table rejection -/

/-- `chainPlan` reduced to its FIRST step (`.assign (idNode 1 0)`) and its first two signatures,
    both retagged `f32`, with the binary32 sum-product algebra. Everything else — shapes, the
    identity read, `inputSlots` — is `chainPlan`'s own. -/
def f32OneNodePlan : RawEvalPlan :=
  { tensorSigs := #[ { shape := #[2], dtype := .f32 }, { shape := #[2], dtype := .f32 } ]
  , inputSlots := #[0]
  , steps := #[.assign { idNode 1 0 with algebra := admittedAlgebraF32 }] }

#guard isOk (checkPlan f32OneNodePlan)
#guard storageOf (checkPlan f32OneNodePlan) == some LeanNCD.StorageKind.float32

-- Control: the ORIGINAL binary64 chain records `.float64`, so fixture 6's acceptance is not an
-- implementation that stamps `.float32` on everything.
#guard storageOf (checkPlan chainPlan) == some LeanNCD.StorageKind.float64

/-- `chainPlan` with a fourth signature appended that is NOT added to `inputSlots`, and dtypes
    `[f32, f32, f64, f64]`. Two trailing mismatches, so first-offending-slot and
    last-offending-slot are distinguishable; four entries, so the reported slot `2` is distinct from
    the table-size count `4`. The unused non-input slot 3 also makes the plan wiring-invalid
    (`missingProduction 3`), which is deliberate: it gives the "storage derivation runs BEFORE outer
    graph wiring" claim a fixture that can fail if the order is ever reversed. -/
def f32MixedTablePlan : RawEvalPlan :=
  { chainPlan with
    tensorSigs := #[ { shape := #[2], dtype := .f32 }
                   , { shape := #[2], dtype := .f32 }
                   , { shape := #[2], dtype := .f64 }
                   , { shape := #[2], dtype := .f64 } ] }

#guard errOf (checkPlan f32MixedTablePlan)
  == some (.assign (.mixedStorageKinds 2 .f32 .f64))

/-! ### Fixture 7: mixed real/Boolean graphs, in BOTH precisions

These fail if the implementation compares concrete dtypes instead of storage kinds, or permanently
assigns `bool` to Float64 storage. -/

-- f64 case: input slot 0 alone retagged `bool`; both f64 destination nodes read that Boolean
-- source, which `checkAssign` admits (gathering is dtype-blind).
def f64BoolChainPlan : RawEvalPlan :=
  { chainPlan with
    tensorSigs := #[ { shape := #[2], dtype := .bool }
                   , { shape := #[2], dtype := .f64 }
                   , { shape := #[2], dtype := .f64 } ] }

#guard isOk (checkPlan f64BoolChainPlan)
#guard storageOf (checkPlan f64BoolChainPlan) == some LeanNCD.StorageKind.float64

-- f32 case: signatures `[f32, bool, f32]`. Node 1 writes the Boolean slot (Boolean algebra) reading
-- the f32 slot 0; node 2 writes the f32 slot 2 reading that Boolean slot 1 — so BOTH an f32→bool
-- and a bool→f32 read occur, in one graph whose derived carrier is `.float32`.
def f32BoolChainPlan : RawEvalPlan :=
  { tensorSigs := #[ { shape := #[2], dtype := .f32 }
                   , { shape := #[2], dtype := .bool }
                   , { shape := #[2], dtype := .f32 } ]
  , inputSlots := #[0]
  , steps := #[ .assign { idNode 1 0 with algebra := admittedAlgebraBool }
              , .assign { idNode 2 1 with algebra := admittedAlgebraF32 } ] }

#guard isOk (checkPlan f32BoolChainPlan)
#guard storageOf (checkPlan f32BoolChainPlan) == some LeanNCD.StorageKind.float32

/-! ### Fixture 8: a structurally valid pointwise step in an f32 graph

`nonlinFailPlan` with its deliberately mismatched pointwise `shape` corrected from `#[3]` to `#[2]`
and both signatures retagged `f32`. Originally the CAPABILITY rejection `f32UnsupportedStep 0
.pointwise`; since F32-B Task 3 (fixture 3.10) it is ACCEPTED, and the graph records `.float32` —
which only `checkPointwiseF32` can produce here, since the binary64 `checkPointwise` refuses an
`.f32` destination (`dtypeNotAdmitted 1 .f32`). -/
def f32PointwiseStep : RawPointwisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[2], fn := .relu }

def f32PointwisePlan : RawEvalPlan :=
  { tensorSigs := #[ { shape := #[2], dtype := .f32 }, { shape := #[2], dtype := .f32 } ]
  , inputSlots := #[0]
  , steps := #[.pointwise f32PointwiseStep] }

#guard isOk (checkPlan f32PointwisePlan)
#guard storageOf (checkPlan f32PointwisePlan) == some LeanNCD.StorageKind.float32

-- Control: the SAME shape-corrected pointwise node in a BINARY64 table is accepted and records
-- `.float64`, so fixture 8's `.float32` is the table's kind and not a constant.
#guard storageOf (checkPlan { f32PointwisePlan with
  tensorSigs := #[ { shape := #[2], dtype := .f64 }, { shape := #[2], dtype := .f64 } ] })
  == some LeanNCD.StorageKind.float64

/-! ### Fixture 14 (second half): `f32UnsupportedStepOrder`

A VALID f32 assignment at step 0, a VALID f32 pointwise node at step 1, and a scatter at step 2
(F32-B fixture 3.11 re-pointed this from the `[assign, pointwise]` graph that reported index 1,
now that pointwise is admitted). The reported error must be `f32UnsupportedStep 2 .scatter`: the
original outer index. A capability pass over only the not-yet-admitted step kinds (a filtered
sublist) would report `0`, and one over only the assignments would report `1`.

The scatter is `f32Scatter`'s shape (fixture 16 below) renumbered to read the pointwise destination
(slot 2, `[2]`) and write a fresh `f32` slot 3 (`[4]`, `Out[2*i] := Z[i]`). The capability pass runs
before any wiring or local check, so the verdict does not depend on that geometry; it is built
well-formed anyway, which the binary64 control below pins. -/
def stepOrderScatter (alg : ContractionAlgebra) : ScatterPlan :=
  { compute := { contextShape := #[], destinationSlot := 3, outputShape := #[2]
               , terms := #[{ iterationShape := #[2], contextPos := #[], outputPos := #[0]
                            , reductionPos := #[], factors := #[.read (idRead 2)] }]
               , algebra := alg }
  , destShape := #[4], outCoeffs := #[#[2]], outBias := #[0]
  , fill := alg.reduceId, reduce := .rejectCollisions }

def f32UnsupportedStepOrder : RawEvalPlan :=
  { tensorSigs := #[ { shape := #[2], dtype := .f32 }
                   , { shape := #[2], dtype := .f32 }
                   , { shape := #[2], dtype := .f32 }
                   , { shape := #[4], dtype := .f32 } ]
  , inputSlots := #[0]
  , steps := #[ .assign { idNode 1 0 with algebra := admittedAlgebraF32 }
              , .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[2], fn := .relu }
              , .scatter (stepOrderScatter admittedAlgebraF32) ] }

#guard errOf (checkPlan f32UnsupportedStepOrder) == some (.f32UnsupportedStep 2 .scatter)

-- Control: the same graph in binary64 (signatures and both algebras retagged) is ACCEPTED, so the
-- scatter above is well-formed and the rejection is the capability verdict alone.
#guard isOk (checkPlan
  { tensorSigs := #[ { shape := #[2], dtype := .f64 }
                   , { shape := #[2], dtype := .f64 }
                   , { shape := #[2], dtype := .f64 }
                   , { shape := #[4], dtype := .f64 } ]
  , inputSlots := #[0]
  , steps := #[ .assign (idNode 1 0)
              , .pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[2], fn := .relu }
              , .scatter (stepOrderScatter admittedAlgebra) ] })

/-! ### Fixture 16: every remaining non-assignment `PlanStep` constructor, through outer `checkPlan`

One raw graph per remaining step kind, each with a HOMOGENEOUS f32 signature context and the step
shape cloned from that kind's own accepted donor elsewhere in this suite — `ScatterCheckTest`'s
`upScatter` (`Out[2*i] := X[i]`, `X : [3]`, extent 6), `ScanTest`'s `linearScan` (`S[iterAt l 0] :=
S0`; `S[iterNext l] := S[l] + X[l]`), and `NonlinCheckTest`'s `baselineAxiswise` (softmax over axis
0). Together with fixture 8's pointwise case these exhaust `PlanStep`'s four non-assignment
constructors.

The scatter and scan cases are rejections. Each is paired with the same graph under a BINARY64
table, which must NOT report `f32UnsupportedStep` — otherwise the fixture would pass for an
implementation that refused these step kinds unconditionally rather than for binary32 specifically.
The axiswise case is an ACCEPTANCE since F32-B Task 3 (fixture 3.10). -/

def isF32Unsupported (i : Nat) (k : PlanStepKind) : Except PlanStepError CheckedEvalPlan → Bool
  | .error (.f32UnsupportedStep i' k') => i == i' && k == k'
  | _ => false

-- Scatter. `upScatter`'s geometry verbatim, with the compute half's algebra and the coherent `fill`
-- moved to the binary32 table so the plan is f32 throughout rather than half-converted.
def f32ScatterCompute : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
                                    , sourceShape := #[3], oobPolicy := .zeroPad }] }]
  , algebra := admittedAlgebraF32 }

def f32Scatter : ScatterPlan :=
  { compute := f32ScatterCompute, destShape := #[6], outCoeffs := #[#[2]], outBias := #[0]
  , fill := admittedAlgebraF32.reduceId, reduce := .rejectCollisions }

def f32ScatterPlan : RawEvalPlan :=
  { tensorSigs := #[ { shape := #[3], dtype := .f32 }, { shape := #[6], dtype := .f32 } ]
  , inputSlots := #[0], steps := #[.scatter f32Scatter] }

#guard errOf (checkPlan f32ScatterPlan) == some (.f32UnsupportedStep 0 .scatter)

#guard !(isF32Unsupported 0 .scatter (checkPlan
  { f32ScatterPlan with
    tensorSigs := #[ { shape := #[3], dtype := .f64 }, { shape := #[6], dtype := .f64 } ] }))

-- Scan. `linearScan`'s geometry verbatim: outer slots `0 = S0` (scalar), `1 = X : [3]`,
-- `2 = S : [3]`; `historyExtents := #[3]`, so `stepExtents = #[2]`.
def f32ScanState : StateSlot :=
  { destSlot := 2, advancingDims := #[0], materialization := .completeHistory }

def f32ScanBaseBlock : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[{ shape := #[], dtype := .f32 }]
  , inputs := #[0], steps := #[], outputs := #[0] }

def f32ScanStepAssign : AssignPlan :=
  { contextShape := #[2], destinationSlot := 2, outputShape := #[]
  , terms := #[ { iterationShape := #[2], contextPos := #[0], outputPos := #[], reductionPos := #[]
                , factors := #[.read { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
                                     , sourceShape := #[3], oobPolicy := .zeroPad }] }
              , { iterationShape := #[2], contextPos := #[0], outputPos := #[], reductionPos := #[]
                , factors := #[.read { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }
                                     , sourceShape := #[3], oobPolicy := .zeroPad }] } ]
  , algebra := admittedAlgebraF32 }

def f32ScanStepBlock : RawPlanBlock :=
  { contextShape := #[2]
  , tensorSigs := #[ { shape := #[3], dtype := .f32 }, { shape := #[3], dtype := .f32 }
                   , { shape := #[], dtype := .f32 } ]
  , inputs := #[0, 1], steps := #[.assign f32ScanStepAssign], outputs := #[2] }

def f32Scan : RawScanPlan :=
  { states := #[f32ScanState]
  , baseBlock := f32ScanBaseBlock
  , baseCaptures := #[{ inputSlot := 0, source := .external 0 }]
  , baseWrites := #[{ outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[]], bias := #[0] } }]
  , stepBlock := f32ScanStepBlock
  , stepCaptures := #[{ inputSlot := 0, source := .external 1 }, { inputSlot := 1, source := .state 0 }]
  , stepWrites := #[{ outputSlot := 2, stateIndex := 0, map := { coeffs := #[#[1]], bias := #[1] } }]
  , historyExtents := #[3]
  , iterationOrder := .axisZeroFastest, boundaryPolicy := .zeroThenBaseOverlay
  , snapshotPolicy := .immutablePreStep }

def f32ScanPlan : RawEvalPlan :=
  { tensorSigs := #[ { shape := #[], dtype := .f32 }, { shape := #[3], dtype := .f32 }
                   , { shape := #[3], dtype := .f32 } ]
  , inputSlots := #[0, 1], steps := #[.scan f32Scan] }

#guard errOf (checkPlan f32ScanPlan) == some (.f32UnsupportedStep 0 .scan)

#guard !(isF32Unsupported 0 .scan (checkPlan
  { f32ScanPlan with
    tensorSigs := #[ { shape := #[], dtype := .f64 }, { shape := #[3], dtype := .f64 }
                   , { shape := #[3], dtype := .f64 } ] }))

-- Axiswise. `baselineAxiswise`'s own field values (`softmax` over axis 0, shape `#[2]`).
def f32AxiswiseStep : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 1, shape := #[2], axisPos := 0, fn := .softmax }

def f32AxiswisePlan : RawEvalPlan :=
  { tensorSigs := #[ { shape := #[2], dtype := .f32 }, { shape := #[2], dtype := .f32 } ]
  , inputSlots := #[0], steps := #[.axiswise f32AxiswiseStep] }

#guard isOk (checkPlan f32AxiswisePlan)
#guard storageOf (checkPlan f32AxiswisePlan) == some LeanNCD.StorageKind.float32

-- Control: the binary64 twin is accepted as `.float64`.
#guard storageOf (checkPlan
  { f32AxiswisePlan with
    tensorSigs := #[ { shape := #[2], dtype := .f64 }, { shape := #[2], dtype := .f64 } ] })
  == some LeanNCD.StorageKind.float64

/- `PlanStepKind.assign` is deliberately never a `f32UnsupportedStep` payload — an assignment is
   a step kind a binary32 graph admits (fixture 6). `PlanStep.kind` is still total over
   it; named directly so the vocabulary's own `.assign` answer stays exercised. -/
#guard (PlanStep.kind (.assign (idNode 1 0))) == PlanStepKind.assign

end LeanNCD.Eval.Plan.GraphCheckTest

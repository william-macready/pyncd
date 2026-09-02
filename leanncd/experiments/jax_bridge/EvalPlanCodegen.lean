import LeanNCD.Eval.Plan.Adapter
import LeanNCD.Eval.Plan.Executable

/-!
# Wave C JAX code generation (`docs/superpowers/plans/2026-08-10-jax-full-affine-semantics.md`, Task 2)

The reusable Lean → Python code generator shared by every JAX-bridge driver. Split out of the
original one-file smoke (`EvalPlanSmoke.lean`) so the driver keeps only fixture selection and module
assembly; this module owns the actual lowering. Two explicit modes, never a silent fallback between
them (plan "Two explicit lowerings"):

* `einsumOnly` — the completed smoke path. Recognizes a projection-only contraction and emits a real
  `jnp.einsum` call, rejecting every non-projection read with a closed `JaxCodegenError`.
* `affineReference` — accepts every current Wave C `CheckedEvalPlan`. It precomputes exact
  per-factor affine lookup tables (safe index + validity mask) in Lean using the shared coordinate
  primitives (`Eval.Plan.Coordinates`), and emits static plan DATA that the committed generic
  runtime (`evalplan_affine_runtime.py`) interprets with ordered factor/reduction/term folds. No
  `einsum`/`jnp.sum`/tree reduction is used on this path.

Kept out of the default build (registered only in the non-default `JaxExperiment` `lean_lib`), no
`LeanNCD` public API touched, no JAX dependency added to this project's toolchain. This module
imports only production `LeanNCD` modules.
-/

namespace JaxBridge

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

/-! ## 1. Closed einsum-codegen diagnostics (unchanged from the smoke) -/

/-- Every way the narrow `einsum`-only backend refuses an otherwise-checked plan. Closed, with a
    node/term/factor/row location on every constructor that has one available. -/
inductive JaxCodegenError
  | emptyTerm             (nodeIndex termIndex : Nat)
  | emptyAssign           (nodeIndex : Nat)
  | nonzeroAffineBias     (nodeIndex termIndex factorIndex rowIndex : Nat) (biasVal : Int)
  | nonProjectionRow      (nodeIndex termIndex factorIndex rowIndex : Nat) (row : Array Int)
  | uncoveredPosition     (nodeIndex termIndex position : Nat)
  | rankTooLarge          (nodeIndex termIndex rank : Nat)
  | bindingSlotOutOfRange (slot tableSize : Nat)
  | missingFixtureInput   (name : String)
  | labelTableExhausted   (nodeIndex termIndex position : Nat)
  -- The one located rejection for any checked step this JAX backend cannot lower to a supported
  -- kernel: a `.pointwise`, `.axiswise`, or `.scan` node (Thread 4 / Wave F) has no affine/einsum
  -- lowering here, so routing it yields this error carrying the FIRST such step's outer-graph index
  -- (not a per-term/factor locator — these kinds have no term/factor structure). Assignment steps
  -- never reach it; they route through the existing affine/einsum path unchanged.
  | unsupportedStep       (stepIndex : Nat)
  -- A `.iverson` predicate factor inside an assignment term: this JAX backend lowers only affine
  -- reads to einsum/affine-table kernels, so a term carrying an Iverson factor is rejected here with
  -- its node/term/factor location. (Predicate/mask execution is not lowered to JAX — Global
  -- Constraints. Reads route through the unchanged path.)
  | iversonFactor         (nodeIndex termIndex factorIndex : Nat)
  | unsupportedAssignment (nodeIndex : Nat) (cause : JaxSupportError)
  deriving DecidableEq, BEq, Repr, Inhabited

/-! ## 2. Deterministic Python string rendering (shared by both modes) -/

/-- Python double-quoted string-literal quoting for source identifiers. -/
def pyStrLit (s : String) : String :=
  let escapeChar : Char → String
    | '\\' => "\\\\"
    | '"'  => "\\\""
    | '\n' => "\\n"
    | '\t' => "\\t"
    | '\r' => "\\r"
    | c    => String.singleton c
  "\"" ++ String.join (s.toList.map escapeChar) ++ "\""

/-- Python tuple literal for a shape, e.g. `#[2, 1]` ↦ `"(2, 1)"`, `#[2]` ↦ `"(2,)"`,
    `#[] ↦ "()"`. The trailing comma on the singleton case is required Python tuple syntax. -/
def pyShapeTuple (shape : Array Nat) : String :=
  match shape.size with
  | 0 => "()"
  | 1 => s!"({shape[0]!},)"
  | _ => "(" ++ String.intercalate ", " (shape.toList.map toString) ++ ")"

/-- Python list literal of `UInt64` bit patterns (`Float.toBits` payloads). -/
def pyUInt64ListLit (xs : Array UInt64) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map toString) ++ "]"

/-- Python list literal of `Nat`s. -/
def pyNatListLit (xs : Array Nat) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map toString) ++ "]"

/-- Python list literal of `Int`s (`toString` renders a leading `-`, valid Python). -/
def pyIntListLit (xs : Array Int) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map toString) ++ "]"

/-- Python list literal of booleans (`True`/`False`). -/
def pyBoolListLit (xs : Array Bool) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map (fun b => if b then "True" else "False")) ++ "]"

/-- A concrete tensor rendered as a Python dict `{"shape": (..), "bits": [..]}` — the
    dtype-preserving canonical form (`Float.toBits`, never a bare float literal). Shared
    expected-bit / input-bit rendering for the affine drivers. -/
def pyTensorEntry (t : DenseTensor) : String :=
  "{\"shape\": " ++ pyShapeTuple t.shape.toArray ++
  ", \"bits\": " ++ pyUInt64ListLit (t.data.map Float.toBits) ++ "}"

/-! ## 3. `einsumOnly`: projection-row recognition and subscript construction -/

/-- Subscript letters are assigned to iteration-basis positions `0, 1, …` in order, one term at a
    time (each term restarts from `a`). -/
def labelTable : Array Char := "abcdefghijklmnopqrstuvwxyz".toList.toArray

/-- Whether one `AffineMap` row is a pure single-`1` projection, and onto which position. `none`
    covers every non-projection shape at once. -/
def rowProjectionTarget (row : Array Int) : Option Nat :=
  let nonzero := (List.range row.size).zip row.toList |>.filter (fun (_, c) => c != 0)
  match nonzero with
  | [(p, 1)] => some p
  | _ => none

/-- One factor's derived `einsum` input subscript (one label per source dimension) and the set of
    iteration-basis positions it covers. Fails loud on any nonzero bias or non-projection row. -/
private def lowerFactor (nodeIndex termIndex factorIndex : Nat) (f : ReadPlan) :
    Except JaxCodegenError (Array Char × Array Nat) := do
  let mut labels : Array Char := #[]
  let mut covered : Array Nat := #[]
  let mut rowIndex : Nat := 0
  for (row, biasVal) in f.map.coeffs.zip f.map.bias do
    unless biasVal == 0 do
      throw (.nonzeroAffineBias nodeIndex termIndex factorIndex rowIndex biasVal)
    match rowProjectionTarget row with
    | none => throw (.nonProjectionRow nodeIndex termIndex factorIndex rowIndex row)
    | some p =>
        match labelTable[p]? with
        | some c =>
            labels := labels.push c
            covered := covered.push p
        | none => throw (.labelTableExhausted nodeIndex termIndex p)
    rowIndex := rowIndex + 1
  return (labels, covered)

/-- One term's derived `einsum` lowering. -/
structure TermLowering where
  factorSubscripts : Array String
  factorSlots      : Array TensorSlot
  outputSubscript  : String
  deriving Repr

private def lowerTerm (nodeIndex termIndex : Nat) (t : TermPlan) :
    Except JaxCodegenError TermLowering := do
  unless t.factors.size > 0 do throw (.emptyTerm nodeIndex termIndex)
  unless t.iterationShape.size ≤ labelTable.size do
    throw (.rankTooLarge nodeIndex termIndex t.iterationShape.size)
  let mut factorSubs : Array String := #[]
  let mut factorSlots : Array TensorSlot := #[]
  let mut coveredAll : Array Bool := Array.replicate t.iterationShape.size false
  for h : fi in [0 : t.factors.size] do
    match t.factors[fi] with
    | .iverson _ => throw (.iversonFactor nodeIndex termIndex fi)
    | .read f =>
      let (labels, covered) ← lowerFactor nodeIndex termIndex fi f
      factorSubs := factorSubs.push (String.ofList labels.toList)
      factorSlots := factorSlots.push f.sourceSlot
      for p in covered do
        coveredAll := coveredAll.set! p true
  for h : p in [0 : coveredAll.size] do
    unless coveredAll[p] do throw (.uncoveredPosition nodeIndex termIndex p)
  let mut outLabels : Array Char := #[]
  for p in t.outputPos do
    match labelTable[p]? with
    | some c => outLabels := outLabels.push c
    | none => throw (.labelTableExhausted nodeIndex termIndex p)
  return { factorSubscripts := factorSubs, factorSlots
         , outputSubscript := String.ofList outLabels.toList }

/-! ## 4. `einsumOnly`: assignment-node emission, in checked graph order -/

structure NodeLowering where
  nodeIndex       : Nat
  destinationSlot : TensorSlot
  terms           : Array TermLowering
  deriving Repr

private def requireJaxSupport (sigs : Array TensorSignature) (nodeIndex : Nat)
    (assign : AssignPlan) : Except JaxCodegenError Unit :=
  match checkJaxAssignSupport sigs assign with
  | .ok _ => pure ()
  | .error cause => throw (.unsupportedAssignment nodeIndex cause)

def lowerAssign (sigs : Array TensorSignature) (nodeIndex : Nat) (a : AssignPlan) :
    Except JaxCodegenError NodeLowering := do
  requireJaxSupport sigs nodeIndex a
  unless a.terms.size > 0 do throw (.emptyAssign nodeIndex)
  let mut terms : Array TermLowering := #[]
  for h : ti in [0 : a.terms.size] do
    let tl ← lowerTerm nodeIndex ti a.terms[ti]
    terms := terms.push tl
  return { nodeIndex, destinationSlot := a.destinationSlot, terms }

def lowerPlan (c : CheckedEvalPlan) : Except JaxCodegenError (Array NodeLowering) := do
  let mut nodes : Array NodeLowering := #[]
  for h : ni in [0 : c.checkedNodes.size] do
    match c.checkedNodes[ni] with
    | .assign a => nodes := nodes.push (← lowerAssign c.raw.tensorSigs ni a.plan)
    | .scan _ | .pointwise _ | .axiswise _ => throw (.unsupportedStep ni)
  return nodes

private def renderTermLine (indent : String) (tl : TermLowering) (varName : String) : String :=
  let subs := String.intercalate "," tl.factorSubscripts.toList
  let sig := pyStrLit (subs ++ "->" ++ tl.outputSubscript)
  let args := String.intercalate ", " (tl.factorSlots.toList.map (fun s => s!"slots[{s}]"))
  s!"{indent}{varName} = jnp.einsum({sig}, {args}, optimize=False)"

private def renderNodeLines (indent : String) (n : NodeLowering) : Array String :=
  let termVar (ti : Nat) := s!"n{n.nodeIndex}_term{ti}"
  let termLines := n.terms.mapIdx (fun ti tl => renderTermLine indent tl (termVar ti))
  let combine := String.intercalate " + " ((List.range n.terms.size).map termVar)
  termLines.push s!"{indent}slots[{n.destinationSlot}] = {combine}"

/-! ## 5. `einsumOnly`: slot init, shape checks, and output reconstruction -/

def renderShapeCheckLine (indent : String) (raw : RawEvalPlan) (b : SlotBinding) :
    Except JaxCodegenError String := do
  match raw.tensorSigs[b.slot]? with
  | none => throw (.bindingSlotOutOfRange b.slot raw.tensorSigs.size)
  | some sig =>
      let nm := pyStrLit b.name
      let shape := pyShapeTuple sig.shape
      return s!"{indent}if tuple(inputs[{nm}].shape) != {shape}:\n" ++
        s!"{indent}    raise ValueError(" ++ pyStrLit "input " ++ " + " ++ nm ++ " + " ++
        pyStrLit s!" expected shape {shape}, got " ++ " + str(tuple(inputs[" ++ nm ++ "].shape)))"

def renderSlotInitLines (indent : String) (raw : RawEvalPlan) (requiredInputs : Array SlotBinding) :
    Except JaxCodegenError (Array String) := do
  let mut lines : Array String := #[]
  for b in requiredInputs do
    let check ← renderShapeCheckLine indent raw b
    lines := lines.push check
    lines := lines.push s!"{indent}slots[{b.slot}] = inputs[{pyStrLit b.name}]"
  return lines

def renderOutputLines (indent : String) (materializedNames : Array SlotBinding) : Array String :=
  materializedNames.map (fun b => s!"{indent}outputs[{pyStrLit b.name}] = slots[{b.slot}]")

/-- The full `forward(inputs)` function body, generated entirely from `PreparedPlan`. -/
def generateForward (plan : PreparedPlan) : Except JaxCodegenError String := do
  let raw := plan.plan.raw
  let nodes ← lowerPlan plan.plan
  let slotInitLines ← renderSlotInitLines "    " raw plan.bindings.requiredInputs.bindings
  let nodeLines := nodes.flatMap (renderNodeLines "    ")
  let outputLines := renderOutputLines "    " plan.bindings.materializedNames
  let lines : Array String :=
    #["def forward(inputs):", s!"    slots = [None] * {raw.tensorSigs.size}"]
    ++ slotInitLines ++ nodeLines
    ++ #["    outputs = {}"] ++ outputLines ++ #["    return outputs"]
  return String.intercalate "\n" lines.toList

/-- Renders the module-level input constants (checked shape + `Float.toBits` payload) the einsum
    smoke's Python consumer reconstructs concrete tensors from. -/
def renderInputConstants (raw : RawEvalPlan) (requiredInputs : Array SlotBinding)
    (inputs : HashMap String DenseTensor) : Except JaxCodegenError String := do
  let mut shapeLines : Array String := #[]
  let mut bitsLines : Array String := #[]
  for b in requiredInputs do
    let sig ← match raw.tensorSigs[b.slot]? with
      | some s => pure s
      | none => throw (.bindingSlotOutOfRange b.slot raw.tensorSigs.size)
    let nm := pyStrLit b.name
    shapeLines := shapeLines.push s!"    {nm}: {pyShapeTuple sig.shape},"
    let bits ← match inputs[b.name]? with
      | some t => pure (t.data.map Float.toBits)
      | none => throw (.missingFixtureInput b.name)
    bitsLines := bitsLines.push s!"    {nm}: {pyUInt64ListLit bits},"
  let shapesBlock := "INPUT_SHAPES = {\n" ++ String.intercalate "\n" shapeLines.toList ++ "\n}"
  let bitsBlock := "INPUT_BITS = {\n" ++ String.intercalate "\n" bitsLines.toList ++ "\n}"
  return shapesBlock ++ "\n" ++ bitsBlock

/-- Renders the einsum smoke's independent expected-output constants (Dense-executed result). -/
def renderExpectedOutputConstants (name : String) (t : DenseTensor) : String :=
  let shape := pyShapeTuple t.shape.toArray
  let bits := pyUInt64ListLit (t.data.map Float.toBits)
  s!"EXPECTED_OUTPUT_NAME = {pyStrLit name}\n" ++
  s!"EXPECTED_OUTPUT_SHAPE = {shape}\n" ++
  s!"EXPECTED_OUTPUT_BITS = {bits}"

/-- Manual renderer for `PlanCompileCause` (the type has no `Repr`/`ToString` of its own). -/
def renderCompileCause : PlanCompileCause → String
  | .inputSignature c => s!"inputSignature: {repr c}"
  | .capability c     => s!"capability: {repr c}"
  | .shape c          => s!"shape: {c}"
  | .scan c           => s!"scan: {repr c}"
  | .invalidPlan c    => s!"invalidPlan: {repr c}"
  | .bindings c       => s!"bindings: {repr c}"
  | .nonlin c         => s!"nonlin: {repr c}"

/-! ## 6. `affineReference`: exact per-factor lookup tables from the shared coordinate primitives -/

/-- For one factor and its term's iteration basis, enumerate the basis in Dense row-major order
    (`allCoords`) and precompute, per iteration coordinate:

    * a safe in-range flat source index (`flatIndex`) when EVERY source dimension is in range
      (`inBoundsPerDim`), or the placeholder `0` otherwise; and
    * a parallel validity mask, `true` exactly when the entry is in range.

    Composes only the shared coordinate primitives, byte-for-byte the pullback `Dense.gatherFactor`
    computes — the per-dimension bounds test happens BEFORE flattening, so a distinct invalid
    coordinate can never alias a valid flat address (proposal §8.3). The runtime gathers only
    through safe indices and re-zeros via the mask, so it never depends on JAX's own out-of-bounds
    gather (which may clamp rather than zero-pad). -/
def buildFactorTable (iterationShape : Array Nat) (f : ReadPlan) : Array Nat × Array Bool :=
  (allCoords iterationShape.toList).foldl
    (fun (acc : Array Nat × Array Bool) iter =>
      let (idxs, masks) := acc
      let src := applyAffine f.map iter
      let shape := f.sourceShape.toList
      if inBoundsPerDim shape src then
        (idxs.push (flatIndex shape (src.map Int.toNat)), masks.push true)
      else
        (idxs.push 0, masks.push false))
    (#[], #[])

private def renderAffineFactor (iterationShape : Array Nat) (f : ReadPlan) : String :=
  let (idxs, masks) := buildFactorTable iterationShape f
  "{\"source_slot\": " ++ toString f.sourceSlot ++
  ", \"safe_index\": " ++ pyNatListLit idxs ++
  ", \"mask\": " ++ pyBoolListLit masks ++ "}"

private def renderAffineTerm (nodeIndex termIndex : Nat) (t : TermPlan) :
    Except JaxCodegenError String := do
  let mut facStrs : Array String := #[]
  for h : fi in [0 : t.factors.size] do
    match t.factors[fi] with
    | .iverson _ => throw (.iversonFactor nodeIndex termIndex fi)
    | .read f => facStrs := facStrs.push (renderAffineFactor t.iterationShape f)
  let facs := String.intercalate ", " facStrs.toList
  return "{\"iteration_shape\": " ++ pyNatListLit t.iterationShape ++
    ", \"output_pos\": " ++ pyNatListLit t.outputPos ++
    ", \"reduction_pos\": " ++ pyNatListLit t.reductionPos ++
    ", \"factors\": [" ++ facs ++ "]}"

/-- One assignment node's static data: destination slot, output shape, and every term's precomputed
    tables in checked term-array order. Rejects a term carrying an Iverson factor with its located
    error (via `renderAffineTerm`). -/
private def renderAffineNode (sigs : Array TensorSignature) (nodeIndex : Nat)
    (a : AssignPlan) : Except JaxCodegenError String := do
  requireJaxSupport sigs nodeIndex a
  let mut termStrs : Array String := #[]
  for h : ti in [0 : a.terms.size] do
    termStrs := termStrs.push (← renderAffineTerm nodeIndex ti a.terms[ti])
  let terms := String.intercalate ", " termStrs.toList
  return "{\"dest\": " ++ toString a.destinationSlot ++
    ", \"output_shape\": " ++ pyNatListLit a.outputShape ++
    ", \"terms\": [" ++ terms ++ "]}"

/-- Every checked node in graph order (`checkedNodes` order is exactly raw-graph order, by
    `checkPlan`'s construction). Total over assignment-only graphs; a `.pointwise`/`.axiswise`/
    `.scan` node has no affine-table lowering here, so the array build rejects it with the one
    located unsupported-step error carrying that node's outer-graph index. -/
private def renderAffineNodesArray (c : CheckedEvalPlan) : Except JaxCodegenError String := do
  let mut entries : Array String := #[]
  for h : ni in [0 : c.checkedNodes.size] do
    match c.checkedNodes[ni] with
    | .assign a => entries := entries.push (← renderAffineNode c.raw.tensorSigs ni a.plan)
    | .scan _ | .pointwise _ | .axiswise _ => throw (.unsupportedStep ni)
  return "[" ++ String.intercalate ", " entries.toList ++ "]"

def renderBindingList (bs : Array SlotBinding) : String :=
  "[" ++ String.intercalate ", "
    (bs.toList.map (fun b => "(" ++ pyStrLit b.name ++ ", " ++ toString b.slot ++ ")")) ++ "]"

/-- Positional `CheckedEvalPlan` static plan data: slot count, ordered input slots, and every
    checked node's affine tables. The complete-graph boundary. -/
def renderAffinePlanPositional (c : CheckedEvalPlan) : Except JaxCodegenError String := do
  let nodes ← renderAffineNodesArray c
  return "{\"num_slots\": " ++ toString c.raw.tensorSigs.size ++
    ", \"input_slots\": " ++ pyNatListLit c.raw.inputSlots ++
    ", \"nodes\": " ++ nodes ++ "}"

/-- Named `PreparedPlan` static plan data: the positional plan plus its source-name bindings
    (`requiredInputs` in `inputSlots` order, `materializedNames` in schedule order). The
    source/corpus boundary. -/
def renderAffinePlanNamed (plan : PreparedPlan) : Except JaxCodegenError String := do
  let c := plan.plan
  let nodes ← renderAffineNodesArray c
  return "{\"num_slots\": " ++ toString c.raw.tensorSigs.size ++
    ", \"input_slots\": " ++ pyNatListLit c.raw.inputSlots ++
    ", \"required_inputs\": " ++ renderBindingList plan.bindings.requiredInputs.bindings ++
    ", \"materialized\": " ++ renderBindingList plan.bindings.materializedNames ++
    ", \"nodes\": " ++ nodes ++ "}"

/-- Positional single `CheckedAssignPlan` static data (one node, no synthetic graph or source
    names). Its runtime call accepts a positional store and returns one result tensor, directly
    paralleling `runDenseAssign`. The checked-kernel boundary. Uses node index `0` (a single node)
    for any located Iverson rejection. -/
def renderAffineAssign (sigs : Array TensorSignature) (c : CheckedAssignPlan) :
    Except JaxCodegenError String :=
  renderAffineNode sigs 0 c.plan

/-- Check, Dense-run, and render one checked-assignment fixture as a `FIXTURES`-list entry:
    `{"name", "kind": "assign", "assign", "store", "expected"}`. The one assign-fixture builder
    every `jax_bridge` driver needs — shared here, on `EvalPlanCodegen`, so a new driver can call it
    directly instead of re-deriving the same check→run→render sequence. -/
def buildAssignFixture (name : String) (sigs : Array TensorSignature) (a : AssignPlan)
    (store : Array DenseTensor) : IO String := do
  let checked ← match checkAssign sigs a with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"{name} check failed: {repr e}")
  let expected ← match runDenseAssign checked store with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"{name} Dense run failed: {repr e}")
  let storeEntries := String.intercalate ", " (store.toList.map pyTensorEntry)
  let rendered ← match renderAffineAssign sigs checked with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{name} render failed: {repr e}")
  pure ("{\"name\": " ++ pyStrLit name ++ ", \"kind\": \"assign\", \"assign\": " ++
    rendered ++ ", \"store\": [" ++ storeEntries ++ "], \"expected\": " ++
    pyTensorEntry expected ++ "}")

/-! ## 7. Explicit mode selection -/

/-- The two lowerings, chosen by the caller — never a silent fallback. -/
inductive LoweringMode
  | einsumOnly
  | affineReference
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Generate the named-plan representation for a source/corpus `PreparedPlan` under an explicit
    mode. `einsumOnly` returns the `forward(inputs)` body (or a closed `JaxCodegenError` rejection);
    `affineReference` returns the static plan DATA, total over every current checked Wave C plan. -/
def generateNamed (mode : LoweringMode) (plan : PreparedPlan) :
    Except JaxCodegenError String :=
  match mode with
  | .einsumOnly       => generateForward plan
  | .affineReference  => renderAffinePlanNamed plan

/-! ## 8. Candidate routing (Thread 5, Tasks 4–5)

Routes each checked assignment through the two existing lowering modes to produce the
`Candidate` types from `LeanNCD.Eval.Plan.Executable`, instead of the raw dict-shaped output
above. Task 4 added the stub signatures; Task 5 fills in the real extraction logic (pulling
tables/operands out of the existing `affineReference`/`einsumOnly` builders above) — see each
function's own doc comment for the two Task 5 signature/scope rulings this reflects.
-/

/-- Convert `affineReference` lowering to `OrderedAffineTableKernelCandidate`: reuse
    `buildFactorTable` (§6, the exact primitive `renderAffineFactor` already calls) to compute each
    factor's safe-index/validity-mask table, one table array per term (outer), one table per factor
    within that term (inner) — matching `tables`'s documented "one per term, then per factor" shape.
-/
def loweringToAffineTableCandidate (sigs : Array TensorSignature) (nodeIndex : Nat)
    (assign : CheckedAssignPlan) : Except JaxCodegenError OrderedAffineTableKernelCandidate := do
  requireJaxSupport sigs nodeIndex assign.plan
  let tables := assign.plan.terms.map (fun term =>
    term.factors.filterMap (fun f => match f with
      | .read r =>
          let (safeIndex, validMask) := buildFactorTable term.iterationShape r
          some ({ source := r.sourceSlot, safeIndex, validMask } : AffineTableReadCandidate)
      | .iverson _ => none))
  return { semanticAssignment := assign, signatureContext := sigs, tables }

/-- Convert `einsumOnly` lowering to `EinsumExperimentKernelCandidate`, reusing
    `rowProjectionTarget` (§3) to recognize each factor's pure-projection rows the same way
    `lowerFactor` does.

    Ruling (Thread 5 Task 5, conflict 2 — see the plan/brief pre-flight analysis):
    `EinsumExperimentKernelCandidate` has one flat `operands`/`outputAxes` pair with no per-term
    dimension, so it can only faithfully represent a SINGLE-TERM `AssignPlan` — the existing
    `einsumOnly` mode already sums multiple per-term `jnp.einsum` calls for a multi-term assign
    (`NodeLowering`/`renderNodeLines` above), which this flat candidate shape cannot express. This
    function therefore lowers only `assign.plan.terms[0]?`; `Executable.validateEinsum` separately
    and independently rejects any candidate whose semantic source has other than exactly one term,
    so a multi-term assign accidentally routed through this function still cannot pass validation.
    `lowerCheckPlanToCandidate` below does NOT call this function — it routes every step through
    `loweringToAffineTableCandidate` only (every current Wave C plan is admitted by that path
    already, per `affineReference`'s own doc comment "accepts every current Wave C CheckedEvalPlan").
    This lowering is real and available, just not yet wired into the plan-level path.

    Total (not `Except`-wrapped, unlike `lowerFactor`), so it cannot reject a non-projection row or
    nonzero bias the way `lowerFactor` does: `rowProjectionTarget` already returns `none` for such a
    row (any nonzero bias is not itself detected here, matching `rowProjectionTarget`'s own
    contract — only the coefficient row is inspected), and `Array.filterMap` silently drops it from
    that factor's axis list rather than failing. The empty-term case (an assign with no terms, which
    `checkAssign` never actually admits — `einsumOnly`'s own `emptyAssign`/`emptyTerm` reject it —
    but this function is total over the type, so it still needs a defined answer) returns empty
    `operands`/`outputAxes`.
-/
def loweringToEinsumCandidate (sigs : Array TensorSignature) (nodeIndex : Nat)
    (assign : CheckedAssignPlan) : Except JaxCodegenError EinsumExperimentKernelCandidate := do
  requireJaxSupport sigs nodeIndex assign.plan
  match assign.plan.terms[0]? with
  | none =>
      return { semanticAssignment := assign, signatureContext := sigs
             , destination := assign.plan.destinationSlot, operands := #[], outputAxes := #[] }
  | some term =>
      let operands := term.factors.filterMap (fun f => match f with
        | .read r => some (#[r.sourceSlot] ++ r.map.coeffs.filterMap rowProjectionTarget)
        | .iverson _ => none)
      return { semanticAssignment := assign, signatureContext := sigs
             , destination := assign.plan.destinationSlot, operands, outputAxes := term.outputPos }

/-- Lower a checked plan to an executable candidate.

    Ruling (Thread 5 Task 5, conflict 1 — see the plan/brief pre-flight analysis): parameter is
    `PreparedPlan`, not the stub's original bare `CheckedEvalPlan` — `JaxExecutableCandidate.source`
    (Task 3) is a `PreparedPlan`, which carries `bindings`/`warnings` that cannot be derived from a
    bare `CheckedEvalPlan`. There were zero existing callers of this function at the time of the
    signature fix (verified by grep), so the change is safe and contained.

    Routes each `.assign` step through `loweringToAffineTableCandidate` only (reference evidence) —
    matching the "Routes each assignment through affineReference (reference evidence)" doc comment
    already on this function from Task 4; `loweringToEinsumCandidate` is deliberately not called
    here (see its own doc comment for why). Iterates `plan.plan.checkedNodes` (each a
    `CheckedPlanStepEvidence`) in checked-node order, which is exactly raw-graph order by
    `CheckedEvalPlan`'s own construction invariant. A `.pointwise`/`.axiswise`/`.scan` step has no
    supported JAX kernel lowering here, so it is rejected with the one located `unsupportedStep`
    error carrying that step's outer-graph index (the FIRST such step, since the loop throws on
    reaching it) — which is why the error type is now `JaxCodegenError`, not the bare `String` the
    stub returned. A well-formed assignment whose affine-table candidate somehow fails validation
    (never reached for any current Wave C plan — the affine path admits all of them) surfaces the
    same located error for that step index rather than being silently dropped.
-/
def lowerCheckPlanToCandidate (plan : PreparedPlan) :
    Except JaxCodegenError JaxExecutableCandidate := do
  let mut steps : Array SomeJaxKernel := #[]
  for h : ni in [0 : plan.plan.checkedNodes.size] do
    match plan.plan.checkedNodes[ni] with
    | .assign a =>
        let lowered ← loweringToAffineTableCandidate plan.plan.raw.tensorSigs ni a
        match validateAndConstructKernel (.affineTable lowered) with
        | .ok k => steps := steps.push k
        | .error _ => throw (.unsupportedStep ni)
    | .scan _ | .pointwise _ | .axiswise _ => throw (.unsupportedStep ni)
  return { source := plan, steps
         , evidence := aggregateEvidenceList (steps.map (·.evidence))
         , aggregated := rfl }

/-! ## 9. Candidate routing tests (Thread 5, Task 5)

Exercises the real (non-`sorry`) lowering + validation functions above against a minimal
identity-copy fixture (`Y[i] := X[i]`), built the same way `test/Eval/Plan/KernelDenseTest.lean`
builds its own. This file lives in the non-default `JaxExperiment` library, so these `#guard`s only
run under `lake build JaxExperiment`, not the default `lake build` — mirroring
`Eval.Plan.ExecutableTest`'s own hand-built fixtures (which cannot reach these functions, since that
default-build test module deliberately does not import this experimental library).
-/

def idSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 } ]

def idRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[3], oobPolicy := .zeroPad }

def idAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read idRead] }]
  , algebra := admittedAlgebra }

def idRaw : RawEvalPlan :=
  { tensorSigs := idSigs, inputSlots := #[0]
  , steps := #[PlanStep.assign idAssign] }

/-- `loweringToAffineTableCandidate` on the identity fixture produces a candidate
    `validateAndConstructKernel` accepts. -/
def testAffineLoweringValid : Bool :=
  match checkAssign idSigs idAssign with
  | .error _ => false
  | .ok checked =>
      match loweringToAffineTableCandidate idSigs 0 checked with
      | .error _ => false
      | .ok candidate =>
          match validateAndConstructKernel (.affineTable candidate) with
          | .ok _ => true
          | .error _ => false

#guard testAffineLoweringValid

/-- `loweringToEinsumCandidate` on the same (single-term, pure-projection) fixture also produces a
    candidate `validateAndConstructKernel` accepts, even though this path is not wired into
    `lowerCheckPlanToCandidate`. -/
def testEinsumLoweringValid : Bool :=
  match checkAssign idSigs idAssign with
  | .error _ => false
  | .ok checked =>
      match loweringToEinsumCandidate idSigs 0 checked with
      | .error _ => false
      | .ok candidate =>
          match validateAndConstructKernel (.einsum candidate) with
          | .ok _ => true
          | .error _ => false

#guard testEinsumLoweringValid

/-- `lowerCheckPlanToCandidate` on a minimal real `PreparedPlan` produces a candidate
    `validateAndConstructExecutable` accepts. -/
def testLowerCheckPlanToCandidateValid : Bool :=
  match checkPlan idRaw with
  | .error _ => false
  | .ok checkedPlan =>
    match checkBindings #[0] #[{ name := "x", slot := 0 }] with
    | .error _ => false
    | .ok requiredInputs =>
      let prepared : PreparedPlan :=
        { plan := checkedPlan
        , bindings := { requiredInputs, materializedNames := #[{ name := "y", slot := 1 }] }
        , warnings := [] }
      match lowerCheckPlanToCandidate prepared with
      | .error _ => false
      | .ok candidate =>
        match validateAndConstructExecutable candidate with
        | .ok _ => true
        | .error _ => false

#guard testLowerCheckPlanToCandidateValid

/-! ### Disposable signature-ownership spike harness (F1-F4)

The temporary `checkAssign` shim admits a Boolean source into this otherwise unchanged real identity
assignment. These guards first prove the current backend hole, then become the shared rejection
harness for both ownership variants.
-/

def spikeExceptOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

def boolSourceSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .bool }, { shape := #[3], dtype := .f64 } ]

def boolSourceRaw : RawEvalPlan :=
  { tensorSigs := boolSourceSigs, inputSlots := #[0]
  , steps := #[PlanStep.assign idAssign] }

def boolSourceStore : Array DenseTensor :=
  #[{ shape := [3], data := #[0.0, 1.0, 1.0] }]

def boolSourcePrepared? : Option PreparedPlan :=
  match checkPlan boolSourceRaw with
  | .error _ => none
  | .ok checkedPlan =>
      match checkBindings #[0] #[{ name := "x", slot := 0 }] with
      | .error _ => none
      | .ok requiredInputs =>
          some
            { plan := checkedPlan
            , bindings := { requiredInputs, materializedNames := #[{ name := "y", slot := 1 }] }
            , warnings := [] }

/-- Exact F2 support rejection, including the outer node and original factor/slot locators. -/
def isBoolSourceRejection (node slot : Nat) {α : Type} : Except JaxCodegenError α → Bool
  | .error (.unsupportedAssignment actualNode (.sourceDType term factor actualSlot .bool)) =>
      actualNode == node && term == 0 && factor == 0 && actualSlot == slot
  | _ => false

def f2PublicEntryRejects {α : Type}
    (entry : CheckedAssignPlan → PreparedPlan → Except JaxCodegenError α) : Bool :=
  match checkAssign boolSourceSigs idAssign, boolSourcePrepared? with
  | .ok checked, some prepared => isBoolSourceRejection 0 0 (entry checked prepared)
  | _, _ => false

#guard f2PublicEntryRejects fun _ _ => lowerAssign boolSourceSigs 0 idAssign
#guard f2PublicEntryRejects fun _ prepared => lowerPlan prepared.plan
#guard f2PublicEntryRejects fun _ prepared => generateForward prepared
#guard f2PublicEntryRejects fun _ prepared => renderAffinePlanPositional prepared.plan
#guard f2PublicEntryRejects fun _ prepared => renderAffinePlanNamed prepared
#guard f2PublicEntryRejects fun checked _ => renderAffineAssign boolSourceSigs checked
#guard f2PublicEntryRejects fun _ prepared => generateNamed .einsumOnly prepared
#guard f2PublicEntryRejects fun _ prepared => generateNamed .affineReference prepared
#guard f2PublicEntryRejects fun checked _ =>
  loweringToAffineTableCandidate boolSourceSigs 0 checked
#guard f2PublicEntryRejects fun checked _ =>
  loweringToEinsumCandidate boolSourceSigs 0 checked
#guard f2PublicEntryRejects fun _ prepared => lowerCheckPlanToCandidate prepared

/-- Variant A gates every retained public semantic lowering/rendering/candidate path. -/
def testVariantABoolSourcePublicPathsRejected : Bool :=
  match checkAssign boolSourceSigs idAssign, boolSourcePrepared? with
  | .ok checked, some prepared =>
      let table : AffineTableReadCandidate :=
        { source := 0, safeIndex := #[0, 1, 2], validMask := #[true, true, true] }
      let affineCandidate : OrderedAffineTableKernelCandidate :=
        { semanticAssignment := checked, signatureContext := boolSourceSigs, tables := #[#[table]] }
      let einsumCandidate : EinsumExperimentKernelCandidate :=
        { semanticAssignment := checked, signatureContext := boolSourceSigs
        , destination := 1, operands := #[#[0, 0]], outputAxes := #[0] }
      isBoolSourceRejection 0 0 (lowerAssign boolSourceSigs 0 idAssign) &&
      isBoolSourceRejection 0 0 (lowerPlan prepared.plan) &&
      isBoolSourceRejection 0 0 (generateForward prepared) &&
      isBoolSourceRejection 0 0 (renderAffinePlanPositional prepared.plan) &&
      isBoolSourceRejection 0 0 (renderAffinePlanNamed prepared) &&
      isBoolSourceRejection 0 0 (renderAffineAssign boolSourceSigs checked) &&
      isBoolSourceRejection 0 0 (generateNamed .einsumOnly prepared) &&
      isBoolSourceRejection 0 0 (generateNamed .affineReference prepared) &&
      isBoolSourceRejection 0 0 (loweringToAffineTableCandidate boolSourceSigs 0 checked) &&
      isBoolSourceRejection 0 0 (loweringToEinsumCandidate boolSourceSigs 0 checked) &&
      !spikeExceptOk (validateAndConstructKernel (.affineTable affineCandidate)) &&
      !spikeExceptOk (validateAndConstructKernel (.einsum einsumCandidate)) &&
      isBoolSourceRejection 0 0 (lowerCheckPlanToCandidate prepared)
  | _, _ => false

#guard testVariantABoolSourcePublicPathsRejected

/- The `IO` fixture boundary must also reject before returning Python. -/
#eval do
  let rejected ←
    try
      let _ ← buildAssignFixture "boolSource" boolSourceSigs idAssign boolSourceStore
      pure false
    catch _ => pure true
  unless rejected do throw (IO.userError "F2 buildAssignFixture did not reject at JAX support")

def locatedStep0Read : ReadPlan :=
  { idRead with sourceSlot := 0 }

def locatedStep1Read : ReadPlan :=
  { idRead with sourceSlot := 2 }

def locatedStep0Assign : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read locatedStep0Read] }]
  , algebra := admittedAlgebra }

def locatedStep1Assign : AssignPlan :=
  { contextShape := #[], destinationSlot := 3, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read locatedStep1Read] }]
  , algebra := admittedAlgebra }

def locatedBoolSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 }
   , { shape := #[3], dtype := .bool }, { shape := #[3], dtype := .f64 } ]

/-- F3: the Boolean external input is slot 2, but its only read is at outer step 1. -/
def locatedBoolRaw : RawEvalPlan :=
  { tensorSigs := locatedBoolSigs, inputSlots := #[0, 2]
  , steps := #[.assign locatedStep0Assign, .assign locatedStep1Assign] }

def locatedBoolPrepared? : Option PreparedPlan :=
  match checkPlan locatedBoolRaw with
  | .error _ => none
  | .ok checkedPlan =>
      match checkBindings #[0, 2] #[{ name := "real", slot := 0 }, { name := "pred", slot := 2 }] with
      | .error _ => none
      | .ok requiredInputs =>
          some
            { plan := checkedPlan
            , bindings :=
                { requiredInputs
                , materializedNames := #[{ name := "r", slot := 1 }, { name := "z", slot := 3 }] }
            , warnings := [] }

def firstBoolReadLocation
    (raw : RawEvalPlan) : Option (Nat × Nat × Nat × TensorSlot) := Id.run do
  let mut found := none
  for h : ni in [0 : raw.steps.size] do
    match raw.steps[ni] with
    | .assign assign =>
        for h2 : ti in [0 : assign.terms.size] do
          let term := assign.terms[ti]
          for h3 : fi in [0 : term.factors.size] do
            match term.factors[fi] with
            | .iverson _ => pure ()
            | .read read =>
                match raw.tensorSigs[read.sourceSlot]? with
                | some sig =>
                    if found.isNone && sig.dtype == .bool then
                      found := some (ni, ti, fi, read.sourceSlot)
                | none => pure ()
    | .scan _ | .pointwise _ | .axiswise _ => pure ()
  return found

#guard firstBoolReadLocation locatedBoolRaw == some (1, 0, 0, 2)

def testVariantALocatedBoolRejectedAt1 : Bool :=
  match locatedBoolPrepared? with
  | none => false
  | some prepared =>
      match lowerCheckPlanToCandidate prepared with
      | .error (.unsupportedAssignment 1 (.sourceDType 0 0 2 .bool)) => true
      | _ => false

#guard testVariantALocatedBoolRejectedAt1

def allRealSubstituteSigs : Array TensorSignature := idSigs

/-- F4: a same-shaped all-real candidate cannot override the Boolean `PreparedPlan` authority. -/
def testVariantAPlanAuthoritySubstitutionRejected : Bool :=
  match boolSourcePrepared?, checkAssign allRealSubstituteSigs idAssign with
  | some prepared, .ok substituteChecked =>
      match loweringToAffineTableCandidate allRealSubstituteSigs 0 substituteChecked with
      | .error _ => false
      | .ok lowered =>
          match validateAndConstructKernel (.affineTable lowered) with
          | .error _ => false
          | .ok kernel =>
              let steps := #[kernel]
              let candidate : JaxExecutableCandidate :=
                { source := prepared, steps
                , evidence := aggregateEvidenceList (steps.map (·.evidence))
                , aggregated := rfl }
              match validateAndConstructExecutable candidate with
              | .error message => message == "Executable source mismatch at step 0"
              | .ok _ => false
  | _, _ => false

#guard testVariantAPlanAuthoritySubstitutionRejected

def locatedAllRealSigs : Array TensorSignature :=
  locatedBoolSigs.map fun sig => { sig with dtype := .f64 }

/-- The complete context may differ first at step 1's support use; the executable reports step 1,
not a cached step-0 decision. -/
def testVariantALocatedContextSubstitutionRejectedAt1 : Bool :=
  match locatedBoolPrepared? with
  | none => false
  | some prepared =>
      match (prepared.plan.checkedNodes[0]? : Option CheckedPlanStepEvidence),
            (prepared.plan.checkedNodes[1]? : Option CheckedPlanStepEvidence) with
      | some (.assign checked0), some (.assign checked1) =>
          match loweringToAffineTableCandidate locatedBoolSigs 0 checked0,
                loweringToAffineTableCandidate locatedAllRealSigs 1 checked1 with
          | .ok lowered0, .ok lowered1 =>
              match validateAndConstructKernel (.affineTable lowered0),
                    validateAndConstructKernel (.affineTable lowered1) with
              | .ok kernel0, .ok kernel1 =>
                  let steps := #[kernel0, kernel1]
                  let candidate : JaxExecutableCandidate :=
                    { source := prepared, steps
                    , evidence := aggregateEvidenceList (steps.map (·.evidence))
                    , aggregated := rfl }
                  match validateAndConstructExecutable candidate with
                  | .error message => message == "Executable source mismatch at step 1"
                  | .ok _ => false
              | _, _ => false
          | _, _ => false
      | _, _ => false

#guard testVariantALocatedContextSubstitutionRejectedAt1

/-- Even with the authoritative complete context, a step-0 assignment candidate cannot be reused
for step 1. This is the assignment-correspondence half of executable well-formedness. -/
def testVariantAAssignmentTieRejectedAt1 : Bool :=
  match locatedBoolPrepared? with
  | none => false
  | some prepared =>
      match (prepared.plan.checkedNodes[0]? : Option CheckedPlanStepEvidence) with
      | some (.assign checked0) =>
          match loweringToAffineTableCandidate locatedBoolSigs 0 checked0 with
          | .error _ => false
          | .ok lowered =>
              match validateAndConstructKernel (.affineTable lowered) with
              | .error _ => false
              | .ok kernel =>
                  let steps := #[kernel, kernel]
                  let candidate : JaxExecutableCandidate :=
                    { source := prepared, steps
                    , evidence := aggregateEvidenceList (steps.map (·.evidence))
                    , aggregated := rfl }
                  match validateAndConstructExecutable candidate with
                  | .error message => message == "Executable source mismatch at step 1"
                  | .ok _ => false
      | _ => false

#guard testVariantAAssignmentTieRejectedAt1

/-! ### Located unsupported-step rejections (Slice 5, Task 5.0)

Three fixtures, each a checked `[assign@0, <unsupported>@1]` graph: a valid identity assignment at
step index 0 and a `.pointwise`/`.axiswise`/`.scan` step at index 1. `lowerCheckPlanToCandidate`
must route the assignment through the affine path, then reject the unsupported step with the one
located `unsupportedStep` error carrying index `1` (NOT `0` — the valid assignment ahead of it is
what makes the required location non-tautological). A `.pointwise`/`.axiswise`/`.scan` step cannot
be a repackaged assignment: each carries its own `RawPointwisePlan`/`RawAxiswisePlan`/`RawScanPlan`
payload, built minimal-but-`checkPlan`-valid here (the scan geometry mirrors
`test/Eval/Plan/ScanTest.lean`'s `linearScan`, which that suite proves `checkScanPlan` admits). -/

def rejectSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 } ]

-- `[assign Y[i]:=X[i] @0, pointwise relu(X)->slot2 @1]`.
def pointwiseStep : RawPointwisePlan :=
  { sourceSlot := 0, destinationSlot := 2, shape := #[3], fn := .relu }

def pointwiseRejectRaw : RawEvalPlan :=
  { tensorSigs := rejectSigs, inputSlots := #[0]
  , steps := #[PlanStep.assign idAssign, PlanStep.pointwise pointwiseStep] }

-- `[assign Y[i]:=X[i] @0, axiswise softmax(X, axis 0)->slot2 @1]`.
def axiswiseStep : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 2, shape := #[3], axisPos := 0, fn := .softmax }

def axiswiseRejectRaw : RawEvalPlan :=
  { tensorSigs := rejectSigs, inputSlots := #[0]
  , steps := #[PlanStep.assign idAssign, PlanStep.axiswise axiswiseStep] }

/-! A minimal linear self-recurrence scan, geometry copied verbatim from `ScanTest.linearScan`:
outer slots `0 = S0` (scalar), `1 = X` (`[3]`), `2 = S` (`[3]`). Base `S[iterAt l 0] := S0`; step
`S[iterNext l] := S[l] + X[l]`. -/

def scanState : StateSlot :=
  { destSlot := 2, advancingDims := #[0], materialization := .completeHistory }

def scanBaseBlock : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[{ shape := #[], dtype := .f64 }]
  , inputs := #[0], steps := #[], outputs := #[0] }

def scanBaseCapture : BlockCapture := { inputSlot := 0, source := .external 0 }

def scanBaseWrite : StateWriteMap :=
  { outputSlot := 0, stateIndex := 0, map := { coeffs := #[#[]], bias := #[0] } }

def scanStepReadX : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[3], oobPolicy := .zeroPad }

def scanStepReadS : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[3], oobPolicy := .zeroPad }

def scanTermX : TermPlan :=
  { iterationShape := #[2], contextPos := #[0], outputPos := #[], reductionPos := #[], factors := #[.read scanStepReadX] }

def scanTermS : TermPlan :=
  { iterationShape := #[2], contextPos := #[0], outputPos := #[], reductionPos := #[], factors := #[.read scanStepReadS] }

def scanStepAssign : AssignPlan :=
  { contextShape := #[2], destinationSlot := 2, outputShape := #[], terms := #[scanTermX, scanTermS]
  , algebra := admittedAlgebra }

def scanStepBlock : RawPlanBlock :=
  { contextShape := #[2]
  , tensorSigs := #[{ shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 }, { shape := #[], dtype := .f64 }]
  , inputs := #[0, 1], steps := #[.assign scanStepAssign], outputs := #[2] }

def scanStepCaptureX : BlockCapture := { inputSlot := 0, source := .external 1 }
def scanStepCaptureS : BlockCapture := { inputSlot := 1, source := .state 0 }

def scanStepWrite : StateWriteMap :=
  { outputSlot := 2, stateIndex := 0, map := { coeffs := #[#[1]], bias := #[1] } }

def scanPlanStep : RawScanPlan :=
  { states := #[scanState]
  , baseBlock := scanBaseBlock, baseCaptures := #[scanBaseCapture], baseWrites := #[scanBaseWrite]
  , stepBlock := scanStepBlock, stepCaptures := #[scanStepCaptureX, scanStepCaptureS], stepWrites := #[scanStepWrite]
  , historyExtents := #[3]
  , iterationOrder := .axisZeroFastest, boundaryPolicy := .zeroThenBaseOverlay
  , snapshotPolicy := .immutablePreStep }

-- Outer slots `0 = S0`, `1 = X`, `2 = S` (scan dest), plus `3 = Y` (the step-0 assign's dest).
def scanRejectSigs : Array TensorSignature :=
  #[ { shape := #[], dtype := .f64 }, { shape := #[3], dtype := .f64 }
   , { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 } ]

-- `Y[i] := X[i]` reading input slot 1 into a fresh slot 3, so the scan (step 1) is not step 0.
def scanAssignRead : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }, sourceShape := #[3], oobPolicy := .zeroPad }

def scanAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 3, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read scanAssignRead] }]
  , algebra := admittedAlgebra }

def scanRejectRaw : RawEvalPlan :=
  { tensorSigs := scanRejectSigs, inputSlots := #[0, 1]
  , steps := #[PlanStep.assign scanAssign, PlanStep.scan scanPlanStep] }

/-- Shared assertion: `checkPlan`-accept, `PreparedPlan`-wrap with the given input bindings, then
    `lowerCheckPlanToCandidate` must reject with `unsupportedStep 1`. -/
def rejectsLocatedAt1 (raw : RawEvalPlan) (inputBindings : Array SlotBinding) : Bool :=
  match checkPlan raw with
  | .error _ => false
  | .ok checkedPlan =>
    match checkBindings raw.inputSlots inputBindings with
    | .error _ => false
    | .ok requiredInputs =>
      let prepared : PreparedPlan :=
        { plan := checkedPlan, bindings := { requiredInputs, materializedNames := #[] }, warnings := [] }
      match lowerCheckPlanToCandidate prepared with
      | .error (.unsupportedStep idx) => idx == 1
      | _ => false

/-- A `.pointwise` step at index 1 is rejected with the located error carrying index `1`. -/
def testPointwiseStepRejectedLocated : Bool :=
  rejectsLocatedAt1 pointwiseRejectRaw #[{ name := "x", slot := 0 }]

#guard testPointwiseStepRejectedLocated

/-- A `.axiswise` step at index 1 is rejected with the located error carrying index `1`. -/
def testAxiswiseStepRejectedLocated : Bool :=
  rejectsLocatedAt1 axiswiseRejectRaw #[{ name := "x", slot := 0 }]

#guard testAxiswiseStepRejectedLocated

/-! Slice 5.3: a MASKED `.axiswise` step (`RawAxiswisePlan.mask` present) is routed to the SAME
generic located `unsupportedStep` error before any Python emission — the complete-step JAX support
check never special-cases the mask into an emittable path. `maskInclude` is a width-1 always-true
positional mask over the `#[3]`-shaped step, so `checkPlan` admits the step; JAX still rejects it. -/

def maskInclude : PosBoolExpr :=
  .rel .eq (.affine ⟨#[0], 0⟩) (.affine ⟨#[0], 0⟩)

-- `[assign Y[i]:=X[i] @0, axiswise softmax(where 0=0)(X, axis 0)->slot2 @1]`.
def maskedAxiswiseStep : RawAxiswisePlan :=
  { sourceSlot := 0, destinationSlot := 2, shape := #[3], axisPos := 0, fn := .softmax
  , mask := some maskInclude }

def maskedAxiswiseRejectRaw : RawEvalPlan :=
  { tensorSigs := rejectSigs, inputSlots := #[0]
  , steps := #[PlanStep.assign idAssign, PlanStep.axiswise maskedAxiswiseStep] }

/-- A MASKED `.axiswise` step at index 1 is rejected with the same located error carrying index `1` —
    masking does not create a new emittable JAX path. -/
def testMaskedAxiswiseStepRejectedLocated : Bool :=
  rejectsLocatedAt1 maskedAxiswiseRejectRaw #[{ name := "x", slot := 0 }]

#guard testMaskedAxiswiseStepRejectedLocated

/-- A `.scan` step at index 1 is rejected with the located error carrying index `1`. -/
def testScanStepRejectedLocated : Bool :=
  rejectsLocatedAt1 scanRejectRaw #[{ name := "s0", slot := 0 }, { name := "x", slot := 1 }]

#guard testScanStepRejectedLocated

/-! ### Slice 5.4 — Iverson factor JAX rejection gate (`idRaw` family)

The predicate/mask parity thread admits a source Iverson factor into the checked plan (Task 5.2), but
this JAX backend lowers only affine reads to einsum/affine-table kernels — a term carrying an Iverson
predicate has no JAX lowering and is rejected with the located `JaxCodegenError.iversonFactor`
established in Task 5.1. The fixture inserts an Iverson at factor index 1 of the identity assignment's
single term (`Y[i] := X[i] · [predicate]`, the `idRaw` family), so `checkPlan` admits it (the
predicate leaf has width 1 == the term's `iterationShape.size`) but both JAX lowering entry points —
the einsum body (`generateNamed .einsumOnly` → `lowerTerm`) and the affine-reference static data
(`generateNamed .affineReference` → `renderAffineTerm`) — reject it with `.iversonFactor 0 0 1`
(node 0, term 0, all-factor index 1, NOT the filtered-read index 0). -/

def idIversonPred : PosBoolExpr :=
  .rel .eq (.affine ⟨#[0], 0⟩) (.affine ⟨#[0], 0⟩)

-- `Y[i] := X[i] · [0 = 0]`: the identity read at factor index 0, an Iverson at all-factor index 1.
def idIversonAssign : AssignPlan :=
  { idAssign with terms := #[{ idAssign.terms[0]! with
      factors := #[.read idRead, .iverson idIversonPred] }] }

def idIversonRaw : RawEvalPlan :=
  { tensorSigs := idSigs, inputSlots := #[0]
  , steps := #[PlanStep.assign idIversonAssign] }

/-- `checkPlan` admits the Iverson-bearing plan (predicate leaf width 1 == `iterationShape.size`). -/
def testIversonPlanChecks : Bool :=
  match checkPlan idIversonRaw with | .ok _ => true | .error _ => false

#guard testIversonPlanChecks

/-- Wrap `idIversonRaw` into a real `PreparedPlan` (via `checkPlan` + `checkBindings`), then generate
    under `mode`; success is a rejection with the located `iversonFactor 0 0 1`. -/
def iversonRejectedUnder (mode : LoweringMode) : Bool :=
  match checkPlan idIversonRaw with
  | .error _ => false
  | .ok checkedPlan =>
    match checkBindings idIversonRaw.inputSlots #[{ name := "x", slot := 0 }] with
    | .error _ => false
    | .ok requiredInputs =>
      let prepared : PreparedPlan :=
        { plan := checkedPlan
        , bindings := { requiredInputs, materializedNames := #[{ name := "y", slot := 1 }] }
        , warnings := [] }
      match generateNamed mode prepared with
      | .error (.iversonFactor n t f) => n == 0 && t == 0 && f == 1
      | _ => false

/-- The einsum lowering body rejects the Iverson factor with its located `iversonFactor 0 0 1`. -/
def testIversonEinsumRejectedLocated : Bool := iversonRejectedUnder .einsumOnly

#guard testIversonEinsumRejectedLocated

/-- The affine-reference static-plan lowering rejects the same factor with the same located error. -/
def testIversonAffineRejectedLocated : Bool := iversonRejectedUnder .affineReference

#guard testIversonAffineRejectedLocated

end JaxBridge

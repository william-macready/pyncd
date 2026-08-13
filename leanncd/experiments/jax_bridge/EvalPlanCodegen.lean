import LeanNCD.Eval.Plan.Adapter

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
def lowerFactor (nodeIndex termIndex factorIndex : Nat) (f : ReadPlan) :
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

def lowerTerm (nodeIndex termIndex : Nat) (t : TermPlan) :
    Except JaxCodegenError TermLowering := do
  unless t.factors.size > 0 do throw (.emptyTerm nodeIndex termIndex)
  unless t.iterationShape.size ≤ labelTable.size do
    throw (.rankTooLarge nodeIndex termIndex t.iterationShape.size)
  let mut factorSubs : Array String := #[]
  let mut factorSlots : Array TensorSlot := #[]
  let mut coveredAll : Array Bool := Array.replicate t.iterationShape.size false
  for h : fi in [0 : t.factors.size] do
    let f := t.factors[fi]
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

def lowerAssign (nodeIndex : Nat) (a : AssignPlan) :
    Except JaxCodegenError NodeLowering := do
  unless a.terms.size > 0 do throw (.emptyAssign nodeIndex)
  let mut terms : Array TermLowering := #[]
  for h : ti in [0 : a.terms.size] do
    let tl ← lowerTerm nodeIndex ti a.terms[ti]
    terms := terms.push tl
  return { nodeIndex, destinationSlot := a.destinationSlot, terms }

def lowerPlan (c : CheckedEvalPlan) : Except JaxCodegenError (Array NodeLowering) := do
  let mut nodes : Array NodeLowering := #[]
  for h : ni in [0 : c.checkedNodes.size] do
    let node ← lowerAssign ni c.checkedNodes[ni].plan
    nodes := nodes.push node
  return nodes

def renderTermLine (indent : String) (tl : TermLowering) (varName : String) : String :=
  let subs := String.intercalate "," tl.factorSubscripts.toList
  let sig := pyStrLit (subs ++ "->" ++ tl.outputSubscript)
  let args := String.intercalate ", " (tl.factorSlots.toList.map (fun s => s!"slots[{s}]"))
  s!"{indent}{varName} = jnp.einsum({sig}, {args}, optimize=False)"

def renderNodeLines (indent : String) (n : NodeLowering) : Array String :=
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
  | .invalidPlan c    => s!"invalidPlan: {repr c}"
  | .bindings c       => s!"bindings: {repr c}"

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

def renderAffineFactor (iterationShape : Array Nat) (f : ReadPlan) : String :=
  let (idxs, masks) := buildFactorTable iterationShape f
  "{\"source_slot\": " ++ toString f.sourceSlot ++
  ", \"safe_index\": " ++ pyNatListLit idxs ++
  ", \"mask\": " ++ pyBoolListLit masks ++ "}"

def renderAffineTerm (t : TermPlan) : String :=
  let facs := String.intercalate ", " (t.factors.toList.map (renderAffineFactor t.iterationShape))
  "{\"iteration_shape\": " ++ pyNatListLit t.iterationShape ++
  ", \"output_pos\": " ++ pyNatListLit t.outputPos ++
  ", \"reduction_pos\": " ++ pyNatListLit t.reductionPos ++
  ", \"factors\": [" ++ facs ++ "]}"

/-- One assignment node's static data: destination slot, output shape, and every term's precomputed
    tables in checked term-array order. -/
def renderAffineNode (a : AssignPlan) : String :=
  let terms := String.intercalate ", " (a.terms.toList.map renderAffineTerm)
  "{\"dest\": " ++ toString a.destinationSlot ++
  ", \"output_shape\": " ++ pyNatListLit a.outputShape ++
  ", \"terms\": [" ++ terms ++ "]}"

/-- Every checked node in graph order (`checkedNodes` order is exactly raw-graph order, by
    `checkPlan`'s construction). -/
def renderAffineNodesArray (c : CheckedEvalPlan) : String :=
  "[" ++ String.intercalate ", " (c.checkedNodes.toList.map (fun cn => renderAffineNode cn.plan))
    ++ "]"

def renderBindingList (bs : Array SlotBinding) : String :=
  "[" ++ String.intercalate ", "
    (bs.toList.map (fun b => "(" ++ pyStrLit b.name ++ ", " ++ toString b.slot ++ ")")) ++ "]"

/-- Positional `CheckedEvalPlan` static plan data: slot count, ordered input slots, and every
    checked node's affine tables. The complete-graph boundary. -/
def renderAffinePlanPositional (c : CheckedEvalPlan) : String :=
  "{\"num_slots\": " ++ toString c.raw.tensorSigs.size ++
  ", \"input_slots\": " ++ pyNatListLit c.raw.inputSlots ++
  ", \"nodes\": " ++ renderAffineNodesArray c ++ "}"

/-- Named `PreparedPlan` static plan data: the positional plan plus its source-name bindings
    (`requiredInputs` in `inputSlots` order, `materializedNames` in schedule order). The
    source/corpus boundary. -/
def renderAffinePlanNamed (plan : PreparedPlan) : String :=
  let c := plan.plan
  "{\"num_slots\": " ++ toString c.raw.tensorSigs.size ++
  ", \"input_slots\": " ++ pyNatListLit c.raw.inputSlots ++
  ", \"required_inputs\": " ++ renderBindingList plan.bindings.requiredInputs.bindings ++
  ", \"materialized\": " ++ renderBindingList plan.bindings.materializedNames ++
  ", \"nodes\": " ++ renderAffineNodesArray c ++ "}"

/-- Positional single `CheckedAssignPlan` static data (one node, no synthetic graph or source
    names). Its runtime call accepts a positional store and returns one result tensor, directly
    paralleling `runDenseAssign`. The checked-kernel boundary. -/
def renderAffineAssign (c : CheckedAssignPlan) : String :=
  renderAffineNode c.plan

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
  pure ("{\"name\": " ++ pyStrLit name ++ ", \"kind\": \"assign\", \"assign\": " ++
    renderAffineAssign checked ++ ", \"store\": [" ++ storeEntries ++ "], \"expected\": " ++
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
  | .affineReference  => .ok (renderAffinePlanNamed plan)

end JaxBridge

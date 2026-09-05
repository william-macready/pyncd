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
  -- Whole-branch review — the term's SOURCE extents disagree with the iteration extents of the
  -- labels it would be emitted with, so the einsum string, though perfectly well-formed, denotes a
  -- different function than the checked assignment: `jnp.einsum` takes each label's extent from the
  -- operand it appears on, while the checked plan takes it from `iterationShape` and zero-pads
  -- every source coordinate outside `sourceShape`. `Y[i] := V[i]` with `sourceShape = #[2]` and
  -- `iterationShape = #[3]` renders `a->a` and returns TWO elements where Dense returns three.
  -- Located at the offending factor's source dimension and the iteration position it projects onto,
  -- carrying both extents (`iterationExtent = none` when the position is outside the iteration
  -- basis). Decided by `LeanNCD.Eval.Plan.einsumTermLabelExtents` — the production validator's OWN
  -- recomputation, called rather than copied, so `validateEinsum` and this emitter cannot disagree
  -- about which candidates have compatible extents.
  | labelExtentMismatch   (nodeIndex termIndex factorIndex sourceDim position sourceExtent : Nat)
                          (iterationExtent : Option Nat)
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
  -- Task 4.5 — the located support rejections this backend now makes BEFORE emitting any Python,
  -- building any candidate, or exposing any `ExecutionEvidence`. Each mirrors one
  -- `LeanNCD.Eval.Plan.JaxSupportError` constructor (see `codegenErrorOfSupport` below); the split
  -- into destination/source dtype keeps the destination's slot and the source's original
  -- term/factor locators, which a single shared constructor could not carry at once.
  | unsupportedDestDType   (nodeIndex : Nat) (slot : TensorSlot) (dtype : ScalarDType)
  | unsupportedAlgebra     (nodeIndex : Nat)
  -- Task 4.5 closure — the assignment is evaluated at a runtime context coordinate
  -- (`AssignPlan.contextShape` non-empty): neither lowering has a kernel parameter for it, so both
  -- would silently emit a context-free kernel (`einsumOnly` contracts the context axis away as an
  -- ordinary label, `affineReference` emits no `context_pos` key at all). Assignment-level, so it
  -- carries the node index and the rejected shape, no term/factor locator.
  | unsupportedContext     (nodeIndex : Nat) (contextShape : Array Nat)
  | unsupportedSourceDType (nodeIndex termIndex factorIndex : Nat) (dtype : ScalarDType)
  | unaryFactor            (nodeIndex termIndex factorIndex : Nat)
  -- The supplied standalone signature table is not even structurally compatible with the same raw
  -- assignment (`checkAssign` re-run under it fails): a caller-supplied table is that entry's
  -- semantic authority, so it is rejected outright rather than consulted for its dtype tags alone.
  | invalidSignatureContext (nodeIndex : Nat) (cause : PlanError)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Map the production support gate's located error into this module's own closed diagnostic
    vocabulary. One-to-one; no case is collapsed and no locator is dropped. -/
def codegenErrorOfSupport : JaxSupportError → JaxCodegenError
  | .destinationDType n slot dt      => .unsupportedDestDType n slot dt
  | .unsupportedAlgebra n _          => .unsupportedAlgebra n
  | .contextualAssignment n ctx      => .unsupportedContext n ctx
  | .sourceDType n ti fi dt          => .unsupportedSourceDType n ti fi dt
  | .unaryFactor n ti fi             => .unaryFactor n ti fi
  | .invalidSignatureContext n cause => .invalidSignatureContext n cause

/-- The one shared support gate every semantic entry point in this module runs first: the supplied
    complete table is the assignment's authority (`checkAssign` is re-run under it), then the JAX
    support policy decides. Located at `nodeIndex` — the real outer step index at a plan-level
    caller, `0` at a standalone one. -/
def requireJaxSupport (sigs : Array TensorSignature) (nodeIndex : Nat)
    (checked : CheckedAssignPlan) : Except JaxCodegenError Unit :=
  match checkJaxAssignSupport sigs nodeIndex checked with
  | .ok _ => .ok ()
  | .error e => .error (codegenErrorOfSupport e)

/-- The candidate conversions' own Iverson gate, carrying the ORIGINAL all-factor index (never a
    reindexed read-only one) — the same located `iversonFactor` both rendering modes already throw.
    Without it a candidate conversion would silently `filterMap` the predicate factor away and hand
    the shortened table array to a validator, which rejects it (`hasIverson`) but with no location
    at all. -/
def requireNoIverson (nodeIndex : Nat) (a : AssignPlan) : Except JaxCodegenError Unit := do
  for h : ti in [0 : a.terms.size] do
    let t := a.terms[ti]
    for h2 : fi in [0 : t.factors.size] do
      match t.factors[fi] with
      | .iverson _ => throw (.iversonFactor nodeIndex ti fi)
      | .read _ => pure ()

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

-- Drift guard: `Executable.lean`'s `validateEinsum` certifies exactly the ranks this table can
-- label, using its own mirrored `einsumLabelLimit` (it cannot import this experimental module —
-- `experiments/jax_bridge` depends on `LeanNCD`, never the reverse). If this table ever grows or
-- shrinks, the two must be changed together or the validator would start certifying a rank
-- `lowerTerm` rejects (or rejecting one it renders).
#guard labelTable.size == einsumLabelLimit

/-- Whether one `AffineMap` row is a pure single-`1` projection, and onto which position. `none`
    covers every non-projection shape at once. -/
def rowProjectionTarget (row : Array Int) : Option Nat :=
  let nonzero := (List.range row.size).zip row.toList |>.filter (fun (_, c) => c != 0)
  match nonzero with
  | [(p, 1)] => some p
  | _ => none

/-- One factor's derived `einsum` input subscript (one label per source dimension) and the set of
    iteration-basis positions it covers. Fails loud on any nonzero bias or non-projection row.

    PRIVATE (Task 4.5): an assignment-semantic helper reachable only behind the contextual
    `lowerAssign` gate, so no caller can lower a factor's meaning without first establishing the
    signature context that decides whether the surrounding assignment is supported at all. -/
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

/-- One term's derived `einsum` lowering. PRIVATE for the same reason as `lowerFactor`. -/
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

/-- One checked assignment's `einsum`-mode lowering, under an explicit complete signature table
    (Task 4.5). `sigs` is this standalone entry's semantic authority: `requireJaxSupport` re-runs
    `checkAssign` under it and applies the JAX support policy before a single subscript is derived,
    so a Boolean destination/source, a tropical algebra, a unary read, a contextful assignment, or a
    structurally incompatible table is rejected here with its located error rather than silently
    rendered. The input is a `CheckedAssignPlan`, not a raw `AssignPlan`: a caller cannot hand this
    function an unchecked assignment at all.

    **Label extents (whole-branch review).** After each term lowers, its source extents must agree
    with the iteration extents of the labels it was emitted with — `einsumTermLabelExtents`, the
    production validator's own recomputation (`Eval/Plan/Executable.lean`), imported rather than
    re-derived. This gate exists because renderability is NOT the standard for a public lowering
    entry: a zero-padded read shorter than its own iteration basis renders a perfectly well-formed
    `a->a`, which `jnp.einsum` then evaluates at the OPERAND's extent and returns a shorter result
    than the checked plan means. `validateEinsum` already refused to certify such a candidate, but
    this function is itself a public entry (and `generateForward`/the plan renderers reach Python
    through it), so returning the program at all would hand a caller a semantically unsupported
    einsum. It runs AFTER `lowerTerm` so every pre-existing located rejection — `.emptyTerm`,
    `.rankTooLarge`, `.uncoveredPosition`, `.nonzeroAffineBias`, `.nonProjectionRow`,
    `.iversonFactor` — keeps strict priority over it, and so that `einsumTermLabelExtents`'
    `noOperand` verdict is unreachable here: it names exactly the factor shapes `lowerTerm` has
    already rejected with a locator of its own (plus a coefficient/source rank disagreement, which
    the support gate's `checkAssign` re-run rules out via `affineRankMismatch`). The affine-reference
    mode is deliberately NOT gated: its tables carry the zero-pad mask explicitly, so it renders the
    mismatch correctly. -/
def lowerAssign (sigs : Array TensorSignature) (nodeIndex : Nat) (checked : CheckedAssignPlan) :
    Except JaxCodegenError NodeLowering := do
  requireJaxSupport sigs nodeIndex checked
  let a := checked.plan
  unless a.terms.size > 0 do throw (.emptyAssign nodeIndex)
  let mut terms : Array TermLowering := #[]
  for h : ti in [0 : a.terms.size] do
    let t := a.terms[ti]
    let tl ← lowerTerm nodeIndex ti t
    match einsumTermLabelExtents t with
    | .mismatch fi d p srcExtent iterExtent =>
        throw (.labelExtentMismatch nodeIndex ti fi d p srcExtent iterExtent)
    | .agree => pure ()
    | .noOperand _ => pure ()  -- unreachable: `lowerTerm` above rejects exactly these factors
    terms := terms.push tl
  return { nodeIndex, destinationSlot := a.destinationSlot, terms }

/-- Every checked node's `einsum`-mode lowering, in graph order. Plan-level: takes NO caller table
    and derives the checked plan's own `raw.tensorSigs` as the authority for every step (Task 4.5,
    spike decision GO B) — there is deliberately no way for a caller to supply a parallel,
    same-shape all-real table here. -/
def lowerPlan (c : CheckedEvalPlan) : Except JaxCodegenError (Array NodeLowering) := do
  let sigs := c.raw.tensorSigs
  let mut nodes : Array NodeLowering := #[]
  for h : ni in [0 : c.checkedNodes.size] do
    match c.checkedNodes[ni] with
    | .assign a => nodes := nodes.push (← lowerAssign sigs ni a)
    | .scan _ | .pointwise _ | .axiswise _ => throw (.unsupportedStep ni)
  return nodes

/-- PRIVATE (Task 4.5): emits `jnp.einsum` from publicly constructible IR, so it is reachable only
    behind `lowerAssign`'s contextual gate. -/
private def renderTermLine (indent : String) (tl : TermLowering) (varName : String) : String :=
  let subs := String.intercalate "," tl.factorSubscripts.toList
  let sig := pyStrLit (subs ++ "->" ++ tl.outputSubscript)
  let args := String.intercalate ", " (tl.factorSlots.toList.map (fun s => s!"slots[{s}]"))
  s!"{indent}{varName} = jnp.einsum({sig}, {args}, optimize=False)"

/-- PRIVATE (Task 4.5): emits the destination write from publicly constructible IR; same gate. -/
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
  | .sourceInvariant c => s!"sourceInvariant: {repr c}"

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

/-- PRIVATE (Task 4.5): emits one factor's gather semantics; reachable only behind
    `renderAffineNode`'s contextual support gate. -/
private def renderAffineFactor (iterationShape : Array Nat) (f : ReadPlan) : String :=
  let (idxs, masks) := buildFactorTable iterationShape f
  "{\"source_slot\": " ++ toString f.sourceSlot ++
  ", \"safe_index\": " ++ pyNatListLit idxs ++
  ", \"mask\": " ++ pyBoolListLit masks ++ "}"

/-- PRIVATE (Task 4.5): emits one term's semantics; same gate. -/
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
    error (via `renderAffineTerm`).

    PRIVATE (Task 4.5), and the single contextual gate of the whole `affineReference` mode: every
    public affine emitter — both plan renderers and the standalone `renderAffineAssign` — reaches a
    node only through here, so `requireJaxSupport` is applied exactly once per node, under the
    table that entry point established (derived for a plan, explicit for a standalone call). -/
private def renderAffineNode (sigs : Array TensorSignature) (nodeIndex : Nat)
    (checked : CheckedAssignPlan) : Except JaxCodegenError String := do
  requireJaxSupport sigs nodeIndex checked
  let a := checked.plan
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
  let sigs := c.raw.tensorSigs
  let mut entries : Array String := #[]
  for h : ni in [0 : c.checkedNodes.size] do
    match c.checkedNodes[ni] with
    | .assign a => entries := entries.push (← renderAffineNode sigs ni a)
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
    for any located Iverson or support rejection.

    Standalone, so it takes the complete signature table explicitly (Task 4.5): that table is this
    call's semantic authority, re-established through `checkAssign` and then the support policy by
    `renderAffineNode`'s gate. -/
def renderAffineAssign (sigs : Array TensorSignature) (c : CheckedAssignPlan) :
    Except JaxCodegenError String :=
  renderAffineNode sigs 0 c

/-- Check, Dense-run, and render one checked-assignment fixture as a `FIXTURES`-list entry. Its
    existing `sigs` argument is now that fixture's explicit semantic authority (Task 4.5): the same
    table checks the assignment and gates its rendering, so a Boolean-source or otherwise
    unsupported fixture fails loud here instead of producing Python.
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

    Standalone conversion, so the complete signature table is explicit and is this call's semantic
    authority (Task 4.5): `requireJaxSupport` re-runs `checkAssign` under `sigs` and applies the
    support policy BEFORE a candidate exists, so an unsupported assignment can never be handed to
    `validateAndConstructKernel` (which would reject it too) or inspected for evidence. The produced
    record itself still stores no signatures — raw candidates are unchanged by this task.
-/
def loweringToAffineTableCandidate (sigs : Array TensorSignature) (nodeIndex : Nat)
    (assign : CheckedAssignPlan) : Except JaxCodegenError OrderedAffineTableKernelCandidate := do
  requireJaxSupport sigs nodeIndex assign
  requireNoIverson nodeIndex assign.plan
  let tables := assign.plan.terms.map (fun term =>
    term.factors.filterMap (fun f => match f with
      | .read r =>
          let (safeIndex, validMask) := buildFactorTable term.iterationShape r
          some ({ source := r.sourceSlot, safeIndex, validMask } : AffineTableReadCandidate)
      | .iverson _ => none))
  return { semanticAssignment := assign, tables }

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
  requireJaxSupport sigs nodeIndex assign
  requireNoIverson nodeIndex assign.plan
  match assign.plan.terms[0]? with
  | none =>
      return { semanticAssignment := assign, destination := assign.plan.destinationSlot
             , operands := #[], outputAxes := #[] }
  | some term =>
      let operands := term.factors.filterMap (fun f => match f with
        | .read r => some (#[r.sourceSlot] ++ r.map.coeffs.filterMap rowProjectionTarget)
        | .iverson _ => none)
      return { semanticAssignment := assign, destination := assign.plan.destinationSlot
             , operands, outputAxes := term.outputPos }

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
  let sigs := plan.plan.raw.tensorSigs
  let mut steps : Array SomeJaxKernel := #[]
  for h : ni in [0 : plan.plan.checkedNodes.size] do
    match plan.plan.checkedNodes[ni] with
    | .assign a =>
        let candidate ← loweringToAffineTableCandidate sigs ni a
        match validateAndConstructKernel sigs (.affineTable candidate) with
        | .ok k => steps := steps.push k
        | .error (.unsupported e) => throw (codegenErrorOfSupport e)
        | .error .invalidCandidate => throw (.unsupportedStep ni)
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
        match validateAndConstructKernel idSigs (.affineTable candidate) with
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
        match validateAndConstructKernel idSigs (.einsum candidate) with
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

/-! ### Task 4.5 — the JAX support gate across every public renderer, lowerer, and conversion

Every fixture here is ADMITTED by the checked backend and rejected only by this experimental
backend. `ExecutableTest` covers the same policy at the validator/executable boundary; what is
exercised here and NOT there is the emission surface: both rendering modes, both plan renderers,
`buildAssignFixture`, both candidate conversions, and the located OUTER STEP INDEX that only a
plan-level walk can produce. -/

/-- Rejected with exactly `expected` (the value is irrelevant; only rejection and its locator are). -/
private def rejectedWith {α : Type} (expected : JaxCodegenError) : Except JaxCodegenError α → Bool
  | .error e => e == expected
  | .ok _ => false

private def preparedOf (raw : RawEvalPlan) (inputs materialized : Array SlotBinding) :
    Option PreparedPlan :=
  match checkPlan raw with
  | .error _ => none
  | .ok checkedPlan =>
    match checkBindings raw.inputSlots inputs with
    | .error _ => none
    | .ok requiredInputs =>
        some { plan := checkedPlan
             , bindings := { requiredInputs, materializedNames := materialized }
             , warnings := [] }

/-! #### Fixture 2 — only the SOURCE signature is Boolean (`bool` slot 0 feeding the real slot 1).
The checked plan accepts it; every public JAX entry point must reject it with the same located
`.unsupportedSourceDType 0 0 0 .bool` (or, at the plan level, that error at the real step index). -/

def boolSourceSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .bool }, { shape := #[3], dtype := .f64 } ]

def boolSourceRaw : RawEvalPlan :=
  { tensorSigs := boolSourceSigs, inputSlots := #[0], steps := #[PlanStep.assign idAssign] }

def boolSourceStore : Array DenseTensor :=
  #[ { shape := [3], data := #[1.0, 0.0, 1.0] }, { shape := [3], data := #[0.0, 0.0, 0.0] } ]

def boolSourcePrepared? : Option PreparedPlan :=
  preparedOf boolSourceRaw #[{ name := "x", slot := 0 }] #[{ name := "y", slot := 1 }]

#guard boolSourcePrepared?.isSome

-- The checked backend admits the Boolean source (Task 4.2: the DESTINATION selects the algebra).
#guard (match checkPlan boolSourceRaw with | .ok _ => true | .error _ => false)

private def boolSourceError : JaxCodegenError := .unsupportedSourceDType 0 0 0 .bool

-- Standalone entries, each taking the complete table explicitly.
#guard (match checkAssign boolSourceSigs idAssign with
  | .error _ => false
  | .ok checked =>
      rejectedWith boolSourceError (lowerAssign boolSourceSigs 0 checked) &&
      rejectedWith boolSourceError (renderAffineAssign boolSourceSigs checked) &&
      rejectedWith boolSourceError (loweringToAffineTableCandidate boolSourceSigs 0 checked) &&
      rejectedWith boolSourceError (loweringToEinsumCandidate boolSourceSigs 0 checked))

-- Plan-level entries, each DERIVING the table from the checked/prepared plan — none of them can be
-- handed a parallel all-real table by a caller.
#guard (match checkPlan boolSourceRaw, boolSourcePrepared? with
  | .ok checkedPlan, some prepared =>
      rejectedWith boolSourceError (lowerPlan checkedPlan) &&
      rejectedWith boolSourceError (renderAffinePlanPositional checkedPlan) &&
      rejectedWith boolSourceError (renderAffinePlanNamed prepared) &&
      rejectedWith boolSourceError (generateForward prepared) &&
      rejectedWith boolSourceError (generateNamed .einsumOnly prepared) &&
      rejectedWith boolSourceError (generateNamed .affineReference prepared) &&
      rejectedWith boolSourceError (lowerCheckPlanToCandidate prepared)
  | _, _ => false)

-- `buildAssignFixture` is `IO`, so its guard is an `#eval` that throws on the wrong outcome: the
-- fixture builder must fail at the RENDER step (the checker and the Dense run both succeed on a
-- Boolean source), so the reported message is the render one.
#eval show IO Unit from do
  let outcome ← try
      let _ ← buildAssignFixture "boolSource" boolSourceSigs idAssign boolSourceStore
      pure "accepted"
    catch e => pure (toString e)
  unless (outcome.splitOn "render failed").length == 2 do
    throw (IO.userError s!"buildAssignFixture did not reject the Boolean source at render: {outcome}")

/-! #### Fixture 4 (rendering half) — an inline unary read is a located rejection in BOTH modes. -/

def unaryRead : ReadPlan := { idRead with unary := some .exp }

def unaryAssign : AssignPlan :=
  { idAssign with terms := #[{ idAssign.terms[0]! with factors := #[.read unaryRead] }] }

def unaryRaw : RawEvalPlan :=
  { tensorSigs := idSigs, inputSlots := #[0], steps := #[PlanStep.assign unaryAssign] }

def unaryPrepared? : Option PreparedPlan :=
  preparedOf unaryRaw #[{ name := "x", slot := 0 }] #[{ name := "y", slot := 1 }]

#guard (match checkPlan unaryRaw with | .ok _ => true | .error _ => false)

#guard (match unaryPrepared? with
  | some prepared =>
      rejectedWith (.unaryFactor 0 0 0) (generateNamed .einsumOnly prepared) &&
      rejectedWith (.unaryFactor 0 0 0) (generateNamed .affineReference prepared)
  | none => false)

#guard (match checkAssign idSigs unaryAssign with
  | .error _ => false
  | .ok checked =>
      rejectedWith (.unaryFactor 0 0 0) (loweringToAffineTableCandidate idSigs 0 checked) &&
      rejectedWith (.unaryFactor 0 0 0) (loweringToEinsumCandidate idSigs 0 checked))

/-! #### Fixture 5 — the Iverson factor keeps its ORIGINAL all-factor index `1` through the new
contextual candidate conversions, exactly as both rendering modes already report it
(`iversonFactor 0 0 1`, asserted above). The read at factor index 0 is what makes the index
non-tautological: a reindexed read-only walk would report `0`. -/

#guard (match checkAssign idSigs idIversonAssign with
  | .error _ => false
  | .ok checked =>
      rejectedWith (.iversonFactor 0 0 1) (loweringToAffineTableCandidate idSigs 0 checked) &&
      rejectedWith (.iversonFactor 0 0 1) (loweringToEinsumCandidate idSigs 0 checked))

/-! #### Fixture 6 — a two-step plan whose step 1 (not step 0) has the Boolean destination. The
rejection must name step `1`: the outer graph index, not "the first assignment" (`0`) and not the
first Boolean thing seen. -/

def mixedBoolDestSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 }
   , { shape := #[3], dtype := .bool } ]

def mixedRead12 : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[3], oobPolicy := .zeroPad }

/-- Step 1: `Z[i] := Y[i]` into the Boolean slot 2, under the Boolean algebra (both must change
    together or `checkAssign` would reject the step before the JAX gate ran). -/
def mixedBoolDestAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read mixedRead12] }]
  , algebra := admittedAlgebraBool }

def mixedBoolDestRaw : RawEvalPlan :=
  { tensorSigs := mixedBoolDestSigs, inputSlots := #[0]
  , steps := #[PlanStep.assign idAssign, PlanStep.assign mixedBoolDestAssign] }

def mixedBoolDestPrepared? : Option PreparedPlan :=
  preparedOf mixedBoolDestRaw #[{ name := "x", slot := 0 }]
    #[{ name := "y", slot := 1 }, { name := "z", slot := 2 }]

#guard (match checkPlan mixedBoolDestRaw with | .ok _ => true | .error _ => false)

#guard (match checkPlan mixedBoolDestRaw, mixedBoolDestPrepared? with
  | .ok checkedPlan, some prepared =>
      rejectedWith (.unsupportedDestDType 1 2 .bool) (lowerPlan checkedPlan) &&
      rejectedWith (.unsupportedDestDType 1 2 .bool) (renderAffinePlanNamed prepared) &&
      rejectedWith (.unsupportedDestDType 1 2 .bool) (lowerCheckPlanToCandidate prepared)
  | _, _ => false)

/-! #### Fixture 11 — plan authority and standalone context attacks

(a) The plan-level conversion has NO caller table: it derives `PreparedPlan.plan.raw.tensorSigs`, so
the Boolean-source plan above cannot be validated by supplying a same-shape all-real substitute. The
guard is the rejection itself — a caller-selectable table (or a plan API that mapped its derived
table to all-`f64`) would make it accept. -/

def allRealSubstituteSigs : Array TensorSignature :=
  boolSourceSigs.map (fun sig => { sig with dtype := ScalarDType.f64 })

-- The substitute really is same-shape and all-real, so the attack is about AUTHORITY, not shape.
#guard allRealSubstituteSigs == idSigs

def testVariantBPlanAuthoritySubstitutionRejected : Bool :=
  match boolSourcePrepared? with
  | none => false
  | some prepared =>
      rejectedWith boolSourceError (lowerCheckPlanToCandidate prepared) &&
      rejectedWith boolSourceError (generateNamed .affineReference prepared)

#guard testVariantBPlanAuthoritySubstitutionRejected

/-! (b) A standalone all-real table whose SHAPES do not match the assignment is rejected by the
re-run `checkAssign`, not silently consulted for its dtype tags. Every standalone entry does this. -/

def mismatchedShapeSigs : Array TensorSignature :=
  #[ { shape := #[4], dtype := .f64 }, { shape := #[3], dtype := .f64 } ]

private def contextError : JaxCodegenError :=
  .invalidSignatureContext 0 (.sourceShapeMismatch 0 0 #[3] #[4])

#guard (match checkAssign idSigs idAssign with
  | .error _ => false
  | .ok checked =>
      rejectedWith contextError (lowerAssign mismatchedShapeSigs 0 checked) &&
      rejectedWith contextError (renderAffineAssign mismatchedShapeSigs checked) &&
      rejectedWith contextError (loweringToAffineTableCandidate mismatchedShapeSigs 0 checked) &&
      rejectedWith contextError (loweringToEinsumCandidate mismatchedShapeSigs 0 checked))

/-! (c) A two-step plan whose Boolean READ is only at step 1. Step 0 is fully supported, so a
per-step decision that cached or reused step 0's context/result would accept the plan; the located
rejection must name step 1. -/

def step1BoolSigs : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[3], dtype := .f64 }
   , { shape := #[3], dtype := .bool }, { shape := #[3], dtype := .f64 } ]

def boolRead2 : ReadPlan :=
  { sourceSlot := 2, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[3], oobPolicy := .zeroPad }

def step1BoolAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 3, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read boolRead2] }]
  , algebra := admittedAlgebra }

def step1BoolRaw : RawEvalPlan :=
  { tensorSigs := step1BoolSigs, inputSlots := #[0, 2]
  , steps := #[PlanStep.assign idAssign, PlanStep.assign step1BoolAssign] }

def step1BoolPrepared? : Option PreparedPlan :=
  preparedOf step1BoolRaw #[{ name := "x", slot := 0 }, { name := "v", slot := 2 }]
    #[{ name := "y", slot := 1 }, { name := "w", slot := 3 }]

#guard (match checkPlan step1BoolRaw with | .ok _ => true | .error _ => false)

-- The exact locator: step 1, term 0, factor 0, `bool` — step and slot cannot be confused (the
-- Boolean slot is 2, the step is 1, and the term/factor are both 0).
#guard (match checkPlan step1BoolRaw, step1BoolPrepared? with
  | .ok checkedPlan, some prepared =>
      rejectedWith (.unsupportedSourceDType 1 0 0 .bool) (lowerPlan checkedPlan) &&
      rejectedWith (.unsupportedSourceDType 1 0 0 .bool) (renderAffinePlanPositional checkedPlan) &&
      rejectedWith (.unsupportedSourceDType 1 0 0 .bool) (generateForward prepared) &&
      rejectedWith (.unsupportedSourceDType 1 0 0 .bool) (lowerCheckPlanToCandidate prepared)
  | _, _ => false)

/-! ### Task 4.5 re-review — the einsum emitter's TERM-level preconditions, both halves agreeing

The validator half of these three fixtures lives in `test/Eval/Plan/ExecutableTest.lean` (fixture
12). What is exercised HERE is the emitter half plus the agreement itself: each assignment is
checked, `lowerAssign` rejects it with its located error, and `validateEinsum` — which used to
certify all three — now rejects the corresponding candidate too. Before the fix, every
`einsumRenderAgrees` call below returned `false` on its `validateEinsum` conjunct while the located
emitter rejection already held, which is exactly the validator/emitter disagreement the re-review
reproduced (`validator=accepted; emitter=rejected emptyTerm 0 0`). -/

/-- `lowerAssign` rejects with exactly `expected` AND `validateEinsum` rejects the candidate the
    conversion builds for the same assignment: agreement, not merely two rejections. -/
private def einsumRenderAgrees (sigs : Array TensorSignature) (a : AssignPlan)
    (expected : JaxCodegenError) : Bool :=
  match checkAssign sigs a with
  | .error _ => false
  | .ok checked =>
      rejectedWith expected (lowerAssign sigs 0 checked) &&
      (match loweringToEinsumCandidate sigs 0 checked with
       | .error _ => false  -- the conversion itself is total here; the VALIDATOR must be the gate
       | .ok candidate => !(validateEinsum sigs candidate))

/-- …and the mirror image: `lowerAssign` renders it and `validateEinsum` accepts the same
    conversion's candidate. The acceptance siblings are what keep the guards above from being
    satisfiable by a validator that simply rejects everything. -/
private def einsumRenderAgreesAccepted (sigs : Array TensorSignature) (a : AssignPlan) : Bool :=
  match checkAssign sigs a with
  | .error _ => false
  | .ok checked =>
      (match lowerAssign sigs 0 checked with | .ok _ => true | .error _ => false) &&
      (match loweringToEinsumCandidate sigs 0 checked with
       | .error _ => false
       | .ok candidate => validateEinsum sigs candidate)

-- (a) Factor-free term: `.emptyTerm 0 0` — the case the re-review reproduced.
def scalarSigs : Array TensorSignature :=
  #[ { shape := #[], dtype := .f64 }, { shape := #[], dtype := .f64 } ]

def scalarRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[], bias := #[] }
  , sourceShape := #[], oobPolicy := .zeroPad }

def factorFreeAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[]
  , terms := #[{ iterationShape := #[], contextPos := #[], outputPos := #[], reductionPos := #[]
               , factors := #[] }]
  , algebra := admittedAlgebra }

def scalarFactorAssign : AssignPlan :=
  { factorFreeAssign with
    terms := #[{ factorFreeAssign.terms[0]! with factors := #[.read scalarRead] }] }

#guard einsumRenderAgrees scalarSigs factorFreeAssign (.emptyTerm 0 0)
#guard einsumRenderAgreesAccepted scalarSigs scalarFactorAssign

-- The affine mode still renders the factor-free term (empty factor list), so the tightening is
-- einsum-scoped: the plan-level path and the corpus route through `affineReference`.
#guard (match checkAssign scalarSigs factorFreeAssign with
  | .error _ => false
  | .ok checked => (match renderAffineAssign scalarSigs checked with
      | .ok _ => true | .error _ => false))

-- (b) Uncovered iteration position: `Y[i] := Σ_j V[i]` leaves position 1 on no operand.
def covSigs : Array TensorSignature :=
  #[ { shape := #[2, 2], dtype := .f64 }, { shape := #[2], dtype := .f64 }
   , { shape := #[2], dtype := .f64 } ]

def vecRead : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1, 0]], bias := #[0] }
  , sourceShape := #[2], oobPolicy := .zeroPad }

def matRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1, 0], #[0, 1]], bias := #[0, 0] }
  , sourceShape := #[2, 2], oobPolicy := .zeroPad }

def uncoveredAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[2]
  , terms := #[{ iterationShape := #[2, 2], contextPos := #[], outputPos := #[0]
               , reductionPos := #[1], factors := #[.read vecRead] }]
  , algebra := admittedAlgebra }

def coveredAssign : AssignPlan :=
  { uncoveredAssign with
    terms := #[{ uncoveredAssign.terms[0]! with factors := #[.read matRead] }] }

#guard einsumRenderAgrees covSigs uncoveredAssign (.uncoveredPosition 0 0 1)
#guard einsumRenderAgreesAccepted covSigs coveredAssign

-- (c) Label-table overflow: rank 27 > `labelTable.size`, every position covered, every row an exact
-- single-`1` projection — only the rank separates it from the accepted rank-26 sibling.
def wideShape (rank : Nat) : Array Nat := Array.replicate rank 1

def wideRow (rank p : Nat) : Array Int :=
  (List.range rank).toArray.map (fun q => if q == p then 1 else 0)

def wideRead (rank : Nat) : ReadPlan :=
  { sourceSlot := 0
  , map := { coeffs := (List.range rank).toArray.map (wideRow rank)
           , bias := Array.replicate rank (0 : Int) }
  , sourceShape := wideShape rank, oobPolicy := .zeroPad }

def wideSigs (rank : Nat) : Array TensorSignature :=
  #[ { shape := wideShape rank, dtype := .f64 }, { shape := #[1], dtype := .f64 } ]

def wideAssign (rank : Nat) : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[1]
  , terms := #[{ iterationShape := wideShape rank, contextPos := #[], outputPos := #[0]
               , reductionPos := ((List.range rank).drop 1).toArray
               , factors := #[.read (wideRead rank)] }]
  , algebra := admittedAlgebra }

#guard einsumRenderAgrees (wideSigs 27) (wideAssign 27) (.rankTooLarge 0 0 27)
#guard einsumRenderAgreesAccepted (wideSigs 26) (wideAssign 26)

/-! ### Whole-branch review — label extents: the public einsum lowering must not emit a program it
does not mean

A zero-padded read whose source extent (2) is smaller than its own iteration extent (3) is a
checked, Dense-executable assignment (`ExecutableTest`'s fixture 13 pins the three-element
zero-padded Dense result). The einsum string it lowers to, `a->a`, is perfectly well-formed — but
`jnp.einsum` takes label `a`'s extent from the OPERAND, so the rendered kernel returns two elements
where Dense returns three. It is a DIFFERENT function.

Round 2 closed this at the evidence boundary only: `validateEinsum` refused to certify it while
`lowerAssign` still rendered it, a deliberate one-sided disagreement pinned here by a fixture named
`einsumRendersButNotCertified`. The whole-branch review ruled that insufficient — `lowerAssign` is
itself a public entry, and `generateForward`/the plan renderers reach emitted Python through it, so
returning the program at all hands a caller a semantically unsupported einsum. Both sides now reject,
through the SAME recomputation (`LeanNCD.Eval.Plan.einsumTermLabelExtents`, called by the emitter,
not copied), and the fixtures below pin the agreement plus the exact located emitter error.

The affine-reference mode still renders the mismatch, and must: its tables carry the zero-pad mask
explicitly, so it computes what the checked plan means. -/

/-- `lowerAssign` rejects with exactly `expected` AND `validateEinsum` rejects the candidate the
    conversion builds for the same assignment — `einsumRenderAgrees`, fixture 12's own agreement
    helper, reused unchanged for the extent rule. -/
def padSigs (srcExtent : Nat) : Array TensorSignature :=
  #[ { shape := #[srcExtent], dtype := .f64 }, { shape := #[3], dtype := .f64 } ]

def padRead (srcExtent : Nat) : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[srcExtent], oobPolicy := .zeroPad }

def padAssign (srcExtent : Nat) : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[3]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read (padRead srcExtent)] }]
  , algebra := admittedAlgebra }

-- The exact located rejection: term 0, factor 0, source dimension 0, iteration position 0, source
-- extent 2 against iteration extent 3 — and `validateEinsum` rejects the same conversion's candidate.
#guard einsumRenderAgrees (padSigs 2) (padAssign 2)
  (.labelExtentMismatch 0 0 0 0 0 2 (some 3))

-- …and the plan-level einsum entries inherit it, since every one routes each `.assign` step through
-- `lowerAssign`. `bit`-for-bit the same located cause, at step 0.
def padRaw : RawEvalPlan :=
  { tensorSigs := padSigs 2, inputSlots := #[0], steps := #[PlanStep.assign (padAssign 2)] }

def padPrepared? : Option PreparedPlan :=
  preparedOf padRaw #[{ name := "v", slot := 0 }] #[{ name := "y", slot := 1 }]

#guard (match checkPlan padRaw, padPrepared? with
  | .ok checkedPlan, some prepared =>
      rejectedWith (.labelExtentMismatch 0 0 0 0 0 2 (some 3)) (lowerPlan checkedPlan) &&
      rejectedWith (.labelExtentMismatch 0 0 0 0 0 2 (some 3)) (generateForward prepared) &&
      rejectedWith (.labelExtentMismatch 0 0 0 0 0 2 (some 3)) (generateNamed .einsumOnly prepared)
  | _, _ => false)

-- The exact-match sibling differs in exactly one number (the source extent) and renders `a->a` —
-- the SAME string the mismatch would have produced — so the rendering cannot be what separates
-- them; both halves accept it, and its plan renders end to end in einsum mode.
#guard einsumRenderAgreesAccepted (padSigs 3) (padAssign 3)

#guard (match checkAssign (padSigs 3) (padAssign 3) with
  | .error _ => false
  | .ok checked =>
      (match lowerAssign (padSigs 3) 0 checked with
       | .error _ => false
       | .ok nl => nl.terms.map (fun tl =>
           String.intercalate "," tl.factorSubscripts.toList ++ "->" ++ tl.outputSubscript)
             == #["a->a"]))

def padOkRaw : RawEvalPlan :=
  { tensorSigs := padSigs 3, inputSlots := #[0], steps := #[PlanStep.assign (padAssign 3)] }

def padOkPrepared? : Option PreparedPlan :=
  preparedOf padOkRaw #[{ name := "v", slot := 0 }] #[{ name := "y", slot := 1 }]

#guard (match padOkPrepared? with
  | some prepared => (match generateForward prepared with | .ok _ => true | .error _ => false)
  | none => false)

-- The affine mode still renders the mismatch (its tables carry the zero-pad mask explicitly), so
-- the tightening is einsum-scoped, exactly as for fixture 12's three preconditions.
#guard (match checkAssign (padSigs 2) (padAssign 2) with
  | .error _ => false
  | .ok checked => (match renderAffineAssign (padSigs 2) checked with
      | .ok _ => true | .error _ => false))

#guard (match padPrepared? with
  | some prepared => (match generateNamed .affineReference prepared with
      | .ok _ => true | .error _ => false)
  | none => false)

/-! ### Task 4.5 closure — a CONTEXTFUL assignment has no rendering in EITHER mode

The emission half of `test/Eval/Plan/ExecutableTest.lean`'s fixture 14. An `AssignPlan` with a
non-empty `contextShape` denotes a family of results indexed by a runtime context coordinate
(`Dense.runDenseAssignAt` binds it at every term's `contextPos`), and neither mode here has a kernel
parameter for that coordinate — nor did either notice: `einsumOnly` used to render the fixture below
as `a->` (the context position treated as an ordinary label and CONTRACTED away) and
`affineReference` used to emit its terms with no `context_pos` key at all, while Dense returns
`10` at context `0` and `20` at context `1`. Both are now the one located
`unsupportedContext` rejection from the shared gate, before any Python.

Unlike the Boolean/tropical/unary fixtures above, there is no plan-level half to assert: `checkPlan`
refuses a contextful top-level step outright (`topLevelContextNotEmpty`, pinned below), so no
`CheckedEvalPlan`/`PreparedPlan` naming one can be built for `lowerPlan`/`renderAffinePlanNamed`/
`generateNamed`/`lowerCheckPlanToCandidate` to be handed. Those entries are covered structurally
instead: each routes every `.assign` step through the same `requireJaxSupport` the standalone
entries below call, so they cannot drift apart. (A contextful assignment is legal only inside a scan
block, and every `.scan` step is already the located `unsupportedStep` rejection asserted above.) -/

def ctxSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }, { shape := #[], dtype := .f64 } ]

def ctxRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[2], oobPolicy := .zeroPad }

/-- `Y[] := X[l]` at context coordinate `l`. -/
def ctxAssign : AssignPlan :=
  { contextShape := #[2], destinationSlot := 1, outputShape := #[]
  , terms := #[{ iterationShape := #[2], contextPos := #[0], outputPos := #[], reductionPos := #[]
               , factors := #[.read ctxRead] }]
  , algebra := admittedAlgebra }

/-- The context-free sibling: same read, same affine map, same source extent, same algebra — the one
    iteration position is classified `outputPos` instead of `contextPos`, which is what makes the
    destination `#[2]`-shaped instead of scalar. -/
def ctxFreeSigs : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f64 }, { shape := #[2], dtype := .f64 } ]

def ctxFreeAssign : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[2]
  , terms := #[{ iterationShape := #[2], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read ctxRead] }]
  , algebra := admittedAlgebra }

def ctxStore : Array DenseTensor :=
  #[ { shape := [2], data := #[10.0, 20.0] }, { shape := [], data := #[0.0] } ]

-- The checked backend admits both; only this backend rejects the contextful one.
#guard (match checkAssign ctxSigs ctxAssign with | .ok _ => true | .error _ => false)
#guard (match checkAssign ctxFreeSigs ctxFreeAssign with | .ok _ => true | .error _ => false)

private def ctxError : JaxCodegenError := .unsupportedContext 0 #[2]

-- Every standalone entry — both rendering modes and both candidate conversions — rejects with the
-- same located cause under the table the caller supplied as its semantic authority.
#guard (match checkAssign ctxSigs ctxAssign with
  | .error _ => false
  | .ok checked =>
      rejectedWith ctxError (lowerAssign ctxSigs 0 checked) &&
      rejectedWith ctxError (renderAffineAssign ctxSigs checked) &&
      rejectedWith ctxError (loweringToAffineTableCandidate ctxSigs 0 checked) &&
      rejectedWith ctxError (loweringToEinsumCandidate ctxSigs 0 checked))

-- The context-free sibling still renders in BOTH modes and is still certified through both
-- conversions, so the gate rejects the context, not the read.
#guard (match checkAssign ctxFreeSigs ctxFreeAssign with
  | .error _ => false
  | .ok checked =>
      (match lowerAssign ctxFreeSigs 0 checked with
       | .error _ => false
       | .ok nl => nl.terms.map (fun tl =>
           String.intercalate "," tl.factorSubscripts.toList ++ "->" ++ tl.outputSubscript)
             == #["a->a"]) &&
      (match renderAffineAssign ctxFreeSigs checked with | .ok _ => true | .error _ => false))

#guard einsumRenderAgreesAccepted ctxFreeSigs ctxFreeAssign

#guard (match checkAssign ctxFreeSigs ctxFreeAssign with
  | .error _ => false
  | .ok checked =>
      match loweringToAffineTableCandidate ctxFreeSigs 0 checked with
      | .error _ => false
      | .ok candidate =>
        match validateAndConstructKernel ctxFreeSigs (.affineTable candidate) with
        | .ok k => k.evidence == ExecutionEvidence.orderedReference64
        | .error _ => false)

-- Plan level: the contextful assignment cannot even be posed as a top-level step, while the
-- context-free sibling's plan renders and lowers end to end through the plan-level entries.
def ctxRaw : RawEvalPlan :=
  { tensorSigs := ctxSigs, inputSlots := #[0], steps := #[PlanStep.assign ctxAssign] }

#guard (match checkPlan ctxRaw with
  | .error e => e == PlanStepError.assign (.topLevelContextNotEmpty 0)
  | .ok _ => false)

def ctxFreeRaw : RawEvalPlan :=
  { tensorSigs := ctxFreeSigs, inputSlots := #[0], steps := #[PlanStep.assign ctxFreeAssign] }

def ctxFreePrepared? : Option PreparedPlan :=
  preparedOf ctxFreeRaw #[{ name := "x", slot := 0 }] #[{ name := "y", slot := 1 }]

#guard (match ctxFreePrepared? with
  | some prepared =>
      (match generateNamed .einsumOnly prepared with | .ok _ => true | .error _ => false) &&
      (match generateNamed .affineReference prepared with | .ok _ => true | .error _ => false) &&
      (match lowerCheckPlanToCandidate prepared with | .ok _ => true | .error _ => false)
  | none => false)

-- `buildAssignFixture` cannot emit a contextful fixture either, and fails BEFORE the render gate:
-- it Dense-runs at the empty context coordinate, which a contextful assignment rejects
-- (`validateContext`). The render gate itself is pinned directly by `renderAffineAssign` above; the
-- point here is that no driver can smuggle one in through the shared fixture builder.
#eval show IO Unit from do
  let outcome ← try
      let _ ← buildAssignFixture "ctxAssign" ctxSigs ctxAssign ctxStore
      pure "accepted"
    catch e => pure (toString e)
  unless (outcome.splitOn "Dense run failed").length == 2 do
    throw (IO.userError s!"buildAssignFixture did not reject the contextful assignment: {outcome}")

end JaxBridge

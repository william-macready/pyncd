import LeanNCD.Eval.Plan.Adapter
import LeanNCD.DSL.Compile

/-!
# Wave C JAX evaluator smoke test (`docs/superpowers/plans/2026-08-10-jax-evalplan-smoke.md`, Task 1)

A narrow, experimental Lean → `jnp.einsum` code generator plus its executable driver, both in one
file per the plan ("one failure mode and one execution cycle"). Input is exclusively `PreparedPlan`
/ `CheckedEvalPlan` (`LeanNCD.Eval.Plan`): the generator reads only checker-produced positional data
and the source-name bindings `prepareEvalPlan` already computed, never source syntax, axis UIDs, or
upstream `NetSpec`.

This experiment targets Wave C's current `AssignPlan`: no context-shape/context-position fields
exist yet on `AssignPlan`/`TermPlan` (that is Wave F's F1 concern), so "no context position is
present" from the plan's exact admitted fragment is true by construction here — there is no field
to check, and nothing has to be added speculatively ahead of F1 landing.

Kept out of the default build: not registered in `lakefile.toml`, no `LeanNCD` public API touched,
no JAX dependency added anywhere in this project's own toolchain.
-/

namespace LeanNCD.Eval.Plan.JaxSmoke

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

/-! ## 1. Closed codegen diagnostics -/

/-- Every way this narrow `einsum`-only backend refuses an otherwise-checked plan. Closed, with a
    node/term/factor/row location on every constructor that has one available — mirrors the
    discipline `PlanError`/`CapabilityError` (`Eval/Plan/Error.lean`) already established: no
    `unsupported : String` escape hatch, no constructor added ahead of a real matcher branch below
    that throws it. -/
inductive JaxCodegenError
  /-- A term with zero factors: `TermPlan.factors` is empty. The exact admitted fragment calls this
      a "factor-free constant term"; this backend has no constant-term lowering. -/
  | emptyTerm             (nodeIndex termIndex : Nat)
  /-- An `AssignPlan` with zero terms. Not reachable from `prepareEvalPlan` today (every source RHS
      lowers to at least one term), but kept as a real, closed rejection rather than an unchecked
      assumption — the same "closed over every matcher branch" discipline as `emptyTerm`. -/
  | emptyAssign           (nodeIndex : Nat)
  /-- One `AffineMap` row (one source dimension) has a nonzero bias — an affine shift such as
      `A[i + 1]`. This is the constructor the shifted fixture below must trigger. -/
  | nonzeroAffineBias     (nodeIndex termIndex factorIndex rowIndex : Nat) (biasVal : Int)
  /-- One `AffineMap` row is not a pure single-`1` projection onto exactly one iteration-basis
      position: zero nonzero entries (a constant/broadcast read), more than one nonzero entry
      (a general affine combination), or a lone nonzero entry whose coefficient is not exactly `1`
      (a stride/scale). `einsum` subscripts cannot express any of these. -/
  | nonProjectionRow      (nodeIndex termIndex factorIndex rowIndex : Nat) (row : Array Int)
  /-- Some output or reduction iteration-basis position is not the projection target of any factor
      row in this term. Covers unused reduction positions that would otherwise silently contribute
      multiplicity, and output-only broadcast positions no factor reads. -/
  | uncoveredPosition     (nodeIndex termIndex position : Nat)
  /-- A term's iteration-basis rank exceeds the deterministic ASCII label table (`labelTable`, 26
      lowercase letters) this generator assigns subscript letters from. -/
  | rankTooLarge          (nodeIndex termIndex rank : Nat)
  /-- A source-name binding refers outside the checked plan's tensor-signature table. This is
      unreachable for `PreparedPlan` values produced by `prepareEvalPlan`, but remains a distinct
      diagnostic rather than being mislabeled as an unrelated lowering failure. -/
  | bindingSlotOutOfRange (slot tableSize : Nat)
  /-- The executable smoke fixture omitted a concrete tensor required by its prepared binding. -/
  | missingFixtureInput   (name : String)
  /-- Defensive, total-match-only branch: a position derived from a checked, in-range affine row
      fell outside `labelTable`. Unreachable given `rankTooLarge` already rejects any term whose
      rank exceeds the table — kept so `labelTable`'s lookup stays a real `Option` match (no `!`/
      `getD` placeholder) rather than an unchecked index. -/
  | labelTableExhausted   (nodeIndex termIndex position : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-! ## 2. Deterministic Python string rendering -/

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

/-! ## 3. Projection-row recognition and subscript construction -/

/-- The deterministic ASCII label table: subscript letters are assigned to iteration-basis
    positions `0, 1, …` in order, one term at a time (each term gets its own fresh `a, b, …`
    naming — the fixture's two terms both start again from `a`, matching the plan's worked
    example `"ab,b->a"` / `"a->a"`). -/
def labelTable : Array Char := "abcdefghijklmnopqrstuvwxyz".toList.toArray

/-- Whether one `AffineMap` row is a pure single-`1` projection, and onto which position. `none`
    covers every non-projection shape at once: no nonzero entry, more than one nonzero entry, or a
    lone nonzero entry whose value isn't exactly `1`. -/
def rowProjectionTarget (row : Array Int) : Option Nat :=
  let nonzero := (List.range row.size).zip row.toList |>.filter (fun (_, c) => c != 0)
  match nonzero with
  | [(p, 1)] => some p
  | _ => none

/-- One factor's derived `einsum` input subscript (one label per source dimension, in source-
    dimension order) and the set of iteration-basis positions it covers. Fails loud on any nonzero
    bias or non-projection row before considering coverage. -/
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

/-- One term's derived `einsum` lowering: per-factor input subscripts (in factor order) paired
    with the source slot each reads, and the output subscript derived from `outputPos`. -/
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

/-! ## 4. Assignment-node emission, in checked graph order -/

/-- One node's derived lowering: which slot it writes and each term's `TermLowering`, in the
    checked plan's own term order (`AssignPlan.terms`). -/
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

/-- The whole checked graph's lowering, in `CheckedEvalPlan.checkedNodes` order — exactly raw graph
    order, by `checkPlan`'s own construction (`Check.lean`). -/
def lowerPlan (c : CheckedEvalPlan) : Except JaxCodegenError (Array NodeLowering) := do
  let mut nodes : Array NodeLowering := #[]
  for h : ni in [0 : c.checkedNodes.size] do
    let node ← lowerAssign ni c.checkedNodes[ni].plan
    nodes := nodes.push node
  return nodes

/-- One term's rendered `jnp.einsum` call, assigned to a node/term-indexed local Python name so
    distinct nodes never collide inside the same `forward` body. -/
def renderTermLine (indent : String) (tl : TermLowering) (varName : String) : String :=
  let subs := String.intercalate "," tl.factorSubscripts.toList
  let sig := pyStrLit (subs ++ "->" ++ tl.outputSubscript)
  let args := String.intercalate ", " (tl.factorSlots.toList.map (fun s => s!"slots[{s}]"))
  s!"{indent}{varName} = jnp.einsum({sig}, {args}, optimize=False)"

/-- One node's rendered Python lines: one `jnp.einsum` line per term, then one line combining every
    term with `+` (in checked term-array order) into the destination slot. Wave C's checker forces
    `algebra == admittedAlgebra` for every node (`checkAssign`, `Check.lean`) — real sum-product
    with `.add`/`.mul` — so `+` is the only combine operator this backend ever needs to emit. -/
def renderNodeLines (indent : String) (n : NodeLowering) : Array String :=
  let termVar (ti : Nat) := s!"n{n.nodeIndex}_term{ti}"
  let termLines := n.terms.mapIdx (fun ti tl => renderTermLine indent tl (termVar ti))
  let combine := String.intercalate " + " ((List.range n.terms.size).map termVar)
  termLines.push s!"{indent}slots[{n.destinationSlot}] = {combine}"

/-! ## 5–7. Slot init, shape checks, and output reconstruction -/

/-- Static input-shape check lines, sourced from the checked plan's own `tensorSigs` (never the
    concrete fixture values) — item 7 of the plan's Task 1 list. Runs before any slot is populated,
    so a caller mismatch is reported before any `einsum` executes. -/
def renderShapeCheckLine (indent : String) (raw : RawEvalPlan) (b : SlotBinding) :
    Except JaxCodegenError String := do
  match raw.tensorSigs[b.slot]? with
  | none => throw (.bindingSlotOutOfRange b.slot raw.tensorSigs.size)
      -- unreachable: `requiredInputs` slots are always in-range table entries because
      -- `prepareEvalPlan` allocates them from `tensorSigs` itself.
  | some sig =>
      let nm := pyStrLit b.name
      let shape := pyShapeTuple sig.shape
      return s!"{indent}if tuple(inputs[{nm}].shape) != {shape}:\n" ++
        s!"{indent}    raise ValueError(" ++ pyStrLit "input " ++ " + " ++ nm ++ " + " ++
        pyStrLit s!" expected shape {shape}, got " ++ " + str(tuple(inputs[" ++ nm ++ "].shape)))"

/-- Positional slot initialization from `PreparedPlan.bindings.requiredInputs` — item 5. Each
    binding both checks its caller-supplied shape and places the tensor into its positional slot. -/
def renderSlotInitLines (indent : String) (raw : RawEvalPlan) (requiredInputs : Array SlotBinding) :
    Except JaxCodegenError (Array String) := do
  let mut lines : Array String := #[]
  for b in requiredInputs do
    let check ← renderShapeCheckLine indent raw b
    lines := lines.push check
    lines := lines.push s!"{indent}slots[{b.slot}] = inputs[{pyStrLit b.name}]"
  return lines

/-- Materialized output reconstruction from `PreparedPlan.bindings.materializedNames` — item 6.
    Entries are emitted in schedule order (exactly as stored, no dedup): a name written by two
    statements gets two `outputs[name] = …` lines, and ordinary Python dict-assignment overwrite
    means the LAST one — the plan's own last write — is what survives, with no separate
    "most recent" bookkeeping needed (mirrors `Adapter.unpack`'s identical idiom). -/
def renderOutputLines (indent : String) (materializedNames : Array SlotBinding) : Array String :=
  materializedNames.map (fun b => s!"{indent}outputs[{pyStrLit b.name}] = slots[{b.slot}]")

/-- The full `forward(inputs)` function body, generated entirely from `PreparedPlan` — no source
    syntax, axis UIDs, or fixture-specific literals appear anywhere in this function. -/
def generateForward (plan : PreparedPlan) : Except JaxCodegenError String := do
  let raw := plan.plan.raw
  let nodes ← lowerPlan plan.plan
  let slotInitLines ← renderSlotInitLines "    " raw plan.bindings.requiredInputs
  let nodeLines := nodes.flatMap (renderNodeLines "    ")
  let outputLines := renderOutputLines "    " plan.bindings.materializedNames
  let lines : Array String :=
    #["def forward(inputs):", s!"    slots = [None] * {raw.tensorSigs.size}"]
    ++ slotInitLines ++ nodeLines
    ++ #["    outputs = {}"] ++ outputLines ++ #["    return outputs"]
  return String.intercalate "\n" lines.toList

/-! ## 8. Fixture preparation, Dense execution, and generated-module writing -/

def affineProg : TLProgram := tlprog!{
  Y[i] := W[i, j] · x[j] + b[i]
}

def affineInputs : HashMap String DenseTensor :=
  HashMap.ofList
    [ ("W", ⟨[2, 1], #[2.0, 3.0]⟩)
    , ("x", ⟨[1], #[5.0]⟩)
    , ("b", ⟨[2], #[1.0, 1.0]⟩) ]

def shiftedProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[i + 1]
}

/-- Renders the module-level constants Task 2's Python consumer reconstructs concrete tensors
    from: each required input's checked shape plus its concrete `Float.toBits` payload (never a
    bare `Float` literal — `Types.lean`'s `ScalarConst` doc comment records why bits, not floats,
    are the dtype-preserving canonical form). Fixture-specific (reads concrete `DenseTensor`
    values), unlike `generateForward` above — this is driver code, item 8, not the generic
    generator, items 1–7. -/
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

/-- Renders the independent expected-output constants: the Dense-executed result, not anything
    reconstructible from the `einsum` lowering itself — this is the numeric oracle Task 2 checks
    JAX eager/`jit` output against. -/
def renderExpectedOutputConstants (name : String) (t : DenseTensor) : String :=
  let shape := pyShapeTuple t.shape.toArray
  let bits := pyUInt64ListLit (t.data.map Float.toBits)
  s!"EXPECTED_OUTPUT_NAME = {pyStrLit name}\n" ++
  s!"EXPECTED_OUTPUT_SHAPE = {shape}\n" ++
  s!"EXPECTED_OUTPUT_BITS = {bits}"

/-- Manual renderer for `PlanCompileCause`, mirroring `Eval.Plan.AdapterTest`'s identical helper:
    the type has no `Repr`/`ToString` of its own (nested `ShapeError` has neither), so a
    diagnosable message dispatches per-constructor. -/
def renderCompileCause : PlanCompileCause → String
  | .inputSignature c => s!"inputSignature: {repr c}"
  | .capability c     => s!"capability: {repr c}"
  | .shape c          => s!"shape: {c}"
  | .invalidPlan c    => s!"invalidPlan: {repr c}"

end LeanNCD.Eval.Plan.JaxSmoke

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.Eval.Plan.JaxSmoke Std

def main (args : List String) : IO Unit := do
  let outputPath := args.head?.getD "generated_evalplan_smoke.py"
  -- Compile + prepare the affine fixture.
  let sched ← match affineProg.compileToScheduled.run 0 with
    | .ok sched _ => pure sched
    | .error e _  => throw (IO.userError s!"affineProg compile failed: {repr e}")
  let prepared ← match prepareEvalPlan sched (InputSignature.ofDenseInputs affineInputs) with
    | .ok p => pure p
    | .error f => throw (IO.userError s!"affineProg prepare failed: {renderCompileCause f.cause}")
  -- Run Dense and require the known-good result.
  let report ← match runPreparedDense prepared affineInputs with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"affineProg Dense run failed: {repr e.cause}")
  let yTensor ← match report.env["Y"]? with
    | some t => pure t
    | none => throw (IO.userError "affineProg Dense run produced no 'Y' tensor")
  unless yTensor.shape == [2] && yTensor.data == #[11.0, 16.0] do
    throw (IO.userError s!"affineProg Dense Y mismatch: shape={yTensor.shape} data={yTensor.data}")
  -- Generate the Python module from the checked, prepared plan only.
  let forwardSrc ← match generateForward prepared with
    | .ok src => pure src
    | .error e => throw (IO.userError s!"affineProg codegen failed: {repr e}")
  let inputConsts ← match
      renderInputConstants prepared.plan.raw prepared.bindings.requiredInputs affineInputs with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"input-constant rendering failed: {repr e}")
  let outputConsts := renderExpectedOutputConstants "Y" yTensor
  let moduleSrc := String.intercalate "\n\n"
    ["import jax.numpy as jnp", inputConsts, outputConsts, forwardSrc]
  IO.FS.writeFile outputPath (moduleSrc ++ "\n")
  IO.println s!"Generated {outputPath}"
  -- Confirm the shifted-affine fixture is rejected by codegen BEFORE any Python is emitted for it.
  let shiftedSched ← match shiftedProg.compileToScheduled.run 0 with
    | .ok sched _ => pure sched
    | .error e _  => throw (IO.userError s!"shiftedProg compile failed: {repr e}")
  let shiftedInputs : HashMap String DenseTensor := HashMap.ofList [("A", ⟨[3], #[1.0, 2.0, 3.0]⟩)]
  let shiftedPrepared ← match prepareEvalPlan shiftedSched (InputSignature.ofDenseInputs shiftedInputs) with
    | .ok p => pure p
    | .error f =>
        throw (IO.userError s!"shiftedProg prepare failed: {renderCompileCause f.cause}")
  match generateForward shiftedPrepared with
  | .ok _ => throw (IO.userError "shiftedProg codegen unexpectedly succeeded: expected a nonzeroAffineBias rejection")
  | .error (.nonzeroAffineBias ni ti fi ri biasVal) =>
      IO.println
        s!"shiftedProg correctly rejected: nonzeroAffineBias node={ni} term={ti} factor={fi} \
row={ri} bias={biasVal}"
  | .error other =>
      throw (IO.userError s!"shiftedProg codegen failed with the wrong error: {repr other}")

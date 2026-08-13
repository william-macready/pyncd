import LeanNCD.Eval.Entry
import LeanNCD.DSL.Compile
import EvalPlanCodegen
import Eval.PropertyOracle.Gen

/-!
# Full Wave C affine JAX corpus driver

Generates one Python data record for every `PropertyOracle.enumPrograms` entry. Every record crosses
the real source boundary (`compileToScheduled → prepareEvalPlan → runPreparedDense`) and contains
only required input bits, checker-produced affine-reference data, every materialized Dense output,
and a structural feature mask. This executable is deliberately outside every Lake target.
-/

namespace JaxBridge.AffineCorpus

open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan LeanNCD.PropertyOracle Std
open JaxBridge

def expectedCount : Nat := 3832

def featureNames : Array String :=
  #[ "nonzero_bias"
   , "nonunit_or_multiaxis_coeff"
   , "negative_invalid"
   , "zero_coeff_row"
   , "multiple_factors"
   , "multiple_terms"
   , "reduction_domain"
   , "multiple_graph_nodes"
   , "internal_read"
   , "zero_extents"
   , "empty_factors"
   , "empty_terms" ]

private def bit (n : Nat) (present : Bool) : Nat := if present then 2 ^ n else 0

private def rows (plan : PreparedPlan) : Array (Array Int) :=
  plan.plan.checkedNodes.flatMap fun c =>
    c.plan.terms.flatMap fun t => t.factors.flatMap fun f => f.map.coeffs

private def factors (plan : PreparedPlan) : Array (TermPlan × ReadPlan) :=
  plan.plan.checkedNodes.flatMap fun c =>
    c.plan.terms.flatMap fun t => t.factors.map fun f => (t, f)

private def isUnitProjection (row : Array Int) : Bool :=
  row.toList.filter (· != 0) == [1]

private def hasNegativeInvalid (plan : PreparedPlan) : Bool :=
  (factors plan).any fun (t, f) =>
    (allCoords t.iterationShape.toList).any fun coord =>
      (applyAffine f.map coord).any (· < 0)

/-- Structural features are read from the checked plan, not inferred from output values or names. -/
def featureMask (plan : PreparedPlan) : Nat :=
  let nodes := plan.plan.checkedNodes
  let allTerms := nodes.flatMap fun c => c.plan.terms
  let allFactors := factors plan
  let allRows := rows plan
  let inputSlots := plan.plan.raw.inputSlots
  bit 0 (allFactors.any fun (_, f) => f.map.bias.any (· != 0)) +
  bit 1 (allRows.any fun row => !isUnitProjection row) +
  bit 2 (hasNegativeInvalid plan) +
  bit 3 (allRows.any fun row => row.all (· == 0)) +
  bit 4 (allTerms.any fun t => t.factors.size > 1) +
  bit 5 (nodes.any fun c => c.plan.terms.size > 1) +
  bit 6 (allTerms.any fun t => !t.reductionPos.isEmpty) +
  bit 7 (nodes.size > 1) +
  bit 8 (allFactors.any fun (_, f) => !inputSlots.contains f.sourceSlot) +
  bit 9 (plan.plan.raw.tensorSigs.any fun s => s.shape.any (· == 0)) +
  bit 10 (allTerms.any fun t => t.factors.isEmpty) +
  bit 11 (nodes.any fun c => c.plan.terms.isEmpty)

private def renderInputs (plan : PreparedPlan) (env : HashMap String DenseTensor) : IO String := do
  let mut entries : Array String := #[]
  for b in plan.bindings.requiredInputs.bindings do
    let t ← match env[b.name]? with
      | some t => pure t
      | none => throw (IO.userError s!"required input {b.name} is absent")
    entries := entries.push (pyStrLit b.name ++ ": " ++ pyTensorEntry t)
  pure ("{" ++ String.intercalate ", " entries.toList ++ "}")

private def renderExpected (plan : PreparedPlan) (report : EvalReport) : IO String := do
  let mut entries : Array String := #[]
  for b in plan.bindings.materializedNames do
    let t ← match report.env[b.name]? with
      | some t => pure t
      | none => throw (IO.userError s!"materialized output {b.name} is absent")
    entries := entries.push ("(" ++ pyStrLit b.name ++ ", " ++ pyTensorEntry t ++ ")")
  pure ("[" ++ String.intercalate ", " entries.toList ++ "]")

private def buildCase (index : Nat) (p : TLProgram) (env : HashMap String DenseTensor) :
    IO String := do
  let sched ← match p.compileToScheduled.run 0 with
    | .ok s _ => pure s
    | .error e _ => throw (IO.userError s!"case {index} compile failed: {repr e}")
  let prepared ← match prepareEvalPlan sched (InputSignature.ofDenseInputs env) with
    | .ok p => pure p
    | .error e =>
        throw (IO.userError s!"case {index} prepare failed: {renderCompileCause e.cause}")
  let report ← match runPreparedDense prepared env with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"case {index} Dense run failed: {repr e.cause}")
  let staticPlan ← match generateNamed .affineReference prepared with
    | .ok src => pure src
    | .error e => throw (IO.userError s!"case {index} affine codegen failed: {repr e}")
  let inputSrc ← renderInputs prepared env
  let expectedSrc ← renderExpected prepared report
  pure ("{\"index\": " ++ toString index ++
    ", \"feature_mask\": " ++ toString (featureMask prepared) ++
    ", \"plan\": " ++ staticPlan ++
    ", \"inputs\": " ++ inputSrc ++
    ", \"expected\": " ++ expectedSrc ++ "}")

private def renderFeatureBits : String :=
  "{" ++ String.intercalate ", "
    (featureNames.toList.mapIdx fun i name => pyStrLit name ++ ": " ++ toString (2 ^ i)) ++ "}"

end JaxBridge.AffineCorpus

open LeanNCD.PropertyOracle
open JaxBridge.AffineCorpus

def main (args : List String) : IO Unit := do
  let outputPath := args.head?.getD "generated_evalplan_affine_corpus.py"
  let skipLast := (← IO.getEnv "JAX_CORPUS_SKIP_LAST") == some "1"
  let source := if skipLast then enumPrograms.dropLast else enumPrograms
  unless source.length == expectedCount do
    throw (IO.userError s!"expected exactly {expectedCount} source cases, got {source.length}")
  let mut rendered : Array String := #[]
  for (index, p, env) in source.zipIdx.map fun (pe, i) => (i, pe.1, pe.2) do
    rendered := rendered.push (← buildCase index p env)
  let moduleSrc :=
    "# Generated by EvalPlanAffineCorpus.lean — do not edit.\n" ++
    "SOURCE_CASE_COUNT = " ++ toString source.length ++ "\n" ++
    "FEATURE_BITS = " ++ renderFeatureBits ++ "\n" ++
    "CASES = [\n" ++ String.intercalate ",\n" rendered.toList ++ "\n]\n"
  IO.FS.writeFile outputPath moduleSrc
  IO.println s!"Generated {outputPath} with {rendered.size} cases"

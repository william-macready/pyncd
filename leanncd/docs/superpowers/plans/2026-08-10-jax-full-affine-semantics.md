# Full Wave C affine semantics in the experimental JAX evaluator

**Status:** draft, 2026-08-10

## Purpose

Extend the completed checked-`EvalPlan` JAX smoke experiment from one projection-only
`jnp.einsum` example to an empirical JAX reference interpretation of every affine read admitted by
Wave C:

- arbitrary integer-affine coefficients and biases;
- positive and negative shifts;
- scales and multi-axis affine expressions;
- constant/zero-coefficient rows;
- per-dimension out-of-bounds detection with zero padding;
- multiple factors and terms with their declared fold order;
- per-term reduction domains;
- chained checked graph nodes and complete materialized outputs; and
- zero-sized output/reduction domains plus the checked kernel's empty-factor/empty-term boundaries.

The completed smoke path remains intact:

```text
CheckedEvalPlan -> projection recognizer -> generated jnp.einsum
```

This slice adds a distinct correctness-oriented path:

```text
CheckedEvalPlan
  -> Lean-precomputed affine lookup tables
  -> generated static plan data
  -> ordered JAX reference runtime
  -> eager/JIT output compared bit-for-bit with Dense
```

The distinction is load-bearing. `jnp.einsum` is an optimization-shaped lowering whose reduction
order is controlled by XLA, not a general implementation of Dense's source-declared
`reference64` folds. The new affine path therefore does not call `einsum`, `jnp.sum`, or another
tree reduction. It materializes factor tensors from exact lookup tables and uses sequential
`jax.lax.fori_loop` carries for factor, reduction-coordinate, and term folds.

## Exit criterion

The slice is complete only when:

1. the existing `run-evalplan.sh` einsum smoke still passes unchanged at the behavior boundary;
2. every one of the 3,832 current `PropertyOracle.enumPrograms` entries compiles, prepares,
   generates, and agrees bit-for-bit with `runPreparedDense` under eager JAX;
3. deterministic representatives covering every declared affine/runtime feature agree under
   `jax.jit`;
4. the hand fixtures below cover semantics absent from the generated corpus;
5. the existing checked-kernel empty/zero/fold-order fixtures agree through the positional JAX
   entry point;
6. coefficient, zero-padding, reduction-order, term-scoping, and corpus-count mutations each fail
   for their named reason;
7. the upstream `NetSpec` smoke and full Lean build remain green; and
8. a final whole-branch review finds no silent semantic fallback or overstated claim.

This is still an experiment. Passing these gates is empirical backend agreement over the declared
corpus and mutation fixtures, not a proof that XLA preserves every IEEE-754 corner case on every
platform.

## Fixed design decisions

### Two explicit lowerings, not a hybrid with ambiguous semantics

- **`einsumOnly`** preserves the completed smoke generator and its typed rejections. It remains the
  evidence that a checked Tensor Logic contraction can produce a real `jnp.einsum` call.
- **`affineReference`** accepts every current Wave C `CheckedEvalPlan`. It is the only path used for
  full affine and corpus parity claims.
- A term never silently falls from one path to the other. The caller chooses the mode.
- The full-affine runner may compare both modes on the original affine-bias fixture, but never uses
  the einsum result as the reference oracle.

### Precompute affine addresses in Lean

All iteration shapes and affine maps are static after `prepareEvalPlan`. For each factor, Lean
enumerates the term's complete iteration basis in Dense row-major order and computes:

- `some flatIndex` only when **every source dimension** is in range; or
- `none` when any source coordinate is negative or at least its dimension extent.

The emitted representation separates this into:

- a safe in-range index table (using `0` as an ignored placeholder for invalid entries); and
- an equally-shaped validity mask.

The JAX runtime gathers only through safe indices and applies `jnp.where(mask, gathered, 0.0)`.
It must not rely on JAX's out-of-bounds gather behavior, which may clamp rather than zero-pad.
When source storage is empty, it emits an all-zero factor tensor without attempting any gather.

Computing coordinates in Lean uses arbitrary-precision `Int`, so this corpus-scale prototype does
not introduce fixed-width overflow while evaluating affine expressions. The emitted lookup table
is intentionally proportional to the static iteration-space size. This is not claimed to be a
scalable large-model representation; replacing tables with runtime affine arithmetic would need a
separate overflow and performance design.

### Preserve Dense's nested fold structure

For each term:

1. gather one full iteration-space tensor per factor;
2. stack those homogeneous tensors and fold multiplication from `1.0` with
   `jax.lax.fori_loop` in factor-array order; an empty factor array yields ones;
3. transpose the product tensor into `outputPos ++ reductionPos` order;
4. reshape it to `(outputSize, reductionSize)`;
5. `vmap` a `jax.lax.fori_loop` that folds each row from `0.0` in row-major reduction-coordinate
   order; a zero reduction extent yields zeros; and
6. reshape the result to the assignment output shape.

Term result tensors are homogeneous by `checkAssign`. Stack them and fold addition from `0.0` with
`jax.lax.fori_loop` in term-array order. An empty term array yields an all-zero output. Checked
nodes execute in graph order and write their positional destination slots before later nodes read
them.

Using stacks makes the factor and term loop bodies homogeneous; the differing factor gathers and
term reductions are computed before those ordered folds. This avoids an infeasible loop over
heterogeneous Python bodies while retaining an explicit carried dependency between arithmetic
steps.

### Share only genuine coordinate primitives with Dense

Move these existing private definitions, without changing their equations, from `Dense.lean` into
`LeanNCD.Eval.Plan.Coordinates`:

- row-major coordinate enumeration;
- affine-map application;
- row-major flattening; and
- per-dimension bounds checking.

Dense must use the shared primitives after the extraction. The experiment-specific
`Option flatIndex` table builder remains in the experimental module; it composes the shared
primitives but is not presented as production Dense API.

This production refactor is a separate task and rollback unit because it touches the trusted Dense
worker. The full existing Wave C differential suite must establish behavior preservation before
experimental code consumes the helpers.

### Keep the experiment importable but non-default

Split reusable code generation out of the executable driver into
`experiments/jax_bridge/EvalPlanCodegen.lean`. Add a non-default `JaxExperiment` Lean library with
`srcDir = "experiments/jax_bridge"` that builds this module only when explicitly requested.

Do not:

- add JAX as a Lean dependency;
- include `JaxExperiment` in `defaultTargets`;
- move experimental code under the public `LeanNCD` namespace tree;
- add a stable wire format; or
- make production modules import the experiment.

The corpus driver may import modules from the `Tests` library after the runner builds that target.
The reusable experimental codegen module itself may import only production `LeanNCD` modules.

### F1 compatibility

This plan is authored against local `main` at `b513c15`, before Wave F F1 lands there. Before
execution, sync to the latest local `main`, run `lake build LeanNCD` to replace any donor-branch
project oleans, and inspect the F1 diff.

If F1's `contextShape`/`contextPos` fields are present:

- `affineReference` still accepts only a complete `CheckedEvalPlan`;
- top-level checked nodes must have empty context, as established by `checkPlan`;
- the emitted iteration basis excludes no field silently—assert the checked empty-context
  condition at codegen or consume the corresponding checked accessor; and
- contextual `CheckedAssignPlan` execution remains outside this slice.

Do not duplicate or revert F1's coordinate-placement logic.

## Exact evidence matrix

### Generated corpus

`Eval.PropertyOracle.Gen.enumPrograms` currently contains exactly 3,832 source programs:

- every program is accepted by Wave C;
- inputs use small exact values over axes of extent 2;
- affine choices cover identity, `+1`, and scale-by-2 reads;
- cases include one- and two-statement graphs, producer-to-consumer dependencies, multiple factors,
  multiple terms, genuine contractions, and multi-term contractions.

The corpus is strong coverage for graph and combinatorial structure but cannot detect floating
fold reassociation: all of its arithmetic is exactly representable. Fold-order claims therefore
belong to the hand fixtures below, not to the 3,832-case count.

### Verified source fixtures

The following assembled Lean block compiled through the repository's `slice-plan` checker, and its
`#eval` outputs were observed from the real source evaluator:

```lean
import LeanNCD.Eval.Entry

namespace LeanNCD.Eval.Plan.JaxAffineFixtures

open LeanNCD LeanNCD.Eval Std

def shiftProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[i + 1]
}

def shiftInputs : HashMap String DenseTensor :=
  HashMap.ofList [("A", ⟨[3], #[1.0, 2.0, 3.0]⟩)]

def scaleProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[2 * i]
}

def scaleInputs : HashMap String DenseTensor :=
  HashMap.ofList [("A", ⟨[3], #[1.0, 2.0, 3.0]⟩)]

def lookbackProg : TLProgram := tlprog!{
  axis i : ℕ = 3
  Y[i] := A[i - 1]
}

def lookbackInputs : HashMap String DenseTensor :=
  HashMap.ofList [("A", ⟨[3], #[1.0, 2.0, 3.0]⟩)]

def multiAxisProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 2
  Y[i, j] := X[2 * i + j]
}

def multiAxisInputs : HashMap String DenseTensor :=
  HashMap.ofList [("X", ⟨[4], #[1.0, 2.0, 3.0, 4.0]⟩)]

def termScopeProg : TLProgram := tlprog!{
  axis i : ℕ = 1
  axis j : ℕ = 2
  Y[i] := A[i] + P[i, j]
}

def termScopeInputs : HashMap String DenseTensor :=
  HashMap.ofList
    [ ("A", ⟨[1], #[10.0]⟩)
    , ("P", ⟨[1, 2], #[1.0, 2.0]⟩) ]

def zeroCoeffRowProg : TLProgram := tlprog!{
  axis i : ℕ = 1
  axis j : ℕ = 3
  Y[i] := A[i] · B[0 * j]
}

def zeroCoeffRowInputs : HashMap String DenseTensor :=
  HashMap.ofList
    [ ("A", ⟨[1], #[2.0]⟩)
    , ("B", ⟨[1], #[5.0]⟩) ]

def reductionOrderProg : TLProgram := tlprog!{
  axis i : ℕ = 1
  axis j : ℕ = 3
  Y[i] := P[i, j]
}

def reductionOrderInputs : HashMap String DenseTensor :=
  HashMap.ofList [("P", ⟨[1, 3], #[1e16, 1.0, 1.0]⟩)]

def zeroOutputProg : TLProgram := tlprog!{
  axis i : ℕ = 0
  Y[i] := A[i]
}

def zeroOutputInputs : HashMap String DenseTensor :=
  HashMap.ofList [("A", ⟨[0], #[]⟩)]

def zeroReductionProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 0
  Y[i] := A[i] · B[j]
}

def zeroReductionInputs : HashMap String DenseTensor :=
  HashMap.ofList
    [ ("A", ⟨[2], #[7.0, 8.0]⟩)
    , ("B", ⟨[0], #[]⟩) ]

def outputOf (p : TLProgram) (inputs : HashMap String DenseTensor) : Option DenseTensor :=
  (TLProgram.eval p inputs).toOption.bind (·.env["Y"]?)

#eval outputOf shiftProg shiftInputs
#eval outputOf scaleProg scaleInputs
#eval outputOf lookbackProg lookbackInputs
#eval outputOf multiAxisProg multiAxisInputs
#eval outputOf termScopeProg termScopeInputs
#eval outputOf zeroCoeffRowProg zeroCoeffRowInputs
#eval outputOf reductionOrderProg reductionOrderInputs
#eval outputOf zeroOutputProg zeroOutputInputs
#eval outputOf zeroReductionProg zeroReductionInputs

end LeanNCD.Eval.Plan.JaxAffineFixtures
```

Observed outputs, in order:

| Fixture | Shape | Data |
|---|---:|---|
| shift `A[i+1]` | `[3]` | `[2, 3, 0]` |
| scale `A[2*i]` | `[3]` | `[1, 3, 0]` |
| look-back `A[i-1]` | `[3]` | `[0, 1, 2]` |
| multi-axis `X[2*i+j]` | `[2,2]` | `[1, 2, 3, 4]` |
| per-term scope `A[i] + P[i,j]` | `[1]` | `[13]` |
| zero coefficient `A[i] * B[0*j]` | `[1]` | `[30]` |
| reduction order `[1e16,1,1]` | `[1]` | `[1e16]` (`0x4341c37937e08000`) |
| zero output extent | `[0]` | `[]` |
| zero reduction extent | `[2]` | `[0, 0]` |

Reversing the reduction-order fixture produces `1.0000000000000002e16`
(`0x4341c37937e08001`) under both eager and JIT JAX. This is the required mutation-sensitive
evidence for the sequential reduction carry.

### Checked-kernel boundary fixtures

The corpus driver must also reuse these existing public definitions from
`Eval.Plan.KernelDenseTest` and compare the affine JAX single-assignment result with both the
existing hand-verified expected value and `runDenseAssign`:

| Existing fixture | Behavior pinned |
|---|---|
| `ptcPlan` | per-term contraction scope: `[53, 116]` |
| `efpPlan` | empty factor product yields ones |
| `etaPlan` | empty term array yields zeros |
| `zerdPlan` | zero reduction extent yields zeros |
| `zoePlan` | zero output extent yields empty storage |
| `fosPlan` | term fold order yields `0.0`, not reassociated `1.0` |

Add one local checked-assignment fixture for a genuinely permuted iteration basis, because source
compilation always places outputs before reductions and would otherwise leave the runtime's
transpose untested:

- source signature `[2,3]`, destination signature `[2]`;
- `iterationShape = #[3,2]`, `outputPos = #[1]`, `reductionPos = #[0]`;
- source-map rows `#[0,1]` and `#[1,0]`;
- source data `#[1,2,3,4,5,6]`; and
- verified `runDenseAssign` output `#[6,15]`.

This exact fixture was compiled and executed while authoring the plan.

Add two further checked-assignment boundaries:

- a three-factor Float-sensitive pair using exact finite, normal binary64 inputs. Dense and eager/JIT
  JAX produce `0x52ace21080787dc7` in declared `[a,b,c]` order and
  `0x52ace21080787dc6` after the `[b,c,a]` mutation; and
- a nonempty `[2]` output reading a `[0]` source through two all-false lookup masks. This reaches the
  empty-storage no-gather guard rather than short-circuiting on a zero output/reduction extent.

Add one complete positional checked graph with input slots `#[0,4]` and three dependent nodes:
slot 4 is copied to slot 1, slot 1 to slot 2, then slots 2 and 0 are added into slot 3. Compare all
five store slots under eager and JIT to pin input placement, checked graph order, and final bits.

The experimental codegen therefore needs three boundary entry points:

- named `PreparedPlan` generation for source/corpus cases; and
- positional `CheckedEvalPlan` generation for complete graph cases; and
- positional `CheckedAssignPlan` generation for the hand-constructed checked-kernel cases above.

The checked-assignment entry does not invent source names or wrap the fixture in a synthetic graph.
Its Python call accepts the positional store and returns one result tensor, directly paralleling
`runDenseAssign`. If F1 has landed, it explicitly rejects or separately routes a nonempty assignment
context; this slice invokes it only at empty context.

## Task 1: Extract shared coordinate primitives without changing Dense

Add:

- `LeanNCD/Eval/Plan/Coordinates.lean`; and
- `test/Eval/Plan/CoordinatesTest.lean`.

Update:

- `LeanNCD/Eval/Plan/Dense.lean`;
- `lakefile.toml`; and
- the Plan subtree table in `LeanNCD/Eval/AGENTS.md`.

Move the exact current equations for row-major coordinate enumeration, affine application, and
row-major flattening into `Coordinates.lean`. Add a named per-dimension bounds predicate and make
`Dense.gatherFactor` call it before flattening, preserving its current behavior. Do not add JAX,
lookup-table, source-name, or codegen concepts to this production module.

Tests must cover:

- scalar, rank-1, and rank-2 row-major coordinate order;
- zero extents producing no coordinates;
- positive, negative, scaled, zero-coefficient, and multi-axis affine rows;
- per-dimension invalid coordinates that would alias a valid flattened address if flattened first;
  and
- valid row-major flat indices.

Run the targeted Plan coordinate/kernel/differential tests together, then the full build. Mutation
check: replace per-dimension validity with flattened-offset validity and confirm the alias fixture
fails; restore and rerun.

**Gate:** the full build remains at 8,640 jobs plus the newly registered coordinate test module,
all 3,832 existing Dense differential cases remain bit-identical, and the diff contains no
experimental import in production code.

Commit this task separately. It changes an existing trusted worker and can be rejected or reverted
without affecting the later experimental design.

## Task 2: Add the table-driven affine JAX reference path

Refactor/add:

- `experiments/jax_bridge/EvalPlanCodegen.lean`;
- `experiments/jax_bridge/EvalPlanSmoke.lean`;
- `experiments/jax_bridge/evalplan_affine_runtime.py`;
- `experiments/jax_bridge/EvalPlanAffineSmoke.lean`;
- `experiments/jax_bridge/evalplan_affine_smoke.py`;
- `experiments/jax_bridge/run-evalplan-affine.sh`; and
- a non-default `JaxExperiment` stanza in `lakefile.toml`.

The shared Lean codegen module owns:

- existing Python quoting, binding, shape, and expected-bit rendering;
- existing `einsumOnly` projection recognition and diagnostics;
- affine lookup-table construction from the shared coordinate primitives;
- named and positional generated-plan representations; and
- explicit mode selection.

The committed Python runtime owns only execution of the emitted static plan data. It must:

- enable/require x64 at its caller boundary;
- use safe index plus mask tables for zero padding;
- never gather from an empty source tensor;
- preserve factor, reduction, and term order as specified above;
- handle empty factor/term arrays and zero output/reduction extents;
- execute positional graph nodes in checked order; and
- remain differentiable with respect to floating input tensors.

The affine smoke driver includes the nine verified source fixtures, six reused checked-kernel
fixtures, four local checked assignments (permuted basis, declared/reordered factor order, and empty
source), and the local positional graph from the evidence matrix. It emits Dense result bits for
every materialized output, positional result, or graph-store slot under comparison. The Python
verifier runs eager and JIT for every hand fixture and checks:

- exact dtype, shape, and `UInt64` bits;
- `grad(sum(Y), A) == [0, 1, 1]` for the shift fixture;
- `grad(sum(Y), A) == [1, 0, 1]` for the scale fixture; and
- the reduction-, term-, and factor-order low-bit distinctions.

The verifier also starts a fresh process with x64 disabled, imports the runtime, then enables x64
and executes eager/JIT. This directly proves runtime import cannot cache a float32 zero before the
caller boundary enables reference64 execution.

Keep `run-evalplan.sh` green and preserve its AST assertion that the original fast-path module
contains `jnp.einsum("ab,b->a", ...)`.

Named mutations:

1. force an invalid lookup-table mask entry true; shift/look-back zero padding must fail;
2. change one precomputed scale/shift index; the corresponding affine fixture must fail;
3. reverse reduction iteration; `reductionOrderProg` must change from
   `0x4341c37937e08000` to `0x4341c37937e08001`;
4. combine terms over one shared reduction domain; `termScopeProg` must change from `13` to `23`;
5. reorder the `fosPlan` term stack from `[0, 1, 2]` to `[0, 2, 1]`; its result must change from
   `0.0` to `1.0`; and
6. disable x64; the dtype gate must fail before bit comparison;
7. reorder the three factor tables from `[a,b,c]` to `[b,c,a]`; the result must change from
   `0x52ace21080787dc7` to `0x52ace21080787dc6`; and
8. remove the empty-source storage guard; the nonempty-output `emptySourceGuard` fixture must fail
   by attempting to gather index zero from empty storage.

Restore after each mutation and rerun the complete affine smoke.

**Gate:** every hand source and checked-kernel case passes under eager and JIT JAX; every named
mutation fails for its intended assertion; the original einsum smoke is unchanged behaviorally;
and `JaxExperiment` remains outside `defaultTargets`.

Commit the codegen/runtime/curated smoke as one task. The Lean tables and Python runtime are one
semantic unit: neither has an independently meaningful success condition without the other.

## Task 3: Run the full Wave C corpus and publish measured coverage

Add:

- `experiments/jax_bridge/EvalPlanAffineCorpus.lean`;
- `experiments/jax_bridge/evalplan_affine_corpus.py`; and
- `experiments/jax_bridge/run-evalplan-affine-corpus.sh`.

Update:

- `experiments/jax_bridge/README.md`;
- `leanncd/AGENTS.md`;
- `LeanNCD/Eval/AGENTS.md`; and
- this plan with a completion record containing measured counts and timings.

The Lean corpus driver imports `Eval.PropertyOracle.Gen` from `Tests`, builds each case through the
real `compileToScheduled -> prepareEvalPlan -> runPreparedDense` pipeline, and emits:

- required named input shapes and bit payloads;
- the affine-reference static plan;
- every materialized output name, shape, and Dense bit payload;
- a structural feature mask; and
- a stable case index.

Abort generation on the first compile, prepare, Dense, or codegen failure. Assert the source count
is exactly 3,832 before writing the module.

The Python corpus verifier:

- reconstructs inputs and expected outputs from bits;
- evaluates all 3,832 cases eagerly through the JAX runtime;
- compares **every** materialized output, not only the last output;
- requires zero mismatches and exactly 3,832 executed cases;
- selects the first case for every distinct feature mask and JIT-checks those representatives;
- JIT-checks every curated hand fixture from Task 2;
- reports source-case count, eager mismatch count, distinct feature-mask count, JIT case count,
  generated artifact size, generation time, eager time, and JIT time; and
- fails if any expected feature bit has no eager or JIT representative.

Feature bits must distinguish at least:

- nonzero bias;
- non-unit or multi-axis coefficient rows;
- a table entry invalid from a negative coordinate;
- a zero-coefficient row;
- multiple factors;
- multiple terms;
- a reduction domain;
- multiple graph nodes;
- an internal producer-to-consumer read;
- zero extents;
- empty factors; and
- empty terms.

The generated corpus supplies the features it actually contains; curated/manual cases supply the
rest. Documentation must attribute each feature to the correct source rather than implying all
3,832 generated cases cover it.

Corpus mutations:

- skip the last source case and confirm the exact-count assertion fails; and
- compare only the last materialized output and confirm a deliberately corrupted earlier output in
  a two-output case is detected by the complete-output assertion but missed by the mutation.

Final validation:

```bash
cd leanncd/experiments/jax_bridge
./setup-python.sh
./run-evalplan.sh
./run-evalplan-affine.sh
./run-evalplan-affine-corpus.sh
./run.sh

cd ../..
"$HOME/.elan/bin/lake" build
```

**Gate:** exact measured counts are recorded only after the real run; both corpus mutations have
teeth; all four experiment runners and the complete Lean build pass; and documentation continues
to distinguish upstream `NetSpec`, einsum-only, affine-reference, and future scan lowering.

Task 3 is separate because corpus scalability and evidence attribution can be rejected while the
curated affine interpreter from Task 2 remains valid.

## Whole-branch review gate

Review the complete branch after Task 3. The reviewer must confirm:

1. per-dimension bounds are checked before flattening;
2. invalid entries cannot reach a clamping JAX gather;
3. empty source storage never performs index zero access;
4. factor, reduction, and term folds retain explicit carried order;
5. affine-reference codegen is total over current checked Wave C plans;
6. source and positional boundaries compare every required result;
7. the 3,832 count and feature attribution come from the executed corpus;
8. F1 fields, if present, are handled explicitly rather than ignored;
9. no experiment enters the default build or production dependency direction; and
10. claims remain empirical and platform-scoped.

## Explicit non-goals

This slice does not add:

- F1 contextual assignment execution;
- checked plan blocks, scans, or `lax.scan`;
- nonlinearities, predicates, masks, max/min, scatter, or affine LHS writes;
- dtypes beyond the checked `f64`/`reference64` mode;
- dynamic shapes;
- a stable plan codec or fingerprint;
- runtime affine arithmetic suitable for large tensors;
- a proof of backend interpretation agreement;
- parameter initialization, optimizers, or training; or
- promotion of the experiment into a public production backend.

After completion, any performance-oriented lowering—runtime affine arithmetic, compact gather
representations, generalized einsum recognition, or scan specialization—must establish agreement
against this ordered affine reference path rather than replacing its semantics by assumption.

# Tensor Logic Semantic Core: Bounded Feasibility Spike

**Executed 2026-10-06.** See the
[results record](tensor_logic_semantic_core_spike_record.md) for proved scope,
observed values, validation, and decisions deliberately left open.

## Scope and process

Full path, bounded to a new proof surface rather than a production capability.
The spike will test the recommendation in the
[semantic gap audit](tensor_logic_semantic_gap_audit.md): a reusable,
carrier-parametric expression/readiness foundation with an actual connection
to the existing index formalism.

The existing isolated session worktree is reused so the user's boundary-policy
and audit edits remain together. `prepare-worktree.sh` warmed its dependencies,
and `lake-build.sh ... LeanNCD` refreshed project imports against its sources.
Baseline: `3bdd7f9c9baa98e541b6951223d0bc89c610a23b`.

## Required outcome

1. A compiling, off-production-path Lean prototype for reads, scalar
   combination, finite reduction with bound coordinates, and a partial primitive.
2. Read stability, including undefinedness, proved without `sorry` or an
   assumed version of the conclusion.
3. Ready evaluation that distinguishes missing values from primitive failure.
4. Shared definitions usable with an exact carrier and native `Float`/`Float32`,
   without requiring floating-point semiring laws.
5. An actual bridge to an existing formal `StMat` or another existing
   categorical index interface, with coordinate behavior proved and bounds
   obligations visible.
6. A results record separating demonstrated feasibility from decisions not
   settled, and identifying unchanged reuse versus analogous new machinery.

## Non-goals

No production expression API, full language implementation, additive collector,
model checker, interpreter replacement, JAX emitter, complex machine execution,
general mixed-dtype graph, or full D-graded algebra instance. No relaxation of
existing backend guards. Exact complex values may be a fixture instance, but
must not be presented as `complex64` support.

A scalar-only fragment does not establish full scalar/array typing,
capture-avoiding substitution, or arbitrary primitive signatures. Record these
limits explicitly rather than infer them from read stability.

## Work items

### S1. Prototype and prove

Artifact: `leanncd/spikes/TensorLogicSemanticCoreSpike.lean`.
Keep the prototype separate from `import LeanNCD`.

Before choosing new representations, inspect these existing interfaces in
bounded windows:

- `UID`, `UnaryOp`, `idxAffineForm` @ `leanncd/LeanNCD/DSL/Ast.lean`.
- `ConstL`, `traverseAxes` @ `leanncd/LeanNCD/DSL/TraverseAxes.lean`.
- `UnaryOp.applyChecked`, `UnaryOp.applyChecked32` @
  `leanncd/LeanNCD/Eval/Error.lean`.
- `idxToRow` @ `leanncd/LeanNCD/DSL/Pipeline/Lowering.lean`.
- `StMat`, `StMat.comp` @ `leanncd/LeanNCD/Base/St.lean`.
- `realizeStMat`, `intToCoeff` @ `leanncd/LeanNCD/Bridge/Realize.lean`.

Expose carrier operations as data and state only the laws a theorem needs.
Use existing index/error vocabulary where it fits. Do not force an existing
Float-specific operation into an exact-carrier interpretation.
Preserve native binary32 operations rather than widen/narrow.

The bridge must involve the actual existing representation, not an unrelated
affine record labelled categorical. A raw signed affine map need not preserve
finite coordinate bounds; successful bounded lookup needs separate evidence.
An example bridge is not a full functor/actegory construction.

### S2. Check, challenge, and record

Artifacts:

- A non-default Lake target for the prototype, without changing default targets.
- A narrow ignore exception making the off-target prototype persistent.
- `papers/semantics/tensor_logic_semantic_core_spike_record.md`.

Use existing Lake wrappers. Compile the source itself and via
`check-snippet.sh`; the plan deliberately embeds no unverified Lean blocks.

Acceptance cases:

- Defined reads/combination and a nonempty reduction.
- Empty reduction with an undefined body, distinguished from primitive
  application outside that reduction.
- Undefined primitive under a zero-valued factor/combination where applicable.
- Missing required store entry, versus an undefined ready primitive.
- Unrelated store entries may differ without affecting a ready result.
- Native binary32/binary64 evaluation through the same definitions, including
  a value that distinguishes rounding behavior if arithmetic is demonstrated.
- Exact carrier evaluation; exact complex evaluation if practical.
- Existing affine/formal index bridge with nontrivial signed coefficients/bias.

Fixture precedents: empty and local fold behavior from
`test/Eval/Plan/KernelDenseTest.lean`; native-carrier/domain conventions from
`test/Eval/Plan/KernelDense32Test.lean` and `Eval/Error.lean`. Scoped read stability
and partial-store readiness are new specification fixtures, not purported
clones of a theorem that the audit did not locate.

Challenge the new soundness surface with two unique textual mutations:
omit a read from the footprint, and break empty-reduction behavior.
Run each through the existing mutation-cycle wrapper against the non-default
target. Observe the intended failure and restored pass; record the commands
and results. The spike does not move a production capability boundary and
therefore does not need per-task production patches or a production regression
manifest. This is a deliberate scaling of the Full process to an experiment.

## Review and completion

One bounded prototype dispatch, followed by write-up from compiled artifacts.
Keep dispatches below 60 turns and approximately 250k peak context. Independent
final review lenses: proof/semantic scope, and reuse/carrier/categorical
compatibility. Findings must be fixed or explicitly adjudicated.

The controller runs both mutations and the full default build. The prototype
must also pass its separate target, since it is intentionally not a default
import. Report pre-existing warnings and axiom dependencies faithfully.

No full production implementation plan is written until the evidence establishes
which interfaces are suitable. The record must say which interface decisions
remain provisional and which future obligations are still unproved.

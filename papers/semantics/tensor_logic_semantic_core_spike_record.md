# Tensor Logic Semantic Core: Feasibility Spike Record

## Status and purpose

**Status: prototype, proof checks, mutation cycles, and full default build
passed; both final reviews clean. Spike complete.**

This is the results record for the
[bounded spike plan](tensor_logic_semantic_core_spike_plan.md), following the
[targeted semantic gap audit](tensor_logic_semantic_gap_audit.md).
The experiment must test reuse, scalar/backend flexibility, and a genuine
categorical-index connection before selecting production interfaces.

The prototype is
[`TensorLogicSemanticCoreSpike.lean`](../../leanncd/LeanNCD/Semantics/TensorLogicSemanticCoreSpike.lean),
checked by the non-default `SemanticCoreSpike` Lake target. It is deliberately
not imported by `LeanNCD`. At the original spike baseline, default builds did
not typecheck it. The expression/readiness validation slice's
`Semantics.ContractTest` now imports its formal-index witness, giving it
indirect default-test coverage without making it a production import.
The existing production evaluator and backend capability guards are unchanged.

## Baseline and setup

- Baseline: `3bdd7f9c9baa98e541b6951223d0bc89c610a23b`.
- Worktree: `pyncd.worktrees/tensor-logic-boundary-policy-review`.
- The existing isolated session worktree was retained, preserving its
  boundary-policy and audit edits.
- `prepare-worktree.sh` copied the warm cache and reported 8,101 Mathlib
  oleans for 8,094 source modules, plus 199 project oleans.
- `lake-build.sh ... LeanNCD` refreshed project-owned imports successfully.
  It emitted pre-existing `sorry`/lint warnings; this is not a claim that
  every imported categorical declaration is proved.
- The prototype was initially tracked in `spikes/` through an ignore exception.
  It now lives in `LeanNCD/Semantics/`, where no ignore exception is needed.
  Its non-default target preserves explicit checking without expanding
  production imports.

## Result: the proposed seam is feasible in a bounded fragment

The prototype proves read stability and partial-store consistency through
one carrier-parametric interpreter, without algebraic laws on the carrier.
It compiles with exact rational and exact complex interpretations, and
executes the same grammar natively with binary32 and binary64 operations.
It also proves that one signed affine read follows an actual realized
`StMat`, while keeping finite bounds explicit.

This establishes a useful semantic seam. It does not select the production
AST, heterogeneous dtype system, complete primitive registry, or categorical
target category, and does not prove program-level additive correspondence.

## Definitions and proof surface

The source uses `Ops K` for scalar zero, addition, multiplication, and a
checked reciprocal. It requires no `CommSemiring`, associativity, or
distributivity instance. `Expr K Addr` is indexed by context type:
`reduce n` has a body in the extended context `Gamma x Fin n`.
Addresses and context are separate parameters; fixture addresses reuse `UID`.

The scalar fragment consists of literals, reads, binary addition/multiplication,
reciprocal, and finite reduction. `footprint` returns a duplicate-preserving
list of structural reads, enumerating actual bound coordinates.

| Definition/theorem | What it establishes | What it does not establish |
| --- | --- | --- |
| `evalWith` | A shared deterministic interpreter, with explicit store and primitive failures | General primitive arity, array results, or algebraic laws |
| `evalWith_stable` | Stores agreeing on every structural read give identical results, including error payloads | Minimal footprints or semantic dependence pruning |
| `eval_stable` | Complete environments agreeing on reads have equal value/domain-failure results | Contribution collection or unique program models |
| `Ready`, `checkReads`, `evalReady` | All required reads are checked before interpreting a partial store | A production scheduler or publication transition relation |
| `ready_consistent` | A partial store agreeing with a complete environment on required reads has the same result, including undefinedness | Construction of every complete extension or ranked program progress |
| `evalReady_stable` | Changing unrelated partial-store entries cannot change the ready-evaluation outcome | Statement-level schedule independence |

`Failure.unavailable address` is distinct from `Failure.domain cause`.
For a future machine, an unavailable read would mean waiting, not an
undefined primitive or evidence that a model does not exist.
Preflight deliberately gives an unavailable read priority over any primitive
failure while the expression is not ready.

Reduction uses a strict right fold with coordinates enumerated in increasing
order. Thus the parenthesization is explicit, not inherited from an exact
semiring assumption. This numerical ordering is provisional; no equivalence
to the production workers' left-fold rounding behavior is claimed.

## Reuse and extension boundaries

| Existing asset | Actual reuse in the spike |
| --- | --- |
| `UID`, `AxisSpec`, `IdxExpr`, `StMatP` | Existing identity and affine presentation vocabulary, unchanged |
| `UnaryDomainOp` | Existing closed primitive-domain diagnostic, wrapped separately from missing-read outcomes |
| `UnaryOp.applyChecked` / `applyChecked32` | Existing native binary64/binary32 reciprocal/domain implementations, unchanged |
| `idxToRow`, `idxAffineForm`, `idxDensify` | Existing signed coefficient/bias lowering, unchanged |
| `realizeStMat`, `intToCoeff`, `StMat`, `Coeff` | Actual formal affine representation and polynomial coefficient interpretation |
| Generic traversal and carrier-shared worker patterns | Engineering precedents, not reused code for the new grammar |

`Expr`, `Ops`, the footprint traversal, and readiness functions are new
prototype definitions. Existing `traverseAxes` traverses the existing AST,
not this context-indexed grammar; the spike does not pretend to have reused
it or proved a DSL adapter. Existing private numerical ops records also
remain untouched rather than being extracted speculatively.

## Carrier evidence

All four interpretations use the same `Expr`, `evalWith`, and stability
theorems.

| Interpretation | Evidence | Qualification |
| --- | --- | --- |
| Exact rational | Kernel-checked fixtures plus executable observed results | A fixture instance, not the only supported scalar domain |
| Native binary64 | Runtime guards compare computed bits with native operations and pin expected bits | No exact-semiring or cross-backend numerical theorem |
| Native binary32 | Same grammar and traversal, native `Float32` arithmetic/reciprocal | No widen/narrow implementation |
| Exact complex | Kernel-checked `I * I = -1` evaluation and zero-reciprocal failure | Noncomputable mathematical `Complex`; not `complex64` machine execution |

The rounding-sensitive expression is `(2^24 + 1) + (-2^24)`. It evaluates
to exact rational one, binary64 one (`0x3ff0000000000000`), and binary32
zero (`0x00000000`). Native reciprocal of two is pinned as
`0x3fe0000000000000` / `0x3f000000`. These intentionally differing results
demonstrate that the common interpreter does not identify precision choices.

The initial exact-complex fixture proofs failed to elaborate because their
simplification did not discharge `Except` binds/error mapping. They were
repaired using explicit definitional reduction and `Except.mapError`; both
subsequent target and snippet checks passed. No failed proof was left admitted.

## Actual categorical-index connection

`signedPresentation` is built using the existing DSL lowering for the index
`-2*i + 3`. `signedMatrix` is the actual
`realizeStMat signedPresentation oneAxis oneAxis`, not a new affine structure
renamed as a categorical object.

`signed_coordinate` proves its polynomial-coordinate interpretation is
`intToCoeff (-2*x + 3)`. `integerCoordinate_eq` specializes that interpretation
to signed integers. `signedRead_connection` then proves that the new read
constructor accesses the address selected by this realized formal map, for
every scalar carrier and operations record.

`boundedSigned` requires separate lower and upper bounds before constructing
`Fin n`. The map sends coordinate two to minus one, so it is not a total map
of the four-element finite coordinate domain merely because its matrix ranks
match. The fixture at coordinate one supplies valid bounds and produces one.

This is a rank-one connection, not a general composition/naturality theorem,
complete `DGradedColoredPROP` interpretation, `Algebra` instance, or
categorical backend. In particular, it does not route dtype information
through the existing `weaveToArrayType` default-real interpretation.
Future carrier-aware categorical realization remains an explicit obligation.

## Observed behavioral discriminators

The executable outputs below were observed through both the target and
snippet check; the exact-complex assertions were kernel-checked instead of
executed as machine arithmetic.

| Case | Observed/proved outcome |
| --- | --- |
| Bound reduction reading values 2, 3, 4 | `ok 9` |
| Empty reduction with reciprocal-of-zero body | `ok 0`; no body coordinate exists |
| Reciprocal applied outside that empty reduction | `domain recip` |
| Zero multiplied by reciprocal of a zero input | `domain recip`, not zero |
| The same expression with required input missing | `unavailable 7`, not primitive failure |
| Reduction with only its first input present | `unavailable 8` |
| Reciprocal of input two | Exact `1/2`, matching native-carrier fixtures |
| Unrelated store values changed to 999 | Equal ready result, proved using `evalReady_stable` |
| Signed affine read at coordinate two | `ok -1` with no fabricated finite-bound proof |
| Exact complex multiplication of two imaginary units | `ok (-1)` |
| Exact complex reciprocal of zero | `domain recip` |

## Checks

Controller checks passed:

```bash
bash leanncd/scripts/lake-build.sh /path/to/worktree/leanncd SemanticCoreSpike
bash .claude/skills/slice-plan/check-snippet.sh \
  leanncd/LeanNCD/Semantics/TensorLogicSemanticCoreSpike.lean
bash leanncd/scripts/lake-build.sh /path/to/worktree/leanncd
```

The original spike's full default build completed successfully with 8,676
jobs. Default targets remain `LeanNCD` and `Tests`; at that baseline the spike
needed its separate check. The later expression/readiness slice adds the
indirect coverage described above.

Printed axiom dependencies:

- `evalWith_stable`, `eval_stable`, `ready_consistent`, `evalReady_stable`:
  `[propext, Quot.sound]`.
- `signed_coordinate`, `integerCoordinate_eq`, `signedRead_connection`:
  `[propext, Classical.choice, Quot.sound]`.

No `sorry`, added axiom, `admit`, or `native_decide` occurs in the spike.
No `sorryAx` appears in these printed proof dependencies. Imported production
modules emitted their pre-existing `sorry`/lint warnings; no global
sorry-free claim is made.

Both controller-run mutations used `mutation-cycle.sh` against the explicit
`SemanticCoreSpike` target, with a SHA-256 manifest verifying exact restoration.

| Mutation | Mutated result | Restoration | Restored target |
| --- | --- | --- | --- |
| Replace the read footprint `[a gamma]` with `[]` | Build failed, including the read case of `evalWith_stable` and footprint/readiness fixtures | Byte-identical, hash check passed | Passed |
| Replace empty reduction success with a reciprocal-domain error | Build failed at reduction-value and empty-domain fixtures | Byte-identical, hash check passed | Passed |

These were type/proof failures after valid source mutations reached Lean,
not parser failures or setup refusals. New mutations were not applied to
production code.

## Final review

The independent proof/semantic review found no significant semantic/proof
errors or unjustified claims across all eight modified/new session files,
including the boundary-policy mathematics, audit conclusions, theorem
hypotheses, and executable definitions. This was a read-only review; it did
not rerun builds or mutations or certify the non-goal semantics.

The independent reuse/carrier/categorical compatibility review also found
no blocking or non-blocking issues. It checked the complete session evidence
and spot-verified the key production contracts. In particular, it confirmed
the distinctions between uniform `K` and heterogeneous dtypes, exact complex
values and `complex64`, the rank-one bridge and a full categorical
interpretation, and default versus explicit build coverage.

Both reviews were read-only, and neither claimed general backend or
denotational/operational correctness. No review findings required a source
change or an adjudication.

The repository token-report command was attempted for the Copilot session:

```bash
python3 .claude/skills/slice-plan/token-report.py b7b54e50-2051-42c5-be3e-9a26cfe9ee84
```

It reported no transcript because it searches Claude session transcripts.
Consequently, the prescribed cumulative-token measurement is unavailable
for this session; no numerical total or compliance claim is inferred.
The prototype dispatch reported 17 tool-bearing turns and 37 individual tool
calls, within its turn cap. It reported no context breach, but the unavailable
session measurement means that report is not independently quantified here.

## Decisions

**Supported next step:** design the first production semantic fragment around
a carrier-parametric interpretation and a separately stated read-stability
contract, reusing the existing UID/index/error vocabulary where appropriate.
The experiment shows no need to require floating-point semiring laws merely
to define interpretation or prove readiness consistency.

Keep these decisions open:

- The full scalar/array typed grammar and capture-avoiding substitution.
- Primitive registry, arity, and extensibility; the spike has reciprocal only.
- Address/signature representation; arbitrary `Addr` and read functions are
  flexible but do not themselves enforce declared tensor roles or bounds.
- Heterogeneous dtypes within an expression/program; `K` is uniform per
  interpretation in this spike.
- Finite footprint representation, diagnostic ordering, and numerical folds.
- A general coordinate interpretation of `D`, its laws, and a semantic target
  category supporting the admitted nonlinear/partial operations.
- Exact versus rounded backend refinement and capability profiles.
- Additive occurrences/models, publication transitions, and ranked progress.

No JAX execution was implemented or checked. The spike demonstrates a
backend-independent reference definition, not a validated JAX adapter.
Existing backend restrictions and categorical coherence obligations remain
unchanged. No production AST migration or implementation plan is selected
by this record.

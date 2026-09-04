# Wave C capability manifest

This is a standalone reference for what the Wave C checked `EvalPlan` boundary actually accepts,
rejects, and covers today — not a design narrative. For the architecture, the correctness laws, and
the reasoning behind each decision, see
[`wave_c_evalplan_proposal.md`](wave_c_evalplan_proposal.md); for the slice-by-slice delivery
history, see [`restructure_suggestions.md`](restructure_suggestions.md). Every number below was
counted from an actual run on this branch, not estimated or copied from planning text.

## 1. Semantic and wire versions

- **Semantic version:** this mechanism was **removed in Wave F F3**. `checkPlan` no longer has a
  `RawEvalPlan.version`/`admittedVersion` check to run — Wave F's `PlanStep.scan` constructor made
  bumping the field the wrong fix once adding a stateful plan step changed the plan language's Lean
  type directly; see
  [`wave_f_scanplan_proposal.md` §2.3](wave_f_scanplan_proposal.md#23-remove-the-unused-in-memory-version-tag).
  There is no version tag today; see
  [`wave_f_capability_manifest.md` §1](wave_f_capability_manifest.md#1-semantic-and-wire-versions)
  for what replaced it (nothing).
- **Wire version:** N/A. C5 (canonical representation and codec — `Plan/Canonical.lean`,
  `Plan/Codec.lean`) is deliberately deferred; see
  [`wave_c_evalplan_proposal.md` A.9](wave_c_evalplan_proposal.md#a9-c5---canonical-representation-and-codec).
  There is no wire format, and therefore nothing to version, until C5 is built.

## 2. Accepted source constructs

The checked fragment accepts exactly (proposal §3.1):

- scan-free `.plain` assignment steps;
- ordinary free LHS axes only;
- concrete `f64` tensor signatures;
- identity nonlinearity;
- real sum-product contraction;
- plain tensor read factors;
- integer-affine reads, including shifts, scales, and multi-axis affine expressions;
- multiple factors per term;
- multiple terms per assignment;
- per-term contracted axes;
- chained scheduled steps and intermediate tensors;
- zero-padded out-of-bounds reads;
- zero/one dimensions if their semantics are explicitly validated;
- the current full-environment observation through `PlanBindings`.

The differential sweep in §4 below is real, counted evidence for most of this list, but its own
generator (`test/Eval/PropertyOracle/Gen.lean`) pins both axes at size 2, generates only rank-≤2
programs, and only produces single-axis affine reads (`.axis`, `.shift _ 1`, `.scale 2 _`) — it
never generates a size-0/size-1 axis or a multi-axis affine expression. Two bullets above are
validated by hand-built fixtures instead: zero/one dimensions by
[`ContractTest.lean:490`](../leanncd/test/Eval/Plan/ContractTest.lean) and
[`KernelDenseTest.lean:279`](../leanncd/test/Eval/Plan/KernelDenseTest.lean), and multi-axis affine
reads by [`KernelCheckTest.lean:94`](../leanncd/test/Eval/Plan/KernelCheckTest.lean)'s two-column
`coeffs` case and C6's own `warnProg` fixture in
[`CompileTest.lean`](../leanncd/test/Eval/Plan/CompileTest.lean) (`X[2 * i + j]`).

## 3. Rejected source constructs

Every rejection is a typed `CapabilityError` constructor
([`LeanNCD/Eval/Plan/Error.lean`](../leanncd/LeanNCD/Eval/Plan/Error.lean)) — there is no
`unsupported : String` escape hatch. All 11 categories, **as of Wave C**:

> **Current-state note (re-derived 2026-09-03, Task 4 of
> [`boolean_predicate_output_evalplan.md`](boolean_predicate_output_evalplan.md)).** The enum has
> since grown a twelfth constructor (`noAdvancingAxis`) and, more importantly, most of the rows
> below no longer have a producer: static throw-site inspection of `capabilityPreflight` finds
> **4 live producer families** — `scatterOrAffineLhs`, `unsupportedLhsSlot`,
> `recurrenceOrCallback`, and `noAdvancingAxis` — and **8 producer-less or structurally unreachable
> constructors** (`scanNode`, `unsupportedNonlin`, `maskOrPredicate`, `unaryFactor`,
> `unsupportedAgg`, `booleanOutput`, `unsupportedDtype`, `dynamicShape`). Enum size is unchanged by
> design: a closed constructor is retained for compatibility once its last producer is removed. Read
> the rows below as the Wave C boundary, not as today's.

| Constructor | Rejects |
|---|---|
| `scanNode` | `ScanStmt.scan` / `.scanPre` |
| `scatterOrAffineLhs` | scatter statements, affine LHS slots |
| `unsupportedLhsSlot` | `freeNorm`, `iterAt`, `iterNext` LHS slots |
| `unsupportedNonlin` | pointwise/axiswise nonlinearities |
| `maskOrPredicate` | masks, predicates, Iverson factors |
| `unaryFactor` | unary functions on a factor |
| `unsupportedAgg` | max/min aggregation |
| `booleanOutput` | Boolean/predicate declared outputs — RETAINED, no producer left (Task 4 admits a `.predicate` declaration; `checkDecl`'s predicate arm is `pure ()`), kept like `scanNode` |
| `unsupportedDtype` | any dtype other than the declared `f64` mode |
| `dynamicShape` | backend- or value-dependent shapes |
| `recurrenceOrCallback` | recurrence- or callback-bearing payloads |

**Two of these — `unsupportedDtype` and `dynamicShape` — are structurally unreachable from the
current AST, not merely unimplemented.** `Compile.lean`'s own doc comment says so
(`capabilityPreflight`: "`unsupportedDtype`/`dynamicShape` are never thrown below"), and this is
confirmed by the AST itself, not just the comment:

- `Decl` ([`LeanNCD/DSL/Ast.lean`](../leanncd/LeanNCD/DSL/Ast.lean)) has constructors `.tensor`,
  `.predicate`, `.linear`, `.axis`, `.iter` — none carries a `ScalarDType` or any other dtype field.
  There is nothing in a declaration for a dtype check to inspect and reject.
- `IdxExpr` (same file) has constructors `.axis`, `.const`, `.scale`, `.shift`, `.affine` — every
  one is integer-affine over a fixed axis basis. None can express a backend- or value-dependent
  shape.

This distinction matters for a future reader deciding whether to "complete" these two categories:
doing so is not a matter of adding a missed check to `Compile.lean`, but of first adding a new AST
constructor (a dtype field on `Decl`, or a value-dependent-shape constructor on `IdxExpr`) that does
not exist today. The other 9 categories are real, exercised rejections of constructs the AST already
expresses.

## 4. Law 1 corpus coverage

The full `PropertyOracle.enumPrograms` differential sweep
([`test/Eval/Plan/DifferentialTest.lean`](../leanncd/test/Eval/Plan/DifferentialTest.lean)) is the
real, counted evidence for Law 1 (residualization):

- **3,832** entries generated;
- **3,832** accepted by `capabilityPreflight`/`prepareEvalPlan` (**0** rejected, 0 rejection
  categories — every generated program today falls inside Wave C's scan-free fragment);
- **100% bit-exact agreement** between `runPreparedDense` and `evalScheduled` on every accepted
  entry, compared on both the indexed environment values (`EvalReport.env`) and the preparation
  warnings (`EvalReport.warnings`) — not values alone.

This is pinned by the file's own `#guard`, not merely printed and eyeballed:

```lean
#guard match sweep with
  | .ok (total, accepted, rejCounts) => total == 3832 && accepted == 3832 && rejCounts.isEmpty
  | .error _ => false
```

A future change that silently shifts the accept/reject boundary, or changes `enumPrograms`'s size,
fails this guard loudly instead of being silently re-baselined.

## 5. Extension points

These are named as what is **not yet supported and why** — a record of deliberate scope discipline,
not a roadmap commitment:

- **Scans.** Rejected via `scanNode` (§3). At Wave C completion, extending the plan to scans still
  needed explicit `ScanPlan` state, transition, geometry, boundary, order, and causality data and had
  been deliberately deferred, not designed. The later
  [`wave_f_scanplan_proposal.md`](wave_f_scanplan_proposal.md) now drafts that design; implementation
  remains unstarted. Adding scan support without explicit checked data would still mean guessing at
  semantics Wave C correctly declined to guess at.
- **Other backends (PyTorch/JAX).** Proposal §4.4/§10 treats Dense, PyTorch, and JAX as
  interpretations of one checked plan language, but only the Dense worker exists today. Whether and
  how PyTorch/JAX consume `CheckedEvalPlan` is contingent on how backend integration is eventually
  architected — `torch_compile/`'s existing ahead-of-time-codegen precedent for backend integration
  is why C5's codec (below) was deferred rather than built speculatively ahead of a real consumer.
- **Canonical representation/codec (C5).** Deferred; see
  [A.9](wave_c_evalplan_proposal.md#a9-c5---canonical-representation-and-codec) for the full
  reasoning (no consumer inside this process's own lifetime needs fingerprint stability or
  serialized bytes) and what would resurrect it (a concrete cross-process or persistence consumer).

## 6. Audit findings confirmed clean

Two findings from this plan's own authoring, recorded here so a future reader does not have to
re-verify them:

- **Three of [A.2](wave_c_evalplan_proposal.md#a2-production-modules-and-dependency-direction)'s
  import-direction constraints hold — this is not a claim that the whole graph matches A.2's
  diagram.** `Dense.lean` imports neither `Compile.lean` nor the legacy `Gather`/`Contract`;
  `Compile.lean` does not import `Dense.lean`; `SizeInfer.lean` imports no plan module.
  (`Canonical.lean` does not exist yet — C5 is deferred — so its A.2 constraint has no module to
  check against.) Two things A.2's diagram does not show as-is: A.2 lists
  `Prepared + Dense + Check + Error + Eval.Report -> Adapter`, but `Adapter.lean` actually imports
  `Compile.lean` too (pre-existing since C4, not introduced by this slice), which transitively
  pulls in `DSL.Ast`, `DSL.Pipeline.Lowering`, and `Eval.Contract`. And A.2's module table also
  lists a `Plan.lean` "stable public umbrella" that was never built; C6's Task 2
  `import LeanNCD.Eval.Plan.Adapter` (`LeanNCD.lean`) supersedes that never-built umbrella as the
  real top-level entry point, so this is superseded scope, not unmet work.
- **The checked semantic IR carries no `String`, `UID`, callback/function, or unordered-map field
  anywhere.** `AffineMap`, `ReadPlan`, `TermPlan`, `AssignPlan`, `RawEvalPlan`
  (`Plan/Kernel.lean`, `Plan/Graph.lean`) and the `CheckedAssignPlan`/`CheckedEvalPlan` wrappers
  (`Plan/Check.lean`) are built entirely from `Nat`, `Int`, `Array`, `TensorSlot` (a `Nat`), and the
  closed `ScalarDType`/`ScalarConst`/`ScalarBinOp`/`ContractionAlgebra`/`NumericMode`/
  `OutOfBoundsPolicy` tags. The source-name-keyed `HashMap String TensorSignature` in
  `InputSignature` and the `SlotBinding`/`PlanBindings` sidecar are boundary/specialization data by
  design (proposal §5.1/§5.4) — they sit outside the checked plan, not inside it.

**Which import to use.** For checked-plan execution with no source compilation, import
`Plan.Check`/`Plan.Dense` directly — neither imports `Compile.lean`, `DSL.Ast`, or the legacy
evaluator. For the named source-to-plan boundary (`prepareEvalPlan`, `pack`/`unpack`/
`runPreparedDense`), import `Plan.Adapter` — this pulls in `Compile.lean` and therefore source
compilation. `import LeanNCD` pulls in everything, including the legacy `Eval.Entry` evaluator.
Only a `Plan/` leaf import (`Plan.Check`/`Plan.Dense`) satisfies A.10's Gate clause: "Wave F and
Wave G can consume checked plan APIs without importing source compilation or legacy execution."

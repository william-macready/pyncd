# Logical nonlinearity scheduling and private route fragments

**Status:** Detailed design and implementation plan; not yet executed.

**Decision:** Preserve nonlinear assignments in the shared `ScheduledProgram`. Schedule once over
logical tensor names. Eval consumers lower or execute that logical assignment directly. Immediately
before categorical routing, expand each top-level nonlinear assignment into a private physical route
fragment containing the necessary contraction and nonlinearity generators. Do not expose generated
tensor names in source validation, the shared schedule, Eval APIs, or serialization.

This document replaces the earlier
[pair-reconstruction plan](nonlinearity_split_pair_reconstruction_archived.md). That approach is not
appropriate because it makes a route-specific physical encoding part of the shared schedule, forcing
Plan compilation, legacy scan evaluation, and the independent oracle to reconstruct the same logical
operation from generated names, adjacency, and trivial reads. The spikes showed that this coupling is
not merely inconvenient: it creates name/protocol machinery and produces incorrect scan results when
the physical pair is evaluated directly.

This document also supersedes:

- the logical-schedule fork described in [`papers/todo.md`](todo.md);
- the three-step Eval lowering in
  [`docs/superpowers/specs/2026-08-21-nonlinearity-in-scans-design.md`](../docs/superpowers/specs/2026-08-21-nonlinearity-in-scans-design.md);
- the corresponding implementation sequence in
  [`leanncd/docs/superpowers/plans/2026-08-21-nonlinearity-in-scans.md`](../leanncd/docs/superpowers/plans/2026-08-21-nonlinearity-in-scans.md).

The older scan design remains authoritative for snapshot semantics, complete-history publication,
state writes, and retained-local-axis mapping except where this document replaces split-pair
handling.

**Table of contents**

- [1. Decision and rationale](#1-decision-and-rationale)
  - [1.1 Notation and terminology](#11-notation-and-terminology)
  - [1.2 Current representation and demonstrated failures](#12-current-representation-and-demonstrated-failures)
  - [1.3 Spike evidence](#13-spike-evidence)
    - [1.3.1 Durable implementation artifacts](#131-durable-implementation-artifacts)
  - [1.4 Selected architecture](#14-selected-architecture)
  - [1.5 Motivations and benefits](#15-motivations-and-benefits)
  - [1.6 Scope and non-goals](#16-scope-and-non-goals)
- [2. Design contract](#2-design-contract)
  - [2.1 One logical scheduled representation](#21-one-logical-scheduled-representation)
  - [2.2 Private physical route program](#22-private-physical-route-program)
  - [2.3 Collision-free route-local identifiers](#23-collision-free-route-local-identifiers)
  - [2.4 Physicalization algorithm](#24-physicalization-algorithm)
  - [2.5 Categorical routing and proof boundary](#25-categorical-routing-and-proof-boundary)
  - [2.6 Eval lowering and execution](#26-eval-lowering-and-execution)
  - [2.7 Scan block IR, allocation, and publication](#27-scan-block-ir-allocation-and-publication)
  - [2.8 Oracle and differential boundaries](#28-oracle-and-differential-boundaries)
  - [2.9 Future compatibility and alternatives](#29-future-compatibility-and-alternatives)
- [3. Detailed implementation plan](#3-detailed-implementation-plan)
  - [3.1 Dependencies and global constraints](#31-dependencies-and-global-constraints)
  - [3.2 Task and risk summary](#32-task-and-risk-summary)
  - [3.3 Task 1: atomic architecture gate](#33-task-1-atomic-architecture-gate)
  - [3.4 Task 2: durable nonlinear route corpus and realization regression](#34-task-2-durable-nonlinear-route-corpus-and-realization-regression)
  - [3.5 Task 3: generalize Plan blocks](#35-task-3-generalize-plan-blocks)
  - [3.6 Task 4: admit nonlinear Plan scans](#36-task-4-admit-nonlinear-plan-scans)
  - [3.7 Task 5: differential documentation and closure](#37-task-5-differential-documentation-and-closure)
- [4. Verification, completion, and fallback](#4-verification-completion-and-fallback)
  - [4.1 Required verification record](#41-required-verification-record)
  - [4.2 Route-adapter time-box](#42-route-adapter-time-box)
  - [4.3 Stop conditions](#43-stop-conditions)
  - [4.4 Definition of done](#44-definition-of-done)
  - [4.5 Future architecture triggers](#45-future-architecture-triggers)

## 1. Decision and rationale

### 1.1 Notation and terminology

| Term | Meaning |
|---|---|
| Logical assignment | One source operation `Y := f(E)`, retaining body `E`, aggregation, placement, and `f` |
| Logical schedule | A `ScheduledProgram` containing logical assignments and logical tensor names |
| Route fragment | One or more route-private physical statements emitted for one logical statement |
| Fragment entry | First physical step in a route fragment |
| Fragment exit | Final physical step; publishes the logical result for downstream routing |
| Internal route name | Collision-free private identifier connecting two steps in one nonlinear fragment |
| Preactivation slot | Eval-local tensor slot containing `E` |
| Result slot | Eval-local tensor slot containing `f(E)` |

The shared schedule has no generated `%nlN` producer/consumer pairs. A nonlinearity remains a field
of its logical `RHSExpr`.

### 1.2 Current representation and demonstrated failures

The current pipeline runs `splitNonlins` before scheduling:

```text
Y := f(E)
  ->
%nlN := E
Y    := f(%nlN)
  ->
schedule
```

Categorical routing benefits from two physical generators:

```text
BrBase(E) -> BrBase(f)
```

They are categorically necessary. One `BrBase` carries one operation; their composition is one
`BrMorph`. Fusing them would be the wrong abstraction.

The problem is where the decomposition occurs. The shared schedule exposes a route-oriented
linearization to consumers that need the logical operation:

- Backend Plan compilation independently lowers the consumer and produces
  `assign E -> assign copy -> pointwise/axiswise`;
- legacy scan evaluation executes the producer as a rank-reduced scratch slice, then reads it through
  the consumer's original full-rank coordinates;
- the independent scan oracle must recognize generated producer/consumer structure;
- generated names require collision, adjacency, fan-out, error-precedence, and publication rules.

The spikes demonstrated real legacy errors:

```text
leading-axis pointwise expected: [2, 3, 20, 300, 200, 30000]
leading-axis pointwise current:  [2, 3, 20, 20, 2000, 2000]
```

An interleaved axiswise recurrence incorrectly produced uniform `0.5` slices instead of:

```text
G[0] = [1, 2, -1, 1]
G[1] = [0.2689414213699951, 0.7310585786300049,
        0.8807970779778823, 0.11920292202211755]
G[2] = [0.3864836956412729, 0.6135163043587272,
        0.9915205505990216, 0.008479449400978346]
```

These are representation-boundary failures, not merely a redundant-copy optimization.

### 1.3 Spike evidence

Thirteen GPT-5.6 Sol/high spikes informed and then de-risked this decision.

1. **Generated-name provenance:** escaped surface names and programmatic ASTs can collide with `%nl`;
   `FreshM` does not inspect tensor names; scheduling guarantees topology, not atomic pair ownership.
2. **Error precedence:** capability-first compilation makes malformed-pair diagnostics unreachable;
   pair-first compilation would add an internal protocol phase before ordinary source diagnostics.
3. **Scan allocation:** an executable model passed 18 mixed recurrence cases and two nonlinear base
   cases when allocation used emitted physical-step count and explicit result-only outputs.
4. **Legacy/oracle semantics:** current split execution is wrong for leading-axis pointwise and
   interleaved axiswise scans; direct unsplit evaluation agrees with independent computation.
5. **Route fragments:** a compiling prototype scheduled without `splitNonlins`, expanded nonlinear
   top-level assignments immediately before routing, and produced structurally identical
   `ThreadedComposed` values for all tested top-level and scan cases.
6. **Formal Agreement skeleton:** a disposable Lean prototype closed
   `compile_eq_physical_route` and the unchanged public `compile_wellFormed` without `sorry` or any
   `RouteSpec` theorem change. Agreement itself consumes only successful `routeCore`, external-count
   equality, and `wellFormedDom`; freshness, coverage, contiguity, and exit evidence are instead
   load-bearing for checked physicalization and route equality.
7. **Generated nonlinear route corpus:** 145 deterministic cases across 13 families ran in 6.70
   seconds. All 137 cases accepted by both pipelines had exact complete route and ACSet equality.
   Eight escaped `%nl0` source-name cases were rejected by the old collision-prone pipeline and
   accepted by the logical pipeline. Six production mutations were caught.
8. **Independent oracle extension:** the logical schedule required only two `.freeNorm` match
   alternatives in `ScanUnroll`. Six semantic fixture groups matched direct expectations and unsplit
   legacy Eval in 5.68 seconds; four independent oracle mutations failed as intended.
9. **Scheduled-API census:** 10 production, 27 test, and 4 experiment `compileToScheduled` sites were
   classified. It found no in-repository architectural blocker, but requires
   public `route` compatibility, a `LinearProgram` compatibility alias, an explicit FreshM-state
   policy, and a larger verification/documentation inventory.
   **Unit correction (2026-08-26):** the test and experiment figures are *call* counts and were
   re-verified exactly. The production figure is a *mention* count, not calls — there is exactly
   **one** production runtime caller, `Eval/Entry.lean`. Of the other nine: one is the definition in
   `DSL/Compile.lean`, one is a comment in `Pipeline/Lowering.lean`, and **seven are
   `Bridge/Agreement.lean` proof references** — which are the proof surface this work repairs, not
   call sites to re-verify. Budget the production side as one caller plus one proof, not ten callers.
10. **Block-step provenance:** a production-shaped checker accepted assignment-to-pointwise/axiswise
    chains, rejected direct capture and nonlinearity-to-nonlinearity sources, and preserved causal
    mapped-state chains. The sound, minimal guard is block-specific nonlinear `sourceCheck`, not a
    change to generic `checkStepGraph`; targeted and full builds passed.
11. **Negative diagnostic differential:** 19 compile cases produced 14 exact results/errors/states,
    three equal successful values with one fewer removed split mint, one equal nonlinear-cycle error
    with two fewer mints, and one intentional `%nl2` old-reject/new-accept collision. Two direct route
    failures also matched exactly. Three diagnostic/result mutations were detected.
12. **Semantic-payload conservation:** 18 matrix programs and 12 full route/ACSet comparisons showed
    that physicalization preserves aggregation, nonlinearity, masks, Iverson factors, metadata,
    affine reads, `.freeNorm`, publication exits, and opaque scan payloads. Nine mutations were
    detected. Masks, predicates, dtypes, and `scanPre` bodies remain intentionally opaque in the
    current categorical projection; route equality is not evidence of their full source semantics.
13. **`BlockStep` migration rehearsal:** the complete 47-occurrence migration, checked-step sum,
    block-local provenance, Dense dispatch, compiler wrapping, and assignment-only causality traversal
    compiled without new imports or production files. Targeted tests, 3,832 differential cases,
    `Tests`, and `LeanNCD` passed. Task 3 is bounded at 1.5-2 focused days.

The route-fragment prototype covered:

- isolated ReLU;
- contraction -> ReLU -> downstream contraction;
- two independent nonlinear branches feeding one join;
- axiswise softmax;
- mixed identity/nonlinear statements;
- unread secondary nonlinear output;
- ReLU recurrence, axiswise recurrence, and coupled scans;
- adversarial internal-name collision;
- route-domain well-formedness and ACSet round trips.

`lake build Tests` and `lake build LeanNCD` passed after the disposable prototype. No tracked file was
changed.

#### 1.3.1 Durable implementation artifacts

The expensive, production-shaped parts of the spikes are preserved under
[`papers/implementation_seeds/nonlinearity_route_fragments/`](implementation_seeds/nonlinearity_route_fragments/).
They are implementation donors, executable specifications, and regression seeds. They are not a new
source tree and must never become a production dependency.

##### Artifact inventory and authority

| Artifact | What it provides | Implementation use | What it does **not** prove |
|---|---|---|---|
| [`adapter_proof/RouteFragmentsSeed.lean`](implementation_seeds/nonlinearity_route_fragments/adapter_proof/RouteFragmentsSeed.lean) | Proof-carrying `PhysicalRouteProgram`; route-name inventory and freshness/injectivity proofs; one-pass physicalization; checked layout, exit, and topology evidence; logical `compileToScheduled`; public-route-shaped wrapper; `compile_eq_physical_route`; repaired `compile_wellFormed`; exact result/state checks | Primary production-code donor for Task 1 | It uses a donor-only import/compatibility arrangement and namespace-visible package constructor; it is not the final module graph or access boundary |
| [`adapter_proof/README.md`](implementation_seeds/nonlinearity_route_fragments/adapter_proof/README.md) | Declaration-level transplant map, safe integration order, exact FreshM observations, verification record, mutation record, and donor limitations | Task 1 handoff checklist; read before copying any declaration | It does not replace the Task 1 API census or full production mutation gate |
| [`fixtures/FixtureSupportSeed.lean`](implementation_seeds/nonlinearity_route_fragments/fixtures/FixtureSupportSeed.lean) | Small executable logical scheduler/physicalizer, fragment observations, old/new route comparison, and reusable smoke/branch fixture shapes | Fixture-construction donor and fast behavioral oracle for Tasks 1 and 2 | Its `PhysicalRouteProgram` uses Boolean checks, not the proof-carrying production representation |
| [`fixtures/RouteFragmentDiagnosticSeed.lean`](implementation_seeds/nonlinearity_route_fragments/fixtures/RouteFragmentDiagnosticSeed.lean) | Nineteen exact compile observations, two direct-route observations, and public-composition checks at multiple initial FreshM states | Direct donor for Task 1's `RouteFragmentDiagnosticTest` | Its local proposed entry points must be replaced with production `compileToScheduled`, `route`, and `compile` |
| [`fixtures/PayloadConservationSeed.lean`](implementation_seeds/nonlinearity_route_fragments/fixtures/PayloadConservationSeed.lean) | Nineteen named payload fixtures separating physical conservation from categorical opacity | Direct donor for Task 2's corpus test and Bridge assertions | Route/ACSet projection equality is not source-semantic equality for opaque fields |
| [`fixtures/RouteFragmentCorpusSeed.lean`](implementation_seeds/nonlinearity_route_fragments/fixtures/RouteFragmentCorpusSeed.lean) | Deterministic 145-case/13-family corpus, 137 common-domain exact comparisons, eight collision transitions, scan-opacity counts, and mutation hooks | Direct donor for Task 2's `RouteFragmentCorpusTest` | It does not execute `Bridge.realize` and does not test runtime Plan scan admission |
| [`fixtures/README.md`](implementation_seeds/nonlinearity_route_fragments/fixtures/README.md) | Exact case outcomes, fixture provenance, caller/proof census, mutation-to-defect map, limitations, and transplant order | Task 1/2 test migration checklist | It does not supersede the production files and commands listed in Sections 3.3 and 3.4 |

When the two implementations differ, the adapter/proof donor is authoritative for production
physicalization and the fixture donors are authoritative for their recorded observations. In
particular, do **not** transplant the fixture support's Boolean-only package as
`PhysicalRouteProgram`; use the checked/proof-carrying adapter design required by Section 2.2.

##### Verified baseline

On 2026-08-25 all five Lean donors typechecked directly from their final durable paths.
**Re-verified 2026-08-26** against `main` at `a063944`: all five still typecheck, the adapter donor
in ~5.3s with its 15 `#guard`s and five `run_cmd` blocks silent, and all five again from inside a
freshly prepared implementation worktree after `lake build LeanNCD`. The donors are therefore live
against the current tree, not a stale snapshot — a later donor failure is a transplant defect, not
base drift.

The adapter donor additionally passed:

- all 15 `#guard`s and five `run_cmd` checks;
- `lake build LeanNCD.DSL.Pipeline.Lowering LeanNCD.Bridge.Agreement`;
- `lake build Tests LeanNCD`;
- mutate/fail/restore/pass cycles for reinserting `splitNonlins`, removing strict route-name growth,
  mapping a nonlinear fragment exit to its entry, and corrupting routed `nExternal`.

The fixture donors retain their own recorded mutation cycles for diagnostic precedence/external
arity, mask/aggregation/metadata/`scanPre` conservation, private-name reuse, `.freeNorm`
degradation, and fragment-exit routing. These results establish that the artifacts are sound starting
points. They do not waive re-running the checks after declarations are transplanted into production:
imports, privacy, API types, and theorem dependencies all change during that move.

##### Claude startup and integration workflow

A future implementation session should use the artifacts in this order:

1. Create the isolated implementation worktree with the repository's `new-slice` workflow so the
   branch starts from local `main` and inherits a warm `.lake`. Do not implement in this planning
   worktree.
2. Read this document and both donor READMEs. Run the five direct donor checks before editing; a
   failure at this point is environment or base drift, not a production-transplant defect.
3. Treat the adapter donor as a declaration source, not a patch to apply wholesale. Create the
   production import graph first, then copy declaration groups in the order below.
4. Replace donor-only adapters with production APIs as soon as their destination exists. Keep a
   temporary compatibility adapter only while its removal is explicit in the same Task 1 gate.
5. After the logical boundary and public route wrapper compile, move the diagnostic fixtures and
   replace every local `logicalSchedule`, `physicalize`, or `proposedCompile` reference with the
   production entry point it is intended to test.
6. Restore Agreement before migrating the 145-case corpus. This keeps proof failure separate from
   fixture-transcription failure and makes the Task 1 day-3 checkpoint meaningful.
7. Migrate the corpus and payload matrix family by family, preserving names, family counts, exact
   outcomes, and mutation hooks. Add Bridge realization checks only in their planned Bridge test
   destinations.
8. Run each planned mutation against production code as mutate/fail/restore/pass. A donor mutation
   result is evidence that the fixture shape has teeth, not evidence that the transplanted production
   assertion still does.
9. Run the full API census and Section 4 verification after the transplant. Do not stop at the five
   donor checks or at route equality.

##### Task 1 production-code transplant

Use [`adapter_proof/RouteFragmentsSeed.lean`](implementation_seeds/nonlinearity_route_fragments/adapter_proof/RouteFragmentsSeed.lean)
as follows:

1. Move the shared `LHSSlot.toReadIdx` declaration to `DSL/Ast` if the production import graph
   requires it.
2. In the new `DSL/Pipeline/RouteFragments.lean`, transplant the name-accessor and inventory group
   (`declaredTensorName?`, route reads/writes/outputs, `routeNameInventory`,
   `maxSourceNameLength`, and `routeName`) with the length, freshness, and injectivity theorems.
3. Transplant `RouteFragment`, the physicalization accumulator and one-step helpers, generated-name
   extraction, layout/exit checks, and the physical topological-order check. Preserve the one-pass
   logical-to-physical construction and opaque copying of `.scan`/`.scanPre`.
4. Transplant `PhysicalRouteProgram` and `physicalizeForRoute`, but make the real constructor/private
   representation inaccessible outside the route boundary. Preserve exact-build, declaration/env/
   external preservation, fragment count/layout/exits, name freshness, and topology evidence.
5. In `Pipeline/Lowering`, keep `routeCore` unchanged and replace public `route` with the checked
   physicalization wrapper. The new module must import only `Types`; do not copy the donor's
   `Agreement` import into production or create a cycle.
6. In `DSL/Compile`, transplant the logical `compileToScheduled`/`compile` factorization. Delete the
   donor-only `scheduleLogical` record conversion once `LinearProgram` becomes the compatibility alias
   and `schedule` consumes the logical shape directly.
7. In `Bridge/Agreement`, transplant the shape of `compile_eq_physical_route` and the repaired
   `compile_wellFormed` proof. Keep the public theorem type and existing `RouteSpec` theorem statements
   unchanged; use the checked physical witness rather than exposing fragment evidence throughout
   Agreement.
8. Move private donor fixtures and executable guards into the Task 1 test modules. Production code
   must not contain test programs or import anything below `papers/`.

The adapter donor pins representative nonzero-start FreshM behavior: ReLU `9 -> 10` versus old
`-> 11`, softmax `23 -> 25` versus old `-> 26`, downstream chain `31 -> 32` versus old `-> 33`,
opaque scan `47 -> 50` versus old `-> 51`, and escaped `%nl8` acceptance `7 -> 8`. At start zero,
`assignUIDs` deliberately spends an extra mint to avoid UID zero, so retain the factorization check
rather than inventing a uniform zero-start delta.

##### Task 1 diagnostic transplant

Copy the named cases from
[`RouteFragmentDiagnosticSeed.lean`](implementation_seeds/nonlinearity_route_fragments/fixtures/RouteFragmentDiagnosticSeed.lean)
into `test/DSL/Pipeline/RouteFragmentDiagnosticTest.lean`, then:

- replace the local scheduler/physicalizer/compiler with production APIs;
- retain all 19 case identities, exact constructors and payloads, error precedence, and final states;
- retain the two direct-route cases at start 7;
- retain composition checks for cases 1, 2, and 16 at starts 0, 7, and 41;
- preserve the intentional distinctions: removed split mints on cases 5, 16, 17, and 18, plus old
  rejection/new acceptance for escaped `%nl2` case 19;
- register the new module in `lakefile.toml`;
- run the diagnostic mutations against production check order and route output, not against a cloned
  helper that production never calls.

This migration is complete only when the test reaches public `compile`, public
`compileToScheduled >>= route`, and direct `route` where specified. A passing test that still
exercises the seed's local pipeline is not a production regression.

##### Task 2 corpus and payload transplant

Use [`RouteFragmentCorpusSeed.lean`](implementation_seeds/nonlinearity_route_fragments/fixtures/RouteFragmentCorpusSeed.lean)
and [`PayloadConservationSeed.lean`](implementation_seeds/nonlinearity_route_fragments/fixtures/PayloadConservationSeed.lean)
to build `test/DSL/Pipeline/RouteFragmentCorpusTest.lean`:

- preserve the deterministic total of 145 cases and all 13 family counts rather than regenerating an
  approximately similar corpus;
- preserve 137 exact common-domain route/ACSet comparisons and the eight `%nl0`
  old-reject/new-accept transitions as separate claims;
- preserve the 40 scan-family observations and 32 split-body observations so opaque scan handling
  cannot disappear inside aggregate equality;
- preserve all 19 named payload fixtures separately from the generated corpus count;
- replace duplicated local physicalizers with the Task 1 production physicalizer before accepting
  any result;
- retain exact complete-value checks, not only selected fields or pretty-printed output;
- move theorem-level ACSet assertions to `Bridge/AcsetCodecTest` and shaped runtime realization
  assertions to `Bridge/RealizeTest`.

The payload matrix has two different obligations. Operation tags, aggregation, and affine reads must
retain exact physical statements and categorical outputs. Masks, Iverson predicates, dtype metadata,
and nested `scanPre` bodies must retain exact physical fields while explicitly demonstrating that the
current categorical projection omits them. Never rewrite the second observation as semantic
equivalence.

##### Commands and completion boundary

Run the donor baseline from `leanncd/`:

```bash
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/adapter_proof/RouteFragmentsSeed.lean
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/FixtureSupportSeed.lean
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/RouteFragmentDiagnosticSeed.lean
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/PayloadConservationSeed.lean
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/RouteFragmentCorpusSeed.lean
```

Then use the targeted and full production commands in Sections 3.3, 3.4, and 4. The artifacts speed
implementation by supplying compiled declaration shapes, proofs, fixtures, expected values, and
mutation targets. They do not change the completion boundary: Task 1 still requires the atomic
logical/physical API flip and Agreement restoration; Task 2 still requires production corpus,
realization, and ACSet wiring; the branch still requires the full builds and independent reviews.

##### Non-negotiable donor boundaries

- Never add `papers/` to Lake's production module search path and never import a seed from production
  or tests.
- Never copy the fixture support's Boolean-only `PhysicalRouteProgram` over the adapter donor's
  proof-carrying design.
- Never keep the donor's `scheduleLogical` once production `schedule` accepts the logical program.
- Never expose the production `PhysicalRouteProgram` constructor merely because the donor namespace
  can see its constructor.
- Never duplicate the donor's local physicalizer in a production test after Task 1 lands; tests must
  exercise the production implementation.
- Never infer source-semantic preservation solely from `ThreadedComposed` or ACSet equality for fields
  intentionally omitted by the categorical projection.
- Never hand-copy observed values from this prose without retaining the executable guard that produced
  them.

### 1.4 Selected architecture

The selected pipeline is:

```text
source normalization
  -> finalizeScans
  -> schedule once, with nonlinear assignments intact
  -> logical ScheduledProgram
       |-> legacy Eval
       |-> Backend Plan lowering
       |-> independent oracle input
       `-> public route
             -> checked physicalizeForRoute
             -> private PhysicalRouteProgram
             -> existing routeCore
             -> ThreadedComposed
```

For Eval:

```text
Y := f(E)
  ->
assign E to preactivationSlot
  ->
pointwise/axiswise f to resultSlot
```

For categorical routing:

```text
Y := f(E)
  ->
private contraction step
  ->
private nonlinear step publishing Y
```

There is one scheduler. The physical route adapter is a deterministic terminal lowering pass; it
does not call `schedule` or `topoSort`.

The public composition remains:

```text
TLProgram.compile = compileToScheduled >>= route
```

Here public `route` accepts a logical `ScheduledProgram`, checks/physicalizes it privately, and then
invokes the existing physical `routeCore`. Direct physical routing remains an internal proof/test
surface. This preserves the normal external composition while deliberately changing the semantic
meaning of `ScheduledProgram` from route-linearized to logical.

**Post-spike final decision.** The four latest spikes do not justify replacing this architecture.
They do replace four weaker implementation assumptions:

1. old FreshM counters are not compatibility targets after the former split phase; exact deltas must
   instead equal removed split mints, while new public composition remains exactly state-equal;
2. assignment-only scan causality requires block-local nonlinear producer provenance;
3. physical payload conservation is stronger than, and must be tested separately from, equality of
   the current categorical projection;
4. successful route equality is insufficient without independent negative-diagnostic and payload
   matrices.

Accordingly, implementation must strengthen the adapter, checker, and regression contracts without
adding another scheduler, exposing physical fragments, changing `routeCore`, adding dummy UID mints,
or admitting currently unsupported EvalPlan capabilities.

### 1.5 Motivations and benefits

1. **One semantic schedule.** Every executable consumer receives the source operation directly.
2. **Minimal Eval plans.** No identity-copy assignment or generated materialized name is created.
3. **Correct scan execution.** Seeded axes are removed before applying the logical nonlinearity.
4. **Categorical fidelity.** Contraction and nonlinearity remain two `BrBase` generators.
5. **No source namespace reservation.** Route-local names are collision-free by construction.
6. **Ordinary diagnostics.** No pair-protocol error phase precedes capability, input, or shape errors.
7. **Proof reuse.** The existing route specification applies to the private physical schedule.
8. **Future backend boundary.** Dense, JAX, PyTorch, and serialization consume logical or checked IR,
   not route-generated names.

### 1.6 Scope and non-goals

This slice includes:

- logical `compileToScheduled` output;
- one scheduling pass;
- private route fragments for top-level nonlinear assignments;
- collision proofs and fragment metadata;
- route equality and categorical agreement repair;
- direct top-level Eval lowering through the existing unsplit path;
- block-local pointwise and axiswise Plan steps;
- nonlinear scan base and recurrence lowering;
- retained-axis, publication, state-write, oracle, and differential correctness.

It does not:

- fuse contraction and nonlinearity into one `BrBase`;
- introduce a second scheduler;
- expose `PhysicalRouteProgram` as stable or serialized IR;
- add structured categorical scan bodies;
- change scan snapshot, boundary, iteration-order, or complete-history policy;
- define nonlinear scatter semantics;
- admit masks, predicates, unary factors, max/min aggregation, or new dtypes;
- add JAX or PyTorch execution;
- remove `splitNonlins` immediately; it remains a non-production regression/fallback helper until
  route equality and proofs are complete.

## 2. Design contract

### 2.1 One logical scheduled representation

`TLProgram.compileToScheduled` must return a schedule produced from `finalizeScans` without invoking
`splitNonlins`.

`LinearProgram` currently differs from `ScanProgram` only by an unenforced prose invariant. Task 1
must stop using that invariant internally while preserving source compatibility for this slice:

- make `schedule` accept the post-`finalizeScans` logical program;
- make `splitNonlins` return the same schedulable program type for regression-only callers;
- retain `LinearProgram` as a deprecated compatibility alias to the schedulable scan-program type;
- update its six current matches across `Types.lean`, `Lowering.lean`, and `LoweringTest.lean`.

The logical scheduler continues to provide:

- stable topological ordering;
- cycle rejection;
- external-name calculation;
- explicit-size collection;
- preservation of unread secondary outputs.

Exact post-change examples:

```text
source ReLU statements:             1 logical scheduled statement
source softmax statements:          1 logical scheduled statement
ReLU followed by contraction:       2 logical scheduled statements
scan nonlinear base/recur body:     original logical statement counts
generated %nl names:                0
```

The API flip and production route wiring are one atomic change: `TLProgram.compile` must reuse this
logical scheduled boundary and call public `route`, which owns checked private physicalization and
then invokes `routeCore`, in the same Task 1 gate. The public equation
`compile = compileToScheduled >>= route` remains valid. There is no green intermediate architecture
in which `compileToScheduled` is logical but `compile` retains an independent old split route chain.

Removing `splitNonlins` changes the numeric state returned by `FreshM` because route-generated UIDs
are no longer minted. That counter is an implementation detail, not a stable compiled output:

- `compile` and `compileToScheduled >>= route` must return the same final state;
- results and errors remain deterministic for a given starting state;
- every failure before the former split phase preserves its exact old final state;
- after that phase, the former counter is intentionally not preserved on either success or failure;
- every explained delta equals exactly the number of removed nonlinear split mints reached by the old
  pipeline;
- common-domain error constructor, payload, and precedence remain unchanged;
- tests, caches, and documentation must not snapshot the obsolete numeric value.

The negative differential observed:

```text
one-nonlinearity success:     old state - new state = 1
two-nonlinearity cycle error: old state 4, new state 2
identity cycle error:         old state = new state = 2
```

Compensating UID mints solely to reproduce old failure counters is forbidden: it would preserve a
removed route-specific encoding and complicate future failure sites without semantic benefit.

### 2.2 Private physical route program

Add a private route-layer module, preferably `DSL/Pipeline/RouteFragments.lean`, containing conceptual
types equivalent to:

```text
RouteFragment:
  logicalIndex
  firstStep
  lastStep
  optional internalName

PhysicalRouteProgram:
  route-private ScheduledProgram
  one RouteFragment per logical statement
  proofs/checkable evidence for freshness, coverage, exits, and topology
```

The exact Lean representation may use arrays or lists to match adjacent routing code. Its constructor
must be private and proof-carrying (or expose an equivalent checked package whose evidence cannot be
discarded), and it must establish:

1. declarations, dtype environment, externals, and explicit sizes are unchanged;
2. fragments form a contiguous, nonempty partition of physical statements;
3. fragment order equals logical statement order;
4. identity plain assignments and scans have one physical step;
5. nonlinear plain assignments have exactly two ordered steps;
5a. every input class in §2.4's ten-class table is explicitly classified, and no class reaches a
    catch-all — in particular a nonlinear `.plain (.scatter …)` is rejected, never copied as one
    step, and `fragmentWidth` agrees with `physicalizeOne` on every class;
6. the first nonlinear step publishes only the private internal name;
7. the second publishes the logical output name;
8. private names are pairwise distinct and absent from every source declaration/read/write name;
9. scans and `scanPre` nodes, including opaque nested payloads, are copied byte-for-byte;
10. downstream logical reads resolve to the fragment exit.

The evidence above is consumed by checked construction and a physicalization-correctness/route-
equality theorem. The formal spike showed that it should not be falsely threaded through
`compile_wellFormed`, whose proof needs only successful `routeCore`, external-count equality, and
domain validation.

`PhysicalRouteProgram` is not checked Eval IR, a backend API, or a serialization format. It exists
only between public logical `route` and physical `routeCore`.

### 2.3 Collision-free route-local identifiers

The adapter must not reserve `%nl` or any user prefix.

Let `maxSourceNameLength` be the maximum character length among every tensor declaration, statement
write, and `read`/`unaryFn` tensor name in the logical schedule. The internal name for nonlinear
fragment ordinal `n` is a string of `#` characters of length:

```text
maxSourceNameLength + n + 1
```

Required facts:

- each internal name is longer than every source name;
- different ordinals yield different lengths;
- internal names are pairwise distinct;
- no generated name is external;
- no source-level validation rule or reserved prefix is needed.

The proof must use the same definition as the executable adapter. A fallback such as `%nlN` with an
unchecked freshness assumption is forbidden.

### 2.4 Physicalization algorithm

`physicalizeForRoute` consumes an already scheduled logical program in one left-to-right pass.

For an identity plain assignment:

```text
emit original statement
fragment = currentStep .. currentStep
```

For a nonlinear plain assignment:

```text
emit private producer:
  name/nonlinearity = internalName/identity
  body/aggregation  = logical body/aggregation
  slots             = logical slots with freeNorm degraded to free

emit logical consumer:
  name/nonlinearity = logical name/full logical nonlinearity, including any mask
  body               = one read of internalName at logical output coordinates
  aggregation        = sum
  slots              = logical slots

fragment = producerStep .. consumerStep
```

For `.scan` and `.scanPre`:

```text
copy node exactly
fragment = currentStep .. currentStep
```

**Every input class must be classified; no catch-all may absorb an unclassified one.** The three
cases above do not cover the constructor surface. `ScanStmt.plain` also admits `Stmt.scatter` and
`Stmt.recurMorphism`, and a `.scatter` carries its own `RHSExpr.nonlin`. Physicalization must
therefore classify all ten classes below, and the classification must be a deliverable — a table in
`LeanNCD/DSL/AGENTS.md` with **no cell reading "silently ignored"**:

| # | Input class | Reachable from surface `compile`? | Required handling |
|---:|---|---|---|
| 1 | `.plain (.assign …)`, `nonlin = .identity` | yes | copy, width 1 |
| 2 | `.plain (.assign …)`, `nonlin = .pointwise _`, **not** `slotsBecomeScatter` | yes | split, width 2 |
| 3 | `.plain (.assign …)`, `nonlin = .axiswise _ none`, **not** `slotsBecomeScatter` | yes | split, width 2 |
| 4 | `.plain (.assign …)`, `nonlin = .axiswise _ (some mask)`, **not** `slotsBecomeScatter` | yes | split, width 2; mask rides the consumer |
| 5 | `.plain (.scatter …)`, `nonlin = .identity` | yes | copy, width 1 |
| 6 | `.plain (.scatter …)`, `nonlin ≠ .identity`, **OR** `.plain (.assign …)`, `nonlin ≠ .identity` **AND** `slotsBecomeScatter` | **no** — `checkScatterNonlin` rejects both spellings first, byte-identical payload | **reject; never a silent copy.** At least two known doors closed (implementation review, 2026-08-26): an `.assign` with an `.affine` or diagonal LHS would otherwise take the split arm and silently drop the affine placement (`LHSSlot.toReadIdx` maps `.affine _ => none`). A third door — `.iterAt`/`.iterNext` LHS slots on a `.plain (.assign …)`, which `toReadIdx` also collapses, discarding the pinned literal/shift — is known open, not yet closed; see `LeanNCD/DSL/AGENTS.md`'s case table and the slice's SDD ledger for the reproduction. |
| 7 | `.plain (.recurMorphism …)` | no — `unsupportedRecurMorphism` | copy, width 1 (carries no `RHSExpr`) |
| 8 | `.scan …` (`isAffine = false`) | yes | copy verbatim, width 1 |
| 9 | `.scan …` (`isAffine = true`) | yes | copy verbatim, width 1 |
| 10 | `.scanPre …` | no from surface; yes hand-built | copy verbatim, width 1 |

Class 6 is the one this design previously left implicit, and it is unsound to leave to a catch-all.
Today's `splitStmt` handles it with `| .scatter .. => return [s]   -- always identity-nonlin here
(rejected upstream otherwise)`. That comment is accurate **today** for exactly one reason:
`splitStmt` is reachable only from `splitNonlins`, reachable only from the two `DSL/Compile.lean`
chains, both of which run `checkScatterNonlin` first. The predicate is sound by an *unenforced
call-site precondition*, not by its own text.

**This design changes the caller set that precondition depends on.** Public `route` now accepts a
logical `ScheduledProgram` from any caller — that is the point of this section — so a hand-built
logical schedule carrying a nonlinear `.scatter` never passes `checkScatterNonlin`, reaches the
catch-all, and is copied as one physical step. It then routes as **one** `BrBase` with the
nonlinearity absent from the categorical presentation, silently. If `fragmentWidth` carries the same
catch-all, `fragmentLayoutOk` agrees with the miscount and cannot detect it — so `physicalizeOne` and
`fragmentWidth` must be changed together.

Note that **no diff exhibits this**: `splitStmt`'s `.scatter` arm text does not change in this work.
Only the set of callers relying on its precondition changes. Rejecting is the correct resolution
because §1.6 places nonlinear scatter semantics out of scope, and "out of scope" must mean *reject*,
not *silently mis-route*. Reuse `unsupportedNonlinScatter` rather than minting a diagnostic: nothing
reachable from `compile` can hit it, so common-domain error precedence is unchanged.

Classes 8 and 9 carry a second, *intentional* divergence to pin in the same table so a later reader
does not read it as a defect: old `splitScan` splits nonlinearities **inside** scan base/recur
bodies; physicalization copies the scan node verbatim. That is the scan-semantics fix of §1.2, not a
regression. For routing it must be projection-equal, because scan routing uses a representative
statement and does not encode the body (§2.5). Assert both halves separately.

No physicalization case may:

- reorder logical statements;
- call scheduling;
- publish an internal name;
- alter external names or explicit sizes;
- alter declarations, dtype environment, aggregation, masks/predicates, affine reads, or opaque
  nested payloads;
- split scan bodies;
- inspect target capability policy.

Public `route` accepts a logical `ScheduledProgram`, checks/physicalizes it, and then calls
`routeCore`. The supported external pattern `compileToScheduled >>= route` remains valid. A
hand-built route-linearized schedule is no longer a supported public-`route` input; old/new
regression tests send the old split schedule through the physical `routeCore` test boundary.

Physical conservation and categorical representation are distinct contracts. The adapter preserves
every logical field before `routeCore`, but the current categorical projection intentionally omits:

- axiswise masks (`ScanStmt.toBrBaseP` uses only the operation tag);
- Iverson factors (`Factor.read?` contributes no routed read);
- dtype metadata (`BrBaseP` has no dtype and ACSet records reals);
- nested `scanPre` bodies (only the wrapper is routed/serialized).

Tests must assert both pre-route preservation and the current opacity. Equal route/ACSet outputs when
only an opaque field changes must be described as projection equality, never full semantic equality.

### 2.5 Categorical routing and proof boundary

The existing `routeCore` continues to consume a physical `ScheduledProgram`. Route specifications
remain stated over that physical input.

All existing `RouteSpec` theorem statements should remain unchanged, including:

- route step/routing lengths and indexed lookup;
- `buildStep` geometry, weave, and reindexing facts;
- `buildNameToStep` bounds;
- external-index injectivity and bounds;
- routable order and input-weave properties.

New adapter checks and lemmas own:

- field preservation;
- fragment coverage and contiguity;
- internal-name freshness and injectivity;
- fragment-exit lookup for every logical output;
- preservation of topological order;
- scan-node identity;
- exact route equality with the old split pipeline on their common accepted domain.

Freshness, coverage, contiguity, exit, and topology mutations must break checked physicalization or
the adapter-correctness/route-equality theorem. They do not need to break Agreement: the formal spike
proved that `routeCore_routable` already derives routed topology and that Agreement consumes only
successful physical routing.

Replace the internal agreement witness `compile_eq_route` with a witness that exposes:

```text
source compile
  -> logical ScheduledProgram
  -> PhysicalRouteProgram
  -> routeCore physical.scheduled
```

The formal spike compiled this witness and the unchanged public `compile_wellFormed` without
`sorry`. Agreement needs exactly:

- `routeCore physical.scheduled = .ok (tc.steps, tc.routing)`;
- `tc.nExternal = physical.scheduled.extNames.card`;
- `tc.wellFormedDom = true`.

`realizeCompiled`, realization definitions, and ACSet codec proofs must not depend on logical
fragment indices.

Current scan routing is opaque: it routes one `.scan` or `.scanAffine` node using a representative
statement and does not encode the nonlinear scan body. Copying a logical scan node therefore
preserves current categorical output. Structured scan bodies remain a separate future design.

### 2.6 Eval lowering and execution

Legacy Eval already evaluates an unsplit assignment in the correct order:

```text
contract body
-> resolve nonlinearity from logical slots
-> apply nonlinearity
```

Inside scans, `evalStmtSliceSeeded` removes seeded iteration axes before resolving the marked local
axis. With a logical statement there is no rank-reduced generated scratch to read through full-rank
coordinates.

Backend Plan already supports a hand-built unsplit top-level nonlinearity:

```text
residualize logical body to preactivationSlot
-> derive result signature
-> pointwise/axiswise to resultSlot
-> materialize logical name only
```

Make `nonlinResultSignature` the one owner of result shape/dtype derivation across top-level, base,
and recurrence lowering. For this slice it preserves the `f64` preactivation signature.

### 2.7 Scan block IR, allocation, and publication

`RawPlanBlock` must contain:

```text
BlockStep.assign
BlockStep.pointwise
BlockStep.axiswise
```

Rename `RawPlanBlock.assignments` to `steps`. `checkPlanBlock` continues using `checkStepGraph`.
`runDenseBlock` dispatches to existing checked assignment and nonlinearity workers. Every pointwise
or axiswise block source must be the destination of a preceding local assignment, never a block
capture or another nonlinearity node. Therefore any state-derived preactivation passes through an
assignment term and scan-history causality remains sound while inspecting only assignment terms.
This restriction matches every compiler-emitted nonlinear block in this slice and prevents a
capture -> nonlinearity -> assignment chain from laundering a look-ahead or deep-history read past
the causality checker.

The verified implementation point is the nonlinear node's block-specific `sourceCheck` in
`checkPlanBlock`. Do not modify generic `checkStepGraph`. Track preceding `.assign` destinations and
reject any other nonlinear source with:

```text
BlockError.nonlinearSourceNotLocalAssignment nodeIndex sourceSlot
```

Diagnostic order is normative:

```text
block outputs
  -> node context
  -> destination range/availability
  -> source range/availability
  -> nonlinear assignment-provenance
  -> nonlinear local check
  -> scan causality
```

After `assignments` becomes `steps`, `ScanPlanError.causalityFailure.stmtIndex` denotes the block-step
index, not the filtered assignment ordinal. Tests and diagnostics must pin that meaning.

For each logical scan statement:

- identity emits one assignment destination;
- nonlinear emits a preactivation destination followed by a result destination;
- every destination is allocated from current `blockSigs.size`;
- source indices and logical ordinals are diagnostic data, never slot arithmetic.

`retainedAxisPos` is the count of preceding `.free | .freeNorm` slots. Iteration slots do not count
toward the local tensor's nonlinearity axis.

Publication is normative:

| Surface | Preactivation | Result |
|---|---|---|
| Tensor signatures | Required | Required |
| Assignment destination | Required | Forbidden |
| Nonlinearity source | Required | Forbidden |
| Nonlinearity destination | Forbidden | Required |
| Top-level binding/materialization | Forbidden | Required |
| Recurrence scratch binding | Forbidden | Required, internal |
| Persistent-state block output | Forbidden | Required |
| State write source | Forbidden | Required |
| Base write source/output | Forbidden | Required |

Recurrence scratch results enter `scratchSlotOf` but not `RawPlanBlock.outputs`. Only values consumed
by base or state writes are published as block outputs. Construct `baseOutputs` and `stepOutputs`
explicitly; never derive them from `Array.range` or statement counts.

### 2.8 Oracle and differential boundaries

The independent scan unroller must not import Plan compilation or route-fragment helpers.

It must support:

- `.freeNorm` as a retained local axis marker;
- nonlinear base assignments;
- nonlinear recurrence statements;
- leading/interleaved retained axes;
- coupled state and scratch dependencies.

The exact pointwise and axiswise histories in Section 1.2 are mandatory oracle fixtures.

The independent-oracle spike confirmed that the existing scan-free leaf evaluator already preserves
and applies logical `RHSExpr.nonlin`. The minimal unroller change is two match alternatives:

- `buildGeom` accepts and preserves `.freeNorm`;
- `baseFreeSlots` accepts and preserves `.freeNorm`.

Six fixture groups—leading pointwise, interleaved axiswise, leading persistent nonlinear, nonlinear
base, scratch-to-scratch-to-state, and coupled states—must remain independent regression coverage.
Wrong retained-axis mapping, skipped nonlinearity, preactivation publication, and base/result
confusion are the four required oracle mutations.

Differential comparison uses source-visible names:

- original input names;
- logical scheduled outputs;
- checked Plan materialized names;
- exact warning order.

There are no generated scheduled names to ignore. A missing logical result must fail.

The generated scan-free corpus currently has 3,832 accepted cases but no nonlinear pairs; it remains
a general semantic regression gate, not evidence for nonlinear lowering. The 17-case scan corpus is
expected to move from 9 accepted / 4 nonlinear rejection / 4 aggregation rejection to:

```text
13 accepted / 0 nonlinear rejection / 4 aggregation rejection
```

A separate durable nonlinear route corpus owns adapter coverage: 145 deterministic cases across 13
families, of which 137 lie in both pipelines' accepted domain and must have exact complete
`ThreadedComposed` and ACSet equality. The remaining eight deliberately use escaped `%nl0` source
names: the old generated-name pipeline rejects them through collision-induced cyclic dataflow, while
the logical pipeline correctly accepts them. Equality claims are therefore common-domain claims, and
new acceptance of those eight cases is an intentional bug fix rather than a regression.

A separate 19-case compile diagnostic corpus owns failure compatibility:

- 14 exact old/new results or errors, including final state;
- three successful one-nonlinearity programs with equal values and exactly one removed mint;
- one two-nonlinearity cycle with the same `cyclicDataflow` error and old/new states `4/2`;
- one `%nl2` collision with intentional old rejection and new acceptance.

The corpus is exact and reproducible below; `@n` means final FreshM state `n`, and `same value`
requires exact `ThreadedComposed` equality:

| # | Donor/construction | Old expectation | New expectation |
|---:|---|---|---|
| 1 | Direct `Y[i] := Ghost[i]` with no declaration (`Ghost` becomes external) | success `@2` | same value `@2` |
| 2 | Clone `StructuralTest` declared-rank mismatch | `rankMismatch "W" 2 1 @3` | exact same |
| 3 | Exact surface program `A[i] := X[i]; B[i] := X[i,j]` | `rankMismatch "X" 1 2 @3` | exact same |
| 4 | Combine fixture 2 with `StructuralTest`'s nat-`.freeNorm` defect | `rankMismatch "W" 2 1 @4` | exact same |
| 5 | Exact surface program `axis m : ℕ; Y[m.] := softmax(X[m])` | success `@3` | same value `@2` |
| 6 | Clone `StructuralTest` nat-`.freeNorm` programmatic case | `normAxisNotReal "m" @2` | exact same |
| 7 | Clone `StructuralTest` real-valued iteration-axis case | `iterAxisNotNat "l" @2` | exact same |
| 8 | Clone `StructuralTest` predicate-nonlinearity case | `predicateNonlin "P" @2` | exact same |
| 9 | Clone `MaxReduceTest` predicate-aggregation case | `predicateAgg "P" @2` | exact same |
| 10 | Clone `ScatterNonlinRejectTest.RSN1` | `unsupportedNonlinScatter "Out" @2` | exact same |
| 11 | Clone `StructuralTest` scatter-in-scan case | `scatterInScan "Out" @3` | exact same |
| 12 | Clone `IterDeclTest` undeclared scan-axis case | `scanAxisNotIter "l" @4` | exact same |
| 13 | Clone `RejectTest.SS4` | `causalityViolation "S" @4` | exact same |
| 14 | Clone `RejectTest.UF5` | `scanProjectionUnsupported "y" @5` | exact same |
| 15 | Clone `LoweringTest` identity `A <-> B` cycle | `cyclicDataflow "schedule: cyclic dataflow" @2` | exact same |
| 16 | Change both fixture-15 RHSs to ReLU | same cycle error `@4` | same error `@2` |
| 17 | Exact surface program `A[q,s.] := softmax(where s ≤ q)(Q[q,d] · K[s,d])` | success `@5` | same value `@4` |
| 18 | Clone the one-ReLU source, changing only its output tensor name to a long all-`#` name | success `@3` | same value `@2` |
| 19 | Programmatic escaped `%nl2[i] := X[i]; Y[i] := relu(%nl2[i])` | `cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)" @3` | success `@2` |

Two direct route-domain failures, both started at state 7, must also remain exact:
`undeclaredName "Ghost"` with no external declaration and the existing `wellFormedDom`
`shapeMismatch` with an unused external. The compile/route layer has no warning channel
(`FreshM` carries `CompileError` and state only); warning-order comparison belongs to the
warning-bearing Plan/Eval differential.

For compile cases 1, 2, and 16, also start at states `0`, `7`, and `41` and require exact
result/error/final-state equality between new `TLProgram.compile` and
`compileToScheduled >>= route`. These nine observations are composition checks, not additional
corpus cases.

Three implementation mutations give this corpus teeth: change the production rank-error
constructor/payload, swap `checkReadRanks` and `checkDtypes`, and corrupt successful routed
`nExternal`. Each must fail exact result/error/state comparison.

### 2.9 Future compatibility and alternatives

The logical schedule is the extension boundary for future source semantics. Checked positional Plan
IR is the backend execution and serialization boundary. `PhysicalRouteProgram` is private routing
machinery.

Compatibility policy:

- public `compileToScheduled >>= route` remains supported;
- public `route` now expects logical schedules and physicalizes privately;
- `LinearProgram` remains a deprecated alias for this slice;
- direct callers that manually construct split physical schedules must move to logical schedules;
- no built-in `ScheduledProgram` serializer exists, but external structural caches/snapshots will
  observe fewer statements and no generated names;
- the FreshM final counter is not preserved, as specified in Section 2.1.

Future feature impact:

- new pointwise/axiswise functions extend terminal lowerings;
- unary factors extend contraction residualization;
- max/min extend contraction algebra;
- masks/predicates extend nonlinearity payload and workers;
- dtype-changing operations update the shared signature rule;
- nonlinear scatter remains separate because before/after placement and collision reduction differ.

The slice may regression-test masks, Iverson predicates, predicate/tensor dtype environments,
programmatic nonlinear max/min, and `scanPre` at the route-adapter boundary without admitting any of
them to checked EvalPlan execution. Programmatic `relu(maxreduce(...))` and
`relu(minreduce(...))` test payload conservation but do not change surface grammar.

Rejected alternatives:

- **Keep the three-step Plan:** retains a full-shape identity copy.
- **Fuse one `BrBase`:** loses the correct categorical factorization.
- **Neutral split-pair schedule:** requires namespace, protocol, diagnostic, legacy, and oracle
  reconstruction machinery.
- **Directly generalize `routeCore`:** forces widespread logical-index/physical-index proof changes.
- **Second scheduler:** creates permanent schedule-agreement obligations.
- **Structured categorical scans now:** substantially broadens `Target`, realization, proof, and ACSet
  scope without changing current observable categorical behavior.

## 3. Detailed implementation plan

### 3.1 Dependencies and global constraints

Task 1 is one atomic architecture gate. Tasks 2 and 3 depend on Task 1 completing its day-5 green
gate. Task 4 depends on Task 3's general `BlockStep` vertical slice. Task 5 depends on Tasks 2 and 4
(and therefore transitively on Task 3). Task 3 is architecturally fallback-compatible, but this
execution plan does not authorize starting or landing it before Task 1 succeeds.

Post-spike ownership is explicit:

| Learning | Mandatory implementation change | Owning task |
|---|---|---:|
| FreshM changes also occur on post-split failures | Exact 19-case diagnostic, two-case route-domain, and public-composition state gates; no compensating mints | 1 |
| Logical fields may be categorically opaque | Preserve every physical payload field and distinguish conservation from projection equality | 1 |
| The generated route corpus does not cover payload semantics | Keep the 145/137 generated counts and add a separate 19-case named payload matrix | 2 |
| Assignment-only causality needs producer-kind evidence | Enforce preceding-local-assignment provenance in block-specific nonlinear `sourceCheck` | 3 |
| The checked-node migration has a safe compiler-derived order | Follow the seven-step migration sequence and retain block-step diagnostic indices | 3 |
| Payload tests must not widen backend admission | Continue admitting only unmasked pointwise/axiswise `f64` in checked EvalPlan | 4 |
| Projection limits must remain visible after implementation | Document mask, predicate, dtype, and `scanPre` opacity without claiming semantic equality | 5 |

Global constraints:

- exactly one scheduling pass;
- no generated name in `compileToScheduled`;
- no user namespace reservation;
- route fragments split only top-level `.plain` nonlinear assignments;
- scan nodes remain route-opaque and byte-for-byte copied;
- physicalization preserves every logical payload field before `routeCore`;
- route/ACSet equality describes the existing categorical projection, not fields that projection
  structurally omits;
- existing `routeCore` and `RouteSpec` theorem statements remain unchanged;
- current routed presentations remain exactly equal on both pipelines' common accepted domain;
- escaped `%nl0` source names rejected only by the old generated-name collision become accepted;
- top-level source nonlinearities produce exactly two Plan steps;
- admitted nonlinear scan statements produce exactly two block steps;
- preactivations are never materialized, published, or state-written;
- no new checked EvalPlan/backend capability is admitted beyond unmasked pointwise/axiswise `f64`;
- route-adapter regression tests may use already accepted masks, predicates, dtype metadata,
  programmatic nonlinear max/min, and `scanPre` without admitting their execution;
- full Tests and `LeanNCD` builds gate every task;
- Task 1 is governed by the day-3 checkpoint and day-5 gate in Section 4.2;
- no Task 1 intermediate commit may change the logical API without simultaneously preserving
  `compile = compileToScheduled >>= route`, where public logical `route` performs checked
  physicalization and invokes existing `routeCore`, plus the public `compile_wellFormed` result and
  the independent scan-oracle guards;
- helpers may be prepared privately inside Task 1, but the architecture flip, production adapter
  wiring, proof repair, and any oracle-guard migration land atomically.

The required import graph is acyclic and exact at the new boundary:

```text
DSL/Ast.lean                         (pipeline root)
  <- DSL/Pipeline/Types.lean         (imports Ast)
       <- DSL/Pipeline/RouteFragments.lean (imports Types only)
            <- DSL/Pipeline/Lowering.lean  (imports RouteFragments)
```

`RouteFragments.lean` must not import `Lowering`, `Structural`, or any `Eval` module. If
`LHSSlot.toReadIdx` is required by both route physicalization and lowering, Task 1 moves it to
`DSL/Ast.lean`; it must not create a reverse import.

### 3.2 Task and risk summary

| Task | Deliverable | Planned fixtures / mutation cycles | Risk |
|---|---|---:|---|
| 1 | Atomic logical boundary, physical adapter, public API compatibility, decisive route equality, and Agreement restoration | 12 architecture fixtures plus a nonlinear-scatter rejection fixture, 19 compile and 2 route-domain differential cases / 15 cycles; full API-census verification | High integration risk; formal proof and diagnostic feasibility established |
| 2 | Durable 145-case route corpus plus 19 named payload-conservation fixtures, scan opacity, realization, and ACSet regression | 13 generated families plus 19 named fixtures / 12 cycles | High categorical regression value; opacity boundary is explicit |
| 3 | General `BlockStep` vertical slice with nonlinear-source causality guard | 9 fixtures / at least 6 cycles; 47 field occurrences on 46 code lines | High checked-IR blast radius; rehearsal bounds work at 1.5-2 days |
| 4 | Nonlinear scan admission, independent oracle, allocation, and publication | 19 cross-layer fixtures including 6 oracle groups, plus 17-case corpus / 13 cycles | Highest runtime semantic risk |
| 5 | Differential, stale-document repair, and whole-branch closure | 5 differential fixtures / 3 cycles | High verification value |

Estimated effort is **13-18 focused engineer-days** for one engineer familiar with the compiler,
including reviews and mutation verification.

Every mutation cycle in this plan means exactly: make one stated mutation in the implementation
under test (production code, or the independent oracle when testing the oracle's teeth), **observe
failure**, **restore**, and **observe pass** in the same named fixture, proof, or documentation gate.
Merely predicting a failure or mutating the assertion does not count.

### 3.3 Task 1: atomic architecture gate

> **Executable plan (2026-08-26):** Task 1 has its own slice plan,
> [`leanncd/docs/superpowers/plans/2026-08-26-nonlinearity-t1-logical-schedule.md`](../leanncd/docs/superpowers/plans/2026-08-26-nonlinearity-t1-logical-schedule.md),
> per CLAUDE.md Rule 13 (one implementation plan per slice). It decomposes this task into three
> dispatchable sub-tasks — the `RouteFragments` module, the atomic flip, and the diagnostic
> differential — and maps this section's fourteen mutation cycles onto them 1:1 with none dropped.
> **Atomicity is unchanged**: the sub-tasks share one branch, and the logical API flip, route wiring,
> and Agreement repair still land together in the second of them. The separation exists because
> route equality can be established *before* the flip (compare `splitNonlins → schedule → routeCore`
> against `schedule → physicalizeForRoute → routeCore`), which makes the module independently
> reviewable. Sections 2 and 4 of this document remain the governing contract; Tasks 2-5 below stay
> unplanned until that slice lands.

**Outcome**

Within one architecture gate, `compileToScheduled` becomes logical, a proof-carrying private
`PhysicalRouteProgram` is added, public `route` physicalizes logical schedules, production `compile`
reuses `compileToScheduled >>= route`, the categorical agreement witness is restored, and all
affected oracle guards remain valid.

**Acceleration artifacts**

Begin with the [Task 1 production-code transplant](#task-1-production-code-transplant) and
[Task 1 diagnostic transplant](#task-1-diagnostic-transplant) instructions in Section 1.3.1. The
adapter donor supplies compiled declaration/proof shapes; the diagnostic donor supplies exact
observations and states. Do not independently redesign those pieces unless production integration
invalidates a recorded donor assumption, and record any such divergence before proceeding.

**Files**

- `leanncd/LeanNCD/DSL/Ast.lean` (only if moving `LHSSlot.toReadIdx`)
- `leanncd/LeanNCD/DSL/Pipeline/Types.lean`
- `leanncd/LeanNCD/DSL/Pipeline/RouteFragments.lean` (new in this task)
- `leanncd/LeanNCD.lean` (explicit import, so the new module is reachable from `import LeanNCD`
  rather than only transitively through `Lowering`)
- `leanncd/LeanNCD/DSL/AGENTS.md` (phase-table row plus Section 2.4's ten-class case table)
- `leanncd/LeanNCD/DSL/Pipeline/Lowering.lean`
- `leanncd/LeanNCD/DSL/Compile.lean`
- `leanncd/LeanNCD/DSL/Pipeline/RouteSpec.lean`
- `leanncd/LeanNCD/Bridge/Agreement.lean`
- `leanncd/LeanNCD/Eval/Entry.lean` (verification first)
- `leanncd/LeanNCD/Eval/Eval.lean` (verification first)
- `leanncd/LeanNCD/Eval/Scan.lean` (split-specific comments and verification)
- `leanncd/lakefile.toml`
- `leanncd/test/Eval/PropertyOracle/ScanUnroll.lean` (if the logical boundary changes its guard input)
- `leanncd/test/Eval/PropertyOracle/ScanOracle.lean` (same condition)
- `leanncd/test/DSL/Pipeline/LoweringTest.lean`
- `leanncd/test/DSL/Pipeline/RouteWeaveTest.lean`
- `leanncd/test/DSL/Pipeline/RouteFragmentDiagnosticTest.lean` (new)
- `leanncd/test/DSL/Pipeline/ScanAffineTest.lean`
- `leanncd/test/Bridge/AgreementTest.lean`
- `leanncd/test/Bridge/AcsetCodecTest.lean` (verification only)
- `leanncd/test/Eval/Plan/NonlinCompileTest.lean`
- `leanncd/test/Eval/Plan/DifferentialTest.lean`
- `leanncd/test/Eval/EntryTest.lean`
- `leanncd/test/Eval/Plan/AdapterTest.lean`
- `leanncd/test/Eval/Plan/CompileTest.lean`
- `leanncd/test/Eval/Plan/ContractTest.lean`
- `leanncd/test/Eval/Plan/SignatureTest.lean`
- `leanncd/test/DSL/CompileExamplesTest.lean`
- `leanncd/test/Eval/PropertyOracleScanTest.lean`
- `leanncd/experiments/jax_bridge/EvalPlanSmoke.lean` (verification)
- `leanncd/experiments/jax_bridge/EvalPlanAffineSmoke.lean` (verification)
- `leanncd/experiments/jax_bridge/EvalPlanAffineCorpus.lean` (verification)
- `leanncd/experiments/jax_bridge/EvalPlanCodegen.lean` (verification)

**Implementation**

1. Make `schedule` accept logical post-`finalizeScans` statements; retain `LinearProgram` as a
   deprecated compatibility alias during this slice.
2. Keep `splitNonlins` as a non-production regression/fallback helper.
3. Add `RouteFragments` under the exact import graph above. Inventory every declaration/read/write
   name, generate strictly longer ordinal-distinct `#` names, and split only nonlinear top-level
   `.plain .assign` statements in one left-to-right pass. Copy `.scan` and `.scanPre` exactly.
4. Make `PhysicalRouteProgram` private and proof-carrying (or equivalently checked), including
   declaration/environment/external preservation, fragment nonemptiness/coverage/contiguity,
   freshness/injectivity, unique logical exits, and physical topological order.
5. Extract one source-to-logical-schedule chain. Make public `route` checked-physicalize a logical
   schedule and call `routeCore`. Flip `compileToScheduled` and production `compile` together so the
   public `compileToScheduled >>= route` factorization remains valid. Do not retain a second
   scheduler or old production route chain.
6. Keep existing `RouteSpec` statements unchanged. Port the spike's proven
   `compile_eq_physical_route` witness and restore the unchanged public `compile_wellFormed`.
   Agreement uses only successful `routeCore`, external-count equality, and domain validation.
   Adapter evidence is consumed by checked physicalization and route-equivalence tests/theorems.
7. Preserve capability, shape, input, cycle, external-name, and output ordering. The compile layer has
   no warnings; preserve warning order at the later Plan/Eval boundary. Update top-level Plan
   expectations from three steps to two through the existing unsplit path.
8. Update `ScanUnroll`/`ScanOracle` guards in this same gate if they observe scheduled input shape;
   preserve oracle independence and do not import route or Plan helpers.
9. Apply the FreshM-state policy in Section 2.1 and add exact regression for
   `compile = compileToScheduled >>= route`, including final state.
10. Verify the API census sites: 27 test calls, 4 experiment calls, and on the production side the
    single runtime caller (`Eval/Entry.lean`) plus the seven `Bridge/Agreement.lean` proof
    references — see the unit correction in Section 1.3 item 9 before sizing this.
11. Preserve complete physical payloads separately from current categorical projection. Do not claim
    that route/ACSet equality represents masks, Iverson predicates, dtypes, or nested `scanPre` bodies.
12. Add the 19-case compile and two-case direct-route differential from Section 2.8. Common-domain
    constructor, payload, precedence, and pre-split state must match exactly; post-split state deltas
    must equal removed mints. The compile layer has no warning channel. Register the new diagnostic
    module in the `Tests` lakefile globs.

**Fixtures and donors**

1. `NonlinCompileTest.reluProg`: one logical statement, no generated name, and two Plan steps; clone
   its source construction locally in `RouteWeaveTest` for old/new route equality rather than
   importing a test module.
2. `NonlinCompileTest.softmaxProg`: the axiswise equivalent, cloned locally for route equality.
3. ReLU followed by downstream contraction: exact complete `ThreadedComposed` equality and correct
   fragment-exit lookup.
4. Two nonlinear branches feeding a join: logical order, private-name injectivity, and route equality.
5. Unread secondary nonlinear output: survives scheduling and physicalization.
6. Add a named, public axiswise source fixture in `RouteWeaveTest` from source syntax; assert
   `.freeNorm` degradation, collision-free physicalization, and exact route equality. Task 2 reuses
   this fixture's source construction.
7. Clone the private `DSL/Pipeline/ScanAffineTest.reluScan` source construction where a ReLU scan is
   needed; do not cite or expose the private definition as a reusable symbol. Assert unsplit logical
   body counts and one opaque copied physical scan node.
8. Reuse fixture 6's named axiswise source construction inside a recurrence; assert one opaque copied
   scan node.
9. Clone public `ScanCompileTest.coupledSched`/`coupledInputs` constructions locally for coupled
   oracle/guard coverage; do not import the test module.
10. Adversarial long-`#` source names: generated names remain absent from the source set.
11. Existing identity schedule: unchanged step, slot, and routed values.
12. Add an exact-type regression in `Bridge/AgreementTest.lean` for the unchanged public
    `compile_wellFormed` statement; no existing fixture currently guards that signature. Confirmed
    2026-08-26: `test/Bridge/AgreementTest.lean` is 12 lines and `#check`s only
    `@realize_fromThreadedComposed_agree`, `@agree_dom`, and `@agree_cod`, so a silent weakening of
    `compile_wellFormed` would currently go unnoticed. Follow that file's idiom:
    `#check @compile_wellFormed`.
13. Hand-built logical schedule carrying a nonlinear `.plain (.scatter …)`: physicalization rejects
    it (Section 2.4 class 6) rather than copying it as one step. This class is unreachable from
    `TLProgram.compile` — `checkScatterNonlin` rejects first — so the fixture must construct the
    schedule directly and call public `route`, which is precisely the surface this work widens.

Diagnostic differential donors. **Paths verified 2026-08-26** — three of these are not in the
directory their bare name suggests, so they are given in full here:

- clone rank/dtype/predicate/scatter fixtures from `test/DSL/Pipeline/StructuralTest.lean`;
- clone the predicate-aggregation case from `test/DSL/MaxReduceTest.lean` (**not** under
  `test/Eval/Plan/`);
- clone the undeclared scan-axis case from `test/DSL/IterDeclTest.lean`;
- clone `RSN1` from `test/Eval/Portfolio/ScatterNonlinRejectTest.lean` (**not** under
  `test/DSL/Pipeline/`);
- clone `SS4` and `UF5` from `test/Eval/Portfolio/RejectTest.lean` (**not** under
  `test/DSL/Pipeline/`);
- clone the identity cycle from `test/DSL/Pipeline/LoweringTest.lean`, then add the two-ReLU
  `A <-> B` cycle;
- clone the masked-attention statement from `test/Bridge/AcsetCodecTest.lean` guard 2, omitting its
  tensor declaration so it is exactly case 17 in Section 2.8;
- add the exact `%nl2`, long-`#`, route-domain, and composition cases from Section 2.8.

**Mutation checks**

- Reinsert `splitNonlins` into `compileToScheduled`; logical-count/name fixtures fail.
- Use `maxLen` rather than `maxLen + ordinal + 1`; the collision fixture fails.
- Use one internal name twice; branch injectivity fails.
- Map a logical output to fragment entry; the downstream-chain route equality fails.
- Split a scan body; opaque-scan identity fails.
- Invoke `schedule` during physicalization; the no-second-scheduler guard fails.
- Remove internal-name freshness checking; checked physicalization or route equality fails.
- Remove fragment-coverage checking; checked physicalization or the coverage theorem fails.
- Remove fragment-exit checking; the downstream route-equality fixture fails.
- Reverse physical topology; checked physicalization or route equality fails.
- Restore the catch-all so a nonlinear `.plain (.scatter …)` is copied as one step instead of
  rejected (Section 2.4 class 6); the hand-built nonlinear-scatter rejection fixture fails. Mutate
  `physicalizeOne` and `fragmentWidth` together, since leaving both catch-alls in agreement is
  exactly the defect being guarded.
- Restore the old split-shape oracle guard after the logical flip; the oracle guard fails.
- Change the production rank-error branch to emit a different constructor/payload; the diagnostic
  differential fails.
- Swap production `checkReadRanks`/`checkDtypes`; the dual-defect precedence fixture fails.
- Corrupt successful routed `nExternal`; exact result comparison fails.

Each of these fifteen items is one production-mutation/observed-fail/restore/observed-pass cycle.
(The fifteenth, the class-6 catch-all, was added 2026-08-26 with Section 2.4's case table.)

**Day-3 internal checkpoint**

This is an internal checkpoint inside Task 1, not a task or merge boundary. By day 3, the adapter and
all collision/coverage/exit/topology proofs must compile without `sorry`; the import graph must match
the graph above; no scheduler call may exist in physicalization; and the five decisive equality cases
(ReLU, softmax, chain, named axiswise source, opaque scan) must pass. If not, stop under Section 4.2.

**Day-5 atomic green gate**

```bash
cd leanncd
"$HOME/.elan/bin/lake" build DSL.Pipeline.LoweringTest DSL.Pipeline.RouteWeaveTest DSL.Pipeline.ScanAffineTest
"$HOME/.elan/bin/lake" build DSL.Pipeline.RouteFragmentDiagnosticTest
"$HOME/.elan/bin/lake" build Bridge.AgreementTest Bridge.AcsetCodecTest Eval.Plan.NonlinCompileTest Eval.Plan.DifferentialTest
"$HOME/.elan/bin/lake" build DSL.CompileExamplesTest Eval.EntryTest Eval.Plan.AdapterTest Eval.Plan.CompileTest Eval.Plan.ContractTest Eval.Plan.SignatureTest
"$HOME/.elan/bin/lake" build Eval.PropertyOracle.ScanOracle Eval.PropertyOracleScanTest
"$HOME/.elan/bin/lake" build JaxExperiment
"$HOME/.elan/bin/lake" env bash experiments/jax_bridge/run-evalplan.sh
"$HOME/.elan/bin/lake" env bash experiments/jax_bridge/run-evalplan-affine.sh
"$HOME/.elan/bin/lake" env bash experiments/jax_bridge/run-evalplan-affine-corpus.sh
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

> **Known pre-existing gap (confirmed 2026-08-26, during the slice plan's Task 2):** `lake build
> JaxExperiment` fails in `experiments/jax_bridge/EvalPlanCodegen.lean` (stale `RawEvalPlan`/
> `CheckedPlanStepEvidence` field references), and this is **not** caused by this slice's work —
> `git diff` against every T1/T2 commit confirms `EvalPlanCodegen.lean` is untouched by either. It
> predates this branch, matching the "repair experiments/jax_bridge" item already open from the
> 2026-08-21 checkpoint. The `run-evalplan*.sh` scripts depend on `JaxExperiment` building and so
> also fail. This gate line item cannot go green until that separate, out-of-scope repair lands;
> everything else in this gate is unaffected and was independently verified green (`Tests` 8657
> jobs, `LeanNCD` 8543 jobs).

Require two reviews: one for logical/physical pipeline and route equality, one for proof evidence,
oracle guards, and unchanged public Agreement. Task 1 succeeds only when every command is green and no
intermediate commit exposes a broken architecture.

### 3.4 Task 2: durable nonlinear route corpus and realization regression

**Outcome**

The 145-case deterministic corpus proven by the spike becomes a durable test, alongside a separate
19-case named payload matrix. On the common accepted domain, scans remain opaque and complete route
presentations, domains, realization, and ACSet round trips remain exactly unchanged. The old
collision failures become explicit new acceptances, and fields omitted by the categorical projection
are nevertheless pinned before routing.

**Acceleration artifacts**

Begin with the [Task 2 corpus and payload transplant](#task-2-corpus-and-payload-transplant)
instructions in Section 1.3.1. Preserve the donor's generated family/count structure and named payload
fixtures; replace its local physicalizer with Task 1 production APIs rather than regenerating the
corpus or retaining parallel test-only routing logic.

**Files**

- `leanncd/lakefile.toml`
- `leanncd/test/DSL/Pipeline/RouteFragmentCorpusTest.lean` (new)
- `leanncd/test/DSL/Pipeline/RouteWeaveTest.lean`
- `leanncd/test/Bridge/AcsetCodecTest.lean`
- `leanncd/test/Bridge/RealizeTest.lean`

**Generated families**

Generate with deterministic code:

- chains of depths 1-4: 32 cases;
- contractions with zero/one/multiple reduction axes: 24;
- `.freeNorm` first/middle/last: 9;
- branches/joins: 8;
- repeated downstream reads: 8;
- unread secondary outputs: 8;
- adversarial long and escaped names: 8;
- deliberate `%nl0` source collisions: 8;
- nonlinear scan base: 8;
- nonlinear scan recurrence: 8;
- nonlinear statements around scans: 8;
- coupled scans: 8;
- multi-axis scans: 8.

Total: 145. Do not use private `ScanGen.template2`; clone public source constructions or construct
families locally. For the 137 cases accepted by both pipelines compare:

- complete `ThreadedComposed`;
- generator sequence and routing wires;
- external arity/domain, degrees, weaves, and reindexings;
- `wellFormedDom`;
- `Bridge/RealizeTest` realization output;
- ACSet encode/decode round trip.

For scans also assert unsplit logical counts, byte-for-byte physical scan identity, old/new routed
node equality, and absence of a structured categorical body. For the eight `%nl0` cases assert the
old collision-induced `cyclicDataflow` rejection and new logical-pipeline acceptance; do not weaken
the common-domain equality claim to pretend the old bug accepted them.

**Named payload-conservation matrix**

Keep these 19 named fixtures separate from the generated count so semantic overlap cannot inflate
the 145/137 totals:

- clone `NonlinCompileTest.reluProg`, changing only the tag to sigmoid, tanh, GELU, and leaky ReLU
  (four fixtures);
- clone `NonlinCompileTest.softmaxProg`, changing only the tag to normalize and L2-normalize
  (two fixtures);
- clone `LoweringTest` AGG1, constructing programmatic ReLU-over-max and ReLU-over-min
  (two fixtures; surface grammar remains unchanged);
- clone `AcsetCodecTest`'s causal-attention mask, then negate only the predicate (two fixtures);
- combine `ParsePredicatesTest.band` with the ReLU donor, then negate only the Iverson predicate
  (two fixtures);
- clone `CompileTest.acceptedSched`, changing declarations/environment to tensor and predicate
  metadata respectively (two fixtures);
- clone `LoweringTest`'s strided read for scale and shift, and
  `AcsetCodecTest`'s strided convolution for a general affine read (three fixtures);
- clone `RecurMorphismTest.stepTC`, changing only the nested operation and only the nested output
  weave (two adapter-local `scanPre` fixtures).

For operation tags, aggregation, and affine reads, require exact physical statements, generator
sequence, route, ACSet, and round-trip. For masks, Iverson predicates, dtype metadata, and `scanPre`,
require exact physical-field preservation plus an explicit assertion that changing only the opaque
field does not change the current route/ACSet projection. Do not call that semantic equivalence.
`scanPre` cases exercise hand-built adapter input; public `recurMorphism` rejection remains unchanged.

**Mutation checks**

- Route from fragment entry rather than exit: 64 corpus failures.
- Reuse one internal name: 48 failures.
- Reorder fragment steps: 113 failures.
- Recompute externals from private reads: 113 failures.
- Split nested scan bodies: 32 explicit structural failures.
- Mishandle `.freeNorm`: 48 explicit structural/value failures.
- Drop nonlinear aggregation to sum; max/min physical and route assertions fail.
- Drop an axiswise mask; pre-route conservation fails even though current route remains equal.
- Change a nonlinearity tag; exact generator sequence fails.
- Clear declarations, environment, or explicit sizes; metadata conservation fails.
- Replace a nontrivial affine read by identity; exact reindexing fails.
- Replace a nested `scanPre` body by default; byte-for-byte payload conservation fails.

Each of these twelve items is one production-mutation/observed-fail/restore/observed-pass cycle.

**Gate**

```bash
cd leanncd
"$HOME/.elan/bin/lake" build DSL.Pipeline.RouteWeaveTest Bridge.AcsetCodecTest Bridge.RealizeTest
"$HOME/.elan/bin/lake" build DSL.Pipeline.RouteFragmentCorpusTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

Require two reviews: route/indexing equality and scan/realization/ACSet preservation.

### 3.5 Task 3: generalize Plan blocks

**Outcome**

`RawPlanBlock.steps : Array BlockStep` replaces assignment-only blocks. Checking, execution, and scan
causality support assign, pointwise, and axiswise nodes while every assignment-only plan remains
unchanged.

**Files**

- `leanncd/LeanNCD/Eval/Plan/RawStep.lean`
- `leanncd/LeanNCD/Eval/Plan/Block.lean`
- `leanncd/LeanNCD/Eval/Plan/Scan.lean`
- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/test/Eval/Plan/BlockTest.lean`
- `leanncd/test/Eval/Plan/NonlinCheckTest.lean` (fixture donor and verification)
- `leanncd/test/Eval/Plan/ScanTest.lean`
- `leanncd/test/Eval/Plan/ScanCompileTest.lean`

The `assignments` field has **47 occurrences on 46 code lines across the seven migration files above**
(all except verification-only `NonlinCheckTest`), including its declaration. This is the audited
migration inventory; it is not the former, incorrect count of 54 textual matches.

The full rehearsal found no additional production file and no import cycle. Its only non-mechanical
dependencies were the checked-node array type, `runDenseBlock`'s former `.plan` assumption,
assignment-only scan causality traversal, and test assertions over nested sum-wrapped steps. Budget
this task at **1.5-2 focused days**, including six mutation cycles and reviews.

**Implementation**

Follow the compiler-verified order:

1. Add `BlockStep`, its source/destination/context accessors, and rename
   `RawPlanBlock.assignments` to `steps` at all 47 field occurrences.
2. Add the `CheckedBlockStepEvidence` sum and precise `BlockError` cases, including
   `nonlinearSourceNotLocalAssignment nodeIndex sourceSlot`.
3. Migrate `checkPlanBlock` while continuing to delegate generic availability/production wiring to
   unchanged `checkStepGraph`. Enforce nonlinear provenance only in block-specific nonlinear
   `sourceCheck`, after range/availability and before local nonlinearity checking.
4. Migrate `runDenseBlock` to exhaustive checked-step dispatch using existing Dense workers.
5. Wrap compiler-produced assignments as `.assign`; do not admit nonlinear scan source yet.
6. Make scan causality inspect only `.assign` nodes after block checking, while retaining original
   block-step indices in `causalityFailure`.
7. Update fixtures and structural assertions. Pattern-match `Except` results rather than comparing
   them directly because checked blocks intentionally lack `BEq`; extract nested sum-wrapped steps
   before record-field assertions.

**Fixtures and donors**

1. Clone `BlockTest.stepBlock`; append pointwise execution.
2. Clone it again; append axiswise execution.
3. Clone `forwardReadBlock`; use an unproduced pointwise source.
4. Restore source production, then collide on its destination.
5. Clone `ScanTest.stepBlockLookAheadG`; replace its assignment with a pointwise node sourcing the
   captured state slot directly. Block checking rejects that source before scan causality can be
   bypassed.
6. Clone `ScanTest.stepBlockLookAheadG`; insert pointwise from the captured state slot and make the
   original look-ahead assignment consume the pointwise result. Block checking rejects this
   capture -> nonlinearity -> assignment laundering path.
7. Clone the pointwise fixture, then source an axiswise node from its nonlinear result;
   `nonlinearSourceNotLocalAssignment` rejects nonlinearity -> nonlinearity.
8. Clone `ScanTest.deepHistoryScan`; preserve its causal assignment read and append pointwise from
   that assignment destination. Block provenance and scan causality both accept it.
9. Clone `ScanTest.stepBlockLookAheadG`; append pointwise after the look-ahead assignment. Block
   provenance accepts the chain, then `checkScanPlan` rejects the assignment at its block-step index.

**Mutation checks**

At least six cycles are mandatory:

- remove the pointwise Dense dispatch arm;
- remove the axiswise Dense dispatch arm;
- route nonlinearity nodes through assignment checking;
- remove the shared pointwise/axiswise preceding-local-assignment guard; direct capture, laundering,
  and nonlinear-chain fixtures 5-7 become incorrectly accepted;
- revert causality filtering for look-ahead history;
- revert causality filtering for deep-history reads.

Each item is one production-mutation/observed-fail/restore/observed-pass cycle.

**Gate**

```bash
cd leanncd
"$HOME/.elan/bin/lake" build Eval.Plan.BlockTest Eval.Plan.NonlinCheckTest Eval.Plan.ScanTest Eval.Plan.ScanCompileTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

Require two reviews because this changes the checked-node sum and all block dispatch. Although this
task can survive an architecture fallback in principle, it must not start before Task 1's gate in this
plan.

### 3.6 Task 4: admit nonlinear Plan scans

**Outcome**

Logical pointwise and axiswise base/recurrence statements compile and execute through checked block
steps. Only result slots are bound, published, or state-written. Legacy Eval, checked Plan, and the
independent oracle agree.

**Files**

- `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- `leanncd/test/Eval/Plan/CompileTest.lean`
- `leanncd/test/Eval/Plan/ScanCompileTest.lean`
- `leanncd/test/Eval/Plan/ScanTest.lean`
- `leanncd/test/Eval/Plan/DifferentialTest.lean`
- `leanncd/test/Eval/PropertyOracle/ScanUnroll.lean`
- `leanncd/test/Eval/PropertyOracle/ScanOracle.lean`
- `leanncd/test/Eval/PropertyOracleScanTest.lean`

**Implementation**

1. Admit unmasked pointwise/axiswise logical scan statements and `.freeNorm`.
2. Reuse top-level nonlinearity signature and chain helpers.
3. Implement `retainedAxisPos` over `.free | .freeNorm`.
4. Update output shapes, base writes, recurrence writes, and scratch context-axis checks.
5. Allocate every physical destination from current signature count.
6. Emit one block step for identity and two for nonlinear statements.
7. Bind recurrence scratch names to result slots while keeping them internal.
8. Publish only base/state-write result slots through explicit output arrays.
9. Keep masked axiswise rejection at nonlinearity resolution.
10. Extend the independent unroller without importing Plan or route helpers: add only `.freeNorm`
    preservation alternatives to `buildGeom` and `baseFreeSlots`; existing leaf evaluation already
    handles logical nonlinear expressions.
11. Rebaseline the 17-case corpus to 13/0/4 only after observing that exact split.

**Fixtures and exact donors**

- Clone the private `DSL/Pipeline/ScanAffineTest.reluScan` source construction locally wherever a
  ReLU scan source is required.
- Use public `ScanCompileTest.coupledSched` and `coupledInputs` for coupled cases.
- Reuse Task 1's named axiswise source fixture construction for axiswise cases.
- Use existing `ScanCompileTest.scratchSched`, `multiBaseSched`,
  `NonlinCompileTest.sampleMask`, and `NonlinDenseTest.axiswisePlan` where applicable.
- Do not cite private `ScanGen.template2` as directly reusable.

Positional/execution fixtures:

1. `G[l+1,j.] := softmax(...)`; local axis position 0.
2. Interleaved iteration/local axes with marker in the middle.
3. Marker last among several local axes.
4. Leading-axis pointwise exact history from Section 1.2.
5. Interleaved axiswise exact history from Section 1.2.

Publication/dependency fixtures:

6. Nonlinear scratch consumed by later scratch.
7. Nonlinear scratch consumed by state.
8. Persistent state's own nonlinear recurrence.
9. Coupled linear/nonlinear states.
10. Exact capture order after a nonlinear logical statement.

Base fixtures:

11. Pointwise nonlinear base with differing preactivation/result.
12. Nonlinear free-face plus point override.
13. Successful axiswise nonlinear base.

Negative/write-safety fixtures:

14. Masked axiswise base rejection.
15. Masked axiswise recurrence rejection.
16. `.freeNorm` with pointwise ReLU rejection.
17. `.freeNorm` context-axis scratch rejection.
18. State write pointed at preactivation while outputs retain result.
19. Mixed identity/nonlinear outputs contain results only.

The following six fixture groups must also execute through the independent oracle with the observed
values from the spike:

1. leading pointwise: `[2,3,20,300,200,30000]`;
2. interleaved axiswise:
   `G[0]=[1,2,-1,1]`,
   `G[1]=[.268941,.731059,.880797,.119203]`,
   `G[2]=[.386484,.613516,.991521,.008479]`;
3. leading persistent nonlinear: `[1,0,0,2,6,18]`;
4. nonlinear base: `[0,3,0,3]`;
5. scratch-to-scratch-to-state: `[1,5,5,2,0,0]`;
6. coupled states: `G=[1,0,0]`, `H=[1,1,0]`.

**Mutation checks**

- publish/write preactivation instead of result;
- remove retained-axis remapping;
- advance allocation by logical statement count;
- revert `.freeNorm` independently in output shape, base write, recurrence write, and scratch
  validation (four cycles);
- derive captures after rather than before allocation;
- reintroduce `Array.range` outputs.
- in the independent oracle only, use the wrong retained-axis mapping;
- in the independent oracle only, skip nonlinear leaf evaluation;
- in the independent oracle only, publish preactivation;
- in the independent oracle only, confuse base and result slots.

These are nine production and four independent-oracle
mutation/observed-fail/restore/observed-pass cycles.

**Gate**

```bash
cd leanncd
"$HOME/.elan/bin/lake" build Eval.Plan.CompileTest Eval.Plan.ScanCompileTest Eval.Plan.ScanTest Eval.Plan.DifferentialTest
"$HOME/.elan/bin/lake" build Eval.PropertyOracle.ScanOracle Eval.PropertyOracleScanTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

Require reviews for compiler allocation/axis mapping/diagnostics and for publication/oracle
independence/Dense semantics.

### 3.7 Task 5: differential documentation and closure

**Outcome**

All executable paths agree on source-visible results. Active documentation describes one logical
schedule and the private physical route adapter. Superseded plans keep permanent archival banners.

**Files**

- `leanncd/test/Eval/Plan/DifferentialTest.lean`
- `leanncd/test/DSL/CompileExamplesTest.lean` (split-specific comment)
- `leanncd/LeanNCD.lean`
- `leanncd/LeanNCD/Eval/AGENTS.md`
- `leanncd/LeanNCD/DSL/AGENTS.md`
- `leanncd/experiments/jax_bridge/README.md`
- `leanncd/realize.md`
- `leanncd/SORRY_INVENTORY.md`
- `papers/eval_ir.md`
- `papers/jax_evalplan_architecture.md`
- `papers/leanncd.md`
- `papers/code_walkthrough.md`
- `papers/NaperianTyping.md`
- `papers/NaperianTypingIntegrationPlan.md`
- `papers/copilot_code_analysis.md`
- `papers/restructure_suggestions.md`
- `papers/semantic_payload_audit.md`
- `papers/todo.md`
- `papers/wave_f_scanplan_proposal.md`
- `papers/nonlinearity_split_pair_direct_lowering.md`
- `docs/superpowers/specs/2026-06-12-lean-dsl-tensor-logic-design.md`
- `docs/superpowers/specs/2026-08-21-nonlinearity-in-scans-design.md`
- `leanncd/docs/superpowers/plans/2026-08-21-nonlinearity-in-scans.md`
- `leanncd/docs/superpowers/plans/2026-08-21-wiring-loop-generalization.md`

The wiring-loop plan is included because its active next-slice pointer sends readers to the
superseded nonlinearity plan. Preserve its completed historical record, but replace that pointer with
this plan.

Verification-only:

- `leanncd/test/DSL/Pipeline/RouteWeaveTest.lean`
- `leanncd/test/Bridge/AcsetCodecTest.lean`
- `leanncd/test/Bridge/AgreementTest.lean`
- `leanncd/test/Bridge/RealizeTest.lean`

**Implementation**

1. Add differential cases for persistent nonlinear state, interleaved axiswise recurrence,
   scratch-to-state, nonlinear base, and coupled states.
2. Compare exact source-visible keys and warning order; no generated-name projection is allowed.
3. Confirm the 3,832-case scan-free gate and 17-case 13/0/4 scan split.
4. Document logical scheduling, private proof-carrying physicalization, collision proof, opaque scans,
   public logical `route`, the deprecated `LinearProgram` alias, FreshM compatibility, Plan block
   steps, and checked/backend boundaries in every active architecture inventory above.
   Where a broader historical plan such as `NaperianTypingIntegrationPlan.md` is not otherwise being
   revised, replace only its active `splitNonlins` invariant with a dated pointer to this canonical
   boundary.
5. Retain permanent superseded banners on archived scan documents. Their status prose must direct all
   implementation work here and must not recommend neutral pairs, shared splitting, pair recognition,
   or redundant three-step lowering.
6. Append a completion record with commits, route equality, proof gate, corpus counts, fixture
   mutations, and review adjudications.
7. Run the active-document stale-recommendation scan below. It deliberately excludes this canonical
   decision record and archived plans, where rejected/historical terminology remains necessary.

**Mutation checks**

- remove one logical result from a differential report;
- compare preactivation instead of result;
- restore one prohibited multiline active pipeline form matched by the stale-recommendation scan.

Each item is one production-mutation/observed-fail/restore/observed-pass cycle; the third mutation is
to the production documentation inventory checked by the stale-recommendation gate.

**Gate**

```bash
cd leanncd
"$HOME/.elan/bin/lake" build DSL.Pipeline.RouteWeaveTest Bridge.AcsetCodecTest Bridge.AgreementTest Bridge.RealizeTest
"$HOME/.elan/bin/lake" build Eval.Plan.DifferentialTest Eval.PropertyOracle.ScanOracle
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
active_docs=(
  LeanNCD.lean LeanNCD/Eval/AGENTS.md LeanNCD/DSL/AGENTS.md
  experiments/jax_bridge/README.md realize.md SORRY_INVENTORY.md
  ../papers/eval_ir.md ../papers/jax_evalplan_architecture.md ../papers/leanncd.md
  ../papers/code_walkthrough.md ../papers/NaperianTyping.md
  ../papers/NaperianTypingIntegrationPlan.md ../papers/copilot_code_analysis.md
  ../papers/restructure_suggestions.md ../papers/semantic_payload_audit.md
  ../papers/todo.md ../papers/wave_f_scanplan_proposal.md
  ../docs/superpowers/specs/2026-06-12-lean-dsl-tensor-logic-design.md
)
if rg -n -U --multiline-dotall \
  'finalizeScans.{0,80}splitNonlins|splitNonlins.{0,80}(schedule|route|LinearProgram)|LinearProgram.{0,80}no nonlinearity|generated .?%nl.{0,80}(shared|scheduled|source-level)' \
  "${active_docs[@]}"; then
  echo "active documentation still recommends the superseded shared split pipeline" >&2
  exit 1
fi
```

Run two independent whole-branch reviews:

- logical scheduling, categorical adapter/proofs, and unchanged routed semantics;
- checked Plan allocation/publication, oracle independence, differential soundness, and stale-doc
  inventory.

Task 5's documentation edits themselves do not require a separate Lean run; the commands above are the
mandatory whole-branch closure gate after the implementation tasks.

## 4. Verification, completion, and fallback

### 4.1 Required verification record

The implementation is incomplete until its record contains:

- every task gate and full `lake build`;
- exact logical statement counts and absence of generated scheduled names;
- public `compile = compileToScheduled >>= route` result/error/final-state equality;
- verification of all production, test, and experiment callers from the API census;
- retention of the deprecated `LinearProgram` alias;
- every fragment interval and logical-output exit for regression graphs;
- collision proof results and adversarial-name fixture;
- Section 2.4's ten-class case table, every class classified, no cell reading "silently ignored",
  and the class-6 nonlinear-scatter rejection fixture and its mutation cycle;
- exact old/new `ThreadedComposed` equality for all 137 common-domain generated cases;
- intentional old-reject/new-accept results for all eight `%nl0` collision cases;
- all 19 named payload fixtures, distinguishing physical conservation from categorical opacity;
- all 19 compile-diagnostic and two route-domain differential results, including explained state
  deltas;
- route-domain, realization-where-shaped, and ACSet results;
- unchanged `RouteSpec` theorem statement inventory;
- restored public `compile_wellFormed`;
- exact Plan step/signature/materialization counts;
- exact pointwise and axiswise scan histories;
- 145-case route, 19-case payload, 19-case diagnostic, two-case route-domain, 3,832-case scan-free,
  and 17-case scan corpus results;
- every fixture and mutation cycle;
- both whole-branch review findings and adjudications.

### 4.2 Route-adapter time-box

The formal spike removed the primary Agreement-feasibility uncertainty: its physical witness and the
unchanged public `compile_wellFormed` compiled without `sorry`. Task 1's production integration is
still time-boxed to at most five focused days.

**By the end of day 3:**

- adapter compiles without `sorry`;
- collision proofs are complete;
- no scheduler call exists in physicalization;
- top-level and scan route regressions are exactly equal;
- the revised agreement-witness shape type-checks.

**By the end of day 5:**

- public `compile_wellFormed` is restored;
- route, bridge, scan, and ACSet gates are green;
- no existing `RouteSpec` theorem statement changed;
- no structured scan representation was introduced.

If either checkpoint fails, stop. Do not land a partial logical API flip, generalize `routeCore`,
extend categorical scans opportunistically, or revive the rejected shared-split/neutral-pair design.
Reassess the logical/private-physical boundary from the recorded proof obstruction before writing a
new plan.

### 4.3 Stop conditions

Stop and revise rather than improvise if:

- logical scheduling changes valid-program dependency order, externals, diagnostics, or outputs;
- physicalization invokes scheduling;
- internal identifiers can collide with any source name;
- a logical output cannot map uniquely to one fragment exit;
- new and old routed presentations differ on any of the 137 common-domain corpus cases;
- public `compileToScheduled >>= route` compatibility or final-state equality is lost;
- any common-domain error constructor, payload, or precedence changes;
- any pre-split failure state changes or any later state delta is not exactly the removed split mints;
- implementation attempts to preserve obsolete post-split counters through compensating UID mints;
- any physicalization input class in Section 2.4's ten-class table reaches a catch-all instead of an
  explicit classification, or `fragmentWidth` and `physicalizeOne` disagree on any class;
- closing class 6 (nonlinear `.plain (.scatter …)`) would change any diagnostic reachable from
  `TLProgram.compile`;
- physicalization changes or drops aggregation, masks, Iverson factors, dtype metadata, affine reads,
  or opaque `scanPre` bodies;
- route/ACSet equality is presented as evidence for a payload the categorical projection omits;
- any nonlinearity maps to the wrong `BrOp`;
- masked, predicate, Boolean, programmatic max/min, scatter-nonlinear, or `scanPre` execution becomes
  admitted to EvalPlan unintentionally;
- preserving route equality requires splitting scan bodies;
- any existing `RouteSpec` theorem statement must change;
- `compile_wellFormed` cannot be restored through a physical witness;
- assignment-only Plan blocks change after Task 3;
- scratch results must become block outputs to be consumed locally;
- a checked nonlinear block node can consume a capture or another nonlinear node directly;
- preactivation and result cannot be distinguished in base/state writes;
- the independent oracle must import Plan or route implementation;
- the 17-case corpus does not produce 13/0/4 after admission;
- differential comparison can pass with a missing logical result.

### 4.4 Definition of done

- `compileToScheduled` contains logical nonlinear assignments and no route-generated names.
- `TLProgram.compile = compileToScheduled >>= route`, including final FreshM state, and shares one
  logical scheduling pass.
- Public `route` accepts logical schedules and owns checked private physicalization.
- `LinearProgram` remains as a deprecated compatibility alias.
- Physical route fragments are private, contiguous, collision-free, and non-rescheduling.
- Every top-level nonlinear assignment routes as two necessary generators.
- All ten physicalization input classes of Section 2.4 are explicitly classified in
  `LeanNCD/DSL/AGENTS.md` with no cell reading "silently ignored"; class 6 rejects; `physicalizeOne`
  and `fragmentWidth` agree on every class.
- Routed presentations and existing categorical projections are unchanged on all 137 common-domain
  corpus cases; eight generated-name collision cases become newly accepted.
- All eight nonlinearity tags route correctly; programmatic max/min nonlinear ASTs route as
  maxreduce/minreduce followed by the nonlinear generator.
- Masks, Iverson factors, dtype metadata, affine maps, and nested `scanPre` bodies survive
  physicalization exactly; their existing categorical opacity is explicitly pinned.
- Scans remain one opaque categorical node.
- Existing `RouteSpec` statements and public agreement theorems remain stable.
- Top-level nonlinear Eval plans contain exactly assign plus pointwise/axiswise.
- Legacy nonlinear scans execute logical statements directly.
- Plan blocks check and execute assign, pointwise, and axiswise nodes.
- Checked block nonlinearities consume only preceding local assignment destinations, keeping
  assignment-only scan causality complete.
- Every admitted nonlinear scan statement emits exactly two block steps.
- Preactivations are never materialized, published, or state-written.
- Retained-axis mapping works for leading, interleaved, and trailing local axes.
- Legacy Eval, checked Plan, and independent oracle agree on all admitted source-visible results.
- The route, payload, diagnostic, route-domain, scan-free, and 17-case 13/0/4 scan gates are green.
- Full builds, all 49 mandatory mutation checks (14 + 1 for Section 2.4's class-6 catch-all in
  Task 1, 12 in Task 2, 6 in Task 3, 13 in Task 4, 3 in Task 5), and whole-branch reviews are green
  or adjudicated.
- Documentation contains no active recommendation for split-pair shared scheduling.

### 4.5 Future architecture triggers

Reconsider the boundary only if:

- a categorical consumer needs structured scan bodies;
- target-specific scheduling, rather than terminal lowering, becomes necessary;
- route fragments require more than local contraction/nonlinearity chains;
- fusion needs logical operations to survive checked backend lowering;
- `PhysicalRouteProgram` is proposed as public or serialized IR;
- nonlinear scatter semantics require placement-aware multi-stage fragments.

Until then, one logical schedule plus a private physical route adapter is the smallest architecture
that preserves categorical factorization, removes redundant Eval work, fixes scan semantics, and
keeps target divergence at the terminal lowering boundary.

# leanncd restructuring suggestions

> **✅ E1 "one traversal to rule the collectors" is COMPLETE and merged to `main` (2026-07-23).**
>
> Every AST node now has a single `NodeName.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec)`,
> instantiated three ways — `Id` (remap, `X.mapUID`), `ConstL (List AxisSpec)` (`specs*`),
> `ConstL (List UID)` (`*AxisUIDs`) — replacing the hand-written `mapUID`/`specs*`/`*AxisUIDs` families
> and the bespoke `TermTraversable` typeclass. `main` builds green.
>
> **Merged PRs:**
>
> - **#1** — E1 prototype: full-AST feasibility spike (`test/DSL/TraverseAxesSpike.lean`).
> - **#2** — sub-projects 1 & 2: migrate `specs*` (AxisSpec) and `*AxisUIDs` (UID) collectors to `traverseAxes`.
> - **#3** — sub-project 3: migrate the `mapUID` (remap) family to `traverseAxes @ Id`.
> - **#4** — sub-project 4: retire the vestigial `TermTraversable` typeclass (`assignUIDs` now calls
>   `TLProgram.mapUID`; `Exec/Traversable.lean` + unused `WithUID` deleted; no bespoke traversal
>   abstraction and no cross-layer `Eval.Contract` import remain).
> - **#5** — permanent Id/uid equivalence certificates (`test/DSL/TraverseAxesEquiv.lean`).
>
> **Standing, kernel-checked, per-node equivalence certificates (all three directions):**
> `traverseAxes_const_eq_specs*` (12, specs) in `TraverseAxesSpike.lean`; `*.mapUID_eq_ref` (12, remap)
> and `*AxisUIDs_eq_ref` (5 public uid collectors) in `TraverseAxesEquiv.lean` — each proves the
> production `traverseAxes`-instantiation equals an independent hand-written reference
> (`[propext, Quot.sound]` or fewer; no `sorry`). The `*AxisUidFusion` lemmas in `Structural.lean`
> additionally prove specs↔uid agreement per node.
>
> **Design/plan docs:** `docs/superpowers/specs/2026-07-1{5,6,7}-e1-*` (prototype slices; sub-project 1/2/3/4
> plans; scaffolding-refactor follow-up [DONE]; mapUID go/no-go spike). See the [E1](#e1-one-traversal-to-rule-the-collectors-van-laarhoven)
> section below for the original vision. No E1 follow-on work is outstanding.

A global review of `leanncd/` (~9,200 lines of Lean across 49 modules) after the recent wave of
feature fixes (`Factor.unaryFn` inline transcendentals, new `Nonlin` activations, `l2normalize`,
the friendly `/` operator, multi-axis scans, scan aggregators, the multi-output `schedule` fix,
and the scan-projection guard). Each fix was locally surgical; collectively they exposed
structural duplication that is now worth paying down. This document catalogs concrete
restructuring opportunities, organized into independently plannable spikes, ordered so that
earlier spikes reduce the cost and risk of later ones. Part I (Spikes 1–8) stays close to the
existing architecture; Part II (end of document) collects exploratory, higher-risk redesign
directions that deliberately go beyond it.

**Method.** Three parallel deep-reads (DSL pipeline, Eval interpreter, proof track + bridge),
each claim cross-checked against the code; the highest-leverage claims (dead code, exact
duplicates, hardcoded semiring constants) were re-verified independently. Everything below
carries `file:line` references against HEAD as of 2026-07-09.

## Terminal goal (2026-07-30): a PyTorch/JAX execution layer via `EvalPlan`

> **This section outranks the wave ordering below.** The eventual target is a real execution
> backend — PyTorch first (eager, for fast semantic bring-up; a `torch_compile/` prototype already
> exists in-repo), then JAX (stricter, static-shape, `lax.scan`) — both lowered from **one
> backend-neutral `EvalPlan`**, with the Lean `DenseTensor` evaluator retained as the small,
> inspectable reference semantics. See `copilot_code_analysis.md` Appendix A for the full design.
>
> ```text
> TLProgram → compile+validate → ScheduledProgram → EvalPlan
>                                                     ├→ DenseTensor reference worker
>                                                     ├→ PyTorch lowering → eager/compile
>                                                     └→ JAX lowering → jit → execute
> ```
>
> The governing rule: *"If JAX and PyTorch require different meanings for an `EvalPlan` constructor,
> the constructor is underspecified. Backend-specific optimization metadata is acceptable;
> backend-specific mathematical semantics is not."*

**Four consequences that reorder this document.**

**1. Spike 4 is not deduplication — it IS the backend contract.** Appendix A's Phase 1 is verbatim
"finish Spike 4's checked sizes, `Combine`, dtype-aware assignment, `ResolvedNonlin`, typed scatter,
structured errors, and `EvalReport`" — i.e. 4a, 4b, 4c, 4d, 4g, 4h, 4i are each a named prerequisite
for executing anything on a GPU. Spike 4 should be read as *the highest-priority remaining work*,
and its linear `4a→4b→4c→…` order is wrong. Use the dependency waves:

```text
4b → 4a → 4c                    (identities FIRST, then unify, then dtype-aware dispatch)
Spike 3a ✅ → ResolvedNonlin (4d) → 4c
4b + 4a + 4c + 4d → minimal EvalPlan → JAX/PyTorch stateless oracle
4g → EvalPlan scatter capability
4e diagnostic split → 4h → warning half of 4i
minimal EvalPlan + E2 recurrence → 4f → scan lowering
```

Two corrections to earlier advice in this doc: **4b precedes 4a** (both contraction identities must
exist before the seeded/unseeded merge), and **4f comes after the `EvalPlan` boundary**, not early as
a "safe decomposition" — the plan-level pure state transition must be defined first. And **4h is not
last**: structured errors are required to map Python/JAX exceptions into a closed `BackendError`
family *before the backend becomes public*.

**2. `E4` (EvalPlan) moves from "prototype-first" to the critical path; `E10` (codegen) from
"recorded-only" to the eventual deliverable.** `EvalPlan` is the semantic, versioned source of truth
— canonical, hashed (the hash is both the JIT cache key and the identity in backend errors),
serializable, and containing no Lean or backend callbacks. Generated Python is *one lowering*;
exported StableHLO is a *cache artifact*, not a semantics.

**3. `E5` splits into two axes with very different tractability — do not conflate them.**

| Axis | Status | Priority |
|---|---|---|
| eval ↔ **routed** (`BrMorph`) agreement | **Blocked, not merely unscheduled** — the routed path ends in a `Quotient` of raw syntax with *no denotation into numbers*; every `realize*` is `noncomputable`. Needs the `Br` interpreter, a separate deferred milestone. | Low |
| eval ↔ **backend** (`EvalPlan`→PyTorch/JAX) agreement | **Achievable now**, and it is the actual prize: a differential test matrix (emit → eager → jit → reference agreement → cross-backend → device → export → VJP). | **High** |

The first milestone is deliberately *not* "JAX runs a model." It is: *for the declared scan-free
`reference64` fragment, every checked `EvalPlan` either produces matching `DenseTensor` and
jitted-JAX outputs, or is rejected before backend execution with a typed capability error.*

**4. The payload audit's carry/reject decisions must target `EvalPlan`, not `BrBaseP`.** This is the
sharpest correction. Every payload [`semantic_payload_audit.md`](semantic_payload_audit.md) found
dropped is a **required `EvalPlan` field**:

| Audited payload | Required `EvalPlan` home |
|---|---|
| axiswise mask | nonlinearity step: *function, resolved axis, **mask**, exceptional-row policy* |
| `UnaryOp` | pointwise function step |
| `ScatterOpts.fill`/`.reduce` | scatter step: *destination map, output shape, **fill, collision operation**, OOB policy, injectivity* |
| `AggOp` + dtype | `ContractionAlgebra` (`factorOp`/`factorId`/`reduceOp`/`reduceId`) + `TensorSig.dtype : ScalarDType` |
| per-term contraction scoping | contraction step: *factors, **per-term reduction axes**, factor op/identity, term op/identity* |
| scan bodies | scan step: *ordered state signatures, **base plan, step plan**, static iteration shape/order, causality certification* |

So "reject routed" is at best a temporary staging device and never the long-term answer — you cannot
reject `log(X[i])` if the goal is to emit `torch.log`. Conversely, **carrying payload into `BrBaseP`
buys nothing for execution**: the routed path is a serialization/proof artifact for Python-acset
interop, not an execution IR. Appendix A's warning against routing JAX generation through `NetSpec`
("would create a second, semantically incomplete IR") applies with equal force to routing it through
`BrBaseP`. Expensive routed-side work — notably reworking `weaveToArrayType_congr` and
`Agreement.lean` conjunct-2 to admit a step-level dtype — should be **deferred** in favour of the same
classification landing in the shared contraction algebra and `EvalPlan`.

**What stays true from the 2026-07-26 addendum:** the demonstrated correctness bugs still come first
(they are Wave 1 of the revised Spike 4 sequencing: "freeze failures and policies"), and the
four-guarantee lens still applies — it now has a fifth consumer, since *backend* agreement is the
strongest available form of semantic closure.

## Table of Contents

- [Terminal goal (2026-07-30): a PyTorch/JAX execution layer via `EvalPlan`](#terminal-goal-2026-07-30-a-pytorchjax-execution-layer-via-evalplan)

- [0. Constraints — what must NOT be restructured](#0-constraints--what-must-not-be-restructured)
- [Wave 1 — mechanical deletions and corrections (near-zero risk)](#wave-1--mechanical-deletions-and-corrections-near-zero-risk)
  - [Spike 1: dead code, stale docs, housekeeping](#spike-1-dead-code-stale-docs-housekeeping)
- [Wave 2 — structural unification of the executable tracks](#wave-2--structural-unification-of-the-executable-tracks)
  - [Spike 2: one home for AST accessors and read/axis traversals](#spike-2-one-home-for-ast-accessors-and-readaxis-traversals)
  - [Spike 3: make the Nonlin wildcard hazards unrepresentable](#spike-3-make-the-nonlin-wildcard-hazards-unrepresentable)
  - [Spike 4: Eval interpreter unification](#spike-4-eval-interpreter-unification)
  - [Spike 5 (cross-cutting, after 2–4): decompose `finalizeScans`](#spike-5-cross-cutting-after-24-decompose-finalizescans)
- [Wave 3 — proof track: consolidate lemma bases, prune the sorry surface, simplify types](#wave-3--proof-track-consolidate-lemma-bases-prune-the-sorry-surface-simplify-types)
  - [Spike 6: proof-infrastructure consolidation (RouteSpec + AcsetCodec, ~600 lines)](#spike-6-proof-infrastructure-consolidation-routespec--acsetcodec-600-lines)
  - [Spike 7: prune the sorry surface to the honest open core (38 → ~14)](#spike-7-prune-the-sorry-surface-to-the-honest-open-core-38--14)
  - [Spike 8: proof-adjacent type cleanups (the noncomputable/computable seam)](#spike-8-proof-adjacent-type-cleanups-the-noncomputablecomputable-seam)
- [Suggested spike ordering and dependencies](#suggested-spike-ordering-and-dependencies)
- [Part II — Exploratory redesigns (creative, higher-risk, prototype-first)](#part-ii--exploratory-redesigns-creative-higher-risk-prototype-first)
  - [How the explorations relate to the Part I spikes](#how-the-explorations-relate-to-the-part-i-spikes)
  - [E1. One traversal to rule the collectors (van Laarhoven)](#e1-one-traversal-to-rule-the-collectors-van-laarhoven)
  - [E2. A typed core IR the pipeline narrows into ("trees that grow")](#e2-a-typed-core-ir-the-pipeline-narrows-into-trees-that-grow)
  - [E3. Evaluate over an arbitrary semiring](#e3-evaluate-over-an-arbitrary-semiring)
  - [E4. EvalPlan — make the evaluator run the same affine maps the route proves things about](#e4-evalplan--make-the-evaluator-run-the-same-affine-maps-the-route-proves-things-about)
  - [E5. An executable denotation for the routed artifact](#e5-an-executable-denotation-for-the-routed-artifact)
  - [E6. Property-based oracles (the tests the portfolio can't express)](#e6-property-based-oracles-the-tests-the-portfolio-cant-express)
  - [E7. Accumulate compile diagnostics (the Validation applicative)](#e7-accumulate-compile-diagnostics-the-validation-applicative)
  - [E8. Open registration of unary functions](#e8-open-registration-of-unary-functions)
  - [E9. Datatype-generic acset codecs](#e9-datatype-generic-acset-codecs)
  - [E10. Stage the interpreter into a code generator](#e10-stage-the-interpreter-into-a-code-generator)
  - [E11. Investigation: do UIDs earn their keep?](#e11-investigation-do-uids-earn-their-keep)
  - [E12. Named simp sets for the proof domains (tiny)](#e12-named-simp-sets-for-the-proof-domains-tiny)
  - [E13. Generators for `Br` — closing `BrOp`, and promoting E6's laws to theorems](#e13-generators-for-br--closing-brop-and-promoting-e6s-laws-to-theorems)
  - [E14. A simplifier: local algebraic rewrite rules over the DSL AST](#e14-a-simplifier-local-algebraic-rewrite-rules-over-the-dsl-ast)
  - [How the exploratory ideas compose](#how-the-exploratory-ideas-compose)

---

**Headline numbers if all recommended spikes land:**

| Metric | Now | After |
|--------|-----|-------|
| Net lines deleted | — | ≈1,100–1,300 |
| `sorry`s in the default build | 38 | ≈14 (the honest open surface) |
| Sites to touch when adding one new nonlin | 9 | ≈5 |
| Hand-maintained "MUST match X" mirror pairs | 3 | 0 |
| Byte-identical duplicate functions | 6+ | 0 |

---

## 0. Constraints — what must NOT be restructured

These boundaries came out of the review as *deliberate architecture*, and several look
superficially like duplication. Any implementation plan should treat them as fixed:

1. **The three parallel type families are not redundant.** Math tower (`Base/`,
   noncomputable, dependent), presentation (`DSL/Target.lean` `*P` types, computable,
   `ToExpr`), and acset (`Acset/`, flat relational rows byte-faithful to Python) each exist
   for a distinct reason, documented at `LeanNCD.lean:58-74`. Do not merge them or try to
   derive one from another. The conversions (`realize*`, `fromThreadedComposed`, CSV codec)
   are genuine boundary crossings.
2. **`SBrInstance` stays a list-of-rows.** The relational shape mirrors Python's
   `acset/instances.py` byte-for-byte; replacing rows with maps would break interop and
   invalidate the round-trip proofs' statements.
3. **RouteSpec unfolds `Lowering` definitionally.** `RouteSpec.lean`'s ~30 theorems unfold
   `buildStep`, `stepDegAxesMulti`, `dedupByUid`, `inputReadFactors`, `routeCore` by
   definition. Any change to those bodies — even semantically neutral — costs proof repair.
   This is the binding sequencing constraint: Spike 6 (which makes RouteSpec robust to such
   changes) should precede or accompany anything that touches `buildStep`. Conversely,
   `liveFix`, `topoSort`, and `stepMkWeave` are *outside* the proved surface (RouteSpec
   starts from `ScheduledProgram`) and are free to change.
4. **`brOpIdx`/`brOpOfIdx` stay an explicit table.** The index is a *serialization format*
   (acset labels via `natToUnary`). Deriving it from constructor order (`BrOp.toCtorIdx`)
   would make a constructor reorder silently change the wire format. Keep the table;
   optionally add a `#guard` totality check (`(List.range 15).map (brOpIdx ∘ brOpOfIdx) ==
   List.range 15`). (A different question about the same type, left to **E13**: this constraint
   is about `BrOp`'s wire-format *stability*, not about whether its constructors are a *complete*
   generating set for `Br` — the two are independent concerns about one inductive.)
5. **Two guards that share an error constructor are different checks.** `finalizeScans`'
   `inconsistentScanAxes` (`Structural.lean:489-492`, axis *sets*) and `buildStep`'s
   `outputAxesConsistent` (`Lowering.lean:476-486`, axis *order*) must not be merged; give
   them distinct messages or a cross-reference comment.
6. **`cartesianList` (`Eval/Scan.lean:20-22`) is not a duplicate of
   `DenseTensor.allCoords`** — its iteration order (last axis slowest) is load-bearing for
   scan causality. Add a cross-reference comment so nobody "deduplicates" it.

---

## Wave 1 — mechanical deletions and corrections (near-zero risk)

### Spike 1: dead code, stale docs, housekeeping

> **✅ DONE — merged to `main` 2026-07-10** (commits `1cf92d3..3bb7e13`; full `lake build` green,
> 8,604 jobs; whole-branch review clean). All eight sub-items **1a–1h** landed, including the
> optional behavior-changing **1h** (fail-loud `cyclicDataflow` reject, added test-first).
> Reference drift found and corrected during execution: the `_scratch_nf` doc citation was at
> `BrNF.lean:34` (not `Br.lean:288`); the `Shape.lean` "Task 6" placeholder was at `:515`; and
> `St.lean` was indeed **not** sorry-free (`swap_hexagon_fwd/rev`, `St.lean:267-268`), so the
> `SORRY_INVENTORY.md` claim was corrected — the full sorry recount stays deferred to Spike 7.

---

## Wave 2 — structural unification of the executable tracks

### Spike 2: one home for AST accessors and read/axis traversals

> **✅ 2c/2d/2e DONE — merged to `main` via PR #10 (2026-07-24).**
> Commits `3b2a625..89f9b55` (6 refactor + 1 spec doc + 1 docstring-restore); `lake build` green (8,609 jobs)
> at every commit; each task passed an independent spec+quality review and a whole-branch review (ready to merge).
> Net effect: **−44 lines of Lean**; **10 duplicate/mirror functions eliminated** (`stmtName`, `stmtSlots`,
> `Stmt.lhsSlots`, `declName`, `Stmt.nonlin`, `lhsAxisUID?`, `lhsSlotIdx`, `slotOutIdx`, `scatterOutDim`,
> `stateShape`) onto single homes in `DSL/Ast.lean` (or, for the HashMap-bound pair, within the Eval layer).
>
> **Status of the five sub-items:**
> - **2b** — subsumed by **E1** (`traverseAxes` replaced the `specs*`/`*AxisUIDs` collector towers). No separate work.
> - **2c/2d/2e** — done on the branch above.
> - **2a** — ✅ **DONE** via Approach D (`Factor.read?` classifier — a plain filterMap, not a traversal; reads need collection only). All of Spike 2 is now complete.
>
> **Design deviations from the original plan (deliberate, reviewed):**
> - **2c axis accessors** unified onto a single rich primitive `LHSSlot.axisSpec? : LHSSlot → Option AxisSpec`,
>   with `axisUID? := axisSpec?.map (·.uid)` **derived** — folding in `Stmt.lhsAxes` and `stmtLhsRank`'s inner
>   match (a twin the doc missed). The two genuinely *selective* projections were kept distinct and **named**:
>   `LHSSlot.freeUID?` (free-only, diagonal detection) and `LHSSlot.normUID?` (freeNorm-only, norm-axis lookup) —
>   `UID = Nat`, so widening either would typecheck yet silently change behavior; a build alone can't catch it.
> - **`outputShape`/`stateShape`** consolidated **within the Eval layer** (kept `outputShape`, deleted `stateShape`),
>   *not* moved to `Ast.lean` as the 2c table says — `Ast.lean` cannot import `HashMap`.
> - **Corrections found during execution:** `Stmt.lhsSlots` was **not** dead (18 callers in `test/Eval/`); the
>   survey had searched only `LeanNCD/`. `Structural`'s free-only and `normAxisUidOf`'s freeNorm-only matches are
>   intentionally selective (now `freeUID?`/`normUID?`), *not* `axisUID?` twins.
>
> **Equivalence certificates — WILL NOT BUILD (decision 2026-07-25):** the kernel-checked `*_eq_ref`
> certificates (E1-style + `freeUID?`/`normUID?` selectivity teeth) were specced in
> `docs/superpowers/specs/2026-07-24-spike2-cde-equivalence-certificates.md` but will **not** be written —
> proving `new = old` against pre-refactor baselines that were themselves never verified buys little.
> All of Spike 2 relies on `lake build` + the pinned suite + the per-task/whole-branch reviews. The spec
> is retained (marked NOT PLANNED) as a ready-made pickup if that calculus ever changes.

### Spike 3: make the Nonlin wildcard hazards unrepresentable

> **✅ 3a/3b DONE — branch `spike3-nonlin-elab` (2026-07-29).** Commits `70b5233..d65320e` (4 code commits + 2 fix commits); `lake build` green (8610 jobs) at every task boundary; sorry-free; each task passed an independent spec+quality review.
>
> **Actuals and deviations from the original plan:**
> - **`AxiswiseFn`, not `RowwiseFn`** — softmax/normalize act along ONE designated axis of an arbitrary-rank tensor; "row" was a `perRow` implementation view, not the source semantics. Constructor is `Nonlin.axiswise`.
> - **`Nonlin` is now `identity | pointwise PointwiseFn | axiswise AxiswiseFn (Option BoolExpr)`** in `DSL/Ast.lean`, with `PointwiseFn.toBrOp` / `AxiswiseFn.toBrOp` (the "two tiny tables") also in `Ast.lean` (it already imports `DSL.Target`), and `PointwiseFn.apply` in `Eval/Nonlin.lean`. All 6 migration sites were verified arm-by-arm semantically identical to the old 9-arm matches. Both in-code hazard comments are deleted — the hazard is now unrepresentable.
> - **The Spike 6a payoff was real and measured:** `RouteSpec.lean`, `Bridge/*`, `AcsetCodec.lean`, `Csv.lean`, and `Target.lean` are **untouched** across the whole branch (empty diff), and RouteSpec rebuilt clean with no edit — so the `Nonlin→BrOp` change required **zero** proof repair, versus the "budget RouteSpec repair" this doc warned about. `brOpIdx` wire format intact.
> - **3b landed as TWO closed keyword categories** (`tl_pointwise_kw`, `tl_axiswise_kw`) rather than one generic `tl_nonlin_kw`: only the axiswise category admits a `(where …)` mask, so `relu(where …)` is now unrepresentable at *parse* ("parse, don't validate") instead of merely rejected during elaboration. The `atomic("(" "where")` lookahead was preserved byte-identically and `ParseLayer34Test`'s `softmax(sum)` regression case still passes unweakened.
> - **Diagnostic cost — broader than "a blunter message" (measured, not estimated).** Routing keywords through categories (including 3b's `tl_unary_kw`) means Lean's `expected …` sets now name the *category* rather than the typeable keywords for **any** malformed RHS head, not just `relu(where …)`: `H[i] := 3 + X[i]` now reports `expected tl_agg, tl_axiswise_kw, tl_pointwise_kw or tl_unary_kw` instead of listing relu/sigmoid/…/softmax, and `relu(where …)` reports `expected tl_unary_kw` (an unrelated category — `tl_factor` is merely the last `tl_sum_expr` alternative to fail). Lean has no way to alias a category name in an `expected` set, so this is an accepted trade for the closed-category safety; `tl_agg` was already category-led, so only the reach is new. Recorded in `Syntax.lean`'s comment block and mitigated by keyword-mapping tests that assert every keyword by full `Nonlin` equality. **A favorable, unplanned side effect:** a *malformed* axiswise mask (`softmax(where <bad>)`) now errors *inside* the mask rather than backtracking to bare `softmax` and failing later at `tl_rhs` — a strictly better, more local diagnostic that cannot affect any previously-parsing program.
> - **`identStr` collapsed 23 sites**, not the 19 this doc estimated.
> - **A prerequisite bug fix was added as Task 0** (see below).
>
> **Task 0 — nonlinear scatter was silently erased (fixed).** Independent review (`copilot_code_analysis.md`) demonstrated, and we re-verified on `main`, that `evalScatter` never applied `rhs.nonlin`: `Out[2*i] := relu(X[i])` compiled and evaluated with the `relu` dropped. The "scatters carry no nonlinearity" claim at `Lowering.lean:30,44` was only a comment. Policy now enforced: **scatter + identity accepted; scatter + non-identity rejected during validation** (`CompileError.unsupportedNonlinScatter`, checked in both `TLProgram.compile` and `compileToScheduled` before `lowerArith`, plus a defensive `EvalError` in `evalScatter`). Supporting it later needs a semantic decision — activation before collision-reduction, or after fill/reduce — deliberately not chosen here. Note the check must match `.assign` guarded by `slotsBecomeScatter` **as well as** `.scatter`: the elaborator only ever emits `Stmt.assign`, and `lowerArith` (the sole `.scatter` producer) runs *after* validation, so a `.scatter`-only check would be a dead no-op.
>
> **⚠️ Honest scope — what this spike does and does NOT establish.** Spike 3 establishes **representation closure** for `Nonlin` (every nonlinearity's category is encoded in its constructor; every match is exhaustive with no semantic wildcard) and source-level **keyword/mask shape validity**. It does **NOT** establish **semantic closure**: `BrBaseP` still carries no field for the softmax mask, the `UnaryOp`, `ScatterOpts`, or dtype, so routed lowering can still drop payload (an inline `log(X[i])` and a plain `X[i]` still lower identically). Grouping prevents *misclassification*; it cannot manufacture a new function's evaluator/target/codec semantics — a new `AxiswiseFn` still needs all of those. It also repairs **no** categorical proof gap (`weave_unique`, the flagship graded instance) and leaves ACSet operation-tag decoding outside the validated boundary. See [`semantic_payload_audit.md`](semantic_payload_audit.md) and the [terminal goal](#terminal-goal-2026-07-30-a-pytorchjax-execution-layer-via-evalplan) section for the remaining stages.
>
> **3c remains deferred** — with a sharper reason than "evaluate whether it pays": `BrBaseP` has no field for the `UnaryOp` at all, so merging `Factor.unaryFn` into `Factor.read` before that payload is designed would make the loss *less visible*, not fix it. Blocked on the semantic-payload audit.

### Spike 4: Eval interpreter unification

**4a. `evalAssignWith` = `evalAssignSeeded` with an empty seed.**
(`Eval/Contract.lean:73-103` vs `:162-195`) — ~80% token-identical; every delta (frees
filter, baseCoord init, termContr filter, outShape) reduces to the unseeded form when
`seed = {}`. Delete `evalAssignWith`; keep one function. **Two real payoffs beyond line
count:** (i) the unseeded version has a fail-loud unsized-free-axis check (:82-84) that the
seeded version *lacks* — today a scan slice with an unsized free axis silently yields an
empty tensor via `getD 0`; unification ports the check to the scan path (a bug-shaped hole
closed). (ii) Pass `Combine` as a struct instead of three loose `(mul, combine, unit0)`
params (the struct already exists at :109-112, defined *below* its would-be first use — move
it up). Pinned by ContractTest, ScanTest, MaxReduceTest, EvalExamplesTest.

**4b. Add the ⊗-unit to `Combine` now.** `prod := 1.0` — the within-term combine's unit — is
hardcoded at `Contract.lean:95,187` and `Scatter.lean:42`. The planned general-semiring
notation (`agg(min, +)`, portfolio doc §19.2) needs `unit1 = 0.0` for an additive combine, so
today's code would be *wrong*, not just inelegant. Adding `unit1 : Float := 1.0` to `Combine`
and threading it to those three sites is a 10-line change that unblocks the semiring work and
documents the invariant.

**4c. Unify the contract-then-nonlin dispatch.** `evalPlain`'s assign arm
(`Eval/Eval.lean:33-51`) and `evalStmtSliceSeeded` (`Eval/Scan.lean:37-53`) duplicate the
Combine selection and the 7-line axisPos-resolution match. **Semantic divergence found:** the
scan path inlines only the agg match, skipping `combineFor`'s predicate→`Combine.bool` branch
(`Contract.lean:137-143`) — a predicate state inside a scan would contract with `Combine.real`,
unlike the identical statement outside a scan. Unify into one
`evalAssignStmt (decls … seed) (s : Stmt)` (thread `decls` through `evalScan` — one new
parameter), with `evalPlain` passing `seed = {}`. Fixes the divergence and deletes ~17 lines.
Error-message prefixes change; no test pins them.

**4d. Move nonlin axis resolution into `Nonlin.lean`.** `applyNonlin` takes
`axisPos/axisUids` that 6 of 9 variants ignore, forcing both callers to pre-resolve with the
hazard-prone match. Give `Nonlin` a `normMask? : Nonlin → Option (Option BoolExpr)`
classifier and make `applyNonlin` `Except`-returning, owning the axis lookup. Callers shrink
to one line; the classification lives in exactly one place, adjacent to the constructor list.
(If Spike 3a lands first, this is nearly free — classification is then just a 3-arm match.)

**4e. Split `Eval/Shape.lean` (521 lines, five jobs).** New layout:
`Eval/Slots.lean` (AST/slot vocabulary: `lhsSlots`, `readsOf` deletion per Spike 2,
`LHSSlot.outExtent` per 2d, `outputShape`), `Eval/SizeSolve.lean` (constraint types,
diagnostic rendering, the exact-RREF solver — :26-371), `Eval/SizeInfer.lean` (fixpoint
driver + scatter shapes — :373-498). Pure file moves. **Caution:**
`AffineShapeSolverTest.lean` pins exact substrings of rendered diagnostics ("rank=1, vars=2",
"ml-hint: …") — moving files is safe, editing `renderSolveDiagnostic` is not.

> **✅ DONE 2026-08-02 (Wave E).** `Shape.lean` is now a compatibility umbrella over
> `Slots.lean`, `SizeSolve.lean`, and `SizeInfer.lean`. The split follows the actual branched
> dependency graph rather than adding another lower-level abstraction; duplicate affine-position
> construction was consolidated while solver behavior and diagnostic rendering stayed unchanged.

**4f. Decompose `evalScan`** (`Eval/Scan.lean:91-135`, 45 lines, four phases already numbered
in comments) into `allocStates` / `applyBase` / `runRecurStep` + an `iterWritePositions`
helper for the `(position, index+δ)` bookkeeping that appears twice (δ=0 base, δ=1 recur).
Behavior-neutral; preserve the `work` vs `stepEnv` insert ordering (:130-132) exactly.

**4g. Replace the stringly-typed scatter reduce.** `opts.reduce : Option String` is matched
as `some "sum" | some "max" | _ => overwrite` (`Eval/Scatter.lean:53-56`) — an unrecognized
string silently overwrites, violating the fail-loud convention. Introduce
`inductive ReduceOp | sum | max | overwrite`, parse/validate once at the boundary.

> **✅ DONE — merged to `main` 2026-08-01** (commits `a3098c0..c86005e`; full `lake build` green,
> 8,612 jobs; whole-branch review clean via `docs/superpowers/plans/2026-08-01-scatter-collision-policy.md`).
> Landed as `CollisionReduce | rejectCollisions | overwrite | sum | max | min` — one more
> constructor than proposed here (`min`, for `AggOp` parity) and a different default: absence of
> an explicit policy now means `rejectCollisions`, not `overwrite`, confirmed safe because no
> surface-compiled scatter pattern in the codebase ever collides (`lowerArith` already rejects any
> surface-detectable collision independently). Also fixed a second, related defect found while
> implementing this: `evalScatter`'s RHS value computation ignored `rhs.agg` entirely (always a
> real sum-of-products, even for a declared `maxreduce`/`minreduce`) — routed through the same
> `Combine` record Wave B built for `Contract.lean` instead. Two adjacent gaps surfaced but
> deliberately not fixed here: a scatter-shaped LHS combined with a scan iteration slot compiled
> when it arguably should be rejected at compile time, and Lean's compile-time collision detection
> (`LHSSlot.collapses`) is narrower than the Python reference implementation's `_scatter_injective`.
>
> **First gap ✅ DONE — merged to `main` 2026-08-01** (commits `047b023..fd72d48`, merge `f2d0a2b`;
> full `lake build` green, 8,612 jobs; via
> `docs/superpowers/plans/2026-08-01-scatter-scan-compile-check.md`). New compile-phase function
> `checkScatterNoScan`, mirroring `checkScatterNonlin`'s exact shape and pipeline position, plus a
> new `CompileError.scatterInScan` constructor — purely structural, no axis-size information
> needed. The second gap (broadening `LHSSlot.collapses` toward a general injectivity check)
> **remains deferred, now for a confirmed architectural reason, not an assumed one**: tracing the
> actual call graph showed `checkScatterNonlin`/`lowerArith` have no concrete axis sizes available
> at all (`inferAxisSizes` only runs later, inside `evalScheduled`, after compilation has already
> finished) — a Python-`_scatter_injective`-style enumeration cannot run at this point in the
> pipeline. Would need a sound symbolic over-approximation instead; a separate, harder task. See
> `scatter-in-scan-compiles-but-should-reject` in project memory for the full writeup.

**4h. Structured `EvalError` (largest item — do last).** `abbrev EvalError := String`
(`Eval/Tensor.lean:4`) vs the structured `CompileError`. Tests show the cost:
`AffineShapeSolverTest` needs 5–8 chained `.contains` substring assertions per case, and
`SolveDiagnostic` — already a structured value — is eagerly flattened to a string at every
throw site (`Shape.lean:330,340,353,366`). Proposal: an inductive with
`unknownTensor / unsizedAxis / sizeConflict / solveFailure (SolveDiagnostic) / domainError
(UnaryOp, Float) / normAxisError / unsupported String`, plus a `ToString` that reuses
`renderSolveDiagnostic`. Migration plan: keep `ToString` output byte-identical first (tests
pass unchanged), migrate assertions to field matches second. ~20 throw sites across 6 files;
`SolveDiagnostic` and friends need un-`private`-ing.

> **✅ DONE 2026-08-02 (Wave E).** `Eval/Error.lean` now owns closed, layered
> `EvalError`/`ShapeError`/`EvalWarning` values and their sole renderers. Compile and shape causes
> remain nested, unary-domain failures retain tensor/coordinate context, unknown-tensor and
> domain-operation tags are closed enums rather than strings or impossible total operations, and
> typed tests inspect payloads without losing byte-compatible presentation text.

**4i. Small decoupling wins:** `Eval/Eval.lean` imports all of `DSL.Compile` solely for the
`TLProgram.eval` wrapper (:78-83) — move the wrapper out (e.g. `Eval/Entry.lean`) so the
interpreter depends only on `DSL.Ast` + `Pipeline.Types`. (Already, in miniature, the
worker/wrapper split **E4**'s exploration names explicitly: `compileToScheduled`+`evalScheduled`
is the worker, `TLProgram.eval` the thin boundary around it.) And `evalScheduled` drops solver
warnings into `dbg_trace` (`Eval/Eval.lean:64`) — return them instead
(`AffineShapeSolverTest:412` already asserts on a returned list elsewhere).

> **✅ DONE 2026-08-02 (Wave E).** `Eval.lean` is now a compiler-independent scheduled worker
> returning `EvalReport { env, warnings }` on success and `EvalFailure { error, warnings }` when
> execution fails after inference; `Entry.lean` alone joins it with `DSL.Compile`. `TLProgram.eval`
> preserves warnings on both outcomes as the sole source API; the initially-added output-only
> compatibility projection was removed before merge because it silently discarded diagnostics and
> duplicated the entry surface. Callers explicitly inspect `EvalReport.env`. `dbg_trace` was
> removed.

### Spike 5 (cross-cutting, after 2–4): decompose `finalizeScans`

`Structural.lean:406-521` — one 115-line function doing seven jobs (base-axis adoption,
scanPre partition, dep fixpoint, connected components, cross-component guard, per-component
validation ×4 + node assembly, plain classification), with five local closures. It absorbed
four behavioral fixes this cycle (multi-axis, heterogeneous-coupling reject, scan-projection
reject, aggregators) and is where the next scan feature will land too. Extract:

```lean
def Stmt.scanAxisSet : Stmt → List UID                    -- the axSet closure
def scanDeps (stmts) : HashMap String (List UID)          -- reads-only fixpoint (dep)
def scanComponents (iterStmts) : List (List UID)          -- CC by repeated merge
def mkScanNode (dep nonPre comp) : Except CompileError ScanStmt   -- classify + validate + build
```

`finalizeScans` becomes ~15 lines of plumbing; the four validation loops live inside
`mkScanNode` next to the classification predicates they guard. Uses Spike 2's
`LHSSlot.axisUID?` and `IterSlot`. Well pinned: StructuralTest (scan grouping, coupled scans,
missing base, causality), ScanTest, RecurrenceTest (RC4/RC9), KnownGap/RejectTest (UF5), the
3-D scan test. Behavior-dense — this is the one Wave-2 spike that warrants its own detailed
plan with a test-first checklist.

Optional adjacent cleanup: `ScanStmt.scan`'s positional
`String → List AxisSpec → List Stmt → List Stmt → Bool` constructor produces `.scan _ _ b r _`
patterns at ~15 sites; a `ScanNode` structure argument would name the fields. Medium churn,
readability-only — fold into this spike or skip.

---

## Wave 3 — proof track: consolidate lemma bases, prune the sorry surface, simplify types

Three spikes, each an independent lens on the proof track: **Spike 6** consolidates proof
*scripts* (no statement changes), **Spike 7** prunes the *sorry surface* to its honest open
core, and **Spike 8** simplifies the *types* the proofs are stated over (the
noncomputable/computable seam). None of the three depends on Wave 2; see the ordering table
at the end for how they interleave with it.

### Spike 6: proof-infrastructure consolidation (RouteSpec + AcsetCodec, ~600 lines)

No statement changes anywhere in this spike — pure proof-engineering. It also *future-proofs*
the proofs against Wave-2 pipeline changes, which is why 6a is worth doing early if Spike 3
is planned.

**6a. Factor `ScanStmt.toBrBaseP` out of `buildStep`.** ✅ **DONE (2026-07-25, branch `spike6a-tobrbasep`)** —
reshaped `buildStep` (`Lowering.lean:498-564`) as `guards; pure (sc.toBrBaseP, ← wires)`, collapsing
five RouteSpec lemmas' repeated `cases sc` + `bind_pure_pair_ok` dance onto one
`buildStep_ok_eq : buildStep … = .ok (b, w) → b = sc.toBrBaseP ∧ …` plus `rfl` projections. Future
`BrBaseP` field additions need zero new extraction lemmas — this is what made Spike 3a's `buildStep`
touch cheap.

> *Actuals: the repair surface was **7 proof bodies, not 5** — two more, `buildStep_ok_guard` and
> `buildStep_outputWeaves_length_one`, also `unfold buildStep`. Six
> field-projection proofs collapse to one-liners off the new `buildStep_ok_eq` (`rfl` for the four
> plain fields, `simp` for the length lemma, and `buildStep_wires_mapM` is literally its second
> conjunct); `buildStep_ok_guard` reasons about the throw-guards (which stay in `buildStep`) so it
> was untouched. Net **−35 lines of Lean** (RouteSpec 908→874; `Lowering` net −1), well short of the −150 estimate,
> because `ScanStmt.toBrBaseP` and `buildStep_ok_eq` are net-new — the real payoff is structural
> (future `BrBaseP` fields = zero new extraction lemmas; Spike 3a's `buildStep` touch is now cheap),
> not line count. Zero statement changes; sorry-free; `[propext, Quot.sound]`. Two clean commits,
> two whole-task reviews.*

**6b. One `routeCore` elimination lemma.** Six proofs (RouteSpec :87-162, :469-513, :692-712)
re-unfold `routeCore`, case on `routableInOrder`, case on the `mapM`. Prove
`routeCore_ok_elim` once (+ a generic `routeCore_forall_steps` for the three
per-step-property lifts). ≈ −120 lines.

**6c. Shared `Util/ListMapM.lean`.** RouteSpec's private `mapM_ok_length/getD/mem` (:19-83)
are re-exported for AcsetCodec (:897-906); `map_eq_range_map_getD` is duplicated *verbatim*
in `Realize.lean:173-178`; `find?_unique` lives in AcsetCodec. One shared util module.

**6d. AcsetCodec (1,593 lines): split + two combinators.** Split into `Codec.lean` (defs,
≈330 lines), `Isolation.lean` (generic list lemmas), `RoundTrip.lean` (the theorem). Then two
proof schemas that account for ~700 lines collapse:

- *Keyed-table isolation*: `filterSlot_flatMap_off` (:601-626) and `filterSlot_samples_off`
  (:1050-1081) are the same proof modulo row type; one polymorphic `filter_tagged_groups`
  lemma covers both plus the degree-slot case (:637-665). ≈ −120 lines.
- *find?-uniqueness-by-injective-key*: `lookupSize_from` (:752), `lookupName_from` (:784),
  `from_equation_find` (:1370), `from_inputRow_find` (:1383), and two ~45-line blocks inside
  `decodeReindexing_from` all follow membership-witness + injectivity + `find?_unique`. One
  `find?_of_injective_key` combinator per-site cost drops to ~5 lines. ≈ −150–200 lines.

### Spike 7: prune the sorry surface to the honest open core (38 → ~14)

> **✅ DONE — merged to `main` 2026-07-10** (commits `eb09a6d..c707fce`; full `lake build` green,
> 8,603 jobs — down from 8,604 as `BrNF` left the build; whole-branch review clean). All of
> **7a/7b/7c** landed: 7a deleted the impossible `TargetActegory StObj (Mat ℝ) ℝ` instance +
> `instAlgebraBrMatR` + `construct_correspondence` (**−17** sorries); 7b parked `BrNF` (R100 rename
> to `spikes/BrNF.lean`, **−≈6**) and **demoted** `instance : Elemental BrObj` → `def brElemental`;
> 7c **deleted** `grothendieck_split` (**−1**, chosen over restating). Confirmed **pure subtraction —
> no new proofs, no sorry re-introduced**; `St.swap_hexagon_fwd/rev`, `instDGradedStBr`, and
> `brCancelPoint`'s proof were left untouched (out of scope). A trailing `docs:` commit swept the
> stale references the deletions exposed. `Br.lean:298`'s doc records the cospan-model
> requirement 7b surfaced (`BrNF`'s bijective wiring provably can't interpret `copyW`/`delW`;
> see `leanncd/LeanNCD/Base/AGENTS.md` and Part II's **E13**) — not repeated here.

The Bridge track (Realize/Agreement/AcsetCodec/SBr/RouteSpec) and the whole executable track
were **zero-sorry** at the time of the census; all 38 were math-tower.

**What remains after 7a–7c (~14, the honest open surface):**

| Item | Status |
|------|--------|
| `St.swap_hexagon_fwd/rev` (`St.lean:267-268`) | **The one recommended proof spike.** Provable as stated, same genre as the proved `tensorHom_assoc`. Known friction (recorded from a prior attempt): the associator casts are defeq-not-syntactic — needs the `rw`/`erw` cast-bridge idiom (cf. `Br_swap_hexagon_fwd`'s `cast_quot_id`), *not* simp; budget a focused Br-hexagon-sized effort, not a quick win. Closing them makes `St` fully sorry-free; the Adapter consumers already exist. |
| `brCancelPoint` (`Br.lean:300`) | True; parked pending the cospan model (7b). Not load-bearing. **Not yet a scheduled spike** — 7b names the requirement but doesn't scope it; see **E13**, which also depends on this model existing. |
| `weave_unique` (`Core/Weave.lean:32`) | Double-gated (`broadcast_gen`, `brCancelPoint`); park. |
| `instDGradedStBr` 10 fields (`Instances/StBr.lean:15-24`) | The genuine long pole: `act` is de-risked (spike S0, ~400–650 lines), `sh_act` redesigned to `≅`, `broadcast_gen` deep. Staged work, unaffected by this doc. |

### Spike 8: proof-adjacent type cleanups (the noncomputable/computable seam)

> **✅ DONE — merged to `main` 2026-07-11** (commits `2db951c..7831816`; full `lake build` green,
> 8,602 jobs — down from 8,604 as `Base/Category` and `DSL/SizeExpr` fold/relocate away;
> whole-branch review clean, opus-verified). **8a** deleted the nearly-dead `StMatP'` (chosen over
> wire-through, which would touch the proved `RouteSpec` surface). **8d** merged `Base/Category`
> into `ColoredPROP.lean`. **8c** swapped `Axis.size`/`DType.nat` from the noncomputable `Numeric`
> to the computable `SizeExpr` (relocating `SizeExpr` `DSL/`→`Base/` first to avoid a Base→DSL
> layering inversion), deleting the lossy `toNumeric` bridge and the `Numeric` abbrev (`Coeff`
> kept — it backs the `StMat` laws) and making `realizeAxis` identity-on-size; the `StMat` category
> laws were verified **byte-identical** (signature-only swap, no proof-meaning change, no sorry
> touched). **8b** intentionally skipped (churn without payoff). A trailing `docs:` commit swept the
> stale `Numeric` references the swap exposed.

---

## Suggested spike ordering and dependencies

> **THIS IS THE AUTHORITATIVE WORK ORDER (rewritten 2026-07-30).** It supersedes the original
> Wave 1/2/3 grouping and the 2026-07-26 addendum's ordering advice, both of which predate the
> [terminal goal](#terminal-goal-2026-07-30-a-pytorchjax-execution-layer-via-evalplan). The waves
> below are ordered by *dependency*, not by risk. Where a spike's own body text still describes the
> old ordering, this section wins.

### Landed

| | Spike | Date | Ref |
|---|---|---|---|
| ✅ | **Spike 1** — dead code, stale docs, housekeeping | 2026-07-10 | `1cf92d3..3bb7e13` |
| ✅ | **Spike 7a/7b/7c** — sorry-surface pruning (38 → ~14) | 2026-07-10 | `eb09a6d..c707fce` |
| ✅ | **Spike 8** — proof-adjacent type cleanups | 2026-07-11 | `2db951c..7831816` |
| ✅ | **E6** — property-based oracles (all 3 laws) | 2026-07-12 | the regression net Spikes 4/5 + E4 build against |
| ✅ | **E1** — one traversal (`traverseAxes`) | 2026-07-23 | PRs #1–#5; absorbed Spike **2b** |
| ✅ | **Spike 2** — *all of it* (2c/2d/2e, then 2a) | 2026-07-24/25 | PR #10, PR #11 |
| ✅ | **Spike 6a** — factor `ScanStmt.toBrBaseP` out of `buildStep` | 2026-07-25 | PR #13 — paid off immediately in Spike 3 (zero RouteSpec repair) |
| ✅ | **Spike 3** — 3a/3b + the Task-0 scatter reject | 2026-07-29 | PR #14; **3c deferred** |
| ✅ | **Semantic payload audit** (roadmap Stage 3) | 2026-07-30 | `papers/semantic_payload_audit.md` |
| ⚠️ | **Wave B** — 4a/4d/4c DONE; 4b's `unit1` DONE, its `ContractionAlgebra` classifier NOT built (deferred to Wave C) | 2026-07-31 | `d08a1d8..383bc0b`; `docs/superpowers/plans/2026-07-31-wave-b-eval-unification.md` |
| ✅ | **Wave D** — 4g typed scatter collision policy (`CollisionReduce`) | 2026-08-01 | `a3098c0..c86005e`; `docs/superpowers/plans/2026-08-01-scatter-collision-policy.md` |
| ✅ | **checkScatterNoScan** — reject scatter+scan-iteration-slot at compile time (Wave D follow-up finding) | 2026-08-01 | `047b023..fd72d48`, merge `f2d0a2b`; `docs/superpowers/plans/2026-08-01-scatter-scan-compile-check.md` |
| ✅ | **Wave E** — 4e shape split, 4h structured diagnostics, 4i `EvalReport`/entry boundary | 2026-08-02 | full cached `lake build` green (8,618 jobs) |
| ✅ | **Wave C EvalPlan proposal** — architecture, phase/workstream breakdown, correctness laws, acceptance criteria (design only; Wave C implementation not started) | 2026-08-03, revised 2026-08-05 | `papers/wave_c_evalplan_proposal.md` (896ae22, revised 3ebdee1) |
| ✅ | **Wave C C0** — executable contract: capability classifiers, preflight ordering, 10 fixture/mutation `run_cmd` pairs (`Eval.Plan.ContractTest`), registered in the default build target | 2026-08-05 | full cached `lake build` green (8,619 jobs) |
| ✅ | **Wave C C1** — static signature boundary: `TensorSignature`/`InputSignature` vocabulary, `inferAxisSizesCore` extraction, `inferAxisSizesFromSignature`, six test categories (`Eval.Plan.SignatureTest`), registered in the default build target | 2026-08-05 | full cached `lake build` green (8,622 jobs) |
| ✅ | **Wave C C2** — checked local kernel vertical slice: local-operation IR (`Plan/Kernel.lean`), `PlanError`/`PositionalInputError` diagnostics (`Plan/Error.lean`), the private-constructor checker `checkAssign` (`Plan/Check.lean`), and the Dense interpreter `runDenseAssign` (`Plan/Dense.lean`), with 32 `#guard` fixtures across three test modules (`Eval.Plan.KernelCheckTest` 15, `Eval.Plan.KernelDenseTest` 16, `Eval.Plan.CheckedPrivacyTest` 1), registered in the default build target | 2026-08-06 | full cached `lake build` green (8,629 jobs) |
| ✅ | **Wave C C3** — checked graph vertical slice: the raw graph IR `RawEvalPlan` (`Plan/Graph.lean`), the graph-wiring checker `checkPlan` and private-constructor `CheckedEvalPlan` (`Plan/Check.lean`), the `PositionalInputError.arityMismatch` diagnostic (`Plan/Error.lean`), and the graph interpreter `runDensePlan` (`Plan/Dense.lean`), with 36 `#guard` fixtures across two test modules (`Eval.Plan.GraphCheckTest` 16, `Eval.Plan.GraphDenseTest` 20), registered in the default build target | 2026-08-06 | full cached `lake build` green (8,632 jobs) |
| ✅ | **Wave C C4** — source compiler and representation boundary: `capabilityPreflight`/`prepareEvalPlan` (`Plan/Compile.lean`), the source-name-keyed `PlanBindings`/`PreparedPlan` sidecar (`Plan/Prepared.lean`), the named-entry adapter `pack`/`unpack`/`runPreparedDense` (`Plan/Adapter.lean`), and the neutral-leaf `EvalReport` move (`Eval/Report.lean`), plus the alpha-renaming law and the full `PropertyOracle.enumPrograms` differential sweep against the legacy evaluator (3,832/3,832 entries agree bit-for-bit, 0 rejected) and 3 test-the-tester mutations (`Eval.Plan.DifferentialTest`), alongside `Eval.Plan.CompileTest` (29 `#guard`s) and `Eval.Plan.AdapterTest` (3 `run_cmd` blocks / 9 checks), all registered in the default build target | 2026-08-06 | full cached `lake build` green (8,639 jobs) |
| ✅ | **Wave C C6** — adversarial audit and handoff: closed 5 real test-coverage gaps (`InputBindingError.storageMismatch`, `PlanCompileCause.shape` exercised through `prepareEvalPlan`, non-empty-warnings-survive-a-failure, `PlanRunCause.execution` documented+exercised, 4 `CapabilityError` sub-cases — `iterAt`/`iterNext`/`axiswise`/`min` — through the real `capabilityPreflight`) and documented 2 dead-code findings (`ScalarConst.f32`/`.bool`, 4 `Compile.lean` helper branches); made `Eval/Plan/` discoverable (`Eval/AGENTS.md`, `AGENTS.md`, `import LeanNCD.Eval.Plan.Adapter` in `LeanNCD.lean`, so `import LeanNCD` alone now reaches the checked-plan API); and published the capability manifest (`papers/wave_c_capability_manifest.md`), which also confirms the module import graph matches A.2 and the checked semantic IR carries no `String`/`UID`/callback/unordered-map field | 2026-08-07 | full cached `lake build` green (8,639 jobs) |

### Remaining — the critical path to an executing backend

> **Wave C is complete** (C0-C4, C6; **C5 — canonical representation and codec — is deferred**, see
> A.9). C0 (executable contract), C1 (signature-driven shape inference), C2 (checked local kernel
> vertical slice), C3 (checked graph vertical slice), C4 (source compiler and representation
> boundary), and C6 (adversarial audit and handoff) are done. The detailed architecture is written
> up in [`wave_c_evalplan_proposal.md`](wave_c_evalplan_proposal.md) (design-only beyond
> C0/C1/C2/C3/C4/C6; C5 retained there as a design record only). Wave C's own handoff is done: a
> consumer picking this up next should read
> [`wave_c_capability_manifest.md`](wave_c_capability_manifest.md) first — it states exactly what
> the checked plan boundary accepts, rejects, covers by differential test, and does not yet
> support, without re-deriving any of it from the full proposal. What comes after Wave C is not
> named here yet.

```text
Wave A  Correctness freeze — ✅ THE THREE AUDIT FINDINGS DONE 2026-07-30 (c754165..14b1353)
        · finding C  ✅ splitStmt now threads agg onto the LINEAR step (it is the step that
                       contracts); nonlin step stated .sum explicitly. Was an EVAL bug, not just
                       a routing-label one. Guarded by LoweringTest AGG1/AGG2, which build the
                       stmt programmatically because the grammar makes relu(maxreduce(..))
                       unparseable — teeth verified by mutation (reverting fails AGG1).
        · finding D  ✅ brOpOfIdx? is now the single table; brOpOfIdx derives via .getD .contract
                       so the two cannot drift. 3 #guards (mutual-inverse on 0..14 + two
                       out-of-range). Both round-trip lemmas axiom-free; decode_op/decodeStep_eq
                       closed unchanged. Genuinely-partial decode deliberately NOT done (restates
                       5 theorems + realizeSBr — a separate project).
        · finding E' ✅ blankArrayRow comment corrected (op index rides in EquationRow.lhsName,
                       NOT elementwiseFn — the old claim matched a superseded plan).
          [letters = papers/semantic_payload_audit.md "Cross-cutting findings"]
        · finding #4  ✅ recurMorphism REJECTED at compile (CompileError.unsupportedRecurMorphism).
                       Probe confirmed the analysis exactly: compile .ok ops=[scanPre] while eval
                       errored, and toBrBaseP discarded the whole ThreadedComposed. Reverses
                       RecurMorphismTest's live `hasOp .. BrOp.scanPre` guard — which could never
                       have caught the bug (it checked the op TAG, not the discarded payload).
        · finding #5  ⚠️ HARDENED, NOT CLOSED. evalScan now fails loud on an unsized iteration
                       extent, but the analysis's MECHANISM was wrong: the reported program is
                       rejected by the pre-existing `axes.isEmpty` guard (compileToScheduled yields
                       `SCAN G axes=[]`), so the new check is unreachable for it and untested. Open:
                       (a) why a .scan with axes=[] is constructible; (b) where the
                       `lean_array_set_panic` originates — it is in the EVAL path, not compile
                       (Shape.lean:431,472's getD 0 are the suspects).
        · finding #17 ✅ writeSBr now returns `Except CsvError` — it used to emit `RawAxis:1,` (an
                       axis with an EMPTY size) and return normally after `encodeSize` had already
                       REFUSED the compound expression. Regression tests cover both fallible paths
                       (`axisSizes` and `ArrayRow.maxValue`); all byte-exact fixture assertions pass
                       unchanged, so only the error channel moved.
        · finding #5  ✅ CLOSED after re-probing (my earlier "not closed" was wrong — I had compared
                       two different programs). Panic gone; the named error fires.
        · finding #5b ✅ DONE 2026-07-31 (its own spike, not a Wave A item).
                       Whitespace is SEMANTIC in an LHS slot: `ident "+1"` is one ATOM, so `l +1` ⇒
                       .iterNext (scan recurrence) but `l + 1` ⇒ .affine (.shift l 1) (a shifted
                       write, and it flips the axis kind nat→real), yielding a degenerate
                       `SCAN .. axes=[]`. The natural spacing silently means something else rather
                       than failing. DECIDED: accept BOTH spacings + REQUIRE a declared AND PINNED
                       iteration axis for scans. The PIN is the load-bearing half and is NOT implied
                       by declaration (`axis l : ℕ` carries no size — `Decl.axis` takes
                       `Option Nat`); requiring `= N` is what closes #5 at the source. An earlier
                       note here wrongly credited mere declaration. PROPOSED SYNTAX: a new `iter`
                       decl keyword in pinned form only — `iter l = 3` — which makes both
                       "unpinned" and "wrong kind" ungrammatical rather than validated.
                       STRICT variant DECIDED 2026-07-30 (`iter` is the ONLY way to declare an
                       iteration axis) — because under permissive `iter` is only a comment: if
                       `axis l : ℕ = 3` still counts, the reclassifier must accept both spellings and
                       no code can rely on `Decl.iter`. Strict makes it a real invariant (present ⇒
                       iteration axis, pinned, ℕ-kinded) and collapses the error to one failure mode.
                       Breaking change: ~10 recurrences / 6 files to ADD, plus ~25 axes / ~14 lines /
                       5 files to CONVERT from `axis … : ℕ = N`, plus 5 AST sites in ScanGen.
                       ⚠️ NOT a mechanical keyword swap (an earlier note here said ~23 and
                       "mechanical" — both wrong): `axis X : ℕ = N` does NOT imply X iterates, so
                       four files' ℕ axes must STAY `axis` (RecurrenceTest:77 is a no-recurrence mask
                       contraction — the trap most likely to catch a bulk edit; ConvPoolTest's `p`;
                       RelationalTest; EdgeCaseTest; SyntaxTest:7 is a syntax quotation), co-iterating
                       comma groups swap wholesale (`axis r,c` ⇒ `iter r,c`), and MIXED groups must be
                       SPLIT (EvalExamplesTest:268 `axis l : ℕ = 3, s : ℕ = 2` ⇒ `iter l = 3` +
                       `axis s : ℕ = 2`). Count is ±2; the per-program pass belongs in the plan.
                       Spec: docs/superpowers/specs/2026-07-30-scan-axis-declaration-spike.md
                       SHIPPED 2026-07-31 via an 11-task plan: `iter <ident> = <num>[, ...]` is now
                       the ONLY way to declare a scan iteration axis, both spacings elaborate
                       identically, and an undeclared iteration axis is rejected at COMPILE time
                       (`CompileError.scanAxisNotIter`, replacing RJ6's old eval-time path — same
                       defect, correct mechanism). The actual file-touch list differed from the
                       table above: `ConvPoolTest`/`FeedforwardTest`/`ParseExamplesTest`/
                       `ParseProgramTest` needed NO changes (no real recurrences, or parse-only —
                       never in the table's favor); `AcsetCodecTest`/`CompileExamplesTest` DID need
                       `iter` added despite not appearing in the table at all; `ScanGen.lean`'s 6
                       programmatic `Decl.axis` entries did NOT need conversion (built directly in
                       Lean, bypassing the surface grammar `iter` disambiguates). Also found and
                       fixed: `explicitSizes` (`Lowering.lean`'s `schedule`) needed a new
                       `Decl.iter` fold-arm or a pinned `iter` axis's size would silently never
                       reach shape resolution. Full `leanncd/` build green (8611 jobs), no new
                       sorries, property-oracle suite unaffected.
        · finding G   ✅ DONE (docs-only) — PROBED 2026-07-30, UNREACHABLE via surface syntax. A
                       scan base case does not name its own
                       iteration axis: `G[j,0]` elaborates to `.iterAt (scanAxis "") n` with an
                       EMPTY name and uid 0 (Elab.lean:244), and `finalizeScans` recovers the axis
                       BY SLOT POSITION from the matching step (Structural.lean:849-851). Deliberate
                       and documented, so this is a fragility (silent misattribution if base and
                       recur slot orders disagree — nothing enforces they agree; outputAxesConsistent
                       is a DIFFERENT check, across a coupled scan's outputs on the routed path after
                       grouping), not a reproduced defect. Only slot-level naming (`G[j, l@0]`) would
                       CLOSE it, but #5b defuses it — folded in as Part 5 of the spec: a
                       single-candidate rule removes the failure mode for single-axis scans (needing
                       no declaration at all), and the "left as-is" miss arm becomes a named
                       rejection so the multi-axis remainder is loud instead of silent.
        · finding H   ✅ DONE 2026-07-30 — PROBED, then fixed. An axis KIND's size was write-only:
                       `axis l : ℕ[3]` parses to `AxisKind.nat (some (.lit 3))` and pins NOTHING.
                       Probed: it yields the same "unsized iteration axis" error as declaring no
                       axis at all, because `explicitSizes` folds only `.axis ax (some n)`
                       (Lowering.lean:176-178) and the sole `AxisSpec.kind` consumers are the two
                       dtype checks. A spelling that looks like an extent pin and is not. DECIDED
                       2026-07-30 (revised after review): remove the PAYLOAD FROM THE TYPE, not the
                       spelling from the grammar — `AxisKind` becomes `| real | nat`, which deletes
                       the ℝ[…]/ℕ[…] productions with it and makes the state a TYPE error, so no
                       CompileError and no test are needed. AxisKind is mentioned in only 5 places in
                       LeanNCD/ and is not serialized, so the payload is provably write-only. Cost:
                       70 mechanical construction-site edits across 20 files. An earlier decision
                       here (reject the form with `unsupportedAxisKindSize`) was WRONG — it left the
                       state representable for programmatic ASTs and contradicted the `iter`
                       reasoning in the same spec (make bad states ungrammatical, not validated); a
                       check can be bypassed by a new entry point, as Task-0/#4 showed. Wiring the
                       size in was also rejected (tl_size yields a general SizeExpr; explicitSizes is
                       HashMap UID Nat, so only `.lit` could be wired — symbolic extents need the
                       affine solver, a feature not a fix). SEPARABLE from #5b: ship it ahead of the
                       spike. Side effect: tl_size/elabTLSize become reachable only from
                       test/DSL/SizeExprTest.lean — KEEP them. H IS AN UNFINISHED FEATURE, NOT CRUFT:
                       papers/leanncd.md:1421-1431 SPECIFIES the bracket forms ("Layer 1", §14.3), so
                       the parser + AST field were built to spec and only the consumer was never
                       written — which is also why 15 oracle sites populate the kind size. Deleting
                       tl_size is mechanically safe (cost = 4 run_cmd blocks at SizeExprTest:40-67;
                       the 20 SizeExpr guards at :10-38 don't touch it) but is a SPEC DEVIATION
                       needing a paper update, so it is a judgement call, not cleanup. The paper's own
                       resolution is to FINISH it: wire ℕ[n] to the affine size solver (out of scope).
                       Same bucket: SizeExpr.eval has ZERO production callers (Base/SizeExpr.lean:
                       21-27, self-recursive only); SizeExpr is used in production only as inert
                       labels. Keeping these is not the retracted "keep it for the future solver"
                       argument — that kept a REACHABLE trap; Part 2b removes reachability, after
                       which no program can reach tl_size and it cannot mislead anyone.
        · Wave A is now fully closed: #5b (Parts 1/2a/3/4 — the `iter` keyword breaking change)
          shipped 2026-07-31, joining G and H, both DONE 2026-07-30. #6 (the broader boundary DECODER defaults —
          realizeStMat zero-fill, realizeBrBaseP, AcsetCodec, realizeSBr → empty identity) is
          Stage-5 bridge-hardening, not Wave A, per the audit's own assignment.

Wave B  THE BACKEND CONTRACT — Spike 4, resequenced (highest priority)
        ⚠️ PARTIALLY DONE 2026-07-31 (d08a1d8..383bc0b) — see
        `docs/superpowers/plans/2026-07-31-wave-b-eval-unification.md`. 4a, 4d, and 4c below are
        fully DONE. Of 4b, only `Combine.unit1` (the missing multiplicative identity) landed —
        `Combine` stayed the reference evaluator's own record, function-valued as before. The
        closed, serializable `ContractionAlgebra`/`ScalarBinOp` tag classifier this line
        originally called for was explicitly NOT built: that plan's own Global Constraints
        deferred it as having no consumer yet outside the EvalPlan/backend work below (Wave C),
        and building it speculatively ahead of that consumer would be exactly the premature
        abstraction this project's CLAUDE.md asks not to do. Whoever picks up Wave C should build
        `ContractionAlgebra` there, against a real `EvalPlan` consumer, not assume it already
        exists from this line.
        · ContractionAlgebra + BOTH identities   (= 4b + the shared classifier)
              factorOp/factorId/reduceOp/reduceId; `Combine` becomes one interpretation
        · 4a  ✅ unify seeded/unseeded assignment — ports the fail-loud unsized-axis check
                                                   to the scan path (closes a bug)
        · 4d  ✅ ResolvedNonlin + checked NormAxis — cheap now that Spike 3a has landed
        · 4c  ✅ one dtype-aware worker            — kills the plain-vs-scan divergence that
                                                   Appendix A warns must not be recreated
        dependencies:  4b → 4a → 4c ;  Spike 3a ✅ → 4d → 4c

Wave C  ✅ DONE 2026-08-07 (C0-C4, C6; C5 deferred) — Minimal EvalPlan (E4), the first checked
        backend boundary
        · canonical, versioned (`admittedVersion = 1`); no Lean/backend callbacks — **not yet
          serializable to bytes**: hashing/wire-encoding was C5, deliberately deferred (A.9) —
          nothing outside one process's own lifetime needs it yet
        · SHIPPED SCOPE IS SCAN-FREE, exactly as scoped here: only `.plain` assignment steps are
          admitted; no `ScanPlan`/`.scan`/`.scanPre` exists anywhere in the checked IR. **Scans
          are still not in** — see Wave F below, which remains unstarted and unscoped beyond the
          one-line note it already had before Wave C began.
        · real sum-product contraction, identity nonlinearity, integer-affine reads
          (shifts/scales/multi-axis), zero-padded OOB reads, chained/intermediate tensors; typed
          capability rejection for everything else (11 `CapabilityError` categories — see
          `papers/wave_c_capability_manifest.md` §3 for the full accept/reject boundary)
        first milestone is NOT "JAX runs a model" — it is: every checked EvalPlan in the
        declared reference64 fragment either matches DenseTensor or is rejected with a
        typed capability error before Python starts. **Achieved, counted, not estimated:**
        3,832/3,832 `PropertyOracle.enumPrograms` entries agree bit-for-bit against `DenseTensor`,
        0 rejected (`Eval.Plan.DifferentialTest`) — see the differential-sweep scope caveat in
        Learnings below before citing this number for a capability the generator doesn't vary.
        · proposal ✅ DONE 2026-08-03, revised 2026-08-05 — `papers/wave_c_evalplan_proposal.md`
        · C0 ✅ (executable contract) → C1 ✅ (signature-driven shape inference) → C2 ✅ (checked
          local kernel) → C3 ✅ (checked graph) → C4 ✅ (source compiler + representation boundary)
          → **C5 deferred** (canonical bytes/fingerprint — no consumer yet; `deriving Hashable`
          would suffice in-process if one ever appears) → C6 ✅ (adversarial audit + handoff:
          closed 5 real coverage gaps, made `Plan/` discoverable from `import LeanNCD`, published
          the capability manifest). Full detail in the Landed table above; this row is now a
          pointer, not the source of truth — read `papers/wave_c_capability_manifest.md` first.

Wave D  ✅ DONE 2026-08-01 (a3098c0..c86005e) — 4g typed scatter policy (CollisionReduce;
        separate RHS agg from collision reduce)
        · follow-up ✅ DONE 2026-08-01 (047b023..fd72d48) — checkScatterNoScan, a compile-time
          gap Wave D's own review surfaced (scatter+scan-iteration-slot compiled when it should
          reject); the OTHER gap it surfaced (broadening `LHSSlot.collapses`) stays deferred —
          confirmed no concrete axis sizes exist at `lowerArith`'s point in the pipeline
Wave E  ✅ DONE 2026-08-02  4e → 4h → 4i  diagnostics split, structured errors, EvalReport
        · compiler-independent scheduled worker + diagnostic-preserving source entry are in place
Wave F  NOT STARTED, NOT SCOPED beyond this note — this is where scans enter the checked-plan
        world. 4f  decompose evalScan — AFTER the EvalPlan boundary (now built, Wave C), not
        before. Needs an explicit `ScanPlan` state/transition/geometry/boundary/order/causality
        design (proposal §7/§A.12) that Wave C deliberately did not attempt — nothing in C0-C6
        assumes scan support exists, and the capability manifest documents its absence as a
        stated non-goal, not an oversight.
        · then one-axis coupled lax.scan, then flattened multi-axis
Wave G  Backends (E10): PyTorch eager first (fast semantic bring-up; torch_compile/
        prototype exists) → JAX jit as the stricter static backend → optimization fast
        paths, each guarded by generic-lowering differential tests
```

### Learnings from Wave C (2026-08-07 retrospective)

Six slices (C0-C4, C6) executed via `superpowers:subagent-driven-development`, one worktree and
one whole-branch review each; C5 planned-then-deliberately-not-built. What generalizes beyond
this Wave:

- **The final whole-branch review is the tier that earns its keep, every time.** Per-task reviews
  (3-4 per slice, all clean) never once found what the whole-branch pass found: C0's self-
  contradicting capability matrix, C1's tautological parity fixtures, C4's 4 real coverage gaps,
  C6's false coverage-attribution claim and "matches A.2 exactly" overclaim. Each was invisible in
  any single task's diff by construction — the defect was a relationship *between* tasks, or
  between a claim and code the task never touched. Do not trim this step to save a dispatch.
- **A fix wave can reintroduce the same failure mode it was sent to fix.** C6's final-review fix
  wave corrected a false coverage-attribution in the capability manifest — and its own replacement
  citation was *also* wrong (it cited a rejection test as confirming a capability). The scoped
  re-review caught it. Lesson: a fix-wave re-review must independently re-check factual/citation
  claims the fix rewrote, not just confirm the flagged line changed.
- **A differential sweep's coverage claim is bounded by its generator, and that bound must be
  stated, not assumed.** `PropertyOracle.enumPrograms` pins both axes to size 2 and generates only
  single-axis affine reads — it was, until C6's review caught it, incorrectly credited with
  confirming zero/one-dimension and multi-axis-affine coverage it structurally cannot generate.
  Any doc citing a property-test sweep as evidence for a capability must check what the generator
  actually varies, not what the test *file* is titled.
- **A shipped subsystem is invisible until something makes it importable and documented.** C0-C4
  shipped 10 files and a working compiler; nothing outside `Plan/` itself could reach it — `import
  LeanNCD` didn't pull it in, and neither `AGENTS.md` mentioned it existed. This is exactly the gap
  the `slice-plan` skill's checklist doesn't cover (it verifies code, not discoverability) — worth
  adding "is the new subsystem reachable from where a reader already looks" to that checklist for
  the next multi-slice wave.
- **Defer infrastructure until a real consumer exists, even mid-wave.** C5 (canonical
  representation and codec) was the natural next slice by sheer sequencing momentum; stopping to
  ask "what actually needs this" collapsed it to "nothing yet" and saved a whole slice. The
  reasoning is recorded in A.9 specifically so it can be reopened cheaply if a real consumer
  (cross-process serialization, a stability-sensitive cache) appears later — deferral is not the
  same as foreclosure.
- **The commit-range citation convention (caret form, and which commit counts as "last") is now
  settled by precedent, not something to re-derive each time.** It recurred as a review finding in
  C2, C3, and C4's docs steps. C6's final reviewer resolved it definitively by reading the actual
  git history of every prior slice's DONE blockquote: the range always excludes the docs-authoring
  commit itself (matches C1-C4), but must include any *substantive* final-review fix-wave commit
  (the C3/C4 correction, `33e595e`). Cite this paragraph instead of re-litigating it next time.

### Independent — schedule anytime, parallel to the above

- **Spike 5** (`finalizeScans` decomposition) — behavior-dense; needs genuine test-first care.
- **Spike 6b/6c/6d** (RouteSpec `routeCore` elim, shared `ListMapM`, AcsetCodec split) — pure proof engineering.
- **Proof track** — quarantine `weave_unique` under `Experimental`; generated `sorryAx`/axiom-closure CI over a named trusted-core API; regenerate `SORRY_INVENTORY.md` from source (it currently contradicts the build). Keep the weave countermodel as a permanent model test.
- **St hexagons** proof spike; **cospan model** spike (unlocks E13 once scoped).
- **Phantom semiring parameter** — `TargetActegory`'s semiring type parameter is a
  parametricity witness with no live instance constraining it (finding #10, 2026-07-26 review).
  Separate a scalar-semantics interface from the shape action. E3-adjacent, but distinct from
  E3's `EvalSemiring` (that's the Eval-interpreter's Float-level semiring; this is the
  categorical Algebra/Construct machinery's type-level parameter).

### Deferred or blocked — with the reason

| Item | Status |
|---|---|
| **`BrBaseP` payload carry** (dtype/nonlin tags, `Agreement` conjunct-2 rework) | **Deferred** — buys nothing for execution; the routed path cannot execute. Revisit only if Python-acset fidelity becomes the priority. |
| **E5 eval ↔ routed agreement** | **Blocked** — needs a `Br` denotation into numbers (a separate deferred milestone); every `realize*` is `noncomputable`. |
| **Spike 3c** (`unaryFn` → `read`) | **Deferred** — `BrBaseP`/`EvalPlan` must first define how `UnaryOp` is preserved; merging the constructor early hides the loss. |
| **E13** (close `BrOp`) | Blocked on the cospan spike; and its real question is payload closure, not name closure. |

### Verification standard for every item above

`lake build` (full suite; **8,610 jobs** as of 2026-07-30) is the gate — it elaborates `LeanNCD` plus
the `Tests` library, firing every `#guard`/`example`-by-`rfl`. The portfolio pins numeric behavior,
reject paths, and the two historical wildcard bugs (FF5–FF8), so mechanical refactors are unusually
safe. Beyond Wave C, add the backend evidence tiers (emit → eager → jit → reference agreement →
cross-backend → device → export → VJP) and state which tier a claim rests on.

---

## Part II — Exploratory redesigns (creative, higher-risk, prototype-first)

Part I optimizes the architecture as it stands. This part asks a different question: *if the
recent fixes are symptoms, what would the design look like that doesn't produce them?* Each
idea below names the design pattern or functional-programming pearl it draws from, sketches
what it would concretely look like in this codebase, and ends with a verdict
(**spike-worthy** — could be planned today; **prototype-first** — build a throwaway proof of
concept before committing; **recorded-only** — worth knowing about, not worth doing now).
None of these are prerequisites for Part I, but they are not free-floating either: several
*replace*, *fold into*, *depend on*, or *should precede* a specific Part I spike. The per-idea
writeups note this inline; [How the explorations relate to the Part I spikes](#how-the-explorations-relate-to-the-part-i-spikes)
below consolidates it into one map so the interaction is decidable at planning time.

| # | Idea | Pattern provenance | Verdict |
|---|------|--------------------|---------|
| E1 | One traversal to rule the collectors | van Laarhoven traversals (Kmett lenses) | ✅ DONE 2026-07-23 |
| E2 | A typed core IR the pipeline narrows into | "Trees that grow" (GHC), typestate | **Wave B/D** (light form) — `ResolvedNonlin` is its first instance |
| E3 | Evaluate over an arbitrary semiring | algebra-parameterized interpreters | **folds into Wave B**'s `ContractionAlgebra` |
| E4 | EvalPlan: run the route's own affine maps | stride-based einsum; "one artifact, two consumers" | **CRITICAL PATH (Wave C)** — the backend-neutral IR |
| E5 | Executable denotation of the routed artifact | denotational semantics as executable spec | **split**: eval↔backend = Wave C gate; eval↔routed **blocked** (no `Br` denotation) |
| E6 | Property-based oracles for the pipeline | QuickCheck / metamorphic testing | ✅ DONE 2026-07-12 |
| E7 | Accumulate compile diagnostics | the Validation applicative | spike-worthy |
| E8 | Open registration of unary functions | environment extensions, command macros | recorded-only |
| E9 | Datatype-generic acset codecs | custom `deriving` handlers | recorded-only |
| E10 | Stage the interpreter into a code generator | Futamura projections | **THE DELIVERABLE (Wave G)** — PyTorch eager, then JAX jit |
| E11 | Do UIDs earn their keep? | locally-nameless discipline | investigation |
| E12 | Named simp sets for the proof domains | mathlib attribute hygiene | spike-worthy (tiny) |
| E13 | Generators for `Br` — closing `BrOp`, promoting E6's laws to theorems | GHC's Core as a small closed generating set; System FC | investigation → spike-worthy |
| E14 | A simplifier: local algebraic rewrite rules over the DSL AST | GHC's Simplifier + `RULES` pragma; worker/wrapper; specialization; CSE | spike-worthy (after E2) |

### How the explorations relate to the Part I spikes

Each exploration sits in one of five relationships to the concrete spikes. The distinction
matters for planning: two must be *decided at a specific spike* (you cannot do the spike its
plain way and add the exploration later without wasted work), two are worth doing *before* the
spikes they protect or reshape, and the rest are genuinely independent — pull them in whenever.

| Idea | Relationship to Part I | When to act |
| ---- | ---------------------- | ----------- |
| **E1** (one traversal) | ✅ **Landed** — replaced **2b** (the axis-collector towers) plus `mapUID` and `TermTraversable` (its `Id` case). **2a** (reads) was *not* subsumed — `traverseAxes` focuses on `AxisSpec`, so a read's tensor name never reaches the effect — and was done separately via **Approach D** (`Factor.read?`). | *Done (E1 merged; 2a via Approach D).* |
| **E12** (named simp sets) | **Folds into** Spike 6 | *During Spike 6* — register the lemmas as you consolidate them, not as a separate pass. |
| **E3** (semiring) | **Depends on** Spike 4a/4b — it is their payoff (`unit1` threaded, one evaluator body) | *After Spike 4.* Not a competitor to Spike 4; do not attempt before it. |
| **E10** (codegen) | **Depends on** E4 (its `EvalPlan` is ~80% of the specialization) | *After E4*, and only once the Python-target work is actually scheduled. |
| **E6** (property oracles) | ✅ **DONE 2026-07-12** — the regression net Spikes 4/5 and E4 can now build against | Landed early as intended; the scan-unrolling oracle is precisely what de-risks Spike 5's `finalizeScans` rewrite and E4's plan compiler, whenever those are picked up. |
| **E11** (UID investigation) | **Precedes/reshapes** Spike 2 — a "yes, delete UIDs" outcome changes what 2b/2c relocate | *Before committing Spike 2* — one focused day. If UIDs survive, Spike 2 proceeds unchanged; if not, 2b/2c shrink or move. |
| **E4** (EvalPlan) | **Overlaps** Spike 4 — rewrites the same `Contract`/`Gather`/`Scatter` internals Spike 4 unifies | *Decide at Spike 4.* If E4 is on the roadmap, weigh how much of Spike 4's internal unification (4c/4d/4f) it would supersede before investing there; keep 4a/4b regardless (E4 builds on them, as E3 does). |
| **E2 light** (typed core IR) | **Overlaps** the Wave-2 executable spikes (3–5) — `CoreStmt` makes unwritable the invariants 3/4/5 only document | *After Spikes 3–5*, as their typed successor — or fold the `Recurrence` structure into Spike 5 if attempted concurrently. |
| **E5** (executable denotation) | **Independent** — new executable spec; complements proof-track Spikes 6/7, replaces nothing | Anytime; cheap to start incrementally. |
| **E7** (Validation applicative) | **Independent** — a *Compile*-layer change (`resolveDecls`/`checkReadRanks`/`checkDtypes`), distinct from Spike 4h's *Eval*-layer `EvalError` | Anytime; self-contained. |
| **E8** (open unary registration) | **Independent, recorded-only** — Spike 3b already shrinks the syntax/elab share | Deferred; revisit only if the function inventory starts growing monotonically. |
| **E9** (generic codecs) | **Independent, recorded-only** — Spike 6d's combinators already capture most of the line savings | Deferred; revisit only if the acset table inventory grows. |
| **E13** (`Br` generators) | **Depends on** a cospan wiring model that Spike 7b *names* but does not schedule — this is not yet a task anywhere in this doc; **informed by** Spike 3a (the same closed-generating-set move, already worked for `Nonlin`); **feeds** E5/E6 | *Budget the cospan model itself first* (Wave 3b, alongside the St-hexagons proof spike) — E13's closure question is only answerable once it exists. Do Spike 3a before attempting E13's own investigation; it's a worked precedent for the same move. |
| **E14** (simplifier) | **Depends on** E2 (a stable `CoreStmt` to rewrite over); **absorbs** the CSE/scan-specialization follow-ons E4 opens up; **precedes** E10 if both are pursued (E10's Futamura-style specialization is more effective over E14's already-simplified/unrolled programs than over the raw interpreter) | *After E2*, opportunistically once E4 lands (its plan fragments make CSE/specialization cheap to implement); before E10, if E10 is ever scheduled. |

**So: should the explorations come first?** Mostly no — do the Part I spikes on their own
schedule and pull each exploration in at the point above. The two exceptions were **E6** and
**E11**: E6 was the safety net worth having in place before the behavior-dense spikes (4, 5) and
E4 touch anything (✅ done 2026-07-12 — see E6 above), and E11 is a one-day question worth
answering before Spike 2 invests in relocating UID-keyed accessors. **E13** is a third kind of
exception, in the opposite direction:
it cannot come first even if resourced, because its prerequisite — a scoped cospan wiring model
— doesn't exist as a task anywhere yet; scoping that model (Wave 3b) is the first available step,
not E13's own investigation. The remaining sequencing among the explorations themselves
(E6 → E3 → E4 → E5) is covered in [How the exploratory ideas compose](#how-the-exploratory-ideas-compose).

> **⚠️ The phase diagram that used to live here has been REMOVED (2026-07-30).** It duplicated —
> and by then contradicted — Part I's ordering, notably still showing `Spike 4: 4a → 4b first`
> (backwards; both contraction identities must exist before the seeded/unseeded merge) and `E4` as an
> optional "decision point" (it is now the critical path). **There is exactly one work order:
> [Suggested spike ordering and dependencies](#suggested-spike-ordering-and-dependencies).** Consult
> it, not this section, for sequencing.

What remains Part II's own contribution is *where each exploration slots into that single order*:

| Exploration | Placement in the authoritative order | Note |
|---|---|---|
| **E6** property oracles | ✅ **DONE** 2026-07-12 | the regression net Waves B/C build against |
| **E11** UID investigation | ✅ resolved before the Spike 2 commit | — |
| **E1** one traversal | ✅ **DONE** 2026-07-23 | absorbed Spike 2b |
| **E4** `EvalPlan` | **Wave C — critical path, not optional** | the first checked backend boundary |
| **E3** semiring evaluation | folds into **Wave B**'s `ContractionAlgebra` | 4b's ⊗-unit is its prerequisite, and the algebra *is* its payoff |
| **E2** (light) checked boundaries | **Wave B/D** — `ResolvedNonlin` (4d) is its first instance; `SizedScan`/`ValidatedScatter` follow in D | do it selectively at boundaries, not by indexing the whole compiler |
| **E10** interpreter → codegen | **Wave G** — the deliverable | PyTorch eager, then JAX jit |
| **E5** denotation/agreement | **split**: eval↔backend is Wave C's gate; eval↔routed is **blocked** on a `Br` denotation | see the Deferred table |
| **E12** named simp sets | folds into Spike 6 (independent track) | — |
| **E7** accumulate diagnostics | anytime; self-contained. Overlaps Wave E's structured errors — do them together | — |
| **E13** close `BrOp` | blocked on the cospan spike | and its real question is *payload* closure, not name closure |
| **E14** simplifier | after E2; before E10 if both are pursued | — |
| **E8, E9** open unary registry / generic codecs | recorded-only; revisit if inventories grow | — |

One independent item is worth not deferring indefinitely despite being off the critical path:
scoping the **cospan wiring model** is Spike 7b's own flagged gap (`brCancelPoint` is parked on it,
not just E13), so it earns its keep regardless of whether E13 is ever pursued.

### E1. One traversal to rule the collectors (van Laarhoven)

> **Prototype result (IdxExpr slice only, 2026-07-15):** `test/DSL/TraverseAxesSpike.lean`
> tested whether one `traverseAxes` definition subsumes `IdxExpr.mapUID`/`specsIdx`/
> `idxAxisUIDs` for the non-recursive `IdxExpr` node. All three equivalence theorems closed
> cleanly with sound, hand-written proofs — no universe issues, no typeclass diamonds. Two
> are fully computational with zero axioms; the third uses only the standard axioms `propext`
> and `Quot.sound` from a Mathlib lemma. No `sorry`, `admit`, or custom axioms were needed.
> This does **not** yet decide E1 for `BoolExpr`/`PredArith` or the rest of the AST — see
> `docs/superpowers/specs/2026-07-15-e1-traverseaxes-prototype-design.md` for the full go/no-go
> criteria and what remains before committing to E1 broadly or falling back to Spike 2a/2b.
> (**Outcome:** E1 was adopted and replaced the axis collectors, i.e. **2b**; **2a** — reads — was
> not covered by `traverseAxes` and was done separately via Approach D, `Factor.read?`.)
> (**Correction, since attempted:** the phrase "mutually-recursive `BoolExpr`/`PredArith` cluster"
> above was inaccurate — `PredArith` recurses only into itself and `IdxExpr`; `BoolExpr` recurses
> into itself and `PredArith`, one direction only, so there's no cycle. PredArith has since been
> attempted — see the next blockquote below.)

> **Prototype result (PredArith slice, 2026-07-15):** extended
> `test/DSL/TraverseAxesSpike.lean` to `PredArith.traverseAxes`, testing genuine self-recursion
> (`.mul`/`.iabs`) and composition with the already-proven `IdxExpr.traverseAxes` (via
> `.embed`) — both risks the IdxExpr-only slice couldn't test. 2 of 3 theorems closed, both
> independently verified sound: `traverseAxes_const_eq_specsPred` (collect AxisSpecs) and
> `traverseAxes_const_eq_predAxisUIDs` (collect UIDs). Both use real induction with genuine,
> correctly-used inductive hypotheses for the `.mul` and `.iabs` self-recursive cases, and
> delegate cleanly to the already-proven `IdxExpr` slice's lemmas for the `.embed` case. The
> third theorem (`traverseAxes_id_eq_predMapUID`, the remap) did not close — not due to
> proof-search failure, but because `PredArith.mapUID` is declared `partial def` with genuine
> self-recursive cases (`.mul`/`.iabs` call it recursively), which causes Lean to generate zero
> equation lemmas for the entire definition, even for the non-recursive `.embed` case. This is
> an unrelated production-code-style limitation, not a flaw in the `traverseAxes` technique
> itself. `PredArith.traverseAxes` required no `partial` annotation — it compiled as ordinary
> structural recursion. This still does **not** decide E1 for `BoolExpr` (same shape of
> self-recursion, untested) or the rest of the AST — see
> `docs/superpowers/specs/2026-07-15-e1-traverseaxes-predarith-design.md` for the full go/no-go
> criteria and what remains.

Spike 2 deduplicates the collectors by sharing functions. The pearl-level fix is stronger:
almost every function in `Traverse.lean`, the `specs*` family, and the `*AxisUIDs` family is
the *same* traversal instantiated at a different applicative functor:

```lean
def Factor.traverseAxes [Applicative f] (g : AxisSpec → f AxisSpec) : Factor → f Factor
-- rename/remap  = traverseAxes at Id        (subsumes Factor.mapUID and friends)
-- collect specs = traverseAxes at Const (List AxisSpec)   (subsumes specsFactor…)
-- collect uids  = traverseAxes at Const (List UID)        (subsumes termAxisUIDs…)
```

One definition per AST node (`IdxExpr`, `BoolExpr`, `Factor`, `LHSSlot`, `Stmt`), and every
mapper/collector — present and future — is a two-line instantiation. A `Const` applicative is
~5 lines (Lean core doesn't ship one). The catch discovered in review: the rebuild tower maps
`UData → UData` (`Traverse.lean`) while the collectors return `AxisSpec` — the two views of
"an axis occurrence" must be reconciled into one canonical occurrence type before the
traversal can subsume both. That reconciliation is itself clarifying (it answers "what IS an
axis occurrence?" once), but it's why this is prototype-first rather than a drop-in
replacement for Spike 2. If the prototype works, it *replaces* Spike **2b** (the axis collectors) entirely and
makes `TermTraversable` (`Exec/Traversable.lean`) its `Id` special case. (**As shipped**, E1 = `traverseAxes`,
axis-focused — it did *not* subsume **2a** (reads); a read's tensor name never reaches the leaf effect. 2a was
done separately via Approach D, `Factor.read?`.)

*References:* Gibbons & Oliveira, [The Essence of the Iterator Pattern](http://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf) (JFP 2009) — traversal as applicative-functor iteration, the `Const`-vs-`Id` instantiation trick used above; van Laarhoven, [CPS-based functional references](https://www.twanvl.nl/blog/haskell/cps-functional-references) (2009); Kmett, [`lens`](https://hackage.haskell.org/package/lens) (the library that industrialized the encoding).

> **Prototype result (BoolExpr slice, 2026-07-15):** extended `test/DSL/TraverseAxesSpike.lean` to
> `BoolExpr.traverseAxes` — no new risk pattern versus the `PredArith` slice, a scaling/confirmation
> check (more constructors, one more composition layer). `BoolExpr.traverseAxes` compiled as
> ordinary structural recursion, no `partial` needed (matching `PredArith.traverseAxes`). Both
> collecting-direction theorems
> (`traverseAxes_const_eq_specsBool` and `traverseAxes_const_eq_boolAxisUIDs`) closed cleanly on
> the first build with the brief's proof scripts, independently verified axiom-clean, confirming
> the pattern generalizes across the full non-mutual layered stack (IdxExpr → PredArith → BoolExpr).
> The remap theorem's expected failure was confirmed with a single quick check (not a fresh search) —
> `BoolExpr.mapUID` hits the same `partial def` + self-recursion + zero-equation-lemmas wall
> `PredArith.mapUID` did. This completes the layered (non-mutual-recursion) part of the AST below
> `Factor`; `Factor`/`LHSSlot`/`Stmt`/`Decl`/`TLProgram` remain open — see
> `docs/superpowers/specs/2026-07-15-e1-traverseaxes-boolexpr-design.md` for the full go/no-go criteria.

> **Prototype result (Factor slice, 2026-07-16):** extended `test/DSL/TraverseAxesSpike.lean` to
> `Factor.traverseAxes` — the first node carrying tensor names (`String`, untouched passthrough)
> and a `List IdxExpr` traversed via a nested sub-traversal (`Traversable.traverse (IdxExpr.traverseAxes
> g)`) rather than a bare per-element projection. Both collecting-direction theorems
> (`traverseAxes_const_eq_specsFactor` and `traverseAxes_const_eq_factorAxisUIDs`) closed cleanly
> with sound proofs — the new list-of-sub-traversal induction lemma worked via ordinary list
> induction, no friction beyond the expected shape. The remap theorem split per case: `.read` and
> `.unaryFn` both closed (the hoped-for outcome, confirming `Factor.mapUID`'s non-`partial`,
> non-self-recursive shape avoids the blocking wall), while `.iverson` was deferred pre-implementation
> as it requires `BoolExpr`'s own remap (the same `partial def`/zero-equation-lemmas wall). Every
> theorem attempted at implementation closed. Full `lake build` succeeded, 8,609 jobs,
> no `sorry`/`native_decide`. `ProdTerm`/`SumExpr`/`RHSExpr`/`LHSSlot`/`Stmt`/`Decl`/`TLProgram`
> remain open — see `docs/superpowers/specs/2026-07-16-e1-traverseaxes-factor-design.md` for the
> full go/no-go criteria.

> **Prototype result (ProdTerm slice, 2026-07-16):** extended `test/DSL/TraverseAxesSpike.lean`
> to `ProdTerm.traverseAxes` — the first non-inductive (record) node in the series, needing no
> `cases`/`induction` on `ProdTerm` itself. Both collecting-direction theorems closed cleanly,
> including the `termAxisUIDs` bridge — the first slice comparing directly against a real public
> production function (`termAxisUIDs`, from `Eval/Contract.lean:34-38`) rather than a local copy
> or extraction. The remap direction's blocking wall (`partial def`, zero equation lemmas)
> reappears here through the `List` of factors rather than through inductive case-splitting — a
> single `.iverson` anywhere in `p.factors` would sink an unconditional theorem — so instead of
> an unconditional theorem, a CONDITIONAL lemma (`traverseAxes_id_eq_prodTermMapUID_of_factors`,
> "if every factor in the list individually satisfies its own remap equality, the list-level
> equality follows") was attempted. The conditional lemma closed cleanly via list induction,
> representing a new proof shape not seen in prior slices (the first hypothesis-parameterized
> theorem). This resolution is expected to generalize cleanly to `SumExpr`, which has the
> identical one-field-record-wrapping-a-list shape one layer up (`structure SumExpr where terms :
> List ProdTerm`). Full `lake build` succeeded, 8,609 jobs, no `sorry`/`native_decide`.
> `SumExpr`/`RHSExpr`/`LHSSlot`/`Stmt`/`Decl`/`TLProgram` remain open — see
> `docs/superpowers/specs/2026-07-16-e1-traverseaxes-prodterm-design.md` for the full go/no-go
> criteria.

> **Prototype result (SumExpr slice, 2026-07-16):** extended `test/DSL/TraverseAxesSpike.lean` to
> `SumExpr.traverseAxes` — structurally identical to `ProdTerm` one layer higher (`structure
> SumExpr where terms : List ProdTerm`). All three theorems (2 collecting-direction, 1
> conditional remap) closed exactly as pre-verified during design — confirming the `ProdTerm`
> design doc's prediction that the conditional-lemma pattern generalizes mechanically across
> identically-shaped record-wrapping-a-list nodes, with zero implementation-time surprises. The
> UID-collecting theorem compares directly against the bare expression `s.terms.flatMap
> termAxisUIDs` rather than a new named def, since no `SumExpr`-level production function
> exists to copy or point at — a deliberate one-off exception to this file's usual pattern.
> Full `lake build` succeeded, 8,609 jobs, no `sorry`/`native_decide`. `RHSExpr`/`LHSSlot`/
> `Stmt`/`Decl`/`TLProgram` remain open — see
> `docs/superpowers/specs/2026-07-16-e1-traverseaxes-sumexpr-design.md` for the full go/no-go
> criteria.

> **Prototype result (RHSExpr slice + Nonlin building block, 2026-07-16):** extended
> `test/DSL/TraverseAxesSpike.lean` to `RHSExpr` — the first slice since `IdxExpr` needing
> genuinely fresh design work rather than a mechanical continuation. Bundled a new
> `Nonlin.traverseAxes` building block (the first `Option`-based traversal in the series, 9
> constructors including 3 carrying a mask) whose exhaustive match closes off, by construction,
> production's documented `specsNonlin` wildcard hazard. The `Nonlin` collecting-direction
> theorem (against a local `specsNonlin'` copy) closed cleanly; no UID-collecting theorem
> added (production never touches mask UIDs). Remap: `.identity` closes trivially, the masked
> case (demonstrated for `.softmax`; `.normalize`/`.l2normalize` follow the identical shape and
> were not separately proved) closes conditionally on its `BoolExpr` mask's own remap. Resolved
> a real production semantic
> asymmetry — `specsRHS` includes the nonlin mask's axes, `readAxisUIDs` deliberately excludes
> them — with two named traversal functions (`traverseAxesWithMask`/`traverseAxesNoMask`)
> rather than a flag. `traverseAxesWithMask` serves AxisSpec-collecting and remap;
> `traverseAxesNoMask` serves UID-collecting only (compared directly against the real
> `readAxisUIDs`). The remap theorem (`traverseAxes_id_eq_rhsExprMapUID`) is conditional on TWO
> independent hypotheses (about `r.body` and `r.nonlin` separately) — the first slice with a
> two-hypothesis conditional remap. All theorems in both tasks closed exactly as pre-verified
> during design (staged, built, reverted before implementation) — zero implementation-time
> surprises. Full `lake build` succeeded, 8,609 jobs, no `sorry`/`native_decide`.
> `LHSSlot`/`Stmt`/`Decl`/`TLProgram` remain open — see
> `docs/superpowers/specs/2026-07-16-e1-traverseaxes-rhsexpr-design.md` for the full go/no-go
> criteria.

> **Prototype result (LHSSlot slice, 2026-07-16):** extended `test/DSL/TraverseAxesSpike.lean`
> to `LHSSlot.traverseAxes` — the simplest traversal shape in the series (4 of 5 arms apply `g`
> directly to a bare `AxisSpec`, no sub-traversal; the 5th delegates to the already-proven
> `IdxExpr.traverseAxes`). The collecting-direction theorem (`traverseAxes_const_eq_specsLHS`,
> against a local `specsLHS'` copy) closed cleanly. The remap theorem
> (`traverseAxes_id_eq_lhsSlotMapUID`) closed FULLY UNCONDITIONALLY — the first time since
> `IdxExpr` itself — because `LHSSlot.mapUID` is flat/non-partial and its only dependency,
> `IdxExpr.mapUID`, never touches `BoolExpr` and so never hits the `partial def`/
> zero-equation-lemmas wall every intermediate slice needed a hypothesis to work around.
> Explicitly out of scope: `lhsAxisUID?`/`freeAxisUIDs` (`Eval/Shape.lean:501-506`,
> `Eval/Contract.lean:29`) are classify-and-filter functions, not collectors — `.affine` maps
> to `none` there, not "the axes inside its `IdxExpr`" (which is what any instantiation of this
> traversal produces instead) — so no instantiation of `LHSSlot.traverseAxes` can reproduce
> them; this is a different function shape, not a missing production counterpart. Full `lake
> build` succeeded, 8,609 jobs, no `sorry`/`native_decide`. `Stmt`/`Decl`/`TLProgram` remain
> open — see `docs/superpowers/specs/2026-07-16-e1-traverseaxes-lhsslot-design.md` for the
> full go/no-go criteria.

> **Prototype result (Stmt slice, 2026-07-16):** extended `test/DSL/TraverseAxesSpike.lean` to
> `Stmt` — 3 constructors: `.assign`/`.scatter` (structurally near-identical, `.scatter` adds a
> trailing `ScatterOpts`) and `.recurMorphism` (a "pre-built morphism escape hatch" carrying one
> bare `AxisSpec` and an untouched `ThreadedComposed`, the presentation-layer routing-DAG type —
> confirmed unrelated to the AST/traversal layer). Both collecting-direction theorems closed
> cleanly — one against a local `specsStmt'` copy (`traverseAxes_const_eq_specsStmt`), and one
> against the real, private-backed production `Stmt.uids` (`traverseAxes_const_eq_stmtUids`) via
> the new `Stmt.uids_eq` bridge, the first slice in the series to reach a real, private-backed
> production function this way. All three remap theorems closed as pre-verified:
> `traverseAxes_id_eq_stmtMapUID_recurMorphism` fully unconditionally, and
> `traverseAxes_id_eq_stmtMapUID_assign`/`_scatter` each conditional on exactly one hypothesis
> about `RHSExpr.traverseAxesWithMask`. A genuinely new obstacle surfaced: `Stmt.uids` is public
> but built entirely from `private` helpers (`specsStmt`/`specsLHS`/`specsRHS`/... down to
> `specsIdx`), and Lean cannot delta-reduce through a private declaration from outside its file
> even via a public wrapper — a strictly harder wall than the `partial def`/zero-equation-lemmas
> wall every slice since `PredArith` has navigated. Resolved by adding `Stmt.uids_eq` — a theorem
> restating `Stmt.uids` in terms of the already-public `idxAxisUIDs`/`boolAxisUIDs`/
> `termAxisUIDs`, proved via six new private bridge lemmas — to
> `LeanNCD/DSL/Pipeline/Structural.lean` itself: **the first production-file change on this
> branch**, requiring a new cross-layer import (`LeanNCD.Eval.Contract`) that breaks the
> deliberate non-crossing layering between `DSL/Pipeline` and `Eval` for the first time. Every
> addition is marked with a `SPIKE EXCEPTION` comment carrying exact `TO REVERT:` instructions
> (search that literal string in `Structural.lean`), so it can be cleanly removed independent
> of whether E1 itself is adopted.
> A smaller dependency gap also surfaced: no prior slice needed a `Nonlin` UID-collecting
> theorem, since `readAxisUIDs` deliberately excludes the nonlin mask while `Stmt.uids` includes
> it — closed with one new lemma, `traverseAxes_const_eq_nonlinAxisUIDs`, structurally identical
> to the existing AxisSpec-collecting one at the UID layer instead. Full `lake build` succeeded,
> 8,609 jobs, no `sorry`/`native_decide`, across both the `Structural.lean` production-file
> change and the spike-file extension. `Decl`/`TLProgram` remain open — see
> `docs/superpowers/specs/2026-07-16-e1-traverseaxes-stmt-design.md` for the full go/no-go
> criteria, including the note that any future slice needing to reach another
> private-and-publicly-wrapped production function should expect to repeat this pattern, not
> assume it was a one-time cost.

> **Prototype result (Decl slice, 2026-07-17):** extended `test/DSL/TraverseAxesSpike.lean` to
> `Decl.traverseAxes` — the flattest traversal shape in the series: no constructor wraps a
> nested `IdxExpr`/`BoolExpr`/`RHSExpr`/`LHSSlot`, every arm bottoms out directly in a bare
> `AxisSpec` or a `List AxisSpec`. The collecting-direction theorem
> (`traverseAxes_const_eq_specsDecl`, against a local `specsDecl'` copy) closed cleanly. The
> remap theorem (`traverseAxes_id_eq_declMapUID`) closed FULLY UNCONDITIONALLY, matching
> `LHSSlot`'s and `IdxExpr`'s precedent — `Decl.mapUID` is flat/non-partial and its only
> dependency, `AxisSpec.mapUID`, carries no `partial def`/self-recursion wall anywhere in its
> own chain. This is the first slice calling `Traversable.traverse` directly on a bare
> `List AxisSpec` rather than through a node-level `traverseAxes` wrapper, surfacing two
> naming/inference details no prior slice needed: `Traversable.traverse`'s own implicit
> applicative parameter is named `m`, not `f`; and a direct `ConstL`-typed call needs an
> explicit type ascription on its target lambda, since `ConstL` erases its second type parameter
> and Lean can't otherwise infer it. Checked whether `Decl` reproduces `Stmt.uids`'s
> private-helper-chain wall (per the checkpoint's specific caution) and confirmed it does NOT:
> `Decl` has no public wrapper at all (no `Decl.uids`, no `declAxisUIDs`) — the only production
> collector touching it, `specsDecl`, is consumed only by `TLProgram`'s own private/public
> chain. **No production-file change was needed this slice.** That risk is flagged forward
> instead: `TLProgram.axisNames` has the identical public-wrapper-over-private-helpers shape
> that trapped `Stmt.uids`, so the next (final) slice should expect to navigate it. Full `lake
> build` succeeded, 8,609 jobs (module-level build green at 8,487 jobs across three
> checkpoints along the way), no `sorry`/`native_decide`; `specsDecl'` confirmed byte-identical
> to production's private `specsDecl`. `TLProgram` remains open — see
> `docs/superpowers/specs/2026-07-17-e1-traverseaxes-decl-design.md` for the full go/no-go
> criteria.

> **Prototype result (TLProgram slice, 2026-07-17):** extended `test/DSL/TraverseAxesSpike.lean`
> to `TLProgram.traverseAxes` — **the FINAL AST node.** It combines a `List Decl` sub-traversal
> and a `List Stmt` sub-traversal via `<$> ... <*>`; the collecting-direction theorem
> (`traverseAxes_const_eq_specsProgram`, against a local `specsProgram'` copy built from the
> already-proven `specsDecl'`/`specsStmt'`) closed cleanly. The remap theorem
> (`traverseAxes_id_eq_tlProgramMapUID`) is conditional on exactly ONE hypothesis, about
> `p.stmts` — `p.decls` needs none, since `Decl`'s own remap is already fully unconditional. It
> closed exactly as pre-verified, with zero implementation-time surprises. Two genuinely new
> wrinkles surfaced while scoping: (1) there is no named `TLProgram.mapUID` — the remap logic is
> written inline in the `TermTraversable TLProgram` instance — so this slice's remap theorem
> targets the real `TermTraversable.traverseUID f p` directly (confirmed against the actual
> instance at `Traverse.lean:79-80`), the first slice to do so rather than pointing at a named
> production function or a local copy; (2) `TLProgram.axisNames` confirmed the checkpoint's own
> prediction that it shares `Stmt.uids`'s public-wrapper-over-private-helpers shape, but adds a
> `.eraseDups`/`.name`-projection step beyond anything `Stmt.uids_eq` needed — scoped out as a
> deliberate non-goal (matching `Nonlin`'s and `LHSSlot`'s own non-goals), so **no
> production-file change was needed this slice either**, despite the checkpoint's prediction: the
> wall is real, but this scoping choice avoids needing to cross it. Module build succeeded at
> 8,487 jobs, full-project build at 8,609 jobs, no `sorry`/`native_decide`. **E1 has now achieved
> full AST coverage** — every node in `DSL/Ast.lean` (`IdxExpr` through `TLProgram`, eleven
> slices) has a `traverseAxes` definition and at least one proven equivalence in each direction,
> with zero `sorry`/`native_decide` anywhere in the series — see
> `docs/superpowers/specs/2026-07-17-e1-traverseaxes-tlprogram-design.md` for the full go/no-go
> criteria and what E1's own adoption decision against Spike 2a/2b would still need to weigh.
> (**Outcome:** adopted; E1 replaced **2b** (axis collectors); **2a** — reads — was done separately
> via Approach D, `Factor.read?`.)

> **Production migration — decision and motivation (2026-07-17):** the go/no-go decision above
> is **GO** — E1 is adopted, and production is being migrated off the three hand-maintained
> families (`mapUID`, `specs*`, `*AxisUIDs`) onto `traverseAxes`-based implementations. The
> motivation draws directly on the eleven slices above, not on this decision being asserted
> fresh:
>
> - **The original case for E1** (made before any slice was attempted, still holding after all
>   eleven): almost every function in `Traverse.lean`'s `mapUID` family, the `specs*` family, and
>   the `*AxisUIDs` family is *the same traversal instantiated at a different applicative functor*
>   — remap at `Id`, collect-`AxisSpec`s at `Const (List AxisSpec)`, collect-UIDs at
>   `Const (List UID)` (see the `Factor.traverseAxes` sketch and the surrounding discussion
>   earlier in this section). If it works, it *replaces* Spike **2b** (the axis collectors) entirely and makes
>   `TermTraversable` (`Exec/Traversable.lean`) its `Id` special case. It worked, across all
>   eleven AST nodes, with zero exceptions to the pattern's basic shape. (`traverseAxes` is axis-focused, so
>   **2a** — reads — was *not* subsumed; it was done separately via Approach D, `Factor.read?`.)
> - **Zero `sorry`/`native_decide` across the entire eleven-slice series** — every collecting-
>   direction theorem closed with a sound, kernel-checked proof, and every remap theorem that
>   *could* close (see next point) closed either fully unconditionally or via an explicit,
>   independently-verified hypothesis. This is a stronger correctness posture than production's
>   *current* code enjoys (see next point).
> - **A genuine defect in production's current `mapUID` family, found and characterized by the
>   `PredArith`/`BoolExpr` slices, that migration fixes as a side effect, not merely papers
>   over:** `PredArith.mapUID` and `BoolExpr.mapUID` are declared `partial def` with genuine
>   self-recursion, which causes Lean to generate **zero equation lemmas for the entire
>   definition** — nothing about their current behavior is mechanically provable today, in
>   production, right now. `PredArith.traverseAxes`/`BoolExpr.traverseAxes` compiled as ordinary
>   structural recursion with no `partial` annotation needed at all. Migrating `mapUID` to be
>   `traverseAxes`-derived doesn't just consolidate code — it closes a standing gap where two of
>   eleven nodes' remap behavior was entirely opaque to proof.
> - **A documented, previously-triggered production hazard that migration closes by
>   construction:** `specsNonlin`'s wildcard fallback (`_ => []`) is safe today only because every
>   *current* non-masked `Nonlin` variant happens to contribute no axes — its own module doc in
>   `Structural.lean` warns this already silently swallowed `l2normalize`'s mask once before a
>   fix. `Nonlin.traverseAxes` (built during the `RHSExpr` slice) is a 9-arm *exhaustive* match
>   with no wildcard, so Lean's totality checker forces any future masked variant to be handled
>   explicitly — the hazard cannot recur once `specsNonlin` is `traverseAxes`-derived.
> - **A real production semantic asymmetry, found and resolved once, that the migration must
>   carry forward rather than flatten:** `specsRHS` includes the nonlin mask's axes;
>   `readAxisUIDs` deliberately excludes them (per-term contraction scoping must not see mask
>   axes). The `RHSExpr` slice resolved this with two named traversal instantiations
>   (`traverseAxesWithMask`/`traverseAxesNoMask`) rather than a boolean flag — production's
>   migration reuses this exact resolution, not a fresh one.
> - **Proof that crossing into production, when a slice's scope demands it, is tractable and
>   reversible:** the `Stmt` slice needed the *only* production-file change across all eleven
>   slices (`Stmt.uids_eq`, bridging `Stmt.uids`'s private-helper-chain wall), landed cleanly with
>   a new cross-layer import, and was marked with `SPIKE EXCEPTION`/`TO REVERT` comments precisely
>   so that decision could be revisited independently of E1's own fate. Both `Decl` and
>   `TLProgram` later confirmed the *same risk shape* recurs (a public wrapper over private
>   helpers) without *forcing* a production change every time — whether a bridge is needed
>   depends on the exact scope chosen, not on the wall's mere existence. This distinction —
>   confirmed real, but not always requiring action — is exactly what this migration's own
>   sub-project 1 design doc (linked below) had to get right when it found `TLProgram.axisNames`'s
>   wall real but avoidable given its scoping choice.
> - **Explicit, load-bearing non-goals, established slice by slice, that the migration inherits
>   rather than re-litigates:** `lhsAxisUID?`/`freeAxisUIDs` (`LHSSlot`) are classify-and-filter,
>   not collectors — no instantiation of any traversal can reproduce them. `Decl.axisCount`/
>   `Decl.name`/`declName` are classify- or name-extraction-shaped, not axis-collector-shaped.
>   `TLProgram.axisNames`'s `.eraseDups`/`.name`-projection step is scoped out for the same
>   reason. All three stay hand-written, permanently outside this migration's scope — not
>   oversights, but functions of a genuinely different shape than `traverseAxes` produces.
>
> **Decomposition:** three sub-projects, safest-first — **`specs*` → `*AxisUIDs` → `mapUID`**.
> Blast-radius research done before scoping sub-project 1 found the risk profile is much smaller
> than the families' scale suggests: `mapUID` has exactly one production call site in total
> (`Structural.lean`'s `assignUIDs`, via `TermTraversable.traverseUID`); every `specs*` function
> is `private` with zero external callers by construction; `*AxisUIDs` has a small,
> well-understood set of callers. The same research surfaced a related-but-out-of-scope
> axis-collector ecosystem in `DSL/Pipeline/Lowering.lean` (`idxAxes`, a byte-for-byte duplicate
> of `specsIdx`; `dedupByUid`/`tensorAxes`/`ScanStmt.stepRetainedAxes`/`stepDegAxesMulti`, feeding
> `RouteSpec.lean`'s correctness proofs) — explicitly fenced off from this migration, not
> something a "unify everything with a similar name" pass should sweep in.
>
> Sub-project 1 (`specs*`) is scoped and designed at
> `docs/superpowers/specs/2026-07-17-e1-production-migration-specs-design.md`, on branch
> `e1-production-migration-specs`. It also introduces the one new piece of shared infrastructure
> every later sub-project builds on: a production home for `traverseAxes` itself
> (`LeanNCD/DSL/TraverseAxes.lean`, promoted verbatim from the spike, alongside the minimal
> `ConstL` applicative the spike used in place of Mathlib's `Monoid`-ceremony-requiring
> `Functor.Const`).

### E2. A typed core IR the pipeline narrows into ("trees that grow")

The scan-projection bug hunt surfaced a class of hazard Part I only documents, never removes:
**phase invariants that live in comments.** "Classification must happen before `splitNonlins`
because `splitStmt` reuses slots verbatim"; "after `lowerArith` every affine LHS is a
scatter"; "post-split, every statement is either pure contraction or pure nonlin" — each is
an invariant some later phase silently relies on, and each is exactly the kind of fact a type
can carry. Two escalation levels:

- **Light (spike-worthy): one extra type at the one boundary that has already bitten.**
  After `splitNonlins`, introduce `CoreStmt` — no `nonlin` field on contractions; nonlin
  application is its own constructor; scans carry an explicit
  `structure Recurrence where state : String; init : Stmt; step : Stmt` instead of parallel
  base/recur lists paired by name-matching. `eval`/`route` consume only `CoreStmt`. Payoffs:
  `buildStep`'s op selection becomes total by construction (no `.identity`-with-agg fallback
  chain), `evalScan`'s `stateNames` name-matching (`Eval/Scan.lean:99,126-133`) disappears,
  and the splitNonlins slot-reuse subtlety becomes unwritable rather than documented.
- **Heavy (recorded-only): phase-indexed programs.** `Prog (φ : Phase)` with type families
  narrowing field types per phase, GHC's "trees that grow" transplanted. Honest cost: Lean's
  `deriving` (`DecidableEq`, `Repr`, `ToExpr` — all load-bearing here for elaboration-time
  embedding) does not play well with indexed families, and every test constructing record
  literals pays churn. The light form captures most of the value; escalate only if a third
  phase-invariant bug appears.
- **A third option, worth recording between the two:** rather than narrowing *types* per
  phase, `CoreStmt` could instead carry small explicit *witness* terms for the invariants a
  phase currently relies on in a comment — closer to how System FC gave GADT refinement an
  explicit `Coercion`/`Cast` term instead of a smarter type index (see **E13**'s use of the
  same move for `Br`). Cheaper than the Heavy tier (no indexed family, no `deriving` fight),
  but only checkable, not enforced by the type — a middle ground, not yet worth choosing
  between with the others.

*References:* Najd & Peyton Jones, [Trees that Grow](https://simon.peytonjones.org/trees-that-grow/) (JUCS 2017; [arXiv](https://arxiv.org/abs/1610.04799)) — the type-family-per-phase idiom from GHC's own AST; Strom & Yemini, [Typestate: A Programming Language Concept for Enhancing Software Reliability](https://www.cs.cmu.edu/~aldrich/papers/classic/tse12-typestate.pdf) (IEEE TSE 1986) — invariants a type carries across phases.

### E3. Evaluate over an arbitrary semiring

`Combine {mul, combine, unit0}` plus Spike 4b's `unit1` is already a semiring struct with an
apology. Name it, finish it, and parameterize the *whole* interpreter (contract, scan,
scatter — `evalScatter` currently hardcodes ℝ and ignores `rhs.agg` entirely,
`Scatter.lean:40-47`):

```lean
structure EvalSemiring where
  add : Float → Float → Float := (· + ·);  zero : Float := 0
  mul : Float → Float → Float := (· * ·);  one  : Float := 1
```

Instances: `real`, `maxTimes`/`minTimes` (exist today as `Combine.max/min`), `bool` (exists),
plus the two that unlock known gaps for free: **`minPlus`** (`add := min, mul := (+), zero :=
+∞, one := 0`) closes KG-min's open half — shortest path, Viterbi, DTW — with *zero* new
evaluator code once the surface `agg(⊕,⊗)` notation (already designed, portfolio §19.2)
selects the instance; and **`logSumExp`** (with a max-shift for stability) gives the
log-domain HMM forward algorithm and numerically-stable marginalization. One interface, three
textbook algorithms. Mathlib connection worth recording: `Tropical` exists in mathlib, so if
the semiring interface is ever lifted from `Float` to a typeclass, the tropical instances can
be *certified* against mathlib's, giving the Eval track its first proof surface that isn't
shape-only. Sequencing: requires Spike 4a/4b (one evaluator body, `unit1` threaded) — this is
their payoff, not their competitor.

*Reference:* Dolan, [Fun with Semirings: a functional pearl on the abuse of linear algebra](https://stedolan.net/research/semirings.pdf) (ICFP 2013; [ACM](https://dl.acm.org/doi/10.1145/2500365.2500613)) — one semiring interface yielding transitive closure, shortest paths, and dataflow; the direct provenance for the `minPlus`/`logSumExp` instances above.

### E4. EvalPlan — make the evaluator run the same affine maps the route proves things about

The deepest structural observation from the review. The evaluator's per-point protocol —
build a `HashMap UID Int` coordinate, `evalIdx` each `IdxExpr` against it, silently `getD 0`
on a missing UID (`Gather.lean:8-12`) — re-implements, in dictionary form, exactly what the
presentation layer already represents as integer matrices: `idxDensify` (`Ast.lean:47`)
turns an `IdxExpr` into a dense coefficient row, and `elaborateReindexings` assembles those
rows into `StMatP`s that `RouteSpec` proves well-formed. The evaluator never touches them.

Proposal: a plan-compilation pass `Stmt → EvalPlan`, where each factor carries a densified
affine map (coefficient rows over `frees ++ termContr` + bias — i.e., an `StMatP` in all but
name) from the loop coordinate vector (a flat `Array Int`) to the source offset. Gather
becomes dot-product-and-index; the per-cell `HashMap` copy (`Contract.lean:94,186` — a full
map clone per contraction cell) disappears; scan seeds become one extra bias contribution
composed into the plan.

Three distinct payoffs: (1) **correctness** — the `getD 0` silent-default hazard (any
seeding/scoping bug reads plane 0 instead of failing) is structurally eliminated, since plan
compilation resolves every axis once, fail-loud; (2) **performance** — per-point cost drops
from hash-map allocation to integer arithmetic, asymptotically removing the dominant
interpreter overhead; (3) **architecture** — eval and route come to consume *the same
artifact*, which is precisely what makes E5's agreement statement natural. Cost: a genuine
rewrite of `Contract`/`Gather`/`Scatter` internals (~300 lines) with numeric-equivalence risk
— prototype on the scan-free fragment and diff against the current evaluator over the whole
portfolio before committing.

Named explicitly, this split *is* GHC's worker/wrapper transformation: a lean "worker" over the
dense affine-map/integer-coordinate representation, wrapped by a thin boundary that does the
`HashMap`/`Except` boxing today's `Contract`/`Gather` conflate into one function. The framing
generalizes past this one boundary — `evalScan`'s four numbered phases (Spike 4f) are a second
candidate worker/wrapper split once `EvalPlan` exists. Two further payoffs the plan
representation unlocks, folded into **E14** rather than duplicated here: once affine-map
fragments are directly comparable (not `HashMap`-driven dictionaries), **CSE** across statements
and **compile-time unrolling of small, statically-known scan lengths** (the same transform E6's
scan-unroll oracle already builds, reused as a real optimization rather than a test) both become
straightforward passes over the plan.

*References:* the [`numpy.einsum`](https://numpy.org/doc/stable/reference/generated/numpy.einsum.html) Einstein-summation convention — the stride/coefficient-row contraction spec this plan representation mirrors; Gill & Hutton, [The Worker/Wrapper Transformation](https://people.cs.nott.ac.uk/pszgmh/wrapper.pdf) (JFP 2009) — the general pattern this split instantiates.

### E5. An executable denotation for the routed artifact

`LeanNCD.lean:87-94` names the principal open seam: the categorical meaning of a runnable
artifact — `realize` and the §8 agreement — is deferred proof work. There is a cheaper
attack that changes the epistemic situation *now*: give the routed presentation an
**executable** semantics,

```lean
def evalBrBaseP    : BrBaseP → List DenseTensor → Except EvalError DenseTensor
def evalThreaded   : ThreadedComposed → (ext : List DenseTensor) → Except EvalError (List DenseTensor)
```

and state the agreement as a *test* long before it's a theorem: for every scan-free portfolio
program `p`, `evalThreaded (route p) ext ≈ TLProgram.eval p env`. (Scan-free because the
routed artifact deliberately collapses scan bodies — `LeanNCD.lean:84-86`; the fragment still
covers most of the portfolio.) This catches a whole class of bug RouteSpec cannot: RouteSpec
proves weave *shapes* are right, not that the wiring *means* the right contraction. It also
gives the eventual `realize`-agreement proof its computational skeleton — the denotation is
the function the proof will characterize. Cheap to start (`evalBrBaseP` for `contract`/
`relu`-class ops is a small wrapper over existing Eval pieces), incremental thereafter. This
denotation is also the natural home for **E13**'s question: once `evalBrBaseP` runs over `Br`'s
actual generators, whether those generators are closed stops being abstract — a gap in the
denotation *is* a gap in the generating set.

*Reference:* [Denotational semantics](https://en.wikipedia.org/wiki/Denotational_semantics) — giving a program a meaning as a mathematical (here, *executable*) function; the agreement test characterizes `route` against that denotation before the eventual `realize` proof does.

### E6. Property-based oracles (the tests the portfolio can't express)

> **✅ DONE — merged to `main` 2026-07-12** (commits `faedda0..456294a`; full `lake build` green,
> 8,611 jobs). All three laws landed: reordering + materialization (`Compare`/`Transforms`/
> `Gen`/`Oracle.lean`, 2026-07-11) and the scan-unrolling oracle (`ScanGen`/`ScanUnroll`/
> `ScanOracle.lean` + entry, 2026-07-12) — a curated six-template scan generator, a mechanical
> 1-D/2-D unroll transform (independent traversal order from `evalScan`'s own), and a new
> slice-extraction comparator (`sliceTensorAtMulti`, the inverse of `writeSliceAtMulti`). One
> real bug caught along the way, exactly the kind this spike exists to catch: template 6's
> `G[r,c]+A[r,c]` was silently computing multiplication instead of addition (all-zeros output),
> found only because the scan-unroll law checks the actual *value*, not just well-formedness —
> the well-formedness-only contract tests from the generator task had missed it entirely. The
> bullets below are retained as the record of the original design.

The portfolio pins ~130 hand-computed examples — excellent, but every one is a point. The
pipeline has *laws*, and Lean has a QuickCheck (`Plausible` — confirmed present in this
project's `lake-manifest.json` via mathlib). Three oracles stand out, in increasing order of
power:

1. **Reordering invariance:** independent top-level statements can be permuted without
   changing `eval` output (pins `topoSort`+`schedule` semantics, which Spike 1a is about to
   touch).
2. **Materialization invariance:** `Y := A + B·C` ≡ `T1 := A; T2 := B·C; Y := T1 + T2` —
   the per-term-scoping law, generalized from EC13/EC15's two points to all small programs.
3. **Scan-unrolling oracle (the strong one):** a scan over `axis l = L` must equal the
   hand-unrolled `L`-statement program with explicit indices. This is a *complete* semantic
   characterization of `evalScan` against the far simpler non-scan evaluator — precisely the
   oracle that would have caught the RC5/RC6-era silent-wrong-scan bugs mechanically, and the
   regression net under which Spike 5's `finalizeScans` rewrite and E4's plan compiler become
   low-anxiety changes.

The generator is the real work (small well-formed `TLProgram`s: 1–3 axes of size ≤3, 1–4
statements), and it need not round-trip through surface syntax — generate `Stmt` values
directly. Spike-worthy independent of everything else; highest value if landed *before*
Spikes 4/5/E4.

One further implication, expanded in **E13**: these three laws are exactly the shape of
equation GHC's `RULES` pragma promotes from "tested behavior" to "a trusted rewrite" — landing
E6 is a down-payment on eventually restating reordering/materialization/scan-unrolling as
theorems about `Br` itself, not just facts about `Eval`.

*References:* Claessen & Hughes, [QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs](https://www.cs.tufts.edu/~nr/cs257/archive/john-hughes/quick.pdf) (ICFP 2000) — the property/generator model (`Plausible` is its Lean port); Chen et al., [Metamorphic Testing: A Review of Challenges and Opportunities](https://dl.acm.org/doi/10.1145/3143561) (ACM Computing Surveys 2018; [tech report](https://www.cs.hku.hk/data/techreps/document/TR-2017-04.pdf)) — the invariance-relation oracles (reordering, materialization, scan-unrolling) above.

### E7. Accumulate compile diagnostics (the Validation applicative)

`FreshM = EStateM CompileError Nat` fails on the *first* error. For a human-facing DSL this
is a UX tax: fix one undeclared name, recompile, find the next. The classic fix is the
Validation applicative — same structure as `Except`, but `<*>` accumulates errors instead of
short-circuiting. The pipeline is already `mapM`-shaped in exactly the phases where
accumulation helps (`resolveDecls`, `checkReadRanks`, `checkDtypes` — per-statement,
independent checks); phases with genuine data dependence (`unifyAxes` onward) keep fail-fast.
Minimal version, no monad surgery: those three phases collect a `List CompileError` and throw
`CompileError.many : List CompileError → CompileError` at the phase boundary. Small,
self-contained, immediate payoff in every reject-test iteration loop.

*References:* McBride & Paterson, [Applicative Programming with Effects](https://openaccess.city.ac.uk/id/eprint/13222/1/Applicative-final.pdf) (JFP 2008) — the applicative structure whose error-accumulating `<*>` this exploits; the [`validation`](https://hackage.haskell.org/package/validation) package (the canonical accumulating instance).

### E8. Open registration of unary functions

Adding `atan` today touches `UnaryOp`, `Syntax.lean`, `Elab.lean`, and `applyUnaryFn` (4
sites; Spike 3b reduces the syntax/elab share). The open-datatype endgame is a command macro:

```lean
declare_unary_fn atan Float.atan            -- total
declare_unary_fn log  Float.log  (domain := fun v => v > 0)
```

backed by an environment extension (the same mechanism as `@[simp]` registration): `UnaryOp`
becomes a `String` key validated *at elaboration time* against the registry (so fail-loud is
preserved — a typo'd function name is still a compile error), and `applyUnaryFn` becomes a
registry lookup. Why recorded-only: it trades a closed inductive — which the AST's
`DecidableEq/ToExpr` deriving and any future proofs about evaluation lean on — for
extensibility that isn't currently in demand (five functions, stable for the foreseeable
future). Revisit if the function inventory starts growing monotonically. Open question to
resolve first either way: whether `Factor.unaryFn`'s op survives into the routed artifact at
all (the Br layer has no per-factor op today) — if the route is silently lossy for unary fns,
that's a Part-I-grade finding worth its own check.

*Reference:* [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/) — environment extensions and command macros (the same mechanism backing `@[simp]` registration) that a `declare_unary_fn` command would use.

### E9. Datatype-generic acset codecs

`AcsetCodec.lean`'s encode/decode pairs and their round-trip lemmas follow one schema per row
type. Lean 4 supports custom `deriving` handlers — a `deriving AcsetRow` that generates
`toRow`/`ofRow` and a `by simp`-discharged round-trip lemma for records of scalars is
feasible metaprogramming. Why recorded-only: Constraint 4 (the wire format is
position-sensitive and append-only by convention) means generated code must be pinned against
format drift anyway, and Spike 6d's combinators already capture most of the line savings
without metaprogram maintenance. The pattern earns its keep only if the table inventory grows
(e.g., when scan bodies get their own acset representation).

*Reference:* [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/) — custom `deriving` handlers (the metaprogram that would generate `toRow`/`ofRow` and the round-trip lemma).

### E10. Stage the interpreter into a code generator

`papers/pytorch_compilation.md` already contemplates compiling tensor-logic to Python. The
pearl framing: the evaluator is an interpreter `eval : Program → Env → Tensors`; its first
Futamura projection — specialize it to a fixed program — is a code generator. (A different sense
of "specialize" than **E14**'s GHC-style per-instantiation specialization — this one is
partial evaluation of the *interpreter itself*, Futamura's move, not a rewrite pass over
programs it runs; the two compose rather than compete, since E14's unrolled scan is itself a
more-specialized program for E10 to then specialize the interpreter against.) E4's `EvalPlan`
is 80% of that specialization already (per-statement dense affine maps + a semiring tag is
essentially an einsum call spec): `EvalPlan → String` emitting `torch.einsum`/`scatter_add`
calls is a small pretty-printer, and the Lean evaluator becomes the differential-testing
oracle for the emitted code. Recorded-only until the Python-target work is actually
scheduled, but it strengthens the case for E4: the plan representation serves eval,
route-agreement, *and* codegen.

Worth noting for when this is scheduled: unlike GHC (lazy, heap-allocated), Lean 4's own
compiler is the closer architectural cousin here — it compiles a strict functional language via
reference counting with **reuse analysis** (Perceus): a dying, same-shaped allocation's memory
is reused in place for a fresh one, rather than freed and reallocated. `EvalPlan → String`
emitting real tensor-allocating calls is exactly where a reuse-style analysis pays off — a
source tensor that's dead after a statement and shape-matches that statement's output is a
candidate for an in-place write instead of a fresh allocation, a performance angle GHC's own
lineage wouldn't suggest looking for.

*References:* Futamura, "Partial Evaluation of Computation Process — An Approach to a Compiler-Compiler" (Systems, Computers, Controls 1971; reprinted in *Higher-Order and Symbolic Computation* 12(4):381–391, 1999); overview: [Partial evaluation — Futamura projections](https://en.wikipedia.org/wiki/Partial_evaluation#Futamura_projections) — specializing an interpreter to a fixed program *is* a compiler; Reinking, Xie, de Moura & Leijen, [Perceus: Garbage Free Reference Counting with Reuse](https://xnning.github.io/papers/perceus.pdf) (PLDI 2021) — the reuse-analysis technique above, from Lean 4's own compiler.

### E11. Investigation: do UIDs earn their keep?

> **✅ DONE — merged to `main` 2026-07-15.** All three honest unknowns resolved: no phase
> distinguishes same-named occurrences after unification (marks live on the LHS slot, never on
> `AxisSpec` identity); `unifyAxes`'s own doc comment already admitted it's identity given
> `assignUIDs`'s one-uid-per-name invariant, confirmed by tracing every bucket it could ever
> group; and the bridge/acset layer's `axisUidFor3` is an unrelated, independently-synthesized
> id — `AxisP` carries no pipeline uid at all. Outcome: **major simplification**, matching Spike
> 1a's shape. Deleted `unifyAxes`, `collectAxisNameUID`, and `Exec/Context.lean`'s generic
> coequalizer (`EqClass`/`Context`/`Context.merge`/`Context.apply`); merged the now-redundant
> `CanonicalProgram` into `ResolvedProgram` (identical once `ctx` is gone); dropped the
> write-only `ctx` field from `LoweredProgram`/`ScanProgram`/`LinearProgram`/`ScheduledProgram`.
> `Compile.lean`'s pipeline: 9 phases → 8. Explicitly **descoped**: full elimination of `Nat` UID
> as axis identity (rekeying `Eval`'s `HashMap UID _` by `String` name) — that reaches
> `dedupByUid`, which `RouteSpec.lean` unfolds definitionally (`dedupByUid_eq_foldl := rfl`),
> Constraint 3's proof-repair territory, deferred pending Spike 6. See
> `docs/superpowers/specs/2026-07-15-e11-uid-investigation-design.md` for the full evidence trail.

Axis identity is *defined* to be name-based within program scope (§12.1, quoted at
`Structural.lean:12`), yet the pipeline mints `Nat` UIDs (`FreshM`), then runs a coequalizer
(`Exec/Context.lean`) and `unifyAxes` to merge the UIDs that name-identity says were never
distinct. That's two representations of one equivalence relation, plus a phase to reconcile
them. The question worth one focused day: **what breaks if resolved names (plus a fresh-name
supply for `%nl`-style compiler-generated intermediates) are the identity, and UID minting
disappears?** Honest unknowns that the investigation must answer, not assume: whether any
phase genuinely distinguishes same-named occurrences (marks like `freeNorm`/`iterAt` live on
slots, not identities, so plausibly not); whether `Context`'s coequalizer does work beyond
name-unification (declared-vs-used axis reconciliation); and what the bridge/acset layers key
on (`axisUidFor3` suggests UIDs are load-bearing in serialization). Outcome either way is
valuable: either a major simplification (delete a phase and a monad parameter) or a precise
doc note on exactly why UIDs are necessary — which no comment currently states.

*Reference:* Charguéraud, [The Locally Nameless Representation](https://link.springer.com/article/10.1007/s10817-011-9225-2) (Journal of Automated Reasoning 2012) — names for free variables, indices for bound ones; the discipline that would let resolved names be the axis identity.

### E12. Named simp sets for the proof domains (tiny)

Mathlib-style hygiene: register the codec and route projection lemmas in named simp sets
(`@[acset_simp]`, `@[route_simp]`) so downstream proofs say `simp [acset_simp]` instead of
hand-curated lemma lists — the unused-simp-arg lint warnings currently scattered through
`AcsetCodec.lean:873-889` and `Agreement.lean:78-104` are the symptom this treats. Fold into
Spike 6 if adopted.

*Reference:* Lean reference manual, [Simp sets](https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-sets/) — `register_simp_attr` for named, non-default simp sets (`@[acset_simp]`, `@[route_simp]`).

### E13. Generators for `Br` — closing `BrOp`, and promoting E6's laws to theorems

GHC's Core is a deliberately small, *closed* set of primitive term formers (`Var`, `Lit`, `App`,
`Lam`, `Let`, `Case`, `Cast`, `Tick`, `Type`, `Coercion` — [Peyton Jones, *The Glasgow Haskell
Compiler*](https://simon.peytonjones.org/assets/pdfs/glasgow-haskell-compiler.pdf), §3) that
every surface feature desugars into — every optimization pass is `Core → Core`, so one
simplifier serves every language feature at once. `Br` already has this shape: `BrOp` is the
flat content-generator inductive, and `copyW`/`delW`/`swap` are the CD/comonoid structural
generators, wired via `NData`. The question this doc doesn't currently ask: **is that generating
set actually closed?**

Spike 7b already answers "not yet," concretely: `NData`'s wiring is a bijection
(`OutPort ≃ InPort`), which is *provably* unable to interpret `copyW` (one-in-two-out) —
`BrNF.lean:243-244` admits exactly this, which is why `brCancelPoint` is parked pending a
cospan (non-bijective) wiring model. This is structurally the same failure GHC hit with GADTs:
the original Core had no term former that could carry the type-equality evidence a GADT match
refines, so System FC extended Core with explicit `Coercion`/`Cast` formers — a new *generator*,
not a bigger proof. Reframed this way, **the cospan model isn't a patch to `BrNF`, it's `Br`'s
System-FC moment**: the generating set needs a new construct (non-bijective wiring), the same
way Core's did. Worth stating in Spike 7b's writeup, since it changes the *size* of the
undertaking from "fix a proof" to "extend the presentation" — smaller in code, but a genuine
design decision about what `Br`'s generators are allowed to express.

The second half: if `BrOp` (plus the corrected wiring model) is ever confirmed to be a closed
generating set — closed specifically under the DSL's own semantics-preserving transforms — then
**E6's three laws stop being test oracles and become candidate categorical theorems.**
Reordering, materialization, and scan-unrolling are exactly the shape of equation GHC's `RULES`
pragma promotes from "observed to hold" to "a rewrite the compiler is licensed to perform": E6,
which tests these laws at the `Eval` level today, is a down-payment on eventually restating them
as equations between `Br`-terms built from the same generators E5's
`evalBrBaseP`/`evalThreaded` already consume. This doesn't change E6's plan — it changes what
E6's *result* is worth: a passing property oracle is now legible as evidence for a specific
future theorem statement, not just regression coverage.

**Verdict:** investigation first (analogous to E11 — "is `BrOp` closed?" is a bounded question,
not a redesign) — but note the investigation can't fully close until the cospan wiring model
Spike 7b names actually exists (currently unscheduled; budget it as its own spike, Wave 3b), and
Spike 3a's Nonlin closure is a worked precedent worth doing first regardless. Spike-worthy once
answered; the payoff compounds with E5/E6 rather than competing with them.

*References:* Peyton Jones et al., [The Glasgow Haskell Compiler](https://simon.peytonjones.org/assets/pdfs/glasgow-haskell-compiler.pdf) — Core as a small closed IR, §3; Sulzmann, Chakravarty, Peyton Jones & Donnelly, [System F with Type Equality Coercions](https://www.microsoft.com/en-us/research/wp-content/uploads/2007/01/tldi22-sulzmann-with-appendix.pdf) (TLDI 2007) — the `Coercion`/`Cast` extension to Core that GADTs forced; Peyton Jones, Tolmach & Hoare, [Playing by the Rules: Rewriting as a practical optimisation technique in GHC](https://www.microsoft.com/en-us/research/publication/playing-by-the-rules-rewriting-as-a-practical-optimisation-technique-in-ghc/) (Haskell Workshop 2001) — `RULES` as user-trusted equations over Core terms, the model for promoting E6's laws.

### E14. A simplifier: local algebraic rewrite rules over the DSL AST

Nothing in Spikes 1–8 or E1–E13 does peephole simplification on `TLProgram` itself — the closest
things are *test*-side transforms (E6's `materializeSplit`/reordering) and *representation*
changes (E2's `CoreStmt`, E4's `EvalPlan`). GHC's actual optimization workhorse is neither: it's
the Simplifier, a small set of local, confluence-checked rewrites applied to a stable Core IR,
plus a user-extensible layer (`RULES`) for library-specific equations the compiler can't derive
on its own. The direct analogue here, once E2's `CoreStmt` exists as a stable rewrite target:

```lean
def simplifyStmt : CoreStmt → CoreStmt   -- one local rewrite step
def simplify     : List CoreStmt → List CoreStmt   -- fixpoint of simplifyStmt, bounded
```

A first useful rule set, all sound by construction against the exact-comparison discipline E6
already established (any candidate rule gets the SAME treatment as a metamorphic law — generate,
compare, and if it ever fails on a well-formed program that's a finding, not a bug in the rule):
additive identity (`X + 0 ⇒ X`, a zero-term dropped from a sum), redundant materialization
(the literal inverse of E6's `materializeSplit` — collapsing a chain of single-use intermediates
back into one statement when nothing else reads them), and — the two payoffs worth calling out on
their own —

- **Common subexpression elimination.** Once E4's `EvalPlan` exists, two statements' affine-map
  fragments are directly, structurally comparable (not `HashMap`-driven dictionaries reconciled
  at runtime), so detecting and sharing an identical sub-computation across statements (e.g. two
  attention heads both reading the same `Q·Kᵀ` slice) becomes a straightforward fixpoint pass
  rather than a semantic proof exercise.
- **Compile-time unrolling of small, statically-known scan lengths.** Every scan axis size is a
  compile-time literal (`Decl.axis l (some L)`) — this is GHC's specialization pass in miniature
  (turning a parameterized computation into a monomorphic, straight-line one per concrete size).
  The transform is *the same code* as E6's scan-unroll oracle, reused as a real optimization
  rather than a test: what's being built right now to check `evalScan` against its unrolled form
  is, with no new logic, a compiler pass that replaces a small scan with its unrolled form.

**Verdict:** spike-worthy, but sequenced *after* E2 (needs a stable IR to rewrite over) and best
started once E4 exists (CSE and scan-specialization are its cheapest, highest-value first rules).
Not a competitor to E6 — the two share machinery (the unroll transform) and a verification
discipline (generate-and-compare), they just answer different questions ("does this hold" vs.
"can we always rewrite to this").

*References:* Peyton Jones, Tolmach & Hoare, [Playing by the Rules: Rewriting as a practical optimisation technique in GHC](https://www.microsoft.com/en-us/research/publication/playing-by-the-rules-rewriting-as-a-practical-optimisation-technique-in-ghc/) (Haskell Workshop 2001) — the `RULES` mechanism this pass generalizes; Peyton Jones, [The Glasgow Haskell Compiler](https://simon.peytonjones.org/assets/pdfs/glasgow-haskell-compiler.pdf) — the Simplifier's role as GHC's central, repeatedly-applied optimization pass.

### How the exploratory ideas compose

E3 + E4 + E5 are one program viewed from three sides: a single **plan representation**
(dense affine maps — the route's own `StMatP` language), evaluated over a **semiring
parameter**, that **denotes** the routed artifact. Landing all three would leave the
codebase with one semantic core serving four consumers — the Float interpreter, tropical/
log-domain evaluation, the executable agreement test, and (eventually, E10) code generation —
where today there are two disconnected coordinate systems and no executable bridge. E6 is the
safety net that makes the migration testable; E1/E2 are the AST-side analogues of the same
"one definition, many instantiations" move. If only one exploratory thread gets pursued,
E6 → E3 → E4 → E5 in that order is the highest-value path.

E13 and E14 are a second such pair, one level up. E13 asks whether `Br`'s generators are closed
— the categorical precondition for E6's laws to become theorems and for E5's denotation to be
complete. E14 asks what a closed, stable `CoreStmt` (E2) buys once you're willing to rewrite it —
the GHC-Simplifier analogue, absorbing CSE and scan-specialization as its first two payoffs.
Neither is on the critical path above, but both are the natural *next* question once E2/E5/E6
land: E13 is "did E5/E6 characterize everything," E14 is "now that there's a stable IR, what do
we do with it besides interpret it."

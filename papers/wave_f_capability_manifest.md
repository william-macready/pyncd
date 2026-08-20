# Wave F capability manifest

This is a standalone reference for what the Wave F checked scan graph actually accepts, rejects, and
covers today — not a design narrative. For the architecture, the correctness laws, and the reasoning
behind each decision, see [`wave_f_scanplan_proposal.md`](wave_f_scanplan_proposal.md); for Wave C's
scan-free `EvalPlan` boundary, see [`wave_c_capability_manifest.md`](wave_c_capability_manifest.md).
Every number below was counted from an actual run on this branch, not estimated or copied from
planning text.

## 1. Semantic and wire versions

- **Semantic version:** the in-memory `RawEvalPlan.version`/`admittedVersion`
  (`LeanNCD/Eval/Plan/Check.lean`) and `PlanError.versionNotAdmitted` were **removed in Wave F F3**,
  not merely deferred or bumped. Adding `PlanStep.scan` changes the plan language's Lean type
  directly — any caller that built the old `AssignPlan`-only `RawEvalPlan.steps` must be recompiled
  and migrated regardless of what number a version field would have held, so bumping it would have
  protected nothing a real consumer depended on. See
  [`wave_f_scanplan_proposal.md` §2.3](wave_f_scanplan_proposal.md#23-remove-the-unused-in-memory-version-tag)
  for the full argument. There is no version tag today, and nothing has replaced it.
- **Wire version:** still N/A, unchanged from Wave C. C5's canonical representation and codec remain
  deliberately deferred; see
  [`wave_c_capability_manifest.md` §1](wave_c_capability_manifest.md#1-semantic-and-wire-versions).

## 2. Accepted scan source constructs

The source compiler admits a `.scan` only when every base and step operation already fits the
checked Wave C local kernel: `f64`, real sum-product contraction, identity nonlinearity, plain/affine
read factors, and zero padding (proposal §5.1). Within that kernel, the admitted fragment is a
rectangular uniform lattice recurrence, confirmed by the three-way differential gate in §4 below:

- rectangular uniform n-dimensional scans, with every advancing axis writing `q + 1`;
- advancing dimensions in arbitrary tensor positions — they need not trail, be contiguous, or follow
  context order;
- coupled recurrences (several states advancing together in one scan);
- external per-step reads (a step block reading a non-state tensor at the current coordinate);
- contractions inside a recurrence;
- deep constant (non-positive) look-back, with zero padding for out-of-range history reads;
- block-local scratch, private to the step block and never published past the scan's boundary;
- more than one scan axis in a single scan;
- more than one scan per schedule;
- a plain (scan-free) statement consuming a published scan history downstream.

A state's boundary may be written as one free-axis "main" face plus one or more disjoint,
fully-pinned point overrides — **not** two or more full free-axis faces (the standard
row-0-plus-column-0 tabulation-DP pattern), which always overlap at the origin and are rejected; see
[proposal §5.1](wave_f_scanplan_proposal.md#51-accepted-source-fragment) for the exact geometric
argument.

## 3. Rejected scan source constructs

Every syntactically visible rejection is a `CapabilityError` constructor
(`LeanNCD/Eval/Plan/Error.lean`); Wave F's two changes to that closed 12-constructor family are
`scanNode` (Wave C's `.scan`/`.scanPre` rejection — it has no producer left now that `compileScan`
exists, but the constructor stays for `.scanPre`, which is still rejected via the separate
`recurrenceOrCallback` constructor, not `scanNode`) and `noAdvancingAxis` (new: a `.scan` declaring an
empty advancing-axis list).

Every rejection that needs an inferred size or a lowered affine map — and so cannot be decided at
capability preflight — is one of a closed **24-constructor** `ScanCompileError` family
(`LeanNCD/Eval/Plan/Error.lean`), organized into the same categories the type's own doc comments
group them into:

| Category | Constructors |
|---|---|
| §4.2 state/base/result pairing | `noPersistentState`, `orphanBaseState`, `orphanAdvancingResult`, `duplicateStateResult`, `stateResultNotAdvancing`, `partialAdvancingResult`, `duplicateScratchProducer` |
| Block dependency order | `blockReadNotAvailable`, `stateReadInBaseBlock` |
| Context axes | `duplicateContextAxis`, `scanAxisZeroExtent`, `iterNextInBaseBlock`, `iterAtInStepBlock`, `pinnedAxisNotContext`, `contextAxisAsFreeOutput`, `advancingAxisNotInLhs`, `duplicateAxisInLhs` |
| Per-state geometry | `inconsistentStateRank`, `inconsistentAdvancingDim`, `inconsistentStateExtent` |
| Base write placement (§5.1: in range, boundary-touching, pairwise disjoint) | `baseWriteNotAtBoundary`, `baseWritePinOutOfRange`, `baseWritesOverlap` |
| §7.4 causality | `stateReadNotCausal` |

No `unsupportedScan : String` escape hatch exists in either family.

**Constructors this plan's audit found under-specified, now closed (Task 1).** Three payloads
carried too little to distinguish real, distinct user errors:

- `ScanCompileError.duplicateAxisInLhs` now carries `isBase`, so a duplicate axis in a base statement
  and one in a step statement no longer assert byte-identical expected values.
- `ScanCompileError.blockReadNotAvailable` now carries a `ReadUnavailableCause`
  (`unknownName`/`forwardReference`/`selfRead`), so an unresolvable name, a forward reference to a
  later scratch producer, and a statement reading the name it is itself about to produce are three
  distinguishable rejections instead of one.
- `ScanPlanError.causalityFailure` (a *different* family — `LeanNCD/Eval/Plan/Scan.lean`, thrown by
  the checker directly against a constructed `RawScanPlan` rather than from source) now carries the
  offending statement index alongside the state/term/factor indices it already had, so two different
  step assignments failing at the same term/factor position no longer collide.

Every call site of all three constructors was grepped across the whole `leanncd/` tree for this task
and confirmed to match the new arity — no stale three- or four-argument construction survives
anywhere.

**Gaps deliberately left, named and non-blocking:**

- `checkScanPlan` never checks a state destination slot's **dtype** — it reads the state's signature
  purely for `.shape`. Contained downstream: `checkAssign` separately rejects any non-`f64` source, so
  nothing can actually populate a mis-labeled state; a captured state is separately covered by
  `captureSignatureMismatch`, which compares the whole signature including dtype.
- The **wrong-arity-read gap**: a wrong-arity read confined to non-advancing dimensions inside a scan
  block surfaces as `invalidPlan` ("internal compiler bug") rather than a source-level diagnostic —
  but this plan's audit confirmed it is **unreachable from real source**. `TLProgram.compileToScheduled`
  runs `checkReadRanks` pre-grouping, over the flat statement list, before `finalizeScans` partitions
  it into base/recurrence blocks — so a scan's base and recurrence statements are arity-checked
  exactly like plain ones, before any scan-specific compilation begins. The gap is reachable only from
  a hand-built `ScheduledProgram` that skips the front end entirely.
- The independent oracle's `rewriteRead` (`test/Eval/PropertyOracle/ScanUnroll.lean`) performs **no
  causality check of its own** — it evaluates a state read's advancing indices by range and liveness
  alone. Not live: `compileScan` rejects a non-causal read from source first, and `checkScanPlan`
  rejects it again at the plan level, so the oracle never sees one. Recorded as a consistency gap
  (the oracle rejects every other out-of-fragment construct explicitly), not a bug.

## 4. Law 1 corpus coverage for scans

The curated `enumScanCases` generator (`test/Eval/PropertyOracle/ScanGen.lean`) and the hand-written
`ScanCompileTest.lean` fixtures together give the real, counted evidence for Law 1 over scans
(`test/Eval/Plan/DifferentialTest.lean`):

- **17** generated cases total, split **9 accepted / 4 `unsupportedNonlin` / 4 `unsupportedAgg`** —
  pinned by `DifferentialTest.lean`'s `scanCorpusSplit` `run_cmd` assertion (`total == 17 && accepted
  == 9 && nonlin == 4 && agg == 4`), which fails loudly rather than silently re-baselining if the
  accept/reject boundary ever shifts.
- **21** total scan programs pass the three-way differential gate: **12 hand-written** (the nine
  acceptance schedules covering `ScanCompileTest.lean`'s twelve lettered shapes, a two-warning
  fixture, a whole-surface alpha-rename, and a scan over an axis sharing a NAME but not a UID with a
  free output axis) plus the **9** accepted generated cases.
- All 21 agree bit-for-bit across three independent legs: the compiled checked path
  (`prepareEvalPlan` → `runPreparedDense`), the legacy `evalScheduled` oracle, and the independent
  scan-free unrolling (`PropertyOracle.independentRun`) — compared on materialized state, whole
  environment, and (between the first two legs only) preparation warnings.
- Beyond raw count, `DifferentialTest.lean` asserts a structurally derived feature table over the
  gated schedules themselves (not by fixture name): deep look-back and zero padding, coupled states,
  scratch, external reads, contraction, extent one, more than one scan axis, several base writes for
  one state, a non-trailing advancing dimension, more than one scan in a schedule, and a plain
  consumer of a published history.
- The pre-existing Wave C scan-free sweep (3,832 entries, 100% accepted, 100% bit-exact) is unchanged
  by this slice.

## 5. Extension points

Stated as what is **not yet supported and why** — a record of deliberate scope discipline, not a
roadmap commitment. Reproduced from
[proposal §1](wave_f_scanplan_proposal.md#1-executive-summary)'s "Functionality still missing after
Wave F" table:

| Missing capability | Consequence after Wave F |
|---|---|
| Pointwise and axiswise nonlinearities | Rejected in both ordinary `PlanStep.assign` operations and scan base/step blocks. |
| Masks, predicates, Iverson/Boolean factors, and Boolean outputs | Rejected rather than represented in `AssignPlan` or `CheckedPlanBlock`. |
| Unary factor functions | Rejected in ordinary assignments and scans. |
| Max/min aggregation | Only real sum-product reduction is admitted. |
| Scatter and affine LHS writes | Wave D source semantics are not yet represented by checked `EvalPlan`. |
| Dtypes beyond the admitted concrete `f64` mode and dynamic shapes | Still rejected at the checked-plan preparation boundary. |
| `.scanPre`, callbacks, nonlinear scan bodies, and predicate-dispatch scan bodies | Still rejected even though `PlanStep.scan` exists. |
| General n-dimensional recurrence geometry and arbitrary state writes | The first checked scan remains the rectangular uniform all-axis `+1` fragment. |
| Multi-face full-boundary writes (the standard n-D tabulation-DP pattern, e.g. row-0-plus-column-0) and genuinely overlapping writes with no declared precedence | Neither is achievable in this version — both need an offset/restricted-range or conflict-resolving base-write geometry beyond pin-plus-full-free. |
| PyTorch/JAX execution and optimized `lax.scan`/compact-carry/wavefront/parallel-prefix lowering | Dense remains the only general checked worker delivered by Wave F. |

The next semantic-expansion work after Wave F should be a named **checked local-kernel capability
wave**, extending `AssignPlan`, its checker, and Dense interpretation one operation family at a time,
then reusing the same checked operation inside `CheckedPlanBlock`. This ordering, and which operation
family comes first, is **not chosen or ordered by Wave F** — it is the next wave's own scoping
question.

## 6. Audit findings confirmed clean

Findings from this plan's own final audit, recorded here so a future reader does not have to
re-verify them:

- **`import LeanNCD` reaches the source scan compiler transitively.** The top-level `LeanNCD.lean`
  imports `Eval.Plan.Adapter`, which imports `Eval.Plan.Compile` (the source compiler, including
  `compileScan`) directly. A consumer that wants checked-scan execution with **no** source compilation
  must instead import a narrower `Eval.Plan.*` leaf directly — `Eval.Plan.EvalPlan` (which imports
  only `Eval.Plan.Scan`, which imports only `Eval.Plan.Block`, and so on down to `Eval.Plan.Error`) —
  never `Eval.Plan.Adapter` or `Eval.Plan.Compile`. This is the concrete resolution of the Gate's
  "without importing source compilation" clause.
- **`DSL/AGENTS.md`'s import-direction claim, corrected (Task 3).** The claim that "`Eval/*` imports
  `DSL.Ast`/`DSL.Compile`/`Pipeline.Types`/`TraverseAxes` but never `Pipeline.Structural`/`Lowering`
  directly" was false as of F4: `Eval/Plan/Compile.lean` imports `Pipeline.Lowering` directly, reusing
  `idxToRow` to lower a scan's affine reads exactly as `Lowering.lean` itself does. The claim now
  states that exception explicitly; every other `Eval/*` file still never imports
  `Pipeline.Structural`/`Lowering`.
- **Checker/error mutation-matrix work.** Task 1/2 of this plan closed three real gaps found by this
  plan's own audit — `causalityFailure`, `duplicateAxisInLhs`, and `blockReadNotAvailable` each
  under-specified a locator that let two genuinely distinct user errors collide on one payload (§3
  above has the detail). The wrong-arity-read gap and the state-destination dtype gap are named, not
  fixed, for the reasons given in §3: the former is unreachable from real source, and the latter is
  contained downstream by `checkAssign`/`captureSignatureMismatch`.

**Which import to use.** For checked-scan execution with no source compilation, import
`Eval.Plan.EvalPlan`/`Eval.Plan.Scan` directly — neither imports `Eval.Plan.Compile`, `DSL.Ast`, or
the legacy evaluator. For the named source-to-plan boundary (`prepareEvalPlan`, `pack`/`unpack`/
`runPreparedDense`), import `Eval.Plan.Adapter` — this pulls in `Eval.Plan.Compile` and therefore
source compilation. `import LeanNCD` pulls in everything, including the legacy `Eval.Entry` evaluator
and the full DSL pipeline. Only a `Plan/` leaf import (`Eval.Plan.EvalPlan`/`Eval.Plan.Scan`)
satisfies the Gate's clause that "Wave G can consume checked scan APIs without importing source
compilation or legacy execution."

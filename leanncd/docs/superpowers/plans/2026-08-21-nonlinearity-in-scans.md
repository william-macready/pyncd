# Nonlinearity inside scan blocks

> **Permanently archived — do not execute any task below.** The three-step expectations,
> split-pair recognition, and shared-split compilation in this plan are superseded by
> [`papers/nonlinearity_split_pair_direct_lowering.md`](../../../../papers/nonlinearity_split_pair_direct_lowering.md).
> The canonical replacement uses one logical unsplit `ScheduledProgram`, a private collision-free
> `PhysicalRouteProgram` immediately before existing `routeCore`, no second scheduler, opaque scans,
> and unchanged `RouteSpec` statements. The replacement plan incorporates the valid block IR,
> publication, and local-axis work. Everything below is historical evidence, not implementation
> guidance.

**Status:** Permanently superseded; retained for provenance only.

**Dependency**: this plan depends on `2026-08-21-wiring-loop-generalization.md` having already landed
on `main` — specifically, `checkPlanBlock`/`checkPlan` must already delegate to the generalized
`WiringNode`/`checkStepGraph` implementation (that plan's own Task 1) before this plan's Task 1
(`BlockStep`/`CheckedBlockStepEvidence`, formerly this plan's Task 2) can extend that dispatch with new
arms. See that plan's own §3 for `WiringNode`/`checkStepGraph`'s design — not re-described here.

## 0. Session verification record (2026-08-21)

Everything below was re-verified directly against the repo at `main` (`e09a270`, already pushed to
`origin/main`), by reading the real files — not carried over from the design doc's own citations,
which the design doc itself warns may have drifted across its several revision passes.

**Design doc read in full**:
`docs/superpowers/specs/2026-08-21-nonlinearity-in-scans-design.md`. Its headline decision (§1,
Option B: `splitScan`/`splitNonlins`/`route` stay untouched; `compileScan`'s own Phase 1 classifier
gains split-pair recognition instead) was treated as settled when this archived plan was written; it
is now rejected by the permanent supersession banner above.

**`compileScan`'s current Phase 1 classifier** (`LeanNCD/Eval/Plan/Compile.lean`) — confirmed by
reading it directly: `checkScanBlockStmt` (`Compile.lean`) still calls `checkNonlinScanBlock`, whose
body is exactly `.identity => pure () | .pointwise _ => throw (.unsupportedNonlin ...) | .axiswise
.. => throw (.unsupportedNonlin ...)` — unconditional rejection, unchanged since Thread 4.
`checkScanLHSSlot` still rejects `.freeNorm` unconditionally (`.freeNorm a => throw
(.unsupportedLhsSlot ...)`), also unchanged. `checkNonlinTopLevel` (the top-level, `.plain`-statement
admission Thread 4 added) admits all three `Nonlin` kinds unconditionally. Once
`checkNonlinScanBlock` is relaxed to match `checkNonlinTopLevel`'s body, the two functions become
literally identical (mirroring `_stmtName`'s already-unused status in `checkNonlinTopLevel`) —
confirmed by direct comparison, not assumed; the design doc's §9 "bonus find" holds.

`compileScan`'s Phase 1 (state/scratch classification) destructures `base`/`recur` via
`assignPartsOrFail` into `Array (String × List LHSSlot × RHSExpr)` triples, then classifies each by
inspecting `.iterNext`/`.iterAt` slot presence — it never inspects `rhs.nonlin` for classification
purposes at all. This means Phase 1's classification logic is unaffected by whether a triple carries
a real `Nonlin` or `.identity`, which is exactly why recombining split pairs BEFORE classification
(rather than after) is safe: the recombined triple's real `slots`/`nonlin` flow into classification
unchanged from how a hypothetical never-split `.identity`-nonlin triple would.

**`splitStmt`'s exact current output shape** (`LeanNCD/DSL/Pipeline/Lowering.lean`) — confirmed by
reading it directly AND by running it for real (see the verified snippet below, not a hand-derived
guess): for a statement `s` with `rhs.nonlin ≠ .identity`, `splitStmt s` returns `[linStep, nlStep]`
where `linStep := .assign "%nl{uid}" linSlots { body := rhs.body, nonlin := .identity, agg :=
rhs.agg }` (`linSlots` degrades every `.freeNorm` to `.free`, an existing fix landed during Thread 4
— see below) and `nlStep := .assign nm slots { body := trivial-single-read-of-"%nl{uid}", nonlin :=
rhs.nonlin, agg := .sum }`. The `%nl{uid}` name comes from `FreshM`'s `freshUData`, so it is
compiler-fresh and can never collide with a real source name — surface syntax cannot produce an
identifier starting with `%`. `splitScan` (`Lowering.lean`) applies `splitStmt` to every `base`/
`recur` statement via `flatMapM`, in source order, so split pairs always arrive at `compileScan`
ADJACENT and in the order `[linStep, nlStep]` — never interleaved with another statement's halves.

**The `.freeNorm`-degrade-on-the-linear-half fix is already landed on `main`, not something this
plan adds.** `LeanNCD/DSL/AGENTS.md`'s Pitfalls section already documents it in full (found and
fixed during Thread 4 Task 3, 2026-08-21) — `linSlots := slots.map (fun sl => match sl with |
.freeNorm a => .free a | _ => sl)`, confirmed present in `splitStmt`'s real body by direct reading
and by the verified snippet below. This plan's own recombination logic relies on this fix (a
recombined triple's `slots` must come from `nlStep`, which still carries the ORIGINAL `.freeNorm`
marker) but does not need to touch `Lowering.lean` at all.

**Verified via `check-snippet.sh`** (real repo, real `splitStmt`, not a simulated shape): a fresh
`Stmt.assign "Y" [.free i, .freeNorm j] {... nonlin := .axiswise .softmax none}` run through the
real `splitStmt` produces exactly `[(n1 starts-with "%nl", [.free i, .free j], ...), ("Y", [.free i,
.freeNorm j], nonlin = .axiswise .softmax none)]` — confirming both the naming convention and the
freeNorm-degrade fix empirically, not by reading alone.

**`resolveNonlinAxis`'s current body** (`Compile.lean`) — confirmed unchanged from Thread 4: takes
`(stmtName, nonlin, slots)`, finds every `.freeNorm`-marked position in `slots` (full list, `.iterAt`/
`.iterNext` included in the count), and cross-checks against `nonlin`'s kind: `.axiswise _ (some _)`
→ `maskedAxiswiseNotSupported`; `.axiswise _ none` with zero/one/two+ markers → `noMarkedReductionAxis`
/ `some p` / `multipleMarkedReductionAxes`; `.identity`/`.pointwise _` with any marker →
`unmarkedReductionAxis`. `NonlinCompileError` (`Error.lean`) already has exactly these four
constructors — added by Thread 4, unchanged by this plan. This plan reuses `resolveNonlinAxis`
verbatim at the scan-block call site too (design doc §5's "no new `ScanCompileError` constructor,
reuse `PlanCompileCause.nonlin`/`liftNonlin` directly" ruling, confirmed correct: `compileScan`'s own
return type is `Except PlanCompileFailure CompiledScan`, so `liftNonlin warnings (resolveNonlinAxis
...)` inside a scan-block `do`-block aborts `compileScan` exactly as it aborts `prepareEvalPlan` at
top level — no new wrapping needed).

**`checkNonlinScanBlock`/`checkScanLHSSlot`'s current bodies** — quoted above; both need exactly one
relaxation each (merge into `checkNonlinTopLevel`'s body under a shared name `checkNonlin`; drop the
`.freeNorm` rejection).

**`RawPlanBlock`/`CheckedPlanBlock`'s current fields** (`RawStep.lean`/`Block.lean`) — confirmed by
reading both directly: `RawPlanBlock { contextShape, tensorSigs, inputs, assignments : Array
AssignPlan, outputs }`; `CheckedPlanBlock { raw, checkedNodes : Array CheckedAssignPlan }` (private
constructor). The design doc's own snippet (§5) proposes renaming `assignments` to `steps : Array
BlockStep` — adopted below, exactly as drafted, since "least expensive time to fix the name, before
any wire format is frozen" still holds and no wire-format/serialization code depends on the field
name (confirmed by grepping `acset/` and `data_transfer/` for `RawPlanBlock`/`assignments`: zero
hits — this type is never serialized).

**`checkPlanBlock`/`runDenseBlock`'s current bodies** (`Block.lean`) — confirmed by reading both in
full. `checkPlanBlock`'s wiring loop (input validation, then per-assignment: block-context check →
destination-availability → source-availability via a direct per-term/factor loop → `checkAssign` →
mark produced) is structurally IDENTICAL to `checkPlan`'s own loop (`EvalPlan.lean`), differing only
in: (a) the context obligation (`blockContextMismatch` against `block.contextShape`, vs. `checkPlan`'s
`topLevelContextNotEmpty` against an implicit empty context), (b) the error wrapper (`BlockError.wiring`
vs. `PlanStepError.assign`), and (c) an extra `outputs`-range/uniqueness check `checkPlan` has no
analogue for (there is no "declared outputs" concept at the outer-graph level — every outer slot must
simply be produced). Every `PlanError`-shaped failure at BOTH call sites (`slotOutOfRange`,
`duplicateInputSlot`, `inputSlotsNotOrdered`, `inputSlotOverwritten`, `duplicateDestination`,
`invalidForwardRead`, `missingProduction`, all via `nodeError` where per-node) is embedded through
exactly one wrapper function per call site (`.assign`/`.wiring`) — confirmed by reading every throw
site in both functions side by side, not assumed from the design doc's own §7 summary.

**`checkPlan`/`checkScanPlan`'s current bodies, especially the `.assign`-vs-generic asymmetry design
doc §7 describes** — confirmed: `checkPlan`'s three match blocks (context-check, destination loop,
source-check) each have a `.assign` arm using a direct per-term/per-factor loop (preserving `ti`/`fi`
locators for `invalidForwardRead`) and a `.scan _ | .pointwise _ | .axiswise _` arm using the generic
`PlanStep.sourceSlots`/`destinationSlots` accessors with placeholder locators `0 0`. `runDensePlan`'s
dispatch match already has all four `PlanStep` arms (Thread 4 added `.pointwise`/`.axiswise`).
`checkScanPlan` (`Scan.lean`) calls `checkPlanBlock raw.baseBlock`/`raw.stepBlock`, confirming
`RawPlanBlock`/`checkPlanBlock` is exactly the "block" half of the two structurally-parallel levels
the design doc's §5 describes.

**The `.freeNorm` inventory (design doc §8) — every site independently re-confirmed by direct
reading, not re-derived from the design doc's own list; the design doc directly confirmed only the
step-block `outputUids` site, this pass confirms the rest:**

| Site | Confirmed current behavior | Fix needed |
|---|---|---|
| step-block `outputUids` (`compileScan` Phase 4) | `slots.filterMap (fun sl => match sl with \| .free a => some a.uid \| _ => none)` — a `.freeNorm` slot falls into `_ => none`, silently dropped from the output shape | add `.freeNorm a` to the `some a.uid` arm |
| base-block `outputUids` (`compileScan` Phase 3) | identical pattern, identical bug, one function earlier | same fix |
| base write-map construction (`compileScan` Phase 3) | the per-slot loop building `StateWriteMap.map`'s rows matches `.iterAt _ lit`/`.free _`/falls to `.freeNorm _ \| .iterNext _ \| .affine _ => unreachable, throw unsupportedLhsSlot` | change the unreachable arm's `.freeNorm _` case to be treated identically to `.free _` (contributes an identity row at the next free position) |
| step write-map construction (`compileScan` Phase 4) | same shape: `.iterNext a`/`.free _`/falls to `.freeNorm _ \| .iterAt .. \| .affine _ => unreachable, throw` | same fix, `.freeNorm _` treated identically to `.free _` |
| scratch context-axis validation (`compileScan` Phase 1, non-state recurrence classification) | `.free a => if (ctxIndexOf a.uid).isSome then throw contextAxisAsFreeOutput` — a `.freeNorm` slot naming a context axis falls into the wildcard `_ => pure ()` and is silently NOT rejected | add `.freeNorm a` alongside `.free a` in this check |
| "unreachable"-commented branches assuming `.freeNorm` cannot appear in a scan block | both write-map sites above carry exactly this comment (`-- unreachable: Phase 1 rejected .iterNext here and preflight rejected .freeNorm/.affine in any scan block`) | update both comments alongside the code fix, Task 3's own discipline applied here |

No sixth site was found beyond the design doc's own list. `scanSlotAxisOrFail` (used throughout
Phase 1/2 for rank/geometry, e.g. `duplicateAxisInLhs`, `advancingAxisNotInLhs`,
`inconsistentStateExtent`) uses `LHSSlot.axisSpec?`, which ALREADY treats `.free`/`.freeNorm`
identically (`.free a => some a \| .freeNorm a => some a`) — confirmed by reading `DSL/Ast.lean`
directly, so Phase 1/2's rank/geometry logic needs NO fix; only Phase 3/4's write-side logic
(inventoried above) needs one, exactly matching the design doc's own framing ("the rule throughout:
`.freeNorm` contributes the same local UID, extent, and identity-placement row as `.free` everywhere
except the one place that inspects it specifically").

**A finding beyond the design doc's own explicit list, found this session, not previously called
out**: `checkScanPlan`'s own causality loop (`Scan.lean`) currently walks
`raw.stepBlock.assignments[ai].terms[ti].factors[fi]` for EVERY assignment in the step block, checking
`stateReadCausal` whenever a factor's `sourceSlot` matches a captured state. Once `RawPlanBlock.steps`
becomes `Array BlockStep`, this loop must dispatch: `.assign a => (unchanged term/factor loop)` /
`.pointwise _ | .axiswise _ => pure ()`. The `pure ()` case is not a gap: by this plan's own §6
publication contract (chaining helper), a `.pointwise`/`.axiswise` `BlockStep`'s `sourceSlot` is
ALWAYS a freshly-allocated internal slot produced by the immediately-preceding `.assign` step in the
SAME block — never a capture slot — so it can never be a captured-state read and needs no
independent causality check. Confirmed by re-deriving the chaining helper's own slot-allocation
scheme (Task 2/5 below): captures occupy positions `0 .. captureCount`, and internal/published slots
are allocated starting at `captureCount + stepsProducedSoFar`, strictly after every capture.

**The `route`/`repStmt` mislabeling bug the design doc's §1 documents as discovered-but-out-of-scope**
is independently reconfirmed by this pass's own reading of `Lowering.lean`'s `ScanStmt.repStmt`/
`ScanStmt.toBrBaseP` — real, pre-existing, unrelated to `Eval/Plan/`, not touched by this plan. Its
closure-task completion record must mention it for discoverability (per the design doc's own
instruction), without fixing it.

**`test/Eval/PropertyOracle/ScanUnroll.lean`/`ScanOracle.lean` need NO changes.** Confirmed by
reading both directly: `ScanUnroll.lean`'s `independentRun` implements the CHECKED (Jacobi) semantics
against the LEGACY evaluator's own split shape (`advScratch`, populated from `splitNonlins`'
`%nl`-shape directly, per its own doc comment) — entirely orthogonal to `Eval/Plan/`'s
`prepareEvalPlan`/`compileScan`, which this plan touches exclusively. `ScanOracle.lean`'s own scope
note states directly: it "runs over the whole 17-case corpus, INCLUDING the eight cases [the Plan
compiler] rejects as capability failures but which the legacy evaluator still executes" — i.e. its
two-way (legacy vs. independent-unroll) comparison has never depended on what the Plan-layer compiler
accepts. This matches the design doc's own Option-B resolution (§1): since `splitScan`/`splitNonlins`
stay untouched, nothing about the legacy-evaluator-facing oracle machinery changes.

**A real, load-bearing, previously-unstated finding: this plan changes `test/Eval/Plan/
DifferentialTest.lean`'s pinned scan-corpus split, and this is the INTENDED, designed-for outcome —
not a regression to guard against, unlike Thread 4's own "confirmatory, unchanged" framing for the
same guard.** Confirmed by reading `test/Eval/PropertyOracle/ScanGen.lean`'s `template2` directly:
its recurrence statement is `.assign "S" [.free j2, .iterNext l] { body := ...; nonlin := .pointwise
.relu }` — a `.pointwise` nonlinearity directly on a PERSISTENT STATE result (`S` also has a base
write, making it a state, not scratch) — exactly design decision #2 from the design doc's §4
("a persistent scan state may itself be the direct output of a nonlinearity"). This case carries NO
`.freeNorm` marker at all (pointwise needs none), so once `checkNonlinScanBlock` admits `.pointwise`
and `compileScan`'s Phase 1/3/4 correctly recombine and chain it, `template2`'s four generated cases
(`L ∈ {2,3} × Aneg ∈ {true,false}`) are predicted to move from `.rejectedNonlin` to `.accepted`.
`test/Eval/Plan/DifferentialTest.lean`'s `scanCorpusSplit` guard (currently pinned `total == 17 &&
accepted == 9 && nonlin == 4 && agg == 4`) must be re-pinned to the predicted `total == 17 && accepted
== 13 && nonlin == 0 && agg == 4` — Task 6 verifies this against a REAL `lake build` run and, if the
real run disagrees with this prediction, that is a genuine defect in Tasks 1-5 to report, not a
number to silently accept (mirroring this same file's own stop-condition precedent, applied in the
opposite direction from Thread 4's "no change expected" case). `checkScanCase`'s own `| cause => throw
"rejected for an unexpected reason"` fallback (already present, unmodified) already guards against a
DIFFERENT, unexpected new-tier rejection (e.g. a `.nonlin`/`.scan (.malformedNonlinSplit ...)` cause)
silently passing as `.rejectedNonlin` — no code change needed there, since no template is expected to
hit either.

**`RawPlanBlock`/`.assignments` usage sites across the whole repo**, via a direct grep (paths
relative to `leanncd/`), confirming the exact Files list for the rename task: production —
`LeanNCD/Eval/Plan/RawStep.lean` (the field), `LeanNCD/Eval/Plan/Block.lean` (`checkPlanBlock`/
`runDenseBlock`'s own reads), `LeanNCD/Eval/Plan/Scan.lean` (the causality loop, above), `LeanNCD/
Eval/Plan/Compile.lean` (`compileScan`'s Phase 3/4 construction sites, matched anonymously —
`RawPlanBlock`'s own name never appears literally there since the struct literal's type is inferred).
Tests, each constructing `RawPlanBlock` literals with `assignments := #[...]`: `test/Eval/Plan/
BlockTest.lean` (4 literal sites, 7 fixtures total), `test/Eval/Plan/ScanTest.lean` (≈25 literal
sites across 74 `run_cmd`/`#guard` entries), `test/Eval/Plan/ScanCompileTest.lean` (2 literal-
construction sites inside `compileScan`'s own output plus ≈9 `.assignments`-reading assertion
sites). `lakefile.toml`'s `Tests` `globs` list already includes all three test modules — no new
`globs` entry needed for this rename (only for a genuinely NEW test file, if one is added below).

**`test/Eval/Plan/CompileTest.lean`'s existing scan-block nonlin-rejection fixtures** (the two
`#guard errOf (capabilityPreflight { acceptedSched with stmts := [.scan "s" [...] [] [.assign "Y"
[.iterNext ...] {... nonlin := .pointwise .relu / .axiswise .softmax none}]  false] }) == some
(.unsupportedNonlin ...)` blocks) are the exact fixtures this plan must INVERT (same literal
programs, assertion flips from `errOf ... == some (.unsupportedNonlin ...)` to `isOk`).
`test/Eval/Plan/ScanContractTest.lean`'s `nonlinRecur`/`freeNormBase` fixtures test
`PlanContract.WaveF.classifyScanStmtF` — a SEPARATE, already-shipped, deliberately-FROZEN test-only
classifier (mirrors `checkScanBlockStmt`'s pre-Thread-4 shape but is never called from production
code) — confirmed unaffected by re-reading `ContractTest.lean`'s and `CompileTest.lean`'s own
comments, which already state this precedent for the analogous top-level case ("C0's frozen
`classifyNonlin` still rejects `.pointwise`/`.axiswise` outright"). **`ScanContractTest.lean` is NOT
touched by this plan** — its fixtures continue to assert the frozen classifier's own (unchanged)
behavior, exactly as `CompileTest.lean`'s comment already documents for the top-level analogue.

**Donor fixtures inventoried by name**, confirmed present via direct reading (not assumed from the
file names alone): `test/Eval/Plan/NonlinCheckTest.lean` — `baselinePointwise`/`baselineAxiswise`,
`pointwiseSourceSlotOob`/`axisiwiseSourceSlotOob`, `pointwiseDestSlotOob`/`axisiwiseDestSlotOob`,
`pointwiseSourceBoolDtype`/`axisiwiseSourceBoolDtype`, `pointwiseDestBoolDtype`/
`axisiwiseDestBoolDtype`, `pointwiseSourceShapeMismatch`/`axisiwiseSourceShapeMismatch`,
`pointwiseDestShapeMismatch`/`axisiwiseDestShapeMismatch`, `axisiwiseAxisPositionOob`,
`rank0Pointwise`/`rank0Axiswise`. `test/Eval/Plan/NonlinCompileTest.lean` — `reluProg`/
`reluProgPrepared` (`tlprog!{ H[i] := relu(W[i, j] · x[j]) }`), `softmaxProg`/`softmaxProgPrepared`
(`tlprog!{ Y[q, s.] := softmax(A[q, s]) }`), `spuriousMarkerPointwise`, `doubleMarkerAxiswise`.
`test/Eval/Plan/NonlinDenseTest.lean` — `pointwisePlan`/`pointwiseInputs` (relu on `[-1,2]` →
`[0,2]`), `axiswisePlan`/`axiswiseInputs` (normalize on `[[1,3],[2,2]]`). `test/Eval/Plan/
BlockTest.lean` — `stepBlock`/`blockAssign`/`blockSigs` (the accept baseline), `forwardReadBlock`/
`fwdAssignA`/`fwdAssignB` (the `invalidForwardRead` regression), `missingProductionBlock`. `test/Eval/
Plan/ScanCompileTest.lean` — the "I-J" base fixture (`baseBlock.assignments` asserted `outputShape
#[3]`), used as the donor for a base-block axiswise fixture's shape.

**`.claude/skills/slice-plan/check-snippet.sh` ran clean against every new Lean declaration this plan
ships**, four scratch files, all green on final form (one authoring-time fix, noted per-snippet below):
split-pair recombination (against the REAL `splitStmt`, not a simulated shape); the retained-local-
axis remap (`retainedAxisPos`, six cases including the design doc's own worked "iteration slot before
the marker" example); the shared chaining helper (`chainNonlinStep`/`NonlinChainedStep`) against the
real `AssignPlan`/`RawPointwisePlan`/`RawAxiswisePlan`; and the running slot-accounting scheme
`compileScan`'s Phase 3/4 needs once a statement can consume one or two physical slots. `WiringNode`/
`checkStepGraph` itself (two further `check-snippet.sh` passes) is verified in
`2026-08-21-wiring-loop-generalization.md`'s own §0/§7, not re-verified here — this plan only builds
new cases atop it. Full detail in §9 below.

## 1. Purpose

Lift the scope boundary Thread 4 deliberately left in place: a scan's `base`/`recur` blocks may now
carry a real `.pointwise`/`.axiswise` nonlinearity (unmasked), Dense-only, checked and executed with
the SAME `RawPointwisePlan`/`RawAxiswisePlan`/`checkPointwise`/`checkAxiswise`/`runDensePointwise`/
`runDenseAxiswise` machinery Thread 4 already built for the top level — no second nonlinearity
representation. This closes out thread 4's own architecture-doc row (which currently reads
"scan-block nonlinearity stays rejected") rather than opening a new thread.

## 2. Scope

### 2.1 In scope

- `compileScan`'s Phase 1 classifier recognizes and recombines `splitStmt`'s `%nl...`-prefixed
  split pairs back into one logical statement, before state/scratch classification runs.
- `checkNonlinTopLevel`/`checkNonlinScanBlock` merge into one `checkNonlin`, called identically by
  `checkStmt` and `checkScanBlockStmt`.
- `checkScanLHSSlot` admits `.freeNorm` (relaxed, not removed — same "admit syntactically, validate
  later" split `checkLHSSlot` already uses).
- A new `BlockStep` closed sum (`PlanStep` minus `.scan`) and `CheckedBlockStepEvidence`; `RawPlanBlock
  .assignments : Array AssignPlan` renamed to `steps : Array BlockStep`.
- A generalized availability/production-order wiring loop, shared by `checkPlan` (outer) and
  `checkPlanBlock` (block), with no behavior change to either's existing `.assign`/`.scan` handling.
- A shared two-step nonlin-chaining helper, used by `prepareEvalPlan`'s `.plain` branch (refactor,
  parity-gated) and `compileScan`'s base/step phases (new).
- The retained-local-axis remap for `resolveNonlinAxis`'s output, used identically by both callers.
- The `.freeNorm` inventory fixes in `compileScan`'s Phase 1/3/4 (table in §0 above).
- Base-block AND step-block nonlinearity; a persistent state may itself be the direct output of a
  nonlinearity (design decisions #1/#2).
- New end-to-end fixtures (pointwise-on-scratch, pointwise-on-state, axiswise-on-scratch, axiswise-
  on-state, base-block nonlinearity, positional-correctness cases) plus the re-pinned
  `scanCorpusSplit` guard.

### 2.2 Explicitly out of scope (deliberate, stated plainly so a reader does not assume otherwise)

- **Masked `.axiswise` inside a scan block stays deferred**, exactly as at the top level — rejected
  by the SAME `resolveNonlinAxis` call (`maskedAxiswiseNotSupported`), no new mechanism. It would
  need a UID-free, position-based compiled predicate IR with no precedent in this codebase; that is
  new IR design work, not in this plan's sizing.
- **Boolean dtypes** are untouched — orthogonal, `ScalarDType.bool` remains reserved-but-unused
  everywhere in `Eval/Plan/`.
- **Scatter** is untouched — a scatter statement is rejected unconditionally by `checkStmt`/
  `checkScanBlockStmt` before `checkNonlin` is ever reached, regardless of this plan.
- **Iverson predicate factors** are untouched — orthogonal to `BlockStep`/nonlin chaining, live two
  levels below (`AssignPlan.terms[*].factors`), already shared between block and outer contexts for
  a reason unrelated to this plan (same `AssignPlan`/`TermPlan` type in both contexts).
- **The `route`/`ScanStmt.repStmt` mislabeling bug** (design doc §1) is real, pre-existing, and
  reachable today through `TLProgram.compile`/the `tl!{...}` macro for any nonlinear scan statement
  — flagged in this plan's closure-task completion record for discoverability, not fixed here; it
  belongs to the Br/categorical lowering subsystem, not the Eval/Plan Backend IR this plan targets.
- **PyTorch/JAX interpreter support for the new scan-block nonlin steps** is unaffected by this plan
  in the same way it was unaffected by Thread 4 — `RawPointwisePlan`/`RawAxiswisePlan`/
  `CheckedPointwisePlan`/`CheckedAxiswisePlan` are unchanged types, already backend-neutral; only
  Dense workers exist, exactly as before.
- **The scan-block redundant identity-copy inefficiency** (three compiled `BlockStep`s per real
  nonlin statement instead of two, mirroring the top-level path's own known redundancy from Thread
  4's Task 3) is inherited, not fixed — Option A (which would have avoided it) was ruled out by the
  design doc's §1 for carrying unbounded risk into `route`/the oracle machinery, for a benefit not
  worth that risk.

### Global constraints (exact values)

- `test/Eval/Plan/DifferentialTest.lean`'s `scanCorpusSplit` guard changes from `total == 17 &&
  accepted == 9 && nonlin == 4 && agg == 4` to `total == 17 && accepted == 13 && nonlin == 0 && agg
  == 4` (Task 6) — a predicted, designed-for change, verified against a real `lake build` run before
  landing, not assumed.
- `LeanNCD/Eval/AGENTS.md`'s "Find It Fast" `Plan/` row stays at **17 files** — this plan adds no new
  file, only new declarations inside existing ones (unlike Thread 4, which added `Nonlin.lean` and
  incremented 16→17).
- `test/Eval/PropertyOracle/ScanUnroll.lean`/`ScanOracle.lean`: **zero changes**, confirmed in §0.
- `LeanNCD/DSL/Pipeline/Lowering.lean` (`splitStmt`/`splitScan`/`splitNonlins`) and `LeanNCD/DSL/
  AGENTS.md`: **zero changes** — the design doc's Option-B decision and this plan's own §0 both
  confirm nothing about the split shape or its documentation needs to move.
- `test/Eval/Plan/ScanContractTest.lean`: **zero changes** — frozen test-only classifier, confirmed
  in §0.

## 3. Architecture

### 3.1 Split-pair recombination (`compileScan` Phase 1)

A new function, `recombineNonlinSplitPairsCore`, walks a destructured `base`/`recur` triple list
(`List (String × List LHSSlot × RHSExpr)`, `assignPartsOrFail`'s own output type) and merges an
adjacent `%nl`-prefixed linear half with its nonlin partner into one logical triple carrying the
partner's own `name`/`slots`/`nonlin` and the linear half's own `body`/`agg` — reconstructing exactly
what the statement looked like before `splitStmt` split it. A statement that was never split passes
through unchanged.

Three independent confirmations gate the merge (matching this file's own "necessary, not sufficient"
preflight discipline elsewhere): the first half's name starts with `"%nl"` (a `FreshM`-fresh name,
never producible by surface syntax); its own `nonlin` is `.identity`; its successor's `readFactors`
is exactly `[(name, _)]` (a trivial single read of it, via the existing `RHSExpr.readFactors`
accessor — chosen over comparing `List IdxExpr` directly, since `IdxExpr` has no `BEq`). Any mismatch
throws a new `ScanCompileError.malformedNonlinSplit` — a compiler-internal-bug signal (this shape is
guaranteed by `splitStmt`'s own construction for any program that went through the real pipeline),
never a silent fallback.

Verified via `check-snippet.sh` against the real `splitStmt`, `LHSSlot`, `RHSExpr`, and
`readFactors`:

```lean
private def recombineNonlinSplitPairsCore (scanName : String) (isBase : Bool) :
    Nat → List (String × List LHSSlot × RHSExpr) →
    Except ScanCompileError (List (String × List LHSSlot × RHSExpr))
  | _, [] => pure []
  | i, (n1, s1, r1) :: rest =>
      if n1.startsWith "%nl" then
        match r1.nonlin, rest with
        | .identity, (n2, s2, r2) :: rest' =>
            match r2.readFactors with
            | [(rn, _)] =>
                if rn == n1 then do
                  let tail ← recombineNonlinSplitPairsCore scanName isBase (i + 2) rest'
                  pure ((n2, s2, { body := r1.body, nonlin := r2.nonlin, agg := r1.agg }) :: tail)
                else throw (.malformedNonlinSplit scanName isBase i n1)
            | _ => throw (.malformedNonlinSplit scanName isBase i n1)
        | _, _ => throw (.malformedNonlinSplit scanName isBase i n1)
      else do
        let tail ← recombineNonlinSplitPairsCore scanName isBase (i + 1) rest
        pure ((n1, s1, r1) :: tail)
```

`i` is threaded purely for the error's own `stmtIndex` locator (a logical position: recombined
entries advance it by 2, unrecombined ones by 1) — it plays no role in the recursion's own
termination, which is by strict structural decrease on the list argument.

Called from `compileScan`'s Phase 1, immediately after `baseParts ← liftCapability warnings
(base.toArray.mapM (assignPartsOrFail "scan base"))` (and identically for `recurParts`), replacing
each with its recombined `.toArray`, wrapped at the call site via `scanErr warnings` (this file's own
established pattern for `ScanCompileError`, since no generic `liftX` exists for it — confirmed by
re-reading the file's own `liftCapability`/`liftShape`/`liftPlanError`/`liftBindings`/`liftNonlin`
family and `scanErr`'s own doc comment, which states directly that `ScanCompileError` has no upstream
`Except` to lift because `compileScan` builds it "at dozens of sites" via direct value construction —
this call site is the first exception, a genuine new `Except ScanCompileError` value needing the same
`scanErr`-wrapping treatment manually).

New `ScanCompileError` constructor (`Error.lean`, alongside the existing "block dependency order"
group):

```lean
| malformedNonlinSplit (scan : String) (isBase : Bool) (stmtIndex : Nat) (name : String)
```

### 3.2 Retained-local-axis remap (§2 of the design doc)

`resolveNonlinAxis` is unchanged. Its returned position `p` indexes the statement's FULL LHS slot
list; a scan-block statement's own local output shape (built from `.free`/`.freeNorm`-only filtering,
per the §0 inventory) excludes `.iterAt`/`.iterNext` positions entirely, so `p` must be remapped to
its position among retained (`.free`/`.freeNorm`) slots before it can be `RawAxiswisePlan.axisPos`.

```lean
def retainedAxisPos (slots : List LHSSlot) (p : Nat) : Nat :=
  ((slots.take (p + 1)).filter (fun sl => match sl with
    | .free _ | .freeNorm _ => true | _ => false)).length - 1
```

Verified via `check-snippet.sh`, six cases: two top-level no-op cases (marker with no interleaved
iteration slots at all, confirming the remap is provably identity there); the design doc's own worked
example (`.iterNext axL` at position 0, `.freeNorm axJ` at position 1 → remaps to local position 0);
an iteration slot AFTER the marker (no shift); iteration slots interleaved between multiple local
axes with the marker last; and a multi-axis, non-trailing-advancing-dimension case (two iteration
slots surrounding one free slot, marker after all of them) — all six match hand-computed expectations
exactly.

Both callers (top-level `.plain` branch and `compileScan`'s Phase 3/4) apply this remap to
`resolveNonlinAxis`'s output before building a `RawAxiswisePlan`, including the top-level caller
(where it is provably a no-op, per the design doc's own instruction to make this one application of
a shared function rather than an implicit identity — Task 3's mutation check confirms the no-op
claim directly).

### 3.3 The shared chaining helper

Extracted from `prepareEvalPlan`'s `.plain` branch's existing two-step-vs-one-step logic (Thread 4
Task 3), generalized to be node-kind-agnostic: it builds only the raw ingredients
(`AssignPlan`, optionally paired with a `RawPointwisePlan`/`RawAxiswisePlan`), never a `PlanStep`/
`BlockStep` itself — each caller wraps the result into whichever closed sum it needs.

```lean
inductive NonlinChainedStep
  | assignOnly          (a : AssignPlan)
  | assignThenPointwise (a : AssignPlan) (p : RawPointwisePlan)
  | assignThenAxiswise  (a : AssignPlan) (x : RawAxiswisePlan)

def chainNonlinStep (nonlin : Nonlin) (axisPos : Option Nat) (assignPlan : AssignPlan)
    (outputShape : Array Nat) (internalSlot publishedSlot : TensorSlot) : NonlinChainedStep :=
  match nonlin with
  | .identity => .assignOnly assignPlan
  | .pointwise pf =>
      .assignThenPointwise assignPlan
        { sourceSlot := internalSlot, destinationSlot := publishedSlot, shape := outputShape
        , fn := pf }
  | .axiswise fn _ =>
      .assignThenAxiswise assignPlan
        { sourceSlot := internalSlot, destinationSlot := publishedSlot, shape := outputShape
        , axisPos := axisPos.getD 0, fn := fn }
```

Verified via `check-snippet.sh` against the real `AssignPlan`/`RawPointwisePlan`/`RawAxiswisePlan`,
three cases (identity threads the payload verbatim; pointwise and axiswise each build the correct
raw step at the caller-supplied slots).

**Publication contract** (design doc §6), enforced by construction, not by a runtime check: for
`.identity`, the caller must pass the SAME value for `internalSlot`/`publishedSlot` (one physical
slot, published directly — byte-for-byte what `prepareEvalPlan` already does today); for a real
nonlinearity, the caller allocates TWO distinct slots and this function is called only AFTER
`resolveNonlinAxis` (and, inside a scan block, `retainedAxisPos`) has already succeeded — a rejected
statement allocates nothing and never reaches this function. Callers publish (name-environment /
block-output bookkeeping) only `publishedSlot`, never `internalSlot` — this is the caller's own
responsibility (§3.5 below), not something `chainNonlinStep` enforces internally, since it has no
name environment or output-slot list to enforce it against.

### 3.4 The generalized wiring loop (built by a prerequisite slice)

`WiringNode`/`checkStepGraph` — the shared generalization of `checkPlan`'s and `checkPlanBlock`'s
wiring loops — is built entirely by `2026-08-21-wiring-loop-generalization.md`'s own Task 1, landed on
`main` before this plan's own execution starts; see that plan's §3 for the type, the `liftWiring :
PlanError → E` collapse, and its two-instantiation verification. This plan's own Task 1 (§3.5 below)
only ADDS new `WiringNode`-building cases to `checkPlanBlock`'s existing per-node loop for the two new
`BlockStep` arms — it does not touch `checkStepGraph`/`WiringNode` themselves.

### 3.5 `BlockStep`/`CheckedBlockStepEvidence`

```lean
inductive BlockStep
  | assign    (a : AssignPlan)
  | pointwise (p : RawPointwisePlan)
  | axiswise  (a : RawAxiswisePlan)
  deriving DecidableEq, BEq, Repr, Inhabited

def BlockStep.sourceSlots : BlockStep → Array TensorSlot
  | .assign a => a.terms.flatMap (·.factors.map (·.sourceSlot))
  | .pointwise p => #[p.sourceSlot]
  | .axiswise a => #[a.sourceSlot]

def BlockStep.destinationSlot : BlockStep → TensorSlot
  | .assign a => a.destinationSlot
  | .pointwise p => p.destinationSlot
  | .axiswise a => a.destinationSlot
```

`BlockStep`/its two accessors live in `RawStep.lean`, immediately before `RawPlanBlock` (whose
`assignments : Array AssignPlan` field is renamed to `steps : Array BlockStep`) — `RawStep.lean`
already imports both `Kernel.lean` (`AssignPlan`) and `Nonlin.lean` (`RawPointwisePlan`/
`RawAxiswisePlan`), so this needs no new import. `CheckedBlockStepEvidence` (mirroring
`CheckedPlanStepEvidence`'s shape, one arm per `BlockStep` constructor) lives in `Block.lean` itself —
unlike `CheckedPlanStepEvidence`, which had to move to `EvalPlan.lean` because `checkPlan` needs both
`checkAssign` AND `checkScanPlan` simultaneously visible, `Block.lean` already transitively sees
`checkAssign` (via `Dense.lean → Check.lean`) AND `checkPointwise`/`checkAxiswise` (via `Dense.lean →
Check.lean → Graph.lean → RawStep.lean → Nonlin.lean`) — confirmed by reading this exact import
chain directly, not assumed; `BlockStep` never needs `checkScanPlan` at all, so it has no reason to
move further downstream.

```lean
inductive CheckedBlockStepEvidence
  | assign    (c : CheckedAssignPlan)
  | pointwise (c : CheckedPointwisePlan)
  | axiswise  (c : CheckedAxiswisePlan)
```

`BlockError` gains one new arm, mirroring `PlanStepError.nonlin` exactly (`NonlinPlanError` carries
no locator of its own, so `nodeIndex` is real new information):

```lean
| nonlin (nodeIndex : Nat) (cause : NonlinPlanError)
```

`checkPlanBlock` is rewritten to build one `WiringNode BlockError CheckedBlockStepEvidence` per
`BlockStep` (via a `match step with | .assign a => ... | .pointwise p => ... | .axiswise a => ...`
building each field), and to delegate the whole loop to `checkStepGraph n block.inputs
BlockError.wiring nodes`; the pre-existing `outputs`-range/uniqueness check and the block-context
obligation (`blockContextMismatch`, built into each node's own `contextCheck`) are unchanged in
substance, just re-homed into this call shape. `.assign`'s own `sourceCheck` keeps the rich per-term/
per-factor loop (preserving `ti`/`fi`); `.pointwise`/`.axiswise` use the generic `BlockStep.
sourceSlots`-based loop with placeholder locators `0 0` — the identical split `checkPlan` already
uses for `.assign` vs. `.scan`/`.pointwise`/`.axiswise`.

`runDenseBlock`'s dispatch loop gains a 3-arm match mirroring `runDensePlan`'s own dispatch pattern
exactly: `.assign c => runDenseAssignAt` (unchanged); `.pointwise c => runDensePointwise c
(store.getD c.raw.sourceSlot placeholder)`; `.axiswise c => runDenseAxiswise c (store.getD
c.raw.sourceSlot placeholder)`, writing to `c.raw`/`node.plan`'s own destination slot in each case
(`BlockStep.destinationSlot`-shaped access, per-arm rather than through the generic accessor, since
`runDenseBlock` already destructures `CheckedBlockStepEvidence` for its own worker dispatch anyway).

`checkPlan` (`EvalPlan.lean`) is likewise rewritten onto `checkStepGraph`, its 4 `PlanStep` arms
built the same way; `runDensePlan` is UNCHANGED (Thread 4 already gave it all 4 arms).

### 3.6 `compileScan`'s Phase 3/4 slot accounting

Once a base/step statement can consume ONE (`.identity`) or TWO (`.pointwise`/`.axiswise`) physical
destination slots, the existing index-based formula (`destSlot := baseInputCount + bi` / `stepInputCount
+ ri`, one slot per LOOP INDEX) no longer holds — statement count and physical-slot count diverge.
The fix: allocate from a RUNNING COUNTER (`baseStepsAcc.size` / `stepStepsAcc.size`, the number of
`BlockStep`s pushed SO FAR), since every `BlockStep`, of any kind, consumes exactly one destination
slot.

```lean
def allocateBlockSlots (inputCount : Nat) (stepsSoFar : Nat) (nonlin : Nonlin) :
    TensorSlot × TensorSlot × Nat :=
  let internalSlot := inputCount + stepsSoFar
  match nonlin with
  | .identity => (internalSlot, internalSlot, 1)
  | _ => (internalSlot, internalSlot + 1, 2)
```

Verified via `check-snippet.sh`: three individual calls matching hand-computed slot numbers for a
mixed identity/pointwise/axiswise sequence at `inputCount = 5`, then a left `foldl` across the whole
sequence (both in natural order and reversed, confirming the accounting is order-general, not an
artifact of "identity always first") producing the correct PUBLISHED-slot array — exactly what
`RawPlanBlock.outputs` (base) / the state-write `outputSlot` list (step) must become, REPLACING
today's `(Array.range baseParts.size).map (· + baseInputCount)` formula, which assumed one statement
= one slot.

Applied per-statement inside Phase 3 (base) / Phase 4 (step), in this order, for the RECOMBINED
triple `(nm, slots, rhs)`: compute `outputUids`/`outputShape` (via the §0-inventory-fixed
`.free`/`.freeNorm` filter); resolve `axisPos? ← liftNonlin warnings (resolveNonlinAxis nm rhs.nonlin
slots)`, remapped via `retainedAxisPos slots` when `some`; allocate `(internalSlot, publishedSlot,
consumed) := allocateBlockSlots baseInputCount baseStepsAcc.size rhs.nonlin`; run
`residualizeAssignment` targeting `internalSlot` (UNCHANGED — its own doc comment already states it
only builds the `AssignPlan` value, publication is the caller's policy); call `chainNonlinStep
rhs.nonlin axisPos? assignPlan outputShape internalSlot publishedSlot`; push `.assign`/`.pointwise`/
`.axiswise` `BlockStep`(s) onto `baseStepsAcc`/`stepStepsAcc` (one or two, matching
`NonlinChainedStep`'s own arm) and the corresponding `TensorSignature`(s) onto `baseSigs`/`stepSigs`
(both slots share `outputShape` when two are allocated — the nonlin step is shape-preserving by the
raw types' own field structure); record `publishedSlot` (never `internalSlot`) as the base write's
`StateWriteMap.outputSlot` / the step's `resultSlotOf`/`scratchSlotOf` entry / the base block's own
`outputs` array entry.

This is the mechanism that makes §3's publication law (design doc §3: only the result slice is ever
named/published; the preactivation is produced but never externally visible) hold by CONSTRUCTION:
nothing outside this per-statement block ever sees `internalSlot`.

**A load-bearing safety-net dependency, not a checker gap** (required per the skill's own §2, since
this is exactly the "which rows must vs. must not be a given kind" write-geometry defect shape's
sibling question, applied to "which slot a write targets" rather than "which rows"): if Phase 3/4
ever mistakenly recorded `internalSlot` instead of `publishedSlot` as a `StateWriteMap.outputSlot`,
would any checker catch it? Yes — `checkWrites` (`Scan.lean`, unchanged by this plan) already
requires `block.outputs.contains w.outputSlot` (`writeSourceNotBlockOutput`) and that every declared
output is written exactly once (`blockOutputNotWritten`); PROVIDED `outputs`/`stepOutputs` themselves
are built correctly (this plan's own new responsibility, verified above), a wrong `outputSlot`
mapping is rejected there. Task 5 pins this with a deliberate mutation fixture (build a
`StateWriteMap` pointing at the internal slot instead of the published one; confirm `checkScanPlan`
rejects it via `writeSourceNotBlockOutput`) rather than treating the existing check as
folklore-safe by inference.

## 4. Case × class table — `checkNonlinIO`'s reuse inside the block-level checker

Required per the slice-plan skill: `checkPointwise`/`checkAxiswise`/`checkNonlinIO` are reused **100%
verbatim** at block level (zero code changes — confirmed: `Nonlin.lean` is untouched by this plan),
but every `(c)`/silently-ignored cell is a candidate instance _N+1_ of the write-geometry defect shape
regardless of whether the reused code itself changed. Rows 1-15 restate Thread 4's own Task 1 table,
confirmed unchanged at block level; rows 16-19 are new, specific to the block-level reuse context.

| # | Case | At block level | Class |
|---|---|---|---|
| 1-9 | slot range, dtype (×2), dtype agreement, shape agreement (×2), axisPos range, rank-0 admission | Identical semantics — `checkPointwise`/`checkAxiswise` take `sigs : Array TensorSignature`, which at block level is `block.tensorSigs` (the block's own LOCAL table), exactly mirroring how `.assign`'s own `checkAssign` already operates against `block.tensorSigs` inside `checkPlanBlock` today | **Required, unchanged from Thread 4** |
| 10 | masked axiswise forbidden | `RawAxiswisePlan` has no mask field regardless of context — still forbidden by type absence uniformly | Forbidden by type absence |
| 11 | negative axisPos | `axisPos : Nat` regardless of context | Forbidden by type |
| 12 | `sourceSlot == destinationSlot` (never-produced) | The SAME unreachability argument transfers, proven by the SAME `checkStepGraph` code (not a re-derivation): destination-check-then-source-check against one shared `available` snapshot per node, identical at both call sites | Silently ignored *locally*, proven unreachable structurally — pinned by a Task 1 regression fixture at the block level too (mirroring Thread 4's own Task 2 pair) |
| 13 | duplicate destination | Owned by `checkStepGraph`'s outer bookkeeping, shared with the outer call site | Silently ignored by design, shared ownership |
| 14 | forward read | Same | Silently ignored by design, shared ownership |
| 15 | worker-side out-of-bounds | `runDensePointwise`/`runDenseAxiswise` reused verbatim; still shape-preserving by construction (no coordinate arithmetic that can go out of range) — unaffected by which store array `runDenseBlock` passes them versus `runDensePlan` | Not a write-path predicate at all, same reasoning as Thread 4's own row 15 |
| 16 | block-context obligation (`blockContextMismatch`) applied to a `.pointwise`/`.axiswise` `BlockStep` | `RawPointwisePlan`/`RawAxiswisePlan` carry no `contextShape` field at all — nothing to check against, mirroring the outer level's own "skips `checkAssign`'s specific check since it has no `contextShape` field" treatment exactly | N/A by type absence, not a gap |
| 17 | nonlin step's destination membership in `block.outputs` | Neither `checkNonlinIO` nor `checkPointwise`/`checkAxiswise` inspect `block.outputs` at all — correctly so, since `.assign` doesn't either; outputs-membership is `checkWrites`'/`checkPlanBlock`'s own outer bookkeeping, never a per-node checker's job | N/A — owned entirely by the caller's bookkeeping, identical division of labor to `.assign` |
| 18 | internal-vs-published slot confusion (a write-map naming the wrong physical slot) | `checkNonlinIO` has zero awareness of "internal" vs. "published" — that distinction is `chainNonlinStep`'s/`compileScan`'s own responsibility. **Not silently unguarded**: `checkWrites`'s existing `writeSourceNotBlockOutput`/`blockOutputNotWritten` (`Scan.lean`, unchanged) catch a wrong mapping, PROVIDED this plan's own `outputs`/`stepOutputs` accumulator (§3.6) is itself built correctly — the safety net is pre-existing, but the precondition it relies on is THIS plan's new code, not already-proven | Silently ignored by `checkNonlinIO` itself, proven safe by an existing sibling check under a NEW precondition — pinned by Task 5's own mutation fixture (§3.6), not left as an inferred guarantee |
| 19 | per-step/per-base slice shape vs. a state's complete-history shape | `outputShape`/`shape` passed into `chainNonlinStep` is always the block's own local per-statement slice (from `resolveSizeOrFail` over the statement's own retained UIDs) — `checkNonlinIO` never sees, and does not need to know about, a state's complete-history shape (which lives only in the OUTER `tensorSigs` table, at the state's own `destSlot`) | Required and automatically correct by construction, mirroring how `.assign`'s own `outputShape` already works today |

## 5. Task graph and review weight

```text
Task 1: BlockStep/CheckedBlockStepEvidence + assignments→steps rename ──┐
                                                                          │
Task 2: shared chaining helper + .plain branch refactor ─────────────────┤
                                                                          ├─> Task 5: Phase 2/3/4
Task 3: checkNonlin merge + checkScanLHSSlot relaxation ─────────────────┤    integration
                                                                          │
Task 4: compileScan Phase 1 split-pair recombination ────────────────────┘
                                                                               │
                                                                               ▼
                                                                          Task 6: differential/
                                                                          corpus + closure
```

Task 1 depends on the wiring-loop generalization slice (`2026-08-21-wiring-loop-generalization.md`)
having already landed — it wires `checkPlanBlock`/`runDenseBlock` onto the `checkStepGraph` loop that
slice generalizes (§3.4). Tasks 2, 3, and 4 are each independent of Task 1 and of each other (different
files/functions, no shared mutable state, verified above via three separate spike files with zero
cross-dependency) and may run in parallel with Task 1 and with each other. Task 5 depends on ALL of
Tasks 1-4: it needs `BlockStep` to exist (Task 1), the chaining helper (Task 2), the relaxed preflight
so a real program can reach `compileScan` at all (Task 3), and recombined statements to operate on
(Task 4). Task 6 depends on Task 5.

Task 1 touches the closed `RawPlanBlock`/`CheckedPlanBlock`/`PlanStep`/`CheckedPlanStepEvidence`
sums every backend and every existing `.assign`/`.scan` test depends on — soundness-relevant, per this
repo's own standing rule; it gets two independent reviewers, the same standing rule the wiring-loop
generalization slice's own Task 1 already applied to itself. Task 5 is the architectural centerpiece
(mirrors Thread 4's own Task 3 in weight) and also gets two independent reviewers for the same reason.

| Task | Outcome | Independent review reason | Risk / process weight |
|---|---|---|---|
| 1 | `BlockStep`/`CheckedBlockStepEvidence` (new); `RawPlanBlock.assignments` → `steps : Array BlockStep`; `checkPlanBlock`/`runDenseBlock` rewired with 3 arms; `BlockError.nonlin` (new); `Scan.lean`'s causality loop dispatches on `BlockStep` | Touches the closed sum every scan depends on, PLUS a wide mechanical rename (≈40 call sites across 3 test files) a reviewer needs the exact file list for, not a skim | **High, two independent reviewers** for the closed-sum/new-arms half; the rename half is mechanical (≈40 literal-site edits: wrap each existing `AssignPlan` in `.assign`, rename the field) verified by full-suite green, not independently risky once the type change is right. Two NEW fixtures (a pointwise and an axiswise `BlockStep`, donors named in Task 1 below) plus the two `sourceSlot==destinationSlot` regressions mirroring Thread 4's own Task 2 pair. |
| 2 | `chainNonlinStep`/`NonlinChainedStep`; `prepareEvalPlan`'s `.plain` branch refactored onto it | New, small, isolated function plus a refactor of already-shipped compiler code with an explicit parity gate | **Moderate.** One parity fixture (`.identity` byte-for-byte unchanged — re-run an existing `NonlinCompileTest.lean` identity-path fixture unedited) plus the 3 cases already verified in §3.3. |
| 3 | `checkNonlin` (merged); `checkScanLHSSlot` admits `.freeNorm` | Preflight-only change, independently reviewable and testable without any of Tasks 1/2/4/5 existing yet | **Low-moderate.** 3 fixture edits: invert `CompileTest.lean`'s two existing scan-block-rejection guards (`errOf ... unsupportedNonlin` → `isOk`); add one new `.freeNorm`-inside-a-scan-admitted fixture (donor: the existing top-level `.freeNorm`-admitted fixture, adapted to a `.scan` wrapper). `ScanContractTest.lean` explicitly NOT touched (§0). |
| 4 | `ScanCompileError.malformedNonlinSplit` (new); `recombineNonlinSplitPairsCore`/wiring into Phase 1 | New logic with no precedent to copy, but self-contained (pure function over statement triples) and unit-testable without any of Tasks 1/2/3/5 | **Moderate.** Verified via `check-snippet.sh` against the REAL `splitStmt` (§0/§3.1) — the implementer re-runs the identical style of fixture as a real `test/Eval/Plan/ScanCompileTest.lean` addition (a genuine `.scan` node whose recurrence has `nonlin ≠ .identity`, run through `compileToScheduled` then Phase 1 directly, asserting the recombined triple's exact shape), plus one `malformedNonlinSplit` fixture (a hand-built triple list violating the trivial-read shape). |
| 5 | `retainedAxisPos`; Phase 3/4 slot accounting (`allocateBlockSlots`); `resolveNonlinAxis`/`chainNonlinStep` wired into Phase 3/4; the `.freeNorm` inventory fixes; base/step `BlockStep` sequences instead of single `AssignPlan`s | Architectural centerpiece — new classification/compilation logic with no precedent to copy, the design doc's own highest-uncertainty area | **High, two independent reviewers, no fixture-count discount.** Full test matrix per §12 below: positional-correctness (≥4), publication-correctness (≥5), base-block-correctness (≥3), negative (≥4), plus the internal/published-slot mutation fixture (§3.6). Expect at least one fix round; its own gate re-runs the FULL `Eval.Plan.*` suite, not just its own new fixtures, mirroring Thread 4's Task 3 precedent for the same reason (it edits `compileScan`, the one production scan-specializer every scan fixture depends on). |
| 6 | New end-to-end differential fixtures; re-pinned `scanCorpusSplit` (predicted `13/0/4`); doc corrections; discoverability; completion record; whole-branch review | Every prior slice's most valuable finding came from the whole-branch tier, never a per-task diff | **High, two independent reviewers.** |

## Task 1: `BlockStep`/`CheckedBlockStepEvidence`

### Outcome

`RawPlanBlock.steps : Array BlockStep` (renamed from `assignments : Array AssignPlan`);
`CheckedPlanBlock.checkedNodes : Array CheckedBlockStepEvidence`; `checkPlanBlock`/`runDenseBlock`
handle all 3 `BlockStep` arms via the `checkStepGraph` loop from `2026-08-21-wiring-loop-generalization.md`'s
own Task 1; `Scan.lean`'s causality loop dispatches
on `BlockStep`; every existing `RawPlanBlock` literal across the test suite is updated to the new
field name and wraps its existing `AssignPlan`s in `.assign`.

### Files

- `LeanNCD/Eval/Plan/RawStep.lean` (`BlockStep`, `BlockStep.sourceSlots`/`destinationSlot`;
  `RawPlanBlock.assignments` → `steps : Array BlockStep`)
- `LeanNCD/Eval/Plan/Block.lean` (`CheckedBlockStepEvidence`; `BlockError.nonlin`; `checkPlanBlock`/
  `runDenseBlock` rewired with 3 arms, using `checkStepGraph` from `2026-08-21-wiring-loop-
  generalization.md`'s own Task 1)
- `LeanNCD/Eval/Plan/Scan.lean` (the causality loop's dispatch, §0's own finding)
- `test/Eval/Plan/BlockTest.lean` (field rename in every literal; two new fixtures)
- `test/Eval/Plan/ScanTest.lean` (field rename in every literal — ≈25 sites, no behavior change)
- `test/Eval/Plan/ScanCompileTest.lean` (field rename at `compileScan`'s own two construction sites,
  which this file exercises indirectly through `prepareEvalPlan`; its `.assignments`-reading
  assertions become `.steps`-reading, unwrapping `.assign a => a...` where a field of the wrapped
  `AssignPlan` is inspected)

### Implementation

1. `RawStep.lean`: add `BlockStep`/`BlockStep.sourceSlots`/`BlockStep.destinationSlot` exactly as
   verified in §3.5, immediately before `RawPlanBlock`. Rename `RawPlanBlock.assignments` to `steps :
   Array BlockStep`.
2. `Block.lean`: add `CheckedBlockStepEvidence` (§3.5); add `BlockError.nonlin (nodeIndex : Nat)
   (cause : NonlinPlanError)`, re-deriving `BlockError`'s existing `DecidableEq, BEq, Repr, Inhabited`
   (all already-supported field types). Rewrite `checkPlanBlock`'s node-building (from the
   `AssignPlan`-only `WiringNode`-per-assignment loop built by `2026-08-21-wiring-loop-
   generalization.md`'s own Task 1) into a `match step with | .assign a => ... |
   .pointwise p => ... | .axiswise a => ...` building each field per arm — `.assign`'s arm is
   that other plan's own code unchanged; `.pointwise`/`.axiswise` use `BlockStep.sourceSlots`/
   `destinationSlot` for the generic source-check/destination-slots fields (placeholder locators
   `0 0`, mirroring `checkPlan`'s own `.scan`/`.pointwise`/`.axiswise` treatment) and `checkPointwise`/
   `checkAxiswise` for `localCheck`, wrapping a failure as `.nonlin ni e`. Rewrite `runDenseBlock`'s
   dispatch loop with the 3-arm match (§3.5).
3. `Scan.lean`: change the causality loop's iteration from `raw.stepBlock.assignments[ai]` (an
   `AssignPlan` directly) to `match raw.stepBlock.steps[ai] with | .assign a => (existing term/
   factor loop, unchanged) | .pointwise _ | .axiswise _ => pure ()`, per §0's own finding and its
   justification (a nonlin `BlockStep`'s source is always a freshly-allocated internal slot,
   never a capture).
4. Every other `.assignments` read/construction site in `Scan.lean`/`Block.lean`/`Compile.lean` is
   Task 5's concern (Phase 3/4 construction) except the ones this task must fix for the TEST suite to
   keep compiling: `BlockTest.lean`/`ScanTest.lean`/`ScanCompileTest.lean`'s own literals, updated
   mechanically (`assignments := #[a1, a2]` → `steps := #[.assign a1, .assign a2]`; every
   `.assignments.getD i default`/`.assignments.size`/`.assignments.map (...)` read updated to `.steps`
   with an added `.assign a =>`/`match` where the read inspects an `AssignPlan` field directly).

### Fixtures (donors named)

- **Block-level pointwise/axiswise accept**, `BlockTest.lean`: clone `stepBlock`/`blockAssign`'s
  shape, add a second slot and a `.pointwise { sourceSlot := 1, destinationSlot := 2, shape := #[3],
  fn := .relu }` `BlockStep` after the existing `.assign`, mirroring `NonlinDenseTest.lean`'s
  `pointwisePlan` donor tensor (`relu` on a small vector) — confirm `checkPlanBlock` accepts and
  `runDenseBlock` produces the expected tensor. Clone again with `.axiswise { ...; axisPos := 1; fn :=
  .normalize }`, donor tensor from `NonlinDenseTest.lean`'s `axiswisePlan`/`axiswiseInputs`.
- **`sourceSlot == destinationSlot`, never-produced** (mirrors Thread 4's Task 2 pair, at block
  level): clone `BlockTest.lean`'s `forwardReadBlock` shape but with a single `.pointwise { sourceSlot
  := 1, destinationSlot := 1, ... }` step where slot 1 is not a block input and has no producer;
  confirm `checkPlanBlock` rejects via `.wiring (.invalidForwardRead ...)`.
- **`sourceSlot == destinationSlot`, already-produced**: clone the above with an `.assign` producing
  slot 1 first; confirm rejection via `.wiring (.duplicateDestination ...)`.

### Mutation checks

- Remove the `.pointwise`/`.axiswise` arms from `runDenseBlock`'s dispatch one at a time; the
  corresponding fixture must fail to compile (exhaustiveness), not silently produce a wrong tensor.
- Confirm `Scan.lean`'s causality-loop dispatch change is behavior-preserving for `.assign`-kind
  `BlockStep`s: re-run every existing `ScanTest.lean` causality fixture (look-ahead-bias rejection,
  deep-history accept) unedited; all must stay green.

### Gate

```bash
cd leanncd
lake build Eval.Plan.BlockTest Eval.Plan.ScanTest Eval.Plan.ScanCompileTest
lake build Tests
lake build LeanNCD
```

**Two independent reviewers** — new arms on a soundness-relevant closed sum every scan depends on,
per this repo's own standing rule; mirrors Thread 4's own Task 2 precedent exactly.

## Task 2: shared chaining helper

### Outcome

`chainNonlinStep`/`NonlinChainedStep` exist in `Compile.lean`; `prepareEvalPlan`'s `.plain` branch
is refactored to call it instead of its own inline two-branch logic. `.identity` statements compile
byte-for-byte as before.

### Files

- `LeanNCD/Eval/Plan/Compile.lean` (`NonlinChainedStep`, `chainNonlinStep`; `prepareEvalPlan`'s
  `.plain` branch)

### Implementation

1. Add `NonlinChainedStep`/`chainNonlinStep` exactly as verified in §3.3, placed near
   `resolveNonlinAxis`.
2. Refactor `prepareEvalPlan`'s `.plain` branch: after computing `retainedUids`/`outputShape`/
   `axisPos?` exactly as today, allocate `destSlot`/`publishedSlot` exactly as today (the branch's
   existing per-`Nonlin`-kind slot allocation is UNCHANGED — only the STEP CONSTRUCTION collapses
   into one `match chainNonlinStep rhs.nonlin (axisPos?.map (retainedAxisPos slots)) assignPlan
   outputShape destSlot publishedSlot with | .assignOnly a => stepsAcc.push (.assign a) | .
   assignThenPointwise a p => stepsAcc.push (.assign a) |>.push (.pointwise p) | .assignThenAxiswise a
   x => stepsAcc.push (.assign a) |>.push (.axiswise x)` in place of the three separate `match
   rhs.nonlin with` branches that build `PlanStep`s directly today).

### Fixtures

- **Parity** (`NonlinCompileTest.lean`): re-run `identityIsolatedPrepared` (already-existing,
  unedited) and confirm the resulting `PreparedPlan`'s step count/slot numbering is IDENTICAL to
  before the refactor — this is the regression-sensitive branch.
- **Pointwise/axiswise unchanged**: re-run `reluProgPrepared`/`softmaxProgPrepared` (already-existing,
  unedited) and confirm `steps.size == 3` still holds (Thread 4's own pinned count).

### Mutation checks

- Temporarily make `chainNonlinStep`'s `.identity` branch allocate an unused second slot anyway;
  confirm `tensorSigs.size`/slot numbering changes versus the baseline and would therefore have been
  a silent regression — restore, confirm parity.

### Gate

```bash
cd leanncd
lake build Eval.Plan.NonlinCompileTest
lake build Tests
lake build LeanNCD
```

Independent task review.

## Task 3: `checkNonlin` merge + `checkScanLHSSlot` relaxation

### Outcome

`checkNonlin` (one function, replacing `checkNonlinTopLevel`/`checkNonlinScanBlock`) admits all three
`Nonlin` kinds at both call sites (`checkStmt`/`checkScanBlockStmt`). `checkScanLHSSlot` admits
`.freeNorm`. A scan-block statement carrying `.pointwise`/`.axiswise`/`.freeNorm` now passes
`capabilityPreflight` — it is NOT yet correctly compiled (Task 5), but preflight no longer stands in
its way.

### Files

- `LeanNCD/Eval/Plan/Compile.lean` (`checkNonlinTopLevel`/`checkNonlinScanBlock` → `checkNonlin`;
  `checkScanLHSSlot`)
- `test/Eval/Plan/CompileTest.lean` (invert two existing fixtures; add one new fixture)

### Implementation

1. Delete `checkNonlinTopLevel`/`checkNonlinScanBlock`; add one `checkNonlin (_stmtName : String) :
   Nonlin → Except CapabilityError Unit` with the body `.identity => pure () | .pointwise _ => pure
   () | .axiswise .. => pure ()` (Thread 4's own `checkNonlinTopLevel` body, verbatim). Update
   `checkStmt`'s and `checkScanBlockStmt`'s call sites to `checkNonlin nm rhs.nonlin`.
2. `checkScanLHSSlot`: change `.freeNorm a => throw (.unsupportedLhsSlot ...)` to `.freeNorm _ =>
   pure ()`.

### Fixtures (donors named)

- **Invert existing**: `CompileTest.lean`'s two `#guard errOf (capabilityPreflight { ... [.scan "s"
  [...] [] [.assign "Y" [.iterNext ...] {...; nonlin := .pointwise .relu / .axiswise .softmax
  none}] false] }) == some (.unsupportedNonlin ...)` blocks — change the assertion to `isOk`, same
  literal programs, unedited otherwise.
- **New**: clone the top-level `.freeNorm`-admitted fixture (`CompileTest.lean`, the "`.freeNorm` at
  top level (Thread 4): structurally ADMITTED now" block), wrap the same statement inside a `.scan`
  node (mirroring `ScanContractTest.lean`'s `freeNormBase` shape: `.assign "S" [.freeNorm j, .iterAt l
  0] {...; nonlin := .identity}` as a base statement) — confirm `capabilityPreflight` now accepts it.
  (This one fixture alone, with `.identity` nonlin, will still be REJECTED downstream by
  `resolveNonlinAxis` as `unmarkedReductionAxis` once Task 5 lands — that is correct and expected,
  exactly mirroring the top-level `spuriousMarkerPointwise` fixture's own intentional-narrowing shape;
  this task's own fixture only asserts the PREFLIGHT-level acceptance, not full compilation.)

### Mutation checks

- Revert `checkScanLHSSlot`'s relaxation; confirm the new `.freeNorm`-in-scan fixture starts failing
  at preflight again — restore, confirm it passes.

### Gate

```bash
cd leanncd
lake build Eval.Plan.CompileTest
lake build Tests
lake build LeanNCD
```

Independent task review.

## Task 4: `compileScan` Phase 1 split-pair recombination

### Outcome

`ScanCompileError.malformedNonlinSplit` exists; `recombineNonlinSplitPairsCore` exists and is wired
into `compileScan`'s Phase 1, replacing `baseParts`/`recurParts` with their recombined forms before
state/scratch classification runs. Not yet reachable end-to-end from a real program (Task 3's
preflight relaxation and Task 5's chaining wiring are both still needed) — unit-tested directly.

### Files

- `LeanNCD/Eval/Plan/Error.lean` (`ScanCompileError.malformedNonlinSplit`)
- `LeanNCD/Eval/Plan/Compile.lean` (`recombineNonlinSplitPairsCore`; Phase 1's `baseParts`/
  `recurParts` construction)
- `test/Eval/Plan/ScanCompileTest.lean` (new fixtures)

### Implementation

1. `Error.lean`: add `| malformedNonlinSplit (scan : String) (isBase : Bool) (stmtIndex : Nat) (name
   : String)` to `ScanCompileError`, alongside the "block dependency order" group.
2. `Compile.lean`: add `recombineNonlinSplitPairsCore` exactly as verified in §3.1. In `compileScan`'s
   Phase 1, replace `let baseParts ← liftCapability warnings (base.toArray.mapM (assignPartsOrFail
   "scan base"))` with the same line followed by `let baseParts ← match recombineNonlinSplitPairsCore
   scanName true 0 baseParts.toList with | .error e => throw (scanErr warnings e) | .ok r => pure
   r.toArray`; identically for `recurParts` with `isBase := false`.

### Fixtures (donors named)

- **Real recombination through the real pipeline** (`ScanCompileTest.lean`): construct a `ScanStmt.
  scan` whose recurrence statement carries `nonlin := .pointwise .relu` (donor shape:
  `ScanContractTest.lean`'s `nonlinRecur`), run it through `compileToScheduled` (which invokes the
  real `splitNonlins`/`splitScan`/`splitStmt`) to get genuinely pre-split `base`/`recur` lists, then
  call `recombineNonlinSplitPairsCore` directly on the destructured triples and assert the recombined
  triple's `name`/`slots`/`nonlin`/`body` match the ORIGINAL (pre-split) statement's own fields
  exactly — this is the same style of check already verified against real `splitStmt` output in this
  plan's own `check-snippet.sh` pass (§0/§3.1), now landed as a real, shipped test.
- **`malformedNonlinSplit`**: hand-build a triple list where a `%nl`-prefixed entry's successor's
  `readFactors` does not match (e.g. reads a different name) — confirm the exact rejection.

### Mutation checks

- Swap the successor triple's `readFactors` name in the malformed fixture to the CORRECT name;
  confirm the fixture starts round-tripping correctly (proving the check was actually load-bearing,
  not vacuously always-rejecting).

### Gate

```bash
cd leanncd
lake build Eval.Plan.ScanCompileTest
lake build Tests
lake build LeanNCD
```

Independent task review.

## Task 5: Phase 2/3/4 integration — `compileScan` fully admits scan-block nonlinearity

### Outcome

A real source program with a `.pointwise`/`.axiswise` statement inside a scan's base or step block
compiles through `prepareEvalPlan` into a correct `BlockStep` sequence and executes correctly,
including when the nonlinear statement is a persistent state's own result. A masked axiswise
statement inside a scan block is rejected with the same `NonlinCompileError.maskedAxiswiseNotSupported`
as at top level.

### Files

- `LeanNCD/Eval/Plan/Compile.lean` (`retainedAxisPos`, `allocateBlockSlots`; `compileScan`'s Phase
  3/4)
- `test/Eval/Plan/ScanCompileTest.lean` (new end-to-end fixtures)

### Implementation

1. Add `retainedAxisPos` (§3.2) and `allocateBlockSlots` (§3.6) to `Compile.lean`, near
   `resolveNonlinAxis`/`chainNonlinStep`.
2. Apply the §0 `.freeNorm`-inventory fixes: base-block and step-block `outputUids` construction
   admit `.freeNorm a` alongside `.free a`; base and step write-map construction treat `.freeNorm _`
   identically to `.free _` (contributes an identity row at the next free position, rather than
   falling into the `unreachable` throw arm); the scratch (non-state) recurrence classification's
   context-axis check (`contextAxisAsFreeOutput`) admits `.freeNorm a` alongside `.free a`. Update
   both "unreachable"-comments at the write-map sites to reflect that `.freeNorm` is now a real,
   admitted case there, not an unreachable one.
3. Rewrite Phase 3 (base block): rename `baseAssigns : Array AssignPlan` to `baseSteps : Array
   BlockStep`; per statement, resolve `axisPos? ← liftNonlin warnings (resolveNonlinAxis nm rhs.nonlin
   slots)`; allocate via `allocateBlockSlots baseInputCount baseSteps.size rhs.nonlin`; build the
   `AssignPlan` targeting `internalSlot` (unchanged `residualizeAssignment` call, `destSlot` argument
   now `internalSlot`); call `chainNonlinStep rhs.nonlin (axisPos?.map (retainedAxisPos slots))
   assignPlan outputShape internalSlot publishedSlot`; push the resulting one or two `BlockStep`(s);
   push the matching `TensorSignature`(s) onto `baseSigs`; record `publishedSlot` (never
   `internalSlot`) in the base write's `StateWriteMap.outputSlot` and in the base block's own
   `outputs` accumulator (now built incrementally, not via `Array.range baseParts.size`).
4. Rewrite Phase 4 (step block) identically, renaming `stepAssigns` to `stepSteps`, with
   `resultSlotOf`/`scratchSlotOf` recording `publishedSlot`.
5. `RawScanPlan`'s `baseBlock`/`stepBlock` literal construction (Phase 6, assembly) uses `steps :=
   baseSteps`/`steps := stepSteps` (matching Task 1's rename) and `outputs := <the incrementally-built
   published-slot array>` (base) / `stepOutputs` (step, already incrementally built for the
   per-state write loop — Phase 4's OWN state-result loop, which iterates `stateNames` not
   statements, is UNCHANGED by this task, since a state's result slot is looked up via
   `resultSlotOf.getD`, which already resolves to the published slot once step 4 above records it
   there).

### Fixtures (donors named)

- **Positional correctness** (§12 of the design doc, `ScanCompileTest.lean`): an axiswise state
  result with an iteration slot BEFORE the marked local axis (donor shape: the design doc's own
  worked example, `G[l + 1, j.] := softmax(...)`, already verified against `retainedAxisPos` in §3.2);
  a multi-axis scan with the marker in the middle of several local axes; the marker last.
- **Publication correctness**: a nonlinear SCRATCH statement (donor: `NonlinCompileTest.lean`'s
  `reluProg` pattern, adapted into a scan recurrence) consumed by a LATER scratch statement in the
  same block; a nonlinear STATE result (donor: `ScanGen.lean`'s `template2` shape, `.pointwise .relu`
  on a state); a coupled scan with one nonlinear and one linear state (donor: `ScanGen.lean`'s
  `template3` coupled-state shape, one state's recurrence given `nonlin := .pointwise .relu`);
  explicit assertion that the committed state tensor is the RESULT (post-nonlin), never the
  preactivation (compare against a hand-computed expected tensor that WOULD differ if the
  preactivation leaked through).
- **Base-block correctness**: a nonlinear base state (donor: `ScanCompileTest.lean`'s "I-J" base
  fixture shape, `outputShape #[3]`, with `nonlin := .pointwise .relu` added); a pinned override plus
  a free-face base write, one of the two nonlinear.
- **Negative**: masked axiswise in base and step (donor: `NonlinCompileTest.lean`'s `sampleMask`),
  confirm `maskedAxiswiseNotSupported`; a `.freeNorm` marker on a `.pointwise` scan-block statement
  (donor: Task 3's own new preflight-only fixture, now run all the way through — confirm
  `unmarkedReductionAxis`).
- **The internal/published-slot mutation** (§3.6's own safety-net dependency): hand-build a
  `StateWriteMap` whose `outputSlot` is deliberately set to the internal (pre-nonlin) slot rather than
  the published one; confirm `checkScanPlan` rejects it via `writeSourceNotBlockOutput`.

### Mutation checks

- Swap `chainNonlinStep`'s call inside Phase 3/4 to always take the `.identity` branch (ignoring the
  real `nonlin`); confirm every axiswise/pointwise-in-scan fixture starts producing the WRONG
  (preactivation) tensor rather than failing to compile — restore, confirm correctness returns. This
  is the direct test of §3's publication law actually holding, not merely being stated.
- Revert the `retainedAxisPos` remap (use the raw `resolveNonlinAxis` position directly); confirm the
  "iteration slot before the marker" fixture now produces a wrong/out-of-range `axisPos` — restore.

### Gate

```bash
cd leanncd
lake build Eval.Plan.ScanCompileTest
lake build Tests   # the FULL Eval.Plan.* suite — this task edits compileScan, the one production
  # scan-specializer every scan fixture depends on, mirroring Thread 4's own Task 3 precedent
lake build LeanNCD
```

**Two independent reviewers**, no fixture-count discount — architectural centerpiece, per the task
brief's own instruction.

## Task 6: differential/corpus re-verification and closure

### Outcome

New end-to-end differential fixtures prove the compiled Dense path agrees with `evalScheduled` for
real nonlin-in-scan programs. `scanCorpusSplit` is re-pinned to its predicted, verified new value.
Discoverability is updated. A completion record states exactly what shipped, verified against real
code/output, and flags the `route`/`repStmt` bug for the next reader.

### Files

- `test/Eval/Plan/DifferentialTest.lean` (new fixtures; re-pinned `scanCorpusSplit` guard)
- `papers/jax_evalplan_architecture.md` (thread 4's row)
- `LeanNCD/Eval/AGENTS.md` (`Plan/` file-table rows for `Nonlin.lean`/`RawStep.lean`/`Block.lean`/
  `Scan.lean`/`EvalPlan.lean`/`Compile.lean`/`Error.lean`; the "Understand why a source scan was
  rejected" and "Check that a compiled scan still MATCHES the legacy evaluator" entry-point rows)
- A completion record, appended to this plan's own closing section (matching the convention Thread
  4's own plan and `2026-08-13-thread-5-jax-executable-kernels.md` both used)

### Implementation

1. Add end-to-end differential fixtures for the scan-block nonlin cases Task 5 introduced (reusing
   Task 5's own donor programs/tensors verbatim, comparing `prepareEvalPlan` + `runPreparedDense`
   against `evalScheduled` bit-for-bit via `envEq`, exactly as `DifferentialTest.lean`'s existing
   `checkScanCase`/`scanParityCheck` machinery already does for every other accepted case — no new
   comparison machinery needed).
2. Re-run `scanCorpusSplit` for real and update the pinned guard from `total == 17 && accepted == 9 &&
   nonlin == 4 && agg == 4` to the observed values. **If the observed values do not match this plan's
   own predicted `13/0/4` split** (§0), that is a genuine Task 1-5 defect to report and fix, per this
   file's own established stop-condition precedent — do not silently accept a different number
   without understanding why `template2` did not fully admit.
3. `papers/jax_evalplan_architecture.md`: correct thread 4's row — replace "scan-block nonlinearity
   stays rejected (deliberate scope boundary, Section 2.2 above)" with a statement that scan-block
   nonlinearity (base and step blocks alike, including a persistent state as the direct output of a
   nonlinearity) is now ALSO admitted, Dense-only, via the same `PlanStep`/`BlockStep` reference
   semantics; masked axiswise stays deferred uniformly at both levels. Frame this as an EXTENSION of
   thread 4's own row, not a new thread.
4. `LeanNCD/Eval/AGENTS.md`: update `Nonlin.lean`'s row to note it is now also reused, unchanged, by
   the block-level checker; `RawStep.lean`'s row to mention `BlockStep`; `Block.lean`'s row to mention
   the generalized `checkStepGraph`/3-arm `CheckedBlockStepEvidence`; `Scan.lean`'s row (causality
   loop dispatch) if its current text names `assignments`; `EvalPlan.lean`'s row if it names
   `checkPlan`'s own loop shape in a way this plan's refactor makes stale; `Compile.lean`'s row to
   mention scan-block nonlin compilation. Update the "Understand why a source scan was rejected"
   entry-point row's `.nonlin` clause to state it now applies inside scan blocks too (reused
   verbatim), and mention `.scan (.malformedNonlinSplit ...)` as a new, expected-never-to-fire
   internal-consistency check. Update "Check that a compiled scan still MATCHES the legacy evaluator"
   row's stated corpus numbers to the new re-pinned split. The "Find It Fast" `Plan/` row's file count
   stays 17 (no new file).
5. Write the completion record: what shipped (recombination, the wiring-loop generalization,
   `BlockStep`, the chaining helper, the retained-axis remap, the `.freeNorm` inventory fixes, Phase
   3/4's integration); what stays deliberately out of scope and why (§2.2, verbatim); the real
   `scanCorpusSplit` numbers observed (not assumed); a prominent mention of the `route`/`repStmt`
   mislabeling bug (§0/design doc §1) for the next reader, without fixing it.
6. **Verify every claim in the completion record against real code/output before writing it** — per
   the skill's own rule 1. In particular: do not write the corpus-split numbers without pasting real
   `lake build` output; do not write "no second local-operation representation was added" without
   re-confirming `BlockStep`'s own structure against `Kernel.lean`'s `AssignPlan`.

### Gate

```bash
cd leanncd
lake build Eval.Plan.DifferentialTest
grep -n "scan-block nonlinearity stays rejected" ../papers/jax_evalplan_architecture.md  # must return nothing
lake build LeanNCD
lake build   # full suite
```

**Two independent whole-branch reviewers**, per this repo's own standing lesson (skill §4: the
whole-branch tier is where every prior slice's most valuable finding came from) — do not compress
this because Tasks 1-5 land clean.

## 6. Definition of done

- [ ] Precondition confirmed: `2026-08-21-wiring-loop-generalization.md` has already landed on
      `main` — `checkStepGraph`/`WiringNode` exist in `Block.lean` and `checkPlan`/`checkPlanBlock`
      already delegate to them, before this plan's own Task 1 begins.
- [ ] `RawPlanBlock.steps : Array BlockStep`; `CheckedBlockStepEvidence` exists; `checkPlanBlock`/
      `runDenseBlock` handle all 3 arms; `BlockError.nonlin` exists; `Scan.lean`'s causality loop
      dispatches on `BlockStep`, skipping `.pointwise`/`.axiswise` with the stated justification.
- [ ] `chainNonlinStep`/`NonlinChainedStep` exist; `prepareEvalPlan`'s `.plain` branch uses it;
      `.identity` statements compile byte-for-byte unchanged (parity fixture green).
- [ ] `checkNonlin` (merged) admits `.pointwise`/`.axiswise` at BOTH `checkStmt` and
      `checkScanBlockStmt`; `checkScanLHSSlot` admits `.freeNorm`; `ScanContractTest.lean` untouched.
- [ ] `ScanCompileError.malformedNonlinSplit` exists; `recombineNonlinSplitPairsCore` correctly
      round-trips a real `splitStmt`-produced pair back to the original statement's own
      `name`/`slots`/`nonlin`/`body`, verified against the real pipeline (not just a hand-simulated
      shape).
- [ ] `retainedAxisPos`/`allocateBlockSlots` exist; the `.freeNorm` inventory fixes (outputUids ×2,
      write-map ×2, scratch-context-check ×1) are applied with their "unreachable" comments updated;
      Phase 3/4 produce `BlockStep` sequences and record only PUBLISHED slots in `StateWriteMap.
      outputSlot`/block `outputs` — pinned by the internal/published-slot mutation fixture.
- [ ] A masked axiswise statement inside a scan block is rejected identically to the top-level case
      (`maskedAxiswiseNotSupported`).
- [ ] Full positional/publication/base-block/negative test matrix (§12-style, Task 5) passes.
- [ ] `scanCorpusSplit` re-pinned to its REAL observed value, confirmed matching the predicted
      `13/0/4` split (or investigated and explained if not).
- [ ] `papers/jax_evalplan_architecture.md`'s thread 4 row and `LeanNCD/Eval/AGENTS.md`'s Plan/-table
      rows and entry-point rows are updated; no line numbers appear in any of it.
- [ ] The `route`/`repStmt` mislabeling bug is flagged in the completion record for discoverability.
- [ ] `lake build` (full suite) green.
- [ ] Two independent reviewers signed off on Tasks 1 and 5, and two independent reviewers signed
      off on the final whole-branch review (Task 6).

## 7. Risks and stop conditions

### 7.1 Expected high-effort areas

- Task 5's Phase 3/4 rewrite touches `compileScan`, the one production scan-specializer every scan
  fixture depends on — its gate re-runs the FULL `Eval.Plan.*` suite, not just its own new fixtures.
- Task 1's closed-sum extension (`BlockStep`) is exactly the shape of defect Wave F's own review found
  expensive to catch late (a diff showing only added/refactored code cannot show whether an existing
  arm's behavior silently changed) — hence two independent reviewers. The wiring-loop refactor itself
  carries this same risk shape; it is reviewed on that basis in `2026-08-21-wiring-loop-
  generalization.md`, not here.

### 7.2 Stop rather than broaden scope

- If Task 5 reveals that the `.freeNorm` inventory (§0) has a site beyond the five already found —
  stop and report; do not silently widen `compileScan`'s edits to cover it without re-scoping.
- If Task 6's `scanCorpusSplit` re-run disagrees with the predicted `13/0/4` split — this is a genuine
  Task 1-5 defect (per this file's own stop-condition precedent), not a number to accept without
  understanding why.
- Do not attempt to lift the masked-axiswise-in-scan restriction mid-implementation even if it looks
  small once `resolveNonlinAxis` is wired into scan blocks — it requires new UID-free predicate IR
  design with no precedent in this codebase, entirely outside this plan's sizing.
- Do not attempt to fix the `route`/`repStmt` mislabeling bug — flag it, per the design doc's own
  explicit instruction; fixing it belongs to whoever next touches the Br/categorical lowering
  subsystem, with its own review.

## 8. Plan-authoring verification record

- Every Lean declaration this plan ships was compiled via `check-snippet.sh` against the real repo
  this session, four scratch files, all green in their final form: the split-pair recombination
  (against the REAL `splitStmt`, run for real, not simulated — confirmed the `.freeNorm`-degrade fix
  is already landed and confirmed the recombined triple exactly reconstructs the original statement);
  the retained-axis remap (six cases, including the design doc's own worked example); the shared
  chaining helper (three cases against the real `AssignPlan`/`RawPointwisePlan`/`RawAxiswisePlan`);
  and the running slot-accounting scheme for Phase 3/4, confirmed order-general via both a forward and
  a reversed statement sequence. The generalized wiring loop (`WiringNode`/`checkStepGraph`) was
  verified separately, as part of `2026-08-21-wiring-loop-generalization.md`'s own authoring session —
  not re-verified here, since this plan only adds new cases atop it.
- Every prose claim of the "X reuses Y"/"no second Z"/"both are reachable from W" shape was checked
  against real code before being written: `checkPlan`'s and `checkPlanBlock`'s exact three-way
  difference (context obligation, error wrapper, the block-only `outputs` check) confirmed by reading
  both functions side by side; the import chain making `CheckedBlockStepEvidence`'s home in
  `Block.lean` (rather than needing to move downstream like `CheckedPlanStepEvidence` did) confirmed
  by tracing `Block.lean → Dense.lean → Check.lean → Graph.lean → RawStep.lean → Nonlin.lean`
  directly; the causality-loop exemption for `.pointwise`/`.axiswise` `BlockStep`s confirmed by
  re-deriving the chaining helper's own slot-allocation scheme (captures always precede internal/
  published slots); `ScanUnroll.lean`/`ScanOracle.lean` needing zero changes confirmed by reading
  both files' own scope notes directly, not inferred from the design doc's Option-B framing alone;
  `ScanContractTest.lean` needing zero changes confirmed by reading its own fixtures and comparing
  against `CompileTest.lean`'s already-stated "frozen classifier" precedent for the analogous
  top-level case; and the `scanCorpusSplit` prediction (`13/0/4`) confirmed by directly reading
  `ScanGen.lean`'s `template2` definition, not assumed from the design doc's own text (which does not
  make this specific numeric prediction at all — it is this plan's own finding).
- Every file path this plan names was verified with `ls`/`grep`/direct reading this session,
  including the exact `.assignments`/`RawPlanBlock` usage sites across the whole repo (production:
  `RawStep.lean`, `Block.lean`, `Scan.lean`, `Compile.lean`; tests: `BlockTest.lean`, `ScanTest.lean`,
  `ScanCompileTest.lean`) and confirming all three affected test modules are already present in
  `lakefile.toml`'s `Tests` `globs` list (no new `globs` entry needed, since this plan adds no new
  test file).
- No `File.lean:NNN` line numbers appear in any task's Implementation/Files/Gate text above, or in
  the completion-record instructions Task 6 is handed — every locator is by function/constructor
  name.
- The design doc's own citations were spot-checked against current `main` rather than trusted, per
  the task brief's own instruction; no drift was found between the design doc's claims and the real
  code EXCEPT one addition beyond its explicit scope: the causality-loop dispatch finding (§0) and
  the `scanCorpusSplit` numeric prediction, both genuinely new findings from this session, not
  present in the design doc's own text, folded into Tasks 1 and 6 respectively above.

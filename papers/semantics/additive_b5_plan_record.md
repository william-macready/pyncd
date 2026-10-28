# B5 plan authoring and verification record

## Final controller package check

The controller independently reran ordered patch replay to final tree
`45b78959139948adea38bb9e557858574be263e1`: four patches, 23 files.
Unfiltered stock manifest checks passed all 8 pre and 16 post entries.
All 24 unique entries carry observed failure expectations. The live plan is
514 lines; local document links and whitespace checks passed. Public
`leanncd/` source remains unchanged; no commits, merges or pushes were made.
The task-owned prototype and replay worktrees were removed after every changed
file matched the final snapshot hashes and the changed-path inventories contained
only files preserved in the verified patches. The standalone plan package and
session verification logs remain available.

Pre-close SDK accounting measured **33.46M cumulative input tokens for plan
authoring**, using the exact user-message boundary rather than subtracting an
approximate design-note cost. This exceeds the 12-20M estimate but remains below
the 50M authoring target. The long-running controller peaked at **276,033**
input tokens, exceeding the approximately 250k context target; that breach is
explicitly recorded. Fresh specialist contexts remained below their 60-call
and 250k limits. These are measured checkpoints, not predictions of later
execution cost; final administrative calls add a small further amount.

## Final status and authority

2026-10-27: **execution-ready plan package; implementation NOT authorized or
executed.** Owner approval covers the three recommendations in
`additive_b5_design.md` and authoring this plan. No commits, merges or pushes.
No implementation source was applied to the public planning checkout.
All required semantic/fixture authoring gates below are closed with observed
evidence; future execution builds, mutation reruns and whole-branch reviews are
instructions, not falsely recorded as already completed.

Base: `d62c885707fe10e0679d85b8cdbcf8d7d6e1e9a9`.
Final23-file implementation snapshot:
`45b78959139948adea38bb9e557858574be263e1`.
Final T3 patch SHA-256:
`a3b596f7cc3f477ed2859e639b92503be9bceb84c543831842370813eec1025d`.
T1/T2a/T2b patch hashes remain those in the plan.

## Immutable evidence and mechanical fidelity

Evidence directory:
`/Users/williammacready/.copilot/session-state/8e34eaec-8c9e-43b5-acb1-a477132523c1/files/b5-authoring/`.
Facts: `controller_facts.md`, `native_facts.md`, `oracle_facts.md`,
`boundary_facts.md`, `closure_facts.md`, `rank_facts.md`.
FINAL sections supersede early failed/in-progress notes.
Original logs remain in the session directory, not copied into the repository.

| Input increment, in order | Bytes | SHA-256 |
|---|---:|---|
| native_prototype.patch | 35619 | `5976cb28247cd24e6cee08995595f805c992361802bacd3a6d84fd1dcaad33e4` |
| oracle_prototype.patch | 36896 | `e6db2c45db4d77f401af267e1000cb7e417cce66f3b3fd1aee13c234efa206e1` |
| boundary_prototype.patch | 3636 | `8d53b92cc83386d30c24c824123ff2cea0a807b5e47224b5b28e849dd041a513` |
| closure_prototype.patch | 7993 | `df3b12cd431972f1098f0e5f8d2940508e5b8eb1cb7cd4c0ff06371cdcaa142d` |
| rank_prototype.patch | 1017 | `ab528315b7487f3dfdb9e6e57c605cb752ad8f723190cdcfd469252e57784075` |

`additive_b5_patches/assemble.py` starts from the base in a dedicated Git index,
applies the first3 inputs, adds B5BoundaryTest registration, then applies closure
and rank. This order matters: closure requires exact pre-closure tree
`db0880d6372e21e4e4931dea11512e58d1591e95`, including boundary registration.
Rank is incremental after closure; neither immutable patch was rewritten.
The intermediate closure-only tree was
`c78d0ff9917b4fa2923ed875993a2b2a1b7f0758`.

The generator assigns both new native modules, lake registration and the JAX
fixture file to T3, not production T2a. It mechanically emits4 ordered patches
and `snapshots.json`: input hashes, stage trees, exact paths, final file hashes.
Dedicated index/lock cleanup is automatic; ordinary public index/source untouched.
Forward `git apply --cached --whitespace=error --check`, ordered application,
exact tree equality and final file hashes pass. No unverified Lean fences were
authored. The verified Lean exists in detached checkouts and patch assets only.

Final generation command (one plain command):

```text
python3 /Users/williammacready/code/python/pyncd.worktrees/b5-multi-writer-scatter-design-note/papers/semantics/additive_b5_patches/assemble.py --generate /Users/williammacready/.copilot/session-state/8e34eaec-8c9e-43b5-acb1-a477132523c1/files/b5-authoring /Users/williammacready/.copilot/session-state/8e34eaec-8c9e-43b5-acb1-a477132523c1/files/b5-authoring/closure_prototype.patch /Users/williammacready/.copilot/session-state/8e34eaec-8c9e-43b5-acb1-a477132523c1/files/b5-authoring/rank_prototype.patch
```

## Actual build schedule and intermediate failures

All builds used `bash <checkout>/leanncd/scripts/lake-build.sh
<checkout>/leanncd <targets>`. No raw Lake invocation by this drafter.
Existing warnings are not new or claimed absent; no admissions were added.

| State / target | Actual result | Evidence owner |
|---|---|---|
| unchanged public base, Tests JaxExperiment | GREEN8836 jobs | controller baseline |
| A1 native targeted + B5NativeTest | GREEN8621 jobs | native-final.log |
| A1 alone, Tests | FAILED only two unmigrated oracle targets | native-full-tests.log; not full green |
| A1+A2 targeted oracle targets | GREEN8568 jobs | oracle-targeted-final.log |
| A1+A2, Tests JaxExperiment | GREEN8838 jobs | oracle-full-final.log |
| boundary observation probe | GREEN8523 jobs | boundary-probe.log |
| exact db088 combined replay, including final9 boundary guards, Tests JaxExperiment | GREEN8839 jobs | drafter-owned replay |
| exact T2b registration/source gate, Tests JaxExperiment | GREEN8837 jobs | drafter-owned replay |
| exact T1 API-only source, Tests JaxExperiment | GREEN8836 jobs | drafter-owned replay |
| exact T2a after T1, LeanNCD CollectTest CollectEvalTest CollectPlanTest | GREEN8620 jobs | drafter-owned replay |
| closure-only combined replay, Tests JaxExperiment | GREEN8839 jobs | drafter-owned replay |
| rank-inclusive prototype, Tests JaxExperiment | GREEN8839 jobs | rank-full-green.log |
| exact final45b789 replay, Tests JaxExperiment | GREEN8839 jobs | drafter-owned replay, exit0 |

T2b verification temporarily used its exact lake blob, omitting both new native
module registrations while fixture files remained physically present but unused.
T1 verification reversed T3/T2b/T2a in the exclusively owned replay and compared
all23-package-path predecessors (22 paths before closure) to exact T1 objects.
After the full T1 build, T2a was applied and targeted-built, then T2b/T3 restored,
closure and rank applied. Final23 file hashes match the final snapshot exactly.
No additional stage worktree or branch was created.

The native-only full failure is deliberate coupling evidence: the language
activation and oracle migration are one T2 integration unit. T2a never claims
individual full green. Local fixture drafting syntax/import failures in A2/A3
were fixed before final pins and remain in session logs, not relabeled successes.
The final replay output contained no required-target failure or new admission.

## Mutation evidence, including initial survivor

**Final24 unique rows =17 native +4 oracle +2 closure +1 rank.**
Initial concrete inventory was21; final is3 more, and2 above the design's16–22
estimated range. The extra rows close measured unsized-source, JAX pre-emission
and isolated fallback-rank coverage gaps, without production/policy expansion.
M16-FIX replaces M16 and is NOT an extra row.

Initial stock native run: **16 PASS /1 SURVIVOR**. M16 survived because old
privacy guards used checked `run64`/`run32`, not reference `ref64`.
A3 added named `referenceScratchPrivate`, observed a real reference result,
reran the same privacy production mutant and killed it with the named semantic
failure. This is a repaired regression guard, not a native production fix.
The initial16/17 history is retained; it is never retroactively17/17.
A1's2 instrumented cycles are provisional, not extra final evidence; its earlier
semantically-equivalent neutral mutant survived and is not counted as a kill.

| Final rows | Actual distinguishing evidence | Standard cycle result |
|---|---|---|
| M01 | strict extent mismatch guards | mutated failure / restored green / byte-identical |
| M02–M04 | neutral rewrite, collector algebra, tropical scatter publication | same |
| M05–M07 | declaration requirement, distinct UIDs, assign-only fallback | same |
| M08–M10 | multi-axis refusal, normalized cancellation, dimension payload | same |
| M11–M15,M17 | B6, collisions, actual f32 order, identity, all writers, route | same |
| M16-FIX | named reference scratch privacy failure | same; closure-m16.log |
| O01–O04 | independent normalized geometry, stride extent, tropical entry, exact shape | same; semantic expects rerun4/4 PASS |
| C01 | typed unsized source, never default0 | same; closure-unsized-cycle.log |
| C02 | actual prepared B5 rejected by lowerPlan/generateForward before emission | same; closure-jax-cycle.log |
| R01 | undeclared fallback basis rank, isolated from declared-rank checks | same; rank-cycle.log |

The first oracle run had no expectation check; its later4/4 stock rerun checked
the copied semantic expectations and byte-identical restoration. Native16
expectations were copied from observed failing guard prefixes plus `Expression`;
the repaired M16 uses its named semantic expectation. No invented failure text.

Final manifest generation mechanically replaced old M16 with M16-FIX, appended
only C01/C02 from closure plus R01, and preserved all4 oracle rows. It asserted
24 unique labels AND24 unique `(file,old,new)` triples, nonempty observed expects,
and unique final old strings. Task ownership: oracle=T2b; all others=T3.
Base classification was by actual file existence/unique old-string match, not
fixture age or whether the containing file changed.

| Manifest | Rows | Unfiltered stock check actually observed |
|---|---:|---|
| additive_b5_mutations.json | 8 | base:8 selected/unique; final replay:8 selected/unique |
| additive_b5_mutations_post.json | 16 | final replay:16 selected/unique |

Pre labels: M03,M11,M12,M13,M14,M15,M16-FIX,C02.
The final native16 source expectations, oracle4, repaired M16 and3 new rows each
have actual standard mutation-cycle proof in the appropriate identical production
tree. Aggregate24-row manifest reruns after implementation are still mandatory;
they were not redundantly rerun as an authoring close-out and are not claimed here.
New closure predicate/inferred pins postdate some original native cycles: M02's
old log does not falsely claim to contain later predicate guard failures.

## Closed coverage adjudications and donors

The plan's final32 families include actual new native/oracle rows and clearly
identified inherited controls; all outstanding authoring questions are closed.

- **Reference privacy:** F15 now uses `ref64 interleave`, independently of checked
  run64/run32. Actual private-name membership is `some false`; named M16 rerun kills.
- **Inferred basis:** F30 `inferredBasis` clones interleave and unpins only k.
  Three native legs retain `[-5,-7,-2,-3]`; declarations still supply axis identity.
- **Unsized source/basis:** `constantWriters` removes A/B reads and produces
  `[2,0,2,0]`. Unpin i→`unsizedSource` refuses the actual affine source slot;
  additionally unpin k→`unsizedBasis` refuses the free basis slot. All3 legs
  expose existing `unsizedScatterOutput`, not a default extent. C01 isolates it.
- **Native bool-to-tropical neutral copy:** F31 predicate B `[1,0]` beside max
  A `[-5,-2]` gives `[0,-inf,-2,-inf]`; min positive A `[5,2]` gives
  `[0,+inf,2,+inf]`. All3 actual legs compare bits. Signature builder preserves
  bool dtype. No Source-bool oracle or new cast policy is claimed.
- **Rank:** closure's declared `rankMismatch` donor observes S1→2 but does not
  isolate the new B5 check. F32 `fallbackRankMismatch` instead clones undeclared
  mixed, doubles ONLY affine writer slots, keeps rank1 bare fallback, and observes
  `rankMismatch "S" 1 2` through `sourceError`. Removing only
  `checkWriterGroup`'s basis comparison kills its new named guard (R01).
  Existing `CompileTest.destinationRankSched` / `rankScanDestinationSched` remain
  declared/scan rank siblings, not substitutes for this isolated proof.
- **JAX before Python:** F29 local `b5ScatterScheduled` prepares via public
  `prepareEvalPlan`, yielding `["scatter","scatter","assign"]`.
  `b5ScatterRejectedBeforeEmission` pins both lowerPlan and generateForward
  `.unsupportedStep 0`; C02 kills that exact named guard. No raw checked-plan
  fabrication, Python emission, kernel change or default Tests dependency.
- **B6 negative placement/source box/order:** inspected retained
  `ScatterCheckTest.boxCompute` has source `[3,2]`.
  `boxCheck #[1,0] (-1)` pins `scatterWriteOutOfRange 0 (-1) 1 2`;
  negative-coefficient `#[-1,0] 0` pins `(0,-2,0,0)`.
  Two-dimensional destination `[2,7]`, identity rows and bias `[-1,0]` is doubly
  invalid: dimension0 range and dimension1 extent. It pins
  `scatterDestExtentMismatch 1 7 2`; corrected `[2,2]` pins the range error.
  This specifically proves extent-before-range, not a new global priority rule.
  Empty `[0,2]` source with zero row/bias5 accepts where nonempty source refuses.
  Exact source corners are distinguished by existing `#[3,-1]` / `#[2,-1]` rows.
  `ScatterCompileTest.upsampleScatter` pins source3/dest6/coeff2/bias0;
  `zeroCoeffProg`/`zeroCoeffBiasProg`, `ScatterTest.b6Run` retain typed raw/reference
  payload and negative/stride/empty neighbours. B5 zeroPlanCause/S#1 remain intact.
- **Boundary payload:** final9 boundary guards compile in combined replay.
  lateMismatch distinguishes writer3 from1/2 and dimension1 from0; cancellation
  distinguishes normalized/raw axis count; explicit bare scatter is not fallback.
- **Stage honesty:** SOURCE counts222/195/88;216 scatter-bearing=117 multi-axis
  +99 shape5-only;81 of99 SOURCE admit then SHAPED sizeConflict,18 retain SOURCE
  refusals.9 hand SHAPED rows=5 accepts+4 shape refusals. markedSquare separately
  passes shape but later refuses `unmarkedReductionAxis "Y#1" 1`. Six mixed rows
  actually run four value legs; fG remains syntax failure/conditions0, fGStride
  actual parity/conditions0. No blanket full-preparation/value claim.

## Metadata, proof, ABI and discoverability

- DSL geometry classification has no Eval dependency; oracle normalization and
  stride extent logic are independent. Production observation may call preparation,
  prediction does not call production eligibility/extent/vote/shape helpers.
- `Eval/CollectorShape.lean` uses existing `LHSSlot.outExtent`; raw plan checks,
  dense workers, algebra tables and cast decisions are unchanged.
- New private-constructor CheckedScheduledProgram field retains source obligations;
  source env is rebuilt before collection. Metadata clones remain intact.
- New CompileError missing/repeated basis constructors; existing rankMismatch;
  typed ShapeError writerExtentMismatch uses public name,1-based writer,0-based
  dimension,expected,actual. Existing error wrappers/inference priority remain.
- Bridge.Agreement proof gained a real route match case; theorem statement
  unchanged, no admissions/bridge implementation.
- `explicitF64` invents declarations: undeclared fallback evidence is actual
  checked f32, not a falsely declared f64 program. Native B6 remains its existing
  node payload; reference S#1 spelling is not a new typed owner/writer API.
- Direct reference `evalScatter` already defensively rejects nonidentity nonlin;
  no new silently-ignored cell was assumed from evalPlain alone.
- Blanket Source multiWriterScatter allowance retired; separate single-writer
  extent condition unchanged. No Core/carrier/mixed evaluator changes.
- `scatterInScan` remains producerless compatibility API, not a new blanket guard.
- Hook sections measured: root0, DSL1787, Eval1597, Plan2078, Semantics0 chars;
  no trimming required. New module reachable through existing LeanNCD→Eval imports;
  execution T4 adds current AGENTS guidance and performs the literal value/count
  sweeps in the plan, without rewriting historical records as new history.

## Usage and process breaches

Initial design estimate82–130M total included12–20M authoring; skill authoring
target50M and execution ceiling~175M are distinct constraints.
Exact SDK checkpoint at the user-plan message boundary:
**29.736M authoring /32.616M all-session**. Authoring exceeded the12–20M estimate
by9.736M above its upper bound, but remains below50M at this checkpoint.
Prototype/mutation closure, isolated rank proof and exact intermediate replay
verification account for additional work; no capability scope was expanded.
Final parent accounting must add subsequent package/closure calls, not present
this checkpoint as a false final exact total.

| Agent scope | Calls | Input | Peak context |
|---|---:|---:|---:|
| controller, combined design+plan | 98 |17.792M |265,081 |
| A1 native |51 |4.075M |111,095 |
| A2 oracle |49 |3.884M |117,008 |
| fresh drafter, reported checkpoint |44 |3.684M |117,219 |
| A3 closure incl rank |42 |3.182M |105,668 |

**Controller peak265,081 exceeded the ~250k target.** Cause: long combined
design/plan context and mutation coordination; this is disclosed, not hidden by
the fresh drafter split. All specialist dispatches were below60 calls/250k at
the checkpoint. Drafter's45-call target was explicitly extended to55/hard60
for final closure/replay verification. Subsequent totals belong in parent close-out.
SDK inputTokens already includes cache tokens; don't add cache fields again.
token-report has no Claude transcript here, so SDK usage records are authoritative.

## Package validation and handoff

Ordered patch replay and source/file hashes pass; unfiltered8/16 manifests pass
against appropriate base/final checkouts; exact final full Tests JaxExperiment
is GREEN8839. No residual semantic authoring blocker, skipped guard or promised
unmeasured fixture remains. Source/build ownership was exclusive throughout
replay; no mutable prototype source was read while another agent owned it.
Manual docs/script whitespace, Python syntax, local links, plan≤800 lines and
unchanged public Lean source are checked at handoff. Patch source whitespace is
checked by Git apply, not by treating patch context spaces as plain added text.

The parent independently verifies package/scope, records final usage and cleans
owned prototype checkouts. Future implementation must still run every task,
actual24-row manifests, full builds and two whole-branch review lenses, then use
its separately authorized integration workflow. No outward push is authorized.

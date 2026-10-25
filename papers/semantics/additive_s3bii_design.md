# S3b-ii design note: tropical multi-writer collection (top level), plus the two folded decisions

Status: DESIGN, 2026-10-24, base main 04e2aef0 (S3b landed and pushed to local main; unpushed). Evidence: `additive_s3bii_audit.md` (read-only, nothing executed; every
"audit" claim below is code reading, unobserved until a task observes it). Predecessors: `additive_s3b_record.md` sections 9-10, `additive_production_decision_note.md` (A7 casts).

## 1. Intent

A tensor written by several statements that are all `maxreduce` (max-plus) or all `minreduce` (min-plus) is collected with max resp. min. Today only real-sum and predicate writer sets
are collected; any `.assign` writer with agg != sum throws `multiWriterAlgebra`. The user wants Bellman-style programs to be writable as separate statements:
`Vn[s] := maxreduce(Q[s,a])` plus `Vn[s] := Term[s]` (terminal value), and `D[v] := minreduce(W[u,v] * D0[u])` plus `D[v] := S[v]` (source init).

Honest value statement: the one-statement multi-term form (`maxreduce(Q[s,a] + Term[s])`) already runs today, at top level and inside scans (audit P5). S3b-ii buys ergonomics
and a uniform rule at top level, not new expressiveness.

## 2. Fixed decisions (user, 2026-10-24; do not reopen)

D1. `real -> bool` reads COERCE: truth = (stored != 0), the same rule as the bool -> tropical cast. Replaces identity pass-through. Meaning change for non-0/1 real values read by a predicate statement.
D2. An all-neutral scan state's annotation VOTES (rule in section 4). Flips the pinned `parkedAllNeutralScanState`.
D3. F2 stays option A: the max-plus<->min-plus and tropical->bool cast rejections stay; a one-copy bypass is documented, not closed.
D4. Scope: TOP-LEVEL multi-writer collection only. In-scan multi-writer (two writers of one state or scratch name inside a scan body) stays refused (`duplicateStateResult`, `duplicateScratchProducer`,
    `duplicateWriteForOutput`); it needs a separate scan-body desugar in both backends and is a later slice only on request (not audited in depth; estimate about as large as this whole slice).
D5. Copy writers abstain (the user chose "abstain" over "strict"); the exact rule is the author's call, section 4.

## 3. Goals, non-goals, anti-goals

Goals: all-max / all-min writer groups collect with max / min in the reference evaluator and the checked plan (f64, f32); the agreed sort is the tensor's sort for the cast checks (writers and readers);
D1 and D2 landed with their migrated expectations recorded old -> new; Bellman programs P1-P3 (audit section 7) pass as value fixtures on both backends.
Non-goals (each parked with an owner in the plan): in-scan collection, B5 (scatter writers), F3, the `real -> bool` REJECTION (superseded by D1), JAX/Python tropical, oracle per-tensor sorts.
Anti-goals: a multi-writer tropical name with no sort-map entry (silently disables cast checks for writers and readers: audit 2c); a silently changed expectation (every flip recorded with its reason);
a max/min writer group accepted whose writers disagree; a bool reader of a max-plus multi-writer tensor accepted.

## 4. The rule (one helper, two consumers)

Writer votes. For a set of writer statements of one name: every NON-neutral writer votes its `Stmt.algebra env` (`isSortNeutral`: one term, one bare read/unary factor, no contracted axis, identity nonlinearity).
Neutral writers ABSTAIN while any non-neutral writer exists (so `Vn[s] := Term[s]` and even `Vn[s] := minreduce(Term[s])` beside a `maxreduce(...)` writer give max-plus; the rewrite fixes a neutral copy's out-of-range pad AND changes how it reads a PREDICATE: the bool -> tropical
cast is selected by the statement's annotation, so `Vn[s] := Reach[s]` beside a max writer reads true/false as `0`/`-inf`, not `1`/`0`; pinned by `cpMax`/`cpMin` in `CollectPlanTest`, and the same holds for an all-neutral max scan state whose base copies a predicate, pinned in `DualityTest`). If NO writer is non-neutral, neutral writers vote by their non-sum annotations: all non-sum votes agree -> that sort; max vs min -> refusal;
only `sum` -> real. The agreed sort is the group's sort; every abstaining neutral writer is rewritten to it (`Stmt.withAgg`, the `scanStateStmts` mechanism) so its bare out-of-range read pads the group's 0_K.
Disagreement among voters: scan state -> `scanStateAlgebraMismatch` (unchanged); top-level group -> `multiWriterAlgebra name` (unchanged constructor). A predicate destination stays bool (agg must be sum: `predicateAgg` fires first).

Consumers: (a) `scanStateSorts`/`scanStateAlgebra` in `DSL/Ast.lean` (this is D2: today neutral writers never vote, so an all-neutral state is real; the helper makes the all-neutral case vote);
(b) the top-level writer group in `DSL/Pipeline/Collect.lean` (`checkWriterGroup`, `collectorStmt`) and `scheduleAlgebras`. This is the design's reuse point: one helper, both sites.
NOTE for the user: in the scan rule today a neutral writer beside a non-neutral one is ignored whatever its annotation (pinned: "neutral max base + min recurrence = min-plus"); the top-level rule above deliberately matches it.

## 5. Mechanism (audit section 1-2)

Collection stays a desugaring: writer k becomes `T#k`, one collector `T[...] := T#1[idx] + ... + T#n[idx]` is inserted after the last writer; today its agg is hard-coded `.sum`. Change: the collector takes the agreed agg
(`nonlin := .identity` unchanged: tropical writers already have identity nonlin, `tropicalNonlin` runs first). Both evaluators fold terms with `combineFor ... agg` / `reduceOp`, so the collector is max (min) of the private writers
with no backend change (audit, to be OBSERVED in T2). Unwritten cells cannot occur (writers need bare free slots on the same axes), so 0_K cells are neutral for the fold.
Sort map: `scheduleAlgebras` today skips names with 2+ writers and `checkSortCasts` skips destinations with no entry; after this slice a tropical group MUST get its agreed entry in the same change
(use `Stmt.algebra env`, so a predicate stays bool; no entry on disagreement, collection remains the refusal). Private `T#k` and the collector never pass `checkSortCasts` (collection runs later); `algebraOf T#k` is real by the clone declaration, fine since only the collector reads them.
D1 code sites (audit section 4): reference `boolReadCast` (needs the destination: for a `predicate` destination a real source coerces `v != 0 -> unit1 else unit0`), `Eval/Scatter.lean` call; plan `residualizeAssignment` (new destination-is-bool
parameter at the top-level, scan base and scan step call sites) plus a new `ReadPlan` flag beside `boolToTropical`, applied in `gatherFactorWith` via `ScalarKernelOps.isTrue`, admitted in `checkAssign` only for a bare read, bool algebra, non-bool source.
Raw-plan tests build `ReadPlan`s directly: the flag defaults to false so they stay unchanged.

## 6. Refusals that stay, and tests that flip (audit section 5)

STAY: mixed groups (max+min, sum+max, max+sum, min+sum, sum+min), scatter writers (`multiWriterScatter`), scan-node writers (`multiWriterScan`), nonlinear tropical writers (`tropicalNonlin`), shape mismatches (`writerShapeMismatch`).
VOTE-RULE CONSEQUENCES (observed, pinned in `CollectPlanTest`): a neutral `maxreduce`/`minreduce` copy beside a NON-neutral sum writer is ACCEPTED and runs as sum (its annotation is dropped and its pad is `0`; it used to be refused `multiWriterAlgebra`; `vrSumMax`/`vrSumMin`), so "sum+max STAY" means a NON-neutral max writer; a relu or Iverson-only copy beside a max writer is non-neutral and votes real, so it is refused `multiWriterAlgebra` (`vrRelu`/`vrIv`); D2 also newly refuses scan programs that read an all-neutral max scratch with a bool or min-plus statement, or have it read a min-plus tensor (`sortCastUnsupported`, pinned in `ScanCompileTest`).
FLIP: `CollectTest` C6 and `c6min` (admitted: assert `dests` and collector agg); `CollectEvalTest` J4 and `j4m` (values A=[[1,2],[3,4]], B=[[5,6],[7,8]] -> `[6,8]` / `[1,3]`, hand-derived, to be observed);
`CompileTest` (d) "multi-writer tropical set" -> `sortCastUnsupported "W" "N"`. KEEP C5, C6b, C6c, `c6bm`, `c6cm`, scan-writer and priority blocks; ADD max+min both orders. D1 flips: `DifferentialTest` "T4.3/7 boolean scalar non-binary" (0.75 -> 1.0) and its direct check, plus comment/pin updates
(`CompileTest` predicate reads real, `BoolCastTest` (c)). D2 flips: `DualityTest.parkedAllNeutralScanState` (`[[4,4],[0,0]]` -> `[[4,4],[-inf,-inf]]`), `ScanCompileTest` "S3bF/neutral scratch max/min" (`[3,4,4,4,0,0]` -> `[3,4,4,4,-inf,-inf]` / `+inf`; sum unchanged),
the test-side `localStateAgg` and `oracleNeutral` guards restated independently. Audit did not classify all 44 files that mention a predicate declaration: T3 starts by measuring which fixtures read a real tensor from a predicate with non-0/1 values.

## 7. Coverage and oracle

Production: value fixtures on reference, plan f64 and plan f32 (P1-P3, mixed-group refusals, bool and other-tropical READERS of a collected tensor -> `sortCastUnsupported`, predicate and scatter/scan-writer neighbours, a neutral-copy writer with an out-of-range read).
Oracle: the sorted S2b oracle collects by target and picks one carrier, so an all-max/all-min program should already be expressible with no oracle change; no existing sorted fixture has two writers of one tensor. T4 tries 2-3 four-leg fixtures; if the harness
mis-classifies, the honest fallback is production-only coverage (as S3b did for duality). Not decided in advance.

## 8. Process, size, risks

Process weight: Full-lite. Above Direct (new rule in a soundness surface, six or more patches) but authoring must stay cheap: S3b authoring cost 159M tokens vs a ~50M target, driven by hand mutation cycles inside prototype dispatches and one reviewer holding three lenses.
So: NO pre-built patch series. The plan lists tasks with exact acceptance checks; each task is one implementer dispatch (at most two work items, test-first, observed values, one hand mutation per item reported in the commit body), I run the full `Tests` build per task;
a small manifest is added only for the entries a task proves non-redundant. Two final reviews (one lens each: semantic fidelity; false rejections and weakened tests), then merge locally. Not pushed without a request.
Tasks (order is dependency order): T1 shared vote helper + D2; T2 collection change + sort-map entry + the C6/J4/CompileTest flips; T3 D1 coerce; T4 Bellman and neighbour fixtures (+ oracle attempt); T5 docs sweep. Estimated 5 core patches (T1 helper+D2 1-2, T2 1-2, T3 2) plus fixtures and docs.
Risks, in order: (1) the sort-map entry (must ship with collection, fixtures both directions); (2) the shared vote rule changes scan behaviour in two ways at once (D2 and any divergence from today's mixed-state rule): T1 must leave every mixed-state fixture unchanged;
(3) D1 touches both backends' read paths: a missed call site (top-level, scan base, scan step, scatter) silently keeps identity there (S3b T5's four-caller lesson: a hand mutation per caller). Unverified: `route`/`RouteFragments` on a multi-term tropical collector, the oracle on a two-writer program, `.recurMorphism` writers in `writerGroups`, docs rows that mention the refusal outside `papers/semantics`.

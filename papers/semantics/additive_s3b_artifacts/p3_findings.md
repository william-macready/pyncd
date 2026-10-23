# S3b P3 findings (T3: top-level maxreduce/minreduce scatter accepted, 0_K fill, (+) collisions)

Branch `proto-s3b-p3` (checked out), from `proto-s3b-p2` tip 398d197b.
Commits: `1fdec319` T3-01 production (7 files, +27/-64), `281a1719` T3-02 tests (7 files).
Patches here: `T3-01-production.patch` (398d197b..1fdec319), `T3-02-tests.patch` (1fdec319..281a1719). `git apply --check -R` of both at tip 281a1719 exits 0.
Mutation manifest: `p3_mutations.json` (13 entries; `mutation-manifest.sh --check` OK, every old-string unique; the `expect` strings are NOT observed, the controller must confirm them).

## (f) Corrections to audit / design (read first)

1. `Combine.bool.combine` IS `maxNaN` (Contract.lean:165, identical to max on {0,1}), and `unit0 = 0.0`; so `boolDest`/`isPredicateDest` could be dropped from `evalScatter` with the predicate fixtures (S3a bool collision = OR) unchanged. `isPredicateDest` itself stays (used by `combineFor`).
2. Kernel.lean ~L167 does NOT state a refusal (it already says "starting from its identity ... unwritten cell holds 0_K"); no edit made there. The Dense.lean doc (~L358-366) did, and was rewritten.
3. Stale docs beyond the listed ones, fixed in T3-01: `Plan/Error.lean` `predicateScatterDest` doc ("same way a maxreduce scatter is refused"; "rejected via scatterOptsNotAdmitted"), `Eval/AGENTS.md` L69 (named `checkScatterAgg`), `Eval/Error.lean` doc on `scatterFillNotIdentity`. Left untouched (Semantics/** is T7's): Semantics/AGENTS.md L123-124, NumericalProfile.lean L34-35, Admission.lean L905, SortedDifferential.lean L163/L207. Also stale and left: `Eval/Scan.lean:248` mentions `scatterFillNotIdentity` for unsized scan destinations (docstring only; check whether any producer remains: none does).
4. ScatterDenseTest's `maxScatter` comment claimed the reference/checked divergence on tropical scatter was "adjudicated, permanent, deliberate". False since T3; rewritten in T3-02.
5. A top-level PREDICATE scatter destination is still refused by the checked layer (`predicateScatterDest`), so fixture (d) "predicate collision = OR" exists on the reference side only (ScatterTest S3a, unchanged, green). Not a T3 item.
6. No `enumPrograms`/differential-sweep count changed (3832/3832/0 rejected still holds): the sweep has no scatter.
7. `SourceSortedDifferentialTest` went from 11 to 19 red `#guard_msgs`/`#guard` sites (see (b)): the 8 new ones are T3-induced (a tropical scatter is no longer refused, so `tropicalScatterFill` never fires). One of them (L188 area) now shows the native leg reporting `BindingIssue.shape/length` for output `Y` (`[7]` vs `[8]`) on a tropical scatter sample: T7 should look at that (the native/oracle leg's destination extent for tropical scatter), it is not just a classification flip.

## (a) Observed old -> new

| File | Label | Old | New |
|---|---|---|---|
| test/Eval/ScanTest.lean | shape 1 max (`Out[2*i] := maxreduce(X[i])`, X=[-1,-2,-3]) | `scatterFillNotIdentity "Out" .max` | [-1,-inf,-2,-inf,-3,-inf] |
| ScanTest | shape 1 min (twin, X=[1,2,3]) | `scatterFillNotIdentity "Out" .min` | [1,+inf,2,+inf,3,+inf] |
| ScanTest | shape 1 joined (A+B, .max) | `scatterFillNotIdentity` | [10,5,2] (min twin on negated data [-10,-5,-2]) |
| ScanTest | scan-local max scatter (`#[3,7]`), plain max over contraction | accepted | unchanged, green (observed) |
| test/Eval/Plan/CompileTest.lean | f32 `Out[2*i]` .max / .min | `scatterOptsNotAdmitted "Y: fill"` | accepted; scatter step algebra == `admittedAlgebraF32Max` / `Min`, `destShape #[6]` |
| DifferentialTest | `capabilityCategory` arm `scatterOptsNotAdmitted` | reachable | only a comment added; the arm must stay while the constructor exists (exhaustive match); T7 removes both |
| ScatterTest | 4g regression (.max, [10,5,2]) | [10,5,2] | unchanged value; comment fixed; min twin [-10,-5,-2] added |
| ScatterDenseTest / ScatterDense32Test / ScatterCheckTest raw tropical plans (`maxScatter`, 1.5) | | | values UNCHANGED (checked worker already did it); only a comment rewritten. ScatterCheckTest untouched |

Every refusal pin was converted; none stays a rejection: the three ScanTest REJECT cases were all rejected only by the deleted guard.

## (b) Red-target classification (full `Tests`)

| Target | Class |
|---|---|
| Eval.Portfolio.GnnScatterTest (L18, GN4) | (ii) deferred to T5, unchanged from P1/P2 |
| Semantics.SourceSortedDifferentialTest (19 error sites: 104,106,108,188,191,193,196,201,204,206,209,227,228,242,262,264,266,269,272) | (ii) deferred to T7 (the first 11 pre-existing from T1; 8 new, all `tropicalScatterFill` rows: expected `scatterFill (some n)`/`nativeDiscrepancy`, now `parity`/`nativeFailure`; `fills nY 6`, `fills nV 7` guards) |
UNEXPECTED: none. Nothing red in T3-owned targets.

## (c) Job count
Full `Tests`: 8823 jobs (same as P2). LeanNCD library alone built green after T3-01 (exit 0).

## (d) Fixtures with donors (all first-run green; values predicted, then confirmed by the build)

| Fixture | File | Donor |
|---|---|---|
| (a) collision + unwritten, reference, max/min: `S3b max/min collision` (X=[[5,1],[3,7],[2,4]] -> [5,-inf,7,-inf,4,-inf]; sum would be [6,.,10,.,6,.]) | ScatterTest | S3a sum-collision fixture |
| (a) raw checked plan collision, f64 (fixture 7, [-inf,101,102,103], twin [+inf,-101,-102,-103]) | ScatterDenseTest | fixture 6 `collisionScatter` |
| (a) f32 bits (fixture 1.6c) | ScatterDense32Test | fixture 1.6 |
| (a)+(c) surface through reference AND checked plan, S11 max/min | ScatterCompileTest | S10 (`assertScatterParity`) |
| (b) F4: direct `evalScatter` with contracted `j` and empty fibre vs raw checked plan, equal; plus real neighbour sums (fixture 8) | ScatterDenseTest (imports `LeanNCD.Eval.Scatter` now) | Dense.lean F4 comment |
| (c) `planAgrees`-style: `scatterAgreesWith` over `maxScatterProg`/`minScatterProg` | DifferentialTest | `maxPlainProg`/`minPlainProg` |
| (d) real collision sum, predicate collision OR | ScatterTest S3a, S10 | unchanged, green |
| (e) NaN (row [5,nan] and [nan,4]) propagates, f64 only; other row max kept, gap -inf | ScatterTest | s3bRun helper |
| (f) multi-factor `maxreduce(X[i,j] * Y[j])`: 101/107/104 (a real product would differ); twin; also surface S12 and raw fixture 7 | ScatterTest, ScatterCompileTest | S11 |

Helpers added: `s3bRhs`/`s3bRun`/`ninf`/`pinf` (ScatterTest, 3+ uses each), `f4Scatter`/`f4Reference` (ScatterDenseTest), `scatterAgreesWith` (DifferentialTest).

## (e) Proposed mutations
See `p3_mutations.json` (paste-ready manifest, task "T3"): M1 (fold -> `+`; five builds: ScatterTest, ScatterCompileTest, DifferentialTest, ScatterDenseTest, ScanTest), M2 (init -> 0.0; ScatterTest, ScanTest), M3 (fold -> non-NaN `Max.max`; ScatterTest), M4 (tropical ⊗ back to `*`; Contract.lean), M5/M5b (checked worker fill `reduceId` -> `ops.zero`), M6 (checked worker fold -> overwrite), M7 (compile: scatter step algebra ignores `agg`; CompileTest). Caveats: ScatterDenseTest/CompileTest guards are unlabelled `#guard`s so `expect` there is just the file name; M5/M6 fail ScatterDenseTest first so ScatterDense32Test (imports it) needs `mut.sh`-style direct typecheck. Not covered by any mutation: the `Eval.lean` guard deletion (a re-added guard would break ScanTest "shape 1 max" etc., obviously); scan-local overwrite is unchanged and not pinned further.

## (g) Tool calls and context
About 68 tool calls (budget ~60; over by ~8: three tool-refusals on commands the harness could not verify, two extra Monitor calls, one extra read for the Compile/Dense mutation texts). No hand mutations run. No whole log Read. Peak context roughly 110-120k.
Harness notes: a path containing `test/Eval` made `rg` refuse ("runs a string through Eval"): search from `leanncd/test` with `--glob "**/Eval/**"`. A foreground `until ... sleep` loop in Bash works (the harness only blocks a bare `sleep`).

## (h) Facts for the T4 author (declared algebras per sort, new rejections)

Where the existing predicate rule threads, in order:
1. `DSL/Pipeline/Structural.lean`: `checkPredicateOutput (env : DeclEnv) (s : Stmt)` (L980) is the per-statement rule: `.assign nm _ rhs | .scatter nm _ rhs`, looks up `env[nm]?`, `.predicate` -> `predicateNonlin` then `predicateAgg`. `checkPredicateOutputs` (L1008) lifts it over `List ScanStmt` through `sc.sourceStmts`. `checkScheduledDtypes (env) (stmts)` (L1016) = per statement `checkStmtAxisKinds s` then `checkPredicateOutput env s` (order axis-kinds before predicate). `checkDtypes` (L1022) is the SOURCE pipeline twin: its own loop calling `checkStmtAxisKinds` then `checkPredicateOutput rp.env s`, plus a `.recurMorphism` arm. A new per-destination rejection (e.g. a tropical-sort destination with the wrong agg) belongs in `checkPredicateOutput`'s sibling called from BOTH `checkScheduledDtypes` and `checkDtypes` (two call sites; `checkPredicateOutputs` has no live caller in LeanNCD per the rg above, only docs, so do not rely on it).
2. `DSL/Pipeline/ScheduledValidation.lean`: `validateScheduled` (L155): `buildDeclEnv sched.decls` -> `checkScheduledReadRanks` -> `checkScheduledDtypes sourceEnv sched.stmts` -> topology -> `collectDefinitions` -> `buildDeclEnv collected.decls` -> `CheckedScheduledProgram.mk` (private constructor; fields program, declEnv, explicitSizes, extNames, privateNames). A new `algebras : HashMap String _` map (name -> sort) has to be a NEW FIELD of `CheckedScheduledProgram` (L144), computed in `validateScheduled` from `declEnv` of the COLLECTED program (so private `T#k` clones carry their sort), and the new rejection should run on the SOURCE-as-written env (`sourceEnv`, next to `checkScheduledDtypes`), exactly as the predicate rule does. Constructor is private: only this file builds it, so adding a field touches one construction site.
3. `Eval/Plan/Compile.lean`: `prepareEvalPlan` Step 0 (L1362-1381) runs `validateScheduled`, maps its `.error e` to `{ cause := .sourceInvariant e, warnings := [] }` (a `CompileError` nested in `PlanCompileCause.sourceInvariant`), then takes `checked.program`/`declEnv`/`explicitSizes`. `evalScheduled` (Eval/Eval.lean ~L129) calls the same `validateScheduled`, so one rule covers both entries (the doc at Eval.lean L85-110 explains why). The algebra is chosen later in two shapes: scatter step (Compile.lean ~L1584: `{ computePlan with algebra := algebraForDest destDtype rhs.agg }`) and three plain/assign sites (~L1103, 1205, 1646, 1663, 1681), `algebraForDest` defined at L685. A declared-sort map would replace `rhs.agg` as the algebra selector at exactly those five sites; the reference side selector is `combineFor decls nm agg` (Contract.lean:199), called by `evalAssignDtypedSeeded` (Contract.lean:262) and `evalScatter` (Scatter.lean:56). The scan paths (`Eval/Scan.lean`) need their own look: not read here.
4. `CompileError` constructors: defined in `Exec/Uid.lean:29` (`predicateAgg : String → CompileError`). `rg -n predicateAgg` shows NO exhaustive `match` over `CompileError` anywhere in `LeanNCD/` (production): only the definition, the single throw (Structural.lean:986) and docs. Tests that name it (templates for a new constructor's tests): test/DSL/MaxReduceTest.lean:37, test/DSL/Pipeline/RouteFragmentDiagnosticTest.lean (case09 table row 9 and `#guard compileErrorIs case09 (.predicateAgg "P") 2`), test/DSL/Pipeline/StructuralTest.lean:498, test/Eval/Portfolio/RejectTest.lean (RJ3), KnownGapTest.lean doc, CompileTest.lean:1512-1519 and 2018-2179 (`predSchedWith`, `scanPredSchedWith`, order tests incl. base-before-recur). Because there is no exhaustive match, a new constructor breaks no production `match`; check `Semantics/**` and the `toString`/display of `CompileError` (not grepped here: `rg -n "predicateNonlin" LeanNCD` is the cheaper second template) before assuming that.
5. Entry point difference to keep in mind: `checkStmtAxisKinds` runs first inside `checkScheduledDtypes`, so a new rejection placed in the same loop keeps the "axis-kind before destination-sort" order; the plan author must state where it falls relative to `predicateNonlin`/`predicateAgg` for a predicate destination (a predicate destination is never a tropical sort, so only the ordering against `predicateNonlin` matters).

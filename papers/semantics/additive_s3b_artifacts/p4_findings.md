# P4 findings (T4: `SortAlgebra`, `algebraOf`, sort rejections)

Branch `proto-s3b-p4` (from proto-s3b-p3 281a1719). Commits: `041bfe0c` T4-01 production, `ccf9f745` T4-02 tests.
Patches (apply --check -R verified at the tip): `T4-01-production.patch` (281a1719..041bfe0c), `T4-02-tests.patch` (041bfe0c..ccf9f745).
Mutations: `p4_mutations.json` (15 entries, `--check` OK, expect strings empty, none run).

## (a) Corrections to audit / design (read first)

1. **The type cannot be called `Algebra`.** `LeanNCD.Algebra` is already a `class` (`LeanNCD/Algebra/Algebra.lean:11`, categorical algebra);
   `LeanNCD.lean` imports both, so the build fails at the aggregate root with "environment already contains
   'LeanNCD.Algebra.noConfusionType'" (the per-module builds of `DSL.Ast` are green, only `LeanNCD` fails). Shipped name: **`SortAlgebra`**
   (`real | bool | maxPlus | minPlus`, deriving DecidableEq, Repr, Lean.ToExpr, Inhabited; BEq comes from DecidableEq). Every later task
   (T5 casts, T6 scan init) must say `SortAlgebra`; `algebraOf`, `algebras`, `Stmt.algebra`, `AggOp.algebra`, `DeclEnv.declAlgebra` keep the planned names.
2. **Cast rule skips a destination with no map entry** (design §3 says "statement's sort"; a multi-writer name has no single sort). The cast
   check uses K = `algebras[dest]` and does nothing when absent. Without this, a multi-writer max-plus writer bare-reading a min-plus tensor would
   throw `sortCastUnsupported` instead of collection's `multiWriterAlgebra` (fixture (d) pins `multiWriterAlgebra "W"` for exactly that shape).
   Consequence: a predicate multi-writer name DOES have an entry (every `predicate` declaration is inserted first), so its writers are cast-checked as bool.
3. **Neutral writers are decided by shape only, not by `agg`.** A scan base `S[j,0] := maxreduce(X[j])` (one read, no contracted axis) is neutral even
   though annotated `max`; its annotation is meaningless and is ignored (fixture: neutral base `.max` + recurrence `.min` is ACCEPTED, state = min-plus).
   For the task's "base max / recur min reject" the base must CONTRACT an axis (`S[j,0] := maxreduce(XK[j,k])`). RC5/RC10 bases are neutral, so unaffected.
   A neutral statement of a top-level single-writer name is NOT neutral for the map: its entry is its own `agg` sort (neutrality only matters inside a scan state).
4. **Order swap `predicateNonlin` / `tropicalNonlin` is unobservable.** `Stmt.algebra` returns `bool` for a predicate destination, so the tropical
   rule never fires on a predicate statement, whichever order the two calls have. The swap mutation (T4-M7) is an EQUIVALENT mutant; the order is
   pinned instead by "predicate relu max still predicateNonlin" and, observably, T4-M7b (predicate-ness dropped from `Stmt.algebra`).
5. **No other place needed the new constructors.** `rg predicateNonlin` over the repo (excluding docs/papers): `Exec/Uid.lean` (definition), `Structural.lean`
   (throw), a doc line in `Eval/Eval.lean`, and tests. `CompileError` derives only `Repr, DecidableEq, BEq, Inhabited`: there is no `toString`/display,
   no `ToExpr`, no Bridge/AcsetCodec arm, no exhaustive `match`. Adding the three constructors in `Exec/Uid.lean` was the whole change; the `LeanNCD` library and
   `Semantics/**` built unchanged.
6. **Observed error precedence** (validateScheduled): `buildDeclEnv` -> `checkScheduledReadRanks` -> per-statement loop over the WHOLE schedule
   (axis kinds, then `checkPredicateOutput`, then `checkTropicalOutput`, source order, scan `base ++ recur`) -> `scheduleAlgebras` (scan-state mismatch, every
   scan node, source order) -> `checkSortCasts` (source order; within a statement, term then factor order) -> topology (`cyclicDataflow`) -> collection
   (`multiWriter*`). Pinned: tropicalNonlin on a later statement beats an earlier scan mismatch; tropicalNonlin on a later statement beats an earlier cast
   violation; scan mismatch beats an earlier cast violation. `checkDtypes` (source pipeline) has only the per-statement part: `axis kinds -> predicate -> tropicalNonlin`.
7. Per-statement `tropicalNonlin` also covers `.scatter` statements (`Stmt.algebra` has an arm for both) and axiswise nonlinearities (softmax pinned).
8. Design doc note ("`RouteFragments`/`physicalizeOne`/`splitNonlins` untouched") confirmed: no route-side file edited; LoweringTest AGG1/AGG2 and
   RouteFragmentCorpusTest `aggregate` are green in the full `Tests` build.

## (b) Pre-existing tests that flipped

None. The full `Tests` build shows exactly the two inherited red targets; no new red target and no changed message in them (GnnScatterTest still fails only GN4;
SourceSortedDifferentialTest still has 19 error sites). No existing fixture reads a tropical tensor into a predicate / other-tropical statement or puts a nonlinearity on a max/min statement.

## (c) Red targets (full `Tests`, 8823 jobs, one run)

- (ii) deferred, inherited: `Eval.Portfolio.GnnScatterTest` (GN4 -> T5), `Semantics.SourceSortedDifferentialTest` (19 sites -> T7).
- (i) T4-owned: none. (iii) UNEXPECTED: none.
- RC10 G[0,1] is not red yet (T6). Library `LeanNCD` green (8614 jobs).

## (d) Fixtures (all green on first run; accept neighbours and reject cases both predicted before the build)

CompileTest.lean (section "S3b T4", donor `predSchedWith`/`assertPredicateParity`/`scanPredSchedWith`/`assertScanPredicateParity`; both entries via parity helpers):
- tropicalNonlin: relu+max, relu+min, softmax+max (rejected via `evalScheduled` AND `prepareEvalPlan`); first-violation order; accept: relu+sum, max+identity; predicate relu+max stays `predicateNonlin`.
- scan agreement: base max/recur min and base real-sum/recur max reject (both entries); accept via `validateScheduled` + `algebraOf "S"` pin: neutral sum base + max recur (max-plus), neutral max base + min recur (min-plus), contracted max base + max recur, all-real; per-statement beats scan mismatch.
- casts: predicate reads max-plus / min-plus; max-plus reads min-plus; min-plus reads max-plus (reject, both entries); accept (both entries, executed): max-plus reads predicate+real+max-plus; real reads tropical and min-plus reads min-plus; `unaryFn` read of min-plus in a max-plus statement; predicate reads real. Precedence: scan agreement before casts; per-statement before casts.
- multi-writer: `W` written twice by max, reading min-plus `N` -> `multiWriterAlgebra "W"` (both entries).
- map pins (`algebraOf`/`algebras`): single-writer max, min, sum, written predicate, UNWRITTEN predicate (bool), unwritten input (real, no entry), two-writer name (no entry, `algebraOf` = real).
- surface: `tlprog!{ tensor f64 E(i,j); tensor f64 M(i); predicate Y(i); M[i] := maxreduce(E[i,j]); Y[i] := M[i] }` -> `TLProgram.eval` and `prepareEvalPlan` (after `compileToScheduled`) give `sortCastUnsupported "Y" "M"` (`compileToScheduled` itself accepts it: `validateScheduled` runs only at execution).
StructuralTest.lean (donor fixture 6, ~L486): `checkDtypes` rejects relu/softmax on `.max`/`.min`; accepts relu+sum, max/min+identity; predicate relu+max = `predicateNonlin`, predicate identity+max = `predicateAgg`; programmatic `TLProgram.compile` gives `tropicalNonlin "M"`.

## (e) Calls / context
About 55 tool calls; peak context roughly 95-110k. No hand mutations. One cheap discovery cost: the `Algebra` name clash only showed up in the full-library build.

## (f) For the T5 author (casts)
- `CheckedScheduledProgram` now has `algebras : Std.HashMap String SortAlgebra` (SOURCE names, partial) and `algebraOf (nm)` (entry, else predicate -> bool, else real; the fallback reads the COLLECTED `declEnv`). Both entries already hold the checked program: `prepareEvalPlan` Step 0 (`checked`, Compile.lean ~L1379-1383) and `evalScheduled` (`checked`, Eval.lean L129-133). Today both immediately project `.program`/`.declEnv`/`.explicitSizes` and drop the rest; T5 has to keep `checked` (or `checked.algebraOf` as a closure) in scope.
- Statement sort for a cast: `algebras[dest]` (same as the check), NOT `Stmt.algebra env` (they differ only for a scan state's neutral base). Private `T#k` clones and multi-writer names have no entry: fall back to `Stmt.algebra`/real.
- `residualizeAssignment` (Compile.lean L711, private): receives `agg : AggOp` and `terms`, builds `.read {sourceSlot, map, sourceShape, oobPolicy := .zeroPad}` at L743 from `resolveSource : String → TensorSlot × Array Nat`. It has NO destination sort or source sort. T5 needs two extra parameters (destination `SortAlgebra`, `algebraOf : String → SortAlgebra`), threaded through its 4 callers (L1089, 1197, 1579, 1631; seen by `rg`, not otherwise audited); the cast field goes next to `oobPolicy`. Under `unaryFn` the read takes real input: no cast.
- Cast table values the plan must realise (accepted cases only): bool -> real 0/1; bool -> max-plus false -inf / true 0.0; bool -> min-plus false +inf / true 0.0; everything else identity. Rejected cases never reach the plan.
- Reference side: `evalPlain`/`evalScan` take `decls : List Decl`, NOT the checked program; they select the statement algebra with `combineFor decls nm agg`. To reach the map they need one more parameter (`algebras : HashMap String SortAlgebra`, or the checked program) from the two call sites in `evalScheduled` (L163, L166), and from `evalScan`'s internal per-statement calls. The pre-existing tests call `evalPlain`/`evalScan` directly with `decls`, so a defaulted parameter (`algebras := {}` falling back to `declAlgebra`) keeps them compiling.

## (g) For the T6 author (scan state init)
- A scan state's sort is already computed: `algebraOf "S"` after `validateScheduled` (base + recurrence agreement; a neutral base adopts the recurrence's annotation; all-neutral = real). Scratch states (recurrence-only names) get entries too. A scan name that is ALSO written by another node has no entry (and later fails `multiWriterScan`).
- The unwritten-cell value for RC10 `G[0,1]` must read this entry for `G`, not the base statement's own `agg` (RC10's base `G[r,0] := Z[r]` is neutral with agg `sum`; its sort is max-plus only through the recurrence).

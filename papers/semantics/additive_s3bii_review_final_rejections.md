# S3b-ii final review: false rejections, false acceptances, weakened tests, docs vs code

Reviewer lens (b) of plan section 2. Read-only, code reading plus `git diff 04e2aef0 HEAD`; nothing built or executed (a full build was running in the tree). Every claim below is from reading code and diffs; "unpinned" means no fixture in the slice observes it.

Totals: 0 Critical, 0 Major, 8 Minor.

## Findings

### F1 (Minor; decision-relevant): the abstain rewrite changes a bool source's VALUES, not only the pad. Design section 4 says otherwise, and no fixture pins it.
Identifier: `desugarMultiWriters` neutral rewrite (`w.withAgg sort.stateAgg`); `boolReadCast` (reference) / `residualizeAssignment` `boolToTropical` (plan); design note section 4 ("a neutral copy's annotation cannot change values, only its out-of-range pad").
Scenario: `predicate Reach(s)`, `Vn[s] := maxreduce(Q[s, a])`, `Vn[s] := Reach[s]`. The copy is neutral, so it abstains and is rewritten to `max`. Both backends key the bool -> tropical cast on the statement's agg (`boolReadCast ... rhs.agg` for `.max`; plan `tropical && isBoolSlot`). The copy therefore reads true -> `0` and false -> `-inf`, where the same statement alone (sum, real `Vn`) reads `1`/`0`. The same goes for a `minreduce(Reach[s])` copy beside a `maxreduce` writer: the user wrote min (false -> `+inf`) and gets max (false -> `-inf`).
Assessment: the semantics are consistent. They match the one-statement form `maxreduce(Q[s,a] + Reach[s])`, the scan precedent (`scanStateStmts` doc names the cast explicitly), and `checkSortCasts` (bool into max-plus is legal). But the design claim the user's D5 choice rested on is false, and `CollectPlanTest`/`CollectTest` have no copy-of-a-predicate fixture. D2 has the same effect for an all-neutral tropical scan state whose base copies a predicate (`S[j,0] := maxreduce(P[j])`, `S[j,l+1] := maxreduce(S[j,l])`): it was real 0/1 before D2 and is now 0/-inf. This value change is not in design section 6's D2 flip list, and no fixture covers it.
Fix: correct design section 4 and the record. Add one value fixture per consumer (top-level copy of a predicate in a max group; all-neutral max state with a predicate base) on reference, plan f64 and plan f32.

### F2 (Minor): D2 also adds new cast REFUSALS for previously accepted surface scans. They are unlisted and unpinned.
Identifier: `scheduleAlgebras` scan branch (`writerSort?`), `checkSortCasts`.
Scenario: a scan whose scratch `T[j] := maxreduce(X0[j + 1])` is the only writer of `T` (all-neutral), read in the same scan by a predicate statement `P[j] := T[j]` or by a `minreduce(T[j])` statement. Before D2, `T`'s entry was `real`, so real -> bool and real -> min-plus were accepted. Now `T` is `maxPlus`, so both are `sortCastUnsupported`. Likewise, `T[j] := maxreduce(N[j])` with `N` min-plus was accepted (statement sort real) and is now refused (statement sort `maxPlus`). Each refusal is a correct consequence of "the state is max-plus" and matches what a top-level single neutral max writer already gets. But design section 6 lists only the max-vs-min conflict and the pad flips as D2 behaviour changes, and no `ScanCompileTest`/`CompileTest` fixture pins a cast refusal on an all-neutral state.
Fix: list these in the record as D2 consequences, and pin one reader refusal plus its real-reader accept neighbour.

### F3 (Minor; weakened coverage): "no entry on a conflicting group" is no longer observable. The old CompileTest (d) was the only fixture that could see it.
Identifier: `scheduleAlgebras` multi-writer branch (`| none => pure ()`); `CompileTest` (d) and its new neighbour "all-neutral max + min group is refused by collection".
Scenario: old (d) had a writer of a two-writer tropical `W` that bare-read min-plus `N`. That fixture asserted the error stayed `multiWriterAlgebra`, i.e. no entry, so the cast was never checked. It was flipped (correctly) to `sortCastUnsupported "W" "N"`. The new conflict fixture (`T := maxreduce(A)`, `T := minreduce(B)`) reads only real `A`, `B`, so it has no cast hazard. A mutation that inserts an entry for a conflicting group (say, the first vote) still yields `multiWriterAlgebra` there. `s3bTGPins` cannot hold a conflict because validation refuses it. So the design requirement "no entry on disagreement, collection remains the refusal" has no failing fixture. The plan's hand mutations covered "entry removed", not "entry leaked".
Fix: add a conflicting group whose max writer also reads a min-plus tensor (e.g. `T := maxreduce(N[i])`, `T := minreduce(B[i, j])`) and pin `multiWriterAlgebra "T"` on both entries.

### F4 (Minor): an accept-side change and a refuse-side change of the vote rule have no neighbour fixture.
Identifier: `writerVotes` / `checkWriterGroup`; `CollectTest` C6* block.
Scenario (a): `Y[i] := A[i, j]` (non-neutral sum) beside `Y[i] := maxreduce(B[i])` (neutral). The max copy abstains, the group is real, and the copy is rewritten to `sum`, which pads `0`. This was `multiWriterAlgebra` before the slice and is accepted now. The tropical mirror (`c6bN`, `c6dN`) is pinned; the real-winning direction, where a user's `maxreduce` annotation is silently dropped, is not.
Scenario (b): `Y[i] := relu(A[i])` beside `Y[i] := maxreduce(B[i, j])`. The relu copy is non-neutral (non-identity nonlin) and votes real, so the result is `multiWriterAlgebra`. This is a plausible Bellman spelling, and it is unpinned. The same holds for an Iverson-only copy (`f.read? = none`, so it is non-neutral).
Fix: add both to `CollectTest` (agg of `Y` and `Y#2` for (a); the error for (b)).

### F5 (Minor; unverified acceptance on a third consumer): `route` now admits tropical multi-writer programs, and no fixture observes the routed result.
Identifier: `route` (Lowering, calls `desugarMultiWriters` directly), `buildStep` BrOp selection (`.max => .maxreduce`); `CollectTest` "Route integration" RT1-RT5 (all sum).
Scenario: `tlprog!{ Y[i] := maxreduce(A[i, j]); Y[i] := maxreduce(B[i, j]) }` through `compile`/`route`. This used to fail with `multiWriterAlgebra` and now routes to a collector step with `BrOp.maxreduce` over n single-read terms. The audit listed this as NOT verified. No task observed it, and the slice adds no RT fixture. As before for single writers, `route` runs no `checkSortCasts`, so the routed path also accepts `rdBool` (a bool reader of a collected max-plus tensor) that both evaluation entries refuse.
Fix: one RT fixture pinning the routed op list for C6, or record it as unverified in the record.

### F6 (Minor): docs vs code, false or garbled claims in live docs.
- `leanncd/docs/test_portfolio.md` section 11 says `BoolCastTest` (j) covers the coerce "on a top-level, scan-base, scan-step and scatter read". It does not. BoolCastTest (j) says the scatter caller "can never see one" (`predicateScatterDest`), and the only scatter coerce fixture is reference-only, in `Eval.ScatterTest`.
- `papers/max_min_aggregation.md` banner: the edit kept the trailing "STILL" of the old "STILL / OPEN:" line, so it now reads "... not `[0,0]`). STILL S3b-ii (on its slice branch ...) closes ...".
- `lean_executable_semantics_path_part_5.md` puts S3b-ii in the list of slices that "remain planned" and in the same parenthesis says "executed on the slice branch".
- `lean_executable_semantics_path_part_4.md`: "Scatter, max/min and scan multi-writer sets are rejected ... and are not yet collected; mixed max/min/sum groups still are." The first clause still states that max/min sets are rejected, and "still are" has no clear referent.
- `DSL/AGENTS.md` Ast row: "`none` is a max-vs-min conflict". `none` is also a non-neutral sum (or nonlinear real) voter beside a tropical one; the Collect row states that correctly.
- `DSL/AGENTS.md` ScheduledValidation row: "each recomputes the sort from the statement's annotation, the declaration and the `scanStateStmts` rewrite" leaves out the new collection neutral rewrite (`Stmt.withAgg` in `desugarMultiWriters`), which is now a second site that rewrites annotations.

### F7 (Minor): stale code docstrings and test comments (live text the T5 sweep missed).
- `Exec/Uid.lean` `CompileError.multiWriterAlgebra`: "a writer of a multi-writer `T` aggregates with `max`/`min`". That is false now: an all-max group is admitted, and the error means the votes conflict.
- `Exec/Uid.lean` `scanStateAlgebraMismatch`: "two non-neutral statements of one scan state carry different sorts". Since D2 it also fires for two NEUTRAL statements (all-neutral max vs min).
- `Eval/Plan/Error.lean` `PlanError.castNotAdmitted` docstring names only `boolToTropical`, but it is now also raised for a misplaced `realToBool`.
- `test/DSL/Pipeline/CollectTest.lean` comment above `c6min`: "The refusal is decided from the writers' sorts, so a check that only tested `agg == .max` would admit all three of these". `c6min` is now admitted.
- `test/Eval/Plan/CompileTest.lean` `s3bPins`: "a two-writer name has NO entry". That is now true only of a sum group (`W` is one); a tropical two-writer name has an entry (`s3bTGPins`).

### F8 (Minor; unpinned edge of D1): a negative-zero source is not in the coerce fixture set.
Identifier: `boolReadCast` `.sum` arm (`v != 0.0`), `float64Ops.isTrue`, `float32Ops.isTrue` (`v != Float32.ofBits 0`).
Scenario: a real source `-0.0` read into a predicate. All three paths use IEEE `!=`, so it reads FALSE everywhere and the code is fine. But the fixture set `{0.25, 0.75, 0, NaN, -2}` would not catch a bit-pattern `isTrue` (e.g. an f32 `toBits != 0` rewrite), which would read `-0` as TRUE on f32 only. D1 makes real sources, where `-0.0` occurs naturally, the common input for the coerce.
Fix: add `-0.0` to `rtbReal` (expect 0).

## Checked and fine

- Top-level: no previously accepted program is newly refused. Before the slice only all-`sum` groups were admitted. Under `writerVotes` they vote `real` (non-neutral sum, relu-sum) or abstain (neutral sum), and predicate groups vote `bool`, so they never conflict. Their `withAgg` rewrite is `.sum -> .sum` (`bool.stateAgg = .sum`), so desugared output is byte-identical for every old accept.
- `checkWriterGroup` and `scheduleAlgebras` call the same `writerSort?` on the same statements. `ScanStmt.writes` and `routeWrites` are definitionally the same. A tropical agreed sort requires every voter to be an `.assign`: a `.recurMorphism` votes real, and scatter writers throw first or make `writerGroups` skip the group. So no tropical group is collected without an entry (the anti-goal is not reachable).
- Real groups with no entry let no cast through. Their writers are real voters or abstainers rewritten to `sum`, and every cast into real is legal. Readers see `algebraOf = real` (declaration fallback). Predicate groups keep the declaration's `bool` entry, so their writers are still checked.
- Predicate destination group: every writer votes `bool` (`ownAlgebra?`), `predicateAgg` fires earlier in `checkPredicateOutput`, and the collector is `sum`, i.e. OR. `Y#k` clones are added to `decls` as well as `env`, so the reference's `isPredicateDest` sees them and the collector's `Y#k` reads are not coerced (matches the plan's bool-slot test).
- Scatter writers stay `multiWriterScatter`; scan-node writers stay `multiWriterScan`; shape check unchanged and still after the algebra check; `reservedNameCollision` unchanged.
- T1 mixed-state behaviour: with any non-neutral writer, `writerVotes` is exactly the old `filterMap ownAlgebra?`. The test diff deletes no mixed-state expectation, and the new ScanOracle guard pins `([max neutral], [min contracted]) -> min`. A plain surface scan can now be refused only through the all-neutral max-vs-min conflict, which is intended D2 and pinned (`ScanCompileTest` `allNeutralMismatch`, both entries, both orders), plus F2.
- D1 refusals: `realToBool` is set only when `destIsBool && !isBoolSlot src` on a `.read` factor (unary reads never carry it), and a bool destination always compiles to `admittedAlgebraBool` (`algebraForDest`). The checker condition therefore holds on every compiler-produced plan, including the scan base/step (j6/j7 read a bool state and a real source in one step) and f32 (`checkAssignF32` accept guard). The scatter call site passes the flag, but `predicateScatterDest` makes it false there.
- Every pre-existing value that changed is on the design's list, with a reason that holds: `DifferentialTest` T4.3/7 0.75 -> 1.0 (0.25/0.75 bare reads coerce to 1, so the max over terms is 1) and its direct `checkBoolScalar` check; `DualityTest` parked pin -> `[[4,4],[-inf,-inf]]`; `ScanCompileTest` neutral scratch max/min tails; `CollectEvalTest` J4 `[6,8]` / j4m `[1,3]` (from hand arithmetic: max/min of row maxima/minima); `CollectTest` C6/c6min; `CompileTest` (d). Nothing else changed in `leanncd/test` except comments.
- C6b/C6c/c6bm/c6cm rewrite: the old intent was "a mixed sum+max set in both orders, so a first-only or last-only check survives neither". It is preserved with a NON-neutral sum writer (`A[i, j]`). The old programs (sum copy) moved to accept neighbours `c6bN`/`c6cN`/`c6bmN`/`c6cmN` with agg assertions, and a three-writer `c6i` (sum in the middle) was added. Nothing was dropped.
- No `#guard` removed without replacement. The `ScanUnroll.localStateAgg` restatement is independent (first-hit search, calls no production helper), and the ScanOracle guard compares it with production plus literal expectations.
- Bool and other-tropical readers of a collected tensor: `CompileTest` (d2) and `CollectPlanTest` `rdBool`/`rdMin` -> `sortCastUnsupported` on reference, plan f64 and plan f32; `rdMax`/`rdReal` accept neighbours.
- Neutral copy pad: `belP1p`/`belP3p` and `tpadMax*`/`tinf*` pin `-inf`/`+inf` pads on all three legs.
- `Eval/AGENTS.md`, `Eval/Plan/AGENTS.md` (the realToBool and castNotAdmitted rule), `Semantics/AGENTS.md` (oracle mixedSorts vs production accept) and the decision-note A7 row match the code.

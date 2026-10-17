VERDICT: APPROVE WITH MINORS (0 Critical, 0 Major, 4 Minor). Reviewed from git objects of 17f7fb68 only; no build run.

## Checklist results

1. Readiness rule: correct for every scenario hunted. Details:
   - Single-writer stability: `outputs` is a subset of `writes`, so only a name's writers can emit it, and `count r <= #writers`. With one writer, `count r == 1` iff `emitted.contains r`; with zero writers both rules are true. `publications` differs from `outputs` only by `eraseDups`, which cannot change `contains`. So the emitted order is IDENTICAL to before for every program in which no name has >= 2 writer nodes (the first eligible index is the same at every step).
   - `outputs = [G,G]` scan: `writes` is `eraseDups`'d so it is one writer, and `publications` is `[G]`, so count 1 = 1. No deadlock, no early release.
   - Plain self-read: the node's own publication is not yet emitted, so `count r <= #writers - 1`; a plain node is NEVER eligible for a read of its own destination, single or multi writer. The docstring claim is true.
   - Scan self-read: the scan arm short-circuits on `sc.writes.contains r` and ignores other writers of `r` (pre-existing; see F3).
   - Zero writers: `0 == 0`, ready immediately (R1's `A`/`B` reads exercise it).
   - Duplicate `reads`: `.all` is idempotent.
   - Fuel: still `stmts.length`, one node consumed per step, so it suffices. The `acc ++ remaining` fallback is textually unchanged; it fires on more inputs (multi-writer self-reads and out-of-order multi-writer sets), all of which `schedule` then rejects through `isTopoOrdered`.
   - `schedule` (Lowering) changes only through `topoSort` + `isTopoOrdered`, same predicate on both sides; `route`/`routeCore` do not call either (only `schedule` calls `topoSort`), so G21's NEW leg is untouched by this commit. No proof module mentions `topoSort`/`eligible`/`isTopoOrdered`.
2. Fixtures: all pin something; none is vacuous. See table.
3. T1-review concern (writer reads T): pinned at the SOURCE path by R3 with the exact `cyclicDataflow "schedule: cyclic dataflow"`; the hand-built/direct path is T3's J1. See checklist 3 below.
4. Prose: one imprecise clause (F2). No `File.lean:NNN` references in the commit.
5. Sibling audit: both rows confirmed; one cell the plan misses (F1).

### Fixture table (old vs new)
| Fixture | Old rule result | New rule result | Distinguishes? |
|---|---|---|---|
| R1 `T:=A; U:=T; T:=B` -> `[T,T,U]` | `[T,U,T]` (reader after first writer) | `[T,T,U]` | yes (strict) |
| R2 `[T:=A,U:=T,T:=B]` not topo-ordered | true (ordered) | false | yes (guard is `!`) |
| R2b `[T:=A,T:=B,U:=T]` ordered | true | true | accept-neighbour by design; kills a "reject all multi-writer" mutant. Fine, the pair is checked in both directions as the plan requires |
| R3 `T:=A; T:=T·B` -> `schedule` error | accepted (reads first writer's T) | `cyclicDataflow "schedule: cyclic dataflow"` | yes; the pattern requires the exact payload, so no other error can satisfy it |
| R3b `T:=A; U:=T·B` -> `[T,U]` | same | same | accept-neighbour; the only difference from R3 is the destination name, valid |
| R4 scan `outputs == [[G,G]]` + plain reader | true | true | readiness rules coincide, BUT it pins `publications` dedup: without `eraseDups` count 2 != 1 so reader is rejected (A2-M2 per ledger, killed). It is not a readiness fixture; fine, its job is the dedup |
| G21 migrated | old leg: `routeCore` error | old leg: `schedule` error | yes |

G21 derivation checked: the collision program is `%nl0 := X; Y_n := relu(%nl0)`; `splitNonlins` mints `%nl0 := %nl0` (a second writer that reads `%nl0`) plus the consumer `Y := relu(%nl0)` reading `%nl0`. After the first writer, count 1 != 2 for both, nothing is eligible, the fallback runs, `isTopoOrdered` is false, so `schedule` throws the `schedule:` payload. All 8 cases are the same program modulo `Y{n}`, so they reject identically. The commit edits only the OLD-leg payload pattern (and prose); the NEW leg clause (`some new`, `wellFormedDom`, acset round trip) and the `| _, _ => false` fallthrough are unchanged, and the NEW leg (public `route` on the single-writer logical schedule) never reaches `topoSort`. The new leg cannot start rejecting because of this commit.

## Findings

### F1 [Minor] Numerator/denominator asymmetry (publications vs writes) is undocumented and unpinned
`eligible` compares `emitted.count r` (publications) with the number of nodes whose `writes` contain `r`. A scan whose recurrence-only scratch `S` is also written by a plain node counts as a writer of `S` but never publishes it. Scenario (hand-built schedule): `[plain S := X, scan{scratch S} .., plain U := S]`. Old rule: `U` ready after the plain write (`emitted.contains S`). New rule: count 1 != 2, so `U` is never ready and `schedule`/`validateScheduled` report `cyclicDataflow`. Changing the denominator to publishers would be WRONG (a reader of pure scratch would become ready, as for an external), so the code is right and deliberate, but the docstring's "scan scratch is never emitted, so a reader of it is never ready" is stated only for the single-writer case, and no fixture pins the mixed case. It is probably unreachable from source (`duplicateScratchProducer`) and T4's `multiWriterScan` rejects scan+plain groups before this matters on the collected path. Audit-table cell the plan misses: row `eligible`/`topoSortFuel`/`isTopoOrdered` has no "plain + scan-scratch" cell; it is R (behaviour change old accepted, new rejects). Fix: add one sentence to the `eligible` docstring and one hand-built `#guard !isTopoOrdered` fixture (Direct path), or park it in plan §2.

### F2 [Minor] AGENTS.md clause overgeneralizes to scan writers
`DSL/AGENTS.md`: "a writer that reads its own (multi-writer) destination is `cyclicDataflow`". True for a plain writer (R3). False for a scan writer: the scan arm of `eligible` short-circuits on `sc.writes.contains r`, so a scan reading its own state never waits on it nor on any other writer of that name (and a plain reader of that name is unaffected). The preceding sentence of the same bullet already says "scan-internal dependencies remain legal", so the two read as contradictory. Fix: "a PLAIN writer that reads its own (multi-writer) destination ...". Also note for T4: because of that short-circuit, a scan sharing its state name with a plain writer would not wait for the plain writer; T4's `multiWriterScan` rejection is what makes this safe, so T4's fixtures must cover plain+scan in both orders.

### F3 [Minor] No fixture that a scan counts as exactly one writer inside a multi-writer group
R4 pins dedup with a lone scan plus a reader; no fixture has a scan AND a plain writer of the same name feeding a reader (the case where "nodes, not occurrences" actually matters for release timing). Mutants such as counting `writes` with duplicates for a two-face scan survive only if they happen to keep count == 1 for R4; the one the ledger lists (A2-M2) is killed. Low value because T4 rejects such groups upstream of the collector, but `schedule` itself still orders such programs before the rejection, so the schedule step is observable. Fix (optional, Direct path): extend R4 with `[plain G := Z0, scanG, plain T := G]` expecting ordered, and the reader-before-scan permutation expecting not ordered.

### F4 [Minor] Verification gap: only two test targets named
The plan's targets are `CollectTest` and `RouteFragmentCorpusTest`; the commit migrated only G21. T2 changes `schedule` behaviour for any existing program with a name of >= 2 writer nodes anywhere in the test tree (hand-built `ScheduledProgram`s in Eval/Plan, PropertyOracle generators, Portfolio). Ledger says "build green (8602 jobs)" for the implementer, which may or may not include every test module. The whole-branch review must rely on the full `lake build` at close-out, not on these two targets; flag it in the close-out. (I could not run it.)

## Sibling audit (T2 rows)
- `eligible`/`topoSortFuel`/`isTopoOrdered`: R confirmed for "multi plain"; "multi incl. scatter" and "plain + scan" cells: R, and the "plain + scan" cell is more specific than the plan states (see F1 and F2, scan arm short-circuits and scratch asymmetry).
- `schedule`: unchanged text; behaviour changes only through `topoSort`/`isTopoOrdered`; confirmed. `routableInOrder` doc in Lowering ("False exactly for a genuine inter-step cycle (topoSort source-order fallback)") remains true because `schedule` now rejects every fallback case first.
- Comments mentioning `isTopoOrdered` in `Eval/Plan/Compile.lean` ("tracks published outputs, not all scan writes") and `Structural.lean` remain true (they are about publications) and are not made false by this commit.

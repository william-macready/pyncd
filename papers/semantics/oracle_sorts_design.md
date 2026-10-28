# Oracle per-tensor sorts and coverage: design note

Historical design: B5 has since widened the bounded native collection boundary,
replacing the three shape-correct D7 refusal donors with actual four-leg value
rows and adding separate SOURCE/SHAPED stages. Unsupported multi-axis/constant
donors retain refusal controls. See [the B5 record](additive_b5_record.md).

Status: DESIGN, 2026-10-26, base main 9507c5af (local main is pushed). Evidence: `oracle_sorts_audit.md` (read-only; every "audit" claim is code reading, unobserved until a task observes it).
Predecessors: `additive_s3b_record.md` sections 9-10, `additive_s3bii_record.md` section 4, `additive_production_decision_note.md` (A1-A2, A7 casts).

## 1. Intent

The Source oracle is the independent four-leg check (oracle, Core leg, legacy native, checked native). It is single-sort: `selectCarrier` picks one carrier per program and a mix is `mixedSorts`.
Every defect found after S3b was found by review, not by the oracle. Mixed-sort programs and copy-form groups are production-only and hand-valued. This slice gives them an independent check, so B5 and in-scan
collection can later be checked against it and not only by hand.

## 2. Decisions (user, 2026-10-26; do not reopen)

D1. **Bar: strict mutation bar, honestly scoped.** Success = re-introducing each defect in section 4 flips an oracle classification or an agreement-corpus guard, run by a mutation manifest, not asserted.
    The defects no oracle can see are listed and stay hand-fixtured, labelled production-only.
D2. **Design: value oracle + independent rule predictor.** A heterogeneous VALUE oracle (per-tensor sorts, casts, collection) on the current Source sublanguage, plus an independent SYNTACTIC rule predictor over the full
    `Stmt` AST compared with production over enumerated corpora. Bool stays OUT of the oracle's sorts. Widening the Source language (bool decls, Iverson, affine/const reads, unary, nonlinearity, scan) is a separate slice.
D3. **Refusals** are classified, not hidden: new `SortedClassification` constructors appended at the end (`refusalParity`, `refusalMismatch`); the existing seven and their printed forms stay. Same refusal = same error constructor name (payload names are brittle).
D4. **Core leg for mixed programs: stratified (K2).** Run the existing single-K Core leg once per target in dependency order, earlier targets entering as rational inputs; legal only while intermediate cells are finite. Weaker than one mixed Core program
    (cross-statement scheduling is not checked); the record says so out loud. A real heterogeneous Core leg (600-1000 proof lines) is its own slice, on request.
D5. **Non-finite cells read by a real statement** (a tropical `±inf` cell in a real product) = new `Unsupported` constructor `nonFiniteIntoReal`, class `unsupportedNumericalProfile`, excluded from parity rows. No IEEE in `ExtVal`.
D6. **Cast decision A (2026-10-24) is encoded exactly**: the oracle refuses a direct max-plus <-> min-plus and tropical -> bool read and accepts the one-real-copy laundered form. Two rows pin the pair; if A is revisited they flip together.
D7. **Scatter/affine writers inside a multi-writer group**: production refuses (`multiWriterScatter`, B5); the harness predicts that refusal so such programs are not false `nativeFailure`. One row.
D8. **Placement: rule tables and the heterogeneous evaluator are test-side** (`test/Semantics/`), so production cannot import the independent rules and tasks need no library rebuild; library edits only where `compareMixedSource` needs a public hook.

## 3. Goals, non-goals, anti-goals

Goals: `compareMixedSource` classifies mixed-sort and copy-form Source programs; per-tensor sort, cast, collection and writer-vote rules are stated independently of production; homogeneous programs agree with the typed `runWith` path.
Non-goals (owners): bool / Iverson / pad / unary / nonlinearity / scan / NaN / signed-zero oracle values (language-widening slice, or the existing test-side property oracles `ScanUnroll`, `ScanOracle`, `DualityTest`); real mixed Core leg (own slice);
B5; in-scan collection; JAX; F2 cast bypass (decision A kept); `route`.
Anti-goals: a rule predictor that calls a production rule helper (the mutation becomes invisible; this is how M1 slipped past the duality property); a corpus with no entry that distinguishes a claimed-killed mutation (the contracted-axis conjunct was once caught by hand-built shapes only);
editing the typed path's shapes (`Contribution K`, `Result K`, `SortedClassification` printed forms: ~63 guards print them); a silently changed expectation; calling the bar met while a "not covered" row has no label.

## 4. The mutation bar (rows; manifest `papers/oracle_sorts_mutations_post.json`, entries copied from observed failures)

Killed by: V = value-oracle row/classification, P = rule-predictor agreement corpus. R-ids are the audit's section 3 ids.

| R | Defect (fix commit) | Mutation site | Killed by |
|---|---|---|---|
| R1/R12 | neutral writer with nonlinearity / Iverson-only copy evades the vote refusal (`38c468f5`; manifest `T9-M1`) | `Stmt.isSortNeutral` drops the nonlin clause | P (corpus has relu / Iverson copies) |
| R6 | colliding-LHS `Out[i+j]` treated as neutral (`669ce30e`) | drop the `axisUids.eraseDups.length <= 1` conjunct | P (no program shape exists) |
| R16 | contracted-axis conjunct of neutrality | drop the contracting-read conjunct | V + P (`Y[i] := A[i,j]` beside `Y[i] := maxreduce(X[i,j])`: oracle predicts refusal) |
| R11 | neutral max/min copy beside a non-neutral sum writer is absorbed; tropical mirror | `writerVotes` lets neutrals vote | V + P (copy-form group: oracle predicts a value) |
| R10 | conflicting group leaks a sort-map entry, changing which refusal fires | `scheduleAlgebras` conflict arm inserts the first vote | V (refusal-constructor identity) + P |
| R9 | all-neutral fallback arm of `writerVotes` (top-level analogue) | fallback arm returns `[]` | P |
| R4 | cast rejections bypassable (decision A): `T4-M3c` max <-> min | `checkSortCasts` accepts | V + P (direct refusal row + laundering pair) |
| R4b | `T4-M3b` tropical -> bool accepted | `checkSortCasts` accepts | P only (needs a predicate declaration; cast corpus) |

Not covered, labelled production-only (hand fixtures stay): `T4-M5` (unary read exempted from the cast check; needs a unary read) and `T4-M3d` (real -> bool rejected; needs bool), R2 NaN truth, R3/R15 unary OOB `f(0)`, R5 raw scan init tie, R7 neutral scratch (scan), R8 predicate abstain rewrite (needs bool), R13 `route`, R14 NaN / `-0.0` (`compareBindings` normalises zero bits).

## 5. Shape of the change (author's calls, marked)

- Oracle values: `ExtVal` (`fin q | negInf | posInf`) is the universal value (audit: sufficient; already the shared observation type). A statement RUNS in its destination tensor's sort (single writer: its own annotation; group: the agreed sort, abstaining neutral copies rewritten to it, so a neutral `minreduce` copy beside a sum writer runs as sum); `(add, mul, zero, one)` come from that sort; each target collects with the target's sort ⊕. Cast LEGALITY is keyed on the destination tensor's sort entry, as in production (`checkSortCasts` reads the map entry of the destination, not the statement): a real or conflicting-group destination has no entry, so its reads are unchecked and cast by identity. Ops re-stated by hand in a NEW test-side file, not `Carrier.lean`, and not via `Semiring`. *(author's call; corrected after the builder check against `checkSortCasts`)*
- Cast rows split by layer: V rows cover real <-> tropical identity and the max-plus <-> min-plus refusal plus the laundered one-real-copy form (all Source-expressible). The tropical -> bool refusal (`T4-M3b`) is P-ONLY: it needs a `predicate` declaration, which Source refuses, so P builds it at the `Stmt` level. D6's "two rows pin the pair" means the direct max <-> min refusal and the laundered form. *(author's call)*
- Refusal precedence is NOT part of the independent spec. The predictor names the constructor only for programs with exactly ONE applicable refusal; the corpora are restricted to such programs. Production's order of refusals is pinned by a few hand rows separately (R10's mutation changes which of two refusals fires, so its row is one of them, with the production constructor stated explicitly in the manifest `expect`). *(author's call)*
- P's production side runs the real pipeline (`validateScheduled` / `compile` on a minimal full program) and observes accept/refuse and the refusal constructor; it never calls `writerSort?`, `checkWriterGroup` or `checkSortCasts` directly (those are the mutation sites). *(author's call)*
- K2 (D4) with a non-finite intermediate tropical cell (unwritten cell, zero-extent reduction): the Core leg is NOT run for that row and `SortedRun` records an explicit `coreNotRun` marker (three-leg row, listed as such, never counted as `fourLegParity`). *(author's call)*
- T0 is a hard gate: if the native legs reject a mixed Source program (`bellman .max .sum`), stop and report; a library fix is a production change outside this slice (Rule 14), not a contingency task. *(author's call)*
- R9 counts as killed by P alone (observed by the manifest); no extra reader row is required. *(author's call)*
- Per-tensor sort rule restated from the spec (audit section 1(a)) including both arms: a single writer uses its OWN annotation even if neutral; a multi-writer group votes (neutrals abstain beside non-neutral; all-neutral voters by non-sum annotation; max vs min = refusal).
- The typed path (`runWith`, `compareSortedSource`, `selectCarrier`, `Carrier.lean`, `Oracle.lean`) is not edited. `compareMixedSource` is a sibling in `SortedDifferential.lean`; native legs already take mixed programs (`runNative (sorted := true)` never selects a carrier; NOT yet observed: task T0 observes it first).
- Mixed profile: product bound for real statements, sum-of-magnitudes bound for tropical ones (the existing sorted profile uses the tropical bound for all and is weaker for real).
- Independence guard: `ScanUnroll.oracleNeutral`/`oracleIdxUids`/`oracleSlotUids` may be reused (already independent, pinned by `neutralShapes`); no other production rule helper (audit section 5 list) may be called. A grep guard in the plan lists the forbidden identifiers.

## 6. Constraints

`checkStructure` requires every used tensor f64 (`typedTensor .f64` in every fixture). Admission refuses everything outside bare-index monomials (audit H1): fixtures stay inside it. Hand-valued expectations are observed from the Core leg or derived independently, never copied from `CollectPlanTest`.
Do NOT start in-scan multi-writer, B5, or any language widening under this slice (Rule 14).

## 7. Left to the builder

File split inside `test/Semantics/`; corpus extent (audit: ~441-pair vote corpus, 16-cell cast corpus, ~35 rows); how the refusal outcome carries the expected constructor; the exact `nonFiniteIntoReal` plumbing; which existing programs are re-expressed (audit section 4: ~12-16 candidates); split of the mixed-differential task (audit flags it at the 60-turn limit).

## 8. Process, cost

Full-lite (new soundness oracle, no production semantics change, no patch series). Audit estimate: T0 probe, T1a rule tables + corpora, T1b mutation cycles, T2 heterogeneous evaluator, T3 `compareMixedSource` (split a/b), T4 stratified Core leg, T5 docs: 5-6 implementer dispatches, ~190-260 turns, ~35-55M execution tokens (Rule 6 budget 175M); authoring target <= ~50M, no prototype series.

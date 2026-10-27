FINDINGS: no merge-blocking item; 4 Important, 9 Minor. Each one is a record statement or a cheap doc/comment/guard fix.

# Oracle per-tensor sorts: final whole-branch review, lens B (coverage and honesty)

Branch `worktree-oracle-sorts`, 67af0367..3a83d69d (8 commits). Read-only review. Inputs: the whole-branch diff, the design (section 4 and D1-D8), the plan (deviations 1-4, Review Focus, the 'Deliberately NOT done' table), facts, ledger, manifest, mutation results, and the session's mutation logs (`mut3.out` final run, `mut2.out` R11 probe) and T4b/T5 reports in the session scratchpad. No build was run.

## Merge-blocking

None. The branch's claims are mostly accurate and the unusual cases (R6, R11) are reported honestly. Several statements are over-broad or missing (below), and the record can fix all of them. Before merge I recommend the four Important items, which are documentation, evidence and comment changes plus at most two guards.

## Important

**I1. R11: the only new-surface evidence is a probe log in the session scratchpad, which will disappear. The masking is also a lasting structural hazard.**
- `mutation_results.md` honestly reports the R11 problem. In the shipped tree the R11 mutant is caught first by the pre-existing `Eval.PropertyOracle.ScanGen` guard. Every new module reaches `ScanGen` through `OracleSortRules` (`import Eval.PropertyOracle.ScanUnroll`, which imports `ScanGen`), so a ScanGen failure stops all 8 new modules from building.
- The new-surface kill was seen once, with ScanGen's guard temporarily commented out. The observed lines are in the scratchpad `mut2.out`:
  - `OracleSortRulesTest` C1 (`#4: production multiWriterAlgebra, predicted []`)
  - C3 (`R11 sum contraction + neutral max copy`)
  - two C4 guards
  - five `OracleMixedValueTest` R11 value guards
- The manifest's R11 `expect` names only the ScanGen line. Re-running the manifest therefore cannot show that the new surface catches R11. Design D1's bar ("run by a mutation manifest, not asserted") is met for R11 only by that one-off probe.
- There is also a lasting hazard. Any future production change that breaks a `ScanGen` guard hides the whole mixed oracle for that build. For example, B5 or in-scan collection, which is the work this slice exists to check.
- Merge: do not block. State it. Before the scratchpad is lost, copy the probe's failing lines into `oracle_sorts_mutation_results.md` or the record.
- Separate follow-up, own item (Rule 14), about one small dispatch plus one cycle: move `oracleNeutral` into a leaf test module with no ScanGen dependency. Both `ScanUnroll` and `OracleSortRules` would import it. The ScanOracle `neutralShapes` pin then still covers it, and the R11 manifest row can `expect` the new-surface strings.

**I2. "60 flips" and "22 distinct programs" overstate the corpus. The record must give the real counts.**
- **Flips.** `rg -c "^#guard parity"` counted guard LINES (T5 report). Of the 60 T4 lines, 7 repeat a program already asserted:
  - the R11 block re-asserts `bellman .sum .max`, `bellmanRev .sum .max`, `bellman .max .sum` and `bellmanRev .max .sum`;
  - the negative-control block re-asserts `bellman .max .max`, `bellman .min .min` and `j4 .max`.
  - That leaves 53 distinct program instances on four legs from T4, plus `chain3` and `chain4` from T5: 55 in all, over 62 lines.
- **Distinct programs.** Commit 39fdf0e8's body says "22 distinct existing programs". That counts donor fixture names, not shapes:
  - 14 of the 22 are single-sort programs, which the typed path could already express: product, contract, strided, collide, zeroY, bellman min-min, J4, j4m, P1, P5, P2, P3, P5m, vrSumOnly.
  - The 8 mixed ones (tcopyMax, tcopyMin, P1c, P2c, P3c, vrSumMax, vrSumMaxR, vrSumMin) all have the copy-form Bellman shape already covered in dispatch 1, with different inputs.
  - The T4 reviewer's count of about 12 structurally distinct shapes in dispatch 2 (about 18 with dispatch 1) is the honest figure.
  - The commit body cannot be changed, so the record must correct it.
- The ledger's T5 line ("60 rows flipped") repeats the overstatement.

**I3. Undeclared deviation from design section 5: the corpora are NOT limited to programs with exactly one refusal.**
- Design section 5 says: "The predictor names the constructor only for programs with exactly ONE applicable refusal; the corpora are restricted to such programs."
- The plan's Global Constraints replaced this with "with several only for membership (design section 5)", citing the design as if it said the same thing. C1 runs all 441 pairs, and many of them carry two predicted refusals, for example a relu max writer beside a colliding-slot writer gives `tropicalNonlin` and `multiWriterScatter`.
- `agrees` (`rs.any (fun r => r.1 == e.1)`) and `classifyRefusal` (`p.refusals.any (fun r => r.1 == l)`) therefore cannot catch a spurious EXTRA predicted refusal on any program production already refuses.
- This is a real weakening of the independent rule check, not just a ledger minor.
- Fix: the record lists it as deviation 5, with the number of C1 programs that have two or more predicted refusals (one `#eval` over `corpusC1`). Optional fix later: restrict the equality check to single-refusal programs and count the others separately.

**I4. The mixed numerical profile's rejection side is never exercised.**
- No row drives `checkMixedProfile` to an error. `rg "outsideEnvelope|nonIntegral"` over the new modules finds nothing, and no manifest mutant targets it.
- Design section 5 makes "product bound for real statements, sum-of-magnitudes for tropical" a design point. Yet a mutant that skipped the whole occurrence loop would survive every guard.
- Impact is limited. Each final cell still goes through `checkExt`, and an inexact native sum would show as `nativeDiscrepancy`, which is loud, not as false parity. That is why this is Important and not blocking.
- Fix, about 2 guards: one real product past the envelope (expect `unsupportedNumericalProfile (outsideEnvelope .. subsetProductBound ..)`) and one tropical sum-of-magnitudes overflow. Or the record states that the rejection arm is untested.

## Minor

**M1. R12's Iverson arm has no mutation row (design section 4 row R1/R12).**
- The row claims R1 and R12 are killed by P. `T9-M1` mutates only the nonlinearity conjunct of `Stmt.isSortNeutral`. The Iverson arm (`| none => false` under `match f.read? with`) is never mutated.
- C1 does contain a pair that would catch it: `writer 3 .sum` (Iverson-only) beside `writer 0 .max`. It is real today and would become max-plus under the mutant. That kill is predicted, not observed.
- Fix: add one manifest row (`| none => false` -> `| none => true`, target `Semantics.OracleSortRulesTest`), or the record says "R12 Iverson arm: distinguishing C1 entry exists, no cycle run".

**M2. The docs over-claim "four legs".**
- `leanncd/docs/test_portfolio.md` says "value parity on four legs (reference oracle, legacy, checked plan, stratified Core) or predicted-refusal parity".
- Some accepted rows have three legs (`maxReadsMax`, `minReadsMin`: Core not run), and non-finite reads into real statements are classed `unsupportedNumericalProfile` and never compared.
- The not-covered sentence also omits the production-only rows: NaN and signed zero, `route`, raw scan init tie, neutral scan scratch, the predicate abstain rewrite, `T4-M5`, `T4-M3d`.
- Suggested wording: "four legs where every intermediate read is finite (three otherwise; a non-finite cell read by a real statement is excluded)". Point to the record for the production-only list.
- The `leanncd/AGENTS.md` row is accurate ("`threeLegParity` states why it did not run"). It points at `../papers/semantics/oracle_sorts_record.md`, which does not exist yet; the controller writes it after this review, so its absence is expected.
- The two record updates (`additive_s3b_record.md`, `additive_s3bii_record.md`) are scoped correctly: CLOSED for mixed and copy-form groups, still open for bool, Iverson, pad, unary, nonlinearity, affine-read and scan values.

**M3. A stale comment contradicts the guard under it.**
- In `OracleMixedValueTest` the comment reads "homogeneous control (the typed path says `fourLegParity`; here Core is not run)", directly above `#guard parity (bellman .max .max) ..`.
- That guard now asserts `fourLegParity` and the Core leg's cells. The comment dates from T4 and was not updated in T5.
- Fix: "here too it is `fourLegParity`".

**M4. The edited comment in `SourceSortedDifferentialTest` is over-broad.**
- It now says production "refuses only a group of two non-neutral voters that disagree".
- Production also refuses an all-neutral max + min group (`multiWriterAlgebra`, facts 5(c), the R10 shape, pinned in this branch's C3 and refusal rows).
- Fix: "refuses a group whose voters disagree (two non-neutral voters, or an all-neutral max + min group)".

**M5. `agrees` misstates why real and bool sorts are not compared.**
- Its docstring and the C3 `Row.expect` comment say "real and bool carry no entry".
- Production does publish `real` entries for single-writer tensors (facts 5(d), 5(f), 5(g): `R:real`, `O:real`, `S:real`). Only real GROUPS have no entry.
- The predictor's non-tropical sorts are dropped from the comparison by choice. As a result, a bool-versus-real confusion on a tensor production publishes is never caught.
- Cheap strengthening: for every entry production publishes, require the predicted sort to equal it, and keep the tropical check in both directions. Otherwise fix the docstring and state the gap.

**M6. `stmtSorts` and the stratified Core leg (D4) need to be stated precisely.**
- Production never publishes a per-statement running sort. So "a neutral copy runs in the group's sort" (Review Focus 1) is checked against production only through native values, and those values do not distinguish it for the bare-copy rows: one occurrence per cell, as the `OracleMixedEvalTest` comment says.
- The Core leg takes `p.stmtSorts`, so it cannot check the sort assignment either. The `allReal` doctor control shows this: Core agrees with the doctored oracle, and only the legs disagree.
- For a mixed program, `fourLegParity` therefore means "Core agrees on the arithmetic under the predictor's sort assignment". The assignment itself is checked by the hand `runs`/`ranIn` rows and by C1-C3 tensor-level agreement.

**M7. Negative controls and RED evidence are thin. The record should state it.**
- The doctor control is all-real only. A partial doctor would hit `inconsistent` ("written in several sorts"), which `compareMixedSource` maps to `referenceUnavailable`, and no row pins that.
- T4 and T5 value rows passed on their first build. Values were derived by hand beforehand, so there is no printed-then-pinned RED. The available evidence is a one-guard sanity flip (T4b), the compile-level RED (T5), and the four `feed` controls.
- `classifyRefusal`, `coreLeg` and `checkMixedProfile` have no manifest mutant. Negative controls stand in for them.
- The T3-E3 kill reads, in the results table, as coming from the per-occurrence sort guards. The value guards of the four mixed Bellman rows also fail, because the mutant makes `runMixed` throw `inconsistent`; it is not a value difference.

**M8. Test quality (Rule 9).**
- `isMismatch` is a substring guard in `OracleMixedRefusalTest`, made redundant by the exact-string guard on the next line. Drop it or keep it, it adds nothing.
- Fixture-index literals are hard-coded:
  - `nonFiniteAt copyMax 5 [1]`
  - `failure copyMax == "...nonFiniteIntoReal 5 [1]"`
  - `bump 5` / `bump 6` / `bump 8`
  - the positional `c2Refused` matrix
  - They are commented and length-guarded, but break silently if a tensor is reordered: the guard fails without saying why. Deriving the declaration from the name (`orderOf`-style) would remove that.
- `#guard` failures print only "Expression" (see the mutation logs). The `run_cmd assertNone` style names the offender. The `parity` guards each re-run `compareMixedSource` four times, which costs time but is not a correctness issue.
- No guard that cannot fail was found. The structural `#guard writers21.length == 21` lines and `!isParity` beside `isDiscrepancy` are redundant but harmless.

**M9. Ledger-deferred minors: record them, no fix needed before merge.**
- T1, repeated-free-axis slot `Y[a,a]`: production treats it as non-bare, the predictor does not model it. If a row ever used it, the result would be a loud `refusalMismatch [] ..`, not a silent pass.
- T2, the `l == c` conjunct of `classifyRefusal` (legs refusing with different constructors): no row exercises it. A hand-built `NativeRun` costs more than it buys.
- T2, the sentinel `referenceUnavailable "accepted: .."`: `compareMixedSource` branches on it, so a future second `referenceUnavailable` return in `classifyRefusal` would silently send rows down the accepted path. Before anyone extends it, a dedicated return value (for example an `Option`) is the durable fix.
- T4: `refusalMismatch [] "runtime"` naming. The three non-finite rows' legs are now pinned `.unavailable` (T5), so that item is closed.
- T5: `coreLeg`'s early `return none` throws away the prefix it has already computed. The zero-filled placeholders are safe only because `runMixed` ran `checkOrder` first. Add a one-line comment at the `extra` binding.
- T1 duplicated private helpers (`aggOf`/`nonlinOf` in `OracleSortRulesTest`): trivial.

## Item-by-item answers

**1. Mutation table versus design section 4.** All 16 audit R-ids are accounted for:

| Row | Status |
|---|---|
| T4-M3b | new surface (P), as designed |
| T4-M3c | new surface (V + P) |
| T9-M1 (R1) | new surface (P); the R12 Iverson half has no cycle (M1) |
| R16 | new surface (V + P; V is only the `r16a` row, since `r16b` stays a conflict under the mutant) |
| R10 | new surface; only the max-first order flips, as predicted |
| R9 | new surface (P) |
| R6 | pre-existing `ScanOracle` guard only, labelled (deviation 2). In the R6 cycle the new modules did build (they do not import `ScanOracle`), so "C1 did not fire" is observed, not masked |
| R11 | masked (I1) |
| T4-M5, T4-M3d, R2, R3/R15, R5, R7, R8, R13, R14 | production-only, labelled in the plan's not-done table and design section 4 |

- No row is silently dropped.
- Over-claimed: R12's Iverson half (M1).
- The R11 masking is honestly reported. In the shipped tree the new surface's R11 kill rests on the probe alone. State it and do not block (I1).

**2. Not-covered labels.** The AGENTS.md row and both record updates are accurate and scoped. `test_portfolio.md` over-claims four legs and leaves out the production-only rows (M2). The AGENTS.md reference to the record file is expected to be missing until the controller writes it.

**3. `threeLegParity` accounting.**
- No code path or guard counts a row as four-leg without Core having run and agreed:
  - `fourLegParity` needs `coreObs = some cs` and `compareTensors` agreement, which also checks missing or extra tensors.
  - `parity`/`parityExt` also require the Core leg's own cells.
  - `maxReadsMax` and `minReadsMin` pin `threeNotRun` and `coreNotRun`.
  - The three non-finite rows pin `unsupportedNumericalProfile (nonFiniteIntoReal ..)` and `legsUnavailable`.
- The counts are overstated (I2).

**4. D4/D5 weaknesses.** All of them must be stated (M6, M7, I3, M5). None needs a fix now except the cheap I4 guards, which are optional.

**5. Test quality.** M8.

**6. Ledger minors.** M9: record all, fix none before merge.

## What the record must state

- **Mutation results.** Killer per row:
  - new surface: T4-M3b, T4-M3c, T9-M1, R16, R10, R9 and the six T3 mutants;
  - R6: pre-existing `ScanOracle` `neutralShapes` only (by design, no program shape);
  - R11: pre-existing `ScanGen` in the shipped tree. The new surface was observed only under a reverted probe; quote the probe's failing lines. Also state the masking hazard: every new module imports `ScanGen` through `ScanUnroll`.
- **R12's Iverson arm** has a distinguishing C1 entry but no mutation cycle.
- **Not covered, production-only** (hand fixtures stay): `T4-M5`, `T4-M3d`, R2, R3/R15, R5, R7, R8, R13 (`route`), R14 (NaN / `-0.0`; `compareBindings` normalises zero bits). Also bool / Iverson / pad / unary / nonlinearity / affine-read / scan values (language-widening slice), and a real heterogeneous Core leg (own slice).
- **Deviations 1-4**, plus deviation 5: refusal comparison over corpora with several refusals is membership only, against design section 5's single-refusal restriction. Give the count of C1 programs with two or more predicted refusals, and say that a spurious extra predicted refusal is undetectable there.
- **Counts:**
  - 62 `parity` guard lines covering 55 distinct program instances on four legs;
  - the T4 "60 flips" are 60 guard lines, 53 distinct instances;
  - 2 rows stay `threeLegParity` (`maxReadsMax`, `minReadsMin`);
  - 3 rows are `unsupportedNumericalProfile nonFiniteIntoReal`;
  - refusal-parity rows by constructor.
- **Re-expressed programs.** "22 distinct" in 39fdf0e8 counts donor names:
  - 14 are single-sort;
  - 8 are mixed, all copy-form Bellman twins;
  - about 12 structural shapes in dispatch 2;
  - the not-expressible donor list from the T4b report (f32 `belP1d`, affine-read `belP1p`/`belP3p`/`B[i+1]`, `-inf` `Tr`, predicate/relu/Iverson/scan/`route`/NaN rows, `nbScat`).
- **D4 (stratified Core).**
  - Cross-statement scheduling is not checked.
  - Core consumes the predictor's `stmtSorts`, so it does not check the sort assignment; only the native legs do, and for bare copies they cannot tell the difference.
  - Core is not run when a later group reads any non-finite cell of an earlier target (checked per tensor, so conservative).
  - Later or unrelated targets enter as zero placeholders, which is sound only because `checkOrder` runs first.
- **D5.** A non-finite cell read by a real statement is classed `unsupportedNumericalProfile nonFiniteIntoReal`. The legs are `.unavailable` there and native bits are not compared.
- **Predictor scope.**
  - Real/bool sorts are not compared with production even where production publishes a `real` entry.
  - `stmtSorts` is checked only by hand rows and, indirectly, by native values.
  - The repeated-free-axis slot `Y[a,a]` is not modelled.
  - The `l == c` conjunct of `classifyRefusal` is not exercised.
  - The accepted path depends on `classifyRefusal`'s sentinel.
- **`checkMixedProfile`** checks occurrence-level envelopes only (no statement or collection bounds as `checkProfile` has), and its rejection arm is exercised by no row unless I4 is done.
- **Evidence.**
  - Value rows were hand-derived and passed on their first build, so there is no printed-then-pinned RED.
  - Negative controls: one all-real doctor (5 programs), four `feed` controls, three doctored-refusal controls.
  - No manifest mutant on `classifyRefusal`, `coreLeg` or `checkMixedProfile`.
- **Typed path.** `compareSortedSource` still refuses mixed groups as `mixedSorts` and still reports the false `nativeFailure` on the three D7 shapes. Both are pinned as contrast, not fixed.

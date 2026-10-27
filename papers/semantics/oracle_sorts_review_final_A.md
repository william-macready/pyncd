FINDINGS (0 merge-blocking, 2 Important, 9 Minor)

# Oracle per-tensor sorts: final whole-branch review, lens A (independence and soundness)

Range 67af0367..3a83d69d (8 commits). Read-only review: I read the whole-branch diff, the plan, design, facts, ledger and mutation results, and I read in full the new modules `OracleSortRules`, `OracleSortRulesTest`, `OracleMixedFixtures`, `OracleMixedDifferential`, `OracleMixedEval`, `OracleMixedEvalTest`, `OracleMixedRefusalTest` and `OracleMixedValueTest`. I also read `ScanUnroll.oracleNeutral`, `Oracle.checkOrder`/`runWith`, `Diagnostics.compareTensors`, `SortedDifferential.compareBindings`/`checkSortedProfile`, and `NumericalProfile.checkProfile`/`checkFiber`/`checkOccurrence`. I ran no builds.

## Merge-blocking

None.

## Verified clean (no finding)

- **Forbidden-identifier grep** over the 8 new test modules prints nothing. The only production observations are `compileToScheduled`, `validateScheduled` and `.algebras` (in `productionVerdict`) and the native legs (`runNative`). `oracleNeutral` is the only shared rule. It is written independently of `Stmt.isSortNeutral` (its own case split, and `oracleIdxUids`/`oracleSlotUids` instead of `axisUids`/`idxAffineForm`).
- **Library diff** is exactly what the plan allows:
  - `Oracle.lean`: 4 lines change, and the only change is dropping `private` on `slots`, `destination`, `assignments` and `checkOrder`. The spacing is restored, and no body changed.
  - `NumericalProfile.lean`: one added constructor, `Unsupported.nonFiniteIntoReal (site : Site)`, with a doc comment. It is purely additive. No exhaustive `match` on `Unsupported` exists (grep found no arms for `coreNotComplete`, `receipt`, `oracleUnavailable`, `rec` or `casesOn`), and `DecidableEq`/`Repr` are still derived.
  - The typed path is untouched: `SortedDifferential.lean`, `Carrier.lean`, `Oracle.runWith`, `compareSortedSource` and `SortedClassification` (7 constructors) are not in the diff.
- **Core leg independence:**
  - `coreLeg` takes `snapshot`, `admitted`, `p`, `order` and `feed`, but never the `runMixed` result. Later groups read the Core leg's own earlier outputs (`fed`).
  - `feed` and `doctor` default to identity. Only the two labelled negative-control blocks pass them (`runDoctored`, `runFed`).
  - The zero placeholders for later or unrelated targets are never read: `coreLeg` runs only after `runMixed` succeeded on the same `order`, and `Oracle.checkOrder` rejects any read of a declaration that is not earlier (`dependencyNotEarlier`).
- **Classification soundness:**
  - `fourLegParity` is produced only on the arm where `coreObs = some cs`, `compareTensors` (Core against oracle, all non-input tensors) returns `.agreement`, the profile is ok, and both legs are `.agrees` under `compareBindings`. That comparison is bit-wise, with only the documented zero-bit normalisation.
  - `threeLegParity` has a single producer, `coreObs = none`, which only the non-finite early return creates.
  - Every value row pins the exact class string (`parity` requires `classOf f == four` plus Core cells). So a four-leg row that degraded to three-leg would fail its guard.
- **Refusal side:**
  - `agrees` compares tropical entries in both directions.
  - C3 rows pin `p.refusals == [e]` exactly, including the payload, so the exact-one-refusal rows are not membership checks.
  - C4 fails loudly on any unmodelled production constructor.

## Important (not merge-blocking; recommended before merge, cheap)

### I1. `coreLeg` decides "not run" from the Core leg's OWN outputs and throws away the prefix it already computed (ledger T5 minor; I upgrade it)

- **Where:** `OracleMixedDifferential.coreLeg`, specifically `if ... ∈ nonFinite then return none`, together with `match t.values.mapM (... | some (.fin q) => some q | _ => none)`.
- **Why it matters:** a target joins `nonFinite` when the Core leg's own observation of it has a `±inf` cell or a `none` (unobserved) cell. Suppose a Core defect turns an intermediate cell non-finite or leaves it unobserved where the oracle has a finite value, and a later group reads that tensor. Then the row becomes `threeLegParity "core not run: non-finite intermediate"` instead of `referenceDiscrepancy`.
  - The early `return none` also discards the targets Core did run. On the two shipped three-leg rows (`maxReadsMax`, `minReadsMin`), Core's `M` cells are computed and never compared. That is a dropped check, against Review Focus 5 and Rule 12.
  - The note "core not run" is also inaccurate: Core ran up to the blocked target.
  - This is not blocking today, because every four-leg row is pinned exactly and only those two rows are three-leg. But `compareMixedSource` is meant to be the check later slices (B5, in-scan collection) run against, and there a `threeLegParity` would silently absorb a Core disagreement.
- **Fix (about 15 lines, test-side, no library rebuild):**
  - When stopping, return the prefix observations (for example `.ok (.partial observed)` or a pair).
  - Compare the prefix with the oracle's tensors for the same declarations, using `compareTensors` on the filtered lists. Classify a disagreement as `referenceDiscrepancy`.
  - Mark "not run" only for the remaining targets.
  - Also decide non-finiteness from the oracle's cell class, or require Core and the oracle to agree on it. That decides only whether Core runs, so no oracle value flows into Core.
  - Add one guard in which `feed` cannot reach the defect but a Core-side non-finite prefix differs. Alternatively, assert that the prefix comparison ran on `maxReadsMax`.

### I2. The one allowed shared import couples the new surface to `ScanGen`'s build, and that is why R11 is masked

- **Where:** `OracleSortRules` imports `Eval.PropertyOracle.ScanUnroll` only for `oracleNeutral`, and `ScanUnroll` imports `Eval.PropertyOracle.ScanGen`.
- **Why it matters:** under the R11 production mutant, `ScanGen`'s elaboration-time guard fails first. Every new module sits downstream of it, so none of them is built.
  - Detection in the shipped tree is intact (Tests are red).
  - However, the design bar for R11 is "V + P", and the new surface's kill is not reproducible from the manifest. It was observed only under a temporary, reverted probe (mutation results, R11 row).
  - The same coupling will hide the mixed oracle's diagnosis for any future production defect that also trips `ScanGen`. This is a build-graph form of the "independence" problem: the verdict exists, but it cannot be observed.
- **Fix (one small test-side move plus one mutation cycle):**
  - Move `oracleNeutral`, `oracleIdxUids` and `oracleSlotUids` into a leaf test module that imports only `LeanNCD.DSL.Ast`, for example `Eval.PropertyOracle.Neutral`.
  - Import it from both `ScanUnroll` and `OracleSortRules`. The `ScanOracle` agreement guard keeps working unchanged.
  - Re-run the R11 manifest entry and replace its `expect` with a new-surface line.
  - If this is not done, the record must state plainly that R11's "V + P" is met only under the probe. The mutation results file already says so, so this item is not blocking.

## Minor

- **M1. The cast-legality key is not independent of production.** It is "keyed on the destination's entry; a destination with no entry is unchecked" (`predict.castRefusals` and `destSort`). The design adopted this rule after reading `checkSortCasts` ("corrected after the builder check"). The vote and neutrality rules are independent, but this one is aligned to production by construction. P therefore cannot detect a defect in WHICH sort keys the cast check, only in the accept and refuse arms (`T4-M3b`/`T4-M3c`). The single-writer "own annotation" arm has the same origin (audit section 1(a)). Fix: say this in the record's independence section.
- **M2. Shared inputs are checked only by the native legs and hand rows.**
  - `runMixed` and `coreLeg` both take `Prediction.stmtSorts` from the predictor. So a predictor error in the per-statement sort is caught only by the native legs and by the hand `ranIn`/`sortsOf` guards. The P corpus (`agrees`) never compares `stmtSorts`, real vs bool, or any non-tropical entry.
  - `runMixed` also reuses `Oracle.destination`, `slots`, `assignments`, `lookup` and `checkOrder`. So `OracleMixedEvalTest` (a), "agreement with `runWith`", checks the sort arithmetic only, not the indexing. Indexing is checked independently by Core (`runSourceAt`) and the native legs.
  - Fix: state both points in the record. No code change is needed; the doctored-prediction control already shows that the legs catch a wrong `stmtSorts`.
- **M3. `checkMixedProfile` is weaker than `checkProfile`.** It omits the summation bounds that `checkProfile`/`checkFiber` enforce (`partialFiber`, `fiberAbsoluteBound`, `partialStatement`, `statementAbsoluteBound`, `partialCollection`, `collectionAbsoluteBound`) and all receipt re-checks of the oracle's occurrences (occurrence count, assignment, read coordinate). This cannot produce a false parity: every non-input cell passes `checkExt`, so the exact value is a representable integer, and parity requires equal bits. It can only turn an f64 rounding difference into a false `nativeDiscrepancy`. The docstring ("exactly as `NumericalProfile.checkProfile` does") is accurate per occurrence but invites over-reading. Fix: add one docstring sentence saying the summation and collection bounds and the receipts are not checked, and say the same in the record (ledger T4 item).
- **M4. The native legs compare only `.output` tensors.** `NativeLegs` binds only role `.output`, so the `tDef` intermediates in chains (`chain3`, `chain4`, `castMax`, `launder`, ...) are compared only oracle-vs-Core. "`fourLegParity` means ... all agree" (the `MixedClassification` docstring) therefore means "agree on outputs" for the native legs. This is inherited from the typed path. Fix: add a docstring clause and say it in the record.
- **M5. Stale comment in `OracleMixedValueTest`.** The comment before `#guard parity (bellman .max .max)` says "here Core is not run". Since T5 that guard asserts `fourLegParity` and Core cells. Fix: delete "here Core is not run" (and the T4-era wording).
- **M6. `refusalLeg` reports the wrong reason on the predicted-accept arm.** In `compareMixedSource` it is used on the predicted-accept `other` arm (a `nativeUnavailable` or `refusalMismatch []` row). There, a leg that accepted is recorded as `.failure "accepted although a refusal was predicted"`, although no refusal was predicted. The text in `MixedRun.legacy`/`checked` is misleading. Fix: use a separate label on that arm, for example `.failure "accepted; other leg did not"`.
- **M7. Deferred minors from the ledger (none must be fixed before merge):**
  - **T1 (`Y[a,a]`):** the predictor treats it as bare, while production treats it as non-bare. If it is ever hit, it surfaces loudly as `refusalMismatch [] "multiWriterScatter"`, not silently.
  - **T2:** the `l == c` conjunct is unexercised. Fix: add one `classifyRefusal` row on a synthetic `NativeRun` whose legs carry different constructors, or record it as unexercised.
  - **T3** (fixture-index brittleness) and **T4** (unpinned item list) are cosmetic.
  - **Also unexercised:** the predicate-destination multi-writer branch of `predict`. `sortOfGroup` returns `bool` and never raises a vote refusal there, and no corpus program has two writers into a predicate. Record it as an untested claim.
- **M8. `File.lean:NNN` in shipped text.** `papers/semantics/oracle_sorts_ledger.md` contains "`ScanGen.lean:246` guard", which breaks the plan's Global Constraint "No `File.lean:NNN` in any shipped text". Fix: name the guard by symbol or by a short quote.
- **M9. Docs claim the record exists and the slice has landed.** The `leanncd/AGENTS.md` entry-point row points at `../papers/semantics/oracle_sorts_record.md`, which does not exist yet. The `additive_s3b_record.md` and `additive_s3bii_record.md` updates say "landed on local main" and "CLOSED ... on local main". Fix: make sure T6 writes the record before the merge commit, so these links and claims are true when they land.

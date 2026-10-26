# Oracle per-tensor sorts and coverage: implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox syntax. Every brief opens with the shell-harness preamble in `.claude/skills/new-slice/SKILL.md`.

**Goal:** mixed-sort and copy-form Source programs get an independent oracle verdict (value parity or predicted-refusal parity), and re-introducing each defect in design section 4 flips an oracle classification or an agreement-corpus guard, observed by a mutation manifest.

**Architecture:** all new rule tables, the heterogeneous evaluator and `compareMixedSource` live test-side (`leanncd/test/Semantics/`), because a library module cannot import test code and production must not import the independent rules (design D8). A rule predictor states sort/vote/cast/refusal rules from the spec; production is observed through the real pipeline (`compileToScheduled` then `validateScheduled`), never through its rule helpers. Library edits are three: un-private four `Oracle` helpers (T3) and one additive `Unsupported` constructor (T4).

**Spec:** `papers/semantics/oracle_sorts_design.md` (approved 2026-10-26; D1-D8 fixed). Evidence: `oracle_sorts_audit.md`, and `oracle_sorts_plan_facts.md` (every value below marked "observed" is from its sections 0 and 5; base 1b8bfc9a). T0 (native legs accept mixed programs) is DONE: PASS, facts section 0.

## Global Constraints

- Every fixture tensor is `typedTensor .f64` (`checkStructure` requires f64). Fixtures stay inside the Source sublanguage: bare-index monomials, no bool decl, no Iverson/unary/nonlinearity/affine read/scan in any VALUE row. The predictor corpora (pipeline level, no values) may use relu, Iverson, predicate decls, colliding and affine write slots.
- Same refusal = same `CompileError` constructor NAME (payload names are not compared). The predictor never encodes the order production raises refusals in: it returns every refusal the spec says applies; a program with exactly one is checked for equality, with several only for membership (design section 5).
- Forbidden in new test modules (grep guard, must print nothing): `isSortNeutral|ownAlgebra|writerVotes|writerSort|scanStateSorts|scanStateAlgebra|scheduleAlgebras|checkSortCasts|checkWriterGroup|desugarMultiWriters|collectorStmt|boolReadCast|gatherCast|declAlgebra|Stmt\.algebra|AggOp\.algebra|axisUids|Combine\.`. Allowed: `validateScheduled`, `.algebras`, `.algebraOf`, `ScanUnroll.oracleNeutral` (import `Eval.PropertyOracle.ScanUnroll`).
- Typed path untouched: `Oracle.runWith`, `Carrier.lean`, `compareSortedSource`, `SortedClassification` (7 constructors, printed forms) keep their shapes (~63 guards print them).
- No `File.lean:NNN` in any shipped text. Each dispatch <= ~60 turns, context <= ~250k (Rule 6); one background build at a time, wait for the notification, no `pgrep` monitors. Execution target <= ~55M tokens (budget 175M).
- Each new test module is added to `[[lean_lib]] name = "Tests"` `globs` in `leanncd/lakefile.toml`; build one with `bash leanncd/scripts/lake-build.sh <leanncd-dir> +Semantics.Module`.

## Deviations from the design (author's calls; report them in the record)

1. D3 said "append constructors to `SortedClassification`". `compareMixedSource` must call the test-side predictor, so it cannot live in the library; its classification is a NEW test-side `MixedClassification`. The existing seven stay unchanged by construction; D3's intent (refusals classified, not hidden) holds.
2. R6 (colliding-LHS) has no program shape; the existing `neutralShapes` guard in `Eval.PropertyOracle.ScanOracle` is expected to be its killer, not new surface. The manifest row lists both; the record states which fired.
3. R10's design shape was wrong (facts 5(c)): `T:=maxreduce(N)` beside `T:=minreduce(B[a,b])` is ACCEPTED. The killing shape is an all-neutral max+min group over a min-plus `N`, max writer first. Likewise R16 is a vote conflict between two NON-neutral voters (facts 5(b)).
4. Interim classification `threeLegParity` between T4 and T5 (oracle, legacy, checked agree; Core not yet run); T5 flips finite rows to `fourLegParity`.

## Review Focus (each line has a test in the owning task)

1. A neutral copy whose annotation disagrees with its group's sort runs in the GROUP's sort (min copy beside a sum writer runs as sum; `bellman .max .min` is accepted and runs as max) (T3, T4).
2. A tropical cell never written (`-inf`/`+inf`) read by a real statement: `unsupportedNumericalProfile nonFiniteIntoReal`, never silently compared (T4).
3. A vacuous corpus: a claimed-killed mutation with no distinguishing entry (the contracted-axis conjunct was once caught by hand shapes only) (T1 self-check guard).
4. A refusal constructor production raises that the predictor does not model: the corpus fails loudly naming it, never skips (T1).
5. `threeLegParity` miscounted as four-leg, or a Core leg skipped silently (T4, T5, record counts).

## File map

| File | Change | Task |
|---|---|---|
| `test/Semantics/OracleSortRules.lean` | NEW: `MSort`, `Prediction`, `predict`, `productionVerdict`, `agrees` | T1 |
| `test/Semantics/OracleSortRulesTest.lean` | NEW: corpora C1-C4 (guards only) | T1 |
| `test/Semantics/OracleMixedFixtures.lean` | NEW: snapshot builder cloned from facts section 5 | T2 |
| `test/Semantics/OracleMixedDifferential.lean` | NEW: `MixedClassification`, `MixedRun`, `classifyRefusal`, later `compareMixedSource` | T2, T4, T5 |
| `test/Semantics/OracleMixedRefusalTest.lean` | NEW: refusal-parity rows | T2 |
| `LeanNCD/Semantics/Source/Oracle.lean` | remove `private` from `slots`, `destination`, `assignments`, `checkOrder` (no body edit) | T3 |
| `test/Semantics/OracleMixedEval.lean`, `OracleMixedEvalTest.lean` | NEW: `runMixed`, agreement guards | T3 |
| `LeanNCD/Semantics/Source/NumericalProfile.lean` | add `Unsupported.nonFiniteIntoReal (site : Site)` (additive; no exhaustive `match` on `Unsupported` exists, facts section 2) | T4 |
| `test/Semantics/OracleMixedValueTest.lean` | NEW: value rows | T4, T5 |
| `leanncd/lakefile.toml` | add the 7 new modules to `Tests` globs, beside `"Semantics.SourceSortedAuditTest"` | each |
| `papers/oracle_sorts_mutations_post.json` | exists (8 entries, `--check` OK, no `expect` yet); T3 adds 5 test-side mutants; T6 fills `expect` | T3, T6 |

## Task 1: rule predictor and agreement corpora (test-side, no library rebuild)

**Interfaces — Produces** (in `OracleSortRules.lean`, namespace `LeanNCD.OracleSorts`):
- `inductive MSort | real | maxPlus | minPlus | bool deriving DecidableEq, Repr`
- `structure Prediction where refusals : List (String × String); sorts : List (String × MSort); stmtSorts : List MSort` (`refusals` = (constructor name, tensor name) pairs the rules say apply; `[]` means accepted; `sorts` = every declared tensor; `stmtSorts` = the sort each input statement RUNS in, aligned with the input list; both meaningful only when `refusals = []`).
- `def predict (decls : List Decl) (stmts : List Stmt) : Prediction`
- `def productionVerdict (decls : List Decl) (stmts : List Stmt) : Except (String × String) (List (String × MSort))` (clone of the observed `verdict` helper, facts section 4: `TLProgram.compileToScheduled`, `.run 0`, `validateScheduled`; error = constructor name from `repr` plus first string payload; ok = `.algebras` entries mapped to `MSort`).
- `def agrees (p : Prediction) (v : Except (String × String) (List (String × MSort))) : Bool`: `p.refusals = []` requires `v = ok m` with tropical entries of `m` equal to the tropical entries of `p.sorts` in BOTH directions (real/bool carry no entry); one predicted refusal requires `v = error` with the same constructor name; several require membership.

**The spec the predictor states** (written from the design/decision note, NOT from production; reuse only `oracleNeutral` for neutrality):
- Annotation sort: `sum` real, `max` maxPlus, `min` minPlus; a predicate destination is bool.
- A tensor with ONE plain writer has that writer's OWN annotation, even if the writer is neutral. A tensor with several plain-assign writers votes: non-neutral writers vote their annotation; neutral writers abstain while any non-neutral writer exists; if none is non-neutral, neutral writers vote their non-`sum` annotations (`sum` abstains); no vote = real; all votes equal = that sort; otherwise refusal `multiWriterAlgebra T`. Only tropical groups get a sort-map entry. Abstaining neutral copies run in the group's sort.
- Any group containing a scatter or a non-bare (affine) write slot: refusal `multiWriterScatter T` (precedence over vote conflicts is NOT modelled; both are returned).
- A statement whose own annotation is tropical and whose nonlinearity is not identity: refusal `tropicalNonlin`.
- Cast legality is keyed on the DESTINATION tensor's entry: a destination with no entry is unchecked; a bare read of a tropical source `a` into destination sort `k` is refused `sortCastUnsupported dst src` iff `k = bool` or (`k` tropical and `k != a`); Iverson and unary factors are unchecked. A source's sort is its entry, else its declaration (bool for predicate, else real). Decision A: direct max<->min refused, the one-real-copy form accepted.

- [ ] **Step 1: observe production on the corpus before writing `predict`.** Write `productionVerdict` and `corpusC1`, print every verdict (constructor histogram). Expected: only `multiWriterAlgebra`, `multiWriterScatter`, `tropicalNonlin`, or accept. If any other constructor appears, STOP and report it (Review Focus 4); do not extend the model silently.
- [ ] **Step 2: write the failing corpus guards**, then `predict` until they pass:
  - C1 pair corpus: 7 shapes x 3 annotations = 21 writers over one tensor `Y` (shapes: bare copy, contracted copy, relu copy, Iverson-only copy, colliding slot `Y[i+j]`, affine single-axis `Y[2i+1]`, plus a bare contracted two-axis copy); all 441 ordered pairs plus the 64 ordered triples over {sum contracted, max neutral, min neutral, max contracted}: `agrees (predict ..) (productionVerdict ..)` for all. Donor for the `Decl`/`Stmt` shapes: `s3bSched`/`s3bStmt` @ `test/Eval/Plan/CompileTest.lean` (clone, change the shape).
  - C2 reader corpus: source sort {real, maxPlus, minPlus, bool (predicate input)} x reader {sum, max, min, predicate-destination}: 16 one-read programs; plus the laundered pair (`M:=maxreduce(Z); R[a]:=M[a]; O:=minreduce(R)` accepted, direct `O:=minreduce(M)` refused `sortCastUnsupported "O" "M"`) and readers of a max group, a real group and a conflicting group.
  - C3 hand rows (each with the OBSERVED production verdict, facts section 5): R11 both orders and mirror (`Y:=Z[a,b]` + `Y:=maxreduce(X[a])` accepted real group, no entry; `Y:=maxreduce(Z[a,b])` + `Y:=X[a]` accepted maxPlus); R16 (`Y:=Z[a,b]` + `Y:=maxreduce(Q[a,b])` and `maxreduce`+`minreduce` contracted, both `multiWriterAlgebra "Y"`); R10 max-first and min-first (`N:=minreduce(Z[a,b]); T:=maxreduce(N[a]); T:=minreduce(X[a])` refused `multiWriterAlgebra "T"` in both orders); single-writer neutral copy `T:=maxreduce(X[a])` read by `minreduce` (`sortCastUnsupported "O" "T"`), read by a sum statement (accepted, `T` maxPlus).
  - C4 self-check guards (vacuity): C1 contains an accepted real group with a neutral tropical copy; an accepted all-neutral maxPlus group; a `multiWriterAlgebra` pair of two contracted non-neutral writers; a relu x max pair; a colliding-slot pair; the set of observed production constructors is a subset of the modelled ones; each of {accept real, accept maxPlus, accept minPlus, each modelled refusal} occurs at least once.
- [ ] **Step 3:** run the forbidden-identifier grep over the two new files (prints nothing); build `+Semantics.OracleSortRulesTest`; commit `test(oracle): independent sort/vote/cast rule predictor and agreement corpora`.

**Cost:** ~25 corpus guards + ~25 hand rows, 0 library rebuilds, ~45 turns. Cycles run in T6.

## Task 2: refusal harness and refusal-parity rows

**Interfaces — Consumes:** T1 `Prediction`, `predict`, `MSort`; `runNative`, `NativeRun`, `LegacyOutcome.failure`, `CheckedOutcome.preparation`, `LegResult` @ facts section 2. **Produces:**
- `OracleMixedFixtures.lean`: `T`, `ext`, `mk (ts : List T) (stmts : List Stmt) : SourceSnapshot`, `st`, `zR`, `rd` and the observed input vectors (facts section 5: `X=[20,2,3,40]`, `Z[a,b]=[-5,-4,-3,5,6,7,15,16,17,25,26,27]`, `Q=B=[1,9,2,3,8,4,7,5,6,0,10,11]`, `W8=[1,0,2,3,4,5,6,7]`; axes `a` 4, `b` 3, `k` 8, declaration ordinals 0,1,2).
- `inductive MixedClassification | fourLegParity | threeLegParity (note : String) | refusalParity (ctor : String) | refusalMismatch (predicted : List (String × String)) (observed : String) | referenceUnavailable (reason : String) | referenceDiscrepancy | unsupportedNumericalProfile (reason : Unsupported) | nativeUnavailable | nativeFailure (legacy checked : LegResult) | nativeDiscrepancy (legacy checked : LegResult) deriving Repr` (all declared now; only the refusal pair is produced here).
- `def classifyRefusal (p : Prediction) (run : NativeRun) : MixedClassification`: when `p.refusals != []`, legacy `.failure` whose text carries `compile failed:` and a predicted constructor name AND checked `.preparation` carrying the same name give `refusalParity ctor`; either leg observed (accepted) or a constructor outside the predicted set gives `refusalMismatch`. When `p.refusals = []` and a leg refused, `refusalMismatch [] ctor`.

- [ ] **Step 1: write the failing rows** in `OracleMixedRefusalTest.lean` using `#guard` on `classifyRefusal (predict ..) run` printed via `repr` (clone `classOf`/`#guard_msgs` style from `SourceSortedDifferentialTest`; donor programs are the facts section 5 builder shapes): R16 (two variants) `refusalParity "multiWriterAlgebra"`; R10 max-first and min-first `refusalParity "multiWriterAlgebra"`; cast decision A direct `refusalParity "sortCastUnsupported"` and, as its accept neighbour, the laundered form `predicted []` with both legs observed (not a refusal row: guard that `classifyRefusal` reports `refusalMismatch [] ..` ONLY when a leg refused, so the laundered form yields a non-mismatch); single-writer neutral copy read by `minreduce` `refusalParity "sortCastUnsupported"`; D7 three shapes (scatter group, two affine writers, affine + bare writer) each `refusalParity "multiWriterScatter"`, where `compareSortedSource` today reports a false `nativeFailure` (facts 5(e); pin the old output once as the contrast, in a comment-free `#guard`).
- [ ] **Step 2: negative controls.** A deliberately doctored `Prediction` (R16 predicted accepted; D7 predicted `sortCastUnsupported`) gives `refusalMismatch`; a doctored accept prediction on the accepted laundered program with `refusals := [("multiWriterAlgebra","M")]` also gives `refusalMismatch`.
- [ ] **Step 3:** grep guard, build `+Semantics.OracleMixedRefusalTest`, commit `test(oracle): predicted-refusal classification and refusal-parity rows`.

**Cost:** ~14 rows + 3 controls, 0 library rebuilds, ~40 turns.

## Task 3: heterogeneous evaluator (one library visibility edit)

**Interfaces — Consumes:** `Oracle.slots`, `destination`, `assignments`, `checkOrder` (made public here; pure visibility), `Oracle.coordinates`, `lookup`, `cellCount`, `AdmittedSource`/`AdmittedStatement.original`, `ExtVal`. **Produces** (`OracleMixedEval.lean`):
- Hand-restated ops over `ExtVal`, no `Semiring`: `MSort.zero/one : MSort -> ExtVal` (real 0/1; maxPlus `-inf`/`0`; minPlus `+inf`/`0`), `MSort.add`, `MSort.mul` (real `+`,`*`; maxPlus `max`,`+` with `-inf` absorbing; minPlus `min`,`+` with `+inf` absorbing), real <-> tropical read cast = identity on `fin`.
- `inductive MixedEvalError | unavailable (u : Oracle.Unavailable) | nonFiniteIntoReal (declaration : Nat) (coordinate : List Nat) | inconsistent (message : String)`; `structure MixedOccurrence` (statement `original`, destination coordinate, `assignment`, running sort, read values : `List ExtVal`); `structure MixedResult := (tensors : List (Oracle.Tensor ExtVal)) (occurrences : List MixedOccurrence)`.
- `def runMixed (admitted : AdmittedSource) (p : Prediction) (order : List Nat) : Except MixedEvalError MixedResult`: each statement runs in `p.stmtSorts[original]`; an occurrence is `mul` over its reads, the statement's occurrences at a cell combine with that sort's `add`, statements writing one tensor combine with the tensor's sort `add`; empty product `one`, empty sum `zero`; a `±inf` read by a REAL statement is `nonFiniteIntoReal` (D5), a min-plus statement reading a max-plus tensor (or the reverse) is `inconsistent` (the predictor refused it; reaching it is a harness bug).

- [ ] **Step 1: edit** `Oracle.lean` (remove four `private`s); build the library target `+LeanNCD.Semantics.Source.Oracle` and confirm no other file changed meaning (`git diff --stat` shows 4 lines).
- [ ] **Step 2: write failing guards** in `OracleMixedEvalTest.lean`: (a) agreement with the typed `Oracle.runWith (Carrier.real|maxPlus|minPlus)` on the homogeneous fixtures `bellman .max .max`, `bellman .min .min`, a real contraction, `collide`, `strided`, `product` (clone the Source fixtures from `SourceSortedDifferentialTest`; compare `ExtVal` cell lists); (b) the observed mixed values on both native legs (facts section 0): `bellman .max .sum = [20,7,17,40]`, `.max .min = [20,7,17,40]`, `.min .sum = [-5,2,3,25]`, `.sum .max = [8,20,51,118]` (Review Focus 1); (c) cast cells: `M:=maxreduce(Z[a,b]); R[a]:=M[a]` gives `R=[-3,7,17,27]`, `S:=Z[a,b]; O:=maxreduce(S[a])` gives `O=[-12,18,48,78]`, laundered `O=[-3,7,17,27]`; (d) the unwritten-cell shapes return `nonFiniteIntoReal` (copy, product with `W8`, min-plus).
- [ ] **Step 3:** append 5 test-side mutant entries to `papers/oracle_sorts_mutations_post.json` (`file` `test/Semantics/OracleMixedEval.lean`; each `old` unique, `--check` OK): `one`/`zero` constant swapped for maxPlus; `add` of minPlus using `max`; abstaining neutral copy running in its own annotation instead of the group's; read cast of a tropical `-inf` treated as finite; `nonFiniteIntoReal` check removed. Targets `Semantics.OracleMixedEvalTest`; `expect` filled in T6.
- [ ] **Step 4:** grep guard, build `+Semantics.OracleMixedEvalTest`, commit.

**Cost:** ~20 guards, 5 test-side mutants (run in T6), 1 library rebuild, ~45 turns.

## Task 4: accepted path, mixed profile, non-finite class

**Interfaces — Consumes:** T1-T3. **Produces:** `NumericalProfile.Unsupported.nonFiniteIntoReal (site : Site)`; in `OracleMixedDifferential.lean`: `structure MixedRun := (prediction : Prediction) (oracle : Except String (List (TensorObservation ExtVal))) (profile : Except Unsupported (List SortedCell)) (legacy checked : LegResult) (classification : MixedClassification)` and `def compareMixedSource (snapshot : SourceSnapshot) (order : Option (List Nat)) : Except SourceDiagnostic MixedRun`.
- Flow: `admitSourceAffine snapshot true`; `predict` on `snapshot.resolved`; refusals -> `classifyRefusal` on `runNative snapshot (sorted := true)`; else `runMixed`; oracle tensors through `oracleTensorsAt id` over `Oracle.Result.mk tensors []`; mixed profile `checkMixedProfile` (test-side): per occurrence, real-sort statements use the PRODUCT envelope exactly as `NumericalProfile.checkProfile` does, tropical statements the sum-of-magnitudes envelope as `checkSortedProfile` does, every finite cell via `checkExt`; legs compared with `compareBindings` (`legOf` is private: restate its 15 lines test-side); classification `threeLegParity "core leg not run"` when both legs agree. `MixedEvalError.nonFiniteIntoReal` maps to `unsupportedNumericalProfile (.nonFiniteIntoReal site)`.

- [ ] **Step 1 (dispatch 1):** add the `Unsupported` constructor; build the library target; write failing rows in `OracleMixedValueTest.lean`: the four mixed Bellman rows and their reversed orders (`threeLegParity`), the homogeneous control `bellman .max .max` (the typed path says `fourLegParity`; here `threeLegParity` until T5), R11 four rows (facts 5(a): values `[8,20,51,118]` real group, `[20,7,17,40]` maxPlus group), (f) neutral-copy chains, (g) real<->tropical cast rows, laundered form, and the three non-finite rows (`unsupportedNumericalProfile (nonFiniteIntoReal ..)`). Implement until green.
- [ ] **Step 2 (dispatch 2):** re-express the Source-expressible existing programs named in audit section 4 (the `bellman`, `collide`, `contract`, `zeroY`, `strided`, `product` rows, `J4`/`j4m` @ `CollectEvalTest`, Bellman P1-P3, `tcopy*`, `vrSumMax`/`vrSumMin` @ `CollectPlanTest`): target >= 12 distinct programs; count and list them in the commit body. Negative control: a doctored `stmtSorts` (running a max group as sum) yields `nativeDiscrepancy`, never parity.
- [ ] **Step 3:** grep guard, build `+Semantics.OracleMixedValueTest`, commit per dispatch.

**Cost:** ~30 rows + 2 controls, 1 library rebuild, ~55 turns split in two dispatches (use `split-handoff-template.md` if dispatch 1 passes ~50).

## Task 5: stratified Core leg (K2)

**Consumes:** T4 `compareMixedSource`; `admitSourceSorted`, `coreTensorsAt`, `compareTensors`, `Oracle.Sorted`. **Produces:** `MixedRun.core : Except String (List (TensorObservation ExtVal))` (or `none` when not run) and the classification upgrade.
- For each target in dependency order, build a sub-snapshot of the statements writing that target with `agg` set to the target's sort annotation (abstaining neutral copies rewritten to the group's sort, from `Prediction.stmtSorts`), earlier targets and inputs entering as inputs with the CORE leg's own earlier outputs as rational values; run `admitSourceSorted` + `coreTensorsAt`. If any needed earlier cell is non-finite, the Core leg is not run for that row and the classification stays `threeLegParity "core not run: non-finite intermediate"` (Review Focus 5). Otherwise Core observations are compared with the oracle's by `compareTensors` and agreement gives `fourLegParity`, disagreement `referenceDiscrepancy`.

- [ ] **Step 1:** write the flip table as guards: every T4 `threeLegParity` row with finite intermediates becomes `fourLegParity`; rows reading an unwritten tropical cell stay `threeLegParity` (list them); add two chain rows with >= 3 targets and one negative control feeding a wrong earlier value (`referenceDiscrepancy`).
- [ ] **Step 2:** implement, build `+Semantics.OracleMixedValueTest`, commit. **Cost:** ~12 flips + 3 new rows, 0 library rebuilds, ~35 turns.

## Task 6: mutation bar, docs, close-out (controller-run, not an implementer dispatch)

- [ ] **Step 1:** fill `expect` in `papers/oracle_sorts_mutations_post.json` by running each of the 8 design rows once without it and copying a distinguishing line from the observed failure; `bash leanncd/scripts/mutation-manifest.sh --check leanncd papers/oracle_sorts_mutations_post.json` passes. Run the manifest in the background (`mutation-manifest.sh leanncd papers/oracle_sorts_mutations_post.json`), results to `papers/semantics/oracle_sorts_mutation_results.md`. Bar: all 8 design rows plus the 5 test-side mutants killed; for each, record WHICH guard fired (new surface or pre-existing). A row killed only by a pre-existing guard (expected: R6 by `Eval.PropertyOracle.ScanOracle`) is reported as such; a surviving row stops the slice (Rule 12).
- [ ] **Step 2 (docs, commands not a dispatch):** `rg -n "oracle per-tensor sorts|mixedSorts" papers/semantics/additive_s3b_record.md papers/semantics/additive_s3bii_record.md leanncd/AGENTS.md leanncd/docs` and update each parked/closed claim with the not-covered list; replace the stale comment before `bellman` in `test/Semantics/SourceSortedDifferentialTest.lean` ("production refuses max + min": facts section 8); add one row to the `leanncd/AGENTS.md` entry-point table for `compareMixedSource`; check each touched AGENTS.md hook section `wc -c` <= ~3k.
- [ ] **Step 3:** controller runs the full `lake build` and `Tests` (background, wait), the forbidden-identifier grep, and `mutation-manifest.sh --check`; then two final whole-branch reviewers (Opus, findings appended to `papers/semantics/oracle_sorts_review_final_A.md` / `_B.md`): A = independence and soundness (shared helpers, predictor vs production coupling, `Unsupported` addition, typed path unchanged), B = coverage and honesty (mutation table vs design section 4, the not-covered labels, `threeLegParity` accounting, D4/D5 weakness stated). Adjudicate, write `papers/semantics/oracle_sorts_record.md` (measured tokens, rows, flips, deviations 1-4, killer per mutation), merge to local main (Rule 13), delete branch and worktree, update memory. Do not push.

## Deliberately NOT done (Rule 14)

| Item | Owner |
|---|---|
| Bool / Iverson / pad / unary / nonlinearity / affine-read / scan values in the oracle | language-widening slice (design D2) |
| NaN, signed zero (`compareBindings` normalises zero bits) | production-only hand fixtures |
| `T4-M5` (unary exemption in cast check), `T4-M3d` (real -> bool rejection), R2, R3, R5, R7, R8, R13-R15 | production-only, labelled in the record |
| Real heterogeneous Core leg (600-1000 proof lines) | own slice, on request (D4) |
| B5, in-scan collection, JAX, F2 cast bypass | unchanged owners |
| Un-privatising `ScanOracle`'s `neutralShapes`/`corpusStmts` | not needed: the predictor corpora are new |

## Risk table

| Task | Fixtures/guards | Mutation cycles (run in T6) | Library rebuild | Turns |
|---|---|---|---|---|
| T1 | ~50 | P rows of 8 | none | ~45 |
| T2 | ~17 | R16, R10, `T4-M3c` end to end | none | ~40 |
| T3 | ~20 | 5 test-side | one (visibility) | ~45 |
| T4 | ~32 | R11 end to end | one (`Unsupported`) | ~55 (2 dispatches) |
| T5 | ~15 | none | none | ~35 |

Total ~215 turns, 6-7 dispatches; the 8 design rows plus 5 test-side mutants = 13 cycles, each rebuilding dependents of `DSL/Ast.lean` or `ScheduledValidation.lean` (first full rebuild observed at ~2 min on stale oleans; warm chains ~20 s).

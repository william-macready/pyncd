# SDD ledger — plan: papers/semantics/oracle_sorts_plan.md

Worktree `.claude/worktrees/oracle-sorts`, branch `worktree-oracle-sorts`, base 67af0367 (local main). Session id c21c5e70-2d48-4d52-a766-348658fcc4d1. Briefs live in the session scratchpad.

## Pre-flight scan

| Pair / task | Produces vs consumes | Finding |
|---|---|---|
| T1 -> T2 | `Prediction`, `predict`, `MSort` -> `classifyRefusal` | consistent |
| T1 -> T3 | `Prediction.stmtSorts`, `MSort` -> `runMixed` | consistent; T3 imports OracleSortRules |
| T2 -> T4 | `MixedClassification`, fixtures -> `compareMixedSource` (same file `OracleMixedDifferential.lean`) | consistent (T2 creates, T4 appends); fixtures module shared by T2/T4/T5 |
| T3 -> T4 | `runMixed`, `MixedEvalError` -> compareMixedSource | consistent |
| T4 -> T5 | `MixedRun` built in T4, `core` field added in T5 | T4 must build `MixedRun` by named fields so T5's addition is one line; carried in T4 dispatch |
| T3 / T4 library edits | T3: 4 visibility edits in Oracle.lean; T4: one `Unsupported` constructor | disjoint files |
| T1 self | C1 counts (7 shapes x 3 = 21 writers; 441 pairs, 64 triples) | the text names 6 shapes then "plus a bare contracted two-axis copy" = 7; consistent |
| T2 self | refusal rows vs `classifyRefusal` | consistent |
| T3 self | mutants target only the test-side file | consistent |
| T4 self | two dispatches; interim `threeLegParity` | consistent |
| T5 self | flips T4 rows | consistent |

No conflicts needing a ruling.

## Log
- T1 dispatched (agent a000e897688340a9f, Sonnet, BASE 67af0367)
- T1 implemented: 9d6eca25 (DONE, ~30 turns, 129k tokens; hard gate passed: C1 histogram accepted 141 / multiWriterScatter 192 / multiWriterAlgebra 92 / tropicalNonlin 80). Reviewer dispatched (a4346b309c8c28cc5).
- Task 1: complete (commits 67af0367..9d6eca25, review clean). Minors (deferred, for final reviewers/record): repeated-free-axis slot (Y[a,a]) non-bare in production, unmodelled+unexercised by predictor; C4 first guard comment says 'contracted' but is looser; real/bool sort parity and stmtSorts not compared with production (only hand rows) — state in record; aggOf/nonlinOf duplicate private helpers in rules file (trivial); R6 NOT killed by C1 (killer = ScanOracle neutralShapes, deviation 2); multi-refusal membership cannot detect a spurious extra predicted refusal.
- T2 implemented: 90cac59a (DONE_WITH_CONCERNS, ~25 turns, 116k tokens). Ruling: classifyRefusal's sentinel referenceUnavailable for predicted-accept+both-legs-accept stays — compareMixedSource only calls classifyRefusal when p.refusals != [], so the sentinel is never a verdict on accepted rows — cost if wrong: T4 must not route accepted rows through it (carried in T4 brief). Reviewer dispatched (a2bc4f11da6261286).
- Task 2: complete (commits 9d6eca25..90cac59a, review clean). Minors (deferred): classifyRefusal sentinel hazard (T4 must branch on p.refusals.isEmpty first); no row exercises the 'l == c' (legs refuse with different constructors) conjunct; isMismatch substring guard at RefusalTest:310 redundant.
- T3 implemented: 10b654fc (DONE_WITH_CONCERNS, ~35 turns, 144k tokens). Concerns: runMixed takes extra stmts param (T4/T5 pass snapshot.resolved.stmts); nonFiniteIntoReal payload = read tensor decl + coordinate; mutant 3 killed via 'inconsistent' not value diff. Reviewer dispatched (a2... see next line).
- Task 3: complete (commits 90cac59a..10b654fc, review clean). Ruling: Oracle.lean edit dropped the space after the name on 4 lines (def slots(origin ...) — semantically inert but a formatting regression in production; restore in T4 dispatch 1 prelude (library rebuilds there anyway); also add the missing maxPlus 'one' mutant (brief said one/zero) — cost if wrong: one extra T6 cycle. Minors deferred: ownSortOf duplicates OracleSortRules annotation table (dedupe while T4 touches); fixture-index brittleness in nonFiniteIntoReal guards.
- T4 dispatch 1: 3350bd62 (prelude: Oracle.lean spacing restored, T3-E6 maxPlus-one mutant added -> 14 manifest entries, ownSortOf deduped) + 90823aeb (accepted path, 53 guards, full build green 8834 jobs); DONE_WITH_CONCERNS, 42 turns, 171k tokens. Concerns: non-finite rows legs report LegResult.unavailable (D5, as typed path); predicted-accept + leg runtime failure -> refusalMismatch [] "runtime" (loud, naming imprecise).
- T4 dispatch 2: 39fdf0e8 (22 value programs + 7 refusal/reader programs, 119 guards, negative control via optional 'doctor' arg on compareMixedSource; full build green 8834) DONE_WITH_CONCERNS, 30 turns, 131k tokens. Concerns: many programs are shape twins; donors adapted to Source sublanguage; doctor param widens signature T5 touches; RED not observed for re-expression rows (values derived by hand). T4 whole-task reviewer dispatched.
- Task 4: complete (commits 10b654fc..39fdf0e8, review clean). Record items: '22 programs' overstates — reviewer counts 12 structurally distinct in dispatch 2 (~18 with dispatch 1), not-expressible list lives in task-4b-report (carry into record); checkMixedProfile checks only occurrence-level envelopes (checkProfile also checks statement/collection bounds) — state in record; non-finite rows' legs are unavailable and unpinned; negative control only all-real doctor; refusalMismatch [] "runtime" naming. Carried to T5 dispatch: fix stale MixedClassification doc comment (OracleMixedDifferential.lean ~19-21), pin legs on 3 non-finite rows.
- T5 implemented: 03e73e64 (143 guards; 60 rows flipped threeLegParity->fourLegParity; maxReadsMax and minReadsMin stay three-leg; chain rows 3 and 4 targets; 4 wrong-earlier-value controls -> referenceDiscrepancy; MixedRun.core : Option (Except ..); doctor kept; defaulted feed test hook; full build green 8834) DONE_WITH_CONCERNS, 38 turns, 162k tokens. Reviewer dispatched.
- Task 5: complete (commits 39fdf0e8..03e73e64, review clean). Minors: coreLeg early 'return none' discards computed prefix (could compare before returning); zero-placeholder soundness rests on checkOrder inside runMixed (uncommented); long docstring line. Implementation tasks done; T6 (controller) starts.
- T6 started: mutation manifest (14 entries, no expect) running in background -> scratchpad/mut1.out; AGENTS.md compareMixedSource row added (md only, no Lean edits during mutation builds)
- T6 mutation run 1 (no expect): 14/14 cycles broke+restored green. R6 killed ONLY by pre-existing ScanOracle.lean guard (deviation 2 as predicted; new C1 did not fire). R11 killed ONLY by pre-existing ScanGen.lean:246 guard, and that failure blocks every downstream new test module from building (masking) -> re-running R11 with that ScanGen guard TEMPORARILY commented out (TEMP-R11-PROBE; must be reverted: git checkout ScanGen.lean) to observe which new guards fire.
- T6: R11 probe (ScanGen guard temporarily off, REVERTED, git status clean): new killers = OracleSortRulesTest C1 #4 + C3 R11 row + OracleMixedValueTest R11 value rows. expect strings filled (R6 -> ScanOracle pre-existing; R11 -> ScanGen pre-existing in the shipped tree). Stale comment before bellman fixed (SourceSortedDifferentialTest, builds). Final manifest run (14 entries with expect) started -> scratchpad/mut3.out

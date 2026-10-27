# Oracle sorts follow-up ledger (Direct path, no plan document)

Worktree `.claude/worktrees/oracle-sorts-followup`, branch `worktree-oracle-sorts-followup`, base ad69b8dd (main, pushed). Scope agreed with the user after the oracle-sorts record: the ScanGen-masking fix first, then items 1-3 of the follow-up list. Items 4 and 5 (predictor corpus gaps, stale wording) are NOT in scope (Rule 14).

1. Leaf module for `oracleNeutral` + its two helpers, so no new oracle module imports `ScanGen`; re-run R11 and R6 manifest cycles and move R11's `expect` onto the new surface.
2. `agrees`/`classifyRefusal`: equality for programs with exactly one predicted refusal, membership counted separately (deviation 5).
3. `classifyRefusal` returns an `Option` instead of the sentinel `referenceUnavailable "accepted: .."`.
4. Manifest rows for `classifyRefusal`, `coreLeg`, `checkMixedProfile` (test-side mutants), each killed.

## Log
- Baseline: worktree at ad69b8dd, full build green (8834). Dispatch F1 (leaf module for oracleNeutral; Sonnet) launched.
- F1 done: 2f4a90cc (leaf module Eval.PropertyOracle.Neutral; ScanUnroll+OracleSortRules import it; bodies verbatim, docstring wording adjusted for forbidden grep; full build green 8835 jobs; import closure of the eight modules verified by controller: only LeanNCD.* library + Neutral). R11/R6 cycles running (followup-mut1.out).
- Prep note for F2: item 2 (equality for exactly-one-refusal programs) is ALREADY implemented in agrees; what remains is making the multi-refusal class an explicit named class (agreesStrict/agreesMember split, pinned counts) and a guard that every modelled refusal constructor is pinned by at least one strict program. Be candid with the user: residual over-prediction-in-combos stays undetectable without modelling production's order (forbidden).

# S2b T2 review (commit 8b11ff79)

VERDICT: APPROVE (no Critical/Major; 3 Minor, all documentation/robustness)

## Findings
1. Minor. The scatter guard `(sorted && rhs.agg != .sum)` is live, but it is NOT what stops a tropical scatter
   being admitted; it only fixes the refusal CAUSE. The `.scatter` arm of `admitAffineStatement` never rebinds `rhs`
   (the `let rhs := if sorted then {rhs with agg := .sum} ...` line is inside the `.assign` arm only), so without the
   guard a max scatter would reach `admitStatement`/`admitAffineWrite` with the original `.max` and be refused as
   `.unsupported .nonSum`, not admitted. Plan T2 cycle `T2-M2` ("tropical scatter admitted") therefore mis-states the
   mutant's effect; Q6 row 6 and A5 still kill it because they assert `scatterPolicy` by cause. Fix: reword the plan/docstring
   (guard pins the cause, defence in depth).
2. Minor. `sortKeys` `(snapshot.resolved.stmts[st.original]?.map stmtAgg).getD .sum` is a silent fallback. It is unreachable
   in practice (`st.original` comes from `source.statements = resolved.stmts.zipIdx.map (i,s)`, `adaptSource_statements`
   Adapter.lean:620; `stmtAgg`'s `_ => .sum` arm is only `.recurMorphism`, which `admitStatement` refuses), so no wrong
   carrier can be selected today. It would mislabel silently if admission ever grew a recurMorphism arm. Optional hardening
   (carry the agg on `AdmittedStatement`, or fail loud); not required.
3. Minor. Q6 row 5 `(admitSourceAffine (single .max)).toOption.isSome = false` pins only refusal, not the `nonSum` cause
   (plan row 12 already says so and parks the cause to T4A). Non-vacuous (flag default flipped to true makes it `true`),
   but it would also pass if the fixture were refused for another reason; rows 2-3 prove the same snapshot is admitted
   sorted, so the only difference is the agg rewrite. Acceptable.

## Questions
1. Admission.lean diff touches only `admitAffineStatement`, `admitSourceAffine`, new `stmtAgg`(private)/`sortKeys`/`admitSourceSorted`
   (hunks at old lines 902-922 only; `diff` of old/new shows 40 changed lines, all >= 902). `admitStatement` (l.655),
   `StatementFields` (l.682), `admitStatement_fields` unchanged. Carrier import is in Adapter.lean, not Admission.lean
   (Admission gets `Oracle.*` through Adapter); fine. Extra: private helper `stmtAgg` is not in the plan list (trivial).
2. sorted = false byte-identical: both new params default `false`; `{rhs with agg := .sum}` and the guard are gated on
   `sorted`; both `nonSum` sites (Admission.lean:662 `admitStatement`, :882 `admitAffineWrite`) untouched. Callers:
   `Provenance.lean:80`, `Observation.lean` via `admitIdentifiedSourceAffine`, `NativeLegs` all use the default or pass `sorted`
   explicitly. With sorted = true the rebound `rhs` (shadowing, same name) is the one passed to both downstream
   calls in the `.assign` arm (`admitStatement ... (.assign name slots rhs)`, `admitAffineWrite ... rhs`), so neither nonSum
   site sees the original agg; the original `statement` is not re-read. `Stmt` has only assign/scatter/recurMorphism
   (DSL/Ast.lean:171); recurMorphism still refused; `freeNorm`/iter slots go through the unchanged `outputForms`/
   `outputIndices` paths and `RHSExpr` has no other agg-bearing field (Ast.lean:138). nonlin check unchanged (a max statement
   with non-identity nonlin is still refused, as for sum).
3. Guard is live: it sits in the `.scatter` arm, where `rhs` is the pattern-bound ORIGINAL `rhs` (no rewrite in that arm), so
   `rhs.agg != .sum` is true for max/min and fires before the bare/affine split and before any `nonSum` site. Not dead; no
   Critical. See Finding 1 for the nuance. Sum scatter passes the guard (A6) and is admitted unchanged.
4. `st.original` is the right index: `AdmittedStatement.original` is the `i` from `source.statements` (zipIdx over
   `resolved.stmts`) and `admitSourceAffine` passes that `i` as `original`. The `getD .sum` fallback cannot fire for admitted
   statements (Finding 2). Destination type read from `table.entry st.output.tensor` (correct key per plan).
5. Refusals order: `admitSourceAffine` fails first, selection after; `sortSelection` carries `sourceError .statement {}`
   (empty origin) , acceptable/parked per plan section 2. A4 pins admission-before-selection and would fail if reordered
   (a reordering yields `sortSelection mixedSorts`).
6. Fixtures: no vacuous rows found. Q6 rows use exact `#guard_msgs` strings (rows 1-4, 6), A4-A7 match plan section 3 rows 7, 9, 10,
   13 and names/comments match what they check (A5 = bareScatter max/min `scatterPolicy`; A6 = sum bare scatter selects "real";
   A7 = unsorted `strided max/min` is `nonSum`, covering the second site; A4 = mixed program + refused statement). Minor
   wording: Q6 row 5 and A7's `isNonSum` are the only cause/non-cause asymmetry (Finding 3). Header of `SourceSortedAuditTest`
   lists plan rows correctly.

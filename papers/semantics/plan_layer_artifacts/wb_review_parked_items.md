# Whole-branch review: parked-items slice (single lens, Direct path)

Branch `worktree-plan-layer-parked-items`, HEAD `3f4ae8ad`, base `main` `57706ae3`. Read-only review;
no build run (the build-green and AxiomAudit claims are the record's, not re-verified here).

## Critical

None.

## Important

None.

## Minor

### M1. Fixture-count breakdown "29 added when its audit cells were closed" is wrong (27 + 2)
- Location: `lean_executable_semantics_path.md` section 4.9 paragraph "The fixture files
  (`test/Semantics/Plan*Test.lean`) hold 125 fixtures (96 shipped with the layer, 29 added when its
  audit cells were closed)"; `plan_layer_record.md` "Parked-items slice" table, docs-commit row
  ("96 shipped with the layer plus 29 from the audit cells").
- Claim: the 125 total is right, the attribution is not. Counting `^#eval check` plus top-level
  `example`/`theorem` over `test/Semantics/Plan*.lean` (the record's own method):
  `b3028e57` (T5) = 96, `main` `57706ae3` (after audit cells) = 123, `HEAD` = 125. The audit-cells
  slice added 27; this slice's `db15f986` added the 2 A2-e rows.
- Failure scenario: a reader reconciling the audit-cells record against the path doc finds 29
  audit-cell fixtures that do not exist.
- Fix: "96 shipped with the layer, 27 added by the audit-cells slice and 2 by the A2-e fixtures"
  (both docs).

### M2. A2-e mutant values unlabelled in plan section 5.2
- Location: `plan_layer_plan.md` section 5.2, row `execAcc` / "transactional vs sequential commit":
  "(`a2e-seq-visible`, `a2e-failed-vs-stuck`: shipped `[0,3,1]` / `failed`, mutant `[0,3,4]` /
  `stuck`; Open items 10)".
- Claim: the mutant values are stated alongside the shipped ones with no "scratch run, not asserted
  by the build" qualifier. Section 10 item 10 and the record's table row do carry the qualifier
  ("observed in a scratch run, not asserted by the build"; "mutant (scratch run)").
- Related: section 10 item 10's sentence "The valid neighbours `chainPlan` and
  `pPlan 2 failureAfterBody` agree under both kernels" (and the record's "valid neighbours agree
  under both") is likewise only half build-asserted: the shipped-kernel neighbour values are pinned
  by the rows, the mutant-kernel neighbour values come from the same scratch run.
- Failure scenario: a reader of section 5.2 alone takes the mutant column as a pinned regression.
- Fix: add "(mutant: scratch run, not built)" to the 5.2 cell; say "agree under both kernels (the
  mutant side observed in the same scratch run)" in item 10.

### M3. Failing-clause lists for the A2-e plans are stated as fact but not asserted by any build
- Location: `plan_layer_plan.md` section 10 item 10 ("`a2e-seq-visible` (`pubOrder@1`; ...)",
  "`a2e-failed-vs-stuck` (`accMat@1`, `pubMat@2`; ...)"); record "Parked-items slice" row `db15f986`
  ("`checkPlan`-invalid (`pubOrder@1`; `accMat@1`, `pubMat@2`)").
- Claim: the new rows in `PlanStepTest.lean` assert only `outcomeRow` values; there is no
  `verdict` row and no `example : a2eSeqVisible.checkPlan = false := by decide` (contrast the
  `invalid-acc-unmaterialised-attempts` row and the `example ... = false` lines in
  `PlanValidityTest.lean`). "Both plans checkPlan-invalid" and the clause names are therefore
  unpinned. Hand derivation against `checkAnn`/`Mat`/`Pub` agrees with the stated lists
  (pub of `cAll` at pc 1 before either occurrence is consumed; point 0 never in `matList`, so
  `accMat@1` and `pubMat@2`; nothing else fails), so this is a missing pin, not a wrong value.
- Failure scenario: a later change to the fixture helpers silently makes a plan valid (the row
  would then no longer be "outside checkPlan's domain") and nothing fails.
- Fix (optional, 1 dispatch or less): add the two `verdict` / `checkPlan = false` assertions.

### M4. "No plan separates the pair" is unqualified in the record
- Location: `plan_layer_record.md` "Parked-items slice" row `8b7cc508`: "... so no plan separates a
  Nodup check from its freshness clause".
- Claim: proved is (a) Nodup check implies the freshness clause at every `[acc G]` / `[pub B]`
  command (`checkAccFresh_of_cov1Nodup`, `checkPubFresh_of_cov2Nodup`, any plan), and (b) on a
  singleton plan, freshness at every step implies Nodup (`nodup_prefixAnn_flatMap`; packaged as
  `checkPlan_nodup_redundant` under `checkSingleton` + full `checkSteps`). For a non-singleton plan
  the pair does separate: `[[.acc [x], .acc [x]]]` fails `checkCov1Nodup` while no freshness clause
  is evaluated (`checkSteps` skips non-singleton commands). The plan 5.1 rows say "at `checkPlan`",
  which carries the singleton restriction; the record sentence drops it.
- Fix: "so on singleton plans (hence at `checkPlan`) no plan separates ...".

### M5. D8 sentence leaves `a` unbound
- Location: `tensor_logic_semantics.md` section 32.3, first paragraph, new sentence "this is the
  publication premise $U\cap\mathcal{C}_P(a)=\varnothing$ of Section 29.2, checked after removing
  $G$".
- Claim: Section 29.2's Publish premise is "$U\cap\mathcal{C}_P(a)=\varnothing$ for every $a\in B$";
  the new sentence omits the quantifier, so `a` is free (the preceding "the same address" gestures
  at it). Anchor `#292-accumulation-and-publication-contracts` matches heading
  `### 29.2 Accumulation and publication contracts`; colour macros are identical to the 29.2
  display. The sentence restates a premise the previous sentence already requires (it adds no new
  fusion constraint and removes none), which is the "cross-reference" disposition recorded for D8.
- Fix: "... $=\varnothing$ for every $a\in B$ of Section 29.2 ...".

## Questions with no finding

- Q1 (Lean): the `Validity.lean` diff is additive only (no removed lines); no `sorry`/`axiom` in
  `Plan/`; `#print axioms` added for all six. Statements match the docs: T1 needs
  `checkSingleton` + `checkSteps`, T2 needs only the Nodup check and `commands[pc]? = some [a]`,
  `checkPlan_eq_core` is unconditional. Not vacuous: `plan.checkPlan = true` and
  `chainPlan.checkPlan = true` are decided in `PlanValidityTest.lean`, so `checkSingleton` and
  `checkSteps` are satisfiable by real plans. `DefAddr.addr_injective` is used only in T2, as the
  record says. No test instantiates the new theorems (not required).
- Q2: plan 5.1 rows and section 10 item 3 match the theorems; `checkAccMat` is described as
  observed only everywhere (5.1 row, item 3, record).
- Q5: snapshot `8b7cc508` is the last commit touching Lean sources (`3f4ae8ad` is docs only);
  record "Authoring facts (measured)" 96 and the T5 row are historical by section; leftover
  `parked`/`OPEN` hits are the by-design `execAcc` order row, the new `checkAccMat` item, and
  D7/D11/D12; every module group the `Semantics/AGENTS.md` Tests sentence names exists in
  `lakefile.toml` (including `Semantics.AxiomAudit`).
- Q6: no `File.lean:NNN` in the changed docs; cited identifiers exist.

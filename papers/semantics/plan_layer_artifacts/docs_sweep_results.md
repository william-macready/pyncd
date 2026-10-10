# Plan layer slice 1: documentation sweep results

Run in the execution worktree after the sweep edits (plan section 8). Hits exclude `plan_layer_*` files.

| grep (plan 8.4) | before | after | disposition of remaining hits |
|---|---|---|---|
| 1. `Not formalized` etc. | 6: spec proof-status rows (Lemma 31.2, Theorem 31.3, Lemma 32.1); path doc lines on "No Part V result is formalized", "Part V backend refinement", and an unrelated binary64 remark | 2 hits | path doc: the binary64 exactness remark is unrelated and stays; spec Section 32.1: "A kernel that commits a successful prefix before failing is not formalized" is true (non-transactional failure is outside slice 1, D5) |
| 2. mentions of Lemma 31.2 / Theorem 31.3 / Lemma 32.1 | spec 11, path doc 0 (4.9 is new) | spec 14, path doc 6, `Semantics/AGENTS.md` 1, `Plan/AGENTS.md` 4 | every hit is a restatement, a proof-status row, or a pointer to them |
| 3. `File.lean:NNN` in the Plan node, path doc, spec | 0 | 0 | none |
| 4. stale statements (`no Lean proof`, `argued on paper`, `proposed contracts and proof targets`, `backend refinement LATER`) | 4 (spec intro, spec 31.4 last paragraph, spec Section 34, path doc diagram) | 3 | spec intro and Section 34 sentences are now limited to results outside the slice-1 profile; path doc diagram keeps the "general compiled storage/backend refinement LATER" row on purpose, with a new LANDED row for the slice-1 plan layer above it |
| exit: spec proof-status rows still "Not formalized" | 3 | 0 | none |

Path doc TOC counts (`rg -c "^#{2,4} "` and `rg -c "^ *- \["`): 38 and 37 (second is first minus 1).

Plan `Plan/AGENTS.md`: 3798 characters in total; the injected Pitfalls section is about 1000 characters (gate: at most about 3000).

Counts quoted in path doc 4.9, re-measured by the controller: 50 `#eval check` rows plus 46 top-level `example`/`theorem` items = 96 fixtures (`leanncd/test/Semantics/Plan*Test.lean`, `PlanFixtures.lean`); 20 mutation cycles, 3 labelled equivalent (`plan_layer_mutation_results.md`: 20/20 PASS).

Conflicts between plan text and the spec, recorded by the sweep dispatch:
1. The grep for "If a related concrete state steps to PlanFailed" misses because of LaTeX markup; the failure-matching restatement sits after the opening block of Section 31.3. Definition 31.1 item 4 is covered by the 31.1 paragraph (`step_failed`).
2. Condition 1 covering: stated both as "terminal, derivable" (role table) and as kept in `Valid` as a diagnostic clause (prose).
3. Section 31.4 "are argued on paper" reworded to "carry a mathematical argument in general", with the slice-1 kernel-checked sentence added.
4. Path doc 4.9 lists modules as plain code bullets with one link to the `Plan/` folder, because per-module link bullets broke the TOC count rule.

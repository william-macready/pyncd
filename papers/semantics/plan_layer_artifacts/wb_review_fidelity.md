# Whole-branch review, spec-Lean fidelity lens (plan section 9.3(b))

Surface: the documentation sweep (plan section 8) at branch HEAD 59e8ef32 vs e259294b.
Lean names cited in the added text were checked by `rg` against `leanncd/LeanNCD/Semantics/Plan/`;
all exist. Theorem statements were read for `terminal_adequacy`, `done_correct`, `failed_correct`,
`done_or_failed`, `done_of_model`, `done_iff_model`, `R`, `SlotView`, `InitOK`/`AccOK`/`PubOK`, `Valid`.

## Findings

### F1 (Important) Two condition numberings collide in the Section 31.1 "As formalized" block

- Location: spec `### 31.1 Acceptance and explicit rejection`, the added "As formalized (slice-1
  profile ...)" paragraph, its role table, and the closing paragraph ("Condition 1 covering is a
  consequence of condition 2 covering plus condition 4 ...").
- Plan 8.1 (Definition 31.1 row): semantic conditions 2-5 as theorems (Def 31.1 numbering) and the
  cond. 1 covering consequence of "cond. 2 covering + cond. 4" (Section 29.3 numbering). The plan
  is an internal document, so the two numberings never sat in one reader-facing place there.
- Edit: the opening paragraph uses Definition 31.1's numbering ("`R_start` (2), `step_R` (3),
  `step_failed` (4), `step_not_stuck` (5)"), directly below the five-item Definition 31.1. The table
  and closing paragraph then switch to Section 29.3's numbering without saying so: "pub B ...
  (condition 4)", "groups duplicate-free (condition 1, Nodup half)", "blocks ... (condition 2 ...)",
  "condition 2 covering plus condition 4". Only one row says "[Section 29.3] condition 3".
  Under Definition 31.1, condition 4 is failure matching and condition 2 is initialization. Neither
  has a covering half.
- Consequence: a reader following the nearest numbered list reads "pub B ... (condition 4)" as
  failure matching, and "condition 1 covering ... from condition 2 covering plus condition 4" makes no
  sense. The Lean docstrings avoid this by always saying "spec 29.3 condition N". Fix: qualify
  every table and closing-paragraph reference as "Section 29.3 condition N", or write "Schedule
  condition N".

### F2 (Important) The path doc's authoritative "Snapshot" paragraph was not updated

- Location: path doc `## 1. Purpose, authority, and current position`, the bold
  "**Snapshot: 2026-10-09, Lean as of `d8ce83ea`: ...**" paragraph and its list of landed
  developments. Also the spec `### Proof status and numbered results` tail: "The table reflects
  [the Lean path document] as of its 2026-10-09 snapshot, which is authoritative for what has
  landed. Update both together."
- Plan 8.2: edit only the status diagram, add 4.9, fix two sentences, update 5.2. The plan does not
  mention the Snapshot paragraph. The 8.4 value-grep patterns cannot find it, because it states
  what landed, not what is missing.
- Edit: the diagram now has a LANDED row for the plan layer, but the Snapshot paragraph still
  names `d8ce83ea` and lists only the source/executor developments. The spec says the table follows
  that snapshot, yet the table now has three Part V rows the snapshot does not include.
- Consequence: the document both files name as authoritative for "what has landed" leaves out
  slice 1. The spec's "update both together" rule is broken by this very sweep. Fix: add the plan
  layer to the Snapshot paragraph with the new date and commit, and update the spec's date.

### F3 (Minor) The path doc 4.8 validation table has no plan-layer row

- Location: path doc `### 4.8 Existing validation and its limits`, the
  `| Landed layer | Tests | Validation record |` table and "All are discovered by the default `Tests`
  target".
- Plan 8.2: put the counts in 4.9. It does not mention 4.8.
- Edit: 4.9 states the counts ("`test/Semantics/Plan*Test.lean` hold 96 fixtures ... 20 mutation
  cycles"), but the 4.8 table, which lists every landed layer's test modules and record, has no
  row for `PlanBatchTest` ... `PlanCorrectnessTest` / `plan_layer_mutation_results.md`. (The tests
  are in the default `Tests` target per `lakefile.toml`, so the sentence below the table stays
  true.)
- Consequence: a reader using 4.8 as the validation index misses the plan layer. Fix: add one row.

### F4 (Minor) Condition 1 covering is called "diagnostic", which the same paragraph's role definition rules out

- Location: spec `### 31.1`, "As formalized" block: the role legend ("*diagnostic* (checked but
  consumed by no theorem)"), the table row "groups cover O_P (condition 1 covering) | terminal,
  derivable ... | `complete_of_refState`", and the closing sentence "it is kept in `Valid` as a
  diagnostic clause". The same wording is in path doc 4.9 "What slice 1 does not do" ("kept as a
  diagnostic clause").
- Plan 8.1: "cond. 1 covering listed as a consequence ... and kept as a diagnostic clause". The edit
  copies the plan's wording.
- Edit/Lean: `complete_of_refState` consumes `hv.coverage1.2` directly, so by the legend this clause
  is *terminal*, not *diagnostic*. The sweep record (docs_sweep_results.md, "Conflicts" item 2)
  notices the tension but leaves it in the spec.
- Consequence: the spec contradicts itself. Fix: say "kept in `Valid` (redundant given condition 2
  covering and condition 4)" rather than "diagnostic".

### F5 (Minor) Path doc 4.9's "does not do" list drops one item from plan section 1

- Location: path doc `#### What slice 1 does not do`.
- Plan 8.2: content includes "the 'does NOT do' list of §1".
- Edit: lists 7 of the 9 items. It drops "Comparing failure occurrence or snapshot between plan and
  executor (D5)". (Dropping the internal "Reconstructing D7, D8, D11, D12" item is correct.)
- Consequence: small. The spec's 31.3 paragraph does say the snapshot may differ from
  `Executor.run`, but 4.9, the path doc's single summary of the slice, never mentions it. Fix: one
  bullet.

### F6 (Minor) "Batched commands" are listed as out of scope, but the slice proves batched accumulation

- Location: `leanncd/LeanNCD/Semantics/Plan/AGENTS.md` Purpose ("Does not own: ... fused or batched
  commands") and `leanncd/LeanNCD/Semantics/AGENTS.md` `## Scope` ("fused/batched plan commands
  remain outside it").
- Plan 8.3 prescribes the Scope wording "fused/batched plan commands".
- Edit vs surroundings: the same node's Code Map has `Batch.lean | batched accumulation ...
  batch_execution (Lemma 32.1)`, the slice-1 `acc G` kernel accumulates a whole group, and the
  spec's Section 34 annotation says "*Batching proved for the transactional singleton accumulate
  kernel*".
- Consequence: an agent cannot tell whether batching is in scope. "Batched" here must mean
  multi-annotation (fused) commands. Fix: say "fused (multi-annotation) commands" and drop "batched".

### F7 (Minor) The added spec paragraphs do not use the spec's notation for pc and states

- Location: every "As formalized (slice-1 profile ...)" paragraph in the spec.
- The spec writes the program counter as `\textcolor{#C16C86}{\mathsf{pc}}` (9 uses) and colors its
  concrete-layer symbols (`\textcolor{#C16C86}{\mathsf{PlanFailed}}`, `\mathsf{C}`, `\Pi`). The
  added text writes plain italic `$pc$`, `$pc=m$`, and uncolored `$\mathsf{Conf}$`. `Need_pub` is spelled
  correctly (`\mathrm{Need}_{\mathrm{pub}}`, matching the four existing uses).
- Consequence: cosmetic, but italic `$pc$` reads as the product p·c in a math document. Fix: use
  `\mathsf{pc}` in the restatements.

## Questions with no finding

- Q1 completeness: every 8.1 row (R, Definition 31.1, step simulation, Lemma 31.2, Theorem 31.3,
  failure matching, conditions by role, materialisation, Lemma 32.1, proof status), all four
  stale-statement edits (spec intro, 31.4 last paragraph, Section 34 list + sentence, path diagram),
  and the 8.2 and 8.3 items are present at the stated headings. Their content matches the Lean
  statements read. The failure-matching restatement appears only under 31.3, not next to
  Definition 31.1 item 4, which the 31.1 block covers via `step_failed` (4). This is acceptable and
  recorded in the sweep record. The 31.4 paragraph names more theorems than the plan does
  (`R_start`, `terminal_adequacy`), and the extra names are accurate. Gaps beyond the plan's own
  scope are F2, F3 and F5.
- Q2 anchors: all new `#...` anchors resolve (`#311-...`, `#293-...`, `#313-...`, `#33-...`,
  `#49-...`, the four `####` slugs, `tensor_logic_semantics.md#part-v-compilation-and-refinement`).
  N-/D-IDs do not leak into the spec or path doc text. Numbering: F1.
- Q3: `### 4.9` follows 4.8. The TOC has 4.9 plus its 4 sub-headings. The heading and TOC counts
  re-measured at 38 and 37. The diagram's LANDED/LATER columns match the existing rows (rg column
  check). 5.2 is updated. Fixture counts re-measured: 50 `#eval check` + 46 = 96 across the seven
  `Plan*Test.lean` files (PlanFixtures has 0). Mutation results: 20/20, 3 EQUIVALENT.
- Q4: Plan/AGENTS.md has Purpose / Code Map / Contracts / Pitfalls. All of its code-map names exist
  (rg). The Pitfalls section is about 1000 characters (≤ 3k). The whole file is 3835 bytes. The
  sweep record says 3798 characters; the gap is plausibly multibyte characters and is not a
  finding. The `Plan/AGENTS.md` link resolves. The Scope sentence and both leanncd/AGENTS.md rows
  are present and name real files and theorems. `Semantics.lean` imports `LeanNCD.Semantics.Plan`,
  so `AxiomAudit` (which audits the whole `LeanNCD.Semantics` namespace) covers the layer.
- Q5: no other markdown makes a now-false Part V proof-status claim. The remaining "proof target"
  and "Part V" hits are unrelated (Naperian papers, scan_route, gap audit, boundary policies) or
  correct (spec 32.1 "not formalized" for prefix-committing kernels). The only missed document
  sections are F2 and F3.
- Q6: no `File.lean:NNN` in any changed doc. The only hit (`St.lean:269-270`, leanncd/AGENTS.md)
  predates this branch. Every cited path is git-tracked, including `plan_layer_plan.md`,
  `plan_layer_mutations_post.json` and `scripts/mutation-manifest.sh`.

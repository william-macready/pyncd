# Whole-branch review, slice 3 (buffer retirement): spec-Lean fidelity lens (097ebeff..ca512754)

### F1 [Minor] Path doc says "ten modules under `Semantics/Plan/`"; there are eleven
- Where: `lean_executable_semantics_path.md`, snapshot paragraph ("extended by slice 2 to fused commands and by slice 3 to retirement of defined published addresses: ten modules under `Semantics/Plan/`"). The hunk was rewritten by this branch.
- Says: ten modules.
- Actual: `ls leanncd/LeanNCD/Semantics/Plan` lists 11 `.lean` files: Batch, Correctness, Faults, Fusion, FusionCorrectness, Memory, Run, Simulation, Step, Syntax, Validity. `Faults.lean` was already there at the base (`git ls-tree 097ebeff` lists it), so the count was stale before this branch, but the branch re-shipped it in a sentence it edited.
- The same stale count is in `leanncd/LeanNCD/Semantics/Plan/AGENTS.md` Code Map ("`Plan.lean`, which imports the ten modules below"). `rg -c "^import" leanncd/LeanNCD/Semantics/Plan.lean` gives `11`, and the table under that sentence has 11 rows. This branch did not edit that line.
- Fix: "eleven modules" in both places (or drop the count).

### F2 [Minor] Path doc "Plan modules" list was missed by the sweep: no `retire`, `RetOK`, `step_retire`, `Live` (and no `Plan/Faults`)
- Where: `lean_executable_semantics_path.md` section 4.9, "#### Plan modules" bullets.
- Says: "`Plan/Syntax`: annotations (`initZero`, `acc`, `pub`)"; "`Plan/Simulation`: per-annotation side conditions (`InitOK`, `AccOK`, `PubOK`, `AnnOK`) and one-step simulation `step_R`, `step_failed`"; "`Plan/Validity`: `Valid` (Definition 31.1, slice-1 form)".
- Actual: `Syntax.lean` has `| retire (B : List (DefAddr P))` in `inductive Ann` plus `retList`/`Ret`/`Live`/`live_input`; `Simulation.lean:89 def RetOK`, `:664 theorem step_retire`; `Validity.lean` has `checkRet` and field `retOK`. `Plan/Faults` is not listed at all (that gap predates this branch).
- Fix: add `retire` to the Syntax annotation list together with `Ret`/`Live`; add `RetOK` and `step_retire` to Simulation; add `checkRet`/`retOK` to Validity (and a `Plan/Faults` bullet).

### F3 [Minor] Path doc says the restatements in 30.3 and 33.2 are headed "As formalized (slice-1 to slice-3 profile ...)"; they are headed "(slice-3 profile ...)"
- Where: `lean_executable_semantics_path.md`, "#### Slices 1-3 profile, fixtures and mutations" ("The spec's restatements are the paragraphs headed "As formalized (slice-1 to slice-3 profile ...)" in Sections 29.3, 30.2, 30.3, 30.4, 31.1-31.4, 32.1 and 33.2").
- Actual: `rg -n "As formalized \(slice"` on the spec: 30.3 (line 4125) is `**As formalized (slice-3 profile: retirement of defined published addresses, ...`, and 33.2 is `**As formalized (slice-3 profile).**`. Every other listed section uses the "slice-1 to slice-3" header.
- Fix: "headed "As formalized (slice-1 to slice-3 profile ...)" or, in 30.3 and 33.2, "(slice-3 profile ...)"".

### F4 [Minor] Spec 29.3 and 31.1 restatements still list only Pub/Cons/Mat as the sets the per-command conditions are checked against
- Where: `tensor_logic_semantics.md` 29.3 "As formalized (slice-1 to slice-3 profile ...)" ("the per-annotation conditions (3, 4 and the freshness/materialisation clauses ...) are evaluated at expanded positions (`offset pc + j`) on the static sets $\mathrm{Pub}(n)$, $\mathrm{Cons}(n)$, $\mathrm{Mat}(n)$"); 31.1 "As formalized ..." ("`Valid` ... is a purely static condition, stated per command pc ... against the prefix sets $\mathrm{Pub}(pc)$, $\mathrm{Cons}(pc)$, $\mathrm{Mat}(pc)$ (the rows below)"). Both headers were changed to the slice-3 profile by this branch; the bodies were not.
- Actual: condition 3 is now over `Live` (`Validity.lean`: `def ReadyOK ... π.Live pc a`), and the new retire clause is over `Live` too (`Simulation.lean`: `def RetOK ... π.Live pc x.addr ∧ P.output x.1.val = false`). `Live = Pub ∧ ¬ Ret`, so the prefix set $\mathrm{Ret}(pc)$ is also a static input. The 31.1 table rows just below already say $\mathrm{Live}(pc)$, so 31.1 contradicts itself; 29.3 has no Live mention at all. A reader of 29.3 alone would think condition 3 is still checked against $\mathrm{Pub}(n)$.
- Fix: add "$\mathrm{Ret}(n)$ (condition 3 and the retire clause read $\mathrm{Live}(n)=\mathrm{Pub}(n)\setminus\mathrm{Ret}(n)$)" to both lists.

### F5 [Minor] Two Lean docstrings touched by the slice still describe the pre-slice-3 shape
- Where: `leanncd/LeanNCD/Semantics/Plan/Memory.lean` docstring of `Decode`; `leanncd/LeanNCD/Semantics/Plan/Validity.lean` docstring of `structure Valid`.
- Says: `Decode`: "succeeds only when every output coordinate is in `Pub(pc)` and its slot is initialised"; `Valid`: "Definition 31.1, slice-1 form (singleton commands, initZero/acc/pub)".
- Actual: `Decode` tests `(π.readPub pc M ⟨t.val, p⟩).isSome`, and `readPub` is `if π.Live pc a then M (place a) else none`, so the condition is `Live(pc)`. The neighbouring `readPub` and `decode_of_R` docstrings were updated to `Live(pc)`; this one was missed, and spec 30.4 states the `Live` form. `Valid` now has the field `retOK : ∀ pc B, π.commands[pc]? = some [.retire B] → π.RetOK pc B`, so the kinds are initZero/acc/pub/retire.
- Fix: `Decode` docstring "`Live(pc)`"; `Valid` docstring "initZero/acc/pub/retire".

### F6 [Minor] "Reading a retired slot ... is `stuck` at run time" leaves out Decode, which reads a retired output as `none` and the run ends `done`
- Where: spec 30.3 "As formalized (slice-3 profile ...)" ("a retired slot is never rewritten, and reading it is a plan defect (rejected by the checker, `stuck` at run time)"); path doc "#### Buffer retirement (slice 3)" ("Reading a retired slot is a plan defect: `ReadyOK` over `Live` is the reader-side rule that rejects it, and a run that does it is `stuck`, never an implementation error").
- Actual: this holds only for reads by an `acc` (fixture `retire-read-after`: `(false, ("stuck", 4, ...))`). The other reader of a slot is `Decode`, and fixture `retire-output` gives `(false, ("run:done", 6, none, [some 7, none, some 3]), none)`: the run is `done` and `Decode` is `none`. Spec 31.1 ("Runtime execution does not detect a retire of an output") states this correctly, so the documents are consistent overall, but the 30.3 sentence read on its own is false for the output reader.
- Fix: "reading it in a later `acc` is a plan defect (rejected by the checker, `stuck` at run time); decoding a retired output yields `none` (31.1)".

### F7 [Minor] Plan AGENTS.md points to a results file for all four manifests that holds only slice 1's results
- Where: `leanncd/LeanNCD/Semantics/Plan/AGENTS.md`, Pitfalls, last bullet ("... and `papers/semantics/plan_layer_slice3_mutations_post.json` (10 cycles, all caught at library proofs), run with `leanncd/scripts/mutation-manifest.sh`; results in `papers/semantics/plan_layer_mutation_results.md`."). The bullet was edited by this branch.
- Actual: `rg -n "S3-|cycles passed" plan_layer_mutation_results.md` gives only `24:20/20 cycles passed.` (slice 1). The slice-3 results are in `papers/semantics/plan_layer_slice3_mutation_results.md` ("10/10 cycles passed.") and slice 2's in `plan_layer_slice2_mutation_results.md`. The wrong pointer for slice 2 was already there before this branch; the branch extended it to slice 3.
- Fix: "results in `plan_layer_mutation_results.md`, `plan_layer_slice2_mutation_results.md` and `plan_layer_slice3_mutation_results.md`".

### F8 [Minor] Design spec 3.4 says `step_init` and `step_acc` need `retPub`; in the code they only carry it forward, and `delta_congr` is used by `step_acc` alone
- Where: `docs/superpowers/specs/2026-10-11-buffer-retirement-design.md` section 3.4, the new bullets ("`R` gets a sixth field `retPub` ... It is needed by `step_pub` (a freshly published member is live) and by `step_init`/`step_acc` (a retired address is not an unpublished write target)"; "`step_acc` and `step_failed` now reach readiness through `evalReady_of_le` and per-member values through `delta_congr`").
- Actual: `rg -n retPub Simulation.lean` lists uses at 534 (`step_init`), 605 (`step_acc`), 658/661 (`step_pub`) and 707 (`step_retire`). In `step_init` and `step_acc` the only use is the last goal, re-establishing `retPub` itself at `pc + 1` (`exact (pub_succ hcmd b).mpr (.inl (hR.retPub b ...))`). Their `dead` goals get "a published address is not a write target" from `InitOK` (`(ok x hx).1`) and from `dest_not_pub`, not from `retPub`. Only `step_pub` (658, `have hp' := hR.retPub b hr` in the `dead` goal) consumes it substantively. `delta_congr` appears only in `step_acc` (584); `step_failed` uses `evalReady_of_le` (749) and not `delta_congr`.
- Fix: "needed by `step_pub` (a freshly published member is live); the other steps only carry it forward"; "`step_acc` and `step_failed` reach readiness through `evalReady_of_le`; `step_acc` gets per-member values through `delta_congr`".

### F9 [Minor] The design spec and the path doc give contradictory accounts of the old "180 fixtures", and the spec's account does not add up
- Where: design spec 3.5 ("All 200 existing fixture rows (by the `rg -c` count ...; the path doc's 180 predates `PlanFaultsTest`)"); path doc "#### Slices 1-3 profile, fixtures and mutations" ("the earlier figure of 180 was counted differently and does not reconcile with this method (see open item O6 ...)").
- Actual: at base 097ebeff, `git grep -c` over `Plan*Test.lean` gives 122 `#eval check` rows and 78 `example`/`theorem` items, so 200 is correct. `PlanFaultsTest` holds 12 + 7 = 19, and 200 - 19 = 181, not 180. "Predates `PlanFaultsTest`" therefore does not account for 180, and the path doc says the figure does not reconcile.
- Fix: in the spec, replace "the path doc's 180 predates `PlanFaultsTest`" with "the path doc's earlier 180 was counted differently (plan O6)".

## Declined to judge

- Proof-status rows and Section 34 bullets that still say "Proved (slice-1 profile)" (Lemma 31.2, Theorem 31.3 rows; the Definition 31.1 bullet "*Proved for the slice-1 profile* (`Valid`, `checkPlan_sound`, ...)"). Each row now has a "Slice 3: statement unchanged ..." suffix, and `Valid` does include `retOK`. These labels understate rather than misstate, and slice 2 left the same labels, so whether to rewrite them is a style choice.
- Design spec 5 row "`Ann` | new constructor `retire` (about 24 constructor-case sites gain an arm)" was not amended. `rg -c "\| \.?retire "` over `Plan/` gives 21 lines, which is "about 24" for an estimate.
- Whether `plan_layer_slice3_plan.md` (tracked, cited by the path doc for "Review Focus" and O6) is meant to stay a shipped reference. It is tracked (`git ls-files` lists it), so the citation is not broken.
- Soundness questions outside this lens, for example that `Faults.lean` has no `retire`-specific text (`rg "retire|Live|Ret\b" Faults.lean` finds nothing; the retire-under-fault fixtures cover it).

## Verified clean

- `tensor_logic_semantics.md`: all 10 changed "As formalized" headers (29.3, 30.2, 30.4, 31.1, 31.2, 31.3 x2, 31.4, 32.1 changed; 30.3 and 33.2 added) were read. Every identifier exists at HEAD with the stated shape:
  - `retire` is `Ann.retire (B : List (DefAddr P))` in Syntax.
  - `Ret`, `Live`, `retList`, `ret_zero`, `live_zero`, `Live.pub`, `live_input` are in Syntax.
  - `execRet` is in Step: a foldl of `Function.update ... none`, total.
  - `postAnn (.retire _) = some c` is in Memory.
  - `readPub` and `SlotView .pub` are guarded by `Live`.
  - `R` fields `dead : ∀ a, Pub pc a → ¬ Live pc a → M (place a) = none` and `retPub : ∀ a, Ret pc a → Pub pc a` are in Memory.
  - `readPub_eq` takes `(ha : π.Live pc a)` and concludes `readPub pc M a = c.published a`.
  - `decode_of_R`'s `outs` is over `Live`.
  - `RetOK` is in Simulation: `π.Live pc x.addr ∧ P.output x.1.val = false`.
  - `ReadyOK` and `checkReady` are over `Live`; `checkRet` has no Nodup; `Valid.retOK` and `checkPlan_iff` are in Validity.
  - `live_output_of_valid` is in Correctness.lean and is used by `terminal_adequacy` and `terminal_adequacy_F`.
- 31.1 roles were checked against the proofs:
  - The Pub half is consumed in `step_retire` via `(ok x hx).1.1`.
  - The ¬Ret half is consumed by no theorem: the only `retOK`/`RetOK` consumers are `step_retire` (`.1.1`) and `live_output_of_valid` (`.2`).
  - The output half is consumed by `live_output_of_valid`.
- Runtime claims were checked against `PlanRetireTest.lean` and `a3a_notes.md`:
  - `retire-output`: `run:done`, Decode `none`.
  - `retire-unpublished`: `run:stuck` at pc 5, slot cleared.
  - `retire-twice`: checker false, run `done`.
  - `retire-dup-in-block`: accepted.
  - `retire-fused-after-read` / `before-read`: checkPlanF true/false.
  - `retire-read-after`: stuck at pc 4.
- The 31.3 "In slices 1-2 that step is trivial (nothing is retired)" is scoped and true. The anchors `#293-...`, `#303-storage-changes-and-retirement` and `#33-scan-compilation-and-buffer-reuse` match headings.
- `lean_executable_semantics_path.md`:
  - The TOC anchors `#buffer-retirement-slice-3`, `#slices-1-3-profile-fixtures-and-mutations` and `#what-slices-1-3-do-not-do` match the three headings. No reference to the old anchors remains outside historical plans.
  - The new theorem rows exist: `step_retire` (Simulation), `checkRet_sound` / `checkRet_complete` (Validity), `live_output_of_valid` (Correctness).
  - Fixture counts: `rg -c "^#eval check"` gives 139 (18+8+7+23+13+17+4+7+1+21+12+8). `rg -c "^(example|theorem)\b"` gives 89 (2+3+30+11+7+9+16+1+6+4). Total 228. PlanRetireTest has 17 rows and 11 items (10 `example` + 1 `theorem`), 28 in all.
  - Mutation labels: 20 + 15 + 9 + 10 = 54, and slices 1-2 = 35. Equivalent labels: 3 in slice 1, 1 in slice 2, 0 in D7 and slice 3.
  - Every slice-3 `expect` is a library location (Simulation/Validity/Memory), matching "every one is killed at a library proof". The snapshot commit f3210475 is after the last `.lean` change (T3 dc698955; 966f38f7 and ca512754 touch no `.lean`).
- AGENTS nodes (`leanncd/AGENTS.md`, `Semantics/AGENTS.md`, `Plan/AGENTS.md`): every new identifier and location in the Code Map, Contracts and Pitfalls exists in the stated file, apart from F1 and F7. `R_transport` in Fusion carries `hret`/`hlive`/`dead`/`retPub`. `readPub_isSome` in Run is over `Live`.
- Design spec 3.1, 3.4, 3.5, 5:
  - The lemma locations are right: `ret_succ` is Simulation:36, `pub_succ_of` 42, `ret_succ_of` 46, `live_succ_of` 50.
  - `evalReady_of_le` is used by `step_acc` and `step_failed`.
  - S3-M1..M10 labels match the manifest. S3-M9 is killed at `readPub_eq` (Memory, rewrite failed).
  - "Row-level probes for M1, M3, M6 only" matches `plan_layer_slice3_record.md`.
  - "200 existing" matches the base count: `git grep -c` at 097ebeff gives 122 rows + 78 items.
- No `File.lean:NNN` citation in any changed document (the one hit, `St.lean:269-270` in `leanncd/AGENTS.md`, predates this branch and is not in a changed hunk).
- Stale-profile sweep (`no retirement|dense non-reused|non-reused storage|180 fixtures|35 mutation|slice-1 and slice-2 profile`, plus `slices 1-2|aliasing, retirement|nothing is retired|non-reused`): every hit is a historical plan or review (`plan_layer_plan.md`, `plan_layer_slice2_plan.md`, `plan_layer_artifacts/*`, `plan_layer_slice2_artifacts/*`), the design spec's own motivation and edit instructions, or a correctly scoped slices-1-2 sentence. No live document is stale apart from F2.


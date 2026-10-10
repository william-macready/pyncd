# Whole-branch review, SOUNDNESS lens (plan 9.3(a)) — Part V Plan-layer slice 1

Worktree `plan-layer-exec`, HEAD 59e8ef32, diff vs e259294b. Scope: the docs sweep
(spec `tensor_logic_semantics.md`, path doc 4.9, `Plan/AGENTS.md`) checked against the Lean.

## Findings

### S1 (Minor) — Section 31.1 "As formalized": condition-1 covering called "diagnostic" but the table says "terminal"
- Location: `tensor_logic_semantics.md`, Section 31.1, paragraph after the clause table
  ("Condition 1 covering is a consequence ... it is kept in `Valid` as a diagnostic clause").
- Claim: the paragraph defines *diagnostic* as "checked but consumed by no theorem", and the
  table row "whole plan: groups cover O_P (condition 1 covering)" gives role *terminal*,
  consumed by `complete_of_refState`. The follow-up sentence then calls the same clause
  "diagnostic". The two statements contradict each other inside one paragraph.
- Evidence: `Correctness.lean` `complete_of_refState` uses `hv.coverage1.2` directly
  (`have hx ... := hv.coverage1.2 ⟨t, o⟩`); it does not go through `cov1_of_cov2_pubOrder`.
  So the clause is consumed and is not diagnostic in the paragraph's own sense.
- Failure scenario: a reader (or a slice-2 implementer trimming `Valid`) takes "diagnostic"
  at face value and drops `coverage1.2`; `complete_of_refState` stops compiling. The build
  catches it, but the doc sends the reader the wrong way. Suggested wording: "redundant (derivable
  via `cov1_of_cov2_pubOrder`) but still the clause `complete_of_refState` consumes".

### S2 (Minor) — Section 31.3 "As formalized": `runPlan_R` credited with more than it states
- Location: Section 31.3, "As formalized" paragraph: "`step_failed` (one command) and
  `runPlan_R` (the whole run) give Conf ->* Failed(o, ...) ... by one `undefined` event from the
  related Conf ... The matched snapshot is that related Conf".
- Claim: true for `step_failed` (statement: `Execution P ops [.undefined o.1 o.2] (.running c)
  (.failed o.1 o.2 c)` from an R-related `c`). `runPlan_R`'s failure disjunct only gives
  `∃ o pc' M' c' events, runPlan = .failed o pc' M' ∧ Execution ... (.running (P.initial η))
  (.failed o.1 o.2 c')`: `c'` is existential and is not tied to `refState pc'`, to R at `pc'`,
  or to a single `undefined` event. "One event from the related Conf" and "the matched snapshot
  is that related Conf" are facts about the proof of `run_R`, not about any exported statement
  for the whole run.
- Failure scenario: a downstream proof (e.g. slice 2 relating `PlanFailed`'s memory to the
  reference snapshot, or a refinement of 31.3 (b) that compares snapshots) cites `runPlan_R`
  for "snapshot = refState pc'" and finds the lemma does not give it.
- Evidence: `Run.lean` `runPlan_R` / `run_R` statements (failure disjunct); `run_R`'s `semFail`
  branch builds `⟨o, pc, M, c, _, rfl, hex⟩` internally but the statement hides `c = refState pc`.
  Fix: attribute the per-step facts to `step_failed` only, and say `runPlan_R` gives "some reference
  failure on the same `o` reached from the initial state".

### S3 (Minor) — Section 31.3 "As formalized": "unobservable" alternative-kernel claim has no theorem
- Location: Section 31.3, last sentence of the "As formalized" paragraph: "On `checkPlan`-valid
  plans, committing raw values versus view values, and transactional versus sequential commit,
  are unobservable (`dest_not_pub`, `acc_slot_isSome`)."
- Claim: stated as a formal fact with theorem names, but no Lean statement compares a raw-value or
  sequential-commit kernel with `execAcc`; neither variant is defined. `dest_not_pub` (a pending
  occurrence's destination is not in `Pub pc`) and `acc_slot_isSome` (materialised unpublished
  slot is initialised) are ingredients of a paper argument, and both are stated under R, not under
  `checkPlan` (the bridge is `checkPlan_sound` + `run_R`'s invariant).
- Failure scenario: a reader cites the sentence as a theorem, for example to justify a kernel
  variant in slice 2 without re-running the proofs. The real evidence is test-level:
  `plan_layer_mutation_results.md` rows A2-b (commit values read raw memory) and A2-e
  (non-transactional acc) are EQUIVALENT mutants, which means the whole proof suite still builds
  with them. Cite those rows, not the two lemmas.
- Related point, same paragraph: "(zero preceding contributions: the accumulate kernel is
  transactional)" gives the wrong reason. A2-e's survival shows that `step_failed` holds for a
  non-transactional kernel too. The single-event match holds because `step_failed` starts from the
  pre-step related `c` and `runFrom` reports the pre-step memory (`.semFail o => .failed o pc M`),
  so any partial commit is discarded. Transactionality is not what makes it hold. The 32.1 paragraph
  ("proved only for the transactional singleton kernel") states the scope correctly, but it repeats
  the "no preceding contributions" reasoning.
- Evidence: `Step.lean` defines only `execAcc` (transactional, `valuesOn (readPub pc M)`);
  `Simulation.lean` `dest_not_pub` / `Run.lean` `acc_slot_isSome` statements. Fix: "are
  unobservable by an argument from `dest_not_pub`, `acc_slot_isSome` (not a stated theorem)".
- Overlap note: prior `review_soundness.md` F-1 (and its lines 60-70) proposed this wording, adding
  the "valid plans" qualifier. This finding makes a different point: the sentence reads as
  kernel-checked, but no theorem states the equivalence. Raw-vs-view is plausible for any plan
  (the view is a sub-store of M, and evaluation succeeded on it), so only the attribution is in
  question.

### S1 addendum: the same contradiction appears in the path doc
- `lean_executable_semantics_path.md` section 4.9, "What slice 1 does not do", has the bullet
  "Dropping the redundant condition-1 covering check (kept as a diagnostic clause)". The clause is
  redundant but it is consumed: `complete_of_refState` uses `coverage1.2`, so it is not
  diagnostic. Dropping it would also mean rerouting `complete_of_refState` through
  `cov1_of_cov2_pubOrder`, and the bullet should say so.

### S4 (Minor): 31.1 and 31.4 credit general condition 3 to `step_R` without its `refState` premise
- Location: Section 31.1 "As formalized" says "conditions 2-5 ... are theorems, `R_start` (2), `step_R` (3),
  `step_failed` (4) and `step_not_stuck` (5)". The paragraph after Theorem 31.3 in Section 31.4 says
  "the generic steps and conditions 2-5 are kernel-checked in Lean (`R_start`, `step_R`, ...)".
  `Plan/AGENTS.md` Contracts bullet 3 says the same.
- Claim: Definition 31.1 states that conditions 2-5 "quantify over ... reachable related states".
  `step_R` also requires `hc : π.refState ops η pc = some c`, so it proves condition 3 only for
  the deterministic reference state. Section 31.2 "As formalized" and AGENTS bullet 4 disclose
  this. The 31.1 and 31.4 sentences, read on their own, state the stronger form.
  `step_failed` and `step_not_stuck` do need only R, so conditions 4 and 5 are as claimed.
- Failure scenario: a reader of 31.1 or 31.4 alone concludes that every R-related state
  simulates, and builds on it (for example a nondeterministic-schedule extension). The claim is
  false in Lean terms, because R2-R4 do not pin untouched accumulators (defect D1).
- Evidence: the statement of `Simulation.lean` `step_R`. Fix: write "`step_R` (3, for
  `Conf = refState pc`; see 31.2)" in both places.

### S5 (Minor): path doc 4.9 calls `SlotView` "the read view"
- Location: section 4.9, "Plan modules", the `Plan/Memory` bullet: "dense memory, the read view
  `SlotView`, `Decode`, ...".
- Claim: `SlotView` is the layout view λ, which maps a resource to an optional slot.
  Spec 30.4 "As formalized" and the `Memory.lean` docstring both say "layout view". The read view
  is `readPub`. Spec 29.3 "As formalized" relies on that read view ("readiness is enforced
  dynamically by the read view"), so mixing up the two names misdirects anyone tracing the
  readiness argument.
- Evidence: `Memory.lean`, `def SlotView` ("The spec's layout view `λ`") and `def readPub`
  ("The read view of published resources"). Fix: "the layout view `SlotView`, the read view
  `readPub`".

### S6 (Minor): `Plan/AGENTS.md` lists "batched commands" as not owned
- Location: `Plan/AGENTS.md` Purpose, "Does not own: ... fused or batched commands".
- Claim: slice 1 executes batched accumulation. An `acc G` command is a batch, which
  `Batch.lean`/`batch_execution` (Lemma 32.1) and `execAcc` cover. What is excluded is fusion
  (several annotations per command) and batching under a non-transactional or partial-commit
  kernel. As written, the bullet contradicts the Code Map row for `Batch.lean` and the Purpose
  sentence "Proves Lemma 32.1".
- Failure scenario: an implementer looking for the batch semantics skips `Batch.lean`, or adds
  a duplicate "batched command" construct. Fix: "fused (multi-annotation) commands".

## Per-question results

1. Overclaim: S2, S3 and S4, all Minor. The following checks found nothing: the 29.2/30.2 initZero
   freshness wording (matches `InitOK` and `acc_zero_of_unconsumed`, which needs R1); the R
   structure (R1-R4 match `structure R` exactly); `decode_of_R` (one direction, and the "iff" holds
   by the definition of `Decode`); terminal adequacy (matches `terminal_adequacy` field for field);
   Theorem 31.3 (a)(b)(c) (match `done_correct`, `failed_correct`, `done_or_failed`/`runPlan_not_stuck`
   and `done_of_model`/`done_iff_model`, with `Valid` as the only plan hypothesis); the Lemma 32.1
   premises (prose lists ready and successful separately, Lean has one premise `evalReady = .evaluated
   (some v)`, so the prose is not stronger); the profile wording.
2. Underclaim or contradiction: S1 (with its addendum). No stale "no Lean proof", "not formalized"
   or "argued on paper" leftovers. The unchanged general Definition 31.1, the 30.4 R and the
   Need_pub argument are all explicitly retained as the general contract and are not contradicted.
3. Proof-status rows: no finding. Every named theorem exists. The rows for 31.2 and 31.3 say
   "slice-1 profile". The 32.1 row says only "Proved", and that is correct: `batch_execution` and
   the `accumulateBatch_*` lemmas hold for any `c : P.Running` and are not profile-restricted.
   The failure half is scoped to `step_failed`.
4. Axioms/sorry: no finding. The sweep added no "axiom-free" or "no sorry" prose. `AxiomAudit.lean`
   audits every theorem and definition under `LeanNCD.Semantics` (prefix match), which covers
   `LeanNCD.Semantics.Program.Plan`, and `Semantics.lean` imports `Plan.lean`.
5. AGENTS node: S6, plus the Contracts bullet 3 part of S4. Verified as accurate: every file in
   the Code Map exists, the eight-module import order matches `Plan.lean`, `coverage_iff_schedule`
   is in `Syntax.lean`, `checkPlan_sound`'s signature is right, `Eval/Plan/EvalPlan.lean` has its
   own `checkPlan`, and the mutation manifest and script exist.

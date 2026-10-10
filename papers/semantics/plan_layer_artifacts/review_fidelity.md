# Plan-layer slice 1: spec-Lean fidelity review (lens 2)

Reviewer: read-only. Worktree HEAD 465af455. Findings appended as found.

## Group 1: spec statements vs Lean (Q1, Q3)

F1 (Important). Failure matching keeps the occurrence; the D5 caveat misplaces the gap.
- Where: plan §2 D5, §8.1 rows "Theorem 31.3" and "failure matching"; a3b_notes.md SPEC RESTATEMENT DRAFT
  (31.3 (b) "Only no-model is claimed, not the occurrence or the snapshot"; D5 "compares no-model, not the
  snapshot or the occurrence").
- Lean: `step_failed @ Plan/Simulation.lean` proves `Execution [.undefined o.1 o.2] (.running c) (.failed o.1 o.2 c)`
  for the SAME `o` the plan reports; `run_R`/`runPlan_R @ Plan/Run.lean` carry that `o` to
  `Execution ... (.running (P.initial η)) (.failed o.1 o.2 c')`. So spec 31.3's requirement
  "Conf ->* Failed(o, σ', α', U')" (same `o`) is proved, snapshot = the related Conf.
- Spec 31.3 (b) never claimed occurrence or snapshot; it already says only `Models = ∅`. What D5 measures
  (plan slot 0 = 0 vs executor accumulator 2) is a difference from `Executor.run`'s deterministic
  schedule, which the spec does not mention in Theorem 31.3.
- Failure scenario: copying the draft makes the spec say the failing occurrence is not matched, which is
  weaker than what Lean proves and contradicts spec 31.3's failure-matching paragraph left in place.
- Fix: restate (b) as in the spec; under failure matching say "matched with the same occurrence o; the
  matched segment is one `undefined` event from Conf; the snapshot is Conf and may differ from the
  executor's own schedule (fixture `failureAfter`)".

F2 (Important). Step simulation (spec 31.2) is not restated, and Lean's form needs an extra invariant.
- Where: plan §8.1 has no row for `### 31.2 Initial states and successful-step simulation`; a3b draft
  has no 31.2 entry; D1-D10/N1-N8 do not record this.
- Lean: `step_R @ Plan/Simulation.lean` needs `hc : π.refState ops η pc = some c` besides `R` and
  `AnnOK`; `run_R @ Plan/Run.lean` carries `refState pc = some c` as a second invariant. Spec 31.2 asks
  `R(C,Conf) ∧ C -> C' ⇒ ∃ Conf'. Conf ->* Conf' ∧ R(C',Conf')` for every R-related Conf. Lean proves it
  only for `Conf = refState pc` (D1 says R2-R4 do not pin untouched accumulators, so R alone does not
  determine Conf).
- Failure scenario: the restated R in 30.4 plus unchanged 31.2 reads as a forward simulation of R alone,
  which Lean does not prove.
- Fix: add an §8.1 row for 31.2: the simulation invariant is `R ∧ Conf = refState pc` (deterministic
  logical post-state, P3), premises `AnnOK pc a` and singleton command; `R_start` is the initialisation
  obligation.

F3 (Important). Definition 31.1 restatement drops the spec's semantic conditions 2-5 without saying
what replaces them.
- Where: spec lines 4142-4156 (conditions 2-5 "quantify over all well-typed inputs and reachable related
  states ... discharged kernel by kernel"); plan §8.1 row "Definition 31.1"; a3b draft table.
- Lean: `Valid @ Plan/Validity.lean` is purely static (per-command `InitOK`/`AccOK`/`ReadyOK`/`PubOK`,
  `Singleton`, coverage); conditions 2-5 become theorems for the fixed slice-1 kernels: `R_start` (2),
  `step_R` (3), `step_failed` (4), `step_not_stuck` (5). That is a different shape (a static sufficient
  condition plus proved obligations), not a restatement of the same five conditions.
- Fix: the §8.1 Definition 31.1 row must say that conditions 2-5 are discharged for the slice-1 kernels
  by those four theorems, and keep the five-condition definition as the general contract.

F4 (Important). Draft table states an unproved claim as fact.
- Where: a3b draft row "groups duplicate-free (cond. 1 Nodup) | (diagnostic; also forced by per-step
  AccOK success)"; plan §8.1 says "copy its bullets and table".
- Lean: no theorem derives `π.accFlat.Nodup` from `AccOK`; plan §1 "does NOT do" lists this exact A2
  conjecture as unproved.
- Fix: "(diagnostic; conjectured to follow from per-step AccOK, not proved)".

F5 (Minor). Draft table omits the Nodup half of condition 2.
- `Valid.coverage2 = Coverage2 = pubFlat.Nodup ∧ covering @ Plan/Syntax.lean`; the draft only lists
  "blocks cover Addr_Def". `checkCov2Nodup` is a shipped clause (plan §5.1). Add a row "blocks
  duplicate-free (cond. 2 Nodup) | diagnostic | none".

F6 (Minor). "Single sort Q" is described as a profile restriction of the theorems.
- Where: plan §1 Global Constraints "single sort `Q`" and "does NOT do: Multiple sorts"; path doc 4.9 is
  to copy the profile and the not-done list.
- Lean: every theorem is generic over `K : S → Type` with `[∀ t, AddCommMonoid ...]` and `ops`; only
  the fixtures use the rational reference. The 4.9 text should say "theorems generic over sorts and
  carriers; fixtures use exact rationals".

Confirmed faithful (no finding): R1-R4 and Decode in the draft match `R`/`Decode`/`readPub @ Plan/Memory.lean`
(`SlotView` acc guard `Mat ∧ ¬Pub`, pc-only); Lemma 31.2 draft matches `terminal_adequacy` (about `runPlan`,
P7 recorded); 31.3 (a) matches `done_correct` (singleton model set, Decode, denotation); (c) matches
`done_or_failed` + `done_of_model` + `done_iff_model` (Lean's converse is stronger: hypothesis is just
`Models η ρ`); Lemma 32.1 matches `batch_execution`/`batch_execution_perm` with the D10 premises
(accumulator/pending/published facts are `accumulateBatch_accumulators/_pending/_published @ Plan/Batch.lean`).
InitOK/AccOK/PubOK/ReadyOK rows match `@ Plan/Simulation.lean`, `@ Plan/Validity.lean`.

## Group 2: §8 edit commands (Q2)

F7 (Important). §8.1 does not say the restatements are profile-scoped additions, and two of them
are false outside the no-reuse profile if they replace the general text.
- Where: §8.1 rows "relation R" (R3 with `SlotView π pc` mapping exactly `Pub pc`) and "Lemma 31.2"
  ("replace the Need_pub route: at pc = m, `Pub m = Addr_Σ`"), plus the manual check "rewrite only the hit
  inside Lemma 31.2's argument".
- Lean: `SlotView .pub a = some (place a)` iff `Pub pc a` (`@ Plan/Memory.lean`) holds only because slice 1
  has no retirement/reuse. Spec Section 33 (two reused state buffers, full-history outputs, `Need_pub` at
  spec 33.3) still needs the general argument: with retirement, published ≠ mapped, so "every output is in
  Need_pub, hence mapped" is the step that matters.
- a3b draft scopes it correctly ("In slice 1 ... needs no Need_pub argument"); the plan's "replace" does not.
- Fix: every §8.1 restatement is an added "As formalized (slice-1 profile: singleton, dense non-reused,
  no retirement)" paragraph; keep the general 30.4 R and the Need_pub argument; say that in slice 1 the
  Need_pub step is trivial because `Pub m = Addr_Σ` and nothing is retired.

F8 (Minor). §8.1 manual-check text names the wrong section for a Need hit.
- `rg -n "mathrm\{Need\}"` hits lines in 30.2 (around "Need_pub(...)"), Lemma 31.2's argument, **33.3**
  ("Full-history outputs change the retention obligation"), and the notation table. The plan says
  "the others (30.2/30.3 and the notation table)"; 30.3 has no hit, 33.3 does. Count 4 is right.

F9 (Minor). §8.1 "materialisation" row quotes "before a kernel updates or reads"; the spec text is
"Before a kernel updates or reads its physical" (capital B, in 30.2 not 30.3). Case-sensitive `rg` on the
quoted string misses it.

F10 (Minor). §8.1 "proof status" row for Lemma 32.1 names only `batch_execution`, `batch_execution_perm`.
The spec's conclusion (accumulator `α ⊕ Δ_G`, remaining `U \ G`, σ unchanged) is
`accumulateBatch_accumulators`/`_pending`/`_published @ Plan/Batch.lean`, and the failure paragraph of 32.1 is
proved only for the transactional singleton kernel (`step_failed @ Plan/Simulation.lean`). Name them and
qualify the failure half.

Verified (no finding): every heading/bold anchor in the §8.1 `rg` commands exists (29.3, 30.1-30.4,
31.1-31.3, 32.1; Definition 31.1, Lemma 31.2 under `### 31.3`, Theorem 31.3 under `### 31.4`, Lemma 32.1);
"They also ensure the readiness", "follows from the others", `4. **Failure matching.**` exist; the three
proof-status rows exist only in the spec table (lines ~200-202), and `rg` finds no Lemma 31.2/Theorem
31.3/Lemma 32.1 string in the path doc, so plan §10 item 1 is correct. Path doc: `### 4.8` is the last
4.x, no 4.9 exists, TOC has no 4.9, the proposed anchor `#49-part-v-slice-1-the-singleton-command-plan-layer`
is the GitHub slug of the proposed heading; "No Part V result is formalized" and "Part V backend
refinement" both exist; the `| Theorem | Mathematical conclusion | Spec result |` header exists (4.6);
counts today are 33 headings / 32 list-links, so the "first minus 1" rule holds now. Caveat: if 4.9 gets
`####` sub-headings (4.6 and 4.7 do), each needs its own TOC line or the rule breaks; §8.2 does not say.
No `File.lean:NNN` in the spec, path doc or plan today.

## Group 3: stale values (Q4), discoverability (Q5), hygiene (Q6)

F11 (Important). §8.4's greps miss four stale statements that become false or misleading after merge.
None contains "Not formalized", "No Part V result", "Part V backend refinement" or a result label:
- spec, intro before `### Proof status and numbered results`: "The [Part V](...) compilation results have
  no Lean proof." (fix: "Lemma 31.2, Theorem 31.3 and Lemma 32.1 are proved for the slice-1 profile; see
  the table").
- spec, last paragraph of `### 31.4 The compiled-correctness theorem`: "the generic steps (Lemma 31.2 ...
  Lemma 32.1 ...) are argued on paper, while conditions 3-5 remain an obligation on each kernel ... not a
  claim that a particular compiler or kernel has already been verified" (the slice-1 kernels are verified:
  `step_R`, `step_failed`, `step_not_stuck`; see F3).
- spec, Part V closing list ("The compilation-layer proof targets are:" ... "These are proposed contracts
  and proof targets, not kernel-checked results"): the first, second, part of the third, fifth and sixth
  bullets now have slice-1 Lean results.
- path doc, the status diagram in section 1: "compiled storage/backend refinement   LATER" (§8.2 updates
  4.8/4.9/5.2 and two sentences, not this diagram).
Suggested extra value-greps: `rg -n "no Lean proof|argued on paper|proposed contracts and proof targets|backend refinement +LATER"`.

F12 (Minor). `leanncd/LeanNCD/Semantics/AGENTS.md` `## Scope` enumerates what the validation layer
covers (expressions, additive models, reference-machine soundness, read-only einsum correspondence); §8.3
adds a line only under `## Current artifact`, so Scope stays incomplete.

F13 (Minor). Name collision not addressed in the intent-layer edits. `leanncd/AGENTS.md` already has
"Checked plan backend | `LeanNCD/Eval/Plan/AGENTS.md`" (`EvalPlan`, `Eval/Plan/Check.lean`). §8.3 adds
"Check or run a Part V plan | `.../Semantics/Plan/Validity.lean` (`checkPlan`)" with no note that the two
"plans" are unrelated and no theorem connects them. Add one Pitfall line to `Plan/AGENTS.md` and word the
Entry Points row "Part V reference plan (not `EvalPlan`)".

Q5 otherwise verified: `LeanNCD.lean` imports `LeanNCD.Semantics`; patch 05 adds
`import LeanNCD.Semantics.Plan` to `LeanNCD/Semantics.lean` and `Plan.lean` imports all 8 modules;
`test/Semantics/AxiomAudit.lean` runs `#audit_axioms LeanNCD.Semantics` on `import LeanNCD.Semantics`,
so the Plan namespace (`LeanNCD.Semantics.Program.Plan`) is axiom-audited automatically (the plan
could cite this as axiom evidence alongside the token grep). Plan/AGENTS.md size: six one-line pitfalls is
about 1-1.5k characters, so ≤ ~3k is plausible; leanncd/AGENTS.md edits touch table rows, not injected
sections.

Q6 hygiene: every existing path in the plan `ls`-valid (mutations_post.json, record.md,
mutation-manifest.sh, lake-build.sh, prepare-worktree.sh, new-slice SKILL.md, token-report.py,
ExecutableReferenceTest.lean, CHECKPOINT.md); `Plan/AGENTS.md` is correctly marked new. No
`File.lean:NNN` in the plan. Risk table has fixture and cycle counts (2+4+5+8+1 = 20). Symbols are
`identifier @ file`. Plan is 609 lines. Unchecked or partial items:
- F6: one Global Constraint ("single sort `Q`") is not exact.
- Donors: §6.1 helper row and `clauseRow`/`verdict` have donor "—"; `startRow`'s "donor `runValidated`
  rows" names no fixture identifier (Minor).
- Reviewer briefs (§9 step 3) give no window sizes or line budgets (checklist last item; Minor).

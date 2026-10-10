# Plan layer, slice 1: Phase A3a prototype notes

Branch `worktree-plan-layer-slice1`. A3a commits: f8cc116c (Validity, Run), 23df4cd1 (fixtures),
3faeb6d (coverage-gap fixture `reinitMid`), ff02d4b (`#print axioms Valid.stepOK`), and this file.

## Files

| file | lines | content |
|---|---|---|
| `leanncd/LeanNCD/Semantics/Plan/Validity.lean` | 206 | `ReadyOK`, `Valid` (Definition 31.1, slice-1 form), `Valid.stepOK`, `occList`/`addrList` and their membership lemmas, the `check*` functions, `checkPlan`, soundness lemmas |
| `leanncd/LeanNCD/Semantics/Plan/Run.lean` | 173 | progress (`step_not_stuck`), the multi-step run lemma (`run_R`) and its `Start` corollaries |
| `leanncd/test/Semantics/PlanValidityTest.lean` | 93 | `clauseRow`/`verdict`, `checkPlan` verdicts on 6 valid and 9 invalid plans (`#eval check` and kernel `decide`) |
| `leanncd/test/Semantics/PlanRunTest.lean` | 50 | `Valid` from `checkPlan_sound` by `decide`; `run_R` instances on the tagged plan and the scalar failure plan |

## Theorems (all proved: no `sorry`, no new axiom, no `native_decide`)

Validity.lean:
- `Valid.stepOK`: a valid plan satisfies the A2 per-pc step condition `StepOK` at every pc. It uses only
  `initFresh`, `accOK` and `pubOK`.
- `mem_occList`, `mem_addrList`: every tagged occurrence, and every defined address, is in the enumeration.
- `checkSteps_ann`: if `checkSteps` holds and command pc is `[a]`, then `checkAnn pc a` holds.
- `target_eq`: an occurrence targets `⟨t, p⟩` iff its destination is p (bridges `OccRef.target` and the
  `∀ o : P.Occurrence t` form used by `InitOK`/`PubOK`).
- `checkInit_sound`, `checkAnn_acc_sound` (gives `AccOK ∧ ReadyOK`), `checkAnn_pub_sound`: per-annotation soundness.
- `checkPlan_sound`: `checkPlan π = true → π.Valid`.

Run.lean:
- `scanGroup_ne_stuck`: a group whose every footprint is readable never reports `stuck` in its scan.
- `foldlM_addAt_some`: the commit phase succeeds when every destination slot is initialised.
- `readPub_isSome`: under R, a published address is readable through the read view.
- `acc_slot_isSome`: under R, a materialised, unpublished address has an initialised slot.
- `step_not_stuck` (**progress**): a valid plan at an R-related state with a command left does not step to `stuck`.
  It needs no `refState` hypothesis; R suffices.
- `run_R` (**run lemma**): from R at pc with `c = refState pc`, the remaining run either finishes at
  `m = commands.length` with R and a reference execution `c →* c'`, or fails on o with a reference execution
  from c to `.failed o c''`. There is no stuck disjunct.
- `runPlan_R`, `runPlan_not_stuck`: the same from `Start`.

PlanRunTest.lean: `plan_valid`, `tagged_run_R` (R at pc 3 on the memory `runPlan` actually returns, no hand-chained
steps), `scalar_bad_matched` (failure at pc 3 on tensor 2, with the matched reference execution).

### `#print axioms`

Observed in this phase's builds:

| declaration | axioms |
|---|---|
| `Valid.stepOK` | `propext, Quot.sound` |
| `mem_occList` | `propext, Quot.sound` |
| `mem_addrList` | `propext, Classical.choice, Quot.sound` |
| `checkPlan_sound` | `propext, Classical.choice, Quot.sound` |
| `step_not_stuck` | `propext, Classical.choice, Quot.sound` |
| `run_R` | `propext, Classical.choice, Quot.sound` |
| `runPlan_R`, `runPlan_not_stuck` | `propext, Classical.choice, Quot.sound` |

`Classical.choice` enters only through Mathlib simp lemmas: `mem_addrList` gets it from the `Equiv` round trip on
`canonicalLayout … .enumerate`. It does not affect computability: `checkPlan` is evaluated by `#eval` and by
kernel `decide`.

## Observed fixture values

`verdict π = (checkPlan π, failing clauses in checkPlan order)`. Values are from the `#eval check` output of
`lake-build.sh … Semantics.PlanValidityTest`. Each one is also a kernel `example … := by decide`.

| fixture | checkPlan | first failing check | all failing clauses | run outcome (if recorded) |
|---|---|---|---|---|
| `plan` (tagged) | true | none | none | done 3, `[0,14,0]` |
| `pPlan 2 reciprocalBody` | true | none | none | done 3 |
| `pPlan 2 failureAfterBody` | true | none | none | failed at pc 1 |
| `sPlan true` | true | none | none | failed at pc 3, tensor 2 |
| `sPlan false` | true | none | none | done 5 |
| `chainPlan` | true | none | none | done 5, `[0,3,4]` |
| `earlyStep` (pub before acc) | false | `checkPubOrder` @1 | `pubOrder@1` | done 3, `[0,14,0]` (refState fails) |
| `dupGroup` | false | `checkCov1Nodup` | `cov1Nodup`, `accFresh@2` | done 4, `[0,16,0]` |
| `noInit` | false | `checkAccMat` @0 | `accMat@0`, `pubMat@1` | stuck 0 |
| `partialInit` (empty fibers unmaterialised) | false | `checkPubMat` @2 | `pubMat@2` | stuck 2 |
| `fused` | false | `checkSingleton` | `singleton` | stuck 0 |
| `chainEarly` (reads unpublished) | false | `checkReady` @1 | `ready@1` | stuck 1 |
| `missingOcc` | false | `checkCov1Complete` | `cov1Complete`, `pubOrder@2` | not recorded |
| `earlyHalf` (pub after one of two groups) | false | `checkPubOrder` @2 | `pubOrder@2` | done 4, `[0,14,0]` |
| `reinitMid` (**new**, re-init after consume) | false | `checkInit` @2 | `initFresh@2` | done 5, **`[0,10,0]`** (correct: 14) |

## Mutation controls (checker level, `Validity.lean`)

Each mutation was applied with Edit, and `lake-build.sh … LeanNCD.Semantics.Plan.Validity` was run. The file was then
restored with `git checkout -- leanncd/LeanNCD/Semantics/Plan/Validity.lean`, and `git status --short` came back empty
before the next cycle.

A broken `Validity.lean` blocks both test modules. So the fixture effect was measured by a scratch evaluator. It was
appended temporarily to `PlanValidityTest.lean`, built once, and then removed by `git checkout`. The evaluator
recomposes `checkPlan` from the real, unmutated `check*` functions, with the one mutated clause forced to true or dropped
(k = 0 is the original, k = 1..6 are mutants a..f). On all 6 valid plans every k gave true. The negative columns are
below.

The re-run of (d) after the gap fix was a real build. It applied the mutant and temporarily replaced the
`checkInit_sound` proof with `sorry`, so that the test module could elaborate. It was then restored and the tree was
clean.

| # | mutation | first proof failure | negative fixtures flipping false → true | caught by |
|---|---|---|---|---|
| a | `checkCov1Complete := π.occList.all fun _ => true` | `Validity.lean:193:19` `checkPlan_sound`: `h1c x (mem_occList π x)` has type `True`, expected `x ∈ π.accFlat` | **none**. `missingOcc` stays false via `pubOrder@2`; its clause row loses `cov1Complete` | (i) proof only. **Equivalent at the `checkPlan` level** (see N6) |
| b | drop `checkPubOrder` from `.pub` | `:179:10` `checkAnn_pub_sound`: unknown identifier `hn` (destructuring shape) | `earlyStep`, `earlyHalf` | (iii) both |
| c | drop `checkPubMat` from `.pub` | `:179:10` `checkAnn_pub_sound`: unknown identifier `hn`; `:174:58` unsolved goals | `partialInit` | (iii) both |
| d | `checkInit := S.all fun _ => (π.consList pc).all fun _ => true` | `:163:9` `checkInit_sound`: `rcases` failed on `∀ x ∈ π.consList pc, True` | **none of the original fixtures**: COVERAGE GAP. After 3faeb6d, `reinitMid` flips: `invalid-reinit-after-consume` got `((true, []), …)`, and `decide` proved `reinitMid.checkPlan = false` false | originally (i) only; after the fix (iii) both |
| e | `checkSingleton := π.commands.all fun _ => true` | `:192:50` `checkPlan_sound`: `hs cmd hc : True`, expected `cmd.length = 1` | `fused` | (iii) both |
| f | drop `checkReady` from `.acc` | `:171:10` `checkAnn_acc_sound`: unknown identifiers `hn`, `hc`; `:167:75` unsolved goals | `chainEarly` | (iii) both |

Mutant-form note: the first attempt at (a), `def checkCov1Complete : Bool := true`, dropped the `π` parameter. It failed
at `:138:42` with "Invalid field notation", which is a syntactic failure, not a semantic catch. All the trivialised
mutants (a, d, e) therefore keep their parameters (`… .all fun _ => true`).

Every proof failure in b, c and f is a failure of **destructuring shape** (`obtain` pattern arity) in a per-annotation
soundness lemma, not a failure of a downstream simulation proof. This is expected: `checkPlan_sound` is the only
consumer of the checks. What makes those three meaningful is the fixture flips, not the proof failures.

## Decision log

1. **Computable enumerations from the certified tensor list.** `occList` is a `flatMap` over `π.tensors`. It splits on
   `P.input t = false` with `dif`, takes `List.finRange` over statements and valuations, and keeps guarded valuations
   with `filterMap` (`if hg : guard … = true`). `addrList` maps `List.finRange (canonicalLayout …).count` through the
   layout's `enumerate` equivalence. Completeness (`mem_occList`, `mem_addrList`) comes from the plan's own
   `tensors_complete` field, so it is a proof, not a `decide`.
   - *Rejected:* quantifying through the `Fintype` instances `definedFintype`/`definedAddressFintype` (`Finset.univ`).
     They are noncomputable (A1 pitfall 6), so `#eval` cannot run them and kernel `decide` cannot reduce them.
     That would have forced `native_decide` or hand proofs for every fixture verdict.
2. **One Bool per `Valid` clause, soundness only.** `checkPlan` is a conjunction in the same order as the fields
   (`checkSteps` dispatches per pc to `checkAnn`). `checkPlan_sound` is the single direction Theorem 31.3 needs:
   accepted plans are correct. Completeness (`Valid → checkPlan = true`) was not proved. Nothing consumes it, and it
   would need the converse of every membership enumeration. This shape is also what lets `clauseRow` report each
   clause separately in fixtures.
3. **`checkSteps` is vacuous on non-singleton commands** (`| _ => true`). `checkSingleton` rejects them separately.
   The per-pc conditions are therefore only ever asserted at singleton positions, matching A2 decision 9.
4. **`ready` is a separate `Valid` field, not part of `StepOK`.** This keeps A2 decision 5: the step and failure
   proofs never use it. Only `step_not_stuck` does.
5. **`coverage1`/`coverage2` are `Valid` fields that no A3a proof uses.** Run.lean never reads them. They are carried
   for Lemma 31.2 (terminal adequacy) in A3b.
6. **Deviations from the A2 ValidityConditions list:**
   - Condition 3 was added as `ready`.
   - Coverage1/2 were added as the whole-plan clauses.
   - `tensors_nodup`/`tensors_complete` stay fields of `Plan`, not of `Valid`.
   - The A2 conjecture (per-step `AccOK`/`PubOK` imply the Coverage Nodup halves) was not pursued. `cov1Nodup` and
     `cov2Nodup` are still checked directly.
   - Otherwise `InitOK`/`AccOK`/`PubOK` are exactly the A2 list.
7. **Fixture verdicts are checked twice:** by `#eval check` (which prints the clause row) and by kernel `decide` on
   `checkPlan` (no `native_decide`). The `Valid` instances in PlanRunTest come from `checkPlan_sound (by decide)`.

## `Valid` field table

SAFETY means a field is needed by `step_R`/`step_failed` (through `Valid.stepOK` or directly in `run_R`). PROGRESS
means it is needed only to rule out `stuck` (`step_not_stuck`). TERMINAL means it is not used in A3a and is reserved
for Lemma 31.2.

| field | class | used by | spec clause |
|---|---|---|---|
| `singleton` | PROGRESS (profile) | `step_not_stuck`, and `run_R` to destructure `[a]`. A fused command steps to `stuck`, never to a wrong `ok` | slice-1 profile; not in 29.3 |
| `coverage1` | TERMINAL | none in A3a | 29.3 condition 1 |
| `coverage2` | TERMINAL | none in A3a | 29.3 condition 2 |
| `initFresh` | SAFETY | `Valid.stepOK` → `step_R` (`step_init`) | N2 (30.2/30.3 freshness) |
| `accOK` | SAFETY + PROGRESS | `step_R` (`step_acc`); `step_failed` (members ∉ `Cons pc`, `run_R:146`); `step_not_stuck` (Mat ⇒ slot initialised) | 30.2/30.3 materialisation; local halves of 29.3 condition 1 |
| `pubOK` | SAFETY + PROGRESS | `step_R` (`step_pub`: order, `Mat ∧ ¬Pub`); `step_not_stuck` (Mat ⇒ slot) | 29.3 condition 4 (order), N1 (Mat), local half of condition 2 |
| `ready` | PROGRESS only | `step_not_stuck` | 29.3 condition 3 (N3) |

## Defect audit (new or sharpened, for spec 29.3 and Definition 31.1)

- **N2 sharpened, now safety-critical with a witness.** `reinitMid` violates only `InitOK` and runs to `done` with
  `[0,10,0]` instead of `[0,14,0]`, which is a silent wrong answer. Definition 31.1 must state initZero freshness
  explicitly: no target is published, and no consumed occurrence targets it. Spec 30.2/30.3 ("materialise before
  update or read") does not imply it.
- **N6 (new): condition 1's covering half is redundant in Definition 31.1.** Take any occurrence y. By
  condition 2's covering half, `y.target` is published at some pc. Condition 4 at that pc then puts y in `Cons pc`,
  so y is in `accFlat`. Hence `cov2Complete ∧ pubOrder ⇒ cov1Complete`, and mutant a is `checkPlan`-equivalent.
  This is argued informally, **not proved in Lean**. The spec should either list it as a consequence or keep it
  explicitly as a diagnostic clause, and say which.
- **N7 (new): 29.3 should classify its conditions by role.** The prose "conditions 1–4 ensure the readiness …
  premises" conflates three roles:
  - Safety: condition 4, N1, N2 and group freshness.
  - Progress: condition 3 and the command profile.
  - Terminal adequacy: conditions 1 and 2.
  Definition 31.1 should say which lemma consumes each, as the field table above does.
- **N8 (wording): Definition 31.1 should be stated per command prefix.** It should use `Pub pc`, `Cons pc` and
  `Mat pc` (prefix-local), not whole-plan orderings. Every clause `checkPlan` decides is local to pc, and the proofs
  use them that way.
- **N4 reinforced:** three schedule-invalid plans (`earlyStep`, `dupGroup`, `reinitMid`) run to `done`, two of them
  with wrong values. Soundness rests on `checkPlan`, not on the runtime.

## Full build

`lake-build.sh <worktree>/leanncd` (default targets, including `Tests`) printed
`Build completed successfully (8778 jobs)` with no `error` lines. It ran after all mutations had been restored,
with 3faeb6d and ff02d4b in place. The only `sorry` warnings come from files outside this work: `Base/St.lean`,
`Base/Br.lean`, `Core/Weave.lean` and `Instances/StBr.lean`.

## Not done (A3b starts here)

- **Lemma 31.2 (terminal adequacy):** from `coverage1 ∧ coverage2` and R at `pc = m`, show that `refState m` is
  complete and that Decode succeeds (`decode_of_R` needs outputs ⊆ `Pub m`). This is the first consumer of the
  `coverage1`/`coverage2` fields.
- **Theorem 31.3:**
  - (a) A valid plan's `done` result decodes to the executor's model or denotation.
  - (b) A `failed` result implies no model, with a matched reference failure. Compare failure and no-model, not the
    snapshot (D5).
  - (c) Never stuck. This is already `runPlan_not_stuck`; A3b only restates it in 31.3's form.
- **Comparison fixtures against the executor's `run`:** outputs on every valid fixture, failure occurrence and
  no-model agreement on `failureAfterBody` and `sPlan true`, and the D5 snapshot difference recorded rather than
  asserted equal.
- **Final mutation list for the manifest:**
  - A2 a–f (b and e equivalent, N5).
  - A3a a–f above (a `checkPlan`-equivalent, N6; d covered only since 3faeb6d).
  - Lemma 31.2/31.3 mutants: drop `coverage2`, drop `cov2Complete`, and weaken Decode.

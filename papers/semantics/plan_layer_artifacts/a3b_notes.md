# Plan layer, slice 1: Phase A3b prototype notes

Branch `worktree-plan-layer-slice1`. A3b commits: 83f2b22 (Correctness.lean), c4cd0bc (comparison fixtures,
`missingPub`), and this file.

## Files

| file | lines | content |
|---|---|---|
| `leanncd/LeanNCD/Semantics/Plan/Correctness.lean` | 154 | `prefixAnn_length`, `Valid.order4`, `cov1_of_cov2_pubOrder` (N6), `complete_of_refState`, Lemma 31.2 `terminal_adequacy`, Theorem 31.3 `done_correct` (a), `failed_correct` (b), `done_or_failed` and `done_of_model` (c), `done_iff_model` |
| `leanncd/test/Semantics/PlanCorrectnessTest.lean` | 120 | runPlan versus executor `run` on all valid fixtures; 31.3 instances; negative fixture `missingPub` |
| `leanncd/LeanNCD/Semantics/Plan.lean` | +1 | imports `Plan.Correctness` |
| `leanncd/lakefile.toml` | +1 | `Semantics.PlanCorrectnessTest` added to the `Tests` globs |

## Theorems (all proved: no `sorry`, no new axiom, no `native_decide`)

Common context: `π : P.Plan`, `hv : π.Valid`, `η : P.Input`, `ops`; `m := π.commands.length`.

- `complete_of_refState`: if `π.refState ops η m = some c` then `P.Complete c`. Pending is empty because
  `refState_R2` gives `o ∈ c.pending t ↔ ¬ Cons m ⟨t,o⟩`, `Cons m = accFlat` (`prefixAnn_length`), and
  `coverage1.2` covers every occurrence. Every address is published because `refState_R2` gives
  `isSome ↔ Pub m`, and `Pub m a` holds by `P.input` or by `coverage2.2`. **This is the first consumer of
  `coverage1`/`coverage2`.**
- **Lemma 31.2** (`terminal_adequacy`):
  ```lean
  theorem terminal_adequacy (hv : π.Valid) (η : P.Input) {m : Nat} {M' : Memory K σ}
      (hrun : π.runPlan ops (Start η) = .done m M') :
      m = π.commands.length ∧ ∃ c, π.refState ops η m = some c ∧ π.R ops η m M' c ∧
        ∃ complete : P.Complete c,
          π.Decode m M' = some (P.outputProjection (P.finalStore c complete))
  ```
  In words: a `done` run stops at m, its memory is R-related to the deterministic reference state at m, that
  state is complete, and Decode returns the output projection of the reference final store. No extra
  hypothesis was needed. Every output coordinate is in `Pub m` via `R.published` and completeness, which then
  feeds `decode_of_R`.
- **Theorem 31.3 (a)** (`done_correct`):
  ```lean
  theorem done_correct (hv : π.Valid) (η : P.Input) {m : Nat} {M' : Memory K σ}
      (hrun : π.runPlan ops (Start η) = .done m M') :
      ∃ c, ∃ success : P.Successful ops η c,
        (∀ ρ, P.Models ops η ρ ↔ ρ = P.finalStore c success.2) ∧
        π.Decode m M' = some (P.outputProjection (P.finalStore c success.2)) ∧
        P.denotation ops η (P.successful_admInput ops η c success) =
          P.outputProjection (P.finalStore c success.2)
  ```
  In words: the model set is the singleton {finalStore}, Decode is its output projection, and that equals
  the denotation. Uses `successful_model`, `successful_unique` and `successful_denotation`, with
  `success = ⟨R.reach, complete⟩`.
- **Theorem 31.3 (b)** (`failed_correct`):
  ```lean
  theorem failed_correct (hv : π.Valid) (η : P.Input) {o : OccRef P} {pc : Nat}
      {M' : Memory K σ} (hrun : π.runPlan ops (Start η) = .failed o pc M') :
      ¬ ∃ ρ, P.Models ops η ρ
  ```
  Proof: the `run_R` failure branch gives `Execution … (.failed o'.1 o'.2 c')`, then `failed_no_model`. The
  failing occurrence and the memory are not compared (D5). `o' = o` is not even used.
- **Theorem 31.3 (c)**:
  ```lean
  theorem done_or_failed (hv : π.Valid) (η : P.Input) :
      (∃ M', π.runPlan ops (Start η) = .done π.commands.length M') ∨
        ∃ o pc M', π.runPlan ops (Start η) = .failed o pc M'
  theorem done_of_model (hv : π.Valid) (η : P.Input) {ρ : Store K σ}
      (hρ : P.Models ops η ρ) :
      ∃ M', π.runPlan ops (Start η) = .done π.commands.length M' ∧
        π.Decode π.commands.length M' = some (P.outputProjection ρ)
  ```
  Never stuck (the existing `runPlan_not_stuck` is the same fact in `≠` form). The converse: a model exists,
  so the run is `done` and decodes to that model's projection.
- Corollary (b)+(c) (`done_iff_model`): `(∃ m M', π.runPlan ops (Start η) = .done m M') ↔ ∃ ρ, P.Models ops η ρ`.
- Stretch N6 (`cov1_of_cov2_pubOrder`): `π.Valid → ∀ x, x ∈ π.accFlat`, proved WITHOUT using `coverage1`.
  It takes `accFlat_complete` (A2's D9 lemma) with `singleton`, `coverage2.2` and `Valid.order4`
  (condition 4 from `pubOK`).

PlanCorrectnessTest: `tagged_model_unique` (31.3 (a) on `taggedOut` through `plan_valid := checkPlan_sound
(by decide)`), `scalar_bad_no_model` (31.3 (b) on `sPlan true`), and `tagged_has_model` (`done_iff_model`).

### `#print axioms`

| declaration | axioms |
|---|---|
| `Valid.order4`, `cov1_of_cov2_pubOrder` | `propext, Quot.sound` |
| `complete_of_refState`, `terminal_adequacy`, `done_correct`, `failed_correct`, `done_or_failed`, `done_of_model`, `done_iff_model` | `propext, Classical.choice, Quot.sound` |
| `tagged_model_unique`, `scalar_bad_no_model`, `tagged_has_model` | `propext, Classical.choice, Quot.sound` |

## Observed comparison table (`lake-build.sh … Semantics.PlanCorrectnessTest`)

The plan side is `(kind, pc, readPub at pc of points 0..2)`. The executor side is
`(outcome.kind, published points 0..2 of the snapshot)`. The donor programs `program n body` and `routed` have
no output tensors, so their Decode is trivially `some`. For them the full read view is compared, which is
stronger. `taggedOut` is compared with the `tagged` donor run (the same program apart from output flags), as
`step-tagged-decode-vs-run` already does.

| fixture | runPlan | Decode / view | executor `run` | asserted |
|---|---|---|---|---|
| tagged (`plan`) | done 3 | `some [0,14,0]` | complete `[0,14,0]` | equal |
| reciprocal (`pPlan 2`) | done 3 | view `[3/4,0,0]` | complete `[3/4,0,0]` | equal |
| chain (`chainPlan`) | done 5 | view `[0,3,4]` | complete `[0,3,4]` | equal |
| scalarRole false | done 5 | `some 2` (tensor 1) | complete, tensor 1 = `some 2` | equal |
| failureAfter (`pPlan 2`) | failed (pc 1) | slot 0 = `some 0` (transactional) | failed; accumulator of point 0 = **2** | both fail; snapshot recorded (D5) |
| scalarRole true | failed (pc 3, tensor 2) | n/a | failed (tensor 2) | both fail |
| `missingPub` (new, invalid) | done 3, slots `[0,14,0]` | **`none`** | not run | `checkPlan = false`, `(false, ["cov2Complete"])`; `checkCov1Complete = true` |

`cmp-done-agree` asserts `[true, true, true, true]` for value equality on the four done cases.

## Mutation cycles (A3b)

Each cycle was applied with Edit, built, then restored with `git checkout -- <file>`. `git status --short` was
empty after each one.

1. **Checker: `checkCov2Complete := π.addrList.all fun _ => true`.** The first proof failure was
   `Validity.lean:193:60` `checkPlan_sound`, "Type mismatch `h2c x (mem_addrList π x)` has type `True`".
   For the fixture effect, `checkPlan_sound`'s coverage2 component was temporarily set to `sorry` and
   `Semantics.PlanCorrectnessTest` was built. Result: `missingPub` flips. `invalid-missing-publication` got
   `((true, []), …)`, and `decide` proved `missingPub.checkPlan = false` false
   (`PlanCorrectnessTest.lean:113:45`). No other fixture changed, which makes `missingPub` the only
   fixture-level catch. Caught by: both.
2. **Theorem: drop the `coverage2` field from `Valid`** (and its `checkPlan_sound` component). `Validity`,
   `Simulation` and `Run` still build, which confirms that no safety or progress proof uses it. The first
   failure was `Correctness.lean:33:37` (`cov1_of_cov2_pubOrder`) and `:55:30` (`complete_of_refState`),
   "Invalid field `coverage2`". The proof catch is by name. Semantic non-vacuity comes from `missingPub`:
   every remaining clause holds, the run is `done 3`, and Decode is `none`. So Lemma 31.2's conclusion is
   false without coverage2. Caught by: proof (fixture witness for the gap).
3. **Theorem: Decode ignores Pub** (`readPub := if π.Pub pc a ∨ True then M (place a) else none`). The first
   form, `M (place a)`, dropped the `π` parameter and failed syntactically with "Invalid field notation"
   (the same trap as A3a mutant a). The parameter-preserving form gives first failures at `Memory.lean:253:23`
   `readPub_eq` (unsolved goals) and `:254:39` (`hp : ¬(π.Pub pc a ∨ True)`). `decode_of_R`, and hence
   `terminal_adequacy`, depend on it. With `readPub_eq` and `Run.readPub_isSome` set to `sorry`, the test
   build first fails at `PlanStepTest.lean:134` `invalid-read-unpublished`, which got
   `("done", 4, none, [some 0, some 3, some 1])` (expected stuck at 1). The read view is shared by the kernels,
   so this matches A2 mutant f. The `missingPub` decode was not reached, because the build stops earlier.
   By argument it would give `some [0,14,0]`. Caught by: both.

## Consolidated mutation list (input to the manifest)

Failure text is copied from the A1/A2/A3a notes; old cycles were not re-run.

| id | file / function | mutation | first observed failure | caught by |
|---|---|---|---|---|
| A1-a | `Batch.lean` `accumulateBatch` | overwrite (`if dest = p then v x else acc`) | `Batch.lean:84:19 Type mismatch ih (Executor.consume …)` in `accumulateBatch_published`; fixture accRow `[0,5,0]` | both |
| A1-b | `Batch.lean` `accumulateBatch` | `G.dropLast.foldl` | `Batch.lean:80:19`, `:88:4`, `:99:4`, `:129:4`; accRow `[0,9,0]` | both |
| A1-c | `Memory.lean` `place` | index `/ 2` (collides) | `Memory.lean:30:91 Application type mismatch` in `place_injective`; `:242:21` `R_start.pubSlot` | proof |
| A1-d | `Memory.lean` `Decode` | zero-fill (`getD 0`, no check) | `Memory.lean:105:2 split_ifs failed` in `decode_some`; decode pc0 `some [0,0,0]` | both |
| A1-e | `Memory.lean` `SlotView` | map `acc x` whenever `¬Pub` (drop `Mat`) | `Memory.lean:241:17 unsolved goals` in `R_start.accSlot` | both |
| A2-a | `Step.lean` `addAt` | overwrite (`some (v x)`) | `Simulation.lean:297` `addAt_some`; tagged `[0,5,0]` | both |
| A2-b | `Step.lean` commit values | read raw memory `fun a => M (place a)` | `:461` `step_acc` `rw [view]` pattern not found; no fixture change | **equivalent** (N5) |
| A2-c | `Step.lean` `execPub` | writes (`ok (execInit B M)`) | `:512` `step_pub`; tagged and chain `[0,0,0]` | both |
| A2-d | fixture plan | initZero only `[addr 1]` | `ok2`: `decide` proves `plan.Mat 2 (addr 0)` false; `step-tagged-run` stuck at 2 | both |
| A2-e | `Step.lean` acc kernel | non-transactional `execAccSeq` | `:451` `step_acc`, `:577` `step_failed`: `split` fails; no fixture change | **equivalent** (N5) |
| A2-f | `Step.lean` scan/values | raw memory (`readPub … .or (M (place a))`) | `:463`, `:490` `step_acc`; `:583` `step_failed`; invalid-read-unpublished `("done", 4, [0,3,1])` | both |
| A3a-a | `Validity.lean` `checkCov1Complete` | `.all fun _ => true` | `Validity.lean:193:19` `checkPlan_sound`: `h1c x (mem_occList π x)` has type `True`; `missingOcc` stays false via `pubOrder@2` | **equivalent at checkPlan** (N6, now proved: `cov1_of_cov2_pubOrder`) |
| A3a-b | `Validity.lean` `checkAnn .pub` | drop `checkPubOrder` | `:179:10` `checkAnn_pub_sound` unknown identifier `hn`; `earlyStep`, `earlyHalf` flip | both |
| A3a-c | `Validity.lean` `checkAnn .pub` | drop `checkPubMat` | `:179:10` unknown identifier `hn`; `:174:58` unsolved goals; `partialInit` flips | both |
| A3a-d | `Validity.lean` `checkInit` | `.all fun _ => … true` | `:163:9` `checkInit_sound`: `rcases` failed; only `reinitMid` flips (added 3faeb6d) | both (needs `reinitMid`) |
| A3a-e | `Validity.lean` `checkSingleton` | `.all fun _ => true` | `:192:50` `checkPlan_sound`: `hs cmd hc : True`; `fused` flips | both |
| A3a-f | `Validity.lean` `checkAnn .acc` | drop `checkReady` | `:171:10` unknown identifiers `hn`, `hc`; `:167:75` unsolved goals; `chainEarly` flips | both |
| A3b-1 | `Validity.lean` `checkCov2Complete` | `.all fun _ => true` | `Validity.lean:193:60` `checkPlan_sound`: `h2c x (mem_addrList π x)` has type `True`; `missingPub` flips to `(true, [])` | both |
| A3b-2 | `Validity.lean` `Valid` | drop field `coverage2` | `Correctness.lean:33:37`, `:55:30` Invalid field `coverage2` (Run/Simulation unaffected) | proof (by name; `missingPub` is the semantic witness) |
| A3b-3 | `Memory.lean` `readPub` | ignore Pub (`Pub ∨ True`) | `Memory.lean:253:23` `readPub_eq` unsolved goals; `PlanStepTest.lean:134` invalid-read-unpublished `("done", 4, none, [some 0, some 3, some 1])` | both |

Mutant-form rule (A3a and A3b): a trivialised mutant must keep its `π` parameter. Otherwise the failure is
syntactic ("Invalid field notation"), not semantic.

## Decision log

1. **Lemma 31.2 is one theorem about `runPlan`, not about an arbitrary R-related state.** The `done` hypothesis
   pins `m` and `refState m` through `runPlan_R`. A helper `complete_of_refState` holds the coverage
   argument and needs only `refState m = some c`, not R.
2. **Completeness from `refState_R2`, not from R.** R2 also lives in R, but `refState_R2` needs no memory. So
   completeness is a fact about the plan's logical prefix plus coverage, which is reusable.
3. **31.3 (a) also states the denotation**, as `P.denotation … (successful_admInput …) = outputProjection`.
   The spec's "Equivalently … equals ⟦P⟧(η)" is therefore in the Lean statement.
4. **31.3 (b) compares no-model only.** `failed_correct` discards the occurrence and the snapshot (D5). The
   fixtures record the snapshot difference (plan slot 0 = 0; executor accumulator = 2) without asserting it.
5. **31.3 (c) is split** into `done_or_failed` (dichotomy, error-free and singleton profile) and
   `done_of_model` (converse). `done_iff_model` pairs (b) with (c). `runPlan_not_stuck` was not re-proved.
6. **Comparison on donors without outputs uses the read view at the stopping pc** (`readPub`). This is stronger
   than Decode, which is trivial there.
7. **N6 is proved, but `checkCov1Complete` was NOT dropped.** `cov1_of_cov2_pubOrder` shows that the
   `coverage1` covering half is derivable from `Valid` minus `coverage1.2`. So `checkCov1Complete` can be
   dropped from `checkPlan` without losing soundness: `checkPlan_sound` would build `coverage1.2` from it. It
   is kept as a diagnostic clause (`missingOcc` names it first), and removing it is a later decision.
   `coverage1.1` (Nodup) is independent (A2 `twice`).

## SPEC RESTATEMENT DRAFT (for the docs sweep; spec text untouched)

**Relation R_Π (30.4), with η explicit and pc-local sets `Pub pc`, `Cons pc`, `Mat pc` computed from
`commands.take pc`:**
- R1 (reach): Conf is reachable from `initial η`.
- R2 (agreement, as equations): `o ∈ U(t) ↔ (t,o) ∉ Cons pc`; `σ(a) defined ↔ a ∈ Pub pc`.
- R3 (memory): for a in Pub pc, `M[place a] = σ(a)`. For x with `x ∈ Mat pc ∧ x ∉ Pub pc`,
  `M[place x] = α(x)`. The layout view depends on pc only.
- R4 (retention): if x is unpublished and some consumed occurrence targets x, then x ∈ Mat pc.
- Decode at pc is partial. It succeeds iff every output coordinate is in Pub pc with an initialised slot, and
  it never fills.

**Definition 31.1 (slice-1 form), per command `pc` with `commands[pc] = [a]`:**

| condition | role | consumed by |
|---|---|---|
| profile: every command is a singleton | progress | `step_not_stuck`, `run_R` |
| initZero S: each x ∉ Pub pc, and no occurrence in Cons pc targets x (N2) | safety | `step_R` |
| acc G: G duplicate-free, G ∩ Cons pc = ∅, every target ∈ Mat pc | safety + progress | `step_R`, `step_failed`, `step_not_stuck` |
| acc G: every footprint address ∈ Pub pc (29.3 cond. 3) | progress | `step_not_stuck` |
| pub B: B duplicate-free, B ∩ Pub pc = ∅, B ⊆ Mat pc (N1), every occurrence targeting B ⊆ Cons pc (29.3 cond. 4) | safety + progress | `step_R`, `step_not_stuck` |
| whole plan: groups duplicate-free (cond. 1 Nodup) | (diagnostic; also forced by per-step AccOK success) | none in A3b |
| whole plan: blocks cover Addr_Def (cond. 2 covering) | terminal | `complete_of_refState` (Lemma 31.2) |
| whole plan: groups cover 𝒪_P (cond. 1 covering) | terminal, **derivable** from cond. 2 + cond. 4 (N6) | `complete_of_refState` |

**Lemma 31.2 (as formalized).** For a valid plan, if the run from Start η ends `done m M'`, then
`m = |commands|`. The deterministic reference state c at m exists and is R-related to M'. c is complete:
U = ∅ by coverage of 𝒪_P, and dom σ = Addr_Σ by coverage of Addr_Def plus inputs. Finally
`Decode_m(M') = ρ_c|Out`, where ρ_c is the final store of c.

**Theorem 31.3 (as formalized; error-free, singleton-command profile).** For a valid plan and a well-typed η:
- (a) `done m M'` ⇒ Models(P, η) = {ρ_c}, Decode = ρ_c|Out, and that equals ⟦P⟧(η).
- (b) `failed o pc M'` ⇒ Models(P, η) = ∅. Only no-model is claimed, not the occurrence or the snapshot.
- (c) The run is never stuck, so it is `done` or `failed`. If Models(P, η) is nonempty, the run is `done` with
  Decode = ρ|Out. Hence `done ⇔ Models ≠ ∅`.

**Defects and wording changes, A1 to A3b:**
- D1: R needs reachability (R1). Resolved: R1 is kept and used through conservation (`acc_zero_of_unconsumed`).
- D2: the layout view depends on pc only. Resolved: `SlotView π pc`.
- D3: state R2 as iff-equations. Resolved.
- D4: "implements the annotations" is redundant. Discharged: `refState (pc+1)` comes out of the step lemmas.
- D5: failure-prefix wording. Resolved: 31.3 (b) compares no-model, not the snapshot or the occurrence
  (executor accumulator 2 versus plan 0).
- D6: Decode is partial; its success belongs to Lemma 31.2. Resolved: `terminal_adequacy`.
- D7, D8, D11, D12: **not recorded in the A1–A3a artifact notes.** Their source (the pre-A1 brief) is not in
  this phase's inputs, so they are not reconstructed here.
- D9: cond. 1 covering follows from cond. 2 and cond. 4. Proved (`accFlat_complete`, `cov1_of_cov2_pubOrder`).
- D10: the Accumulate premises suffice, with Nodup as the list form of "G is a set". Resolved.
- N1: every pub member must be materialised, including empty fibers. Added to PubOK.
- N2: initZero freshness. Added (`InitOK`). It is safety-critical (`reinitMid` silently returns 10).
- N3: cond. 3 is a progress premise, not a simulation premise. Reclassified.
- N4: runPlan does not detect invalid plans. Soundness rests on `checkPlan`; the spec should state this.
- N5: A2 mutants b and e are equivalent, because PlanFailed carries no state. Listed as equivalent.
- N6: cond. 1 covering is redundant. **Proved in Lean (A3b).** The spec should list it as a consequence.
- N7: classify the 31.1 conditions by role (safety / progress / terminal). See the table above.
- N8: state Definition 31.1 per command prefix (Pub pc / Cons pc / Mat pc). See the table above.
- New wording (A3b): the spec's Lemma 31.2 argument routes through "every output address lies in Need_pub,
  so its pub resource is mapped". In slice 1, at pc = m, `Pub m = Addr_Σ` already, so `decode_of_R` needs no
  Need_pub argument. The 31.1 sentence "Terminal adequacy … follows from the others" is accurate: it follows
  from condition 1 (coverage) plus R.

## Full build

See the final report of this phase. A full default build was run once, after all mutation cycles were
restored.

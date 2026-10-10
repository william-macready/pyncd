# Plan layer, slice 1: Phase A2 prototype notes

Branch `worktree-plan-layer-slice1` (A2 base `c6498da9`). Namespace `LeanNCD.Semantics.Program.Plan`.
Every value below was printed by a build. None was derived by hand.

## Files

| File | Lines | Content |
|---|---|---|
| `leanncd/LeanNCD/Semantics/Plan/Syntax.lean` | 216 | A1 file; `Program.Plan` gains `tensors`, `tensors_nodup`, `tensors_complete` |
| `leanncd/LeanNCD/Semantics/Plan/Step.lean` | 157 | `OccRef.dest`/`target`, `StepResult`, `PlanOutcome`, `Singleton`, `validateInput`/`startValidated`, kernels `execInit`/`execAcc`/`execPub`, `stepPlan`, `runFrom`/`runPlan` |
| `leanncd/LeanNCD/Semantics/Plan/Simulation.lean` | 614 | prefix-set succ lemmas, `InitOK`/`AccOK`/`PubOK`/`AnnOK`/`StepOK`/`Order4`, D9, `refState_succ`, R2 from `refState`, kernel memory lemmas, `step_init`/`step_acc`/`step_pub`/`step_R`, `step_failed` |
| `leanncd/LeanNCD/Semantics/Plan.lean` | 5 | aggregator, now imports Step and Simulation |
| `leanncd/test/Semantics/PlanFixtures.lean` | 73 | `unitPlan`/`scalarPlan` constructors (plans now carry tensors) |
| `leanncd/test/Semantics/PlanStepTest.lean` | 169 | `runPlan` fixtures versus the executor's `run`; invalid plans |
| `leanncd/test/Semantics/PlanSimulationTest.lean` | 128 | R at every pc of the tagged run (proof), failure matching (proof), D9 counterexample (proof) |

`PlanBatchTest`/`PlanMemoryTest` changed one line each (plan constructor). Both new test modules are in the
`lakefile.toml` `Tests` globs by module name.

## Kernels (what was built)

- `execInit S M`: `S.foldl (writeDef · · 0)`; `0` is the `AddCommMonoid` zero, as `Program.initial` uses.
- `execAcc pc G M` (transactional): `scanGroup` evaluates every member with `evalReady` on `readPub pc M`
  (first member in list order that is `.notReady` gives `stuck`, `.evaluated none` gives `semFail x`); only if
  all succeed, `G.foldlM (addAt v) M` adds each value into `place x.dest`, which must be `some` (else `stuck`).
- `execPub B M = ok M` if every member slot is `some`, else `stuck`. It writes nothing.
- `stepPlan pc M` runs `commands[pc]?` if it is a singleton `[a]`; a fused command or `pc ≥ m` is `stuck`.
- `runFrom` is structural on the remaining command list (no fuel); `runPlan M = runFrom 0 M commands`.
  A failure reports `failed o pc M` with the PRE-step memory.

## Theorems (all proved: no `sorry`, no new axiom, no `native_decide`)

Step.lean
- `validateInput_accepts`/`validateInput_error`: plan-side copies of `validate_accepts`/`validate_error`.

Simulation.lean
- `prefixAnn_succ`, `cons_succ`, `pub_succ`, `mat_succ`: with `commands[pc]? = some [a]`, the prefix sets at
  `pc+1` are those at `pc` plus `a`'s groups/blocks/inits.
- `slotView_pub`, `slotView_acc`: the slot view maps a resource iff `Pub` (resp. `Mat ∧ ¬Pub`).
- **`refState_succ`, `refState_succ_single` (D4)**: `refState (pc+1) = (refState pc).bind (postAnn · a)`.
- `publishBlock_published_not_mem`/`_mem`/`publishBlock_isSome`: the published store after a block.
- `postAnn_bookkeeping`, `foldlM_bookkeeping`: pending = U minus groups, published = old plus blocks.
- **`refState_R2`**: `refState η pc = some c` implies R2 (`o ∈ pending ↔ ¬Cons pc`, `isSome ↔ Pub pc`).
  No coverage hypothesis is needed; the lemma A1 left open is closed.
- **`accFlat_complete` (D9)**: `Singleton ∧ (∀ y, y ∈ pubFlat) ∧ Order4 → ∀ x, x ∈ accFlat`.
- `acc_zero_of_unconsumed`: under R, an address no consumed occurrence targets has accumulator `0`.
  It uses R1 through `reachable_invariant`/`conservation`.
- `dest_not_pub`: under R, an unconsumed occurrence's destination is not in `Pub pc`. It uses R1, via the
  invariant "published implies empty fiber".
- `execInit_not_mem`/`execInit_mem`, `addAt_some`, `commit_other`, `single_target`/`single_ne`,
  **`commit_def`**: a committed group adds exactly `delta G v` at every defined address
  (`M' (place y) = (M (place y)).map (· + Δ_G y)`), and it leaves untargeted addresses unchanged.
- `scanGroup_ne_ok`, `scanGroup_none`, `scanGroup_semFail`, `evalValue_eq`: these describe the evaluation phase.
- **`step_init`, `step_acc`, `step_pub`**: assume R η pc M c, `refState pc = some c`, the singleton command, its
  `*OK` condition, and a kernel result `ok M'`. Then there is a c' with `refState (pc+1) = some c'`,
  `R η (pc+1) M' c'`, and an `Execution` from c to c'. initZero is the stutter (`events = []`, `c' = c`).
- **`step_R`**: the same statement for any annotation, about `stepPlan … = .ok M'`.
- **`step_failed`**: assume R, `commands[pc]? = some cmd`, "acc members ∉ Cons pc", and `stepPlan … = .semFail o`.
  Then `Execution [.undefined o.1 o.2] (.running c) (.failed o.1 o.2 c)`.
- `step_failed_no_model`: the same hypotheses give `¬ ∃ ρ, Models η ρ`.

PlanSimulationTest.lean
- `tagged_R_every_pc`: R holds at pc 0..3 for the actual run memories `Start η0, m1, m2, m3`, each with
  a `refState` witness, by chaining `R_start` and `step_R`. `finalMemory taggedRun = m3` holds by `rfl`.
- `failure_matched`: on failureAfterBody, the plan's `semFail (statement 1)` at pc 1 matches a reference
  `undefined` segment from `refState 1`, and the input has no model.
- `twice_pub_complete`, `twice_order4`, `twice_not_disjoint`: the D9 counterexample.

### `#print axioms`

`accFlat_complete` uses `[propext, Quot.sound]`. Each of `refState_succ_single`, `refState_R2`,
`acc_zero_of_unconsumed`, `commit_def`, `step_init`, `step_acc`, `step_pub`, `step_R`, `step_failed`
and `step_failed_no_model` uses `[propext, Classical.choice, Quot.sound]`. This is the same set as A1's
theorems and `result_failure`. `validateInput_accepts` and `validateInput_error` use `[propext, Quot.sound]`.
The fixture theorems `tagged_R_every_pc`, `failure_matched`, `twice_order4` and `twice_not_disjoint` use
`[propext, Classical.choice, Quot.sound]`. The remaining helper lemmas have no print of their own. Each is used
by a printed theorem, so its axiom set is a subset of that theorem's set and contains no `sorryAx`.

## Observed fixture values

| check | observed |
|---|---|
| step-tagged-run | `("done", 3, none, [some 0, some 14, some 0])` |
| step-tagged-decode-vs-run (Decode 3, executor `taggedResult`) | `(some [some 0, some 14, some 0], "complete", [some 0, some 14, some 0])` |
| step-tagged-trace (slots at pc 0..3) | `[none×3]`, `[0,0,0]`, `[0,14,0]`, `[0,14,0]` |
| step-reciprocal (run; `summarize 2 reciprocalBody`) | `("done", 3, none, [3/4, 0, 0])`; `("complete", 5, [3/4, 0, 0], 0)` |
| step-reciprocal-readview at pc 3 | `[some 3/4, some 0, some 0]` (collect 1/2 + 1/4 = 3/4, not 1/(2+4) = 1/6) |
| step-failure-after (plan; executor) | `("failed", 1, some (1, 0), [some 0, some 0, some 0])`; `("failed", some (1, 0))` |
| step-scalar-bad (plan; executor tensor) | `("failed", 3, some 2, [some 7, some 2, some 0])`; `("failed", some 2)` |
| step-scalar-good (plan; Decode output 1; executor) | `("done", 5, none, [some 7, some 2, some 3])`, `some 2`, `"complete"` |
| step-start-validated (scalarBinding, all-none, extraDefined, simultaneous) | `[("ok",99), ("error",0), ("error",1), ("error",0)]` (same as donor `runValidated`) |
| step-chain (plan; executor) | `("done", 5, none, [0, 3, 4])`; `"complete", [some 0, some 3, some 4]` |
| invalid-read-unpublished (acc s1 before s0 is published) | `("stuck", 1, none, [some 0, some 0, some 0])` |
| invalid-publish-before-acc | run `("done", 3, none, [0, 14, 0])`, `refState 2 isSome = false` (a mismatch, not caught by the run) |
| invalid-missing-init | `("stuck", 0, none, [none, none, none])` |
| invalid-missing-init-empty-fiber (initZero only point 1) | `("stuck", 2, none, [none, some 14, none])` |
| invalid-duplicate-member (occ 0 0 in two groups) | run `("done", 4, none, [0, 16, 0])`, `refState 3 isSome = false` |
| invalid-fused (two annotations in one command) | `("stuck", 0, none, [none, none, none])` |
| sim-tagged-m-rows (m1, m2, m3) | `[[0,0,0], [0,14,0], [0,14,0]]` |

Failure snapshot comparison for failureAfterBody: the executor's `run` committed `lit 2` first, so its
snapshot accumulator at point 0 is 2 (A0 donor `failure-retained-snapshot`). The transactional plan
committed nothing: slot 0 is 0, and the matched reference segment ends in `.failed … c` with `c = refState 1`.
**Both report the same occurrence (statement 1).**

## Mutation controls

Each mutation was applied by hand and built. The resulting failure was recorded. The file was then restored
with `git checkout -- <file>`, and `git status --short` came back empty. Fixture values for kernel mutations
came from an untracked scratch module that imports only `Plan.Step` and the donors. That module was deleted.
It was needed because `PlanFixtures` imports `Plan`, so a broken `Simulation.lean` would block every fixture.

| # | mutation | proof failure (first) | fixture effect | caught by |
|---|---|---|---|---|
| a | `addAt` overwrites (`some (v x)`) | `Simulation.lean:297` `addAt_some` (rfl mismatch) | tagged `[0, 5, 0]` (expected 14) | proof + fixture |
| b | commit values read raw memory `fun a => M (place a)` (readiness still on `readPub`) | `:461` `step_acc` `rw [view]` pattern not found | **no fixture change** (all rows identical) | proof only |
| c | `execPub` writes (`ok (execInit B M)`) | `:512` `step_pub` (`execInit B M` ≠ `M`) | tagged `[0,0,0]`; chain `[0,0,0]` | proof + fixture |
| d | fixture plan initZero only `[addr 1]` (empty-fiber points 0, 2 not materialised) | `ok2`: `decide` proves `plan.Mat 2 (addr 0)` and `(addr 2)` false | `step-tagged-run` got `("stuck", 2, …, [none, some 14, none])`; decode `none`; trace `none` at pc 3 | proof + fixture |
| e | non-transactional `execAccSeq` (evaluate, commit, continue) | `:451` `step_acc` and `:577` `step_failed`: `split` fails | **no fixture change** | proof only |
| f | scan and values on raw memory (`readPub … .or (M (place a))`) | `:463`, `:490` `step_acc`; `:583` `step_failed` | invalid-read-unpublished becomes `("done", 4, [0, 3, 1])` (expected stuck at 1) | proof + fixture |

Mutants b and e are **observationally equivalent** in this model.
- For b: once `scanGroup` succeeds on `readPub`, every footprint address is published, and `readPub` agrees with raw memory there (`evalWith_stable`).
- For e: `semFail` carries no memory, and `readPub` hides the unpublished accumulator slots that a prefix commit changes.

Their proof failures are failures of proof shape. A3's mutation manifest should list them as equivalent mutants or strengthen the observation, for example by having `PlanFailed` expose memory.

## Decision log

1. **Singleton commands.** `Command` stays `List (Ann P)`. `Singleton π := ∀ cmd ∈ commands, ∃ a, cmd = [a]`.
   `stepCommand` is `stuck` on anything else, as fixture invalid-fused shows. The step lemmas take `commands[pc]? = some [a]`.
2. **Plan carries `tensors`** (scope ii). `validateInput` is a copy of `Executor.validate` over `π.tensors`, and
   `startValidated` returns `(input, Start input)`. It was cheap, so it was done.
3. **Transactional acc** (scope iii). Evaluation reads `readPub pc M` only and never sees the reference state.
4. **`addVal x a b := a + b`** fixes the `AddCommMonoid` index at `x.1`. Without it, instance search fails on
   `K (σ.signature (place x.dest).1).sort` (`HAdd` synth failure).
5. **`StepOK` excludes condition 3** (footprint ⊆ Pub). No step or failure proof needed it, so StepOK holds
   exactly what the proofs used. Condition 3 is a progress obligation for A3.
6. **The acc condition "destination ∉ Pub" is not a hypothesis.** It is derived from R1 (`dest_not_pub`).
7. **R2 fields of the post-state come from `refState_R2`, not per-kernel.** Each step lemma proves
   `postAnn c a = some c'`, and R2 then follows.
8. **The R-at-every-pc fixture is a proof, not `decide`.** `stepPlan` equalities close by `rfl` (kernel reduction,
   ℚ included). `decide` fails because `StepResult` has no `DecidableEq`.
9. Order4 is stated per command (singleton positions). For fused commands it must refer to expanded positions.

## ValidityConditions (what the proofs needed; input to `checkPlan` and to Definition 31.1)

Structural: `tensors_nodup`, `tensors_complete`, and `Singleton π`.

Per `pc < m` with `commands[pc]? = some [a]`. Together these are `StepOK π pc`:

- **initZero S** (`InitOK`): for every x ∈ S, `x.addr ∉ Pub pc`, and no occurrence in `Cons pc` has destination x.
  S need not be duplicate-free.
- **acc G** (`AccOK`): `G.Nodup`; for every x ∈ G, `x ∉ Cons pc` and `x.target ∈ Mat pc`.
- **pub B** (`PubOK`): `B.Nodup`; for every x ∈ B, `x.addr ∉ Pub pc`, `x ∈ Mat pc` (N1), and every occurrence with
  destination x is in `Cons pc` (condition 4, local to pc).

Failure matching needs only: acc members ∉ `Cons pc`.

The step and failure proofs do NOT need the following conditions. A3 does need them:
- Condition 3 (footprint ⊆ `Pub pc`), for progress (`stepPlan ≠ stuck`).
- The commit and publish slots being initialised. Both follow from `Mat ∧ ¬Pub` plus `R.accSlot`, so they are progress lemmas, not conditions.
- `Coverage1 ∧ Coverage2` at pc = m, for terminal adequacy and Decode (`decode_of_R` needs outputs ⊆ `Pub m`).
- Conjecture, **not proved in Lean**: `AccOK`/`PubOK` at every pc imply the Nodup/disjointness halves of Coverage1/2. The union halves need Coverage2-union, and Coverage1-union then follows by D9 (`accFlat_complete`).

The universally quantified `∀ o : P.Occurrence x.1` clauses need a computable enumeration for `checkPlan`.
Beware A1 pitfall 6: the `Fintype` route goes through the noncomputable `definedFintype`.

## Defect audit

- **D1 (R needs reachability): CONFIRMED IN LEAN.** `step_init` and `step_acc` use R1 through
  `acc_zero_of_unconsumed` (conservation) and `dest_not_pub` (published implies empty fiber). Without R1,
  R2-R4 cannot show that a re-materialised accumulator or an acc destination is safe.
- **D4 ("implements the annotations" is redundant): DISCHARGED for singleton commands.**
  `refState_succ_single` and the step lemmas conclude `conf' = refState (pc+1)`. The matching segment is
  then produced, not assumed (`postAnn_execution`).
- **D5 (failure-prefix wording, spec 31.3 and 32.1):** a transactional kernel's matching segment is exactly
  one `undefined` event from Conf, and the snapshot is Conf itself (`step_failed`). The spec's
  `Conf →* Failed(o, σ', α', U')` is satisfied with zero preceding contributions. The executor's `run` on the same input reaches a
  DIFFERENT failure snapshot (accumulator 2 versus 0). It agrees here on o only by coincidence of order, because
  the plan picks the first failing member in list order. Theorem 31.3 should compare failure, and no-model,
  not the snapshot, and in general not the occurrence.
- **D9: PROVED** (`accFlat_complete`, singleton profile). For disjointness, the plan `twice` (the group
  accumulated twice) satisfies Coverage2-union and Order4 but `¬ accFlat.Nodup`. All three facts are proved.
- **N1 sharpened:** the proof needs each published member x to have `SlotView pc (.acc x)` mapped, which is
  `Mat pc x ∧ ¬Pub pc x.addr`. This applies to every defined address, including empty fibers. Mutation d and fixture
  invalid-missing-init-empty-fiber (stuck at pc 2) both show it.
- **N2 (new): initZero needs freshness.** Spec 30.2 and 30.3 require materialisation "before a kernel updates
  or reads", but say nothing against re-materialising. initZero on a published slot breaks `pubSlot`. On an address with a consumed
  contribution, it resets the accumulator and breaks `accSlot`. `InitOK` is the condition the proof needs.
- **N3 (new): condition 3 is not a simulation premise.** It is only a progress premise. Spec 29.3 says
  conditions 1-4 "ensure the readiness … premises at each successful prefix". In the plan, readiness is enforced
  dynamically by the read view, so a plan that violates condition 3 gets stuck (invalid-read-unpublished). It is not unsound.
- **N4 (new): `runPlan` does not detect a schedule-invalid plan.** Publish-before-acc and duplicate group
  membership both run to `done`, with decodes 14 and 16, while `refState` fails. Soundness rests entirely on
  `checkPlan`. Spec 31.1's "accepted plan" framing is consistent with this, but it is worth stating.
- **N5 (new): two of the brief's mutants are equivalent** (b, e above). This is because spec 30.1's
  `PlanFailed(o)` carries no concrete state.

## Full build

`lake-build.sh <worktree>/leanncd` (default targets, including `Tests`) printed
`Build completed successfully (8774 jobs)` and no `error` lines. It ran after all mutations had been restored.
The only `sorry` warnings come from files outside this work: `Base/St.lean`, `Base/Br.lean`,
`Core/Weave.lean` and `Instances/StBr.lean`. After that build, `#print axioms` lines were added to
`Step.lean` and `PlanSimulationTest.lean`, and a targeted rebuild of `Semantics.PlanSimulationTest`
printed `Build completed successfully (2969 jobs)`.

## Not done (A3 starts here)

- `checkPlan` with computable `StepOK`, and the per-pc conditions above, packaged as Definition 31.1.
- Progress: `StepOK ∧ condition 3 ∧ R → stepPlan ≠ stuck`. This also covers commit and publish slots being initialised.
- Multi-step `runFrom` simulation by induction. The fixtures only chain `step_R` by hand. Then Lemma 31.2
  (Coverage at m gives Complete and Decode success) and Theorem 31.3.
- Comparison with `run`, and the mutation manifest. That manifest should mark b and e as equivalent mutants.
- The conjecture that per-step `AccOK`/`PubOK` imply Coverage Nodup, which is unproved.

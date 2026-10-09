# Plan layer, slice 1: Phase A1 prototype notes

Branch `worktree-plan-layer-slice1` (base `3d721f96`). Namespace `LeanNCD.Semantics.Program.Plan`.
Every value below was printed by a build. None was derived by hand.

## Files

| File | Lines | Content |
|---|---|---|
| `leanncd/LeanNCD/Semantics/Plan/Syntax.lean` | 210 | `OccRef`, `DefAddr`, `Ann`, `Command`, structure `Program.Plan`, `ann`, `prefixAnn`, `Pub`/`Cons`/`Mat`, singleton-key view |
| `leanncd/LeanNCD/Semantics/Plan/Batch.lean` | 201 | `Execution.append`, `accumulateBatch`, `delta`, `publishBlock`, Lemma 32.1 |
| `leanncd/LeanNCD/Semantics/Plan/Memory.lean` | 287 | `Slot`, `Memory`, `place`, `Resource`, `SlotView`, `Start`, `readPub`, `Decode`, `postAnn`/`refState`, `R` |
| `leanncd/LeanNCD/Semantics/Plan.lean` | 3 | aggregator (imported from `LeanNCD/Semantics.lean`) |
| `leanncd/test/Semantics/PlanFixtures.lean` | 59 | `taggedOut`, `plan`, `group`/`groupPerm`, `mem3`/`mem3Hole` |
| `leanncd/test/Semantics/PlanBatchTest.lean` | 58 | batch and post-state fixtures |
| `leanncd/test/Semantics/PlanMemoryTest.lean` | 49 | place, Start, SlotView, Decode, R_start fixtures |

The three test modules are listed in the `Tests` globs of `lakefile.toml`.

## Theorems (all proved, no `sorry`, no new axiom, no `native_decide`)

Syntax.lean
- `DefAddr.addr_injective`: the embedding of defined addresses into `Address σ` is injective.
- `Ann.occKey_injective` and `Ann.pubKey_injective`: the singleton-key constructors are injective.
- `keys_perm_aux` and `flatKeys_perm`: the flattened key list is a permutation of the occurrence keys followed by the publication keys.
- `coverage_iff_schedule`: spec 29.3 conditions 1-2 (`Coverage1 ∧ Coverage2`: the flattened groups and blocks are duplicate-free and complete) hold **iff** `flatKeys.Nodup ∧ ∀ k, k ∈ flatKeys`. These are exactly `Schedule.keys_nodup` and `keys_complete`. This is **proved**, not checked with `#eval`.
- `prefixAnn_zero`, `not_cons_zero`, `not_mat_zero`, `pub_zero`: at pc = 0 the prefix sets are empty and `Pub` holds only for inputs.

Batch.lean
- `Executor.Execution.append`: two executions that share an endpoint concatenate.
- `consume_accumulators`: `Executor.consume` adds `single x w`, a `Pi.single` increment.
- `consume_pending`: `consume` removes exactly the identity `x`.
- `accumulateBatch_published`: a batch leaves `published` unchanged.
- `accumulateBatch_accumulators`: the post-batch accumulator is `α + Δ_G`, where `delta` is a sum of `single`s (Lemma 32.1, accumulator half).
- `accumulateBatch_pending`: `o` remains pending iff it was pending and `⟨t,o⟩ ∉ G`, which is `U \ G`.
- `accumulateBatch_perm`: if `G ~ G'` then both batches reach the same state (`List.Perm.sum_eq`).
- **`batch_execution` (Lemma 32.1)**: suppose `G.Nodup`, every member is pending, and each member's `evalReady … = .evaluated (some (v x))`. Then `Execution P ops (contributionEvents G v) (.running c) (.running (accumulateBatch c G v))`.
- `batch_execution_perm`: any enumeration `G'` of the group yields an execution to the same state.
- `publishBlock_accumulators` and `publishBlock_pending`: publishing a block leaves both unchanged.
- **`block_execution`**: suppose `B.Nodup`, every member is unpublished, and every member's fiber is empty. Then there is an `Execution` of one publication event per member that ends at `publishBlock c B`.

Memory.lean
- `place_injective`: `place` is injective.
- `slotView_injective`: two resources mapped to the same slot are equal. A `pub a` and an `acc a` are never mapped together.
- `start_noninput`: Start leaves every non-input slot uninitialised.
- `decode_some`: if Decode succeeds, its value is `readPub` at every output coordinate.
- `evalValue_ready`: whenever `evalValue` succeeds, `evalReady` evaluates to its value.
- `postAnn_execution` and `foldlM_execution`: a successful logical post-state has a matching reference segment.
- **`refState_execution` and `refState_reaches`**: `refState η pc = some c` implies that `c` is reachable from `initial η` by an `Execution`. This is the "success yields `Reaches`" lemma.
- **`R_start`**: `R η 0 (Start η) (initial η)`, which is Lemma 31.2's initialisation obligation.
- **`readPub_eq`**: under R, `fun a => if a ∈ Pub(pc) then M (place a) else none` equals `c.published`.
- `decode_of_R`: under R, if every output coordinate is in `Pub(pc)`, then Decode succeeds and returns the reference published values.

### `#print axioms`

`DefAddr.addr_injective` and `coverage_iff_schedule` use `[propext, Quot.sound]`. Every other printed theorem uses `[propext, Classical.choice, Quot.sound]`: `Execution.append`, `consume_accumulators`, `accumulateBatch_{accumulators,pending,perm}`, `batch_execution`, `batch_execution_perm`, `block_execution`, `place_injective`, `slotView_injective`, `start_noninput`, `decode_some`, `postAnn_execution`, `refState_execution`, `refState_reaches`, `R_start`, `readPub_eq` and `decode_of_R`. The existing reference theorems carry the same set; for example, `result_failure` does.

## Observed fixture values

The fixture is `taggedOut`: `tagged` with `output := true`. Its four occurrences go to point 1 with values 2, 2, 5, 5. The plan is `[[initZero p0..p2], [acc group], [pub p0..p2]]`.

| check | observed |
|---|---|
| batch-accumulators (accRow after the batch) | `[0, 14, 0]` |
| batch-published | `[none, none, none]` (unchanged) |
| batch-pending (card) | `0` |
| batch-permuted (`groupPerm`) | `[0, 14, 0]` |
| batch-agrees-reference (vs `taggedResult`) | `([0, 14, 0], [some 0, some 14, some 0])` |
| refState-prefixes pc = 0..3 | `[0,0,0]/none×3`, `[0,0,0]/none×3`, `[0,14,0]/none×3`, `[0,14,0]/[some 0, some 14, some 0]` |
| refState-early-publish (pub before acc), pc = 2 | `isSome = false` |
| flat-schedule (acc, pub, keys, nodup, nodup) | `(4, 3, 7, true, true)` |
| place-indices | `[0, 1, 2]` |
| start-scalar (`scalarRole true`, input 7) | `[some 7, none, none]` |
| start-tagged | `[none, none, none]` |
| slotview-acc point 1, pc = 0..3 | `[false, true, true, false]` |
| slotview-pub point 1, pc = 0..3 | `[false, false, false, true]` |
| decode (pc0 Start, pc2 mem3, pc3 mem3, pc3 mem3Hole) | `(none, none, some [0, 14, 0], none)` |
| readview-pc3 vs refState 3 | `([some 0, some 14, some 0], some [some 0, some 14, some 0])` |

These are elaborated `example`s:
- `batch_execution` and `batch_execution_perm` on `start0`/`group`, discharged by `decide` and `rfl`.
- `place_injective` at `declarations`.
- `R_start` for `plan` and for an empty plan over `scalarRole true`.

## Mutation controls

Each mutation was applied by hand and built. The resulting failure was recorded. The file was then restored with `git checkout -- <file>`, `git status` came back clean, and the build was green again.

Because the proofs fail first, the fixtures never run. To get fixture-level values, each mutated expression was also evaluated once in a scratch file. That file was deleted and was never committed.

| # | mutation | build failure (first lines) | mutated fixture value |
|---|---|---|---|
| a | `accumulateBatch` overwrites (`if dest = p then v x else acc`) | `Batch.lean:84:19 Type mismatch ih (Executor.consume …)` in `accumulateBatch_published`; `'change' tactic failed` in `_accumulators`/`_pending`; `Batch.lean:133 Type mismatch` in `batch_execution` | accRow `[0, 5, 0]` (expected 14) |
| b | `G.dropLast.foldl` (skips the last member) | same four sites: `Batch.lean:80:19`, `:88:4`, `:99:4`, `:129:4` | accRow `[0, 9, 0]` |
| c | `place` index `/ 2` (collides) | `Memory.lean:30:91 Application type mismatch` in `place_injective`; `Memory.lean:242:21` in `R_start.pubSlot` (`enumerate ⟨…/2,⋯⟩ ≠ a.snd`) | (proof-level) |
| d | Decode zero-fills (`getD 0`, no check) | `Memory.lean:105:2 split_ifs failed: no if-then-else` in `decode_some`; `Memory.lean:270:8 rewrite failed (dite pattern)` in `decode_of_R` | `decode` pc0: `some [0,0,0]` (expected none); holed memory: `some [0,14,0]` (expected none) |
| e | SlotView maps `acc x` whenever `¬Pub` (drops `Mat`) | `Memory.lean:241:17 unsolved goals` in `R_start.accSlot`; incidental `Invalid projection hq.2` in `slotView_injective` | at pc 0, acc point 1 is mapped (`true`) but `Start` holds `none` |

Controls a, b and d are caught by proof shape (the `foldl`/`dite` unfolding) before any value test runs. The value fixtures would also catch them, as the last column shows.

## Decision log (deviations and sharpenings of the brief)

1. **Structure name.** `structure Program.Plan` (declared as `_root_.LeanNCD.Semantics.Program.Plan`) lives inside namespace `Program.Plan`. This makes `P.Plan` and `π.ann` resolve. Auxiliary types are `Program.Plan.{OccRef, DefAddr, Ann, Command, Slot, Memory, Resource}`. This is unlike `Executor.Schedule`, which has no nested `Plan.Plan`.
2. **`prefix` is a Lean keyword.** The prefix is named `prefixAnn pc`. The static sets are lists (`consList`/`pubList`/`matList`) wrapped as the Props `Pub`/`Cons`/`Mat`, with computable `Decidable` instances.
3. **Ann lists carry no Nodup field.** Nodup is a premise of `postAnn` (`acc`/`pub`) and of `Coverage1`/`Coverage2`. The syntax stays plain data.
4. **Δ_G is a whole-accumulator sum of `Pi.single` increments** (`single`, `delta`). With this choice, `consume` equals `α + single x v` and the any-order corollary is `List.Perm.sum_eq` on the Pi `AddCommMonoid`. No dependent `subst` on same-tensor updates was needed.
5. **The post-state is `postAnn` as `Option`, and `refState η pc = foldlM postAnn (initial η) (prefixAnn pc)`.** This makes it deterministic in pc. Values come from `evalValue`, which is `evalReady` on the pre-state. The `getD 0` fallback is unreachable under the guard.
6. **`postAnn` uses `postAcc`/`postPub`.** Their bounded quantifiers are forced through `List.decidableBAll`. Instance search otherwise chose `Fintype.decidableForallFintype` via the noncomputable `definedFintype`/`definedAddressFintype`. **This is a pitfall for A2.**
7. **Bare `consume`/`publish` inside `Program.Plan` resolve to the noncomputable `Program.consume`/`publish`.** Batch.lean qualifies them as `Executor.consume`/`Executor.publish`. **This is a pitfall for A2.**
8. **R3 is stated at `place a`, guarded by `SlotView … = some (place a)`.** Quantifying over arbitrary `ξ` would not typecheck, because `M ξ` and `published a` live over different sorts. `slotView_injective` recovers the spec's injectivity clause.
9. **`R` is a structure** with fields `reach` (R1), `pending`/`published` (R2), `pubSlot`/`accSlot` (R3) and `retain` (R4). `η` is explicit. `R` does not mention `refState`. `refState_reaches` supplies R1 for the deterministic state.
10. **`Start` takes a validated `P.Input`.** It does not re-run validation, because `Executor.validate` needs a tensor list that a `Plan` does not carry. A2 should decide whether `Plan` carries `tensors` (as `Schedule` does) or reuses a schedule's list.
11. **The donors were reused by importing** `Semantics.ExecutableReferenceTest` (`declarations`, `point`, `check`, `vectorStore`, `noInput`, `scalarRole`, `scalarInput`, `taggedResult`). The tagged schedule was not rebuilt, because `flatKeys` plus `coverage_iff_schedule` already covers the schedule view.
12. **The fixture plan materialises (initZero) all three points before publishing.** See defect N1.

## Spec defects audit

- **D1 (R needs reachability): CONFIRMED by analysis.** R2-R4 do not constrain an untouched, unmapped accumulator. Only R1 (with Lemma 26.1) pins it to 0. There is no Lean counter-model; in this prototype the functional `refState` also pins it.
- **D2 (the layout view depends only on pc/commands): CONFIRMED feasible.** `SlotView π pc` was defined without the reference state. `slotView_injective` and `R_start` close. Mutation e shows the `Mat` guard is load-bearing.
- **D3 (clause 2 as equations R2): CONFIRMED.** It is stated as the iff-equations `o ∈ pending ↔ ¬Cons` and `isSome ↔ Pub`. Both discharge at pc = 0.
- **D4 ("implements the annotations" is redundant given a functional post): SUPPORTED, not yet discharged.** `refState` is a function of the annotations, and `refState_execution` produces the matching segment. Redundancy needs A2's step lemma in the form `conf' = refState (pc+1)`.
- **D6 (Decode partial; success belongs to Lemma 31.2): CONFIRMED.** Decode is `none` at pc 0, at pc 2 and on a holed memory. `decode_of_R` gives success under R, given that all outputs are in `Pub(pc)`. A2 must derive that from condition 2 at pc = m. Mutation d turns all of these into silent zeros.
- **D9 (the union half of condition 1 follows from conditions 2 and 4): CONFIRMED by argument; not proved in Lean.** Take any occurrence o. Its destination a is in `Addr_Def`, so o ∈ `C_P(a)`. Condition 2 publishes a. Condition 4 then puts o in an earlier group. The disjointness half does **not** follow.
- **D10 (Accumulate premises suffice): CONFIRMED with a sharpening.** `batch_execution` needs `G ⊆ pending`, readiness (reads published), per-member body success, and `G.Nodup`. Nodup is the list form of "G is a set".
- **N1 (new): publication writes no memory, so every published defined address must be materialised first.** This includes empty-fiber coordinates. Otherwise R3 `pubSlot` fails, because the slot is `none`. Conditions 1-4 do not state this. Sections 30.2/30.3 require initialisation only "before a kernel updates or reads". The slice-1 validity condition should add: each member of a `pub` block is in `Mat` before that block.

## Full build

`lake-build.sh <worktree>/leanncd` (default targets, including `Tests`) printed `Build completed successfully (8770 jobs)` with no `error` lines. The new namespace caused no ambiguity in `NativeLegs.lean` or `SourceDiagnosticNativeTest.lean`, both of which `open LeanNCD.Eval.Plan`.

## Not done (A2 starts here)

- There is no plan step function, no `Correctness`, no `checkPlan`, and no `run` comparison. All of these are A2 per the brief.
- R is not yet proved at pc > 0. The missing lemma is: `refState η (pc+1) = postAnn* (refState η pc) (commands pc)` together with the memory effect of `initZero`/`acc`/`pub`. That gives R preservation.
- R2 is not yet derived from `refState` success. That derivation needs prefix-level Nodup/disjointness from `Coverage1`/`Coverage2` together with `accumulateBatch_pending`.
- D9 still needs a Lean proof.

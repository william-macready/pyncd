# Part V slice 3: buffer retirement Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize spec 30.3's "retire a published resource that is not needed by any remaining contribution, output decoding, or remaining storage operation" in the Plan layer: a new `Ann.retire` annotation that clears the slots of defined published addresses, with `Valid`, `checkPlan_iff`, `step_R`, `step_failed`, `step_not_stuck`, `done_correct`, `failed_correct`, `done_iff_model`, the fused (`FValid`) and fault-oracle (`Faults`) theorems all holding for plans that contain `retire`, statements unchanged except as listed in the spec section 5 (amended by T5).

**Architecture:** `Pub` stays the logical published set; new `Ret`/`Live` (`Live = Pub and not Ret`) are the readable set. `readPub`, `SlotView .pub`, `ReadyOK` and `R`'s `pubSlot` move from `Pub` to `Live`. `R` gains `dead` (R5, a retired slot is `none`) and `retPub` (R6, extra, see D5 below). `RetOK` is a new `Valid` field (`retOK`) checked by `checkRet`. Fused plans need nothing new: `FValid` is `Valid` of the expansion. The code ships as four verified patches applied by the controller; the prototype branch is `worktree-plan-retire-proto`.

**Tech Stack:** Lean 4 + Mathlib (`leanncd/`), `bash leanncd/scripts/lake-build.sh`, `bash leanncd/scripts/mutation-manifest.sh`, `git apply` of patches under `papers/semantics/plan_layer_slice3_patches/`.

**Spec:** docs/superpowers/specs/2026-10-11-buffer-retirement-design.md

Live plan. Authoring facts, measured numbers and the close-out template are in `papers/semantics/plan_layer_slice3_record.md`.
Sources (the only ones cited): `papers/semantics/plan_layer_slice3_artifacts/{a1_notes,a2a_notes,a2b_notes,a3a_notes}.md`, `.../evidence.json`, `.../emit-patches.py`, `papers/semantics/plan_layer_slice3_patches/manifest.json` and the four patches, `papers/semantics/plan_layer_slice3_mutations_post.json`, `papers/semantics/plan_layer_slice3_mutation_results.md`. Structure template: `papers/semantics/plan_layer_slice2_plan.md`.
Identifiers in this plan were checked with `rg -n` in the prototype tree (HEAD `7a44f92c`); on the base tree (`main` 69214c64) the new ones do not exist until T1-T3 land. Lean appears only as one-line signatures from the patches.

## 0. Path declaration

**Process weight: Full path.** Slice 3 adds a constructor to `Ann`, a `Valid` clause and an `R` field, and re-types the read view under every slice 1-2 theorem. The prototype and the four patches already exist and compile; **execution is a controller applying patches** (`git apply --check`, `git apply --index`, gate build, commit). No implementer dispatch is needed for T1-T4 (applying pre-built patches needs no implementer). Dispatches exist only for: the manifest repair of T4b (mechanical, possibly long), the two whole-branch review lenses, and one fixer per finding group.

## Global Constraints

Decisions D1-D4 are the user's, 2026-10-11, taken verbatim from the spec; D5-D8 are prototype facts.

| id | decision (exact) | source |
|---|---|---|
| D1 | Scope: retirement only, dense injective `place`. Rejected: retirement + reuse together. | spec section 2 |
| D2 | `retire B` clears each member's slot to `none` (`execRet`). Rejected: view-only no-op. | spec section 2 |
| D3 | Retirement targets are defined addresses only (`DefAddr P`); inputs are never retired and always live (`live_input`). Rejected: any published address. | spec section 2 |
| D4 | "No remaining reader" is enforced at the reader: `ReadyOK` ranges over `Live`. `RetOK` does not restate it. Rejected: also stating it locally in `RetOK`. | spec section 2 |
| D5 | `R` has TWO new fields, `dead : forall a, Pub pc a -> not Live pc a -> M (place a) = none` (R5, in the spec) and `retPub : forall a, Ret pc a -> Pub pc a` (R6, NOT in the spec). Without R6, neither "a freshly published member is live" (`step_pub`) nor "a retired address is not an unpublished write target" (`step_init`, `step_acc`) is derivable, because `R` does not remember earlier steps' `RetOK`. | a1_notes Deviations 1 |
| D6 | `readPub_eq` is now pointwise on live addresses: `readPub_eq (h : R ...) {a} (ha : Live pc a) : readPub pc M a = c.published a`. The old function equality is false once a retired address keeps its ghost value in `c.published` but reads `none`. New helper `readPub_le` ("no spurious values") serves `step_acc` and `step_failed` through `evalReady_of_le`. `decode_of_R`'s hypothesis `outs` is over `Live` (conclusion unchanged). | a1_notes Memory, Deviations 2-3 |
| D7 | New theorem `live_output_of_valid`: every output coordinate is `Live` at `pc = commands.length` of a `Valid` plan. It is the argument that makes the not-an-output clause of `RetOK` *terminal* (spec 3.4's "one new lemma"). | a2a_notes Correctness |
| D8 | Clause roles (extends the spec 31.1 role table): `Live`, the `Pub` half: safety. `Live`, the `not Ret` half: diagnostic (re-retiring is harmless, fixture `retire-twice`). Not-an-output: terminal. `ReadyOK` over `Live`: progress. No duplicate check inside a retire block (`retire-dup-in-block` is accepted). Roles are the spec's; only the diagnostic and terminal claims are probed by fixtures (Review Focus). | spec 3.3; a3a_notes |

**What this slice deliberately does NOT do (owner):**

| item | owner |
|---|---|
| Buffer reuse and aliasing (a `place` that is not injective in time; `place_injective`/`slotView_injective` reworked; the two-buffer scan of spec 33.2 as a plan) | later buffer-reuse slice (the slice that starts from `dead`) |
| Scan liveness (spec 33.2-33.4) | later slice, after reuse |
| Retiring inputs (needs an ownership story for caller memory; `Ann.retire` takes `DefAddr P`, so a retire of an input is not even expressible; no fixture, comment in `PlanRetireTest`) | not scheduled |
| Copy and relocate storage operations; in-kernel read-before-write | not scheduled |
| Concrete implementation-error sources beyond the abstract `Faults` oracle | not scheduled |
| Mutation-manifest `--task` validation gap (separate open item, recorded in memory; not re-measured here, not touched) | separate |

Not a goal and not touched: `Faults.lean` (a2b_notes: no change needed; it passes through `step_R`/`step_failed`).

## Review Focus

The five failure modes most likely to bite, each with the fixture row or theorem that pins it and the mutants that flip it. Fixture names are the `#eval check` names in `leanncd/test/Semantics/PlanRetireTest.lean` (values observed in a3a_notes); mutants are labels in `papers/semantics/plan_layer_slice3_mutations_post.json`.

1. **Read after retire.** A reader whose footprint contains a retired address must be rejected statically and be `stuck` at run time, never read a stale value. Pinned by `retire-read-after` (checkPlan false, run `stuck`) and its `example`; theorem `readPub_isSome` over `Live` feeding `step_not_stuck`. Mutants: S3-M6 (`checkReady` over `Pub`), S3-M8 (`ReadyOK` over `Pub`), S3-M7 (`SlotView .pub` over `Pub`), S3-M9 (`readPub` over `Pub`). The row flip for S3-M6 was observed by hand (a3a): `retire-read-after`, `retire-fused-before-read`, each with its `example`.
2. **Retire of an output.** Terminal clause: at run time the run still ends `done` and `Decode` returns `none`, so the static check is the only guard. Pinned by `retire-output` (checkPlan false, run `done`, decode `none`) and by the theorem `live_output_of_valid` (consumed by `terminal_adequacy` and `terminal_adequacy_F`). Mutants: S3-M5, S3-M10 (drop the not-an-output clause); S3-M3 (`checkRet` always true) also flips it.
3. **Retire of an unpublished accumulator.** Safety clause (`Pub` half of `Live`): `execRet` does clear a live accumulator. Pinned by `retire-unpublished` (checkPlan false; run `stuck` at the LATER `pub`, not at the retire: the prediction `done` in the spec was wrong, a3a_notes). Mutants: S3-M4 (drops the live clause), S3-M3.
4. **Fused retire order.** Inside one command the retire is judged at its expanded position: `[acc occ1, retire p1]` valid, `[retire p1, acc occ1]` rejected. Pinned by `retire-fused-after-read` (`checkPlanF` true, `done`) and `retire-fused-before-read` (`checkPlanF` false, `stuck`, pre-command memory); theorem `R_transport` (carries `Ret`, `Live`, `dead`, `retPub` along `prefixAnn_eq_expand`). Mutant: S3-M6 flips the verdict half.
5. **Retire under faults.** A fault at the retire position leaves the slot intact (pre-command memory), so those rows cannot distinguish a no-op `execRet`; the `-none` and `retire-fault-after-retire` rows do. Pinned by `retire-fault-at-retire`, `retire-fault-after-retire`, `retire-fault-fused-at-retire` (whole command rolled back), `retire-fault-none`, `retire-fault-fused-none`; `Faults.lean` is unchanged and relies on `step_R`/`step_failed`. Mutants: S3-M1 (`execRet` identity) flips 12 rows by hand (a3a), S3-M2 (`B.tail`) was not row-probed; both are killed first at the library proofs `execRet_mem`, `execRet_not_mem`.

Also pinned, lower risk: `dead` (R5) and `retPub` (R6) preservation in `step_init`, `step_acc`, `step_pub` have NO fixture; they are proofs only (killed mutants only reach them through `execRet_mem`/`execRet_not_mem`). `retire-dup-in-block` (accepted) and `retire-twice` (rejected, run `done`) pin the "no duplicate check inside a block / diagnostic half" decision.

### Case x class table (slice-plan section 2: required / forbidden / silently ignored at run time)

| case | legal | static check | run-time effect | silent at run time? | pinning fixture |
|---|---|---|---|---|---|
| retire a defined, published, non-output address after its last reader | yes | `RetOK`, `ReadyOK` of later readers | slot becomes `none`, `done` | n/a | `retire-valid-chain`, `retire-valid-scalar` |
| same, address never read | yes | `RetOK` | `done` | n/a | `retire-neighbour-other-address` |
| output still decodes after retiring a non-output | yes | `RetOK` | decode unchanged | n/a | `retire-valid-scalar-decode` |
| retire before a reader | no | `ReadyOK` at the reader | reader `stuck` | no (stuck) | `retire-read-after` |
| retire an output | no | `RetOK` not-an-output | `done`, decode `none` | YES | `retire-output` |
| retire an unpublished address | no | `RetOK` `Pub` half | later `pub` `stuck` | no (stuck, late) | `retire-unpublished` |
| retire an unpublished address BEFORE its `initZero` (added after the whole-branch review) | no | `RetOK` `Pub` half | clearing an empty slot is a no-op: `done`, every value correct | YES | `retire-before-init` |
| several distinct addresses in one block: all valid / the second one unpublished (added after the review) | yes / no | `RetOK` over every member (`checkRet` is `B.all`) | all cleared, `done` / the second member's accumulator is cleared, later `pub` `stuck` | no | `retire-multi-distinct`, `retire-multi-second-unpublished` |
| retire the same address twice (two commands) | no (diagnostic) | `RetOK` `not Ret` half | `done`, same memory | YES | `retire-twice` |
| duplicate inside one block | yes | none | `done` | n/a | `retire-dup-in-block` |
| fused, retire after / before a reader | yes / no | `checkPlanF` | `done` / `stuck` | no | `retire-fused-after-read`, `retire-fused-before-read` |
| retire an input | not expressible | type (`DefAddr P`) | n/a | n/a | none (comment in the module) |

The three YES cells (retire an output; retire twice; retire before `initZero`) are the silently-ignored cells: the run cannot see them, only `checkPlan` can. They are pinned by `retire-output`, `retire-twice` and `retire-before-init`, and each fixture carries a verdict `false` that S3-M3 (checker always true) flips (hand-probed: `retire-before-init` also flips when only the live clause of `checkRet` is dropped). The `-multi-` rows and `retire-fault-fused-after-retire` were added after the whole-branch review (see the record, "Deferred minors resolved"); the counts quoted above for T4 are as shipped by the patch.

## File structure

All paths exist in the prototype tree (`ls` at authoring); T4 creates `PlanRetireTest.lean`.

| file | task | role |
|---|---|---|
| `leanncd/LeanNCD/Semantics/Plan/Syntax.lean` | T1 | `Ann.retire`, `Ann.rets`, `retList`, `Ret`, `Live`, `ret_zero`, `live_zero`, `Live.pub`, `live_input` |
| `leanncd/LeanNCD/Semantics/Plan/Memory.lean` | T1 | `SlotView`/`readPub` over `Live`; `R` fields `dead`, `retPub`; `R_start`; `readPub_eq` (pointwise); `decode_of_R`; `postAnn` retire arm |
| `leanncd/LeanNCD/Semantics/Plan/Step.lean` | T1 | `execRet`, `execAnn` retire arm, `execAnn_prefix` over `Live` |
| `leanncd/LeanNCD/Semantics/Plan/Simulation.lean` | T1 | `ret_succ`, `live_succ_of`, `RetOK`, `AnnOK` arm, `readPub_le`, `execRet_mem`, `execRet_not_mem`, `evalReady_of_le`, `delta_congr`, `step_retire`, preservation in `step_init`/`step_acc`/`step_pub`, `step_R`/`step_failed` retire arms |
| `leanncd/LeanNCD/Semantics/Plan/Validity.lean` | T2 | `ReadyOK`/`checkReady` over `Live`; field `retOK`; `checkRet`, `checkRet_sound`, `checkRet_complete`; `checkPlan_sound`/`_complete` arms |
| `leanncd/LeanNCD/Semantics/Plan/Run.lean` | T2 | `readPub_isSome` over `Live`; `step_not_stuck` retire arm |
| `leanncd/LeanNCD/Semantics/Plan/Correctness.lean` | T2 | `Valid.order4` arm; `live_output_of_valid`; `terminal_adequacy` uses it |
| `leanncd/LeanNCD/Semantics/Plan/Fusion.lean` | T3 | `R_transport` carries `Ret`/`Live`/`dead`/`retPub` |
| `leanncd/LeanNCD/Semantics/Plan/FusionCorrectness.lean` | T3 | `decode_prefix_congr`, `terminal_adequacy_F` over `Live` |
| `leanncd/test/Semantics/PlanRetireTest.lean` | T4 (new) | 10 plans, 17 rows, 10 `example`s, 1 theorem |
| `leanncd/lakefile.toml` | T4 | `Semantics.PlanRetireTest` in `Tests` |
| `papers/semantics/plan_layer_slice3_mutations_post.json` | T4 | 10 cycles (already on the prototype branch) |
| `papers/semantics/{tensor_logic_semantics,lean_executable_semantics_path}.md`, `docs/superpowers/specs/2026-10-11-buffer-retirement-design.md`, `leanncd/LeanNCD/Semantics/Plan/AGENTS.md`, `leanncd/LeanNCD/Semantics/AGENTS.md`, `leanncd/AGENTS.md` | T5 | docs sweep |

Reachability (slice-plan checklist): no new module under `LeanNCD/`; `Plan.lean` already imports all eleven Plan modules (`rg -n "^import" leanncd/LeanNCD/Semantics/Plan.lean`), so `import LeanNCD` reaches every changed file. The one new file is a test, registered in the `Tests` globs of `leanncd/lakefile.toml` by patch 04.

## Tasks

All four patches live in `papers/semantics/plan_layer_slice3_patches/`; base = `main` 69214c64 (`git rev-parse main` printed that SHA at authoring); sha256 and symbols in `manifest.json`/`evidence.json`. The sha256 values were re-computed with `shasum -a 256` at authoring and equal the manifest. Job counts are `evidence.json` values at emission on the same base; the gate is "Build completed successfully" with no `error` line, the counts are a sanity signal.

**Bisect caveat (Rule 12).** T1-T3 commits are individually green only for their gate target, not for the whole `LeanNCD` library: after T1 the library stops building at `Validity` (a1_notes), after T2 at `Fusion`. The full library is green from T3, the default targets from T4. This is the same cut the prototype used; do not merge the patches into one commit to hide it.

### T1: core (Syntax, Memory, Step, Simulation)

Patch `01-core.patch` (655 lines; numstat Memory +29/-18, Simulation +198/-22, Step +9/-3, Syntax +43/-1). Base: `main` 69214c64.
Files (exist): the four `leanncd/LeanNCD/Semantics/Plan/{Syntax,Memory,Step,Simulation}.lean` above.
Produced (`identifier @ file`): `Ann.retire`, `Ann.rets`, `retList`, `Ret`, `Live`, `live_input` @ Syntax; `execRet` @ Step; `R.dead`, `R.retPub`, `readPub_eq`, `readPub` @ Memory; `RetOK`, `step_retire`, `ret_succ`, `live_succ_of`, `readPub_le`, `execRet_mem`, `execRet_not_mem`, `evalReady_of_le`, `delta_congr` @ Simulation. Consumed: `pub_succ`, `mat_succ`, `place_injective`, `step_init`, `step_acc`, `step_pub`, `step_R`, `step_failed`.
Fixtures: 0. Mutation cycles of its own: 0 (S3-M1/M2 target `Step.lean` code, run in T4, killed at the T1 proofs `execRet_mem`/`execRet_not_mem`).
- [ ] Gate before touching anything: `/usr/bin/git -C <exec> status --short` prints nothing.
- [ ] `shasum -a 256 <exec>/papers/semantics/plan_layer_slice3_patches/01-core.patch` equals `e5f512d36302dc845e804821fbc02ea8cbe4564e606a1cd3812af44aa570b301`.
- [ ] `/usr/bin/git -C <exec> apply --check <exec>/papers/semantics/plan_layer_slice3_patches/01-core.patch` (any failure is BLOCKED, not a hand-merge).
- [ ] `/usr/bin/git -C <exec> apply --index <exec>/papers/semantics/plan_layer_slice3_patches/01-core.patch`
- [ ] `bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd LeanNCD.Semantics.Plan.Simulation` (redirect to a file; read `tail -n 1`, then `rg -n "error"` over it). Expected last line: `Build completed successfully (2963 jobs).`
- [ ] `rg -n "\b(sorry|admit|axiom|native_decide)\b" <exec>/leanncd/LeanNCD/Semantics/Plan/Syntax.lean <exec>/leanncd/LeanNCD/Semantics/Plan/Memory.lean <exec>/leanncd/LeanNCD/Semantics/Plan/Step.lean <exec>/leanncd/LeanNCD/Semantics/Plan/Simulation.lean` prints nothing.
- [ ] `/usr/bin/git -C <exec> diff --cached --stat` lists exactly the four files; commit: `feat(semantics): Ann.retire, Ret/Live, execRet, R5/R6 and step_retire (Plan slice 3, T1)` with the trailer (below).

Risk: the three largest step proofs (`step_init`, `step_acc`, `step_pub`) gain `dead`/`retPub` preservation, and `step_acc`/`step_failed` are re-routed through `evalReady_of_le`. The prototype needed two tiny proof fixes only (a1_notes); R5 cost about one turn per kernel, so the spec's "drop R5 if disproportionate" fallback is NOT taken.

### T2: validity, run, correctness

Patch `02-validity-run-correctness.patch` (239 lines; Correctness +28/-3, Run +4/-3, Validity +33/-6). Base: T1 committed.
Files (exist): `Plan/{Validity,Run,Correctness}.lean`.
Produced: `checkRet`, `checkRet_sound`, `checkRet_complete`, `Valid.retOK` @ Validity; `live_output_of_valid` @ Correctness. Consumed: `RetOK`, `Live`, `live_input`, `readPub_isSome`, `decode_of_R`, `mem_prefixAnn`, `Valid.singleton`.
Fixtures 0; mutation cycles of its own 0 (S3-M3..M10 run in T4; they are killed at proofs in these files).
- [ ] sha256 of `02-validity-run-correctness.patch` equals `2685544f2fcc980f409935ce9ce06ec6c4b364fe4360f9477ab6cf2c90a78cb6`; `apply --check`; `apply --index`.
- [ ] `bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd LeanNCD.Semantics.Plan.Correctness`. Expected last line: `Build completed successfully (2966 jobs).`
- [ ] The forbidden-token `rg` over the three files prints nothing; `diff --cached --stat` lists the three files.
- [ ] Commit: `feat(semantics): checkRet, Valid.retOK, readPub_isSome over Live and live_output_of_valid (Plan slice 3, T2)`.

Risk: `checkPlan_iff` must stay an exact decision procedure; the patch changes `checkPlan_sound`/`checkPlan_complete`/`checkPlan_nodup_redundant`/`checkAccMat_of_rest` by adding `retire` arms, no new hypothesis (a2a_notes). `Valid` is anonymous-constructed in places; `retOK` is the LAST field.

### T3: fusion

Patch `03-fusion.patch` (55 lines; Fusion +7/-2, FusionCorrectness +6/-4). Base: T2 committed.
Files (exist): `Plan/Fusion.lean`, `Plan/FusionCorrectness.lean`. Produced: `R_transport` (`hret`, `hlive`, fields `dead`, `retPub`), `decode_prefix_congr` over `Live`, `terminal_adequacy_F` (`outs` from `live_output_of_valid` applied to `π.expand`). Statements unchanged. `Faults.lean` is NOT touched and needs no commit.
Fixtures 0; mutation cycles 0 of its own.
- [ ] sha256 of `03-fusion.patch` equals `6e4210402b0bf99a2a5425a7704b986c63a01f89de5ecb7fd67000f0e26a353a`; `apply --check`; `apply --index`.
- [ ] `bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd LeanNCD.Semantics.Plan.FusionCorrectness`. Expected last line: `Build completed successfully (2968 jobs).`
- [ ] Then the whole library: `bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd LeanNCD`. Expected: `Build completed successfully (8598 jobs).` (this builds `Faults` too: evidence lists `LeanNCD.Semantics.Plan.Faults` at 2969 jobs on its own).
- [ ] Commit: `feat(semantics): Fusion R_transport and FusionCorrectness over Ret/Live (Plan slice 3, T3)`.

Risk: a hand-written `Pub` ready proof in `FValid` would be a silent type error; none exists because `FValid := π.expand.Valid` (a2b_notes). Full `LeanNCD` build log is long: read only the tail.

### T4: fixtures, mutation manifest, older-manifest regression

Patch `04-fixtures.patch` (188 lines; `PlanRetireTest.lean` +169 new, `lakefile.toml` +1/-1). Base: T3 committed.
Files: `leanncd/test/Semantics/PlanRetireTest.lean` (new; imports `Semantics.PlanFaultsTest`), `leanncd/lakefile.toml` (`ls` both exist in the prototype tree; the lakefile line gains `"Semantics.PlanRetireTest"` after `"Semantics.PlanFaultsTest"`, with no space before the next entry, cosmetic, parked O2).
Fixtures: 10 plans, 17 `#eval check` rows, 10 `example ... := by decide` verdicts, 1 theorem (`rtChain_valid`) (`evidence.json` fixtures; recount below). Donors: `routed chainBody` (`chainPlan`: tensor 1 point published then read by occurrence 1) and `scalarRole false` (`sPlan false`). Plans: `rtChain`, `rtScalar`, `rtReadAfter`, `rtNeighbour`, `rtOutput`, `rtUnpub`, `rtFusedOk`, `rtFusedBad`, `rtTwice`, `rtDupBlock`.
Mutation cycles: 10 (S3-M1..S3-M10, task tag `S3`), all killed, none equivalent. Every mutant is killed at a library PROOF, so lake never reaches the fixture module in a mutated build (same shape as the D7 manifest). Row-level kills were observed by hand for M1, M3, M6 only (a3a_notes); M2, M4, M5, M7-M10 were not row-probed. The spec's prediction "`readPub` ignoring `Ret` is an equivalent mutant" is WRONG: S3-M9 is killed at `readPub_eq` (it was weakened to a pointwise statement). The spec's planned mutants "R5 weakened" and "`step_retire` omitted from `execAnns_R`" were not run (none is in the manifest); the manifest instead carries S3-M6..S3-M10 (`checkReady`/`ReadyOK`/`SlotView`/`readPub` over `Pub`, `RetOK` without the output conjunct).

Steps (controller, in `<exec>`):
- [ ] sha256 of `04-fixtures.patch` equals `2e1a9d35c60c94c6595d3608177a0b52fe7980f490c3cd4abfc9b191a3325d33`; `apply --check`; `apply --index`.
- [ ] `bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd Semantics.PlanRetireTest`. Expected: `Build completed successfully (2982 jobs).` and 17 printed rows (`check` throws on a mismatch).
- [ ] Recount: `rg -c "^#eval check" <exec>/leanncd/test/Semantics/PlanRetireTest.lean` prints `17`; `rg -c "^(example|theorem)\b" <exec>/leanncd/test/Semantics/PlanRetireTest.lean` prints `11` (10 + 1).
- [ ] Commit (fixtures only): `test(semantics): PlanRetireTest, buffer-retirement fixtures against checkPlan/checkPlanF and runPlan/runPlanE (Plan slice 3, T4)`.
- [ ] Controller, the new manifest: `bash <exec>/leanncd/scripts/mutation-manifest.sh --check <exec>/leanncd <exec>/papers/semantics/plan_layer_slice3_mutations_post.json` prints `manifest OK: 10 entries, 10 selected, every old-string unique`; then `bash <exec>/leanncd/scripts/mutation-manifest.sh --out <exec>/papers/semantics/plan_layer_slice3_mutation_results.md <exec>/leanncd <exec>/papers/semantics/plan_layer_slice3_mutations_post.json` prints `10/10 cycles passed`, and `/usr/bin/git -C <exec> status --short` shows no modified tracked file except the results file. The controller runs this itself; an agent's "green" is not accepted (slice-plan section 5).
- [ ] Full default build: `bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd`. Expected: `Build completed successfully (8793 jobs).`, no `^error`. The only `declaration uses sorry` warnings are the four pre-existing ones (`SORRY_INVENTORY.md`); a fifth is a defect.

**T4b: older manifests (a finding of THIS plan, in scope: spec section 1 "no existing mutation manifest regresses", section 6 risk).** At authoring, on the prototype tree: `mutation-manifest.sh --check` on `plan_layer_slice2_mutations_post.json` (15 entries) and `plan_layer_d7_mutations_post.json` (9 entries) is OK; on `plan_layer_mutations_post.json` (slice 1, 20 entries) it FAILS: entry `A3b-3 readPub ignores Pub (read view exposes raw memory)`: its `old` string `if π.Pub pc a then M (place a) else none` occurs 0 times in `Memory.lean`, because T1 changed the guard to `π.Live`. Further, every `expect` in the slice-1 and slice-2 manifests carries a `File.lean:L:C` location (`rg -c` finds 20 and 15 lines respectively; the D7 manifest has none), and 32 of those 35 entries mutate a file the patches edit (slice 1: `Memory.lean` 4, `Step.lean` 5, `Validity.lean` 8; slice 2: `Step.lean` 4, `Syntax.lean` 4, `FusionCorrectness.lean` 5, `Fusion.lean` 2; the other 3 are `Batch.lean` 2 and `PlanFixtures.lean` 1), so most of those `expect` strings are expected to be stale (UNVERIFIED: `--check` does not read `expect`; only a full run does). Procedure:
- [ ] Run each old manifest unfiltered with `--out <exec>/papers/semantics/scratch_<name>.md` (the file is scratch; delete before committing): slice 1 (20 cycles), slice 2 (15), D7 (9, expected 9/9 untouched). Background the long runs.
- [ ] For slice 1 entry 5: repair `old`/`new` to the `Live` form (`old`: `  if π.Live pc a then M (place a) else none`, `new`: the same with `π.Live pc a ∨ True`), then observe its `expect` from a real run.
- [ ] For each entry reported `expected text not in mutated build log`: the repair is to replace ONLY the stale `File.lean:L:C` location by the one the mutated build now reports (apply the mutant by hand in a scratch copy or read the cycle's build log), keep the message text; never weaken an `expect` to a bare message without recording why. One fixer dispatch per manifest (slice 1, then slice 2), each given only this subsection, the manifest path and the preamble below; each appends findings to `<exec>/papers/semantics/plan_layer_slice3_artifacts/manifest_repair_slice1.md` / `_slice2.md` as it goes.
- [ ] Gate: slice 1 `20/20`, slice 2 `15/15`, D7 `9/9` PASS, every file restored byte-identical. Commit (manifests only, Direct path, recorded): `test(semantics): repair slice 1-2 mutation manifests after slice 3 line shifts`.
- [ ] If a repaired cycle turns out SURVIVING (the mutant now builds), that is a regression of an old guarantee: STOP and report (genuinely blocked), do not weaken the mutant.
Cost: up to 35 mutant builds (each rebuilds the mutated module and its dependents); this is the largest unmeasured cost of the slice (Rule 6 headroom is wide: slice execution budget is <= ~175M and the patch application is small). Not covered by the prototype: the prototype never ran the old manifests.

### T5: documentation sweep (no patch; commands)

Section "Docs sweep" below. One docs commit `docs(semantics): Plan slice 3 (buffer retirement) restatements, path doc, intent layer, spec amendment`. Fixtures 0, mutation cycles 0.

### T6: integration (controller; Rule 13 authorizes all of it, no menu; Rule 14 scope gate applies)

See "Landing and execution procedure". No implementer.

### Risk table

| task | production files | new fixtures | changed fixtures | mutation cycles | split? | main risk |
|---|---|---:|---:|---:|---|---|
| T1 | 4 (Syntax, Memory, Step, Simulation) | 0 | 0 | 0 (S3-M1/M2 killed at its proofs, run in T4) | no | `dead`/`retPub` preservation in the three largest step proofs; whole library not green until T3 |
| T2 | 3 (Validity, Run, Correctness) | 0 | 0 | 0 (S3-M3..M10 killed at its proofs) | no | `checkPlan_iff` stays exact; `retOK` is the last `Valid` field |
| T3 | 2 (Fusion, FusionCorrectness) | 0 | 0 | 0 | no | `R_transport` is an anonymous-constructor proof of `R` (both new fields) |
| T4 | 0 (+ `lakefile.toml`) | 10 plans: 17 rows + 10 `example`s + 1 theorem | 0 | 10 (S3-M1..M10, 10/10 killed, all at proofs) | no | no mutant reaches a fixture; row-level kills probed by hand for M1, M3, M6 only |
| T4b | 0 | 0 | 0 | repairs 35 old cycles (20 + 15) + re-runs D7's 9 | yes (one fixer per manifest) | stale `expect` locations in slice 1-2 manifests; entry `A3b-3` `old` string gone |
| T5 | 0 | 0 | 0 | 0 | no | stale values in a document nobody reopened (value-grep) |
| totals | 9 | 28 (17 + 10 + 1) | 0 | 10 new + 44 old re-run | | old-manifest repair is unmeasured |

## Landing and execution procedure (controller)

Every dispatch brief (T4b fixers, the two reviewers, finding fixers) opens with the preamble of `.claude/skills/new-slice/SKILL.md`, copied verbatim:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command, no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`. Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`; never run `lake` from the worktree root. Use the Read tool for file windows and `rg -n` for search. Stage files by explicit path; never commit `.claude/settings.json`. Stay within the stated turn and context budget and say so in the report if you breach it.

Plus: brief with numbers (windows of 40-60 lines, symbols as `identifier @ file`), budgets per Rule 6 (dispatch context peak <= ~250k, <= ~60 turns), write findings incrementally to a file. Commit trailer for every commit (CLAUDE.md attribution), as a second `-m`:
`Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`. Never push (Rule 13): `main` ends ahead of `origin/main`.

1. **Land the docs-only artifacts on local `main`.** The prototype branch carries Lean commits and must NOT be merged. Gates first: `/usr/bin/git -C /Users/williammacready/code/python/pyncd branch --show-current` prints `main`; `/usr/bin/git -C /Users/williammacready/code/python/pyncd status --short` prints nothing (else stop).
   - [ ] `/usr/bin/git -C /Users/williammacready/code/python/pyncd checkout worktree-plan-retire-proto -- papers/semantics/plan_layer_slice3_plan.md papers/semantics/plan_layer_slice3_record.md papers/semantics/plan_layer_slice3_mutations_post.json papers/semantics/plan_layer_slice3_mutation_results.md papers/semantics/plan_layer_slice3_patches papers/semantics/plan_layer_slice3_artifacts`
   - [ ] `/usr/bin/git -C /Users/williammacready/code/python/pyncd diff --cached --stat` lists only paths under `papers/semantics/plan_layer_slice3_*`; no `.lean`, no `lakefile.toml`.
   - [ ] `/usr/bin/git -C /Users/williammacready/code/python/pyncd commit -m "docs(semantics): slice 3 plan, patches, mutation manifest and authoring artifacts" -m "Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"`
2. **Exec worktree.** `EnterWorktree` (name `plan-retire-exec`), then `bash .claude/skills/new-slice/prepare-worktree.sh --base main` (no `--plan`: step 1 committed the plan to `main`). Call it `<exec>`. If `main` moved since 69214c64, `git apply --check` decides; a failure is BLOCKED.
3. **T1 -> T4** as written above, one commit per task, only the task's files, no edits to patched files. Per task the sequence is: `shasum -a 256`, `apply --check`, `apply --index`, gate build, `diff --cached --stat`, `commit`. Read each patch's sha256 with `rg -n -A2 "<NN-name>.patch" <exec>/papers/semantics/plan_layer_slice3_patches/manifest.json`.
4. **T4b** after T4.
5. **T5** docs sweep, then the forbidden-token grep over the touched trees and the full default build again:
   - [ ] `rg -n "\b(sorry|admit|axiom|native_decide)\b" <exec>/leanncd/LeanNCD/Semantics/Plan <exec>/leanncd/LeanNCD/Semantics/Plan.lean <exec>/leanncd/test/Semantics --glob "Plan*"` prints nothing.
   - [ ] `bash <exec>/leanncd/scripts/lake-build.sh <exec>/leanncd` (no target): `Build completed successfully`, no `^error`.
6. **Two whole-branch review lenses**, each a dispatch writing findings INCREMENTALLY to `<exec>/papers/semantics/plan_layer_slice3_artifacts/wb_review_soundness.md` and `wb_review_fidelity.md`: (a) soundness (every `Valid` clause is consumed or a labelled diagnostic; `R5`/`R6` preservation; no silently-ignored cell of the case x class table; fixtures that can fail); (b) spec-Lean fidelity (the amended spec section 3 and the spec 30.3/31.1 restatements against the code, identifiers and counts). Check usage headroom before launching them in parallel. Findings are adjudicated; one fix dispatch per finding group, given only its plan sections.
7. **Integration** (Rule 13, no menu): `ExitWorktree` with `keep`, then
   - [ ] `/usr/bin/git -C /Users/williammacready/code/python/pyncd merge --no-ff worktree-plan-retire-exec` (use the branch name `prepare-worktree.sh` reported).
   - [ ] `/usr/bin/git -C /Users/williammacready/code/python/pyncd diff --stat worktree-plan-retire-proto HEAD -- leanncd` shows only the files changed after the prototype by T4b and review fixes (expected: manifest and doc paths are outside `leanncd`, so empty unless a fix touched Lean; explain any line).
   - [ ] Tag BEFORE deleting: `/usr/bin/git -C /Users/williammacready/code/python/pyncd tag plan-layer-slice3-proto worktree-plan-retire-proto`.
   - [ ] Worktree first, then branch (git refuses to delete a checked-out branch); `git status` in each first, only identified files discarded: `/usr/bin/git -C /Users/williammacready/code/python/pyncd worktree remove /Users/williammacready/code/python/pyncd/.claude/worktrees/plan-retire-proto`, then `branch -D worktree-plan-retire-proto` (unmerged; the tag keeps history), then `worktree remove <exec>` and `branch -d` of the merged exec branch.
8. Fill the record's close-out (measured token total: `python3 .claude/skills/slice-plan/token-report.py <session-id>`; Rule 6 slice execution <= ~175M; an overrun is stated, not hidden). Update the auto-memory index entry for Part V (merged SHA, unpushed, parked items below).

## Docs sweep (T5, commands)

Run in `<exec>` after T4b. Locate every anchor with `rg -n`; never edit by line number. No `File.lean:NNN` goes into any shipped text; the exit grep at the end checks. Every number below comes from `evidence.json`, the notes or the value-greps at authoring (stated); anything that disagrees at execution is explained before editing a document.

### (a) Spec `papers/semantics/tensor_logic_semantics.md`

```sh
rg -n "no retirement" <exec>/papers/semantics/tensor_logic_semantics.md
rg -n "^### (30\.3|31\.1|33\.2) " <exec>/papers/semantics/tensor_logic_semantics.md
rg -n "^\| (Lemma 31\.2|Theorem 31\.3) " <exec>/papers/semantics/tensor_logic_semantics.md
```
At authoring the first command had 12 hit lines: one in the preamble (profile sentence), the one-line header `**As formalized (slice-1 and slice-2 profile: fused commands by expansion, dense non-reused storage, no retirement).**` in 29.3, 30.2, 30.4, 31.1, 31.2, 31.3 (Lemma 31.2 paragraph), 32.1 (8 hits, identical text), the two-line header variant in 31.4 (`...no retirement;` / `error-free).`), the 31.4 closing sentence ("storage, no retirement) the generic steps ..."), and the closing profile sentence of Part V ("Outside the slice-1 and slice-2 profile (singleton and fused commands, dense non-reused storage, no retirement) these are"). There is NO "As formalized" note in 30.3 or 33.2 yet: both are created (not edited) below.

Edits, in order:
1. **Header, all 8 identical lines** (Edit with `replace_all`): old `**As formalized (slice-1 and slice-2 profile: fused commands by expansion, dense non-reused storage, no retirement).**`, new `**As formalized (slice-1 to slice-3 profile: fused commands by expansion, retirement of defined published addresses, dense injective storage).**`. Then the three variants by hand: 31.4's two-line header gets the same replacement text inside `(...; error-free)`; the 31.4 sentence "(singleton commands, dense non-reused storage, no retirement)" becomes "(singleton and fused commands, retirement of defined published addresses, dense injective storage)"; the preamble sentence, line-wrapped as `dense` at the end of one line and `non-reused storage, no retirement; see the table)` at the start of the next, becomes `retirement of defined published addresses, dense injective storage; see the table)` (anchor: `non-reused storage, no retirement; see the table)`), and "buffer reuse have no Lean proof" stays; the closing Part V sentence becomes "Outside the slice-1 to slice-3 profile (singleton and fused commands, retirement of defined published addresses, dense injective storage) these are". After this, `rg -n "no retirement"` must print nothing.
2. **30.2** (the paragraph ending "...and the published-only view is $\mathrm{Pub}(n)$."): append "Slice 3: the readable view is $\mathrm{Live}(n)=\mathrm{Pub}(n)\setminus\mathrm{Ret}(n)$; a retired address is still in $\mathrm{Pub}(n)$ and in $\mathop{\mathrm{dom}}(\sigma)$, only its slot is cleared (`readPub`, `SlotView .pub` over `Live`)."
3. **30.3** (new paragraph, after the paragraph ending "...matching printed axis names or equal extents is not a layout proof." and before "Liveness between commands is not sufficient"): 
> **As formalized (slice-3 profile: retirement of defined published addresses, dense injective `place`).** The annotation `retire B` retires published addresses of $B$ (defined addresses only; inputs are never retired, `live_input`): `execRet` sets each member's slot to `none`, the reference state is unchanged, so a retired address stays in $\mathop{\mathrm{dom}}(\sigma)$ as ghost history (`dead`: a retired slot is free). The logical published set $\mathrm{Pub}$ is unchanged; the readable set is $\mathrm{Live}=\mathrm{Pub}\setminus\mathrm{Ret}$ (`Live`, `Ret`, `retList`). "Not needed by any remaining contribution" is enforced at the reader: a later `acc` whose footprint contains a retired address fails `ReadyOK`, which ranges over $\mathrm{Live}$. "Not needed by output decoding" is the `RetOK` clause that no member is an output (`live_output_of_valid`: every output is live at the end of a valid plan). "Remaining concrete storage operation" is vacuous: copy and relocate are not formalized. The first two storage effects of the list that involve reuse or copy have no Lean counterpart: `place` is injective, a retired slot is never rewritten, and reading it is a plan defect (checker rejection, `stuck` at run time).
4. **30.4** three statements that became false: (i) in the sentence "Because nothing is retired, the layout view `SlotView` maps exactly the addresses of $\mathrm{Pub}(\mathsf{pc})$ to their published slots." replace by "The layout view `SlotView` maps exactly the addresses of $\mathrm{Live}(\mathsf{pc})$ (the published, not yet retired addresses) to their published slots; $\mathrm{Pub}(\mathsf{pc})$ is the logical set."; (ii) bullet R3: "for $a\in\mathrm{Pub}(\mathsf{pc})$, $M[\mathrm{place}\ a]=\sigma(a)$" becomes "for $a\in\mathrm{Live}(\mathsf{pc})$ ..."; (iii) bullet `Decode` "every output coordinate is in $\mathrm{Pub}(\mathsf{pc})$ with an initialised slot" becomes "... is in $\mathrm{Live}(\mathsf{pc})$ ...". Then add two bullets after R4: "- R5 (dead): for $a\in\mathrm{Pub}(\mathsf{pc})\setminus\mathrm{Live}(\mathsf{pc})$, $M[\mathrm{place}\ a]$ is uninitialised (a retired slot is free); `dead`." and "- R6 (Lean only): a retired address is published (`retPub`); needed because $R$ does not remember earlier steps' conditions." Append: "Slice 3: `readPub_eq` is pointwise on $\mathrm{Live}$ (`readPub pc M a = c.published a` for live $a$); the function equality of slice 1 is false once a retired address keeps its ghost value."
5. **31.1** table: (i) the footprint row ends "...condition 3) | progress | `step_not_stuck` |": change "every footprint address $\in\mathrm{Pub}(\mathsf{pc})$" to "$\in\mathrm{Live}(\mathsf{pc})$ (`ReadyOK`; this is where 30.3's "no remaining reader" is enforced)". (ii) after the `pub $B$:` row insert three rows:
   `| retire $B$: every $x\in B$ is published at pc (the $\mathrm{Pub}$ half of $\mathrm{Live}$) | safety (a retire of an unpublished address would clear a live accumulator) | `step_retire` |`
   `| retire $B$: no $x\in B$ is already retired (the $\neg\mathrm{Ret}$ half of $\mathrm{Live}$; a second retire is harmless at run time) | diagnostic | none (fixture `retire-twice`) |`
   `| retire $B$: no $x\in B$ is an output (`RetOK`) | terminal | `live_output_of_valid`, `terminal_adequacy` |`
   (iii) after the "Slice 2:" paragraph add: "Slice 3: `Valid` gains the field `retOK` and `checkPlan` the clause `checkRet`; `checkPlan_iff` is unchanged in statement. There is no duplicate check inside a retire block (clearing is idempotent). A retire inside a fused command is covered by expansion (`FValid`); `retire-fused-before-read` and `retire-fused-after-read` pin the order. Runtime execution does not detect a retire of an output (the run ends `done` and `Decode` is `none`, `retire-output`): only the checker does."
6. **31.3** Lemma 31.2 paragraph: the sentences "In slice 1 that step is trivial: at $\mathsf{pc}=m$, $\mathrm{Pub}(m)=\mathrm{Addr}_\Sigma$ already and nothing is retired, so `decode_of_R` needs no $\mathrm{Need}_{\mathrm{pub}}$ argument." become "In slices 1-2 that step is trivial (nothing is retired). In slice 3 it is the theorem `live_output_of_valid`: at $\mathsf{pc}=m$ every output coordinate is in $\mathrm{Live}(m)$, because it is published and `RetOK` forbids retiring an output; `decode_of_R` takes that as its hypothesis `outs`."
7. **33.2** (new paragraph after "...as though it still represented $H_0$."):
> **As formalized (slice-3 profile).** Only the retirement half of this example is formalized: a plan may retire $H_0$ after its readers (`retire`, `execRet`; the slot becomes free, `dead`) and the logical address stays in $\sigma$. The reuse half (zero-initializing the freed buffer for $H_2$, the two-buffer schedule, "no remaining kernel may read the overwritten slot") has no Lean counterpart: `place` is injective, so the freed slot is never rewritten. It belongs to the later buffer-reuse slice.
8. **Proof-status rows** (`### Proof status and numbered results`): the `Lemma 31.2` row: append "Slice 3: statement unchanged for plans containing `retire`; outputs are live by `live_output_of_valid` (`Plan.Correctness`)." The `Theorem 31.3` row: append "Slice 3: statements unchanged for plans containing `retire` (`Valid` has the field `retOK`; `checkPlan_iff` still holds)." `Lemma 32.1` row unchanged.

Exit greps (each prints nothing):
```sh
rg -n "no retirement" <exec>/papers/semantics/tensor_logic_semantics.md
rg -n "[A-Za-z]+\.lean:[0-9]+" <exec>/papers/semantics/tensor_logic_semantics.md
```
And re-read the eight 29.3/30.2/30.4/31.1/31.2/31.3/31.4/32.1 notes for any remaining statement that says published implies readable or "nothing is retired" (`rg -n "nothing is retired|nothing retired" ...` must print nothing after edit 6).

### (b) Design spec `docs/superpowers/specs/2026-10-11-buffer-retirement-design.md` (amend for the prototype deviations)

```sh
rg -n "^Status:|^### 3\.(1|4|5)|^## 5\.|180|about 8 cycles|equivalent mutant|About 24|about 24" <exec>/docs/superpowers/specs/2026-10-11-buffer-retirement-design.md
```
- Status line: "design approved ...; this file awaits user review before `writing-plans`." becomes "implemented by `papers/semantics/plan_layer_slice3_plan.md`; sections 3.1, 3.4, 3.5 and 5 amended to the prototype (a1/a2/a3a notes)."
- 3.1, after the `ret_succ` lemma bullet: "`ret_succ` lives in `Plan/Simulation.lean` beside `pub_succ`, not in `Syntax.lean`; added `live_zero`, `Live.pub`, `pub_succ_of`, `ret_succ_of`, `live_succ_of`."
- 3.4, the `R5` bullet: add "`R` gets a sixth field `retPub : forall a, Ret pc a -> Pub pc a` (R6, not in the original design). It is needed by `step_pub` (a freshly published member is live) and `step_init`/`step_acc` (a retired address is not an unpublished write target); `R` does not remember earlier steps' `RetOK`." Add: "`readPub_eq` is restated pointwise on `Live`; the function equality `readPub pc M = c.published` is false once a retired address keeps its ghost value. New helper `readPub_le`; `step_acc` and `step_failed` now reach readiness through `evalReady_of_le` and per-member values through `delta_congr`. `decode_of_R`'s hypothesis `outs` is over `Live` (conclusion unchanged); `live_output_of_valid` produces it."
- 3.5: fixture list item 4 (retire of an unpublished accumulator): "observed: checkPlan false and the run is `stuck` at the later `pub` (the clear does happen), not `done`." Replace "about 8 cycles. Planned mutants: ..." by "10 cycles (`plan_layer_slice3_mutations_post.json`): ... (list S3-M1..S3-M10)" and replace the equivalent-mutant paragraph by "`readPub` over `Pub` (S3-M9) is NOT equivalent: it is killed at the proof `readPub_eq` (restated pointwise on `Live`). The planned mutants 'R5 weakened' and '`step_retire` omitted from `execAnns_R`' were not run. All 10 are killed at library proofs; row-level kills were probed by hand for S3-M1, S3-M3, S3-M6 only." Replace "All 180 existing fixture rows" by the measured count at the base (value-grep (e): 200 by the `rg -c` method at the prototype head minus the 28 new, to be re-measured; the path doc's 180 predates `PlanFaultsTest`).
- Section 5 table: row `R`: "`pubSlot` over `Live`; new fields `dead`, `retPub`"; add rows `readPub_eq` (restated pointwise on `Live`), `decode_of_R` (hypothesis `outs` over `Live`), `live_output_of_valid` (new theorem, `Plan.Correctness`).

### (c) Path doc `papers/semantics/lean_executable_semantics_path.md`

```sh
rg -n "^### 4\.9 |^#### |no retirement|Buffer reuse, aliasing, retirement|buffer reuse, aliasing, retirement|slice-1 and slice-2|slices 1 and 2|180 fixtures|35 mutation|35-cycle|Slice 1 and 2 profile|What slices 1 and 2" <exec>/papers/semantics/lean_executable_semantics_path.md
```
At authoring the profile paragraph, the "does not do" list, the snapshot (lines naming `180 fixtures and a 35-cycle mutation manifest (20 in slice 1, 15 in slice 2)`) and section 5.2 ("Not yet done: buffer reuse, aliasing, retirement and scan liveness") all hit.
- Theorem table (4.9, after the `terminal_adequacy_F ... done_iff_model_F` row): add rows `step_retire` | "From R and `Conf = refState pc`, a retire block satisfying `RetOK` re-establishes R at `pc + 1` with the reference state unchanged and every retired slot `none`" | Section 30.3 retirement; `checkRet_sound`, `checkRet_complete` | "`checkRet` accepts exactly `RetOK`, so `checkPlan_iff` still holds" | Definition 31.1; `live_output_of_valid` | "A valid plan has every output coordinate live at the end, so no retire of an output exists" | Lemma 31.2.
- New `#### Buffer retirement (slice 3)` after `#### Fused commands (slice 2)` and a TOC line for it: three paragraphs from D1-D8 (`Pub` logical vs `Live` readable; `execRet` clears, ghost history stays; `ReadyOK` over `Live` is the reader-side rule; `RetOK` three roles; `R` fields `dead` and `retPub`; `readPub_eq` pointwise; inputs not retirable; the case x class table is section "Review Focus" of `plan_layer_slice3_plan.md`; the design spec's two deviations).
- Rename `#### Slice 1 and 2 profile, fixtures and mutations` to `#### Slices 1-3 profile, fixtures and mutations` and `#### What slices 1 and 2 do not do` to `#### What slices 1-3 do not do`, updating the two TOC lines (the only anchors; check with `rg -n "slice-1-and-2-profile|what-slices-1-and-2"` over `*.md`).
- Profile paragraph: "no retirement" becomes "retirement of defined published addresses (`Pub` logical, `Live` readable; `place` injective, a retired slot is never rewritten)"; "dense non-reused storage (one slot per materialised address, never reused)" stays true. The sentence naming the headings becomes "paragraphs headed "As formalized (slice-1 to slice-3 profile ...)" in Sections 29.3, 30.2, 30.3, 30.4, 31.1-31.4, 32.1 and 33.2".
- Counts (value-grep (e) supplies the measured numbers; at authoring): replace "hold 180 fixtures (129 in slice 1: ...)" by "hold 228 fixtures by the `rg -c` count (139 `#eval check` rows and 89 `example`/`theorem` items), of which 28 are slice 3's `PlanRetireTest` (17 rows, 10 `example`s, 1 theorem)"; replace "ran 35 mutation cycles (20 in slice 1, 15 in slice 2), of which 4 are labelled equivalent (3 in slice 1; S2-M4 at fixture level)" by "ran 54 mutation cycles (20 in slice 1, 15 in slice 2, 9 in the D7 manifest, 10 in slice 3; `rg -c "label"` per manifest), of which 4 are labelled equivalent among the 35 of slices 1-2 (3 in slice 1; S2-M4 at fixture level) and none among the 10 of slice 3 (every one is killed at a library proof)". If the measured fixture total differs from 228, explain before editing (see record: the previous 180 does not reconcile with the same method).
- Snapshot paragraph: same two numbers, "slice-1 to slice-3", and the "Lean as of" SHA refreshed to the merge head.
- "does not do" list: the bullet "Buffer reuse, aliasing, retirement, and liveness for scans." becomes "Buffer reuse and aliasing, retiring inputs, copy and relocate operations, and liveness for scans (retirement of defined published addresses is done, slice 3)."
- Section 5.2: "Slices 1 and 2 of the plan layer have landed" becomes "Slices 1-3 ... singleton and fused commands, retirement of defined published addresses, dense injective storage"; "Not yet done: buffer reuse, aliasing, retirement and scan liveness;" becomes "Not yet done: buffer reuse and aliasing, scan liveness, retiring inputs;".
- TOC rule check, before and after (record both; the second count is the first minus 1):
```sh
rg -c "^#{2,4} " <exec>/papers/semantics/lean_executable_semantics_path.md
rg -c "^ *- \[" <exec>/papers/semantics/lean_executable_semantics_path.md
```

### (d) Intent layer

```sh
awk '/^## Pitfalls/{f=1} f' <exec>/leanncd/LeanNCD/Semantics/Plan/AGENTS.md | wc -c
wc -c <exec>/leanncd/LeanNCD/Semantics/Plan/AGENTS.md
```
At authoring (base tree): whole file 6151 bytes; the hook-injected part (Pitfalls is the only injected section; there are no Checks/Patterns/Context) 1483 bytes. Record before and after; gate <= ~3000 for the Pitfalls section.
`Plan/AGENTS.md`:
- Purpose: "slices 1-2" -> "slices 1-3"; add "retirement of defined published addresses (`retire`, `Live`)" to Owns; "Does not own: ... buffer reuse, retirement," -> "buffer reuse and aliasing, scan liveness, retiring inputs, copy/relocate,"; the `Plan:` line adds `papers/semantics/plan_layer_slice3_plan.md` and 30.3, 33.2 to the spec sections.
- Code Map rows: Syntax (`Ann.retire`, `Ret`, `Live`, `retList`), Memory (`readPub`/`SlotView` over `Live`, `R` fields `dead` and `retPub`, `readPub_eq` pointwise), Step (`execRet`), Simulation (`RetOK`, `step_retire`, `readPub_le`), Validity (`checkRet`, field `retOK`), Run (`readPub_isSome` over `Live`), Correctness (`live_output_of_valid`), Fusion (`R_transport` carries `Ret`/`Live`/`dead`/`retPub`).
- Contracts: the profile bullet "Slice-1/2 profile: ... dense non-reused buffers, ..." -> "Slice-1-3 profile: ... dense injective `place` (a retired slot is cleared, never reused), ..."; add "`Pub` is the logical published set, `Live = Pub \ Ret` the readable one; a retired address stays in `Pub` and in `dom sigma`."
- Pitfalls (keep to three short lines): (1) reads go through `Live`, not `Pub`: `readPub pc M = c.published` is false after a retire, use `readPub_eq` (pointwise on `Live`) and `readPub_le`; (2) `R` has a field `retPub` beyond the spec's R1-R5; any hand-built `R` (`R_start`, `R_transport`) needs both `dead` and `retPub`; (3) retiring an output or retiring twice runs to `done`: only `checkPlan` rejects it.
- Mutation line: add `papers/semantics/plan_layer_slice3_mutations_post.json` (10 cycles, all caught at library proofs; run with `leanncd/scripts/mutation-manifest.sh`).
`leanncd/LeanNCD/Semantics/AGENTS.md` (the Plan row: "the Part V slices 1-2 plan layer (singleton and fused commands (by expansion), dense non-reused storage)"): -> "slices 1-3 ... (singleton and fused commands (by expansion), retirement of defined published addresses, dense injective storage)". `leanncd/AGENTS.md` row `Semantic explorations`: "Part V slice 1-2 plan layer" -> "Part V slice 1-3 plan layer".

### (e) Value-grep of the whole repo (run, then fill the disposition column in the record)

```sh
for p in "180 fixtures" "35 mutation" "35-cycle" "no retirement" "nothing is retired" "retirement" "non-reused" "slices 1-2" "slice-1 and slice-2" "readPub = c.published" "slice 1-2 plan layer"; do rg -c -F --hidden -g '!**/.lake/**' -g '!.git' -g '!papers/semantics/plan_layer_slice3_*' -- "$p" <exec>; done
rg -c "^#eval check" <exec>/leanncd/test/Semantics --glob "Plan*Test.lean"
rg -c "^(example|theorem)\b" <exec>/leanncd/test/Semantics --glob "Plan*Test.lean"
```
Expected totals at the prototype head (measured at authoring): `#eval check` rows 139 (per file: Fusion 18, Batch 8, Memory 7, Validity 23, FusionChecker 13, Retire 17, Faults 12, FusionCorrectness 7, Simulation 1, MultiSort 4, Step 21, Correctness 8) and items 89 (Batch 2, Memory 3, Validity 30, Retire 11, Faults 7, FusionCorrectness 9, Simulation 16, MultiSort 1, Run 4, Correctness 6); total 228, of which 28 are `PlanRetireTest`. Dispositions to apply: documents that state a pre-slice-3 profile ("no retirement", "180 fixtures", "35 mutation", "slices 1-2") and are live (spec, path doc, the three AGENTS files) are EDITs above; historical records (`plan_layer_record.md`, `plan_layer_slice2_record.md`, `plan_layer_slice2_plan.md`, the D7 record, `plan_layer_mutation_results.md`) are kept; `Plan/*.lean` doc comments that say "slice-1 profile" are kept (parked O6, cosmetic); unrelated vocabulary in other trees is kept. A stale value found in a document not listed here is an EDIT.

### (f) Close-out and memory

Fill the "Close-out" section of `papers/semantics/plan_layer_slice3_record.md` (blanks prepared there). Then update the auto-memory index entry for Part V: slice 3 merged SHA, unpushed, parked items below.

## Open items and parked work (each re-verified at authoring)

| id | item | status at authoring | cost |
|---|---|---|---|
| O1 | Buffer reuse and aliasing (starts from `dead`), scan liveness, retiring inputs, copy/relocate, concrete error sources | later slices; `Ann.retire` takes `DefAddr P`; `Faults.lean` is an abstract oracle (re-checked in `Plan/AGENTS.md`) | later |
| O2 | `lakefile.toml` entry `"Semantics.PlanRetireTest","Semantics.SourceBindingUIDTest"` has no space (the patch carries it); cosmetic | present in the prototype lakefile | 1 line, Direct |
| O3 | Row-level kills for S3-M2, M4, M5, M7-M10 not probed (all killed at proofs) | by design; `a3a_notes` | none, or 1 optional probe dispatch |
| O4 | `dead`/`retPub` preservation has no fixture, only proofs | accepted | none |
| O5 | Mutation-manifest `--task` validation gap | separate open item (memory); not part of this slice; not re-measured | separate |
| O6 | Pre-slice-3 fixture count 200 (by `rg -c`) vs the path doc's 180: a difference of 20 (19 are `PlanFaultsTest` fixtures; 1 unexplained) | measured at authoring; the doc edit uses the measured total | none |
| O7 | doc comments that say "slice-1 profile" (`rg -n "slice-1 profile" leanncd/LeanNCD/Semantics/Plan --glob "*.lean"` at the prototype head: the `R` docstring in `Memory.lean`, the module headers of `Correctness.lean` and `Simulation.lean`; none in `Step.lean`, so slice 2's O6 about `Step.lean` is closed or moved) | cosmetic; the patches carry them unchanged | 1 comment edit + rebuild |

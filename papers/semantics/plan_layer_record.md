# Part V Plan layer, slice 1: record

Record, not the live plan (`plan_layer_plan.md`). Authoring facts below; the close-out section is
filled by the controller at the end of execution.

## Authoring dispatches

Tool-use counts are harness counts (CHECKPOINT §7: self-reports ran about 20 percent low).

| phase | output | harness tool uses |
|---|---|---:|
| A1 prototype | `Syntax`, `Batch`, `Memory`; `a1_notes.md` | 102 |
| A2 prototype | `Step`, `Simulation`; `a2_notes.md` | 147 |
| A3a prototype (finish) | `Validity`, `Run`; `a3a_notes.md` | 64 |
| A3b prototype | `Correctness`, comparison fixtures; `a3b_notes.md` | 78 |
| patch emission | `plan_layer_patches/0{1..5}-*.patch`, `manifest.json`, `evidence.json`, `emit-patches.py` | 44 |
| Phase B write-up | `plan_layer_plan.md`, `plan_layer_mutations_post.json`, this file | about 59 (own count at commit) |

## Authoring facts (measured)

- Patch base `0bf02e47`; scratch replay head `f14415ed`, tree `f3eee99e` (evidence.json). Replay:
  applying the five patches to the base gives the prototype tree on all 19 shipped paths.
- Per-task emission builds (evidence.json): T1 2960 jobs, T2 2961, T3 2963, T4 2966, T5 (default
  targets) 8784; all "Build completed successfully". Forbidden-token grep: 18 files, 0 hits.
- Patch sizes (lines): 429, 293, 786, 551, 830.
- Fixture count (scratch tree, counted): 50 `#eval check` rows + 46 top-level `example`/`theorem` = 96.
- Mutation manifest: 20 cycles (T1 2, T2 4, T3 5, T4 8, T5 1); 3 equivalent (A2-b, A2-e, A3a-a).
  `mutation-manifest.sh --check` against the scratch tree: "manifest OK: 20 entries, 20 selected,
  every old-string unique". The full manifest was NOT run at authoring. (Later run on the shipped
  tree, commit `5f1101d0`: 20/20; only the A1-d and A2-d `expect` strings changed; see plan §7 and
  `plan_layer_artifacts/manifest_run.md`.)
- Cycles whose `new` text or `expect` is not verbatim from the notes (to be confirmed by the
  controller's full run):
  - A1-a: mutant is last-writer-wins (`fun _ x`), not the recorded `if dest = p` form; location
    `Batch.lean` line 80 col 19 inferred from A1-b (the recorded line 84 came from a 5-line mutant).
  - A1-c: location moved from the recorded line 30 / 242 to 28 / 240 (recorded mutant was 3 lines;
    this one is 1 line); text reconstructed.
  - A1-d: `expect` keeps only "split_ifs failed" (recorded locations depend on the mutant's shape).
  - A2-d: `expect` "plan.Mat 2 (addr 0)" is the notes' description of the `decide` failure; the
    exact Lean wording is unconfirmed.
  - A2-e: `execAccSeq` body reconstructed (fold with per-member scan and commit).
  - A3b-2: field rename instead of field drop (manifest takes one site per entry).
  - All other cycles: `new` follows the notes' literal mutant text; `expect` locations were checked
    against the shipped files (each cited line holds the declaration the notes name).

## Close-out

- Execution worktree / branch: `.claude/worktrees/plan-layer-exec`, `worktree-plan-layer-exec`.
- Base `main` SHA at execution: `e259294b` (the docs-only landing commit on top of `0bf02e47`).
- Per-task commits and builds (controller ran each; patch sha256 matched `manifest.json`, `apply --check` clean):
  T1 `489443ab` (2960 jobs), T2 `81a3e646` (2961), T3 `de2cb75f` (2963), T4 `9cc2e758` (2966),
  T5 `b3028e57` (full default build, 8784 jobs). `leanncd` tree identical to the prototype branch.
- Docs-sweep commit: `59e8ef32`; whole-branch review fixes `a3faeb8a`; snapshot refresh in the next commit.
- Full default build: 8784 jobs, "Build completed successfully", no `error` line; no `sorry`,
  `axiom`, `admit` or `native_decide` in the shipped Lean (emission grep, plus `AxiomAudit`, which
  covers the whole `LeanNCD.Semantics` namespace, built green).
- Mutation manifest full run in the execution worktree: 20/20 PASS, every file restored
  byte-identical, no `expect` corrected (`plan_layer_mutation_results.md`, commit `ae641ba3`).
- Whole-branch review, soundness lens: `plan_layer_artifacts/wb_review_soundness.md`; no Critical or
  Important, six Minor (condition-1 "diagnostic" label, `runPlan_R` snapshot attribution, the
  unobservable-claim reason, missing `refState pc = some c` premise in three places, `SlotView`
  called the read view, "batched commands" out of scope), all applied.
- Whole-branch review, spec-Lean fidelity lens: `plan_layer_artifacts/wb_review_fidelity.md`; no
  Critical, two Important (Definition 31.1 versus Section 29.3 numbering in the spec block; path doc
  Snapshot paragraph stale), five Minor (4.8 table row, diagnostic wording, dropped does-not-do
  item, batched/fused wording, notation), all applied; the snapshot now names the plan layer.
- Fix dispatches: group A (spec) and group B (path doc and AGENTS nodes), one dispatch each,
  run in parallel on disjoint files.
- Open items resolved / parked (plan section 10): the 11 OPEN audit cells, the A2-e invalid-plan
  distinguishers, the Nodup/Fresh shadowing proof, D8 and the stale `Semantics/AGENTS.md` `Tests`
  sentence are all closed (sections below). Still parked: a proof that `checkAccMat` is implied by
  the other clauses (observed on four attempted plans, not proved), and the slice-2 deferrals D7, D11,
  D12 (implementation errors, multiple sorts in fixtures, `In ∩ Out`).
- Token total (`token-report.py`, this session only; prototype sessions A1-A3b are separate): 55.5M
  across the controller (18.5M, peak context 241k, 120 turns) and 12 dispatches, against the
  Rule 6 execution budget of about 175M. Harness tool uses ran above the agents' self-reports again:
  doc-sweep dispatch 71 (cap 55), fix group A 45 (cap 40), fidelity review 49 (cap 45).
- Merge SHA on local `main`: the `Merge branch 'worktree-plan-layer-exec'` commit; prototype branch
  tagged `plan-layer-slice1-proto` before deletion; branches and worktrees removed; not pushed
  (`main` stays ahead of `origin/main`).

## Review round 1

Two lenses, files `plan_layer_artifacts/review_fidelity.md` (F1..F13) and
`plan_layer_artifacts/review_soundness.md` (F-1..F-6). Section 8 and spec-restatement findings go to
the section 8 fix dispatch; the others were applied to plan sections 1-7, 9, 10 after checking the
claim against the shipped Lean and plan. No finding was rejected.

| ID | lens | severity | disposition |
|---|---|---|---|
| F1 | fidelity | Important | section 8 fix dispatch |
| F2 | fidelity | Important | section 8 fix dispatch |
| F3 | fidelity | Important | section 8 fix dispatch |
| F4 | fidelity | Important | section 8 fix dispatch |
| F5 | fidelity | Minor | section 8 fix dispatch |
| F6 | fidelity | Minor | applied to plan §1 (theorems are sort-generic over `K : S → Type`; only fixtures and profile use one sort); path doc 4.9 wording: section 8 fix dispatch |
| F7 | fidelity | Important | section 8 fix dispatch |
| F8 | fidelity | Minor | section 8 fix dispatch |
| F9 | fidelity | Minor | section 8 fix dispatch |
| F10 | fidelity | Minor | section 8 fix dispatch |
| F11 | fidelity | Important | section 8 fix dispatch |
| F12 | fidelity | Minor | section 8 fix dispatch |
| F13 | fidelity | Minor | section 8 fix dispatch |
| F-1 | soundness | Minor | applied: A2-e equivalence qualified to valid plans (N5, §5.2); reviewer-computed distinguishing plans in §10 item 10, marked not built or verified; A2-b and A3a-a confirmed for all plans |
| F-2 | soundness | Important | section 8 fix dispatch |
| F-3 | soundness | Minor | applied to D9, N6, §5.1 (`accFlat_complete` substantive, `cov1_of_cov2_pubOrder` Valid-level corollary); spec §8.1 citation: section 8 fix dispatch |
| F-4 | soundness | Minor | applied: `execAcc` within-group duplicate and `stepCommand` empty command now OPEN rows; §5 tallies and §10 item 3 parked cost updated; Nodup-pair equivalence and `checkInit` half noted |
| F-5 | soundness | Minor | applied to §3.1 (branch and clean-status gates, Co-Authored-By trailer) |
| F-6 | soundness | Minor | applied to §3.1 and §9.5 (tag `plan-layer-slice1-proto` kept before `branch -D`; review files and `manifest_run.md` in the landing set; Rule 13 scope; scratch worktree removal) |

Tool uses (harness counts): fidelity review 50 (self-reported ~34), soundness review 49
(self-reported ~37), manifest validation 43, Phase B authoring 61, patch emission 44.
Fix dispatches (harness counts): group P (plan body) 47 (self-reported 29, cap 45: breached), group S
(section 8 and spec restatement draft) 66 (self-reported ~41, cap 45: breached). Reconciled by the
controller afterwards: D5 row corrected, decision N9 added to plan section 2 (one-step simulation
proved for `Conf = refState pc` only), `D-sweep-1` renamed to N9. Briefs gave 35 as the aim; both
dispatches ran about 1.4-1.9x over the harness count, so budget fix dispatches at ~25 self-reported.

## Spec defects recovered (D7, D8, D11, D12)

The pre-A1 design review (originating session, section "Spec questions and defects, ranked") listed
twelve defects; D1-D6, D9, D10 were carried through the notes, and these four were not. Recovered
text (spec line numbers dropped):

- **D7 (medium).** The Section 30.1 state type has no implementation-error constructor, though
  Section 31.3 introduces implementation errors as a third terminal outcome. Proposed fix: add the
  constructor. Disposition: deferred with the error-free profile (slice 2, "implementation errors").
- **D8 (low).** The Section 32.3 "output view" is never defined (it occurs once, in the sentence
  "It must not expose partial accumulators through an output view while another contribution
  remains"). Fusion legality is already sequential composition, and the Publish side condition
  already keeps partial accumulators from being exposed. Proposed fix: drop the phrase or
  cross-reference. Disposition: applied in the parked-items slice: the phrase is replaced by the
  publication premise `U ∩ C_P(a) = ∅` of Section 29.2, checked after removing `G` (Section 32.3).
- **D11 (low).** Multi-sort `K` is unaddressed: the design review observed that slots carry one
  carrier and fixed the rationals for slice 1. Note (plan review F6): the theorems are generic over
  `K : S → Type`; only the fixtures use one sort. Disposition: parked (slice 2, multiple sorts).
- **D12 (low).** `In ∩ Out` is left open: if an input may also be an output, `Start` must map
  `pub(a)` for output inputs. Disposition: parked.

## Audit-cells slice (Direct path, tests only)

Closes plan section 10 item 3 (the 11 OPEN rows of section 5). Worktree `plan-layer-audit-cells`,
no production change, no new manifest entries, hand mutants run with `mutation-cycle.sh` and
reported in each commit body; fixtures in `PlanValidityTest.lean` and `PlanStepTest.lean`
(188 lines added). Full default build 8784 jobs green.

| commit | cell | result |
|---|---|---|
| `99b07bcf` | `checkPubFresh` duplicate / already-published | EQUIVALENT at `checkPlan`, paired with `checkCov2Nodup` (`pubTwice`, `pubDupIn`; neighbour `pubSplit`) |
| `a830be4c` | `checkAccFresh` within-group duplicate and consumed half | EQUIVALENT at `checkPlan`, paired with `checkCov1Nodup` (`dupWithin`; neighbour `accSplit`) |
| `316bc888` | `checkAccMat` | EQUIVALENT at `checkPlan`: no plan fails it alone (four attempts, each also trips `initFresh`, `pubMat` or `cov2Complete`); neighbour `lateEmptyInit` |
| `08c974b0` | `stepCommand` empty command | backed (`emptyCmd`: stuck; mutants B1, B1b flip the fixture) |
| `42dc4914` | `stepPlan` at `pc ≥ m` | backed (`step-plan-past-end`; mutant B2 flips the fixture) |
| `5a24ca59` | `checkInit` not-published half | backed at checker level (`reinitPub`: `initFresh@3` alone; run unchanged, done 4 `[0,14,0]`); the mutant stopped the build in `checkInit_sound` before the fixtures, so the flip was inferred from the halves row, not observed |

Also covered by run-level evidence from the same fixtures: the `execPub` already-published row
(`pubTwice` done 4, `pubDupIn` done 3, both `[0,14,0]`) and the within-group duplicate `execAcc`
row (`dupWithin` done 3 `[0,16,0]`, double-counted). No unsound plan found, no silent clause.
For every EQUIVALENT cell the hand mutant breaks `checkPlan_sound` before any fixture is reached,
so the claim "shadowed" rested on the fixtures when this slice closed. The parked-items slice below
proves it for the Nodup/Fresh pairs; `checkAccMat` stays observed only.

Harness tool uses: dispatch A 36 (cap 40), dispatch B 39 (cap 38; one `cd` plus a heredoc edit used
against the plain-command rule). Session token total after this slice (`token-report.py`): 71.5M.

## Parked-items slice (Direct path)

Worktree `plan-layer-parked-items`; closes the items the audit-cells slice left parked.

| commit | item | result |
|---|---|---|
| `db15f986` | A2-e outside the valid domain (plan section 10 item 10) | both reviewer-derived plans built as fixtures (`a2e-seq-visible`, `a2e-failed-vs-stuck`), `checkPlan`-invalid (`pubOrder@1`; `accMat@1`, `pubMat@2`); shipped `[0,3,1]` / `failed`, mutant (scratch run) `[0,3,4]` / `stuck`, exactly as predicted; valid neighbours agree under both |
| `88fed829` | Nodup redundancy | `checkPlan_nodup_redundant` (singleton and `checkSteps` imply `checkCov1Nodup` and `checkCov2Nodup`), `checkPlan_eq_core`; no `DefAddr.addr_injective` needed in this direction |
| `8b7cc508` | converse pairing | `checkAccFresh_of_cov1Nodup`, `checkPubFresh_of_cov2Nodup` (hold without `checkSingleton`): `checkCov1Nodup` implies every accumulate command's freshness clause and `checkCov2Nodup` every publish command's, and on a singleton plan the step checks imply the Nodup checks, so no singleton plan separates a Nodup check from its freshness clause (a non-singleton command is skipped by `checkSteps` but rejected by `checkSingleton`) |
| docs commit | D8, `Tests` sentence, plan sections 5 and 10, path doc counts | spec Section 32.3 cross-references the Publish premise; `Semantics/AGENTS.md` names the test groups and defers to `lakefile.toml`; path doc says 129 fixtures (96 shipped with the layer, 27 from the audit cells, 6 from this slice) and snapshot `8b7cc508` |

Findings: the proof needed no `DefAddr.addr_injective` in the redundancy direction (the reviewer
argument had assumed it). The plan's item 10 mis-cited `chainEarly` for `[0,3,1]` (that fixture
gives `stuck` with `[0,0,0]`); corrected. A scratch probe that imports an already-built test module
prints the shipped values under a mutant (stale downstream oleans): the mutant values here came
from a probe importing only `Semantics.PlanFixtures` with copied definitions, checked to print the
shipped values again after the revert.

Harness tool uses: A2-e dispatch 35 (self-reported 31; cap 40), Nodup proof 43 (cap 50). Full
default build 8784 jobs green; `AxiomAudit`: 5650 constants under `LeanNCD.Semantics` use only
standard axioms, including the new theorems.

Whole-branch review (single lens, `plan_layer_artifacts/wb_review_parked_items.md`; 27 harness tool
uses): no Critical or Important findings, five Minor, all applied: (1) fixture split corrected to
96 + 27 + 6 = 129; (2) the mutant values in plan section 5.2 labelled as a scratch run;
(3) verdict rows and `decide` examples added so the build asserts both A2-e plans are
`checkPlan`-invalid (`invalid-a2e-seq-visible`, `invalid-a2e-failed-vs-stuck`); (4) the pairing
claim qualified to singleton plans; (5) the D8 sentence now says "for every `a ∈ B`".
